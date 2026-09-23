#!/usr/bin/env python3
"""Mutations and a descendant-spawning sleeper for the OPT-1-R2 archive controls.

run_receipt_archive_controls.ps1 invokes this helper under the repository's
owned-process supervisor. `mutate` changes only a disposable copy directory that
the runner created outside the repository; the repository is read through Git
objects only. `sleeper` starts a child process and sleeps, so the runner can
check that a deadline removes the whole owned tree.
"""

import argparse
import gzip
import json
import os
import subprocess
import sys
import time

sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import verify_receipt_archives as verifier  # noqa: E402

MUTATIONS = (
    "positive-copy", "changed-archive-header-byte", "changed-archive-trailer-byte", "missing-archive",
    "extra-archive", "duplicate-manifest-entry", "wrong-base-blob-id", "decompressed-byte-mismatch",
    "original-restored", "manifest-entry-removed", "new-result-line-file",
)


def copy_path(copy, rel):
    return os.path.join(copy, *rel.split("/"))


def load_manifest(copy):
    with open(copy_path(copy, verifier.MANIFEST_REL), "rb") as handle:
        return json.loads(handle.read().decode("utf-8"), object_pairs_hook=verifier.reject_duplicate_keys)


def save_manifest(copy, manifest):
    with open(copy_path(copy, verifier.MANIFEST_REL), "w", encoding="utf-8", newline="\n") as handle:
        json.dump(manifest, handle, indent=2, ensure_ascii=True)
        handle.write("\n")


def flip_byte(path, offset):
    with open(path, "rb") as handle:
        data = bytearray(handle.read())
    data[offset] ^= 0x01
    with open(path, "wb") as handle:
        handle.write(bytes(data))


def base_bytes(repo, entry):
    return verifier.Git(repo).blobs([entry["baseBlobId"]])[entry["baseBlobId"]]


def mutate(case, copy, repo):
    if not os.path.isfile(copy_path(copy, verifier.MANIFEST_REL)):
        raise SystemExit(f"copy {copy} has no manifest")
    manifest = load_manifest(copy)
    first, second = manifest["archives"][0], manifest["archives"][1]
    if case == "positive-copy":
        return "no mutation"
    if case == "changed-archive-header-byte":
        flip_byte(copy_path(copy, first["archivePath"]), 9)
        return f"flipped bit 0 of byte 9 (gzip OS field) of {first['archivePath']}"
    if case == "changed-archive-trailer-byte":
        path = copy_path(copy, first["archivePath"])
        flip_byte(path, os.path.getsize(path) - 1)
        return f"flipped bit 0 of the last byte (gzip ISIZE) of {first['archivePath']}"
    if case == "missing-archive":
        os.remove(copy_path(copy, first["archivePath"]))
        return f"deleted {first['archivePath']}"
    if case == "extra-archive":
        rel = verifier.HISTORY_ROOT + "unlisted-control-extra.json.gz"
        with open(copy_path(copy, rel), "wb") as handle:
            handle.write(gzip.compress(b"{}\n", compresslevel=9, mtime=0))
        return f"added valid gzip {rel} absent from the manifest and the base tree"
    if case == "duplicate-manifest-entry":
        manifest["archives"].insert(1, dict(first))
        save_manifest(copy, manifest)
        return f"inserted a second copy of the {first['originalPath']} entry next to the first"
    if case == "wrong-base-blob-id":
        first["baseBlobId"] = second["baseBlobId"]
        save_manifest(copy, manifest)
        return f"set the {first['originalPath']} baseBlobId to the other entry's blob id {second['baseBlobId']}"
    if case == "decompressed-byte-mismatch":
        data = bytearray(base_bytes(repo, first))
        middle = len(data) // 2
        data[middle] = ord("X") if data[middle] != ord("X") else ord("Y")
        forged = gzip.compress(bytes(data), compresslevel=9, mtime=0)
        with open(copy_path(copy, first["archivePath"]), "wb") as handle:
            handle.write(forged)
        first["archiveSha256"] = verifier.sha256(forged)
        first["archiveBytes"] = len(forged)
        save_manifest(copy, manifest)
        return (f"replaced {first['archivePath']} by a well-formed gzip of the base bytes with byte {middle} changed "
                f"and updated archiveSha256/archiveBytes to match, so only decompressed content differs")
    if case == "original-restored":
        with open(copy_path(copy, first["originalPath"]), "wb") as handle:
            handle.write(base_bytes(repo, first))
        return f"wrote the exact base blob bytes of {first['originalPath']} beside its archive"
    if case == "manifest-entry-removed":
        removed = manifest["archives"].pop(1)
        save_manifest(copy, manifest)
        return f"removed the {removed['originalPath']} entry; its archive stays"
    if case == "new-result-line-file":
        rel = verifier.HISTORY_ROOT + "repair-r2/control-new-result-line.txt"
        line = "CLAIM-DRIFT" + "[control-rule][control-status][review] control.md:1: control\n"
        with open(copy_path(copy, rel), "w", encoding="utf-8", newline="\n") as handle:
            handle.write(line)
        return f"added {rel} holding one synthesized scanner result line"
    raise SystemExit(f"unknown mutation {case!r}")


def sleeper(pid_file):
    child = subprocess.Popen([sys.executable, "-B", "-c", "import time; time.sleep(600)"])
    with open(pid_file, "w", encoding="ascii") as handle:
        handle.write(f"{os.getpid()} {child.pid}\n")
    time.sleep(600)


def main(argv):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = parser.add_subparsers(dest="command", required=True)
    m = sub.add_parser("mutate")
    m.add_argument("--case", required=True, choices=MUTATIONS)
    m.add_argument("--copy", required=True)
    m.add_argument("--repo", required=True)
    s = sub.add_parser("sleeper")
    s.add_argument("--pid-file", required=True)
    args = parser.parse_args(argv)
    if args.command == "mutate":
        print("RECEIPT-CONTROL-MUTATION: " + mutate(args.case, os.path.abspath(args.copy), os.path.abspath(args.repo)),
              flush=True)
        return 0
    sleeper(args.pid_file)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
