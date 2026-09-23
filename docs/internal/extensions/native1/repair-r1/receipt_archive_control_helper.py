#!/usr/bin/env python3
"""Mutation and process-tree helper for the NATIVE-1-R1 receipt-archive controls.

`mutate` applies exactly one registered mutation to a DISPOSABLE COPY that
holds the manifest and the commands-root archives; it refuses a directory
inside the Git repository. `hold` starts a root and a child process that sleep
far beyond any control deadline, so the runner can check that the owned
process tooling removes both. The verifier itself is never modified here.

Exit codes: 0 applied/held; 2 usage error; 4 refused or precondition failure.
"""

import argparse
import gzip
import hashlib
import json
import os
import subprocess
import sys
import time
import zlib

MANIFEST_REL = "docs/internal/extensions/native1/repair-r1/RECEIPT_ARCHIVES.json"
COMMANDS_ROOT = "docs/internal/extensions/native1/commands/"
TARGET = COMMANDS_ROOT + "final-claims-public.json"
SUBSTITUTE = COMMANDS_ROOT + "final-static-command.json"
EXTRA_ARCHIVE = COMMANDS_ROOT + "control-unlisted-receipt.json.gz"
MUTATIONS = (
    "changed-archive-header-byte",
    "changed-archive-trailer-byte",
    "missing-archive",
    "extra-archive",
    "duplicate-manifest-entry",
    "wrong-base-blob-id",
    "decompressed-byte-mismatch",
    "original-restored",
    "manifest-entry-removed",
)
HOLD_SECONDS = 600


class Refused(Exception):
    pass


def sha256(data):
    return hashlib.sha256(data).hexdigest().upper()


def local(copy, rel):
    return os.path.join(copy, *rel.split("/"))


def read_bytes(path):
    with open(path, "rb") as handle:
        return handle.read()


def write_bytes(path, data):
    with open(path, "wb") as handle:
        handle.write(data)


def load_manifest(copy):
    return json.loads(read_bytes(local(copy, MANIFEST_REL)).decode("utf-8"))


def save_manifest(copy, manifest):
    text = json.dumps(manifest, indent=2, ensure_ascii=True) + "\n"
    write_bytes(local(copy, MANIFEST_REL), text.encode("ascii"))


def only_entry(manifest, original):
    matches = [e for e in manifest["archives"] if e["originalPath"] == original]
    if len(matches) != 1:
        raise Refused(f"expected exactly one manifest entry for {original}, found {len(matches)}")
    return matches[0]


def refuse_repository_copy(copy, repo):
    copy_real = os.path.normcase(os.path.realpath(copy))
    repo_real = os.path.normcase(os.path.realpath(repo))
    try:
        inside = os.path.commonpath([copy_real, repo_real]) == repo_real
    except ValueError:
        inside = False
    if inside:
        raise Refused(f"refusing to mutate {copy}: it is inside the repository {repo}")
    if not os.path.isfile(local(copy, MANIFEST_REL)):
        raise Refused(f"{copy} does not hold a disposable manifest copy")


def mutate(case, copy, repo):
    refuse_repository_copy(copy, repo)
    manifest = load_manifest(copy)
    target = only_entry(manifest, TARGET)
    archive_path = local(copy, target["archivePath"])
    changed = []
    if case in ("changed-archive-header-byte", "changed-archive-trailer-byte"):
        data = bytearray(read_bytes(archive_path))
        if data[:4] != b"\x1f\x8b\x08\x00":
            raise Refused("target archive does not start with a plain gzip header")
        # Header byte 4 is the low MTIME byte: decoding ignores it, so only the
        # archive digest can reject this. Trailer byte -8 is the low CRC-32 byte:
        # the recovered bytes are intact but the gzip integrity check fails.
        offset = 4 if case == "changed-archive-header-byte" else len(data) - 8
        before = sha256(bytes(data))
        data[offset] ^= 0x01
        write_bytes(archive_path, bytes(data))
        changed.append((target["archivePath"], before, sha256(bytes(data)), f"offset {offset}"))
    elif case == "missing-archive":
        before = sha256(read_bytes(archive_path))
        os.remove(archive_path)
        changed.append((target["archivePath"], before, "absent", "removed"))
    elif case == "extra-archive":
        path = local(copy, EXTRA_ARCHIVE)
        if os.path.lexists(path):
            raise Refused(f"{EXTRA_ARCHIVE} already exists in the copy")
        data = gzip.compress(b"{}\n", compresslevel=9, mtime=0)
        write_bytes(path, data)
        changed.append((EXTRA_ARCHIVE, "absent", sha256(data), "added"))
    elif case == "duplicate-manifest-entry":
        manifest["archives"].append(dict(target))
        save_manifest(copy, manifest)
        changed.append((MANIFEST_REL, "", "", f"appended a second entry for {TARGET}"))
    elif case == "wrong-base-blob-id":
        substitute = only_entry(manifest, SUBSTITUTE)
        if substitute["baseBlobId"] == target["baseBlobId"]:
            raise Refused("substitute blob id equals the target blob id")
        target["baseBlobId"] = substitute["baseBlobId"]
        save_manifest(copy, manifest)
        changed.append((MANIFEST_REL, "", "", f"{TARGET} baseBlobId := {substitute['baseBlobId']}"))
    elif case == "decompressed-byte-mismatch":
        decoder = zlib.decompressobj(wbits=31)
        raw = bytearray(decoder.decompress(read_bytes(archive_path)) + decoder.flush())
        if not decoder.eof or decoder.unused_data:
            raise Refused("target archive is not one complete gzip member")
        offset = len(raw) // 2
        raw[offset] ^= 0x01
        data = gzip.compress(bytes(raw), compresslevel=9, mtime=0)
        before = sha256(read_bytes(archive_path))
        write_bytes(archive_path, data)
        # Keep the archive digest and length consistent, so that only the
        # comparison of recovered bytes with the base blob can reject this.
        target["archiveSha256"] = sha256(data)
        target["archiveBytes"] = len(data)
        save_manifest(copy, manifest)
        changed.append((target["archivePath"], before, sha256(data),
                        f"recovered byte {offset} flipped; manifest archive digest/length updated"))
    elif case == "original-restored":
        path = local(copy, target["originalPath"])
        if os.path.lexists(path):
            raise Refused(f"{target['originalPath']} already exists in the copy")
        result = subprocess.run(["git", "-C", repo, "cat-file", "blob", target["baseBlobId"]],
                                capture_output=True, timeout=300)
        if result.returncode != 0 or sha256(result.stdout) != target["baseBlobSha256"]:
            raise Refused("could not read the exact base blob for the original receipt")
        write_bytes(path, result.stdout)
        changed.append((target["originalPath"], "absent", sha256(result.stdout), "restored base blob"))
    elif case == "manifest-entry-removed":
        manifest["archives"] = [e for e in manifest["archives"] if e["originalPath"] != TARGET]
        save_manifest(copy, manifest)
        changed.append((MANIFEST_REL, "", "", f"removed the entry for {TARGET}; its archive stays"))
    else:
        raise Refused(f"unregistered mutation {case!r}")
    for path, before, after, detail in changed:
        print(f"MUTATION-APPLIED [{case}] {path} {before} -> {after} ({detail})", flush=True)


def hold(pid_dir):
    os.makedirs(pid_dir, exist_ok=True)
    write_bytes(os.path.join(pid_dir, "root.pid"), str(os.getpid()).encode("ascii"))
    child = subprocess.Popen([sys.executable, os.path.abspath(__file__), "hold-child",
                              "--pid-dir", pid_dir])
    child_pid_file = os.path.join(pid_dir, "child.pid")
    deadline = time.monotonic() + 30
    while not os.path.isfile(child_pid_file) and time.monotonic() < deadline:
        time.sleep(0.05)
    print(f"HOLD-READY root={os.getpid()} child={child.pid}", flush=True)
    time.sleep(HOLD_SECONDS)
    return 0


def hold_child(pid_dir):
    write_bytes(os.path.join(pid_dir, "child.pid"), str(os.getpid()).encode("ascii"))
    time.sleep(HOLD_SECONDS)
    return 0


def main(argv):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = parser.add_subparsers(dest="command", required=True)
    mutate_parser = sub.add_parser("mutate")
    mutate_parser.add_argument("--case", required=True, choices=MUTATIONS)
    mutate_parser.add_argument("--copy", required=True)
    mutate_parser.add_argument("--repo", required=True)
    for name in ("hold", "hold-child"):
        sub.add_parser(name).add_argument("--pid-dir", required=True)
    args = parser.parse_args(argv)
    try:
        if args.command == "mutate":
            mutate(args.case, os.path.abspath(args.copy), os.path.abspath(args.repo))
            return 0
        if args.command == "hold":
            return hold(os.path.abspath(args.pid_dir))
        return hold_child(os.path.abspath(args.pid_dir))
    except (Refused, OSError, KeyError, ValueError, subprocess.TimeoutExpired) as exc:
        print(f"MUTATION-REFUSED {exc}", flush=True)
        return 4


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
