#!/usr/bin/env python3
"""Exports, mutations and a descendant-spawning sleeper for the PRE-1-R1 controls.

run_repair_controls.ps1 invokes this helper under the repository's owned-process
supervisor.
  export   writes the exact committed blob bytes of the lane root and of
           docs/internal/audit_reports/ at a revision into a disposable copy
           directory outside the repository (no checkout conversion);
  mutate   changes only that copy; the repository is read through Git objects;
  sleeper  starts a child process and sleeps, so the runner can check that a
           deadline removes the whole owned tree.
Synthesized scanner text is assembled from pieces at run time, so this file
contains neither a scanner result line nor the scanner summary text.
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
import verify_receipt_archives as va  # noqa: E402
import verify_rewords as vr  # noqa: E402

EXPORT_PREFIXES = (va.HISTORY_ROOT, "docs/internal/audit_reports/")
STAGE_LOG = va.HISTORY_ROOT + "BUILDER_STAGE_LOG.md"
MUTATIONS = (
    "archives-positive-copy", "archives-changed-archive-header-byte", "archives-changed-archive-trailer-byte",
    "archives-missing-archive", "archives-extra-archive", "archives-duplicate-manifest-entry",
    "archives-wrong-base-blob-id", "archives-decompressed-byte-mismatch", "archives-original-restored",
    "archives-audit-report-restored", "archives-manifest-entry-removed", "archives-result-line-file",
    "rewords-positive-copy", "rewords-changed-integer", "rewords-unrecorded-line-changed",
    "rewords-missing-recorded-line", "rewords-reintroduced-pattern", "rewords-wrong-base-line-hash",
    "rewords-manifest-entry-removed", "rewords-pattern-in-new-file",
)


def copy_path(copy, rel):
    return os.path.join(copy, *rel.split("/"))


def load_json(copy, rel):
    with open(copy_path(copy, rel), "rb") as handle:
        return json.loads(handle.read().decode("utf-8"), object_pairs_hook=va.reject_duplicate_keys)


def save_json(copy, rel, value):
    with open(copy_path(copy, rel), "w", encoding="utf-8", newline="\n") as handle:
        json.dump(value, handle, indent=2, ensure_ascii=True)
        handle.write("\n")


def read_bytes(copy, rel):
    with open(copy_path(copy, rel), "rb") as handle:
        return handle.read()


def write_bytes(copy, rel, data):
    os.makedirs(os.path.dirname(copy_path(copy, rel)), exist_ok=True)
    with open(copy_path(copy, rel), "wb") as handle:
        handle.write(data)


def flip_byte(copy, rel, offset):
    data = bytearray(read_bytes(copy, rel))
    data[offset] ^= 0x01
    write_bytes(copy, rel, bytes(data))


def export(repo, rev, dest):
    git = va.Git(repo)
    head = git.resolve_commit(rev)
    if head is None:
        raise SystemExit(f"{rev} is not a commit")
    if os.path.exists(dest):
        raise SystemExit(f"{dest} already exists")
    entries = {}
    for prefix in EXPORT_PREFIXES:
        entries.update(git.tree(head, prefix))
    blobs = {p: e for p, e in entries.items() if e[1] == "blob"}
    objects = git.blobs([e[2] for e in blobs.values()])
    for path, (_mode, _kind, oid) in sorted(blobs.items()):
        write_bytes(dest, path, objects[oid])
    return f"exported {len(blobs)} blobs of {head} under {', '.join(EXPORT_PREFIXES)}"


def mutate(case, copy, repo):
    archives = load_json(copy, va.MANIFEST_REL)
    first, second = archives["archives"][0], archives["archives"][1]
    git = va.Git(repo)
    if case in ("archives-positive-copy", "rewords-positive-copy"):
        return "no mutation"
    if case == "archives-changed-archive-header-byte":
        flip_byte(copy, first["archivePath"], 9)
        return f"flipped bit 0 of byte 9 (gzip OS field) of {first['archivePath']}"
    if case == "archives-changed-archive-trailer-byte":
        size = len(read_bytes(copy, first["archivePath"]))
        flip_byte(copy, first["archivePath"], size - 1)
        return f"flipped bit 0 of the last byte (gzip ISIZE) of {first['archivePath']}"
    if case == "archives-missing-archive":
        os.remove(copy_path(copy, first["archivePath"]))
        return f"deleted {first['archivePath']}"
    if case == "archives-extra-archive":
        rel = va.HISTORY_ROOT + "evidence/unlisted-control-extra.json.gz"
        write_bytes(copy, rel, gzip.compress(b"{}\n", compresslevel=9, mtime=0))
        return f"added valid gzip {rel}, absent from the manifest and the base tree"
    if case == "archives-duplicate-manifest-entry":
        archives["archives"].insert(1, dict(first))
        save_json(copy, va.MANIFEST_REL, archives)
        return f"inserted a second copy of the {first['originalPath']} entry next to the first"
    if case == "archives-wrong-base-blob-id":
        first["baseBlobId"] = second["baseBlobId"]
        save_json(copy, va.MANIFEST_REL, archives)
        return f"set the {first['originalPath']} baseBlobId to the other entry's blob id"
    if case == "archives-decompressed-byte-mismatch":
        data = bytearray(git.blobs([first["baseBlobId"]])[first["baseBlobId"]])
        middle = len(data) // 2
        data[middle] = ord("X") if data[middle] != ord("X") else ord("Y")
        forged = gzip.compress(bytes(data), compresslevel=9, mtime=0)
        write_bytes(copy, first["archivePath"], forged)
        first["archiveSha256"] = va.sha256(forged)
        first["archiveBytes"] = len(forged)
        save_json(copy, va.MANIFEST_REL, archives)
        return (f"replaced {first['archivePath']} by a well-formed gzip of the base bytes with byte {middle} changed and "
                f"updated archiveSha256 and archiveBytes, so only the decompressed content differs")
    if case == "archives-original-restored":
        entry = next(e for e in archives["archives"] if e["selectionKind"] == "result-line")
        write_bytes(copy, entry["originalPath"], git.blobs([entry["baseBlobId"]])[entry["baseBlobId"]])
        return f"wrote the exact base blob bytes of {entry['originalPath']} beside its archive"
    if case == "archives-audit-report-restored":
        entry = next(e for e in archives["archives"] if e["selectionKind"] == "named")
        write_bytes(copy, entry["originalPath"], git.blobs([entry["baseBlobId"]])[entry["baseBlobId"]])
        return f"wrote the exact base blob bytes of {entry['originalPath']} back into audit_reports"
    if case == "archives-manifest-entry-removed":
        removed = archives["archives"].pop(1)
        save_json(copy, va.MANIFEST_REL, archives)
        return f"removed the {removed['originalPath']} entry; its archive stays"
    if case == "archives-result-line-file":
        rel = va.HISTORY_ROOT + "repair-r1/control-result-line.txt"
        line = "CLAIM-DRIFT" + "[control-rule]" + "[control-status]" + "[review] control.md:1: control\n"
        write_bytes(copy, rel, line.encode("ascii"))
        return f"added {rel} holding one synthesized scanner result line"

    rewords = load_json(copy, vr.MANIFEST_REL)
    by_key = {(e["path"], e["baseLineNumber"]): e for e in rewords["rewords"]}
    stage_lines = read_bytes(copy, STAGE_LOG).split(b"\n")
    if case == "rewords-changed-integer":
        entry = by_key[(STAGE_LOG, 488)]
        old = stage_lines[487]
        index = old.index(b"1609")
        stage_lines[487] = old[:index] + b"1610" + old[index + 4:]
        write_bytes(copy, STAGE_LOG, b"\n".join(stage_lines))
        entry["newLineSha256"] = vr.sha256(stage_lines[487])
        entry["newIntegers"] = vr.integers(stage_lines[487])
        save_json(copy, vr.MANIFEST_REL, rewords)
        return (f"changed the reworded count 1609 to 1610 in {STAGE_LOG}:488 and recorded the mutated line's hash and "
                f"integers, so only the integer and digit-run equality with the base line differs")
    if case == "rewords-unrecorded-line-changed":
        stage_lines[425] = stage_lines[425] + b" control"
        write_bytes(copy, STAGE_LOG, b"\n".join(stage_lines))
        return f"appended a word to {STAGE_LOG}:426, which is not a recorded line"
    if case == "rewords-missing-recorded-line":
        del stage_lines[487]
        write_bytes(copy, STAGE_LOG, b"\n".join(stage_lines))
        return f"deleted the reworded line {STAGE_LOG}:488 from the tip copy"
    if case == "rewords-reintroduced-pattern":
        oid = by_key[(STAGE_LOG, 488)]["baseBlobId"]
        base_line = git.blobs([oid])[oid].split(b"\n")[487]
        stage_lines[487] = base_line
        write_bytes(copy, STAGE_LOG, b"\n".join(stage_lines))
        return f"restored the exact base bytes of {STAGE_LOG}:488, which match the summary pattern"
    if case == "rewords-wrong-base-line-hash":
        entry = by_key[(STAGE_LOG, 488)]
        entry["baseLineSha256"] = by_key[(STAGE_LOG, 427)]["baseLineSha256"]
        save_json(copy, vr.MANIFEST_REL, rewords)
        return f"set the {STAGE_LOG}:488 baseLineSha256 to the hash recorded for line 427"
    if case == "rewords-manifest-entry-removed":
        removed = rewords["rewords"].pop()
        save_json(copy, vr.MANIFEST_REL, rewords)
        return f"removed the {removed['path']}:{removed['baseLineNumber']} entry; the tip line stays reworded"
    if case == "rewords-pattern-in-new-file":
        rel = va.HISTORY_ROOT + "repair-r1/control-pattern.md"
        text = "control: " + "scan" + " complete (" + "7 hits, 0 strict failures)\n"
        write_bytes(copy, rel, text.encode("ascii"))
        return f"added {rel} holding one synthesized summary-pattern line"
    raise SystemExit(f"unknown mutation {case!r}")


def sleeper(pid_file):
    child = subprocess.Popen([sys.executable, "-B", "-c", "import time; time.sleep(600)"])
    with open(pid_file, "w", encoding="ascii") as handle:
        handle.write(f"{os.getpid()} {child.pid}\n")
    time.sleep(600)


def main(argv):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = parser.add_subparsers(dest="command", required=True)
    e = sub.add_parser("export")
    e.add_argument("--repo", required=True)
    e.add_argument("--rev", required=True)
    e.add_argument("--dest", required=True)
    m = sub.add_parser("mutate")
    m.add_argument("--case", required=True, choices=MUTATIONS)
    m.add_argument("--copy", required=True)
    m.add_argument("--repo", required=True)
    s = sub.add_parser("sleeper")
    s.add_argument("--pid-file", required=True)
    args = parser.parse_args(argv)
    if args.command == "export":
        print("REPAIR-CONTROL-EXPORT: " + export(os.path.abspath(args.repo), args.rev, os.path.abspath(args.dest)), flush=True)
        return 0
    if args.command == "mutate":
        copy = os.path.abspath(args.copy)
        if not os.path.isfile(copy_path(copy, va.MANIFEST_REL)) or not os.path.isfile(copy_path(copy, vr.MANIFEST_REL)):
            raise SystemExit(f"copy {copy} has no manifests")
        print("REPAIR-CONTROL-MUTATION: " + mutate(args.case, copy, os.path.abspath(args.repo)), flush=True)
        return 0
    sleeper(args.pid_file)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
