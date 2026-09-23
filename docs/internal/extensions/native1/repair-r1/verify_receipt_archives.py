#!/usr/bin/env python3
"""Verify the NATIVE-1-R1 receipt archives against the exact base Git blobs.

The manifest RECEIPT_ARCHIVES.json beside this file records, for every NATIVE-1
command receipt that embedded claim-scanner result lines at the base commit,
the original path, its Git blob id, the SHA-256 and length of those blob bytes,
the archive path, the archive SHA-256 and length and the decompressed length.

Nothing recorded in the manifest is trusted. Every value is recomputed from the
archives (in a directory tree, or as committed blobs with --committed) and from
`git cat-file` on the base commit, and the selected set is recomputed from the
base tree. Missing, duplicate, extra and mismatching entries are rejected.

Exit codes: 0 verified; 1 verification failure; 2 usage error (argparse);
3 environment error (Git unavailable, timeout, unreadable object).
Every failure prints one line `RECEIPT-ARCHIVES: FAIL [<code>] <detail>`.
"""

import argparse
import collections
import hashlib
import json
import os
import re
import subprocess
import sys
import zlib

SCHEMA = "rmq.native1.repair-r1.receipt-archives.v1"
HANDLE = "NATIVE-1-R1"
MANIFEST_REL = "docs/internal/extensions/native1/repair-r1/RECEIPT_ARCHIVES.json"
COMMANDS_ROOT = "docs/internal/extensions/native1/commands/"
RESULT_LINE_REGEX = r"CLAIM-DRIFT\[[^\]\r\n]*\]\[[^\]\r\n]*\]"
RESULT_LINE = re.compile(RESULT_LINE_REGEX.encode("ascii"))
# Any occurrence of the scanner prefix at all. If a receipt contains the prefix
# but no line matches RESULT_LINE, the selection rule is ambiguous and fails.
PREFIX_GUARD = b"CLAIM-DRIFT" + b"["
GIT_TIMEOUT_SECONDS = 300

TOP_KEYS = {"schema", "handle", "baseCommit", "selection", "encoding",
            "referenceResolution", "archives"}
SELECTION_KEYS = {"commandsRoot", "resultLineRegex", "rule"}
ENTRY_KEYS = {"originalPath", "baseBlobId", "baseBlobSha256", "baseBlobBytes",
              "claimScannerResultLines", "archivePath", "archiveSha256",
              "archiveBytes", "decompressedBytes", "referringFilesAtBase"}
HEX40 = re.compile(r"^[0-9a-f]{40}$")
HEX64 = re.compile(r"^[0-9A-F]{64}$")


class EnvironmentFailure(Exception):
    pass


class Git:
    def __init__(self, repo):
        self.repo = repo

    def run(self, *args):
        try:
            result = subprocess.run(
                ["git", "-C", self.repo, *args], capture_output=True,
                timeout=GIT_TIMEOUT_SECONDS)
        except (OSError, subprocess.TimeoutExpired) as exc:
            raise EnvironmentFailure(f"git {' '.join(args[:2])}: {exc}")
        return result

    def checked(self, *args):
        result = self.run(*args)
        if result.returncode != 0:
            raise EnvironmentFailure(
                f"git {' '.join(args[:2])} exited {result.returncode}: "
                f"{result.stderr.decode('utf-8', 'replace').strip()}")
        return result.stdout

    def resolve_commit(self, rev):
        result = self.run("rev-parse", "--verify", "--quiet", rev + "^{commit}")
        if result.returncode != 0:
            return None
        return result.stdout.decode("ascii").strip()

    def tree_blobs(self, rev, prefix):
        """Map path -> blob id for every blob under prefix at rev."""
        out = self.checked("ls-tree", "-r", "-z", "--full-tree", rev, "--", prefix)
        blobs = {}
        for record in out.split(b"\0"):
            if not record:
                continue
            meta, path = record.split(b"\t", 1)
            _mode, kind, oid = meta.split(b" ")
            if kind == b"blob":
                blobs[path.decode("utf-8")] = oid.decode("ascii")
        return blobs

    def blob_bytes(self, oid):
        data = self.checked("cat-file", "blob", oid)
        # The object id is the SHA-1 of the raw object; recomputing it proves
        # these are the stored blob bytes and not a filtered or converted copy.
        header = b"blob %d\0" % len(data)
        if hashlib.sha1(header + data).hexdigest() != oid:
            raise EnvironmentFailure(f"cat-file returned bytes that do not hash to {oid}")
        return data

    def referring_files(self, rev, name):
        pattern = "(?<![A-Za-z0-9_.-])" + re.escape(name) + "(?![A-Za-z0-9_-])"
        result = self.run("grep", "-l", "-z", "-P", "-e", pattern, rev, "--")
        if result.returncode not in (0, 1):
            raise EnvironmentFailure(
                f"git grep exited {result.returncode}: "
                f"{result.stderr.decode('utf-8', 'replace').strip()}")
        prefix = rev + ":"
        paths = []
        for item in result.stdout.split(b"\0"):
            if not item:
                continue
            text = item.decode("utf-8")
            if not text.startswith(prefix):
                raise EnvironmentFailure(f"unexpected git grep path {text!r}")
            paths.append(text[len(prefix):])
        return sorted(paths)


class Reporter:
    def __init__(self):
        self.failures = []

    def fail(self, code, detail):
        self.failures.append(code)
        print(f"RECEIPT-ARCHIVES: FAIL [{code}] {detail}", flush=True)

    def ok(self, detail):
        print(f"RECEIPT-ARCHIVES: ok {detail}", flush=True)


def reject_duplicate_keys(pairs):
    seen = {}
    for key, value in pairs:
        if key in seen:
            raise ValueError(f"duplicate JSON key {key!r}")
        seen[key] = value
    return seen


def safe_relative(path):
    return (isinstance(path, str) and path and not path.startswith("/")
            and "\\" not in path and ":" not in path
            and all(part not in ("", ".", "..") for part in path.split("/")))


def validate_manifest_shape(manifest, rep):
    before = len(rep.failures)
    if not isinstance(manifest, dict):
        rep.fail("manifest-schema", "top level is not an object")
        return False
    if set(manifest) != TOP_KEYS:
        rep.fail("manifest-schema", f"top-level keys {sorted(manifest)} != {sorted(TOP_KEYS)}")
        return False
    if manifest["schema"] != SCHEMA:
        rep.fail("manifest-schema", f"schema {manifest['schema']!r} != {SCHEMA!r}")
    if manifest["handle"] != HANDLE:
        rep.fail("manifest-schema", f"handle {manifest['handle']!r} != {HANDLE!r}")
    if not isinstance(manifest["baseCommit"], str) or not HEX40.match(manifest["baseCommit"]):
        rep.fail("manifest-schema", "baseCommit is not a 40-character lowercase hex id")
    selection = manifest["selection"]
    if not isinstance(selection, dict) or set(selection) != SELECTION_KEYS:
        rep.fail("manifest-schema", "selection keys differ from the pinned set")
    else:
        if selection["commandsRoot"] != COMMANDS_ROOT:
            rep.fail("manifest-schema", "selection.commandsRoot differs from the pinned root")
        if selection["resultLineRegex"] != RESULT_LINE_REGEX:
            rep.fail("manifest-schema", "selection.resultLineRegex differs from the pinned regex")
    for field in ("encoding", "referenceResolution"):
        if not manifest[field]:
            rep.fail("manifest-schema", f"{field} is empty")
    archives = manifest["archives"]
    if not isinstance(archives, list) or not archives:
        rep.fail("manifest-schema", "archives is not a nonempty list")
        return False
    for index, entry in enumerate(archives):
        if not isinstance(entry, dict) or set(entry) != ENTRY_KEYS:
            keys = sorted(entry) if isinstance(entry, dict) else type(entry).__name__
            rep.fail("manifest-schema", f"archives[{index}] keys {keys} != pinned entry keys")
            continue
        for key in ("originalPath", "archivePath"):
            if not safe_relative(entry[key]):
                rep.fail("manifest-schema", f"archives[{index}].{key} is not a safe relative path")
        if isinstance(entry["originalPath"], str) and not entry["originalPath"].startswith(COMMANDS_ROOT):
            rep.fail("manifest-schema", f"archives[{index}].originalPath is outside {COMMANDS_ROOT}")
        if not isinstance(entry["baseBlobId"], str) or not HEX40.match(entry["baseBlobId"]):
            rep.fail("manifest-schema", f"archives[{index}].baseBlobId is not a 40-hex id")
        for key in ("baseBlobSha256", "archiveSha256"):
            if not isinstance(entry[key], str) or not HEX64.match(entry[key]):
                rep.fail("manifest-schema", f"archives[{index}].{key} is not uppercase SHA-256 hex")
        for key in ("baseBlobBytes", "claimScannerResultLines", "archiveBytes", "decompressedBytes"):
            value = entry[key]
            if not isinstance(value, int) or isinstance(value, bool) or value < 0:
                rep.fail("manifest-schema", f"archives[{index}].{key} is not a nonnegative integer")
        refs = entry["referringFilesAtBase"]
        if not isinstance(refs, list) or not all(isinstance(r, str) for r in refs):
            rep.fail("manifest-schema", f"archives[{index}].referringFilesAtBase is not a list of paths")
    return len(rep.failures) == before


def decompress_single_member(data):
    decoder = zlib.decompressobj(wbits=31)  # gzip wrapper: header, CRC-32 and ISIZE checked
    out = decoder.decompress(data) + decoder.flush()
    if not decoder.eof:
        raise ValueError("truncated gzip member")
    if decoder.unused_data:
        raise ValueError(f"{len(decoder.unused_data)} bytes after the first gzip member")
    return out


def count_result_lines(data):
    return sum(1 for line in data.split(b"\n") if RESULT_LINE.search(line))


def main(argv):
    script_root = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                               *([os.pardir] * 5)))
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--tree", default=script_root,
                        help="directory tree holding the manifest and archives (default: this repository)")
    parser.add_argument("--repo", default=None,
                        help="Git repository providing the base objects (default: --tree)")
    parser.add_argument("--committed", default=None, metavar="REV",
                        help="read the manifest and archives as committed blobs at REV instead of --tree")
    args = parser.parse_args(argv)

    tree = os.path.abspath(args.tree)
    git = Git(os.path.abspath(args.repo) if args.repo else tree)
    rep = Reporter()

    if args.committed is not None:
        head = git.resolve_commit(args.committed)
        if head is None:
            print(f"RECEIPT-ARCHIVES: ERROR --committed {args.committed!r} is not a commit", flush=True)
            return 3
        committed_tree = dict(git.tree_blobs(head, COMMANDS_ROOT))
        committed_tree.update(git.tree_blobs(head, MANIFEST_REL))
        source = f"commit {head}"

        def read_source(rel):
            oid = committed_tree.get(rel)
            return None if oid is None else git.blob_bytes(oid)

        def source_exists(rel):
            return rel in committed_tree

        def source_commands_files():
            return sorted(p for p in committed_tree if p.startswith(COMMANDS_ROOT))
    else:
        if not os.path.isdir(tree):
            print(f"RECEIPT-ARCHIVES: ERROR --tree {tree!r} is not a directory", flush=True)
            return 3
        source = f"tree {tree}"

        def read_source(rel):
            full = os.path.join(tree, *rel.split("/"))
            if not os.path.isfile(full):
                return None
            with open(full, "rb") as handle:
                return handle.read()

        def source_exists(rel):
            return os.path.lexists(os.path.join(tree, *rel.split("/")))

        def source_commands_files():
            root = os.path.join(tree, *COMMANDS_ROOT.rstrip("/").split("/"))
            found = []
            for directory, _dirs, files in os.walk(root):
                for name in files:
                    rel = os.path.relpath(os.path.join(directory, name), tree)
                    found.append(rel.replace(os.sep, "/"))
            return sorted(found)

    print(f"RECEIPT-ARCHIVES: source {source}", flush=True)
    manifest_bytes = read_source(MANIFEST_REL)
    if manifest_bytes is None:
        rep.fail("manifest-missing", MANIFEST_REL)
        print("RECEIPT-ARCHIVES: RESULT: FAIL (1 failure)", flush=True)
        return 1
    try:
        manifest = json.loads(manifest_bytes.decode("utf-8"), object_pairs_hook=reject_duplicate_keys)
    except (UnicodeDecodeError, ValueError) as exc:
        rep.fail("manifest-schema", f"unreadable manifest: {exc}")
        print("RECEIPT-ARCHIVES: RESULT: FAIL (1 failure)", flush=True)
        return 1
    if not validate_manifest_shape(manifest, rep):
        print(f"RECEIPT-ARCHIVES: RESULT: FAIL ({len(rep.failures)} failures)", flush=True)
        return 1

    base = git.resolve_commit(manifest["baseCommit"])
    if base != manifest["baseCommit"]:
        rep.fail("base-commit-missing", f"{manifest['baseCommit']} is not a commit in {git.repo}")
        print(f"RECEIPT-ARCHIVES: RESULT: FAIL ({len(rep.failures)} failures)", flush=True)
        return 1

    # Recompute the required set from every blob under the commands root at base.
    base_blobs = git.tree_blobs(base, COMMANDS_ROOT)
    base_bytes = {}
    required = {}
    prefix_holders = set()
    for path in sorted(base_blobs):
        data = git.blob_bytes(base_blobs[path])
        base_bytes[path] = data
        lines = count_result_lines(data)
        if lines:
            required[path] = lines
        if PREFIX_GUARD in data:
            prefix_holders.add(path)
    if prefix_holders != set(required):
        rep.fail("selection-ambiguous",
                 f"prefix-bearing receipts without a result line: {sorted(prefix_holders - set(required))}")
    print(f"RECEIPT-ARCHIVES: base {base}: {len(base_blobs)} blobs under {COMMANDS_ROOT}, "
          f"{len(required)} contain claim-scanner result lines", flush=True)

    entries = manifest["archives"]
    by_original = collections.Counter(e["originalPath"] for e in entries)
    by_archive = collections.Counter(e["archivePath"] for e in entries)
    for path, count in sorted(by_original.items()):
        if count > 1:
            rep.fail("manifest-duplicate-entry", f"originalPath {path} appears {count} times")
    for path, count in sorted(by_archive.items()):
        if count > 1:
            rep.fail("manifest-duplicate-entry", f"archivePath {path} appears {count} times")
    for path in sorted(set(required) - set(by_original)):
        rep.fail("manifest-missing-entry", f"{path} has {required[path]} result lines at base but no manifest entry")
    for path in sorted(set(by_original) - set(required)):
        rep.fail("manifest-extra-entry", f"{path} is not a selected receipt at base")

    verified = 0
    checked = set()
    for entry in entries:
        original = entry["originalPath"]
        if original in checked:
            continue
        checked.add(original)
        entry_failures = len(rep.failures)
        archive_path = entry["archivePath"]
        if archive_path != original + ".gz":
            rep.fail("archive-path-mismatch", f"{archive_path} is not {original}.gz")
        oid = base_blobs.get(original)
        if oid is None:
            rep.fail("base-path-missing", f"{original} is not a blob at base")
            continue
        if entry["baseBlobId"] != oid:
            rep.fail("base-blob-id-mismatch", f"{original}: manifest {entry['baseBlobId']} != base {oid}")
        data = base_bytes[original]
        blob_sha = hashlib.sha256(data).hexdigest().upper()
        if entry["baseBlobSha256"] != blob_sha:
            rep.fail("base-blob-sha256-mismatch", f"{original}: manifest {entry['baseBlobSha256']} != {blob_sha}")
        if entry["baseBlobBytes"] != len(data):
            rep.fail("base-blob-bytes-mismatch", f"{original}: manifest {entry['baseBlobBytes']} != {len(data)}")
        if entry["claimScannerResultLines"] != required.get(original, 0):
            rep.fail("result-line-count-mismatch",
                     f"{original}: manifest {entry['claimScannerResultLines']} != {required.get(original, 0)}")
        referring = git.referring_files(base, original.rsplit("/", 1)[1])
        if entry["referringFilesAtBase"] != referring:
            rep.fail("referring-files-mismatch", f"{original}: manifest list != recomputed {referring}")
        if source_exists(original):
            rep.fail("original-present", f"{original} still exists in the {source.split(' ')[0]}")
        archive = read_source(archive_path)
        if archive is None:
            rep.fail("archive-missing", archive_path)
            continue
        archive_sha = hashlib.sha256(archive).hexdigest().upper()
        if entry["archiveBytes"] != len(archive):
            rep.fail("archive-bytes-mismatch", f"{archive_path}: manifest {entry['archiveBytes']} != {len(archive)}")
        if entry["archiveSha256"] != archive_sha:
            rep.fail("archive-sha256-mismatch", f"{archive_path}: manifest {entry['archiveSha256']} != {archive_sha}")
        try:
            recovered = decompress_single_member(archive)
        except (zlib.error, ValueError) as exc:
            rep.fail("archive-gzip-invalid", f"{archive_path}: {exc}")
            continue
        if entry["decompressedBytes"] != len(recovered):
            rep.fail("decompressed-length-mismatch",
                     f"{archive_path}: manifest {entry['decompressedBytes']} != {len(recovered)}")
        if recovered != data:
            rep.fail("decompressed-bytes-mismatch",
                     f"{archive_path}: recovered SHA-256 {hashlib.sha256(recovered).hexdigest().upper()} != base blob {blob_sha}")
        if len(rep.failures) == entry_failures:
            verified += 1
            rep.ok(f"{archive_path} -> {original} blob {oid} sha256 {blob_sha} bytes {len(data)} "
                   f"archive sha256 {archive_sha} bytes {len(archive)} result-lines {required[original]} "
                   f"referring-files {len(referring)}")

    manifest_archives = set(by_archive)
    base_archives = {p for p in base_blobs if p.endswith(".gz")}
    extras = [p for p in source_commands_files()
              if p.endswith(".gz") and p not in manifest_archives and p not in base_archives]
    for path in extras:
        rep.fail("archive-extra", f"{path} is under {COMMANDS_ROOT} but in neither the manifest nor the base tree")

    if rep.failures:
        print(f"RECEIPT-ARCHIVES: RESULT: FAIL ({len(rep.failures)} failures; "
              f"{verified} of {len(required)} required archives verified)", flush=True)
        return 1
    print(f"RECEIPT-ARCHIVES: RESULT: PASS ({verified} of {len(required)} required archives verified; "
          f"{len(entries)} manifest entries; 0 extra archives; base {base})", flush=True)
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main(sys.argv[1:]))
    except EnvironmentFailure as exc:
        print(f"RECEIPT-ARCHIVES: ERROR {exc}", flush=True)
        sys.exit(3)
