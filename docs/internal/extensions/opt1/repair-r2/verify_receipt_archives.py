#!/usr/bin/env python3
"""Verify the OPT-1-R2 receipt archives against the exact base Git blobs.

RECEIPT_ARCHIVES.json beside this file records, for every blob under
docs/internal/extensions/opt1/ at the pinned base commit that contains a
claim-scanner result line, the original path, its Git blob id, the SHA-256 and
length of the blob bytes, the archive path, the archive SHA-256 and length and
the decompressed length. It also records the files that refer to each original
name and the unselected files that mention scanner text without a result line.

Nothing in the manifest is trusted. Every value is recomputed from the archives
(in a directory tree, or as committed blobs with --committed) and from Git
objects of the base commit, and the selected set is recomputed from every base
blob under the history root. Missing, duplicate, extra and mismatching entries
are rejected, as is an original file present beside its archive.

Exit codes: 0 verified; 1 verification failure; 2 usage error;
3 environment error (Git unavailable, timeout, unreadable object).
Every failure prints one line `RECEIPT-ARCHIVES: FAIL [<code>] <detail>`.
Output never repeats scanner text, so this tool's own log is not a claim
surface.
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

SCHEMA = "rmq.opt1.repair-r2.receipt-archives.v1"
HANDLE = "OPT-1-R2"
BASE_COMMIT = "4cc95012a31cda9459d06d87b3371c8c172bb973"
MANIFEST_REL = "docs/internal/extensions/opt1/repair-r2/RECEIPT_ARCHIVES.json"
HISTORY_ROOT = "docs/internal/extensions/opt1/"
ATTRIBUTES_REL = HISTORY_ROOT + ".gitattributes"
ATTRIBUTES_HEADER = "# OPT-1-R2: exact gzip archives of receipts that embedded claim-scanner result lines."
# A claim-scanner result line is the scanner's emission shape: the prefix, then
# a rule bracket, a status bracket and a verdict bracket.
RESULT_LINE_REGEX = r"CLAIM-DRIFT\[[^\]\r\n]*\]\[[^\]\r\n]*\]\[[^\]\r\n]*\]"
RESULT_LINE = re.compile(RESULT_LINE_REGEX.encode("ascii"))
# The bare prefix, split so this source file does not contain it. Every prefix
# occurrence in a base blob must begin a full result-line match; otherwise the
# selection rule is ambiguous for that blob and verification fails.
PREFIX_GUARD = b"CLAIM-DRIFT" + b"["
# Scanner text that is not a result line: the scanner name or its summary.
SCANNER_TEXT_REGEX = r"CLAIM-DRIFT|scan complete \([0-9]+ hits"
SCANNER_TEXT = re.compile(SCANNER_TEXT_REGEX.encode("ascii"))
GZIP_HEADER = bytes.fromhex("1f8b08000000000002ff")
GIT_TIMEOUT_SECONDS = 300

TOP_KEYS = {"schema", "handle", "baseCommit", "selection", "encoding", "attributes",
            "referenceResolution", "archives", "scannerTextWithoutResultLinesAtBase"}
SELECTION_KEYS = {"historyRoot", "resultLineRegex", "prefixGuard", "scannerTextRegex", "rule"}
ENCODING_KEYS = {"container", "header", "writer", "recovery"}
ATTRIBUTE_KEYS = {"path", "appendedLines", "rule"}
ENTRY_KEYS = {"originalPath", "baseBlobId", "baseBlobMode", "baseBlobSha256", "baseBlobBytes",
              "claimScannerResultLines", "physicalLinesWithResultLines", "archivePath",
              "archiveSha256", "archiveBytes", "decompressedBytes", "referringFilesAtBase"}
HEX40 = re.compile(r"^[0-9a-f]{40}$")
HEX64 = re.compile(r"^[0-9A-F]{64}$")


class EnvironmentFailure(Exception):
    pass


class Git:
    def __init__(self, repo):
        self.repo = repo

    def run(self, args, stdin=None):
        try:
            return subprocess.run(["git", "-C", self.repo, "-c", "core.fsmonitor=false", *args],
                                  input=stdin, capture_output=True, timeout=GIT_TIMEOUT_SECONDS)
        except (OSError, subprocess.TimeoutExpired) as exc:
            raise EnvironmentFailure(f"git {' '.join(args[:2])}: {exc}")

    def checked(self, args, stdin=None):
        result = self.run(args, stdin)
        if result.returncode != 0:
            raise EnvironmentFailure(f"git {' '.join(args[:2])} exited {result.returncode}: "
                                     f"{result.stderr.decode('utf-8', 'replace').strip()}")
        return result.stdout

    def resolve_commit(self, rev):
        result = self.run(["rev-parse", "--verify", "--quiet", rev + "^{commit}"])
        if result.returncode != 0:
            return None
        return result.stdout.decode("ascii").strip()

    def tree(self, rev, prefix):
        """Map path -> (mode, kind, oid) for every entry under prefix at rev."""
        out = self.checked(["ls-tree", "-r", "-z", "--full-tree", rev, "--", prefix])
        entries = {}
        for record in out.split(b"\0"):
            if not record:
                continue
            meta, path = record.split(b"\t", 1)
            mode, kind, oid = meta.decode("ascii").split(" ")
            entries[path.decode("utf-8")] = (mode, kind, oid)
        return entries

    def blobs(self, oids):
        """Read blobs through one bounded cat-file batch; recompute each object id."""
        unique = sorted(set(oids))
        if not unique:
            return {}
        out = self.checked(["cat-file", "--batch"], stdin=("\n".join(unique) + "\n").encode("ascii"))
        result, offset = {}, 0
        for oid in unique:
            end = out.index(b"\n", offset)
            header = out[offset:end].decode("ascii").split(" ")
            if len(header) != 3 or header[0] != oid or header[1] != "blob":
                raise EnvironmentFailure(f"cat-file returned header {header!r} for {oid}")
            size = int(header[2])
            data = out[end + 1:end + 1 + size]
            if len(data) != size or out[end + 1 + size:end + 2 + size] != b"\n":
                raise EnvironmentFailure(f"cat-file returned a truncated object for {oid}")
            if git_blob_id(data) != oid:
                raise EnvironmentFailure(f"cat-file bytes do not hash to {oid}")
            result[oid] = data
            offset = end + 2 + size
        if offset != len(out):
            raise EnvironmentFailure("cat-file returned trailing bytes")
        return result

    def referring_files(self, rev, name):
        pattern = "(?<![A-Za-z0-9_.-])" + re.escape(name) + "(?![A-Za-z0-9_-])"
        result = self.run(["grep", "-l", "-z", "-P", "-e", pattern, rev, "--"])
        if result.returncode not in (0, 1):
            raise EnvironmentFailure(f"git grep exited {result.returncode}: "
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

    def check_attr(self, rev, path):
        out = self.checked(["check-attr", "--source", rev, "-z", "text", "diff", "merge", "--", path])
        fields = out.split(b"\0")
        values = {}
        for index in range(0, len(fields) - 2, 3):
            values[fields[index + 1].decode("ascii")] = fields[index + 2].decode("ascii")
        return values


class Reporter:
    def __init__(self):
        self.failures = []

    def fail(self, code, detail):
        self.failures.append(code)
        print(f"RECEIPT-ARCHIVES: FAIL [{code}] {detail}", flush=True)

    def ok(self, detail):
        print(f"RECEIPT-ARCHIVES: ok {detail}", flush=True)


def git_blob_id(data):
    return hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()


def sha256(data):
    return hashlib.sha256(data).hexdigest().upper()


def reject_duplicate_keys(pairs):
    seen = {}
    for key, value in pairs:
        if key in seen:
            raise ValueError(f"duplicate JSON key {key!r}")
        seen[key] = value
    return seen


def safe_relative(path):
    return (isinstance(path, str) and bool(path) and not path.startswith("/")
            and "\\" not in path and ":" not in path
            and all(part not in ("", ".", "..") for part in path.split("/")))


def is_count(value):
    return isinstance(value, int) and not isinstance(value, bool) and value >= 0


def expected_attribute_lines(archive_paths):
    return [ATTRIBUTES_HEADER] + ["/" + path[len(HISTORY_ROOT):] + " binary" for path in sorted(archive_paths)]


def validate_manifest_shape(manifest, rep):
    before = len(rep.failures)
    if not isinstance(manifest, dict) or set(manifest) != TOP_KEYS:
        keys = sorted(manifest) if isinstance(manifest, dict) else type(manifest).__name__
        rep.fail("manifest-schema", f"top-level keys {keys} != {sorted(TOP_KEYS)}")
        return False
    if manifest["schema"] != SCHEMA:
        rep.fail("manifest-schema", f"schema {manifest['schema']!r} != {SCHEMA!r}")
    if manifest["handle"] != HANDLE:
        rep.fail("manifest-schema", f"handle {manifest['handle']!r} != {HANDLE!r}")
    if manifest["baseCommit"] != BASE_COMMIT:
        rep.fail("manifest-base-commit", f"baseCommit {manifest['baseCommit']!r} != pinned {BASE_COMMIT}")
    selection = manifest["selection"]
    if not isinstance(selection, dict) or set(selection) != SELECTION_KEYS:
        rep.fail("manifest-schema", "selection keys differ from the pinned set")
    else:
        pinned = {"historyRoot": HISTORY_ROOT, "resultLineRegex": RESULT_LINE_REGEX,
                  "prefixGuard": PREFIX_GUARD.decode("ascii"), "scannerTextRegex": SCANNER_TEXT_REGEX}
        for key, value in pinned.items():
            if selection[key] != value:
                rep.fail("manifest-schema", f"selection.{key} differs from the pinned value")
        if not isinstance(selection["rule"], str) or not selection["rule"]:
            rep.fail("manifest-schema", "selection.rule is empty")
    encoding = manifest["encoding"]
    if not isinstance(encoding, dict) or set(encoding) != ENCODING_KEYS:
        rep.fail("manifest-schema", "encoding keys differ from the pinned set")
    elif encoding["header"] != GZIP_HEADER.hex():
        rep.fail("manifest-schema", "encoding.header differs from the pinned gzip header")
    attributes = manifest["attributes"]
    if not isinstance(attributes, dict) or set(attributes) != ATTRIBUTE_KEYS:
        rep.fail("manifest-schema", "attributes keys differ from the pinned set")
    elif attributes["path"] != ATTRIBUTES_REL or not isinstance(attributes["appendedLines"], list):
        rep.fail("manifest-schema", "attributes.path or attributes.appendedLines is not the pinned shape")
    if not isinstance(manifest["referenceResolution"], str) or not manifest["referenceResolution"]:
        rep.fail("manifest-schema", "referenceResolution is empty")
    unselected = manifest["scannerTextWithoutResultLinesAtBase"]
    if not isinstance(unselected, list) or not all(isinstance(p, str) for p in unselected):
        rep.fail("manifest-schema", "scannerTextWithoutResultLinesAtBase is not a list of paths")
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
            if not safe_relative(entry[key]) or not entry[key].startswith(HISTORY_ROOT):
                rep.fail("manifest-schema", f"archives[{index}].{key} is not a safe path under {HISTORY_ROOT}")
        if not isinstance(entry["baseBlobId"], str) or not HEX40.match(entry["baseBlobId"]):
            rep.fail("manifest-schema", f"archives[{index}].baseBlobId is not a 40-hex id")
        if entry["baseBlobMode"] not in ("100644", "100755"):
            rep.fail("manifest-schema", f"archives[{index}].baseBlobMode is not a regular-file mode")
        for key in ("baseBlobSha256", "archiveSha256"):
            if not isinstance(entry[key], str) or not HEX64.match(entry[key]):
                rep.fail("manifest-schema", f"archives[{index}].{key} is not uppercase SHA-256 hex")
        for key in ("baseBlobBytes", "claimScannerResultLines", "physicalLinesWithResultLines",
                    "archiveBytes", "decompressedBytes"):
            if not is_count(entry[key]):
                rep.fail("manifest-schema", f"archives[{index}].{key} is not a nonnegative integer")
        refs = entry["referringFilesAtBase"]
        if not isinstance(refs, list) or not all(isinstance(r, str) for r in refs):
            rep.fail("manifest-schema", f"archives[{index}].referringFilesAtBase is not a list of paths")
    return len(rep.failures) == before


def decompress_single_member(data):
    if data[:10] != GZIP_HEADER:
        raise ValueError(f"header {data[:10].hex()} != pinned {GZIP_HEADER.hex()}")
    decoder = zlib.decompressobj(wbits=31)  # gzip wrapper: CRC-32 and ISIZE are checked
    out = decoder.decompress(data) + decoder.flush()
    if not decoder.eof:
        raise ValueError("truncated gzip member")
    if decoder.unused_data:
        raise ValueError(f"{len(decoder.unused_data)} bytes after the first gzip member")
    return out


def result_line_counts(data):
    return (len(RESULT_LINE.findall(data)),
            sum(1 for line in data.split(b"\n") if RESULT_LINE.search(line)))


def unguarded_prefix(data):
    starts = {match.start() for match in RESULT_LINE.finditer(data)}
    index = data.find(PREFIX_GUARD)
    while index >= 0:
        if index not in starts:
            return True
        index = data.find(PREFIX_GUARD, index + 1)
    return False


def main(argv):
    script_root = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), *([os.pardir] * 5)))
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--tree", default=script_root,
                        help="directory tree holding the manifest and archives (default: this repository)")
    parser.add_argument("--repo", default=None, help="Git repository providing the base objects (default: --tree)")
    parser.add_argument("--committed", default=None, metavar="REV",
                        help="read the manifest, archives and attributes as committed blobs at REV")
    parser.add_argument("--result-json", default=None, help="also write the failure codes and counts as JSON here")
    args = parser.parse_args(argv)

    tree = os.path.abspath(args.tree)
    git = Git(os.path.abspath(args.repo) if args.repo else tree)
    rep = Reporter()
    summary = {"schema": SCHEMA + ".result", "mode": "committed" if args.committed else "tree",
               "source": None, "baseCommit": BASE_COMMIT}

    def finish(code, message):
        print(f"RECEIPT-ARCHIVES: RESULT: {message}", flush=True)
        if args.result_json:
            summary.update({"exit": code, "failureCodes": sorted(set(rep.failures)),
                            "failureCount": len(rep.failures), "result": message})
            with open(args.result_json, "w", encoding="utf-8") as handle:
                json.dump(summary, handle, indent=2)
                handle.write("\n")
        return code

    candidate_tree = None
    if args.committed is not None:
        head = git.resolve_commit(args.committed)
        if head is None:
            print(f"RECEIPT-ARCHIVES: ERROR --committed {args.committed!r} is not a commit", flush=True)
            return 3
        candidate_tree = git.tree(head, HISTORY_ROOT)
        source = f"commit {head}"

        def read_source(rel):
            entry = candidate_tree.get(rel)
            if entry is None or entry[1] != "blob":
                return None
            return git.blobs([entry[2]])[entry[2]]

        def source_exists(rel):
            return rel in candidate_tree

        def source_files():
            return sorted(p for p, e in candidate_tree.items() if e[1] == "blob")
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

        def source_files():
            root = os.path.join(tree, *HISTORY_ROOT.rstrip("/").split("/"))
            found = []
            for directory, _dirs, files in os.walk(root):
                for name in files:
                    found.append(os.path.relpath(os.path.join(directory, name), tree).replace(os.sep, "/"))
            return sorted(found)

    summary["source"] = source
    print(f"RECEIPT-ARCHIVES: source {source}", flush=True)
    manifest_bytes = read_source(MANIFEST_REL)
    if manifest_bytes is None:
        rep.fail("manifest-missing", MANIFEST_REL)
        return finish(1, "FAIL (1 failure)")
    try:
        manifest = json.loads(manifest_bytes.decode("utf-8"), object_pairs_hook=reject_duplicate_keys)
    except (UnicodeDecodeError, ValueError) as exc:
        rep.fail("manifest-schema", f"unreadable manifest: {exc}")
        return finish(1, "FAIL (1 failure)")
    if not validate_manifest_shape(manifest, rep):
        return finish(1, f"FAIL ({len(rep.failures)} failures)")

    base = git.resolve_commit(BASE_COMMIT)
    if base != BASE_COMMIT:
        rep.fail("base-commit-missing", f"{BASE_COMMIT} is not a commit in {git.repo}")
        return finish(1, f"FAIL ({len(rep.failures)} failures)")

    # Recompute the selection from every base blob under the history root.
    base_tree = git.tree(base, HISTORY_ROOT)
    base_blob_paths = sorted(p for p, e in base_tree.items() if e[1] == "blob")
    base_objects = git.blobs([base_tree[p][2] for p in base_blob_paths])
    required, unselected, ambiguous = {}, [], []
    for path in base_blob_paths:
        data = base_objects[base_tree[path][2]]
        occurrences, physical = result_line_counts(data)
        if occurrences:
            required[path] = (occurrences, physical)
        elif SCANNER_TEXT.search(data):
            unselected.append(path)
        if unguarded_prefix(data):
            ambiguous.append(path)
    for path in ambiguous:
        rep.fail("selection-ambiguous", f"{path} holds the scanner prefix outside a full result line")
    print(f"RECEIPT-ARCHIVES: base {base}: {len(base_blob_paths)} blobs under {HISTORY_ROOT}; "
          f"{len(required)} contain claim-scanner result lines; "
          f"{len(unselected)} mention scanner text without a result line", flush=True)
    summary.update({"baseBlobs": len(base_blob_paths), "requiredArchives": len(required),
                    "unselectedScannerTextFiles": len(unselected)})

    if manifest["scannerTextWithoutResultLinesAtBase"] != unselected:
        rep.fail("unselected-list-mismatch", f"manifest list != recomputed {unselected}")
    for path in unselected:
        if not source_exists(path):
            rep.fail("unselected-file-missing", f"{path} mentions scanner text without a result line and must stay")
        elif candidate_tree is not None and candidate_tree[path] != base_tree[path]:
            rep.fail("unselected-file-changed", f"{path} {candidate_tree[path]} != base {base_tree[path]}")

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
        rep.fail("manifest-missing-entry", f"{path} has {required[path][0]} result lines at base but no manifest entry")
    for path in sorted(set(by_original) - set(required)):
        rep.fail("manifest-extra-entry", f"{path} is not a selected receipt at base")
    listed_order = [e["originalPath"] for e in entries]
    if listed_order != sorted(listed_order):
        rep.fail("manifest-order", "archives are not sorted by originalPath")

    verified, checked = 0, set()
    for entry in entries:
        original = entry["originalPath"]
        if original in checked:
            continue
        checked.add(original)
        entry_failures = len(rep.failures)
        archive_path = entry["archivePath"]
        if archive_path != original + ".gz":
            rep.fail("archive-path-mismatch", f"{archive_path} is not {original}.gz")
        base_entry = base_tree.get(original)
        if base_entry is None or base_entry[1] != "blob":
            rep.fail("base-path-missing", f"{original} is not a blob at base")
            continue
        mode, _kind, oid = base_entry
        if entry["baseBlobId"] != oid:
            rep.fail("base-blob-id-mismatch", f"{original}: manifest {entry['baseBlobId']} != base {oid}")
        if entry["baseBlobMode"] != mode:
            rep.fail("base-blob-mode-mismatch", f"{original}: manifest {entry['baseBlobMode']} != base {mode}")
        data = base_objects[oid]
        blob_sha = sha256(data)
        if entry["baseBlobSha256"] != blob_sha:
            rep.fail("base-blob-sha256-mismatch", f"{original}: manifest {entry['baseBlobSha256']} != {blob_sha}")
        if entry["baseBlobBytes"] != len(data):
            rep.fail("base-blob-bytes-mismatch", f"{original}: manifest {entry['baseBlobBytes']} != {len(data)}")
        occurrences, physical = required.get(original, (0, 0))
        if entry["claimScannerResultLines"] != occurrences or entry["physicalLinesWithResultLines"] != physical:
            rep.fail("result-line-count-mismatch",
                     f"{original}: manifest {entry['claimScannerResultLines']}/{entry['physicalLinesWithResultLines']} "
                     f"!= recomputed {occurrences}/{physical}")
        referring = git.referring_files(base, original.rsplit("/", 1)[1])
        if entry["referringFilesAtBase"] != referring:
            rep.fail("referring-files-mismatch", f"{original}: manifest list != recomputed ({len(referring)} files)")
        if source_exists(original):
            rep.fail("original-present", f"{original} still exists in the {source.split(' ')[0]}")
        archive = read_source(archive_path)
        if archive is None:
            rep.fail("archive-missing", archive_path)
            continue
        if candidate_tree is not None and candidate_tree[archive_path][0] != mode:
            rep.fail("archive-mode-mismatch", f"{archive_path}: mode {candidate_tree[archive_path][0]} != {mode}")
        archive_sha = sha256(archive)
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
        if recovered != data or git_blob_id(recovered) != oid:
            rep.fail("decompressed-bytes-mismatch",
                     f"{archive_path}: recovered blob {git_blob_id(recovered)} sha256 {sha256(recovered)} "
                     f"!= base blob {oid} sha256 {blob_sha}")
        if len(rep.failures) == entry_failures:
            verified += 1
            rep.ok(f"{archive_path} -> {original} blob {oid} sha256 {blob_sha} bytes {len(data)} "
                   f"archive sha256 {archive_sha} bytes {len(archive)} result-lines {occurrences} "
                   f"physical-lines {physical} referring-files {len(referring)}")

    # Archives and result-line text that the manifest does not account for.
    listed_archives = set(by_archive)
    base_paths = set(base_tree)
    for path in source_files():
        if path.endswith(".gz") and path not in listed_archives and path not in base_paths:
            rep.fail("archive-extra", f"{path} is under {HISTORY_ROOT} but in neither the manifest nor the base tree")
        elif (path not in base_paths and path not in listed_archives and path != MANIFEST_REL):
            data = read_source(path)
            if data is not None and RESULT_LINE.search(data):
                rep.fail("new-result-line-file", f"{path} is new since base and contains a claim-scanner result line")

    expected_lines = expected_attribute_lines(listed_archives)
    if manifest["attributes"]["appendedLines"] != expected_lines:
        rep.fail("attributes-manifest-mismatch", "attributes.appendedLines differs from the lines implied by the archives")
    if candidate_tree is not None:
        base_attributes = base_objects[base_tree[ATTRIBUTES_REL][2]]
        current = read_source(ATTRIBUTES_REL)
        suffix = ("\n".join(expected_lines) + "\n").encode("utf-8")
        if current != base_attributes + suffix:
            rep.fail("attributes-not-append-only",
                     f"{ATTRIBUTES_REL} is not the base blob followed by exactly the {len(expected_lines)} expected lines")
        for path in sorted(listed_archives):
            values = git.check_attr(head, path)
            if values != {"text": "unset", "diff": "unset", "merge": "unset"}:
                rep.fail("attributes-not-binary", f"{path}: check-attr at {head} gives {values}")
        summary["attributesChecked"] = "exact committed bytes and check-attr --source"
    else:
        summary["attributesChecked"] = "not in tree mode (checkout conversion); use --committed"

    summary.update({"verifiedArchives": verified, "manifestEntries": len(entries)})
    if rep.failures:
        return finish(1, f"FAIL ({len(rep.failures)} failures; {verified} of {len(required)} required archives verified)")
    return finish(0, f"PASS ({verified} of {len(required)} required archives verified; {len(entries)} manifest "
                     f"entries; 0 extra archives; {len(unselected)} unselected scanner-text files present; base {base})")


if __name__ == "__main__":
    try:
        sys.exit(main(sys.argv[1:]))
    except EnvironmentFailure as exc:
        print(f"RECEIPT-ARCHIVES: ERROR {exc}", flush=True)
        sys.exit(3)
