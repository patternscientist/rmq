#!/usr/bin/env python3
"""Verify the PRE-1-R1 rewording of lane Markdown lines against exact base Git blobs.

REWORDS.json beside this file records every line of lane-authored Markdown
under docs/internal/extensions/pre1/ whose base line matches the claim
scanner's summary pattern, with the base blob id, the SHA-256 of the exact base
and new line bytes, and the ordered integers of each.

Nothing in the manifest is trusted. From Git objects of the pinned base commit
the verifier recomputes the set of pattern lines of every Markdown blob under
the root and requires it to equal the manifest set (missing, extra and
duplicate entries fail). For every recorded line it checks the base line hash
and integers against the base blob. For every recorded file it requires the
tip bytes (a directory tree, or committed blobs with --committed) to equal the
base bytes with only the recorded lines replaced, followed by an optional tail
after the last base line, with each new line hashing to its recorded value and
carrying the same ordered integers and digit runs as its base line. Finally no
line of any non-archive file under the root may match the pattern, and with
--committed no changed text path in base..REV may gain a pattern line.

Tree mode compares exact bytes. A checkout converted by core.autocrlf is not the
committed text, so verify a checkout with --committed, or verify an exact export
(repair_control_helper.py export) in tree mode.

Exit codes: 0 verified; 1 verification failure; 2 usage error;
3 environment error (Git unavailable, timeout, unreadable object).
Every failure prints one line `REWORDS: FAIL [<code>] <detail>`. Output never
repeats a base line or scanner text, so this tool's own log is not a claim
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

SCHEMA = "rmq.pre1.repair-r1.rewords.v1"
HANDLE = "PRE-1-R1"
BASE_COMMIT = "84ae12f6f6bad99fd3215c5bdd5b2a93e3779897"
MANIFEST_REL = "docs/internal/extensions/pre1/repair-r1/REWORDS.json"
ROOT = "docs/internal/extensions/pre1/"
# The scanner summary pattern (the self-test's hit-count regex, which PowerShell
# -match applies without regard to case). Python's Unicode IGNORECASE folding
# is at least as broad as that match.
PATTERN_REGEX = r"scan complete \([0-9]+ hits"
PATTERN = re.compile(PATTERN_REGEX, re.IGNORECASE)
INTEGER_REGEX = r"[0-9]+"
INTEGER = re.compile(INTEGER_REGEX)
BINARY_SUFFIXES = (".gz", ".zip")
GIT_TIMEOUT_SECONDS = 300

TOP_KEYS = {"schema", "handle", "baseCommit", "selection", "tailRule", "files", "rewords"}
SELECTION_KEYS = {"root", "fileRule", "patternRegex", "patternFlags", "integerRegex", "lineRule"}
FILE_KEYS = {"path", "baseBlobId", "baseBlobSha256", "baseBlobBytes", "baseLines", "baseEndsWithLineFeed"}
ENTRY_KEYS = {"path", "baseLineNumber", "baseBlobId", "baseLineSha256", "newLineSha256", "baseIntegers", "newIntegers"}
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
        out = self.checked(["ls-tree", "-r", "-z", "--full-tree", rev, "--", prefix])
        entries = {}
        for record in out.split(b"\0"):
            if not record:
                continue
            meta, path = record.split(b"\t", 1)
            mode, kind, oid = meta.decode("ascii").split(" ")
            entries[path.decode("utf-8")] = (mode, kind, oid)
        return entries

    def blob(self, oid):
        data = self.checked(["cat-file", "blob", oid])
        if hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest() != oid:
            raise EnvironmentFailure(f"cat-file bytes do not hash to {oid}")
        return data

    def changed_paths(self, base, head):
        out = self.checked(["diff", "--no-renames", "--name-only", "-z", base, head, "--"])
        return sorted(p.decode("utf-8") for p in out.split(b"\0") if p)

    def blob_at(self, rev, path):
        result = self.run(["rev-parse", "--verify", "--quiet", f"{rev}:{path}"])
        if result.returncode != 0:
            return None
        return self.blob(result.stdout.decode("ascii").strip())


class Reporter:
    def __init__(self):
        self.failures = []

    def fail(self, code, detail):
        self.failures.append(code)
        print(f"REWORDS: FAIL [{code}] {detail}", flush=True)

    def ok(self, detail):
        print(f"REWORDS: ok {detail}", flush=True)


def sha256(data):
    return hashlib.sha256(data).hexdigest().upper()


def reject_duplicate_keys(pairs):
    seen = {}
    for key, value in pairs:
        if key in seen:
            raise ValueError(f"duplicate JSON key {key!r}")
        seen[key] = value
    return seen


def is_count(value):
    return isinstance(value, int) and not isinstance(value, bool) and value >= 0


def integers(line):
    return [int(run) for run in INTEGER.findall(line.decode("utf-8", "replace"))]


def digit_runs(line):
    return INTEGER.findall(line.decode("utf-8", "replace"))


def matches_pattern(line):
    try:
        text = line.decode("utf-8")
    except UnicodeDecodeError:
        text = line.decode("utf-8", "replace")
    return PATTERN.search(text) is not None


def split_lines(data):
    """Lines split on LF; a trailing LF yields no extra line. Returns (lines, ends_with_lf)."""
    parts = data.split(b"\n")
    if data.endswith(b"\n"):
        return parts[:-1], True
    return parts, False


def validate_shape(manifest, rep):
    before = len(rep.failures)
    if not isinstance(manifest, dict) or set(manifest) != TOP_KEYS:
        rep.fail("manifest-schema", "top-level keys differ from the pinned set")
        return False
    if manifest["schema"] != SCHEMA or manifest["handle"] != HANDLE:
        rep.fail("manifest-schema", "schema or handle differs from the pinned value")
    if manifest["baseCommit"] != BASE_COMMIT:
        rep.fail("manifest-base-commit", f"baseCommit {manifest['baseCommit']!r} != pinned {BASE_COMMIT}")
    selection = manifest["selection"]
    if not isinstance(selection, dict) or set(selection) != SELECTION_KEYS:
        rep.fail("manifest-schema", "selection keys differ from the pinned set")
    elif (selection["root"] != ROOT or selection["patternRegex"] != PATTERN_REGEX
          or selection["integerRegex"] != INTEGER_REGEX or selection["patternFlags"] != "IGNORECASE"):
        rep.fail("manifest-schema", "selection root, pattern, flags or integer regex differs from the pinned value")
    if not isinstance(manifest["tailRule"], str) or not manifest["tailRule"]:
        rep.fail("manifest-schema", "tailRule is empty")
    if not isinstance(manifest["files"], list) or not isinstance(manifest["rewords"], list) or not manifest["rewords"]:
        rep.fail("manifest-schema", "files is not a list or rewords is not a nonempty list")
        return False
    for index, entry in enumerate(manifest["files"]):
        if (not isinstance(entry, dict) or set(entry) != FILE_KEYS or not isinstance(entry["path"], str)
                or not isinstance(entry["baseBlobId"], str) or not HEX40.match(entry["baseBlobId"])
                or not isinstance(entry["baseBlobSha256"], str) or not HEX64.match(entry["baseBlobSha256"])
                or not is_count(entry["baseBlobBytes"]) or not is_count(entry["baseLines"])
                or not isinstance(entry["baseEndsWithLineFeed"], bool)):
            rep.fail("manifest-schema", f"files[{index}] is not the pinned file record shape")
    for index, entry in enumerate(manifest["rewords"]):
        if (not isinstance(entry, dict) or set(entry) != ENTRY_KEYS or not isinstance(entry["path"], str)
                or not is_count(entry["baseLineNumber"]) or entry["baseLineNumber"] < 1
                or not isinstance(entry["baseBlobId"], str) or not HEX40.match(entry["baseBlobId"])
                or not all(isinstance(entry[k], str) and HEX64.match(entry[k]) for k in ("baseLineSha256", "newLineSha256"))
                or not all(isinstance(entry[k], list) and all(is_count(v) for v in entry[k])
                           for k in ("baseIntegers", "newIntegers"))):
            rep.fail("manifest-schema", f"rewords[{index}] is not the pinned entry shape")
    return len(rep.failures) == before


def main(argv):
    script_root = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), *([os.pardir] * 5)))
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--tree", default=script_root, help="directory tree holding the manifest and tip files")
    parser.add_argument("--repo", default=None, help="Git repository providing the base objects (default: --tree)")
    parser.add_argument("--committed", default=None, metavar="REV", help="read the manifest and tip files as blobs at REV")
    parser.add_argument("--result-json", default=None, help="also write the failure codes and counts as JSON here")
    args = parser.parse_args(argv)

    tree = os.path.abspath(args.tree)
    git = Git(os.path.abspath(args.repo) if args.repo else tree)
    rep = Reporter()
    summary = {"schema": SCHEMA + ".result", "mode": "committed" if args.committed else "tree", "baseCommit": BASE_COMMIT}

    def finish(code, message):
        print(f"REWORDS: RESULT: {message}", flush=True)
        if args.result_json:
            summary.update({"exit": code, "failureCodes": sorted(set(rep.failures)),
                            "failureCount": len(rep.failures), "result": message})
            with open(args.result_json, "w", encoding="utf-8", newline="\n") as handle:
                json.dump(summary, handle, indent=2)
                handle.write("\n")
        return code

    head = None
    if args.committed is not None:
        head = git.resolve_commit(args.committed)
        if head is None:
            print(f"REWORDS: ERROR --committed {args.committed!r} is not a commit", flush=True)
            return 3
        head_tree = git.tree(head, ROOT)
        source = f"commit {head}"

        def read_source(rel):
            entry = head_tree.get(rel)
            return None if entry is None or entry[1] != "blob" else git.blob(entry[2])

        def source_files():
            return sorted(p for p, e in head_tree.items() if e[1] == "blob")
    else:
        if not os.path.isdir(tree):
            print(f"REWORDS: ERROR --tree {tree!r} is not a directory", flush=True)
            return 3
        source = f"tree {tree}"

        def read_source(rel):
            full = os.path.join(tree, *rel.split("/"))
            if not os.path.isfile(full):
                return None
            with open(full, "rb") as handle:
                return handle.read()

        def source_files():
            root = os.path.join(tree, *ROOT.rstrip("/").split("/"))
            found = []
            for directory, _dirs, files in os.walk(root):
                for name in files:
                    found.append(os.path.relpath(os.path.join(directory, name), tree).replace(os.sep, "/"))
            return sorted(found)

    summary["source"] = source
    print(f"REWORDS: source {source}", flush=True)
    manifest_bytes = read_source(MANIFEST_REL)
    if manifest_bytes is None:
        rep.fail("manifest-missing", MANIFEST_REL)
        return finish(1, "FAIL (1 failure)")
    try:
        manifest = json.loads(manifest_bytes.decode("utf-8"), object_pairs_hook=reject_duplicate_keys)
    except (UnicodeDecodeError, ValueError) as exc:
        rep.fail("manifest-schema", f"unreadable manifest: {exc}")
        return finish(1, "FAIL (1 failure)")
    if not validate_shape(manifest, rep):
        return finish(1, f"FAIL ({len(rep.failures)} failures)")

    base = git.resolve_commit(BASE_COMMIT)
    if base != BASE_COMMIT:
        rep.fail("base-commit-missing", f"{BASE_COMMIT} is not a commit in {git.repo}")
        return finish(1, f"FAIL ({len(rep.failures)} failures)")

    # Recompute the pattern-line selection over every Markdown blob under the root.
    base_tree = git.tree(base, ROOT)
    markdown = sorted(p for p, e in base_tree.items() if e[1] == "blob" and p.endswith(".md"))
    base_data, required = {}, set()
    for path in markdown:
        data = git.blob(base_tree[path][2])
        base_data[path] = data
        lines, _ = split_lines(data)
        for number, line in enumerate(lines, start=1):
            if matches_pattern(line):
                required.add((path, number))
    print(f"REWORDS: base {base}: {len(markdown)} Markdown blobs under {ROOT}; {len(required)} pattern lines in "
          f"{len({p for p, _ in required})} files", flush=True)
    summary.update({"baseMarkdownBlobs": len(markdown), "requiredRewords": len(required)})

    entries = manifest["rewords"]
    keyed = collections.Counter((e["path"], e["baseLineNumber"]) for e in entries)
    for key, count in sorted(keyed.items()):
        if count > 1:
            rep.fail("reword-duplicate-entry", f"{key[0]}:{key[1]} appears {count} times")
    for path, number in sorted(required - set(keyed)):
        rep.fail("reword-missing-entry", f"{path}:{number} matches the pattern at base but has no manifest entry")
    for path, number in sorted(set(keyed) - required):
        rep.fail("reword-extra-entry", f"{path}:{number} is not a pattern line at base")
    order = [(e["path"], e["baseLineNumber"]) for e in entries]
    if order != sorted(order):
        rep.fail("manifest-order", "rewords are not sorted by path and base line")

    recorded = collections.defaultdict(dict)
    for entry in entries:
        recorded[entry["path"]].setdefault(entry["baseLineNumber"], entry)
    managed = sorted({p for p, _ in required} | set(recorded))
    file_records = {f["path"]: f for f in manifest["files"] if isinstance(f, dict)}
    if sorted(file_records) != managed or len(manifest["files"]) != len(file_records):
        rep.fail("files-entry-mismatch", f"files list {sorted(file_records)} != recorded paths {managed}")

    verified = 0
    for path in managed:
        before = len(rep.failures)
        base_entry = base_tree.get(path)
        if base_entry is None or path not in base_data:
            rep.fail("base-path-missing", f"{path} is not a Markdown blob under the root at base")
            continue
        data = base_data[path]
        base_lines, ends_lf = split_lines(data)
        record = file_records.get(path)
        if record is not None and (record["baseBlobId"] != base_entry[2] or record["baseBlobSha256"] != sha256(data)
                                   or record["baseBlobBytes"] != len(data) or record["baseLines"] != len(base_lines)
                                   or record["baseEndsWithLineFeed"] != ends_lf):
            rep.fail("files-entry-mismatch", f"{path}: file record differs from the base blob")
        if not ends_lf:
            rep.fail("base-shape", f"{path}: base blob does not end with a line feed")
        for number, entry in sorted(recorded.get(path, {}).items()):
            if entry["baseBlobId"] != base_entry[2]:
                rep.fail("base-blob-id-mismatch", f"{path}:{number}: manifest {entry['baseBlobId']} != base {base_entry[2]}")
            if number > len(base_lines):
                rep.fail("reword-extra-entry", f"{path}:{number} is beyond the base line count")
                continue
            base_line = base_lines[number - 1]
            if entry["baseLineSha256"] != sha256(base_line):
                rep.fail("base-line-hash-mismatch", f"{path}:{number}: manifest base line hash differs from the base blob")
            if entry["baseIntegers"] != integers(base_line):
                rep.fail("base-integers-mismatch", f"{path}:{number}: manifest base integers differ from the base line")
            if entry["newIntegers"] != entry["baseIntegers"]:
                rep.fail("integers-mismatch", f"{path}:{number}: manifest new integers differ from base integers")
        tip = read_source(path)
        if tip is None:
            rep.fail("tip-file-missing", f"{path} is absent in the {source.split(' ')[0]}")
            continue
        tip_parts = tip.split(b"\n")
        # Each of the first len(base_lines) tip lines must exist and end with a line feed.
        terminated = len(tip_parts) - 1
        changed_unrecorded = []
        for number in range(1, len(base_lines) + 1):
            tip_line = tip_parts[number - 1] if number <= terminated else None
            entry = recorded.get(path, {}).get(number)
            if entry is None:
                if tip_line != base_lines[number - 1]:
                    changed_unrecorded.append(number)
                continue
            if tip_line is None:
                rep.fail("new-line-hash-mismatch", f"{path}:{number}: the recorded line is missing at the tip")
                continue
            if sha256(tip_line) != entry["newLineSha256"]:
                rep.fail("new-line-hash-mismatch", f"{path}:{number}: tip line hash differs from the recorded new line")
            if integers(tip_line) != entry["newIntegers"]:
                rep.fail("new-integers-mismatch", f"{path}:{number}: tip line integers differ from the recorded new integers")
            if digit_runs(tip_line) != digit_runs(base_lines[number - 1]):
                rep.fail("digit-runs-mismatch", f"{path}:{number}: tip line digit runs differ from the base line")
            if b"\r" in tip_line:
                rep.fail("new-line-shape", f"{path}:{number}: tip line holds a carriage return")
        if changed_unrecorded:
            shown = ", ".join(str(n) for n in changed_unrecorded[:5])
            rep.fail("unrecorded-line-changed",
                     f"{path}: {len(changed_unrecorded)} base line(s) outside the recorded set differ or are missing at the tip (first: {shown})")
        tail = b"\n".join(tip_parts[len(base_lines):]) if terminated >= len(base_lines) else b""
        if len(rep.failures) == before:
            verified += 1
            rep.ok(f"{path}: {len(recorded.get(path, {}))} recorded lines replaced; other {len(base_lines) - len(recorded.get(path, {}))} "
                   f"base lines identical; appended tail {len(tail)} bytes")

    # No pattern in any non-archive file under the root at the source.
    pattern_hits = []
    for path in source_files():
        if path.endswith(BINARY_SUFFIXES):
            continue
        data = read_source(path)
        if data is None:
            continue
        lines, _ = split_lines(data)
        for number, line in enumerate(lines, start=1):
            if matches_pattern(line):
                pattern_hits.append((path, number))
    for path, number in pattern_hits:
        rep.fail("pattern-present", f"{path}:{number} matches the summary pattern")
    added_checked = None
    if head is not None:
        # Every changed text path in the range: a pattern line at REV whose exact
        # bytes occur more often than at base (in the same path) is new text.
        added_checked = 0
        for path in git.changed_paths(base, head):
            head_blob = git.blob_at(head, path)
            if head_blob is None or path.endswith(BINARY_SUFFIXES) or b"\0" in head_blob:
                continue
            added_checked += 1
            base_blob = git.blob_at(base, path) or b""
            head_count = collections.Counter(l for l in split_lines(head_blob)[0] if matches_pattern(l))
            base_count = collections.Counter(l for l in split_lines(base_blob)[0] if matches_pattern(l))
            excess = sum((head_count - base_count).values())
            if excess:
                rep.fail("pattern-added", f"{path}: {excess} pattern line(s) at {head[:12]} are not present at base")
    summary.update({"verifiedFiles": verified, "managedFiles": len(managed), "manifestEntries": len(entries),
                    "patternLinesUnderRoot": len(pattern_hits), "addedLinesChecked": added_checked})
    if rep.failures:
        return finish(1, f"FAIL ({len(rep.failures)} failures; {verified} of {len(managed)} files verified)")
    return finish(0, f"PASS ({verified} of {len(managed)} files verified; {len(entries)} recorded lines; 0 pattern lines "
                     f"under the root" + (f"; {added_checked} changed text paths in the range checked" if head else "") +
                     f"; base {base})")


if __name__ == "__main__":
    try:
        sys.exit(main(sys.argv[1:]))
    except EnvironmentFailure as exc:
        print(f"REWORDS: ERROR {exc}", flush=True)
        sys.exit(3)
