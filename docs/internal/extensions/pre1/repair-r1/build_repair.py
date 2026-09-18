#!/usr/bin/env python3
"""Produce the PRE-1-R1 repair from exact base Git objects (producer, run once).

Reads only Git objects of the pinned base commit and writes, into the working
tree of --repo:
  * the gzip archive of the named audit report and of every base blob under
    docs/internal/extensions/pre1/ that holds a claim-scanner result line,
    removing each original file;
  * docs/internal/extensions/pre1/.gitattributes with one `binary` line per
    archive;
  * BUILDER_STAGE_LOG.md and REPORT.md equal to their base blobs with only the
    registered lines replaced (checked against each base line's SHA-256 and
    integer list), written with the working tree's CRLF convention so Git
    stores the exact LF bytes;
  * repair-r1/RECEIPT_ARCHIVES.json and repair-r1/REWORDS.json.

The verifiers do not trust this producer: verify_receipt_archives.py and
verify_rewords.py recompute every recorded value from Git objects. The
registered new lines below are stored in full, never as a substitution of the
base text, so this file does not contain the scanner summary text.
"""

import argparse
import collections
import gzip
import json
import os
import sys

sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import verify_receipt_archives as va  # noqa: E402
import verify_rewords as vr  # noqa: E402

# (path, base line number, SHA-256 of the exact base line bytes, full new line)
REWORDS = [
    ('docs/internal/extensions/pre1/BUILDER_STAGE_LOG.md', 427, 'B9041FFCF36D864B6FED35C600B712F69C973C4BF1D90674C7D6A8DC1C734BBE',
     "| C7-13 | `claim_drift_scan.ps1 -Strict`; `claim_drift_scan.ps1 -SelfTest` (mutex, one wrapper; output under `.lake/claim-scan/`) | 01:31:28 | 23.68 s (both) | 0; 1 | `-Strict`: completed with a summary of 1603 hits and 0 strict failures. `-SelfTest`: probes ok, record-path check ok, then `FAIL -- exclusion removed nothing (11 hits with records, 1603 without)`; rerun directly: same (exit 1) |"),
    ('docs/internal/extensions/pre1/BUILDER_STAGE_LOG.md', 428, '694E3291E8A86E06BE82C3D140AC0EE9BAA8A696069312C1A1175C7894741978',
     "| C7-14 | diagnosis of C7-13: `claim_drift_scan.ps1 -Strict -IncludeProcessRecords` directly; a temporary copy `scripts/claim_drift_scan_probe.ps1` whose hit-count regex is anchored at `^CLAIM-DRIFT: scan complete`, run with `-SelfTest`, then deleted | \u224801:33-01:36 | \u224820 s each | 0; 0 | the records run reports a summary of 2047 hits (rest elided) at its last line, but an earlier emitted hit (line 587) quotes `docs/internal/audit_reports/2026-09-12_PRE1_contract_fresh_blind.md:911`, whose text quotes a scanner summary of 11 hits and 0 strict failures; the self-test's `Get-ReportedHitCount` takes the first matching line anywhere, so it reads 11. With the anchored regex the self-test passes (`exclusion removed 444 hits (2047 -> 1603)`, `RESULT: PASS`). The report was copied unchanged into the repository at Stage 0 (`5f325dd`), as the continuation brief requires; `scripts/claim_drift_scan.ps1` is outside this lane's write scope, so the fix is left to the coordinator. The probe copy was removed and the worktree is clean |"),
    ('docs/internal/extensions/pre1/BUILDER_STAGE_LOG.md', 488, 'B431B175A7B3A7F3E82AD29A942D2FFEFCDEA715CB10C2655831F2B12B860DA6',
     "| R-11h | `claim_drift_scan.ps1 -Strict` (outer `timeout 1800`) | 06:17:01 | 8.29 s | 0 | completed with a summary of 1609 hits and 0 strict failures; against C7-13 the six added hits are review-level numeral matches in this lane's internal logs (`118`, `352`), none in the family or digestion entries |"),
    ('docs/internal/extensions/pre1/REPORT.md', 245, '02A65007166AFC4850EDE6E53CE365765288B4201FD12F7F27321428083D3EA4',
     "a scanner summary of 11 hits and 0 strict failures. The actual records"),
    ('docs/internal/extensions/pre1/REPORT.md', 246, '734A6A0B8DEF9E6A45C863FB94A2DEB40A2E377C836A1729CCFB73FEB83B76E5',
     "run ends with a summary of 2047 hits (rest elided). A temporary copy of the scanner"),
]

SELECTION_RULE = (
    "Result-line entries: every blob under historyRoot at baseCommit whose raw bytes contain a match of "
    "resultLineRegex; every prefixGuard occurrence must begin such a match. Named entries: the pinned originals, "
    "each the blob added unchanged by its addedByCommit. Blobs whose bytes match scannerTextRegex without a "
    "result line are listed and stay; zip containers whose compressed members hold result lines are listed and "
    "stay (the scanner does not read inside them).")
ENCODING = {
    "container": "single-member gzip, deflate level 9, mtime 0, no file name",
    "header": va.GZIP_HEADER.hex(),
    "writer": "Python gzip.compress(data, compresslevel=9, mtime=0)",
    "recovery": "gzip -dc <archivePath> > <originalPath>, or verify_receipt_archives.py, which compares the "
                "decompressed bytes with git cat-file of baseBlobId",
}
ATTRIBUTE_RULE = ("docs/internal/extensions/pre1/.gitattributes did not exist at baseCommit; it holds exactly one "
                  "'/<archive path relative to the lane root> binary' line per archive, sorted, and nothing else.")
REFERENCE_RULE = ("References to an original path or name elsewhere in the repository are not rewritten; this "
                  "manifest resolves each originalPath to its archivePath. referringFilesAtBase lists every file "
                  "at baseCommit whose text names the original file name.")
REWORD_SELECTION = {
    "root": vr.ROOT,
    "fileRule": "every blob under root at baseCommit whose path ends with .md (gzip and zip archives are not Markdown)",
    "patternRegex": vr.PATTERN_REGEX,
    "patternFlags": "IGNORECASE",
    "integerRegex": vr.INTEGER_REGEX,
    "lineRule": "lines are the blob bytes split on LF; a trailing LF ends the last line; SHA-256 values are of the "
                "exact line bytes without the LF",
}
TAIL_RULE = ("At the tip each recorded file equals its base blob with only the recorded lines replaced, followed by "
             "an optional tail after the last base line (the appended R1 section); neither the new lines nor the "
             "tail may match the pattern.")


def write_crlf(path, data):
    with open(path, "wb") as handle:
        handle.write(data.replace(b"\n", b"\r\n"))


def main(argv):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--repo", required=True)
    args = parser.parse_args(argv)
    repo = os.path.abspath(args.repo)
    git = va.Git(repo)
    base = git.resolve_commit(va.BASE_COMMIT)
    if base != va.BASE_COMMIT or vr.BASE_COMMIT != va.BASE_COMMIT:
        raise SystemExit("base commit mismatch")

    def full(rel):
        return os.path.join(repo, *rel.split("/"))

    # Archives.
    tree = git.tree(base, va.HISTORY_ROOT)
    for named in va.NAMED:
        tree.update(git.tree(base, named["originalPath"]))
    paths = sorted(p for p, e in tree.items() if e[1] == "blob")
    objects = git.blobs([tree[p][2] for p in paths])
    selected, unselected, containers = {}, [], []
    for path in paths:
        if not path.startswith(va.HISTORY_ROOT):
            continue
        data = objects[tree[path][2]]
        if va.unguarded_prefix(data):
            raise SystemExit(f"ambiguous selection in {path}")
        if va.RESULT_LINE.search(data):
            selected[path] = ("result-line", path + ".gz")
        elif va.SCANNER_TEXT.search(data):
            unselected.append(path)
        container = va.container_result_lines(path, data)
        if container is not None and container["memberResultLines"]:
            containers.append(container)
    for named in va.NAMED:
        selected[named["originalPath"]] = ("named", named["archivePath"])
    entries = []
    for original in sorted(selected):
        kind, archive_path = selected[original]
        mode, _k, oid = tree[original]
        data = objects[oid]
        archive = gzip.compress(data, compresslevel=9, mtime=0)
        if va.decompress_single_member(archive) != data:
            raise SystemExit(f"round trip failed for {original}")
        occurrences, physical = va.result_line_counts(data)
        os.makedirs(os.path.dirname(full(archive_path)), exist_ok=True)
        with open(full(archive_path), "wb") as handle:
            handle.write(archive)
        if os.path.exists(full(original)):
            os.remove(full(original))
        entries.append({
            "selectionKind": kind, "originalPath": original, "baseBlobId": oid, "baseBlobMode": mode,
            "baseBlobSha256": va.sha256(data), "baseBlobBytes": len(data), "claimScannerResultLines": occurrences,
            "physicalLinesWithResultLines": physical, "summaryPatternLines": va.summary_pattern_lines(data),
            "archivePath": archive_path, "archiveSha256": va.sha256(archive), "archiveBytes": len(archive),
            "decompressedBytes": len(data), "referringFilesAtBase": git.referring_files(base, original.rsplit("/", 1)[1]),
        })
    lines = va.expected_attribute_lines([e["archivePath"] for e in entries])
    if va.ATTRIBUTES_REL in tree:
        raise SystemExit("lane .gitattributes exists at base; this producer only creates it")
    with open(full(va.ATTRIBUTES_REL), "wb") as handle:
        handle.write(("\n".join(lines) + "\n").encode("utf-8"))
    archives_manifest = {
        "schema": va.SCHEMA, "handle": va.HANDLE, "baseCommit": base,
        "selection": {"historyRoot": va.HISTORY_ROOT, "resultLineRegex": va.RESULT_LINE_REGEX,
                      "prefixGuard": va.PREFIX_GUARD.decode("ascii"), "scannerTextRegex": va.SCANNER_TEXT_REGEX,
                      "summaryPatternRegex": va.SUMMARY_PATTERN_REGEX, "named": [dict(n) for n in va.NAMED],
                      "rule": SELECTION_RULE},
        "encoding": ENCODING,
        "attributes": {"path": va.ATTRIBUTES_REL, "baseExists": False, "lines": lines, "rule": ATTRIBUTE_RULE},
        "referenceResolution": REFERENCE_RULE,
        "archives": entries,
        "scannerTextWithoutResultLinesAtBase": unselected,
        "compressedContainersWithResultLinesAtBase": containers,
    }

    # Rewords.
    by_path = collections.defaultdict(dict)
    for path, number, base_sha, new_line in REWORDS:
        by_path[path][number] = (base_sha, new_line.encode("utf-8"))
    files, rewords = [], []
    for path in sorted(by_path):
        oid = tree[path][2]
        data = objects[oid]
        base_lines, ends_lf = vr.split_lines(data)
        if not ends_lf:
            raise SystemExit(f"{path} does not end with LF")
        new_lines = list(base_lines)
        for number, (base_sha, new_line) in sorted(by_path[path].items()):
            old = base_lines[number - 1]
            if vr.sha256(old) != base_sha or not vr.matches_pattern(old):
                raise SystemExit(f"{path}:{number} base line does not match its registered hash or the pattern")
            if vr.matches_pattern(new_line) or b"\n" in new_line or b"\r" in new_line:
                raise SystemExit(f"{path}:{number} new line is not a pattern-free single line")
            if vr.integers(new_line) != vr.integers(old) or vr.digit_runs(new_line) != vr.digit_runs(old):
                raise SystemExit(f"{path}:{number} integers differ")
            new_lines[number - 1] = new_line
            rewords.append({"path": path, "baseLineNumber": number, "baseBlobId": oid,
                            "baseLineSha256": base_sha, "newLineSha256": vr.sha256(new_line),
                            "baseIntegers": vr.integers(old), "newIntegers": vr.integers(new_line)})
        for number, line in enumerate(base_lines, start=1):
            if vr.matches_pattern(line) and number not in by_path[path]:
                raise SystemExit(f"{path}:{number} matches the pattern but is not registered")
        files.append({"path": path, "baseBlobId": oid, "baseBlobSha256": vr.sha256(data), "baseBlobBytes": len(data),
                      "baseLines": len(base_lines), "baseEndsWithLineFeed": True})
        write_crlf(full(path), b"\n".join(new_lines) + b"\n")
    rewords_manifest = {"schema": vr.SCHEMA, "handle": vr.HANDLE, "baseCommit": base, "selection": REWORD_SELECTION,
                        "tailRule": TAIL_RULE, "files": files, "rewords": rewords}

    for rel, value in ((va.MANIFEST_REL, archives_manifest), (vr.MANIFEST_REL, rewords_manifest)):
        with open(full(rel), "w", encoding="utf-8", newline="\n") as handle:
            json.dump(value, handle, indent=2, ensure_ascii=True)
            handle.write("\n")
    print(f"BUILD-REPAIR: {len(entries)} archives, {len(rewords)} reworded lines in {len(files)} files, "
          f"{len(unselected)} unselected scanner-text files, {len(containers)} zip containers; base {base}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
