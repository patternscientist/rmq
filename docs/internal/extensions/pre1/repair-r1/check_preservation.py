#!/usr/bin/env python3
"""Git-object preservation proof for the PRE-1-R1 repair range.

For base..REV (REV defaults to HEAD) this checks, from Git objects only:
  1. scope: `git diff --name-status --no-renames` lists only the pinned write
     scope, and every required repair change is present;
  2. protected identities: the tree or blob ids of RMQ/, scripts/, lakefile.toml,
     lean-toolchain, RMQ.lean, docs/DIGESTION_LOG.md, docs/FAMILY_SUMMARY.md,
     the claim policy, and every base blob under the lane root outside the write
     scope are unchanged (same id and mode);
  3. ledgers: each changed design ledger is its base blob followed by appended
     bytes (no removed or edited line);
  4. frozen rows: the PRE-1 acceptance matrix blob is unchanged, and both row
     byte strings of each of the 31 inherited IDs are equal at base and REV
     (strict UTF-8, missing or duplicate IDs fail);
  5. checker inputs: every input path of the builder, contract and validation
     checkers (pinned below from reading the scripts) is unchanged and outside
     the write scope; in the six checker scripts every code line naming a docs
     path names only a pinned registry or manifest, and no code line names an
     archived or reworded file; no Lean file under RMQ/ or the lane's Lean check
     scripts uses a file-system read.

Exit codes: 0 preserved; 1 a check failed; 2 usage error; 3 Git error.
Every failure prints `PRESERVATION: FAIL [<code>] <detail>`.
"""

import argparse
import hashlib
import json
import re
import subprocess
import sys

BASE_COMMIT = "84ae12f6f6bad99fd3215c5bdd5b2a93e3779897"
LANE = "docs/internal/extensions/pre1/"
REPAIR = LANE + "repair-r1/"
AUDIT = "docs/internal/audit_reports/2026-09-12_PRE1_contract_fresh_blind.md"
REQUIRED = {
    ("D", AUDIT),
    ("A", LANE + "evidence/audit-archive/2026-09-12_PRE1_contract_fresh_blind.md.gz"),
    ("D", LANE + "evidence/author-final-checks-summary.json"),
    ("A", LANE + "evidence/author-final-checks-summary.json.gz"),
    ("A", LANE + ".gitattributes"),
    ("M", LANE + "BUILDER_STAGE_LOG.md"),
    ("M", LANE + "REPORT.md"),
    ("M", "docs/internal/WORKFLOW_DESIGN_DECISIONS.md"),
}
OPTIONAL = {("M", "docs/internal/DESIGN_DECISIONS.md")}
LEDGERS = ("docs/internal/WORKFLOW_DESIGN_DECISIONS.md", "docs/internal/DESIGN_DECISIONS.md")
WRITE_SCOPE_FILES = {p for _, p in REQUIRED | OPTIONAL}
PROTECTED = ("RMQ", "scripts", "lakefile.toml", "lean-toolchain", "RMQ.lean", "docs/DIGESTION_LOG.md",
             "docs/FAMILY_SUMMARY.md", "docs/internal/CLAIM_DRIFT_POLICY.json")
MATRIX = LANE + "ACCEPTANCE_MATRIX.md"
INHERITED_IDS = (
    "REQ-PRE-CONTRACT", "REQ-PRE-INPUT", "REQ-PRE-MACHINE", "REQ-PRE-EXACT", "REQ-PRE-COST", "REQ-PRE-JOIN",
    "CHK-PRE-CONTROLS", "REPLAY-EXACT-REGISTRY", "REPLAY-SELECTOR-NONVACUITY", "REPLAY-SUBPROCESS-DEADLINE",
    "INV-STORE-IDENTITY", "INV-VALUE-DEPENDENCY", "INV-SEMANTIC-NONVACUITY", "INV-TRACE-EXECUTION",
    "INV-STORE-AGREEMENT", "INV-READ-BACKING", "INV-WORD-WIDTH", "INV-ADDRESS-WIDTH", "INV-INSTRUCTION-ATOMICITY",
    "INV-PROGRAM-ACCOUNTING", "INV-ORACLE-INDEPENDENCE", "INV-VALIDATION-REACH", "INV-ALL-SIZE",
    "INV-PROOF-SEPARATION", "INV-NO-SYNTHETIC", "INV-CATEGORY-SEPARATION", "INV-PUBLIC-COMPOSITION",
    "INV-CERTIFICATE-ANTI-BYPASS", "INV-MUTATION-REPRODUCIBILITY", "INV-GLOBAL-PHYSICAL-MACHINE", "INV-WIDTH-SCALING",
)
# Inputs read by each checker, from reading the scripts at the base (paths and
# directory prefixes; Lean builds additionally read every import under RMQ/).
CONSTRUCTION = "RMQ/Core/WordRAM/Construction"
CHECKER_INPUTS = {
    "scripts/preprocessing_builder_gate.ps1": [
        "scripts/owned_process_tree.ps1", "scripts/preprocessing_builder_replay.ps1"],
    "scripts/preprocessing_builder_replay.ps1": [
        LANE + "builder_cases.json", LANE + "builder_manifest.json", LANE + "contract_cases.json",
        LANE + "primitive_manifest.json", "scripts/preprocessing_builder_firewall.ps1",
        "scripts/preprocessing_contract_firewall.ps1", "scripts/preprocessing_contract_replay.ps1",
        "scripts/preprocessing_builder_check.lean", "scripts/owned_process_tree.ps1",
        "RMQ/Validation/PreprocessingContract.lean", "RMQ/Validation/Preprocessing.lean", CONSTRUCTION,
        "lakefile.toml", "lean-toolchain", "RMQ"],
    "scripts/preprocessing_builder_firewall.ps1": [
        "scripts/preprocessing_contract_firewall.ps1", "scripts/owned_process_tree.ps1", LANE + "builder_manifest.json",
        CONSTRUCTION],
    "scripts/preprocessing_contract_gate.ps1": [
        "scripts/owned_process_tree.ps1", "scripts/preprocessing_contract_firewall.ps1",
        "scripts/preprocessing_contract_check.lean", CONSTRUCTION, "lakefile.toml", "lean-toolchain", "RMQ"],
    "scripts/preprocessing_contract_replay.ps1": [
        LANE + "contract_cases.json", LANE + "primitive_manifest.json", "scripts/preprocessing_contract_firewall.ps1",
        "scripts/preprocessing_contract_check.lean", "scripts/owned_process_tree.ps1", CONSTRUCTION,
        "lean-toolchain", "lakefile.toml", "RMQ"],
    "scripts/preprocessing_contract_firewall.ps1": [
        LANE + "primitive_manifest.json", CONSTRUCTION + "/Primitive.lean", CONSTRUCTION + "/Input.lean",
        CONSTRUCTION + "/Model.lean"],
}
ALLOWED_DOC_INPUTS = {LANE + n for n in ("builder_cases.json", "builder_manifest.json", "contract_cases.json",
                                         "primitive_manifest.json")}
REPAIRED_TOKENS = ("author-final-checks-summary", "2026-09-12_PRE1_contract_fresh_blind", "audit-archive",
                   "audit_reports", "BUILDER_STAGE_LOG", "REPORT.md", "REWORDS", "RECEIPT_ARCHIVES", "repair-r1",
                   "pre1/evidence", ".gz")
LEAN_READ = re.compile(r"IO\.FS\.|readFile|readBinFile|IO\.FS\.Handle|System\.FilePath|FilePath\.")
LEAN_CHECK_SCRIPTS = ("scripts/preprocessing_builder_check.lean", "scripts/preprocessing_contract_check.lean",
                      "scripts/preprocessing_spec_check.lean", "scripts/preprocessing_stage_check.lean")
GIT_TIMEOUT_SECONDS = 600


class GitFailure(Exception):
    pass


def git(repo, *args):
    try:
        result = subprocess.run(["git", "-C", repo, "-c", "core.fsmonitor=false", *args], capture_output=True,
                                timeout=GIT_TIMEOUT_SECONDS)
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise GitFailure(f"git {' '.join(args[:2])}: {exc}")
    return result


def checked(repo, *args):
    result = git(repo, *args)
    if result.returncode != 0:
        raise GitFailure(f"git {' '.join(args[:2])} exited {result.returncode}: {result.stderr.decode('utf-8', 'replace').strip()}")
    return result.stdout


def object_id(repo, rev, path):
    result = git(repo, "rev-parse", "--verify", "--quiet", f"{rev}:{path}")
    return result.stdout.decode("ascii").strip() if result.returncode == 0 else None


def blob(repo, rev, path):
    oid = object_id(repo, rev, path)
    return None if oid is None else checked(repo, "cat-file", "blob", oid)


def ls_tree(repo, rev, prefix):
    out = checked(repo, "ls-tree", "-r", "-z", "--full-tree", rev, "--", prefix)
    entries = {}
    for record in out.split(b"\0"):
        if record:
            meta, path = record.split(b"\t", 1)
            mode, kind, oid = meta.decode("ascii").split(" ")
            entries[path.decode("utf-8")] = (mode, kind, oid)
    return entries


def comment_mask(lines):
    """True for PowerShell lines that are comments (`#` lines or inside a `<# ... #>` block)."""
    mask, inside = [], False
    for line in lines:
        stripped = line.strip()
        if inside:
            mask.append(True)
            if "#>" in stripped:
                inside = False
            continue
        if stripped.startswith("<#"):
            mask.append(True)
            inside = "#>" not in stripped[2:]
            continue
        mask.append(stripped.startswith("#"))
    return mask


def matrix_rows(data):
    text = data.decode("utf-8", errors="strict")
    rows = {}
    for number, line in enumerate(text.split("\n"), start=1):
        match = re.match(r"^\| ([A-Z0-9-]+) \|", line)
        if match and match.group(1) in INHERITED_IDS:
            rows.setdefault(match.group(1), []).append((number, line.encode("utf-8")))
    return rows


def main(argv):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--repo", default=".")
    parser.add_argument("--head", default="HEAD")
    parser.add_argument("--result-json", default=None)
    args = parser.parse_args(argv)
    repo = args.repo
    failures, details = [], {}

    def fail(code, detail):
        failures.append(code)
        print(f"PRESERVATION: FAIL [{code}] {detail}", flush=True)

    head = checked(repo, "rev-parse", "--verify", args.head + "^{commit}").decode("ascii").strip()
    base = checked(repo, "rev-parse", "--verify", BASE_COMMIT + "^{commit}").decode("ascii").strip()
    print(f"PRESERVATION: range {base}..{head}", flush=True)

    # 1. Scope.
    out = checked(repo, "diff", "--name-status", "--no-renames", "-z", base, head, "--")
    fields = [f.decode("utf-8") for f in out.split(b"\0") if f]
    changes = set(zip(fields[0::2], fields[1::2]))
    outside = sorted(c for c in changes if c not in REQUIRED and c not in OPTIONAL
                     and not (c[0] == "A" and c[1].startswith(REPAIR)))
    for status, path in outside:
        fail("diff-path-outside-scope", f"{status} {path}")
    for status, path in sorted(REQUIRED - changes):
        fail("required-change-missing", f"{status} {path}")
    details["nameStatus"] = sorted(f"{s} {p}" for s, p in changes)
    print(f"PRESERVATION: {len(changes)} changed paths; {len(outside)} outside the write scope; "
          f"{len(REQUIRED - changes)} required changes missing", flush=True)

    # 2. Protected identities.
    protected = {}
    for path in PROTECTED:
        before, after = object_id(repo, base, path), object_id(repo, head, path)
        protected[path] = {"base": before, "head": after}
        if before is None or before != after:
            fail("protected-path-changed", f"{path}: base {before} head {after}")
    details["protected"] = protected
    base_lane, head_lane = ls_tree(repo, base, LANE), ls_tree(repo, head, LANE)
    unchanged = 0
    for path, entry in sorted(base_lane.items()):
        if path in WRITE_SCOPE_FILES:
            continue
        if head_lane.get(path) != entry:
            fail("lane-path-changed", f"{path}: base {entry} head {head_lane.get(path)}")
        else:
            unchanged += 1
    details["laneBlobsOutsideScopeUnchanged"] = unchanged
    print(f"PRESERVATION: {len(PROTECTED)} protected ids checked; {unchanged} lane blobs outside the write scope unchanged",
          flush=True)

    # 3. Ledgers.
    ledgers = {}
    for path in LEDGERS:
        before, after = blob(repo, base, path), blob(repo, head, path)
        if before == after:
            ledgers[path] = "unchanged"
            continue
        if before is None or after is None or not after.startswith(before):
            fail("ledger-not-append-only", f"{path} is not its base blob followed by appended bytes")
            ledgers[path] = "not-append-only"
        else:
            ledgers[path] = f"appended {len(after) - len(before)} bytes"
    details["ledgers"] = ledgers

    # 4. Frozen rows.
    base_matrix, head_matrix = blob(repo, base, MATRIX), blob(repo, head, MATRIX)
    if object_id(repo, base, MATRIX) != object_id(repo, head, MATRIX):
        fail("matrix-changed", f"{MATRIX} blob differs")
    try:
        base_rows, head_rows = matrix_rows(base_matrix), matrix_rows(head_matrix or b"")
    except UnicodeDecodeError as exc:
        fail("matrix-not-utf8", str(exc))
        base_rows, head_rows = {}, {}
    row_hashes = {}
    for row_id in INHERITED_IDS:
        b_rows, h_rows = base_rows.get(row_id, []), head_rows.get(row_id, [])
        if len(b_rows) != 2 or len(h_rows) != 2:
            fail("frozen-row-count", f"{row_id}: {len(b_rows)} base rows, {len(h_rows)} head rows (expected 2 and 2)")
        if b_rows != h_rows:
            fail("frozen-row-changed", f"{row_id}: row bytes or positions differ")
        row_hashes[row_id] = [f"{n}:{hashlib.sha256(b).hexdigest().upper()}" for n, b in b_rows]
    details["frozenRows"] = row_hashes
    print(f"PRESERVATION: {len(INHERITED_IDS)} inherited IDs, {sum(len(v) for v in base_rows.values())} base rows compared",
          flush=True)

    # 5. Checker inputs and reads.
    inputs = {}
    for checker, paths in CHECKER_INPUTS.items():
        for path in [checker] + paths:
            if path in inputs:
                continue
            before, after = object_id(repo, base, path), object_id(repo, head, path)
            inputs[path] = before
            if before is None or before != after:
                fail("checker-input-changed", f"{path}: base {before} head {after}")
            if path in WRITE_SCOPE_FILES or path.startswith(REPAIR) or any(p.startswith(path + "/") for p in WRITE_SCOPE_FILES):
                fail("checker-input-in-write-scope", path)
    details["checkerInputs"] = inputs
    token_hits, doc_paths = [], []
    for checker in CHECKER_INPUTS:
        text = (blob(repo, head, checker) or b"").decode("utf-8", "replace")
        lines = text.split("\n")
        mask = comment_mask(lines)
        for number, (line, is_comment) in enumerate(zip(lines, mask), start=1):
            for token in REPAIRED_TOKENS:
                if token in line:
                    token_hits.append({"path": checker, "line": number, "token": token,
                                       "class": "comment" if is_comment else "code"})
                    if not is_comment:
                        fail("checker-token-in-code", f"{checker}:{number} names {token} in code")
            if not is_comment:
                for quoted in re.findall(r"['\"](docs/[^'\"]*)['\"]", line):
                    doc_paths.append({"path": checker, "line": number, "docPath": quoted})
                    if quoted not in ALLOWED_DOC_INPUTS:
                        fail("checker-reads-other-doc", f"{checker}:{number} names {quoted}")
                if re.search(r"EnumerateFiles|Get-ChildItem|Get-Content|ReadAll", line) and "docs" in line:
                    fail("checker-enumerates-docs", f"{checker}:{number} reads or enumerates under docs")
    details["checkerTokenHits"] = token_hits
    details["checkerDocPaths"] = doc_paths
    lean_hits = []
    lean_files = [p for p in ls_tree(repo, head, "RMQ") if p.endswith(".lean")] + list(LEAN_CHECK_SCRIPTS)
    for path in sorted(lean_files):
        text = (blob(repo, head, path) or b"").decode("utf-8", "replace")
        for number, line in enumerate(text.split("\n"), start=1):
            if LEAN_READ.search(line):
                lean_hits.append({"path": path, "line": number})
                fail("lean-file-read", f"{path}:{number} uses a file-system read")
    details["leanFilesScanned"] = len(lean_files)
    details["leanFileReads"] = lean_hits
    print(f"PRESERVATION: {len(inputs)} checker inputs unchanged-checked; {len(token_hits)} token hits in checker scripts "
          f"({sum(1 for h in token_hits if h['class'] == 'code')} in code); {len(doc_paths)} docs paths in code; "
          f"{len(lean_files)} Lean files scanned, {len(lean_hits)} file-system reads", flush=True)

    result = {"schema": "rmq.pre1.repair-r1.preservation.v1", "base": base, "head": head,
              "failureCodes": sorted(set(failures)), "failureCount": len(failures), "details": details}
    if args.result_json:
        with open(args.result_json, "w", encoding="utf-8", newline="\n") as handle:
            json.dump(result, handle, indent=2)
            handle.write("\n")
    if failures:
        print(f"PRESERVATION: RESULT: FAIL ({len(failures)} failures)", flush=True)
        return 1
    print(f"PRESERVATION: RESULT: PASS ({len(changes)} changed paths inside the write scope; base {base}; head {head})", flush=True)
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main(sys.argv[1:]))
    except GitFailure as exc:
        print(f"PRESERVATION: ERROR {exc}", flush=True)
        sys.exit(3)
