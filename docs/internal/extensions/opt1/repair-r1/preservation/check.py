"""Exact OPT-1 frozen-row and protected-Git-object preservation checks.

Use check.ps1: its release-gated owned job covers this process and every Git
descendant. Git is captured as binary streams, with its own positive deadline
and proactive output ceiling. No repository source or index is written.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import threading
import time

BASE = "aecf4a580c591e8f694a3699e19e843198089194"
FREEZE = "1f3a4199eaa95324cd1daaadbab89340ca8392c4"
GOVERNANCE = "0e6a00f654abc64f8b68988fa9675b9a839dca2f"
OLD_MATRIX = "docs/internal/extensions/opt1/ACCEPTANCE_MATRIX.md"
REPAIR_ROOT = "docs/internal/extensions/opt1/repair-r1/"
NEW_MATRIX = REPAIR_ROOT + "ACCEPTANCE_MATRIX.md"
PROOF_IDENTITY = REPAIR_ROOT + "PROOF_IDENTITY.md"
FIELDS = "docs/internal/extensions/opt1/certificate-replay/FIELDS.json"
ROOTS = "docs/internal/extensions/opt1/AXIOM_ROOTS.json"
HISTORY = "docs/internal/extensions/opt1/"
OPTIMIZATION = "RMQ/Core/WordRAM/Optimization/"
PACKED = "RMQ/Core/WordRAM/Packed/"
VALIDATOR = "RMQ/Validation/PackedOptimized.lean"
AXIOM_FILES = (
    "scripts/packed_optimized_axiom_check.ps1",
    "scripts/packed_optimized_axiom_union.lean",
    "scripts/packed_optimized_axioms.lean",
)
PROTECTED_SCOPES = (OPTIMIZATION, PACKED, VALIDATOR, *AXIOM_FILES, HISTORY)
INHERITED_IDS = (
    "REQ-OPT-BUDGET", "REQ-OPT-COMPILE", "REQ-OPT-RUN", "REQ-OPT-SPACE",
    "REQ-OPT-CONSUMER", "CHK-OPT-CONTROLS", "REPLAY-EXACT-REGISTRY",
    "REPLAY-SELECTOR-NONVACUITY", "REPLAY-SUBPROCESS-DEADLINE",
    "CHK-OPT-DEVELOPMENT", "CHK-OPT-FINAL", "CHK-OPT-TRUST",
    "CHK-OPT-CONDITIONAL", "CHK-OPT-AUDIT", "INV-STORE-IDENTITY",
    "INV-VALUE-DEPENDENCY", "INV-SEMANTIC-NONVACUITY", "INV-TRACE-EXECUTION",
    "INV-STORE-AGREEMENT", "INV-READ-BACKING", "INV-WORD-WIDTH",
    "INV-ADDRESS-WIDTH", "INV-INSTRUCTION-ATOMICITY", "INV-PROGRAM-ACCOUNTING",
    "INV-ORACLE-INDEPENDENCE", "INV-VALIDATION-REACH", "INV-ALL-SIZE",
    "INV-PROOF-SEPARATION", "INV-NO-SYNTHETIC", "INV-CATEGORY-SEPARATION",
    "INV-PUBLIC-COMPOSITION", "INV-CERTIFICATE-ANTI-BYPASS",
    "INV-MUTATION-REPRODUCIBILITY", "INV-GLOBAL-PHYSICAL-MACHINE", "INV-WIDTH-SCALING",
)
REPAIR_IDS = (
    "REQ-OPT-R1-EXCLUSIVE-REJECTION", "REQ-OPT-R1-CHECKOUT-PROVENANCE",
    "REQ-OPT-R1-PRESERVATION", "CHK-OPT-R1-PRODUCTION-REPLAY",
)
CONTROL_IDS = (
    "P01-EXACT-ROWS", "P02-MISSING-MIDDLE-ROW", "P03-DUPLICATE-MIDDLE-ROW",
    "P04-CHANGED-MIDDLE-ROW", "P05-UNKNOWN-ROW", "P06-MISSING-REPAIR-ROW",
    "P07-DUPLICATE-REPAIR-ROW", "P08-MOJIBAKE", "P09-ORDINARY-UNICODE",
    "P10-PROTECTED-OMISSION", "P11-PROTECTED-BLOB", "P12-PROTECTED-MODE",
    "P13-UNAUTHORIZED-ADDITION", "P14-REPAIR-ADDITION", "P15-INVALID-UTF8",
    "P16-LINE-TERMINATORS", "P17-FIELD-TYPE-ALTERED",
)
MOJIBAKE = ("\u00c2\u00ac", "\u00e2\u20ac\u0153", "\u00e2\u20ac\u009d", "\u00ef\u00bb\u00bf")


class Rejected(Exception):
    def __init__(self, code: str, detail: object):
        self.code = code
        self.detail = detail
        super().__init__(f"{code}: {detail}")


def require(ok: bool, code: str, detail: object) -> None:
    if not ok:
        raise Rejected(code, detail)


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def strict_text(data: bytes, label: str) -> str:
    try:
        return data.decode("utf-8", errors="strict")
    except UnicodeDecodeError as exc:
        raise Rejected("UTF8", {"label": label, "offset": exc.start}) from exc


def reject_mojibake(data: bytes, label: str) -> None:
    text = strict_text(data, label)
    found = [token for token in MOJIBAKE if token in text]
    require(not found, "MOJIBAKE", {"label": label, "tokens": found})


def rows(data: bytes, expected: tuple[str, ...], label: str) -> dict[str, bytes]:
    strict_text(data, label)
    result: dict[str, bytes] = {}
    # A row-content byte string starts at its leading pipe and ends at the
    # trailing pipe. Only the physical LF or CRLF terminator lies outside it.
    # Whitespace, Unicode encoding, punctuation and every column remain exact.
    for line in data.split(b"\n"):
        content = line[:-1] if line.endswith(b"\r") else line
        match = re.match(rb"^\| `((?:REQ|CHK|REPLAY|INV)-[^`]+)` \|", content)
        if not match:
            continue
        require(content.endswith(b"|"), "ROW_SHAPE", {"label": label})
        key = strict_text(match.group(1), label)
        require(key not in result, "ROW_DUPLICATE", {"label": label, "id": key})
        result[key] = content
    require(set(result) == set(expected), "ROW_IDS", {
        "label": label, "expected": len(expected), "actual": len(result),
        "missing": sorted(set(expected) - set(result)),
        "unexpected": sorted(set(result) - set(expected)),
    })
    reject_mojibake(data, label)
    return result


def compare_rows(frozen: dict[str, bytes], candidate: dict[str, bytes], label: str) -> list[dict]:
    changed = [key for key in INHERITED_IDS if frozen[key] != candidate[key]]
    require(not changed, "ROW_BYTES", {"label": label, "changed": changed})
    return [{"id": key, "bytes": len(frozen[key]), "sha256": sha(frozen[key]),
             "byte_equal": frozen[key] == candidate[key]} for key in INHERITED_IDS]


def parse_tree(data: bytes, label: str) -> dict[str, tuple[str, str, str]]:
    result = {}
    for entry in data.split(b"\0"):
        if not entry:
            continue
        head, path = entry.split(b"\t", 1)
        mode, kind, oid = strict_text(head, label).split(" ")
        name = strict_text(path, label)
        require(name not in result, "TREE_DUPLICATE", name)
        result[name] = (mode, kind, oid)
    return result


def check_protected(baseline: dict, candidate: dict) -> list[dict]:
    missing = sorted(set(baseline) - set(candidate))
    require(not missing, "PROTECTED_OMISSION", missing)
    extra = sorted(path for path in set(candidate) - set(baseline)
                   if not path.startswith(REPAIR_ROOT))
    require(not extra, "PROTECTED_ADDITION", extra)
    changed = sorted(path for path in baseline if baseline[path] != candidate[path])
    require(not changed, "PROTECTED_IDENTITY", changed)
    return [{"path": p, "mode": baseline[p][0], "kind": baseline[p][1],
             "blob": baseline[p][2], "equal": True} for p in sorted(baseline)]


def no_duplicate_json(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "JSON_DUPLICATE", key)
        result[key] = value
    return result


def read_json(data: bytes, label: str):
    return json.loads(strict_text(data, label), object_pairs_hook=no_duplicate_json)


def check_field_inventory(fields: dict, proof: bytes, consumers: bytes) -> list[dict]:
    strict_text(proof, "PROOF_IDENTITY.md")
    require(fields["Version"] == "opt1-certificate-fields-v3", "FIELD_VERSION", fields["Version"])
    definitions = fields["Fields"]
    names = [field["Name"] for field in definitions]
    require(len(names) == 39 and len(set(names)) == 39, "FIELD_COUNT", names)
    source = strict_text(consumers, "Consumers.lean")
    generic = re.findall(r"(?m)^theorem (\w+)_expectedType\b", source)
    canonical = re.findall(r"(?m)^theorem (\w+)_canonical\b", source)
    require(len(generic) == 39 and set(generic) == set(names), "GENERIC_CONSUMERS", generic)
    require(len(canonical) == 39 and set(canonical) == set(names), "CANONICAL_CONSUMERS", canonical)
    result = []
    for field in definitions:
        name = field["Name"]
        start = ("<!-- OPT1-R1-FIELD-" + name + "-BEGIN -->\n```lean\n").encode()
        finish = ("\n```\n<!-- OPT1-R1-FIELD-" + name + "-END -->").encode()
        require(proof.count(start) == 1 and proof.count(finish) == 1, "FIELD_MARKERS", name)
        actual = proof.split(start, 1)[1].split(finish, 1)[0]
        expected = field["ExpectedType"].encode("utf-8")
        require(actual == expected, "FIELD_TYPE_BYTES", name)
        result.append({"name": name, "bytes": len(expected), "sha256": sha(expected),
                       "exact_type_bytes": True,
                       "consumers": [name + "_expectedType", name + "_canonical"]})
    return result


class Git:
    """Binary capture; every actual tool call has deadline, ceiling and receipt."""
    def __init__(self, repo: Path, output: Path):
        self.repo, self.output, self.receipts = repo, output, []
        self.output.mkdir()

    def run(self, args: list[str], expected_exit: int = 0, deadline: float = 30.0,
            ceiling: int = 8 * 1024 * 1024) -> bytes:
        number = len(self.receipts) + 1
        stem = self.output / f"git-{number:03d}"
        command = ["git", "--no-pager", "-c", "core.fsmonitor=false", "-c", "core.untrackedCache=false", *args]
        started = time.monotonic()
        overflow = threading.Event()
        counts = [0, 0]
        chunks: list[list[bytes]] = [[], []]
        errors = []
        proc = subprocess.Popen(command, cwd=self.repo, stdin=subprocess.DEVNULL,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                creationflags=subprocess.CREATE_NO_WINDOW if os.name == "nt" else 0)

        def capture(stream, index):
            try:
                with stream, Path(str(stem) + (".stdout.bin" if index == 0 else ".stderr.bin")).open("wb") as log:
                    while chunk := stream.read(65536):
                        log.write(chunk)
                        counts[index] += len(chunk)
                        if sum(counts) > ceiling:
                            overflow.set()
                            break
                        chunks[index].append(chunk)
            except Exception as exc:
                errors.append(repr(exc))

        threads = [threading.Thread(target=capture, args=(proc.stdout, 0), daemon=True),
                   threading.Thread(target=capture, args=(proc.stderr, 1), daemon=True)]
        for thread in threads:
            thread.start()
        timed_out = False
        try:
            while proc.poll() is None:
                if time.monotonic() - started >= deadline:
                    timed_out = True
                    break
                if overflow.is_set():
                    break
                time.sleep(0.01)
        finally:
            if proc.poll() is None:
                proc.kill()
            proc.wait(timeout=10)
            for thread in threads:
                thread.join(timeout=10)
        out, err = b"".join(chunks[0]), b"".join(chunks[1])
        raw_out = Path(str(stem) + ".stdout.bin").read_bytes()
        raw_err = Path(str(stem) + ".stderr.bin").read_bytes()
        receipt = {"command": command, "cwd": str(self.repo), "exit": proc.returncode,
                   "expected_exit": expected_exit, "duration_seconds": time.monotonic() - started,
                   "deadline_seconds": deadline, "output_limit_bytes": ceiling,
                   "timed_out": timed_out, "overflow": overflow.is_set(), "stream_bytes": counts,
                   "stdout_file": str(stem) + ".stdout.bin", "stderr_file": str(stem) + ".stderr.bin",
                   "stdout_sha256": sha(raw_out), "stderr_sha256": sha(raw_err), "capture_errors": errors,
                   "capture_complete": not any(t.is_alive() for t in threads),
                   "root_absent": proc.poll() is not None,
                   "descendant_ownership": "Inherited from check.ps1 owned supervisor; see process.json"}
        self.receipts.append(receipt)
        Path(str(stem) + ".json").write_text(json.dumps(receipt, indent=2), encoding="utf-8")
        require(not timed_out and not overflow.is_set() and not errors and receipt["capture_complete"],
                "GIT_CAPTURE", receipt)
        require(proc.returncode == expected_exit, "GIT_EXIT", receipt)
        return out

    def blob(self, ref: str, path: str) -> bytes:
        return self.run(["cat-file", "blob", ref + ":" + path])

    def tree(self, ref: str) -> dict:
        return parse_tree(self.run(["ls-tree", "-r", "-z", ref, "--", *PROTECTED_SCOPES]), ref)


def source_snapshot(repo: Path, paths: list[str]) -> dict:
    result = {}
    for name in paths:
        path = repo / name
        require(path.is_file() and not path.is_symlink(), "LIVE_PROTECTED_MISSING", name)
        data = path.read_bytes()
        result[name] = {"bytes": len(data), "sha256": sha(data)}
    return result


def run_controls(frozen: dict, old: bytes, new: bytes, baseline: dict,
                 fields: dict, proof: bytes, consumers: bytes) -> list[dict]:
    registry = read_json(Path(__file__).with_name("registry.json").read_bytes(), "registry.json")
    require(registry["version"] == "opt1-r1-preservation-controls-v1", "CONTROL_VERSION", registry)
    require(tuple(case["id"] for case in registry["cases"]) == CONTROL_IDS, "CONTROL_REGISTRY", registry)
    expected_verdicts = {case["id"]: case for case in registry["cases"]}
    results = []

    def case(key, action):
        expected = expected_verdicts[key]
        try:
            action()
            actual, code = "ACCEPT", None
        except Rejected as exc:
            actual, code = "REJECT", exc.code
        require(actual == expected["verdict"] and code == expected["code"], "CONTROL_VERDICT",
                {"id": key, "actual": actual, "code": code, "expected": expected})
        results.append({"id": key, "verdict": actual, "code": code, "passed": True})

    middle = frozen["INV-TRACE-EXECUTION"]
    new_rows = rows(new, INHERITED_IDS + REPAIR_IDS, "live repair matrix")
    repair = new_rows[REPAIR_IDS[2]]
    def check(data):
        return compare_rows(frozen, rows(data, INHERITED_IDS + REPAIR_IDS, "control"), "control")
    case(CONTROL_IDS[0], lambda: check(new))
    case(CONTROL_IDS[1], lambda: check(new.replace(middle, b"", 1)))
    case(CONTROL_IDS[2], lambda: check(new + b"\n" + middle + b"\n"))
    case(CONTROL_IDS[3], lambda: check(new.replace(middle, middle.replace(b"execution", b"Execution", 1), 1)))
    case(CONTROL_IDS[4], lambda: check(new + b"\n| `INV-UNKNOWN` | unauthorized |\n"))
    case(CONTROL_IDS[5], lambda: check(new.replace(repair, b"", 1)))
    case(CONTROL_IDS[6], lambda: check(new + b"\n" + repair + b"\n"))
    # These two deliberately exercise only the independent mojibake category.
    # Neither result substitutes for byte equality of a requirement row.
    case(CONTROL_IDS[7], lambda: reject_mojibake("control: \u00c2\u00ac".encode(), "mojibake control"))
    case(CONTROL_IDS[8], lambda: reject_mojibake("control: \u00ac \u2200 \u2264".encode(), "valid unicode control"))
    protected = sorted(baseline)[len(baseline) // 2]
    omission = dict(baseline); del omission[protected]
    changed = dict(baseline); changed[protected] = (*baseline[protected][:2], "0" * 40)
    mode = dict(baseline); mode[protected] = ("100755", *baseline[protected][1:])
    if mode[protected] == baseline[protected]:
        mode[protected] = ("100644", *baseline[protected][1:])
    extra = dict(baseline); extra[HISTORY + "unauthorized-added.txt"] = ("100644", "blob", "0" * 40)
    allowed = dict(baseline); allowed[REPAIR_ROOT + "control.txt"] = ("100644", "blob", "0" * 40)
    case(CONTROL_IDS[9], lambda: check_protected(baseline, omission))
    case(CONTROL_IDS[10], lambda: check_protected(baseline, changed))
    case(CONTROL_IDS[11], lambda: check_protected(baseline, mode))
    case(CONTROL_IDS[12], lambda: check_protected(baseline, extra))
    case(CONTROL_IDS[13], lambda: check_protected(baseline, allowed))
    case(CONTROL_IDS[14], lambda: rows(old + b"\xff", INHERITED_IDS, "invalid UTF8 control"))
    # Row physical terminators are outside the frozen byte string. Content is
    # copied directly; this control does not normalize a compared row value.
    terminators = b"\r\n".join(new_rows[key] for key in INHERITED_IDS + REPAIR_IDS) + b"\r\n"
    case(CONTROL_IDS[15], lambda: check(terminators))
    name = fields["Fields"][19]["Name"]
    marker = ("<!-- OPT1-R1-FIELD-" + name + "-BEGIN -->\n```lean\n").encode()
    altered_proof = proof.replace(marker, marker + b"True /- changed type -/\n", 1)
    case(CONTROL_IDS[16], lambda: check_field_inventory(fields, altered_proof, consumers))
    require(tuple(row["id"] for row in results) == CONTROL_IDS, "CONTROL_EXECUTED", results)
    return results


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--candidate-ref", required=True)
    parser.add_argument("--repo-root", required=True, type=Path)
    parser.add_argument("--output-directory", required=True, type=Path)
    parser.add_argument("--self-test-only", action="store_true")
    args = parser.parse_args()
    repo, output = args.repo_root.resolve(), args.output_directory.resolve()
    output.mkdir(parents=True, exist_ok=True)
    report = {"version": "opt1-r1-preservation-v1", "base": BASE, "freeze": FREEZE,
              "governance": GOVERNANCE, "candidate": args.candidate_ref, "repo_root": str(repo),
              "self_test_only": args.self_test_only, "status": "INCOMPLETE",
              "source_only": True, "compiled_linkage_and_production_replays": "Not certified by this checker",
              "row_serialization": "Exact UTF-8 bytes from leading pipe to trailing pipe; LF/CRLF terminator excluded",
              "posix_runtime_coverage": "UNEXECUTED unless process.json records a real POSIX invocation"}
    git = Git(repo, output / "git")
    before = None
    index_before = None
    watched = []
    started = time.monotonic()
    try:
        require(re.fullmatch(r"[0-9a-f]{40}", args.candidate_ref) is not None, "CANDIDATE_REF", args.candidate_ref)
        resolved = strict_text(git.run(["rev-parse", "--verify", args.candidate_ref + "^{commit}"]), "candidate").strip()
        require(resolved == args.candidate_ref, "CANDIDATE_REF", resolved)
        git.run(["merge-base", "--is-ancestor", GOVERNANCE, args.candidate_ref])
        git.run(["merge-base", "--is-ancestor", BASE, args.candidate_ref])
        baseline = git.tree(BASE)
        require(sum(p.startswith(OPTIMIZATION) for p in baseline) == 12, "BASE_OPTIMIZATION_COUNT", baseline)
        require(sum(p.startswith(PACKED) for p in baseline) == 55, "BASE_PACKED_COUNT", baseline)
        require(sum(p.startswith(HISTORY) for p in baseline) == 439, "BASE_HISTORY_COUNT", baseline)
        require(all(p in baseline for p in AXIOM_FILES + (VALIDATOR,)), "BASE_REQUIRED_PATHS", baseline)
        report["protected_counts"] = {"optimization": 12, "packed": 55, "validator": 1,
                                      "axiom_scripts": 3, "original_history": 439, "total": len(baseline)}
        watched = sorted(baseline) + [NEW_MATRIX, PROOF_IDENTITY]
        before = source_snapshot(repo, watched)
        report["live_before"] = before
        index_before = git.run(["ls-files", "--stage", "-z", "--", *PROTECTED_SCOPES])
        report["index_before_sha256"] = sha(index_before)
        frozen_blob = git.blob(FREEZE, OLD_MATRIX)
        frozen = rows(frozen_blob, INHERITED_IDS, "freeze matrix")
        baseline_blob = git.blob(BASE, OLD_MATRIX)
        report["freeze_to_base"] = compare_rows(frozen, rows(baseline_blob, INHERITED_IDS, "base matrix"), "base")
        old_live, new_live = (repo / OLD_MATRIX).read_bytes(), (repo / NEW_MATRIX).read_bytes()
        report["freeze_to_live_old"] = compare_rows(frozen, rows(old_live, INHERITED_IDS, "live old matrix"), "live old")
        report["freeze_to_live_repair"] = compare_rows(frozen, rows(new_live, INHERITED_IDS + REPAIR_IDS, "live repair matrix"), "live repair")
        proof = (repo / PROOF_IDENTITY).read_bytes()
        fields = read_json(git.blob(BASE, FIELDS), FIELDS)
        consumers = git.blob(BASE, OPTIMIZATION + "Consumers.lean")
        report["field_types"] = check_field_inventory(fields, proof, consumers)
        root_inventory = read_json(git.blob(BASE, ROOTS), ROOTS)
        require(len(root_inventory["Names"]) == 93 and len(set(root_inventory["Names"])) == 93, "AXIOM_ROOTS", root_inventory)
        report["axiom_root_count"] = 93
        report["controls"] = run_controls(frozen, old_live, new_live, baseline, fields, proof, consumers)
        report["expected_controls"] = list(CONTROL_IDS)
        report["executed_controls"] = [case["id"] for case in report["controls"]]
        if not args.self_test_only:
            candidate = git.tree(args.candidate_ref)
            report["protected_identity"] = check_protected(baseline, candidate)
            candidate_old = git.blob(args.candidate_ref, OLD_MATRIX)
            require(candidate_old == baseline_blob, "OLD_MATRIX_BLOB_BYTES", OLD_MATRIX)
            report["old_matrix_entire_blob_equal"] = True
            report["freeze_to_candidate_old"] = compare_rows(frozen, rows(candidate_old, INHERITED_IDS, "candidate old matrix"), "candidate old")
            candidate_new = git.blob(args.candidate_ref, NEW_MATRIX)
            candidate_new_rows = rows(candidate_new, INHERITED_IDS + REPAIR_IDS, "candidate repair matrix")
            report["freeze_to_candidate_repair"] = compare_rows(frozen, candidate_new_rows, "candidate repair")
            live_new_rows = rows(new_live, INHERITED_IDS + REPAIR_IDS, "live repair matrix")
            require(all(candidate_new_rows[key] == live_new_rows[key] for key in INHERITED_IDS + REPAIR_IDS),
                    "CANDIDATE_LIVE_ROW_BYTES", "candidate/live repair rows differ")
            candidate_proof = git.blob(args.candidate_ref, PROOF_IDENTITY)
            report["candidate_field_types"] = check_field_inventory(fields, candidate_proof, consumers)
            # Ordinary Git blob identity is checked separately from raw row-byte
            # equality, permitting the repository's declared checkout newline
            # conversion while rejecting semantic/other live protected edits.
            dirty = git.run(["diff", "--no-ext-diff", "--name-only", "-z", args.candidate_ref,
                             "--", *PROTECTED_SCOPES])
            changed_protected = [strict_text(path, "protected diff") for path in dirty.split(b"\0")
                                 if path and not strict_text(path, "protected diff").startswith(REPAIR_ROOT)]
            require(not changed_protected, "LIVE_PROTECTED_DIFF", changed_protected)
            untracked = git.run(["ls-files", "--others", "--exclude-standard", "-z", "--", *PROTECTED_SCOPES])
            unexpected_live = [strict_text(path, "untracked protected") for path in untracked.split(b"\0")
                               if path and not strict_text(path, "untracked protected").startswith(REPAIR_ROOT)]
            require(not unexpected_live, "LIVE_PROTECTED_ADDITION", unexpected_live)
            index = git.run(["ls-files", "--stage", "-z", "--", *PROTECTED_SCOPES])
            index_map = {}
            for entry in index.split(b"\0"):
                if not entry:
                    continue
                header, path = entry.split(b"\t", 1)
                mode, oid, stage = header.decode("ascii").split()
                name = strict_text(path, "index")
                require(stage == "0" and name not in index_map, "INDEX_STAGE", name)
                index_map[name] = (mode, "blob", oid)
            report["index_protected_identity"] = check_protected(baseline, index_map)
            report["candidate_receipt_scope"] = "Final supplied candidate Git blobs plus live historical/repair row bytes and protected index/live checks"
        else:
            report["candidate_receipt_scope"] = "Development selftests only; candidate repair Git blobs not certified"
        report["status"] = "PASS"
    except Exception as exc:
        report["status"] = "FAIL"
        report["failure"] = {"code": getattr(exc, "code", type(exc).__name__), "detail": str(exc)}
    finally:
        if before is not None:
            try:
                after = source_snapshot(repo, watched)
                report["live_after"] = after
                report["live_bytes_unchanged"] = before == after
                if before != after:
                    report["status"] = "FAIL"
                    report["restoration_failure"] = [name for name in before if before[name] != after.get(name)]
            except Exception as exc:
                report["status"] = "FAIL"
                report["restoration_failure"] = str(exc)
        if index_before is not None:
            try:
                index_after = git.run(["ls-files", "--stage", "-z", "--", *PROTECTED_SCOPES])
                report["index_after_sha256"] = sha(index_after)
                report["index_bytes_unchanged"] = index_before == index_after
                if index_before != index_after:
                    report["status"] = "FAIL"
                    report["index_restoration_failure"] = "Protected and matrix/proof index entries changed during the check"
            except Exception as exc:
                report["status"] = "FAIL"
                report["index_restoration_failure"] = str(exc)
        report["git_processes"] = git.receipts
        report["duration_seconds"] = time.monotonic() - started
        report["checker_sha256"] = sha(Path(__file__).read_bytes())
        report["registry_sha256"] = sha(Path(__file__).with_name("registry.json").read_bytes())
        (output / "result.json").write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(f"OPT1-R1-PRESERVATION {report['status']} selftest={args.self_test_only} controls={len(report.get('controls', []))}/{len(CONTROL_IDS)}")
    if report["status"] != "PASS":
        print(json.dumps(report.get("failure") or report.get("restoration_failure") or
                         report.get("index_restoration_failure"), ensure_ascii=False), file=sys.stderr)
    return 0 if report["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
