#!/usr/bin/env python3
"""Verify LIFE-1-R2 contract preservation and replay exact in-memory P/Q controls.

Rows include every original byte except the LF record delimiter. No CR, Unicode,
whitespace, or cell normalization establishes row equality. This proves contract
preservation only; historical evidence cells do not establish current acceptance.
The default writes the owned compact receipt; --check writes no files.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass, replace
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time


BASE = "0485a64920a273d0830b926ee46275085222819d"
DIRECTORY = "docs/internal/extensions/lifecycle1"
REPAIR = DIRECTORY + "/repair-r2"
MARKER = b"<!-- APPEND-ONLY-EVIDENCE -->"
HEADER = (b"| ID | Exact frozen requirement | Scope | Evidence needed (exact proposition/check) | "
          b"Named consumer and identity/composition chain | Anti-vacuity challenge attempted and outcome | "
          b"Evidence obtained | Status / residual gap |")
SEPARATOR = b"| --- | --- | --- | --- | --- | --- | --- | --- |"
IDS = tuple(f"L1-{i:02}" for i in range(1, 21)) + (
    "INV-STORE-IDENTITY", "INV-VALUE-DEPENDENCY", "INV-SEMANTIC-NONVACUITY",
    "INV-TRACE-EXECUTION", "INV-STORE-AGREEMENT", "INV-READ-BACKING",
    "INV-WORD-WIDTH", "INV-ADDRESS-WIDTH", "INV-INSTRUCTION-ATOMICITY",
    "INV-PROGRAM-ACCOUNTING", "INV-ORACLE-INDEPENDENCE", "INV-VALIDATION-REACH",
    "INV-ALL-SIZE", "INV-PROOF-SEPARATION", "INV-NO-SYNTHETIC",
    "INV-CATEGORY-SEPARATION", "INV-PUBLIC-COMPOSITION", "INV-CERTIFICATE-ANTI-BYPASS",
    "INV-MUTATION-REPRODUCIBILITY", "INV-GLOBAL-PHYSICAL-MACHINE", "INV-WIDTH-SCALING",
    "CHK-FINAL", "CHK-SCOPE", "L1R1-SELECTOR", "L1R1-CLEANUP",
    "L1R2-CONTRACT-BYTES", "L1R2-HASH",
)
INHERITED_IDS = IDS[:45]
ORIGINAL_IDS = IDS[:43]
ID_PATTERN = r"(?:L1-[0-9]{2}|INV-[A-Z-]+|CHK-[A-Z-]+|L1R[12]-[A-Z-]+)"
PINS = {
    "contract": (23564, "cf7b4e3b7d6124b03ea28f9b05d79ee3288f8e7c7c39ee409b0263c4d147befc"),
    "prompt": (42538, "18ae1f54dcb8036416ef1b6b7ab2922a816698d22da514a02511653b7ff82873"),
    "frozen": (49039, "ad03e9572fff3c630bae7b80f2235d03302d2ab48fadfcc2c6e180c489b975c2"),
    "base_frozen": (46220, "ae991367ef537d61d5af0ef738aad3b7ee1693e22a1ed27469d83a3de65f6417"),
    "base_contract": (19880, "25a1a4550548280950d7e7dbc01fb910321ed261c11ff129bfe92f1f20b78dc6"),
    "base_prompt": (46684, "b434dd888190a1fe31a13bd1981a0f25bd3af78dd4f10f9dc7077339f56ede9b"),
    "original_contract": (53962, "5bd95d24b6cffaf9fb39abb2aa04cca9743aed7884b3f87d03d7428e6b9cd8eb"),
    "original_prompt": (33909, "f82a24460dfa06602fc52e2c78b0fa8402fbb84a0d203b4abb95040fa56b0c18"),
}
# Independent fixed registry; constructors below must reproduce this exact order.
CONTROL_REGISTRY = (
    ("CONTRACT-POSITIVE", "PASS"),
    ("CONTRACT-APPEND-POSITIVE", "PASS"),
    ("CONTRACT-MISSING-MIDDLE", "ID_MISSING"),
    ("CONTRACT-DUPLICATE-MIDDLE", "ID_DUPLICATE"),
    ("CONTRACT-UNKNOWN-ID", "ID_UNKNOWN"),
    ("CONTRACT-ORDER", "ID_ORDER"),
    ("CONTRACT-LATE-REQUIREMENT", "REQUIREMENT"),
    ("CONTRACT-LATE-INHERITED-CELL", "INHERITED_ROW_BYTES"),
    ("CONTRACT-EVIDENCE-CELL", "INHERITED_ROW_BYTES"),
    ("CONTRACT-NEW-ROW-CELL", "ROW_BYTES"),
    ("CONTRACT-EMPTY-CELL", "COLUMNS"),
    ("CONTRACT-MOJIBAKE", "MOJIBAKE"),
    ("CONTRACT-BAD-UTF8", "UTF8"),
    ("CONTRACT-LATE-DUPLICATE", "EVIDENCE_ROW"),
    ("CONTRACT-LATE-UNKNOWN", "EVIDENCE_ROW"),
    ("CONTRACT-PREFIX", "PREFIX_BYTES"),
    ("CONTRACT-FROZEN-LATE-CELL", "INHERITED_ROW_BYTES"),
    ("CONTRACT-PROMPT-LATE-CLAUSE", "REQUIREMENT"),
    ("CONTRACT-PROMPT-BYTES", "PIN"),
    ("CONTRACT-EXTERNAL-PROMPT", "EXTERNAL_PROMPT"),
    ("CONTRACT-SOURCE-SUBSTITUTION", "PIN"),
    ("CONTRACT-PREDICATE-SUBSTITUTION", "ROW_BYTES"),
)


class Rejection(Exception):
    def __init__(self, code: str, detail: str):
        super().__init__(detail)
        self.code = code


def require(condition: bool, code: str, detail: str) -> None:
    if not condition:
        raise Rejection(code, detail)


def identity(data: bytes) -> dict:
    return {"bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}


def strict(data: bytes, origin: str) -> str:
    try:
        text = data.decode("utf-8", errors="strict")
    except UnicodeDecodeError as error:
        raise Rejection("UTF8", f"{origin}: {error}") from error
    require(not text.startswith("\ufeff"), "UTF8", f"{origin}: UTF-8 BOM is not allowed")
    require(not any(bad in text for bad in ("\u00c2\u00ac", "\u00e2\u20ac", "\ufffd")),
            "MOJIBAKE", f"{origin}: recognizable mojibake")
    return text


def pin(data: bytes, name: str) -> None:
    size, sha = PINS[name]
    require(len(data) == size and identity(data)["sha256"] == sha,
            "PIN", f"{name}: exact frozen byte identity changed")


def object_pairs(pairs: list[tuple]) -> dict:
    result = {}
    for key, value in pairs:
        require(key not in result, "JSON_DUPLICATE", f"duplicate JSON key: {key}")
        result[key] = value
    return result


def load_json(data: bytes, origin: str) -> dict:
    try:
        value = json.loads(strict(data, origin), object_pairs_hook=object_pairs)
    except json.JSONDecodeError as error:
        raise Rejection("JSON", f"{origin}: {error}") from error
    require(isinstance(value, dict), "JSON", f"{origin}: root object required")
    return value


def require_ids(actual: tuple | list, expected: tuple, origin: str) -> None:
    seen = set()
    for key in actual:
        require(key in expected, "ID_UNKNOWN", f"{origin}: {key}")
        require(key not in seen, "ID_DUPLICATE", f"{origin}: {key}")
        seen.add(key)
    require(len(actual) == len(expected), "ID_MISSING", f"{origin}: missing {sorted(set(expected) - seen)}")
    require(tuple(actual) == expected, "ID_ORDER", f"{origin}: ordered IDs differ")


@dataclass(frozen=True)
class Row:
    key: str
    cells: tuple[str, ...]
    raw: bytes


def rows(data: bytes, expected: tuple, origin: str) -> tuple[Row, ...]:
    strict(data, origin)
    require(data.count(MARKER) == 1, "MARKER", f"{origin}: exactly one append-only marker required")
    prefix, suffix = data.split(MARKER)
    lines = prefix.split(b"\n")
    require(lines.count(HEADER) == 1 and lines.count(SEPARATOR) == 1,
            "HEADER", f"{origin}: exact eight-column header and separator required")
    result = []
    for line in lines:
        if not line.startswith(b"|") or line in (HEADER, SEPARATOR):
            continue
        parts = line.decode("utf-8").split("|")
        require(len(parts) == 10 and parts[0] == "" and parts[-1] == "",
                "COLUMNS", f"{origin}: not exactly eight columns")
        cells = tuple(part.strip() for part in parts[1:9])
        require(all(cells), "COLUMNS", f"{origin}: empty cell")
        require(re.fullmatch(r"`[A-Z0-9-]+`", cells[0]) is not None,
                "ID_FORMAT", f"{origin}: invalid ID cell {cells[0]!r}")
        result.append(Row(cells[0][1:-1], cells, line))
    require_ids([row.key for row in result], expected, origin)
    require(re.search(rb"(?m)^\|[ \t]*`?[A-Z][A-Z0-9-]*`?[ \t]*\|", suffix) is None,
            "EVIDENCE_ROW", f"{origin}: acceptance-shaped row after append-only marker")
    return tuple(result)


def prompt_requirements(data: bytes, expected: tuple, origin: str) -> dict[str, str]:
    text = strict(data, origin)
    matches = list(re.finditer(r"(?m)^- (" + ID_PATTERN + r"): ([^\r\n]*(?:\r?\n[ \t]+[^\r\n]+)*)", text))
    require_ids([match[1] for match in matches], expected, origin)
    # Joining wrapped source lines matches the original frozen extractor. Rows
    # themselves are never reconstructed from these parsed/trimmed cell values.
    return {match[1]: " ".join(line.strip() for line in match[2].splitlines()) for match in matches}


@dataclass(frozen=True)
class Inputs:
    active: bytes
    frozen: bytes
    prompt: bytes
    contract: bytes
    base_frozen: bytes
    base_contract: bytes
    base_prompt: bytes
    original_contract: bytes
    external_prompt: bytes | None = None
    external_original_prompt: bytes | None = None


def verify(inputs: Inputs) -> dict:
    """Sole production verdict predicate, called unchanged by every P and Q."""
    active = rows(inputs.active, IDS, "active")
    frozen = rows(inputs.frozen, IDS, "frozen")
    inherited = rows(inputs.base_frozen, INHERITED_IDS, "base Git R1 frozen matrix")
    contract = load_json(inputs.contract, "R2 contract")
    old = load_json(inputs.base_contract, "base Git R1 contract")
    original = load_json(inputs.original_contract, "base Git original contract")
    require(contract["base"] == BASE, "BASE", "R2 contract base differs")
    require_ids(contract["orderedIds"], IDS, "R2 contract IDs")
    require_ids([item["id"] for item in contract["requirements"]], IDS, "R2 contract requirements")
    require_ids(old["orderedIds"], INHERITED_IDS, "R1 contract IDs")
    require_ids(list(old["requirements"]), INHERITED_IDS, "R1 contract requirements")
    require_ids(original["expected_ids"], ORIGINAL_IDS, "original contract IDs")
    require_ids([item["id"] for item in original["requirements"]], ORIGINAL_IDS, "original requirements")
    prompt = prompt_requirements(inputs.prompt, IDS, "R2 prompt")
    base_prompt = prompt_requirements(inputs.base_prompt, INHERITED_IDS, "base Git R1 prompt")
    original_bytes = original["source_prompt"]["text"].encode("utf-8")
    original_prompt = prompt_requirements(original_bytes, ORIGINAL_IDS, "original embedded prompt")
    pin(original_bytes, "original_prompt")
    require(original["source_prompt"]["sha256"] == PINS["original_prompt"][1],
            "PROMPT_HASH", "original embedded prompt metadata differs")
    requirements = {item["id"]: item["requirement"] for item in contract["requirements"]}
    original_requirements = {item["id"]: item["requirement"] for item in original["requirements"]}
    comparisons = []
    for i, key in enumerate(IDS):
        require(requirements[key] == frozen[i].cells[1] == active[i].cells[1] == prompt[key],
                "REQUIREMENT", f"{key}: full requirement differs from R2 source prompt")
        if i < len(INHERITED_IDS):
            require(old["requirements"][key] == inherited[i].cells[1] == base_prompt[key] == prompt[key],
                    "REQUIREMENT", f"{key}: inherited full requirement differs from R1 source")
            require(frozen[i].raw == inherited[i].raw and active[i].raw == inherited[i].raw,
                    "INHERITED_ROW_BYTES", f"{key}: inherited complete row bytes differ from base Git blob")
        if i < len(ORIGINAL_IDS):
            require(original_requirements[key] == original_prompt[key] == prompt[key],
                    "REQUIREMENT", f"{key}: inherited full requirement differs from original source")
        require(active[i].raw == frozen[i].raw, "ROW_BYTES", f"{key}: full active/frozen row bytes differ")
        comparisons.append({"id": key, "activeEqualsFrozen": True,
                            "activeAndFrozenEqualBaseGit": True if i < 45 else None,
                            "fullRequirementEqualsPrompt": True,
                            "row": identity(active[i].raw),
                            "requirement": identity(prompt[key].encode("utf-8"))})
    require(inputs.active.startswith(inputs.frozen), "PREFIX_BYTES", "active matrix changed immutable frozen prefix")
    # Pin after the semantic comparisons so mutation receipts identify the exact
    # violated relation. These pins also prevent coordinated source substitution.
    for name in ("base_frozen", "base_contract", "base_prompt", "original_contract", "prompt", "frozen", "contract"):
        pin(getattr(inputs, name), name)
    for name, metadata in (("prompt", "prompt"), ("frozen", "frozen"), ("base_frozen", "originalFrozenGit")):
        require(contract[metadata] == identity(getattr(inputs, name)), "IDENTITY", f"R2 contract {name} metadata differs")
    for data, expected, origin in (
        (inputs.external_prompt, inputs.prompt, "external R2 prompt"),
        (inputs.external_original_prompt, original_bytes, "external original prompt"),
    ):
        if data is not None:
            strict(data, origin)
            require(data == expected, "EXTERNAL_PROMPT", f"{origin}: bytes differ")
    return {"status": "PASS", "rows": 47, "inheritedRows": 45, "columns": 8,
            "changedInheritedIds": [], "orderedIds": list(IDS), "perRow": comparisons,
            "rowByteEquality": "complete UTF-8 row content, LF delimiter excluded; no normalization",
            "immutablePrefix": True,
            "inheritedEvidenceStatus": "historical cells preserved; acceptance not inferred"}


def replace_cell(data: bytes, key: str, index: int, value: str, expected: tuple = IDS) -> bytes:
    row = next(row for row in rows(data, expected, "mutation seed") if row.key == key)
    parts = row.raw.split(b"|")
    parts[index + 1] = b" " + value.encode("utf-8") + b" "
    return data.replace(row.raw, b"|".join(parts), 1)


def controls(seed: Inputs) -> list[tuple[str, str, Inputs]]:
    seed_rows = rows(seed.active, IDS, "control seed")
    middle = seed_rows[21].raw
    remove = seed.active.replace(middle + b"\n", b"", 1)
    duplicate = seed.active.replace(middle + b"\n", middle + b"\n" + middle + b"\n", 1)
    requirement = next(row.cells[1] for row in seed_rows if row.key == "L1-04")
    changed_requirement = replace_cell(seed.active, "L1-04", 1,
                                     requirement.replace("must not satisfy output provenance.", "may satisfy output provenance."))
    first, second = seed_rows[9].raw, seed_rows[10].raw
    reordered = seed.active.replace(first + b"\n" + second, second + b"\n" + first, 1)
    forged_source = replace(seed,
        active=replace_cell(seed.active, "L1R1-CLEANUP", 3, "Substituted source predicate."),
        frozen=replace_cell(seed.frozen, "L1R1-CLEANUP", 3, "Substituted source predicate."),
        base_frozen=replace_cell(seed.base_frozen, "L1R1-CLEANUP", 3, "Substituted source predicate.", INHERITED_IDS))
    return [
        ("CONTRACT-POSITIVE", "PASS", seed),
        ("CONTRACT-APPEND-POSITIVE", "PASS", replace(seed, active=seed.active + b"\n## Evidence for L1-01\nReceipt remains append-only.\n")),
        ("CONTRACT-MISSING-MIDDLE", "ID_MISSING", replace(seed, active=remove)),
        ("CONTRACT-DUPLICATE-MIDDLE", "ID_DUPLICATE", replace(seed, active=duplicate)),
        ("CONTRACT-UNKNOWN-ID", "ID_UNKNOWN", replace(seed, active=seed.active.replace(b"`L1-11`", b"`L1-99`", 1))),
        ("CONTRACT-ORDER", "ID_ORDER", replace(seed, active=reordered)),
        ("CONTRACT-LATE-REQUIREMENT", "REQUIREMENT", replace(seed, active=changed_requirement)),
        ("CONTRACT-LATE-INHERITED-CELL", "INHERITED_ROW_BYTES", replace(seed, active=replace_cell(seed.active, "L1R1-CLEANUP", 7, "Closed without evidence."))),
        ("CONTRACT-EVIDENCE-CELL", "INHERITED_ROW_BYTES", replace(seed, active=replace_cell(seed.active, "L1-04", 6, "Changed evidence cell."))),
        ("CONTRACT-NEW-ROW-CELL", "ROW_BYTES", replace(seed, active=replace_cell(seed.active, "L1R2-HASH", 7, "Closed without replay."))),
        ("CONTRACT-EMPTY-CELL", "COLUMNS", replace(seed, active=replace_cell(seed.active, "L1-10", 6, ""))),
        ("CONTRACT-MOJIBAKE", "MOJIBAKE", replace(seed, active=seed.active + "\n\u00c2\u00ac\n".encode("utf-8"))),
        ("CONTRACT-BAD-UTF8", "UTF8", replace(seed, active=seed.active + b"\n\xff\n")),
        ("CONTRACT-LATE-DUPLICATE", "EVIDENCE_ROW", replace(seed, active=seed.active + b"\n" + middle + b"\n")),
        ("CONTRACT-LATE-UNKNOWN", "EVIDENCE_ROW", replace(seed, active=seed.active + b"\n" + middle.replace(b"INV-VALUE-DEPENDENCY", b"UNUSED-CONTROL") + b"\n")),
        ("CONTRACT-PREFIX", "PREFIX_BYTES", replace(seed, active=seed.active.replace(b"# LIFE-1-R2", b"# LIFE-1-R3", 1))),
        ("CONTRACT-FROZEN-LATE-CELL", "INHERITED_ROW_BYTES", replace(seed, frozen=replace_cell(seed.frozen, "CHK-SCOPE", 7, "Changed frozen final cell."))),
        ("CONTRACT-PROMPT-LATE-CLAUSE", "REQUIREMENT", replace(seed, prompt=seed.prompt.replace(b"an unrelated source cell with the same value must not satisfy output provenance.", b"an unrelated source cell with the same value may satisfy output provenance.", 1))),
        ("CONTRACT-PROMPT-BYTES", "PIN", replace(seed, prompt=seed.prompt + b"\n")),
        ("CONTRACT-EXTERNAL-PROMPT", "EXTERNAL_PROMPT", replace(seed, external_prompt=seed.prompt + b"\n")),
        ("CONTRACT-SOURCE-SUBSTITUTION", "PIN", forged_source),
        ("CONTRACT-PREDICATE-SUBSTITUTION", "ROW_BYTES", replace(seed, active=replace_cell(seed.active, "L1R2-HASH", 3, "True"))),
    ]


def self_test(seed: Inputs, only: str | None = None) -> list[dict]:
    cases = controls(seed)
    require(tuple((key, expected) for key, expected, _ in cases) == CONTROL_REGISTRY,
            "CONTROL_REGISTRY", "constructors differ from exact ordered control registry")
    if only is not None:
        require(only in {key for key, _ in CONTROL_REGISTRY}, "CONTROL_UNKNOWN", f"unknown exact control: {only!r}")
        cases = [case for case in cases if case[0] == only]
        require(len(cases) == 1, "CONTROL_CARDINALITY", "focused control must execute exactly one ID")
    results = []
    for key, expected, challenged in cases:
        changed = {name: identity(getattr(challenged, name)) for name in Inputs.__dataclass_fields__
                   if getattr(challenged, name) != getattr(seed, name) and getattr(challenged, name) is not None}
        require(key == "CONTRACT-POSITIVE" or bool(changed), "CONTROL_NO_MUTATION", f"{key}: unchanged negative seed")
        started = time.monotonic()
        try:
            verify(challenged)
            observed, detail = "PASS", "same verifier accepted"
        except Rejection as error:
            observed, detail = error.code, str(error)
        # Unexpected exceptions are never accepted as the expected rejection.
        results.append({"id": key, "expected": expected, "observed": observed,
                        "status": "PASS" if observed == expected else "FAIL", "detail": detail,
                        "changedInputs": changed, "elapsedSeconds": round(time.monotonic() - started, 6)})
        require(observed == expected, "SELF_TEST", f"{key}: expected {expected}, observed {observed}")
    return results


def git_blob(root: Path, relative: str, receipts: list) -> bytes:
    command = ["git", "cat-file", "blob", f"{BASE}:{relative}"]
    started = time.monotonic()
    try:
        result = subprocess.run(command, cwd=root, capture_output=True, timeout=30, check=False)
    except subprocess.TimeoutExpired as error:
        receipts.append({"command": command, "deadlineSeconds": 30, "timedOut": True,
                         "stdout": identity(error.stdout or b""), "stderr": identity(error.stderr or b"")})
        raise Rejection("GIT_TIMEOUT", relative) from error
    receipts.append({"command": command, "deadlineSeconds": 30, "timedOut": False,
                     "elapsedSeconds": round(time.monotonic() - started, 6), "exitCode": result.returncode,
                     "stdout": identity(result.stdout), "stderr": identity(result.stderr),
                     "stderrText": result.stderr.decode("utf-8", errors="replace")})
    require(result.returncode == 0, "GIT", f"cannot read exact base blob: {relative}")
    return result.stdout


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repository-root", type=Path, default=Path(__file__).resolve().parents[5])
    parser.add_argument("--matrix", type=Path)
    parser.add_argument("--external-prompt", type=Path, help="optional exact R2 launch prompt")
    parser.add_argument("--external-original-prompt", type=Path, help="optional exact original LIFE-1 prompt")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--self-test", action="store_true", help="replay all 22 controls (also the default)")
    mode.add_argument("--only-control", help="execute exactly one fixed control; empty/unknown rejects")
    output = parser.add_mutually_exclusive_group()
    output.add_argument("--check", action="store_true", help="read-only; full receipt on stdout, no writes")
    output.add_argument("--output", type=Path, help="owned receipt or a JSON path under this worktree .lake/repair-r2")
    args = parser.parse_args()
    root = args.repository_root.resolve()
    directory = root / REPAIR
    destination = (args.output or directory / "CONTRACT_VERIFICATION.json").resolve()
    allowed_receipt = Path(__file__).resolve().with_name("CONTRACT_VERIFICATION.json")
    allowed_scratch = Path(__file__).resolve().parents[5] / ".lake/repair-r2"
    if not args.check and not (destination == allowed_receipt or
                              (destination.is_relative_to(allowed_scratch.resolve()) and destination.suffix == ".json")):
        parser.error("output must be the owned R2 receipt or a .json file under this worktree .lake/repair-r2")
    started = time.monotonic()
    receipt = {"schema": "life1-r2-contract-verification-v1", "base": BASE, "repositoryRoot": str(root),
               "startedUtc": datetime.now(timezone.utc).isoformat(), "gitReads": [],
               "scope": "contract-byte preservation only; no theorem or campaign acceptance"}
    try:
        paths = {"active": (args.matrix or directory / "ACCEPTANCE_MATRIX.md").resolve(),
                 "frozen": directory / "ACCEPTANCE_MATRIX.frozen.md", "prompt": directory / "PROMPT.md",
                 "contract": directory / "CONTRACT.json"}
        if args.external_prompt:
            paths["external_prompt"] = args.external_prompt.resolve()
        if args.external_original_prompt:
            paths["external_original_prompt"] = args.external_original_prompt.resolve()
        require(args.check or destination not in paths.values(), "OUTPUT_PATH", "receipt cannot overwrite an input")
        contents = {name: path.read_bytes() for name, path in paths.items()}
        blob_paths = {"base_frozen": DIRECTORY + "/repair-r1/ACCEPTANCE_MATRIX.frozen.md",
                      "base_contract": DIRECTORY + "/repair-r1/CONTRACT.json",
                      "base_prompt": DIRECTORY + "/repair-r1/PROMPT.md",
                      "original_contract": DIRECTORY + "/CONTRACT_REQUIREMENTS.json"}
        blobs = {name: git_blob(root, relative, receipt["gitReads"]) for name, relative in blob_paths.items()}
        inputs = Inputs(**contents, **blobs)
        receipt["inputs"] = {name: identity(getattr(inputs, name)) for name in Inputs.__dataclass_fields__
                             if getattr(inputs, name) is not None}
        receipt["inputPaths"] = {name: str(path) for name, path in paths.items()}
        receipt["verdict"] = verify(inputs)
        receipt["controlRegistry"] = [{"id": key, "expected": expected} for key, expected in CONTROL_REGISTRY]
        receipt["controls"] = self_test(inputs, args.only_control)
        receipt["controlSummary"] = {"selected": len(receipt["controls"]),
                                     "expectedAccept": sum(row["expected"] == "PASS" for row in receipt["controls"]),
                                     "expectedReject": sum(row["expected"] != "PASS" for row in receipt["controls"]),
                                     "allMatched": True, "predicate": "verify(Inputs)"}
        receipt["inputFilesUnchanged"] = all(path.read_bytes() == contents[name] for name, path in paths.items())
        require(receipt["inputFilesUnchanged"], "SOURCE_CHANGED", "input file changed during verification")
        receipt["status"] = "PASS"
    except (Rejection, OSError, KeyError, TypeError, ValueError, StopIteration) as error:
        receipt["status"] = "FAIL"
        receipt["error"] = {"code": error.code if isinstance(error, Rejection) else "INPUT", "detail": str(error)}
    receipt["elapsedSeconds"] = round(time.monotonic() - started, 6)
    receipt["verifier"] = {"path": str(Path(__file__).resolve()), **identity(Path(__file__).read_bytes())}
    receipt["python"] = {"path": sys.executable, "version": sys.version, **identity(Path(sys.executable).read_bytes())}
    git_path = shutil.which("git")
    if git_path:
        receipt["git"] = {"path": git_path, **identity(Path(git_path).read_bytes())}
    receipt["readOnly"] = args.check
    serialized = json.dumps(receipt, ensure_ascii=True, separators=(",", ":")) + "\n"
    if args.check:
        print(serialized, end="")
    else:
        destination.write_bytes(serialized.encode("utf-8"))
        print(json.dumps({"status": receipt["status"], "output": str(destination),
                          "receipt": identity(serialized.encode("utf-8")),
                          "controls": receipt.get("controlSummary"), "error": receipt.get("error")}))
    return 0 if receipt["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
