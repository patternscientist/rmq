#!/usr/bin/env python3
"""Read-only LIFE-1-R1 contract check; --self-test replays exact byte mutations.

Row bytes exclude the LF record delimiter; no CR, whitespace, Unicode, or cell
normalization is permitted in a row comparison. Only wrapped source-prompt
requirements are joined, exactly as in the original contract extractor.
This checks preservation of requirements, not satisfaction of their claims.
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


BASE = "12bd7f0fc2c87f2c9bdef3825bd92477e48e3433"
DIRECTORY = "docs/internal/extensions/lifecycle1"
REPAIR = DIRECTORY + "/repair-r1"
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
)
OLD_IDS = IDS[:43]
ID_PATTERN = r"(?:L1-[0-9]{2}|INV-[A-Z-]+|CHK-[A-Z-]+|L1R1-[A-Z-]+)"
PINS = {
    "contract": (19880, "25a1a4550548280950d7e7dbc01fb910321ed261c11ff129bfe92f1f20b78dc6"),
    "prompt": (46684, "b434dd888190a1fe31a13bd1981a0f25bd3af78dd4f10f9dc7077339f56ede9b"),
    "frozen": (46220, "ae991367ef537d61d5af0ef738aad3b7ee1693e22a1ed27469d83a3de65f6417"),
    "base_frozen": (43437, "8b08e2d7c7f284634d88bfa4262ee447f79a401c78b27dc346ea34d76ccba4a7"),
    "original_prompt": (33909, "f82a24460dfa06602fc52e2c78b0fa8402fbb84a0d203b4abb95040fa56b0c18"),
}
# This ordered registry is independent of the mutation constructors below.
# Each ID consumes verify(Inputs); the versioned source fixes its exact P/Q.
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
)


class Rejection(Exception):
    def __init__(self, code: str, detail: str):
        super().__init__(detail)
        self.code = code
        self.detail = detail


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
        return json.loads(strict(data, origin), object_pairs_hook=object_pairs)
    except json.JSONDecodeError as error:
        raise Rejection("JSON", f"{origin}: {error}") from error


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
    # Inspect the entire append area, not just the first 45 records. Evidence
    # headings and 'Evidence for ...' table cells are allowed; new ID rows are not.
    require(re.search(rb"(?m)^\|[ \t]*`?[A-Z][A-Z0-9-]*`?[ \t]*\|", suffix) is None,
            "EVIDENCE_ROW", f"{origin}: acceptance-shaped row after append-only marker")
    return tuple(result)


def prompt_requirements(data: bytes, expected: tuple, origin: str) -> dict[str, str]:
    text = strict(data, origin)
    matches = list(re.finditer(r"(?m)^- (" + ID_PATTERN + r"): ([^\r\n]*(?:\r?\n[ \t]+[^\r\n]+)*)", text))
    require_ids([match[1] for match in matches], expected, origin)
    return {match[1]: " ".join(line.strip() for line in match[2].splitlines()) for match in matches}


@dataclass(frozen=True)
class Inputs:
    active: bytes
    frozen: bytes
    prompt: bytes
    contract: bytes
    base_frozen: bytes
    base_contract: bytes
    external_prompt: bytes | None = None
    external_original_prompt: bytes | None = None


def verify(inputs: Inputs) -> dict:
    """The sole production verdict predicate, also consumed by every control."""
    active = rows(inputs.active, IDS, "active")
    frozen = rows(inputs.frozen, IDS, "frozen")
    original = rows(inputs.base_frozen, OLD_IDS, "base Git frozen matrix")
    contract = load_json(inputs.contract, "repair contract")
    old_contract = load_json(inputs.base_contract, "base Git contract")
    require(contract["base"] == BASE, "BASE", "repair contract base differs")
    require_ids(contract["orderedIds"], IDS, "repair contract IDs")
    require_ids(list(contract["requirements"]), IDS, "repair contract requirements")
    require_ids(old_contract["expected_ids"], OLD_IDS, "base contract IDs")
    require_ids([row["id"] for row in old_contract["requirements"]], OLD_IDS, "base contract requirements")
    prompt = prompt_requirements(inputs.prompt, IDS, "repair prompt")
    original_prompt = old_contract["source_prompt"]["text"].encode("utf-8")
    old_prompt = prompt_requirements(original_prompt, OLD_IDS, "original embedded prompt")
    old_requirements = {row["id"]: row["requirement"] for row in old_contract["requirements"]}
    pin(original_prompt, "original_prompt")
    require(old_contract["source_prompt"]["sha256"] == PINS["original_prompt"][1],
            "PROMPT_HASH", "original embedded prompt metadata differs")
    for i, key in enumerate(IDS):
        values = (contract["requirements"][key], frozen[i].cells[1], active[i].cells[1])
        require(all(value == prompt[key] for value in values), "REQUIREMENT",
                f"{key}: full requirement differs from repair source prompt")
        if i < len(OLD_IDS):
            require(old_requirements[key] == original[i].cells[1] == old_prompt[key] == prompt[key],
                    "REQUIREMENT", f"{key}: inherited full requirement differs from original source")
            require(frozen[i].raw == original[i].raw and active[i].raw == original[i].raw,
                    "INHERITED_ROW_BYTES", f"{key}: inherited complete row bytes differ from base Git blob")
        require(active[i].raw == frozen[i].raw, "ROW_BYTES", f"{key}: full active/frozen row bytes differ")
    require(inputs.active.startswith(inputs.frozen), "PREFIX_BYTES", "active matrix changed immutable frozen prefix")
    for name in ("prompt", "frozen", "base_frozen"):
        data = getattr(inputs, name)
        pin(data, name)
        metadata = contract[{"base_frozen": "originalFrozenGit"}.get(name, name)]
        require(metadata == identity(data), "IDENTITY", f"contract {name} metadata differs")
    pin(inputs.contract, "contract")
    for data, expected, origin in (
        (inputs.external_prompt, inputs.prompt, "external repair prompt"),
        (inputs.external_original_prompt, original_prompt, "external original prompt"),
    ):
        if data is not None:
            strict(data, origin)
            require(data == expected, "EXTERNAL_PROMPT", f"{origin}: bytes differ")
    return {"status": "PASS", "rows": len(active), "columns": 8, "changedInheritedIds": [],
            "orderedIds": list(IDS), "sourceRequirementEquality": "complete text",
            "rowByteEquality": "complete UTF-8 row content, LF delimiter excluded; no normalization",
            "immutablePrefix": True, "inheritedEvidenceStatus": "historical cells preserved; closure not inferred"}


def replace_cell(data: bytes, key: str, index: int, value: str) -> bytes:
    row = next(row for row in rows(data, IDS, "mutation seed") if row.key == key)
    parts = row.raw.split(b"|")
    parts[index + 1] = b" " + value.encode("utf-8") + b" "
    return data.replace(row.raw, b"|".join(parts), 1)


def controls(seed: Inputs) -> list[tuple[str, str, Inputs]]:
    middle = rows(seed.active, IDS, "control seed")[21].raw
    remove = seed.active.replace(middle + b"\n", b"", 1)
    duplicate = seed.active.replace(middle + b"\n", middle + b"\n" + middle + b"\n", 1)
    changed_requirement = replace_cell(seed.active, "L1-04", 1,
                                     next(row.cells[1] for row in rows(seed.active, IDS, "seed") if row.key == "L1-04")
                                     .replace("must not satisfy output provenance.", "may satisfy output provenance."))
    reordered = seed.active.replace(b"`L1-10`", b"`TEMP`", 1).replace(b"`L1-11`", b"`L1-10`", 1).replace(b"`TEMP`", b"`L1-11`", 1)
    return [
        ("CONTRACT-POSITIVE", "PASS", seed),
        ("CONTRACT-APPEND-POSITIVE", "PASS", replace(seed, active=seed.active + b"\n## Evidence for L1-01\nReceipt remains append-only.\n")),
        ("CONTRACT-MISSING-MIDDLE", "ID_MISSING", replace(seed, active=remove)),
        ("CONTRACT-DUPLICATE-MIDDLE", "ID_DUPLICATE", replace(seed, active=duplicate)),
        ("CONTRACT-UNKNOWN-ID", "ID_UNKNOWN", replace(seed, active=seed.active.replace(b"`L1-11`", b"`L1-99`", 1))),
        ("CONTRACT-ORDER", "ID_ORDER", replace(seed, active=reordered)),
        ("CONTRACT-LATE-REQUIREMENT", "REQUIREMENT", replace(seed, active=changed_requirement)),
        ("CONTRACT-LATE-INHERITED-CELL", "INHERITED_ROW_BYTES", replace(seed, active=replace_cell(seed.active, "CHK-SCOPE", 7, "Closed without evidence."))),
        ("CONTRACT-EVIDENCE-CELL", "INHERITED_ROW_BYTES", replace(seed, active=replace_cell(seed.active, "L1-04", 6, "Changed evidence cell."))),
        ("CONTRACT-NEW-ROW-CELL", "ROW_BYTES", replace(seed, active=replace_cell(seed.active, "L1R1-CLEANUP", 7, "Closed without replay."))),
        ("CONTRACT-EMPTY-CELL", "COLUMNS", replace(seed, active=replace_cell(seed.active, "L1-10", 6, ""))),
        ("CONTRACT-MOJIBAKE", "MOJIBAKE", replace(seed, active=seed.active + "\n\u00c2\u00ac\n".encode("utf-8"))),
        ("CONTRACT-BAD-UTF8", "UTF8", replace(seed, active=seed.active + b"\n\xff\n")),
        ("CONTRACT-LATE-DUPLICATE", "EVIDENCE_ROW", replace(seed, active=seed.active + b"\n" + middle + b"\n")),
        ("CONTRACT-LATE-UNKNOWN", "EVIDENCE_ROW", replace(seed, active=seed.active + b"\n" + middle.replace(b"INV-VALUE-DEPENDENCY", b"UNUSED-CONTROL") + b"\n")),
        ("CONTRACT-PREFIX", "PREFIX_BYTES", replace(seed, active=seed.active.replace(b"# LIFE-1-R1", b"# LIFE-1-R2", 1))),
        ("CONTRACT-FROZEN-LATE-CELL", "INHERITED_ROW_BYTES", replace(seed, frozen=replace_cell(seed.frozen, "CHK-SCOPE", 7, "Changed frozen final cell."))),
        ("CONTRACT-PROMPT-LATE-CLAUSE", "REQUIREMENT", replace(seed, prompt=seed.prompt.replace(b"an unrelated source cell with the same value must not satisfy output provenance.", b"an unrelated source cell with the same value may satisfy output provenance.", 1))),
        ("CONTRACT-PROMPT-BYTES", "PIN", replace(seed, prompt=seed.prompt + b"\n")),
        ("CONTRACT-EXTERNAL-PROMPT", "EXTERNAL_PROMPT", replace(seed, external_prompt=seed.prompt + b"\n")),
    ]


def self_test(seed: Inputs, only: str | None = None) -> list[dict]:
    cases = controls(seed)
    require(tuple((key, expected) for key, expected, _ in cases) == CONTROL_REGISTRY,
            "CONTROL_REGISTRY", "mutation constructors differ from exact ordered control registry")
    if only is not None:
        require(only in {key for key, _ in CONTROL_REGISTRY}, "CONTROL_UNKNOWN", f"unknown exact control: {only!r}")
        cases = [case for case in cases if case[0] == only]
        require(len(cases) == 1, "CONTROL_CARDINALITY", "focused control must execute exactly one ID")
    results = []
    for key, expected, challenged in cases:
        changed = {name: identity(getattr(challenged, name)) for name in Inputs.__dataclass_fields__
                   if getattr(challenged, name) != getattr(seed, name) and getattr(challenged, name) is not None}
        started = time.monotonic()
        try:
            verify(challenged)
            observed, detail = "PASS", "same verifier accepted"
        except Rejection as error:
            observed, detail = error.code, error.detail
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
    parser.add_argument("--external-prompt", type=Path, help="optional exact LIFE-1-R1 launch prompt")
    parser.add_argument("--external-original-prompt", type=Path, help="optional exact original LIFE-1 prompt")
    control_mode = parser.add_mutually_exclusive_group()
    control_mode.add_argument("--self-test", action="store_true")
    control_mode.add_argument("--only-control", help="run exactly one frozen control ID; empty/unknown rejects")
    parser.add_argument("--json-output", type=Path, help="explicit receipt destination; otherwise stdout only")
    args = parser.parse_args()
    root = args.repository_root.resolve()
    directory = root / REPAIR
    started = time.monotonic()
    receipt = {"schema": "life1-r1-contract-verification-v1", "base": BASE, "repositoryRoot": str(root),
               "startedUtc": datetime.now(timezone.utc).isoformat(), "gitReads": [],
               "scope": "contract-byte preservation only; no theorem or campaign acceptance"}
    try:
        active_path = (args.matrix or directory / "ACCEPTANCE_MATRIX.md").resolve()
        inputs = Inputs(active_path.read_bytes(), (directory / "ACCEPTANCE_MATRIX.frozen.md").read_bytes(),
                        (directory / "PROMPT.md").read_bytes(), (directory / "CONTRACT.json").read_bytes(),
                        git_blob(root, DIRECTORY + "/ACCEPTANCE_MATRIX.frozen.md", receipt["gitReads"]),
                        git_blob(root, DIRECTORY + "/CONTRACT_REQUIREMENTS.json", receipt["gitReads"]),
                        args.external_prompt.read_bytes() if args.external_prompt else None,
                        args.external_original_prompt.read_bytes() if args.external_original_prompt else None)
        receipt["inputs"] = {name: identity(getattr(inputs, name)) for name in Inputs.__dataclass_fields__
                             if getattr(inputs, name) is not None}
        receipt["matrixPath"] = str(active_path)
        receipt["verdict"] = verify(inputs)
        receipt["controlRegistry"] = [{"id": key, "expected": expected, "predicate": "verify(Inputs)"}
                                      for key, expected in CONTROL_REGISTRY]
        receipt["controls"] = self_test(inputs, args.only_control) if args.self_test or args.only_control is not None else []
        receipt["controlMode"] = "same verify(Inputs) predicate; immutable in-memory bytes; no fixture files written"
        receipt["inputFilesUnchanged"] = all(
            path.read_bytes() == data for path, data in (
                (active_path, inputs.active), (directory / "ACCEPTANCE_MATRIX.frozen.md", inputs.frozen),
                (directory / "PROMPT.md", inputs.prompt), (directory / "CONTRACT.json", inputs.contract)))
        require(receipt["inputFilesUnchanged"], "SOURCE_CHANGED", "input file changed during verification")
        receipt["status"] = "PASS"
    except (Rejection, OSError, KeyError, TypeError, ValueError) as error:
        receipt["status"] = "FAIL"
        receipt["error"] = {"code": error.code if isinstance(error, Rejection) else "INPUT",
                            "detail": str(error)}
    receipt["elapsedSeconds"] = round(time.monotonic() - started, 6)
    receipt["verifier"] = {"path": str(Path(__file__).resolve()), **identity(Path(__file__).read_bytes())}
    receipt["python"] = {"path": sys.executable, "version": sys.version, **identity(Path(sys.executable).read_bytes())}
    git_path = shutil.which("git")
    if git_path:
        receipt["git"] = {"path": git_path, **identity(Path(git_path).read_bytes())}
    serialized = json.dumps(receipt, ensure_ascii=True, indent=2) + "\n"
    if args.json_output:
        args.json_output.write_bytes(serialized.encode("utf-8"))
    print(serialized, end="")
    return 0 if receipt["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
