#!/usr/bin/env python3
"""Build the R2 47-row disposition appendix from validated, source-bound evidence.

No pending/component-only input can produce the appendix. This generator does
not modify either matrix, repeat heavy commands, or grant coordinator acceptance.
Historical statements are quoted from exact-base Git bytes, never their mutable
working copies. Final report/commit/static certification remains the S gate.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[5]
HERE = Path(__file__).resolve().parent
DIRECTORY = "docs/internal/extensions/lifecycle1"
BASE = "0485a64920a273d0830b926ee46275085222819d"
PRODUCTION = "cb4739220c01e6554a25ff8333652c0501486fa8"
DEPENDENCY_SHA = "66d1d42b1c01288fcb362dd716493f3154cc3c606b49d65b9f1e5f8fbaed68e1"
CONTRACT_PIN = (23564, "cf7b4e3b7d6124b03ea28f9b05d79ee3288f8e7c7c39ee409b0263c4d147befc")
FROZEN_PIN = (49039, "ad03e9572fff3c630bae7b80f2235d03302d2ab48fadfcc2c6e180c489b975c2")
GIT_PINS = {
    DIRECTORY + "/ACCEPTANCE_MATRIX.md": (72806, "18bdb89a0d4873636d434effb9a8e6d4f8c1b13997deb3167159eb1da167ef8e"),
    DIRECTORY + "/repair-r1/CONTROL_REGISTRY.frozen.json": (74726, "385c9bc95ac09b3cc046a7049e954cdf19361330c31f99bd83c9da0c822423f2"),
    DIRECTORY + "/repair-r1/registry_control_cases.json": (12330, "59d2a546c64eef274e878407583b51164d0676edd98fef46b04549d6fdf44a4a"),
    "scripts/lifecycle_dependency_cases.json": (37911, "4c9c7a4259808bb64c74656fd52559752e76f02834f2ac8567f5830968a5b80d"),
}
REQUIRED_CHECKS = (
    "default-build", "dependency-selftest", "dependency-startup", "dependency-focused", "dependency-full",
    "controls-pwsh", "controls-winps", "registry-pwsh", "registry-winps", "final-original-contract",
)
NATIVE_IDS = ["L01-W-EMPTY", "L02-C-EMPTY", "L03-W-SINGLE", "L04-C-SINGLE", "L05-W-REPEAT", "L06-C-REPEAT",
              "L07-W-TIE", "L08-C-TIE", "L09-W-INVALID", "L10-C-INVALID", "L11-W-DIRTY", "L12-C-DIRTY",
              "L13-W-N24", "L14-C-N24", "L15-W-N83", "L16-C-N83"]
REQUIRED_SOURCE_PINS = {
    "scripts/lifecycle_dependency_replay.ps1", "scripts/lifecycle_validator.ps1",
    "scripts/lifecycle_validator_environment.ps1", "scripts/owned_process_tree.ps1",
    "scripts/lifecycle_dependency_cases.json", ".lake/build/bin/rmq_lifecycle_validate.exe",
}
EXPECTED_SCHEMA = {
    "schema": "life1-r2-evidence-v1", "passed": True, "base": BASE, "productionCommit": PRODUCTION,
    "requiredCheckNames": list(REQUIRED_CHECKS),
    "controlCampaigns": {"pwsh": 67, "winps": 66}, "registryCampaigns": {"pwsh": 12, "winps": 12},
    "dependencyFull": {"cases": 26, "acceptCount": 3, "rejectCount": 23},
    "hash": {"vectorCount": 8, "successfulProfiles": ["old-pwsh", "current-pwsh", "current-winps"],
             "oldWinFailureExact": True, "distinctions": 3},
    "materialization": {"initialFailureExact": True, "negativeCount": 3, "positiveCount": 1, "livePassed": True},
    "history": {"schema": 1, "status": "PASS", "r2Base": BASE, "reusedFull16": 2},
    "finalDelivery": "S remains mandatory; generator does not certify report/commit/static gates",
}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def identity(data: bytes) -> dict:
    return {"bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}


def pinned(data: bytes, expected: tuple[int, str], label: str) -> None:
    require((len(data), identity(data)["sha256"]) == expected, "Exact bytes differ: " + label)


def pairs(items: list[tuple]) -> dict:
    result = {}
    for key, value in items:
        require(key not in result, "Duplicate JSON key: " + key)
        result[key] = value
    return result


def decode(data: bytes, label: str) -> str:
    text = data.decode("utf-8", errors="strict")
    require(not text.startswith("\ufeff"), "Unexpected UTF-8 BOM: " + label)
    require(not any(value in text for value in ("\u00c2\u00ac", "\u00e2\u20ac", "\ufffd")), "Recognizable mojibake: " + label)
    return text


def load(path: Path) -> dict:
    value = json.loads(decode(path.read_bytes(), str(path)), object_pairs_hook=pairs)
    require(isinstance(value, dict), "JSON object required: " + str(path))
    return value


def path_for(value: str) -> Path:
    path = Path(value)
    return path.resolve() if path.is_absolute() else (ROOT / path).resolve()


def check_reference(pin: dict) -> Path:
    path = path_for(pin["path"])
    require(path.is_file(), "Missing evidence file: " + str(path))
    actual = identity(path.read_bytes())
    require(actual == {"bytes": pin["bytes"], "sha256": pin["sha256"].lower()}, "Stale evidence pin: " + str(path))
    return path


def reference(path: Path) -> str:
    absolute = path.resolve()
    try:
        label = absolute.relative_to(ROOT).as_posix()
    except ValueError:
        label = absolute.as_posix()
    return f"`{label}` (SHA256 `{identity(absolute.read_bytes())['sha256']}`)"


def git_blob(relative: str, commit: str = BASE) -> bytes:
    result = subprocess.run(["git", "cat-file", "blob", f"{commit}:{relative}"], cwd=ROOT,
                            capture_output=True, timeout=30, check=False)
    require(result.returncode == 0, "Cannot read immutable Git blob: " + commit + ":" + relative)
    require(result.stderr == b"", "Unexpected Git blob diagnostic: " + relative)
    if relative in GIT_PINS and commit == BASE:
        pinned(result.stdout, GIT_PINS[relative], relative)
    return result.stdout


def historical_rows(ids: list[str]) -> tuple[dict, bytes]:
    raw = git_blob(DIRECTORY + "/ACCEPTANCE_MATRIX.md")
    text = decode(raw, "original active Git matrix")
    headings = list(re.finditer(r"(?m)^### ([A-Z0-9-]+) \u2014 Candidate-local closed; S delivery gate applies$", text))
    require([match[1] for match in headings] == ids[:43], "Historical exact ordered43 sections differ")
    cells = {}
    for line in raw.split(b"\n"):
        if not line.startswith(b"| `"):
            continue
        parts = line.split(b"|")
        require(len(parts) == 10 and all(part.strip() for part in parts[1:9]), "Historical eight-column row differs")
        key = parts[1].strip().decode("utf-8")[1:-1]
        require(key not in cells, "Duplicate historical frozen row: " + key)
        cells[key] = tuple(part.decode("utf-8") for part in parts[4:7])
    require(list(cells) == ids[:43], "Historical exact ordered43 frozen rows differ")
    result = {}
    for i, heading in enumerate(headings):
        end = headings[i + 1].start() if i + 1 < len(headings) else len(text)
        section = text[heading.end():end]
        proposition = re.findall(r"(?m)^Quoted conclusion and object chain: ([^\r\n]+)$", section)
        challenge = re.findall(r"(?m)^Final observed evidence and challenge: ([^\r\n]+)$", section)
        require(len(proposition) == len(challenge) == 1, "Historical proposition/challenge cardinality differs: " + heading[1])
        result[heading[1]] = {"proposition": proposition[0], "challenge": challenge[0], "cells": cells[heading[1]]}
    return result, raw


def verify_contract() -> dict:
    checker = HERE / "verify_contract.py"
    require(checker.read_bytes() == git_blob(DIRECTORY + "/repair-r2/verify_contract.py", PRODUCTION),
            "Contract verifier differs from production source freeze")
    command = [sys.executable, str(checker), "--check", "--self-test"]
    result = subprocess.run(command, cwd=ROOT, capture_output=True, timeout=30, check=False)
    require(result.returncode == 0 and result.stderr == b"", "Actual R2 read-only contract verifier failed")
    value = json.loads(result.stdout, object_pairs_hook=pairs)
    require(value["status"] == "PASS" and value["inputFilesUnchanged"] is True and value["readOnly"] is True,
            "Actual R2 verifier lacks successful read-only verdict")
    require(value["verdict"]["rows"] == 47 and value["verdict"]["inheritedRows"] == 45 and
            value["verdict"]["changedInheritedIds"] == [] and value["verdict"]["immutablePrefix"] is True,
            "Actual R2 contract comparison differs")
    require(value["controlSummary"] == {"selected": 22, "expectedAccept": 2, "expectedReject": 20,
                                        "allMatched": True, "predicate": "verify(Inputs)"}, "Actual R2 controls differ")
    return value


def validate_evidence(path: Path, control_registry: dict, narrow_registry: dict, dependency_registry: dict) -> dict:
    value = load(path)
    require(value["schema"] == EXPECTED_SCHEMA["schema"] and value["passed"] is True and
            value["base"] == BASE and value["productionCommit"] == PRODUCTION, "R2 validated packet contract differs")
    pins = value["sourcePins"]
    require(REQUIRED_SOURCE_PINS.issubset(pins), "R2 packet lacks required actual consumed source pins")
    for name, expected in pins.items():
        require(identity(path_for(name).read_bytes())["sha256"] == expected.lower(), "R2 source pin changed: " + name)
    require(pins["scripts/lifecycle_dependency_replay.ps1"].lower() == DEPENDENCY_SHA, "R2 production dependency hash differs")
    checks = value["checks"]
    names = [item["name"] for item in checks]
    require(len(names) == len(set(names)) and set(REQUIRED_CHECKS).issubset(names), "R2 final check names missing or duplicate")
    for item in checks:
        require(item["passed"] is True and item["exit"] == item["expectedExit"] and item["deadline"] > 0 and
                item["seconds"] >= 0, "R2 final check did not finish as required: " + item["name"])
        check_reference(item["receipt"])
    for name in REQUIRED_CHECKS:
        item = next(item for item in checks if item["name"] == name)
        require(item["exit"] == item["expectedExit"] == 0, "Required R2 positive failed: " + name)
    for profile, count in (("pwsh", 67), ("winps", 66)):
        expected = [item for item in control_registry["cases"] if profile in item["profiles"]]
        campaign = value["controlCampaigns"][profile]
        require(len(expected) == count and campaign["passed"] is True and
                campaign["selected"] == [item["id"] for item in expected] and
                [item["id"] for item in campaign["results"]] == campaign["selected"], "R2 ordered full controls differ: " + profile)
        for observed, case in zip(campaign["results"], expected):
            require(observed["passed"] is True and observed["kind"] == case["kind"] and observed["handler"] == case["handler"],
                    "R2 control mapping/outcome differs: " + observed["id"])
            check_reference(observed["receipt"])
            require(isinstance(observed["positive"], dict) and isinstance(observed["negative"], dict),
                    "R2 control lacks checked P/Q disposition: " + observed["id"])
        narrow = value["registryCampaigns"][profile]
        expected_ids = [item["id"] for item in narrow_registry["cases"]]
        require(len(expected_ids) == 12 and narrow["passed"] is True and narrow["selected"] == expected_ids and
                [item["id"] for item in narrow["results"]] == expected_ids and
                all(item["passed"] is True for item in narrow["results"]), "R2 ordered registry controls differ: " + profile)
    full = value["dependency"]["full"]
    expected_cases = dependency_registry["cases"]
    ids = [item["id"] for item in expected_cases]
    require(len(ids) == 26 and full["passed"] is True and full["selected"] == ids and
            [item["id"] for item in full["cases"]] == ids and full["acceptCount"] == 3 and full["rejectCount"] == 23 and
            full["restored"] is True and full["shadowRemoved"] is True, "R2 dependency full26 disposition differs")
    for observed, expected in zip(full["cases"], expected_cases):
        require(observed["expected"] == expected["expected"] and observed["producerExit"] == 0 and
                observed["consumerExit"] == (1 if expected["expected"] == "reject" else 0),
                "R2 dependency producer/consumer verdict differs: " + observed["id"])
    for mode in ("selftest", "startup", "focused"):
        require(value["dependency"][mode]["passed"] is True, "R2 dependency prerequisite lacks PASS: " + mode)
    hashed = value["hash"]
    require(hashed["passed"] is True and hashed["vectorCount"] == 8 and
            hashed["successfulProfiles"] == ["old-pwsh", "current-pwsh", "current-winps"] and
            hashed["oldWinFailureExact"] is True and hashed["distinctions"] == 3, "R2 portable hash evidence differs")
    require(bool(hashed["receipts"]), "R2 hash evidence lacks receipt pins")
    for pin in hashed["receipts"]:
        check_reference(pin)
    materialized = value["materialization"]
    require(materialized["passed"] is True and materialized["initialFailureExact"] is True and
            materialized["negativeCount"] == 3 and materialized["positiveCount"] == 1 and materialized["livePassed"] is True,
            "R2 exact materialization evidence differs")
    check_reference(materialized["receipt"])
    require(value["scope"]["passed"] is True, "R2 current scope check did not pass")
    check_reference(value["fileIndex"])
    return value


def validate_history(path: Path) -> dict:
    history = load(path)
    require(history["schema"] == 1 and history["status"] == "PASS" and history["r2Base"] == BASE,
            "Historical applicability packet differs")
    check_reference(history["fullInventory"])
    for pin in history["inputs"]:
        check_reference(pin)
    current = history["currentApplicability"]
    require(current["formalAndBuildCacheSourceCount"] > 0 and current["copiedArtifactCount"] > 0 and
            current["dependency"]["outsideHashBytesBodyExact"] is True and
            current["dependency"]["currentRaw"]["sha256"] == DEPENDENCY_SHA, "Historical current applicability differs")
    inventory = current["typeAxiomInventory"]
    require(inventory["run"]["exitCode"] == 0 and inventory["run"]["timedOut"] is False and
            inventory["run"]["outputLimitExceeded"] is False and bool(inventory["artifacts"]), "Historical type/axiom inventory failed")
    for artifact in inventory["artifacts"]:
        require(artifact["recorded"] == artifact["actual"], "Historical type/axiom raw profile differs")
        check_reference(artifact["actual"])
    native = history["reusedFull16"]
    require([item["check"] for item in native] == ["final-validator-pwsh-full", "final-validator-winps-full"],
            "Historical full16 profiles differ")
    for item in native:
        require(item["applicableToCurrentUnchangedValidator"] is True and item["exactOrderedNativeIds"] == NATIVE_IDS and
                item["processes"] == 9 and item["exactReturnedStreamsAndSelectorsVerified"] is True,
                "Historical native applicability differs")
        check_reference(item["receipt"])
        check_reference(item["runtime"])
        for pin in item["actualConsumedInputs"]:
            require(identity(path_for(pin["path"]).read_bytes())["sha256"] == pin["historicalAndCurrentSha256"],
                    "Actual native consumed input changed: " + pin["path"])
    return history


def families(packet: dict, history: dict, evidence_path: Path, history_path: Path) -> list[str]:
    checks = {item["name"]: item for item in packet["checks"]}
    check_refs = lambda names: "; ".join(reference(check_reference(checks[name]["receipt"])) for name in names)
    native = history["reusedFull16"]
    return [
        f"R2-B: bounded default build passed in {checks['default-build']['seconds']}s with a {checks['default-build']['deadline']}s outer deadline; {check_refs(['default-build'])}. The final source uses the existing Lean/native cache whose unchanged inputs are separately checked in R2-T.",
        f"R2-T: exact historical source applicability is verified by {reference(history_path)}. Its current source checks cover {history['currentApplicability']['formalAndBuildCacheSourceCount']} formal/build-cache sources, {history['currentApplicability']['copiedArtifactCount']} copied artifacts and the retained exact type/axiom inventory. Historical producer identities, current actual inputs and differing raw serializations remain separate. This reuses the checked propositions; it is not a new proof or a cold-build claim.",
        "R2-N: both unchanged production full16 validator receipts remain applicable after exact consumed-source, executable, tool and runtime checks: " + "; ".join(f"{item['check']} {item['seconds']}s/{item['deadline']}s, nine ordered processes, {reference(check_reference(item['receipt']))}" for item in native) + ". These retained full runs are reused, not relabeled as new executions. The changed dependency hash was an incidental outer capture for those validator runs, not an executed input.",
        f"R2-D: current-pwsh dependency self-test, D20/P06 startup positives, focused D15 and full ordered26 replay all passed. Full replay took {checks['dependency-full']['seconds']}s within {checks['dependency-full']['deadline']}s; each producer exited0 before its fixed consumer, 23 consumers rejected and 3 accepted. Source restoration and valid-shadow removal are true. Receipts: {check_refs(['dependency-selftest', 'dependency-startup', 'dependency-focused', 'dependency-full'])}. The 26-case compiler replay is not attributed to Windows PowerShell.",
        f"R2-C: all applicable unchanged R1 controls passed on repaired production bytes: pwsh67 in {checks['controls-pwsh']['seconds']}s and Windows PowerShell66 in {checks['controls-winps']['seconds']}s. Both exact12 registry/runtime campaigns passed. Ordered IDs, kind/handler mappings, actual bounded process receipts and checked P/Q dispositions are retained in {reference(evidence_path)}. Receipts: {check_refs(['controls-pwsh', 'controls-winps', 'registry-pwsh', 'registry-winps'])}.",
        f"R2-H: eight independently expected byte vectors agree across old-pwsh, current-pwsh and current-winps; three changed-byte/line-ending distinctions remain unequal. The exact old Windows HashData failure remains a rejected old-source positive. Both current file-pin F01 positives and the required finalizer/dependency controls reach the repaired production function. Portable SHA256.Create/ComputeHash plus hexadecimal conversion disposes its cryptographic object and preserves exact input bytes/lowercase output. Packet: {reference(evidence_path)}.",
        f"R2-M: the reviewed initial CRLF profile reproduced the immutable original-checker failure; three exact negative controls and one exact-Git positive are retained. Only the three explicitly authorized original contract files were materialized from exact-base Git bytes before the new protected baseline; no Git content changed. The live unchanged checker passed against the exact external original prompt: {check_refs(['final-original-contract'])}. Current contract verification compares all47 rows, all45 inherited raw rows and all22 exact-code controls. Frozen R2 prefix: {FROZEN_PIN[0]} bytes/SHA256 `{FROZEN_PIN[1]}`.",
        "S: every disposition remains subject to final report/source/receipt bindings, scope and raw-byte checks, exact-base and parent-to-commit design certification, report-sensitive strict claim scan, committed-range diff checks and clean scoped delivery. The external postcommit delivery manifest owns the final identities, avoiding a report/self-hash loop. This appendix does not claim those future results or coordinator acceptance.",
    ]


def render(contract: dict, historical: dict, historical_raw: bytes, packet: dict, history: dict,
           evidence_path: Path, history_path: Path) -> bytes:
    ids = contract["orderedIds"]
    lines = ["# LIFE-1-R2 row dispositions", "",
             "These 47 current local evidence dispositions preserve the frozen obligations. All required component evidence below is validated; the final S delivery gate applies to every row. No coordinator acceptance, native consuming adapter, aggregate certification or fresh blind audit is credited here.", "",
             "Live guards: actual is Continuous.continuousRun model xs left right; initial is the supplied state at Layout.builderBase; cells=buildMemory xs; M=cells.length; B=producer.regs3; n=xs.length; W=wordWidth n. Public guards remain InputDomain model xs and endpoints below 2^W. Word input retains InputFits; comparison input retains its separately counted arbitrary-Int resources.", "",
             f"Historical quote source: `{BASE}:{DIRECTORY}/ACCEPTANCE_MATRIX.md`, {len(historical_raw)} bytes/SHA256 `{identity(historical_raw)['sha256']}`. For every original row, the three frozen obligation cells and the exact appended proposition/object-chain and challenge paragraphs are copied without rewriting. Their historical B/T/N/D/S labels retain their original source epoch; the current R2 families below state the separately checked reuse or fresh evidence. Historical closure labels are not copied as current decisions.", "",
             "No theorem type, input premise, width/cost claim or provenance object changes in this repair. Logical extent is not native backing capacity or alias ownership; arbitrary-Int resources do not acquire a bounded input-bit claim. Returned nonempty helper-line arrays are not complete original process streams. Overflow, lost output or unsupported evidence never counts as success.", "",
             "## Current evidence families", ""]
    for family in families(packet, history, evidence_path, history_path):
        lines.extend((family, ""))
    for key in ids:
        lines.extend(("### Evidence for " + key, ""))
        if key in historical:
            item = historical[key]
            for title, cell in zip(("Frozen proposition/check obligation cell", "Frozen object-chain obligation cell", "Frozen anti-vacuity obligation cell"), item["cells"]):
                lines.extend((title + " (historical planned obligation, exact cell padding retained):", "", "> \u201c" + cell + "\u201d", ""))
            lines.extend(("Historical quoted conclusion and object chain (exact):", "", "> " + item["proposition"], "",
                          "Historical observed evidence and challenge (exact):", "", "> " + item["challenge"], ""))
            if key in {"L1-20", "CHK-FINAL", "CHK-SCOPE"}:
                status = "CURRENT_LOCAL_EVIDENCE_RECORDED; final S certification is required before delivery."
            elif key in {"L1-18", "INV-MUTATION-REPRODUCIBILITY"}:
                status = "UNCHANGED_FORMAL_EVIDENCE_REUSED_AND_CURRENT_REPLAY_RECORDED; final S delivery gate applies."
            else:
                status = "UNCHANGED_FORMAL_EVIDENCE_REUSED; final S delivery gate applies."
            lines.extend(("Current disposition: " + status, "",
                          "Current evidence: R2-T establishes unchanged proposition/consumer/source applicability; R2-N reuses both actual full16 receipts; R2-B and R2-D supply current build and same-source full26 outcomes. R2-C/H/M close the assigned verification portability components. S remains mandatory.", ""))
        elif key == "L1R1-SELECTOR":
            lines.extend(("Current disposition: CURRENT_SELECTOR_EVIDENCE_RECORDED; final S delivery gate applies.", "",
                          "The unchanged production environment adapter distinguishes an omitted selector key from an intentional exact id: selection and restores the caller's prior state. R2-C executes all applicable native/production wrapper boundaries and both12 registry/runtime campaigns on the current source, including inherited ambient values, malformed/empty/duplicate channels and failure restoration. R2-N supplies separately verified applicability of both production full16 runs. No selector, Lean case, diagnostic predicate or registry entry changed in R2.", ""))
        elif key == "L1R1-CLEANUP":
            lines.extend(("Current disposition: CURRENT_FINALIZER_EVIDENCE_RECORDED; final S delivery gate applies.", "",
                          "R2-C/H execute actual source-bound production finalizers under both declared runtimes with successful nonempty real-file pin capture before changed-pin challenges. Integrity and cleanup use independent guards; original stage, integrity and cleanup failures retain their distinct nonzero outcomes and truthful restoration/shadow status. Safe descendant/basename checks remain exact; failing finalizers never restore or overwrite changed originals. R2-D completes all26 current-pwsh producer/client cases and confirms final restoration and shadow removal. The exact old Windows capture failure and old retained-shadow failure remain historical failures with their original source identities.", ""))
        elif key == "L1R2-CONTRACT-BYTES":
            lines.extend(("Current disposition: CURRENT_EXACT_BYTE_EVIDENCE_RECORDED; final S delivery gate applies.", "",
                          "R2-M retains the unchanged checker's initial reviewed CRLF negative and legitimate exact-Git positive, the three disclosed startup materializations and the live external-prompt positive. Old manifests are unchanged. The new47-row checker uses exact complete45 inherited Git rows, eight nonempty cells and full requirement text; 2 positive and20 exact-code negative controls share its sole verifier predicate. Missing, duplicate, reordered, mojibake, late-cell, source and predicate substitutions reject. Initial bytes, immutable Git bytes and the protected R2 live baseline remain distinct; no normalization establishes equality.", ""))
        elif key == "L1R2-HASH":
            lines.extend(("Current disposition: CURRENT_PORTABLE_HASH_EVIDENCE_RECORDED; final S delivery gate applies.", "",
                          "R2-H compares the same exact input byte arrays using independent fixed expectations and the immutable old modern implementation; empty, binary, Unicode-encoded and different line-ending inputs are covered. Both current runtime implementations produce identical lowercase SHA256, and altered bytes remain detectably unequal. R2-C reaches the actual production Hash-Bytes through real file-pin finalizers and dependency selector/registry boundaries; empty/failed pin capture cannot serve as the positive. R2-D establishes complete current-pwsh26 replay. Only the production function body changed; callers, registry, types, diagnostics, safe cleanup and failure verdicts remain protected. The old Windows HashData rejection is preserved, not relabeled or repaired in a fixture.", ""))
        else:
            raise ValueError("Unmapped disposition ID: " + key)
    content = "\n".join(lines).encode("utf-8")
    require(re.findall(rb"(?m)^### Evidence for ([A-Z0-9-]+)$", content) == [key.encode() for key in ids], "Generated exact47 row order differs")
    for item in historical.values():
        for cell in item["cells"]:
            require(("> \u201c" + cell + "\u201d").encode("utf-8") in content, "Historical cell quote changed")
        require(("> " + item["proposition"]).encode("utf-8") in content and
                ("> " + item["challenge"]).encode("utf-8") in content, "Historical proposition/challenge quote changed")
    return content


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    parser.add_argument("--evidence", type=Path, default=ROOT / ".lake/repair-r2/evidence-verified.json")
    parser.add_argument("--history", type=Path, default=HERE / "HISTORY_APPLICABILITY.json")
    parser.add_argument("--check", action="store_true", help="regenerate in memory and compare the owned appendix; no writes")
    parser.add_argument("--schema", action="store_true", help="print required packet schema/counts without consuming evidence or writing")
    args = parser.parse_args()
    if args.schema:
        print(json.dumps(EXPECTED_SCHEMA, indent=2))
        return 0
    contract_bytes = (HERE / "CONTRACT.json").read_bytes()
    pinned(contract_bytes, CONTRACT_PIN, "R2 contract")
    pinned((HERE / "ACCEPTANCE_MATRIX.frozen.md").read_bytes(), FROZEN_PIN, "R2 frozen matrix")
    contract = load(HERE / "CONTRACT.json")
    ids = contract["orderedIds"]
    require(contract["base"] == BASE and len(ids) == len(set(ids)) == 47 and
            ids[-4:] == ["L1R1-SELECTOR", "L1R1-CLEANUP", "L1R2-CONTRACT-BYTES", "L1R2-HASH"] and
            [item["id"] for item in contract["requirements"]] == ids, "Exact43+2+2 R2 contract differs")
    evidence_path, history_path = args.evidence.resolve(), args.history.resolve()
    watched = {path: path.read_bytes() for path in (evidence_path, history_path, HERE / "CONTRACT.json", HERE / "ACCEPTANCE_MATRIX.frozen.md")}
    registry = json.loads(git_blob(DIRECTORY + "/repair-r1/CONTROL_REGISTRY.frozen.json"), object_pairs_hook=pairs)
    narrow = json.loads(git_blob(DIRECTORY + "/repair-r1/registry_control_cases.json"), object_pairs_hook=pairs)
    dependency = json.loads(git_blob("scripts/lifecycle_dependency_cases.json"), object_pairs_hook=pairs)
    packet = validate_evidence(evidence_path, registry, narrow, dependency)
    history = validate_history(history_path)
    verified = verify_contract()
    require(verified["verdict"]["orderedIds"] == ids, "Verifier ordered IDs differ from row contract")
    historical, historical_raw = historical_rows(ids)
    content = render(contract, historical, historical_raw, packet, history, evidence_path, history_path)
    require(all(path.read_bytes() == raw for path, raw in watched.items()), "Evidence changed during generation")
    output = HERE / "ROW_DISPOSITIONS.md"
    require(not output.is_symlink(), "Output must be the regular owned R2 appendix")
    if args.check:
        require(output.read_bytes() == content, "Existing row appendix differs from current validated evidence")
    else:
        output.write_bytes(content)
    print(json.dumps({"status": "PASS", "mode": "check" if args.check else "write", "path": str(output),
                      **identity(content), "ids": 47, "exactHistoricalObligationCells": 129,
                      "exactHistoricalPropositionAndChallengeParagraphs": 86,
                      "samePredicateContractControls": 22, "finalDeliveryGate": "S remains mandatory"}))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError, KeyError, TypeError, IndexError, subprocess.TimeoutExpired) as error:
        print("R2-ROW-DISPOSITIONS: FAIL " + str(error), file=sys.stderr)
        raise SystemExit(1)
