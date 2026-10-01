#!/usr/bin/env python3
"""Generate a 45-ID evidence appendix; never edit either acceptance matrix.

Default dependency/control states are pending. Completion flags require actual
bounded-process receipts, exact ordered registries, and current source pins.
These flags promote verification components only, never final delivery or
coordinator acceptance. Historical proposition cells are quoted unchanged.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[5]
HERE = Path(__file__).resolve().parent
CHECKS = ROOT / ".lake/repair-r1/checks"
BASE = "12bd7f0fc2c87f2c9bdef3825bd92477e48e3433"
DIRECT_BLOCKERS = {"L1-18", "L1-20", "INV-MUTATION-REPRODUCIBILITY", "CHK-FINAL", "CHK-SCOPE", "L1R1-CLEANUP"}
NATIVE_IDS = ["L01-W-EMPTY", "L02-C-EMPTY", "L03-W-SINGLE", "L04-C-SINGLE", "L05-W-REPEAT", "L06-C-REPEAT",
              "L07-W-TIE", "L08-C-TIE", "L09-W-INVALID", "L10-C-INVALID", "L11-W-DIRTY", "L12-C-DIRTY",
              "L13-W-N24", "L14-C-N24", "L15-W-N83", "L16-C-N83"]
NATIVE_STAGES = ["registry", "startup", "focused", "reject-empty", "reject-whitespace", "reject-unknown",
                 "reject-duplicate", "reject-channels", "full"]
REQUIRED_CHECK_PINS = {"scripts/lifecycle_validator.ps1", "scripts/lifecycle_validator_environment.ps1",
                       "scripts/lifecycle_dependency_replay.ps1", "scripts/owned_process_tree.ps1",
                       "scripts/lifecycle_dependency_cases.json", "RMQ/Validation/PackedLifecycle.lean",
                       "RMQ/Validation/LifecycleContract.lean", "scripts/lifecycle_provenance_contract.lean",
                       "lean-toolchain", "lakefile.toml", ".lake/build/bin/rmq_lifecycle_validate.exe"}
HASHDATA_ERROR = "Method invocation failed because [System.Security.Cryptography.SHA256] does not contain a method named 'HashData'."


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def load(path: Path):
    return json.loads(path.read_bytes().decode("utf-8", errors="strict"))


def reference(path: Path) -> str:
    # Short root-relative references remain useful when this text is appended
    # to the active matrix. Hashes identify the exact consumed receipt bytes.
    absolute = path.resolve()
    try:
        name = absolute.relative_to(ROOT).as_posix()
    except ValueError:
        name = str(absolute)
    return f"`{name}` (SHA256 `{sha(path.read_bytes())}`)"


def checked_pins(pins: dict, required: set[str] = frozenset()) -> int:
    require(bool(pins) and required.issubset(pins), "missing required source pins")
    for name, expected in pins.items():
        path = Path(name) if Path(name).is_absolute() else ROOT / name
        require(path.is_file() and sha(path.read_bytes()) == expected.lower(), f"stale or absent source pin: {name}")
    return len(pins)


def process(result: dict, expected_exit: int = 0, empty_streams: bool = False) -> None:
    require(result["ExitCode"] == expected_exit, "unexpected recorded process exit")
    require(result["TimedOut"] is False and result["OutputLimitExceeded"] is False, "incomplete recorded process")
    require(result["Ownership"] == "kill-on-close-job" and result["TerminatedIds"] == [], "recorded ownership/cleanup differs")
    require(result["DeadlineSeconds"] > 0, "recorded process lacks positive deadline")
    require(isinstance(result["StandardOutput"], list) and isinstance(result["StandardError"], list), "missing returned streams")
    if empty_streams:
        require(result["StandardOutput"] == [] and result["StandardError"] == [], "unexpected recorded compiler output")


def check(name: str) -> tuple[Path, dict]:
    path = CHECKS / name / "result.json"
    value = load(path)
    require(value["spec"]["name"] == name, "check name mismatch")
    process(value["result"])
    require(value["result"]["StandardError"] == [], "unexpected outer stderr")
    checked_pins(value["sources"], REQUIRED_CHECK_PINS)
    return path, value


def build_evidence() -> str:
    default_path, default = check("final-default-build-pinned")
    named_path, named = check("final-named-build-pinned")
    targets = ["build", "RMQ.Core.WordRAM.Lifecycle.Capstone", "RMQ.Validation.LifecycleContract", "rmq_lifecycle_validate",
               "RMQ.Headlines.Lifecycle", "RMQ.Core.WordRAM.Lifecycle.Provenance"]
    require(default["spec"]["arguments"] == ["build"] and named["spec"]["arguments"] == targets, "build target contract differs")
    for value in (default, named):
        require(value["result"]["StandardOutput"][-1] == "Build completed successfully.", "missing build completion record")
    return (f"B: recorded default build passed in {default['result']['DurationSeconds']}s and named lifecycle/consumer build "
            f"passed in {named['result']['DurationSeconds']}s; their complete source-pin sets match current bytes. "
            f"Receipts: {reference(default_path)}; {reference(named_path)}. "
            "These are bounded build results with recorded cache reuse, not newly supplied mathematical assumptions.")


def native_evidence() -> str:
    references = []
    for profile in ("pwsh", "winps"):
        startup_path, startup = check(f"final-validator-{profile}-startup")
        path, value = check(f"final-validator-{profile}-full")
        require("-Stage" in startup["spec"]["arguments"] and "startup" in startup["spec"]["arguments"], "startup invocation differs")
        output = value["result"]["StandardOutput"]
        require(len(output) == 1, "full validator outer terminal cardinality differs")
        match = re.fullmatch(r"LIFE1-VALIDATOR PASS stage=full processes=9 logs=(.+)", output[0])
        require(match is not None, "full validator terminal differs")
        directory = Path(match[1])
        directory.resolve().relative_to(ROOT / ".lake")
        passed = load(directory / "PASS.json")
        require(passed["stage"] == "full" and passed["cases"] == NATIVE_IDS and passed["processCount"] == 9
                and passed["identityPreserved"] is True and passed["expectedVerdict"] == "PASS", "full16 PASS summary differs")
        stages = load(directory / "processes.json")
        require([stage["name"] for stage in stages] == NATIVE_STAGES, "native ordered stage registry differs")
        for stage in stages:
            expected = 1 if stage["name"].startswith("reject-") else 0
            require(stage["exitCode"] == stage["expectedExit"] == expected, "native expected exit differs")
            process(stage["result"], expected)
        require(stages[-1]["expectedCases"] == NATIVE_IDS, "native full case list differs")
        require(stages[-1]["result"]["StandardOutput"][-1] == "LIFE1-PASS|mode=full|cases=16", "native full terminal differs")
        actual_lines = stages[-1]["result"]["StandardOutput"]
        require(len(actual_lines) == 17 and
                [line.split("|")[1] for line in actual_lines[:-1] if line.startswith("LIFE1-CASE|") and "|PASS|" in line] == NATIVE_IDS,
                "native actual returned case records are not exact ordered16")
        references.append(f"{profile}: {reference(path)}, full16 {value['result']['DurationSeconds']}s; startup {reference(startup_path)}")
    return "N: both declared runtimes completed the actual production full16 wrapper, with ordered nine-process receipts and matching current source pins. " + "; ".join(references) + "."


def dependency_evidence(args) -> str:
    startup_path, startup = check("final-dependency-startup")
    focused_path, focused = check("final-dependency-focused")
    startup_lines = startup["result"]["StandardOutput"]
    focused_lines = focused["result"]["StandardOutput"]
    require(len(startup_lines) == 3 and startup_lines[:2] == ["LIFE1-DEPENDENCY CASE D20_ACCEPT_IDENTITY PASS", "LIFE1-DEPENDENCY CASE P06_ACCEPT_IDENTITY PASS"]
            and startup_lines[-1].startswith("LIFE1-DEPENDENCY PASS "), "dependency actual startup records differ")
    require(len(focused_lines) == 2 and focused_lines[0] == "LIFE1-DEPENDENCY CASE D15_CODE_FETCH_DROP PASS"
            and focused_lines[-1].startswith("LIFE1-DEPENDENCY PASS "), "dependency actual focused records differ")
    lead = f"D prerequisites: startup and a real focused case passed: {reference(startup_path)}; {reference(focused_path)}. "
    if not args.dependency_complete:
        require(args.dependency_summary is None, "dependency summary supplied without explicit completion request")
        return lead + "D full26 remains PENDING; an active replay or historical full26 receipt does not promote this repair component."
    require(args.dependency_summary is not None, "--dependency-complete requires --dependency-summary")
    outer_path, outer = check("final-dependency-full")
    path = args.dependency_summary.resolve()
    summary = load(path)
    registry = load(ROOT / "scripts/lifecycle_dependency_cases.json")["cases"]
    ids = [case["id"] for case in registry]
    require(len(ids) == 26 and len(set(ids)) == 26, "dependency registry is not exact26")
    require(summary["passed"] is True and summary["restored"] is True and summary["shadowRemoved"] is True, "dependency finalization incomplete")
    require(all(summary[key] is None for key in ("stageError", "integrityError", "cleanupError")), "dependency finalization contains failure")
    require(summary["registrySha256"] == "4c9c7a4259808bb64c74656fd52559752e76f02834f2ac8567f5830968a5b80d", "dependency frozen registry pin differs")
    require(summary["selected"] == ids and [case["id"] for case in summary["cases"]] == ids, "dependency exact ordered IDs differ")
    require(outer["result"]["StandardOutput"] == [f"LIFE1-DEPENDENCY CASE {key} PASS" for key in ids] + [f"LIFE1-DEPENDENCY PASS {path.parent}"], "dependency outer terminal records differ")
    require(sum(case["expected"] == "reject" for case in summary["cases"]) == 23 and
            sum(case["expected"] == "accept" for case in summary["cases"]) == 3, "dependency expected outcomes differ")
    baseline = load(path.parent / "baseline.json")
    require(len(baseline) > 0 and len({pin["path"] for pin in baseline}) == len(baseline), "empty or duplicate dependency baseline")
    checked_pins({pin["path"]: pin["sha256"] for pin in baseline})
    for case, expected in zip(summary["cases"], registry):
        require(case["expected"] == expected["expected"] and case["restored"] is True and case["privateRestored"] is True, "dependency per-case verdict/restoration differs")
        exit_code = 1 if case["expected"] == "reject" else 0
        require(case["consumerExit"] == exit_code, "dependency expected consumer exit differs")
        producer = load(path.parent / f"{case['id']}-producer.json")["result"]
        consumer = load(path.parent / f"{case['id']}-consumer.json")["result"]
        process(producer, 0, True)
        process(consumer, exit_code, case["expected"] == "accept")
        require(producer["DeadlineSeconds"] == consumer["DeadlineSeconds"] == 120, "dependency compiler stage deadline differs")
        # This is exactly the documented production scratch-client serialization,
        # separate from the raw original-source pins checked above.
        client = (ROOT / expected["consumer"]).read_bytes().decode("utf-8").replace("\r\n", "\n").encode("utf-8")
        require(case["consumerHash"] == sha(client), "dependency scratch client identity differs")
    return lead + f"D local verification component RECORDED: exact ordered 26, 23 reject/3 accept, bounded producer/client receipts and nonempty restored baseline match; {reference(path)}; {reference(outer_path)}. Production diagnostic classification remains the source-bound runner's verdict, not a new classifier in this generator."


def controls_evidence(args) -> str:
    if args.controls_observed:
        return observed_controls_evidence(args)
    paths = (args.pwsh_controls, args.winps_controls, args.pwsh_registry_controls, args.winps_registry_controls)
    if not args.controls_complete:
        require(not any(paths), "control summaries supplied without explicit completion request")
        return "C: final full repair controls under pwsh and Windows PowerShell, plus both exact registry-boundary campaigns, remain PENDING. Development labels and both N full16 passes do not replace these campaigns."
    require(all(paths), "--controls-complete requires four explicit full control/registry summary paths")
    registry_path = HERE / "CONTROL_REGISTRY.frozen.json"
    registry = load(registry_path)
    narrow_path = HERE / "registry_control_cases.json"
    narrow = load(narrow_path)
    refs = []
    for profile, path, narrow_summary in (("pwsh", paths[0], paths[2]), ("winps", paths[1], paths[3])):
        value = load(path)
        expected = [case["id"] for case in registry["cases"] if profile in case["profiles"]]
        require(len(expected) == (67 if profile == "pwsh" else 66), "full control profile count differs")
        require(value["passed"] is True and value["profile"] == profile and value["registrySha256"] == sha(registry_path.read_bytes()), "control summary verdict/profile/registry differs")
        require(value["selected"] == expected and [item["id"] for item in value["results"]] == expected, "control exact ordered IDs differ")
        required = {"scripts/lifecycle_validator.ps1", "scripts/lifecycle_validator_environment.ps1", "scripts/lifecycle_dependency_replay.ps1",
                    "scripts/owned_process_tree.ps1", "scripts/lifecycle_dependency_cases.json", ".lake/build/bin/rmq_lifecycle_validate.exe",
                    "docs/internal/extensions/lifecycle1/repair-r1/run_controls.ps1", "docs/internal/extensions/lifecycle1/repair-r1/runtime_profile.ps1"}
        checked_pins(value["sourcePins"], required)
        require(sha(Path(value["shell"]).read_bytes()) == value["shellSha256"].lower(), "control runtime pin differs")
        for item in value["results"]:
            require(item["passed"] is True, "control result failed")
            child = load(Path(item["receipt"]))
            process(child)
            require(child["StandardError"] == [] and len(child["StandardOutput"]) == 1, "control child stream cardinality differs")
        n = load(narrow_summary)
        narrow_ids = [case["id"] for case in narrow["cases"]]
        require(len(narrow_ids) == 12 and n["passed"] is True and n["profile"] == profile and n["sourcesUnchanged"] is True, "registry-boundary summary incomplete")
        require(n["registrySha256"] == sha(narrow_path.read_bytes()) and n["selected"] == narrow_ids and [item["id"] for item in n["results"]] == narrow_ids, "registry-boundary exact IDs/pin differ")
        checked_pins(n["sourcePins"])
        require(n["stageError"] is None and n["integrityError"] is None, "registry-boundary finalization failed")
        for item in n["results"]:
            require(item["passed"] is True and item["positive"]["passed"] is True and item["challenged"]["passed"] is True, "registry P/Q pair incomplete")
        refs.extend((reference(path), reference(narrow_summary)))
    return "C local verification component RECORDED: exact pwsh67/Windows PowerShell66 profile IDs and both 12-control registry campaigns; source pins and bounded child outcomes match. " + "; ".join(refs) + "."


def observed_control_summary(path: Path, profile: str, registry: dict, partial: bool) -> dict:
    value = load(path)
    expected = [case["id"] for case in registry["cases"] if profile in case["profiles"]]
    require(len(expected) == (67 if profile == "pwsh" else 66), "observed full profile registry count differs")
    require(value["profile"] == profile and value["selected"] == expected and
            value["registrySha256"] == sha((HERE / "CONTROL_REGISTRY.frozen.json").read_bytes()), "observed profile/full selection/pin differs")
    observed_ids = expected[:32] if partial else expected
    if partial:
        require(expected[32] == "D01_OMITTED" and len([key for key in observed_ids if key.startswith("S")]) == 23 and
                len([key for key in observed_ids if key.startswith("W")]) == 9, "Windows observed prefix is not exact S23/W09")
    require(value["passed"] is (not partial) and [item["id"] for item in value["results"]] == observed_ids,
            "observed success prefix or campaign verdict differs")
    required = {"scripts/lifecycle_validator.ps1", "scripts/lifecycle_validator_environment.ps1", "scripts/lifecycle_dependency_replay.ps1",
                "scripts/owned_process_tree.ps1", "scripts/lifecycle_dependency_cases.json", ".lake/build/bin/rmq_lifecycle_validate.exe",
                "docs/internal/extensions/lifecycle1/repair-r1/run_controls.ps1", "docs/internal/extensions/lifecycle1/repair-r1/runtime_profile.ps1",
                "docs/internal/extensions/lifecycle1/repair-r1/dependency_child.ps1"}
    checked_pins(value["sourcePins"], required)
    require(sha(Path(value["shell"]).read_bytes()) == value["shellSha256"].lower(), "observed runtime file pin differs")
    require(value["runtime"]["profile"] == profile and value["runtime"]["sha256"].lower() == value["shellSha256"].lower(), "observed actual runtime contract differs")
    for item in value["results"]:
        require(item["passed"] is True, "observed prefix contains failure")
        result = load(Path(item["receipt"]))
        process(result)
        require(result["StandardError"] == [] and len(result["StandardOutput"]) == 1, "observed successful child stream cardinality differs")
        if partial:
            require(result["StandardOutput"] == [f"L1R1-CONTROL|{item['id']}|PASS"], "observed selector/wrapper terminal differs")
    return value


def observed_registry_summary(path: Path, profile: str) -> None:
    value = load(path)
    registry_path = HERE / "registry_control_cases.json"
    registry = load(registry_path)
    ids = [case["id"] for case in registry["cases"]]
    require(len(ids) == 12 and value["passed"] is True and value["profile"] == profile and value["sourcesUnchanged"] is True,
            "observed registry campaign did not pass")
    require(value["selected"] == ids and [item["id"] for item in value["results"]] == ids and
            value["registrySha256"] == sha(registry_path.read_bytes()), "observed exact registry mapping/IDs differ")
    require(value["stageError"] is None and value["integrityError"] is None, "observed registry campaign finalization failed")
    checked_pins(value["sourcePins"])
    for item, case in zip(value["results"], registry["cases"]):
        require(item["passed"] is True, "observed registry pair failed")
        for role, exit_code in (("positive", 0), ("challenged", case["expected"]["exit"])):
            member = item[role]
            require(member["passed"] is True and member["childAbsent"] is True and member["expectedExit"] == exit_code,
                    "observed registry P/Q outcome differs")
            result = load(Path(member["processReceipt"]))
            process(result, exit_code)
            if exit_code == 0:
                require(result["StandardError"] == [] and result["StandardOutput"] == [member["expectedOutput"]], "observed registry positive streams differ")
            else:
                require(result["StandardOutput"] == [] and result["StandardError"] == [member["expectedError"]] and
                        member["expectedError"] == case["expected"]["error"], "observed registry exact rejection differs")


def windows_control_invocation(outer: dict, case: str) -> None:
    spec = outer["spec"]
    arguments = spec["arguments"]

    def exact_argument(flag: str) -> str:
        require(arguments.count(flag) == 1, f"optional Windows invocation requires exactly one {flag}")
        index = arguments.index(flag)
        require(index + 1 < len(arguments), f"optional Windows invocation is missing {flag} value")
        return arguments[index + 1]

    expected_shell = Path("C:/Windows/System32/WindowsPowerShell/v1.0/powershell.exe").resolve()
    require(Path(spec["file"]).resolve() == expected_shell and Path(exact_argument("-Shell")).resolve() == expected_shell,
            "optional Windows invocation used a different shell")
    require(exact_argument("-Profile") == "winps" and exact_argument("-OnlyCase") == case,
            "optional Windows invocation profile/case differs")
    require(Path(exact_argument("-File")).resolve() == (HERE / "run_controls.ps1").resolve(),
            "optional Windows invocation did not use the production repair driver")
    require(arguments.count("-RegistryPath") <= 1, "optional Windows invocation repeats RegistryPath")
    # The current frozen driver resolves an omitted RegistryPath in its body,
    # after PSScriptRoot is established. Its actual summary and current source
    # pins are independently checked by the caller; run labels are not verdicts.
    registry_path = Path(exact_argument("-RegistryPath")) if "-RegistryPath" in arguments else HERE / "CONTROL_REGISTRY.json"
    require(registry_path.is_absolute() and registry_path.resolve() == (HERE / "CONTROL_REGISTRY.json").resolve() and
            registry_path.read_bytes() == (HERE / "CONTROL_REGISTRY.frozen.json").read_bytes(),
            "optional Windows invocation did not use the exact frozen-registry working path")


def observed_deadline(path: Path) -> str:
    outer = load(path)
    windows_control_invocation(outer, "T01_DESCENDANT_TIMEOUT")
    process(outer["result"])
    require(outer["result"]["StandardError"] == [], "optional Windows deadline outer stderr differs")
    checked_pins(outer["sources"], REQUIRED_CHECK_PINS)
    arguments = outer["spec"]["arguments"]
    directory = Path(arguments[arguments.index("-EvidenceRoot") + 1])
    summary = load(directory / "summary.json")
    require(summary["passed"] is True and summary["profile"] == "winps" and summary["selected"] == ["T01_DESCENDANT_TIMEOUT"] and
            [item["id"] for item in summary["results"]] == ["T01_DESCENDANT_TIMEOUT"], "optional deadline selected result differs")
    checked_pins(summary["sourcePins"])
    fixture_path = directory / "T01_DESCENDANT_TIMEOUT/fixture/result.json"
    fixture = load(fixture_path)
    result = fixture["result"]
    require(fixture["passed"] is True and fixture["environmentRestored"] is True and result["TimedOut"] is True and
            result["OutputLimitExceeded"] is False and result["ExitCode"] == -1 and result["DeadlineSeconds"] == 6 and
            result["Ownership"] == "kill-on-close-job" and result["StandardOutput"] == result["StandardError"] == [],
            "optional Windows actual timeout disposition differs")
    require(len(result["TerminatedIds"]) >= 2 and fixture["pids"]["descendant"] in result["TerminatedIds"] and
            fixture["pids"]["root"] in fixture["allObservedAbsent"] and fixture["pids"]["descendant"] in fixture["allObservedAbsent"],
            "optional Windows root/descendant receipt incomplete")
    checked_pins({"scripts/owned_process_tree.ps1": fixture["helperSha256"],
                  "scripts/lifecycle_validator_environment.ps1": fixture["adapterSha256"]})
    return f"Separate Windows T01 observed PASS with the real bounded sleeper/descendant receipt: {reference(path)}; {reference(fixture_path)}."


def observed_finalizer(path: Path) -> str:
    outer = load(path)
    windows_control_invocation(outer, "F01_INTACT_SUCCESS")
    process(outer["result"], 1)
    require(outer["result"]["StandardOutput"] == [], "optional blocked finalizer emitted outer success/output")
    checked_pins(outer["sources"], REQUIRED_CHECK_PINS)
    arguments = outer["spec"]["arguments"]
    directory = Path(arguments[arguments.index("-EvidenceRoot") + 1])
    summary = load(directory / "summary.json")
    require(summary["passed"] is False and summary["profile"] == "winps" and summary["selected"] == ["F01_INTACT_SUCCESS"] and
            summary["results"] == [], "optional finalizer campaign verdict differs")
    checked_pins(summary["sourcePins"])
    fixtures = list((directory / "F01_INTACT_SUCCESS/fixtures").glob("F01_INTACT_SUCCESS-*/result.json"))
    require(len(fixtures) == 1, "optional source-bound finalizer result absent or ambiguous")
    leaf_path = fixtures[0]
    leaf = load(leaf_path)
    require(leaf["id"] == "F01_INTACT_SUCCESS" and leaf["passed"] is False and leaf["records"] == [] and
            leaf["error"] == "L1R1-FINALIZER: P unexpected child exit: 1", "optional finalizer did not fail at the exact intact P boundary")
    require(leaf["source"]["sourceSha256"] == sha((ROOT / "scripts/lifecycle_dependency_replay.ps1").read_bytes()), "optional finalizer production source pin differs")
    process_result = load(leaf_path.parent / "P/process.json")
    process(process_result, 1)
    require(process_result["StandardOutput"] == [] and process_result["StandardError"] == [HASHDATA_ERROR], "optional finalizer P did not produce the exact protected HashData failure")
    production = load(leaf_path.parent / "P/production-evidence/summary.json")
    require(production["passed"] is False and production["stageError"] == HASHDATA_ERROR and production["integrityError"] is None and
            production["cleanupError"] is None, "optional finalizer exact production error category differs")
    entry = load(leaf_path.parent / "P/production-evidence/fixture-finally-entry.json")
    require(entry["enteredMain"] is True and entry["baselineCount"] == 0 and production["restored"] is True and production["shadowRemoved"] is True,
            "optional finalizer failed-capture/cleanup disposition differs")
    return f"Separate Windows F01 intact P observed BLOCKED at protected Hash-Bytes with its exact source pin and HashData error: {reference(path)}; {reference(leaf_path)}. Its capture failed before retaining any pins; restored=true covers an empty baseline only. This is not an accepted negative control."


def observed_controls_evidence(args) -> str:
    paths = (args.pwsh_controls, args.winps_controls, args.pwsh_registry_controls, args.winps_registry_controls)
    require(all(paths), "--controls-observed requires four explicit control/registry summary paths")
    registry = load(HERE / "CONTROL_REGISTRY.frozen.json")
    observed_control_summary(paths[0], "pwsh", registry, False)
    observed_control_summary(paths[1], "winps", registry, True)
    observed_registry_summary(paths[2], "pwsh")
    observed_registry_summary(paths[3], "winps")
    failure_directory = paths[1].parent / "D01_OMITTED"
    failure_path = failure_directory / "process.json"
    failure = load(failure_path)
    process(failure, 1)
    require(failure["StandardOutput"] == [], "Windows D01 blocker emitted unexpected stdout")
    require("CONTROL: exact same-root positive boundary failed" in "\n".join(failure["StandardError"]), "Windows D01 did not fail at its same-root positive boundary")
    positive_path = failure_directory / "fixture/positive.json"
    positive = load(positive_path)
    require(positive["exit"] == 1 and positive["stdout"] == [] and positive["stderr"] == HASHDATA_ERROR + "\r\n" and
            Path(positive["scriptPath"]).resolve() == (ROOT / "scripts/lifecycle_dependency_replay.ps1").resolve(),
            "Windows D01 actual positive did not produce the exact protected HashData failure")
    supplemental = []
    if args.winps_deadline_receipt:
        supplemental.append(observed_deadline(args.winps_deadline_receipt))
    if args.winps_finalizer_receipt:
        supplemental.append(observed_finalizer(args.winps_finalizer_receipt))
    references = "; ".join(reference(path) for path in (*paths, failure_path, positive_path))
    return ("C: BLOCKED_REQUIRED_WINDOWS_DEPENDENCY_AND_FINALIZER_CONTROLS. Actual current-runtime67 controls passed; "
            "Windows selected all66 but passed only the exact first32 (S01..S23 and W01..W09), then D01 failed on the exact protected HashData API error in its positive boundary. "
            "Both 12-control registry campaigns passed. The complete Windows66 requirement remains live; observed evidence does not set controlsComplete. "
            f"Receipts: {references}.\n\n"
            "Historical harness failures: the earlier Windows driver evaluated its default RegistryPath before PSScriptRoot was established, and a separate W01 receipt-array wrapping error caused a count failure after production startup passed. "
            "Control source freeze 7c406b15bdc12333d323c92641ab6c6dad6af7a2 moves registry-default initialization into the driver body and reads JSON receipt arrays directly. "
            "The fresh Windows32 prefix includes W01 success on the corrected source; these historical harness failures are not current failure claims. "
            "The exact registry-byte checks and the separate protected HashData blocker remain in force. " + " ".join(supplemental))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    parser.add_argument("--dependency-complete", action="store_true")
    parser.add_argument("--dependency-summary", type=Path)
    controls_mode = parser.add_mutually_exclusive_group()
    controls_mode.add_argument("--controls-complete", action="store_true")
    controls_mode.add_argument("--controls-observed", action="store_true")
    parser.add_argument("--pwsh-controls", type=Path)
    parser.add_argument("--winps-controls", type=Path)
    parser.add_argument("--pwsh-registry-controls", type=Path)
    parser.add_argument("--winps-registry-controls", type=Path)
    parser.add_argument("--winps-deadline-receipt", type=Path)
    parser.add_argument("--winps-finalizer-receipt", type=Path)
    args = parser.parse_args()
    require(args.controls_observed or not (args.winps_deadline_receipt or args.winps_finalizer_receipt),
            "optional Windows blocker receipts require --controls-observed")
    contract = load(HERE / "CONTRACT.json")
    ids = contract["orderedIds"]
    require(len(ids) == 45 and len(set(ids)) == 45 and ids[-2:] == ["L1R1-SELECTOR", "L1R1-CLEANUP"], "exact43+2 ID contract differs")
    require(list(contract["requirements"]) == ids and contract["base"] == BASE, "contract ordered requirements/base differ")
    manifest = load(HERE / "INITIAL_WORKING_FILES.json")
    historical_path = ROOT / "docs/internal/extensions/lifecycle1/ACCEPTANCE_EVIDENCE.md"
    require(sha(historical_path.read_bytes()) == manifest[historical_path.relative_to(ROOT).as_posix()]["sha256"], "historical evidence bytes changed")
    historical = historical_path.read_bytes().decode("utf-8", errors="strict")
    rows = []
    for line in historical.splitlines():
        if not line.startswith("| `"):
            continue
        cells = line.split("|")
        require(len(cells) == 7, "historical five-column table shape differs")
        rows.append((cells[1].strip().strip("`"), cells[2]))
    require([key for key, _ in rows] == ids[:43], "historical exact ordered43 IDs differ")
    # Reuse is based on unchanged actual Lean/consumer bytes, not on a prior
    # status label. Each quoted cell remains historical, with its live guards.
    reused = [name for name in manifest if name.endswith(".lean") or name in ("lean-toolchain", "lakefile.toml")]
    checked_pins({name: manifest[name]["sha256"] for name in reused})
    families = [build_evidence(), native_evidence(), dependency_evidence(args), controls_evidence(args)]
    lines = ["# LIFE-1-R1 row dispositions", "",
             "Status: BLOCKED. Formal evidence reusable; final delivery blocked. These 45 dispositions do not record coordinator acceptance or campaign closure.", "",
             "Every inherited proposition/object-chain cell below is quoted exactly from the original historical ACCEPTANCE_EVIDENCE.md cell, including its cell padding. Historical candidate-closure labels are not copied as current dispositions.", "",
             "Live guards: actual is Continuous.continuousRun model xs left right; initial is the supplied state at Layout.builderBase; cells=buildMemory xs; M=cells.length; B=producer.regs3; n=xs.length; W=wordWidth n. Public guards remain InputDomain model xs and endpoints below 2^W. Word input uses InputFits; comparison input retains separately counted arbitrary-Int resources.", "",
             f"Historical source: {reference(historical_path)}. Current reuse checks cover {len(reused)} exact initial Lean/consumer/toolchain byte identities. No new Lean proof, theorem type, assumption, native capacity claim, or arbitrary-Int bit bound follows from this repair.", "",
             "The S delivery gate applies to every row: final source/receipt/report identities, original contract integrity, strict claim/design checks, scoped committed delivery, and required runtime controls remain mandatory. Original protected contract working files retain inherited CRLF bytes and fail the original raw hash gate. Windows PowerShell cannot execute the protected Hash-Bytes implementation's modern .NET APIs; its required source-derived cleanup controls remain blocked pending coordinator direction.", "",
             "Available process evidence uses the protected helper's returned nonempty lines. It is not complete raw stream identity; overflow or exceptional cleanup can prevent output recovery. No missing evidence is promoted to a pass.", "",
             "## Fresh verification families", ""]
    for family in families:
        lines.extend((family, ""))
    quotes = dict(rows)
    for key in ids:
        lines.extend((f"### Evidence for {key}", ""))
        if key in quotes:
            lines.extend(("Historical proposition/object-chain cell, quoted without rewriting:", "", "> \u201c" + quotes[key] + "\u201d", ""))
        else:
            lines.extend(("New repair row; no historical formal proposition is asserted. The frozen requirement remains in CONTRACT.json and the 45-row matrix.", ""))
        if key in DIRECT_BLOCKERS:
            status = "BLOCKED_LOCAL_VERIFICATION; formal evidence reusable where applicable; final delivery blocked."
            detail = "Direct blockers: Windows PowerShell protected Hash-Bytes API availability and original protected working-file serialization; S applies."
        elif key == "L1R1-SELECTOR":
            status = ("LOCAL_VERIFICATION_COMPONENT_RECORDED" if args.controls_complete else
                      "OBSERVED_SELECTOR_COMPONENTS" if args.controls_observed else "PENDING_FINAL_CONTROLS") + "; final delivery blocked."
            detail = ("Both production full16 wrappers and the Windows32 selector/wrapper components are observed; the full C requirement and global S remain blocked."
                      if args.controls_observed else "Both production full16 wrappers passed; final C evidence and S remain required.")
        else:
            status = "UNCHANGED_FORMAL_EVIDENCE_REUSED; formal evidence reusable; final delivery blocked."
            detail = "The quoted historical formal chain is reused only under its unchanged source and stated guards; S applies."
        lines.extend((f"Disposition: {status}", "", detail, "",
                      "Fresh references: B and N above; D prerequisites passed; " +
                      ("D full26 component recorded." if args.dependency_complete else "D full26 pending.") + " " +
                      ("C component recorded." if args.controls_complete else "C partial observations recorded; required Windows dependency/finalizer controls blocked."
                       if args.controls_observed else "C final controls pending."), ""))
    content = "\n".join(lines)
    require(re.findall(r"(?m)^### Evidence for (.+)$", content) == ids, "generated exact45-ID appendix differs")
    for key, cell in rows:
        require(("> \u201c" + cell + "\u201d") in content, f"historical cell quote changed: {key}")
    output = HERE / "ROW_DISPOSITIONS.md"
    require(not output.is_symlink(), "row disposition output must be a regular scoped file")
    output.write_bytes(content.encode("utf-8"))
    print(json.dumps({"path": str(output), "bytes": len(output.read_bytes()), "sha256": sha(output.read_bytes()),
                      "ids": 45, "historicalExactCells": 43, "reusedSourcePins": len(reused),
                      "dependencyComplete": args.dependency_complete, "controlsComplete": args.controls_complete,
                      "controlsObserved": args.controls_observed,
                      "status": "BLOCKED; final delivery blocked"}))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError, KeyError, TypeError, IndexError) as error:
        print(f"ROW-DISPOSITIONS: FAIL {error}", file=sys.stderr)
        raise SystemExit(1)
