"""Compose R3 evidence using the protected R2 receipt parsers.

This collector reads retained facts; the recorded PowerShell predicates remain
the production verdicts. Historical profiles remain historical executions.
"""
import argparse
import base64
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import time

sys.dont_write_bytecode = True
ROOT = next(p for p in Path(__file__).resolve().parents
            if (p / "lean-toolchain").is_file() and (p / "scripts").is_dir())
NATIVE = ROOT / "docs/internal/extensions/lifecycle-native-p0"
HERE = NATIVE / "repair-r3"
BASE = "9519b2c1af5e2cf59536b311db5e8dc81376a32f"
REGISTRY_SHA = "16E26C5B131BBE258B3813BCDB252414E8BED454EF6286EB2ED7F7EF3496261D"
RETAINED_SHA = "521BFA0CD6DEE84383AB41F8B7D6CC0F226EEFABFC96113EF5EBE835A48A20EB"
PARSER = NATIVE / "repair-r2/verify_results.py"
if hashlib.sha256(PARSER.read_bytes()).hexdigest().upper() != "CE931FD260A5FDA818E06BEEF1C66C6152189B46984FC4510EB445376244CAD2":
    raise ValueError("protected R2 receipt parser byte identity")
spec = importlib.util.spec_from_file_location("r3_reused_r2_results", PARSER)
V = importlib.util.module_from_spec(spec)
spec.loader.exec_module(V)
# Only the explicit current-source consumers use this parser instance. Its
# registry directory remains repair-r2; no historical parser file is changed.
V.ROOT, V.BASE = ROOT, BASE
need, readj, NL = V.need, V.readj, V.NL


def same_path(a, b):
    return Path(a).resolve() == Path(b).resolve()


def frozen(path, digest, pins):
    pin = pins.add(path)
    need(pin["sha256"] == digest, "frozen registry byte identity: " + str(path))
    return readj(path)


def artifact_capture(capture, pins):
    """Bind a row to its actually retained CAPTURE.json when one exists."""
    path = Path(capture["spec"]["stdout"]).parent / "CAPTURE.json"
    need(path.is_file(), "actual emitted capture record missing")
    pins.add(path)
    need(readj(path) == capture, "recorded capture object differs from raw capture record")


def captured_driver(capture, driver):
    args = capture["spec"]["arguments"]
    need(len(args) == 3 and args[:2] == ["-NoProfile", "-File"] and same_path(args[2], driver["path"]) and
         same_path(capture["spec"]["cwd"], ROOT), "actual captured driver/working-directory identity")


def groups(paths, registry, pins, head):
    all_rows, facts, source_heads = [], [], []
    for path in paths:
        launch = readj(path); launch_pin = pins.add(path)
        group, selected = launch["group"], launch["selected"]
        need(group in ["tiny", "focused", "integrity"] and launch["failure"] is None, "group identity/failure")
        allowed = [r["id"] for r in registry["controls"]
                   if (r["mode"] in ["literal", "selector"] if group == "tiny" else r["mode"] == group)]
        need(selected and all(key in allowed for key in selected), "group requested mode/IDs")
        V.roster(selected, [key for key in allowed if key in selected], "group requested ordered subset")
        result_path = Path(launch["results"]); result = readj(result_path); pins.add(result_path)
        expected = "".join("R3 CONTROL PASS " + x + NL for x in selected)
        expected += "R3 CONTROLS evidence=" + str(result_path.parent) + NL
        need((launch["expectedStdout"], launch["expectedStderr"], launch["expectedExit"]) ==
             (expected, "", 0), "group declared full stream contract")
        V.capture(launch["capture"], pins, expected, "", 0)
        artifact_capture(launch["capture"], pins)
        need(launch["capture"]["launcher"]["DeadlineSeconds"] == (1200 if group == "focused" else 300),
             "group deadline contract")
        for key in ["driver", "launcherScript"]:
            pins.walk(launch[key])
        captured_driver(launch["capture"], launch["driver"])
        need(result["head"] == launch["head"] and result["failure"] is None and
             result["integrityFailure"] is None and result["candidateUnchanged"] is True,
             "group source head/final integrity")
        V.git("merge-base", "--is-ancestor", result["head"], head)
        source_heads.append(result["head"])
        pins.walk(result["sourcePins"])
        required_sources = [HERE / "literal_selector_controls.ps1", HERE / "CONTROL_REGISTRY.json",
            NATIVE / "repair-r2/certify_profiles.ps1", ROOT / "scripts/packed_native_lifecycle_stream_check.ps1",
            ROOT / "scripts/owned_process_tree.ps1", ROOT / "scripts/packed_native_lifecycle_storage_replay.ps1",
            NATIVE / "repair-r1/run_owned.ps1", NATIVE / "repair-r1/integrity_controls.ps1",
            NATIVE / "repair-r2/harness_stream_controls.ps1"]
        V.roster([str(Path(p["path"]).resolve()) for p in result["sourcePins"]],
                 [str(p.resolve()) for p in required_sources], "group exact source pins")
        need(result["omittedDefaultProfiles"] == registry["defaultProfiles"], "omitted selector default roster")
        V.roster(result["selected"], selected, "group executed selection")
        V.roster([r["id"] for r in result["controls"]], selected, "group complete records")
        for record in result["controls"]:
            row = next(r for r in registry["controls"] if r["id"] == record["id"])
            for key in ["id", "mode", "predicate", "tier", "verdict"]:
                need(record[key] == row[key], "new registry object/predicate/verdict mapping")
            pins.walk(record["driver"])
            c = record["capture"]; artifact_capture(c, pins)
            captured_driver(c, record["driver"])
            if row["mode"] == "literal":
                emitted = [base64.b64decode(row[key], validate=True) for key in ["stdout", "stderr"]]
                for key, expected_bytes in zip(["stdout", "stderr"], emitted):
                    need(Path(c["spec"][key]).read_bytes() == expected_bytes, "actual prescribed emitted bytes")
                if row["failure"] == "invalid-utf8":
                    pins.add(c["spec"]["exit"])
                    need(readj(c["spec"]["exit"]) == c["actual"], "malformed case actual ordinary exit artifact")
                    # R2.capture checks all transport/ordinary-exit guards before
                    # decoding. Its strict decoder must reject these known bytes.
                    try:
                        V.capture(c, pins, "", "", row["exit"])
                    except UnicodeDecodeError:
                        pass
                    else:
                        raise ValueError("malformed UTF-8 was decoded")
                    wanted = "STREAM: invalid UTF-8 capture: " + c["spec"]["stdout"]
                else:
                    V.capture(c, pins, emitted[0].decode("utf-8"), emitted[1].decode("utf-8"), row["exit"])
                    prescribed = [base64.b64decode(row[key], validate=True)
                                  for key in ["expectedStdout", "expectedStderr"]]
                    need((emitted == prescribed) == (row["verdict"] == "accept"), "literal independent byte verdict")
                    wanted = None if row["verdict"] == "accept" else row["failure"]
                need(record["failure"] == wanted and record["childAbsent"] is True,
                     "literal actual production rejection/cleanup")
                need(c["launcher"]["DeadlineSeconds"] == 60, "tiny child deadline")
            elif row["mode"] == "selector":
                V.capture(c, pins, "BOUNDARY REJECTED " + row["id"] + NL, "", 0)
                need(record["failure"] == row["failure"] and record["noWorkBeforeRejection"] is True,
                     "direct selector verdict/no-work marker")
                need(not (Path(record["driver"]["path"]).parent / "must-not-exist").exists(),
                     "rejected selector created output")
                driver = V.raw(record["driver"]["path"])
                need("-Kinds " + row["expression"] + ";throw 'UNEXPECTED NORMAL RETURN'" in driver,
                     "actual selector expression/normal-return trap")
            elif row["mode"] == "focused":
                pins.walk(record["manifest"]); pins.walk(record["receipt"]); pins.walk(record["summary"])
                manifest = readj(record["manifest"]["path"])
                need(set(manifest["profiles"]) == {"focused"} and manifest["head"] == result["head"] and
                     same_path(manifest["profiles"]["focused"], record["receipt"]["path"]),
                     "actual focused manifest is exactly one executed profile")
                output = Path(record["manifest"]["path"]).parent
                expected = "OWNED focused exit=0 evidence=" + str(output / "focused") + NL
                expected += "PROFILE CERTIFIED focused manifest=" + record["manifest"]["path"] + NL
                V.capture(c, pins, expected, "", 0)
                receipt, inner, _ = V.profile_receipt("focused", record["receipt"]["path"], pins)
                need(record["validation"] == receipt["streamValidation"], "focused same full production predicate")
                native = V.native_summary("focused", V.raw(inner["spec"]["stdout"]), pins)
                need(native["summary"] == record["summary"] and native["selected"] == ["pop-unique"],
                     "focused same actual native object")
            else:
                need(row["mode"] == "integrity", "unsupported new control mode")
                pins.walk(record["results"])
                target = Path(record["results"]["path"]).parent
                expected = "STREAM CONTROL PASS success-positive" + NL + "STREAM CONTROL PASS error-positive" + NL
                expected += "STREAM CONTROLS evidence=" + str(target) + NL
                V.capture(c, pins, expected, "", 0)
                harness = readj(record["results"]["path"])
                V.roster(harness["selected"], ["success-positive", "error-positive"], "actual integrity pair")
                V.verify_harness(record["results"]["path"], pins, complete=False)
            all_rows.append(record)
        facts.append(dict(group=group, launch=launch_pin, results=pins.add(result_path), selected=selected))
    need(len(set(source_heads)) == 1, "groups did not test one source freeze")
    V.roster([r["id"] for r in all_rows], [r["id"] for r in registry["controls"]], "all37 actual new controls")
    return facts, all_rows, source_heads[0]


def retained(path, contract, registry, pins, head, contract_path):
    r = readj(path); result_pin = pins.add(path); pins.walk(r["pins"])
    root = Path(path).resolve().parent
    launch_path = Path(str(root) + "-outer") / "LAUNCH.json"
    pins.add(launch_path); launch = readj(launch_path)
    need(launch["head"] == head and launch["failure"] is None and same_path(launch["results"], path),
         "actual final retained launch/result identity")
    expected = "R3 RETAINED PASS cases=40 evidence=" + str(root) + NL
    need((launch["expectedStdout"], launch["expectedStderr"], launch["expectedExit"]) == (expected, "", 0),
         "final retained declared complete output")
    c = launch["capture"]; V.capture(c, pins, expected, "", 0); artifact_capture(c, pins)
    args = c["spec"]["arguments"]
    need(len(args) == 7 and args[:2] == ["-NoProfile", "-File"] and
         same_path(args[2], HERE / "revalidate_retained.ps1") and args[3] == "-ContractPath" and
         same_path(args[4], contract_path) and args[5] == "-OutputRoot" and same_path(args[6], root) and
         same_path(c["spec"]["cwd"], ROOT) and c["launcher"]["DeadlineSeconds"] == 300,
         "actual retained exact command/deadline")
    pins.walk(launch["driver"]); pins.walk(launch["launcherScript"])
    need(same_path(launch["driver"]["path"], HERE / "revalidate_retained.ps1"), "retained actual driver pin")
    need(r["success"] is True and r["failure"] is None and r["currentHead"] == head and
         r["oldHead"] == BASE and same_path(r["historicalRoot"], registry["historicalRoot"]),
         "final retained candidate/historical identities")
    integrity = r["finalIntegrity"]
    need(integrity["attempted"] is True and integrity["success"] is True and integrity["errors"] == [] and
         integrity["restorationWrites"] == 0 and integrity["checkedPins"] == len(r["pins"]),
         "retained independent final pin/tree outcome")
    contracts = contract["retainedContracts"]
    ids = ["profile-" + key for key in registry["profiles"]] + ["integrity-" + key for key in registry["integrity"]]
    V.roster([c["id"] for c in contracts], ids, "retained independent21 contracts")
    tiers = [("root", "historical-actual-root-child"), ("leaf", "historical-actual-leaf-child"),
             ("copiedFocused", "historical-copied-focused"), ("syntheticLauncher", "synthetic-launcher-component")]
    ids += [tier + "/" + row["id"] for category, tier in tiers for row in registry[category]]
    V.roster([row["id"] for row in r["registry"]], ids, "retained40 exact ordered cases")
    for row, declared in zip(r["registry"][:21], contracts):
        for key in ["capture", "expectedStdout", "expectedStderr", "expectedExit", "producingRoot"]:
            need(row[key] == declared[key], "retained contract object/expected string identity")
        need(row["tier"] == "retained-historical-capture" and row["predicate"] == "Assert-LNOuterCapture" and
             row["Q"] == dict(accepted=True, failure=None), "retained21 literal production acceptance")
        V.capture(row["capture"], pins, row["expectedStdout"], row["expectedStderr"], row["expectedExit"])
        pins.walk(declared["sourcePins"]); pins.walk(declared["rawPins"])
    index = 21
    for category, tier in tiers:
        for definition in registry[category]:
            row = r["registry"][index]; index += 1
            need(row["tier"] == tier and row["Q"] == dict(accepted=definition["currentAccept"], failure=definition["failure"]),
                 "retained exact current verdict/tier")
            need(row["P"] == dict(accepted=definition["oldAccept"], failure=None if definition["oldAccept"] else definition["failure"]),
                 "retained exact old accepted/rejected verdict")
            c, name = row["capture"], definition["id"]
            out, err = row["expectedStdout"], row["expectedStderr"]
            if category == "root":
                expected_err = "" if name == "otherwise-empty-bom" else "PROCESS: expected failure" + NL
                need((out, err, row["expectedExit"], row["profile"]) ==
                     ("", expected_err, 0 if name == "otherwise-empty-bom" else 7, name), "root prescribed contract")
                if name == "error-plus-ascii": err += "UNEXPECTED OUTER DIAGNOSTIC" + NL
                if name in ["error-plus-bom", "otherwise-empty-bom"]: err += "\ufeff"
            elif category == "leaf":
                need((out, err, row["expectedExit"], row["profile"]) ==
                     ("component evidence" + NL, "PROCESS: declared component failure" + NL, 1, "process-component"),
                     "leaf prescribed contract")
                if name == "nul-stdout": out += "\0"
                if name == "bom-stdout": out = "\ufeff" + out
                if name == "extra-error-words": err += "UNEXPECTED OUTER DIAGNOSTIC" + NL
            else:
                focused = contract["retainedContracts"][0]
                need(focused["id"] == "profile-focused" and (out, err, row["expectedExit"], row["profile"]) ==
                     (focused["expectedStdout"], "", 0, "wrapper-focused"), "copied focused independent baseline contract")
                if name == "trailing-nul-stdout": out += "\0"
                if name == "leading-bom-stdout": out = "\ufeff" + out
                if name == "nul-only-stderr": err = "\0"
                if name == "extra-error-words": err = "UNEXPECTED OUTER DIAGNOSTIC" + NL
            expected_predicate = "Assert-LNWrapperCapture focused -> Assert-LNOuterCapture" if category in ["copiedFocused", "syntheticLauncher"] else "Assert-LNOuterCapture"
            need(row["predicate"] == expected_predicate, "retained production predicate mapping")
            if category != "syntheticLauncher":
                V.capture(c, pins, out, err, row["expectedExit"])
            else:
                # The R2 helper supports blank-launcher mutations only. Inspect
                # this explicitly synthetic Unicode component, retaining its
                # original ordinary exits/transport and exact child bytes.
                pins.walk(c["raw"]); launch, spec = c["launcher"], c["spec"]
                V.ordinary(launch, c["actual"], 0)
                need(not launch["StandardOutput"] and not launch["StandardError"] and not launch["RetentionErrors"] and
                     not Path(spec["error"]).exists() and not Path(spec["overflow"]).exists(), "synthetic retained transport guards")
                need(V.raw(spec["stdout"]) == out and V.raw(spec["stderr"]) == err, "synthetic unchanged child streams")
                for channel, key in [("stdout", "RawStandardOutput"), ("stderr", "RawStandardError")]:
                    need(V.raw(launch[key]) == (chr(definition["codepoint"]) if definition["channel"] == channel else ""),
                         "synthetic prescribed launcher component")
    return dict(results=result_pin, launch=pins.add(launch_path), cases=ids, finalIntegrity=integrity,
                tiers={"retainedHistorical": 21, "actualRoot": 4, "actualLeaf": 4, "copiedFocused": 5, "syntheticLauncher": 6})


def current_run(path, profiles_path, rows, contract, pins, head):
    launch = readj(path); launch_pin = pins.add(path)
    result_path = Path(launch["results"]); root = result_path.resolve().parent
    result = readj(result_path); pins.add(result_path)
    need(launch["head"] == result["head"] == head and launch["failure"] is None and result["success"] is True and
         result["failure"] is None and result["base"] == BASE and same_path(result["worktree"], ROOT),
         "actual final current invocation identity/outcome")
    integrity = result["finalIntegrity"]
    need(integrity == dict(attempted=True, success=True, errors=[]), "current final independent integrity")
    expected = ""
    for kind in ["checks", "claims"]:
        expected += "OWNED " + kind + " exit=0 evidence=" + str(root / "profiles" / kind) + NL
        expected += "PROFILE CERTIFIED " + kind + " manifest=" + str(root / "profiles/PROFILES.json") + NL
    expected += "CURRENT PROFILES PASS evidence=" + str(root) + NL
    need((launch["expectedStdout"], launch["expectedStderr"], launch["expectedExit"]) == (expected, "", 0),
         "current entire actual outer stream contract")
    c = launch["capture"]; V.capture(c, pins, expected, "", 0); artifact_capture(c, pins)
    args = c["spec"]["arguments"]
    need(len(args) == 9 and args[:2] == ["-NoProfile", "-File"] and same_path(args[2], HERE / "certify_current.ps1") and
         args[3] == "-OutputRoot" and same_path(args[4], root) and args[5] == "-FocusedManifest" and
         same_path(args[6], result["focusedManifest"]["path"]) and args[7] == "-HistoricalContract" and
         same_path(args[8], result["historicalContract"]["path"]) and same_path(c["spec"]["cwd"], ROOT) and
         c["launcher"]["DeadlineSeconds"] == launch["deadlineSeconds"] == 1200,
         "actual final current exact arguments/working-directory/deadline")
    pins.walk(launch["driver"]); pins.walk(launch["launcherScript"])
    need(same_path(launch["driver"]["path"], HERE / "certify_current.ps1"), "current actual versioned driver pin")
    for key in ["sourcePins", "focusedManifest", "historicalContract", "seed", "profiles"]:
        pins.walk(result[key])
    required = [HERE / "certify_current.ps1", NATIVE / "repair-r2/certify_profiles.ps1", NATIVE / "repair-r1/run_owned.ps1",
                NATIVE / "repair-r1/final_checks.ps1", NATIVE / "repair-r2/claim_expectations.ps1",
                ROOT / "scripts/owned_process_tree.ps1", ROOT / "scripts/packed_native_lifecycle_stream_check.ps1",
                ROOT / "scripts/packed_native_lifecycle_integrity_check.ps1"]
    V.roster([str(Path(p["path"]).resolve()) for p in result["sourcePins"]], [str(p.resolve()) for p in required],
             "final invocation exact source pins")
    focused = next(row for row in rows if row["id"] == "selector-focused")
    need(result["focusedManifest"] == focused["manifest"], "final invocation actual focused input identity")
    history = readj(result["historicalContract"]["path"])
    need(history["success"] is True and history["mode"] == "full-contract" and history["base"] == BASE and
         history["historicalR2"] == contract["historicalR2"], "seed same reviewed historical facts")
    seed = readj(result["seed"]["path"])
    expected_seed = {kind: contract["historicalR2"]["profiles"][kind]["receipt"]["path"]
                     for kind in ["full", "integrity", "dependencies"]}
    expected_seed["focused"] = focused["receipt"]["path"]
    need(seed == dict(head=head, profiles=expected_seed), "final exact four-profile seed")
    need(same_path(result["profiles"]["path"], profiles_path) and
         same_path(profiles_path, root / "profiles/PROFILES.json"), "actual final composed manifest identity")
    manifest = readj(profiles_path)
    for kind in ["checks", "claims"]:
        need(same_path(manifest["profiles"][kind], root / "profiles" / kind / "RECEIPT.json"), "actual fresh profile receipt join")
    before, after = result["before"], result["after"]
    need(before == after and before["head"] == head and result["initialStatus"] == result["finalStatus"] == [],
         "current actual clean identical before/after source snapshots")
    need(before["index"] == V.git("ls-files", "--stage", "-z").decode("utf-8"), "current semantic index equals producing snapshot")
    paths = set(V.git("ls-files", "--cached", "--others", "--exclude-standard", "-z").decode("utf-8").split("\0")) - {""}
    V.roster([p["path"] for p in before["files"]], sorted(paths), "current tracked/untracked exact snapshot roster", ordered=False)
    for pin in before["files"]:
        need("missing" not in pin, "missing producing source file")
        pins.add(ROOT / pin["path"], pin)
    need(result["scanInputsBefore"] == result["scanInputsAfter"], "current all scanned bytes unchanged around actual invocation")
    scan_paths = {str(p.resolve()) for p in NATIVE.rglob("*") if p.is_file()}
    scan_paths.update(str((ROOT / p).resolve()) for p in ["docs/internal/DESIGN_DECISIONS.md", "docs/internal/WORKFLOW_DESIGN_DECISIONS.md"])
    V.roster([str(Path(p["path"]).resolve()) for p in result["scanInputsBefore"]], sorted(scan_paths), "complete actual scan input byte inventory", ordered=False)
    pins.walk(result["scanInputsBefore"])
    return dict(launch=launch_pin, results=pins.add(result_path), head=head, scanInputCount=len(scan_paths), finalIntegrity=integrity)


def final_checks(stdout, capture, pins, head, contract_path):
    facts = V.check_results(stdout, pins); result = readj(facts["results"]["path"])
    need(result["head"] == head, "fresh final checks must certify current HEAD")
    checks = {row["name"]: row for row in result["checks"]}
    check_root = Path(facts["results"]["path"]).parent
    commands = {
        "hygiene": ("rg", ["-n", r"\b(sorry|admit|axiom|unsafe|opaque|implemented_by|partial|extern|noncomputable)\b|import Mathlib", "RMQ", "lakefile.toml"], 1),
        "native-decision": ("rg", ["-n", r"native_decide|Lean\.ofReduceBool", "RMQ"], 1),
        "working-whitespace": ("git", ["diff", "--check"], 0),
        "range-whitespace": ("git", ["diff", "--check", BASE + "..HEAD"], 0),
        "clean": ("git", ["-c", "core.excludesfile=", "status", "--porcelain=v1", "--untracked-files=all"], 0)}
    for name, (file, arguments, expected) in commands.items():
        c = checks[name]
        need((c["file"], c["arguments"], c["expected"], c["exit"]) == (file, arguments, expected, expected),
             "final exact command/ordinary exit: " + name)
        need(Path(c["log"]).read_bytes() == b"", "final required empty command output: " + name)
    c = checks["contract"]
    need(c["file"] == "python" and same_path(c["arguments"][0], HERE / "verify_contract.py") and
         c["arguments"][1] == "--output" and same_path(c["arguments"][2], check_root / "CONTRACT.json") and
         len(c["arguments"]) == 3 and c["expected"] == c["exit"] == 0, "successor contract exact dispatch")
    actual_contract = check_root / "CONTRACT.json"; pins.add(actual_contract)
    need(actual_contract.read_bytes() == Path(contract_path).read_bytes(), "supplied final contract must be final-check generated exact artifact")
    shell = capture["spec"]["file"]
    expected_design = {"design-whole": ["-NoProfile", "-File", "scripts/design_decision_check.ps1", "-Strict", "-Base", BASE]}
    for commit in V.git("rev-list", "--reverse", BASE + ".." + head).decode().splitlines():
        parent = V.git("rev-parse", commit + "^").decode().strip()
        expected_design["design-" + commit[:12]] = ["-NoProfile", "-File", "scripts/design_decision_check.ps1", "-Strict", "-Base", parent, "-Head", commit]
    for name, arguments in expected_design.items():
        c = checks[name]
        need(same_path(c["file"], shell) and c["arguments"] == arguments and c["exit"] == c["expected"] == 0,
             "whole-range/each-parent strict design command")
    return facts


def claim_inputs(path, pins):
    """Check retained producing commands/exits, without duplicating the classifier."""
    expectation = readj(path)
    roots = ["docs/internal/extensions/lifecycle-native-p0", "docs/internal/DESIGN_DECISIONS.md",
             "docs/internal/WORKFLOW_DESIGN_DECISIONS.md"]
    need(expectation["Roots"] == roots, "claims complete source roots")
    producer_path = Path(path).parent / "producer/CAPTURE.json"
    pins.add(producer_path); producer = readj(producer_path)
    V.capture(producer, pins, "", "", 0)
    need(same_path(producer["spec"]["cwd"], ROOT) and producer["launcher"]["DeadlineSeconds"] == 1200,
         "actual bounded claims expectation producer")
    args = producer["spec"]["arguments"]
    need(len(args) == 8 and args[:2] == ["-NoProfile", "-File"] and
         same_path(args[2], NATIVE / "repair-r2/claim_expectations.ps1") and
         args[3:5] == ["-Produce", "-RepositoryRoot"] and same_path(args[5], ROOT) and
         args[6] == "-EvidenceRoot" and same_path(args[7], Path(path).parent), "actual expectation producer command")
    policy = readj(ROOT / "docs/internal/CLAIM_DRIFT_POLICY.json")
    V.roster([c["id"] for c in expectation["Captures"]], [t["id"] for t in policy["terms"]], "claims actual rg term roster")
    rg_paths = [p["path"] for p in expectation["SourcePins"] if Path(p["path"]).name.lower() in ["rg.exe", "rg"]]
    need(len(rg_paths) == 1, "one pinned claim rg executable")
    for observed, term in zip(expectation["Captures"], policy["terms"]):
        pins.walk(observed["raw"])
        specs = [p for p in observed["raw"] if Path(p["path"]).name == "spec.json"]
        need(len(specs) == 1, "one actual claim rg spec")
        s = readj(specs[0]["path"])
        arguments = ["--json", "--pcre2"] + (["--multiline"] if term.get("multiline") else [])
        arguments += ["--glob", "!**/audit_reports/**", "--glob", "!**/*WORKLOG.md", "--", term["pattern"]] + roots
        need(same_path(s["file"], rg_paths[0]) and same_path(s["cwd"], ROOT) and s["arguments"] == arguments,
             "claim actual exact rg command")
        need(not Path(s["error"]).exists() and not Path(s["overflow"]).exists() and
             Path(s["stderr"]).read_bytes() == b"", "claim rg completed raw capture")
        actual = readj(s["exit"])
        need(actual == observed["actual"] and type(actual["exitCode"]) is int and actual["exitCode"] in [0, 1],
             "claim actual ordinary rg0/1 artifact")
        raw = V.raw(s["stdout"])
        need(raw.endswith("\n"), "claim rg JSONL terminator")
        records = [json.loads(line) for line in raw[:-1].split("\n")]
        need(records and records[-1]["type"] == "summary" and
             all(r["type"] in ["begin", "match", "end", "summary"] for r in records), "claim complete rg JSON records")
        need(actual["exitCode"] == (0 if any(r["type"] == "match" for r in records) else 1),
             "claim actual rg exit agrees with retained match/no-match records")
    return dict(producer=pins.add(producer_path), termCaptures=len(expectation["Captures"]))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--groups", nargs="+", required=True, metavar="LAUNCH")
    for name in ["retained", "contract", "profiles", "current-run", "output"]:
        parser.add_argument("--" + name, required=True)
    args = parser.parse_args(); started = time.monotonic(); pins = V.Pins()
    verifier_pin = pins.add(__file__); pins.add(PARSER)
    head = V.git("rev-parse", "HEAD").decode().strip()
    need(V.git("status", "--porcelain=v1", "--untracked-files=all") == b"", "final candidate must be clean")
    registry = frozen(HERE / "CONTROL_REGISTRY.json", REGISTRY_SHA, pins)
    retained_registry = frozen(HERE / "retained_registry.json", RETAINED_SHA, pins)
    contract = readj(args.contract); contract_pin = pins.add(args.contract)
    need(contract["success"] is True and contract["mode"] == "full-contract" and contract["base"] == BASE and
         contract["head"] == head and same_path(contract["worktree"], ROOT) and len(contract["rows"]) == 18 and
         contract["changedIds"] == [], "final full18 contract identity")
    pins.walk(contract["verifier"]); pins.walk(contract["currentOwnedSources"])
    need(same_path(contract["verifier"]["path"], HERE / "verify_contract.py"), "actual successor contract verifier")
    need(contract["historicalR2"]["packageCommit"] == BASE and
         contract["historicalR2"]["historicalBase"] == "2307e3ad0739e0e1d9c3f186cdc568631086fddf", "historical source identity")
    need(contract["currentRegistries"]["literal"]["sha256"] == REGISTRY_SHA and
         contract["currentRegistries"]["retained"]["sha256"] == RETAINED_SHA, "contract same frozen registries")
    group_facts, rows, source_head = groups(args.groups, registry, pins, head)
    retained_facts = retained(args.retained, contract, retained_registry, pins, head, args.contract)
    manifest = readj(args.profiles); manifest_pin = pins.add(args.profiles)
    need(manifest["head"] == head and set(manifest["profiles"]) == set(V.PROFILES), "final exact six-profile manifest/current head")
    current_facts = current_run(args.current_run, args.profiles, rows, contract, pins, head)
    profile_facts = {}
    for kind in V.PROFILES:
        path = manifest["profiles"][kind]
        if kind in ["full", "integrity", "dependencies"]:
            historical = contract["historicalR2"]["profiles"][kind]
            need(same_path(path, historical["receipt"]["path"]), "historical profile receipt identity")
            pins.add(path, historical["receipt"])
            profile_facts[kind] = dict(reusedHistorical=True, **historical)
            continue
        need(Path(path).resolve().is_relative_to((ROOT / ".lake").resolve()), "current profile receipt belongs to current checkout")
        receipt, c, receipt_pin = V.profile_receipt(kind, path, pins)
        need(same_path(c["spec"]["cwd"], ROOT), "current profile actual working directory")
        stdout = V.raw(c["spec"]["stdout"])
        if kind == "focused":
            actual = next(r for r in rows if r["id"] == "selector-focused")
            need(same_path(path, actual["receipt"]["path"]), "manifest actual focused invocation identity")
            facts = V.native_summary(kind, stdout, pins)
        elif kind == "checks":
            facts = final_checks(stdout, c, pins, head, args.contract)
        else:
            pins.walk(receipt["claimExpectation"])
            need(same_path(manifest["claimExpectationPath"], receipt["claimExpectation"]["path"]), "claims source-derived producing expectation identity")
            facts = V.claim_records(stdout, receipt["claimExpectation"]["path"], pins)
            expectation = readj(receipt["claimExpectation"]["path"])
            # Whole actual records are parsed above; require the actual scanner
            # driver to name the complete subtree plus both ledgers.
            command = receipt["command"]
            need("-Strict -Path @('docs/internal/extensions/lifecycle-native-p0','docs/internal/DESIGN_DECISIONS.md','docs/internal/WORKFLOW_DESIGN_DECISIONS.md')" in command,
                 "fresh entire native subtree/both-ledger claim invocation")
            need(expectation["SourcePins"], "claims current source pins missing")
            facts["producingInputs"] = claim_inputs(receipt["claimExpectation"]["path"], pins)
        profile_facts[kind] = dict(receipt=receipt_pin, reusedHistorical=False, facts=facts)
    report = HERE / "REPORT.md"; report_pin = pins.add(report)
    need(report.read_bytes().decode("utf-8").startswith("Status: CANDIDATE_COMPLETE\nI found no assigned or inherited acceptance criterion unmet; coordinator acceptance is still required.") or
         report.read_bytes().decode("utf-8").startswith("Status: CANDIDATE_COMPLETE\r\nI found no assigned or inherited acceptance criterion unmet; coordinator acceptance is still required."),
         "complete report candidate declaration")
    need(V.git("rev-parse", "HEAD").decode().strip() == head and
         V.git("status", "--porcelain=v1", "--untracked-files=all") == b"", "final collector clean same HEAD")
    # Rehash after all reads; a cached pin inventory alone is not final integrity.
    for pin in pins.records.values():
        data = Path(pin["path"]).read_bytes()
        need(len(data) == pin["bytes"] and hashlib.sha256(data).hexdigest().upper() == pin["sha256"], "collector final pin changed")
    result = dict(success=True, base=BASE, sourceCommit=source_head, finalPackageCommit=head, worktree=str(ROOT),
                  report=report_pin, contract=contract_pin, groups=group_facts, retained=retained_facts,
                  profiles=profile_facts, currentRun=current_facts, finalProfileManifest=manifest_pin, verifier=verifier_pin,
                  claimComposition=contract["claimComposition"], distinctPins=len(pins.records),
                  pinOccurrences=pins.occurrences, pins=sorted(pins.records.values(), key=lambda p: p["path"].lower()),
                  seconds=round(time.monotonic() - started, 3), cleanHead=head,
                  scope="Local literal/selector evidence composition. Historical full/integrity/dependencies remain retained runs; retained40 are components, not new native execution. Coordinator acceptance, adapter and campaign audit remain separate.")
    Path(args.output).write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(f"R3 RESULTS PASS: 37 controls, 40 retained cases, six composed profiles; {len(pins.records)} distinct pins")


if __name__ == "__main__":
    main()
