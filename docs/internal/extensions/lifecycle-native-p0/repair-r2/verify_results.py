"""Collect R2 certification facts from complete retained process evidence.

This collector does not rerun native operations or substitute for the caller-used
PowerShell predicates. It checks their exact recorded inputs, exits, raw bytes,
registries and verdicts. Deliberately changed/restored fixture source pins are
not treated as current-file pins; immutable raw captures are checked separately.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time

ROOT = next(p for p in Path(__file__).resolve().parents if (p / "lean-toolchain").is_file() and (p / "scripts").is_dir())
HERE = ROOT / "docs/internal/extensions/lifecycle-native-p0/repair-r2"
BASE = "2307e3ad0739e0e1d9c3f186cdc568631086fddf"
NATIVE = "docs/internal/extensions/lifecycle-native-p0/"
PROFILES = ["focused", "full", "integrity", "dependencies", "claims", "checks"]
INTEGRITY_IDS = ["intact-success", "intact-stage-error", "malformed-stdout-intact",
    "stage-error-and-pin-change", "stage-error-and-capture-error", "success-and-pin-change",
    "mixed-diagnostic-and-pin-change", "timeout-and-pin-change", "success-and-tracked-change",
    "success-and-index-change", "success-and-untracked-addition", "success-and-untracked-byte-change",
    "success-and-link-map-change", "partial-identity-and-pin-change", "missing-baseline"]
DEPENDENCY_IDS = ["complete-inventory", "bea5ce75-incomplete", "omit-lean.exe", "omit-leanc.exe",
    "omit-clang.exe", "omit-ld.lld.exe", "omit-libleanshared.dll", "omit-libInit_shared.dll",
    "omit-libclang-cpp.dll", "omit-libLLVM-19.dll", "omit-libc++.dll", "omit-zlib1.dll",
    "omit-libleanshared_1.dll", "same-name-wrong-path", "complete-unchanged-finalizer",
    "tamper-zlib1.dll", "tamper-link.map", "tamper-manifest-hash", "restored-finalizer"]
HARNESS_IDS = ["success-positive", "error-positive", "success-extra-stderr", "error-extra-stderr",
    "success-extra-stdout", "error-extra-stdout", "selector-empty", "selector-unknown",
    "selector-duplicate", "launcher-blank-stdout", "launcher-blank-stderr"]
MUTATIONS = ["positive", "extra-stdout", "extra-stderr", "blank-stdout", "blank-stderr",
    "missing-output", "duplicate-output", "misleading-success", "mixed-streams", "wrong-exit",
    "missing-ordinary-exit", "timeout", "output-limit", "launcher-blank-stdout",
    "launcher-blank-stderr", "launcher-output", "launcher-retention-error", "missing-launcher-raw"]
BOUNDARIES = ["controlids-empty-array", "controlids-empty-string", "controlids-whitespace",
    "controlids-unknown", "controlids-duplicate", "kind-missing", "kind-empty", "kind-unknown"]
NL = "\r\n"  # These receipts are the assigned Windows/PowerShell platform.


def need(value, reason):
    if not value:
        raise ValueError(reason)


def readj(path):
    return json.loads(Path(path).read_bytes().decode("utf-8-sig"))


def raw(path):
    return Path(path).read_bytes().decode("utf-8", errors="strict")


def git(*args):
    result = subprocess.run(["git", "-c", "core.excludesfile=", "-C", str(ROOT), *args],
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)
    need(result.returncode == 0, "Git command failed: " + result.stderr.decode(errors="replace"))
    return result.stdout


class Pins:
    def __init__(self):
        self.records = {}
        self.occurrences = 0

    def add(self, path, expected=None):
        path = Path(path).resolve()
        need(path.is_file(), "missing evidence: " + str(path))
        key = str(path).lower(); self.occurrences += 1
        if key not in self.records:
            digest = hashlib.sha256()
            with path.open("rb") as stream:
                for block in iter(lambda: stream.read(1024 * 1024), b""):
                    digest.update(block)
            self.records[key] = {"path": str(path), "bytes": path.stat().st_size,
                                 "sha256": digest.hexdigest().upper()}
        result = self.records[key]
        if expected is not None:
            need(result["bytes"] == expected["bytes"] and result["sha256"] == expected["sha256"].upper(),
                 "pin mismatch: " + str(path))
        return result

    def walk(self, obj):
        # Call only on explicitly immutable evidence objects, not entire mutation
        # summaries whose captured source/map hashes describe pre-restoration data.
        if isinstance(obj, dict):
            if all(k in obj for k in ("path", "bytes", "sha256")):
                self.add(obj["path"], obj)
            for value in obj.values():
                self.walk(value)
        elif isinstance(obj, list):
            for value in obj:
                self.walk(value)


def roster(actual, expected, label, ordered=True):
    need(len(actual) == len(set(actual)), label + " duplicate ID")
    need(actual == expected if ordered else set(actual) == set(expected), label + " missing/extra/reordered ID")


def ordinary(launcher, actual, expected):
    need(not launcher["TimedOut"] and not launcher["OutputLimitExceeded"], "incomplete bounded process")
    need(actual is not None and type(actual["exitCode"]) is int and type(launcher["ExitCode"]) is int and
         actual["exitCode"] == launcher["ExitCode"] == expected,
         "actual ordinary exit mismatch")
    need(launcher["DeadlineSeconds"] > 0 and launcher["DurationSeconds"] >= 0, "unbounded process")


def capture(c, pins, stdout, stderr, exit_code, allow_blank_launcher=None):
    pins.walk(c.get("raw", []))
    launch, spec = c["launcher"], c["spec"]
    ordinary(launch, c["actual"], exit_code)
    need(not launch["StandardOutput"] and not launch["StandardError"] and not launch["RetentionErrors"],
         "unexpected launcher output/retention failure")
    for key in ["error", "overflow"]:
        need(not Path(spec[key]).exists(), "present capture error/overflow")
    for key, stream in [("RawStandardOutput", "stdout"), ("RawStandardError", "stderr")]:
        pins.add(launch[key])
        need(raw(launch[key]) == (NL if allow_blank_launcher == stream else ""), "raw launcher bytes differ")
    pins.add(spec["stdout"]); pins.add(spec["stderr"])
    need(raw(spec["stdout"]) == stdout and raw(spec["stderr"]) == stderr, "actual raw stream contract differs")
    if "exit" in spec:
        pins.add(spec["exit"])
        need(readj(spec["exit"]) == c["actual"], "ordinary exit artifact differs")


def evidence_path(stdout, prefix, root):
    lines = stdout.split(NL)
    selected = [line[len(prefix):] for line in lines if line.startswith(prefix)]
    need(len(selected) == 1, "evidence line cardinality: " + prefix)
    path = Path(selected[0]).resolve()
    need(path.is_relative_to(root.resolve()), "evidence path escapes declared root")
    return path


def profile_receipt(kind, path, pins):
    receipt_pin = pins.add(path); receipt = readj(path)
    need(receipt["kind"] == kind and receipt["streamValidation"]["validated"] is True,
         "wrapper profile/production stream verdict")
    validation = receipt["streamValidation"]
    need(validation["profile"] == kind and validation["expectedStderr"] == "" and validation["expectedExit"] == 0,
         "wrapper declared profile contract")
    pins.walk(receipt["raw"])
    raw_paths = [str(Path(p["path"]).resolve()).lower() for p in receipt["raw"]]
    need(len(raw_paths) == len(set(raw_paths)), "duplicate wrapper raw pin")
    specs = [p for p in receipt["raw"] if Path(p["path"]).name == "spec.json"]
    need(len(specs) == 1, "one pinned wrapper capture spec required")
    spec = readj(specs[0]["path"])
    for p in [spec["stdout"], spec["stderr"], spec["exit"], receipt["outer"]["RawStandardOutput"], receipt["outer"]["RawStandardError"]]:
        need(str(Path(p).resolve()).lower() in raw_paths, "unpinned actual capture surface")
    c = dict(launcher=receipt["outer"], actual=receipt["actual"], spec=spec)
    capture(c, pins, validation["expectedStdout"], "", 0)
    return receipt, c, receipt_pin


def native_summary(kind, stdout, pins):
    path = evidence_path(stdout, "LIFECYCLE-REPLAY evidence=", ROOT / ".lake/lifecycle-native-p0/runs")
    summary_pin = pins.add(path / "SUMMARY.json"); s = readj(summary_pin["path"])
    need(Path(s["runRoot"]).resolve() == path and Path(s["repositoryRoot"]).resolve() == ROOT,
         "native summary object identity")
    need(s["success"] is True and s["failure"] is None and s["integrity"]["attempted"] is True and
         s["integrity"]["success"] is True and s["integrity"]["errors"] == [], "native final integrity/verdict")
    registry = readj(ROOT / (NATIVE + "REGISTRY.json"))
    expected_ids = [c["id"] for c in registry["cases"]] if kind == "full" else ["pop-unique"]
    roster(s["selected"], expected_ids, "native selected")
    need(stdout == "LIFECYCLE-REPLAY evidence=" + s["runRoot"] + NL +
         f"LIFECYCLE-REPLAY PASS cases={len(expected_ids)} selfTest={'True' if kind == 'full' else 'False'}" + NL,
         "native exact output")
    need(s["integrity"]["checkedPins"] == len(s["capturedPins"]) > 0, "native final captured pin count")
    pins.walk(s["capturedPins"]); pins.walk(s["sources"]); pins.walk(s["identity"])
    historical = readj(ROOT / (NATIVE + "repair-r1/RESULTS.json"))
    original = readj(ROOT / (NATIVE + "RESULTS.json"))
    if kind == "full":
        roster([c["id"] for c in s["checks"]], [c["id"] for c in original["checks"]], "native checks")
        roster([c["name"] for c in s["stages"]], [c["name"] for c in historical["native"]["stages"]], "native stages")
        need(len(s["selected"]) == 23 and len(s["checks"]) == 65 and len(s["stages"]) == 58,
             "native23/65/58 counts")
    for row in registry["cases"]:
        if row["id"] not in expected_ids:
            continue
        stage = next(c for c in s["stages"] if c["name"] == row["id"])
        ordinary(stage["launcher"], stage["child"], row["expectedExit"])
        need(stage["stderr"]["bytes"] == 0 and not stage["childError"] and not stage["launcherError"] and
             not stage["nativeOutputLimitExceeded"], "native operational case diagnostics")
    return {"summary": summary_pin, "selected": s["selected"], "checks": len(s["checks"]),
            "stages": len(s["stages"]), "capturedPins": len(s["capturedPins"]), "integritySuccess": True}


def integrity_results(stdout, pins):
    path = evidence_path(stdout, "INTEGRITY CONTROLS evidence=", ROOT / ".lake/repair-r1")
    result_pin = pins.add(path / "RESULTS.json"); result = readj(result_pin["path"])
    roster([c["id"] for c in result["controls"]], INTEGRITY_IDS, "integrity15")
    need(result["fixtureRestoration"] and result["candidateUnchanged"], "integrity restoration")
    need(stdout == "".join("CONTROL PASS " + x + NL for x in INTEGRITY_IDS) +
         "INTEGRITY CONTROLS evidence=" + str(path) + NL, "integrity exact stdout")
    pins.walk(result["source"]); pins.walk(result["helper"])
    facts = []
    for row in result["controls"]:
        pins.walk(row["summary"]); pins.walk(row["fixtureSource"])
        s = readj(row["summary"]["path"]); contract = row["streamContract"]
        wanted_integrity = row["id"] in INTEGRITY_IDS[:3]
        need(row["expectedIntegrity"] == wanted_integrity and row["expectedSuccess"] == (row["id"] == "intact-success"),
             "integrity original case-to-verdict mapping")
        need(contract["validated"] is True and s["success"] == row["expectedSuccess"] and
             s["integrity"]["success"] == row["expectedIntegrity"] and s["failure"] == row["stageFailure"],
             "integrity independent stage/final verdict")
        need(s["integrity"]["attempted"] is True and s["integrity"]["checkedPins"] >= 8 and row["integrity"] == s["integrity"],
             "integrity attempted finalization and exact reported object")
        fixture = Path(row["fixtureSource"]["path"]).parents[1]
        pin_cases = ["stage-error-and-pin-change", "success-and-pin-change", "mixed-diagnostic-and-pin-change",
                     "timeout-and-pin-change", "partial-identity-and-pin-change"]
        tree_cases = pin_cases + ["success-and-tracked-change", "success-and-index-change", "success-and-untracked-addition", "success-and-untracked-byte-change"]
        errors = []
        if row["id"] in pin_cases:
            errors.append("INTEGRITY: changed captured pin: " + str(fixture / "native/packed-rmq/tests/lifecycle_storage_probe.c"))
        if row["id"] == "success-and-link-map-change":
            errors.append("INTEGRITY: changed captured pin: " + str(Path(s["runRoot"]) / "link.map"))
        if row["id"] in tree_cases: errors.append("INTEGRITY: live tracked/index/untracked baseline changed")
        if row["id"] == "missing-baseline": errors.append("INTEGRITY: UNCOVERED; initial tree inventory unavailable")
        if row["id"] == "stage-error-and-capture-error":
            need(len(s["integrity"]["errors"]) == 1 and s["integrity"]["errors"][0].startswith(
                "INTEGRITY: artifact capture failed: " + str(Path(s["runRoot"]) / "link.map") + "; "), "runtime-specific locked-map error")
        else:
            need(Counter(s["integrity"]["errors"]) == Counter(errors), "independent exact integrity error set")
        expected_exit = 0 if row["expectedSuccess"] else 1
        expected_out = "LIFECYCLE-REPLAY evidence=" + s["runRoot"] + NL
        if row["expectedSuccess"]:
            expected_out += "LIFECYCLE-REPLAY PASS cases=1 selfTest=False" + NL
        expected_err = ("" if s["failure"] is None else s["failure"] + NL) + "".join(e + NL for e in s["integrity"]["errors"])
        need(contract == dict(expectedStdout=expected_out, expectedStderr=expected_err,
                              expectedExit=expected_exit, validated=True), "integrity exact stream contract")
        capture(row["capture"], pins, expected_out, expected_err, expected_exit)
        need(row["actualExit"] == row["outer"]["ExitCode"] == expected_exit, "integrity outer exit")
        stem = Path(s["runRoot"]) / "000-fixture-stage"
        out_path, err_path = Path(str(stem) + ".stdout"), Path(str(stem) + ".stderr")
        pins.add(out_path); pins.add(err_path)
        malformed = row["id"] == "malformed-stdout-intact"
        timeout = row["id"] == "timeout-and-pin-change"
        need(out_path.read_bytes() == (b"\xff" if malformed else b""), "integrity inner stdout")
        need(err_path.read_bytes() == (b"unexpected\r\n" if row["id"] == "mixed-diagnostic-and-pin-change" else b""), "integrity inner stderr")
        inner_exit = None
        if not timeout:
            exit_path = Path(str(stem) + ".exit.json"); pins.add(exit_path)
            inner_exit = 7 if row["id"] in ["intact-stage-error", "stage-error-and-pin-change", "stage-error-and-capture-error"] else 0
            need(readj(exit_path)["exitCode"] == inner_exit, "integrity real inner ordinary exit")
        if not malformed:
            need(len(s["stages"]) == 1, "integrity real stage cardinality")
            stage = s["stages"][0]; pins.walk(stage)
            need(stage["launcher"]["TimedOut"] == timeout and not stage["launcher"]["OutputLimitExceeded"] and
                 not stage["nativeOutputLimitExceeded"] and not stage["launcherError"] and not stage["childError"], "integrity stage guard")
            if not timeout:
                ordinary(stage["launcher"], stage["child"], inner_exit)
        facts.append(dict(id=row["id"], outerExit=expected_exit, nativeExit=inner_exit,
                          timeout=timeout, integritySuccess=row["expectedIntegrity"], stageFailure=s["failure"]))
    return dict(results=result_pin, controls=facts, fixtureRestoration=True, candidateUnchanged=True)


def dependency_results(stdout, pins):
    path = evidence_path(stdout, "DEPENDENCY CONTROLS PASS evidence=", ROOT / ".lake/repair-r1")
    result_pin = pins.add(path / "RESULTS.json"); r = readj(result_pin["path"])
    roster([c["id"] for c in r["controls"]], DEPENDENCY_IDS, "dependency19", False)
    need(r["installedToolsUnchanged"] and r["fixtureRestored"] and len(r["closure"]["nodes"]) == 11,
         "dependency closure/restoration")
    need(stdout == "DEPENDENCY CONTROLS PASS evidence=" + str(path) + NL, "dependency exact stdout")
    pins.walk(r.get("closure", {})); pins.walk(r.get("source", {})); pins.walk(r["pins"]); pins.walk(r["oldSummary"])
    missing = {Path(p).name.lower() for p in r["oldMissing"]}
    need(missing == {"libclang-cpp.dll", "libllvm-19.dll", "libc++.dll", "zlib1.dll"}, "measured old omissions")
    return dict(results=result_pin, controls=[c["id"] for c in r["controls"]], localNodes=11,
                oldMissing=sorted(missing), installedToolsUnchanged=True, fixtureRestored=True)


def claim_records(stdout, expectation, pins):
    e = readj(expectation); pins.add(expectation); pins.walk(e.get("SourcePins", [])); pins.walk(e.get("Captures", []))
    need(e["Profile"] == "claims-strict-subtree-ledgers" and e["ExpectedExit"] == 0 and
         e["Stderr"] == "" and e["StrictFailures"] == 0, "claims expectation contract")
    footer = e["Footer"]; need(footer and stdout.endswith(footer), "claim exact footer")
    remaining = Counter(e["Records"]); keys = sorted(remaining)
    need(all(r.startswith("CLAIM-DRIFT[") and r.endswith(NL) for r in keys), "claim record grammar")
    need(not any(keys[i].startswith(keys[i-1]) for i in range(1, len(keys))), "ambiguous claim record prefixes")
    body = stdout[:-len(footer)]; offset = 0
    while offset < len(body):
        matches = [r for r in keys if body.startswith(r, offset)]
        need(len(matches) == 1 and remaining[matches[0]] > 0, "unexpected/duplicate claim record")
        remaining[matches[0]] -= 1; offset += len(matches[0])
    need(not any(remaining.values()), "missing claim record")
    return dict(expectation=pins.add(expectation), records=len(e["Records"]), hits=e["Hits"],
                strictFailures=0, footer=footer.rstrip("\r\n"))


def check_results(stdout, pins):
    path = evidence_path(stdout, "FINAL CHECKS evidence=", ROOT / ".lake/repair-r1")
    result_pin = pins.add(path / "RESULTS.json"); r = readj(result_pin["path"])
    need(r["base"] == BASE, "final checks exact base")
    commits = git("rev-list", "--reverse", BASE + ".." + r["head"]).decode().splitlines()
    ids = ["contract", "hygiene", "native-decision", "working-whitespace", "range-whitespace", "design-whole"]
    ids += ["design-" + c[:12] for c in commits] + ["clean"]
    roster([c["name"] for c in r["checks"]], ids, "final check registry")
    need(all(c["exit"] == c["expected"] for c in r["checks"]), "failed final check")
    need(stdout == "".join("CHECK PASS " + x + NL for x in ids) + "FINAL CHECKS evidence=" + str(path) + NL, "final checks exact stdout")
    pins.walk(r.get("pins", []))
    for c in r["checks"]:
        pins.add(c["log"])
    return dict(results=result_pin, head=r["head"], checks=ids)


def verify_harness(path, pins, complete=True):
    result_pin = pins.add(path); r = readj(path); registry = readj(HERE / "HARNESS_STREAM_REGISTRY.json")
    roster([c["id"] for c in registry["controls"]], HARNESS_IDS, "harness frozen registry")
    ids = [c["id"] for c in r["controls"]]
    roster(ids, HARNESS_IDS if complete else r["selected"], "harness executed registry")
    need(r["selected"] == ids, "harness selected mapping")
    for key in ["registry", "source", "validator"]:
        pins.walk(r[key])
    facts = []
    for c in r["controls"]:
        row = next(x for x in registry["controls"] if x["id"] == c["id"])
        need(c["outcome"] == row["outcome"] and c["predicate"] == row["predicate"], "harness registry verdict mapping")
        pins.walk(c["raw"])
        if row["kind"] == "launcher":
            stream = row["stream"]
            need(c["surface"] == "STREAM: " + c["id"] + " launcher " + stream + " differs", "launcher exact failure")
            capture(c["capture"], pins, "", "", 0, stream)
        else:
            positive = row["outcome"] == "accept"
            expected_error = "" if positive else ("STREAM-SELECTOR: " + row["stream"] if row["kind"] == "selector"
                else "STREAM: integrity-" + row["case"] + " " + row["stream"] + " differs")
            need(c["surface"] == expected_error, "harness exact failure surface")
            stdout = raw(c["capture"]["spec"]["stdout"])
            if positive:
                control_root = Path(c["inner"]["spec"]["cwd"]).resolve().parent
                need(stdout == "CONTROL PASS " + row["case"] + NL + "INTEGRITY CONTROLS evidence=" + str(control_root) + NL,
                     "harness exact positive output")
            else:
                need(stdout == "", "harness rejected stdout")
            capture(c["capture"], pins, stdout, "" if positive else expected_error + NL, 0 if positive else 1)
            if row["kind"] == "harness":
                need(c["fixtureRestored"] and c["carrierUnchanged"], "harness fixture/carrier restoration")
                pins.walk(c["summary"]); s = readj(c["summary"]["path"])
                need(s["selected"] == ["pop-unique"] and s["integrity"]["success"] and not s["integrity"]["errors"], "harness inner guards")
                native_exit = 0 if row["case"] == "intact-success" else 7; runner_exit = int(native_exit != 0)
                need(len(s["stages"]) == 1, "harness one real native stage")
                ordinary(s["stages"][0]["launcher"], s["stages"][0]["child"], native_exit)
                pins.walk(s["stages"])
                inner_out = "LIFECYCLE-REPLAY evidence=" + s["runRoot"] + NL
                if not runner_exit:
                    inner_out += "LIFECYCLE-REPLAY PASS cases=1 selfTest=False" + NL
                inner_err = "PROCESS: fixture-stage actual child or launcher exit differs from 0" + NL if runner_exit else ""
                if row["stream"] == "stdout": inner_out = "UNEXPECTED OUTER DIAGNOSTIC" + NL + inner_out
                if row["stream"] == "stderr": inner_err = "UNEXPECTED OUTER DIAGNOSTIC" + NL + inner_err
                capture(c["inner"], pins, inner_out, inner_err, runner_exit)
        facts.append(dict(id=c["id"], outcome=c["outcome"], surface=c["surface"], predicate=c["predicate"]))
    return dict(results=result_pin, controls=facts, completeRegistry=complete)


def expected_wrapper_failure(profile, mutation, baseline_stdout, snapshot, claim):
    if mutation == "positive": return None
    if mutation == "observed-mixed-holdout": return "STREAM: wrapper-observed-focused-extra-stdout stderr differs"
    prefix = "STREAM: wrapper-" + profile
    if mutation in ["extra-stdout", "blank-stdout", "misleading-success"]:
        return "STREAM: claim footer differs" if profile == "claims" else prefix + " stdout differs"
    if mutation in ["extra-stderr", "blank-stderr", "mixed-streams"]: return prefix + " stderr differs"
    if mutation == "missing-output":
        return "STREAM: claim footer differs" if profile == "claims" else (prefix + " stdout differs" if profile in ["focused", "full"] else "STREAM: evidence line missing")
    if mutation == "duplicate-output":
        if profile != "claims": return prefix + " stdout differs"
        if not claim["Records"]: return "STREAM: unexpected claim output with empty record roster"
        # .NET reports UTF-16 character offsets.
        count = len((baseline_stdout[:-len(claim["Footer"])]).encode("utf-16-le")) // 2
        return "STREAM: unexpected or duplicate claim record/text at character " + str(count)
    if mutation in ["wrong-exit", "missing-ordinary-exit"]: return prefix + " ordinary exit differs"
    if mutation in ["timeout", "output-limit"]: return prefix + " incomplete bounded capture"
    if mutation in ["launcher-blank-stdout", "launcher-blank-stderr"]: return prefix + " launcher " + mutation.rsplit("-", 1)[1] + " differs"
    if mutation == "launcher-output": return prefix + " launcher output"
    if mutation == "launcher-retention-error": return prefix + " launcher retention failed"
    if mutation == "missing-launcher-raw": return "STREAM: raw capture missing: " + snapshot["launcher"]["RawStandardOutput"]
    raise ValueError("unmapped wrapper mutation")


def verify_wrapper_controls(path, manifest, baselines, pins, claim_path, complete=True):
    result_pin = pins.add(path); r = readj(path); registry = readj(HERE / "WRAPPER_STREAM_REGISTRY.json")
    expected = ["wrapper-" + p + "-" + m for p in PROFILES for m in MUTATIONS]
    expected += ["wrapper-focused-process-" + m for m in ["positive", "extra-stdout", "extra-stderr"]]
    expected += ["wrapper-boundary-" + m for m in BOUNDARIES]
    expected += ["wrapper-focused-observed-mixed-holdout"]
    roster([x["id"] for x in registry["controls"]], expected, "wrapper120 registry")
    executed = [x["id"] for x in r["controls"]]
    roster(executed, expected if complete else r["selected"], "wrapper120 executions")
    need(all(key in expected for key in executed), "unknown executed wrapper control")
    need(r["success"] is True and r["failure"] is None and r["registryCount"] == 120 and
         r["selected"] == executed and r["immutableInputsUnchanged"], "wrapper campaign result")
    need(Path(r["profileManifest"]).resolve() == Path(manifest).resolve(), "wrapper manifest identity")
    pins.walk(r["sourcePins"])
    claim = readj(claim_path) if any(c["profile"] == "claims" for c in r["controls"]) else {"Records": [], "Footer": ""}
    if any(c["profile"] == "claims" for c in r["controls"]):
        produced_receipt_path = readj(manifest)["profiles"]["claims"]
        produced = readj(produced_receipt_path)["claimExpectation"]
        need(r["claimExpectationPin"] == produced and Path(r["claimExpectationSourceReceipt"]).resolve() == Path(produced_receipt_path).resolve(),
             "wrapper claims language is not bound to producing receipt")
        pins.walk(produced)
    facts = []
    for c in r["controls"]:
        row = next(item for item in registry["controls"] if item["id"] == c["id"])
        for key in ["id", "profile", "mode", "expected"]:
            need(c[key] == row[key], "wrapper registry field mapping")
        need(c["passed"] and c["fixtureRestored"] and c["actualFailure"] == c["expectedFailure"], "wrapper exact verdict/restoration")
        if c["mode"] == "boundary":
            pins.walk(c["raw"])
            specs = [p for p in c["raw"] if Path(p["path"]).name == "BOUNDARY_SPEC.json"]
            errors = [p for p in c["raw"] if Path(p["path"]).name == "ERROR.json"]
            need(len(specs) == len(errors) == 1, "one real boundary spec/error")
            spec, error = readj(specs[0]["path"]), readj(errors[0]["path"])
            need(error == dict(message=c["actualFailure"], type=c["expectedExceptionType"], fqid=c["expectedFullyQualifiedErrorId"]),
                 "boundary exact observed exception")
            need(spec["message"] == error["message"] and spec["type"] == error["type"] and spec["fqid"] == error["fqid"] and spec["id"] == c["id"],
                 "boundary producer expectation identity")
            outer_root = Path(specs[0]["path"]).parent / "outer"
            pins.add(outer_root / "CAPTURE.json")
            outer = readj(outer_root / "CAPTURE.json")
            capture(outer, pins, "BOUNDARY REJECTED " + c["id"] + NL, "", 0)
            need(c["actualOuterExit"] == 0 and row["expected"] == "reject", "boundary driver/target outcome separation")
            facts.append(dict(id=c["id"], mode="boundary", expected="reject", actualFailure=c["actualFailure"],
                              exceptionType=error["type"], fullyQualifiedErrorId=error["fqid"], driverExit=0))
            continue
        need(Path(c["sourceReceipt"]).resolve() == Path(readj(manifest)["profiles"][c["profile"]]).resolve(), "wrapper baseline receipt identity")
        pins.walk(c["raw"])
        baseline = baselines[c["profile"]]; mutation = row["mutation"]
        if c["mode"] == "component":
            snapshots = [p for p in c["raw"] if Path(p["path"]).name == "CAPTURE.json"]
            need(len(snapshots) == 1, "component observed snapshot")
            snapshot = readj(snapshots[0]["path"])
            expected_failure = expected_wrapper_failure(c["profile"], mutation, baseline, snapshot, claim)
            need(c.get("replayExpectedFailure", c["actualFailure"]) == expected_failure, "component exact replay failure surface")
            if mutation == "missing-launcher-raw":
                need(not Path(snapshot["launcher"]["RawStandardOutput"]).exists(), "missing launcher mutation absent")
            elif mutation == "wrong-exit": need(snapshot["actual"]["exitCode"] == snapshot["launcher"]["ExitCode"] == 99, "wrong exit mutation")
            elif mutation == "missing-ordinary-exit": need(snapshot["actual"] is None, "null ordinary exit mutation")
            elif mutation == "timeout": need(snapshot["launcher"]["TimedOut"], "timeout mutation")
            elif mutation == "output-limit": need(snapshot["launcher"]["OutputLimitExceeded"], "output-limit mutation")
            elif mutation == "launcher-retention-error": need(snapshot["launcher"]["RetentionErrors"] == ["injected isolated retention failure"], "retention mutation")
            else:
                observed_out, observed_err = raw(snapshot["spec"]["stdout"]), raw(snapshot["spec"]["stderr"])
                expected_out, expected_err = baseline, ""
                if mutation == "extra-stdout": expected_out += "UNEXPECTED WRAPPER STDOUT" + NL
                if mutation == "extra-stderr": expected_err = "UNEXPECTED WRAPPER STDERR" + NL
                if mutation == "blank-stdout": expected_out += NL
                if mutation == "blank-stderr": expected_err = NL
                if mutation == "misleading-success": expected_out += '{"success":true,"validated":true}' + NL
                if mutation == "observed-mixed-holdout":
                    expected_out += "UNEXPECTED WRAPPER STDOUT" + NL
                    expected_err = "UNRELATED SECOND STDERR DIAGNOSTIC" + NL
                    need(c["observedStreamContract"] == dict(expectedStdout=expected_out, expectedStderr="", expectedExit=0,
                         profile="wrapper-observed-focused-extra-stdout", positiveAccepted=True), "mixed holdout same P/Q contract")
                if mutation == "duplicate-output": expected_out += baseline
                if mutation == "mixed-streams": expected_err = baseline
                if mutation == "missing-output":
                    cut = baseline.rfind(NL, 0, len(baseline) - len(NL))
                    expected_out = "" if cut < 0 else baseline[:cut + len(NL)]
                need(observed_out == expected_out and observed_err == expected_err, "component challenged byte objects differ")
                if mutation.startswith("launcher-blank-"):
                    key = "RawStandardOutput" if mutation.endswith("stdout") else "RawStandardError"
                    need(raw(snapshot["launcher"][key]) == NL, "launcher blank retained bytes")
                if mutation == "launcher-output": need(snapshot["launcher"]["StandardOutput"] == ["UNEXPECTED LAUNCHER OUTPUT"], "launcher output mutation")
        else:
            need(c["actualOuterExit"] == (0 if mutation == "positive" else 1) and c["actualInnerExit"] == 0,
                 "actual wrapper process verdict")
            receipts = [p for p in c["raw"] if Path(p["path"]).name == "RECEIPT.json"]
            need(len(receipts) == 1, "real wrapper receipt")
            receipt = readj(receipts[0]["path"])
            need(receipt["streamValidation"]["validated"] == (mutation == "positive") and
                 receipt["streamValidation"].get("failure") == c["actualFailure"], "real production wrapper stream verdict")
            ordinary(receipt["outer"], receipt["actual"], 0)
            need(c["actualFailure"] == expected_wrapper_failure("focused", mutation, baseline, {}, claim), "real wrapper exact failure")
            expected_out = baseline + ("UNEXPECTED WRAPPER STDOUT" + NL if mutation == "extra-stdout" else "")
            expected_err = "UNEXPECTED WRAPPER STDERR" + NL if mutation == "extra-stderr" else ""
            need(c["observedStreamContract"] == dict(expectedStdout=expected_out, expectedStderr=expected_err, expectedExit=0, validated=True),
                 "real wrapper two-sided observed-stream contract")
            wrapper_root = Path(receipts[0]["path"]).parent
            inner_spec = readj(wrapper_root / "spec.json")
            capture(dict(launcher=receipt["outer"], actual=receipt["actual"], spec=inner_spec), pins, expected_out, expected_err, 0)
            outer_root = wrapper_root.parent / "outer"
            pins.add(outer_root / "CAPTURE.json"); outer = readj(outer_root / "CAPTURE.json")
            capture(outer, pins, "OWNED focused exit=0 evidence=" + str(wrapper_root) + NL, "", 0 if mutation == "positive" else 1)
        facts.append(dict(id=c["id"], mode=c["mode"], expected=c["expected"], actualFailure=c["actualFailure"]))
    return dict(results=result_pin, count=len(facts), completeRegistry=complete, controls=facts, immutableInputsUnchanged=True)


def old_reproduction(path, pins):
    path = Path(path).resolve()
    if path.is_dir():
        candidates = list(path.rglob("RECEIPT.json"))
        candidates = [p for p in candidates if readj(p).get("kind") == "ACTUAL_ADVERSARIAL_CONTROL_HARNESS"]
        need(len(candidates) == 1, "one actual immutable old reproduction")
        path = candidates[0]
    receipt_pin = pins.add(path); r = readj(path); pins.walk(r["pins"])
    need(r["candidate"] == BASE and r["selected"] == ["intact-success", "intact-stage-error"], "old reproduction exact base/selection")
    ordinary(r["outer"], r["actual"], 0)
    spec = readj(path.parent / "spec.json"); pins.add(path.parent / "spec.json")
    expected_out = "CONTROL PASS intact-success" + NL + "CONTROL PASS intact-stage-error" + NL + "INTEGRITY CONTROLS evidence=" + str(path.parent / "controls-output") + NL
    need(raw(spec["stdout"]) == expected_out and raw(spec["stderr"]) == "" and readj(spec["exit"]) == r["actual"], "old reproduction actual accepted stdout/exit")
    controls_path = path.parent / "controls-output/RESULTS.json"; pins.add(controls_path); c = readj(controls_path)
    roster([x["id"] for x in c["controls"]], ["intact-success", "intact-stage-error"], "old two actual controls")
    need(c["fixtureRestoration"] and c["candidateUnchanged"], "old reproduction restoration")
    identity_path = next((p / "IDENTITY.json" for p in path.parents if (p / "IDENTITY.json").is_file()), None)
    need(identity_path is not None, "old reproduction immutable source identity")
    identity = readj(identity_path); pins.add(identity_path); pins.walk(identity["oldSource"])
    carrier = Path(identity["immutableSource"])
    for source in identity["sourcePins"]:
        data = git("show", BASE + ":" + source["path"])
        need(len(data) == source["bytes"] and hashlib.sha256(data).hexdigest().upper() == source["sha256"].upper(), "old source Git object changed")
        pins.add(carrier / source["path"], source)
    old = git("show", BASE + ":" + NATIVE + "repair-r1/integrity_controls.ps1")
    need(Path(identity["oldSource"]["path"]).read_bytes() == old, "old harness exact Git source")
    source = old.decode("utf-8")
    rootline = "$repo=[IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../../../../..'))"
    need(source.count(rootline) == 1, "old harness unique root anchor")
    # The copied coordinator driver substitutes its literal $repo value. Read
    # that declared value from the immutable reproduction driver, then bind it
    # to the actual carrier instead of normalizing stream/source bytes.
    driver_text = raw(identity["driver"]); pins.add(identity["driver"])
    roots = re.findall(r"(?m)^\$repo='([^']+)'\r?$", driver_text)
    need(len(roots) == 1 and Path(roots[0]).resolve() == carrier.resolve(), "old reproduction driver source root")
    derived = source.replace(rootline, "$repo='" + roots[0] + "'")
    anchors = list(re.finditer(r"(?m)^  \$mutation\r?$", derived)); need(len(anchors) == 1, "old harness unique injection anchor")
    newline = "\r\n" if "\r\n" in derived else "\n"
    at = anchors[0].start(); derived = derived[:at] + "  [Console]::Error.WriteLine('UNEXPECTED OUTER DIAGNOSTIC')" + newline + derived[at:]
    need((path.parent / "controls-derived.ps1").read_bytes() == derived.encode("utf-8"), "old harness exact derived delta")
    production = git("show", BASE + ":scripts/packed_native_lifecycle_storage_replay.ps1").decode("utf-8")
    prefix_at = production.index("  $LeanRoot = [IO.Path]::GetFullPath($LeanRoot)")
    suffix_at = production.rindex("  $taskSuccess = $true")
    historical = pins.add(identity["historicalReceipt"])
    need(historical["bytes"] == 4331 and historical["sha256"] == "D47623CC4480AD592093871D59224ED8DB3B33B5E34D65C64F3BBD08BF7C83F7", "historical coordinator receipt changed")
    facts = []
    for row in c["controls"]:
        pins.walk(row["summary"]); pins.walk(row["fixtureSource"])
        fixture_source = raw(row["fixtureSource"]["path"])
        need(fixture_source.startswith(production[:prefix_at]) and fixture_source.endswith(production[suffix_at:]),
             "old complete production prefix/suffix")
        summary = readj(row["summary"]["path"]); pins.walk(summary["stages"])
        native_exit = 0 if row["id"] == "intact-success" else 7
        need(summary["integrity"]["success"] and not summary["integrity"]["errors"] and len(summary["stages"]) == 1, "old counterexample inner integrity")
        ordinary(summary["stages"][0]["launcher"], summary["stages"][0]["child"], native_exit)
        wanted = ["UNEXPECTED OUTER DIAGNOSTIC"] + ([] if native_exit == 0 else ["PROCESS: fixture-stage actual child or launcher exit differs from 0"])
        need(row["outer"]["StandardError"] == wanted and row["actualExit"] == int(native_exit != 0), "old actual unexpected stderr")
        facts.append(dict(id=row["id"], nativeExit=native_exit, runnerExit=row["actualExit"], harnessAccepted=True, stderr=wanted))
    return dict(receipt=receipt_pin, identity=pins.add(identity_path), historicalReceipt=historical,
                actualHarnessExit=0, cases=facts, meaning="Old harness still accepted; never relabeled rejected.")


def main():
    ap = argparse.ArgumentParser()
    for name in ["profiles", "harness", "wrapper-controls", "old-reproduction", "output"]:
        ap.add_argument("--" + name, required=True)
    args = ap.parse_args(); started = time.monotonic(); pins = Pins()
    manifest = readj(args.profiles); pins.add(args.profiles)
    need(set(manifest["profiles"]) == set(PROFILES), "exact six supported profiles required")
    claim_receipt = readj(manifest["profiles"]["claims"])
    need(isinstance(claim_receipt.get("claimExpectation"), dict), "producing claims receipt must pin its expectation")
    pins.walk(claim_receipt["claimExpectation"])
    claim_path = claim_receipt["claimExpectation"]["path"]
    if manifest.get("claimExpectationPath"):
        need(Path(manifest["claimExpectationPath"]).resolve() == Path(claim_path).resolve(), "manifest claims expectation is not the producing object")
    result = {"base": BASE, "head": git("rev-parse", "HEAD").decode().strip(), "worktree": str(ROOT),
              "profiles": {}, "verifier": pins.add(__file__)}
    baselines = {}
    for kind in PROFILES:
        receipt, c, receipt_pin = profile_receipt(kind, manifest["profiles"][kind], pins)
        stdout = raw(c["spec"]["stdout"]); baselines[kind] = stdout
        facts = (native_summary(kind, stdout, pins) if kind in ["focused", "full"] else
                 integrity_results(stdout, pins) if kind == "integrity" else
                 dependency_results(stdout, pins) if kind == "dependencies" else
                 claim_records(stdout, claim_path, pins) if kind == "claims" else check_results(stdout, pins))
        result["profiles"][kind] = dict(receipt=receipt_pin, actualExit=0, seconds=receipt["outer"]["DurationSeconds"],
                                       deadlineSeconds=receipt["outer"]["DeadlineSeconds"], streamValidation=True, facts=facts)
    result["harness"] = verify_harness(args.harness, pins)
    result["wrapperControls"] = verify_wrapper_controls(args.wrapper_controls, args.profiles, baselines, pins, claim_path)
    result["oldReproduction"] = old_reproduction(args.old_reproduction, pins)
    result.update(success=True, distinctPins=len(pins.records), pinOccurrences=pins.occurrences,
                  pins=sorted(pins.records.values(), key=lambda p: p["path"].lower()), seconds=round(time.monotonic() - started, 3),
                  fixturePinBoundary="Native successful-run captures are rehashed. Mutated/restored control summaries contribute only immutable summary/raw-stage/capture evidence, never stale fixture-source/map hashes from their capturedPins inventory.",
                  status="Local diagnostic certification evidence; coordinator acceptance, consuming adapter and campaign audit remain separate.")
    Path(args.output).write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(f"RESULTS PASS: six profiles, native23/65/58, integrity15, dependency19, harness11, wrapper120; {len(pins.records)} distinct pins")


if __name__ == "__main__":
    main()
