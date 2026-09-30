"""Exact R2 row/scope/history checks. This does not certify the new native runs.

Historical source pins resolve against named immutable Git objects, never the
successor's intentionally edited working scripts. Raw artifact pins still hash
their actual files. Claim coverage remains a composition until the caller runs
the unchanged-policy scan of the complete native subtree and both ledgers.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parents[5]
OUT = Path(__file__).resolve().parent
BASE = "2307e3ad0739e0e1d9c3f186cdc568631086fddf"
GOVERNANCE = "7b227c49ef2ec044b702126cc41c9add847eed01"
BRANCH = "codex/life-native-p0-r2-outer-diagnostics"
FROZEN_SHA256 = "7DBC035076EA9CACE20AC735B1AA85B099AEF3D5B5B1AFE514ABA2C0C63E237E"
PROMPT_SHA256 = "7DD65657F4B6B6436FCCD02A54DEC2FCFDB5584663EC0EDE2B56FFD35EDE3DB6"
NATIVE = "docs/internal/extensions/lifecycle-native-p0/"
R1 = NATIVE + "repair-r1/"
R2 = NATIVE + "repair-r2/"
LEDGER = "docs/internal/WORKFLOW_DESIGN_DECISIONS.md"
ORIGINAL = "bea5ce75f788c4035031ba81e69d8de36eda3f92"
ORIGINAL_FINAL = "0c873072e84be9e1d65edab1985bcff1d23abef1"
CAMPAIGN = Path("C:/Users/poin/Documents/RMQ/lifecycle-implementation-20260920")
REVIEW = CAMPAIGN / "native-p0-r1-review"
ORIGINAL_ROOT = Path("C:/Users/poin/.codex/worktrees/af4b/RMQ")
R1_ROOT = Path("C:/Users/poin/.codex/worktrees/587c/RMQ")
COUNTER = REVIEW / "actual-outer-diagnostic-68bbac4f331c4ff5b154e4c68e983681"
IDS = ["LN0-01", "LN0-02", "LN0-03", "LN0-04", "LN0-05", "LN0-06",
       "INV-SEMANTIC-NONVACUITY", "INV-ORACLE-INDEPENDENCE",
       "INV-CATEGORY-SEPARATION", "INV-MUTATION-REPRODUCIBILITY",
       "CHK-FINAL", "CHK-SCOPE", "NP0R1-INTEGRITY", "NP0R1-TOOLCHAIN",
       "NP0R2-STREAMS", "NP0R2-REPORT"]
ALLOWED = {R1 + "integrity_controls.ps1", R1 + "run_owned.ps1",
           R1 + "final_checks.ps1", "scripts/packed_native_lifecycle_stream_check.ps1",
           LEDGER}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def git(*args, input=None):
    result = subprocess.run(["git", "-c", "core.excludesfile=", "-C", str(ROOT),
                             *args], input=input, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, check=False)
    require(result.returncode == 0,
            "git failed: " + repr(args) + ": " + result.stderr.decode(errors="replace"))
    return result.stdout


def sha(raw):
    return hashlib.sha256(raw).hexdigest().upper()


def readj(path):
    return json.loads(Path(path).read_text(encoding="utf-8-sig"))


def pin(path):
    path = Path(path)
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return {"path": str(path), "bytes": path.stat().st_size,
            "sha256": digest.hexdigest().upper()}


def blob(path, ref=BASE, filtered=False):
    return git("cat-file", "--filters", f"{ref}:{path}") if filtered else git("show", f"{ref}:{path}")


def rows(raw):
    text = raw.decode("utf-8", errors="strict")
    require(not any(token in text for token in ("\u00c2\u00ac", "\u00e2\u20ac", "\ufffd")),
            "recognizable mojibake or replacement character")
    answer = {}
    for line in raw.splitlines():
        if not re.match(rb"^\| `[A-Z][A-Z0-9-]*` \|", line):
            continue
        cells = line.split(b"|")
        require(len(cells) == 10, "eight-column row required")
        key = cells[1].strip().strip(b"`").decode("utf-8")
        require(key not in answer, "duplicate ID: " + key)
        answer[key] = line
    return answer


def row_context():
    start = readj(OUT / "START.json")
    require(start["base"] == start["initialHead"] == BASE, "initial exact base")
    require(start["governance"] == GOVERNANCE and start["branch"] == BRANCH,
            "initial governance/branch")
    require(start["initialClean"] is True and start["preflight"] == "PASS",
            "initial clean/preflight evidence")
    require(start["runtimeCatalog"] == ["rmq-audit-prompt", "rmq-coordinator", "rmq-proof-sprint"]
            and start["requiredSkill"] == "rmq-proof-sprint", "runtime catalog")
    prompt_pin = pin(start["prompt"]["path"])
    require(Path(start["prompt"]["path"]).resolve() == (CAMPAIGN / "LIFE-NATIVE-P0-R2_PROMPT.md").resolve(),
            "commissioning prompt path changed")
    require(prompt_pin["bytes"] == start["prompt"]["bytes"] and
            prompt_pin["sha256"] == start["prompt"]["sha256"].upper() == PROMPT_SHA256, "prompt pin changed")
    prompt = Path(start["prompt"]["path"]).read_text(encoding="utf-8-sig")
    requirements = dict(re.findall(r"^- ([A-Z0-9-]+): (.+)$", "\n".join(prompt.splitlines()), re.M))
    frozen_raw = (OUT / "ACCEPTANCE_ROWS.txt").read_bytes()
    require(sha(frozen_raw) == start["frozenRowsSha256"].upper() == FROZEN_SHA256, "initial frozen-row pin changed")
    frozen, inherited = rows(frozen_raw), rows(blob(R1 + "ACCEPTANCE_MATRIX.md"))
    require(list(frozen) == IDS and list(inherited) == IDS[:14], "initial/base exact ordered IDs")
    require(all(frozen[k] == inherited[k] for k in inherited), "initial inherited row bytes changed")
    for key in IDS:
        require(key in requirements and frozen[key].split(b"|")[2].strip().decode() == requirements[key],
                "prompt requirement changed: " + key)
    return frozen, inherited, requirements, prompt_pin


def verify_rows(raw, context):
    frozen, inherited, requirements, _ = context
    current = rows(raw)
    require(list(current) == IDS, "missing/extra/reordered IDs")
    for key in IDS:
        require(current[key] == frozen[key], "frozen row bytes changed: " + key)
        require(current[key].split(b"|")[2].strip().decode() == requirements[key],
                "prompt requirement changed: " + key)
        if key in inherited:
            require(current[key] == inherited[key], "inherited row bytes changed: " + key)
    return current


def row_controls(raw, context):
    first = context[0][IDS[0]]
    require(b"Open at freeze" in raw, "changed-cell control has no mutation target")
    tests = {
        "missing": raw.replace(first, b"", 1),
        "duplicate": raw + b"\n" + first + b"\n",
        "changed-cell": raw.replace(b"Open at freeze", b"Closed at freeze", 1),
        "mojibake": raw.replace(b"Implement", "\u00c2\u00acImplement".encode(), 1),
        "changed-requirement": raw.replace(b"Implement a reproducible probe", b"Implement a label", 1),
        "invalid-utf8": raw.replace(b"Implement", b"\xffImplement", 1),
        "ninth-column": raw.replace(first, first[:-1] + b" extra |", 1),
        "reordered": raw.replace(first, b"", 1) + b"\n" + first + b"\n",
    }
    outcomes = []
    for name, mutated in tests.items():
        require(mutated != raw, "vacuous row control: " + name)
        try:
            verify_rows(mutated, context)
        except (ValueError, UnicodeError) as error:
            outcomes.append({"id": name, "expected": "REJECT", "actual": "REJECT",
                             "surface": str(error)})
        else:
            raise ValueError("negative accepted: " + name)
    verify_rows(raw, context)
    return [{"id": "unchanged", "expected": "ACCEPT", "actual": "ACCEPT"}] + outcomes


def tree(ref):
    answer = {}
    for row in git("ls-tree", "-rz", ref).split(b"\0"):
        if row:
            metadata, path = row.split(b"\t", 1)
            mode, kind, object_id = metadata.decode().split()
            answer[path.decode("utf-8")] = (mode, kind, object_id)
    return answer


def filtered_blobs(paths):
    # One Git subprocess supplies checkout-filtered bytes for all protected paths.
    # Git's batch objectsize is the *unfiltered* size, even when --filters grows
    # LF into CRLF. Use a fresh framing marker and fail on any collision instead
    # of silently truncating filtered content at that unfiltered size.
    names = [f"{BASE}:{path} {path}" for path in paths]
    marker = ("RMQ_CONTRACT_FRAME_" + sha(os.urandom(32)) + " ").encode()
    format_arg = "--batch=" + marker.decode() + "%(objectname) %(objecttype)"
    output = git("cat-file", format_arg, "--filters", input=("\n".join(names) + "\n").encode())
    pieces = output.split(marker)
    require(pieces[0] == b"" and len(pieces) == len(paths) + 1, "cat-file framing collision/missing path")
    for path, piece in zip(paths, pieces[1:]):
        header, content = piece.split(b"\n", 1)
        require(re.fullmatch(rb"[0-9a-f]{40} blob", header) is not None and content.endswith(b"\n"),
                "malformed cat-file response: " + path)
        yield path, content[:-1]


def verify_scope():
    require(git("branch", "--show-current").decode().strip() == BRANCH, "wrong branch")
    git("merge-base", "--is-ancestor", BASE, "HEAD")
    git("merge-base", "--is-ancestor", GOVERNANCE, "HEAD")
    base_tree, current_tree = tree(BASE), tree("HEAD")
    tracked_changes = git("diff", "--name-only", "-z", BASE).decode().split("\0")
    untracked = git("ls-files", "--others", "--exclude-standard", "-z").decode().split("\0")
    staged = git("diff", "--cached", "--name-only", "-z", BASE).decode().split("\0")
    changed = sorted(set(tracked_changes + untracked + staged) - {""})
    require(all(p in ALLOWED or p.startswith(R2) for p in changed), "outside write scope: " + repr(changed))
    protected = [p for p in base_tree if p not in ALLOWED]
    for p, content in filtered_blobs(protected):
        require(current_tree.get(p) == base_tree[p], "protected committed path changed: " + p)
        require((ROOT / p).is_file() and (ROOT / p).read_bytes() == content,
                "protected working bytes changed: " + p)
    ledger_base = blob(LEDGER)
    require(blob(LEDGER, "HEAD").startswith(ledger_base), "committed WDD prefix changed")
    require((ROOT / LEDGER).read_bytes().startswith(blob(LEDGER, filtered=True)), "working WDD prefix changed")
    def integrity_cases(raw):
        blocks = re.findall(rb"(?ms)^\$cases=@\(\n(.*?)^\)\n", raw.replace(b"\r\n", b"\n"))
        require(len(blocks) == 1, "unique original integrity registry block")
        return blocks[0]
    original_cases = integrity_cases(blob(R1 + "integrity_controls.ps1"))
    require(integrity_cases((ROOT / (R1 + "integrity_controls.ps1")).read_bytes()) == original_cases,
            "original fifteen integrity case definitions changed")
    integrity_ids = re.findall(rb"@\{id='([^']+)'", original_cases)
    require(len(integrity_ids) == len(set(integrity_ids)) == 15, "original integrity registry cardinality")
    # The explicitly permitted old callers may change; all other historical
    # reports, receipts, matrices, production/finally/PE/process code are above.
    return {"changedPaths": changed, "protectedBasePaths": len(protected),
            "workflowLedgerAppendOnly": True, "indexScopeChecked": True,
            "unchangedIntegrityCaseDefinitions": [key.decode() for key in integrity_ids],
            "checkoutByteRule": "Every protected base working path equals git cat-file --filters BASE:path; committed modes/blobs also equal the exact base."}


class HistoricalPins:
    def __init__(self):
        self.checked = {}
        self.occurrences = 0
        self.git_sources = []
        self.source_cache = {}

    def check(self, item):
        self.occurrences += 1
        path = Path(item["path"])
        require(path.is_absolute(), "historical pin is not absolute: " + str(path))
        key = str(path.resolve()).lower()
        expected = (item["bytes"], item["sha256"].upper())
        if key in self.checked:
            require(self.checked[key] == expected, "conflicting historical pin: " + str(path))
            return
        historical = None
        for root, refs in [(R1_ROOT, [BASE, "fda02922bf9e8c0707b9913013d3c16c80afe7c9", "1811eeb9e2f783cc455e44a618a99af77b0172ed"]),
                           (ORIGINAL_ROOT, [ORIGINAL_FINAL, ORIGINAL])]:
            try:
                relative = path.relative_to(root).as_posix()
            except ValueError:
                continue
            if relative.startswith(".lake/"):
                break
            for ref in refs:
                cache_key = (relative, ref)
                if cache_key not in self.source_cache:
                    exists = subprocess.run(["git", "-C", str(ROOT), "cat-file", "-e", f"{ref}:{relative}"],
                                            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode == 0
                    self.source_cache[cache_key] = (blob(relative, ref), blob(relative, ref, True)) if exists else None
                source = self.source_cache[cache_key]
                if source:
                    for encoding, raw in zip(["Git blob", "Git checkout filters"], source):
                        if (len(raw), sha(raw)) == expected:
                            historical = {"path": str(path), "repositoryPath": relative, "commit": ref,
                                          "representation": encoding, "bytes": expected[0], "sha256": expected[1]}
                            break
                if historical:
                    break
            # A tracked historical source must match an immutable source version.
            if any(self.source_cache.get((relative, ref)) for ref in refs):
                require(historical is not None, "historical Git source mismatch: " + str(path))
            break
        if historical:
            self.git_sources.append(historical)
        else:
            actual = pin(path)
            require((actual["bytes"], actual["sha256"]) == expected, "raw artifact pin mismatch: " + str(path))
        self.checked[key] = expected

    def walk(self, obj):
        if isinstance(obj, dict):
            if all(k in obj for k in ("path", "bytes", "sha256")):
                self.check(obj)
            for child in obj.values():
                self.walk(child)
        elif isinstance(obj, list):
            for child in obj:
                self.walk(child)


def historical_evidence():
    pins = HistoricalPins()
    original_review_path = CAMPAIGN / "native-p0-review/IDENTITY_ROWS_PINS.json"
    require(pin(original_review_path)["sha256"] == "EDC60E5175DBF15CE0F5AEC42612AC938BADB1A3BE1EB35C8FC5F345FB7C6375", "original reviewed pin index changed")
    original_review = readj(original_review_path)
    for path, expected in original_review["pins"].items():
        pins.check(dict(path=path, **expected))
    require(len(original_review["pins"]) == 251, "original historical pin inventory changed")
    result = json.loads(blob(R1 + "RESULTS.json"))
    final_path = R1_ROOT / ".lake/repair-r1/FINAL_CERTIFICATION.json"
    require(pin(final_path)["sha256"] == "518192E33E7921CB21B2FC87457FE4F5F445D24E3B9EB37772AA49F34F284427", "R1 final certification changed")
    final = readj(final_path)
    pins.walk(result); pins.walk(final)
    require(final["head"] == BASE, "historical certification candidate")
    receipts = {}
    for key in ["native", "focused", "integrityControls", "dependencyControls", "sourceChecks"]:
        receipt = readj(result[key]["receipt"]["path"]); pins.walk(receipt)
        require(receipt["outer"]["ExitCode"] == receipt["actual"]["exitCode"] == 0 and
                not receipt["outer"]["TimedOut"] and not receipt["outer"]["OutputLimitExceeded"],
                "historical ordinary receipt failure: " + key)
        receipts[key] = receipt
    native = readj(result["native"]["summary"]["path"]); pins.walk(native)
    focused = readj(result["focused"]["summary"]["path"]); pins.walk(focused)
    registry = json.loads(blob(NATIVE + "REGISTRY.json"))
    original = json.loads(blob(NATIVE + "RESULTS.json"))
    require(native["success"] and native["integrity"]["success"] and not native["integrity"]["errors"], "historical native success")
    require(native["selected"] == [case["id"] for case in registry["cases"]] and len(native["selected"]) == 23, "historical ordered23 cases")
    require([c["id"] for c in native["checks"]] == [c["id"] for c in original["checks"]] and len(native["checks"]) == 65, "historical65 native checks")
    require([s["name"] for s in native["stages"]] == [s["name"] for s in result["native"]["stages"]] and len(native["stages"]) == 58, "historical58 stages")
    require(len(native["capturedPins"]) == native["integrity"]["checkedPins"] == 616, "historical616 captures")
    require(focused["selected"] == ["pop-unique"] and focused["success"] and focused["integrity"]["success"], "historical focused selector")
    controls = readj(result["integrityControls"]["results"]["path"]); pins.walk(controls)
    require(len(controls["controls"]) == 15 and controls["fixtureRestoration"] and controls["candidateUnchanged"], "historical15 integrity controls/restoration")
    for control in controls["controls"]:
        summary = readj(control["summary"]["path"]); pins.walk(summary)
        expected_out = ["LIFECYCLE-REPLAY evidence=" + summary["runRoot"]]
        if summary["success"]:
            expected_out.append("LIFECYCLE-REPLAY PASS cases=1 selfTest=False")
        expected_err = ([] if summary["failure"] is None else [summary["failure"]]) + summary["integrity"]["errors"]
        require(control["outer"]["StandardOutput"] == expected_out and control["outer"]["StandardError"] == expected_err,
                "historical recorded streams changed: " + control["id"])
    dependencies = readj(result["dependencyControls"]["results"]["path"]); pins.walk(dependencies)
    require(len(dependencies["controls"]) == 19 and dependencies["installedToolsUnchanged"] and dependencies["fixtureRestored"], "historical19 dependency controls/restoration")
    require(len(dependencies["closure"]["nodes"]) == 11 and len(dependencies["oldMissing"]) == 4, "historical11-node closure/four omissions")
    for key in ["checks", "claims"]:
        pins.walk(readj(final["finalChecks"][key]["receipt"]["path"]))
    pins.walk(readj(final["finalChecks"]["exactChecks"]["path"]))
    counter = verify_counterexample(pins)
    return {"originalPins": 251, "distinctVerifiedPins": len(pins.checked), "pinOccurrences": pins.occurrences,
            "historicalSourcePins": pins.git_sources, "nativeCases": 23, "nativeChecks": 65,
            "nativeStages": 58, "nativeCaptures": 616, "integrityControls": 15,
            "dependencyControls": 19, "counterexample": counter}


def verify_counterexample(pins):
    receipt = pin(COUNTER / "RECEIPT.json")
    require(receipt["bytes"] == 4331 and receipt["sha256"] == "D47623CC4480AD592093871D59224ED8DB3B33B5E34D65C64F3BBD08BF7C83F7", "named immutable negative receipt changed")
    record = readj(receipt["path"]); controls = readj(COUNTER / "controls-output/RESULTS.json")
    pins.walk(record); pins.walk(controls)
    require(record["candidate"] == BASE and record["outer"]["ExitCode"] == record["actual"]["exitCode"] == 0 and
            not record["outer"]["TimedOut"] and not record["outer"]["OutputLimitExceeded"], "old actual harness did not accept")
    def receipt_source(path):
        expected = next(p for p in record["pins"] if Path(p["path"]).is_relative_to(R1_ROOT)
                        and Path(p["path"]).relative_to(R1_ROOT).as_posix() == path)
        candidates = [blob(path), blob(path, filtered=True)]
        matched = [b for b in candidates if len(b) == expected["bytes"] and sha(b) == expected["sha256"].upper()]
        require(bool(matched), "counterexample source representation mismatch: " + path)
        return matched[0].decode("utf-8")
    original = receipt_source(R1 + "integrity_controls.ps1")
    rootline = "$repo=[IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../../../../..'))"
    require(original.count(rootline) == 1, "old driver root anchor")
    derived = original.replace(rootline, "$repo='C:/Users/poin/.codex/worktrees/587c/RMQ'")
    anchors = list(re.finditer(r"(?m)^  \$mutation\r?$", derived))
    require(len(anchors) == 1, "old driver body anchor")
    newline = "\r\n" if "\r\n" in derived else "\n"
    position = anchors[0].start()
    derived = derived[:position] + "  [Console]::Error.WriteLine('UNEXPECTED OUTER DIAGNOSTIC')" + newline + derived[position:]
    require(derived.encode() == (COUNTER / "controls-derived.ps1").read_bytes(), "old exact driver delta")
    production = receipt_source("scripts/packed_native_lifecycle_storage_replay.ps1")
    start = production.index("  $LeanRoot = [IO.Path]::GetFullPath($LeanRoot)")
    stop = production.rindex("  $taskSuccess = $true")
    require([c["id"] for c in controls["controls"]] == ["intact-success", "intact-stage-error"], "old two-case selection")
    outcomes = []
    for control in controls["controls"]:
        fixture = Path(control["fixtureSource"]["path"]).read_bytes().decode("utf-8")
        require(fixture.startswith(production[:start]) and fixture.endswith(production[stop:]), "old production prefix/suffix changed")
        summary = readj(control["summary"]["path"]); pins.walk(summary)
        require(summary["integrity"]["success"] and summary["integrity"]["errors"] == [] and len(summary["stages"]) == 1, "old counterexample integrity/stage")
        code = 0 if control["id"] == "intact-success" else 7
        stage = summary["stages"][0]
        require(stage["child"]["exitCode"] == stage["launcher"]["ExitCode"] == code and
                stage["stdout"]["bytes"] == stage["stderr"]["bytes"] == 0, "old inner outcomes")
        expected = ["UNEXPECTED OUTER DIAGNOSTIC"] + ([] if code == 0 else ["PROCESS: fixture-stage actual child or launcher exit differs from 0"])
        require(control["outer"]["StandardError"] == expected and control["actualExit"] == (0 if code == 0 else 1), "old observed outer anomaly")
        outcomes.append({"id": control["id"], "nativeExit": code, "runnerExit": control["actualExit"],
                         "outerStderr": expected, "historicalHarnessAccepted": True})
    require(controls["fixtureRestoration"] and controls["candidateUnchanged"], "old fixture restoration")
    return {"receipt": receipt, "exactOldSourceCommit": BASE, "exactDriverDelta": True,
            "completeProductionPrefixSuffix": True, "actualHarnessExit": 0, "cases": outcomes,
            "scope": "Reverified immutable actual-process evidence; not a new execution and never relabeled rejected."}


def claim_composition():
    provenance_path = ORIGINAL_ROOT / ".lake/lifecycle-native-baseline/source-provenance.json"
    context_path = ORIGINAL_ROOT / ".lake/lifecycle-native-p0/checks/default-claim-context.json"
    provenance, context = readj(provenance_path), readj(context_path)
    actual_tree = tree("HEAD")
    require(len(provenance["sources"]) == 1125, "baseline source count")
    for source in provenance["sources"]:
        path = source["path"]
        require(path in actual_tree and actual_tree[path][2] == source["gitBlob"], "baseline Git blob changed: " + path)
        require(pin(ROOT / path)["sha256"].lower() == source["sha256"].lower(), "baseline working source changed: " + path)
    require(context["scanRoots"] == ["README.md", "artifact", "docs", "paper"] and
            context["excludedFinalRescan"] == [NATIVE.rstrip("/"), "docs/internal/DESIGN_DECISIONS.md", LEDGER], "claim scan boundary changed")
    files = [ROOT / "README.md"] + [p for directory in ["artifact", "docs", "paper"] for p in (ROOT / directory).rglob("*") if p.is_file()]
    live = {p.relative_to(ROOT).as_posix(): p for p in files
            if not p.relative_to(ROOT).as_posix().startswith(NATIVE)
            and p.relative_to(ROOT).as_posix() not in [LEDGER, "docs/internal/DESIGN_DECISIONS.md"]}
    require(set(live) == {e["path"] for e in context["files"]}, "outside claim path set changed")
    for expected in context["files"]:
        actual = pin(live[expected["path"]])
        require(actual["bytes"] == expected["bytes"] and actual["sha256"] == expected["sha256"], "outside claim bytes changed: " + expected["path"])
    for path, key in [("scripts/claim_drift_scan.ps1", "scannerSha256"), ("docs/internal/CLAIM_DRIFT_POLICY.json", "policySha256")]:
        require(pin(ROOT / path)["sha256"] == context[key], "claim dependency changed: " + path)
    resolved_rg = shutil.which("rg")
    require(resolved_rg and Path(resolved_rg).resolve() == Path(context["ripgrepPath"]).resolve(), "ripgrep path changed")
    require(pin(resolved_rg)["sha256"] == context["ripgrepSha256"], "ripgrep bytes changed")
    require((os.environ.get("RIPGREP_CONFIG_PATH") or None) == context["ripgrepConfigPath"], "ripgrep config changed")
    certification = json.loads(blob(NATIVE + "CERTIFICATION.json"))
    full = certification["fullClaims"]
    require(full["actualExit"] == 0 and full["strictFailures"] == 0, "historical default-root claims failed")
    history = HistoricalPins(); history.walk(full)
    full_receipt = readj(full["receipt"]["path"]); history.walk(full_receipt)
    require(full_receipt["actualExit"] == full_receipt["result"]["ExitCode"] == 0 and
            not full_receipt["result"]["TimedOut"] and not full_receipt["result"]["OutputLimitExceeded"] and
            full_receipt["sourceCommit"] == ORIGINAL and full_receipt["command"] == "scripts/claim_drift_scan.ps1 -Strict",
            "historical full scan actual command/exit/timeout/overflow")
    raw_out = next(p for p in full["rawFiles"] if p["path"].endswith("stdout.log"))
    raw_err = next(p for p in full["rawFiles"] if p["path"].endswith("stderr.log"))
    require(raw_err["bytes"] == 0 and Path(raw_out["path"]).read_text(encoding="utf-8-sig").splitlines()[-1] ==
            "CLAIM-DRIFT: scan complete (3479 hits, 0 strict failures)", "historical full scan raw result")
    return {"baselineSources": 1125, "outsideClaimPaths": len(live),
            "baselineProvenance": pin(provenance_path), "defaultClaimContext": pin(context_path),
            "historicalFullScan": full, "scannerPolicyRipgrepConfigUnchanged": True,
            "pendingFinalRescan": [NATIVE.rstrip("/"), "docs/internal/DESIGN_DECISIONS.md", LEDGER],
            "coverage": "Verified original complete default-root scan plus exact unchanged outside paths. Caller must separately supply final unchanged-policy complete subtree/ledger rescan; this verifier does not claim a new full scan."}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", required=True)
    parser.add_argument("--rows-only", action="store_true")
    args = parser.parse_args()
    started = time.monotonic()
    context = row_context(); raw = (OUT / "ACCEPTANCE_MATRIX.md").read_bytes()
    verify_rows(raw, context)
    result = {"success": True, "mode": "rows-only" if args.rows_only else "full-contract",
              "base": BASE, "head": git("rev-parse", "HEAD").decode().strip(),
              "worktree": str(ROOT), "rows": IDS, "inheritedRows": IDS[:14], "changedIds": [],
              "prompt": context[3], "rowControls": row_controls(raw, context),
              "frozenRows": pin(OUT / "ACCEPTANCE_ROWS.txt")}
    if not args.rows_only:
        result["scope"] = verify_scope()
        result["historicalEvidence"] = historical_evidence()
        result["claimComposition"] = claim_composition()
        result["currentOwnedSources"] = [pin(ROOT / p) for p in sorted(ALLOWED) if (ROOT / p).is_file()]
    result["seconds"] = round(time.monotonic() - started, 3)
    Path(args.output).write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    suffix = "" if args.rows_only else (f", {result['scope']['protectedBasePaths']} protected base paths, "
        f"{result['historicalEvidence']['distinctVerifiedPins']} historical pins, "
        f"{result['claimComposition']['outsideClaimPaths']} unchanged outside paths")
    print(f"CONTRACT PASS: 16 frozen rows, 9 row controls{suffix}")


if __name__ == "__main__":
    main()
