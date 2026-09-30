"""R3 contract adapter: new rows/scope, explicitly historical R2 evidence.

The protected R2 parsers remain unchanged. Their historical root/base describe
the runs they inspect, not this checkout. The emitted retainedContracts are
inputs for a separate call of the current PowerShell Assert-LNOuterCapture;
Python reconstruction alone does not establish that production verdict.
"""
import argparse
import importlib.util
import json
from pathlib import Path
import re
import sys
import time

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[5]
HERE = Path(__file__).resolve().parent
NATIVE = "docs/internal/extensions/lifecycle-native-p0/"
R3 = NATIVE + "repair-r3/"
BASE = "9519b2c1af5e2cf59536b311db5e8dc81376a32f"
GOVERNANCE = "7b227c49ef2ec044b702126cc41c9add847eed01"
BRANCH = "codex/life-native-p0-r3-literal-streams"
LEDGER = "docs/internal/WORKFLOW_DESIGN_DECISIONS.md"
ALLOWED = {"scripts/packed_native_lifecycle_stream_check.ps1",
           NATIVE + "repair-r2/certify_profiles.ps1",
           NATIVE + "repair-r1/final_checks.ps1", LEDGER}
CAMPAIGN = Path("C:/Users/poin/Documents/RMQ/lifecycle-implementation-20260920")
R2_ROOT = Path("C:/Users/poin/.codex/worktrees/eafd/RMQ")
R2_BASE = "2307e3ad0739e0e1d9c3f186cdc568631086fddf"
PROMPT_SHA = "901E5559C45A711B92BD686482934596D7259D0D21D7FA628B7C1851969C4172"
FROZEN_SHA = "D567FF2B9F861A6A910CC94A9E7ABB44D2D559893CBBC7293CEFBE798CE01ABF"
MANIFEST_SHA = "5C41CAB7E65E07E14763E2977E66AB06073901E0A9E70252C130E0F9A5E23E15"
FINAL_SHA = "7AA1748F86B6BE85C9DC40602D1B78DFD0AC73AD57BF848010E98B3BE989BF03"
PROFILE_SHA = "FA532B198B5EF6D627F61EF645FE3B030B640B28A1E489C2E1DCC950EFC63ACF"


def load(name, filename, expected_sha):
    path = ROOT / (NATIVE + "repair-r2/" + filename)
    import hashlib
    if hashlib.sha256(path.read_bytes()).hexdigest().upper() != expected_sha:
        raise ValueError("protected R2 parser identity: " + filename)
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


C = load("r3_inherited_contract", "verify_contract.py",
         "6F1CFB871656215513FA91F617EA563BC9B2EE4EBFBE04D77A7F2E7C30A69871")
V = load("r3_historical_results", "verify_results.py",
         "CE931FD260A5FDA818E06BEEF1C66C6152189B46984FC4510EB445376244CAD2")
# Explicitly configure only the historical result parser's producing root.
# Its base remains 2307; current scope and final dispatch use 9519 separately.
V.ROOT = R2_ROOT
# Git plumbing only asks for immutable object/history data shared by these
# worktrees. Use the governed current checkout, without changing a safe.directory
# setting or pretending that the captures were produced in the current root.
V.git = C.git
IDS = C.IDS + ["NP0R3-LITERAL", "NP0R3-SELECTOR"]
need, git, pin = C.require, C.git, C.pin


def row_context():
    start, freeze = C.readj(HERE / "START.json"), C.readj(HERE / "FREEZE.json")
    need(start["base"] == start["head"] == BASE and start["branch"] == BRANCH,
         "initial exact base/branch")
    need(Path(start["worktree"]).resolve() == ROOT and start["initialClean"] is True
         and start["initialStatus"] == "", "initial clean exact worktree")
    need(start["governance"] == GOVERNANCE and start["preflightExit"] == 0
         and start["runtimeProjectSkills"] == ["rmq-audit-prompt", "rmq-coordinator", "rmq-proof-sprint"]
         and start["requiredSkills"] == ["rmq-proof-sprint"], "preflight role inventory")
    expected_preflight = ["governance=" + GOVERNANCE, "checkout=" + BASE]
    expected_preflight += [key + "=rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint"
                          for key in ["expected", "checkout_skills", "working_skills", "runtime_skills"]]
    expected_preflight += ["required=rmq-proof-sprint", "required_mode=role-skills", "PASS"]
    need([line for line in start["preflightOutput"] if line.startswith("SKILL-PREFLIGHT: ")]
         == ["SKILL-PREFLIGHT: " + line for line in expected_preflight], "complete preflight outcome")
    prompt_path = CAMPAIGN / "LIFE-NATIVE-P0-R3_PROMPT.md"
    prompt = pin(prompt_path)
    need(prompt["bytes"] == 28741 and prompt["sha256"] == PROMPT_SHA,
         "independently pinned commissioning prompt")
    need(Path(freeze["prompt"]["path"]).resolve() == prompt_path.resolve()
         and freeze["prompt"]["bytes"] == 28741
         and freeze["prompt"]["sha256"].upper() == PROMPT_SHA, "freeze prompt identity")
    raw = (HERE / "ACCEPTANCE_ROWS.txt").read_bytes()
    need(C.sha(raw) == FROZEN_SHA == freeze["rowsSha256"].upper(), "initial full row bytes")
    need(freeze["base"] == BASE and freeze["ids"] == IDS and freeze["inherited"] == 16,
         "freeze exact ordered contract")
    requirements = dict(re.findall(r"^- ([A-Z0-9-]+): (.+)$",
                        "\n".join(prompt_path.read_bytes().decode("utf-8-sig", errors="strict").splitlines()), re.M))
    frozen = C.rows(raw)
    inherited = C.rows(C.blob(NATIVE + "repair-r2/ACCEPTANCE_MATRIX.md", BASE))
    need(list(frozen) == IDS and list(inherited) == IDS[:16], "initial ordered inherited IDs")
    for key in IDS:
        need(frozen[key].split(b"|")[2].strip().decode("utf-8") == requirements[key],
             "pinned prompt requirement: " + key)
        if key in inherited:
            need(frozen[key] == inherited[key], "exact inherited full row: " + key)
    return frozen, inherited, requirements, prompt


def verify_rows(raw, context):
    frozen, inherited, requirements, _ = context
    current = C.rows(raw)
    need(list(current) == IDS, "missing/extra/reordered IDs")
    for key in IDS:
        need(current[key] == frozen[key], "frozen full row changed: " + key)
        need(current[key].split(b"|")[2].strip().decode("utf-8") == requirements[key],
             "pinned prompt requirement changed: " + key)
        if key in inherited:
            need(current[key] == inherited[key], "inherited full row changed: " + key)


def row_controls(raw, context):
    first = context[0][IDS[0]]
    tests = {
        "missing": raw.replace(first, b"", 1),
        "duplicate": raw + b"\n" + first + b"\n",
        "changed-cell": raw.replace(b"Open at freeze", b"Closed at freeze", 1),
        "mojibake": raw.replace(b"Implement", "\u00c2\u00acImplement".encode(), 1),
        "changed-requirement": raw.replace(b"Implement a reproducible probe", b"Implement a label", 1),
        "invalid-utf8": raw.replace(b"Implement", b"\xffImplement", 1),
        "ninth-column": raw.replace(first, first[:-1] + b" extra |", 1),
        "reordered": raw.replace(first, b"", 1) + b"\n" + first + b"\n",
        "literal-requirement": raw.replace(b"literal equality after strict", b"cultural equality after strict", 1),
        "selector-requirement": raw.replace(b"explicitly bound null", b"implicitly bound null", 1),
    }
    results = [{"id": "unchanged", "expected": "ACCEPT", "actual": "ACCEPT"}]
    verify_rows(raw, context)
    for key, mutant in tests.items():
        need(mutant != raw, "vacuous row mutation: " + key)
        try:
            verify_rows(mutant, context)
        except (ValueError, UnicodeError) as error:
            results.append(dict(id=key, expected="REJECT", actual="REJECT", surface=str(error)))
        else:
            raise ValueError("row mutation accepted: " + key)
    return results


def verify_scope():
    need(git("branch", "--show-current").decode().strip() == BRANCH, "current exact branch")
    need(Path(git("rev-parse", "--show-toplevel").decode().strip()).resolve() == ROOT, "current exact root")
    for ref in [BASE, GOVERNANCE]:
        git("merge-base", "--is-ancestor", ref, "HEAD")
    base_tree, current_tree = C.tree(BASE), C.tree("HEAD")
    changed = set()
    for args in [("diff", "--name-only", "-z", BASE),
                 ("diff", "--cached", "--name-only", "-z", BASE),
                 ("ls-files", "--others", "--exclude-standard", "-z")]:
        changed.update(git(*args).decode("utf-8").split("\0"))
    changed.discard("")
    need(all(path in ALLOWED or path.startswith(R3) for path in changed),
         "outside R3 write scope: " + repr(sorted(changed)))
    protected = [path for path in base_tree if path not in ALLOWED]
    # filtered_blobs takes its ref from the inherited module's BASE variable.
    # Limit this temporary binding to this helper, then restore its historical
    # base before any historical source or baseline composition is evaluated.
    old_base = C.BASE
    try:
        C.BASE = BASE
        for path, raw in C.filtered_blobs(protected):
            need(current_tree.get(path) == base_tree[path], "protected committed mode/blob: " + path)
            need((ROOT / path).is_file() and (ROOT / path).read_bytes() == raw,
                 "protected checkout-filtered bytes: " + path)
    finally:
        C.BASE = old_base
    need(C.blob(LEDGER, "HEAD").startswith(C.blob(LEDGER, BASE)), "committed WDD prefix changed")
    need((ROOT / LEDGER).read_bytes().startswith(C.blob(LEDGER, BASE, True)), "working WDD prefix changed")
    return dict(changedPaths=sorted(changed), protectedBasePaths=len(protected),
                workflowLedgerAppendOnly=True, indexScopeChecked=True,
                narrowHistoricalEdits=narrow_historical_edits(),
                checkoutByteRule="Committed mode/blob and actual git cat-file --filters 9519 bytes both checked.")


def narrow_historical_edits():
    """Exact anchored transformations bind all other inherited caller bytes."""
    guard = "\n".join([
        "# Validate the complete selection before creating output or invoking any profile.",
        "if($PSBoundParameters.ContainsKey('Kinds')){",
        "  if($null -eq $Kinds -or $Kinds.Count -eq 0 -or @($Kinds|Where-Object {[string]::IsNullOrWhiteSpace($_)}).Count){throw 'CERTIFY-SELECTOR: empty'}",
        "  $known=[Collections.Generic.HashSet[string]]::new([string[]]@('focused','full','integrity','dependencies','checks','claims'),[StringComparer]::Ordinal)",
        "  $seen=[Collections.Generic.HashSet[string]]::new([StringComparer]::Ordinal)",
        "  foreach($kind in $Kinds){",
        "    if(-not $known.Contains($kind)){throw 'CERTIFY-SELECTOR: unknown'}",
        "    if(-not $seen.Add($kind)){throw 'CERTIFY-SELECTOR: duplicate'}",
        "  }", "}", ""])
    facts = []
    for path in sorted(ALLOWED - {LEDGER}):
        candidates = []
        for filtered in [False, True]:
            source = C.blob(path, BASE, filtered).decode("utf-8", errors="strict")
            newline = "\r\n" if "\r\n" in source else "\n"
            def replace(old, new):
                nonlocal source
                need(source.count(old) == 1, "unique inherited syntax anchor: " + path)
                source = source.replace(old, new)
            if path.endswith("packed_native_lifecycle_stream_check.ps1"):
                replace("if($Actual -cne $Expected)",
                        "if(-not [string]::Equals($Actual,$Expected,[StringComparison]::Ordinal))")
                replace("rev-list --reverse '" + R2_BASE + "..HEAD'",
                        "rev-list --reverse '" + BASE + "..HEAD'")
            elif path.endswith("final_checks.ps1"):
                replace("$base='" + R2_BASE + "'", "$base='" + BASE + "'")
                replace("'../repair-r2/verify_contract.py'", "'../repair-r3/verify_contract.py'")
            else:
                anchor = "$ErrorActionPreference='Stop'" + newline
                replace(anchor, anchor + guard.replace("\n", newline))
                replace("  if($kind -cnotin @('focused','full','integrity','dependencies','checks','claims')){throw 'unsupported certification profile'}" + newline, "")
            candidates.append(source.encode("utf-8"))
        need((ROOT / path).read_bytes() in candidates, "historical caller delta exceeds exact authorized repair: " + path)
        facts.append(dict(path=path, allOtherInheritedBytesPreserved=True,
                          representation="exact Git blob or exact checkout-filtered bytes, then only prescribed anchored edit"))
    return facts


class HistoricalPins(V.Pins):
    """Tracked historical sources use exact Git identities; raw artifacts use files."""
    def __init__(self):
        super().__init__()
        self.git_sources = []
        self.blobs = {}
        self.trees = {}

    def add(self, path, expected=None):
        path = Path(path).resolve()
        key = str(path).lower()
        if expected is None or key in self.records:
            return super().add(path, expected)
        contexts = [(R2_ROOT, [BASE, "4d6f195b306bd1615aced8c7a7cd1db0d48a8d69",
                               "c3fcc2e0beb08d090382f56d16dbe9446639164a"]),
                    (C.R1_ROOT, [R2_BASE, "fda02922bf9e8c0707b9913013d3c16c80afe7c9",
                                 "1811eeb9e2f783cc455e44a618a99af77b0172ed"]),
                    (C.ORIGINAL_ROOT, [C.ORIGINAL_FINAL, C.ORIGINAL])]
        for root, refs in contexts:
            if not path.is_relative_to(root):
                continue
            relative = path.relative_to(root).as_posix()
            if relative.startswith(".lake/"):
                break
            found_source = False
            for ref in refs:
                cache_key = (ref, relative)
                if cache_key not in self.blobs:
                    if ref not in self.trees:
                        self.trees[ref] = C.tree(ref)
                    if relative not in self.trees[ref]:
                        self.blobs[cache_key] = None
                    else:
                        self.blobs[cache_key] = [(kind, C.blob(relative, ref, filtered))
                                                for kind, filtered in [("Git blob", False), ("Git checkout filters", True)]]
                for representation, raw in self.blobs[cache_key] or []:
                    found_source = True
                    if len(raw) == expected["bytes"] and C.sha(raw) == expected["sha256"].upper():
                        item = dict(path=str(path), bytes=len(raw), sha256=C.sha(raw))
                        self.records[key] = item
                        self.occurrences += 1
                        self.git_sources.append(dict(**item, repositoryPath=relative, commit=ref,
                                                     representation=representation))
                        return item
            if found_source:
                # Some preserved Windows working sources were written with CRLF
                # although their exact Git blobs and today's smudge result use
                # LF. Check their actual raw pin first; only the source-to-Git
                # relation uses the unchanged repository's clean filter. Raw
                # stdout/stderr never enter this tracked-source branch.
                actual = C.pin(path)
                need(actual["bytes"] == expected["bytes"] and actual["sha256"] == expected["sha256"].upper(),
                     "retained historical source raw pin: " + str(path))
                object_id = git("hash-object", "--path=" + relative, "--stdin", input=path.read_bytes()).decode().strip()
                matches = [ref for ref in refs if self.trees[ref].get(relative, (None, None, None))[2] == object_id]
                need(bool(matches), "historical tracked clean-filter identity: " + str(path))
                self.records[key] = actual
                self.occurrences += 1
                self.git_sources.append(dict(**actual, repositoryPath=relative, commit=matches[0],
                    gitBlob=object_id, representation="Exact retained raw source pin plus Git clean-filter blob identity"))
                return actual
            need(not found_source, "historical tracked Git identity mismatch: " + str(path))
            break
        return super().add(path, expected)


def integrity_contracts(result):
    """Reconstruct fixed case diagnostics, preserving the old Windows runtime text.

    Lock and decoder wording below is the pinned historical platform contract,
    derived there by the source's independent lock/decode operations. It is not
    asserted as a portable .NET wording or inferred from current capture text.
    """
    contracts = []
    for row in result["controls"]:
        key = row["id"]
        summary = V.readj(row["summary"]["path"])
        run = Path(summary["runRoot"])
        fixture = Path(row["fixtureSource"]["path"]).parents[1]
        errors = []
        pin_cases = ["stage-error-and-pin-change", "success-and-pin-change",
                     "mixed-diagnostic-and-pin-change", "timeout-and-pin-change", "partial-identity-and-pin-change"]
        if key in pin_cases:
            errors.append("INTEGRITY: changed captured pin: " + str(fixture / "native/packed-rmq/tests/lifecycle_storage_probe.c"))
        if key == "success-and-link-map-change":
            errors.append("INTEGRITY: changed captured pin: " + str(run / "link.map"))
        if key in pin_cases + ["success-and-tracked-change", "success-and-index-change",
                               "success-and-untracked-addition", "success-and-untracked-byte-change"]:
            errors.append("INTEGRITY: live tracked/index/untracked baseline changed")
        if key == "missing-baseline":
            errors.append("INTEGRITY: UNCOVERED; initial tree inventory unavailable")
        if key == "stage-error-and-capture-error":
            path = str(run / "link.map")
            errors.append("INTEGRITY: artifact capture failed: " + path + "; The process cannot access the file '"
                          + path + "' because it is being used by another process.")
        failure = None
        if key in ["intact-stage-error", "stage-error-and-pin-change", "stage-error-and-capture-error"]:
            failure = "PROCESS: fixture-stage actual child or launcher exit differs from 0"
        elif key == "timeout-and-pin-change":
            failure = "PROCESS: fixture-stage was not a completed bounded process; see retained logs"
        elif key == "mixed-diagnostic-and-pin-change":
            failure = "DIAGNOSTIC: unexpected or mixed stderr for fixture-stage"
        elif key == "partial-identity-and-pin-change":
            failure = "IDENTITY: missing file " + str(fixture / "missing-tool.exe")
        elif key == "malformed-stdout-intact":
            failure = ('DIAGNOSTIC: invalid raw stage evidence for fixture-stage; Exception calling "ReadAllText" '
                       'with "2" argument(s): "Unable to translate bytes [FF] at index 0 from specified code page to Unicode."')
        need(summary["failure"] == failure and summary["integrity"]["errors"] == errors,
             "source-derived complete historical diagnostic order: " + key)
        stdout = "LIFECYCLE-REPLAY evidence=" + str(run) + V.NL
        if key == "intact-success":
            stdout += "LIFECYCLE-REPLAY PASS cases=1 selfTest=False" + V.NL
        stderr = "".join(message + V.NL for message in ([failure] if failure else []) + errors)
        expected = dict(expectedStdout=stdout, expectedStderr=stderr,
                        expectedExit=0 if key == "intact-success" else 1, validated=True)
        need(row["streamContract"] == expected, "independently reconstructed historical stream contract: " + key)
        contracts.append(dict(id="integrity-" + key, profile="integrity-" + key,
                              producingRoot=str(R2_ROOT), capture=row["capture"],
                              sourcePins=[row["fixtureSource"]], rawPins=[row["summary"]] + row["capture"]["raw"],
                              **expected))
    return contracts


def historical_r2():
    pins = HistoricalPins()
    review_manifest = CAMPAIGN / "native-p0-r2-review/EVIDENCE_PIN_MANIFEST.json"
    need(pin(review_manifest)["sha256"] == MANIFEST_SHA, "independent R2 review pin inventory")
    inventory = V.readj(review_manifest)
    need(inventory["count"] == len(inventory["entries"]) == 3016 and inventory["occurrences"] == 4498,
         "reviewed R2 inventory cardinality")
    for item in inventory["entries"]:
        pins.add(item["path"], item)
    final_path = R2_ROOT / ".lake/repair-r2/FINAL_CERTIFICATION.json"
    need(pin(final_path)["sha256"] == FINAL_SHA, "R2 exact final certificate")
    final = V.readj(final_path)
    need(final["base"] == R2_BASE and final["finalPackageCommit"] == BASE,
         "historical final package/base identity")
    profiles_path = Path(final["finalProfileManifest"]["path"])
    need(pin(profiles_path)["sha256"] == PROFILE_SHA, "R2 final manifest identity")
    manifest = V.readj(profiles_path)
    need(manifest["head"] == BASE and set(manifest["profiles"]) == set(V.PROFILES),
         "R2 historical six-profile final manifest")
    claim_receipt = V.readj(manifest["profiles"]["claims"])
    claim_path = claim_receipt["claimExpectation"]["path"]
    need(Path(manifest["claimExpectationPath"]).resolve() == Path(claim_path).resolve(),
         "historical claims producing expectation identity")
    facts, baselines, contracts = {}, {}, []
    for kind in V.PROFILES:
        receipt, capture, receipt_pin = V.profile_receipt(kind, manifest["profiles"][kind], pins)
        capture["raw"] = receipt["raw"]
        stdout = V.raw(capture["spec"]["stdout"])
        baselines[kind] = stdout
        fact = (V.native_summary(kind, stdout, pins) if kind in ["focused", "full"] else
                V.integrity_results(stdout, pins) if kind == "integrity" else
                V.dependency_results(stdout, pins) if kind == "dependencies" else
                V.claim_records(stdout, claim_path, pins) if kind == "claims" else
                V.check_results(stdout, pins))
        facts[kind] = dict(receipt=receipt_pin, facts=fact)
        # Each parser above independently checks the whole source-derived
        # language. Claims admits any ordering of its exact record multiset.
        contracts.append(dict(id="profile-" + kind, profile="wrapper-" + kind,
                              producingRoot=str(R2_ROOT), capture=capture,
                              sourcePins=[], rawPins=[receipt_pin] + receipt["raw"],
                              expectedStdout=stdout, expectedStderr="", expectedExit=0, validated=True))
    need(facts["checks"]["facts"]["head"] == BASE, "historical final checks head")
    ledger = V.readj(final["finalLedger"]["record"]["path"])
    harness = V.verify_harness(ledger["harness"]["results"]["path"], pins)
    wrapper = V.verify_wrapper_controls(ledger["wrapperControls"]["results"]["path"],
                                        profiles_path, baselines, pins, claim_path)
    old = V.old_reproduction(ledger["oldReproduction"]["receipt"]["path"], pins)
    controls = V.readj(facts["integrity"]["facts"]["results"]["path"])
    contracts += integrity_contracts(controls)
    source_paths = ["scripts/packed_native_lifecycle_stream_check.ps1",
                    "scripts/packed_native_lifecycle_storage_replay.ps1",
                    "scripts/owned_process_tree.ps1",
                    NATIVE + "repair-r1/run_owned.ps1", NATIVE + "repair-r1/integrity_controls.ps1",
                    NATIVE + "repair-r1/final_checks.ps1", NATIVE + "repair-r2/claim_expectations.ps1"]
    source_pins = []
    for path in source_paths:
        historical = R2_ROOT / path
        need(historical.read_bytes() in [C.blob(path, BASE), C.blob(path, BASE, True)],
             "producing historical caller bytes: " + path)
        source_pins.append(dict(**pins.add(historical), repositoryPath=path, commit=BASE))
    for contract in contracts:
        contract["sourcePins"] += source_pins
    need(len(contracts) == 21 and len({c["id"] for c in contracts}) == 21,
         "six historical profiles plus fifteen integrity contracts")
    return dict(producingRoot=str(R2_ROOT), historicalBase=R2_BASE, packageCommit=BASE,
                independentReviewManifest=pin(review_manifest), verifiedManifestEntries=3016,
                finalCertificate=pin(final_path), profiles=facts, harness=harness,
                wrapperControls=wrapper, oldReproduction=old, distinctPins=len(pins.records),
                pinOccurrences=pins.occurrences, historicalGitSources=pins.git_sources,
                meaning="Preserved finite historical executions and exact raw bytes; not new native runs or a current-head checks roster."), contracts


def current_registries():
    literal_path, retained_path = HERE / "CONTROL_REGISTRY.json", HERE / "retained_registry.json"
    need(pin(literal_path)["sha256"] == "16E26C5B131BBE258B3813BCDB252414E8BED454EF6286EB2ED7F7EF3496261D",
         "frozen new literal/selector registry complete bytes")
    need(pin(retained_path)["sha256"] == "521BFA0CD6DEE84383AB41F8B7D6CC0F226EEFABFC96113EF5EBE835A48A20EB",
         "frozen retained registry complete bytes")
    literal, retained = V.readj(literal_path), V.readj(retained_path)
    expected = []
    for stage in ["success", "error"]:
        expected.append("literal-" + stage + "-exact")
        expected += ["literal-" + stage + "-" + mutation + "-" + channel
                     for mutation in ["bom", "nul", "shy", "ascii"] for channel in ["stdout", "stderr"]]
    expected += ["holdout-" + key for key in ["lf-crlf", "normalization", "zero-width", "nonbreaking-space",
                                              "invalid-utf8", "overlong-utf8", "literal-codepoints"]]
    expected += ["selector-" + key for key in ["null", "empty-array", "empty-string", "whitespace", "unknown",
                                               "duplicate", "late-empty", "late-unknown", "unknown-bom", "unknown-nul", "focused"]]
    expected += ["integrity-caller-pair"]
    V.roster([row["id"] for row in literal["controls"]], expected, "new37 registry")
    need(literal["defaultProfiles"] == ["focused", "full", "integrity", "dependencies", "checks", "claims"],
         "actual default profile roster")
    need(retained["oldHead"] == BASE and Path(retained["historicalRoot"]).resolve() == R2_ROOT
         and retained["profiles"] == V.PROFILES and retained["integrity"] == V.INTEGRITY_IDS,
         "retained historical source/roster identity")
    retained_ids = ["profile-" + key for key in V.PROFILES] + ["integrity-" + key for key in V.INTEGRITY_IDS]
    for category in ["root", "leaf", "copiedFocused", "syntheticLauncher"]:
        keys = [row["id"] for row in retained[category]]
        need(len(keys) == len(set(keys)), "duplicate retained category ID")
        retained_ids += [category + "-" + key for key in keys]
    need(len(retained_ids) == len(set(retained_ids)) == 40, "retained40 exact ordered unique roster")
    return dict(literal=pin(literal_path), literalIds=expected, retained=pin(retained_path),
                retainedIds=retained_ids,
                boundary="Exact whole registry bytes bind IDs, case objects, predicates, evidence tiers and expected verdicts; execution remains a separate production check.")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", required=True)
    parser.add_argument("--rows-only", action="store_true")
    args = parser.parse_args()
    started = time.monotonic()
    context = row_context()
    raw = (HERE / "ACCEPTANCE_MATRIX.md").read_bytes()
    verify_rows(raw, context)
    result = dict(success=True, mode="rows-only" if args.rows_only else "full-contract",
                  base=BASE, head=git("rev-parse", "HEAD").decode().strip(), worktree=str(ROOT),
                  historicalHead=BASE, historicalRoot=str(R2_ROOT), verifier=pin(__file__),
                  rows=IDS, inheritedRows=IDS[:16], changedIds=[], prompt=context[3],
                  frozenRows=pin(HERE / "ACCEPTANCE_ROWS.txt"), rowControls=row_controls(raw, context))
    if not args.rows_only:
        result["scope"] = verify_scope()
        result["currentRegistries"] = current_registries()
        result["historicalR1"] = C.historical_evidence()
        result["historicalR2"], result["retainedContracts"] = historical_r2()
        result["claimComposition"] = C.claim_composition()
        result["currentOwnedSources"] = [pin(ROOT / p) for p in sorted(ALLOWED)]
        result["pendingProductionChecks"] = [
            "Current Assert-LNOuterCapture on all 21 retainedContracts, with original paths unchanged",
            "Complete new literal/selector registry and actual focused certify_profiles invocation",
            "Current-head final checks and fresh entire native subtree/both-ledger strict claims"]
    result["seconds"] = round(time.monotonic() - started, 3)
    Path(args.output).write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    suffix = "" if args.rows_only else (f", {result['scope']['protectedBasePaths']} protected paths, "
        "R2 native23/65/58 integrity15 dependency19 harness11 wrapper120 retained, 21 historical contracts")
    print(f"CONTRACT PASS: 18 frozen rows, {len(result['rowControls'])} row controls{suffix}")


if __name__ == "__main__":
    main()
