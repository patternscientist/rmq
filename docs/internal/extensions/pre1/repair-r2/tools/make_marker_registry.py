"""Generate docs/internal/extensions/pre1/repair-r2/marker_controls.json (PRE-1-R2)."""
import json
import sys

consumers = {
    "builder": {
        "path": "scripts/preprocessing_builder_check.lean",
        "marker": "PRE1-BUILDER-TYPED-CONSUMERS PASS",
        "deadlineSeconds": 900,
        "declarationAnchor": "#print axioms efficientBuildWord_def\n",
        "witnessAnchor": "def consumerWitness : Unit :=\n",
        "endAnchor": "end PRE1BuilderConsumer",
    },
    "capstone": {
        "path": "RMQ/Validation/PreprocessingContract.lean",
        "marker": "PRE1-CAPSTONE-TYPED-CONSUMERS PASS",
        "deadlineSeconds": 1800,
        "declarationAnchor": "#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.builderProgramWord_static\n",
        "witnessAnchor": "def consumerWitness : Unit :=\n",
        "endAnchor": "end RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks",
    },
    "contract": {
        "path": "scripts/preprocessing_contract_check.lean",
        "marker": "PRE1-CONTRACT-TYPED-CONSUMERS PASS",
        "deadlineSeconds": 900,
        "declarationAnchor": "#print axioms Conservative.execute_eq_of_fits\n",
        "witnessAnchor": "def consumerWitness : Unit :=\n",
        "endAnchor": "end PRE1ContractConsumer",
    },
    "spec": {
        "path": "scripts/preprocessing_spec_check.lean",
        "marker": "PRE1-SPEC-TYPED-CONSUMERS PASS",
        "deadlineSeconds": 1800,
        "declarationAnchor": "#print axioms positions_fixture\n",
        "witnessAnchor": None,
        "endAnchor": "end PRE1SpecConsumer",
    },
    "stage": {
        "path": "scripts/preprocessing_stage_check.lean",
        "marker": "PRE1-STAGE-TYPED-CONSUMERS PASS",
        "deadlineSeconds": 3600,
        "declarationAnchor": "#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_342\n",
        "witnessAnchor": "def consumerWitness : Unit :=\n",
        "endAnchor": "end PRE1StageConsumer",
    },
}

cases = []


def consumer_case(key, cls, requirement, edits, expect_exit, marker, diagnostics, error_at_first_edit):
    cases.append({
        "id": "%s-%s" % (key, cls),
        "kind": "consumer",
        "consumer": key,
        "class": cls,
        "requirement": requirement,
        "edits": edits,
        "expectedExit": expect_exit,
        "expectedMarker": marker,
        "diagnostics": diagnostics,
        "errorAtFirstEdit": error_at_first_edit,
    })


for key, c in consumers.items():
    d = c["declarationAnchor"]
    consumer_case(key, "unchanged", "marker present with exit 0 on the unchanged file", [], "zero", True, [], False)
    consumer_case(key, "a-example", "(a) a failing anonymous example",
                  [{"op": "insert-after", "anchor": d, "text": "example : (2 : Nat) + 2 = 5 := rfl\n"}],
                  "nonzero", False, [], True)
    consumer_case(key, "b-guard", "(b) a failing #guard-style check",
                  [{"op": "insert-after", "anchor": d, "text": "#guard (2 : Nat) + 2 == 5\n"}],
                  "nonzero", False, [], True)
    if key == "builder":
        consumer_case(key, "b-run-cmd", "(b) a failing run_cmd check (the V3-1 host-module check against a different module)",
                      [{"op": "replace",
                        "anchor": "  let host := `RMQ.Core.WordRAM.Construction.Builder.Program\n",
                        "text": "  let host := `RMQ.Core.WordRAM.Construction.Builder.Output\n"}],
                      "nonzero", False, ["V3-1:"], False)
    edits_c = [{"op": "insert-after", "anchor": d,
                "text": "theorem r2MarkerControlDeep : (List.replicate 20000 0).length = 20000 := rfl\n"}]
    edits_d = [{"op": "insert-after", "anchor": d,
                "text": "theorem r2MarkerControlUnknown : (2 : Nat) + 2 = 4 := r2MarkerControlNoSuchConstant\n"}]
    if c["witnessAnchor"] is not None:
        edits_c.append({"op": "insert-after", "anchor": c["witnessAnchor"], "text": "  let _ := @r2MarkerControlDeep\n"})
        edits_d.append({"op": "insert-after", "anchor": c["witnessAnchor"], "text": "  let _ := @r2MarkerControlUnknown\n"})
    consumer_case(key, "c-max-recursion",
                  "(c) a declaration that fails with a maximum-recursion-depth error (the CAB2/CAB4 class), referenced by the witness where one exists",
                  edits_c, "nonzero", False, ["maximum recursion depth has been reached"], True)
    consumer_case(key, "d-unknown-identifier",
                  "(d) an unknown identifier inside a checked theorem, referenced by the witness where one exists",
                  edits_d, "nonzero", False, ["unknown identifier"], True)
    consumer_case(key, "e-unreferenced", "(e) a failure in a declaration the witness does not reference",
                  [{"op": "insert-after", "anchor": d, "text": "theorem r2MarkerControlUnreferenced : (2 : Nat) + 2 = 5 := rfl\n"}],
                  "nonzero", False, [], True)
    if key in ("builder", "capstone"):
        consumer_case(key, "f-after-marker", "additional: a failing check placed after the verdict-marker command",
                      [{"op": "replace", "anchor": c["endAnchor"], "text": "#guard (2 : Nat) + 2 == 5\n" + c["endAnchor"]}],
                      "nonzero", False, [], True)

cases.append({"id": "deadline-descendant-cleanup", "kind": "deadline", "deadlineSeconds": 45,
              "requirement": "an owned child that starts a descendant is removed with its descendant at the deadline"})
for mutation in ("remove-last", "swap-first-two", "version", "content"):
    cases.append({"id": "registry-" + mutation, "kind": "registry", "mutation": mutation, "expectedExit": 1,
                  "expectedMarker": "MARKER-CONTROLS: FAIL registry",
                  "requirement": "a registry that is not the pinned one is rejected before any case"})
selectors = [
    ("omitted", None, True, 0, "MARKER-CONTROLS: SELECTOR-PROBE selected="),
    ("valid", "contract-unchanged", False, 0, "MARKER-CONTROLS: RESULT: PASS executed 1 of 1"),
    ("empty", "''", False, 2, "MARKER-CONTROLS: SELECTOR-ERROR [empty]"),
    ("whitespace", "' '", False, 2, "MARKER-CONTROLS: SELECTOR-ERROR [whitespace]"),
    ("malformed", "Contract_Unchanged", False, 2, "MARKER-CONTROLS: SELECTOR-ERROR [malformed]"),
    ("unknown", "contract-no-such-case", False, 2, "MARKER-CONTROLS: SELECTOR-ERROR [unknown]"),
    ("duplicate", "contract-unchanged,contract-unchanged", False, 2, "MARKER-CONTROLS: SELECTOR-ERROR [duplicate]"),
]
for name, value, probe, code, marker in selectors:
    cases.append({"id": "selector-" + name, "kind": "selector", "selector": value, "probe": probe,
                  "expectedExit": code, "expectedMarker": marker,
                  "requirement": "selector boundary: " + name})

registry = {
    "version": "PRE1-R2-MARKER-CONTROLS-V1",
    "lean": "leanprover/lean4:v4.22.0 through `lake env lean` on a disposable copy outside the repository, LEAN_NUM_THREADS=1",
    "consumers": consumers,
    "cases": cases,
}
text = json.dumps(registry, ensure_ascii=False, indent=2) + "\n"
open(sys.argv[1], "w", encoding="utf-8", newline="\n").write(text)
print(len(cases), "cases")
print(",".join("'%s'" % c["id"] for c in cases))
