/-
Independence regression for the packed structural countdown.

`paper/THEOREM_LEDGER.md` (row `L-PACK-00`) claims that the `210` inside
`427 = 1 + 2*3 + 2*210` is the packed controller's own structural countdown and
is **not** the charged-trace event budget, and states the claim in a precise,
checkable form:

> They are numerically equal and independent at declaration and proof-term
> level: the packed proof references neither `SuccinctClassic.queryCost` nor
> `nonSyntheticWeight`.

That was prose. This script makes it a checked property: it walks the transitive
constant closure of the countdown theorem's type *and* proof term and fails if
either charged-cost declaration appears anywhere in it.

The scope is deliberately narrow, matching the ledger. The claim is about
declarations and proof terms, **not** module closures -- the packed module's
compilation closure does transitively reach the charged declaration
(`ReviewerController` -> `ReviewerSparsePrelude` -> `ReadProgram` ->
`SuccinctFinalStoreParam` -> `SuccinctFinalRAM`). This script guards the true
property, not the false one.

Two anti-vacuity guards, because a dependency check that silently stops finding
anything looks exactly like a dependency check that passes:

* **Existence.** Every name below is resolved against the environment first. A
  rename or a move turns this script into an error, not a pass.
* **Positive control.** The same collector is run on a declaration that *is*
  charged, and must find `nonSyntheticWeight` there. If the collector breaks --
  wrong field walked, closure not transitive, `value?` returning `none` -- the
  control fails and the script fails with it.

Run: `lake env lean scripts/independence_check.lean`
-/
-- The RMQ development is Std-only, so the metaprogramming API is not otherwise
-- in scope. Names below are fully qualified: several RMQ modules introduce
-- their own `Name`, which shadows `Lean.Name` under a bare `open Lean`.
import Lean
import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReviewerArchitectureCapstone
import RMQ.Core.SuccinctFinalModelAdequacy

namespace RMQIndependenceCheck

/-- Every constant reachable from `n`'s type or value, transitively. -/
partial def deps (env : Lean.Environment) (n : Lean.Name) (seen : Lean.NameSet) : Lean.NameSet :=
  if seen.contains n then seen
  else
    let seen := seen.insert n
    match env.find? n with
    | none => seen
    | some ci =>
      let used :=
        ci.type.getUsedConstants ++
          (match ci.value? with
           | some v => v.getUsedConstants
           | none => #[])
      used.foldl (fun acc m => deps env m acc) seen

/-- The packed controller's structural countdown: the source of the `210` in
`427 = 1 + 2*3 + 2*210`. -/
def target : Lean.Name :=
  `RMQ.SuccinctFinal.PackedCellProbe.packedReviewerControllerMeasure_valid_eq_427

/-- The charged-cost declarations the countdown must stay clear of. -/
def forbidden : List Lean.Name :=
  [ `RMQ.SuccinctClassic.queryCost
  , `RMQ.WordRAM.TraceEvent.nonSyntheticWeight ]

/-- Positive control A, **type-reachable**: a projection whose statement *is*
about the charged sum, so the witness sits in its type. -/
def controlType : Lean.Name :=
  `RMQ.SuccinctFinal.ConcreteBPNativeSuccinctRMQFinalTraceModelAdequacy.nonSyntheticWeight_sum_eq_cost

/-- Positive control B, **value-reachable only**. Its type mentions
`TraceEvent` and `Nat` and *not* the witness; only the body reaches the witness.

This control exists because control A alone was not enough, and the gap was
found by injection rather than by reading. Breaking the collector so it never
walks proof terms left control A passing -- it finds the witness in the *type* --
while the real target's closure silently collapsed from 1855 constants to 16 and
still reported PASS. A dependency check that examines nothing passes everything.
Control B fails closed in exactly that case. -/
def valueOnlyControl (e : RMQ.WordRAM.TraceEvent) : Nat :=
  RMQ.WordRAM.TraceEvent.nonSyntheticWeight e

/-- Name of control B. -/
def controlValue : Lean.Name := `RMQIndependenceCheck.valueOnlyControl

/-- The constant both positive controls must exhibit. -/
def controlWitness : Lean.Name := `RMQ.WordRAM.TraceEvent.nonSyntheticWeight

/-- Floor on the target's closure size. Blunt, and deliberately far below the
observed 1855: it does not track drift, it catches collapse. A collector that
truncates deep recursion could still satisfy both controls, which are shallow. -/
def closureFloor : Nat := 500

end RMQIndependenceCheck

#eval show Lean.Elab.Command.CommandElabM Unit from do
  let env ← Lean.getEnv
  let names := RMQIndependenceCheck.target :: RMQIndependenceCheck.controlType ::
    RMQIndependenceCheck.controlValue :: RMQIndependenceCheck.forbidden
  -- Guard 1: existence. A rename must break this script, not quietly pass it.
  let missing := names.filter (fun n => (env.find? n).isNone)
  unless missing.isEmpty do
    throwError "INDEPENDENCE: FAIL (declaration(s) not found: {missing}). \
This script names them explicitly so a rename cannot make the check vacuous. \
Update the names and re-derive the claim; do not delete the check."
  -- Guard 2: positive controls. The collector must find charged constants
  -- through a type (A) *and* through a proof term (B). A alone is not enough:
  -- a collector that never walks values still satisfies it.
  for (lbl, c) in [("A/type", RMQIndependenceCheck.controlType),
                   ("B/value", RMQIndependenceCheck.controlValue)] do
    let d := RMQIndependenceCheck.deps env c Lean.NameSet.empty
    unless d.contains RMQIndependenceCheck.controlWitness do
      throwError "INDEPENDENCE: FAIL (positive control {lbl} did not exhibit \
{RMQIndependenceCheck.controlWitness} in the closure of {c}; closure was \
{d.size} constants). The collector is broken, so a PASS on the real target \
would mean nothing."
    Lean.logInfo m!"INDEPENDENCE: control {lbl} OK ({d.size} constants, \
charged witness present)"
  -- The actual property.
  let targetDeps :=
    RMQIndependenceCheck.deps env RMQIndependenceCheck.target Lean.NameSet.empty
  -- Guard 3: collapse tripwire, for collector regressions the shallow controls
  -- cannot see.
  if targetDeps.size < RMQIndependenceCheck.closureFloor then
    throwError "INDEPENDENCE: FAIL (closure of {RMQIndependenceCheck.target} is \
{targetDeps.size} constants, below the floor of \
{RMQIndependenceCheck.closureFloor}). This is a collapse, not a cleanup: the \
check is examining too little to mean anything. Diagnose the collector before \
touching this floor."
  let leaked := RMQIndependenceCheck.forbidden.filter targetDeps.contains
  unless leaked.isEmpty do
    throwError "INDEPENDENCE: FAIL ({RMQIndependenceCheck.target} now depends \
on charged-cost declaration(s): {leaked}). The two 210s are no longer \
independent at proof-term level, so paper/THEOREM_LEDGER.md row L-PACK-00 and \
the RMQ/Headlines/RMQ.lean docstring are false as written. Fix the dependency \
or retract the claim -- do not weaken this check."
  Lean.logInfo m!"INDEPENDENCE: RESULT: PASS ({RMQIndependenceCheck.target} closure \
= {targetDeps.size} constants, none of {RMQIndependenceCheck.forbidden})"
