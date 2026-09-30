import RMQ.Core.WordRAM.Lifecycle.ArrayRun

/-! # Owner-consuming lifecycle loops

These loops erase the temporary transition records, whose retained pre-states
can otherwise share arrays with the owner being executed. They call exactly
the existing primitive evaluators. The refinements quantify over every program,
fuel, boundary sequence, and owner, including fault and missing-fetch cases.
Native allocation behavior remains a separately measured property.
-/

namespace RMQ.SuccinctFinal.PackedNative.Lifecycle

open PackedLifecycle

def runThin (program : Array Instruction) : Nat → Owner → Owner
  | 0, owner => owner
  | fuel + 1, owner =>
      if owner.status = .running then
        match program[owner.pc]? with
        | none => owner
        | some instruction => runThin program fuel (executeArray instruction owner)
      else owner

theorem runThin_eq_runOwner (program : Array Instruction) (fuel : Nat) (owner : Owner) :
    runThin program fuel owner = runOwner program fuel owner := by
  induction fuel generalizing owner with
  | zero => rfl
  | succ fuel ih =>
      by_cases hs : owner.status = .running
      · cases hf : program[owner.pc]? <;> simp [runThin, runOwner, stepArray, hs, hf, ih]
      · simp [runThin, runOwner, stepArray, hs]

def runBoundaryThin : List Boundary → Owner → Owner
  | [], owner => owner
  | boundary :: rest, owner =>
      match owner.status with
      | .halted _ => runBoundaryThin rest (executeBoundaryArray boundary owner)
      | _ => owner

theorem runBoundaryThin_eq_runBoundaryOwner (boundaries : List Boundary) (owner : Owner) :
    runBoundaryThin boundaries owner = runBoundaryOwner boundaries owner := by
  induction boundaries generalizing owner with
  | nil => rfl
  | cons boundary rest ih =>
      cases hs : owner.status <;>
        simp [runBoundaryThin, runBoundaryOwner, boundaryStepArray, hs, ih]

def requestProtocolThin (entry : PackedConstruction.Operand) (left right : Nat)
    (owner : Owner) : Owner :=
  runBoundaryThin [.left left, .right right, .entry entry, .activate] owner

theorem requestProtocolThin_eq_requestProtocolOwner
    (entry : PackedConstruction.Operand) (left right : Nat) (owner : Owner) :
    requestProtocolThin entry left right owner = requestProtocolOwner entry left right owner :=
  runBoundaryThin_eq_runBoundaryOwner _ _

end RMQ.SuccinctFinal.PackedNative.Lifecycle
