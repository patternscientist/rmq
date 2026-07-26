import RMQ.Core.SuccinctFinal.RAM.GeometryClosure

/-!
C06 final independent check of the ported F03 module.

Imports the module as a real dependency -- so this file passes only if the olean
genuinely carries the theorems -- and then tests that they SAY the intended
thing: expected-type pins written from the row text rather than from the proofs,
non-vacuity witnesses, and an anti-bypass consumer.
-/

open RMQ

namespace C06F03

/-! ### 1. Expected-type pins, written independently of the declarations. -/

/-- The literal `EG-CP-F03` claim at the controller: the whole-query trace under
a supplied store depends on the semantic shape only through its size. -/
def ExpectedGeometryClosure : Prop :=
  ∀ (a b : Cartesian.CartesianShape) (store : WordRAM.ReadStore) (l r : Nat),
    a.size = b.size →
      SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
          a store l r =
        SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
          b store l r

/-- The same claim at the public entry, over input lists. -/
def ExpectedPublicClosure : Prop :=
  ∀ (xs ys : List Int) (store : WordRAM.ReadStore) (l r : Nat),
    xs.length = ys.length →
      SuccinctClassic.queryTraceResultWithStore xs store l r =
        SuccinctClassic.queryTraceResultWithStore ys store l r

example : ExpectedGeometryClosure :=
  fun _ _ store l r h =>
    SuccinctFinal.GeometryClosure.T4_wholeQuery_trace_size_only h store l r

example : ExpectedPublicClosure :=
  fun xs ys store l r h =>
    SuccinctFinal.GeometryClosure.queryTraceResultWithStore_size_only xs ys store l r h

/-! ### 2. Non-vacuity: the hypotheses hold off the diagonal. -/

def shapeL : Cartesian.CartesianShape := .node (.node .empty .empty) .empty
def shapeR : Cartesian.CartesianShape := .node .empty (.node .empty .empty)

example : shapeL.size = shapeR.size := by decide
example : shapeL ≠ shapeR := by decide
example : shapeL.bpCode ≠ shapeR.bpCode := by decide

/-- The controller-level theorem instantiated at two genuinely different shapes
of equal size. -/
example (store : WordRAM.ReadStore) (l r : Nat) :
    SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        shapeL store l r =
      SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        shapeR store l r :=
  SuccinctFinal.GeometryClosure.T4_wholeQuery_trace_size_only (by decide) store l r

/-- The public theorem instantiated at two different lists of equal length. -/
example (store : WordRAM.ReadStore) (l r : Nat) :
    SuccinctClassic.queryTraceResultWithStore [3, 1, 2, 0] store l r =
      SuccinctClassic.queryTraceResultWithStore [0, 2, 1, 3] store l r :=
  SuccinctFinal.GeometryClosure.queryTraceResultWithStore_size_only
    [3, 1, 2, 0] [0, 2, 1, 3] store l r rfl

/-! ### 3. Anti-bypass: equal SIZE is the hypothesis, never equal shape. -/

example (a b : Cartesian.CartesianShape) (h : a.size = b.size)
    (store : WordRAM.ReadStore) (l r : Nat) :
    SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        a store l r =
      SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        b store l r :=
  SuccinctFinal.GeometryClosure.T4_wholeQuery_trace_size_only h store l r

/-! ### 4. The positive factorisation: a witness that mentions no input list. -/

example (xs : List Int) (store : WordRAM.ReadStore) (l r : Nat) :
    SuccinctClassic.queryTraceResultWithStore xs store l r =
      SuccinctFinal.GeometryClosure.publicQueryOfLength xs.length store l r :=
  SuccinctFinal.GeometryClosure.queryTraceResultWithStore_factors xs store l r

#print axioms SuccinctFinal.GeometryClosure.T4_wholeQuery_trace_size_only
#print axioms SuccinctFinal.GeometryClosure.queryTraceResultWithStore_size_only
#print axioms SuccinctFinal.GeometryClosure.queryTraceResultWithStore_factors

end C06F03
