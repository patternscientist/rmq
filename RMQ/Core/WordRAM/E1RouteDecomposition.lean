import RMQ.Core.SuccinctFinalRAM

/-!
# E1 route inventory: positional decomposition of the whole-query trace

The accepted whole-query object
`concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult` is the fold of
the five-instruction closed control program
`concreteBPNativeSuccinctRMQWholeQueryProgram` under
`WholeQueryProgram.evalGlobalWordTrace`.  The E1 machine simulation
(frozen matrix REQ-E1-03/04) proceeds component by component, so it needs
the whole-query trace pinned - POSITIONALLY - as the concatenation of the
component traces actually taken by the control flow, and the whole-query
value pinned as the corresponding register expression.

This module records that inventory as checked theorems, one per control
branch:

* both selects hit and the structural close/LCA answers: the trace is
  `select(left) ++ select(right-1) ++ lca ++ rank(answer+1)` and the value
  is the predecessor of the rank answer;
* both selects hit but the close/LCA misses: the trace stops after the
  (empty-trace-free) LCA leg and the value is `none`;
* either select misses: the trace is just the two select legs and the
  value is `none`.

Nothing here mentions the machine; these are route-side facts consumed by
the E1 simulation modules.
-/

namespace RMQ
namespace SuccinctFinal

/--
Whole-query decomposition, full valid path: if both select-close legs
produce closes and the all-size structural close/LCA leg produces an
answer close, the whole-query global trace is positionally the
concatenation of the four component traces, and the value is the
predecessor of the answer-rank result.
-/
theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_decompose_of_selects_lca_some
    (shape : Cartesian.CartesianShape) (left right : Nat)
    {leftClose rightClose answerClose : Nat}
    (hleft :
      (concreteBPNativeSelectCloseGlobalWordTraceResult shape left).value =
        some leftClose)
    (hright :
      (concreteBPNativeSelectCloseGlobalWordTraceResult shape
          (right - 1)).value = some rightClose)
    (hlca :
      (concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
          shape leftClose rightClose).value = some answerClose) :
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).trace =
      (concreteBPNativeSelectCloseGlobalWordTraceResult shape left).trace ++
        (concreteBPNativeSelectCloseGlobalWordTraceResult shape
          (right - 1)).trace ++
        (concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
          shape leftClose rightClose).trace ++
        (concreteBPNativeRankCloseWordTraceResultAtSegment shape
          concreteBPNativeRankCloseTraceSegmentBase (answerClose + 1)).trace ∧
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).value =
      some
        ((concreteBPNativeRankCloseWordTraceResultAtSegment shape
            concreteBPNativeRankCloseTraceSegmentBase
            (answerClose + 1)).value - 1) := by
  constructor <;>
    simp [concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult,
      concreteBPNativeSuccinctRMQWholeQueryProgram,
      WholeQueryProgram.evalGlobalWordTrace,
      WholeQueryInstr.evalGlobalWordTrace,
      WordRAM.TraceResult.map, WordRAM.TraceResult.bind,
      WordRAM.TraceResult.pure, WholeQueryNatExpr.eval,
      WholeQueryState.empty, WholeQueryState.opt, WholeQueryState.setOpt,
      WholeQueryState.nat, WholeQueryState.setNat,
      hleft, hright, hlca, List.append_assoc]

/--
Whole-query decomposition, close/LCA miss: if both select-close legs
produce closes but the all-size structural close/LCA leg answers `none`,
the whole-query global trace is the three-leg concatenation (the rank leg
never runs) and the value is `none`.
-/
theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_decompose_of_lca_none
    (shape : Cartesian.CartesianShape) (left right : Nat)
    {leftClose rightClose : Nat}
    (hleft :
      (concreteBPNativeSelectCloseGlobalWordTraceResult shape left).value =
        some leftClose)
    (hright :
      (concreteBPNativeSelectCloseGlobalWordTraceResult shape
          (right - 1)).value = some rightClose)
    (hlca :
      (concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
          shape leftClose rightClose).value = none) :
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).trace =
      (concreteBPNativeSelectCloseGlobalWordTraceResult shape left).trace ++
        (concreteBPNativeSelectCloseGlobalWordTraceResult shape
          (right - 1)).trace ++
        (concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
          shape leftClose rightClose).trace ∧
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).value = none := by
  constructor <;>
    simp [concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult,
      concreteBPNativeSuccinctRMQWholeQueryProgram,
      WholeQueryProgram.evalGlobalWordTrace,
      WholeQueryInstr.evalGlobalWordTrace,
      WordRAM.TraceResult.map, WordRAM.TraceResult.bind,
      WordRAM.TraceResult.pure, WholeQueryNatExpr.eval,
      WholeQueryState.empty, WholeQueryState.opt, WholeQueryState.setOpt,
      hleft, hright, hlca, List.append_assoc]

/--
Whole-query decomposition, left-select miss: the whole-query global trace
is the two select legs and the value is `none` (the close/LCA instruction
writes `none` without running its leaf, and the rank leg never runs).
-/
theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_decompose_of_left_select_none
    (shape : Cartesian.CartesianShape) (left right : Nat)
    (hleft :
      (concreteBPNativeSelectCloseGlobalWordTraceResult shape left).value =
        none) :
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).trace =
      (concreteBPNativeSelectCloseGlobalWordTraceResult shape left).trace ++
        (concreteBPNativeSelectCloseGlobalWordTraceResult shape
          (right - 1)).trace ∧
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).value = none := by
  constructor <;>
    simp [concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult,
      concreteBPNativeSuccinctRMQWholeQueryProgram,
      WholeQueryProgram.evalGlobalWordTrace,
      WholeQueryInstr.evalGlobalWordTrace,
      WordRAM.TraceResult.map, WordRAM.TraceResult.bind,
      WordRAM.TraceResult.pure, WholeQueryNatExpr.eval,
      WholeQueryState.empty, WholeQueryState.opt, WholeQueryState.setOpt,
      hleft]

/--
Whole-query decomposition, right-select miss: symmetric to the left-select
miss (the left select may hit; the close/LCA instruction still writes
`none` without running its leaf).
-/
theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_decompose_of_right_select_none
    (shape : Cartesian.CartesianShape) (left right : Nat)
    (hright :
      (concreteBPNativeSelectCloseGlobalWordTraceResult shape
          (right - 1)).value = none) :
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).trace =
      (concreteBPNativeSelectCloseGlobalWordTraceResult shape left).trace ++
        (concreteBPNativeSelectCloseGlobalWordTraceResult shape
          (right - 1)).trace ∧
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).value = none := by
  cases hleft :
      (concreteBPNativeSelectCloseGlobalWordTraceResult shape left).value with
  | none =>
      exact
        concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_decompose_of_left_select_none
          shape left right hleft
  | some leftClose =>
      constructor <;>
        simp [concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult,
          concreteBPNativeSuccinctRMQWholeQueryProgram,
          WholeQueryProgram.evalGlobalWordTrace,
          WholeQueryInstr.evalGlobalWordTrace,
          WordRAM.TraceResult.map, WordRAM.TraceResult.bind,
          WordRAM.TraceResult.pure, WholeQueryNatExpr.eval,
          WholeQueryState.empty, WholeQueryState.opt, WholeQueryState.setOpt,
          hleft, hright]

/-! ## The route's own control classification, and the UNCONDITIONAL
decomposition

The four branch decompositions above are exhaustive, but each is stated
under its own hypotheses, so every consumer has to redo the same case
analysis before it can use one.  This section performs the split ONCE and
yields a single statement with no branch hypothesis at all.

The classification is read off the control program itself
(`concreteBPNativeSuccinctRMQWholeQueryProgram`, five instructions): the two
`selectClose` instructions run unconditionally, `lcaClose` scrutinises the
two select results, and `rankCloseIfSome` / `outputPredIfSome` scrutinise the
LCA result.  So the control flow is determined by exactly THREE `Option`
scrutinees.  The rank leg's own result is a `Nat`, written with `setNat` and
read back by `outputPredIfSome` without being tested, so it is NOT a fourth
determinant - nothing branches on it.

Everything downstream that must follow the route's case split - in
particular the whole-query category function - is defined by matching on
`WholeQueryBranch`, so "the same case split" is true by construction rather
than by convention.
-/

/--
Which legs the whole-query control program actually runs, as determined by
the three `Option` scrutinees its five instructions branch on.

The two `none` constructors are kept apart even though they induce the same
trace: they record WHICH determinant fired, which is exactly the information
a category-level discriminator needs.
-/
inductive WholeQueryBranch where
  /-- The left select missed; the right select still runs, the LCA
  instruction writes `none` without running its leaf. -/
  | leftSelectNone
  /-- The left select hit but the right select missed. -/
  | rightSelectNone (leftClose : Nat)
  /-- Both selects hit; the close/LCA leg ran and answered `none`, so the
  rank leg never runs. -/
  | lcaNone (leftClose rightClose : Nat)
  /-- Both selects hit and the close/LCA leg answered; all four legs run. -/
  | full (leftClose rightClose answerClose : Nat)
deriving Repr, DecidableEq

/-- The route's control classification for one query, computed from the
component legs' own values. -/
def wholeQueryBranch (shape : Cartesian.CartesianShape) (left right : Nat) :
    WholeQueryBranch :=
  match (concreteBPNativeSelectCloseGlobalWordTraceResult shape left).value with
  | none => .leftSelectNone
  | some leftClose =>
    match
        (concreteBPNativeSelectCloseGlobalWordTraceResult shape
          (right - 1)).value with
    | none => .rightSelectNone leftClose
    | some rightClose =>
      match
          (concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
            shape leftClose rightClose).value with
      | none => .lcaNone leftClose rightClose
      | some answerClose => .full leftClose rightClose answerClose

/-! ### Forward classification lemmas -/

theorem wholeQueryBranch_eq_leftSelectNone
    (shape : Cartesian.CartesianShape) (left right : Nat)
    (hleft :
      (concreteBPNativeSelectCloseGlobalWordTraceResult shape left).value =
        none) :
    wholeQueryBranch shape left right = .leftSelectNone := by
  simp [wholeQueryBranch, hleft]

theorem wholeQueryBranch_eq_rightSelectNone
    (shape : Cartesian.CartesianShape) (left right : Nat) {leftClose : Nat}
    (hleft :
      (concreteBPNativeSelectCloseGlobalWordTraceResult shape left).value =
        some leftClose)
    (hright :
      (concreteBPNativeSelectCloseGlobalWordTraceResult shape
          (right - 1)).value = none) :
    wholeQueryBranch shape left right = .rightSelectNone leftClose := by
  simp [wholeQueryBranch, hleft, hright]

theorem wholeQueryBranch_eq_lcaNone
    (shape : Cartesian.CartesianShape) (left right : Nat)
    {leftClose rightClose : Nat}
    (hleft :
      (concreteBPNativeSelectCloseGlobalWordTraceResult shape left).value =
        some leftClose)
    (hright :
      (concreteBPNativeSelectCloseGlobalWordTraceResult shape
          (right - 1)).value = some rightClose)
    (hlca :
      (concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
          shape leftClose rightClose).value = none) :
    wholeQueryBranch shape left right = .lcaNone leftClose rightClose := by
  simp [wholeQueryBranch, hleft, hright, hlca]

theorem wholeQueryBranch_eq_full
    (shape : Cartesian.CartesianShape) (left right : Nat)
    {leftClose rightClose answerClose : Nat}
    (hleft :
      (concreteBPNativeSelectCloseGlobalWordTraceResult shape left).value =
        some leftClose)
    (hright :
      (concreteBPNativeSelectCloseGlobalWordTraceResult shape
          (right - 1)).value = some rightClose)
    (hlca :
      (concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
          shape leftClose rightClose).value = some answerClose) :
    wholeQueryBranch shape left right = .full leftClose rightClose answerClose := by
  simp [wholeQueryBranch, hleft, hright, hlca]

/-! ### Route receipt and value as functions of the branch

Both take the branch as an ARGUMENT rather than recomputing it, so the match
iota-reduces the moment a classification lemma has fixed the constructor.
-/

/-- The route's whole-query receipt, positionally, on a given branch. -/
def wholeQueryBranchTrace (shape : Cartesian.CartesianShape)
    (left right : Nat) : WholeQueryBranch → List WordRAM.TraceEvent
  | .leftSelectNone =>
      (concreteBPNativeSelectCloseGlobalWordTraceResult shape left).trace ++
        (concreteBPNativeSelectCloseGlobalWordTraceResult shape
          (right - 1)).trace
  | .rightSelectNone _ =>
      (concreteBPNativeSelectCloseGlobalWordTraceResult shape left).trace ++
        (concreteBPNativeSelectCloseGlobalWordTraceResult shape
          (right - 1)).trace
  | .lcaNone leftClose rightClose =>
      (concreteBPNativeSelectCloseGlobalWordTraceResult shape left).trace ++
        (concreteBPNativeSelectCloseGlobalWordTraceResult shape
          (right - 1)).trace ++
        (concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
          shape leftClose rightClose).trace
  | .full leftClose rightClose answerClose =>
      (concreteBPNativeSelectCloseGlobalWordTraceResult shape left).trace ++
        (concreteBPNativeSelectCloseGlobalWordTraceResult shape
          (right - 1)).trace ++
        (concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
          shape leftClose rightClose).trace ++
        (concreteBPNativeRankCloseWordTraceResultAtSegment shape
          concreteBPNativeRankCloseTraceSegmentBase (answerClose + 1)).trace

/-- The route's whole-query value on a given branch: `none` on all three
short branches, the rank answer's predecessor on the full path.

Note the absent `left`/`right` parameters.  Unlike the receipt - which
names the two select legs at `left` and `right - 1` explicitly - the value
depends on the query endpoints ONLY through the branch classification.  An
earlier draft carried `left right` here and never used them; they are
dropped rather than left decorative. -/
def wholeQueryBranchValue (shape : Cartesian.CartesianShape) :
    WholeQueryBranch → Option Nat
  | .leftSelectNone => none
  | .rightSelectNone _ => none
  | .lcaNone _ _ => none
  | .full _ _ answerClose =>
      some
        ((concreteBPNativeRankCloseWordTraceResultAtSegment shape
            concreteBPNativeRankCloseTraceSegmentBase
            (answerClose + 1)).value - 1)

/-- The route's whole-query receipt, at the branch the route itself takes. -/
def wholeQueryRouteTrace (shape : Cartesian.CartesianShape)
    (left right : Nat) : List WordRAM.TraceEvent :=
  wholeQueryBranchTrace shape left right (wholeQueryBranch shape left right)

/-- The route's whole-query value, at the branch the route itself takes. -/
def wholeQueryRouteValue (shape : Cartesian.CartesianShape)
    (left right : Nat) : Option Nat :=
  wholeQueryBranchValue shape (wholeQueryBranch shape left right)

/--
THE THREE-WAY SPLIT, PERFORMED ONCE.

Unconditionally - with no branch hypothesis whatsoever - the whole-query
global trace is positionally `wholeQueryRouteTrace` and the whole-query value
is `wholeQueryRouteValue`.  Consumers case-split on `wholeQueryBranch` (or
not at all) instead of re-deriving the four decompositions above.

This is exactly as strong as the four decompositions together: each of them
is recovered by composing this statement with the corresponding
classification lemma, which is what the four corollaries below do.
-/
theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_decompose
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).trace =
      wholeQueryRouteTrace shape left right ∧
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).value =
      wholeQueryRouteValue shape left right := by
  unfold wholeQueryRouteTrace wholeQueryRouteValue
  cases hleft :
      (concreteBPNativeSelectCloseGlobalWordTraceResult shape left).value with
  | none =>
      rw [wholeQueryBranch_eq_leftSelectNone shape left right hleft]
      exact
        concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_decompose_of_left_select_none
          shape left right hleft
  | some leftClose =>
      cases hright :
          (concreteBPNativeSelectCloseGlobalWordTraceResult shape
            (right - 1)).value with
      | none =>
          rw [wholeQueryBranch_eq_rightSelectNone shape left right hleft
            hright]
          exact
            concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_decompose_of_right_select_none
              shape left right hright
      | some rightClose =>
          cases hlca :
              (concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
                shape leftClose rightClose).value with
          | none =>
              rw [wholeQueryBranch_eq_lcaNone shape left right hleft hright
                hlca]
              exact
                concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_decompose_of_lca_none
                  shape left right hleft hright hlca
          | some answerClose =>
              rw [wholeQueryBranch_eq_full shape left right hleft hright hlca]
              exact
                concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_decompose_of_selects_lca_some
                  shape left right hleft hright hlca

/-- Receipt half of the unconditional decomposition. -/
theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_trace_eq
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).trace =
      wholeQueryRouteTrace shape left right :=
  (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_decompose
    shape left right).1

/-- Value half of the unconditional decomposition. -/
theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_value_eq
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).value =
      wholeQueryRouteValue shape left right :=
  (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_decompose
    shape left right).2

/-! ### The route value is `none` on exactly the three short branches

Stated as an iff so that it is usable in both directions: the glue needs
"the branch is short, therefore the value is `none`" when discharging the
`none` arms, and "the value is `none`, therefore the branch is short" when
ruling out a machine that produced `none` off the full path.
-/

/-- The whole-query value is `none` precisely when the route did NOT reach
the rank leg. -/
theorem wholeQueryRouteValue_eq_none_iff
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    wholeQueryRouteValue shape left right = none ↔
      ∀ leftClose rightClose answerClose,
        wholeQueryBranch shape left right ≠
          .full leftClose rightClose answerClose := by
  unfold wholeQueryRouteValue
  cases hb : wholeQueryBranch shape left right with
  | leftSelectNone => simp [wholeQueryBranchValue]
  | rightSelectNone lc => simp [wholeQueryBranchValue]
  | lcaNone lc rc => simp [wholeQueryBranchValue]
  | full lc rc ac => simp [wholeQueryBranchValue]

end SuccinctFinal
end RMQ
