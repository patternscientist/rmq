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

end SuccinctFinal
end RMQ
