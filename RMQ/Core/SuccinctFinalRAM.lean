import RMQ.Core.SuccinctFinal
import RMQ.Core.GenericSelect.RAM
import RMQ.Core.SuccinctClose.RelativeRmmMacro.ConcreteDirectoryRAM

/-!
# Word-RAM bridge for the final BP-native succinct RMQ query

This module is an additive refinement layer over `SuccinctFinal`.  The existing
final capstone remains the reference theorem; the definitions below replay the
same final query shape with interpreted close-select, rank-seed, and answer-rank
leaves, then prove that the interpreted query refines the existing `Costed`
query.
-/

namespace RMQ
namespace SuccinctFinal

/-- Interpreted close-select leg for the built generic sparse-exception source. -/
def concreteBPNativeSelectCloseInterpretedCosted
    (shape : Cartesian.CartesianShape)
    (idx : Nat) : Costed (Option Nat) :=
  (GenericSelect.sparseExceptionSelectData shape.bpCode false)
    |>.selectInterpretedCosted idx

/-- Interpreted false-rank leg for the built BP-close rank component. -/
def concreteBPNativeRankCloseInterpretedCosted
    (shape : Cartesian.CartesianShape)
    (pos : Nat) : Costed Nat :=
  (builtRelativeSplitBPCloseRankData shape)
    |>.rankRegisterInterpretedCosted false pos

/--
Interpreted compact LCA-close leg.

The compact close directory is unchanged; the rank seed callback it consumes is
now the interpreted false-rank query above.
-/
def concreteBPNativeLCACloseInterpretedCosted
    (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) : Costed (Option Nat) :=
  (concreteBPNativeCloseDirectory shape).lcaCloseCostedWithRankSeed
    (concreteBPNativeRankCloseInterpretedCosted shape)
    leftClose rightClose

/--
Final BP-native RMQ query with interpreted close-select, compact close/LCA, and
answer-rank leaves.
-/
def concreteBPNativeSuccinctRMQQueryInterpretedCosted
    (shape : Cartesian.CartesianShape)
    (left right : Nat) : Costed (Option Nat) :=
  Costed.bind (concreteBPNativeSelectCloseInterpretedCosted shape left)
    fun leftClose? =>
      Costed.bind
        (concreteBPNativeSelectCloseInterpretedCosted shape (right - 1))
        fun rightClose? =>
          match leftClose?, rightClose? with
          | some leftClose, some rightClose =>
              Costed.bind
                (concreteBPNativeLCACloseInterpretedCosted shape
                  leftClose rightClose)
                fun answerClose? =>
                  match answerClose? with
                  | some answerClose =>
                      Costed.map (fun closeRank => some (closeRank - 1))
                        (concreteBPNativeRankCloseInterpretedCosted
                          shape (answerClose + 1))
                  | none => Costed.pure none
          | _, _ => Costed.pure none

/-- Optional-natural registers used by the final whole-query control program. -/
inductive WholeQueryOptReg where
  | leftClose
  | rightClose
  | answerClose
  | output
deriving Repr, DecidableEq

/-- Natural registers used by the final whole-query control program. -/
inductive WholeQueryNatReg where
  | closeRank
deriving Repr, DecidableEq

/-- Concrete register state for the final BP-native RMQ query program. -/
structure WholeQueryState where
  leftClose? : Option Nat := none
  rightClose? : Option Nat := none
  answerClose? : Option Nat := none
  closeRank : Nat := 0
  output? : Option Nat := none
deriving Repr

namespace WholeQueryState

/-- Empty initial register state. -/
def empty : WholeQueryState where

/-- Read an optional-natural register. -/
def opt (state : WholeQueryState) : WholeQueryOptReg -> Option Nat
  | .leftClose => state.leftClose?
  | .rightClose => state.rightClose?
  | .answerClose => state.answerClose?
  | .output => state.output?

/-- Read a natural register. -/
def nat (state : WholeQueryState) : WholeQueryNatReg -> Nat
  | .closeRank => state.closeRank

/-- Write an optional-natural register. -/
def setOpt (state : WholeQueryState) (reg : WholeQueryOptReg)
    (value : Option Nat) : WholeQueryState :=
  match reg with
  | .leftClose => { state with leftClose? := value }
  | .rightClose => { state with rightClose? := value }
  | .answerClose => { state with answerClose? := value }
  | .output => { state with output? := value }

/-- Write a natural register. -/
def setNat (state : WholeQueryState) (reg : WholeQueryNatReg)
    (value : Nat) : WholeQueryState :=
  match reg with
  | .closeRank => { state with closeRank := value }

end WholeQueryState

/--
First-order natural expressions for the final query-control program.

These expressions may inspect the two public query inputs and the program's own
registers. They do not contain Lean callbacks.
-/
inductive WholeQueryNatExpr where
  | const (value : Nat)
  | inputLeft
  | inputRight
  | optNatD (reg : WholeQueryOptReg) (fallback : Nat)
  | natReg (reg : WholeQueryNatReg)
  | add (left right : WholeQueryNatExpr)
  | sub (left right : WholeQueryNatExpr)
deriving Repr, DecidableEq

namespace WholeQueryNatExpr

/-- Evaluate a first-order query expression. -/
def eval (left right : Nat) (state : WholeQueryState) :
    WholeQueryNatExpr -> Nat
  | .const value => value
  | .inputLeft => left
  | .inputRight => right
  | .optNatD reg fallback => (state.opt reg).getD fallback
  | .natReg reg => state.nat reg
  | .add a b => a.eval left right state + b.eval left right state
  | .sub a b => a.eval left right state - b.eval left right state

end WholeQueryNatExpr

/--
Closed instruction set for the final BP-native RMQ query.

This is first-order control over already-interpreted component leaves: it has
fixed instruction constructors, register operands, and arithmetic expressions,
not higher-order continuations or arbitrary callbacks.
-/
inductive WholeQueryInstr where
  | selectClose (dst : WholeQueryOptReg) (idx : WholeQueryNatExpr)
  | lcaClose (dst leftReg rightReg : WholeQueryOptReg)
  | rankCloseIfSome
      (dst : WholeQueryNatReg) (guard : WholeQueryOptReg)
      (pos : WholeQueryNatExpr)
  | outputPredIfSome
      (dst guard : WholeQueryOptReg) (src : WholeQueryNatReg)
deriving Repr

namespace WholeQueryInstr

/-- Execute one whole-query instruction. -/
def eval (shape : Cartesian.CartesianShape) (left right : Nat)
    (instr : WholeQueryInstr) (state : WholeQueryState) :
    Costed WholeQueryState :=
  match instr with
  | .selectClose dst idx =>
      Costed.map
        (fun close? => state.setOpt dst close?)
        (concreteBPNativeSelectCloseInterpretedCosted shape
          (idx.eval left right state))
  | .lcaClose dst leftReg rightReg =>
      match state.opt leftReg, state.opt rightReg with
      | some leftClose, some rightClose =>
          Costed.map
            (fun answer? => state.setOpt dst answer?)
            (concreteBPNativeLCACloseInterpretedCosted shape
              leftClose rightClose)
      | _, _ => Costed.pure (state.setOpt dst none)
  | .rankCloseIfSome dst guard pos =>
      match state.opt guard with
      | some _ =>
          Costed.map
            (fun closeRank => state.setNat dst closeRank)
            (concreteBPNativeRankCloseInterpretedCosted shape
              (pos.eval left right state))
      | none => Costed.pure state
  | .outputPredIfSome dst guard src =>
      match state.opt guard with
      | some _ => Costed.pure (state.setOpt dst (some (state.nat src - 1)))
      | none => Costed.pure (state.setOpt dst none)

end WholeQueryInstr

/-- First-order whole-query control programs for the final RMQ path. -/
abbrev WholeQueryProgram := List WholeQueryInstr

namespace WholeQueryProgram

/-- Execute a whole-query control program. -/
def eval (shape : Cartesian.CartesianShape) (left right : Nat) :
    WholeQueryProgram -> WholeQueryState -> Costed WholeQueryState
  | [], state => Costed.pure state
  | instr :: rest, state =>
      Costed.bind (instr.eval shape left right state) fun state' =>
        eval shape left right rest state'

end WholeQueryProgram

/-- The closed whole-query control program for the final BP-native RMQ query. -/
def concreteBPNativeSuccinctRMQWholeQueryProgram : WholeQueryProgram :=
  [ WholeQueryInstr.selectClose .leftClose .inputLeft
  , WholeQueryInstr.selectClose .rightClose
      (.sub .inputRight (.const 1))
  , WholeQueryInstr.lcaClose .answerClose .leftClose .rightClose
  , WholeQueryInstr.rankCloseIfSome .closeRank .answerClose
      (.add (.optNatD .answerClose 0) (.const 1))
  , WholeQueryInstr.outputPredIfSome .output .answerClose .closeRank
  ]

/--
Final BP-native RMQ query as one closed whole-query control program.

The component leaves remain the existing interpreted select-close, compact
close/LCA, and two-level register-backed rank leaves; the surrounding query
control is now a first-order instruction list rather than open Lean-side
continuations.
-/
def concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted
    (shape : Cartesian.CartesianShape)
    (left right : Nat) : Costed (Option Nat) :=
  Costed.map WholeQueryState.output?
    (WholeQueryProgram.eval shape left right
      concreteBPNativeSuccinctRMQWholeQueryProgram
      WholeQueryState.empty)

theorem concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted_refines_queryInterpretedCosted
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted shape left right =
      concreteBPNativeSuccinctRMQQueryInterpretedCosted shape left right := by
  unfold concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted
    concreteBPNativeSuccinctRMQWholeQueryProgram
    WholeQueryProgram.eval WholeQueryInstr.eval
    concreteBPNativeSuccinctRMQQueryInterpretedCosted
  apply Costed.ext
  · cases hleft :
        (concreteBPNativeSelectCloseInterpretedCosted shape left).value with
    | none =>
        simp [hleft, WholeQueryProgram.eval, WholeQueryInstr.eval,
          WholeQueryNatExpr.eval, WholeQueryState.empty,
          WholeQueryState.opt, WholeQueryState.setOpt, Costed.bind,
          Costed.map, Costed.pure]
    | some leftClose =>
        cases hright :
            (concreteBPNativeSelectCloseInterpretedCosted
              shape (right - 1)).value with
        | none =>
            simp [hleft, hright, WholeQueryProgram.eval,
              WholeQueryInstr.eval, WholeQueryNatExpr.eval,
              WholeQueryState.empty, WholeQueryState.opt,
              WholeQueryState.setOpt, Costed.bind, Costed.map, Costed.pure]
        | some rightClose =>
            cases hanswer :
                (concreteBPNativeLCACloseInterpretedCosted
                  shape leftClose rightClose).value with
            | none =>
                simp [hleft, hright, hanswer, WholeQueryProgram.eval,
                  WholeQueryInstr.eval, WholeQueryNatExpr.eval,
                  WholeQueryState.empty, WholeQueryState.opt,
                  WholeQueryState.setOpt, Costed.bind, Costed.map,
                  Costed.pure]
            | some answerClose =>
                simp [hleft, hright, hanswer, WholeQueryProgram.eval,
                  WholeQueryInstr.eval, WholeQueryNatExpr.eval,
                  WholeQueryState.empty, WholeQueryState.opt,
                  WholeQueryState.nat, WholeQueryState.setOpt,
                  WholeQueryState.setNat, Costed.bind, Costed.map,
                  Costed.pure]
  · cases hleft :
        (concreteBPNativeSelectCloseInterpretedCosted shape left).value with
    | none =>
        simp [hleft, WholeQueryProgram.eval, WholeQueryInstr.eval,
          WholeQueryNatExpr.eval, WholeQueryState.empty,
          WholeQueryState.opt, WholeQueryState.setOpt, Costed.bind,
          Costed.map, Costed.pure]
    | some leftClose =>
        cases hright :
            (concreteBPNativeSelectCloseInterpretedCosted
              shape (right - 1)).value with
        | none =>
            simp [hleft, hright, WholeQueryProgram.eval,
              WholeQueryInstr.eval, WholeQueryNatExpr.eval,
              WholeQueryState.empty, WholeQueryState.opt,
              WholeQueryState.setOpt, Costed.bind, Costed.map, Costed.pure]
        | some rightClose =>
            cases hanswer :
                (concreteBPNativeLCACloseInterpretedCosted
                  shape leftClose rightClose).value with
            | none =>
                simp [hleft, hright, hanswer, WholeQueryProgram.eval,
                  WholeQueryInstr.eval, WholeQueryNatExpr.eval,
                  WholeQueryState.empty, WholeQueryState.opt,
                  WholeQueryState.setOpt, Costed.bind, Costed.map,
                  Costed.pure]
            | some answerClose =>
                simp [hleft, hright, hanswer, WholeQueryProgram.eval,
                  WholeQueryInstr.eval, WholeQueryNatExpr.eval,
                  WholeQueryState.empty, WholeQueryState.opt,
                  WholeQueryState.nat, WholeQueryState.setOpt,
                  WholeQueryState.setNat, Costed.bind, Costed.map,
                  Costed.pure]

theorem concreteBPNativeSelectCloseInterpretedCosted_refines_selectCloseCosted
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    concreteBPNativeSelectCloseInterpretedCosted shape idx =
      concreteBPNativeSelectCloseCosted
        builtGenericSparseExceptionSelectBPCloseAccessFamily shape idx := by
  unfold concreteBPNativeSelectCloseInterpretedCosted
    concreteBPNativeSelectCloseCosted
    builtGenericSparseExceptionSelectBPCloseAccessFamily
    builtGenericSparseExceptionSelectBPCloseAccessDirectory
  simpa [GenericSelect.sparseExceptionSelectSource,
    GenericSelect.SparseExceptionSelectData.toChargedSelectPositionSource]
    using
      (GenericSelect.SparseExceptionSelectData.selectInterpretedCosted_refines_selectCosted
        (GenericSelect.sparseExceptionSelectData shape.bpCode false) idx)

theorem concreteBPNativeRankCloseInterpretedCosted_refines_rankCloseCosted
    (shape : Cartesian.CartesianShape) (pos : Nat) :
    concreteBPNativeRankCloseInterpretedCosted shape pos =
      concreteBPNativeRankCloseCosted
        builtGenericSparseExceptionSelectBPCloseAccessFamily shape pos := by
  unfold concreteBPNativeRankCloseInterpretedCosted
    concreteBPNativeRankCloseCosted
    builtGenericSparseExceptionSelectBPCloseAccessFamily
    builtGenericSparseExceptionSelectBPCloseAccessDirectory
  rw [
    (builtRelativeSplitBPCloseRankData shape)
      |>.rankRegisterInterpretedCosted_refines_rankInterpretedCosted false pos]
  exact
    (builtRelativeSplitBPCloseRankData shape)
      |>.rankInterpretedCosted_refines_rankCosted false pos

theorem concreteBPNativeLCACloseInterpretedCosted_refines_lcaCloseCosted
    (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) :
    concreteBPNativeLCACloseInterpretedCosted shape leftClose rightClose =
      concreteBPNativeLCACloseCosted
        builtGenericSparseExceptionSelectBPCloseAccessFamily
        shape leftClose rightClose := by
  unfold concreteBPNativeLCACloseInterpretedCosted
    concreteBPNativeLCACloseCosted
  have hfun :
      concreteBPNativeRankCloseInterpretedCosted shape =
        concreteBPNativeRankCloseCosted
          builtGenericSparseExceptionSelectBPCloseAccessFamily shape := by
    funext pos
    exact concreteBPNativeRankCloseInterpretedCosted_refines_rankCloseCosted
      shape pos
  simp [hfun]

theorem concreteBPNativeSuccinctRMQQueryInterpretedCosted_refines_queryCosted
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    concreteBPNativeSuccinctRMQQueryInterpretedCosted shape left right =
      concreteBPNativeSuccinctRMQQueryCosted
        builtGenericSparseExceptionSelectBPCloseAccessFamily
        shape left right := by
  unfold concreteBPNativeSuccinctRMQQueryInterpretedCosted
    concreteBPNativeSuccinctRMQQueryCosted
  simp only [
    concreteBPNativeSelectCloseInterpretedCosted_refines_selectCloseCosted,
    concreteBPNativeLCACloseInterpretedCosted_refines_lcaCloseCosted,
    concreteBPNativeRankCloseInterpretedCosted_refines_rankCloseCosted]
  rfl

theorem concreteBPNativeSuccinctRMQQueryInterpretedCosted_cost_le
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    (concreteBPNativeSuccinctRMQQueryInterpretedCosted
      shape left right).cost <=
        concreteBPNativeSuccinctRMQQueryCost
          SuccinctSelect.sparseDenseFalseSelectQueryCost := by
  rw [concreteBPNativeSuccinctRMQQueryInterpretedCosted_refines_queryCosted]
  exact
    concreteBPNativeSuccinctRMQQueryCosted_cost_le
      builtGenericSparseExceptionSelectBPCloseAccessFamily shape left right

theorem concreteBPNativeSuccinctRMQQueryInterpretedCosted_exact
    {n : Nat} {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    {left len : Nat} (hlen : 0 < len) (hbound : left + len <= n) :
    (concreteBPNativeSuccinctRMQQueryInterpretedCosted
      shape left (left + len)).erase =
        some (scanWindow shape.representative left len) := by
  rw [concreteBPNativeSuccinctRMQQueryInterpretedCosted_refines_queryCosted]
  exact
    concreteBPNativeSuccinctRMQQueryCosted_exact
      builtGenericSparseExceptionSelectBPCloseAccessFamily
      hshape hlen hbound

theorem concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted_cost_le
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    (concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted
      shape left right).cost <=
        concreteBPNativeSuccinctRMQQueryCost
          SuccinctSelect.sparseDenseFalseSelectQueryCost := by
  rw [
    concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted_refines_queryInterpretedCosted]
  exact
    concreteBPNativeSuccinctRMQQueryInterpretedCosted_cost_le
      shape left right

theorem concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted_exact
    {n : Nat} {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    {left len : Nat} (hlen : 0 < len) (hbound : left + len <= n) :
    (concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted
      shape left (left + len)).erase =
        some (scanWindow shape.representative left len) := by
  rw [
    concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted_refines_queryInterpretedCosted]
  exact
    concreteBPNativeSuccinctRMQQueryInterpretedCosted_exact
      hshape hlen hbound

/--
Interpreter-backed two-sided public capstone for the built generic-select
BP-native succinct RMQ path.

This theorem has the same lower-bound, payload, cost, and exactness shape as the
current public generic sparse-exception capstone, but its query clause is the
interpreted query defined in this module.
-/
theorem builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_interpreted_profile :
    SuccinctSpace.LittleOLinear
        (concreteBPNativeSuccinctRMQOverhead
          genericSparseExceptionBPCloseAccessOverhead) /\
      forall n : Nat,
        EncodingLowerBound.doubledLogSlackLower n <=
          2 *
            (2 * n +
              concreteBPNativeSuccinctRMQOverhead
                genericSparseExceptionBPCloseAccessOverhead n) /\
        EncodingLowerBound.logSlackLower n <=
          2 * n +
            concreteBPNativeSuccinctRMQOverhead
              genericSparseExceptionBPCloseAccessOverhead n /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            (builtGenericSparseExceptionSelectBPCloseAccessFamily
              |>.directory shape).payload.length <=
              genericSparseExceptionBPCloseAccessOverhead n) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            (concreteBPNativeSuccinctRMQPayload
              builtGenericSparseExceptionSelectBPCloseAccessFamily
              shape).length =
              2 * n +
                concreteBPNativeSuccinctRMQOverhead
                  genericSparseExceptionBPCloseAccessOverhead n) /\
        (forall shape left right,
          (concreteBPNativeSuccinctRMQQueryInterpretedCosted
            shape left right).cost <=
              concreteBPNativeSuccinctRMQQueryCost
                SuccinctSelect.sparseDenseFalseSelectQueryCost) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            forall {left len : Nat},
              0 < len ->
                left + len <= n ->
                  (concreteBPNativeSuccinctRMQQueryInterpretedCosted
                    shape left (left + len)).erase =
                    some (scanWindow shape.representative left len)) := by
  have h :=
    builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_profile
  dsimp only at h
  constructor
  · exact h.1
  · intro n
    rcases h.2 n with
      ⟨hdoubled, hlog, hpayloadLe, hpayloadLen, hcost, hexact⟩
    exact
      ⟨hdoubled, hlog, hpayloadLe, hpayloadLen,
        (by
          intro shape left right
          exact
            concreteBPNativeSuccinctRMQQueryInterpretedCosted_cost_le
              shape left right),
        (by
          intro shape hshape left len hlen hbound
          exact
            concreteBPNativeSuccinctRMQQueryInterpretedCosted_exact
              hshape hlen hbound)⟩

/--
Whole-query-interpreted two-sided public capstone for the built generic-select
BP-native succinct RMQ path.

This strengthens the interpreted capstone by routing the query-level control
itself through the closed `WholeQueryProgram`; the component leaves are still
the interpreted select-close, compact close/LCA, and register-backed rank
queries.
-/
theorem builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_whole_query_interpreted_profile :
    SuccinctSpace.LittleOLinear
        (concreteBPNativeSuccinctRMQOverhead
          genericSparseExceptionBPCloseAccessOverhead) /\
      forall n : Nat,
        EncodingLowerBound.doubledLogSlackLower n <=
          2 *
            (2 * n +
              concreteBPNativeSuccinctRMQOverhead
                genericSparseExceptionBPCloseAccessOverhead n) /\
        EncodingLowerBound.logSlackLower n <=
          2 * n +
            concreteBPNativeSuccinctRMQOverhead
              genericSparseExceptionBPCloseAccessOverhead n /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            (builtGenericSparseExceptionSelectBPCloseAccessFamily
              |>.directory shape).payload.length <=
              genericSparseExceptionBPCloseAccessOverhead n) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            (concreteBPNativeSuccinctRMQPayload
              builtGenericSparseExceptionSelectBPCloseAccessFamily
              shape).length =
              2 * n +
                concreteBPNativeSuccinctRMQOverhead
                  genericSparseExceptionBPCloseAccessOverhead n) /\
        (forall shape left right,
          (concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted
            shape left right).cost <=
              concreteBPNativeSuccinctRMQQueryCost
                SuccinctSelect.sparseDenseFalseSelectQueryCost) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            forall {left len : Nat},
              0 < len ->
                left + len <= n ->
                  (concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted
                    shape left (left + len)).erase =
                    some (scanWindow shape.representative left len)) := by
  have h :=
    builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_interpreted_profile
  constructor
  · exact h.1
  · intro n
    rcases h.2 n with
      ⟨hdoubled, hlog, hpayloadLe, hpayloadLen, _hcost, _hexact⟩
    exact
      ⟨hdoubled, hlog, hpayloadLe, hpayloadLen,
        (by
          intro shape left right
          exact
            concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted_cost_le
              shape left right),
        (by
          intro shape hshape left len hlen hbound
          exact
            concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted_exact
              hshape hlen hbound)⟩

end SuccinctFinal
end RMQ
