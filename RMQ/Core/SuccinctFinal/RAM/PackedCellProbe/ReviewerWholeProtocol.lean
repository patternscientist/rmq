import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReviewerSelectProtocol
import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReviewerLcaProtocol

/-!
# Fixed whole-query request/reply protocol

The four instruction occurrences of the public whole-query program are encoded
as constructors, not as a stored instruction list.  This is the logical side of
the final reviewer controller; its requests are subsequently lowered to the
single reviewer-memory cell array.
-/

namespace RMQ
namespace SuccinctFinal
namespace PackedCellProbe

inductive PackedReviewerWholeState where
  | leftSelect
      (n left right : Nat) (select : PackedReviewerSelectState)
  | rightSelect
      (n left right : Nat) (leftClose : Option Nat)
      (select : PackedReviewerSelectState)
  | lcaClose
      (n left right leftClose rightClose : Nat)
      (lca : PackedReviewerLcaState)
  | finalRank
      (n left right answerClose : Nat) (rank : PackedReviewerRankState)
  | done (value : Option Nat)

/-- The closed logical whole-query controller, before physical lowering. -/
def packedReviewerWholeStart (n left right : Nat) : PackedReviewerWholeState :=
  let invocation : PackedReviewerInvocation :=
    { instruction := .leftSelect, argument := left }
  .leftSelect n left right (packedReviewerSelectStart invocation n left)

def packedReviewerWholeNextRequest :
    PackedReviewerWholeState -> Option PackedReviewerLogicalRequest
  | .leftSelect _ _ _ select => packedReviewerSelectNextRequest select
  | .rightSelect _ _ _ _ select => packedReviewerSelectNextRequest select
  | .lcaClose _ _ _ _ _ lca => packedReviewerLcaNextRequest lca
  | .finalRank _ _ _ _ rank => packedReviewerRankNextRequest rank
  | .done _ => none

def packedReviewerWholeAfterLeftSelect
    (n left right : Nat) (leftClose : Option Nat) :
    PackedReviewerWholeState :=
  let index := right - 1
  let invocation : PackedReviewerInvocation :=
    { instruction := .rightSelect, argument := index }
  .rightSelect n left right leftClose
    (packedReviewerSelectStart invocation n index)

def packedReviewerWholeAfterRightSelect
    (n left right : Nat) (leftClose rightClose : Option Nat) :
    PackedReviewerWholeState :=
  match leftClose, rightClose with
  | some leftValue, some rightValue =>
      .lcaClose n left right leftValue rightValue
        (packedReviewerLcaStart n leftValue rightValue)
  | _, _ => .done none

def packedReviewerWholeAfterLca
    (n left right : Nat) (answerClose : Option Nat) :
    PackedReviewerWholeState :=
  match answerClose with
  | none => .done none
  | some answer =>
      let invocation : PackedReviewerInvocation :=
        { instruction := .finalRank, argument := answer + 1 }
      .finalRank n left right answer
        (.superSample invocation .close n (answer + 1))

def packedReviewerWholeConsumeReply
    (state : PackedReviewerWholeState) (reply : Option (List Bool)) :
    PackedReviewerWholeState :=
  match state with
  | .leftSelect n left right select =>
      let select' := packedReviewerSelectConsumeReply select reply
      match packedReviewerSelectResult select' with
      | some leftClose =>
          packedReviewerWholeAfterLeftSelect n left right leftClose
      | none => .leftSelect n left right select'
  | .rightSelect n left right leftClose select =>
      let select' := packedReviewerSelectConsumeReply select reply
      match packedReviewerSelectResult select' with
      | some rightClose =>
          packedReviewerWholeAfterRightSelect n left right leftClose rightClose
      | none => .rightSelect n left right leftClose select'
  | .lcaClose n left right leftClose rightClose lca =>
      let lca' := packedReviewerLcaConsumeReply lca reply
      match packedReviewerLcaResult lca' with
      | some answerClose =>
          packedReviewerWholeAfterLca n left right answerClose
      | none => .lcaClose n left right leftClose rightClose lca'
  | .finalRank n left right answerClose rank =>
      let rank' := packedReviewerRankConsumeReply rank reply
      match packedReviewerRankResult rank' with
      | some closeRank => .done (some (closeRank - 1))
      | none => .finalRank n left right answerClose rank'
  | .done value => .done value

def packedReviewerWholeResult : PackedReviewerWholeState -> Option (Option Nat)
  | .done value => some value
  | _ => none

/-- The fixed whole protocol has at most 210 logical word reads. -/
def packedReviewerWholeRemaining : PackedReviewerWholeState -> Nat
  | .leftSelect _ _ _ select => packedReviewerSelectRemaining select + 175
  | .rightSelect _ _ _ _ select => packedReviewerSelectRemaining select + 140
  | .lcaClose _ _ _ _ _ lca => packedReviewerLcaRemaining lca + 11
  | .finalRank _ _ _ _ rank => packedReviewerRankRemaining rank
  | .done _ => 0

/-! ## Proof-side supplied-store driver

This driver exists only to state the logical simulation theorem.  The physical
controller does not call it and does not contain a `ReadStore`.
-/

structure PackedReviewerLogicalEvent where
  request : PackedReviewerLogicalRequest
  reply : Option (List Bool)
deriving Repr, DecidableEq

structure PackedReviewerLogicalRun where
  terminal : Option (Option Nat)
  state : PackedReviewerWholeState
  trace : List PackedReviewerLogicalEvent

def packedReviewerDriveLogical
    (store : WordRAM.ReadStore) : Nat -> PackedReviewerWholeState ->
      PackedReviewerLogicalRun
  | 0, state =>
      { terminal := packedReviewerWholeResult state
        state := state
        trace := [] }
  | fuel + 1, state =>
      match packedReviewerWholeResult state with
      | some value => { terminal := some value, state := state, trace := [] }
      | none =>
          match packedReviewerWholeNextRequest state with
          | none => { terminal := none, state := state, trace := [] }
          | some request =>
              let reply := store.readWord? request.segment request.index
              let tail :=
                packedReviewerDriveLogical store fuel
                  (packedReviewerWholeConsumeReply state reply)
              { terminal := tail.terminal
                state := tail.state
                trace := { request := request, reply := reply } :: tail.trace }

theorem packedReviewerDriveLogical_trace_length_le
    (store : WordRAM.ReadStore) (fuel : Nat) (state : PackedReviewerWholeState) :
    (packedReviewerDriveLogical store fuel state).trace.length <= fuel := by
  induction fuel generalizing state with
  | zero => simp [packedReviewerDriveLogical]
  | succ fuel ih =>
      unfold packedReviewerDriveLogical
      split
      case h_1 => simp
      case h_2 =>
        split
        case h_1 => simp
        case h_2 request heq =>
          simp only [List.length_cons]
          have htail :=
            ih (packedReviewerWholeConsumeReply state
              (store.readWord? request.segment request.index))
          omega

theorem packedReviewerDriveLogical_read_backed
    (store : WordRAM.ReadStore) (fuel : Nat) (state : PackedReviewerWholeState) :
    forall event,
      event ∈ (packedReviewerDriveLogical store fuel state).trace ->
        event.reply =
          store.readWord? event.request.segment event.request.index := by
  induction fuel generalizing state with
  | zero => simp [packedReviewerDriveLogical]
  | succ fuel ih =>
      unfold packedReviewerDriveLogical
      split
      case h_1 => simp
      case h_2 =>
        split
        case h_1 => simp
        case h_2 request heq =>
          intro event hmem
          simp only [List.mem_cons] at hmem
          rcases hmem with rfl | htail
          · rfl
          · exact
              ih (packedReviewerWholeConsumeReply state
                (store.readWord? request.segment request.index)) event htail

end PackedCellProbe
end SuccinctFinal
end RMQ
