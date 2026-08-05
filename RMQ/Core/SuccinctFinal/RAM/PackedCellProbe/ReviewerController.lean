import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReviewerSparsePrelude
import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReviewerLogicalLowering
import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReviewerWholeProtocol

/-!
# The all-size reviewer-memory request/reply controller

The public controller has three executable phases.  It first requests header
cell zero, then performs the fixed K1 sparse-count prelude, and finally lowers
the fixed logical whole-query protocol one request at a time.  Its state is
proof-free and contains no shape, semantic store, program list, source list,
answer oracle, or memory.  Only the external driver receives a cell array.
-/

namespace RMQ
namespace SuccinctFinal
namespace PackedCellProbe

/-! ## Requests and proof-free state -/

/-- Provenance of an attempted physical cell request. -/
inductive PackedReviewerPhysicalOrigin where
  | header
  | sparsePrelude (request : PackedReviewerSparsePreludeRequest)
  | wholeQuery (request : PackedReviewerLogicalRequest)
deriving Repr, DecidableEq

/--
One first-order physical request.  `ordinal` is the position inside the
current logical read; `cellCount` records whether that read crosses a cell
boundary without replacing the ordered per-cell events.
-/
structure PackedReviewerPhysicalRequest where
  origin : PackedReviewerPhysicalOrigin
  address : Nat
  ordinal : Nat
  cellCount : Nat
deriving Repr, DecidableEq

/--
The controller state.  Naturals beyond the public inputs and decoded counts are
only fixed-protocol control counters; lists are only replies already supplied.
The logical-step counter is operational: normalization consumes it one request
at a time, so it is not a stored claim about the eventual physical trace.
-/
inductive PackedReviewerControllerState where
  | header (n left right : Nat)
  | preludeReady (n left right longCount : Nat)
      (state : PackedReviewerSparsePreludeState)
  | preludeProbe (n left right longCount : Nat)
      (state : PackedReviewerSparsePreludeState)
      (nextOrdinal : Nat) (repliesRev : List (List Bool))
  | wholeReady (n left right longCount sparseCount logicalStepsLeft : Nat)
      (state : PackedReviewerWholeState)
  | wholeProbe (n left right longCount sparseCount logicalStepsAfterReply : Nat)
      (state : PackedReviewerWholeState)
      (nextOrdinal : Nat) (repliesRev : List (List Bool))
  | done (value : Option Nat)
  | failed

/-- The stable public controller entry point. -/
def packedReviewerController (n left right : Nat) :
    PackedReviewerControllerState :=
  if left < right ∧ right <= n then
    .header n left right
  else
    .done none

def packedReviewerSparsePreludeRemaining :
    PackedReviewerSparsePreludeState -> Nat
  | .awaitSuper _ _ => 3
  | .awaitBlock _ _ _ => 2
  | .awaitFlag _ _ _ _ => 1
  | .done _ _ _ => 0

/-- The current prelude plan, guarded by the exact logical word count. -/
def packedReviewerCurrentPreludePlan
    (n longCount : Nat) (state : PackedReviewerSparsePreludeState) : List Nat :=
  match packedReviewerSparsePreludeNextRequest state with
  | none => []
  | some request =>
      if request.index n < packedSourceWordCount n longCount request.source then
        packedReviewerSparsePreludeRequestPlan n longCount request
      else []

/-- Decode a completed prelude plan; `none` is a genuine logical failure. -/
def packedReviewerDecodePreludeReplies
    (n longCount : Nat) (state : PackedReviewerSparsePreludeState)
    (cells : List (List Bool)) : Option (List Bool) :=
  match packedReviewerSparsePreludeNextRequest state with
  | none => none
  | some request =>
      if request.index n < packedSourceWordCount n longCount request.source then
        some (packedReviewerDecodeSpan n
          (packedReviewerSparsePreludeRequestBitAddress n longCount request)
          (packedSourceReadWidth n longCount request.source (request.index n))
          cells)
      else none

/-! ## Pure normalization of zero-cell logical attempts -/

/--
Advance absent logical words without issuing decorative cells, stopping at
the next nonempty physical plan or the terminal whole-query value.
-/
def packedReviewerNormalizeWhole : Nat ->
    (n left right longCount sparseCount : Nat) ->
    PackedReviewerWholeState -> PackedReviewerControllerState
  | 0, _n, _left, _right, _longCount, _sparseCount, state =>
      match packedReviewerWholeResult state with
      | some value => .done value
      | none => .failed
  | fuel + 1, n, left, right, longCount, sparseCount, state =>
      match packedReviewerWholeResult state with
      | some value => .done value
      | none =>
          match packedReviewerWholeNextRequest state with
          | none => .failed
          | some request =>
              let plan :=
                packedReviewerLogicalPlan n longCount sparseCount request
              match plan with
              | [] =>
                  packedReviewerNormalizeWhole fuel n left right longCount
                    sparseCount
                    (packedReviewerWholeConsumeReply state
                      (packedReviewerLogicalDecode n longCount sparseCount
                        request []))
              | _ :: _ =>
                  .wholeProbe n left right longCount sparseCount fuel state 0 []

/--
Advance the K1 prelude until it either needs a real cell, fails, or produces
the sparse count.  Empty plans are decoded as empty reply windows and do not
create physical events.
-/
def packedReviewerNormalizePrelude : Nat ->
    (n left right longCount : Nat) ->
    PackedReviewerSparsePreludeState -> PackedReviewerControllerState
  | 0, n, left, right, longCount, state =>
      match packedReviewerSparsePreludeResult state with
      | some sparseCount =>
          packedReviewerNormalizeWhole
            210
            n left right longCount sparseCount
            (packedReviewerWholeStart n left right)
      | none => .failed
  | fuel + 1, n, left, right, longCount, state =>
      match packedReviewerSparsePreludeResult state with
      | some sparseCount =>
          packedReviewerNormalizeWhole
            210
            n left right longCount sparseCount
            (packedReviewerWholeStart n left right)
      | none =>
          let plan := packedReviewerCurrentPreludePlan n longCount state
          match plan with
          | [] =>
              match packedReviewerDecodePreludeReplies n longCount state [] with
              | none => .failed
              | some reply =>
                  packedReviewerNormalizePrelude fuel n left right longCount
                    (packedReviewerSparsePreludeConsumeReply state reply)
          | _ :: _ =>
              .preludeProbe n left right longCount state 0 []

/-! ## Public request/reply transition -/

/-- The next physical request, if the controller is nonterminal. -/
def packedReviewerNextRequest :
    PackedReviewerControllerState -> Option PackedReviewerPhysicalRequest
  | .header _ _ _ =>
      some { origin := .header, address := 0, ordinal := 0, cellCount := 1 }
  | .preludeProbe n _ _ longCount state next _ =>
      match packedReviewerSparsePreludeNextRequest state with
      | none => none
      | some request =>
          let plan := packedReviewerCurrentPreludePlan n longCount state
          match plan[next]? with
          | none => none
          | some address =>
              some
                { origin := .sparsePrelude request
                  address := address
                  ordinal := next
                  cellCount := plan.length }
  | .wholeProbe n _ _ longCount sparseCount _ state next _ =>
      match packedReviewerWholeNextRequest state with
      | none => none
      | some request =>
          let plan :=
            packedReviewerLogicalPlan n longCount sparseCount request
          match plan[next]? with
          | none => none
          | some address =>
              some
                { origin := .wholeQuery request
                  address := address
                  ordinal := next
                  cellCount := plan.length }
  | _ => none

/-- Terminal result (`none` here means the RMQ result itself is absent). -/
def packedReviewerControllerResult :
    PackedReviewerControllerState -> Option (Option Nat)
  | .done value => some value
  | _ => none

/-- The state records a physical-driver failure. -/
def packedReviewerControllerFailed : PackedReviewerControllerState -> Bool
  | .failed => true
  | _ => false

/-- Consume exactly the reply to `packedReviewerNextRequest`. -/
def packedReviewerConsumeReply
    (state : PackedReviewerControllerState) (reply : Option (List Bool)) :
    PackedReviewerControllerState :=
  match state, reply with
  | _, none => .failed
  | .header n left right, some cell =>
      let longCount := SuccinctSpace.bitsToNatLE cell
      let prelude := packedReviewerSparsePreludeInit n longCount
      packedReviewerNormalizePrelude
        (packedReviewerSparsePreludeRemaining prelude)
        n left right longCount prelude
  | .preludeProbe n left right longCount prelude next repliesRev,
      some cell =>
      let plan := packedReviewerCurrentPreludePlan n longCount prelude
      let repliesRev' := cell :: repliesRev
      if next + 1 < plan.length then
        .preludeProbe n left right longCount prelude (next + 1) repliesRev'
      else
        match packedReviewerDecodePreludeReplies n longCount prelude
            repliesRev'.reverse with
        | none => .failed
        | some logicalReply =>
            let prelude' :=
              packedReviewerSparsePreludeConsumeReply prelude logicalReply
            packedReviewerNormalizePrelude
              (packedReviewerSparsePreludeRemaining prelude')
              n left right longCount prelude'
  | .wholeProbe n left right longCount sparseCount logicalStepsAfterReply
      whole next repliesRev,
      some cell =>
      let repliesRev' := cell :: repliesRev
      match packedReviewerWholeNextRequest whole with
      | none => .failed
      | some request =>
          let plan :=
            packedReviewerLogicalPlan n longCount sparseCount request
          if next + 1 < plan.length then
            .wholeProbe n left right longCount sparseCount
              logicalStepsAfterReply whole (next + 1) repliesRev'
          else
            let logicalReply :=
              packedReviewerLogicalDecode n longCount sparseCount request
                repliesRev'.reverse
            let whole' := packedReviewerWholeConsumeReply whole logicalReply
            packedReviewerNormalizeWhole logicalStepsAfterReply
              n left right longCount sparseCount whole'
  | _, some _ => .failed

/-! ## The actual memory-only run -/

/-- One attempted cell access, including unsuccessful attempts. -/
structure PackedReviewerPhysicalEvent where
  request : PackedReviewerPhysicalRequest
  reply : Option (List Bool)
deriving Repr, DecidableEq

/-- Result, residual state, and ordered attempted physical trace of one run. -/
structure PackedReviewerRun where
  terminal : Option (Option Nat)
  failed : Bool
  state : PackedReviewerControllerState
  trace : List PackedReviewerPhysicalEvent

/--
The structural execution budget supplied to the physical driver.  It bounds the
trace even for arbitrary memory; adequacy to reach a terminal state is proved
separately for the canonical reviewer memory.  The final literal cap is proved
only after the run is defined.
-/
def packedReviewerControllerMeasure : PackedReviewerControllerState -> Nat
  | .header n left right =>
      1 + 2 * packedReviewerSparsePreludeRemaining
          (packedReviewerSparsePreludeInit n 0) +
        2 * packedReviewerWholeRemaining
          (packedReviewerWholeStart n left right)
  | .preludeReady n left right _ state =>
      2 * packedReviewerSparsePreludeRemaining state +
        2 * packedReviewerWholeRemaining
          (packedReviewerWholeStart n left right)
  | .preludeProbe n left right longCount state next _ =>
      2 * (packedReviewerSparsePreludeRemaining state - 1) +
        (packedReviewerCurrentPreludePlan n longCount state).length - next +
        2 * packedReviewerWholeRemaining
          (packedReviewerWholeStart n left right)
  | .wholeReady _ _ _ _ _ logicalStepsLeft _ =>
      2 * logicalStepsLeft
  | .wholeProbe n _ _ longCount sparseCount logicalStepsAfterReply state next _ =>
      match packedReviewerWholeNextRequest state with
      | none => 0
      | some request =>
          2 * logicalStepsAfterReply +
            (packedReviewerLogicalPlan n longCount sparseCount request).length -
              next
  | .done _ => 0
  | .failed => 0

def packedReviewerDriveAgainstMemoryAux
    (memory : List (List Bool)) : Nat -> PackedReviewerControllerState ->
      PackedReviewerRun
  | 0, state =>
      { terminal := packedReviewerControllerResult state
        failed := packedReviewerControllerFailed state
        state := state
        trace := [] }
  | fuel + 1, state =>
      match packedReviewerControllerResult state with
      | some value =>
          { terminal := some value, failed := false, state := state, trace := [] }
      | none =>
          match packedReviewerNextRequest state with
          | none =>
              { terminal := none
                failed := packedReviewerControllerFailed state
                state := state
                trace := [] }
          | some request =>
              let reply := memory[request.address]?
              let tail := packedReviewerDriveAgainstMemoryAux memory fuel
                (packedReviewerConsumeReply state reply)
              { terminal := tail.terminal
                failed := tail.failed
                state := tail.state
                trace := { request := request, reply := reply } :: tail.trace }

/--
The external driver.  Memory appears here and nowhere in the controller state
or transition functions.
-/
def packedReviewerRunAgainstMemory
    (memory : List (List Bool)) (n left right : Nat) : PackedReviewerRun :=
  let controller := packedReviewerController n left right
  packedReviewerDriveAgainstMemoryAux memory
    (packedReviewerControllerMeasure controller) controller

theorem packedReviewerDriveAgainstMemoryAux_trace_length_le
    (memory : List (List Bool)) (fuel : Nat)
    (state : PackedReviewerControllerState) :
    (packedReviewerDriveAgainstMemoryAux memory fuel state).trace.length <= fuel := by
  induction fuel generalizing state with
  | zero => simp [packedReviewerDriveAgainstMemoryAux]
  | succ fuel ih =>
      cases hresult : packedReviewerControllerResult state with
      | some value =>
          simp [packedReviewerDriveAgainstMemoryAux, hresult]
      | none =>
          cases hrequest : packedReviewerNextRequest state with
          | none =>
              simp [packedReviewerDriveAgainstMemoryAux, hresult, hrequest]
          | some request =>
              simp only [packedReviewerDriveAgainstMemoryAux, hresult,
                hrequest, List.length_cons]
              have htail := ih
                (packedReviewerConsumeReply state (memory[request.address]?))
              omega

/-- Every recorded reply is exactly the lookup made in the supplied memory. -/
theorem packedReviewerDriveAgainstMemoryAux_memory_only
    (memory : List (List Bool)) (fuel : Nat)
    (state : PackedReviewerControllerState) :
    forall event,
      event ∈ (packedReviewerDriveAgainstMemoryAux memory fuel state).trace ->
        event.reply = memory[event.request.address]? := by
  induction fuel generalizing state with
  | zero => simp [packedReviewerDriveAgainstMemoryAux]
  | succ fuel ih =>
      cases hresult : packedReviewerControllerResult state with
      | some value =>
          simp [packedReviewerDriveAgainstMemoryAux, hresult]
      | none =>
          cases hrequest : packedReviewerNextRequest state with
          | none =>
              simp [packedReviewerDriveAgainstMemoryAux, hresult, hrequest]
          | some request =>
              simp only [packedReviewerDriveAgainstMemoryAux, hresult,
                hrequest, List.mem_cons]
              intro event hmem
              rcases hmem with rfl | htail
              · rfl
              · exact ih
                  (packedReviewerConsumeReply state (memory[request.address]?))
                  event htail

/-- The structural start measure is bounded by the derived literal `427`. -/
theorem packedReviewerControllerMeasure_start_le_427
    (n left right : Nat) :
    packedReviewerControllerMeasure (packedReviewerController n left right) <=
      427 := by
  by_cases hvalid : left < right ∧ right <= n
  · have hleft : left < n := by omega
    simp [packedReviewerController, hvalid, packedReviewerControllerMeasure,
      packedReviewerSparsePreludeRemaining, packedReviewerSparsePreludeInit,
      packedReviewerWholeRemaining, packedReviewerWholeStart,
      packedReviewerSelectStart, hleft, packedReviewerSelectRemaining,
      packedReviewerEntryRemaining]
  · simp [packedReviewerController, hvalid, packedReviewerControllerMeasure]

/-- Every all-size controller run attempts at most 427 physical cells. -/
theorem packedReviewerRunAgainstMemory_trace_length_le_427
    (memory : List (List Bool)) (n left right : Nat) :
    (packedReviewerRunAgainstMemory memory n left right).trace.length <= 427 := by
  unfold packedReviewerRunAgainstMemory
  exact Nat.le_trans
    (packedReviewerDriveAgainstMemoryAux_trace_length_le memory
      (packedReviewerControllerMeasure (packedReviewerController n left right))
      (packedReviewerController n left right))
    (packedReviewerControllerMeasure_start_le_427 n left right)

/-- The public run has no supplied store or alternate reply source. -/
theorem packedReviewerRunAgainstMemory_memory_only
    (memory : List (List Bool)) (n left right : Nat) :
    forall event,
      event ∈ (packedReviewerRunAgainstMemory memory n left right).trace ->
        event.reply = memory[event.request.address]? := by
  unfold packedReviewerRunAgainstMemory
  exact packedReviewerDriveAgainstMemoryAux_memory_only memory _ _

end PackedCellProbe
end SuccinctFinal
end RMQ
