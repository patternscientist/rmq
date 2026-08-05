import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReviewerWholeProtocol

/-!
# Ordered logical-controller simulation

This module is deliberately proof-side.  It replays each first-order logical
request against a supplied `ReadStore`, erases the retained instruction/site
provenance to the corresponding `WordRAM.readWord` event, and proves that the
fixed logical reviewer protocol is the already accepted `packedWholeQueryRun`.
The executable physical controller does not call any definition in this file.

The load-bearing endpoint is
`packedReviewerDriveLogical_210_simulates_packedWholeQueryRun`: on a valid
half-open query, one run simultaneously has the reference value, the matching
terminal controller state, and the complete ordered reference trace.
-/

namespace RMQ
namespace SuccinctFinal
namespace PackedCellProbe

/-- Erase proof-only request provenance while preserving the exact read. -/
def PackedReviewerLogicalEvent.erase
    (event : PackedReviewerLogicalEvent) : WordRAM.TraceEvent :=
  .readWord event.request.segment event.request.index event.reply

@[simp] theorem PackedReviewerLogicalEvent.erase_mk
    (request : PackedReviewerLogicalRequest) (reply : Option (List Bool)) :
    ({ request := request, reply := reply } : PackedReviewerLogicalEvent).erase =
      .readWord request.segment request.index reply :=
  rfl

/-! ## Proof-only generic component driver -/

/--
Proof-side result of running one fixed reviewer component.  The physical
controller does not contain this supplied-store driver; the public carrier lets
downstream proofs inspect the raw ordered requests before physical lowering.
-/
structure PackedReviewerComponentRun (State Value : Type) where
  terminal : Option Value
  state : State
  trace : List PackedReviewerLogicalEvent

private def PackedReviewerComponentRun.prepend
    {State Value : Type}
    (request : PackedReviewerLogicalRequest) (reply : Option (List Bool))
    (tail : PackedReviewerComponentRun State Value) :
    PackedReviewerComponentRun State Value where
  terminal := tail.terminal
  state := tail.state
  trace := { request := request, reply := reply } :: tail.trace

private def packedReviewerDriveComponent
    {State Value : Type}
    (result : State -> Option Value)
    (nextRequest : State -> Option PackedReviewerLogicalRequest)
    (consumeReply : State -> Option (List Bool) -> State)
    (store : WordRAM.ReadStore) : Nat -> State ->
      PackedReviewerComponentRun State Value
  | 0, state =>
      { terminal := result state, state := state, trace := [] }
  | fuel + 1, state =>
      match result state with
      | some value =>
          { terminal := some value, state := state, trace := [] }
      | none =>
          match nextRequest state with
          | none => { terminal := none, state := state, trace := [] }
          | some request =>
              let reply := store.readWord? request.segment request.index
              let tail :=
                packedReviewerDriveComponent result nextRequest consumeReply
                  store fuel (consumeReply state reply)
              { terminal := tail.terminal
                state := tail.state
                trace := { request := request, reply := reply } :: tail.trace }

private def packedReviewerDriveEntry (store : WordRAM.ReadStore) :=
  packedReviewerDriveComponent packedReviewerEntryResult
    packedReviewerEntryNextRequest packedReviewerEntryConsumeReply store

private def packedReviewerDriveRank (store : WordRAM.ReadStore) :=
  packedReviewerDriveComponent packedReviewerRankResult
    packedReviewerRankNextRequest packedReviewerRankConsumeReply store

private def packedReviewerDriveWordSelect (store : WordRAM.ReadStore) :=
  packedReviewerDriveComponent packedReviewerWordSelectResult
    packedReviewerWordSelectNextRequest packedReviewerWordSelectConsumeReply
    store

private def packedReviewerDriveFringe (store : WordRAM.ReadStore) :=
  packedReviewerDriveComponent packedReviewerFringeResult
    packedReviewerFringeNextRequest packedReviewerFringeConsumeReply store

private def packedReviewerDriveBPWindow (store : WordRAM.ReadStore) :=
  packedReviewerDriveComponent packedReviewerBPWindowResult
    packedReviewerBPWindowNextRequest packedReviewerBPWindowConsumeReply store

private def packedReviewerDriveInteriorNat (store : WordRAM.ReadStore) :=
  packedReviewerDriveComponent packedReviewerInteriorNatResult
    packedReviewerInteriorNatNextRequest
    packedReviewerInteriorNatConsumeReply store

private def packedReviewerDriveSelect (store : WordRAM.ReadStore) :=
  packedReviewerDriveComponent packedReviewerSelectResult
    packedReviewerSelectNextRequest packedReviewerSelectConsumeReply store

private def packedReviewerDriveInterior (store : WordRAM.ReadStore) :=
  packedReviewerDriveComponent packedReviewerInteriorResult
    packedReviewerInteriorNextRequest packedReviewerInteriorConsumeReply store

private def packedReviewerDriveLca (store : WordRAM.ReadStore) :=
  packedReviewerDriveComponent packedReviewerLcaResult
    packedReviewerLcaNextRequest packedReviewerLcaConsumeReply store

private def packedReviewerDriveWhole (store : WordRAM.ReadStore) :=
  packedReviewerDriveComponent packedReviewerWholeResult
    packedReviewerWholeNextRequest packedReviewerWholeConsumeReply store

private theorem packedReviewerDriveComponent_add_fuel_of_terminal
    {State Value : Type}
    (result : State -> Option Value)
    (nextRequest : State -> Option PackedReviewerLogicalRequest)
    (consumeReply : State -> Option (List Bool) -> State)
    (store : WordRAM.ReadStore) (fuel extra : Nat) (state : State)
    (value : Value)
    (hterminal :
      (packedReviewerDriveComponent result nextRequest consumeReply store fuel
        state).terminal = some value) :
    packedReviewerDriveComponent result nextRequest consumeReply store
        (fuel + extra) state =
      packedReviewerDriveComponent result nextRequest consumeReply store fuel
        state := by
  induction fuel generalizing state with
  | zero =>
      rw [packedReviewerDriveComponent] at hterminal
      have hresult : result state = some value := hterminal
      cases extra with
      | zero => rfl
      | succ extra =>
          simp [packedReviewerDriveComponent, hresult]
  | succ fuel ih =>
      rw [packedReviewerDriveComponent] at hterminal
      cases hresult : result state with
      | some current =>
          have hcurrent : current = value := by
            simpa [hresult] using hterminal
          subst current
          rw [Nat.succ_add]
          simp [packedReviewerDriveComponent, hresult]
      | none =>
          cases hrequest : nextRequest state with
          | none =>
              simp [hresult, hrequest] at hterminal
          | some request =>
              rw [Nat.succ_add]
              have htail :
                  (packedReviewerDriveComponent result nextRequest consumeReply
                    store fuel
                    (consumeReply state
                      (store.readWord? request.segment request.index))).terminal =
                    some value := by
                simpa [hresult, hrequest] using hterminal
              have hstable :=
                ih (state :=
                  consumeReply state
                    (store.readWord? request.segment request.index)) htail
              conv =>
                lhs
                rw [packedReviewerDriveComponent]
              conv =>
                rhs
                rw [packedReviewerDriveComponent]
              simp only [hresult, hrequest]
              rw [hstable]

private theorem packedReviewerDriveComponent_succ_of_request
    {State Value : Type}
    (result : State -> Option Value)
    (nextRequest : State -> Option PackedReviewerLogicalRequest)
    (consumeReply : State -> Option (List Bool) -> State)
    (store : WordRAM.ReadStore) (fuel : Nat) (state : State)
    (request : PackedReviewerLogicalRequest)
    (hresult : result state = none)
    (hrequest : nextRequest state = some request) :
    packedReviewerDriveComponent result nextRequest consumeReply store
        (fuel + 1) state =
      let reply := store.readWord? request.segment request.index
      let tail :=
        packedReviewerDriveComponent result nextRequest consumeReply store fuel
          (consumeReply state reply)
      tail.prepend request reply := by
  rw [packedReviewerDriveComponent, hresult, hrequest]
  rfl

private theorem packedReviewerDriveComponent_of_result
    {State Value : Type}
    (result : State -> Option Value)
    (nextRequest : State -> Option PackedReviewerLogicalRequest)
    (consumeReply : State -> Option (List Bool) -> State)
    (store : WordRAM.ReadStore) (fuel : Nat) (state : State) (value : Value)
    (hresult : result state = some value) :
    packedReviewerDriveComponent result nextRequest consumeReply store fuel
        state =
      { terminal := some value, state := state, trace := [] } := by
  cases fuel <;> simp [packedReviewerDriveComponent, hresult]

/--
Splice a delegated component phase into an enclosing controller.  The enclosing
state exposes exactly the component's next request while that component is
running, and switches to `after` on the reply which makes the component
terminal.  Any unused component fuel is harmless because the continuation is
already terminal at its own budget.
-/
private theorem packedReviewerDriveComponent_embedded_phase
    {InnerState OuterState InnerValue OuterValue : Type}
    (innerResult : InnerState -> Option InnerValue)
    (innerNextRequest : InnerState -> Option PackedReviewerLogicalRequest)
    (innerConsumeReply : InnerState -> Option (List Bool) -> InnerState)
    (outerResult : OuterState -> Option OuterValue)
    (outerNextRequest : OuterState -> Option PackedReviewerLogicalRequest)
    (outerConsumeReply : OuterState -> Option (List Bool) -> OuterState)
    (wrap : InnerState -> OuterState) (after : InnerValue -> OuterState)
    (store : WordRAM.ReadStore) (innerFuel outerFuel : Nat)
    (innerState : InnerState) (innerValue : InnerValue)
    (outerValue : OuterValue)
    (hinnerStart : innerResult innerState = none)
    (hinnerTerminal :
      (packedReviewerDriveComponent innerResult innerNextRequest
        innerConsumeReply store innerFuel innerState).terminal =
        some innerValue)
    (houterTerminal :
      (packedReviewerDriveComponent outerResult outerNextRequest
        outerConsumeReply store outerFuel (after innerValue)).terminal =
        some outerValue)
    (hresult : ∀ state, innerResult state = none ->
      outerResult (wrap state) = none)
    (hrequest : ∀ state, innerResult state = none ->
      outerNextRequest (wrap state) = innerNextRequest state)
    (hconsume : ∀ state reply, innerResult state = none ->
      outerConsumeReply (wrap state) reply =
        match innerResult (innerConsumeReply state reply) with
        | some value => after value
        | none => wrap (innerConsumeReply state reply)) :
    let innerRun :=
      packedReviewerDriveComponent innerResult innerNextRequest
        innerConsumeReply store innerFuel innerState
    let outerTail :=
      packedReviewerDriveComponent outerResult outerNextRequest
        outerConsumeReply store outerFuel (after innerValue)
    packedReviewerDriveComponent outerResult outerNextRequest
        outerConsumeReply store (innerFuel + outerFuel) (wrap innerState) =
      { terminal := outerTail.terminal
        state := outerTail.state
        trace := innerRun.trace ++ outerTail.trace } := by
  induction innerFuel generalizing innerState with
  | zero =>
      simp [packedReviewerDriveComponent, hinnerStart] at hinnerTerminal
  | succ innerFuel ih =>
      cases hnext : innerNextRequest innerState with
      | none =>
          simp [packedReviewerDriveComponent, hinnerStart, hnext] at hinnerTerminal
      | some request =>
          let reply := store.readWord? request.segment request.index
          let nextState := innerConsumeReply innerState reply
          have htailTerminal :
              (packedReviewerDriveComponent innerResult innerNextRequest
                innerConsumeReply store innerFuel nextState).terminal =
                some innerValue := by
            simpa [packedReviewerDriveComponent, hinnerStart, hnext, reply,
              nextState] using hinnerTerminal
          rw [Nat.succ_add]
          simp only [packedReviewerDriveComponent, hinnerStart,
            hresult innerState hinnerStart, hrequest innerState hinnerStart,
            hnext]
          rw [hconsume innerState reply hinnerStart]
          cases hnextResult : innerResult nextState with
          | some value =>
              have hinnerDoneValue :=
                packedReviewerDriveComponent_of_result innerResult
                  innerNextRequest innerConsumeReply store innerFuel nextState
                  value hnextResult
              have hvalue : value = innerValue := by
                rw [hinnerDoneValue] at htailTerminal
                exact Option.some.inj htailTerminal
              subst value
              have hstable :=
                packedReviewerDriveComponent_add_fuel_of_terminal
                  outerResult outerNextRequest outerConsumeReply store
                  outerFuel innerFuel (after innerValue) outerValue
                  houterTerminal
              have hinnerDone :=
                packedReviewerDriveComponent_of_result innerResult
                  innerNextRequest innerConsumeReply store innerFuel nextState
                  innerValue hnextResult
              have hinnerTrace :
                  (packedReviewerDriveComponent innerResult innerNextRequest
                    innerConsumeReply store innerFuel
                    (innerConsumeReply innerState reply)).trace = [] := by
                simpa [nextState] using congrArg
                  (fun run => run.trace) hinnerDone
              have hstable' :
                  packedReviewerDriveComponent outerResult outerNextRequest
                      outerConsumeReply store (innerFuel + outerFuel)
                      (after innerValue) =
                    packedReviewerDriveComponent outerResult outerNextRequest
                      outerConsumeReply store outerFuel
                      (after innerValue) := by
                simpa [Nat.add_comm] using hstable
              simp only
              rw [hstable', hinnerTrace]
              simp
          | none =>
              have hih := ih nextState hnextResult htailTerminal
              simpa [PackedReviewerComponentRun.prepend, nextState, reply,
                List.cons_append] using congrArg
                  (PackedReviewerComponentRun.prepend request reply) hih

private def PackedReviewerComponentRun.Simulates
    {State Value : Type}
    (run : PackedReviewerComponentRun State Value)
    (reference : WordRAM.TraceResult Value)
    (done : Value -> State) : Prop :=
  run.terminal = some reference.value /\
    run.state = done reference.value /\
    run.trace.map PackedReviewerLogicalEvent.erase = reference.trace

private def packedReviewerTracePrepend
    {Value : Type} (request : PackedReviewerLogicalRequest)
    (reply : Option (List Bool)) (tail : WordRAM.TraceResult Value) :
    WordRAM.TraceResult Value where
  value := tail.value
  trace :=
    WordRAM.TraceEvent.readWord request.segment request.index reply :: tail.trace

private theorem packedReviewerDriveComponent_add_fuel_of_simulates
    {State Value : Type}
    (result : State -> Option Value)
    (nextRequest : State -> Option PackedReviewerLogicalRequest)
    (consumeReply : State -> Option (List Bool) -> State)
    (store : WordRAM.ReadStore) (fuel extra : Nat) (state : State)
    (reference : WordRAM.TraceResult Value) (done : Value -> State)
    (h :
      (packedReviewerDriveComponent result nextRequest consumeReply store fuel
        state).Simulates reference done) :
    (packedReviewerDriveComponent result nextRequest consumeReply store
      (fuel + extra) state).Simulates reference done := by
  have hstable :=
    packedReviewerDriveComponent_add_fuel_of_terminal result nextRequest
      consumeReply store fuel extra state reference.value h.1
  rw [hstable]
  exact h

private theorem PackedReviewerComponentRun.prepend_simulates
    {State Value : Type} (run : PackedReviewerComponentRun State Value)
    (request : PackedReviewerLogicalRequest) (reply : Option (List Bool))
    (reference : WordRAM.TraceResult Value) (done : Value -> State)
    (h : run.Simulates reference done) :
    (run.prepend request reply).Simulates
      (packedReviewerTracePrepend request reply reference) done := by
  rcases h with ⟨hterminal, hstate, htrace⟩
  exact ⟨hterminal, hstate, by
    simp [PackedReviewerComponentRun.prepend, packedReviewerTracePrepend,
      PackedReviewerLogicalEvent.erase, htrace]⟩

private theorem packedReviewerDriveComponent_embedded_phase_simulates
    {InnerState OuterState InnerValue OuterValue : Type}
    (innerResult : InnerState -> Option InnerValue)
    (innerNextRequest : InnerState -> Option PackedReviewerLogicalRequest)
    (innerConsumeReply : InnerState -> Option (List Bool) -> InnerState)
    (outerResult : OuterState -> Option OuterValue)
    (outerNextRequest : OuterState -> Option PackedReviewerLogicalRequest)
    (outerConsumeReply : OuterState -> Option (List Bool) -> OuterState)
    (wrap : InnerState -> OuterState) (after : InnerValue -> OuterState)
    (innerDone : InnerValue -> InnerState)
    (outerDone : OuterValue -> OuterState)
    (store : WordRAM.ReadStore) (innerFuel outerFuel : Nat)
    (innerState : InnerState) (innerReference : WordRAM.TraceResult InnerValue)
    (continuation : InnerValue -> WordRAM.TraceResult OuterValue)
    (hinnerStart : innerResult innerState = none)
    (hinner :
      (packedReviewerDriveComponent innerResult innerNextRequest
        innerConsumeReply store innerFuel innerState).Simulates
        innerReference innerDone)
    (houter :
      (packedReviewerDriveComponent outerResult outerNextRequest
        outerConsumeReply store outerFuel (after innerReference.value)).Simulates
        (continuation innerReference.value) outerDone)
    (hresult : forall state, innerResult state = none ->
      outerResult (wrap state) = none)
    (hrequest : forall state, innerResult state = none ->
      outerNextRequest (wrap state) = innerNextRequest state)
    (hconsume : forall state reply, innerResult state = none ->
      outerConsumeReply (wrap state) reply =
        match innerResult (innerConsumeReply state reply) with
        | some value => after value
        | none => wrap (innerConsumeReply state reply)) :
    (packedReviewerDriveComponent outerResult outerNextRequest
      outerConsumeReply store (innerFuel + outerFuel)
      (wrap innerState)).Simulates
        (WordRAM.TraceResult.bind innerReference continuation) outerDone := by
  rcases hinner with ⟨hinnerTerminal, _, hinnerTrace⟩
  rcases houter with ⟨houterTerminal, houterState, houterTrace⟩
  have hsplice :=
    packedReviewerDriveComponent_embedded_phase innerResult innerNextRequest
      innerConsumeReply outerResult outerNextRequest outerConsumeReply wrap
      after store innerFuel outerFuel innerState innerReference.value
      (continuation innerReference.value).value hinnerStart hinnerTerminal
      houterTerminal hresult hrequest hconsume
  rw [hsplice]
  exact ⟨houterTerminal, houterState, by
    simp [PackedReviewerComponentRun.Simulates, WordRAM.TraceResult.bind,
      List.map_append, hinnerTrace, houterTrace]⟩

/-! ## Atomic state-machine equivalences -/

private theorem packedReviewerDriveEntry_simulates
    (store : WordRAM.ReadStore) (invocation : PackedReviewerInvocation)
    (kind : PackedReviewerEntryKind) (index : Nat) :
    let run :=
      packedReviewerDriveEntry store 4
        (.baseOccurrence invocation kind index)
    let reference :=
      packedSelectEntryRead
        (match kind with
        | .super => concreteBPNativeSelectCloseTraceSegmentLayout.superTable
        | .local => concreteBPNativeSelectCloseTraceSegmentLayout.localTable)
        store index
    run.Simulates reference PackedReviewerEntryState.done := by
  have hdecode : SuccinctSpace.bitsToNatLE = WordRAM.bitsToNatLE :=
    funext fun word =>
      (SuccinctSpace.WordRAMBridge.bitsToNatLE_eq word).symm
  cases kind <;>
    simp [PackedReviewerComponentRun.Simulates, packedReviewerDriveEntry,
      packedReviewerDriveComponent, packedReviewerEntryResult,
      packedReviewerEntryNextRequest, packedReviewerEntryConsumeReply,
      packedReviewerDecodeNat, packedSelectEntryRead,
      concreteBPNativeSelectCloseTraceSegmentLayout,
      WordRAM.TraceResult.bind, WordRAM.TraceResult.map,
      WordRAM.TraceResult.pure, WordRAM.TraceResult.ofProgramWithStore,
      WordRAM.TraceResult.relabelReadSegmentsWith, WordRAM.TraceResult.ofResult,
      WordRAM.Program.evalR, WordRAM.ReadStore.pullback,
      WordRAM.singletonSegmentMap, WordRAM.TraceEvent.singletonSegmentMap,
      WordRAM.TraceEvent.relabelReadSegmentWith,
      PackedReviewerEntryKind.segmentBase, concreteBPNativeDeadTraceSegment,
      hdecode]

private theorem packedReviewerDriveRankFold_simulates
    (store : WordRAM.ReadStore) (invocation : PackedReviewerInvocation)
    (kind : PackedReviewerRankKind) (n : Nat) (word : List Bool)
    (effectiveLimit j tail acc base : Nat) :
    let state : PackedReviewerRankState :=
      .fold invocation kind n word effectiveLimit j (tail + 1) acc base
    let run := packedReviewerDriveRank store (tail + 1) state
    let reference :=
      WordRAM.TraceResult.map (fun value => base + value)
        (SuccinctClose.bpChunkedWordRankTraceFromWithStore store 21
          (packedFringeChunkBits n) kind.target word effectiveLimit j (tail + 1)
          acc)
    run.Simulates reference PackedReviewerRankState.done := by
  induction tail generalizing j acc with
  | zero =>
      simp [PackedReviewerComponentRun.Simulates, packedReviewerDriveRank,
        packedReviewerDriveComponent, packedReviewerRankResult,
        packedReviewerRankNextRequest, packedReviewerRankConsumeReply,
        packedReviewerDecodeNat,
        SuccinctClose.bpChunkedWordRankTraceFromWithStore,
        SuccinctClose.bpChunkReadTraceResult, WordRAM.TraceResult.map,
        WordRAM.TraceResult.bind, WordRAM.TraceResult.pure,
        PackedReviewerLogicalEvent.erase]
  | succ tail ih =>
      let request : PackedReviewerLogicalRequest :=
        { invocation := invocation
          site := .rankChunk
          segment := 21
          index :=
            SuccinctClose.bpFringeChunkSlot (packedFringeChunkBits n)
              (SuccinctClose.bpFringeWindowChunkValue
                (packedFringeChunkBits n) word j)
              (SuccinctClose.bpWordChunkSliceLen
                (packedFringeChunkBits n) effectiveLimit j)
              (SuccinctClose.bpWordChunkSliceLen
                (packedFringeChunkBits n) effectiveLimit j) }
      let reply := store.readWord? request.segment request.index
      let acc' :=
        SuccinctClose.bpWordRankStepDecoded
          (packedFringeChunkBits n) kind.target
          (SuccinctClose.bpWordChunkSliceLen
            (packedFringeChunkBits n) effectiveLimit j)
          acc (packedReviewerDecodeNat reply)
      have hih := ih (j := j + 1) (acc := acc')
      have hstep :=
        packedReviewerDriveComponent_succ_of_request
          packedReviewerRankResult packedReviewerRankNextRequest
          packedReviewerRankConsumeReply store (tail + 1)
          (.fold invocation kind n word effectiveLimit j ((tail + 1) + 1)
            acc base)
          request (by rfl) (by rfl)
      dsimp only
      rw [packedReviewerDriveRank, hstep]
      simpa [PackedReviewerComponentRun.Simulates,
        PackedReviewerComponentRun.prepend, packedReviewerDriveRank,
        packedReviewerRankConsumeReply,
        packedReviewerDecodeNat, request, reply, acc',
        PackedReviewerLogicalEvent.erase,
        SuccinctClose.bpChunkedWordRankTraceFromWithStore,
        SuccinctClose.bpChunkReadTraceResult, WordRAM.TraceResult.map,
        WordRAM.TraceResult.bind, WordRAM.TraceResult.pure,
        List.map_cons, List.map_append, Nat.add_assoc] using hih

private theorem packedReviewerDriveRankFold_pos_simulates
    (store : WordRAM.ReadStore) (invocation : PackedReviewerInvocation)
    (kind : PackedReviewerRankKind) (n : Nat) (word : List Bool)
    (effectiveLimit j remaining acc base : Nat) (hremaining : 0 < remaining) :
    let state : PackedReviewerRankState :=
      .fold invocation kind n word effectiveLimit j remaining acc base
    let run := packedReviewerDriveRank store remaining state
    let reference :=
      WordRAM.TraceResult.map (fun value => base + value)
        (SuccinctClose.bpChunkedWordRankTraceFromWithStore store 21
          (packedFringeChunkBits n) kind.target word effectiveLimit j remaining
          acc)
    run.Simulates reference PackedReviewerRankState.done := by
  cases remaining with
  | zero => omega
  | succ tail =>
      simpa using packedReviewerDriveRankFold_simulates store invocation kind n
        word effectiveLimit j tail acc base

private theorem packedReviewerDriveRank_simulates
    (store : WordRAM.ReadStore) (invocation : PackedReviewerInvocation)
    (kind : PackedReviewerRankKind) (n pos : Nat) :
    let state : PackedReviewerRankState :=
      .superSample invocation kind n pos
    let run := packedReviewerDriveRank store 11 state
    let reference :=
      packedRankRead kind.superSegment kind.blockSegment kind.wordSegment 21
        (packedFringeChunkBits n) kind.target store (kind.bitLength n)
        (kind.wordSize n) (kind.blocksPerSuper n) pos
    run.Simulates reference PackedReviewerRankState.done := by
  let q := packedReviewerRankQueryPos kind n pos
  let superState : PackedReviewerRankState :=
    .superSample invocation kind n pos
  let superRequest : PackedReviewerLogicalRequest :=
    { invocation := invocation
      site := .rankSuper
      segment := kind.superSegment
      index := q / kind.wordSize n / kind.blocksPerSuper n }
  let superReply :=
    store.readWord? superRequest.segment superRequest.index
  let blockState : PackedReviewerRankState :=
    .blockSample invocation kind n pos (packedReviewerDecodeNat superReply)
  let blockRequest : PackedReviewerLogicalRequest :=
    { invocation := invocation
      site := .rankBlock
      segment := kind.blockSegment
      index := q / kind.wordSize n }
  let blockReply :=
    store.readWord? blockRequest.segment blockRequest.index
  let wordState : PackedReviewerRankState :=
    .word invocation kind n pos (packedReviewerDecodeNat superReply)
      (packedReviewerDecodeNat blockReply)
  let wordRequest : PackedReviewerLogicalRequest :=
    { invocation := invocation
      site := .rankWord
      segment := kind.wordSegment
      index := q / kind.wordSize n }
  let wordReply := store.readWord? wordRequest.segment wordRequest.index
  let tailState := packedReviewerRankConsumeReply wordState wordReply
  let tailReference : WordRAM.TraceResult Nat :=
    match packedReviewerDecodeNat superReply,
        packedReviewerDecodeNat blockReply, wordReply with
    | some superValue, some blockValue, some word =>
        WordRAM.TraceResult.map
          (fun localRank => superValue + blockValue + localRank)
          (SuccinctClose.bpChunkedWordRankTraceResultAtSegmentWithStore
            store 21 (packedFringeChunkBits n) kind.target word
            (q - q / kind.wordSize n * kind.wordSize n))
    | _, _, _ => WordRAM.TraceResult.pure 0
  have hsuperStep :
      packedReviewerDriveRank store 11 superState =
        (packedReviewerDriveRank store 10 blockState).prepend
          superRequest superReply := by
    simpa [packedReviewerDriveRank, superState, superRequest, superReply,
      blockState, q, packedReviewerRankConsumeReply] using
      (packedReviewerDriveComponent_succ_of_request
        packedReviewerRankResult packedReviewerRankNextRequest
        packedReviewerRankConsumeReply store 10 superState superRequest
        (by rfl) (by rfl))
  have hblockStep :
      packedReviewerDriveRank store 10 blockState =
        (packedReviewerDriveRank store 9 wordState).prepend
          blockRequest blockReply := by
    simpa [packedReviewerDriveRank, blockState, blockRequest, blockReply,
      wordState, q, packedReviewerRankConsumeReply] using
      (packedReviewerDriveComponent_succ_of_request
        packedReviewerRankResult packedReviewerRankNextRequest
        packedReviewerRankConsumeReply store 9 blockState blockRequest
        (by rfl) (by rfl))
  have hwordStep :
      packedReviewerDriveRank store 9 wordState =
        (packedReviewerDriveRank store 8 tailState).prepend
          wordRequest wordReply := by
    simpa [packedReviewerDriveRank, wordState, wordRequest, wordReply,
      tailState, q] using
      (packedReviewerDriveComponent_succ_of_request
        packedReviewerRankResult packedReviewerRankNextRequest
        packedReviewerRankConsumeReply store 8 wordState wordRequest
        (by rfl) (by rfl))
  have htail :
      (packedReviewerDriveRank store 8 tailState).Simulates tailReference
        PackedReviewerRankState.done := by
    cases hsuper : superReply with
    | none =>
        simp [tailState, tailReference, wordState, blockState,
          packedReviewerRankConsumeReply, packedReviewerDecodeNat,
          packedReviewerDriveRank, packedReviewerDriveComponent,
          packedReviewerRankResult, PackedReviewerComponentRun.Simulates,
          hsuper]
    | some superWord =>
        cases hblock : blockReply with
        | none =>
            simp [tailState, tailReference, wordState, blockState,
              packedReviewerRankConsumeReply, packedReviewerDecodeNat,
              packedReviewerDriveRank, packedReviewerDriveComponent,
              packedReviewerRankResult, PackedReviewerComponentRun.Simulates,
              hsuper, hblock]
        | some blockWord =>
            cases hword : wordReply with
            | none =>
                simp [tailState, tailReference, wordState, blockState,
                  packedReviewerRankConsumeReply, packedReviewerDecodeNat,
                  packedReviewerDriveRank, packedReviewerDriveComponent,
                  packedReviewerRankResult,
                  PackedReviewerComponentRun.Simulates,
                  hsuper, hblock, hword]
            | some word =>
                let limit := q - q / kind.wordSize n * kind.wordSize n
                let effectiveLimit :=
                  SuccinctClose.bpWordRankEffLimit word limit
                let count :=
                  SuccinctClose.bpWordChunkCount (packedFringeChunkBits n)
                    effectiveLimit
                let base :=
                  SuccinctSpace.bitsToNatLE superWord +
                    SuccinctSpace.bitsToNatLE blockWord
                let foldState : PackedReviewerRankState :=
                  .fold invocation kind n word effectiveLimit 0 count 0 base
                let foldReference :=
                  WordRAM.TraceResult.map (fun value => base + value)
                    (SuccinctClose.bpChunkedWordRankTraceFromWithStore store 21
                      (packedFringeChunkBits n) kind.target word effectiveLimit
                      0 count 0)
                by_cases hcount : count = 0
                · simp [tailState, tailReference, wordState, blockState,
                    packedReviewerRankConsumeReply, packedReviewerDecodeNat,
                    packedReviewerRankStartFold, packedReviewerDriveRank,
                    packedReviewerDriveComponent, packedReviewerRankResult,
                    PackedReviewerComponentRun.Simulates,
                    SuccinctClose.bpChunkedWordRankTraceResultAtSegmentWithStore,
                    SuccinctClose.bpChunkedWordRankTraceFromWithStore,
                    WordRAM.TraceResult.map, WordRAM.TraceResult.bind,
                    WordRAM.TraceResult.pure, q, limit, effectiveLimit, count,
                    base, hsuper, hblock, hword, hcount]
                · have hpositive : 0 < count := Nat.pos_of_ne_zero hcount
                  have hfold :
                      (packedReviewerDriveRank store count foldState).Simulates
                        foldReference PackedReviewerRankState.done := by
                    simpa [foldState, foldReference] using
                      (packedReviewerDriveRankFold_pos_simulates store
                        invocation kind n word effectiveLimit 0 count 0 base
                        hpositive)
                  have hterminal :
                      (packedReviewerDriveComponent packedReviewerRankResult
                        packedReviewerRankNextRequest
                        packedReviewerRankConsumeReply store count
                        foldState).terminal = some foldReference.value := by
                    simpa [packedReviewerDriveRank] using hfold.1
                  have hpad :=
                    packedReviewerDriveComponent_add_fuel_of_terminal
                      packedReviewerRankResult packedReviewerRankNextRequest
                      packedReviewerRankConsumeReply store count (8 - count)
                      foldState foldReference.value hterminal
                  have hle : count <= 8 := by
                    exact SuccinctClose.bpWordChunkCount_le_eight
                      (packedFringeChunkBits n) effectiveLimit
                  have hsum : count + (8 - count) = 8 :=
                    Nat.add_sub_of_le hle
                  have hrun8 :
                      packedReviewerDriveRank store 8 foldState =
                        packedReviewerDriveRank store count foldState := by
                    change
                      packedReviewerDriveComponent packedReviewerRankResult
                          packedReviewerRankNextRequest
                          packedReviewerRankConsumeReply store 8 foldState =
                        packedReviewerDriveComponent packedReviewerRankResult
                          packedReviewerRankNextRequest
                          packedReviewerRankConsumeReply store count foldState
                    rw [← hsum]
                    exact hpad
                  have hfold8 :
                      (packedReviewerDriveRank store 8 foldState).Simulates
                        foldReference PackedReviewerRankState.done := by
                    rw [hrun8]
                    exact hfold
                  simpa [tailState, tailReference, wordState, blockState,
                    packedReviewerRankConsumeReply, packedReviewerDecodeNat,
                    packedReviewerRankStartFold,
                    SuccinctClose.bpChunkedWordRankTraceResultAtSegmentWithStore,
                    q, limit, effectiveLimit, count, base, foldState,
                    foldReference, hsuper, hblock, hword, hcount] using hfold8
  have hwordPrefix :=
    PackedReviewerComponentRun.prepend_simulates
      (run := packedReviewerDriveRank store 8 tailState)
      (request := wordRequest) (reply := wordReply)
      (reference := tailReference) (done := PackedReviewerRankState.done) htail
  have hblockPrefix :=
    PackedReviewerComponentRun.prepend_simulates
      (run := (packedReviewerDriveRank store 8 tailState).prepend
        wordRequest wordReply)
      (request := blockRequest) (reply := blockReply)
      (reference := packedReviewerTracePrepend wordRequest wordReply
        tailReference)
      (done := PackedReviewerRankState.done) hwordPrefix
  have hprefix :=
    PackedReviewerComponentRun.prepend_simulates
      (run := ((packedReviewerDriveRank store 8 tailState).prepend
        wordRequest wordReply).prepend blockRequest blockReply)
      (request := superRequest) (reply := superReply)
      (reference := packedReviewerTracePrepend blockRequest blockReply
        (packedReviewerTracePrepend wordRequest wordReply tailReference))
      (done := PackedReviewerRankState.done) hblockPrefix
  have hrun :
      packedReviewerDriveRank store 11 superState =
        (((packedReviewerDriveRank store 8 tailState).prepend
          wordRequest wordReply).prepend blockRequest blockReply).prepend
            superRequest superReply := by
    rw [hsuperStep, hblockStep, hwordStep]
  have href :
      packedRankRead kind.superSegment kind.blockSegment kind.wordSegment 21
          (packedFringeChunkBits n) kind.target store (kind.bitLength n)
          (kind.wordSize n) (kind.blocksPerSuper n) pos =
        packedReviewerTracePrepend superRequest superReply
          (packedReviewerTracePrepend blockRequest blockReply
            (packedReviewerTracePrepend wordRequest wordReply tailReference)) := by
    simp [packedRankRead, packedReviewerTracePrepend, tailReference,
      superRequest, superReply, blockRequest, blockReply, wordRequest,
      wordReply, q, packedReviewerRankQueryPos, packedReviewerDecodeNat,
      SuccinctClose.bpChunkReadTraceResult,
      SuccinctClose.bpWordReadTraceResult, WordRAM.TraceResult.bind]
    constructor <;> rfl
  dsimp only
  change
    (packedReviewerDriveRank store 11 superState).Simulates
      (packedRankRead kind.superSegment kind.blockSegment kind.wordSegment 21
        (packedFringeChunkBits n) kind.target store (kind.bitLength n)
        (kind.wordSize n) (kind.blocksPerSuper n) pos)
      PackedReviewerRankState.done
  rw [hrun, href]
  exact hprefix

private theorem packedReviewerDriveWordSelectSelectChunk_simulates
    (store : WordRAM.ReadStore) (invocation : PackedReviewerInvocation)
    (n : Nat) (target : Bool) (word : List Bool)
    (j remaining occurrence extra : Nat) :
    let state : PackedReviewerWordSelectState :=
      .selectChunk invocation n target word j remaining occurrence
    let run := packedReviewerDriveWordSelect store (extra + 1) state
    let reference :=
      WordRAM.TraceResult.map
        (fun selected? =>
          some (j * packedFringeChunkBits n + selected?.getD 0))
        (SuccinctClose.bpChunkReadTraceResult store 22
          (SuccinctClose.bpChunkSelectSlot (packedFringeChunkBits n)
            (SuccinctClose.bpFringeWindowChunkValue
              (packedFringeChunkBits n) word j)
            occurrence))
    run.Simulates reference PackedReviewerWordSelectState.done := by
  let state : PackedReviewerWordSelectState :=
    .selectChunk invocation n target word j remaining occurrence
  let request : PackedReviewerLogicalRequest :=
    { invocation := invocation
      site := .selectChunkValue
      segment := 22
      index :=
        SuccinctClose.bpChunkSelectSlot (packedFringeChunkBits n)
          (SuccinctClose.bpFringeWindowChunkValue
            (packedFringeChunkBits n) word j)
          occurrence }
  let reply := store.readWord? request.segment request.index
  let value :=
    some
      (j * packedFringeChunkBits n +
        (packedReviewerDecodeNat reply).getD 0)
  let doneState : PackedReviewerWordSelectState := .done value
  have hstep :=
    packedReviewerDriveComponent_succ_of_request
      packedReviewerWordSelectResult packedReviewerWordSelectNextRequest
      packedReviewerWordSelectConsumeReply store extra state request
      (by rfl) (by rfl)
  have hdone :=
    packedReviewerDriveComponent_of_result
      packedReviewerWordSelectResult packedReviewerWordSelectNextRequest
      packedReviewerWordSelectConsumeReply store extra doneState value (by rfl)
  have hdoneSim :
      (packedReviewerDriveComponent packedReviewerWordSelectResult
        packedReviewerWordSelectNextRequest
        packedReviewerWordSelectConsumeReply store extra doneState).Simulates
        (WordRAM.TraceResult.pure value) PackedReviewerWordSelectState.done := by
    rw [hdone]
    simp [PackedReviewerComponentRun.Simulates, WordRAM.TraceResult.pure,
      doneState]
  have hprefix :=
    PackedReviewerComponentRun.prepend_simulates
      (run := packedReviewerDriveComponent packedReviewerWordSelectResult
        packedReviewerWordSelectNextRequest
        packedReviewerWordSelectConsumeReply store extra doneState)
      (request := request) (reply := reply)
      (reference := WordRAM.TraceResult.pure value)
      (done := PackedReviewerWordSelectState.done) hdoneSim
  dsimp only
  rw [packedReviewerDriveWordSelect, hstep]
  simpa [PackedReviewerComponentRun.Simulates,
    PackedReviewerComponentRun.prepend, packedReviewerWordSelectConsumeReply,
    packedReviewerDecodeNat, state, request, reply, value, doneState,
    SuccinctClose.bpChunkReadTraceResult, WordRAM.TraceResult.map,
    WordRAM.TraceResult.bind, WordRAM.TraceResult.pure,
    packedReviewerTracePrepend, PackedReviewerLogicalEvent.erase] using hprefix

private theorem packedReviewerDriveWordSelectFrom_simulates
    (store : WordRAM.ReadStore) (invocation : PackedReviewerInvocation)
    (n : Nat) (target : Bool) (word : List Bool)
    (j tail occurrence : Nat) :
    let state : PackedReviewerWordSelectState :=
      .rankChunk invocation n target word j (tail + 1) occurrence
    let run := packedReviewerDriveWordSelect store (tail + 2) state
    let reference :=
      SuccinctClose.bpChunkedWordSelectTraceFromWithStore store 21 22
        (packedFringeChunkBits n) target word j (tail + 1) occurrence
    run.Simulates reference PackedReviewerWordSelectState.done := by
  induction tail generalizing j occurrence with
  | zero =>
      let state : PackedReviewerWordSelectState :=
        .rankChunk invocation n target word j 1 occurrence
      let request : PackedReviewerLogicalRequest :=
        { invocation := invocation
          site := .selectChunkRank
          segment := 21
          index :=
            SuccinctClose.bpFringeChunkSlot (packedFringeChunkBits n)
              (SuccinctClose.bpFringeWindowChunkValue
                (packedFringeChunkBits n) word j)
              (SuccinctClose.bpWordChunkSliceLen
                (packedFringeChunkBits n) word.length j)
              (SuccinctClose.bpWordChunkSliceLen
                (packedFringeChunkBits n) word.length j) }
      let reply := store.readWord? request.segment request.index
      let rank :=
        SuccinctClose.bpChunkRankOfEntry (packedFringeChunkBits n) target
          (SuccinctClose.bpWordChunkSliceLen
            (packedFringeChunkBits n) word.length j)
          ((packedReviewerDecodeNat reply).getD 0)
      have hstep :=
        packedReviewerDriveComponent_succ_of_request
          packedReviewerWordSelectResult packedReviewerWordSelectNextRequest
          packedReviewerWordSelectConsumeReply store 1 state request
          (by rfl) (by rfl)
      dsimp only
      rw [packedReviewerDriveWordSelect, hstep]
      dsimp only
      by_cases hfound : occurrence < rank
      · have hconsume :
            packedReviewerWordSelectConsumeReply state reply =
              .selectChunk invocation n target word j 1 occurrence := by
          unfold packedReviewerWordSelectConsumeReply
          change (if occurrence < rank then _ else _) = _
          rw [if_pos hfound]
        rw [hconsume]
        have hfound' :
            occurrence <
              SuccinctClose.bpChunkRankOfEntry (packedFringeChunkBits n) target
                (SuccinctClose.bpWordChunkSliceLen
                  (packedFringeChunkBits n) word.length j)
                (((store.readWord? 21
                  (SuccinctClose.bpFringeChunkSlot (packedFringeChunkBits n)
                    (SuccinctClose.bpFringeWindowChunkValue
                      (packedFringeChunkBits n) word j)
                    (SuccinctClose.bpWordChunkSliceLen
                      (packedFringeChunkBits n) word.length j)
                    (SuccinctClose.bpWordChunkSliceLen
                      (packedFringeChunkBits n) word.length j))).map
                  SuccinctSpace.bitsToNatLE).getD 0) := by
          simpa [rank, reply, request, packedReviewerDecodeNat] using hfound
        have hselect :=
          packedReviewerDriveWordSelectSelectChunk_simulates store invocation
            n target word j 1 occurrence 0
        have hprefix :=
          PackedReviewerComponentRun.prepend_simulates
            (run := packedReviewerDriveWordSelect store 1
              (.selectChunk invocation n target word j 1 occurrence))
            (request := request) (reply := reply)
            (reference :=
              WordRAM.TraceResult.map
                (fun selected? =>
                  some (j * packedFringeChunkBits n + selected?.getD 0))
                (SuccinctClose.bpChunkReadTraceResult store 22
                  (SuccinctClose.bpChunkSelectSlot (packedFringeChunkBits n)
                    (SuccinctClose.bpFringeWindowChunkValue
                      (packedFringeChunkBits n) word j)
                    occurrence)))
            (done := PackedReviewerWordSelectState.done) hselect
        simpa [PackedReviewerComponentRun.prepend,
          packedReviewerWordSelectConsumeReply, packedReviewerDecodeNat, state,
          request, reply, rank, hfound, hfound',
          SuccinctClose.bpChunkedWordSelectTraceFromWithStore,
          SuccinctClose.bpChunkReadTraceResult, WordRAM.TraceResult.map,
          WordRAM.TraceResult.bind, packedReviewerTracePrepend] using hprefix
      · have hconsume :
            packedReviewerWordSelectConsumeReply state reply = .done none := by
          unfold packedReviewerWordSelectConsumeReply
          change (if occurrence < rank then _ else _) = _
          simp [hfound]
        rw [hconsume]
        have hfound' :
            ¬ occurrence <
              SuccinctClose.bpChunkRankOfEntry (packedFringeChunkBits n) target
                (SuccinctClose.bpWordChunkSliceLen
                  (packedFringeChunkBits n) word.length j)
                (((store.readWord? 21
                  (SuccinctClose.bpFringeChunkSlot (packedFringeChunkBits n)
                    (SuccinctClose.bpFringeWindowChunkValue
                      (packedFringeChunkBits n) word j)
                    (SuccinctClose.bpWordChunkSliceLen
                      (packedFringeChunkBits n) word.length j)
                    (SuccinctClose.bpWordChunkSliceLen
                      (packedFringeChunkBits n) word.length j))).map
                  SuccinctSpace.bitsToNatLE).getD 0) := by
          simpa [rank, reply, request, packedReviewerDecodeNat] using hfound
        have hdone :=
          packedReviewerDriveComponent_of_result
            packedReviewerWordSelectResult packedReviewerWordSelectNextRequest
            packedReviewerWordSelectConsumeReply store 1
            (.done none) none (by rfl)
        have hnone :
            (packedReviewerDriveWordSelect store 1 (.done none)).Simulates
              (WordRAM.TraceResult.pure none)
              PackedReviewerWordSelectState.done := by
          change
            (packedReviewerDriveComponent packedReviewerWordSelectResult
              packedReviewerWordSelectNextRequest
              packedReviewerWordSelectConsumeReply store 1
              (.done none)).Simulates (WordRAM.TraceResult.pure none)
                PackedReviewerWordSelectState.done
          rw [hdone]
          simp [PackedReviewerComponentRun.Simulates,
            WordRAM.TraceResult.pure]
        have hprefix :=
          PackedReviewerComponentRun.prepend_simulates
            (run := packedReviewerDriveWordSelect store 1 (.done none))
            (request := request) (reply := reply)
            (reference := WordRAM.TraceResult.pure none)
            (done := PackedReviewerWordSelectState.done) hnone
        simpa [PackedReviewerComponentRun.prepend,
          packedReviewerWordSelectConsumeReply, packedReviewerDecodeNat, state,
          request, reply, rank, hfound, hfound',
          SuccinctClose.bpChunkedWordSelectTraceFromWithStore,
          SuccinctClose.bpChunkReadTraceResult, WordRAM.TraceResult.bind,
          packedReviewerTracePrepend] using hprefix
  | succ tail ih =>
      let request : PackedReviewerLogicalRequest :=
        { invocation := invocation
          site := .selectChunkRank
          segment := 21
          index :=
            SuccinctClose.bpFringeChunkSlot (packedFringeChunkBits n)
              (SuccinctClose.bpFringeWindowChunkValue
                (packedFringeChunkBits n) word j)
              (SuccinctClose.bpWordChunkSliceLen
                (packedFringeChunkBits n) word.length j)
              (SuccinctClose.bpWordChunkSliceLen
                (packedFringeChunkBits n) word.length j) }
      let reply := store.readWord? request.segment request.index
      let rank :=
        SuccinctClose.bpChunkRankOfEntry (packedFringeChunkBits n) target
          (SuccinctClose.bpWordChunkSliceLen
            (packedFringeChunkBits n) word.length j)
          ((packedReviewerDecodeNat reply).getD 0)
      have hstep :=
        packedReviewerDriveComponent_succ_of_request
          packedReviewerWordSelectResult packedReviewerWordSelectNextRequest
          packedReviewerWordSelectConsumeReply store (tail + 2)
          (.rankChunk invocation n target word j ((tail + 1) + 1)
            occurrence)
          request (by rfl) (by rfl)
      dsimp only
      rw [packedReviewerDriveWordSelect, hstep]
      dsimp only
      by_cases hfound : occurrence < rank
      · have hconsume :
            packedReviewerWordSelectConsumeReply
                (.rankChunk invocation n target word j ((tail + 1) + 1)
                  occurrence)
                reply =
              .selectChunk invocation n target word j ((tail + 1) + 1)
                occurrence := by
          unfold packedReviewerWordSelectConsumeReply
          change (if occurrence < rank then _ else _) = _
          simp [hfound]
        rw [hconsume]
        have hfound' :
            occurrence <
              SuccinctClose.bpChunkRankOfEntry (packedFringeChunkBits n) target
                (SuccinctClose.bpWordChunkSliceLen
                  (packedFringeChunkBits n) word.length j)
                (((store.readWord? 21
                  (SuccinctClose.bpFringeChunkSlot (packedFringeChunkBits n)
                    (SuccinctClose.bpFringeWindowChunkValue
                      (packedFringeChunkBits n) word j)
                    (SuccinctClose.bpWordChunkSliceLen
                      (packedFringeChunkBits n) word.length j)
                    (SuccinctClose.bpWordChunkSliceLen
                      (packedFringeChunkBits n) word.length j))).map
                  SuccinctSpace.bitsToNatLE).getD 0) := by
          simpa [rank, reply, request, packedReviewerDecodeNat] using hfound
        have hselect :=
          packedReviewerDriveWordSelectSelectChunk_simulates store invocation
            n target word j ((tail + 1) + 1) occurrence (tail + 1)
        have hprefix :=
          PackedReviewerComponentRun.prepend_simulates
            (run := packedReviewerDriveWordSelect store (tail + 2)
              (.selectChunk invocation n target word j ((tail + 1) + 1)
                occurrence))
            (request := request) (reply := reply)
            (reference :=
              WordRAM.TraceResult.map
                (fun selected? =>
                  some (j * packedFringeChunkBits n + selected?.getD 0))
                (SuccinctClose.bpChunkReadTraceResult store 22
                  (SuccinctClose.bpChunkSelectSlot (packedFringeChunkBits n)
                    (SuccinctClose.bpFringeWindowChunkValue
                      (packedFringeChunkBits n) word j)
                    occurrence)))
            (done := PackedReviewerWordSelectState.done) hselect
        simpa [PackedReviewerComponentRun.prepend,
          packedReviewerWordSelectConsumeReply, packedReviewerDecodeNat,
          request, reply, rank, hfound, hfound',
          SuccinctClose.bpChunkedWordSelectTraceFromWithStore,
          SuccinctClose.bpChunkReadTraceResult, WordRAM.TraceResult.map,
          WordRAM.TraceResult.bind, packedReviewerTracePrepend] using hprefix
      · have hconsume :
            packedReviewerWordSelectConsumeReply
                (.rankChunk invocation n target word j ((tail + 1) + 1)
                  occurrence)
                reply =
              .rankChunk invocation n target word (j + 1) (tail + 1)
                (occurrence - rank) := by
          unfold packedReviewerWordSelectConsumeReply
          change (if occurrence < rank then _ else _) = _
          rw [if_neg hfound]
          rfl
        rw [hconsume]
        have hfound' :
            ¬ occurrence <
              SuccinctClose.bpChunkRankOfEntry (packedFringeChunkBits n) target
                (SuccinctClose.bpWordChunkSliceLen
                  (packedFringeChunkBits n) word.length j)
                (((store.readWord? 21
                  (SuccinctClose.bpFringeChunkSlot (packedFringeChunkBits n)
                    (SuccinctClose.bpFringeWindowChunkValue
                      (packedFringeChunkBits n) word j)
                    (SuccinctClose.bpWordChunkSliceLen
                      (packedFringeChunkBits n) word.length j)
                    (SuccinctClose.bpWordChunkSliceLen
                      (packedFringeChunkBits n) word.length j))).map
                  SuccinctSpace.bitsToNatLE).getD 0) := by
          simpa [rank, reply, request, packedReviewerDecodeNat] using hfound
        have hih :=
          ih (j := j + 1) (occurrence := occurrence - rank)
        have hprefix :=
          PackedReviewerComponentRun.prepend_simulates
            (run := packedReviewerDriveWordSelect store (tail + 2)
              (.rankChunk invocation n target word (j + 1) (tail + 1)
                (occurrence - rank)))
            (request := request) (reply := reply)
            (reference :=
              SuccinctClose.bpChunkedWordSelectTraceFromWithStore store 21 22
                (packedFringeChunkBits n) target word (j + 1) (tail + 1)
                (occurrence - rank))
            (done := PackedReviewerWordSelectState.done) hih
        simpa [PackedReviewerComponentRun.prepend,
          packedReviewerWordSelectConsumeReply, packedReviewerDecodeNat,
          request, reply, rank, hfound, hfound',
          SuccinctClose.bpChunkedWordSelectTraceFromWithStore,
          SuccinctClose.bpChunkReadTraceResult, WordRAM.TraceResult.bind,
          packedReviewerTracePrepend] using hprefix

private theorem packedReviewerDriveWordSelectFrom_pos_simulates
    (store : WordRAM.ReadStore) (invocation : PackedReviewerInvocation)
    (n : Nat) (target : Bool) (word : List Bool)
    (j remaining occurrence : Nat) (hremaining : 0 < remaining) :
    let state : PackedReviewerWordSelectState :=
      .rankChunk invocation n target word j remaining occurrence
    let run := packedReviewerDriveWordSelect store (remaining + 1) state
    let reference :=
      SuccinctClose.bpChunkedWordSelectTraceFromWithStore store 21 22
        (packedFringeChunkBits n) target word j remaining occurrence
    run.Simulates reference PackedReviewerWordSelectState.done := by
  cases remaining with
  | zero => omega
  | succ tail =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        packedReviewerDriveWordSelectFrom_simulates store invocation n target
          word j tail occurrence

private theorem packedReviewerDriveWordSelect_simulates
    (store : WordRAM.ReadStore) (invocation : PackedReviewerInvocation)
    (n : Nat) (target : Bool) (word : List Bool) (occurrence : Nat) :
    let state :=
      packedReviewerWordSelectStart invocation n target word occurrence
    let run :=
      packedReviewerDriveWordSelect store
        (packedReviewerWordSelectRemaining state) state
    let reference :=
      SuccinctClose.bpChunkedWordSelectTraceResultAtSegmentsWithStore store 21
        22 (packedFringeChunkBits n) target word occurrence
    run.Simulates reference PackedReviewerWordSelectState.done := by
  let count :=
    SuccinctClose.bpWordChunkCount (packedFringeChunkBits n) word.length
  by_cases hcount : count = 0
  · simp [packedReviewerWordSelectStart, count, hcount,
      SuccinctClose.bpChunkedWordSelectTraceResultAtSegmentsWithStore,
      SuccinctClose.bpChunkedWordSelectTraceFromWithStore,
      packedReviewerDriveWordSelect, packedReviewerDriveComponent,
      packedReviewerWordSelectResult, packedReviewerWordSelectRemaining,
      PackedReviewerComponentRun.Simulates, WordRAM.TraceResult.pure]
  · have hpositive : 0 < count := Nat.pos_of_ne_zero hcount
    simpa [packedReviewerWordSelectStart, count, hcount,
      packedReviewerWordSelectRemaining,
      SuccinctClose.bpChunkedWordSelectTraceResultAtSegmentsWithStore] using
      (packedReviewerDriveWordSelectFrom_pos_simulates store invocation n
        target word 0 count occurrence hpositive)

/-!
The remaining atom and composite equivalences are below.  They deliberately
retain the same proof-only driver shape, so every ordered-trace equation is
about actual request/reply transitions rather than an event-value inventory.
-/

private theorem packedReviewerDriveFringeFrom_simulates
    (store : WordRAM.ReadStore) (invocation : PackedReviewerInvocation)
    (n : Nat) (window : List Bool) (relLo relHi j tail : Nat)
    (foldState : Nat × Option (Nat × Nat)) :
    let state : PackedReviewerFringeState :=
      .chunk invocation n window relLo relHi j (tail + 1) foldState
    let run := packedReviewerDriveFringe store (tail + 1) state
    let execution :=
      (SuccinctClose.bpFringeChunkFoldComputationFrom
        (packedFringeChunkBits n) window relLo relHi j (tail + 1) foldState).run
        (SuccinctClose.flatWordStoreOfReadStore store 21)
    let reference :=
      SuccinctClose.flatStoreExecutionTraceResultAtSegment 21 execution
    run.Simulates reference PackedReviewerFringeState.done := by
  induction tail generalizing j foldState with
  | zero =>
      simp [PackedReviewerComponentRun.Simulates, packedReviewerDriveFringe,
        packedReviewerDriveComponent, packedReviewerFringeResult,
        packedReviewerFringeNextRequest, packedReviewerFringeConsumeReply,
        packedReviewerDecodeNat,
        SuccinctClose.bpFringeChunkFoldComputationFrom,
        SuccinctSpace.FlatStoreComputation.bind,
        SuccinctSpace.FlatStoreComputation.read,
        SuccinctSpace.FlatStoreComputation.pure,
        SuccinctSpace.FlatStoreExecution.append,
        SuccinctClose.flatStoreExecutionTraceResultAtSegment,
        SuccinctClose.flatWordStoreOfReadStore,
        PackedReviewerLogicalEvent.erase]
  | succ tail ih =>
      let request : PackedReviewerLogicalRequest :=
        { invocation := invocation
          site := .fringeChunk
            (SuccinctClose.bpFringeChunkSlot (packedFringeChunkBits n)
              (SuccinctClose.bpFringeWindowChunkValue
                (packedFringeChunkBits n) window j)
              (SuccinctClose.bpFringeChunkStartOff
                (packedFringeChunkBits n) relLo j)
              (SuccinctClose.bpFringeChunkEndOff
                (packedFringeChunkBits n) relHi j))
          segment := 21
          index :=
            SuccinctClose.bpFringeChunkSlot (packedFringeChunkBits n)
              (SuccinctClose.bpFringeWindowChunkValue
                (packedFringeChunkBits n) window j)
              (SuccinctClose.bpFringeChunkStartOff
                (packedFringeChunkBits n) relLo j)
              (SuccinctClose.bpFringeChunkEndOff
                (packedFringeChunkBits n) relHi j) }
      let reply := store.readWord? request.segment request.index
      let nextFold :=
        SuccinctClose.bpFringeChunkStepDecoded (packedFringeChunkBits n)
          relLo relHi j foldState (packedReviewerDecodeNat reply)
      have hstep :=
        packedReviewerDriveComponent_succ_of_request
          packedReviewerFringeResult packedReviewerFringeNextRequest
          packedReviewerFringeConsumeReply store (tail + 1)
          (.chunk invocation n window relLo relHi j ((tail + 1) + 1)
            foldState)
          request (by rfl) (by rfl)
      have hih := ih (j := j + 1) (foldState := nextFold)
      have hprefix :=
        PackedReviewerComponentRun.prepend_simulates
          (run := packedReviewerDriveFringe store (tail + 1)
            (.chunk invocation n window relLo relHi (j + 1) (tail + 1)
              nextFold))
          (request := request) (reply := reply)
          (reference :=
            SuccinctClose.flatStoreExecutionTraceResultAtSegment 21
              ((SuccinctClose.bpFringeChunkFoldComputationFrom
                (packedFringeChunkBits n) window relLo relHi (j + 1)
                (tail + 1) nextFold).run
                (SuccinctClose.flatWordStoreOfReadStore store 21)))
          (done := PackedReviewerFringeState.done) hih
      dsimp only
      rw [packedReviewerDriveFringe, hstep]
      simpa [PackedReviewerComponentRun.prepend,
        packedReviewerFringeConsumeReply, packedReviewerDecodeNat,
        request, reply, nextFold,
        SuccinctClose.bpFringeChunkFoldComputationFrom,
        SuccinctSpace.FlatStoreComputation.bind,
        SuccinctSpace.FlatStoreComputation.read,
        SuccinctSpace.FlatStoreExecution.append,
        SuccinctClose.flatStoreExecutionTraceResultAtSegment,
        SuccinctClose.flatWordStoreOfReadStore,
        packedReviewerTracePrepend, PackedReviewerLogicalEvent.erase,
        List.map_append] using hprefix

private theorem packedReviewerDriveFringeFrom_pos_simulates
    (store : WordRAM.ReadStore) (invocation : PackedReviewerInvocation)
    (n : Nat) (window : List Bool) (relLo relHi j remaining : Nat)
    (foldState : Nat × Option (Nat × Nat)) (hremaining : 0 < remaining) :
    let state : PackedReviewerFringeState :=
      .chunk invocation n window relLo relHi j remaining foldState
    let run := packedReviewerDriveFringe store remaining state
    let execution :=
      (SuccinctClose.bpFringeChunkFoldComputationFrom
        (packedFringeChunkBits n) window relLo relHi j remaining foldState).run
        (SuccinctClose.flatWordStoreOfReadStore store 21)
    let reference :=
      SuccinctClose.flatStoreExecutionTraceResultAtSegment 21 execution
    run.Simulates reference PackedReviewerFringeState.done := by
  cases remaining with
  | zero => omega
  | succ tail =>
      simpa using packedReviewerDriveFringeFrom_simulates store invocation n
        window relLo relHi j tail foldState

private theorem packedReviewerDriveFringe_simulates
    (store : WordRAM.ReadStore) (invocation : PackedReviewerInvocation)
    (n : Nat) (window : List Bool) (seed relLo relHi count : Nat) :
    let state :=
      packedReviewerFringeStart invocation n window seed relLo relHi count
    let run :=
      packedReviewerDriveFringe store
        (packedReviewerFringeRemaining state) state
    let reference :=
      SuccinctClose.bpFringeChunkFoldTraceResultAtSegmentWithStore store 21
        (packedFringeChunkBits n) window seed relLo relHi count
    run.Simulates reference PackedReviewerFringeState.done := by
  by_cases hcount : count = 0
  · simp [packedReviewerFringeStart, hcount,
      PackedReviewerComponentRun.Simulates,
      packedReviewerDriveFringe, packedReviewerDriveComponent,
      packedReviewerFringeResult, packedReviewerFringeRemaining,
      SuccinctClose.bpFringeChunkFoldTraceResultAtSegmentWithStore,
      SuccinctClose.bpFringeChunkFoldComputation,
      SuccinctClose.bpFringeChunkFoldComputationFrom,
      SuccinctSpace.FlatStoreComputation.pure,
      SuccinctClose.flatStoreExecutionTraceResultAtSegment]
  · have hpositive : 0 < count := Nat.pos_of_ne_zero hcount
    simpa [packedReviewerFringeStart, hcount,
      packedReviewerFringeRemaining,
      SuccinctClose.bpFringeChunkFoldTraceResultAtSegmentWithStore,
      SuccinctClose.bpFringeChunkFoldComputation] using
      packedReviewerDriveFringeFrom_pos_simulates store invocation n window
        relLo relHi 0 count (seed, none) hpositive

private theorem packedReviewerDriveBPWindow_simulates
    (store : WordRAM.ReadStore) (invocation : PackedReviewerInvocation)
    (n blockSize close : Nat) :
    let state :=
      packedReviewerBPWindowStart invocation n blockSize close
    let run := packedReviewerDriveBPWindow store 4 state
    let reference := packedLocalBPWindowBitsRead store n blockSize close
    run.Simulates reference PackedReviewerBPWindowState.done := by
  simp [PackedReviewerComponentRun.Simulates,
    packedReviewerDriveBPWindow, packedReviewerDriveComponent,
    packedReviewerBPWindowStart, packedReviewerBPWindowResult,
    packedReviewerBPWindowNextRequest,
    packedReviewerBPWindowConsumeReply, packedLocalBPWindowBitsRead,
    packedLocalBPBlockWordsRead,
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpCodeWordReadTraceResultWithStore,
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.readStorePayloadWordValue,
    WordRAM.TraceResult.bind, WordRAM.TraceResult.map,
    WordRAM.TraceResult.pure, PackedReviewerLogicalEvent.erase,
    SuccinctSpace.flattenPayloadWords]
  split <;> split <;> split <;> split <;>
    simp_all [SuccinctSpace.flattenPayloadWords]

private def packedReviewerInteriorNatReference
    (store : WordRAM.ReadStore) (start next remaining : Nat)
    (repliesRev : List (Option (List Bool))) :
    WordRAM.TraceResult (Option Nat) :=
  let addresses := SuccinctSpace.consecutiveWordIndices (start + next) remaining
  WordRAM.TraceResult.map
    (fun replies =>
      SuccinctSpace.fixedWidthNatTableMachineDecode
        (repliesRev.reverse ++ replies))
    (SuccinctClose.flatStoreExecutionTraceResultAtSegment 20
      ((SuccinctSpace.FlatStoreComputation.readMany addresses).run
        (SuccinctClose.flatWordStoreOfReadStore store 20)))

private theorem consecutiveWordIndices_map_add
    (base start count : Nat) :
    (SuccinctSpace.consecutiveWordIndices start count).map
        (fun index => base + index) =
      SuccinctSpace.consecutiveWordIndices (base + start) count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
      simp [SuccinctSpace.consecutiveWordIndices, ih, Nat.add_assoc]

private theorem packedReviewerDriveInteriorNatFrom_simulates
    (store : WordRAM.ReadStore) (invocation : PackedReviewerInvocation)
    (n start next tail : Nat)
    (repliesRev : List (Option (List Bool))) :
    let state : PackedReviewerInteriorNatState :=
      .read invocation n start next (tail + 1) repliesRev
    let run := packedReviewerDriveInteriorNat store (tail + 1) state
    let reference :=
      packedReviewerInteriorNatReference store start next (tail + 1) repliesRev
    run.Simulates reference PackedReviewerInteriorNatState.done := by
  induction tail generalizing next repliesRev with
  | zero =>
      simp [PackedReviewerComponentRun.Simulates,
        packedReviewerDriveInteriorNat, packedReviewerDriveComponent,
        packedReviewerInteriorNatResult,
        packedReviewerInteriorNatNextRequest,
        packedReviewerInteriorNatConsumeReply,
        packedReviewerInteriorNatReference,
        SuccinctSpace.consecutiveWordIndices,
        SuccinctSpace.FlatStoreComputation.readMany,
        SuccinctSpace.FlatStoreComputation.bind,
        SuccinctSpace.FlatStoreComputation.read,
        SuccinctSpace.FlatStoreComputation.pure,
        SuccinctSpace.FlatStoreExecution.append,
        SuccinctClose.flatStoreExecutionTraceResultAtSegment,
        SuccinctClose.flatWordStoreOfReadStore,
        WordRAM.TraceResult.map, WordRAM.TraceResult.bind,
        WordRAM.TraceResult.pure, PackedReviewerLogicalEvent.erase]
  | succ tail ih =>
      let request : PackedReviewerLogicalRequest :=
        { invocation := invocation
          site := .interiorChunk (start + next)
          segment := 20
          index := start + next }
      let reply := store.readWord? request.segment request.index
      let nextReplies := reply :: repliesRev
      have hstep :=
        packedReviewerDriveComponent_succ_of_request
          packedReviewerInteriorNatResult
          packedReviewerInteriorNatNextRequest
          packedReviewerInteriorNatConsumeReply store (tail + 1)
          (.read invocation n start next ((tail + 1) + 1) repliesRev)
          request (by rfl) (by rfl)
      have hih :=
        ih (next := next + 1) (repliesRev := nextReplies)
      have hprefix :=
        PackedReviewerComponentRun.prepend_simulates
          (run := packedReviewerDriveInteriorNat store (tail + 1)
            (.read invocation n start (next + 1) (tail + 1) nextReplies))
          (request := request) (reply := reply)
          (reference :=
            packedReviewerInteriorNatReference store start (next + 1)
              (tail + 1) nextReplies)
          (done := PackedReviewerInteriorNatState.done) hih
      dsimp only
      rw [packedReviewerDriveInteriorNat, hstep]
      simpa [PackedReviewerComponentRun.prepend,
        packedReviewerInteriorNatConsumeReply, request, reply, nextReplies,
        packedReviewerInteriorNatReference,
        SuccinctSpace.consecutiveWordIndices,
        SuccinctSpace.FlatStoreComputation.readMany,
        SuccinctSpace.FlatStoreComputation.bind,
        SuccinctSpace.FlatStoreComputation.read,
        SuccinctSpace.FlatStoreExecution.append,
        SuccinctClose.flatStoreExecutionTraceResultAtSegment,
        SuccinctClose.flatWordStoreOfReadStore,
        WordRAM.TraceResult.map, WordRAM.TraceResult.bind,
        packedReviewerTracePrepend, PackedReviewerLogicalEvent.erase,
        List.map_append, List.reverse_cons, List.append_assoc,
        Nat.add_assoc] using hprefix

private theorem packedReviewerDriveInteriorNatFrom_pos_simulates
    (store : WordRAM.ReadStore) (invocation : PackedReviewerInvocation)
    (n start next remaining : Nat)
    (repliesRev : List (Option (List Bool))) (hremaining : 0 < remaining) :
    let state : PackedReviewerInteriorNatState :=
      .read invocation n start next remaining repliesRev
    let run := packedReviewerDriveInteriorNat store remaining state
    let reference :=
      packedReviewerInteriorNatReference store start next remaining repliesRev
    run.Simulates reference PackedReviewerInteriorNatState.done := by
  cases remaining with
  | zero => omega
  | succ tail =>
      simpa using packedReviewerDriveInteriorNatFrom_simulates store invocation
        n start next tail repliesRev

private theorem packedReviewerDriveInteriorNat_simulates
    (store : WordRAM.ReadStore) (invocation : PackedReviewerInvocation)
    (n entryCount width base index : Nat) :
    let state :=
      packedReviewerInteriorNatStart invocation n entryCount width base index
    let run :=
      packedReviewerDriveInteriorNat store
        (packedReviewerInteriorNatRemaining state) state
    let reference :=
      SuccinctClose.flatStoreExecutionTraceResultAtSegment 20
        ((packedInteriorReadNatOf n entryCount width base index).run
          (SuccinctClose.flatWordStoreOfReadStore store 20))
    run.Simulates reference PackedReviewerInteriorNatState.done := by
  unfold packedReviewerInteriorNatStart packedInteriorReadNatOf
  by_cases hindex : index < entryCount
  · simp only [hindex, if_true]
    by_cases hcount :
        SuccinctSpace.fixedWidthNatTableMachineChunkCount width
            (packedBpCodeWordWidth n) = 0
    · simp [hcount, PackedReviewerComponentRun.Simulates,
        packedReviewerDriveInteriorNat, packedReviewerDriveComponent,
        packedReviewerInteriorNatResult,
        packedReviewerInteriorNatRemaining,
        SuccinctSpace.fixedWidthNatTableMachineFootprintAt,
        SuccinctSpace.fixedWidthNatTableMachineFootprint,
        SuccinctSpace.consecutiveWordIndices,
        SuccinctSpace.FlatStoreComputation.readMany,
        SuccinctSpace.FlatStoreComputation.map,
        SuccinctSpace.FlatStoreComputation.pure,
        SuccinctSpace.FlatStoreExecution.append,
        SuccinctClose.flatStoreExecutionTraceResultAtSegment,
        WordRAM.TraceResult.pure]
    · have hpositive :
          0 < SuccinctSpace.fixedWidthNatTableMachineChunkCount width
            (packedBpCodeWordWidth n) := by omega
      have hrun :=
        packedReviewerDriveInteriorNatFrom_pos_simulates store invocation n
          (base + index *
            SuccinctSpace.fixedWidthNatTableMachineChunkCount width
              (packedBpCodeWordWidth n))
          0
          (SuccinctSpace.fixedWidthNatTableMachineChunkCount width
            (packedBpCodeWordWidth n)) [] hpositive
      simpa [hcount, packedReviewerInteriorNatRemaining,
        packedReviewerInteriorNatReference,
        consecutiveWordIndices_map_add,
        SuccinctSpace.fixedWidthNatTableMachineFootprintAt,
        SuccinctSpace.fixedWidthNatTableMachineFootprint,
        SuccinctSpace.FlatStoreComputation.map,
        SuccinctSpace.FlatStoreExecution.append,
        SuccinctClose.flatStoreExecutionTraceResultAtSegment,
        WordRAM.TraceResult.map, WordRAM.TraceResult.bind,
        WordRAM.TraceResult.pure, Nat.add_comm] using hrun
  · simp only [hindex, if_false]
    have hrun :=
      packedReviewerDriveInteriorNatFrom_pos_simulates store invocation n
        (packedInteriorOffsets n).deadAddress 0 1 [] (by omega)
    simpa [packedReviewerInteriorNatRemaining,
      packedReviewerInteriorNatReference,
      SuccinctSpace.consecutiveWordIndices,
      SuccinctSpace.FlatStoreComputation.map,
      WordRAM.TraceResult.map] using hrun

private theorem packedReviewerDriveInterior_readNat_splice
    (store : WordRAM.ReadStore) (invocation : PackedReviewerInvocation)
    (readState : PackedReviewerInteriorNatState)
    (natContinuation : PackedReviewerInteriorNatContinuation)
    (reserve : Nat) (reference : WordRAM.TraceResult (Option Nat))
    (continuation : Option Nat ->
      WordRAM.TraceResult PackedReviewerCandidate)
    (hreadStart : packedReviewerInteriorNatResult readState = none)
    (hread :
      (packedReviewerDriveInteriorNat store
        (packedReviewerInteriorNatRemaining readState) readState).Simulates
          reference PackedReviewerInteriorNatState.done)
    (hcontinuation :
      let next :=
        packedReviewerInteriorFinishNat invocation reference.value
          natContinuation
      let ready :=
        packedReviewerInteriorNormalize
          (packedReviewerInteriorRemaining next + 1) next
      (packedReviewerDriveInterior store reserve ready).Simulates
        (continuation reference.value) PackedReviewerInteriorState.done) :
    (packedReviewerDriveInterior store
      (packedReviewerInteriorNatRemaining readState + reserve)
      (.readNat invocation readState natContinuation)).Simulates
      (WordRAM.TraceResult.bind reference continuation)
      PackedReviewerInteriorState.done := by
  let after : Option Nat -> PackedReviewerInteriorState :=
    fun value =>
      let next :=
        packedReviewerInteriorFinishNat invocation value natContinuation
      packedReviewerInteriorNormalize
        (packedReviewerInteriorRemaining next + 1) next
  apply packedReviewerDriveComponent_embedded_phase_simulates
    packedReviewerInteriorNatResult packedReviewerInteriorNatNextRequest
    packedReviewerInteriorNatConsumeReply packedReviewerInteriorResult
    packedReviewerInteriorNextRequest packedReviewerInteriorConsumeReply
    (fun read => .readNat invocation read natContinuation) after
    PackedReviewerInteriorNatState.done PackedReviewerInteriorState.done
    store (packedReviewerInteriorNatRemaining readState) reserve readState
    reference continuation hreadStart
  · simpa [packedReviewerDriveInteriorNat] using hread
  · simpa [packedReviewerDriveInterior, after] using hcontinuation
  · intros
    rfl
  · intros
    rfl
  · intro state reply _
    simp only [packedReviewerInteriorConsumeReply]
    cases hnext : packedReviewerInteriorNatResult
        (packedReviewerInteriorNatConsumeReply state reply) <;>
      simp [hnext, after]

private def PackedReviewerInteriorReady : PackedReviewerInteriorState -> Prop
  | .done _ => True
  | .readNat _ read _ => packedReviewerInteriorNatResult read = none

private def packedReviewerInteriorContinuationPotential :
    PackedReviewerInteriorState -> Nat
  | .done _ => 0
  | .readNat _ _ continuation =>
      packedReviewerInteriorNatContinuationRemaining continuation

private theorem packedReviewerInteriorFinishCandidate_ready_or_potential_lt
    (invocation : PackedReviewerInvocation)
    (value : PackedReviewerCandidate)
    (continuation : PackedReviewerCandidateContinuation) :
    let next :=
      packedReviewerInteriorFinishCandidate invocation value continuation
    PackedReviewerInteriorReady next ∨
      packedReviewerInteriorContinuationPotential next <
        packedReviewerCandidateContinuationRemaining continuation := by
  induction continuation generalizing value with
  | finish =>
      simp [packedReviewerInteriorFinishCandidate, PackedReviewerInteriorReady]
  | localTwoLeft n macroIdx localStart count encoded outer ih =>
      right
      simp [packedReviewerInteriorFinishCandidate,
        packedReviewerInteriorStartLocalSpan,
        packedReviewerInteriorReadNat,
        packedReviewerInteriorContinuationPotential,
        packedReviewerInteriorNatContinuationRemaining,
        packedReviewerCandidateContinuationRemaining]
  | localTwoRight left outer ih =>
      simpa [packedReviewerInteriorFinishCandidate,
        packedReviewerCandidateContinuationRemaining] using
        ih (SuccinctClose.bpCandidateMerge? left value)
  | globalTwoLeft n macroStart macroSpanCount encoded outer ih =>
      right
      simp [packedReviewerInteriorFinishCandidate,
        packedReviewerInteriorStartGlobalSpan,
        packedReviewerInteriorReadNat,
        packedReviewerInteriorContinuationPotential,
        packedReviewerInteriorNatContinuationRemaining,
        packedReviewerCandidateContinuationRemaining]
  | globalTwoRight left outer ih =>
      simpa [packedReviewerInteriorFinishCandidate,
        packedReviewerCandidateContinuationRemaining] using
        ih (SuccinctClose.bpCandidateMerge? left value)
  | adjacentLeft n macroStart rightCount outer ih =>
      right
      simp [packedReviewerInteriorFinishCandidate,
        packedReviewerInteriorStartLocalTwo,
        packedReviewerInteriorReadNat,
        packedReviewerInteriorContinuationPotential,
        packedReviewerInteriorNatContinuationRemaining,
        packedReviewerCandidateContinuationRemaining]
  | adjacentRight left outer ih =>
      simpa [packedReviewerInteriorFinishCandidate,
        packedReviewerCandidateContinuationRemaining] using
        ih (SuccinctClose.bpCandidateMerge? left value)
  | leftMiddleLeft n macroStart middleCount outer ih =>
      right
      simp [packedReviewerInteriorFinishCandidate,
        packedReviewerInteriorStartGlobalTwo,
        packedReviewerInteriorReadNat,
        packedReviewerInteriorContinuationPotential,
        packedReviewerInteriorNatContinuationRemaining,
        packedReviewerCandidateContinuationRemaining]
  | leftMiddleMiddle left outer ih =>
      simpa [packedReviewerInteriorFinishCandidate,
        packedReviewerCandidateContinuationRemaining] using
        ih (SuccinctClose.bpCandidateMerge? left value)
  | crossLeft n macroStart middleCount rightCount outer ih =>
      right
      simp [packedReviewerInteriorFinishCandidate,
        packedReviewerInteriorStartGlobalTwo,
        packedReviewerInteriorReadNat,
        packedReviewerInteriorContinuationPotential,
        packedReviewerInteriorNatContinuationRemaining,
        packedReviewerCandidateContinuationRemaining]
      omega
  | crossMiddle n macroStart middleCount rightCount left outer ih =>
      right
      simp [packedReviewerInteriorFinishCandidate,
        packedReviewerInteriorStartLocalTwo,
        packedReviewerInteriorReadNat,
        packedReviewerInteriorContinuationPotential,
        packedReviewerInteriorNatContinuationRemaining,
        packedReviewerCandidateContinuationRemaining]
  | crossRight left middle outer ih =>
      simpa [packedReviewerInteriorFinishCandidate,
        packedReviewerCandidateContinuationRemaining] using
        ih (SuccinctClose.bpCandidateMerge3? left middle value)

private theorem packedReviewerInteriorFinishNat_ready_or_potential_lt
    (invocation : PackedReviewerInvocation) (value : Option Nat)
    (continuation : PackedReviewerInteriorNatContinuation) :
    let next :=
      packedReviewerInteriorFinishNat invocation value continuation
    PackedReviewerInteriorReady next ∨
      packedReviewerInteriorContinuationPotential next <
        packedReviewerInteriorNatContinuationRemaining continuation := by
  cases continuation with
  | summaryBaseline n block outer =>
      right
      simp [packedReviewerInteriorFinishNat, packedReviewerInteriorReadNat,
        packedReviewerInteriorContinuationPotential,
        packedReviewerInteriorNatContinuationRemaining]
  | summaryMin n block baseline outer =>
      right
      simp [packedReviewerInteriorFinishNat, packedReviewerInteriorReadNat,
        packedReviewerInteriorContinuationPotential,
        packedReviewerInteriorNatContinuationRemaining]
  | summaryMax n block baseline minRel outer =>
      right
      simp [packedReviewerInteriorFinishNat, packedReviewerInteriorReadNat,
        packedReviewerInteriorContinuationPotential,
        packedReviewerInteriorNatContinuationRemaining]
  | summaryArg n block baseline minRel maxRel outer =>
      simpa [packedReviewerInteriorFinishNat,
        packedReviewerInteriorNatContinuationRemaining] using
        packedReviewerInteriorFinishCandidate_ready_or_potential_lt invocation
          ((match baseline, minRel, maxRel, value with
            | some b, some mn, some mx, some arg => some (b, mn, mx, arg)
            | _, _, _, _ => none).map
              (SuccinctClose.bpRelativeSummaryMinCandidate
                (packedInteriorLayout n).blockSize
                (packedInteriorLayout n).blocksPerSuper block)) outer
  | localOffset n macroIdx localStart level outer =>
      cases value with
      | none =>
          have hcandidate :=
            packedReviewerInteriorFinishCandidate_ready_or_potential_lt
              invocation none outer
          rcases hcandidate with hready | hlt
          · exact Or.inl (by
              simpa [packedReviewerInteriorFinishNat] using hready)
          · exact Or.inr (by
              simp [packedReviewerInteriorFinishNat,
                packedReviewerInteriorNatContinuationRemaining]
              omega)
      | some offset =>
          right
          simp [packedReviewerInteriorFinishNat,
            packedReviewerInteriorStartMinCandidate,
            packedReviewerInteriorReadNat,
            packedReviewerInteriorContinuationPotential,
            packedReviewerInteriorNatContinuationRemaining]
  | globalBlock n macroStart level outer =>
      cases value with
      | none =>
          have hcandidate :=
            packedReviewerInteriorFinishCandidate_ready_or_potential_lt
              invocation none outer
          rcases hcandidate with hready | hlt
          · exact Or.inl (by
              simpa [packedReviewerInteriorFinishNat] using hready)
          · exact Or.inr (by
              simp [packedReviewerInteriorFinishNat,
                packedReviewerInteriorNatContinuationRemaining]
              omega)
      | some block =>
          right
          simp [packedReviewerInteriorFinishNat,
            packedReviewerInteriorStartMinCandidate,
            packedReviewerInteriorReadNat,
            packedReviewerInteriorContinuationPotential,
            packedReviewerInteriorNatContinuationRemaining]
  | localLevel n macroIdx localStart count outer =>
      cases value with
      | none =>
          have hcandidate :=
            packedReviewerInteriorFinishCandidate_ready_or_potential_lt
              invocation none outer
          rcases hcandidate with hready | hlt
          · exact Or.inl (by
              simpa [packedReviewerInteriorFinishNat] using hready)
          · exact Or.inr (by
              simp [packedReviewerInteriorFinishNat,
                packedReviewerInteriorNatContinuationRemaining]
              omega)
      | some encoded =>
          right
          simp [packedReviewerInteriorFinishNat,
            packedReviewerInteriorStartLocalSpan,
            packedReviewerInteriorReadNat,
            packedReviewerInteriorContinuationPotential,
            packedReviewerInteriorNatContinuationRemaining,
            packedReviewerCandidateContinuationRemaining]
          omega

  | globalLevel n macroStart macroSpanCount outer =>
      cases value with
      | none =>
          have hcandidate :=
            packedReviewerInteriorFinishCandidate_ready_or_potential_lt
              invocation none outer
          rcases hcandidate with hready | hlt
          · exact Or.inl (by
              simpa [packedReviewerInteriorFinishNat] using hready)
          · exact Or.inr (by
              simp [packedReviewerInteriorFinishNat,
                packedReviewerInteriorNatContinuationRemaining]
              omega)
      | some encoded =>
          right
          simp [packedReviewerInteriorFinishNat,
            packedReviewerInteriorStartGlobalSpan,
            packedReviewerInteriorReadNat,
            packedReviewerInteriorContinuationPotential,
            packedReviewerInteriorNatContinuationRemaining,
            packedReviewerCandidateContinuationRemaining]
          omega

private theorem packedReviewerInteriorNormalize_eq_self_of_ready
    (fuel : Nat) (state : PackedReviewerInteriorState)
    (hready : PackedReviewerInteriorReady state) :
    packedReviewerInteriorNormalize fuel state = state := by
  cases state with
  | done value =>
      cases fuel <;> rfl
  | readNat invocation read continuation =>
      simp only [PackedReviewerInteriorReady] at hready
      cases fuel with
      | zero => rfl
      | succ fuel =>
          simp [packedReviewerInteriorNormalize, hready]

private theorem packedReviewerInteriorNormalize_ready_of_potential_lt
    (state : PackedReviewerInteriorState) (fuel : Nat)
    (hpotential : packedReviewerInteriorContinuationPotential state < fuel) :
    PackedReviewerInteriorReady
      (packedReviewerInteriorNormalize fuel state) := by
  induction fuel generalizing state with
  | zero =>
      omega
  | succ fuel ih =>
      cases state with
      | done value =>
          simp [packedReviewerInteriorNormalize, PackedReviewerInteriorReady]
      | readNat invocation read continuation =>
          cases hread : packedReviewerInteriorNatResult read with
          | none =>
              simp [packedReviewerInteriorNormalize, hread,
                PackedReviewerInteriorReady]
          | some value =>
              let next :=
                packedReviewerInteriorFinishNat invocation value continuation
              have hstep :=
                packedReviewerInteriorFinishNat_ready_or_potential_lt
                  invocation value continuation
              simp only [packedReviewerInteriorNormalize, hread]
              change PackedReviewerInteriorReady
                (packedReviewerInteriorNormalize fuel next)
              rcases hstep with hready | hlt
              · rw [packedReviewerInteriorNormalize_eq_self_of_ready fuel
                  next hready]
                exact hready
              · apply ih next
                simp only [next] at hlt ⊢
                simp [packedReviewerInteriorContinuationPotential] at hpotential
                omega

/-! ## Proof-side interior continuation semantics -/

private def packedReviewerInteriorRunComputation
    (store : WordRAM.ReadStore)
    (computation : SuccinctSpace.FlatStoreComputation α) :
    WordRAM.TraceResult α :=
  SuccinctClose.flatStoreExecutionTraceResultAtSegment 20
    (computation.run (SuccinctClose.flatWordStoreOfReadStore store 20))

@[simp] private theorem packedReviewerInteriorRunComputation_pure
    (store : WordRAM.ReadStore) (value : α) :
    packedReviewerInteriorRunComputation store
        (SuccinctSpace.FlatStoreComputation.pure value) =
      WordRAM.TraceResult.pure value :=
  rfl

@[simp] private theorem packedReviewerInteriorRunComputation_bind
    (store : WordRAM.ReadStore)
    (computation : SuccinctSpace.FlatStoreComputation α)
    (next : α -> SuccinctSpace.FlatStoreComputation β) :
    packedReviewerInteriorRunComputation store
        (SuccinctSpace.FlatStoreComputation.bind computation next) =
      WordRAM.TraceResult.bind
        (packedReviewerInteriorRunComputation store computation)
        (fun value => packedReviewerInteriorRunComputation store (next value)) :=
  by
    simp [packedReviewerInteriorRunComputation,
      SuccinctSpace.FlatStoreComputation.bind,
      SuccinctSpace.FlatStoreExecution.append,
      SuccinctClose.flatStoreExecutionTraceResultAtSegment,
      WordRAM.TraceResult.bind]

@[simp] private theorem packedReviewerInteriorRunComputation_map
    (store : WordRAM.ReadStore) (f : α -> β)
    (computation : SuccinctSpace.FlatStoreComputation α) :
    packedReviewerInteriorRunComputation store
        (SuccinctSpace.FlatStoreComputation.map f computation) =
      WordRAM.TraceResult.map f
        (packedReviewerInteriorRunComputation store computation) := by
  simp [SuccinctSpace.FlatStoreComputation.map, WordRAM.TraceResult.map]

@[simp] private theorem packedReviewerTraceResult_bind_assoc
    (first : WordRAM.TraceResult α) (second : α -> WordRAM.TraceResult β)
    (third : β -> WordRAM.TraceResult γ) :
    WordRAM.TraceResult.bind (WordRAM.TraceResult.bind first second) third =
      WordRAM.TraceResult.bind first
        (fun value => WordRAM.TraceResult.bind (second value) third) := by
  simp [WordRAM.TraceResult.bind, List.append_assoc]

@[simp] private theorem packedReviewerTraceResult_pure_bind
    (value : α) (next : α -> WordRAM.TraceResult β) :
    WordRAM.TraceResult.bind (WordRAM.TraceResult.pure value) next = next value :=
  rfl

@[simp] private theorem packedReviewerTraceResult_bind_pure
    (result : WordRAM.TraceResult α) :
    WordRAM.TraceResult.bind result WordRAM.TraceResult.pure = result := by
  cases result
  simp [WordRAM.TraceResult.bind, WordRAM.TraceResult.pure]

private def packedReviewerInteriorCandidateContinuationComputation
    (value : PackedReviewerCandidate) :
    PackedReviewerCandidateContinuation ->
      SuccinctSpace.FlatStoreComputation PackedReviewerCandidate
  | .finish => SuccinctSpace.FlatStoreComputation.pure value
  | .localTwoLeft n macroIdx localStart count encoded outer =>
      let domain :=
        SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSize
      SuccinctSpace.FlatStoreComputation.bind
        (packedLocalSpanCandidateComputation n macroIdx
          (localStart + count - encoded % domain) (encoded / domain))
        (fun right =>
          packedReviewerInteriorCandidateContinuationComputation
            (SuccinctClose.bpCandidateMerge? value right) outer)
  | .localTwoRight left outer =>
      packedReviewerInteriorCandidateContinuationComputation
        (SuccinctClose.bpCandidateMerge? left value) outer
  | .globalTwoLeft n macroStart macroSpanCount encoded outer =>
      let domain :=
        SuccinctClose.bpSparseLevelDomain
          (packedInteriorLayout n).macroSampleCount
      SuccinctSpace.FlatStoreComputation.bind
        (packedGlobalSpanCandidateComputation n
          (macroStart + macroSpanCount - encoded % domain) (encoded / domain))
        (fun right =>
          packedReviewerInteriorCandidateContinuationComputation
            (SuccinctClose.bpCandidateMerge? value right) outer)
  | .globalTwoRight left outer =>
      packedReviewerInteriorCandidateContinuationComputation
        (SuccinctClose.bpCandidateMerge? left value) outer
  | .adjacentLeft n macroStart rightCount outer =>
      SuccinctSpace.FlatStoreComputation.bind
        (packedLocalTwoSpanCandidateComputation n (macroStart + 1) 0 rightCount)
        (fun right =>
          packedReviewerInteriorCandidateContinuationComputation
            (SuccinctClose.bpCandidateMerge? value right) outer)
  | .adjacentRight left outer =>
      packedReviewerInteriorCandidateContinuationComputation
        (SuccinctClose.bpCandidateMerge? left value) outer
  | .leftMiddleLeft n macroStart middleCount outer =>
      SuccinctSpace.FlatStoreComputation.bind
        (packedGlobalTwoSpanCandidateComputation n (macroStart + 1) middleCount)
        (fun middle =>
          packedReviewerInteriorCandidateContinuationComputation
            (SuccinctClose.bpCandidateMerge? value middle) outer)
  | .leftMiddleMiddle left outer =>
      packedReviewerInteriorCandidateContinuationComputation
        (SuccinctClose.bpCandidateMerge? left value) outer
  | .crossLeft n macroStart middleCount rightCount outer =>
      SuccinctSpace.FlatStoreComputation.bind
        (packedGlobalTwoSpanCandidateComputation n (macroStart + 1) middleCount)
        (fun middle =>
          SuccinctSpace.FlatStoreComputation.bind
            (packedLocalTwoSpanCandidateComputation n
              (macroStart + 1 + middleCount) 0 rightCount)
            (fun right =>
              packedReviewerInteriorCandidateContinuationComputation
                (SuccinctClose.bpCandidateMerge3? value middle right) outer))
  | .crossMiddle n macroStart middleCount rightCount left outer =>
      SuccinctSpace.FlatStoreComputation.bind
        (packedLocalTwoSpanCandidateComputation n
          (macroStart + 1 + middleCount) 0 rightCount)
        (fun right =>
          packedReviewerInteriorCandidateContinuationComputation
            (SuccinctClose.bpCandidateMerge3? left value right) outer)
  | .crossRight left middle outer =>
      packedReviewerInteriorCandidateContinuationComputation
        (SuccinctClose.bpCandidateMerge3? left middle value) outer
termination_by continuation => continuation

private def packedReviewerInteriorNatContinuationComputation
    (value : Option Nat) : PackedReviewerInteriorNatContinuation ->
      SuccinctSpace.FlatStoreComputation PackedReviewerCandidate
  | .summaryBaseline n block outer =>
      SuccinctSpace.FlatStoreComputation.bind
        (packedInteriorReadNatOf n (packedInteriorLayout n).blockCount
          (packedInteriorLayout n).relativeWidth
          (packedInteriorOffsets n).minRel block) fun minRel =>
        SuccinctSpace.FlatStoreComputation.bind
          (packedInteriorReadNatOf n (packedInteriorLayout n).blockCount
            (packedInteriorLayout n).relativeWidth
            (packedInteriorOffsets n).maxRel block) fun maxRel =>
          SuccinctSpace.FlatStoreComputation.bind
            (packedInteriorReadNatOf n (packedInteriorLayout n).blockCount
              (packedInteriorLayout n).relativeWidth
              (packedInteriorOffsets n).argOffset block) fun argOffset =>
            let summary : Option (Nat × Nat × Nat × Nat) :=
              match value, minRel, maxRel, argOffset with
              | some b, some mn, some mx, some arg => some (b, mn, mx, arg)
              | _, _, _, _ => none
            packedReviewerInteriorCandidateContinuationComputation
              (summary.map
                (SuccinctClose.bpRelativeSummaryMinCandidate
                  (packedInteriorLayout n).blockSize
                  (packedInteriorLayout n).blocksPerSuper block)) outer
  | .summaryMin n block baseline outer =>
      SuccinctSpace.FlatStoreComputation.bind
        (packedInteriorReadNatOf n (packedInteriorLayout n).blockCount
          (packedInteriorLayout n).relativeWidth
          (packedInteriorOffsets n).maxRel block) fun maxRel =>
        SuccinctSpace.FlatStoreComputation.bind
          (packedInteriorReadNatOf n (packedInteriorLayout n).blockCount
            (packedInteriorLayout n).relativeWidth
            (packedInteriorOffsets n).argOffset block) fun argOffset =>
          let summary : Option (Nat × Nat × Nat × Nat) :=
            match baseline, value, maxRel, argOffset with
            | some b, some mn, some mx, some arg => some (b, mn, mx, arg)
            | _, _, _, _ => none
          packedReviewerInteriorCandidateContinuationComputation
            (summary.map
              (SuccinctClose.bpRelativeSummaryMinCandidate
                (packedInteriorLayout n).blockSize
                (packedInteriorLayout n).blocksPerSuper block)) outer
  | .summaryMax n block baseline minRel outer =>
      SuccinctSpace.FlatStoreComputation.bind
        (packedInteriorReadNatOf n (packedInteriorLayout n).blockCount
          (packedInteriorLayout n).relativeWidth
          (packedInteriorOffsets n).argOffset block) fun argOffset =>
        let summary : Option (Nat × Nat × Nat × Nat) :=
          match baseline, minRel, value, argOffset with
          | some b, some mn, some mx, some arg => some (b, mn, mx, arg)
          | _, _, _, _ => none
        packedReviewerInteriorCandidateContinuationComputation
          (summary.map
            (SuccinctClose.bpRelativeSummaryMinCandidate
              (packedInteriorLayout n).blockSize
              (packedInteriorLayout n).blocksPerSuper block)) outer
  | .summaryArg n block baseline minRel maxRel outer =>
      let summary : Option (Nat × Nat × Nat × Nat) :=
        match baseline, minRel, maxRel, value with
        | some b, some mn, some mx, some arg => some (b, mn, mx, arg)
        | _, _, _, _ => none
      packedReviewerInteriorCandidateContinuationComputation
        (summary.map
          (SuccinctClose.bpRelativeSummaryMinCandidate
            (packedInteriorLayout n).blockSize
            (packedInteriorLayout n).blocksPerSuper block)) outer
  | .localOffset n macroIdx _ _ outer =>
      match value with
      | some offset =>
          SuccinctSpace.FlatStoreComputation.bind
            (packedMinCandidateComputation n
              (macroIdx * (packedInteriorLayout n).macroSize + offset))
            (fun candidate =>
              packedReviewerInteriorCandidateContinuationComputation candidate
                outer)
      | none =>
          packedReviewerInteriorCandidateContinuationComputation none outer
  | .globalBlock n _ _ outer =>
      match value with
      | some block =>
          SuccinctSpace.FlatStoreComputation.bind
            (packedMinCandidateComputation n block)
            (fun candidate =>
              packedReviewerInteriorCandidateContinuationComputation candidate
                outer)
      | none =>
          packedReviewerInteriorCandidateContinuationComputation none outer
  | .localLevel n macroIdx localStart count outer =>
      match value with
      | none =>
          packedReviewerInteriorCandidateContinuationComputation none outer
      | some encoded =>
          let domain :=
            SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSize
          SuccinctSpace.FlatStoreComputation.bind
            (packedLocalSpanCandidateComputation n macroIdx localStart
              (encoded / domain)) fun left =>
            SuccinctSpace.FlatStoreComputation.bind
              (packedLocalSpanCandidateComputation n macroIdx
                (localStart + count - encoded % domain) (encoded / domain))
              (fun right =>
                packedReviewerInteriorCandidateContinuationComputation
                  (SuccinctClose.bpCandidateMerge? left right) outer)
  | .globalLevel n macroStart macroSpanCount outer =>
      match value with
      | none =>
          packedReviewerInteriorCandidateContinuationComputation none outer
      | some encoded =>
          let domain :=
            SuccinctClose.bpSparseLevelDomain
              (packedInteriorLayout n).macroSampleCount
          SuccinctSpace.FlatStoreComputation.bind
            (packedGlobalSpanCandidateComputation n macroStart
              (encoded / domain)) fun left =>
            SuccinctSpace.FlatStoreComputation.bind
              (packedGlobalSpanCandidateComputation n
                (macroStart + macroSpanCount - encoded % domain)
                (encoded / domain))
              (fun right =>
                packedReviewerInteriorCandidateContinuationComputation
                  (SuccinctClose.bpCandidateMerge? left right) outer)

private def packedReviewerInteriorNatStateReference
    (store : WordRAM.ReadStore) : PackedReviewerInteriorNatState ->
      WordRAM.TraceResult (Option Nat)
  | .done value => WordRAM.TraceResult.pure value
  | .read _ _ start next remaining repliesRev =>
      packedReviewerInteriorNatReference store start next remaining repliesRev

private def packedReviewerInteriorStateReference
    (store : WordRAM.ReadStore) : PackedReviewerInteriorState ->
      WordRAM.TraceResult PackedReviewerCandidate
  | .done value => WordRAM.TraceResult.pure value
  | .readNat _ read continuation =>
      WordRAM.TraceResult.bind
        (packedReviewerInteriorNatStateReference store read)
        (fun value =>
          packedReviewerInteriorRunComputation store
            (packedReviewerInteriorNatContinuationComputation value
              continuation))

private theorem packedReviewerInteriorNatReference_trace_length
    (store : WordRAM.ReadStore) (start next remaining : Nat)
    (repliesRev : List (Option (List Bool))) :
    (packedReviewerInteriorNatReference store start next remaining
      repliesRev).trace.length = remaining := by
  induction remaining generalizing next with
  | zero =>
      simp [packedReviewerInteriorNatReference,
        SuccinctSpace.consecutiveWordIndices,
        SuccinctSpace.FlatStoreComputation.readMany,
        SuccinctSpace.FlatStoreComputation.pure,
        SuccinctClose.flatStoreExecutionTraceResultAtSegment]
  | succ remaining ih =>
      simp [packedReviewerInteriorNatReference,
        SuccinctSpace.consecutiveWordIndices,
        SuccinctSpace.FlatStoreComputation.readMany,
        SuccinctSpace.FlatStoreComputation.bind,
        SuccinctSpace.FlatStoreComputation.read,
        SuccinctSpace.FlatStoreComputation.pure,
        SuccinctSpace.FlatStoreExecution.append,
        SuccinctClose.flatStoreExecutionTraceResultAtSegment, ih]

private theorem packedReviewerInteriorNatStateReference_start
    (store : WordRAM.ReadStore) (invocation : PackedReviewerInvocation)
    (n entryCount width base index : Nat) :
    packedReviewerInteriorNatStateReference store
        (packedReviewerInteriorNatStart invocation n entryCount width base
          index) =
      packedReviewerInteriorRunComputation store
        (packedInteriorReadNatOf n entryCount width base index) := by
  unfold packedReviewerInteriorNatStart packedInteriorReadNatOf
  by_cases hindex : index < entryCount
  · simp only [hindex, if_true]
    by_cases hcount :
        SuccinctSpace.fixedWidthNatTableMachineChunkCount width
            (packedBpCodeWordWidth n) = 0
    · simp [hcount, packedReviewerInteriorNatStateReference,
        packedReviewerInteriorRunComputation,
        SuccinctSpace.fixedWidthNatTableMachineFootprintAt,
        SuccinctSpace.fixedWidthNatTableMachineFootprint,
        SuccinctSpace.consecutiveWordIndices,
        SuccinctSpace.FlatStoreComputation.readMany,
        SuccinctSpace.FlatStoreComputation.map,
        SuccinctSpace.FlatStoreComputation.pure,
        SuccinctSpace.FlatStoreExecution.append,
        SuccinctClose.flatStoreExecutionTraceResultAtSegment,
        WordRAM.TraceResult.pure]
    · simp [hcount, packedReviewerInteriorNatStateReference,
        packedReviewerInteriorNatReference,
        packedReviewerInteriorRunComputation,
        consecutiveWordIndices_map_add,
        SuccinctSpace.fixedWidthNatTableMachineFootprintAt,
        SuccinctSpace.fixedWidthNatTableMachineFootprint,
        SuccinctSpace.FlatStoreComputation.map,
        SuccinctSpace.FlatStoreExecution.append,
        SuccinctClose.flatStoreExecutionTraceResultAtSegment,
        WordRAM.TraceResult.map, WordRAM.TraceResult.bind,
        WordRAM.TraceResult.pure, Nat.add_comm]
  · simp [hindex, packedReviewerInteriorNatStateReference,
      packedReviewerInteriorNatReference,
      packedReviewerInteriorRunComputation,
      SuccinctSpace.consecutiveWordIndices,
      SuccinctSpace.FlatStoreComputation.readMany,
      SuccinctSpace.FlatStoreComputation.map,
      SuccinctSpace.FlatStoreComputation.bind,
      SuccinctSpace.FlatStoreComputation.read,
      SuccinctSpace.FlatStoreComputation.pure,
      SuccinctSpace.FlatStoreExecution.append,
      SuccinctClose.flatStoreExecutionTraceResultAtSegment,
      WordRAM.TraceResult.map, WordRAM.TraceResult.bind,
      WordRAM.TraceResult.pure]

private theorem packedReviewerInteriorStateReference_finishCandidate
    (store : WordRAM.ReadStore) (invocation : PackedReviewerInvocation)
    (value : PackedReviewerCandidate)
    (continuation : PackedReviewerCandidateContinuation) :
    packedReviewerInteriorStateReference store
        (packedReviewerInteriorFinishCandidate invocation value continuation) =
      packedReviewerInteriorRunComputation store
        (packedReviewerInteriorCandidateContinuationComputation value
          continuation) := by
  induction continuation generalizing value with
  | finish =>
      simp [packedReviewerInteriorFinishCandidate,
        packedReviewerInteriorStateReference,
        packedReviewerInteriorCandidateContinuationComputation]
  | localTwoLeft n macroIdx localStart count encoded outer ih =>
      simp [packedReviewerInteriorFinishCandidate,
        packedReviewerInteriorStartLocalSpan,
        packedReviewerInteriorStartMinCandidate,
        packedReviewerInteriorReadNat,
        packedReviewerInteriorStateReference,
        packedReviewerInteriorCandidateContinuationComputation,
        packedReviewerInteriorNatContinuationComputation,
        packedReviewerInteriorNatStateReference_start,
        packedLocalSpanCandidateComputation, packedMinCandidateComputation,
        packedSummaryComputation, ih, WordRAM.TraceResult.bind,
        List.append_assoc]
      split <;> simp_all [WordRAM.TraceResult.bind, List.append_assoc]
  | localTwoRight left outer ih =>
      simpa [packedReviewerInteriorFinishCandidate,
        packedReviewerInteriorCandidateContinuationComputation] using
        ih (SuccinctClose.bpCandidateMerge? left value)
  | globalTwoLeft n macroStart macroSpanCount encoded outer ih =>
      simp [packedReviewerInteriorFinishCandidate,
        packedReviewerInteriorStartGlobalSpan,
        packedReviewerInteriorStartMinCandidate,
        packedReviewerInteriorReadNat,
        packedReviewerInteriorStateReference,
        packedReviewerInteriorCandidateContinuationComputation,
        packedReviewerInteriorNatContinuationComputation,
        packedReviewerInteriorNatStateReference_start,
        packedGlobalSpanCandidateComputation, packedMinCandidateComputation,
        packedSummaryComputation, ih, WordRAM.TraceResult.bind,
        List.append_assoc]
      split <;> simp_all [WordRAM.TraceResult.bind, List.append_assoc]
  | globalTwoRight left outer ih =>
      simpa [packedReviewerInteriorFinishCandidate,
        packedReviewerInteriorCandidateContinuationComputation] using
        ih (SuccinctClose.bpCandidateMerge? left value)
  | adjacentLeft n macroStart rightCount outer ih =>
      simp [packedReviewerInteriorFinishCandidate,
        packedReviewerInteriorStartLocalTwo,
        packedReviewerInteriorStartLocalSpan,
        packedReviewerInteriorStartMinCandidate,
        packedReviewerInteriorReadNat,
        packedReviewerInteriorStateReference,
        packedReviewerInteriorCandidateContinuationComputation,
        packedReviewerInteriorNatContinuationComputation,
        packedReviewerInteriorNatStateReference_start,
        packedLocalTwoSpanCandidateComputation,
        packedLocalSpanCandidateComputation, packedMinCandidateComputation,
        packedSummaryComputation, ih, WordRAM.TraceResult.bind,
        List.append_assoc]
      split <;> simp_all [WordRAM.TraceResult.bind, List.append_assoc]
  | adjacentRight left outer ih =>
      simpa [packedReviewerInteriorFinishCandidate,
        packedReviewerInteriorCandidateContinuationComputation] using
        ih (SuccinctClose.bpCandidateMerge? left value)
  | leftMiddleLeft n macroStart middleCount outer ih =>
      simp [packedReviewerInteriorFinishCandidate,
        packedReviewerInteriorStartGlobalTwo,
        packedReviewerInteriorStartGlobalSpan,
        packedReviewerInteriorStartMinCandidate,
        packedReviewerInteriorReadNat,
        packedReviewerInteriorStateReference,
        packedReviewerInteriorCandidateContinuationComputation,
        packedReviewerInteriorNatContinuationComputation,
        packedReviewerInteriorNatStateReference_start,
        packedGlobalTwoSpanCandidateComputation,
        packedGlobalSpanCandidateComputation, packedMinCandidateComputation,
        packedSummaryComputation, ih, WordRAM.TraceResult.bind,
        List.append_assoc]
      split <;> simp_all [WordRAM.TraceResult.bind, List.append_assoc]
  | leftMiddleMiddle left outer ih =>
      simpa [packedReviewerInteriorFinishCandidate,
        packedReviewerInteriorCandidateContinuationComputation] using
        ih (SuccinctClose.bpCandidateMerge? left value)
  | crossLeft n macroStart middleCount rightCount outer ih =>
      simp [packedReviewerInteriorFinishCandidate,
        packedReviewerInteriorStartGlobalTwo,
        packedReviewerInteriorStartGlobalSpan,
        packedReviewerInteriorStartLocalTwo,
        packedReviewerInteriorStartLocalSpan,
        packedReviewerInteriorStartMinCandidate,
        packedReviewerInteriorReadNat,
        packedReviewerInteriorStateReference,
        packedReviewerInteriorCandidateContinuationComputation,
        packedReviewerInteriorNatContinuationComputation,
        packedReviewerInteriorNatStateReference_start,
        packedGlobalTwoSpanCandidateComputation,
        packedGlobalSpanCandidateComputation,
        packedLocalTwoSpanCandidateComputation,
        packedLocalSpanCandidateComputation, packedMinCandidateComputation,
        packedSummaryComputation, ih, WordRAM.TraceResult.bind,
        List.append_assoc]
      split <;> simp_all [WordRAM.TraceResult.bind, List.append_assoc]
  | crossMiddle n macroStart middleCount rightCount left outer ih =>
      simp [packedReviewerInteriorFinishCandidate,
        packedReviewerInteriorStartLocalTwo,
        packedReviewerInteriorStartLocalSpan,
        packedReviewerInteriorStartMinCandidate,
        packedReviewerInteriorReadNat,
        packedReviewerInteriorStateReference,
        packedReviewerInteriorCandidateContinuationComputation,
        packedReviewerInteriorNatContinuationComputation,
        packedReviewerInteriorNatStateReference_start,
        packedLocalTwoSpanCandidateComputation,
        packedLocalSpanCandidateComputation, packedMinCandidateComputation,
        packedSummaryComputation, ih, WordRAM.TraceResult.bind,
        List.append_assoc]
      split <;> simp_all [WordRAM.TraceResult.bind, List.append_assoc]
  | crossRight left middle outer ih =>
      simpa [packedReviewerInteriorFinishCandidate,
        packedReviewerInteriorCandidateContinuationComputation] using
        ih (SuccinctClose.bpCandidateMerge3? left middle value)

private theorem packedReviewerInteriorStateReference_finishNat
    (store : WordRAM.ReadStore) (invocation : PackedReviewerInvocation)
    (value : Option Nat)
    (continuation : PackedReviewerInteriorNatContinuation) :
    packedReviewerInteriorStateReference store
        (packedReviewerInteriorFinishNat invocation value continuation) =
      packedReviewerInteriorRunComputation store
        (packedReviewerInteriorNatContinuationComputation value
          continuation) := by
  cases continuation with
  | summaryBaseline n block outer =>
      simp [packedReviewerInteriorFinishNat,
        packedReviewerInteriorReadNat,
        packedReviewerInteriorStateReference,
        packedReviewerInteriorNatContinuationComputation,
        packedReviewerInteriorNatStateReference_start,
        WordRAM.TraceResult.bind, List.append_assoc]
  | summaryMin n block baseline outer =>
      simp [packedReviewerInteriorFinishNat,
        packedReviewerInteriorReadNat,
        packedReviewerInteriorStateReference,
        packedReviewerInteriorNatContinuationComputation,
        packedReviewerInteriorNatStateReference_start,
        WordRAM.TraceResult.bind, List.append_assoc]
  | summaryMax n block baseline minRel outer =>
      simp [packedReviewerInteriorFinishNat,
        packedReviewerInteriorReadNat,
        packedReviewerInteriorStateReference,
        packedReviewerInteriorNatContinuationComputation,
        packedReviewerInteriorNatStateReference_start,
        WordRAM.TraceResult.bind, List.append_assoc]
  | summaryArg n block baseline minRel maxRel outer =>
      simpa [packedReviewerInteriorFinishNat,
        packedReviewerInteriorNatContinuationComputation] using
        packedReviewerInteriorStateReference_finishCandidate store invocation
          ((match baseline, minRel, maxRel, value with
            | some b, some mn, some mx, some arg => some (b, mn, mx, arg)
            | _, _, _, _ => none).map
              (SuccinctClose.bpRelativeSummaryMinCandidate
                (packedInteriorLayout n).blockSize
                (packedInteriorLayout n).blocksPerSuper block)) outer
  | localOffset n macroIdx localStart level outer =>
      cases value with
      | none =>
          simpa [packedReviewerInteriorFinishNat,
            packedReviewerInteriorNatContinuationComputation] using
            packedReviewerInteriorStateReference_finishCandidate store
              invocation none outer
      | some offset =>
          simp [packedReviewerInteriorFinishNat,
            packedReviewerInteriorStartMinCandidate,
            packedReviewerInteriorReadNat,
            packedReviewerInteriorStateReference,
            packedReviewerInteriorNatContinuationComputation,
            packedReviewerInteriorCandidateContinuationComputation,
            packedReviewerInteriorNatStateReference_start,
            packedMinCandidateComputation, packedSummaryComputation,
            WordRAM.TraceResult.bind, List.append_assoc]
          constructor <;> rfl
  | globalBlock n macroStart level outer =>
      cases value with
      | none =>
          simpa [packedReviewerInteriorFinishNat,
            packedReviewerInteriorNatContinuationComputation] using
            packedReviewerInteriorStateReference_finishCandidate store
              invocation none outer
      | some block =>
          simp [packedReviewerInteriorFinishNat,
            packedReviewerInteriorStartMinCandidate,
            packedReviewerInteriorReadNat,
            packedReviewerInteriorStateReference,
            packedReviewerInteriorNatContinuationComputation,
            packedReviewerInteriorCandidateContinuationComputation,
            packedReviewerInteriorNatStateReference_start,
            packedMinCandidateComputation, packedSummaryComputation,
            WordRAM.TraceResult.bind, List.append_assoc]
          constructor <;> rfl
  | localLevel n macroIdx localStart count outer =>
      cases value with
      | none =>
          simpa [packedReviewerInteriorFinishNat,
            packedReviewerInteriorNatContinuationComputation] using
            packedReviewerInteriorStateReference_finishCandidate store
              invocation none outer
      | some encoded =>
          simp [packedReviewerInteriorFinishNat,
            packedReviewerInteriorStartLocalSpan,
            packedReviewerInteriorReadNat,
            packedReviewerInteriorStateReference,
            packedReviewerInteriorNatContinuationComputation,
            packedReviewerInteriorCandidateContinuationComputation,
            packedReviewerInteriorNatStateReference_start,
            packedLocalSpanCandidateComputation,
            packedMinCandidateComputation, packedSummaryComputation,
            packedReviewerInteriorStateReference_finishCandidate,
            WordRAM.TraceResult.bind, List.append_assoc]
          constructor <;>
            split <;> simp_all [WordRAM.TraceResult.bind, List.append_assoc]
  | globalLevel n macroStart macroSpanCount outer =>
      cases value with
      | none =>
          simpa [packedReviewerInteriorFinishNat,
            packedReviewerInteriorNatContinuationComputation] using
            packedReviewerInteriorStateReference_finishCandidate store
              invocation none outer
      | some encoded =>
          simp [packedReviewerInteriorFinishNat,
            packedReviewerInteriorStartGlobalSpan,
            packedReviewerInteriorReadNat,
            packedReviewerInteriorStateReference,
            packedReviewerInteriorNatContinuationComputation,
            packedReviewerInteriorCandidateContinuationComputation,
            packedReviewerInteriorNatStateReference_start,
            packedGlobalSpanCandidateComputation,
            packedMinCandidateComputation, packedSummaryComputation,
            packedReviewerInteriorStateReference_finishCandidate,
            WordRAM.TraceResult.bind, List.append_assoc]
          constructor <;>
            split <;> simp_all [WordRAM.TraceResult.bind, List.append_assoc]

private theorem packedReviewerInteriorNatStateReference_eq_pure_of_result_eq
    (store : WordRAM.ReadStore) (state : PackedReviewerInteriorNatState)
    (value : Option Nat)
    (hresult : packedReviewerInteriorNatResult state = some value) :
    packedReviewerInteriorNatStateReference store state =
      WordRAM.TraceResult.pure value := by
  cases state with
  | read invocation n start next remaining repliesRev =>
      simp [packedReviewerInteriorNatResult] at hresult
  | done result =>
      simp [packedReviewerInteriorNatResult] at hresult
      subst result
      rfl

private theorem packedReviewerInteriorStateReference_normalize
    (store : WordRAM.ReadStore) (fuel : Nat)
    (state : PackedReviewerInteriorState) :
    packedReviewerInteriorStateReference store
        (packedReviewerInteriorNormalize fuel state) =
      packedReviewerInteriorStateReference store state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      cases state with
      | done value => rfl
      | readNat invocation read continuation =>
          cases hresult : packedReviewerInteriorNatResult read with
          | none =>
              simp [packedReviewerInteriorNormalize, hresult]
          | some value =>
              have hread :=
                packedReviewerInteriorNatStateReference_eq_pure_of_result_eq
                  store read value hresult
              calc
                packedReviewerInteriorStateReference store
                    (packedReviewerInteriorNormalize (fuel + 1)
                      (.readNat invocation read continuation)) =
                  packedReviewerInteriorStateReference store
                    (packedReviewerInteriorNormalize fuel
                      (packedReviewerInteriorFinishNat invocation value
                        continuation)) := by
                          simp [packedReviewerInteriorNormalize, hresult]
                _ = packedReviewerInteriorStateReference store
                    (packedReviewerInteriorFinishNat invocation value
                      continuation) := ih _
                _ = packedReviewerInteriorRunComputation store
                    (packedReviewerInteriorNatContinuationComputation value
                      continuation) :=
                        packedReviewerInteriorStateReference_finishNat store
                          invocation value continuation
                _ = packedReviewerInteriorStateReference store
                    (.readNat invocation read continuation) := by
                      simp [packedReviewerInteriorStateReference, hread]

private def PackedReviewerInteriorWellFormed :
    PackedReviewerInteriorState -> Prop
  | .done _ => True
  | .readNat _ read _ =>
      packedReviewerInteriorNatResult read ≠ none ∨
        0 < packedReviewerInteriorNatRemaining read

private def PackedReviewerInteriorRunnable :
    PackedReviewerInteriorState -> Prop
  | .done _ => True
  | .readNat _ read _ =>
      packedReviewerInteriorNatResult read = none /\
        0 < packedReviewerInteriorNatRemaining read

private theorem packedReviewerInteriorNatStart_progress
    (invocation : PackedReviewerInvocation)
    (n entryCount width base index : Nat) :
    let state :=
      packedReviewerInteriorNatStart invocation n entryCount width base index
    packedReviewerInteriorNatResult state ≠ none ∨
      0 < packedReviewerInteriorNatRemaining state := by
  unfold packedReviewerInteriorNatStart
  by_cases hindex : index < entryCount
  · simp only [hindex, if_true]
    by_cases hcount :
        SuccinctSpace.fixedWidthNatTableMachineChunkCount width
            (packedBpCodeWordWidth n) = 0
    · simp [hcount, packedReviewerInteriorNatResult]
    · right
      simp [hcount, packedReviewerInteriorNatRemaining]
      omega
  · simp [hindex, packedReviewerInteriorNatRemaining]

private theorem packedReviewerInteriorReadNat_wellFormed
    (invocation : PackedReviewerInvocation)
    (n entryCount width base index : Nat)
    (continuation : PackedReviewerInteriorNatContinuation) :
    PackedReviewerInteriorWellFormed
      (packedReviewerInteriorReadNat invocation n entryCount width base index
        continuation) := by
  simpa [packedReviewerInteriorReadNat, PackedReviewerInteriorWellFormed] using
    packedReviewerInteriorNatStart_progress invocation n entryCount width base
      index

private theorem packedReviewerInteriorFinishCandidate_wellFormed
    (invocation : PackedReviewerInvocation)
    (value : PackedReviewerCandidate)
    (continuation : PackedReviewerCandidateContinuation) :
    PackedReviewerInteriorWellFormed
      (packedReviewerInteriorFinishCandidate invocation value continuation) := by
  induction continuation generalizing value with
  | finish =>
      simp [packedReviewerInteriorFinishCandidate,
        PackedReviewerInteriorWellFormed]
  | localTwoLeft n macroIdx localStart count encoded outer ih =>
      simp only [packedReviewerInteriorFinishCandidate]
      unfold packedReviewerInteriorStartLocalSpan
      exact packedReviewerInteriorReadNat_wellFormed _ _ _ _ _ _ _
  | localTwoRight left outer ih =>
      simpa [packedReviewerInteriorFinishCandidate] using
        ih (SuccinctClose.bpCandidateMerge? left value)
  | globalTwoLeft n macroStart macroSpanCount encoded outer ih =>
      simp only [packedReviewerInteriorFinishCandidate]
      unfold packedReviewerInteriorStartGlobalSpan
      exact packedReviewerInteriorReadNat_wellFormed _ _ _ _ _ _ _
  | globalTwoRight left outer ih =>
      simpa [packedReviewerInteriorFinishCandidate] using
        ih (SuccinctClose.bpCandidateMerge? left value)
  | adjacentLeft n macroStart rightCount outer ih =>
      simp only [packedReviewerInteriorFinishCandidate]
      unfold packedReviewerInteriorStartLocalTwo
      exact packedReviewerInteriorReadNat_wellFormed _ _ _ _ _ _ _
  | adjacentRight left outer ih =>
      simpa [packedReviewerInteriorFinishCandidate] using
        ih (SuccinctClose.bpCandidateMerge? left value)
  | leftMiddleLeft n macroStart middleCount outer ih =>
      simp only [packedReviewerInteriorFinishCandidate]
      unfold packedReviewerInteriorStartGlobalTwo
      exact packedReviewerInteriorReadNat_wellFormed _ _ _ _ _ _ _
  | leftMiddleMiddle left outer ih =>
      simpa [packedReviewerInteriorFinishCandidate] using
        ih (SuccinctClose.bpCandidateMerge? left value)
  | crossLeft n macroStart middleCount rightCount outer ih =>
      simp only [packedReviewerInteriorFinishCandidate]
      unfold packedReviewerInteriorStartGlobalTwo
      exact packedReviewerInteriorReadNat_wellFormed _ _ _ _ _ _ _
  | crossMiddle n macroStart middleCount rightCount left outer ih =>
      simp only [packedReviewerInteriorFinishCandidate]
      unfold packedReviewerInteriorStartLocalTwo
      exact packedReviewerInteriorReadNat_wellFormed _ _ _ _ _ _ _
  | crossRight left middle outer ih =>
      simpa [packedReviewerInteriorFinishCandidate] using
        ih (SuccinctClose.bpCandidateMerge3? left middle value)

private theorem packedReviewerInteriorFinishNat_wellFormed
    (invocation : PackedReviewerInvocation) (value : Option Nat)
    (continuation : PackedReviewerInteriorNatContinuation) :
    PackedReviewerInteriorWellFormed
      (packedReviewerInteriorFinishNat invocation value continuation) := by
  cases continuation with
  | summaryBaseline n block outer =>
      simp only [packedReviewerInteriorFinishNat]
      exact packedReviewerInteriorReadNat_wellFormed _ _ _ _ _ _ _
  | summaryMin n block baseline outer =>
      simp only [packedReviewerInteriorFinishNat]
      exact packedReviewerInteriorReadNat_wellFormed _ _ _ _ _ _ _
  | summaryMax n block baseline minRel outer =>
      simp only [packedReviewerInteriorFinishNat]
      exact packedReviewerInteriorReadNat_wellFormed _ _ _ _ _ _ _
  | summaryArg n block baseline minRel maxRel outer =>
      simp only [packedReviewerInteriorFinishNat]
      exact packedReviewerInteriorFinishCandidate_wellFormed _ _ _
  | localOffset n macroIdx localStart level outer =>
      cases value with
      | none =>
          simpa [packedReviewerInteriorFinishNat] using
            packedReviewerInteriorFinishCandidate_wellFormed invocation none
              outer
      | some offset =>
          simp only [packedReviewerInteriorFinishNat]
          unfold packedReviewerInteriorStartMinCandidate
          exact packedReviewerInteriorReadNat_wellFormed _ _ _ _ _ _ _
  | globalBlock n macroStart level outer =>
      cases value with
      | none =>
          simpa [packedReviewerInteriorFinishNat] using
            packedReviewerInteriorFinishCandidate_wellFormed invocation none
              outer
      | some block =>
          simp only [packedReviewerInteriorFinishNat]
          unfold packedReviewerInteriorStartMinCandidate
          exact packedReviewerInteriorReadNat_wellFormed _ _ _ _ _ _ _
  | localLevel n macroIdx localStart count outer =>
      cases value with
      | none =>
          simpa [packedReviewerInteriorFinishNat] using
            packedReviewerInteriorFinishCandidate_wellFormed invocation none
              outer
      | some encoded =>
          simp only [packedReviewerInteriorFinishNat]
          unfold packedReviewerInteriorStartLocalSpan
          exact packedReviewerInteriorReadNat_wellFormed _ _ _ _ _ _ _
  | globalLevel n macroStart macroSpanCount outer =>
      cases value with
      | none =>
          simpa [packedReviewerInteriorFinishNat] using
            packedReviewerInteriorFinishCandidate_wellFormed invocation none
              outer
      | some encoded =>
          simp only [packedReviewerInteriorFinishNat]
          unfold packedReviewerInteriorStartGlobalSpan
          exact packedReviewerInteriorReadNat_wellFormed _ _ _ _ _ _ _

private theorem packedReviewerInteriorNormalize_wellFormed
    (fuel : Nat) (state : PackedReviewerInteriorState)
    (hwellFormed : PackedReviewerInteriorWellFormed state) :
    PackedReviewerInteriorWellFormed
      (packedReviewerInteriorNormalize fuel state) := by
  induction fuel generalizing state with
  | zero => exact hwellFormed
  | succ fuel ih =>
      cases state with
      | done value => exact hwellFormed
      | readNat invocation read continuation =>
          cases hresult : packedReviewerInteriorNatResult read with
          | none =>
              simpa [packedReviewerInteriorNormalize, hresult] using hwellFormed
          | some value =>
              simp only [packedReviewerInteriorNormalize, hresult]
              exact ih _
                (packedReviewerInteriorFinishNat_wellFormed invocation value
                  continuation)

private theorem packedReviewerInteriorNormalize_ready
    (state : PackedReviewerInteriorState) :
    PackedReviewerInteriorReady
      (packedReviewerInteriorNormalize
        (packedReviewerInteriorRemaining state + 1) state) := by
  apply packedReviewerInteriorNormalize_ready_of_potential_lt
  cases state <;>
    simp [packedReviewerInteriorContinuationPotential,
      packedReviewerInteriorRemaining] <;> omega

private theorem packedReviewerInteriorRunnable_of_ready_of_wellFormed
    (state : PackedReviewerInteriorState)
    (hready : PackedReviewerInteriorReady state)
    (hwellFormed : PackedReviewerInteriorWellFormed state) :
    PackedReviewerInteriorRunnable state := by
  cases state with
  | done value => trivial
  | readNat invocation read continuation =>
      simp only [PackedReviewerInteriorReady] at hready
      simp only [PackedReviewerInteriorWellFormed] at hwellFormed
      simp only [PackedReviewerInteriorRunnable]
      refine And.intro hready ?_
      rcases hwellFormed with hfinished | hpositive
      · exact False.elim (hfinished hready)
      · exact hpositive

private theorem packedReviewerInteriorStartRaw_wellFormed
    (invocation : PackedReviewerInvocation)
    (n startBlock count : Nat) :
    PackedReviewerInteriorWellFormed
      (packedReviewerInteriorStartRaw invocation n startBlock count) := by
  unfold packedReviewerInteriorStartRaw
  by_cases hcount : count = 0
  · simp [hcount, PackedReviewerInteriorWellFormed]
  · simp only [hcount, if_false]
    by_cases hwithin :
        count <= (packedInteriorLayout n).macroSize -
          startBlock % (packedInteriorLayout n).macroSize
    · simp only [hwithin, if_true]
      unfold packedReviewerInteriorStartLocalTwo
      exact packedReviewerInteriorReadNat_wellFormed _ _ _ _ _ _ _
    · simp only [hwithin, if_false]
      by_cases hmiddle :
          (count -
              ((packedInteriorLayout n).macroSize -
                startBlock % (packedInteriorLayout n).macroSize)) /
            (packedInteriorLayout n).macroSize = 0
      · simp only [hmiddle, if_true]
        unfold packedReviewerInteriorStartLocalTwo
        exact packedReviewerInteriorReadNat_wellFormed _ _ _ _ _ _ _
      · simp only [hmiddle, if_false]
        by_cases hright :
            (count -
                ((packedInteriorLayout n).macroSize -
                  startBlock % (packedInteriorLayout n).macroSize)) %
              (packedInteriorLayout n).macroSize = 0
        · simp only [hright, if_true]
          unfold packedReviewerInteriorStartLocalTwo
          exact packedReviewerInteriorReadNat_wellFormed _ _ _ _ _ _ _
        · simp only [hright, if_false]
          unfold packedReviewerInteriorStartLocalTwo
          exact packedReviewerInteriorReadNat_wellFormed _ _ _ _ _ _ _

private theorem packedReviewerInteriorStart_runnable
    (invocation : PackedReviewerInvocation)
    (n startBlock count : Nat) :
    PackedReviewerInteriorRunnable
      (packedReviewerInteriorStart invocation n startBlock count) := by
  let raw := packedReviewerInteriorStartRaw invocation n startBlock count
  have hready := packedReviewerInteriorNormalize_ready raw
  have hwellFormed := packedReviewerInteriorNormalize_wellFormed
    (packedReviewerInteriorRemaining raw + 1) raw
    (packedReviewerInteriorStartRaw_wellFormed invocation n startBlock count)
  exact packedReviewerInteriorRunnable_of_ready_of_wellFormed _ hready
    hwellFormed

private theorem packedReviewerDriveInterior_state_simulates_of_length
    (store : WordRAM.ReadStore) (fuel : Nat) :
    forall state : PackedReviewerInteriorState,
      PackedReviewerInteriorRunnable state ->
      (packedReviewerInteriorStateReference store state).trace.length = fuel ->
      (packedReviewerDriveInterior store fuel state).Simulates
        (packedReviewerInteriorStateReference store state)
        PackedReviewerInteriorState.done := by
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    intro state hrunnable hfuel
    cases state with
  | done value =>
      simp [packedReviewerInteriorStateReference,
        WordRAM.TraceResult.pure] at hfuel
      have hzero : fuel = 0 := by omega
      subst fuel
      simp [packedReviewerInteriorStateReference,
        packedReviewerDriveInterior, packedReviewerDriveComponent,
        packedReviewerInteriorResult, PackedReviewerComponentRun.Simulates,
        WordRAM.TraceResult.pure]
  | readNat invocation read continuation =>
      simp only [PackedReviewerInteriorRunnable] at hrunnable
      rcases hrunnable with ⟨hreadResult, hpositive⟩
      cases read with
      | done value =>
          simp [packedReviewerInteriorNatResult] at hreadResult
      | read childInvocation n start next remaining repliesRev =>
          let readState : PackedReviewerInteriorNatState :=
            .read childInvocation n start next remaining repliesRev
          let readReference :=
            packedReviewerInteriorNatReference store start next remaining
              repliesRev
          let continuationReference :=
            packedReviewerInteriorRunComputation store
              (packedReviewerInteriorNatContinuationComputation
                readReference.value continuation)
          let nextState :=
            packedReviewerInteriorFinishNat invocation readReference.value
              continuation
          let ready :=
            packedReviewerInteriorNormalize
              (packedReviewerInteriorRemaining nextState + 1) nextState
          have hremaining : 0 < remaining := by
            simpa [readState, packedReviewerInteriorNatRemaining] using hpositive
          have hread :
              (packedReviewerDriveInteriorNat store remaining readState).Simulates
                readReference PackedReviewerInteriorNatState.done := by
            simpa [readState, readReference] using
              packedReviewerDriveInteriorNatFrom_pos_simulates store
                childInvocation n start next remaining repliesRev hremaining
          have hreadyReference :
              packedReviewerInteriorStateReference store ready =
                continuationReference := by
            calc
              packedReviewerInteriorStateReference store ready =
                  packedReviewerInteriorStateReference store nextState := by
                    exact packedReviewerInteriorStateReference_normalize store
                      (packedReviewerInteriorRemaining nextState + 1) nextState
              _ = packedReviewerInteriorRunComputation store
                    (packedReviewerInteriorNatContinuationComputation
                      readReference.value continuation) :=
                    packedReviewerInteriorStateReference_finishNat store
                      invocation readReference.value continuation
              _ = continuationReference := rfl
          have hreadyWellFormed : PackedReviewerInteriorWellFormed ready := by
            apply packedReviewerInteriorNormalize_wellFormed
            exact packedReviewerInteriorFinishNat_wellFormed invocation
              readReference.value continuation
          have hreadyRunnable : PackedReviewerInteriorRunnable ready :=
            packedReviewerInteriorRunnable_of_ready_of_wellFormed ready
              (packedReviewerInteriorNormalize_ready nextState)
              hreadyWellFormed
          have hreadLength : readReference.trace.length = remaining := by
            exact packedReviewerInteriorNatReference_trace_length store start
              next remaining repliesRev
          have houterLength :
              (packedReviewerInteriorStateReference store
                (.readNat invocation readState continuation)).trace.length =
                  readReference.trace.length +
                    continuationReference.trace.length := by
            simp [packedReviewerInteriorStateReference,
              packedReviewerInteriorNatStateReference, readState,
              readReference, continuationReference, WordRAM.TraceResult.bind]
          have hfuel' :
              (packedReviewerInteriorStateReference store
                (.readNat invocation readState continuation)).trace.length =
                  fuel := by
            simpa [readState] using hfuel
          have hreadyLength :
              (packedReviewerInteriorStateReference store ready).trace.length =
                continuationReference.trace.length :=
            congrArg (fun result => result.trace.length) hreadyReference
          have hcontinuationLess :
              continuationReference.trace.length < fuel := by
            rw [← hfuel', houterLength, hreadLength]
            omega
          have hcontinuation :=
            ih continuationReference.trace.length hcontinuationLess ready
              hreadyRunnable hreadyLength
          have hcontinuation' :
              (packedReviewerDriveInterior store
                continuationReference.trace.length ready).Simulates
                  continuationReference PackedReviewerInteriorState.done := by
            simpa [hreadyReference] using hcontinuation
          have hsplice :=
            packedReviewerDriveInterior_readNat_splice store invocation readState
              continuation continuationReference.trace.length readReference
              (fun value =>
                packedReviewerInteriorRunComputation store
                  (packedReviewerInteriorNatContinuationComputation value
                    continuation)) (by rfl) hread (by
                simpa [nextState, ready, continuationReference] using
                  hcontinuation')
          have hfuelDecomp :
              fuel = remaining + continuationReference.trace.length := by
            rw [← hfuel', houterLength, hreadLength]
          simpa [packedReviewerInteriorStateReference,
            packedReviewerInteriorNatStateReference, readState, readReference,
            continuationReference, WordRAM.TraceResult.bind, hreadLength,
            hfuelDecomp] using hsplice

private theorem packedReviewerDriveInterior_state_simulates
    (store : WordRAM.ReadStore) (state : PackedReviewerInteriorState)
    (hrunnable : PackedReviewerInteriorRunnable state) :
    let reference := packedReviewerInteriorStateReference store state
    (packedReviewerDriveInterior store reference.trace.length state).Simulates
      reference PackedReviewerInteriorState.done := by
  simpa using
    packedReviewerDriveInterior_state_simulates_of_length store
      (packedReviewerInteriorStateReference store state).trace.length state
      hrunnable rfl

private theorem packedReviewerInteriorStateReference_startRaw
    (store : WordRAM.ReadStore) (invocation : PackedReviewerInvocation)
    (n startBlock count : Nat) :
    packedReviewerInteriorStateReference store
        (packedReviewerInteriorStartRaw invocation n startBlock count) =
      packedReviewerInteriorRunComputation store
        (packedInteriorRangeMinComputation n startBlock count) := by
  unfold packedReviewerInteriorStartRaw packedInteriorRangeMinComputation
  by_cases hcount : count = 0
  · simp [hcount, packedReviewerInteriorStateReference]
  · simp only [hcount, if_false]
    by_cases hwithin :
        count <= (packedInteriorLayout n).macroSize -
          startBlock % (packedInteriorLayout n).macroSize
    · simp only [hwithin, if_true]
      simp [packedReviewerInteriorStartLocalTwo,
        packedReviewerInteriorReadNat,
        packedReviewerInteriorStateReference,
        packedReviewerInteriorNatStateReference_start,
        packedReviewerInteriorNatContinuationComputation,
        packedReviewerInteriorCandidateContinuationComputation,
        packedLocalTwoSpanCandidateComputation,
        packedLocalSpanCandidateComputation, packedMinCandidateComputation,
        packedSummaryComputation, WordRAM.TraceResult.bind,
        List.append_assoc]
      split <;> simp_all [WordRAM.TraceResult.bind, List.append_assoc]
    · simp only [hwithin, if_false]
      by_cases hmiddle :
          (count -
              ((packedInteriorLayout n).macroSize -
                startBlock % (packedInteriorLayout n).macroSize)) /
            (packedInteriorLayout n).macroSize = 0
      · simp only [hmiddle, if_true]
        simp [packedReviewerInteriorStartLocalTwo,
          packedReviewerInteriorReadNat,
          packedReviewerInteriorStateReference,
          packedReviewerInteriorNatStateReference_start,
          packedReviewerInteriorNatContinuationComputation,
          packedReviewerInteriorCandidateContinuationComputation,
          packedAdjacentMacroCandidateComputation,
          packedLocalTwoSpanCandidateComputation,
          packedLocalSpanCandidateComputation, packedMinCandidateComputation,
          packedSummaryComputation, WordRAM.TraceResult.bind,
          List.append_assoc]
        split <;> simp_all [WordRAM.TraceResult.bind, List.append_assoc]
      · simp only [hmiddle, if_false]
        by_cases hright :
            (count -
                ((packedInteriorLayout n).macroSize -
                  startBlock % (packedInteriorLayout n).macroSize)) %
              (packedInteriorLayout n).macroSize = 0
        · simp only [hright, if_true]
          simp [packedReviewerInteriorStartLocalTwo,
            packedReviewerInteriorReadNat,
            packedReviewerInteriorStateReference,
            packedReviewerInteriorNatStateReference_start,
            packedReviewerInteriorNatContinuationComputation,
            packedReviewerInteriorCandidateContinuationComputation,
            packedLeftMiddleMacroCandidateComputation,
            packedLocalTwoSpanCandidateComputation,
            packedGlobalTwoSpanCandidateComputation,
            packedLocalSpanCandidateComputation,
            packedGlobalSpanCandidateComputation,
            packedMinCandidateComputation, packedSummaryComputation,
            WordRAM.TraceResult.bind, List.append_assoc]
          split <;> simp_all [WordRAM.TraceResult.bind, List.append_assoc]
        · simp only [hright, if_false]
          simp [packedReviewerInteriorStartLocalTwo,
            packedReviewerInteriorReadNat,
            packedReviewerInteriorStateReference,
            packedReviewerInteriorNatStateReference_start,
            packedReviewerInteriorNatContinuationComputation,
            packedReviewerInteriorCandidateContinuationComputation,
            packedCrossMacroCandidateComputation,
            packedLocalTwoSpanCandidateComputation,
            packedGlobalTwoSpanCandidateComputation,
            packedLocalSpanCandidateComputation,
            packedGlobalSpanCandidateComputation,
            packedMinCandidateComputation, packedSummaryComputation,
            WordRAM.TraceResult.bind, List.append_assoc]
          split <;> simp_all [WordRAM.TraceResult.bind, List.append_assoc]

private theorem packedReviewerInteriorStateReference_start
    (store : WordRAM.ReadStore) (invocation : PackedReviewerInvocation)
    (n startBlock count : Nat) :
    packedReviewerInteriorStateReference store
        (packedReviewerInteriorStart invocation n startBlock count) =
      packedReviewerInteriorRunComputation store
        (packedInteriorRangeMinComputation n startBlock count) := by
  unfold packedReviewerInteriorStart
  rw [packedReviewerInteriorStateReference_normalize]
  exact packedReviewerInteriorStateReference_startRaw store invocation n
    startBlock count

private theorem packedReviewerInteriorStateReference_start_eq_read
    (store : WordRAM.ReadStore) (invocation : PackedReviewerInvocation)
    (n startBlock count : Nat) :
    packedReviewerInteriorStateReference store
        (packedReviewerInteriorStart invocation n startBlock count) =
      packedInteriorRangeMinRead concreteBPNativeInteriorTraceSegments store n
        startBlock count := by
  rw [packedReviewerInteriorStateReference_start]
  rfl

private theorem packedReviewerDriveInterior_exact_simulates
    (store : WordRAM.ReadStore) (invocation : PackedReviewerInvocation)
    (n startBlock count : Nat) :
    let state :=
      packedReviewerInteriorStart invocation n startBlock count
    let reference :=
      packedInteriorRangeMinRead concreteBPNativeInteriorTraceSegments store n
        startBlock count
    (packedReviewerDriveInterior store reference.trace.length state).Simulates
      reference PackedReviewerInteriorState.done := by
  let state := packedReviewerInteriorStart invocation n startBlock count
  let reference :=
    packedInteriorRangeMinRead concreteBPNativeInteriorTraceSegments store n
      startBlock count
  have hrun := packedReviewerDriveInterior_state_simulates store state
    (packedReviewerInteriorStart_runnable invocation n startBlock count)
  have href : packedReviewerInteriorStateReference store state = reference := by
    exact packedReviewerInteriorStateReference_start_eq_read store invocation n
      startBlock count
  simpa [href, state, reference] using hrun

private theorem packedInteriorRangeMinRead_canonical_trace_length_le_33
    (shape : Cartesian.CartesianShape) (hsize : 4 <= shape.size)
    (startBlock count : Nat)
    (hbound : startBlock + count <=
      (packedInteriorLayout shape.size).blockCount) :
    (packedInteriorRangeMinRead concreteBPNativeInteriorTraceSegments
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) shape.size startBlock
      count).trace.length <= 33 := by
  rw [← packedInteriorRangeMinRead_eq shape
    concreteBPNativeInteriorTraceSegments
    (concreteBPNativeSuccinctRMQGlobalReadStore shape) startBlock count]
  rw [← WordRAM.TraceResult.toCosted_cost_eq_trace_length]
  rw [SuccinctClose.ConcreteCompactBPCloseLCADirectory.concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore_refines_of_agree
    shape concreteBPNativeInteriorTraceSegments
    (concreteBPNativeSuccinctRMQGlobalReadStore_canonicalComponent shape)
    startBlock count]
  change
    (SuccinctClose.canonicalRelativeRmmInteriorRangeMinCostedWithStore shape
      (SuccinctClose.canonicalRelativeRmmInteriorComponentStore
        shape).store.words startBlock count).cost <= 33
  rw [SuccinctClose.canonicalRelativeRmmInteriorRangeMinCostedWithStore_eq_current]
  exact
    SuccinctClose.canonicalRelativeRmmInteriorRangeMinCosted_cost_le_thirty_three_literal_of_size_ge_four_of_bounded
      shape hsize startBlock count (by
        simpa [packedInteriorLayout_eq] using hbound)

private theorem packedReviewerDriveInterior_simulates
    (shape : Cartesian.CartesianShape)
    (invocation : PackedReviewerInvocation)
    (startBlock count : Nat) (hsize : 4 <= shape.size)
    (hbound : startBlock + count <=
      (packedInteriorLayout shape.size).blockCount) :
    let store := concreteBPNativeSuccinctRMQGlobalReadStore shape
    let state :=
      packedReviewerInteriorStart invocation shape.size startBlock count
    let reference :=
      packedInteriorRangeMinRead concreteBPNativeInteriorTraceSegments store
        shape.size startBlock count
    (packedReviewerDriveInterior store 33 state).Simulates reference
      PackedReviewerInteriorState.done := by
  let store := concreteBPNativeSuccinctRMQGlobalReadStore shape
  let state :=
    packedReviewerInteriorStart invocation shape.size startBlock count
  let reference :=
    packedInteriorRangeMinRead concreteBPNativeInteriorTraceSegments store
      shape.size startBlock count
  have hexact := packedReviewerDriveInterior_exact_simulates store invocation
    shape.size startBlock count
  have hlength : reference.trace.length <= 33 := by
    exact packedInteriorRangeMinRead_canonical_trace_length_le_33 shape hsize
      startBlock count hbound
  have hpad :=
    packedReviewerDriveComponent_add_fuel_of_simulates
      packedReviewerInteriorResult packedReviewerInteriorNextRequest
      packedReviewerInteriorConsumeReply store reference.trace.length
      (33 - reference.trace.length) state reference
      PackedReviewerInteriorState.done (by simpa [store, state, reference] using
        hexact)
  have hfuel : reference.trace.length + (33 - reference.trace.length) = 33 :=
    Nat.add_sub_of_le hlength
  simpa [packedReviewerDriveInterior, hfuel, store, state, reference] using hpad

/-! ## Close/LCA phase splices -/

private theorem packedReviewerDriveFringe_fixed_simulates
    (store : WordRAM.ReadStore) (invocation : PackedReviewerInvocation)
    (n : Nat) (window : List Bool) (seed relLo relHi count fuel : Nat)
    (hcount : count <= fuel) :
    let state :=
      packedReviewerFringeStart invocation n window seed relLo relHi count
    let reference :=
      SuccinctClose.bpFringeChunkFoldTraceResultAtSegmentWithStore store 21
        (packedFringeChunkBits n) window seed relLo relHi count
    (packedReviewerDriveFringe store fuel state).Simulates reference
      PackedReviewerFringeState.done := by
  let state :=
    packedReviewerFringeStart invocation n window seed relLo relHi count
  let reference :=
    SuccinctClose.bpFringeChunkFoldTraceResultAtSegmentWithStore store 21
      (packedFringeChunkBits n) window seed relLo relHi count
  have hexact :=
    packedReviewerDriveFringe_simulates store invocation n window seed relLo
      relHi count
  have hremaining : packedReviewerFringeRemaining state <= fuel := by
    by_cases hzero : count = 0
    · simp [state, packedReviewerFringeStart, packedReviewerFringeRemaining,
        hzero]
    · simpa [state, packedReviewerFringeStart, hzero] using hcount
  have hpad :=
    packedReviewerDriveComponent_add_fuel_of_simulates
      packedReviewerFringeResult packedReviewerFringeNextRequest
      packedReviewerFringeConsumeReply store
      (packedReviewerFringeRemaining state)
      (fuel - packedReviewerFringeRemaining state) state reference
      PackedReviewerFringeState.done (by
        simpa [packedReviewerDriveFringe, state, reference] using hexact)
  have hfuel :
      packedReviewerFringeRemaining state +
          (fuel - packedReviewerFringeRemaining state) = fuel :=
    Nat.add_sub_of_le hremaining
  simpa [packedReviewerDriveFringe, hfuel, state, reference] using hpad

private theorem packedReviewerDriveLca_sameFringe_simulates
    (store : WordRAM.ReadStore) (invocation : PackedReviewerInvocation)
    (n leftClose rightClose seed base start : Nat) (window : List Bool)
    (relLo relHi count : Nat) (hpositive : 0 < count)
    (hcount : count <= 33) :
    let fringe :=
      packedReviewerFringeStart invocation n window seed relLo relHi count
    let reference :=
      SuccinctClose.bpFringeChunkFoldTraceResultAtSegmentWithStore store 21
        (packedFringeChunkBits n) window seed relLo relHi count
    (packedReviewerDriveLca store 33
      (.sameFringe invocation n leftClose rightClose seed base start
        fringe)).Simulates
      (WordRAM.TraceResult.map
        (packedReviewerLcaFinishSameFringe base seed start) reference)
      PackedReviewerLcaState.done := by
  let fringe :=
    packedReviewerFringeStart invocation n window seed relLo relHi count
  let reference :=
    SuccinctClose.bpFringeChunkFoldTraceResultAtSegmentWithStore store 21
      (packedFringeChunkBits n) window seed relLo relHi count
  have hfringe :=
    packedReviewerDriveFringe_fixed_simulates store invocation n window seed
      relLo relHi count 33 hcount
  have hdone : packedReviewerFringeResult fringe = none := by
    simp [fringe, packedReviewerFringeStart, Nat.ne_of_gt hpositive,
      packedReviewerFringeResult]
  apply packedReviewerDriveComponent_embedded_phase_simulates
    packedReviewerFringeResult packedReviewerFringeNextRequest
    packedReviewerFringeConsumeReply packedReviewerLcaResult
    packedReviewerLcaNextRequest packedReviewerLcaConsumeReply
    (fun child =>
      .sameFringe invocation n leftClose rightClose seed base start child)
    (fun fold =>
      .done (packedReviewerLcaFinishSameFringe base seed start fold))
    PackedReviewerFringeState.done PackedReviewerLcaState.done
    store 33 0 fringe reference
    (fun fold => WordRAM.TraceResult.pure
      (packedReviewerLcaFinishSameFringe base seed start fold))
  · exact hdone
  · simpa [packedReviewerDriveFringe, fringe, reference] using hfringe
  · simp [packedReviewerDriveLca, packedReviewerDriveComponent,
      PackedReviewerComponentRun.Simulates, packedReviewerLcaResult,
      WordRAM.TraceResult.pure]
  · intro state hstate
    cases state <;>
      simp [packedReviewerFringeResult, packedReviewerLcaResult] at hstate ⊢
  · intro state hstate
    cases state <;>
      simp [packedReviewerFringeResult, packedReviewerFringeNextRequest,
        packedReviewerLcaNextRequest] at hstate ⊢
  · intro state reply hstate
    cases state <;>
      simp [packedReviewerFringeResult, packedReviewerFringeConsumeReply,
        packedReviewerLcaConsumeReply] at hstate ⊢ <;>
      split <;> simp_all [packedReviewerFringeResult]

private theorem packedReviewerDriveLca_sameWindow_simulates
    (store : WordRAM.ReadStore) (invocation : PackedReviewerInvocation)
    (n leftClose rightClose seed : Nat) :
    let blockSize := packedSummaryBlockSizeRaw n
    let state : PackedReviewerLcaState :=
      .sameWindow invocation n leftClose rightClose seed
        (packedReviewerBPWindowStart invocation n blockSize leftClose)
    let reference :=
      packedSameBlockCloseSeededRead store 21
        (packedLocalBPWindowBitsRead store n blockSize leftClose)
        n blockSize leftClose rightClose seed
    (packedReviewerDriveLca store 37 state).Simulates reference
      PackedReviewerLcaState.done := by
  let blockSize := packedSummaryBlockSizeRaw n
  let base := packedLocalBPWindowBase n blockSize leftClose
  let start := leftClose + 1
  let relLo := start - base
  let relHi :=
    leftClose + 1 + (rightClose - leftClose + 1) - 1 - base
  let count := Nat.min (relHi / packedFringeChunkBits n + 1) 33
  let windowState :=
    packedReviewerBPWindowStart invocation n blockSize leftClose
  let windowReference :=
    packedLocalBPWindowBitsRead store n blockSize leftClose
  let continuation : List Bool -> WordRAM.TraceResult (Option Nat) :=
    fun window =>
      WordRAM.TraceResult.map
        (packedReviewerLcaFinishSameFringe base seed start)
        (SuccinctClose.bpFringeChunkFoldTraceResultAtSegmentWithStore store 21
          (packedFringeChunkBits n) window seed relLo relHi count)
  have hpositive : 0 < count := by
    exact Nat.lt_min.mpr ⟨Nat.zero_lt_succ _, by decide⟩
  have hcount : count <= 33 := Nat.min_le_right _ _
  have hwindow :=
    packedReviewerDriveBPWindow_simulates store invocation n blockSize
      leftClose
  have hfringe :=
    packedReviewerDriveLca_sameFringe_simulates store invocation n leftClose
      rightClose seed base start windowReference.value relLo relHi count
      hpositive hcount
  have hsplice :=
    packedReviewerDriveComponent_embedded_phase_simulates
      packedReviewerBPWindowResult packedReviewerBPWindowNextRequest
      packedReviewerBPWindowConsumeReply packedReviewerLcaResult
      packedReviewerLcaNextRequest packedReviewerLcaConsumeReply
      (fun child =>
        .sameWindow invocation n leftClose rightClose seed child)
      (packedReviewerLcaStartSameFringe invocation n leftClose rightClose seed)
      PackedReviewerBPWindowState.done PackedReviewerLcaState.done
      store 4 33 windowState windowReference continuation
      (by rfl)
      (by simpa [packedReviewerDriveBPWindow, windowState, windowReference]
        using hwindow)
      (by
        simpa [packedReviewerLcaStartSameFringe, blockSize, base, start,
          relLo, relHi, count, continuation, windowReference] using hfringe)
      (by
        intro state _
        rfl)
      (by
        intro state _
        rfl)
      (by
        intro state reply _
        change
          (match packedReviewerBPWindowResult
              (packedReviewerBPWindowConsumeReply state reply) with
            | some bits =>
                packedReviewerLcaStartSameFringe invocation n leftClose
                  rightClose seed bits
            | none =>
                .sameWindow invocation n leftClose rightClose seed
                  (packedReviewerBPWindowConsumeReply state reply)) = _
        split <;> simp_all)
  simpa [blockSize, base, start, relLo, relHi, count, windowState,
    windowReference, continuation, packedSameBlockCloseSeededRead,
    WordRAM.TraceResult.bind, WordRAM.TraceResult.map] using hsplice

private theorem packedReviewerDriveLca_sameSeed_simulates
    (store : WordRAM.ReadStore) (invocation : PackedReviewerInvocation)
    (n leftClose rightClose : Nat) :
    let blockSize := packedSummaryBlockSizeRaw n
    let seedPos := packedLocalBPWindowBase n blockSize leftClose
    let state : PackedReviewerLcaState :=
      .sameSeed invocation n leftClose rightClose
        (packedReviewerLcaRankStart invocation n seedPos)
    let reference :=
      packedSameBlockCloseDecodedRead store (packedRankCloseLeaf store n) 21
        n blockSize leftClose rightClose
    (packedReviewerDriveLca store 48 state).Simulates reference
      PackedReviewerLcaState.done := by
  let blockSize := packedSummaryBlockSizeRaw n
  let seedPos := packedLocalBPWindowBase n blockSize leftClose
  let rankState := packedReviewerLcaRankStart invocation n seedPos
  let rankReference := packedRankCloseLeaf store n seedPos
  let continuation : Nat -> WordRAM.TraceResult (Option Nat) :=
    fun rankFalse =>
      let seed := packedReviewerLcaSeed n blockSize leftClose rankFalse
      packedSameBlockCloseSeededRead store 21
        (packedLocalBPWindowBitsRead store n blockSize leftClose)
        n blockSize leftClose rightClose seed
  have hrank :=
    packedReviewerDriveRank_simulates store invocation .close n seedPos
  have hwindow :=
    packedReviewerDriveLca_sameWindow_simulates store invocation n leftClose
      rightClose
      (packedReviewerLcaSeed n blockSize leftClose rankReference.value)
  have hsplice :=
    packedReviewerDriveComponent_embedded_phase_simulates
      packedReviewerRankResult packedReviewerRankNextRequest
      packedReviewerRankConsumeReply packedReviewerLcaResult
      packedReviewerLcaNextRequest packedReviewerLcaConsumeReply
      (fun child => .sameSeed invocation n leftClose rightClose child)
      (packedReviewerLcaStartSameWindow invocation n leftClose rightClose)
      PackedReviewerRankState.done PackedReviewerLcaState.done
      store 11 37 rankState rankReference continuation
      (by rfl)
      (by
        simpa [packedReviewerDriveRank, packedReviewerLcaRankStart, rankState,
          rankReference, packedRankCloseLeaf, packedRankCloseRead] using hrank)
      (by
        simpa [continuation, packedReviewerLcaStartSameWindow, blockSize]
          using hwindow)
      (by
        intro state _
        rfl)
      (by
        intro state _
        rfl)
      (by
        intro state reply _
        change
          (match packedReviewerRankResult
              (packedReviewerRankConsumeReply state reply) with
            | some rankFalse =>
                packedReviewerLcaStartSameWindow invocation n leftClose
                  rightClose rankFalse
            | none =>
                .sameSeed invocation n leftClose rightClose
                  (packedReviewerRankConsumeReply state reply)) = _
        split <;> simp_all)
  simpa [blockSize, seedPos, rankState, rankReference, continuation,
    packedSameBlockCloseDecodedRead, packedLocalBPSeed,
    packedReviewerLcaSeed, WordRAM.TraceResult.bind, WordRAM.TraceResult.map]
    using hsplice

private theorem packedReviewerDriveLca_rightFringe_simulates
    (store : WordRAM.ReadStore) (invocation : PackedReviewerInvocation)
    (n leftClose rightClose seed base start : Nat)
    (left middle : PackedReviewerCandidate) (window : List Bool)
    (relLo relHi count : Nat) (hpositive : 0 < count)
    (hcount : count <= 33) :
    let fringe :=
      packedReviewerFringeStart invocation n window seed relLo relHi count
    let reference :=
      SuccinctClose.bpFringeChunkFoldTraceResultAtSegmentWithStore store 21
        (packedFringeChunkBits n) window seed relLo relHi count
    (packedReviewerDriveLca store 33
      (.rightFringe invocation n leftClose rightClose seed base start left
        middle fringe)).Simulates
      (WordRAM.TraceResult.map
        (fun fold =>
          SuccinctClose.bpCandidateClose?
            (SuccinctClose.bpCandidateMerge3? left middle
              (SuccinctClose.bpFringeCandGlobal base seed start fold.2)))
        reference)
      PackedReviewerLcaState.done := by
  let fringe :=
    packedReviewerFringeStart invocation n window seed relLo relHi count
  let reference :=
    SuccinctClose.bpFringeChunkFoldTraceResultAtSegmentWithStore store 21
      (packedFringeChunkBits n) window seed relLo relHi count
  let finish : Nat × Option (Nat × Nat) -> Option Nat :=
    fun fold =>
      SuccinctClose.bpCandidateClose?
        (SuccinctClose.bpCandidateMerge3? left middle
          (SuccinctClose.bpFringeCandGlobal base seed start fold.2))
  have hfringe :=
    packedReviewerDriveFringe_fixed_simulates store invocation n window seed
      relLo relHi count 33 hcount
  have hdone : packedReviewerFringeResult fringe = none := by
    simp [fringe, packedReviewerFringeStart, Nat.ne_of_gt hpositive,
      packedReviewerFringeResult]
  apply packedReviewerDriveComponent_embedded_phase_simulates
    packedReviewerFringeResult packedReviewerFringeNextRequest
    packedReviewerFringeConsumeReply packedReviewerLcaResult
    packedReviewerLcaNextRequest packedReviewerLcaConsumeReply
    (fun child =>
      .rightFringe invocation n leftClose rightClose seed base start left
        middle child)
    (fun fold => .done (finish fold))
    PackedReviewerFringeState.done PackedReviewerLcaState.done
    store 33 0 fringe reference
    (fun fold => WordRAM.TraceResult.pure (finish fold))
  · exact hdone
  · simpa [packedReviewerDriveFringe, fringe, reference] using hfringe
  · simp [packedReviewerDriveLca, packedReviewerDriveComponent,
      PackedReviewerComponentRun.Simulates, packedReviewerLcaResult,
      WordRAM.TraceResult.pure]
  · intro state _
    rfl
  · intro state _
    rfl
  · intro state reply _
    change
      (match packedReviewerFringeResult
          (packedReviewerFringeConsumeReply state reply) with
        | some fold => PackedReviewerLcaState.done (finish fold)
        | none =>
            PackedReviewerLcaState.rightFringe invocation n leftClose
              rightClose seed base start left middle
              (packedReviewerFringeConsumeReply state reply)) = _
    split <;> simp_all

private theorem packedReviewerDriveLca_rightWindow_simulates
    (store : WordRAM.ReadStore) (invocation : PackedReviewerInvocation)
    (n leftClose rightClose seed : Nat)
    (left middle : PackedReviewerCandidate) :
    let blockSize := packedSummaryBlockSizeRaw n
    let state : PackedReviewerLcaState :=
      .rightWindow invocation n leftClose rightClose seed left middle
        (packedReviewerBPWindowStart invocation n blockSize rightClose)
    let reference :=
      WordRAM.TraceResult.map
        (fun right =>
          SuccinctClose.bpCandidateClose?
            (SuccinctClose.bpCandidateMerge3? left middle right))
        (packedRightFringeCandidateRead store 21 n blockSize rightClose seed)
    (packedReviewerDriveLca store 37 state).Simulates reference
      PackedReviewerLcaState.done := by
  let blockSize := packedSummaryBlockSizeRaw n
  let base := packedLocalBPWindowBase n blockSize rightClose
  let start :=
    SuccinctClose.blockStartOf blockSize
      (SuccinctClose.blockOfClose blockSize rightClose)
  let span := rightClose - start + 2
  let relLo := start - base
  let relHi := start + span - 1 - base
  let count := Nat.min (relHi / packedFringeChunkBits n + 1) 33
  let windowState :=
    packedReviewerBPWindowStart invocation n blockSize rightClose
  let windowReference :=
    packedLocalBPWindowBitsRead store n blockSize rightClose
  let finish : PackedReviewerCandidate -> Option Nat :=
    fun right =>
      SuccinctClose.bpCandidateClose?
        (SuccinctClose.bpCandidateMerge3? left middle right)
  let continuation : List Bool -> WordRAM.TraceResult (Option Nat) :=
    fun window =>
      WordRAM.TraceResult.map
        (fun fold =>
          finish (SuccinctClose.bpFringeCandGlobal base seed start fold.2))
        (SuccinctClose.bpFringeChunkFoldTraceResultAtSegmentWithStore store 21
          (packedFringeChunkBits n) window seed relLo relHi count)
  have hpositive : 0 < count := by
    exact Nat.lt_min.mpr ⟨Nat.zero_lt_succ _, by decide⟩
  have hcount : count <= 33 := Nat.min_le_right _ _
  have hwindow :=
    packedReviewerDriveBPWindow_simulates store invocation n blockSize
      rightClose
  have hfringe :=
    packedReviewerDriveLca_rightFringe_simulates store invocation n leftClose
      rightClose seed base start left middle windowReference.value relLo relHi
      count hpositive hcount
  have hsplice :=
    packedReviewerDriveComponent_embedded_phase_simulates
      packedReviewerBPWindowResult packedReviewerBPWindowNextRequest
      packedReviewerBPWindowConsumeReply packedReviewerLcaResult
      packedReviewerLcaNextRequest packedReviewerLcaConsumeReply
      (fun child =>
        .rightWindow invocation n leftClose rightClose seed left middle child)
      (packedReviewerLcaStartRightFringe invocation n leftClose rightClose seed
        left middle)
      PackedReviewerBPWindowState.done PackedReviewerLcaState.done
      store 4 33 windowState windowReference continuation
      (by rfl)
      (by simpa [packedReviewerDriveBPWindow, windowState, windowReference]
        using hwindow)
      (by
        simpa [packedReviewerLcaStartRightFringe, blockSize, base, start,
          span, relLo, relHi, count, continuation, windowReference, finish]
          using hfringe)
      (by intro state _; rfl)
      (by intro state _; rfl)
      (by
        intro state reply _
        change
          (match packedReviewerBPWindowResult
              (packedReviewerBPWindowConsumeReply state reply) with
            | some bits =>
                packedReviewerLcaStartRightFringe invocation n leftClose
                  rightClose seed left middle bits
            | none =>
                .rightWindow invocation n leftClose rightClose seed left
                  middle (packedReviewerBPWindowConsumeReply state reply)) = _
        split <;> simp_all)
  simpa [blockSize, base, start, span, relLo, relHi, count, windowState,
    windowReference, continuation, finish, packedRightFringeCandidateRead,
    WordRAM.TraceResult.bind, WordRAM.TraceResult.map] using hsplice

private theorem packedReviewerDriveLca_rightSeed_simulates
    (store : WordRAM.ReadStore) (invocation : PackedReviewerInvocation)
    (n leftClose rightClose : Nat)
    (left middle : PackedReviewerCandidate) :
    let blockSize := packedSummaryBlockSizeRaw n
    let seedPos := packedLocalBPWindowBase n blockSize rightClose
    let state :=
      packedReviewerLcaStartRightSeed invocation n leftClose rightClose left
        middle
    let reference :=
      WordRAM.TraceResult.bind
        (packedLocalBPSeed n (packedRankCloseLeaf store n) blockSize rightClose)
        (fun rightSeed =>
          WordRAM.TraceResult.map
            (fun right =>
              SuccinctClose.bpCandidateClose?
                (SuccinctClose.bpCandidateMerge3? left middle right))
            (packedRightFringeCandidateRead store 21 n blockSize rightClose
              rightSeed))
    (packedReviewerDriveLca store 48 state).Simulates reference
      PackedReviewerLcaState.done := by
  let blockSize := packedSummaryBlockSizeRaw n
  let seedPos := packedLocalBPWindowBase n blockSize rightClose
  let rankState := packedReviewerLcaRankStart invocation n seedPos
  let rankReference := packedRankCloseLeaf store n seedPos
  let continuation : Nat -> WordRAM.TraceResult (Option Nat) :=
    fun rankFalse =>
      let seed := packedReviewerLcaSeed n blockSize rightClose rankFalse
      WordRAM.TraceResult.map
        (fun right =>
          SuccinctClose.bpCandidateClose?
            (SuccinctClose.bpCandidateMerge3? left middle right))
        (packedRightFringeCandidateRead store 21 n blockSize rightClose seed)
  have hrank :=
    packedReviewerDriveRank_simulates store invocation .close n seedPos
  have hwindow :=
    packedReviewerDriveLca_rightWindow_simulates store invocation n leftClose
      rightClose
      (packedReviewerLcaSeed n blockSize rightClose rankReference.value)
      left middle
  have hsplice :=
    packedReviewerDriveComponent_embedded_phase_simulates
      packedReviewerRankResult packedReviewerRankNextRequest
      packedReviewerRankConsumeReply packedReviewerLcaResult
      packedReviewerLcaNextRequest packedReviewerLcaConsumeReply
      (fun child =>
        .rightSeed invocation n leftClose rightClose left middle child)
      (fun rankFalse =>
        packedReviewerLcaStartRightWindow invocation n leftClose rightClose
          rankFalse left middle)
      PackedReviewerRankState.done PackedReviewerLcaState.done
      store 11 37 rankState rankReference continuation
      (by rfl)
      (by
        simpa [packedReviewerDriveRank, packedReviewerLcaRankStart, rankState,
          rankReference, packedRankCloseLeaf, packedRankCloseRead] using hrank)
      (by simpa [continuation, blockSize] using hwindow)
      (by intro state _; rfl)
      (by intro state _; rfl)
      (by
        intro state reply _
        change
          (match packedReviewerRankResult
              (packedReviewerRankConsumeReply state reply) with
            | some rankFalse =>
                packedReviewerLcaStartRightWindow invocation n leftClose
                  rightClose rankFalse left middle
            | none =>
                .rightSeed invocation n leftClose rightClose left middle
                  (packedReviewerRankConsumeReply state reply)) = _
        split <;> simp_all)
  simpa [packedReviewerLcaStartRightSeed, blockSize, seedPos, rankState,
    rankReference, continuation, packedLocalBPSeed, packedReviewerLcaSeed,
    WordRAM.TraceResult.bind, WordRAM.TraceResult.map] using hsplice

private theorem packedReviewerLca_gap_implies_size_ge_four
    (n leftClose rightClose : Nat) (hrightClose : rightClose < 2 * n)
    (hgap :
      SuccinctClose.blockOfClose (packedSummaryBlockSizeRaw n) leftClose + 1 <
        SuccinctClose.blockOfClose (packedSummaryBlockSizeRaw n) rightClose) :
    4 <= n := by
  by_cases hsize : 4 <= n
  · exact hsize
  have hn : n = 0 \/ n = 1 \/ n = 2 \/ n = 3 := by omega
  have hscale : 2 * n <= 2 * packedSummaryBlockSizeRaw n := by
    rcases hn with rfl | rfl | rfl | rfl
    · omega
    · unfold packedSummaryBlockSizeRaw packedSummaryBase
      omega
    · unfold packedSummaryBlockSizeRaw packedSummaryBase
      omega
    · have hlog : 1 <= Nat.log2 3 :=
        (Nat.le_log2 (by omega : 3 ≠ 0)).2 (by decide)
      unfold packedSummaryBlockSizeRaw packedSummaryBase
      omega
  have hblockSize : 0 < packedSummaryBlockSizeRaw n := by
    simp [packedSummaryBlockSizeRaw, packedSummaryBase]
  have hrightBlock :
      SuccinctClose.blockOfClose (packedSummaryBlockSizeRaw n) rightClose <
        2 := by
    unfold SuccinctClose.blockOfClose
    apply (Nat.div_lt_iff_lt_mul hblockSize).2
    omega
  omega

private theorem packedReviewerDriveLca_startMiddle_simulates
    (shape : Cartesian.CartesianShape)
    (invocation : PackedReviewerInvocation)
    (leftClose rightClose : Nat) (left : PackedReviewerCandidate)
    (hrightClose : rightClose < shape.bpCode.length) :
    let store := concreteBPNativeSuccinctRMQGlobalReadStore shape
    let n := shape.size
    let blockSize := packedSummaryBlockSizeRaw n
    let leftBlock := SuccinctClose.blockOfClose blockSize leftClose
    let rightBlock := SuccinctClose.blockOfClose blockSize rightClose
    let interiorReference :=
      if leftBlock + 1 < rightBlock then
        packedInteriorRangeMinRead concreteBPNativeInteriorTraceSegments store
          n (leftBlock + 1) (rightBlock - leftBlock - 1)
      else WordRAM.TraceResult.pure none
    let continuation : PackedReviewerCandidate ->
        WordRAM.TraceResult (Option Nat) :=
      fun middle =>
        WordRAM.TraceResult.bind
          (packedLocalBPSeed n (packedRankCloseLeaf store n) blockSize
            rightClose)
          (fun rightSeed =>
            WordRAM.TraceResult.map
              (fun right =>
                SuccinctClose.bpCandidateClose?
                  (SuccinctClose.bpCandidateMerge3? left middle right))
              (packedRightFringeCandidateRead store 21 n blockSize rightClose
                rightSeed))
    (packedReviewerDriveLca store 81
      (packedReviewerLcaStartMiddle invocation n leftClose rightClose left)).Simulates
        (WordRAM.TraceResult.bind interiorReference continuation)
        PackedReviewerLcaState.done := by
  let store := concreteBPNativeSuccinctRMQGlobalReadStore shape
  let n := shape.size
  let blockSize := packedSummaryBlockSizeRaw n
  let leftBlock := SuccinctClose.blockOfClose blockSize leftClose
  let rightBlock := SuccinctClose.blockOfClose blockSize rightClose
  let startBlock := leftBlock + 1
  let count := rightBlock - leftBlock - 1
  let interior :=
    packedReviewerInteriorStart invocation n startBlock count
  let interiorReference :=
    packedInteriorRangeMinRead concreteBPNativeInteriorTraceSegments store n
      startBlock count
  let continuation : PackedReviewerCandidate ->
      WordRAM.TraceResult (Option Nat) :=
    fun middle =>
      WordRAM.TraceResult.bind
        (packedLocalBPSeed n (packedRankCloseLeaf store n) blockSize rightClose)
        (fun rightSeed =>
          WordRAM.TraceResult.map
            (fun right =>
              SuccinctClose.bpCandidateClose?
                (SuccinctClose.bpCandidateMerge3? left middle right))
            (packedRightFringeCandidateRead store 21 n blockSize rightClose
              rightSeed))
  by_cases hgap : leftBlock + 1 < rightBlock
  · have hsize : 4 <= n := by
      apply packedReviewerLca_gap_implies_size_ge_four n leftClose rightClose
      · simpa [n, Cartesian.CartesianShape.bpCode_length] using hrightClose
      · simpa [leftBlock, rightBlock, blockSize] using hgap
    have hrightBlock :
        rightBlock <= (packedInteriorLayout n).blockCount := by
      have hraw :=
        SuccinctClose.ConcreteCompactBPCloseLCADirectory.canonicalBPRelativeSummary_blockOfClose_le_blockCountRaw
          (shape := shape) hrightClose
      simpa [rightBlock, blockSize, n, packedInteriorLayout,
        packedSummaryBlockCountRaw, packedSummaryBase,
        SuccinctClose.canonicalBPRelativeSummaryBlockCountRaw,
        SuccinctClose.canonicalBPRelativeSummaryBase] using hraw
    have hbound :
        startBlock + count <= (packedInteriorLayout n).blockCount := by
      dsimp [startBlock, count]
      omega
    have hinterior :=
      packedReviewerDriveInterior_simulates shape invocation startBlock count
        (by simpa [n] using hsize) (by simpa [n] using hbound)
    by_cases hresult : packedReviewerInteriorResult interior = none
    · have hright :=
        packedReviewerDriveLca_rightSeed_simulates store invocation n leftClose
          rightClose left interiorReference.value
      have hsplice :=
        packedReviewerDriveComponent_embedded_phase_simulates
          packedReviewerInteriorResult packedReviewerInteriorNextRequest
          packedReviewerInteriorConsumeReply packedReviewerLcaResult
          packedReviewerLcaNextRequest packedReviewerLcaConsumeReply
          (fun child =>
            .middle invocation n leftClose rightClose left child)
          (fun middle =>
            packedReviewerLcaStartRightSeed invocation n leftClose rightClose
              left middle)
          PackedReviewerInteriorState.done PackedReviewerLcaState.done
          store 33 48 interior interiorReference continuation
          hresult
          (by
            simpa [store, n, startBlock, count, interior,
              interiorReference, packedReviewerDriveInterior] using hinterior)
          (by simpa [continuation, blockSize] using hright)
          (by intro state _; rfl)
          (by intro state _; rfl)
          (by
            intro state reply _
            change
              (match packedReviewerInteriorResult
                  (packedReviewerInteriorConsumeReply state reply) with
                | some middle =>
                    packedReviewerLcaStartRightSeed invocation n leftClose
                      rightClose left middle
                | none =>
                    PackedReviewerLcaState.middle invocation n leftClose
                      rightClose left
                      (packedReviewerInteriorConsumeReply state reply)) = _
            split <;> simp_all)
      simpa [packedReviewerLcaStartMiddle, hgap, store, n, blockSize,
        leftBlock, rightBlock, startBlock, count, interior,
        interiorReference, continuation, hresult] using hsplice
    · obtain ⟨middle, hmiddle⟩ :
          exists middle, packedReviewerInteriorResult interior = some middle := by
        cases h : packedReviewerInteriorResult interior with
        | none => exact False.elim (hresult h)
        | some middle => exact ⟨middle, rfl⟩
      have hrun :=
        packedReviewerDriveComponent_of_result packedReviewerInteriorResult
          packedReviewerInteriorNextRequest packedReviewerInteriorConsumeReply
          store 33 interior middle hmiddle
      have hvalue : middle = interiorReference.value := by
        have hterminal := hinterior.1
        rw [show packedReviewerDriveInterior store 33 interior =
            { terminal := some middle, state := interior, trace := [] } by
              simpa [packedReviewerDriveInterior] using hrun] at hterminal
        exact Option.some.inj hterminal
      have htrace : interiorReference.trace = [] := by
        have htraceEq := hinterior.2.2
        rw [show packedReviewerDriveInterior store 33 interior =
            { terminal := some middle, state := interior, trace := [] } by
              simpa [packedReviewerDriveInterior] using hrun] at htraceEq
        simpa using htraceEq.symm
      have hrefPure :
          interiorReference = WordRAM.TraceResult.pure middle := by
        calc
          interiorReference =
              WordRAM.TraceResult.mk interiorReference.value
                interiorReference.trace := by
            cases interiorReference
            rfl
          _ = WordRAM.TraceResult.mk middle interiorReference.trace :=
            congrArg
              (fun value =>
                WordRAM.TraceResult.mk value interiorReference.trace)
              hvalue.symm
          _ = WordRAM.TraceResult.pure middle := by
            simpa [WordRAM.TraceResult.pure] using
              congrArg (WordRAM.TraceResult.mk middle) htrace
      have hright :=
        packedReviewerDriveLca_rightSeed_simulates store invocation n leftClose
          rightClose left middle
      have hpad :=
        packedReviewerDriveComponent_add_fuel_of_simulates
          packedReviewerLcaResult packedReviewerLcaNextRequest
          packedReviewerLcaConsumeReply store 48 33
          (packedReviewerLcaStartRightSeed invocation n leftClose rightClose
            left middle)
          (continuation middle) PackedReviewerLcaState.done
          (by simpa [continuation, blockSize] using hright)
      simpa [packedReviewerLcaStartMiddle, hgap, interior, hmiddle, store, n,
        blockSize, leftBlock, rightBlock, startBlock, count,
        interiorReference, hrefPure, continuation, WordRAM.TraceResult.bind,
        WordRAM.TraceResult.pure] using hpad
  · have hright :=
      packedReviewerDriveLca_rightSeed_simulates store invocation n leftClose
        rightClose left none
    have hpad :=
      packedReviewerDriveComponent_add_fuel_of_simulates
        packedReviewerLcaResult packedReviewerLcaNextRequest
        packedReviewerLcaConsumeReply store 48 33
        (packedReviewerLcaStartRightSeed invocation n leftClose rightClose left
          none)
        (continuation none) PackedReviewerLcaState.done
        (by simpa [continuation, blockSize] using hright)
    simpa [packedReviewerLcaStartMiddle, hgap, store, n, blockSize,
      leftBlock, rightBlock, continuation, WordRAM.TraceResult.bind,
      WordRAM.TraceResult.pure] using hpad

private theorem packedReviewerDriveLca_leftFringe_simulates
    (shape : Cartesian.CartesianShape)
    (invocation : PackedReviewerInvocation)
    (leftClose rightClose seed base start : Nat) (window : List Bool)
    (relLo relHi count : Nat) (hpositive : 0 < count)
    (hcount : count <= 33)
    (hrightClose : rightClose < shape.bpCode.length) :
    let store := concreteBPNativeSuccinctRMQGlobalReadStore shape
    let n := shape.size
    let fringe :=
      packedReviewerFringeStart invocation n window seed relLo relHi count
    let foldReference :=
      SuccinctClose.bpFringeChunkFoldTraceResultAtSegmentWithStore store 21
        (packedFringeChunkBits n) window seed relLo relHi count
    let leftReference :=
      WordRAM.TraceResult.map
        (fun fold =>
          SuccinctClose.bpFringeCandGlobal base seed start fold.2)
        foldReference
    let blockSize := packedSummaryBlockSizeRaw n
    let leftBlock := SuccinctClose.blockOfClose blockSize leftClose
    let rightBlock := SuccinctClose.blockOfClose blockSize rightClose
    let continuation : PackedReviewerCandidate ->
        WordRAM.TraceResult (Option Nat) :=
      fun left =>
        WordRAM.TraceResult.bind
          (if leftBlock + 1 < rightBlock then
            packedInteriorRangeMinRead concreteBPNativeInteriorTraceSegments
              store n (leftBlock + 1) (rightBlock - leftBlock - 1)
          else WordRAM.TraceResult.pure none)
          (fun middle =>
            WordRAM.TraceResult.bind
              (packedLocalBPSeed n (packedRankCloseLeaf store n) blockSize
                rightClose)
              (fun rightSeed =>
                WordRAM.TraceResult.map
                  (fun right =>
                    SuccinctClose.bpCandidateClose?
                      (SuccinctClose.bpCandidateMerge3? left middle right))
                  (packedRightFringeCandidateRead store 21 n blockSize
                    rightClose rightSeed)))
    (packedReviewerDriveLca store 114
      (.leftFringe invocation n leftClose rightClose seed base start
        fringe)).Simulates
      (WordRAM.TraceResult.bind leftReference continuation)
      PackedReviewerLcaState.done := by
  let store := concreteBPNativeSuccinctRMQGlobalReadStore shape
  let n := shape.size
  let fringe :=
    packedReviewerFringeStart invocation n window seed relLo relHi count
  let foldReference :=
    SuccinctClose.bpFringeChunkFoldTraceResultAtSegmentWithStore store 21
      (packedFringeChunkBits n) window seed relLo relHi count
  let leftOfFold : Nat × Option (Nat × Nat) -> PackedReviewerCandidate :=
    fun fold => SuccinctClose.bpFringeCandGlobal base seed start fold.2
  let blockSize := packedSummaryBlockSizeRaw n
  let leftBlock := SuccinctClose.blockOfClose blockSize leftClose
  let rightBlock := SuccinctClose.blockOfClose blockSize rightClose
  let continuation : PackedReviewerCandidate ->
      WordRAM.TraceResult (Option Nat) :=
    fun left =>
      WordRAM.TraceResult.bind
        (if leftBlock + 1 < rightBlock then
          packedInteriorRangeMinRead concreteBPNativeInteriorTraceSegments
            store n (leftBlock + 1) (rightBlock - leftBlock - 1)
        else WordRAM.TraceResult.pure none)
        (fun middle =>
          WordRAM.TraceResult.bind
            (packedLocalBPSeed n (packedRankCloseLeaf store n) blockSize
              rightClose)
            (fun rightSeed =>
              WordRAM.TraceResult.map
                (fun right =>
                  SuccinctClose.bpCandidateClose?
                    (SuccinctClose.bpCandidateMerge3? left middle right))
                (packedRightFringeCandidateRead store 21 n blockSize
                  rightClose rightSeed)))
  have hfringe :=
    packedReviewerDriveFringe_fixed_simulates store invocation n window seed
      relLo relHi count 33 hcount
  have hdone : packedReviewerFringeResult fringe = none := by
    simp [fringe, packedReviewerFringeStart, Nat.ne_of_gt hpositive,
      packedReviewerFringeResult]
  have hmiddle :=
    packedReviewerDriveLca_startMiddle_simulates shape invocation leftClose
      rightClose (leftOfFold foldReference.value) hrightClose
  have hsplice :=
    packedReviewerDriveComponent_embedded_phase_simulates
      packedReviewerFringeResult packedReviewerFringeNextRequest
      packedReviewerFringeConsumeReply packedReviewerLcaResult
      packedReviewerLcaNextRequest packedReviewerLcaConsumeReply
      (fun child =>
        .leftFringe invocation n leftClose rightClose seed base start child)
      (fun fold =>
        packedReviewerLcaStartMiddle invocation n leftClose rightClose
          (leftOfFold fold))
      PackedReviewerFringeState.done PackedReviewerLcaState.done
      store 33 81 fringe foldReference
      (fun fold => continuation (leftOfFold fold)) hdone
      (by simpa [packedReviewerDriveFringe, fringe, foldReference] using
        hfringe)
      (by
        simpa [continuation, leftOfFold, blockSize, leftBlock, rightBlock]
          using hmiddle)
      (by intro state _; rfl)
      (by intro state _; rfl)
      (by
        intro state reply _
        change
          (match packedReviewerFringeResult
              (packedReviewerFringeConsumeReply state reply) with
            | some fold =>
                packedReviewerLcaStartMiddle invocation n leftClose
                  rightClose (leftOfFold fold)
            | none =>
                PackedReviewerLcaState.leftFringe invocation n leftClose
                  rightClose seed base start
                  (packedReviewerFringeConsumeReply state reply)) = _
        split <;> simp_all)
  simpa [store, n, fringe, foldReference, leftOfFold, blockSize, leftBlock,
    rightBlock, continuation, WordRAM.TraceResult.map,
    WordRAM.TraceResult.bind, WordRAM.TraceResult.pure] using hsplice

private theorem packedReviewerDriveLca_leftWindow_simulates
    (shape : Cartesian.CartesianShape)
    (invocation : PackedReviewerInvocation)
    (leftClose rightClose seed : Nat)
    (hrightClose : rightClose < shape.bpCode.length) :
    let store := concreteBPNativeSuccinctRMQGlobalReadStore shape
    let n := shape.size
    let blockSize := packedSummaryBlockSizeRaw n
    let state : PackedReviewerLcaState :=
      .leftWindow invocation n leftClose rightClose seed
        (packedReviewerBPWindowStart invocation n blockSize leftClose)
    let leftReference :=
      packedLeftFringeCandidateRead store 21 n blockSize leftClose seed
    let leftBlock := SuccinctClose.blockOfClose blockSize leftClose
    let rightBlock := SuccinctClose.blockOfClose blockSize rightClose
    let continuation : PackedReviewerCandidate ->
        WordRAM.TraceResult (Option Nat) :=
      fun left =>
        WordRAM.TraceResult.bind
          (if leftBlock + 1 < rightBlock then
            packedInteriorRangeMinRead concreteBPNativeInteriorTraceSegments
              store n (leftBlock + 1) (rightBlock - leftBlock - 1)
          else WordRAM.TraceResult.pure none)
          (fun middle =>
            WordRAM.TraceResult.bind
              (packedLocalBPSeed n (packedRankCloseLeaf store n) blockSize
                rightClose)
              (fun rightSeed =>
                WordRAM.TraceResult.map
                  (fun right =>
                    SuccinctClose.bpCandidateClose?
                      (SuccinctClose.bpCandidateMerge3? left middle right))
                  (packedRightFringeCandidateRead store 21 n blockSize
                    rightClose rightSeed)))
    (packedReviewerDriveLca store 118 state).Simulates
      (WordRAM.TraceResult.bind leftReference continuation)
      PackedReviewerLcaState.done := by
  let store := concreteBPNativeSuccinctRMQGlobalReadStore shape
  let n := shape.size
  let blockSize := packedSummaryBlockSizeRaw n
  let base := packedLocalBPWindowBase n blockSize leftClose
  let start := leftClose + 1
  let span :=
    SuccinctClose.blockStartOf blockSize
        (SuccinctClose.blockOfClose blockSize leftClose) +
      blockSize - leftClose
  let relLo := start - base
  let relHi := start + span - 1 - base
  let count := Nat.min (relHi / packedFringeChunkBits n + 1) 33
  let windowState :=
    packedReviewerBPWindowStart invocation n blockSize leftClose
  let windowReference :=
    packedLocalBPWindowBitsRead store n blockSize leftClose
  let leftBlock := SuccinctClose.blockOfClose blockSize leftClose
  let rightBlock := SuccinctClose.blockOfClose blockSize rightClose
  let continuation : PackedReviewerCandidate ->
      WordRAM.TraceResult (Option Nat) :=
    fun left =>
      WordRAM.TraceResult.bind
        (if leftBlock + 1 < rightBlock then
          packedInteriorRangeMinRead concreteBPNativeInteriorTraceSegments
            store n (leftBlock + 1) (rightBlock - leftBlock - 1)
        else WordRAM.TraceResult.pure none)
        (fun middle =>
          WordRAM.TraceResult.bind
            (packedLocalBPSeed n (packedRankCloseLeaf store n) blockSize
              rightClose)
            (fun rightSeed =>
              WordRAM.TraceResult.map
                (fun right =>
                  SuccinctClose.bpCandidateClose?
                    (SuccinctClose.bpCandidateMerge3? left middle right))
                (packedRightFringeCandidateRead store 21 n blockSize
                  rightClose rightSeed)))
  let foldContinuation : List Bool -> WordRAM.TraceResult (Option Nat) :=
    fun window =>
      WordRAM.TraceResult.bind
        (WordRAM.TraceResult.map
          (fun fold =>
            SuccinctClose.bpFringeCandGlobal base seed start fold.2)
          (SuccinctClose.bpFringeChunkFoldTraceResultAtSegmentWithStore store
            21 (packedFringeChunkBits n) window seed relLo relHi count))
        continuation
  have hpositive : 0 < count := by
    exact Nat.lt_min.mpr ⟨Nat.zero_lt_succ _, by decide⟩
  have hcount : count <= 33 := Nat.min_le_right _ _
  have hwindow :=
    packedReviewerDriveBPWindow_simulates store invocation n blockSize
      leftClose
  have hfringe :=
    packedReviewerDriveLca_leftFringe_simulates shape invocation leftClose
      rightClose seed base start windowReference.value relLo relHi count
      hpositive hcount hrightClose
  have hsplice :=
    packedReviewerDriveComponent_embedded_phase_simulates
      packedReviewerBPWindowResult packedReviewerBPWindowNextRequest
      packedReviewerBPWindowConsumeReply packedReviewerLcaResult
      packedReviewerLcaNextRequest packedReviewerLcaConsumeReply
      (fun child =>
        .leftWindow invocation n leftClose rightClose seed child)
      (packedReviewerLcaStartLeftFringe invocation n leftClose rightClose seed)
      PackedReviewerBPWindowState.done PackedReviewerLcaState.done
      store 4 114 windowState windowReference foldContinuation
      (by rfl)
      (by simpa [packedReviewerDriveBPWindow, windowState, windowReference]
        using hwindow)
      (by
        simpa [foldContinuation, base, start, span, relLo, relHi, count,
          continuation, packedReviewerLcaStartLeftFringe, blockSize, n,
          store] using hfringe)
      (by intro state _; rfl)
      (by intro state _; rfl)
      (by
        intro state reply _
        change
          (match packedReviewerBPWindowResult
              (packedReviewerBPWindowConsumeReply state reply) with
            | some bits =>
                packedReviewerLcaStartLeftFringe invocation n leftClose
                  rightClose seed bits
            | none =>
                PackedReviewerLcaState.leftWindow invocation n leftClose
                  rightClose seed
                  (packedReviewerBPWindowConsumeReply state reply)) = _
        split <;> simp_all)
  simpa [store, n, blockSize, base, start, span, relLo, relHi, count,
    windowState, windowReference, leftBlock, rightBlock, continuation,
    foldContinuation, packedLeftFringeCandidateRead,
    WordRAM.TraceResult.map, WordRAM.TraceResult.bind,
    WordRAM.TraceResult.pure] using hsplice

private theorem packedReviewerDriveLca_leftSeed_simulates
    (shape : Cartesian.CartesianShape)
    (invocation : PackedReviewerInvocation)
    (leftClose rightClose : Nat)
    (hrightClose : rightClose < shape.bpCode.length) :
    let store := concreteBPNativeSuccinctRMQGlobalReadStore shape
    let n := shape.size
    let state : PackedReviewerLcaState :=
      .leftSeed invocation n leftClose rightClose
        (packedReviewerLcaRankStart invocation n
          (packedLocalBPWindowBase n (packedSummaryBlockSizeRaw n)
            leftClose))
    let reference := packedCrossBlockCloseRead
      (packedRankCloseLeaf store n) concreteBPNativeInteriorTraceSegments 21
      store n leftClose rightClose
    (packedReviewerDriveLca store 129 state).Simulates reference
      PackedReviewerLcaState.done := by
  let store := concreteBPNativeSuccinctRMQGlobalReadStore shape
  let n := shape.size
  let blockSize := packedSummaryBlockSizeRaw n
  let seedPos := packedLocalBPWindowBase n blockSize leftClose
  let rankState := packedReviewerLcaRankStart invocation n seedPos
  let rankReference := packedRankCloseLeaf store n seedPos
  let leftBlock := SuccinctClose.blockOfClose blockSize leftClose
  let rightBlock := SuccinctClose.blockOfClose blockSize rightClose
  let afterLeft : PackedReviewerCandidate ->
      WordRAM.TraceResult (Option Nat) :=
    fun left =>
      WordRAM.TraceResult.bind
        (if leftBlock + 1 < rightBlock then
          packedInteriorRangeMinRead concreteBPNativeInteriorTraceSegments
            store n (leftBlock + 1) (rightBlock - leftBlock - 1)
        else WordRAM.TraceResult.pure none)
        (fun middle =>
          WordRAM.TraceResult.bind
            (packedLocalBPSeed n (packedRankCloseLeaf store n) blockSize
              rightClose)
            (fun rightSeed =>
              WordRAM.TraceResult.map
                (fun right =>
                  SuccinctClose.bpCandidateClose?
                    (SuccinctClose.bpCandidateMerge3? left middle right))
                (packedRightFringeCandidateRead store 21 n blockSize
                  rightClose rightSeed)))
  let continuation : Nat -> WordRAM.TraceResult (Option Nat) :=
    fun rankFalse =>
      let seed := packedReviewerLcaSeed n blockSize leftClose rankFalse
      WordRAM.TraceResult.bind
        (packedLeftFringeCandidateRead store 21 n blockSize leftClose seed)
        afterLeft
  have hrank :=
    packedReviewerDriveRank_simulates store invocation .close n seedPos
  have hwindow :=
    packedReviewerDriveLca_leftWindow_simulates shape invocation leftClose
      rightClose
      (packedReviewerLcaSeed n blockSize leftClose rankReference.value)
      hrightClose
  have hsplice :=
    packedReviewerDriveComponent_embedded_phase_simulates
      packedReviewerRankResult packedReviewerRankNextRequest
      packedReviewerRankConsumeReply packedReviewerLcaResult
      packedReviewerLcaNextRequest packedReviewerLcaConsumeReply
      (fun child => .leftSeed invocation n leftClose rightClose child)
      (packedReviewerLcaStartLeftWindow invocation n leftClose rightClose)
      PackedReviewerRankState.done PackedReviewerLcaState.done
      store 11 118 rankState rankReference continuation
      (by rfl)
      (by
        simpa [packedReviewerDriveRank, packedReviewerLcaRankStart, rankState,
          rankReference, packedRankCloseLeaf, packedRankCloseRead] using hrank)
      (by simpa [continuation, afterLeft, blockSize] using hwindow)
      (by intro state _; rfl)
      (by intro state _; rfl)
      (by
        intro state reply _
        change
          (match packedReviewerRankResult
              (packedReviewerRankConsumeReply state reply) with
            | some rankFalse =>
                packedReviewerLcaStartLeftWindow invocation n leftClose
                  rightClose rankFalse
            | none =>
                PackedReviewerLcaState.leftSeed invocation n leftClose
                  rightClose (packedReviewerRankConsumeReply state reply)) = _
        split <;> simp_all)
  simpa [store, n, blockSize, seedPos, rankState, rankReference, leftBlock,
    rightBlock, afterLeft, continuation, packedCrossBlockCloseRead,
    packedLocalBPSeed, packedReviewerLcaSeed, WordRAM.TraceResult.bind,
    WordRAM.TraceResult.map] using hsplice
/-! ## Close-select phase splices -/

private theorem packedReviewerDriveSelect_superEntry_splice
    (store : WordRAM.ReadStore) (invocation : PackedReviewerInvocation)
    (n index reserve : Nat)
    (continuation :
      Option GenericSelect.SparseDenseSelectDenseLocalEntry ->
        WordRAM.TraceResult (Option Nat))
    (hcontinuation :
      let reference :=
        packedSelectEntryRead
          concreteBPNativeSelectCloseTraceSegmentLayout.superTable store
          (GenericSelect.selectSuperSlot index (packedSelectSuperStride n))
      (packedReviewerDriveSelect store reserve
        (packedReviewerSelectAfterSuper invocation n index
          reference.value)).Simulates
        (continuation reference.value) PackedReviewerSelectState.done) :
    let entryState : PackedReviewerEntryState :=
      .baseOccurrence invocation .super
        (GenericSelect.selectSuperSlot index (packedSelectSuperStride n))
    let reference :=
      packedSelectEntryRead
        concreteBPNativeSelectCloseTraceSegmentLayout.superTable store
        (GenericSelect.selectSuperSlot index (packedSelectSuperStride n))
    (packedReviewerDriveSelect store (4 + reserve)
      (.superEntry invocation n index entryState)).Simulates
        (WordRAM.TraceResult.bind reference continuation)
        PackedReviewerSelectState.done := by
  let slot := GenericSelect.selectSuperSlot index (packedSelectSuperStride n)
  let entryState : PackedReviewerEntryState :=
    .baseOccurrence invocation .super slot
  let reference :=
    packedSelectEntryRead
      concreteBPNativeSelectCloseTraceSegmentLayout.superTable store slot
  have hentry :=
    packedReviewerDriveEntry_simulates store invocation
      PackedReviewerEntryKind.super slot
  apply packedReviewerDriveComponent_embedded_phase_simulates
    packedReviewerEntryResult packedReviewerEntryNextRequest
    packedReviewerEntryConsumeReply packedReviewerSelectResult
    packedReviewerSelectNextRequest packedReviewerSelectConsumeReply
    (fun entry => .superEntry invocation n index entry)
    (packedReviewerSelectAfterSuper invocation n index)
    PackedReviewerEntryState.done PackedReviewerSelectState.done
    store 4 reserve entryState reference continuation
  · rfl
  · simpa [packedReviewerDriveEntry, entryState, reference] using hentry
  · simpa [packedReviewerDriveSelect, reference] using hcontinuation
  · intro state hstate
    cases state <;>
      simp [packedReviewerEntryResult, packedReviewerSelectResult] at hstate ⊢
  · intro state hstate
    cases state <;>
      simp [packedReviewerEntryResult, packedReviewerEntryNextRequest,
        packedReviewerSelectNextRequest] at hstate ⊢
  · intro state reply hstate
    cases state <;>
      simp [packedReviewerEntryResult, packedReviewerEntryConsumeReply,
        packedReviewerSelectConsumeReply] at hstate ⊢

private theorem packedReviewerDriveSelect_localEntry_splice
    (store : WordRAM.ReadStore) (invocation : PackedReviewerInvocation)
    (n index localSlot reserve : Nat)
    (super : GenericSelect.SparseDenseSelectDenseLocalEntry)
    (continuation :
      Option GenericSelect.SparseDenseSelectDenseLocalEntry ->
        WordRAM.TraceResult (Option Nat))
    (hcontinuation :
      let reference :=
        packedSelectEntryRead
          concreteBPNativeSelectCloseTraceSegmentLayout.localTable store
          localSlot
      (packedReviewerDriveSelect store reserve
        (packedReviewerSelectAfterLocal invocation n index localSlot super
          reference.value)).Simulates
        (continuation reference.value) PackedReviewerSelectState.done) :
    let entryState : PackedReviewerEntryState :=
      .baseOccurrence invocation .local localSlot
    let reference :=
      packedSelectEntryRead
        concreteBPNativeSelectCloseTraceSegmentLayout.localTable store localSlot
    (packedReviewerDriveSelect store (4 + reserve)
      (.localEntry invocation n index localSlot super entryState)).Simulates
        (WordRAM.TraceResult.bind reference continuation)
        PackedReviewerSelectState.done := by
  let entryState : PackedReviewerEntryState :=
    .baseOccurrence invocation .local localSlot
  let reference :=
    packedSelectEntryRead
      concreteBPNativeSelectCloseTraceSegmentLayout.localTable store localSlot
  have hentry :=
    packedReviewerDriveEntry_simulates store invocation
      PackedReviewerEntryKind.local localSlot
  apply packedReviewerDriveComponent_embedded_phase_simulates
    packedReviewerEntryResult packedReviewerEntryNextRequest
    packedReviewerEntryConsumeReply packedReviewerSelectResult
    packedReviewerSelectNextRequest packedReviewerSelectConsumeReply
    (fun entry =>
      .localEntry invocation n index localSlot super entry)
    (packedReviewerSelectAfterLocal invocation n index localSlot super)
    PackedReviewerEntryState.done PackedReviewerSelectState.done
    store 4 reserve entryState reference continuation
  · rfl
  · simpa [packedReviewerDriveEntry, entryState, reference] using hentry
  · simpa [packedReviewerDriveSelect, reference] using hcontinuation
  · intro state hstate
    cases state <;>
      simp [packedReviewerEntryResult, packedReviewerSelectResult] at hstate ⊢
  · intro state hstate
    cases state <;>
      simp [packedReviewerEntryResult, packedReviewerEntryNextRequest,
        packedReviewerSelectNextRequest] at hstate ⊢
  · intro state reply hstate
    cases state <;>
      simp [packedReviewerEntryResult, packedReviewerEntryConsumeReply,
        packedReviewerSelectConsumeReply] at hstate ⊢

private theorem packedReviewerDriveSelect_longRelative_simulates
    (store : WordRAM.ReadStore) (invocation : PackedReviewerInvocation)
    (base slot : Nat) :
    (packedReviewerDriveSelect store 1
      (.longRelative invocation base slot)).Simulates
        (GenericSelect.bpRelativeOffsetReadTraceResultWithStore store 12 base
          slot)
        PackedReviewerSelectState.done := by
  simp [PackedReviewerComponentRun.Simulates, packedReviewerDriveSelect,
    packedReviewerDriveComponent, packedReviewerSelectResult,
    packedReviewerSelectNextRequest, packedReviewerSelectConsumeReply,
    packedReviewerDecodeNat,
    GenericSelect.bpRelativeOffsetReadTraceResultWithStore,
    SuccinctClose.bpChunkReadTraceResult, WordRAM.TraceResult.map,
    WordRAM.TraceResult.bind, WordRAM.TraceResult.pure,
    PackedReviewerLogicalEvent.erase]

private theorem packedReviewerDriveSelect_sparseRelative_simulates
    (store : WordRAM.ReadStore) (invocation : PackedReviewerInvocation)
    (base slot : Nat) :
    (packedReviewerDriveSelect store 1
      (.sparseRelative invocation base slot)).Simulates
        (GenericSelect.bpRelativeOffsetReadTraceResultWithStore store 16 base
          slot)
        PackedReviewerSelectState.done := by
  simp [PackedReviewerComponentRun.Simulates, packedReviewerDriveSelect,
    packedReviewerDriveComponent, packedReviewerSelectResult,
    packedReviewerSelectNextRequest, packedReviewerSelectConsumeReply,
    packedReviewerDecodeNat,
    GenericSelect.bpRelativeOffsetReadTraceResultWithStore,
    SuccinctClose.bpChunkReadTraceResult, WordRAM.TraceResult.map,
    WordRAM.TraceResult.bind, WordRAM.TraceResult.pure,
    PackedReviewerLogicalEvent.erase]

private theorem packedReviewerDriveSelect_readWord_splice
    (store : WordRAM.ReadStore) (reserve : Nat)
    (state : PackedReviewerSelectState)
    (request : PackedReviewerLogicalRequest)
    (after : Option (List Bool) -> PackedReviewerSelectState)
    (continuation : Option (List Bool) ->
      WordRAM.TraceResult (Option Nat))
    (hresult : packedReviewerSelectResult state = none)
    (hrequest : packedReviewerSelectNextRequest state = some request)
    (hconsume : forall reply,
      packedReviewerSelectConsumeReply state reply = after reply)
    (hcontinuation :
      (packedReviewerDriveSelect store reserve
        (after (store.readWord? request.segment request.index))).Simulates
          (continuation
            (store.readWord? request.segment request.index))
          PackedReviewerSelectState.done) :
    (packedReviewerDriveSelect store (1 + reserve) state).Simulates
      (WordRAM.TraceResult.bind
        (SuccinctClose.bpWordReadTraceResult store request.segment
          request.index)
        continuation)
      PackedReviewerSelectState.done := by
  let reply := store.readWord? request.segment request.index
  have hstep :=
    packedReviewerDriveComponent_succ_of_request packedReviewerSelectResult
      packedReviewerSelectNextRequest packedReviewerSelectConsumeReply store
      reserve state request hresult hrequest
  change
    (packedReviewerDriveComponent packedReviewerSelectResult
      packedReviewerSelectNextRequest packedReviewerSelectConsumeReply store
      (1 + reserve) state).Simulates _ _
  rw [show 1 + reserve = reserve + 1 by omega, hstep]
  have hprefix :=
    PackedReviewerComponentRun.prepend_simulates
      (run := packedReviewerDriveSelect store reserve (after reply))
      (request := request) (reply := reply)
      (reference := continuation reply)
      (done := PackedReviewerSelectState.done)
      (by simpa [reply] using hcontinuation)
  simpa [packedReviewerDriveSelect, hconsume,
    SuccinctClose.bpWordReadTraceResult, WordRAM.TraceResult.bind,
    packedReviewerTracePrepend, reply] using hprefix

private theorem packedReviewerDriveRankStartFold_zeroBase_simulates
    (store : WordRAM.ReadStore) (invocation : PackedReviewerInvocation)
    (n : Nat) (word : List Bool) (limit : Nat) :
    let state :=
      packedReviewerRankStartFold invocation .close n word limit 0
    let run :=
      packedReviewerDriveRank store (packedReviewerRankRemaining state) state
    let reference :=
      SuccinctClose.bpChunkedWordRankTraceResultAtSegmentWithStore store 21
        (packedFringeChunkBits n) false word limit
    run.Simulates reference PackedReviewerRankState.done := by
  let effectiveLimit := SuccinctClose.bpWordRankEffLimit word limit
  let count :=
    SuccinctClose.bpWordChunkCount (packedFringeChunkBits n) effectiveLimit
  by_cases hcount : count = 0
  · simp [packedReviewerRankStartFold, effectiveLimit, count, hcount,
      packedReviewerRankRemaining, packedReviewerDriveRank,
      packedReviewerDriveComponent, packedReviewerRankResult,
      PackedReviewerComponentRun.Simulates,
      SuccinctClose.bpChunkedWordRankTraceResultAtSegmentWithStore,
      SuccinctClose.bpChunkedWordRankTraceFromWithStore,
      WordRAM.TraceResult.pure]
  · have hpositive : 0 < count := Nat.pos_of_ne_zero hcount
    have hfold :=
      packedReviewerDriveRankFold_pos_simulates store invocation
        PackedReviewerRankKind.close n word effectiveLimit 0 count 0 0
        hpositive
    have hmapId (result : WordRAM.TraceResult Nat) :
        WordRAM.TraceResult.map (fun value => 0 + value) result = result := by
      cases result
      simp [WordRAM.TraceResult.map, WordRAM.TraceResult.bind,
        WordRAM.TraceResult.pure]
    rw [hmapId] at hfold
    simpa [packedReviewerRankStartFold, effectiveLimit, count, hcount,
      packedReviewerRankRemaining,
      SuccinctClose.bpChunkedWordRankTraceResultAtSegmentWithStore,
      PackedReviewerRankKind.target] using hfold

private theorem packedReviewerDriveSelect_denseBeforeRank_splice
    (store : WordRAM.ReadStore) (invocation : PackedReviewerInvocation)
    (n index basePosition baseOccurrence reserve : Nat) (word : List Bool)
    (rankState : PackedReviewerRankState)
    (reference : WordRAM.TraceResult Nat)
    (continuation : Nat -> WordRAM.TraceResult (Option Nat))
    (hrankStart : packedReviewerRankResult rankState = none)
    (hrank :
      (packedReviewerDriveRank store
        (packedReviewerRankRemaining rankState) rankState).Simulates
          reference PackedReviewerRankState.done)
    (hcontinuation :
      (packedReviewerDriveSelect store reserve
        (packedReviewerSelectAfterDenseBeforeRank invocation n index
          basePosition baseOccurrence word reference.value)).Simulates
        (continuation reference.value) PackedReviewerSelectState.done) :
    (packedReviewerDriveSelect store
      (packedReviewerRankRemaining rankState + reserve)
      (.denseBeforeRank invocation n index basePosition baseOccurrence word
        rankState)).Simulates
      (WordRAM.TraceResult.bind reference continuation)
      PackedReviewerSelectState.done := by
  apply packedReviewerDriveComponent_embedded_phase_simulates
    packedReviewerRankResult packedReviewerRankNextRequest
    packedReviewerRankConsumeReply packedReviewerSelectResult
    packedReviewerSelectNextRequest packedReviewerSelectConsumeReply
    (fun rank =>
      .denseBeforeRank invocation n index basePosition baseOccurrence word rank)
    (packedReviewerSelectAfterDenseBeforeRank invocation n index basePosition
      baseOccurrence word)
    PackedReviewerRankState.done PackedReviewerSelectState.done
    store (packedReviewerRankRemaining rankState) reserve rankState reference
    continuation hrankStart (by simpa [packedReviewerDriveRank] using hrank)
    (by simpa [packedReviewerDriveSelect] using hcontinuation)
  · intros
    rfl
  · intros
    rfl
  · intro state reply _
    simp only [packedReviewerSelectConsumeReply]
    cases hnext : packedReviewerRankResult
        (packedReviewerRankConsumeReply state reply) <;> simp [hnext]

private theorem packedReviewerDriveSelect_denseUptoRank_splice
    (store : WordRAM.ReadStore) (invocation : PackedReviewerInvocation)
    (n index basePosition baseOccurrence beforeFirst reserve : Nat)
    (word : List Bool) (rankState : PackedReviewerRankState)
    (reference : WordRAM.TraceResult Nat)
    (continuation : Nat -> WordRAM.TraceResult (Option Nat))
    (hrankStart : packedReviewerRankResult rankState = none)
    (hrank :
      (packedReviewerDriveRank store
        (packedReviewerRankRemaining rankState) rankState).Simulates
          reference PackedReviewerRankState.done)
    (hcontinuation :
      (packedReviewerDriveSelect store reserve
        (packedReviewerSelectAfterDenseUptoRank invocation n index basePosition
          baseOccurrence beforeFirst word reference.value)).Simulates
        (continuation reference.value) PackedReviewerSelectState.done) :
    (packedReviewerDriveSelect store
      (packedReviewerRankRemaining rankState + reserve)
      (.denseUptoRank invocation n index basePosition baseOccurrence
        beforeFirst word rankState)).Simulates
      (WordRAM.TraceResult.bind reference continuation)
      PackedReviewerSelectState.done := by
  apply packedReviewerDriveComponent_embedded_phase_simulates
    packedReviewerRankResult packedReviewerRankNextRequest
    packedReviewerRankConsumeReply packedReviewerSelectResult
    packedReviewerSelectNextRequest packedReviewerSelectConsumeReply
    (fun rank =>
      .denseUptoRank invocation n index basePosition baseOccurrence
        beforeFirst word rank)
    (packedReviewerSelectAfterDenseUptoRank invocation n index basePosition
      baseOccurrence beforeFirst word)
    PackedReviewerRankState.done PackedReviewerSelectState.done
    store (packedReviewerRankRemaining rankState) reserve rankState reference
    continuation hrankStart (by simpa [packedReviewerDriveRank] using hrank)
    (by simpa [packedReviewerDriveSelect] using hcontinuation)
  · intros
    rfl
  · intros
    rfl
  · intro state reply _
    simp only [packedReviewerSelectConsumeReply]
    cases hnext : packedReviewerRankResult
        (packedReviewerRankConsumeReply state reply) <;> simp [hnext]

private theorem packedReviewerDriveSelect_denseFirstSelect_splice
    (store : WordRAM.ReadStore) (invocation : PackedReviewerInvocation)
    (n baseWord : Nat) (selectState : PackedReviewerWordSelectState)
    (reference : WordRAM.TraceResult (Option Nat))
    (hselectStart : packedReviewerWordSelectResult selectState = none)
    (hselect :
      (packedReviewerDriveWordSelect store
        (packedReviewerWordSelectRemaining selectState) selectState).Simulates
          reference PackedReviewerWordSelectState.done) :
    (packedReviewerDriveSelect store
      (packedReviewerWordSelectRemaining selectState)
      (.denseFirstSelect invocation n baseWord selectState)).Simulates
        (WordRAM.TraceResult.map
          (fun local? =>
            local?.map
              (fun offset => baseWord * packedSelectWordSize n + offset))
          reference)
        PackedReviewerSelectState.done := by
  let finish : Option Nat -> Option Nat :=
    fun local? =>
      local?.map (fun offset => baseWord * packedSelectWordSize n + offset)
  have hphase :=
    packedReviewerDriveComponent_embedded_phase_simulates
      packedReviewerWordSelectResult packedReviewerWordSelectNextRequest
      packedReviewerWordSelectConsumeReply packedReviewerSelectResult
      packedReviewerSelectNextRequest packedReviewerSelectConsumeReply
      (fun select => .denseFirstSelect invocation n baseWord select)
      (fun local? => .done (finish local?))
      PackedReviewerWordSelectState.done PackedReviewerSelectState.done
      store (packedReviewerWordSelectRemaining selectState) 0 selectState
      reference (fun local? => WordRAM.TraceResult.pure (finish local?))
      hselectStart (by simpa [packedReviewerDriveWordSelect] using hselect)
      (by simp [packedReviewerDriveSelect, packedReviewerDriveComponent,
        packedReviewerSelectResult, PackedReviewerComponentRun.Simulates,
        WordRAM.TraceResult.pure])
      (by intros; rfl) (by intros; rfl)
      (by
        intro state reply _
        simp only [packedReviewerSelectConsumeReply]
        cases hnext : packedReviewerWordSelectResult
            (packedReviewerWordSelectConsumeReply state reply) <;>
          simp [hnext, finish])
  simpa [WordRAM.TraceResult.map, finish] using hphase

private theorem packedReviewerDriveSelect_denseSecondSelect_splice
    (store : WordRAM.ReadStore) (invocation : PackedReviewerInvocation)
    (n baseWord : Nat) (selectState : PackedReviewerWordSelectState)
    (reference : WordRAM.TraceResult (Option Nat))
    (hselectStart : packedReviewerWordSelectResult selectState = none)
    (hselect :
      (packedReviewerDriveWordSelect store
        (packedReviewerWordSelectRemaining selectState) selectState).Simulates
          reference PackedReviewerWordSelectState.done) :
    (packedReviewerDriveSelect store
      (packedReviewerWordSelectRemaining selectState)
      (.denseSecondSelect invocation n baseWord selectState)).Simulates
        (WordRAM.TraceResult.map
          (fun local? =>
            local?.map
              (fun offset => baseWord * packedSelectWordSize n + offset))
          reference)
        PackedReviewerSelectState.done := by
  let finish : Option Nat -> Option Nat :=
    fun local? =>
      local?.map (fun offset => baseWord * packedSelectWordSize n + offset)
  have hphase :=
    packedReviewerDriveComponent_embedded_phase_simulates
      packedReviewerWordSelectResult packedReviewerWordSelectNextRequest
      packedReviewerWordSelectConsumeReply packedReviewerSelectResult
      packedReviewerSelectNextRequest packedReviewerSelectConsumeReply
      (fun select => .denseSecondSelect invocation n baseWord select)
      (fun local? => .done (finish local?))
      PackedReviewerWordSelectState.done PackedReviewerSelectState.done
      store (packedReviewerWordSelectRemaining selectState) 0 selectState
      reference (fun local? => WordRAM.TraceResult.pure (finish local?))
      hselectStart (by simpa [packedReviewerDriveWordSelect] using hselect)
      (by simp [packedReviewerDriveSelect, packedReviewerDriveComponent,
        packedReviewerSelectResult, PackedReviewerComponentRun.Simulates,
        WordRAM.TraceResult.pure])
      (by intros; rfl) (by intros; rfl)
      (by
        intro state reply _
        simp only [packedReviewerSelectConsumeReply]
        cases hnext : packedReviewerWordSelectResult
            (packedReviewerWordSelectConsumeReply state reply) <;>
          simp [hnext, finish])
  simpa [WordRAM.TraceResult.map, finish] using hphase

private theorem packedReviewerDriveSelect_pad
    (store : WordRAM.ReadStore) (fuel target : Nat)
    (state : PackedReviewerSelectState)
    (reference : WordRAM.TraceResult (Option Nat))
    (hle : fuel <= target)
    (h : (packedReviewerDriveSelect store fuel state).Simulates reference
      PackedReviewerSelectState.done) :
    (packedReviewerDriveSelect store target state).Simulates reference
      PackedReviewerSelectState.done := by
  have hpad :=
    packedReviewerDriveComponent_add_fuel_of_simulates
      packedReviewerSelectResult packedReviewerSelectNextRequest
      packedReviewerSelectConsumeReply store fuel (target - fuel) state
      reference PackedReviewerSelectState.done
      (by simpa [packedReviewerDriveSelect] using h)
  simpa [packedReviewerDriveSelect, Nat.add_sub_of_le hle] using hpad

private theorem packedReviewerRankStartFold_remaining_le_eight
    (invocation : PackedReviewerInvocation) (n : Nat) (word : List Bool)
    (limit : Nat) :
    packedReviewerRankRemaining
      (packedReviewerRankStartFold invocation .close n word limit 0) <= 8 := by
  let effectiveLimit := SuccinctClose.bpWordRankEffLimit word limit
  let count :=
    SuccinctClose.bpWordChunkCount (packedFringeChunkBits n) effectiveLimit
  by_cases hcount : count = 0
  · simp [packedReviewerRankStartFold, effectiveLimit, count, hcount,
      packedReviewerRankRemaining]
  · simpa [packedReviewerRankStartFold, effectiveLimit, count, hcount,
      packedReviewerRankRemaining] using
      (SuccinctClose.bpWordChunkCount_le_eight (packedFringeChunkBits n)
        effectiveLimit)

private theorem packedReviewerWordSelectStart_remaining_le_nine
    (invocation : PackedReviewerInvocation) (n : Nat) (word : List Bool)
    (occurrence : Nat) :
    packedReviewerWordSelectRemaining
      (packedReviewerWordSelectStart invocation n false word occurrence) <= 9 := by
  let count :=
    SuccinctClose.bpWordChunkCount (packedFringeChunkBits n) word.length
  by_cases hcount : count = 0
  · simp [packedReviewerWordSelectStart, count, hcount,
      packedReviewerWordSelectRemaining]
  · have hle :=
      SuccinctClose.bpWordChunkCount_le_eight (packedFringeChunkBits n)
        word.length
    simp only [packedReviewerWordSelectStart, count, hcount, if_false,
      packedReviewerWordSelectRemaining]
    omega

private theorem packedReviewerDriveSelect_normalizedFirstSelect_simulates
    (store : WordRAM.ReadStore) (invocation : PackedReviewerInvocation)
    (n baseWord : Nat) (word : List Bool) (occurrence : Nat) :
    let selectState :=
      packedReviewerWordSelectStart invocation n false word occurrence
    let state :=
      match packedReviewerWordSelectResult selectState with
      | some local? =>
          PackedReviewerSelectState.done
            (local?.map
              (fun offset => baseWord * packedSelectWordSize n + offset))
      | none =>
          PackedReviewerSelectState.denseFirstSelect invocation n baseWord
            selectState
    let reference :=
      WordRAM.TraceResult.map
        (fun local? =>
          local?.map
            (fun offset => baseWord * packedSelectWordSize n + offset))
        (SuccinctClose.bpChunkedWordSelectTraceResultAtSegmentsWithStore store
          21 22 (packedFringeChunkBits n) false word occurrence)
    (packedReviewerDriveSelect store 9 state).Simulates reference
      PackedReviewerSelectState.done := by
  let count :=
    SuccinctClose.bpWordChunkCount (packedFringeChunkBits n) word.length
  let selectState :=
    packedReviewerWordSelectStart invocation n false word occurrence
  let reference :=
    SuccinctClose.bpChunkedWordSelectTraceResultAtSegmentsWithStore store 21
      22 (packedFringeChunkBits n) false word occurrence
  have hselect :=
    packedReviewerDriveWordSelect_simulates store invocation n false word
      occurrence
  by_cases hcount : count = 0
  · simp [selectState, count, hcount, packedReviewerWordSelectStart,
      packedReviewerWordSelectResult, packedReviewerDriveSelect,
      packedReviewerDriveComponent, packedReviewerSelectResult, reference,
      SuccinctClose.bpChunkedWordSelectTraceResultAtSegmentsWithStore,
      SuccinctClose.bpChunkedWordSelectTraceFromWithStore,
      WordRAM.TraceResult.map, WordRAM.TraceResult.bind,
      WordRAM.TraceResult.pure, PackedReviewerComponentRun.Simulates]
  · have hstart : packedReviewerWordSelectResult selectState = none := by
      simp [selectState, packedReviewerWordSelectStart, count, hcount,
        packedReviewerWordSelectResult]
    have hsplice :=
      packedReviewerDriveSelect_denseFirstSelect_splice store invocation n
        baseWord selectState reference hstart
        (by simpa [selectState, reference] using hselect)
    have hle :=
      packedReviewerWordSelectStart_remaining_le_nine invocation n word
        occurrence
    have hpad :=
      packedReviewerDriveSelect_pad store
        (packedReviewerWordSelectRemaining selectState) 9
        (.denseFirstSelect invocation n baseWord selectState)
        (WordRAM.TraceResult.map
          (fun local? =>
            local?.map
              (fun offset => baseWord * packedSelectWordSize n + offset))
          reference)
        (by simpa [selectState] using hle) hsplice
    simpa [selectState, reference, hstart] using hpad

private theorem packedReviewerDriveSelect_normalizedSecondSelect_simulates
    (store : WordRAM.ReadStore) (invocation : PackedReviewerInvocation)
    (n baseWord : Nat) (word : List Bool) (occurrence : Nat) :
    let selectState :=
      packedReviewerWordSelectStart invocation n false word occurrence
    let state :=
      match packedReviewerWordSelectResult selectState with
      | some local? =>
          PackedReviewerSelectState.done
            (local?.map
              (fun offset => baseWord * packedSelectWordSize n + offset))
      | none =>
          PackedReviewerSelectState.denseSecondSelect invocation n baseWord
            selectState
    let reference :=
      WordRAM.TraceResult.map
        (fun local? =>
          local?.map
            (fun offset => baseWord * packedSelectWordSize n + offset))
        (SuccinctClose.bpChunkedWordSelectTraceResultAtSegmentsWithStore store
          21 22 (packedFringeChunkBits n) false word occurrence)
    (packedReviewerDriveSelect store 9 state).Simulates reference
      PackedReviewerSelectState.done := by
  let count :=
    SuccinctClose.bpWordChunkCount (packedFringeChunkBits n) word.length
  let selectState :=
    packedReviewerWordSelectStart invocation n false word occurrence
  let reference :=
    SuccinctClose.bpChunkedWordSelectTraceResultAtSegmentsWithStore store 21
      22 (packedFringeChunkBits n) false word occurrence
  have hselect :=
    packedReviewerDriveWordSelect_simulates store invocation n false word
      occurrence
  by_cases hcount : count = 0
  · simp [selectState, count, hcount, packedReviewerWordSelectStart,
      packedReviewerWordSelectResult, packedReviewerDriveSelect,
      packedReviewerDriveComponent, packedReviewerSelectResult, reference,
      SuccinctClose.bpChunkedWordSelectTraceResultAtSegmentsWithStore,
      SuccinctClose.bpChunkedWordSelectTraceFromWithStore,
      WordRAM.TraceResult.map, WordRAM.TraceResult.bind,
      WordRAM.TraceResult.pure, PackedReviewerComponentRun.Simulates]
  · have hstart : packedReviewerWordSelectResult selectState = none := by
      simp [selectState, packedReviewerWordSelectStart, count, hcount,
        packedReviewerWordSelectResult]
    have hsplice :=
      packedReviewerDriveSelect_denseSecondSelect_splice store invocation n
        baseWord selectState reference hstart
        (by simpa [selectState, reference] using hselect)
    have hle :=
      packedReviewerWordSelectStart_remaining_le_nine invocation n word
        occurrence
    have hpad :=
      packedReviewerDriveSelect_pad store
        (packedReviewerWordSelectRemaining selectState) 9
        (.denseSecondSelect invocation n baseWord selectState)
        (WordRAM.TraceResult.map
          (fun local? =>
            local?.map
              (fun offset => baseWord * packedSelectWordSize n + offset))
          reference)
        (by simpa [selectState] using hle) hsplice
    simpa [selectState, reference, hstart] using hpad

private theorem packedReviewerDriveSelect_denseSecondWord_simulates
    (store : WordRAM.ReadStore) (invocation : PackedReviewerInvocation)
    (n index basePosition baseOccurrence beforeFirst uptoFirst : Nat) :
    let state : PackedReviewerSelectState :=
      .denseSecondWord invocation n index basePosition baseOccurrence
        beforeFirst uptoFirst
    let reference :=
      WordRAM.TraceResult.bind
        (SuccinctClose.bpWordReadTraceResult store 0
          (basePosition / packedSelectWordSize n + 1))
        fun secondWord? =>
          match secondWord? with
          | none => WordRAM.TraceResult.pure none
          | some secondWord =>
              WordRAM.TraceResult.map
                (fun local? =>
                  local?.map fun offset =>
                    (basePosition / packedSelectWordSize n + 1) *
                        packedSelectWordSize n +
                      offset)
                (SuccinctClose.bpChunkedWordSelectTraceResultAtSegmentsWithStore
                  store 21 22 (packedFringeChunkBits n) false secondWord
                  (index - baseOccurrence - (uptoFirst - beforeFirst)))
    (packedReviewerDriveSelect store 10 state).Simulates reference
      PackedReviewerSelectState.done := by
  let slot := basePosition / packedSelectWordSize n + 1
  let request : PackedReviewerLogicalRequest :=
    { invocation := invocation
      site := .denseBPWord slot
      segment := 0
      index := slot }
  let after :=
    packedReviewerSelectAfterDenseSecondWord invocation n index basePosition
      baseOccurrence beforeFirst uptoFirst
  let continuation : Option (List Bool) ->
      WordRAM.TraceResult (Option Nat)
    | none => WordRAM.TraceResult.pure none
    | some secondWord =>
        WordRAM.TraceResult.map
          (fun local? =>
            local?.map fun offset =>
              slot * packedSelectWordSize n + offset)
          (SuccinctClose.bpChunkedWordSelectTraceResultAtSegmentsWithStore
            store 21 22 (packedFringeChunkBits n) false secondWord
            (index - baseOccurrence - (uptoFirst - beforeFirst)))
  apply packedReviewerDriveSelect_readWord_splice store 9
    (.denseSecondWord invocation n index basePosition baseOccurrence
      beforeFirst uptoFirst)
    request after continuation
  · rfl
  · rfl
  · intro reply
    rfl
  · cases hreply : store.readWord? request.segment request.index with
    | none =>
        simp [after, continuation, packedReviewerSelectAfterDenseSecondWord,
          packedReviewerDriveSelect, packedReviewerDriveComponent,
          packedReviewerSelectResult, PackedReviewerComponentRun.Simulates,
          WordRAM.TraceResult.pure, hreply]
    | some secondWord =>
        have hnormalized :=
          packedReviewerDriveSelect_normalizedSecondSelect_simulates store
            invocation n slot secondWord
            (index - baseOccurrence - (uptoFirst - beforeFirst))
        simpa [after, continuation,
          packedReviewerSelectAfterDenseSecondWord, slot, request, hreply]
          using hnormalized

private theorem packedReviewerDriveSelect_afterDenseUpto_simulates
    (store : WordRAM.ReadStore) (invocation : PackedReviewerInvocation)
    (n index basePosition baseOccurrence beforeFirst : Nat)
    (word : List Bool) (uptoFirst : Nat) :
    let localOccurrence := index - baseOccurrence
    let baseWord := basePosition / packedSelectWordSize n
    let reference :=
      if localOccurrence < uptoFirst - beforeFirst then
        WordRAM.TraceResult.map
          (fun local? =>
            local?.map fun offset =>
              baseWord * packedSelectWordSize n + offset)
          (SuccinctClose.bpChunkedWordSelectTraceResultAtSegmentsWithStore
            store 21 22 (packedFringeChunkBits n) false word
            (beforeFirst + localOccurrence))
      else
        WordRAM.TraceResult.bind
          (SuccinctClose.bpWordReadTraceResult store 0 (baseWord + 1))
          fun secondWord? =>
            match secondWord? with
            | none => WordRAM.TraceResult.pure none
            | some secondWord =>
                WordRAM.TraceResult.map
                  (fun local? =>
                    local?.map fun offset =>
                      (baseWord + 1) * packedSelectWordSize n + offset)
                  (SuccinctClose.bpChunkedWordSelectTraceResultAtSegmentsWithStore
                    store 21 22 (packedFringeChunkBits n) false secondWord
                    (index - baseOccurrence -
                      (uptoFirst - beforeFirst)))
    (packedReviewerDriveSelect store 10
      (packedReviewerSelectAfterDenseUptoRank invocation n index basePosition
        baseOccurrence beforeFirst word uptoFirst)).Simulates
      reference PackedReviewerSelectState.done := by
  let localOccurrence := index - baseOccurrence
  let baseWord := basePosition / packedSelectWordSize n
  by_cases hlocal : localOccurrence < uptoFirst - beforeFirst
  · have hfirst :=
      packedReviewerDriveSelect_normalizedFirstSelect_simulates store
        invocation n baseWord word (beforeFirst + localOccurrence)
    have hpad :=
      packedReviewerDriveSelect_pad store 9 10
        (match packedReviewerWordSelectResult
            (packedReviewerWordSelectStart invocation n false word
              (beforeFirst + localOccurrence)) with
        | some local? =>
            .done
              (local?.map
                (fun offset => baseWord * packedSelectWordSize n + offset))
        | none =>
            .denseFirstSelect invocation n baseWord
              (packedReviewerWordSelectStart invocation n false word
                (beforeFirst + localOccurrence)))
        (WordRAM.TraceResult.map
          (fun local? =>
            local?.map
              (fun offset => baseWord * packedSelectWordSize n + offset))
          (SuccinctClose.bpChunkedWordSelectTraceResultAtSegmentsWithStore
            store 21 22 (packedFringeChunkBits n) false word
            (beforeFirst + localOccurrence)))
        (by omega) hfirst
    simpa [packedReviewerSelectAfterDenseUptoRank, localOccurrence, baseWord,
      hlocal] using hpad
  · have hsecond :=
      packedReviewerDriveSelect_denseSecondWord_simulates store invocation n
        index basePosition baseOccurrence beforeFirst uptoFirst
    simpa [packedReviewerSelectAfterDenseUptoRank, localOccurrence, baseWord,
      hlocal] using hsecond

private theorem packedReviewerDriveSelect_afterDenseBefore_simulates
    (store : WordRAM.ReadStore) (invocation : PackedReviewerInvocation)
    (n index basePosition baseOccurrence : Nat) (word : List Bool)
    (beforeFirst : Nat) :
    let uptoReference :=
      SuccinctClose.bpChunkedWordRankTraceResultAtSegmentWithStore store 21
        (packedFringeChunkBits n) false word word.length
    let reference :=
      WordRAM.TraceResult.bind uptoReference fun uptoFirst =>
        let localOccurrence := index - baseOccurrence
        let baseWord := basePosition / packedSelectWordSize n
        if localOccurrence < uptoFirst - beforeFirst then
          WordRAM.TraceResult.map
            (fun local? =>
              local?.map fun offset =>
                baseWord * packedSelectWordSize n + offset)
            (SuccinctClose.bpChunkedWordSelectTraceResultAtSegmentsWithStore
              store 21 22 (packedFringeChunkBits n) false word
              (beforeFirst + localOccurrence))
        else
          WordRAM.TraceResult.bind
            (SuccinctClose.bpWordReadTraceResult store 0 (baseWord + 1))
            fun secondWord? =>
              match secondWord? with
              | none => WordRAM.TraceResult.pure none
              | some secondWord =>
                  WordRAM.TraceResult.map
                    (fun local? =>
                      local?.map fun offset =>
                        (baseWord + 1) * packedSelectWordSize n + offset)
                    (SuccinctClose.bpChunkedWordSelectTraceResultAtSegmentsWithStore
                      store 21 22 (packedFringeChunkBits n) false secondWord
                      (index - baseOccurrence -
                        (uptoFirst - beforeFirst)))
    (packedReviewerDriveSelect store 18
      (packedReviewerSelectAfterDenseBeforeRank invocation n index
        basePosition baseOccurrence word beforeFirst)).Simulates
      reference PackedReviewerSelectState.done := by
  let rankState :=
    packedReviewerRankStartFold invocation .close n word word.length 0
  let rankReference :=
    SuccinctClose.bpChunkedWordRankTraceResultAtSegmentWithStore store 21
      (packedFringeChunkBits n) false word word.length
  let continuation : Nat -> WordRAM.TraceResult (Option Nat) :=
    fun uptoFirst =>
      let localOccurrence := index - baseOccurrence
      let baseWord := basePosition / packedSelectWordSize n
      if localOccurrence < uptoFirst - beforeFirst then
        WordRAM.TraceResult.map
          (fun local? =>
            local?.map fun offset =>
              baseWord * packedSelectWordSize n + offset)
          (SuccinctClose.bpChunkedWordSelectTraceResultAtSegmentsWithStore
            store 21 22 (packedFringeChunkBits n) false word
            (beforeFirst + localOccurrence))
      else
        WordRAM.TraceResult.bind
          (SuccinctClose.bpWordReadTraceResult store 0 (baseWord + 1))
          fun secondWord? =>
            match secondWord? with
            | none => WordRAM.TraceResult.pure none
            | some secondWord =>
                WordRAM.TraceResult.map
                  (fun local? =>
                    local?.map fun offset =>
                      (baseWord + 1) * packedSelectWordSize n + offset)
                  (SuccinctClose.bpChunkedWordSelectTraceResultAtSegmentsWithStore
                    store 21 22 (packedFringeChunkBits n) false secondWord
                    (index - baseOccurrence -
                      (uptoFirst - beforeFirst)))
  let count :=
    SuccinctClose.bpWordChunkCount (packedFringeChunkBits n)
      (SuccinctClose.bpWordRankEffLimit word word.length)
  have hrank :=
    packedReviewerDriveRankStartFold_zeroBase_simulates store invocation n
      word word.length
  by_cases hcount : count = 0
  · have hnext :=
      packedReviewerDriveSelect_afterDenseUpto_simulates store invocation n
        index basePosition baseOccurrence beforeFirst word 0
    have hpad :=
      packedReviewerDriveSelect_pad store 10 18
        (packedReviewerSelectAfterDenseUptoRank invocation n index basePosition
          baseOccurrence beforeFirst word 0)
        (continuation 0) (by omega)
        (by simpa [continuation] using hnext)
    simpa [packedReviewerSelectAfterDenseBeforeRank, rankState, count, hcount,
      packedReviewerRankStartFold, packedReviewerRankResult, rankReference,
      continuation, SuccinctClose.bpChunkedWordRankTraceResultAtSegmentWithStore,
      SuccinctClose.bpChunkedWordRankTraceFromWithStore,
      WordRAM.TraceResult.bind, WordRAM.TraceResult.pure] using hpad
  · have hstart : packedReviewerRankResult rankState = none := by
      simp [rankState, packedReviewerRankStartFold, count, hcount,
        packedReviewerRankResult]
    have hnext :=
      packedReviewerDriveSelect_afterDenseUpto_simulates store invocation n
        index basePosition baseOccurrence beforeFirst word rankReference.value
    have hsplice :=
      packedReviewerDriveSelect_denseUptoRank_splice store invocation n index
        basePosition baseOccurrence beforeFirst 10 word rankState rankReference
        continuation hstart
        (by simpa [rankState, rankReference] using hrank)
        (by simpa [continuation] using hnext)
    have hle :=
      packedReviewerRankStartFold_remaining_le_eight invocation n word
        word.length
    have hle' : packedReviewerRankRemaining rankState <= 8 := by
      dsimp only [rankState]
      exact hle
    have hpad :=
      packedReviewerDriveSelect_pad store
        (packedReviewerRankRemaining rankState + 10) 18
        (.denseUptoRank invocation n index basePosition baseOccurrence
          beforeFirst word rankState)
        (WordRAM.TraceResult.bind rankReference continuation)
        (by omega) hsplice
    simpa [packedReviewerSelectAfterDenseBeforeRank, rankState, rankReference,
      continuation, hstart] using hpad

private theorem packedReviewerDriveSelect_afterDenseFirst_some_simulates
    (store : WordRAM.ReadStore) (invocation : PackedReviewerInvocation)
    (n index basePosition baseOccurrence : Nat) (word : List Bool) :
    let wordSize := packedSelectWordSize n
    let beforeLimit := basePosition - basePosition / wordSize * wordSize
    let beforeReference :=
      SuccinctClose.bpChunkedWordRankTraceResultAtSegmentWithStore store 21
        (packedFringeChunkBits n) false word beforeLimit
    let continuation : Nat -> WordRAM.TraceResult (Option Nat) :=
      fun beforeFirst =>
        let uptoReference :=
          SuccinctClose.bpChunkedWordRankTraceResultAtSegmentWithStore store 21
            (packedFringeChunkBits n) false word word.length
        WordRAM.TraceResult.bind uptoReference fun uptoFirst =>
          let localOccurrence := index - baseOccurrence
          let baseWord := basePosition / packedSelectWordSize n
          if localOccurrence < uptoFirst - beforeFirst then
            WordRAM.TraceResult.map
              (fun local? =>
                local?.map fun offset =>
                  baseWord * packedSelectWordSize n + offset)
              (SuccinctClose.bpChunkedWordSelectTraceResultAtSegmentsWithStore
                store 21 22 (packedFringeChunkBits n) false word
                (beforeFirst + localOccurrence))
          else
            WordRAM.TraceResult.bind
              (SuccinctClose.bpWordReadTraceResult store 0 (baseWord + 1))
              fun secondWord? =>
                match secondWord? with
                | none => WordRAM.TraceResult.pure none
                | some secondWord =>
                    WordRAM.TraceResult.map
                      (fun local? =>
                        local?.map fun offset =>
                          (baseWord + 1) * packedSelectWordSize n + offset)
                      (SuccinctClose.bpChunkedWordSelectTraceResultAtSegmentsWithStore
                        store 21 22 (packedFringeChunkBits n) false secondWord
                        (index - baseOccurrence -
                          (uptoFirst - beforeFirst)))
    (packedReviewerDriveSelect store 26
      (packedReviewerSelectAfterDenseFirstWord invocation n index
        basePosition baseOccurrence (some word))).Simulates
      (WordRAM.TraceResult.bind beforeReference continuation)
      PackedReviewerSelectState.done := by
  let wordSize := packedSelectWordSize n
  let beforeLimit := basePosition - basePosition / wordSize * wordSize
  let rankState :=
    packedReviewerRankStartFold invocation .close n word beforeLimit 0
  let rankReference :=
    SuccinctClose.bpChunkedWordRankTraceResultAtSegmentWithStore store 21
      (packedFringeChunkBits n) false word beforeLimit
  let continuation : Nat -> WordRAM.TraceResult (Option Nat) :=
    fun beforeFirst =>
      let uptoReference :=
        SuccinctClose.bpChunkedWordRankTraceResultAtSegmentWithStore store 21
          (packedFringeChunkBits n) false word word.length
      WordRAM.TraceResult.bind uptoReference fun uptoFirst =>
        let localOccurrence := index - baseOccurrence
        let baseWord := basePosition / packedSelectWordSize n
        if localOccurrence < uptoFirst - beforeFirst then
          WordRAM.TraceResult.map
            (fun local? =>
              local?.map fun offset =>
                baseWord * packedSelectWordSize n + offset)
            (SuccinctClose.bpChunkedWordSelectTraceResultAtSegmentsWithStore
              store 21 22 (packedFringeChunkBits n) false word
              (beforeFirst + localOccurrence))
        else
          WordRAM.TraceResult.bind
            (SuccinctClose.bpWordReadTraceResult store 0 (baseWord + 1))
            fun secondWord? =>
              match secondWord? with
              | none => WordRAM.TraceResult.pure none
              | some secondWord =>
                  WordRAM.TraceResult.map
                    (fun local? =>
                      local?.map fun offset =>
                        (baseWord + 1) * packedSelectWordSize n + offset)
                    (SuccinctClose.bpChunkedWordSelectTraceResultAtSegmentsWithStore
                      store 21 22 (packedFringeChunkBits n) false secondWord
                      (index - baseOccurrence -
                        (uptoFirst - beforeFirst)))
  let count :=
    SuccinctClose.bpWordChunkCount (packedFringeChunkBits n)
      (SuccinctClose.bpWordRankEffLimit word beforeLimit)
  have hrank :=
    packedReviewerDriveRankStartFold_zeroBase_simulates store invocation n
      word beforeLimit
  by_cases hcount : count = 0
  · have hnext :=
      packedReviewerDriveSelect_afterDenseBefore_simulates store invocation n
        index basePosition baseOccurrence word 0
    have hpad :=
      packedReviewerDriveSelect_pad store 18 26
        (packedReviewerSelectAfterDenseBeforeRank invocation n index
          basePosition baseOccurrence word 0)
        (continuation 0) (by omega)
        (by simpa [continuation] using hnext)
    simpa [packedReviewerSelectAfterDenseFirstWord, rankState, count, hcount,
      packedReviewerRankStartFold, packedReviewerRankResult, rankReference,
      continuation, beforeLimit, wordSize,
      SuccinctClose.bpChunkedWordRankTraceResultAtSegmentWithStore,
      SuccinctClose.bpChunkedWordRankTraceFromWithStore,
      WordRAM.TraceResult.bind, WordRAM.TraceResult.pure] using hpad
  · have hstart : packedReviewerRankResult rankState = none := by
      simp [rankState, packedReviewerRankStartFold, count, hcount,
        packedReviewerRankResult]
    have hnext :=
      packedReviewerDriveSelect_afterDenseBefore_simulates store invocation n
        index basePosition baseOccurrence word rankReference.value
    have hsplice :=
      packedReviewerDriveSelect_denseBeforeRank_splice store invocation n index
        basePosition baseOccurrence 18 word rankState rankReference
        continuation hstart
        (by simpa [rankState, rankReference] using hrank)
        (by simpa [continuation] using hnext)
    have hle :=
      packedReviewerRankStartFold_remaining_le_eight invocation n word
        beforeLimit
    have hle' : packedReviewerRankRemaining rankState <= 8 := by
      dsimp only [rankState]
      exact hle
    have hpad :=
      packedReviewerDriveSelect_pad store
        (packedReviewerRankRemaining rankState + 18) 26
        (.denseBeforeRank invocation n index basePosition baseOccurrence word
          rankState)
        (WordRAM.TraceResult.bind rankReference continuation)
        (by omega) hsplice
    simpa [packedReviewerSelectAfterDenseFirstWord, rankState, rankReference,
      continuation, hstart, beforeLimit, wordSize, count, hcount,
      packedReviewerRankStartFold, packedReviewerRankResult] using hpad

private theorem packedReviewerDriveSelect_dense_simulates
    (store : WordRAM.ReadStore) (invocation : PackedReviewerInvocation)
    (n index basePosition baseOccurrence : Nat) :
    (packedReviewerDriveSelect store 27
      (.denseFirstWord invocation n index basePosition
        baseOccurrence)).Simulates
      (packedDenseTwoWordSelectRead 0 21 22 (packedFringeChunkBits n) false
        store (packedSelectWordSize n) basePosition baseOccurrence index)
      PackedReviewerSelectState.done := by
  let slot := basePosition / packedSelectWordSize n
  let request : PackedReviewerLogicalRequest :=
    { invocation := invocation
      site := .denseBPWord slot
      segment := 0
      index := slot }
  let after :=
    packedReviewerSelectAfterDenseFirstWord invocation n index basePosition
      baseOccurrence
  let continuation : Option (List Bool) ->
      WordRAM.TraceResult (Option Nat)
    | none => WordRAM.TraceResult.pure none
    | some word =>
        let wordSize := packedSelectWordSize n
        let beforeLimit := basePosition - basePosition / wordSize * wordSize
        WordRAM.TraceResult.bind
          (SuccinctClose.bpChunkedWordRankTraceResultAtSegmentWithStore store 21
            (packedFringeChunkBits n) false word beforeLimit)
          fun beforeFirst =>
            WordRAM.TraceResult.bind
              (SuccinctClose.bpChunkedWordRankTraceResultAtSegmentWithStore
                store 21 (packedFringeChunkBits n) false word word.length)
              fun uptoFirst =>
                let localOccurrence := index - baseOccurrence
                let baseWord := basePosition / packedSelectWordSize n
                if localOccurrence < uptoFirst - beforeFirst then
                  WordRAM.TraceResult.map
                    (fun local? =>
                      local?.map fun offset =>
                        baseWord * packedSelectWordSize n + offset)
                    (SuccinctClose.bpChunkedWordSelectTraceResultAtSegmentsWithStore
                      store 21 22 (packedFringeChunkBits n) false word
                      (beforeFirst + localOccurrence))
                else
                  WordRAM.TraceResult.bind
                    (SuccinctClose.bpWordReadTraceResult store 0
                      (baseWord + 1))
                    fun secondWord? =>
                      match secondWord? with
                      | none => WordRAM.TraceResult.pure none
                      | some secondWord =>
                          WordRAM.TraceResult.map
                            (fun local? =>
                              local?.map fun offset =>
                                (baseWord + 1) * packedSelectWordSize n +
                                  offset)
                            (SuccinctClose.bpChunkedWordSelectTraceResultAtSegmentsWithStore
                              store 21 22 (packedFringeChunkBits n) false
                              secondWord
                              (index - baseOccurrence -
                                (uptoFirst - beforeFirst)))
  have hsplice :=
    packedReviewerDriveSelect_readWord_splice store 26
      (.denseFirstWord invocation n index basePosition baseOccurrence)
      request after continuation rfl rfl (fun _ => rfl) (by
        cases hreply : store.readWord? request.segment request.index with
        | none =>
            simp [after, continuation, packedReviewerSelectAfterDenseFirstWord,
              packedReviewerDriveSelect, packedReviewerDriveComponent,
              packedReviewerSelectResult, PackedReviewerComponentRun.Simulates,
              WordRAM.TraceResult.pure, hreply]
        | some word =>
            have hword :=
              packedReviewerDriveSelect_afterDenseFirst_some_simulates store
                invocation n index basePosition baseOccurrence word
            simpa [after, continuation, request, hreply] using hword)
  simpa [packedDenseTwoWordSelectRead, slot, request, continuation] using
    hsplice

private theorem packedReviewerDriveSelect_longRank_splice
    (store : WordRAM.ReadStore) (invocation : PackedReviewerInvocation)
    (n index pos reserve : Nat)
    (super : GenericSelect.SparseDenseSelectDenseLocalEntry)
    (continuation : Nat -> WordRAM.TraceResult (Option Nat))
    (hcontinuation :
      let reference :=
        packedRankRead 9 10 11 21 (packedFringeChunkBits n) true store
          (packedSuperSlots n) (packedLongFlagWordSize n) 1 pos
      (packedReviewerDriveSelect store reserve
        (packedReviewerSelectAfterLongRank invocation n index super
          reference.value)).Simulates
        (continuation reference.value) PackedReviewerSelectState.done) :
    let rankState : PackedReviewerRankState :=
      .superSample invocation .selectLong n pos
    let reference :=
      packedRankRead 9 10 11 21 (packedFringeChunkBits n) true store
        (packedSuperSlots n) (packedLongFlagWordSize n) 1 pos
    (packedReviewerDriveSelect store (11 + reserve)
      (.longRank invocation n index super rankState)).Simulates
        (WordRAM.TraceResult.bind reference continuation)
        PackedReviewerSelectState.done := by
  let rankState : PackedReviewerRankState :=
    .superSample invocation .selectLong n pos
  let reference :=
    packedRankRead 9 10 11 21 (packedFringeChunkBits n) true store
      (packedSuperSlots n) (packedLongFlagWordSize n) 1 pos
  have hrank :=
    packedReviewerDriveRank_simulates store invocation
      PackedReviewerRankKind.selectLong n pos
  apply packedReviewerDriveComponent_embedded_phase_simulates
    packedReviewerRankResult packedReviewerRankNextRequest
    packedReviewerRankConsumeReply packedReviewerSelectResult
    packedReviewerSelectNextRequest packedReviewerSelectConsumeReply
    (fun rank => .longRank invocation n index super rank)
    (packedReviewerSelectAfterLongRank invocation n index super)
    PackedReviewerRankState.done PackedReviewerSelectState.done
    store 11 reserve rankState reference continuation
  · rfl
  · simpa [packedReviewerDriveRank, rankState, reference,
      PackedReviewerRankKind.superSegment,
      PackedReviewerRankKind.blockSegment,
      PackedReviewerRankKind.wordSegment,
      PackedReviewerRankKind.bitLength, PackedReviewerRankKind.wordSize,
      PackedReviewerRankKind.blocksPerSuper,
      PackedReviewerRankKind.target] using hrank
  · simpa [packedReviewerDriveSelect, reference] using hcontinuation
  · intros
    rfl
  · intros
    rfl
  · intro state reply _
    simp only [packedReviewerSelectConsumeReply]
    cases hnext : packedReviewerRankResult
        (packedReviewerRankConsumeReply state reply) <;> simp [hnext]

private theorem packedReviewerDriveSelect_sparseRank_splice
    (store : WordRAM.ReadStore) (invocation : PackedReviewerInvocation)
    (n index localSlot reserve : Nat)
    (super loc : GenericSelect.SparseDenseSelectDenseLocalEntry)
    (continuation : Nat -> WordRAM.TraceResult (Option Nat))
    (hcontinuation :
      let reference :=
        packedRankRead 13 14 15 21 (packedFringeChunkBits n) true store
          (packedSparseSlots n) (packedSparseWordSize n) 1 localSlot
      (packedReviewerDriveSelect store reserve
        (packedReviewerSelectAfterSparseRank invocation n index localSlot
          super loc reference.value)).Simulates
        (continuation reference.value) PackedReviewerSelectState.done) :
    let rankState : PackedReviewerRankState :=
      .superSample invocation .selectSparse n localSlot
    let reference :=
      packedRankRead 13 14 15 21 (packedFringeChunkBits n) true store
        (packedSparseSlots n) (packedSparseWordSize n) 1 localSlot
    (packedReviewerDriveSelect store (11 + reserve)
      (.sparseRank invocation n index localSlot super loc rankState)).Simulates
        (WordRAM.TraceResult.bind reference continuation)
        PackedReviewerSelectState.done := by
  let rankState : PackedReviewerRankState :=
    .superSample invocation .selectSparse n localSlot
  let reference :=
    packedRankRead 13 14 15 21 (packedFringeChunkBits n) true store
      (packedSparseSlots n) (packedSparseWordSize n) 1 localSlot
  have hrank :=
    packedReviewerDriveRank_simulates store invocation
      PackedReviewerRankKind.selectSparse n localSlot
  apply packedReviewerDriveComponent_embedded_phase_simulates
    packedReviewerRankResult packedReviewerRankNextRequest
    packedReviewerRankConsumeReply packedReviewerSelectResult
    packedReviewerSelectNextRequest packedReviewerSelectConsumeReply
    (fun rank =>
      .sparseRank invocation n index localSlot super loc rank)
    (packedReviewerSelectAfterSparseRank invocation n index localSlot super loc)
    PackedReviewerRankState.done PackedReviewerSelectState.done
    store 11 reserve rankState reference continuation
  · rfl
  · simpa [packedReviewerDriveRank, rankState, reference,
      PackedReviewerRankKind.superSegment,
      PackedReviewerRankKind.blockSegment,
      PackedReviewerRankKind.wordSegment,
      PackedReviewerRankKind.bitLength, PackedReviewerRankKind.wordSize,
      PackedReviewerRankKind.blocksPerSuper,
      PackedReviewerRankKind.target] using hrank
  · simpa [packedReviewerDriveSelect, reference] using hcontinuation
  · intros
    rfl
  · intros
    rfl
  · intro state reply _
    simp only [packedReviewerSelectConsumeReply]
    cases hnext : packedReviewerRankResult
        (packedReviewerRankConsumeReply state reply) <;> simp [hnext]

private theorem packedReviewerDriveSelect_long_simulates
    (store : WordRAM.ReadStore) (invocation : PackedReviewerInvocation)
    (n index : Nat)
    (super : GenericSelect.SparseDenseSelectDenseLocalEntry) :
    let pos := GenericSelect.selectSuperSlot index (packedSelectSuperStride n)
    let rankState : PackedReviewerRankState :=
      .superSample invocation .selectLong n pos
    let rankReference :=
      packedRankRead 9 10 11 21 (packedFringeChunkBits n) true store
        (packedSuperSlots n) (packedLongFlagWordSize n) 1 pos
    let continuation : Nat -> WordRAM.TraceResult (Option Nat) :=
      fun exceptionRank =>
        GenericSelect.bpRelativeOffsetReadTraceResultWithStore store 12
          (GenericSelect.relativeSplitSelectEntryBasePosition
            (packedSelectWordSize n) super)
          (GenericSelect.relativeSplitSelectLongCompactSlot exceptionRank
            (index - super.baseOccurrence) (packedSelectSuperStride n))
    (packedReviewerDriveSelect store 12
      (.longRank invocation n index super rankState)).Simulates
      (WordRAM.TraceResult.bind rankReference continuation)
      PackedReviewerSelectState.done := by
  let pos := GenericSelect.selectSuperSlot index (packedSelectSuperStride n)
  let rankReference :=
    packedRankRead 9 10 11 21 (packedFringeChunkBits n) true store
      (packedSuperSlots n) (packedLongFlagWordSize n) 1 pos
  let continuation : Nat -> WordRAM.TraceResult (Option Nat) :=
    fun exceptionRank =>
      GenericSelect.bpRelativeOffsetReadTraceResultWithStore store 12
        (GenericSelect.relativeSplitSelectEntryBasePosition
          (packedSelectWordSize n) super)
        (GenericSelect.relativeSplitSelectLongCompactSlot exceptionRank
          (index - super.baseOccurrence) (packedSelectSuperStride n))
  apply packedReviewerDriveSelect_longRank_splice store invocation n index pos
    1 super continuation
  have hrelative :=
    packedReviewerDriveSelect_longRelative_simulates store invocation
      (GenericSelect.relativeSplitSelectEntryBasePosition
        (packedSelectWordSize n) super)
      (GenericSelect.relativeSplitSelectLongCompactSlot rankReference.value
        (index - super.baseOccurrence) (packedSelectSuperStride n))
  simpa [packedReviewerSelectAfterLongRank, continuation, rankReference] using
    hrelative

private theorem packedReviewerDriveSelect_sparse_simulates
    (store : WordRAM.ReadStore) (invocation : PackedReviewerInvocation)
    (n index localSlot : Nat)
    (super loc : GenericSelect.SparseDenseSelectDenseLocalEntry) :
    let rankState : PackedReviewerRankState :=
      .superSample invocation .selectSparse n localSlot
    let rankReference :=
      packedRankRead 13 14 15 21 (packedFringeChunkBits n) true store
        (packedSparseSlots n) (packedSparseWordSize n) 1 localSlot
    let continuation : Nat -> WordRAM.TraceResult (Option Nat) :=
      fun exceptionRank =>
        GenericSelect.bpRelativeOffsetReadTraceResultWithStore store 16
          (GenericSelect.relativeSplitSelectLocalBasePosition
            (packedSelectWordSize n) super loc)
          (GenericSelect.relativeSplitSelectSparseCompactSlot exceptionRank
            (index -
              GenericSelect.relativeSplitSelectLocalBaseOccurrence super loc)
            (packedSelectLocalStride n))
    (packedReviewerDriveSelect store 12
      (.sparseRank invocation n index localSlot super loc
        rankState)).Simulates
      (WordRAM.TraceResult.bind rankReference continuation)
      PackedReviewerSelectState.done := by
  let rankReference :=
    packedRankRead 13 14 15 21 (packedFringeChunkBits n) true store
      (packedSparseSlots n) (packedSparseWordSize n) 1 localSlot
  let continuation : Nat -> WordRAM.TraceResult (Option Nat) :=
    fun exceptionRank =>
      GenericSelect.bpRelativeOffsetReadTraceResultWithStore store 16
        (GenericSelect.relativeSplitSelectLocalBasePosition
          (packedSelectWordSize n) super loc)
        (GenericSelect.relativeSplitSelectSparseCompactSlot exceptionRank
          (index -
            GenericSelect.relativeSplitSelectLocalBaseOccurrence super loc)
          (packedSelectLocalStride n))
  apply packedReviewerDriveSelect_sparseRank_splice store invocation n index
    localSlot 1 super loc continuation
  have hrelative :=
    packedReviewerDriveSelect_sparseRelative_simulates store invocation
      (GenericSelect.relativeSplitSelectLocalBasePosition
        (packedSelectWordSize n) super loc)
      (GenericSelect.relativeSplitSelectSparseCompactSlot rankReference.value
        (index -
          GenericSelect.relativeSplitSelectLocalBaseOccurrence super loc)
        (packedSelectLocalStride n))
  simpa [packedReviewerSelectAfterSparseRank, continuation, rankReference] using
    hrelative

private theorem packedReviewerDriveSelect_afterLocal_simulates
    (store : WordRAM.ReadStore) (invocation : PackedReviewerInvocation)
    (n index localSlot : Nat)
    (super : GenericSelect.SparseDenseSelectDenseLocalEntry)
    (loc? : Option GenericSelect.SparseDenseSelectDenseLocalEntry) :
    let reference : WordRAM.TraceResult (Option Nat) :=
      match loc? with
      | none => WordRAM.TraceResult.pure none
      | some loc =>
          if GenericSelect.relativeSplitSelectEntryIsMarked loc then
            packedSparseDirectoryRead
              concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory
              21 store (packedFringeChunkBits n) (packedSparseSlots n)
              (packedSparseWordSize n) 1 (packedSelectLocalStride n)
              (GenericSelect.relativeSplitSelectLocalBasePosition
                (packedSelectWordSize n) super loc)
              localSlot
              (index -
                GenericSelect.relativeSplitSelectLocalBaseOccurrence super loc)
          else
            packedDenseTwoWordSelectRead 0 21 22 (packedFringeChunkBits n)
              false store (packedSelectWordSize n)
              (GenericSelect.relativeSplitSelectLocalBasePosition
                (packedSelectWordSize n) super loc)
              (GenericSelect.relativeSplitSelectLocalBaseOccurrence super loc)
              index
    (packedReviewerDriveSelect store 27
      (packedReviewerSelectAfterLocal invocation n index localSlot super
        loc?)).Simulates reference PackedReviewerSelectState.done := by
  cases loc? with
  | none =>
      simp [packedReviewerSelectAfterLocal, packedReviewerDriveSelect,
        packedReviewerDriveComponent, packedReviewerSelectResult,
        PackedReviewerComponentRun.Simulates, WordRAM.TraceResult.pure]
  | some loc =>
      by_cases hmarked : GenericSelect.relativeSplitSelectEntryIsMarked loc
      · have hsparse :=
          packedReviewerDriveSelect_sparse_simulates store invocation n index
            localSlot super loc
        have hpad :=
          packedReviewerDriveSelect_pad store 12 27
            (.sparseRank invocation n index localSlot super loc
              (.superSample invocation .selectSparse n localSlot))
            (packedSparseDirectoryRead
              concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory
              21 store (packedFringeChunkBits n) (packedSparseSlots n)
              (packedSparseWordSize n) 1 (packedSelectLocalStride n)
              (GenericSelect.relativeSplitSelectLocalBasePosition
                (packedSelectWordSize n) super loc)
              localSlot
              (index -
                GenericSelect.relativeSplitSelectLocalBaseOccurrence super loc))
            (by omega)
            (by simpa [packedSparseDirectoryRead] using hsparse)
        simpa [packedReviewerSelectAfterLocal, hmarked] using hpad
      · have hdense :=
          packedReviewerDriveSelect_dense_simulates store invocation n index
            (GenericSelect.relativeSplitSelectLocalBasePosition
              (packedSelectWordSize n) super loc)
            (GenericSelect.relativeSplitSelectLocalBaseOccurrence super loc)
        simpa [packedReviewerSelectAfterLocal, hmarked] using hdense

private theorem packedReviewerDriveSelect_afterSuper_simulates
    (store : WordRAM.ReadStore) (invocation : PackedReviewerInvocation)
    (n index : Nat)
    (super? : Option GenericSelect.SparseDenseSelectDenseLocalEntry) :
    let reference : WordRAM.TraceResult (Option Nat) :=
      match super? with
      | none => WordRAM.TraceResult.pure none
      | some super =>
          if GenericSelect.relativeSplitSelectEntryIsMarked super then
            WordRAM.TraceResult.bind
              (packedRankRead 9 10 11 21 (packedFringeChunkBits n) true store
                (packedSuperSlots n) (packedLongFlagWordSize n) 1
                (GenericSelect.selectSuperSlot index
                  (packedSelectSuperStride n)))
              fun exceptionRank =>
                GenericSelect.bpRelativeOffsetReadTraceResultWithStore store 12
                  (GenericSelect.relativeSplitSelectEntryBasePosition
                    (packedSelectWordSize n) super)
                  (GenericSelect.relativeSplitSelectLongCompactSlot
                    exceptionRank (index - super.baseOccurrence)
                    (packedSelectSuperStride n))
          else
            let localSlot :=
              GenericSelect.relativeSplitSelectLocalSlot index
                (packedSelectSuperStride n) (packedSelectLocalSlotsPerSuper n)
                (packedSelectLocalStride n) super
            WordRAM.TraceResult.bind
              (packedSelectEntryRead
                concreteBPNativeSelectCloseTraceSegmentLayout.localTable store
                localSlot)
              fun loc? =>
                match loc? with
                | none => WordRAM.TraceResult.pure none
                | some loc =>
                    if GenericSelect.relativeSplitSelectEntryIsMarked loc then
                      packedSparseDirectoryRead
                        concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory
                        21 store (packedFringeChunkBits n)
                        (packedSparseSlots n) (packedSparseWordSize n) 1
                        (packedSelectLocalStride n)
                        (GenericSelect.relativeSplitSelectLocalBasePosition
                          (packedSelectWordSize n) super loc)
                        localSlot
                        (index -
                          GenericSelect.relativeSplitSelectLocalBaseOccurrence
                            super loc)
                    else
                      packedDenseTwoWordSelectRead 0 21 22
                        (packedFringeChunkBits n) false store
                        (packedSelectWordSize n)
                        (GenericSelect.relativeSplitSelectLocalBasePosition
                          (packedSelectWordSize n) super loc)
                        (GenericSelect.relativeSplitSelectLocalBaseOccurrence
                          super loc)
                        index
    (packedReviewerDriveSelect store 31
      (packedReviewerSelectAfterSuper invocation n index super?)).Simulates
      reference PackedReviewerSelectState.done := by
  cases super? with
  | none =>
      simp [packedReviewerSelectAfterSuper, packedReviewerDriveSelect,
        packedReviewerDriveComponent, packedReviewerSelectResult,
        PackedReviewerComponentRun.Simulates, WordRAM.TraceResult.pure]
  | some super =>
      by_cases hmarked : GenericSelect.relativeSplitSelectEntryIsMarked super
      · have hlong :=
          packedReviewerDriveSelect_long_simulates store invocation n index
            super
        have hpad :=
          packedReviewerDriveSelect_pad store 12 31
            (.longRank invocation n index super
              (.superSample invocation .selectLong n
                (GenericSelect.selectSuperSlot index
                  (packedSelectSuperStride n))))
            (WordRAM.TraceResult.bind
              (packedRankRead 9 10 11 21 (packedFringeChunkBits n) true store
                (packedSuperSlots n) (packedLongFlagWordSize n) 1
                (GenericSelect.selectSuperSlot index
                  (packedSelectSuperStride n)))
              fun exceptionRank =>
                GenericSelect.bpRelativeOffsetReadTraceResultWithStore store 12
                  (GenericSelect.relativeSplitSelectEntryBasePosition
                    (packedSelectWordSize n) super)
                  (GenericSelect.relativeSplitSelectLongCompactSlot
                    exceptionRank (index - super.baseOccurrence)
                    (packedSelectSuperStride n)))
            (by omega) (by simpa using hlong)
        simpa [packedReviewerSelectAfterSuper, hmarked] using hpad
      · let localSlot :=
          GenericSelect.relativeSplitSelectLocalSlot index
            (packedSelectSuperStride n) (packedSelectLocalSlotsPerSuper n)
            (packedSelectLocalStride n) super
        let continuation :
            Option GenericSelect.SparseDenseSelectDenseLocalEntry ->
              WordRAM.TraceResult (Option Nat) :=
          fun loc? =>
            match loc? with
            | none => WordRAM.TraceResult.pure none
            | some loc =>
                if GenericSelect.relativeSplitSelectEntryIsMarked loc then
                  packedSparseDirectoryRead
                    concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory
                    21 store (packedFringeChunkBits n) (packedSparseSlots n)
                    (packedSparseWordSize n) 1 (packedSelectLocalStride n)
                    (GenericSelect.relativeSplitSelectLocalBasePosition
                      (packedSelectWordSize n) super loc)
                    localSlot
                    (index -
                      GenericSelect.relativeSplitSelectLocalBaseOccurrence
                        super loc)
                else
                  packedDenseTwoWordSelectRead 0 21 22
                    (packedFringeChunkBits n) false store
                    (packedSelectWordSize n)
                    (GenericSelect.relativeSplitSelectLocalBasePosition
                      (packedSelectWordSize n) super loc)
                    (GenericSelect.relativeSplitSelectLocalBaseOccurrence
                      super loc)
                    index
        have hlocal :=
          packedReviewerDriveSelect_localEntry_splice store invocation n index
            localSlot 27 super continuation (by
              let reference :=
                packedSelectEntryRead
                  concreteBPNativeSelectCloseTraceSegmentLayout.localTable
                  store localSlot
              have hafter :=
                packedReviewerDriveSelect_afterLocal_simulates store invocation
                  n index localSlot super reference.value
              simpa [continuation, reference] using hafter)
        simpa [packedReviewerSelectAfterSuper, hmarked, localSlot,
          continuation] using hlocal

/-! ## Composite protocol equivalences -/

private theorem packedReviewerDriveSelect_simulates
    (store : WordRAM.ReadStore) (invocation : PackedReviewerInvocation)
    (n index : Nat) (hindex : index < n) :
    let state := packedReviewerSelectStart invocation n index
    let run :=
      packedReviewerDriveSelect store (packedReviewerSelectRemaining state)
        state
    let reference := packedSelectCloseLeaf store n index
    run.Simulates reference PackedReviewerSelectState.done := by
  let slot := GenericSelect.selectSuperSlot index (packedSelectSuperStride n)
  let continuation :
      Option GenericSelect.SparseDenseSelectDenseLocalEntry ->
        WordRAM.TraceResult (Option Nat) :=
    fun super? =>
      match super? with
      | none => WordRAM.TraceResult.pure none
      | some super =>
          if GenericSelect.relativeSplitSelectEntryIsMarked super then
            WordRAM.TraceResult.bind
              (packedRankRead 9 10 11 21 (packedFringeChunkBits n) true store
                (packedSuperSlots n) (packedLongFlagWordSize n) 1 slot)
              fun exceptionRank =>
                GenericSelect.bpRelativeOffsetReadTraceResultWithStore store 12
                  (GenericSelect.relativeSplitSelectEntryBasePosition
                    (packedSelectWordSize n) super)
                  (GenericSelect.relativeSplitSelectLongCompactSlot
                    exceptionRank (index - super.baseOccurrence)
                    (packedSelectSuperStride n))
          else
            let localSlot :=
              GenericSelect.relativeSplitSelectLocalSlot index
                (packedSelectSuperStride n) (packedSelectLocalSlotsPerSuper n)
                (packedSelectLocalStride n) super
            WordRAM.TraceResult.bind
              (packedSelectEntryRead
                concreteBPNativeSelectCloseTraceSegmentLayout.localTable store
                localSlot)
              fun loc? =>
                match loc? with
                | none => WordRAM.TraceResult.pure none
                | some loc =>
                    if GenericSelect.relativeSplitSelectEntryIsMarked loc then
                      packedSparseDirectoryRead
                        concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory
                        21 store (packedFringeChunkBits n)
                        (packedSparseSlots n) (packedSparseWordSize n) 1
                        (packedSelectLocalStride n)
                        (GenericSelect.relativeSplitSelectLocalBasePosition
                          (packedSelectWordSize n) super loc)
                        localSlot
                        (index -
                          GenericSelect.relativeSplitSelectLocalBaseOccurrence
                            super loc)
                    else
                      packedDenseTwoWordSelectRead 0 21 22
                        (packedFringeChunkBits n) false store
                        (packedSelectWordSize n)
                        (GenericSelect.relativeSplitSelectLocalBasePosition
                          (packedSelectWordSize n) super loc)
                        (GenericSelect.relativeSplitSelectLocalBaseOccurrence
                          super loc)
                        index
  have hsuper :=
    packedReviewerDriveSelect_superEntry_splice store invocation n index 31
      continuation (by
        let reference :=
          packedSelectEntryRead
            concreteBPNativeSelectCloseTraceSegmentLayout.superTable store slot
        have hafter :=
          packedReviewerDriveSelect_afterSuper_simulates store invocation n
            index reference.value
        simpa [continuation, reference, slot] using hafter)
  simpa [packedReviewerSelectStart, hindex, packedReviewerSelectRemaining,
    packedReviewerEntryRemaining, packedSelectCloseLeaf,
    packedSelectCloseRead, slot, continuation] using hsuper

private theorem packedReviewerDriveSelect_out_of_range_simulates
    (store : WordRAM.ReadStore) (invocation : PackedReviewerInvocation)
    (n index : Nat) (hindex : ¬ index < n) :
    let state := packedReviewerSelectStart invocation n index
    let run :=
      packedReviewerDriveSelect store (packedReviewerSelectRemaining state)
        state
    let reference := packedSelectCloseLeaf store n index
    run.Simulates reference PackedReviewerSelectState.done := by
  simp [packedReviewerSelectStart, hindex, packedSelectCloseLeaf,
    packedSelectCloseRead, PackedReviewerComponentRun.Simulates,
    packedReviewerDriveSelect, packedReviewerDriveComponent,
    packedReviewerSelectResult, packedReviewerSelectRemaining,
    WordRAM.TraceResult.pure]

private theorem packedReviewerDriveSelect_35_simulates
    (store : WordRAM.ReadStore) (invocation : PackedReviewerInvocation)
    (n index : Nat) (hindex : index < n) :
    (packedReviewerDriveSelect store 35
      (packedReviewerSelectStart invocation n index)).Simulates
      (packedSelectCloseLeaf store n index) PackedReviewerSelectState.done := by
  have hsim :=
    packedReviewerDriveSelect_simulates store invocation n index hindex
  simpa [packedReviewerSelectStart, hindex, packedReviewerSelectRemaining,
    packedReviewerEntryRemaining] using hsim

private theorem packedReviewerDriveLca_129_simulates
    (shape : Cartesian.CartesianShape) (leftClose rightClose : Nat)
    (hrightClose : rightClose < shape.bpCode.length) :
    let store := concreteBPNativeSuccinctRMQGlobalReadStore shape
    let state := packedReviewerLcaStart shape.size leftClose rightClose
    let reference :=
      packedLcaCloseLeaf store shape.size leftClose rightClose
    (packedReviewerDriveLca store 129 state).Simulates reference
      PackedReviewerLcaState.done := by
  let store := concreteBPNativeSuccinctRMQGlobalReadStore shape
  let n := shape.size
  let invocation : PackedReviewerInvocation :=
    { instruction := .lcaClose
      argument := leftClose
      argument2 := rightClose }
  let blockSize := packedSummaryBlockSizeRaw n
  by_cases hsame :
      SuccinctClose.blockOfClose blockSize leftClose =
        SuccinctClose.blockOfClose blockSize rightClose
  · have hsameRun :=
      packedReviewerDriveLca_sameSeed_simulates store invocation n leftClose
        rightClose
    have hpad :=
      packedReviewerDriveComponent_add_fuel_of_simulates
        packedReviewerLcaResult packedReviewerLcaNextRequest
        packedReviewerLcaConsumeReply store 48 81
        (.sameSeed invocation n leftClose rightClose
          (packedReviewerLcaRankStart invocation n
            (packedLocalBPWindowBase n blockSize leftClose)))
        (packedSameBlockCloseDecodedRead store (packedRankCloseLeaf store n)
          21 n blockSize leftClose rightClose)
        PackedReviewerLcaState.done (by
          simpa [blockSize] using hsameRun)
    simpa [store, n, invocation, blockSize, packedReviewerLcaStart, hsame,
      packedLcaCloseLeaf, packedLcaCloseRead] using hpad
  · have hcross :=
      packedReviewerDriveLca_leftSeed_simulates shape invocation leftClose
        rightClose hrightClose
    simpa [store, n, invocation, blockSize, packedReviewerLcaStart, hsame,
      packedLcaCloseLeaf, packedLcaCloseRead] using hcross

/-! ## Public fixed component runs -/

/-- The concrete fixed-35 supplied-store select run used by controller proofs. -/
def packedReviewerSelectLogicalRun35
    (shape : Cartesian.CartesianShape)
    (invocation : PackedReviewerInvocation) (index : Nat) :
    PackedReviewerComponentRun PackedReviewerSelectState (Option Nat) :=
  packedReviewerDriveSelect
    (concreteBPNativeSuccinctRMQGlobalReadStore shape) 35
    (packedReviewerSelectStart invocation shape.size index)

/--
The fixed select run has the canonical value, terminal state, and full ordered
logical trace.  Its un-erased trace remains available as `run.trace`.
-/
theorem packedReviewerSelectLogicalRun35_simulates
    (shape : Cartesian.CartesianShape)
    (invocation : PackedReviewerInvocation) (index : Nat)
    (hindex : index < shape.size) :
    let run := packedReviewerSelectLogicalRun35 shape invocation index
    let reference :=
      packedSelectCloseLeaf
        (concreteBPNativeSuccinctRMQGlobalReadStore shape) shape.size index
    run.terminal = some reference.value /\
      run.state = .done reference.value /\
      run.trace.map PackedReviewerLogicalEvent.erase = reference.trace := by
  simpa [packedReviewerSelectLogicalRun35,
    PackedReviewerComponentRun.Simulates] using
      packedReviewerDriveSelect_35_simulates
        (concreteBPNativeSuccinctRMQGlobalReadStore shape) invocation
        shape.size index hindex

/-- The concrete fixed-129 canonical close/LCA run used by controller proofs. -/
def packedReviewerLcaLogicalRun129
    (shape : Cartesian.CartesianShape) (leftClose rightClose : Nat) :
    PackedReviewerComponentRun PackedReviewerLcaState (Option Nat) :=
  packedReviewerDriveLca
    (concreteBPNativeSuccinctRMQGlobalReadStore shape) 129
    (packedReviewerLcaStart shape.size leftClose rightClose)

/--
The fixed close/LCA run has the canonical value, terminal state, and full
ordered logical trace.  Both canonical reachability bounds are explicit.
-/
theorem packedReviewerLcaLogicalRun129_simulates
    (shape : Cartesian.CartesianShape) (leftClose rightClose : Nat)
    (_hleftClose : leftClose < shape.bpCode.length)
    (hrightClose : rightClose < shape.bpCode.length) :
    let run := packedReviewerLcaLogicalRun129 shape leftClose rightClose
    let reference :=
      packedLcaCloseLeaf
        (concreteBPNativeSuccinctRMQGlobalReadStore shape) shape.size
        leftClose rightClose
    run.terminal = some reference.value /\
      run.state = .done reference.value /\
      run.trace.map PackedReviewerLogicalEvent.erase = reference.trace := by
  simpa [packedReviewerLcaLogicalRun129,
    PackedReviewerComponentRun.Simulates] using
      packedReviewerDriveLca_129_simulates shape leftClose rightClose
        hrightClose

/-! ## Whole-run composition -/

private theorem packedSelectCloseLeaf_canonical_value_eq
    (shape : Cartesian.CartesianShape) (index : Nat) :
    (packedSelectCloseLeaf
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) shape.size index).value =
        SuccinctSpace.bpCloseOfInorder? shape index := by
  rw [← packedSelectCloseLeaf_eq shape
    (concreteBPNativeSuccinctRMQGlobalReadStore shape) index]
  rw [concreteBPNativeSelectCloseGlobalWordTraceResultWithStore_globalReadStore]
  have href :=
    concreteBPNativeSelectCloseGlobalWordTraceResult_refines_interpretedCosted
      shape index
  have hvalue := congrArg Costed.value href
  have hexact := concreteBPNativeSelectCloseInterpretedCosted_exact shape index
  exact hvalue.trans (by simpa [Costed.erase] using hexact)

private theorem packedSelectCloseLeaf_canonical_some_and_bound
    (shape : Cartesian.CartesianShape) (index : Nat)
    (hindex : index < shape.size) :
    exists close,
      (packedSelectCloseLeaf
        (concreteBPNativeSuccinctRMQGlobalReadStore shape) shape.size
        index).value = some close /\
      close < shape.bpCode.length := by
  rcases SuccinctSpace.bpCloseOfInorder?_some_of_lt shape hindex with
    ⟨close, hclose⟩
  refine ⟨close, ?_, ?_⟩
  · rw [packedSelectCloseLeaf_canonical_value_eq, hclose]
  · exact SuccinctSpace.bpCloseOfInorder?_bounds shape hclose

private def packedReviewerAfterLcaReference
    (store : WordRAM.ReadStore) (n : Nat) :
    Option Nat -> WordRAM.TraceResult (Option Nat)
  | none => WordRAM.TraceResult.pure none
  | some answerClose =>
      WordRAM.TraceResult.map (fun closeRank => some (closeRank - 1))
        (packedRankCloseLeaf store n (answerClose + 1))

private def packedReviewerAfterRightSelectReference
    (store : WordRAM.ReadStore) (n : Nat) :
    Option Nat -> Option Nat -> WordRAM.TraceResult (Option Nat)
  | some leftClose, some rightClose =>
      WordRAM.TraceResult.bind
        (packedLcaCloseLeaf store n leftClose rightClose)
        (packedReviewerAfterLcaReference store n)
  | _, _ => WordRAM.TraceResult.pure none

private def packedReviewerAfterLeftSelectReference
    (store : WordRAM.ReadStore) (n right : Nat) :
    Option Nat -> WordRAM.TraceResult (Option Nat)
  | leftClose =>
      WordRAM.TraceResult.bind
        (packedSelectCloseLeaf store n (right - 1))
        (packedReviewerAfterRightSelectReference store n leftClose)

private theorem packedWholeQueryRun_eq_reviewerComposition
    (store : WordRAM.ReadStore) (n left right : Nat) :
    packedWholeQueryRun store n left right =
      WordRAM.TraceResult.bind (packedSelectCloseLeaf store n left)
        (packedReviewerAfterLeftSelectReference store n right) := by
  cases hleft : (packedSelectCloseLeaf store n left).value with
  | none =>
      cases hright :
          (packedSelectCloseLeaf store n (right - 1)).value <;>
        simp [packedWholeQueryRun,
          concreteBPNativeSuccinctRMQWholeQueryProgram, packedProgramRun,
          packedInstrStep, packedReviewerAfterLeftSelectReference,
          packedReviewerAfterRightSelectReference,
          packedReviewerAfterLcaReference, WholeQueryState.empty,
          WholeQueryState.setOpt, WholeQueryState.setNat,
          WholeQueryState.opt, WholeQueryState.nat, WholeQueryNatExpr.eval,
          WordRAM.TraceResult.map, WordRAM.TraceResult.bind,
          WordRAM.TraceResult.pure, hleft, hright, List.append_assoc]
  | some leftClose =>
      cases hright :
          (packedSelectCloseLeaf store n (right - 1)).value with
      | none =>
          simp [packedWholeQueryRun,
            concreteBPNativeSuccinctRMQWholeQueryProgram, packedProgramRun,
            packedInstrStep, packedReviewerAfterLeftSelectReference,
            packedReviewerAfterRightSelectReference,
            packedReviewerAfterLcaReference, WholeQueryState.empty,
            WholeQueryState.setOpt, WholeQueryState.setNat,
            WholeQueryState.opt, WholeQueryState.nat,
            WholeQueryNatExpr.eval, WordRAM.TraceResult.map,
            WordRAM.TraceResult.bind, WordRAM.TraceResult.pure, hleft,
            hright, List.append_assoc]
      | some rightClose =>
          cases hlca :
              (packedLcaCloseLeaf store n leftClose rightClose).value <;>
            simp [packedWholeQueryRun,
              concreteBPNativeSuccinctRMQWholeQueryProgram,
              packedProgramRun, packedInstrStep,
              packedReviewerAfterLeftSelectReference,
              packedReviewerAfterRightSelectReference,
              packedReviewerAfterLcaReference, WholeQueryState.empty,
              WholeQueryState.setOpt, WholeQueryState.setNat,
              WholeQueryState.opt, WholeQueryState.nat,
              WholeQueryNatExpr.eval, WordRAM.TraceResult.map,
              WordRAM.TraceResult.bind, WordRAM.TraceResult.pure, hleft,
              hright, hlca, List.append_assoc]

private theorem packedReviewerDriveWhole_afterLca_simulates
    (shape : Cartesian.CartesianShape) (left right : Nat)
    (answerClose : Option Nat) :
    let store := concreteBPNativeSuccinctRMQGlobalReadStore shape
    let state :=
      packedReviewerWholeAfterLca shape.size left right answerClose
    (packedReviewerDriveWhole store 11 state).Simulates
      (packedReviewerAfterLcaReference store shape.size answerClose)
      PackedReviewerWholeState.done := by
  let store := concreteBPNativeSuccinctRMQGlobalReadStore shape
  let n := shape.size
  cases answerClose with
  | none =>
      simp [packedReviewerWholeAfterLca, packedReviewerAfterLcaReference,
        packedReviewerDriveWhole, packedReviewerDriveComponent,
        packedReviewerWholeResult, PackedReviewerComponentRun.Simulates,
        WordRAM.TraceResult.pure]
  | some answerClose =>
      let invocation : PackedReviewerInvocation :=
        { instruction := .finalRank, argument := answerClose + 1 }
      let rankState : PackedReviewerRankState :=
        .superSample invocation .close n (answerClose + 1)
      let rankReference := packedRankCloseLeaf store n (answerClose + 1)
      let continuation : Nat -> WordRAM.TraceResult (Option Nat) :=
        fun closeRank => WordRAM.TraceResult.pure (some (closeRank - 1))
      have hrank :=
        packedReviewerDriveRank_simulates store invocation .close n
          (answerClose + 1)
      have hsplice :=
        packedReviewerDriveComponent_embedded_phase_simulates
          packedReviewerRankResult packedReviewerRankNextRequest
          packedReviewerRankConsumeReply packedReviewerWholeResult
          packedReviewerWholeNextRequest packedReviewerWholeConsumeReply
          (fun child =>
            .finalRank n left right answerClose child)
          (fun closeRank => .done (some (closeRank - 1)))
          PackedReviewerRankState.done PackedReviewerWholeState.done
          store 11 0 rankState rankReference continuation
          (by rfl)
          (by
            simpa [packedReviewerDriveRank, rankState, rankReference,
              packedRankCloseLeaf, packedRankCloseRead] using hrank)
          (by
            simp [packedReviewerDriveWhole, packedReviewerDriveComponent,
              PackedReviewerComponentRun.Simulates,
              packedReviewerWholeResult, continuation,
              WordRAM.TraceResult.pure])
          (by intro state _; rfl)
          (by intro state _; rfl)
          (by
            intro state reply _
            change
              (match packedReviewerRankResult
                  (packedReviewerRankConsumeReply state reply) with
                | some closeRank =>
                    PackedReviewerWholeState.done (some (closeRank - 1))
                | none =>
                    PackedReviewerWholeState.finalRank n left right
                      answerClose
                      (packedReviewerRankConsumeReply state reply)) = _
            split <;> simp_all)
      simpa [store, n, invocation, rankState, rankReference, continuation,
        packedReviewerWholeAfterLca, packedReviewerAfterLcaReference,
        packedReviewerDriveWhole, WordRAM.TraceResult.map,
        WordRAM.TraceResult.bind, WordRAM.TraceResult.pure] using hsplice

private theorem packedReviewerDriveWhole_lca_simulates
    (shape : Cartesian.CartesianShape) (left right leftClose rightClose : Nat)
    (hleftClose : leftClose < shape.bpCode.length)
    (hrightClose : rightClose < shape.bpCode.length) :
    let store := concreteBPNativeSuccinctRMQGlobalReadStore shape
    let lcaState := packedReviewerLcaStart shape.size leftClose rightClose
    let lcaReference :=
      packedLcaCloseLeaf store shape.size leftClose rightClose
    (packedReviewerDriveWhole store 140
      (.lcaClose shape.size left right leftClose rightClose lcaState)).Simulates
      (WordRAM.TraceResult.bind lcaReference
        (packedReviewerAfterLcaReference store shape.size))
      PackedReviewerWholeState.done := by
  let store := concreteBPNativeSuccinctRMQGlobalReadStore shape
  let n := shape.size
  let lcaState := packedReviewerLcaStart n leftClose rightClose
  let lcaReference := packedLcaCloseLeaf store n leftClose rightClose
  have hlca :=
    packedReviewerDriveLca_129_simulates shape leftClose rightClose
      hrightClose
  have htail :=
    packedReviewerDriveWhole_afterLca_simulates shape left right
      lcaReference.value
  have hsplice :=
    packedReviewerDriveComponent_embedded_phase_simulates
      packedReviewerLcaResult packedReviewerLcaNextRequest
      packedReviewerLcaConsumeReply packedReviewerWholeResult
      packedReviewerWholeNextRequest packedReviewerWholeConsumeReply
      (fun child =>
        .lcaClose n left right leftClose rightClose child)
      (packedReviewerWholeAfterLca n left right)
      PackedReviewerLcaState.done PackedReviewerWholeState.done
      store 129 11 lcaState lcaReference
      (packedReviewerAfterLcaReference store n)
      (by
        by_cases hsame :
            SuccinctClose.blockOfClose (packedSummaryBlockSizeRaw n)
                leftClose =
              SuccinctClose.blockOfClose (packedSummaryBlockSizeRaw n)
                rightClose
        · simp [lcaState, packedReviewerLcaStart, hsame,
            packedReviewerLcaResult]
        · simp [lcaState, packedReviewerLcaStart, hsame,
            packedReviewerLcaResult])
      (by simpa [store, n, lcaState, lcaReference,
        packedReviewerDriveLca] using hlca)
      (by simpa [store, n, lcaReference, packedReviewerDriveWhole] using
        htail)
      (by intro state _; rfl)
      (by intro state _; rfl)
      (by
        intro state reply _
        change
          (match packedReviewerLcaResult
              (packedReviewerLcaConsumeReply state reply) with
            | some answerClose =>
                packedReviewerWholeAfterLca n left right answerClose
            | none =>
                PackedReviewerWholeState.lcaClose n left right leftClose
                  rightClose (packedReviewerLcaConsumeReply state reply)) = _
        split <;> simp_all)
  simpa [store, n, lcaState, lcaReference, packedReviewerDriveWhole] using
    hsplice

private theorem packedReviewerDriveWhole_rightSelect_simulates
    (shape : Cartesian.CartesianShape) (left right leftClose : Nat)
    (hleftClose : leftClose < shape.bpCode.length)
    (hrightIndex : right - 1 < shape.size) :
    let store := concreteBPNativeSuccinctRMQGlobalReadStore shape
    let index := right - 1
    let invocation : PackedReviewerInvocation :=
      { instruction := .rightSelect, argument := index }
    let selectState :=
      packedReviewerSelectStart invocation shape.size index
    let selectReference := packedSelectCloseLeaf store shape.size index
    (packedReviewerDriveWhole store 175
      (.rightSelect shape.size left right (some leftClose)
        selectState)).Simulates
      (WordRAM.TraceResult.bind selectReference
        (packedReviewerAfterRightSelectReference store shape.size
          (some leftClose)))
      PackedReviewerWholeState.done := by
  let store := concreteBPNativeSuccinctRMQGlobalReadStore shape
  let n := shape.size
  let index := right - 1
  let invocation : PackedReviewerInvocation :=
    { instruction := .rightSelect, argument := index }
  let selectState := packedReviewerSelectStart invocation n index
  let selectReference := packedSelectCloseLeaf store n index
  obtain ⟨rightClose, hrightValue, hrightClose⟩ :=
    packedSelectCloseLeaf_canonical_some_and_bound shape index
      (by simpa [n, index] using hrightIndex)
  have hselect :=
    packedReviewerDriveSelect_35_simulates store invocation n index
      (by simpa [n, index] using hrightIndex)
  have htail :=
    packedReviewerDriveWhole_lca_simulates shape left right leftClose
      rightClose hleftClose hrightClose
  have hsplice :=
    packedReviewerDriveComponent_embedded_phase_simulates
      packedReviewerSelectResult packedReviewerSelectNextRequest
      packedReviewerSelectConsumeReply packedReviewerWholeResult
      packedReviewerWholeNextRequest packedReviewerWholeConsumeReply
      (fun child =>
        .rightSelect n left right (some leftClose) child)
      (packedReviewerWholeAfterRightSelect n left right (some leftClose))
      PackedReviewerSelectState.done PackedReviewerWholeState.done
      store 35 140 selectState selectReference
      (packedReviewerAfterRightSelectReference store n (some leftClose))
      (by
        simp [selectState, packedReviewerSelectStart,
          show index < n by simpa [n, index] using hrightIndex,
          packedReviewerSelectResult])
      (by simpa [selectState, selectReference,
        packedReviewerDriveSelect] using hselect)
      (by
        rw [hrightValue]
        simpa [store, n, packedReviewerAfterRightSelectReference,
          packedReviewerWholeAfterRightSelect,
          packedReviewerDriveWhole] using htail)
      (by intro state _; rfl)
      (by intro state _; rfl)
      (by
        intro state reply _
        change
          (match packedReviewerSelectResult
              (packedReviewerSelectConsumeReply state reply) with
            | some rightClose =>
                packedReviewerWholeAfterRightSelect n left right
                  (some leftClose) rightClose
            | none =>
                PackedReviewerWholeState.rightSelect n left right
                  (some leftClose)
                  (packedReviewerSelectConsumeReply state reply)) = _
        split <;> simp_all)
  simpa [store, n, index, invocation, selectState, selectReference,
    packedReviewerDriveWhole] using hsplice

private theorem packedReviewerDriveWhole_simulates
    (shape : Cartesian.CartesianShape) (left right : Nat)
    (hleft : left < right) (hright : right <= shape.size) :
    let store := concreteBPNativeSuccinctRMQGlobalReadStore shape
    let state := packedReviewerWholeStart shape.size left right
    let reference := packedWholeQueryRun store shape.size left right
    (packedReviewerDriveWhole store 210 state).Simulates reference
      PackedReviewerWholeState.done := by
  let store := concreteBPNativeSuccinctRMQGlobalReadStore shape
  let n := shape.size
  let invocation : PackedReviewerInvocation :=
    { instruction := .leftSelect, argument := left }
  let selectState := packedReviewerSelectStart invocation n left
  let selectReference := packedSelectCloseLeaf store n left
  have hleftIndex : left < n := by
    dsimp [n]
    omega
  have hrightIndex : right - 1 < n := by
    dsimp [n]
    omega
  obtain ⟨leftClose, hleftValue, hleftClose⟩ :=
    packedSelectCloseLeaf_canonical_some_and_bound shape left
      (by simpa [n] using hleftIndex)
  have hselect :=
    packedReviewerDriveSelect_35_simulates store invocation n left hleftIndex
  have htail :=
    packedReviewerDriveWhole_rightSelect_simulates shape left right leftClose
      hleftClose (by simpa [n] using hrightIndex)
  have hsplice :=
    packedReviewerDriveComponent_embedded_phase_simulates
      packedReviewerSelectResult packedReviewerSelectNextRequest
      packedReviewerSelectConsumeReply packedReviewerWholeResult
      packedReviewerWholeNextRequest packedReviewerWholeConsumeReply
      (fun child => .leftSelect n left right child)
      (packedReviewerWholeAfterLeftSelect n left right)
      PackedReviewerSelectState.done PackedReviewerWholeState.done
      store 35 175 selectState selectReference
      (packedReviewerAfterLeftSelectReference store n right)
      (by
        simp [selectState, packedReviewerSelectStart, hleftIndex,
          packedReviewerSelectResult])
      (by simpa [selectState, selectReference,
        packedReviewerDriveSelect] using hselect)
      (by
        rw [hleftValue]
        simpa [store, n, packedReviewerAfterLeftSelectReference,
          packedReviewerWholeAfterLeftSelect,
          packedReviewerDriveWhole] using htail)
      (by intro state _; rfl)
      (by intro state _; rfl)
      (by
        intro state reply _
        change
          (match packedReviewerSelectResult
              (packedReviewerSelectConsumeReply state reply) with
            | some leftClose =>
                packedReviewerWholeAfterLeftSelect n left right leftClose
            | none =>
                PackedReviewerWholeState.leftSelect n left right
                  (packedReviewerSelectConsumeReply state reply)) = _
        split <;> simp_all)
  have hcomposed :
      (packedReviewerDriveWhole store 210
        (packedReviewerWholeStart n left right)).Simulates
        (WordRAM.TraceResult.bind selectReference
          (packedReviewerAfterLeftSelectReference store n right))
        PackedReviewerWholeState.done := by
    simpa [packedReviewerWholeStart, invocation, selectState,
      packedReviewerDriveWhole] using hsplice
  simpa [store, n, selectReference,
    packedWholeQueryRun_eq_reviewerComposition] using hcomposed

private theorem packedReviewerDriveLogical_eq_component
    (store : WordRAM.ReadStore) (fuel : Nat)
    (state : PackedReviewerWholeState) :
    let logical := packedReviewerDriveLogical store fuel state
    let component := packedReviewerDriveWhole store fuel state
    logical.terminal = component.terminal /\
      logical.state = component.state /\
      logical.trace = component.trace := by
  induction fuel generalizing state with
  | zero =>
      simp [packedReviewerDriveLogical, packedReviewerDriveWhole,
        packedReviewerDriveComponent]
  | succ fuel ih =>
      cases hresult : packedReviewerWholeResult state with
      | some value =>
          simp [packedReviewerDriveLogical, packedReviewerDriveWhole,
            packedReviewerDriveComponent, hresult]
      | none =>
          cases hrequest : packedReviewerWholeNextRequest state with
          | none =>
              simp [packedReviewerDriveLogical, packedReviewerDriveWhole,
                packedReviewerDriveComponent, hresult, hrequest]
          | some request =>
              have htail :=
                ih (packedReviewerWholeConsumeReply state
                  (store.readWord? request.segment request.index))
              simpa [packedReviewerDriveLogical, packedReviewerDriveWhole,
                packedReviewerDriveComponent, hresult, hrequest] using htail

/--
On every valid half-open query, the fixed 210-read logical controller over the
canonical reviewer store is the accepted packed whole-query run occurrence by
occurrence.
-/
theorem packedReviewerDriveLogical_210_simulates_packedWholeQueryRun
    (shape : Cartesian.CartesianShape) (left right : Nat)
    (hleft : left < right) (hright : right <= shape.size) :
    let store := concreteBPNativeSuccinctRMQGlobalReadStore shape
    let run :=
      packedReviewerDriveLogical store 210
        (packedReviewerWholeStart shape.size left right)
    let reference := packedWholeQueryRun store shape.size left right
    run.terminal = some reference.value /\
      run.state = .done reference.value /\
      run.trace.map PackedReviewerLogicalEvent.erase = reference.trace := by
  let store := concreteBPNativeSuccinctRMQGlobalReadStore shape
  have hcomponent :=
    packedReviewerDriveWhole_simulates shape left right hleft hright
  have heq :=
    packedReviewerDriveLogical_eq_component store 210
      (packedReviewerWholeStart shape.size left right)
  have htrace :=
    congrArg (List.map PackedReviewerLogicalEvent.erase) heq.2.2
  simpa [store, PackedReviewerComponentRun.Simulates] using
    And.intro (heq.1.trans hcomponent.1)
      (And.intro (heq.2.1.trans hcomponent.2.1)
        (htrace.trans hcomponent.2.2))

/-- Indexed ordered-trace preservation for the canonical fixed run. -/
theorem packedReviewerDriveLogical_210_trace_get?_eq
    (shape : Cartesian.CartesianShape) (left right : Nat)
    (hleft : left < right) (hright : right <= shape.size)
    (position : Nat) :
    let store := concreteBPNativeSuccinctRMQGlobalReadStore shape
    let run :=
      packedReviewerDriveLogical store 210
        (packedReviewerWholeStart shape.size left right)
    let reference := packedWholeQueryRun store shape.size left right
    (run.trace.map PackedReviewerLogicalEvent.erase)[position]? =
      reference.trace[position]? := by
  have hsim :=
    packedReviewerDriveLogical_210_simulates_packedWholeQueryRun shape left
      right hleft hright
  simpa using congrArg (fun trace => trace[position]?) hsim.2.2

/-- Every retained logical occurrence erases to the reference occurrence. -/
theorem packedReviewerDriveLogical_210_occurrence_erases
    (shape : Cartesian.CartesianShape) (left right : Nat)
    (hleft : left < right) (hright : right <= shape.size)
    (position : Nat) (event : PackedReviewerLogicalEvent)
    (hget :
      (packedReviewerDriveLogical
        (concreteBPNativeSuccinctRMQGlobalReadStore shape) 210
        (packedReviewerWholeStart shape.size left right)).trace[position]? =
          some event) :
    (packedWholeQueryRun
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) shape.size left
      right).trace[position]? = some event.erase := by
  have hindexed :=
    packedReviewerDriveLogical_210_trace_get?_eq shape left right hleft
      hright position
  dsimp only at hindexed
  rw [List.getElem?_map, hget] at hindexed
  simpa using hindexed.symm

/-! ## Canonical component orbits and their accepted reference values

The proof-side state towers pin in-flight nested components to the exact
orbit of their canonical start.  The orbit is the same trajectory the
supplied-store driver walks, so a completed orbit inherits the driver's
simulated reference value.  The bridging lemmas stay private with the
driver; only the orbit definition and the per-component value corollaries
are public.
-/

/-- One canonical-store request/reply step of an arbitrary component. -/
def packedReviewerComponentCanonicalStep
    {State : Type}
    (nextRequest : State -> Option PackedReviewerLogicalRequest)
    (consumeReply : State -> Option (List Bool) -> State)
    (store : WordRAM.ReadStore) (state : State) : State :=
  match nextRequest state with
  | none => state
  | some request =>
      consumeReply state (store.readWord? request.segment request.index)

/-- The exact canonical-store orbit of an arbitrary component. -/
def packedReviewerComponentCanonicalRun
    {State : Type}
    (nextRequest : State -> Option PackedReviewerLogicalRequest)
    (consumeReply : State -> Option (List Bool) -> State)
    (store : WordRAM.ReadStore) : Nat -> State -> State
  | 0, state => state
  | fuel + 1, state =>
      packedReviewerComponentCanonicalStep nextRequest consumeReply store
        (packedReviewerComponentCanonicalRun nextRequest consumeReply store
          fuel state)

private theorem packedReviewerComponentCanonicalRun_succ_comm
    {State : Type}
    (nextRequest : State -> Option PackedReviewerLogicalRequest)
    (consumeReply : State -> Option (List Bool) -> State)
    (store : WordRAM.ReadStore) (fuel : Nat) (state : State) :
    packedReviewerComponentCanonicalRun nextRequest consumeReply store
        (fuel + 1) state =
      packedReviewerComponentCanonicalRun nextRequest consumeReply store fuel
        (packedReviewerComponentCanonicalStep nextRequest consumeReply store
          state) := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      show packedReviewerComponentCanonicalStep nextRequest consumeReply store
          (packedReviewerComponentCanonicalRun nextRequest consumeReply store
            (fuel + 1) state) = _
      rw [ih]
      rfl

private theorem packedReviewerDriveComponent_terminal_mono
    {State Value : Type}
    (result : State -> Option Value)
    (nextRequest : State -> Option PackedReviewerLogicalRequest)
    (consumeReply : State -> Option (List Bool) -> State)
    (store : WordRAM.ReadStore) {fuel fuel' : Nat} {state : State}
    {value : Value}
    (hterminal :
      (packedReviewerDriveComponent result nextRequest consumeReply store
        fuel state).terminal = some value)
    (hle : fuel <= fuel') :
    (packedReviewerDriveComponent result nextRequest consumeReply store fuel'
      state).terminal = some value := by
  induction fuel' generalizing fuel state with
  | zero =>
      have hzero : fuel = 0 := by omega
      subst hzero
      exact hterminal
  | succ fuel' ih =>
      cases fuel with
      | zero =>
          have hresult :
              result state = some value := by
            simpa [packedReviewerDriveComponent] using hterminal
          simp [packedReviewerDriveComponent, hresult]
      | succ fuel =>
          cases hresult : result state with
          | some other =>
              have hvalue : other = value := by
                simpa [packedReviewerDriveComponent, hresult] using hterminal
              subst other
              simp [packedReviewerDriveComponent, hresult]
          | none =>
              cases hrequest : nextRequest state with
              | none =>
                  simp [packedReviewerDriveComponent, hresult, hrequest]
                    at hterminal
              | some request =>
                  have htail :
                      (packedReviewerDriveComponent result nextRequest
                        consumeReply store fuel
                        (consumeReply state
                          (store.readWord? request.segment
                            request.index))).terminal = some value := by
                    simpa [packedReviewerDriveComponent, hresult, hrequest]
                      using hterminal
                  have hnext := ih htail (by omega)
                  simpa [packedReviewerDriveComponent, hresult, hrequest]
                    using hnext

private theorem packedReviewerDriveComponent_terminal_of_canonicalRun_result
    {State Value : Type}
    (result : State -> Option Value)
    (nextRequest : State -> Option PackedReviewerLogicalRequest)
    (consumeReply : State -> Option (List Bool) -> State)
    (store : WordRAM.ReadStore)
    (hdone :
      forall state value, result state = some value ->
        nextRequest state = none)
    {fuel : Nat} {state : State} {value : Value}
    (hresult :
      result
          (packedReviewerComponentCanonicalRun nextRequest consumeReply store
            fuel state) = some value) :
    (packedReviewerDriveComponent result nextRequest consumeReply store fuel
      state).terminal = some value := by
  induction fuel generalizing state with
  | zero =>
      simpa [packedReviewerDriveComponent,
        packedReviewerComponentCanonicalRun] using hresult
  | succ fuel ih =>
      rw [packedReviewerComponentCanonicalRun_succ_comm] at hresult
      cases hres : result state with
      | some other =>
          have hstep :
              packedReviewerComponentCanonicalStep nextRequest consumeReply
                store state = state := by
            unfold packedReviewerComponentCanonicalStep
            rw [hdone state other hres]
          rw [hstep] at hresult
          have hstable :
              forall k,
                packedReviewerComponentCanonicalRun nextRequest consumeReply
                  store k state = state := by
            intro k
            induction k with
            | zero => rfl
            | succ k ihk =>
                show packedReviewerComponentCanonicalStep nextRequest
                    consumeReply store
                    (packedReviewerComponentCanonicalRun nextRequest
                      consumeReply store k state) = state
                rw [ihk, hstep]
          rw [hstable fuel] at hresult
          have hvalue : other = value := by
            rw [hres] at hresult
            exact Option.some.inj hresult
          subst other
          simp [packedReviewerDriveComponent, hres]
      | none =>
          cases hrequest : nextRequest state with
          | none =>
              have hstep :
                  packedReviewerComponentCanonicalStep nextRequest
                    consumeReply store state = state := by
                unfold packedReviewerComponentCanonicalStep
                rw [hrequest]
              rw [hstep] at hresult
              have hstable :
                  forall k,
                    packedReviewerComponentCanonicalRun nextRequest
                      consumeReply store k state = state := by
                intro k
                induction k with
                | zero => rfl
                | succ k ihk =>
                    show packedReviewerComponentCanonicalStep nextRequest
                        consumeReply store
                        (packedReviewerComponentCanonicalRun nextRequest
                          consumeReply store k state) = state
                    rw [ihk, hstep]
              rw [hstable fuel] at hresult
              rw [hres] at hresult
              cases hresult
          | some request =>
              have hstep :
                  packedReviewerComponentCanonicalStep nextRequest
                    consumeReply store state =
                    consumeReply state
                      (store.readWord? request.segment request.index) := by
                unfold packedReviewerComponentCanonicalStep
                rw [hrequest]
              rw [hstep] at hresult
              have htail := ih hresult
              simpa [packedReviewerDriveComponent, hres, hrequest] using htail

/-- A completed canonical rank orbit returns the accepted reference value. -/
theorem packedReviewerRankCanonicalRun_result_eq
    (shape : Cartesian.CartesianShape)
    (invocation : PackedReviewerInvocation)
    (kind : PackedReviewerRankKind) (pos fuel : Nat) {value : Nat}
    (hresult :
      packedReviewerRankResult
          (packedReviewerComponentCanonicalRun packedReviewerRankNextRequest
            packedReviewerRankConsumeReply
            (concreteBPNativeSuccinctRMQGlobalReadStore shape) fuel
            (.superSample invocation kind shape.size pos)) = some value) :
    value =
      (packedRankRead kind.superSegment kind.blockSegment kind.wordSegment 21
        (packedFringeChunkBits shape.size) kind.target
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (kind.bitLength shape.size) (kind.wordSize shape.size)
        (kind.blocksPerSuper shape.size) pos).value := by
  have hdone :
      forall state v, packedReviewerRankResult state = some v ->
        packedReviewerRankNextRequest state = none := by
    intro state v hres
    cases state <;>
      simp_all [packedReviewerRankResult, packedReviewerRankNextRequest]
  have hterm :=
    packedReviewerDriveComponent_terminal_of_canonicalRun_result
      packedReviewerRankResult packedReviewerRankNextRequest
      packedReviewerRankConsumeReply
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) hdone hresult
  have hsim := packedReviewerDriveRank_simulates
    (concreteBPNativeSuccinctRMQGlobalReadStore shape) invocation kind
    shape.size pos
  have hsimTerminal :
      (packedReviewerDriveComponent packedReviewerRankResult
        packedReviewerRankNextRequest packedReviewerRankConsumeReply
        (concreteBPNativeSuccinctRMQGlobalReadStore shape) 11
        (.superSample invocation kind shape.size pos)).terminal =
        some
          (packedRankRead kind.superSegment kind.blockSegment
            kind.wordSegment 21 (packedFringeChunkBits shape.size) kind.target
            (concreteBPNativeSuccinctRMQGlobalReadStore shape)
            (kind.bitLength shape.size) (kind.wordSize shape.size)
            (kind.blocksPerSuper shape.size) pos).value :=
    hsim.1
  have hvalueSide :=
    packedReviewerDriveComponent_terminal_mono packedReviewerRankResult
      packedReviewerRankNextRequest packedReviewerRankConsumeReply
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) hterm
      (Nat.le_max_left fuel 11)
  have hreferenceSide :=
    packedReviewerDriveComponent_terminal_mono packedReviewerRankResult
      packedReviewerRankNextRequest packedReviewerRankConsumeReply
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) hsimTerminal
      (Nat.le_max_right fuel 11)
  rw [hvalueSide] at hreferenceSide
  exact Option.some.inj hreferenceSide

/-! ## The long-flag rank reference value over the canonical store

The canonical store serves the three long-flag rank sample segments from the
accepted record's own tables, and its word segment appends sentinel entries
past the chunked flag words.  Agreement is therefore total on the sample and
chunk segments but only index-wise on the word segment; a per-index variant of
the store-agreement conversion closes the gap, because a clamped in-range
query never touches the sentinel suffix.
-/

theorem packedReviewerBpWordRead_toCosted_of_read
    {payload : List Bool}
    (pstore : SuccinctSpace.PayloadWordStore payload)
    {store : WordRAM.ReadStore} {segment i : Nat}
    (hread : store.readWord? segment i = pstore.words[i]?) :
    (SuccinctClose.bpWordReadTraceResult store segment i).toCosted =
      pstore.readWordCosted i := by
  apply Costed.ext
  · show store.readWord? segment i = (pstore.readWordCosted i).value
    rw [hread]
    rfl
  · show (1 : Nat) = (pstore.readWordCosted i).cost
    simp

theorem packedReviewerRankWithStore_toCosted_of_reads_true
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      SuccinctRank.TwoLevelPayloadLiveStoredWordRankData
        bits superOverhead blockOverhead queryCost)
    {store : WordRAM.ReadStore}
    {superSegment blockSegment wordSegment chunkSegment c : Nat}
    (hsuper :
      forall address,
        store.readWord? superSegment address =
          (data.superSampleWords true)[address]?)
    (hblock :
      forall address,
        store.readWord? blockSegment address =
          (data.blockSampleWords true)[address]?)
    (hchunk :
      forall address,
        store.readWord? chunkSegment address =
          (SuccinctClose.bpFringeChunkTable c).store.words[address]?)
    (pos : Nat)
    (hword :
      store.readWord? wordSegment (data.wordIndex pos) =
        data.bitWords.store.words[data.wordIndex pos]?) :
    (data.bpChunkedRankTraceResultWithStore store superSegment
        blockSegment wordSegment chunkSegment c true pos).toCosted =
      data.bpChunkedRankCosted c true pos := by
  have hsuper' :
      forall address,
        store.readWord? superSegment address =
          data.superTables.trueTable.store.words[address]? := hsuper
  have hblock' :
      forall address,
        store.readWord? blockSegment address =
          data.blockTables.trueTable.store.words[address]? := hblock
  unfold SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.bpChunkedRankTraceResultWithStore
    SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.bpChunkedRankCosted
  rw [WordRAM.TraceResult.bind_toCosted,
    SuccinctClose.bpChunkReadTraceResult_toCosted_of_agree
      data.superTables.trueTable hsuper']
  show
    Costed.bind
        (data.superTables.trueTable.readCosted (data.superIndex pos))
        _ =
      Costed.bind
        (data.superTables.trueTable.readCosted (data.superIndex pos))
        _
  congr 1
  funext super?
  rw [WordRAM.TraceResult.bind_toCosted,
    SuccinctClose.bpChunkReadTraceResult_toCosted_of_agree
      data.blockTables.trueTable hblock']
  show
    Costed.bind
        (data.blockTables.trueTable.readCosted (data.wordIndex pos))
        _ =
      Costed.bind
        (data.blockTables.trueTable.readCosted (data.wordIndex pos))
        _
  congr 1
  funext delta?
  rw [WordRAM.TraceResult.bind_toCosted,
    packedReviewerBpWordRead_toCosted_of_read data.bitWords.store hword]
  congr 1
  funext word?
  cases super? <;> cases delta? <;> cases word? <;>
    first
      | rfl
      | rw [WordRAM.TraceResult.map_toCosted,
          SuccinctClose.bpChunkedWordRankTraceResultAtSegmentWithStore_toCosted_of_agree
            (SuccinctClose.bpFringeChunkTable c) hchunk]

end PackedCellProbe
end SuccinctFinal
end RMQ
