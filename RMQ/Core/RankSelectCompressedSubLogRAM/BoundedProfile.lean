import RMQ.Core.RankSelectCompressedSubLogRAM.GlobalStore

namespace RMQ

namespace RankSelectSpec

open GenericSelect

/--
Small numeric envelope for natural data carried by a rank/select `WordRAM`
trace event. Payload reads contribute their segment/index address; word-local
rank/select primitives contribute the natural operands/results visible in the
trace.
-/
def subLogCompressedFIDTraceEventNatEnvelope :
    WordRAM.TraceEvent -> Nat
  | WordRAM.TraceEvent.readWord segment index _ => Nat.max segment index
  | WordRAM.TraceEvent.wordRank _ limit result => Nat.max limit result
  | WordRAM.TraceEvent.wordSelect _ occurrence none => occurrence
  | WordRAM.TraceEvent.wordSelect _ occurrence (some result) =>
      Nat.max occurrence result

/-- Maximum natural envelope over a rank/select trace. -/
def subLogCompressedFIDTraceNatEnvelope :
    List WordRAM.TraceEvent -> Nat
  | [] => 0
  | event :: rest =>
      Nat.max (subLogCompressedFIDTraceEventNatEnvelope event)
        (subLogCompressedFIDTraceNatEnvelope rest)

/--
Trace-local bit width for bounded rank/select execution stories.

This is a finite width computed from the trace itself, mirroring the final RMQ
bounded global trace theorem. It is not an asymptotic word-size theorem.
-/
def subLogCompressedFIDTraceEventBitWidth
    (trace : List WordRAM.TraceEvent) : Nat :=
  Nat.log2 (subLogCompressedFIDTraceNatEnvelope trace) + 1

/-- Read addresses exposed by a rank/select event fit in the declared width. -/
def subLogCompressedFIDTraceEventReadAddressFitsInBits
    (bits : Nat) : WordRAM.TraceEvent -> Prop
  | WordRAM.TraceEvent.readWord segment index _ =>
      WordRAM.Register.AddressFitsInBits bits segment index
  | WordRAM.TraceEvent.wordRank _ _ _ => True
  | WordRAM.TraceEvent.wordSelect _ _ _ => True

/-- Word-primitive natural operands/results exposed by an event fit in bits. -/
def subLogCompressedFIDTraceEventPrimitiveOperandsFitInBits
    (bits : Nat) : WordRAM.TraceEvent -> Prop
  | WordRAM.TraceEvent.readWord _ _ _ => True
  | WordRAM.TraceEvent.wordRank _ limit result =>
      WordRAM.Register.FitsInBits bits limit /\
        WordRAM.Register.FitsInBits bits result
  | WordRAM.TraceEvent.wordSelect _ occurrence result =>
      WordRAM.Register.FitsInBits bits occurrence /\
        forall value, result = some value ->
          WordRAM.Register.FitsInBits bits value

theorem subLogCompressedFIDTraceEventNatEnvelope_le_traceNatEnvelope_of_mem
    {trace : List WordRAM.TraceEvent} {event : WordRAM.TraceEvent}
    (hmem : List.Mem event trace) :
    subLogCompressedFIDTraceEventNatEnvelope event <=
      subLogCompressedFIDTraceNatEnvelope trace := by
  induction trace with
  | nil =>
      cases hmem
  | cons head tail ih =>
      cases hmem with
      | head =>
          exact Nat.le_max_left _ _
      | tail _ htail =>
          exact Nat.le_trans (ih htail) (Nat.le_max_right _ _)

theorem subLogCompressedFIDTraceEventNatEnvelope_lt_two_pow_bitWidth_of_mem
    {trace : List WordRAM.TraceEvent} {event : WordRAM.TraceEvent}
    (hmem : List.Mem event trace) :
    subLogCompressedFIDTraceEventNatEnvelope event <
      2 ^ subLogCompressedFIDTraceEventBitWidth trace := by
  have hle :=
    subLogCompressedFIDTraceEventNatEnvelope_le_traceNatEnvelope_of_mem
      (trace := trace) (event := event) hmem
  have hlt :
      subLogCompressedFIDTraceNatEnvelope trace <
        2 ^ subLogCompressedFIDTraceEventBitWidth trace := by
    unfold subLogCompressedFIDTraceEventBitWidth
    exact Nat.lt_log2_self
  exact Nat.lt_of_le_of_lt hle hlt

theorem subLogCompressedFIDTraceEventReadAddressFitsInBits_of_mem
    {trace : List WordRAM.TraceEvent} {event : WordRAM.TraceEvent}
    (hmem : List.Mem event trace) :
    subLogCompressedFIDTraceEventReadAddressFitsInBits
      (subLogCompressedFIDTraceEventBitWidth trace) event := by
  have hlt :=
    subLogCompressedFIDTraceEventNatEnvelope_lt_two_pow_bitWidth_of_mem
      (trace := trace) (event := event) hmem
  cases event with
  | readWord segment index word? =>
      have hmax :
          Nat.max segment index <
            2 ^ subLogCompressedFIDTraceEventBitWidth trace := by
        simpa [subLogCompressedFIDTraceEventNatEnvelope] using hlt
      constructor
      · exact Nat.lt_of_le_of_lt (Nat.le_max_left segment index) hmax
      · exact Nat.lt_of_le_of_lt (Nat.le_max_right segment index) hmax
  | wordRank target limit result =>
      trivial
  | wordSelect target occurrence result =>
      trivial

theorem subLogCompressedFIDTraceEventPrimitiveOperandsFitInBits_of_mem
    {trace : List WordRAM.TraceEvent} {event : WordRAM.TraceEvent}
    (hmem : List.Mem event trace) :
    subLogCompressedFIDTraceEventPrimitiveOperandsFitInBits
      (subLogCompressedFIDTraceEventBitWidth trace) event := by
  have hlt :=
    subLogCompressedFIDTraceEventNatEnvelope_lt_two_pow_bitWidth_of_mem
      (trace := trace) (event := event) hmem
  cases event with
  | readWord segment index word? =>
      trivial
  | wordRank target limit result =>
      have hmax :
          Nat.max limit result <
            2 ^ subLogCompressedFIDTraceEventBitWidth trace := by
        simpa [subLogCompressedFIDTraceEventNatEnvelope] using hlt
      constructor
      · exact Nat.lt_of_le_of_lt (Nat.le_max_left limit result) hmax
      · exact Nat.lt_of_le_of_lt (Nat.le_max_right limit result) hmax
  | wordSelect target occurrence result =>
      cases result with
      | none =>
          constructor
          · simpa [WordRAM.Register.FitsInBits,
              subLogCompressedFIDTraceEventNatEnvelope] using hlt
          · intro value hvalue
            cases hvalue
      | some result =>
          have hmax :
              Nat.max occurrence result <
                2 ^ subLogCompressedFIDTraceEventBitWidth trace := by
            simpa [subLogCompressedFIDTraceEventNatEnvelope] using hlt
          constructor
          · exact Nat.lt_of_le_of_lt
              (Nat.le_max_left occurrence result) hmax
          · intro value hvalue
            cases hvalue
            exact Nat.lt_of_le_of_lt
              (Nat.le_max_right occurrence result) hmax

/-- Trace-local bit width for the global access trace. -/
def subLogCompressedFIDGlobalAccessTraceEventBits
    (bits : List Bool) (i : Nat) : Nat :=
  subLogCompressedFIDTraceEventBitWidth
    (subLogCompressedFIDGlobalAccessTraceResult bits i).trace

/-- Trace-local bit width for the global rank trace. -/
def subLogCompressedFIDGlobalRankTraceEventBits
    (bits : List Bool) (target : Bool) (pos : Nat) : Nat :=
  subLogCompressedFIDTraceEventBitWidth
    (subLogCompressedFIDGlobalRankTraceResult bits target pos).trace

/-- Trace-local bit width for the global select trace. -/
def subLogCompressedFIDGlobalSelectTraceEventBits
    (bits : List Bool) (target : Bool) (occurrence : Nat) : Nat :=
  subLogCompressedFIDTraceEventBitWidth
    (subLogCompressedFIDGlobalSelectTraceResult bits target occurrence).trace

theorem subLogCompressedFIDGlobalAccessTraceResult_event_bounds
    (bits : List Bool) (i : Nat) :
    forall event,
      List.Mem event
        (subLogCompressedFIDGlobalAccessTraceResult bits i).trace ->
        subLogCompressedFIDTraceEventReadAddressFitsInBits
          (subLogCompressedFIDGlobalAccessTraceEventBits bits i) event /\
        subLogCompressedFIDTraceEventPrimitiveOperandsFitInBits
          (subLogCompressedFIDGlobalAccessTraceEventBits bits i) event := by
  intro event hmem
  constructor
  · exact
      subLogCompressedFIDTraceEventReadAddressFitsInBits_of_mem
        (trace := (subLogCompressedFIDGlobalAccessTraceResult bits i).trace)
        (event := event) hmem
  · exact
      subLogCompressedFIDTraceEventPrimitiveOperandsFitInBits_of_mem
        (trace := (subLogCompressedFIDGlobalAccessTraceResult bits i).trace)
        (event := event) hmem

theorem subLogCompressedFIDGlobalRankTraceResult_event_bounds
    (bits : List Bool) (target : Bool) (pos : Nat) :
    forall event,
      List.Mem event
        (subLogCompressedFIDGlobalRankTraceResult bits target pos).trace ->
        subLogCompressedFIDTraceEventReadAddressFitsInBits
          (subLogCompressedFIDGlobalRankTraceEventBits
            bits target pos) event /\
        subLogCompressedFIDTraceEventPrimitiveOperandsFitInBits
          (subLogCompressedFIDGlobalRankTraceEventBits
            bits target pos) event := by
  intro event hmem
  constructor
  · exact
      subLogCompressedFIDTraceEventReadAddressFitsInBits_of_mem
        (trace :=
          (subLogCompressedFIDGlobalRankTraceResult
            bits target pos).trace)
        (event := event) hmem
  · exact
      subLogCompressedFIDTraceEventPrimitiveOperandsFitInBits_of_mem
        (trace :=
          (subLogCompressedFIDGlobalRankTraceResult
            bits target pos).trace)
        (event := event) hmem

theorem subLogCompressedFIDGlobalSelectTraceResult_event_bounds
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    forall event,
      List.Mem event
        (subLogCompressedFIDGlobalSelectTraceResult
          bits target occurrence).trace ->
        subLogCompressedFIDTraceEventReadAddressFitsInBits
          (subLogCompressedFIDGlobalSelectTraceEventBits
            bits target occurrence) event /\
        subLogCompressedFIDTraceEventPrimitiveOperandsFitInBits
          (subLogCompressedFIDGlobalSelectTraceEventBits
            bits target occurrence) event := by
  intro event hmem
  constructor
  · exact
      subLogCompressedFIDTraceEventReadAddressFitsInBits_of_mem
        (trace :=
          (subLogCompressedFIDGlobalSelectTraceResult
            bits target occurrence).trace)
        (event := event) hmem
  · exact
      subLogCompressedFIDTraceEventPrimitiveOperandsFitInBits_of_mem
        (trace :=
          (subLogCompressedFIDGlobalSelectTraceResult
            bits target occurrence).trace)
        (event := event) hmem

/--
Bounded target-indexed global execution story for compressed/FID rank/select.

This extends the target-indexed global payload-store theorem with a finite
trace-local event width for each access/rank/select query. Every payload-read
address and every natural operand/result exposed by a word primitive fits the
corresponding trace-local width.
-/
theorem subLogCompressedFIDTargetGlobalPayloadStore_bounded_execution_story
    (bits : List Bool) (target : Bool) :
    (forall i,
      (subLogCompressedFIDGlobalAccessTraceResult bits i).toCosted =
          subLogAccessInterpretedCosted bits i /\
        (subLogCompressedFIDGlobalAccessTraceResult bits i).toCosted =
          subLogAccessCosted bits i /\
        (forall event,
          event ∈ (subLogCompressedFIDGlobalAccessTraceResult bits i).trace ->
            event.isReadWord \/ event.isWordPrimitive) /\
        (forall event,
          event ∈ (subLogCompressedFIDGlobalAccessTraceResult bits i).trace ->
            event.matchesReadStore
              (subLogCompressedFIDTargetGlobalTraceReadStore bits target)) /\
        (forall event,
          event ∈ (subLogCompressedFIDGlobalAccessTraceResult bits i).trace ->
            subLogCompressedFIDTraceEventReadAddressFitsInBits
              (subLogCompressedFIDGlobalAccessTraceEventBits bits i) event) /\
        (forall event,
          event ∈ (subLogCompressedFIDGlobalAccessTraceResult bits i).trace ->
            subLogCompressedFIDTraceEventPrimitiveOperandsFitInBits
              (subLogCompressedFIDGlobalAccessTraceEventBits bits i) event)) /\
      (forall pos,
        (subLogCompressedFIDGlobalRankTraceResult
          bits target pos).toCosted =
            subLogRankInterpretedCosted bits target pos /\
          (subLogCompressedFIDGlobalRankTraceResult
            bits target pos).toCosted =
            subLogRankCosted bits target pos /\
          (forall event,
            event ∈
                (subLogCompressedFIDGlobalRankTraceResult
                  bits target pos).trace ->
              event.isReadWord \/ event.isWordPrimitive) /\
          (forall event,
            event ∈
                (subLogCompressedFIDGlobalRankTraceResult
                  bits target pos).trace ->
              event.matchesReadStore
                (subLogCompressedFIDTargetGlobalTraceReadStore
                  bits target)) /\
          (forall event,
            event ∈
                (subLogCompressedFIDGlobalRankTraceResult
                  bits target pos).trace ->
              subLogCompressedFIDTraceEventReadAddressFitsInBits
                (subLogCompressedFIDGlobalRankTraceEventBits
                  bits target pos) event) /\
          (forall event,
            event ∈
                (subLogCompressedFIDGlobalRankTraceResult
                  bits target pos).trace ->
              subLogCompressedFIDTraceEventPrimitiveOperandsFitInBits
                (subLogCompressedFIDGlobalRankTraceEventBits
                  bits target pos) event)) /\
      forall occurrence,
        (subLogCompressedFIDGlobalSelectTraceResult
          bits target occurrence).toCosted =
            subLogSelectFromPackedClarkRouteInterpretedCosted
              bits target occurrence /\
          (subLogCompressedFIDGlobalSelectTraceResult
            bits target occurrence).toCosted =
            subLogSelectFromPackedClarkRouteCosted bits target occurrence /\
          (forall event,
            event ∈
                (subLogCompressedFIDGlobalSelectTraceResult
                  bits target occurrence).trace ->
              event.isReadWord \/ event.isWordPrimitive) /\
          (forall event,
            event ∈
                (subLogCompressedFIDGlobalSelectTraceResult
                  bits target occurrence).trace ->
              event.matchesReadStore
                (subLogCompressedFIDTargetGlobalTraceReadStore
                  bits target)) /\
          (forall event,
            event ∈
                (subLogCompressedFIDGlobalSelectTraceResult
                  bits target occurrence).trace ->
              subLogCompressedFIDTraceEventReadAddressFitsInBits
                (subLogCompressedFIDGlobalSelectTraceEventBits
                  bits target occurrence) event) /\
          (forall event,
            event ∈
                (subLogCompressedFIDGlobalSelectTraceResult
                  bits target occurrence).trace ->
              subLogCompressedFIDTraceEventPrimitiveOperandsFitInBits
                (subLogCompressedFIDGlobalSelectTraceEventBits
                  bits target occurrence) event) := by
  rcases
    subLogCompressedFIDTargetGlobalPayloadStore_execution_story
      bits target with
    ⟨haccess, hrank, hselect⟩
  constructor
  · intro i
    rcases haccess i with ⟨hinterp, hcost, hclass, hstore⟩
    exact
      ⟨hinterp, hcost, hclass, hstore,
        (fun event hmem =>
          (subLogCompressedFIDGlobalAccessTraceResult_event_bounds
            bits i event hmem).1),
        (fun event hmem =>
          (subLogCompressedFIDGlobalAccessTraceResult_event_bounds
            bits i event hmem).2)⟩
  constructor
  · intro pos
    rcases hrank pos with ⟨hinterp, hcost, hclass, hstore⟩
    exact
      ⟨hinterp, hcost, hclass, hstore,
        (fun event hmem =>
          (subLogCompressedFIDGlobalRankTraceResult_event_bounds
            bits target pos event hmem).1),
        (fun event hmem =>
          (subLogCompressedFIDGlobalRankTraceResult_event_bounds
            bits target pos event hmem).2)⟩
  · intro occurrence
    rcases hselect occurrence with ⟨hinterp, hcost, hclass, hstore⟩
    exact
      ⟨hinterp, hcost, hclass, hstore,
        (fun event hmem =>
          (subLogCompressedFIDGlobalSelectTraceResult_event_bounds
            bits target occurrence event hmem).1),
        (fun event hmem =>
          (subLogCompressedFIDGlobalSelectTraceResult_event_bounds
            bits target occurrence event hmem).2)⟩

/-- Trace-local bit width for the all-target global access trace. -/
def subLogCompressedFIDAllTargetsGlobalAccessTraceEventBits
    (bits : List Bool) (i : Nat) : Nat :=
  subLogCompressedFIDTraceEventBitWidth
    (subLogCompressedFIDAllTargetsGlobalAccessTraceResult bits i).trace

/-- Trace-local bit width for the all-target global rank trace. -/
def subLogCompressedFIDAllTargetsGlobalRankTraceEventBits
    (bits : List Bool) (target : Bool) (pos : Nat) : Nat :=
  subLogCompressedFIDTraceEventBitWidth
    (subLogCompressedFIDAllTargetsGlobalRankTraceResult bits target pos).trace

/-- Trace-local bit width for the all-target global select trace. -/
def subLogCompressedFIDAllTargetsGlobalSelectTraceEventBits
    (bits : List Bool) (target : Bool) (occurrence : Nat) : Nat :=
  subLogCompressedFIDTraceEventBitWidth
    (subLogCompressedFIDAllTargetsGlobalSelectTraceResult
      bits target occurrence).trace

theorem subLogCompressedFIDAllTargetsGlobalAccessTraceResult_event_bounds
    (bits : List Bool) (i : Nat) :
    forall event,
      List.Mem event
        (subLogCompressedFIDAllTargetsGlobalAccessTraceResult bits i).trace ->
        subLogCompressedFIDTraceEventReadAddressFitsInBits
          (subLogCompressedFIDAllTargetsGlobalAccessTraceEventBits
            bits i) event /\
        subLogCompressedFIDTraceEventPrimitiveOperandsFitInBits
          (subLogCompressedFIDAllTargetsGlobalAccessTraceEventBits
            bits i) event := by
  intro event hmem
  constructor
  · exact
      subLogCompressedFIDTraceEventReadAddressFitsInBits_of_mem
        (trace :=
          (subLogCompressedFIDAllTargetsGlobalAccessTraceResult
            bits i).trace)
        (event := event) hmem
  · exact
      subLogCompressedFIDTraceEventPrimitiveOperandsFitInBits_of_mem
        (trace :=
          (subLogCompressedFIDAllTargetsGlobalAccessTraceResult
            bits i).trace)
        (event := event) hmem

theorem subLogCompressedFIDAllTargetsGlobalRankTraceResult_event_bounds
    (bits : List Bool) (target : Bool) (pos : Nat) :
    forall event,
      List.Mem event
        (subLogCompressedFIDAllTargetsGlobalRankTraceResult
          bits target pos).trace ->
        subLogCompressedFIDTraceEventReadAddressFitsInBits
          (subLogCompressedFIDAllTargetsGlobalRankTraceEventBits
            bits target pos) event /\
        subLogCompressedFIDTraceEventPrimitiveOperandsFitInBits
          (subLogCompressedFIDAllTargetsGlobalRankTraceEventBits
            bits target pos) event := by
  intro event hmem
  constructor
  · exact
      subLogCompressedFIDTraceEventReadAddressFitsInBits_of_mem
        (trace :=
          (subLogCompressedFIDAllTargetsGlobalRankTraceResult
            bits target pos).trace)
        (event := event) hmem
  · exact
      subLogCompressedFIDTraceEventPrimitiveOperandsFitInBits_of_mem
        (trace :=
          (subLogCompressedFIDAllTargetsGlobalRankTraceResult
            bits target pos).trace)
        (event := event) hmem

theorem subLogCompressedFIDAllTargetsGlobalSelectTraceResult_event_bounds
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    forall event,
      List.Mem event
        (subLogCompressedFIDAllTargetsGlobalSelectTraceResult
          bits target occurrence).trace ->
        subLogCompressedFIDTraceEventReadAddressFitsInBits
          (subLogCompressedFIDAllTargetsGlobalSelectTraceEventBits
            bits target occurrence) event /\
        subLogCompressedFIDTraceEventPrimitiveOperandsFitInBits
          (subLogCompressedFIDAllTargetsGlobalSelectTraceEventBits
            bits target occurrence) event := by
  intro event hmem
  constructor
  · exact
      subLogCompressedFIDTraceEventReadAddressFitsInBits_of_mem
        (trace :=
          (subLogCompressedFIDAllTargetsGlobalSelectTraceResult
            bits target occurrence).trace)
        (event := event) hmem
  · exact
      subLogCompressedFIDTraceEventPrimitiveOperandsFitInBits_of_mem
        (trace :=
          (subLogCompressedFIDAllTargetsGlobalSelectTraceResult
            bits target occurrence).trace)
        (event := event) hmem

/--
Bounded target-independent global execution story for compressed/FID
rank/select.

This is the all-target analogue of the RMQ global payload-store packet: one
concrete read store supports access, rank/select for both `false` and `true`,
and every trace event has a finite trace-local width bounding payload-read
addresses and word-primitive natural operands/results.
-/
theorem subLogCompressedFIDGlobalPayloadStore_bounded_execution_story
    (bits : List Bool) :
    (forall i,
      (subLogCompressedFIDAllTargetsGlobalAccessTraceResult bits i).toCosted =
          subLogAccessInterpretedCosted bits i /\
        (subLogCompressedFIDAllTargetsGlobalAccessTraceResult bits i).toCosted =
          subLogAccessCosted bits i /\
        (forall event,
          event ∈
              (subLogCompressedFIDAllTargetsGlobalAccessTraceResult
                bits i).trace ->
            event.isReadWord \/ event.isWordPrimitive) /\
        (forall event,
          event ∈
              (subLogCompressedFIDAllTargetsGlobalAccessTraceResult
                bits i).trace ->
            event.matchesReadStore
              (subLogCompressedFIDGlobalTraceReadStore bits)) /\
        (forall event,
          event ∈
              (subLogCompressedFIDAllTargetsGlobalAccessTraceResult
                bits i).trace ->
            subLogCompressedFIDTraceEventReadAddressFitsInBits
              (subLogCompressedFIDAllTargetsGlobalAccessTraceEventBits
                bits i) event) /\
        (forall event,
          event ∈
              (subLogCompressedFIDAllTargetsGlobalAccessTraceResult
                bits i).trace ->
            subLogCompressedFIDTraceEventPrimitiveOperandsFitInBits
              (subLogCompressedFIDAllTargetsGlobalAccessTraceEventBits
                bits i) event)) /\
      (forall target pos,
        (subLogCompressedFIDAllTargetsGlobalRankTraceResult
          bits target pos).toCosted =
            subLogRankInterpretedCosted bits target pos /\
          (subLogCompressedFIDAllTargetsGlobalRankTraceResult
            bits target pos).toCosted =
            subLogRankCosted bits target pos /\
          (forall event,
            event ∈
                (subLogCompressedFIDAllTargetsGlobalRankTraceResult
                  bits target pos).trace ->
              event.isReadWord \/ event.isWordPrimitive) /\
          (forall event,
            event ∈
                (subLogCompressedFIDAllTargetsGlobalRankTraceResult
                  bits target pos).trace ->
              event.matchesReadStore
                (subLogCompressedFIDGlobalTraceReadStore bits)) /\
          (forall event,
            event ∈
                (subLogCompressedFIDAllTargetsGlobalRankTraceResult
                  bits target pos).trace ->
              subLogCompressedFIDTraceEventReadAddressFitsInBits
                (subLogCompressedFIDAllTargetsGlobalRankTraceEventBits
                  bits target pos) event) /\
          (forall event,
            event ∈
                (subLogCompressedFIDAllTargetsGlobalRankTraceResult
                  bits target pos).trace ->
              subLogCompressedFIDTraceEventPrimitiveOperandsFitInBits
                (subLogCompressedFIDAllTargetsGlobalRankTraceEventBits
                  bits target pos) event)) /\
      forall target occurrence,
        (subLogCompressedFIDAllTargetsGlobalSelectTraceResult
          bits target occurrence).toCosted =
            subLogSelectFromPackedClarkRouteInterpretedCosted
              bits target occurrence /\
          (subLogCompressedFIDAllTargetsGlobalSelectTraceResult
            bits target occurrence).toCosted =
            subLogSelectFromPackedClarkRouteCosted bits target occurrence /\
          (forall event,
            event ∈
                (subLogCompressedFIDAllTargetsGlobalSelectTraceResult
                  bits target occurrence).trace ->
              event.isReadWord \/ event.isWordPrimitive) /\
          (forall event,
            event ∈
                (subLogCompressedFIDAllTargetsGlobalSelectTraceResult
                  bits target occurrence).trace ->
              event.matchesReadStore
                (subLogCompressedFIDGlobalTraceReadStore bits)) /\
          (forall event,
            event ∈
                (subLogCompressedFIDAllTargetsGlobalSelectTraceResult
                  bits target occurrence).trace ->
              subLogCompressedFIDTraceEventReadAddressFitsInBits
                (subLogCompressedFIDAllTargetsGlobalSelectTraceEventBits
                  bits target occurrence) event) /\
          (forall event,
            event ∈
                (subLogCompressedFIDAllTargetsGlobalSelectTraceResult
                  bits target occurrence).trace ->
              subLogCompressedFIDTraceEventPrimitiveOperandsFitInBits
                (subLogCompressedFIDAllTargetsGlobalSelectTraceEventBits
                  bits target occurrence) event) := by
  rcases subLogCompressedFIDGlobalPayloadStore_execution_story bits with
    ⟨haccess, hrank, hselect⟩
  constructor
  · intro i
    rcases haccess i with ⟨hinterp, hcost, hclass, hstore⟩
    exact
      ⟨hinterp, hcost, hclass, hstore,
        (fun event hmem =>
          (subLogCompressedFIDAllTargetsGlobalAccessTraceResult_event_bounds
            bits i event hmem).1),
        (fun event hmem =>
          (subLogCompressedFIDAllTargetsGlobalAccessTraceResult_event_bounds
            bits i event hmem).2)⟩
  constructor
  · intro target pos
    rcases hrank target pos with ⟨hinterp, hcost, hclass, hstore⟩
    exact
      ⟨hinterp, hcost, hclass, hstore,
        (fun event hmem =>
          (subLogCompressedFIDAllTargetsGlobalRankTraceResult_event_bounds
            bits target pos event hmem).1),
        (fun event hmem =>
          (subLogCompressedFIDAllTargetsGlobalRankTraceResult_event_bounds
            bits target pos event hmem).2)⟩
  · intro target occurrence
    rcases hselect target occurrence with
      ⟨hinterp, hcost, hclass, hstore⟩
    exact
      ⟨hinterp, hcost, hclass, hstore,
        (fun event hmem =>
          (subLogCompressedFIDAllTargetsGlobalSelectTraceResult_event_bounds
            bits target occurrence event hmem).1),
        (fun event hmem =>
          (subLogCompressedFIDAllTargetsGlobalSelectTraceResult_event_bounds
            bits target occurrence event hmem).2)⟩

theorem subLogSelectFromPackedClarkRouteInterpretedCosted_cost_le
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    (subLogSelectFromPackedClarkRouteInterpretedCosted
      bits target occurrence).cost <=
        fixedWeightSubLogConcretePackedClarkQueryCost := by
  rw [subLogSelectFromPackedClarkRouteInterpretedCosted_refines]
  exact
    (fixedWeightSubLogConcretePackedClarkProfile bits).2.2.2.2
      target occurrence |>.1

theorem subLogSelectFromPackedClarkRouteInterpretedCosted_erase
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    (subLogSelectFromPackedClarkRouteInterpretedCosted
      bits target occurrence).erase =
        Succinct.select target bits occurrence := by
  rw [subLogSelectFromPackedClarkRouteInterpretedCosted_refines]
  exact subLogSelectFromPackedClarkRouteCosted_erase bits target occurrence

theorem fixedWeightSubLogConcretePackedClarkInterpretedProfile
    (bits : List Bool) :
    (fixedWeightSubLogConcretePackedClarkPayload bits).length <=
        fixedWeightPayloadBudget bits +
          fixedWeightSubLogConcretePackedClarkOverhead bits.length /\
      SuccinctSpace.LittleOLinear
        fixedWeightSubLogConcretePackedClarkOverhead /\
      (forall i,
        (subLogAccessInterpretedCosted bits i).cost <=
            fixedWeightSubLogConcretePackedClarkQueryCost /\
          (subLogAccessInterpretedCosted bits i).erase = bits[i]?) /\
      (forall target pos,
        (subLogRankInterpretedCosted bits target pos).cost <=
            fixedWeightSubLogConcretePackedClarkQueryCost /\
          (subLogRankInterpretedCosted bits target pos).erase =
            Succinct.rankPrefix target bits pos) /\
      forall target occurrence,
        (subLogSelectFromPackedClarkRouteInterpretedCosted
          bits target occurrence).cost <=
            fixedWeightSubLogConcretePackedClarkQueryCost /\
          (subLogSelectFromPackedClarkRouteInterpretedCosted
            bits target occurrence).erase =
            Succinct.select target bits occurrence := by
  refine
    ⟨fixedWeightSubLogConcretePackedClarkPayload_length_le bits,
      fixedWeightSubLogConcretePackedClarkOverhead_littleO,
      ?_, ?_, ?_⟩
  · intro i
    exact
      ⟨by
        rw [subLogAccessInterpretedCosted_cost]
        exact Nat.le_trans (by omega : 4 <= 6)
          (Nat.le_max_left 6 (subLogPackedClarkSelectQueryCost + 4)),
        subLogAccessInterpretedCosted_erase bits i⟩
  · intro target pos
    exact
      ⟨by
        rw [subLogRankInterpretedCosted_cost]
        exact Nat.le_max_left 6 (subLogPackedClarkSelectQueryCost + 4),
        subLogRankInterpretedCosted_erase bits target pos⟩
  · intro target occurrence
    exact
      ⟨subLogSelectFromPackedClarkRouteInterpretedCosted_cost_le
        bits target occurrence,
        subLogSelectFromPackedClarkRouteInterpretedCosted_erase
          bits target occurrence⟩


end RankSelectSpec

end RMQ
