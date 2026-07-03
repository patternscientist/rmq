import RMQ.Core.RankSelectPublic
import RMQ.Core.RankSelectCompressedSubLogRAM

/-!
# Public Word-RAM replay surface for compressed/FID rank/select

This module is the public facade corresponding to
`RankSelectCompressedSubLogRAM`: it packages the interpreted access, rank, and
select queries into the same compressed/FID family theorem shape as
`RankSelectPublic`.
-/

namespace RMQ

namespace RankSelect

/-- Interpreted access query for the concrete fixed-weight compressed/FID family. -/
abbrev compressedFIDFixedWeightAccessInterpretedCosted
    (bits : List Bool) (i : Nat) : Costed (Option Bool) :=
  RMQ.RankSelectSpec.subLogAccessInterpretedCosted bits i

/-- Four-segment read-only store for the compressed/FID access trace replay. -/
abbrev compressedFIDFixedWeightAccessTraceReadStore
    (bits : List Bool) : WordRAM.ReadStore :=
  RMQ.RankSelectSpec.subLogAccessTraceReadStore bits

/-- Trace-result replay for the concrete fixed-weight compressed/FID access query. -/
abbrev compressedFIDFixedWeightAccessTraceResult
    (bits : List Bool) (i : Nat) : WordRAM.TraceResult (Option Bool) :=
  RMQ.RankSelectSpec.subLogAccessTraceResult bits i

/-- Interpreted rank query for the concrete fixed-weight compressed/FID family. -/
abbrev compressedFIDFixedWeightRankInterpretedCosted
    (bits : List Bool) (target : Bool) (pos : Nat) : Costed Nat :=
  RMQ.RankSelectSpec.subLogRankInterpretedCosted bits target pos

/-- Six-segment read-only store for the compressed/FID rank trace replay. -/
abbrev compressedFIDFixedWeightRankTraceReadStore
    (bits : List Bool) (target : Bool) : WordRAM.ReadStore :=
  RMQ.RankSelectSpec.subLogRankTraceReadStore bits target

/-- Trace-result replay for the concrete fixed-weight compressed/FID rank query. -/
abbrev compressedFIDFixedWeightRankTraceResult
    (bits : List Bool) (target : Bool) (pos : Nat) :
    WordRAM.TraceResult Nat :=
  RMQ.RankSelectSpec.subLogRankTraceResult bits target pos

/-- Interpreted select query for the concrete fixed-weight compressed/FID family. -/
abbrev compressedFIDFixedWeightSelectInterpretedCosted
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    Costed (Option Nat) :=
  RMQ.RankSelectSpec.subLogSelectFromPackedClarkRouteInterpretedCosted
    bits target occurrence

/-- Target-specific read-only store for the compressed/FID select trace replay. -/
abbrev compressedFIDFixedWeightSelectTraceReadStore
    (bits : List Bool) (target : Bool) : WordRAM.ReadStore :=
  RMQ.RankSelectSpec.subLogSelectFromPackedClarkRouteTraceReadStore
    bits target

/-- Trace-result replay for the concrete fixed-weight compressed/FID select query. -/
abbrev compressedFIDFixedWeightSelectTraceResult
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  RMQ.RankSelectSpec.subLogSelectFromPackedClarkRouteTraceResult
    bits target occurrence

/--
Target-indexed global store for the access/rank/select trace packets.

The store is target-indexed because the current rank and Clark-select routing
payloads are target-specific.  The access, rank, and select traces are relabeled
into disjoint segment ranges of this one store.  The target-independent public
store below keeps access shared and includes both false/true rank and select
target ranges at once.
-/
abbrev compressedFIDFixedWeightTargetGlobalTraceReadStore
    (bits : List Bool) (target : Bool) : WordRAM.ReadStore :=
  RMQ.RankSelectSpec.subLogCompressedFIDTargetGlobalTraceReadStore
    bits target

/--
Target-independent global store for the compressed/FID access/rank/select trace
packets.

The access range is shared once, while rank and select have disjoint false/true
target ranges.
-/
abbrev compressedFIDFixedWeightGlobalTraceReadStore
    (bits : List Bool) : WordRAM.ReadStore :=
  RMQ.RankSelectSpec.subLogCompressedFIDGlobalTraceReadStore bits

/-- Access trace relabeled into the target-indexed global compressed/FID store. -/
abbrev compressedFIDFixedWeightGlobalAccessTraceResult
    (bits : List Bool) (i : Nat) : WordRAM.TraceResult (Option Bool) :=
  RMQ.RankSelectSpec.subLogCompressedFIDGlobalAccessTraceResult bits i

/-- Rank trace relabeled into the target-indexed global compressed/FID store. -/
abbrev compressedFIDFixedWeightGlobalRankTraceResult
    (bits : List Bool) (target : Bool) (pos : Nat) :
    WordRAM.TraceResult Nat :=
  RMQ.RankSelectSpec.subLogCompressedFIDGlobalRankTraceResult
    bits target pos

/-- Select trace relabeled into the target-indexed global compressed/FID store. -/
abbrev compressedFIDFixedWeightGlobalSelectTraceResult
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  RMQ.RankSelectSpec.subLogCompressedFIDGlobalSelectTraceResult
    bits target occurrence

/-- Access trace relabeled into the target-independent global compressed/FID store. -/
abbrev compressedFIDFixedWeightGlobalPayloadStoreAccessTraceResult
    (bits : List Bool) (i : Nat) : WordRAM.TraceResult (Option Bool) :=
  RMQ.RankSelectSpec.subLogCompressedFIDAllTargetsGlobalAccessTraceResult
    bits i

/-- Rank trace relabeled into the target-independent global compressed/FID store. -/
abbrev compressedFIDFixedWeightGlobalPayloadStoreRankTraceResult
    (bits : List Bool) (target : Bool) (pos : Nat) :
    WordRAM.TraceResult Nat :=
  RMQ.RankSelectSpec.subLogCompressedFIDAllTargetsGlobalRankTraceResult
    bits target pos

/-- Select trace relabeled into the target-independent global compressed/FID store. -/
abbrev compressedFIDFixedWeightGlobalPayloadStoreSelectTraceResult
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  RMQ.RankSelectSpec.subLogCompressedFIDAllTargetsGlobalSelectTraceResult
    bits target occurrence

/-- Read-address width predicate for compressed/FID rank/select trace events. -/
abbrev compressedFIDFixedWeightTraceEventReadAddressFitsInBits
    (bits : Nat) (event : WordRAM.TraceEvent) : Prop :=
  RMQ.RankSelectSpec.subLogCompressedFIDTraceEventReadAddressFitsInBits
    bits event

/--
Word-primitive operand/result width predicate for compressed/FID rank/select
trace events.
-/
abbrev compressedFIDFixedWeightTraceEventPrimitiveOperandsFitInBits
    (bits : Nat) (event : WordRAM.TraceEvent) : Prop :=
  RMQ.RankSelectSpec.subLogCompressedFIDTraceEventPrimitiveOperandsFitInBits
    bits event

/-- Trace-local event bit width for a global access trace. -/
abbrev compressedFIDFixedWeightGlobalAccessTraceEventBits
    (bits : List Bool) (i : Nat) : Nat :=
  RMQ.RankSelectSpec.subLogCompressedFIDGlobalAccessTraceEventBits bits i

/-- Trace-local event bit width for a global rank trace. -/
abbrev compressedFIDFixedWeightGlobalRankTraceEventBits
    (bits : List Bool) (target : Bool) (pos : Nat) : Nat :=
  RMQ.RankSelectSpec.subLogCompressedFIDGlobalRankTraceEventBits
    bits target pos

/-- Trace-local event bit width for a global select trace. -/
abbrev compressedFIDFixedWeightGlobalSelectTraceEventBits
    (bits : List Bool) (target : Bool) (occurrence : Nat) : Nat :=
  RMQ.RankSelectSpec.subLogCompressedFIDGlobalSelectTraceEventBits
    bits target occurrence

/-- Trace-local event bit width for the target-independent global access trace. -/
abbrev compressedFIDFixedWeightGlobalPayloadStoreAccessTraceEventBits
    (bits : List Bool) (i : Nat) : Nat :=
  RMQ.RankSelectSpec.subLogCompressedFIDAllTargetsGlobalAccessTraceEventBits
    bits i

/-- Trace-local event bit width for the target-independent global rank trace. -/
abbrev compressedFIDFixedWeightGlobalPayloadStoreRankTraceEventBits
    (bits : List Bool) (target : Bool) (pos : Nat) : Nat :=
  RMQ.RankSelectSpec.subLogCompressedFIDAllTargetsGlobalRankTraceEventBits
    bits target pos

/-- Trace-local event bit width for the target-independent global select trace. -/
abbrev compressedFIDFixedWeightGlobalPayloadStoreSelectTraceEventBits
    (bits : List Bool) (target : Bool) (occurrence : Nat) : Nat :=
  RMQ.RankSelectSpec.subLogCompressedFIDAllTargetsGlobalSelectTraceEventBits
    bits target occurrence

theorem compressedFIDFixedWeightAccessInterpretedCosted_refines_accessCosted
    (bits : List Bool) (i : Nat) :
    compressedFIDFixedWeightAccessInterpretedCosted bits i =
      RMQ.RankSelectSpec.subLogAccessCosted bits i := by
  exact
    RMQ.RankSelectSpec.subLogAccessInterpretedCosted_refines_subLogAccessCosted
      bits i

/--
Execution-story packet for the access leg of the concrete fixed-weight
compressed/FID family.

The trace result projects to the interpreted access query, refines the existing
costed access query, contains only Word-RAM read/word-primitive events, and all
reads agree with the concrete four-segment access payload store.
-/
theorem compressedFIDFixedWeightAccessTraceResult_execution_story
    (bits : List Bool) (i : Nat) :
    (compressedFIDFixedWeightAccessTraceResult bits i).toCosted =
        compressedFIDFixedWeightAccessInterpretedCosted bits i /\
      (compressedFIDFixedWeightAccessTraceResult bits i).toCosted =
        RMQ.RankSelectSpec.subLogAccessCosted bits i /\
      (forall event,
        event ∈ (compressedFIDFixedWeightAccessTraceResult bits i).trace ->
          event.isReadWord \/ event.isWordPrimitive) /\
      (forall event,
        event ∈ (compressedFIDFixedWeightAccessTraceResult bits i).trace ->
          event.matchesReadStore
            (compressedFIDFixedWeightAccessTraceReadStore bits)) := by
  exact
    RMQ.RankSelectSpec.subLogAccessTraceResult_execution_story bits i

theorem compressedFIDFixedWeightRankInterpretedCosted_refines_rankCosted
    (bits : List Bool) (target : Bool) (pos : Nat) :
    compressedFIDFixedWeightRankInterpretedCosted bits target pos =
      RMQ.RankSelectSpec.subLogRankCosted bits target pos := by
  exact
    RMQ.RankSelectSpec.subLogRankInterpretedCosted_refines_subLogRankCosted
      bits target pos

/--
Execution-story packet for the rank leg of the concrete fixed-weight
compressed/FID family.

The trace result projects to the interpreted rank query, refines the existing
costed rank query, contains only Word-RAM read/word-primitive events, and all
reads agree with the concrete six-segment rank payload store.
-/
theorem compressedFIDFixedWeightRankTraceResult_execution_story
    (bits : List Bool) (target : Bool) (pos : Nat) :
    (compressedFIDFixedWeightRankTraceResult bits target pos).toCosted =
        compressedFIDFixedWeightRankInterpretedCosted bits target pos /\
      (compressedFIDFixedWeightRankTraceResult bits target pos).toCosted =
        RMQ.RankSelectSpec.subLogRankCosted bits target pos /\
      (forall event,
        event ∈
            (compressedFIDFixedWeightRankTraceResult
              bits target pos).trace ->
          event.isReadWord \/ event.isWordPrimitive) /\
      (forall event,
        event ∈
            (compressedFIDFixedWeightRankTraceResult
              bits target pos).trace ->
          event.matchesReadStore
            (compressedFIDFixedWeightRankTraceReadStore bits target)) := by
  exact
    RMQ.RankSelectSpec.subLogRankTraceResult_execution_story bits target pos

theorem compressedFIDFixedWeightSelectInterpretedCosted_refines_selectCosted
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    compressedFIDFixedWeightSelectInterpretedCosted bits target occurrence =
      RMQ.RankSelectSpec.subLogSelectFromPackedClarkRouteCosted
        bits target occurrence := by
  exact
    RMQ.RankSelectSpec.subLogSelectFromPackedClarkRouteInterpretedCosted_refines
      bits target occurrence

/--
Execution-story packet for the select leg of the concrete fixed-weight
compressed/FID family.

The trace first reads the charged packed-Clark route directory, then performs
the constant local fixed-weight block decode through code/length/class/shared
decoder payload reads.
-/
theorem compressedFIDFixedWeightSelectTraceResult_execution_story
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    (compressedFIDFixedWeightSelectTraceResult
      bits target occurrence).toCosted =
        compressedFIDFixedWeightSelectInterpretedCosted
          bits target occurrence /\
      (compressedFIDFixedWeightSelectTraceResult
        bits target occurrence).toCosted =
        RMQ.RankSelectSpec.subLogSelectFromPackedClarkRouteCosted
          bits target occurrence /\
      (forall event,
        event ∈
            (compressedFIDFixedWeightSelectTraceResult
              bits target occurrence).trace ->
          event.isReadWord \/ event.isWordPrimitive) /\
      (forall event,
        event ∈
            (compressedFIDFixedWeightSelectTraceResult
              bits target occurrence).trace ->
          event.matchesReadStore
            (compressedFIDFixedWeightSelectTraceReadStore bits target)) := by
  exact
    RMQ.RankSelectSpec.subLogSelectFromPackedClarkRouteTraceResult_execution_story
      bits target occurrence

/--
One target-indexed global payload-store execution theorem for the concrete
fixed-weight compressed/FID family.

For a fixed `bits` and `target`, the access, rank, and select trace packets are
relabeled into disjoint segment ranges of one concrete read store, while still
projecting to the interpreted queries and the existing costed query semantics.
-/
theorem compressedFIDFixedWeightTargetGlobalPayloadStore_execution_story
    (bits : List Bool) (target : Bool) :
    (forall i,
      (compressedFIDFixedWeightGlobalAccessTraceResult bits i).toCosted =
          compressedFIDFixedWeightAccessInterpretedCosted bits i /\
        (compressedFIDFixedWeightGlobalAccessTraceResult bits i).toCosted =
          RMQ.RankSelectSpec.subLogAccessCosted bits i /\
        (forall event,
          event ∈
              (compressedFIDFixedWeightGlobalAccessTraceResult
                bits i).trace ->
            event.isReadWord \/ event.isWordPrimitive) /\
        (forall event,
          event ∈
              (compressedFIDFixedWeightGlobalAccessTraceResult
                bits i).trace ->
            event.matchesReadStore
              (compressedFIDFixedWeightTargetGlobalTraceReadStore
                bits target))) /\
      (forall pos,
        (compressedFIDFixedWeightGlobalRankTraceResult
          bits target pos).toCosted =
            compressedFIDFixedWeightRankInterpretedCosted
              bits target pos /\
          (compressedFIDFixedWeightGlobalRankTraceResult
            bits target pos).toCosted =
            RMQ.RankSelectSpec.subLogRankCosted bits target pos /\
          (forall event,
            event ∈
                (compressedFIDFixedWeightGlobalRankTraceResult
                  bits target pos).trace ->
              event.isReadWord \/ event.isWordPrimitive) /\
          (forall event,
            event ∈
                (compressedFIDFixedWeightGlobalRankTraceResult
                  bits target pos).trace ->
              event.matchesReadStore
                (compressedFIDFixedWeightTargetGlobalTraceReadStore
                  bits target))) /\
      forall occurrence,
        (compressedFIDFixedWeightGlobalSelectTraceResult
          bits target occurrence).toCosted =
            compressedFIDFixedWeightSelectInterpretedCosted
              bits target occurrence /\
          (compressedFIDFixedWeightGlobalSelectTraceResult
            bits target occurrence).toCosted =
            RMQ.RankSelectSpec.subLogSelectFromPackedClarkRouteCosted
              bits target occurrence /\
          (forall event,
            event ∈
                (compressedFIDFixedWeightGlobalSelectTraceResult
                  bits target occurrence).trace ->
              event.isReadWord \/ event.isWordPrimitive) /\
          (forall event,
            event ∈
                (compressedFIDFixedWeightGlobalSelectTraceResult
                  bits target occurrence).trace ->
              event.matchesReadStore
                (compressedFIDFixedWeightTargetGlobalTraceReadStore
                  bits target)) := by
  exact
    RMQ.RankSelectSpec.subLogCompressedFIDTargetGlobalPayloadStore_execution_story
      bits target

/--
Bounded target-indexed global payload-store execution theorem for the concrete
fixed-weight compressed/FID family.

This is the rank/select analogue of RMQ's bounded global trace packet: for
fixed `bits` and `target`, access/rank/select global traces are backed by one
target-indexed read store, and every trace event has a finite trace-local width
bounding payload-read addresses and word-primitive natural operands/results.
-/
theorem compressedFIDFixedWeightTargetGlobalPayloadStore_bounded_execution_story
    (bits : List Bool) (target : Bool) :
    (forall i,
      (compressedFIDFixedWeightGlobalAccessTraceResult bits i).toCosted =
          compressedFIDFixedWeightAccessInterpretedCosted bits i /\
        (compressedFIDFixedWeightGlobalAccessTraceResult bits i).toCosted =
          RMQ.RankSelectSpec.subLogAccessCosted bits i /\
        (forall event,
          event ∈
              (compressedFIDFixedWeightGlobalAccessTraceResult bits i).trace ->
            event.isReadWord \/ event.isWordPrimitive) /\
        (forall event,
          event ∈
              (compressedFIDFixedWeightGlobalAccessTraceResult bits i).trace ->
            event.matchesReadStore
              (compressedFIDFixedWeightTargetGlobalTraceReadStore
                bits target)) /\
        (forall event,
          event ∈
              (compressedFIDFixedWeightGlobalAccessTraceResult bits i).trace ->
            compressedFIDFixedWeightTraceEventReadAddressFitsInBits
              (compressedFIDFixedWeightGlobalAccessTraceEventBits
                bits i) event) /\
        (forall event,
          event ∈
              (compressedFIDFixedWeightGlobalAccessTraceResult bits i).trace ->
            compressedFIDFixedWeightTraceEventPrimitiveOperandsFitInBits
              (compressedFIDFixedWeightGlobalAccessTraceEventBits
                bits i) event)) /\
      (forall pos,
        (compressedFIDFixedWeightGlobalRankTraceResult
          bits target pos).toCosted =
            compressedFIDFixedWeightRankInterpretedCosted
              bits target pos /\
          (compressedFIDFixedWeightGlobalRankTraceResult
            bits target pos).toCosted =
            RMQ.RankSelectSpec.subLogRankCosted bits target pos /\
          (forall event,
            event ∈
                (compressedFIDFixedWeightGlobalRankTraceResult
                  bits target pos).trace ->
              event.isReadWord \/ event.isWordPrimitive) /\
          (forall event,
            event ∈
                (compressedFIDFixedWeightGlobalRankTraceResult
                  bits target pos).trace ->
              event.matchesReadStore
                (compressedFIDFixedWeightTargetGlobalTraceReadStore
                  bits target)) /\
          (forall event,
            event ∈
                (compressedFIDFixedWeightGlobalRankTraceResult
                  bits target pos).trace ->
              compressedFIDFixedWeightTraceEventReadAddressFitsInBits
                (compressedFIDFixedWeightGlobalRankTraceEventBits
                  bits target pos) event) /\
          (forall event,
            event ∈
                (compressedFIDFixedWeightGlobalRankTraceResult
                  bits target pos).trace ->
              compressedFIDFixedWeightTraceEventPrimitiveOperandsFitInBits
                (compressedFIDFixedWeightGlobalRankTraceEventBits
                  bits target pos) event)) /\
      forall occurrence,
        (compressedFIDFixedWeightGlobalSelectTraceResult
          bits target occurrence).toCosted =
            compressedFIDFixedWeightSelectInterpretedCosted
              bits target occurrence /\
          (compressedFIDFixedWeightGlobalSelectTraceResult
            bits target occurrence).toCosted =
            RMQ.RankSelectSpec.subLogSelectFromPackedClarkRouteCosted
              bits target occurrence /\
          (forall event,
            event ∈
                (compressedFIDFixedWeightGlobalSelectTraceResult
                  bits target occurrence).trace ->
              event.isReadWord \/ event.isWordPrimitive) /\
          (forall event,
            event ∈
                (compressedFIDFixedWeightGlobalSelectTraceResult
                  bits target occurrence).trace ->
              event.matchesReadStore
                (compressedFIDFixedWeightTargetGlobalTraceReadStore
                  bits target)) /\
          (forall event,
            event ∈
                (compressedFIDFixedWeightGlobalSelectTraceResult
                  bits target occurrence).trace ->
              compressedFIDFixedWeightTraceEventReadAddressFitsInBits
                (compressedFIDFixedWeightGlobalSelectTraceEventBits
                  bits target occurrence) event) /\
          (forall event,
            event ∈
                (compressedFIDFixedWeightGlobalSelectTraceResult
                  bits target occurrence).trace ->
              compressedFIDFixedWeightTraceEventPrimitiveOperandsFitInBits
                (compressedFIDFixedWeightGlobalSelectTraceEventBits
                  bits target occurrence) event) := by
  exact
    RMQ.RankSelectSpec.subLogCompressedFIDTargetGlobalPayloadStore_bounded_execution_story
      bits target

/--
Target-independent global payload-store execution theorem for the concrete
fixed-weight compressed/FID family.

For fixed `bits`, the access trace and both false/true target rank/select
traces are relabeled into disjoint segment ranges of one concrete read store,
while still projecting to the interpreted queries and the existing costed query
semantics.
-/
theorem compressedFIDFixedWeightGlobalPayloadStore_execution_story
    (bits : List Bool) :
    (forall i,
      (compressedFIDFixedWeightGlobalPayloadStoreAccessTraceResult
        bits i).toCosted =
          compressedFIDFixedWeightAccessInterpretedCosted bits i /\
        (compressedFIDFixedWeightGlobalPayloadStoreAccessTraceResult
          bits i).toCosted =
          RMQ.RankSelectSpec.subLogAccessCosted bits i /\
        (forall event,
          event ∈
              (compressedFIDFixedWeightGlobalPayloadStoreAccessTraceResult
                bits i).trace ->
            event.isReadWord \/ event.isWordPrimitive) /\
        (forall event,
          event ∈
              (compressedFIDFixedWeightGlobalPayloadStoreAccessTraceResult
                bits i).trace ->
            event.matchesReadStore
              (compressedFIDFixedWeightGlobalTraceReadStore bits))) /\
      (forall target pos,
        (compressedFIDFixedWeightGlobalPayloadStoreRankTraceResult
          bits target pos).toCosted =
            compressedFIDFixedWeightRankInterpretedCosted
              bits target pos /\
          (compressedFIDFixedWeightGlobalPayloadStoreRankTraceResult
            bits target pos).toCosted =
            RMQ.RankSelectSpec.subLogRankCosted bits target pos /\
          (forall event,
            event ∈
                (compressedFIDFixedWeightGlobalPayloadStoreRankTraceResult
                  bits target pos).trace ->
              event.isReadWord \/ event.isWordPrimitive) /\
          (forall event,
            event ∈
                (compressedFIDFixedWeightGlobalPayloadStoreRankTraceResult
                  bits target pos).trace ->
              event.matchesReadStore
                (compressedFIDFixedWeightGlobalTraceReadStore bits))) /\
      forall target occurrence,
        (compressedFIDFixedWeightGlobalPayloadStoreSelectTraceResult
          bits target occurrence).toCosted =
            compressedFIDFixedWeightSelectInterpretedCosted
              bits target occurrence /\
          (compressedFIDFixedWeightGlobalPayloadStoreSelectTraceResult
            bits target occurrence).toCosted =
            RMQ.RankSelectSpec.subLogSelectFromPackedClarkRouteCosted
              bits target occurrence /\
          (forall event,
            event ∈
                (compressedFIDFixedWeightGlobalPayloadStoreSelectTraceResult
                  bits target occurrence).trace ->
              event.isReadWord \/ event.isWordPrimitive) /\
          (forall event,
            event ∈
                (compressedFIDFixedWeightGlobalPayloadStoreSelectTraceResult
                  bits target occurrence).trace ->
              event.matchesReadStore
                (compressedFIDFixedWeightGlobalTraceReadStore bits)) := by
  exact
    RMQ.RankSelectSpec.subLogCompressedFIDGlobalPayloadStore_execution_story
      bits

/--
Bounded target-independent global payload-store execution theorem for the
concrete fixed-weight compressed/FID family.

This is the polished rank/select analogue of RMQ's bounded global payload-store
packet: one concrete read store supports access, rank/select for both targets,
and every trace event has a finite trace-local width bounding payload-read
addresses and word-primitive natural operands/results.
-/
theorem compressedFIDFixedWeightGlobalPayloadStore_bounded_execution_story
    (bits : List Bool) :
    (forall i,
      (compressedFIDFixedWeightGlobalPayloadStoreAccessTraceResult
        bits i).toCosted =
          compressedFIDFixedWeightAccessInterpretedCosted bits i /\
        (compressedFIDFixedWeightGlobalPayloadStoreAccessTraceResult
          bits i).toCosted =
          RMQ.RankSelectSpec.subLogAccessCosted bits i /\
        (forall event,
          event ∈
              (compressedFIDFixedWeightGlobalPayloadStoreAccessTraceResult
                bits i).trace ->
            event.isReadWord \/ event.isWordPrimitive) /\
        (forall event,
          event ∈
              (compressedFIDFixedWeightGlobalPayloadStoreAccessTraceResult
                bits i).trace ->
            event.matchesReadStore
              (compressedFIDFixedWeightGlobalTraceReadStore bits)) /\
        (forall event,
          event ∈
              (compressedFIDFixedWeightGlobalPayloadStoreAccessTraceResult
                bits i).trace ->
            compressedFIDFixedWeightTraceEventReadAddressFitsInBits
              (compressedFIDFixedWeightGlobalPayloadStoreAccessTraceEventBits
                bits i) event) /\
        (forall event,
          event ∈
              (compressedFIDFixedWeightGlobalPayloadStoreAccessTraceResult
                bits i).trace ->
            compressedFIDFixedWeightTraceEventPrimitiveOperandsFitInBits
              (compressedFIDFixedWeightGlobalPayloadStoreAccessTraceEventBits
                bits i) event)) /\
      (forall target pos,
        (compressedFIDFixedWeightGlobalPayloadStoreRankTraceResult
          bits target pos).toCosted =
            compressedFIDFixedWeightRankInterpretedCosted
              bits target pos /\
          (compressedFIDFixedWeightGlobalPayloadStoreRankTraceResult
            bits target pos).toCosted =
            RMQ.RankSelectSpec.subLogRankCosted bits target pos /\
          (forall event,
            event ∈
                (compressedFIDFixedWeightGlobalPayloadStoreRankTraceResult
                  bits target pos).trace ->
              event.isReadWord \/ event.isWordPrimitive) /\
          (forall event,
            event ∈
                (compressedFIDFixedWeightGlobalPayloadStoreRankTraceResult
                  bits target pos).trace ->
              event.matchesReadStore
                (compressedFIDFixedWeightGlobalTraceReadStore bits)) /\
          (forall event,
            event ∈
                (compressedFIDFixedWeightGlobalPayloadStoreRankTraceResult
                  bits target pos).trace ->
              compressedFIDFixedWeightTraceEventReadAddressFitsInBits
                (compressedFIDFixedWeightGlobalPayloadStoreRankTraceEventBits
                  bits target pos) event) /\
          (forall event,
            event ∈
                (compressedFIDFixedWeightGlobalPayloadStoreRankTraceResult
                  bits target pos).trace ->
              compressedFIDFixedWeightTraceEventPrimitiveOperandsFitInBits
                (compressedFIDFixedWeightGlobalPayloadStoreRankTraceEventBits
                  bits target pos) event)) /\
      forall target occurrence,
        (compressedFIDFixedWeightGlobalPayloadStoreSelectTraceResult
          bits target occurrence).toCosted =
            compressedFIDFixedWeightSelectInterpretedCosted
              bits target occurrence /\
          (compressedFIDFixedWeightGlobalPayloadStoreSelectTraceResult
            bits target occurrence).toCosted =
            RMQ.RankSelectSpec.subLogSelectFromPackedClarkRouteCosted
              bits target occurrence /\
          (forall event,
            event ∈
                (compressedFIDFixedWeightGlobalPayloadStoreSelectTraceResult
                  bits target occurrence).trace ->
              event.isReadWord \/ event.isWordPrimitive) /\
          (forall event,
            event ∈
                (compressedFIDFixedWeightGlobalPayloadStoreSelectTraceResult
                  bits target occurrence).trace ->
              event.matchesReadStore
                (compressedFIDFixedWeightGlobalTraceReadStore bits)) /\
          (forall event,
            event ∈
                (compressedFIDFixedWeightGlobalPayloadStoreSelectTraceResult
                  bits target occurrence).trace ->
              compressedFIDFixedWeightTraceEventReadAddressFitsInBits
                (compressedFIDFixedWeightGlobalPayloadStoreSelectTraceEventBits
                  bits target occurrence) event) /\
          (forall event,
            event ∈
                (compressedFIDFixedWeightGlobalPayloadStoreSelectTraceResult
                  bits target occurrence).trace ->
              compressedFIDFixedWeightTraceEventPrimitiveOperandsFitInBits
                (compressedFIDFixedWeightGlobalPayloadStoreSelectTraceEventBits
                  bits target occurrence) event) := by
  exact
    RMQ.RankSelectSpec.subLogCompressedFIDGlobalPayloadStore_bounded_execution_story
      bits

/--
Pointwise interpreted compressed/FID profile.

The payload bound and asymptotic overhead are identical to the existing
compressed/FID profile; the query clauses use the interpreted replay functions.
-/
theorem compressedFIDFixedWeightInterpretedConstantQueryProfile
    (bits : List Bool) :
    (compressedFIDFixedWeightPayload bits).length <=
        fixedWeightPayloadBudget bits +
          compressedFIDFixedWeightOverhead bits.length /\
      SuccinctSpace.LittleOLinear compressedFIDFixedWeightOverhead /\
      (forall i,
        (compressedFIDFixedWeightAccessInterpretedCosted bits i).cost <=
            compressedFIDFixedWeightQueryCost /\
          (compressedFIDFixedWeightAccessInterpretedCosted bits i).erase =
            bits[i]?) /\
      (forall target pos,
        (compressedFIDFixedWeightRankInterpretedCosted
          bits target pos).cost <= compressedFIDFixedWeightQueryCost /\
          (compressedFIDFixedWeightRankInterpretedCosted
            bits target pos).erase =
            Succinct.rankPrefix target bits pos) /\
      forall target occurrence,
        (compressedFIDFixedWeightSelectInterpretedCosted
          bits target occurrence).cost <=
            compressedFIDFixedWeightQueryCost /\
          (compressedFIDFixedWeightSelectInterpretedCosted
            bits target occurrence).erase =
            Succinct.select target bits occurrence := by
  exact
    RMQ.RankSelectSpec.fixedWeightSubLogConcretePackedClarkInterpretedProfile
      bits

/-- Concrete compressed/FID directory whose access/rank/select queries are interpreted replays. -/
def compressedFIDFixedWeightInterpretedDirectory
    (bits : List Bool) :
    CompressedDirectory bits
      (compressedFIDFixedWeightOverhead bits.length)
      compressedFIDFixedWeightQueryCost where
  payload := compressedFIDFixedWeightPayload bits
  payload_length_le :=
    (compressedFIDFixedWeightInterpretedConstantQueryProfile bits).1
  accessCosted := compressedFIDFixedWeightAccessInterpretedCosted bits
  rankCosted := compressedFIDFixedWeightRankInterpretedCosted bits
  selectCosted := compressedFIDFixedWeightSelectInterpretedCosted bits
  access_cost_le := by
    intro i
    exact
      ((compressedFIDFixedWeightInterpretedConstantQueryProfile
        bits).2.2.1 i).1
  rank_cost_le := by
    intro target pos
    exact
      ((compressedFIDFixedWeightInterpretedConstantQueryProfile
        bits).2.2.2.1 target pos).1
  select_cost_le := by
    intro target occurrence
    exact
      ((compressedFIDFixedWeightInterpretedConstantQueryProfile
        bits).2.2.2.2 target occurrence).1
  access_exact := by
    intro i
    exact
      ((compressedFIDFixedWeightInterpretedConstantQueryProfile
        bits).2.2.1 i).2
  rank_exact := by
    intro target pos
    exact
      ((compressedFIDFixedWeightInterpretedConstantQueryProfile
        bits).2.2.2.1 target pos).2
  select_exact := by
    intro target occurrence
    exact
      ((compressedFIDFixedWeightInterpretedConstantQueryProfile
        bits).2.2.2.2 target occurrence).2

/-- Concrete fixed-weight compressed/FID family with interpreted query replays. -/
def compressedFIDFixedWeightInterpretedFamily :
    CompressedFamily
      compressedFIDFixedWeightOverhead
      compressedFIDFixedWeightQueryCost where
  directory := compressedFIDFixedWeightInterpretedDirectory
  overhead_littleO := compressedFIDFixedWeightOverheadLittleO

/-- Family theorem for the interpreted compressed/FID rank/select replay. -/
theorem compressedFIDFixedWeightInterpretedFamilyProfile :
    SuccinctSpace.LittleOLinear compressedFIDFixedWeightOverhead /\
      forall bits : List Bool,
        ((compressedFIDFixedWeightInterpretedFamily.directory bits).payload.length <=
          fixedWeightPayloadBudget bits +
            compressedFIDFixedWeightOverhead bits.length) /\
          (forall i,
            ((compressedFIDFixedWeightInterpretedFamily.directory bits).accessQueryCosted
                i).cost <=
                compressedFIDFixedWeightQueryCost /\
              ((compressedFIDFixedWeightInterpretedFamily.directory bits).accessQueryCosted
                i).erase = bits[i]?) /\
          (forall target pos,
            ((compressedFIDFixedWeightInterpretedFamily.directory bits).rankQueryCosted
                target pos).cost <=
                compressedFIDFixedWeightQueryCost /\
              ((compressedFIDFixedWeightInterpretedFamily.directory bits).rankQueryCosted
                target pos).erase =
                Succinct.rankPrefix target bits pos) /\
          (forall target occurrence,
            ((compressedFIDFixedWeightInterpretedFamily.directory bits).selectQueryCosted
                target occurrence).cost <=
                compressedFIDFixedWeightQueryCost /\
              ((compressedFIDFixedWeightInterpretedFamily.directory bits).selectQueryCosted
                target occurrence).erase =
                Succinct.select target bits occurrence) := by
  exact
    RMQ.RankSelectSpec.CompressedBitVectorRankSelectFamily.fixed_weight_constant_query_profile
      compressedFIDFixedWeightInterpretedFamily

/--
Fused public capstone for the fixed-weight compressed/FID rank/select spoke.

This theorem packages the four public layers that are usually cited together:
the compressed `fixedWeightPayloadBudget bits + o(n)` family profile, the
interpreted `WordRAM` replay profile, the target-independent global payload
store for shared access plus rank/select false/true, and the bounded
trace-local event-width companion. It is still a model-level theorem: payload
bits, proof-only fields, WordRAM trace/cost events, and Lean runtime behavior
remain separate.
-/
theorem compressedFIDFixedWeightGlobalPayloadStoreFusedProfile :
    (SuccinctSpace.LittleOLinear compressedFIDFixedWeightOverhead /\
      forall bits : List Bool,
        ((compressedFIDFixedWeightFamily.directory bits).payload.length <=
          fixedWeightPayloadBudget bits +
            compressedFIDFixedWeightOverhead bits.length) /\
          (forall i,
            ((compressedFIDFixedWeightFamily.directory bits).accessQueryCosted
                i).cost <= compressedFIDFixedWeightQueryCost /\
              ((compressedFIDFixedWeightFamily.directory bits).accessQueryCosted
                i).erase = bits[i]?) /\
          (forall target pos,
            ((compressedFIDFixedWeightFamily.directory bits).rankQueryCosted
                target pos).cost <= compressedFIDFixedWeightQueryCost /\
              ((compressedFIDFixedWeightFamily.directory bits).rankQueryCosted
                target pos).erase =
                Succinct.rankPrefix target bits pos) /\
          (forall target occurrence,
            ((compressedFIDFixedWeightFamily.directory bits).selectQueryCosted
                target occurrence).cost <=
                compressedFIDFixedWeightQueryCost /\
              ((compressedFIDFixedWeightFamily.directory bits).selectQueryCosted
                target occurrence).erase =
                Succinct.select target bits occurrence)) /\
      (SuccinctSpace.LittleOLinear compressedFIDFixedWeightOverhead /\
        forall bits : List Bool,
          ((compressedFIDFixedWeightInterpretedFamily.directory bits).payload.length <=
            fixedWeightPayloadBudget bits +
              compressedFIDFixedWeightOverhead bits.length) /\
            (forall i,
              ((compressedFIDFixedWeightInterpretedFamily.directory bits).accessQueryCosted
                  i).cost <=
                  compressedFIDFixedWeightQueryCost /\
                ((compressedFIDFixedWeightInterpretedFamily.directory bits).accessQueryCosted
                  i).erase = bits[i]?) /\
            (forall target pos,
              ((compressedFIDFixedWeightInterpretedFamily.directory bits).rankQueryCosted
                  target pos).cost <=
                  compressedFIDFixedWeightQueryCost /\
                ((compressedFIDFixedWeightInterpretedFamily.directory bits).rankQueryCosted
                  target pos).erase =
                  Succinct.rankPrefix target bits pos) /\
            (forall target occurrence,
              ((compressedFIDFixedWeightInterpretedFamily.directory bits).selectQueryCosted
                  target occurrence).cost <=
                  compressedFIDFixedWeightQueryCost /\
                ((compressedFIDFixedWeightInterpretedFamily.directory bits).selectQueryCosted
                  target occurrence).erase =
                  Succinct.select target bits occurrence)) /\
        (forall bits : List Bool,
          (forall i,
            (compressedFIDFixedWeightGlobalPayloadStoreAccessTraceResult
              bits i).toCosted =
                compressedFIDFixedWeightAccessInterpretedCosted bits i /\
              (compressedFIDFixedWeightGlobalPayloadStoreAccessTraceResult
                bits i).toCosted =
                RMQ.RankSelectSpec.subLogAccessCosted bits i /\
              (forall event,
                event ∈
                    (compressedFIDFixedWeightGlobalPayloadStoreAccessTraceResult
                      bits i).trace ->
                  event.isReadWord \/ event.isWordPrimitive) /\
              (forall event,
                event ∈
                    (compressedFIDFixedWeightGlobalPayloadStoreAccessTraceResult
                      bits i).trace ->
                  event.matchesReadStore
                    (compressedFIDFixedWeightGlobalTraceReadStore bits))) /\
            (forall target pos,
              (compressedFIDFixedWeightGlobalPayloadStoreRankTraceResult
                bits target pos).toCosted =
                  compressedFIDFixedWeightRankInterpretedCosted
                    bits target pos /\
                (compressedFIDFixedWeightGlobalPayloadStoreRankTraceResult
                  bits target pos).toCosted =
                  RMQ.RankSelectSpec.subLogRankCosted bits target pos /\
                (forall event,
                  event ∈
                      (compressedFIDFixedWeightGlobalPayloadStoreRankTraceResult
                        bits target pos).trace ->
                    event.isReadWord \/ event.isWordPrimitive) /\
                (forall event,
                  event ∈
                      (compressedFIDFixedWeightGlobalPayloadStoreRankTraceResult
                        bits target pos).trace ->
                    event.matchesReadStore
                      (compressedFIDFixedWeightGlobalTraceReadStore bits))) /\
            forall target occurrence,
              (compressedFIDFixedWeightGlobalPayloadStoreSelectTraceResult
                bits target occurrence).toCosted =
                  compressedFIDFixedWeightSelectInterpretedCosted
                    bits target occurrence /\
                (compressedFIDFixedWeightGlobalPayloadStoreSelectTraceResult
                  bits target occurrence).toCosted =
                  RMQ.RankSelectSpec.subLogSelectFromPackedClarkRouteCosted
                    bits target occurrence /\
                (forall event,
                  event ∈
                      (compressedFIDFixedWeightGlobalPayloadStoreSelectTraceResult
                        bits target occurrence).trace ->
                    event.isReadWord \/ event.isWordPrimitive) /\
                (forall event,
                  event ∈
                      (compressedFIDFixedWeightGlobalPayloadStoreSelectTraceResult
                        bits target occurrence).trace ->
                    event.matchesReadStore
                      (compressedFIDFixedWeightGlobalTraceReadStore bits))) /\
          forall bits : List Bool,
            (forall i,
              (compressedFIDFixedWeightGlobalPayloadStoreAccessTraceResult
                bits i).toCosted =
                  compressedFIDFixedWeightAccessInterpretedCosted bits i /\
                (compressedFIDFixedWeightGlobalPayloadStoreAccessTraceResult
                  bits i).toCosted =
                  RMQ.RankSelectSpec.subLogAccessCosted bits i /\
                (forall event,
                  event ∈
                      (compressedFIDFixedWeightGlobalPayloadStoreAccessTraceResult
                        bits i).trace ->
                    event.isReadWord \/ event.isWordPrimitive) /\
                (forall event,
                  event ∈
                      (compressedFIDFixedWeightGlobalPayloadStoreAccessTraceResult
                        bits i).trace ->
                    event.matchesReadStore
                      (compressedFIDFixedWeightGlobalTraceReadStore bits)) /\
                (forall event,
                  event ∈
                      (compressedFIDFixedWeightGlobalPayloadStoreAccessTraceResult
                        bits i).trace ->
                    compressedFIDFixedWeightTraceEventReadAddressFitsInBits
                      (compressedFIDFixedWeightGlobalPayloadStoreAccessTraceEventBits
                        bits i) event) /\
                (forall event,
                  event ∈
                      (compressedFIDFixedWeightGlobalPayloadStoreAccessTraceResult
                        bits i).trace ->
                    compressedFIDFixedWeightTraceEventPrimitiveOperandsFitInBits
                      (compressedFIDFixedWeightGlobalPayloadStoreAccessTraceEventBits
                        bits i) event)) /\
              (forall target pos,
                (compressedFIDFixedWeightGlobalPayloadStoreRankTraceResult
                  bits target pos).toCosted =
                    compressedFIDFixedWeightRankInterpretedCosted
                      bits target pos /\
                  (compressedFIDFixedWeightGlobalPayloadStoreRankTraceResult
                    bits target pos).toCosted =
                    RMQ.RankSelectSpec.subLogRankCosted bits target pos /\
                  (forall event,
                    event ∈
                        (compressedFIDFixedWeightGlobalPayloadStoreRankTraceResult
                          bits target pos).trace ->
                      event.isReadWord \/ event.isWordPrimitive) /\
                  (forall event,
                    event ∈
                        (compressedFIDFixedWeightGlobalPayloadStoreRankTraceResult
                          bits target pos).trace ->
                      event.matchesReadStore
                        (compressedFIDFixedWeightGlobalTraceReadStore bits)) /\
                  (forall event,
                    event ∈
                        (compressedFIDFixedWeightGlobalPayloadStoreRankTraceResult
                          bits target pos).trace ->
                      compressedFIDFixedWeightTraceEventReadAddressFitsInBits
                        (compressedFIDFixedWeightGlobalPayloadStoreRankTraceEventBits
                          bits target pos) event) /\
                  (forall event,
                    event ∈
                        (compressedFIDFixedWeightGlobalPayloadStoreRankTraceResult
                          bits target pos).trace ->
                      compressedFIDFixedWeightTraceEventPrimitiveOperandsFitInBits
                        (compressedFIDFixedWeightGlobalPayloadStoreRankTraceEventBits
                          bits target pos) event)) /\
              forall target occurrence,
                (compressedFIDFixedWeightGlobalPayloadStoreSelectTraceResult
                  bits target occurrence).toCosted =
                    compressedFIDFixedWeightSelectInterpretedCosted
                      bits target occurrence /\
                  (compressedFIDFixedWeightGlobalPayloadStoreSelectTraceResult
                    bits target occurrence).toCosted =
                    RMQ.RankSelectSpec.subLogSelectFromPackedClarkRouteCosted
                      bits target occurrence /\
                  (forall event,
                    event ∈
                        (compressedFIDFixedWeightGlobalPayloadStoreSelectTraceResult
                          bits target occurrence).trace ->
                      event.isReadWord \/ event.isWordPrimitive) /\
                  (forall event,
                    event ∈
                        (compressedFIDFixedWeightGlobalPayloadStoreSelectTraceResult
                          bits target occurrence).trace ->
                      event.matchesReadStore
                        (compressedFIDFixedWeightGlobalTraceReadStore bits)) /\
                  (forall event,
                    event ∈
                        (compressedFIDFixedWeightGlobalPayloadStoreSelectTraceResult
                          bits target occurrence).trace ->
                      compressedFIDFixedWeightTraceEventReadAddressFitsInBits
                        (compressedFIDFixedWeightGlobalPayloadStoreSelectTraceEventBits
                          bits target occurrence) event) /\
                  (forall event,
                    event ∈
                        (compressedFIDFixedWeightGlobalPayloadStoreSelectTraceResult
                          bits target occurrence).trace ->
                      compressedFIDFixedWeightTraceEventPrimitiveOperandsFitInBits
                        (compressedFIDFixedWeightGlobalPayloadStoreSelectTraceEventBits
                          bits target occurrence) event) := by
  exact
    ⟨compressedFIDFixedWeightFamilyProfile,
      compressedFIDFixedWeightInterpretedFamilyProfile,
      compressedFIDFixedWeightGlobalPayloadStore_execution_story,
      compressedFIDFixedWeightGlobalPayloadStore_bounded_execution_story⟩

end RankSelect

end RMQ
