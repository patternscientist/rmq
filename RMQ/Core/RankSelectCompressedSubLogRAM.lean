import RMQ.Core.RankSelectCompressedSubLogPackedClark
import RMQ.Core.GenericSelect.RAM
import RMQ.Core.WordRAM.Register

/-!
# Word-RAM replay for the sub-log compressed/FID rank/select path

The existing compressed/FID capstone already charges reads through concrete
payload stores.  This module adds an additive replay layer: every code,
length/class, rank-base, decoder, and packed-Clark local read is routed through
the current first-order `WordRAM` read bridges, then proved equal to the
existing `Costed` query.
-/

namespace RMQ

namespace SuccinctSpace

/-- Interpreted two-level read over two bounded payload-word stores. -/
def twoLevelReadInterpretedCosted2 {ps : List Bool} {ws : Nat}
    (superStore : BoundedPayloadWordStore ps ws)
    {pb : List Bool} {wb : Nat} (blockStore : BoundedPayloadWordStore pb wb)
    (superIdx blockIdx : Nat) : Costed Nat :=
  Costed.bind
      ((superStore.store.readProgram superIdx).eval
        superStore.wordRAMStore).toCosted fun base? =>
    Costed.bind
      ((blockStore.store.readProgram blockIdx).eval
        blockStore.wordRAMStore).toCosted fun rel? =>
      Costed.pure
        (bitsToNatLE (base?.getD []) + bitsToNatLE (rel?.getD []))

theorem twoLevelReadInterpretedCosted2_refines_twoLevelReadCosted2
    {ps : List Bool} {ws : Nat}
    (superStore : BoundedPayloadWordStore ps ws)
    {pb : List Bool} {wb : Nat}
    (blockStore : BoundedPayloadWordStore pb wb)
    (superIdx blockIdx : Nat) :
    twoLevelReadInterpretedCosted2 superStore blockStore superIdx blockIdx =
      twoLevelReadCosted2 superStore blockStore superIdx blockIdx := by
  unfold twoLevelReadInterpretedCosted2 twoLevelReadCosted2
  unfold BoundedPayloadWordStore.wordRAMStore
  rw [PayloadWordStore.readProgram_refines_readWordCosted
      superStore.store superIdx,
    PayloadWordStore.readProgram_refines_readWordCosted
      blockStore.store blockIdx]
  rfl

end SuccinctSpace

namespace RankSelectSpec

open GenericSelect

/-- Interpreted read from a bounded payload-word store. -/
def boundedWordReadInterpretedCosted
    {payload : List Bool} {wordSize : Nat}
    (store : SuccinctSpace.BoundedPayloadWordStore payload wordSize)
    (i : Nat) : Costed (Option (List Bool)) :=
  ((store.store.readProgram i).eval store.wordRAMStore).toCosted

theorem boundedWordReadInterpretedCosted_refines_readWordCosted
    {payload : List Bool} {wordSize : Nat}
    (store : SuccinctSpace.BoundedPayloadWordStore payload wordSize)
    (i : Nat) :
    boundedWordReadInterpretedCosted store i =
      store.store.readWordCosted i := by
  exact SuccinctSpace.PayloadWordStore.readProgram_refines_readWordCosted
    store.store i

/-- Interpreted shared-decoder read for the sub-log fixed-weight decoder. -/
def subLogDecodeReadInterpretedCosted (bits : List Bool) (slot : Nat) :
    Costed (Option (List Bool)) :=
  boundedWordReadInterpretedCosted
    (fixedWeightSubLogSharedDecoderStore bits) slot

theorem subLogDecodeReadInterpretedCosted_refines_subLogDecodeReadCosted
    (bits : List Bool) (slot : Nat) :
    subLogDecodeReadInterpretedCosted bits slot =
      subLogDecodeReadCosted bits slot := by
  unfold subLogDecodeReadInterpretedCosted subLogDecodeReadCosted
  exact boundedWordReadInterpretedCosted_refines_readWordCosted
    (fixedWeightSubLogSharedDecoderStore bits) slot

/-- Interpreted access query for the sub-log compressed/FID local decoder. -/
def subLogAccessInterpretedCosted (bits : List Bool) (i : Nat) :
    Costed (Option Bool) :=
  Costed.bind
      (boundedWordReadInterpretedCosted
        (subLogCodeStore bits) (subLogChunkAccessRoute bits i).blockIndex)
      fun code? =>
  Costed.bind
      (boundedWordReadInterpretedCosted
        (subLogLenStore bits) (subLogChunkAccessRoute bits i).blockIndex)
      fun len? =>
  Costed.bind
      (boundedWordReadInterpretedCosted
        (subLogClassStore bits) (subLogChunkAccessRoute bits i).blockIndex)
      fun class? =>
  Costed.bind
      (subLogDecodeReadInterpretedCosted bits
        (fixedWeightSharedDecodeSlotFromReadValues [len?, class?] [code?]))
      fun decoded? =>
    Costed.pure ((decoded?.getD [])[(subLogChunkAccessRoute bits i).offset]?)

theorem subLogAccessInterpretedCosted_refines_subLogAccessCosted
    (bits : List Bool) (i : Nat) :
    subLogAccessInterpretedCosted bits i = subLogAccessCosted bits i := by
  unfold subLogAccessInterpretedCosted subLogAccessCosted
  simp [boundedWordReadInterpretedCosted_refines_readWordCosted,
    subLogDecodeReadInterpretedCosted_refines_subLogDecodeReadCosted]

theorem subLogAccessInterpretedCosted_cost
    (bits : List Bool) (i : Nat) :
    (subLogAccessInterpretedCosted bits i).cost = 4 := by
  rw [subLogAccessInterpretedCosted_refines_subLogAccessCosted,
    subLogAccessCosted_cost]

theorem subLogAccessInterpretedCosted_erase
    (bits : List Bool) (i : Nat) :
    (subLogAccessInterpretedCosted bits i).erase = bits[i]? := by
  rw [subLogAccessInterpretedCosted_refines_subLogAccessCosted]
  exact subLogAccessCosted_erase bits i

/-! ### Trace-result access replay -/

/--
Trace-preserving read from a bounded payload-word store, embedded in a caller
chosen global segment.
-/
def boundedWordReadTraceResultAtSegment
    {payload : List Bool} {wordSize : Nat}
    (segment deadSegment : Nat)
    (store : SuccinctSpace.BoundedPayloadWordStore payload wordSize)
    (i : Nat) : WordRAM.TraceResult (Option (List Bool)) :=
  WordRAM.TraceResult.relabelReadSegmentsWith
    (WordRAM.singletonSegmentMap segment deadSegment)
    (WordRAM.TraceResult.ofResult
      ((store.store.readProgram i).eval store.wordRAMStore))

theorem boundedWordReadTraceResultAtSegment_refines_interpretedCosted
    {payload : List Bool} {wordSize : Nat}
    (segment deadSegment : Nat)
    (store : SuccinctSpace.BoundedPayloadWordStore payload wordSize)
    (i : Nat) :
    (boundedWordReadTraceResultAtSegment segment deadSegment store i).toCosted =
      boundedWordReadInterpretedCosted store i := by
  unfold boundedWordReadTraceResultAtSegment boundedWordReadInterpretedCosted
  rw [WordRAM.TraceResult.relabelReadSegmentsWith_toCosted]
  exact WordRAM.TraceResult.ofResult_toCosted
    ((store.store.readProgram i).eval store.wordRAMStore)

theorem boundedWordReadTraceResultAtSegment_matchesReadStore
    {payload : List Bool} {wordSize : Nat}
    (segment deadSegment : Nat)
    (store : SuccinctSpace.BoundedPayloadWordStore payload wordSize)
    (globalStore : WordRAM.ReadStore)
    (hread :
      forall localSegment index,
        globalStore.readWord?
            (WordRAM.singletonSegmentMap
              segment deadSegment localSegment) index =
          (WordRAM.ReadStore.ofStore store.wordRAMStore).readWord?
            localSegment index)
    (i : Nat) :
    forall event,
      event ∈
          (boundedWordReadTraceResultAtSegment
            segment deadSegment store i).trace ->
        event.matchesReadStore globalStore := by
  unfold boundedWordReadTraceResultAtSegment
  exact
    WordRAM.TraceResult.relabelReadSegmentsWith_matchesReadStore
      (WordRAM.TraceResult.ofResult
        ((store.store.readProgram i).eval store.wordRAMStore))
      (WordRAM.ReadStore.ofStore store.wordRAMStore) globalStore
      (WordRAM.singletonSegmentMap segment deadSegment) hread
      (by
        intro event hmem
        simpa [WordRAM.TraceEvent.matchesReadStore_ofStore] using
          WordRAM.Program.eval_reads_subset_readStore
            (store.store.readProgram i) store.wordRAMStore event hmem)

def subLogAccessCodeSegment : Nat := 0
def subLogAccessLengthSegment : Nat := 1
def subLogAccessClassSegment : Nat := 2
def subLogAccessDecoderSegment : Nat := 3
def subLogAccessDeadSegment : Nat := 4

/-- Four-segment read-only store for the sub-log access trace replay. -/
def subLogAccessTraceReadStore (bits : List Bool) :
    WordRAM.ReadStore where
  readWord? segment index :=
    match segment with
    | 0 => (subLogCodeStore bits).wordRAMStore.readWord? 0 index
    | 1 => (subLogLenStore bits).wordRAMStore.readWord? 0 index
    | 2 => (subLogClassStore bits).wordRAMStore.readWord? 0 index
    | 3 =>
        (fixedWeightSubLogSharedDecoderStore bits).wordRAMStore.readWord?
          0 index
    | _ + 4 => none

private theorem subLogAccessTraceReadStore_code_read
    (bits : List Bool) :
    forall localSegment index,
      (subLogAccessTraceReadStore bits).readWord?
          (WordRAM.singletonSegmentMap
            subLogAccessCodeSegment subLogAccessDeadSegment localSegment)
          index =
        (WordRAM.ReadStore.ofStore
          (subLogCodeStore bits).wordRAMStore).readWord?
          localSegment index := by
  intro localSegment index
  cases localSegment <;>
    simp [subLogAccessTraceReadStore, subLogAccessCodeSegment,
      subLogAccessDeadSegment, WordRAM.singletonSegmentMap,
      WordRAM.TraceEvent.singletonSegmentMap, WordRAM.ReadStore.ofStore,
      SuccinctSpace.BoundedPayloadWordStore.wordRAMStore,
      SuccinctSpace.PayloadWordStore.wordRAMStore,
      WordRAM.Store.readWord?]

private theorem subLogAccessTraceReadStore_len_read
    (bits : List Bool) :
    forall localSegment index,
      (subLogAccessTraceReadStore bits).readWord?
          (WordRAM.singletonSegmentMap
            subLogAccessLengthSegment subLogAccessDeadSegment localSegment)
          index =
        (WordRAM.ReadStore.ofStore
          (subLogLenStore bits).wordRAMStore).readWord?
          localSegment index := by
  intro localSegment index
  cases localSegment <;>
    simp [subLogAccessTraceReadStore, subLogAccessLengthSegment,
      subLogAccessDeadSegment, WordRAM.singletonSegmentMap,
      WordRAM.TraceEvent.singletonSegmentMap, WordRAM.ReadStore.ofStore,
      SuccinctSpace.BoundedPayloadWordStore.wordRAMStore,
      SuccinctSpace.PayloadWordStore.wordRAMStore,
      WordRAM.Store.readWord?]

private theorem subLogAccessTraceReadStore_class_read
    (bits : List Bool) :
    forall localSegment index,
      (subLogAccessTraceReadStore bits).readWord?
          (WordRAM.singletonSegmentMap
            subLogAccessClassSegment subLogAccessDeadSegment localSegment)
          index =
        (WordRAM.ReadStore.ofStore
          (subLogClassStore bits).wordRAMStore).readWord?
          localSegment index := by
  intro localSegment index
  cases localSegment <;>
    simp [subLogAccessTraceReadStore, subLogAccessClassSegment,
      subLogAccessDeadSegment, WordRAM.singletonSegmentMap,
      WordRAM.TraceEvent.singletonSegmentMap, WordRAM.ReadStore.ofStore,
      SuccinctSpace.BoundedPayloadWordStore.wordRAMStore,
      SuccinctSpace.PayloadWordStore.wordRAMStore,
      WordRAM.Store.readWord?]

private theorem subLogAccessTraceReadStore_decoder_read
    (bits : List Bool) :
    forall localSegment index,
      (subLogAccessTraceReadStore bits).readWord?
          (WordRAM.singletonSegmentMap
            subLogAccessDecoderSegment subLogAccessDeadSegment localSegment)
          index =
        (WordRAM.ReadStore.ofStore
          (fixedWeightSubLogSharedDecoderStore bits).wordRAMStore).readWord?
          localSegment index := by
  intro localSegment index
  cases localSegment <;>
    simp [subLogAccessTraceReadStore, subLogAccessDecoderSegment,
      subLogAccessDeadSegment, WordRAM.singletonSegmentMap,
      WordRAM.TraceEvent.singletonSegmentMap, WordRAM.ReadStore.ofStore,
      SuccinctSpace.BoundedPayloadWordStore.wordRAMStore,
      SuccinctSpace.PayloadWordStore.wordRAMStore,
      WordRAM.Store.readWord?]

/-- Trace-result version of the concrete sub-log compressed/FID access query. -/
def subLogAccessTraceResult (bits : List Bool) (i : Nat) :
    WordRAM.TraceResult (Option Bool) :=
  WordRAM.TraceResult.bind
      (boundedWordReadTraceResultAtSegment
        subLogAccessCodeSegment subLogAccessDeadSegment
        (subLogCodeStore bits) (subLogChunkAccessRoute bits i).blockIndex)
      fun code? =>
  WordRAM.TraceResult.bind
      (boundedWordReadTraceResultAtSegment
        subLogAccessLengthSegment subLogAccessDeadSegment
        (subLogLenStore bits) (subLogChunkAccessRoute bits i).blockIndex)
      fun len? =>
  WordRAM.TraceResult.bind
      (boundedWordReadTraceResultAtSegment
        subLogAccessClassSegment subLogAccessDeadSegment
        (subLogClassStore bits) (subLogChunkAccessRoute bits i).blockIndex)
      fun class? =>
  WordRAM.TraceResult.bind
      (boundedWordReadTraceResultAtSegment
        subLogAccessDecoderSegment subLogAccessDeadSegment
        (fixedWeightSubLogSharedDecoderStore bits)
        (fixedWeightSharedDecodeSlotFromReadValues [len?, class?] [code?]))
      fun decoded? =>
    WordRAM.TraceResult.pure
      ((decoded?.getD [])[(subLogChunkAccessRoute bits i).offset]?)

theorem subLogAccessTraceResult_refines_interpretedCosted
    (bits : List Bool) (i : Nat) :
    (subLogAccessTraceResult bits i).toCosted =
      subLogAccessInterpretedCosted bits i := by
  simp [subLogAccessTraceResult, subLogAccessInterpretedCosted,
    boundedWordReadTraceResultAtSegment_refines_interpretedCosted,
    subLogDecodeReadInterpretedCosted,
    WordRAM.TraceResult.bind_toCosted,
    WordRAM.TraceResult.pure_toCosted]

theorem subLogAccessTraceResult_matchesReadStore
    (bits : List Bool) (i : Nat) :
    forall event,
      event ∈ (subLogAccessTraceResult bits i).trace ->
        event.matchesReadStore (subLogAccessTraceReadStore bits) := by
  unfold subLogAccessTraceResult
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      boundedWordReadTraceResultAtSegment_matchesReadStore
        subLogAccessCodeSegment subLogAccessDeadSegment
        (subLogCodeStore bits) (subLogAccessTraceReadStore bits)
        (subLogAccessTraceReadStore_code_read bits)
        (subLogChunkAccessRoute bits i).blockIndex
  · apply WordRAM.TraceResult.bind_trace_forall
    · exact
        boundedWordReadTraceResultAtSegment_matchesReadStore
          subLogAccessLengthSegment subLogAccessDeadSegment
          (subLogLenStore bits) (subLogAccessTraceReadStore bits)
          (subLogAccessTraceReadStore_len_read bits)
          (subLogChunkAccessRoute bits i).blockIndex
    · apply WordRAM.TraceResult.bind_trace_forall
      · exact
          boundedWordReadTraceResultAtSegment_matchesReadStore
            subLogAccessClassSegment subLogAccessDeadSegment
            (subLogClassStore bits) (subLogAccessTraceReadStore bits)
            (subLogAccessTraceReadStore_class_read bits)
            (subLogChunkAccessRoute bits i).blockIndex
      · apply WordRAM.TraceResult.bind_trace_forall
        · exact
            boundedWordReadTraceResultAtSegment_matchesReadStore
              subLogAccessDecoderSegment subLogAccessDeadSegment
              (fixedWeightSubLogSharedDecoderStore bits)
              (subLogAccessTraceReadStore bits)
              (subLogAccessTraceReadStore_decoder_read bits)
              (fixedWeightSharedDecodeSlotFromReadValues
                [_, _] [_])
        · exact WordRAM.TraceResult.pure_trace_forall
            (fun event =>
              event.matchesReadStore (subLogAccessTraceReadStore bits)) _

theorem subLogAccessTraceResult_event_read_or_primitive
    (bits : List Bool) (i : Nat) :
    forall event,
      event ∈ (subLogAccessTraceResult bits i).trace ->
        event.isReadWord \/ event.isWordPrimitive := by
  intro event _hmem
  exact WordRAM.TraceEvent.isReadWord_or_isWordPrimitive event

/--
Execution-story packet for the access leg of the compressed/FID sub-log path.

It is the first standalone rank/select analogue of the RMQ global execution
story: the trace result projects to the interpreted query, refines the existing
costed access query, contains only Word-RAM read/word-primitive events, and
all reads agree with the concrete four-segment access payload store.
-/
theorem subLogAccessTraceResult_execution_story
    (bits : List Bool) (i : Nat) :
    (subLogAccessTraceResult bits i).toCosted =
        subLogAccessInterpretedCosted bits i /\
      (subLogAccessTraceResult bits i).toCosted =
        subLogAccessCosted bits i /\
      (forall event,
        event ∈ (subLogAccessTraceResult bits i).trace ->
          event.isReadWord \/ event.isWordPrimitive) /\
      (forall event,
        event ∈ (subLogAccessTraceResult bits i).trace ->
          event.matchesReadStore (subLogAccessTraceReadStore bits)) := by
  constructor
  · exact subLogAccessTraceResult_refines_interpretedCosted bits i
  constructor
  · rw [subLogAccessTraceResult_refines_interpretedCosted,
      subLogAccessInterpretedCosted_refines_subLogAccessCosted]
  constructor
  · exact subLogAccessTraceResult_event_read_or_primitive bits i
  · exact subLogAccessTraceResult_matchesReadStore bits i

/-- Interpreted two-level rank-base read for sub-log rank. -/
def subLogRankBaseInterpretedCosted
    (bits : List Bool) (target : Bool) (blockIndex : Nat) : Costed Nat :=
  SuccinctSpace.twoLevelReadInterpretedCosted2
    (subLogRankSuperStore bits target)
    (subLogRankRelativeStore bits target)
    (blockIndex / subLogRankSuperblockSpan bits)
    blockIndex

theorem subLogRankBaseInterpretedCosted_refines_subLogRankBaseCosted
    (bits : List Bool) (target : Bool) (blockIndex : Nat) :
    subLogRankBaseInterpretedCosted bits target blockIndex =
      subLogRankBaseCosted bits target blockIndex := by
  unfold subLogRankBaseInterpretedCosted subLogRankBaseCosted
  exact
    SuccinctSpace.twoLevelReadInterpretedCosted2_refines_twoLevelReadCosted2
      (subLogRankSuperStore bits target)
      (subLogRankRelativeStore bits target)
      (blockIndex / subLogRankSuperblockSpan bits)
      blockIndex

/-- Interpreted rank query for the concrete sub-log rank route. -/
def subLogRankInterpretedCosted
    (bits : List Bool) (target : Bool) (pos : Nat) : Costed Nat :=
  let blockIndex := subLogRankBlockIndex bits pos
  Costed.bind
    (subLogRankBaseInterpretedCosted bits target blockIndex) fun base =>
  Costed.bind
      (boundedWordReadInterpretedCosted
        (subLogCodeStore bits) blockIndex) fun code? =>
  Costed.bind
      (boundedWordReadInterpretedCosted
        (subLogLenStore bits) blockIndex) fun len? =>
  Costed.bind
      (boundedWordReadInterpretedCosted
        (subLogClassStore bits) blockIndex) fun class? =>
  Costed.bind
      (subLogDecodeReadInterpretedCosted bits
        (fixedWeightSharedDecodeSlotFromReadValues [len?, class?] [code?]))
      fun decoded? =>
    Costed.pure
      (base +
        Succinct.rankPrefix target (decoded?.getD [])
          (subLogRankLocalLimit bits pos))

theorem subLogRankInterpretedCosted_refines_subLogRankCosted
    (bits : List Bool) (target : Bool) (pos : Nat) :
    subLogRankInterpretedCosted bits target pos =
      subLogRankCosted bits target pos := by
  unfold subLogRankInterpretedCosted subLogRankCosted
  simp [subLogRankBaseInterpretedCosted_refines_subLogRankBaseCosted,
    boundedWordReadInterpretedCosted_refines_readWordCosted,
    subLogDecodeReadInterpretedCosted_refines_subLogDecodeReadCosted]

theorem subLogRankInterpretedCosted_cost
    (bits : List Bool) (target : Bool) (pos : Nat) :
    (subLogRankInterpretedCosted bits target pos).cost = 6 := by
  rw [subLogRankInterpretedCosted_refines_subLogRankCosted,
    subLogRankCosted_cost]

theorem subLogRankInterpretedCosted_erase
    (bits : List Bool) (target : Bool) (pos : Nat) :
    (subLogRankInterpretedCosted bits target pos).erase =
      Succinct.rankPrefix target bits pos := by
  rw [subLogRankInterpretedCosted_refines_subLogRankCosted]
  exact subLogRankCosted_erase bits target pos

/-! ### Trace-result rank replay -/

def subLogRankSuperSegment : Nat := 0
def subLogRankRelativeSegment : Nat := 1
def subLogRankCodeSegment : Nat := 2
def subLogRankLengthSegment : Nat := 3
def subLogRankClassSegment : Nat := 4
def subLogRankDecoderSegment : Nat := 5
def subLogRankDeadSegment : Nat := 6

/-- Six-segment read-only store for the sub-log rank trace replay. -/
def subLogRankTraceReadStore
    (bits : List Bool) (target : Bool) : WordRAM.ReadStore where
  readWord? segment index :=
    match segment with
    | 0 => (subLogRankSuperStore bits target).wordRAMStore.readWord? 0 index
    | 1 => (subLogRankRelativeStore bits target).wordRAMStore.readWord? 0 index
    | 2 => (subLogCodeStore bits).wordRAMStore.readWord? 0 index
    | 3 => (subLogLenStore bits).wordRAMStore.readWord? 0 index
    | 4 => (subLogClassStore bits).wordRAMStore.readWord? 0 index
    | 5 =>
        (fixedWeightSubLogSharedDecoderStore bits).wordRAMStore.readWord?
          0 index
    | _ + 6 => none

private theorem subLogRankTraceReadStore_super_read
    (bits : List Bool) (target : Bool) :
    forall localSegment index,
      (subLogRankTraceReadStore bits target).readWord?
          (WordRAM.singletonSegmentMap
            subLogRankSuperSegment subLogRankDeadSegment localSegment)
          index =
        (WordRAM.ReadStore.ofStore
          (subLogRankSuperStore bits target).wordRAMStore).readWord?
          localSegment index := by
  intro localSegment index
  cases localSegment <;>
    simp [subLogRankTraceReadStore, subLogRankSuperSegment,
      subLogRankDeadSegment, WordRAM.singletonSegmentMap,
      WordRAM.TraceEvent.singletonSegmentMap, WordRAM.ReadStore.ofStore,
      SuccinctSpace.BoundedPayloadWordStore.wordRAMStore,
      SuccinctSpace.PayloadWordStore.wordRAMStore,
      WordRAM.Store.readWord?]

private theorem subLogRankTraceReadStore_relative_read
    (bits : List Bool) (target : Bool) :
    forall localSegment index,
      (subLogRankTraceReadStore bits target).readWord?
          (WordRAM.singletonSegmentMap
            subLogRankRelativeSegment subLogRankDeadSegment localSegment)
          index =
        (WordRAM.ReadStore.ofStore
          (subLogRankRelativeStore bits target).wordRAMStore).readWord?
          localSegment index := by
  intro localSegment index
  cases localSegment <;>
    simp [subLogRankTraceReadStore, subLogRankRelativeSegment,
      subLogRankDeadSegment, WordRAM.singletonSegmentMap,
      WordRAM.TraceEvent.singletonSegmentMap, WordRAM.ReadStore.ofStore,
      SuccinctSpace.BoundedPayloadWordStore.wordRAMStore,
      SuccinctSpace.PayloadWordStore.wordRAMStore,
      WordRAM.Store.readWord?]

private theorem subLogRankTraceReadStore_code_read
    (bits : List Bool) (target : Bool) :
    forall localSegment index,
      (subLogRankTraceReadStore bits target).readWord?
          (WordRAM.singletonSegmentMap
            subLogRankCodeSegment subLogRankDeadSegment localSegment)
          index =
        (WordRAM.ReadStore.ofStore
          (subLogCodeStore bits).wordRAMStore).readWord?
          localSegment index := by
  intro localSegment index
  cases localSegment <;>
    simp [subLogRankTraceReadStore, subLogRankCodeSegment,
      subLogRankDeadSegment, WordRAM.singletonSegmentMap,
      WordRAM.TraceEvent.singletonSegmentMap, WordRAM.ReadStore.ofStore,
      SuccinctSpace.BoundedPayloadWordStore.wordRAMStore,
      SuccinctSpace.PayloadWordStore.wordRAMStore,
      WordRAM.Store.readWord?]

private theorem subLogRankTraceReadStore_len_read
    (bits : List Bool) (target : Bool) :
    forall localSegment index,
      (subLogRankTraceReadStore bits target).readWord?
          (WordRAM.singletonSegmentMap
            subLogRankLengthSegment subLogRankDeadSegment localSegment)
          index =
        (WordRAM.ReadStore.ofStore
          (subLogLenStore bits).wordRAMStore).readWord?
          localSegment index := by
  intro localSegment index
  cases localSegment <;>
    simp [subLogRankTraceReadStore, subLogRankLengthSegment,
      subLogRankDeadSegment, WordRAM.singletonSegmentMap,
      WordRAM.TraceEvent.singletonSegmentMap, WordRAM.ReadStore.ofStore,
      SuccinctSpace.BoundedPayloadWordStore.wordRAMStore,
      SuccinctSpace.PayloadWordStore.wordRAMStore,
      WordRAM.Store.readWord?]

private theorem subLogRankTraceReadStore_class_read
    (bits : List Bool) (target : Bool) :
    forall localSegment index,
      (subLogRankTraceReadStore bits target).readWord?
          (WordRAM.singletonSegmentMap
            subLogRankClassSegment subLogRankDeadSegment localSegment)
          index =
        (WordRAM.ReadStore.ofStore
          (subLogClassStore bits).wordRAMStore).readWord?
          localSegment index := by
  intro localSegment index
  cases localSegment <;>
    simp [subLogRankTraceReadStore, subLogRankClassSegment,
      subLogRankDeadSegment, WordRAM.singletonSegmentMap,
      WordRAM.TraceEvent.singletonSegmentMap, WordRAM.ReadStore.ofStore,
      SuccinctSpace.BoundedPayloadWordStore.wordRAMStore,
      SuccinctSpace.PayloadWordStore.wordRAMStore,
      WordRAM.Store.readWord?]

private theorem subLogRankTraceReadStore_decoder_read
    (bits : List Bool) (target : Bool) :
    forall localSegment index,
      (subLogRankTraceReadStore bits target).readWord?
          (WordRAM.singletonSegmentMap
            subLogRankDecoderSegment subLogRankDeadSegment localSegment)
          index =
        (WordRAM.ReadStore.ofStore
          (fixedWeightSubLogSharedDecoderStore bits).wordRAMStore).readWord?
          localSegment index := by
  intro localSegment index
  cases localSegment <;>
    simp [subLogRankTraceReadStore, subLogRankDecoderSegment,
      subLogRankDeadSegment, WordRAM.singletonSegmentMap,
      WordRAM.TraceEvent.singletonSegmentMap, WordRAM.ReadStore.ofStore,
      SuccinctSpace.BoundedPayloadWordStore.wordRAMStore,
      SuccinctSpace.PayloadWordStore.wordRAMStore,
      WordRAM.Store.readWord?]

/-- Trace-result version of the sub-log rank two-level base read. -/
def subLogRankBaseTraceResult
    (bits : List Bool) (target : Bool) (blockIndex : Nat) :
    WordRAM.TraceResult Nat :=
  WordRAM.TraceResult.bind
      (boundedWordReadTraceResultAtSegment
        subLogRankSuperSegment subLogRankDeadSegment
        (subLogRankSuperStore bits target)
        (blockIndex / subLogRankSuperblockSpan bits))
      fun base? =>
  WordRAM.TraceResult.bind
      (boundedWordReadTraceResultAtSegment
        subLogRankRelativeSegment subLogRankDeadSegment
        (subLogRankRelativeStore bits target) blockIndex)
      fun rel? =>
    WordRAM.TraceResult.pure
      (SuccinctSpace.bitsToNatLE (base?.getD []) +
        SuccinctSpace.bitsToNatLE (rel?.getD []))

theorem subLogRankBaseTraceResult_refines_interpretedCosted
    (bits : List Bool) (target : Bool) (blockIndex : Nat) :
    (subLogRankBaseTraceResult bits target blockIndex).toCosted =
      subLogRankBaseInterpretedCosted bits target blockIndex := by
  apply Costed.ext <;>
    simp [subLogRankBaseTraceResult, subLogRankBaseInterpretedCosted,
    SuccinctSpace.twoLevelReadInterpretedCosted2,
    boundedWordReadTraceResultAtSegment_refines_interpretedCosted,
    boundedWordReadInterpretedCosted,
    Costed.bind, Costed.pure,
    WordRAM.TraceResult.bind_toCosted,
    WordRAM.TraceResult.pure_toCosted]

theorem subLogRankBaseTraceResult_matchesReadStore
    (bits : List Bool) (target : Bool) (blockIndex : Nat) :
    forall event,
      event ∈ (subLogRankBaseTraceResult bits target blockIndex).trace ->
        event.matchesReadStore (subLogRankTraceReadStore bits target) := by
  unfold subLogRankBaseTraceResult
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      boundedWordReadTraceResultAtSegment_matchesReadStore
        subLogRankSuperSegment subLogRankDeadSegment
        (subLogRankSuperStore bits target)
        (subLogRankTraceReadStore bits target)
        (subLogRankTraceReadStore_super_read bits target)
        (blockIndex / subLogRankSuperblockSpan bits)
  · apply WordRAM.TraceResult.bind_trace_forall
    · exact
        boundedWordReadTraceResultAtSegment_matchesReadStore
          subLogRankRelativeSegment subLogRankDeadSegment
          (subLogRankRelativeStore bits target)
          (subLogRankTraceReadStore bits target)
          (subLogRankTraceReadStore_relative_read bits target)
          blockIndex
    · exact WordRAM.TraceResult.pure_trace_forall
        (fun event =>
          event.matchesReadStore (subLogRankTraceReadStore bits target)) _

/-- Trace-result version of the concrete sub-log compressed/FID rank query. -/
def subLogRankTraceResult
    (bits : List Bool) (target : Bool) (pos : Nat) :
    WordRAM.TraceResult Nat :=
  let blockIndex := subLogRankBlockIndex bits pos
  WordRAM.TraceResult.bind
      (subLogRankBaseTraceResult bits target blockIndex)
      fun base =>
  WordRAM.TraceResult.bind
      (boundedWordReadTraceResultAtSegment
        subLogRankCodeSegment subLogRankDeadSegment
        (subLogCodeStore bits) blockIndex)
      fun code? =>
  WordRAM.TraceResult.bind
      (boundedWordReadTraceResultAtSegment
        subLogRankLengthSegment subLogRankDeadSegment
        (subLogLenStore bits) blockIndex)
      fun len? =>
  WordRAM.TraceResult.bind
      (boundedWordReadTraceResultAtSegment
        subLogRankClassSegment subLogRankDeadSegment
        (subLogClassStore bits) blockIndex)
      fun class? =>
  WordRAM.TraceResult.bind
      (boundedWordReadTraceResultAtSegment
        subLogRankDecoderSegment subLogRankDeadSegment
        (fixedWeightSubLogSharedDecoderStore bits)
        (fixedWeightSharedDecodeSlotFromReadValues [len?, class?] [code?]))
      fun decoded? =>
    WordRAM.TraceResult.pure
      (base +
        Succinct.rankPrefix target (decoded?.getD [])
          (subLogRankLocalLimit bits pos))

theorem subLogRankTraceResult_refines_interpretedCosted
    (bits : List Bool) (target : Bool) (pos : Nat) :
    (subLogRankTraceResult bits target pos).toCosted =
      subLogRankInterpretedCosted bits target pos := by
  simp [subLogRankTraceResult, subLogRankInterpretedCosted,
    subLogRankBaseTraceResult_refines_interpretedCosted,
    boundedWordReadTraceResultAtSegment_refines_interpretedCosted,
    subLogDecodeReadInterpretedCosted,
    WordRAM.TraceResult.bind_toCosted,
    WordRAM.TraceResult.pure_toCosted]

theorem subLogRankTraceResult_matchesReadStore
    (bits : List Bool) (target : Bool) (pos : Nat) :
    forall event,
      event ∈ (subLogRankTraceResult bits target pos).trace ->
        event.matchesReadStore (subLogRankTraceReadStore bits target) := by
  unfold subLogRankTraceResult
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      subLogRankBaseTraceResult_matchesReadStore bits target
        (subLogRankBlockIndex bits pos)
  · apply WordRAM.TraceResult.bind_trace_forall
    · exact
        boundedWordReadTraceResultAtSegment_matchesReadStore
          subLogRankCodeSegment subLogRankDeadSegment
          (subLogCodeStore bits)
          (subLogRankTraceReadStore bits target)
          (subLogRankTraceReadStore_code_read bits target)
          (subLogRankBlockIndex bits pos)
    · apply WordRAM.TraceResult.bind_trace_forall
      · exact
          boundedWordReadTraceResultAtSegment_matchesReadStore
            subLogRankLengthSegment subLogRankDeadSegment
            (subLogLenStore bits)
            (subLogRankTraceReadStore bits target)
            (subLogRankTraceReadStore_len_read bits target)
            (subLogRankBlockIndex bits pos)
      · apply WordRAM.TraceResult.bind_trace_forall
        · exact
            boundedWordReadTraceResultAtSegment_matchesReadStore
              subLogRankClassSegment subLogRankDeadSegment
              (subLogClassStore bits)
              (subLogRankTraceReadStore bits target)
              (subLogRankTraceReadStore_class_read bits target)
              (subLogRankBlockIndex bits pos)
        · apply WordRAM.TraceResult.bind_trace_forall
          · exact
              boundedWordReadTraceResultAtSegment_matchesReadStore
                subLogRankDecoderSegment subLogRankDeadSegment
                (fixedWeightSubLogSharedDecoderStore bits)
                (subLogRankTraceReadStore bits target)
                (subLogRankTraceReadStore_decoder_read bits target)
                (fixedWeightSharedDecodeSlotFromReadValues
                  [_, _] [_])
          · exact WordRAM.TraceResult.pure_trace_forall
              (fun event =>
                event.matchesReadStore
                  (subLogRankTraceReadStore bits target)) _

theorem subLogRankTraceResult_event_read_or_primitive
    (bits : List Bool) (target : Bool) (pos : Nat) :
    forall event,
      event ∈ (subLogRankTraceResult bits target pos).trace ->
        event.isReadWord \/ event.isWordPrimitive := by
  intro event _hmem
  exact WordRAM.TraceEvent.isReadWord_or_isWordPrimitive event

/--
Execution-story packet for the rank leg of the compressed/FID sub-log path.

The trace result projects to the interpreted rank query, refines the existing
costed rank query, contains only Word-RAM read/word-primitive events, and all
reads agree with the concrete six-segment rank payload store.
-/
theorem subLogRankTraceResult_execution_story
    (bits : List Bool) (target : Bool) (pos : Nat) :
    (subLogRankTraceResult bits target pos).toCosted =
        subLogRankInterpretedCosted bits target pos /\
      (subLogRankTraceResult bits target pos).toCosted =
        subLogRankCosted bits target pos /\
      (forall event,
        event ∈ (subLogRankTraceResult bits target pos).trace ->
          event.isReadWord \/ event.isWordPrimitive) /\
      (forall event,
        event ∈ (subLogRankTraceResult bits target pos).trace ->
          event.matchesReadStore (subLogRankTraceReadStore bits target)) := by
  constructor
  · exact subLogRankTraceResult_refines_interpretedCosted bits target pos
  constructor
  · rw [subLogRankTraceResult_refines_interpretedCosted,
      subLogRankInterpretedCosted_refines_subLogRankCosted]
  constructor
  · exact subLogRankTraceResult_event_read_or_primitive bits target pos
  · exact subLogRankTraceResult_matchesReadStore bits target pos

/-- Interpreted decode of one sub-log block by index. -/
def subLogDecodeBlockByIndexInterpretedCosted
    (bits : List Bool) (blockIndex : Nat) : Costed (List Bool) :=
  Costed.bind
      (boundedWordReadInterpretedCosted
        (subLogCodeStore bits) blockIndex) fun code? =>
  Costed.bind
      (boundedWordReadInterpretedCosted
        (subLogLenStore bits) blockIndex) fun len? =>
  Costed.bind
      (boundedWordReadInterpretedCosted
        (subLogClassStore bits) blockIndex) fun class? =>
  Costed.bind
      (subLogDecodeReadInterpretedCosted bits
        (fixedWeightSharedDecodeSlotFromReadValues [len?, class?] [code?]))
      fun decoded? =>
    Costed.pure (decoded?.getD [])

theorem subLogDecodeBlockByIndexInterpretedCosted_refines
    (bits : List Bool) (blockIndex : Nat) :
    subLogDecodeBlockByIndexInterpretedCosted bits blockIndex =
      subLogDecodeBlockByIndexCosted bits blockIndex := by
  unfold subLogDecodeBlockByIndexInterpretedCosted
    subLogDecodeBlockByIndexCosted
  simp [boundedWordReadInterpretedCosted_refines_readWordCosted,
    subLogDecodeReadInterpretedCosted_refines_subLogDecodeReadCosted]

/-- Interpreted decode of a constant-size sub-log block window. -/
def subLogDecodeBlockWindowInterpretedCosted
    (bits : List Bool) (startBlock count : Nat) :
    Costed (List (List Bool)) :=
  match count with
  | 0 => Costed.pure []
  | count' + 1 =>
      Costed.bind
          (subLogDecodeBlockByIndexInterpretedCosted bits startBlock)
          fun block =>
        Costed.map
          (fun rest => block :: rest)
          (subLogDecodeBlockWindowInterpretedCosted bits
            (startBlock + 1) count')

theorem subLogDecodeBlockWindowInterpretedCosted_refines
    (bits : List Bool) (startBlock count : Nat) :
    subLogDecodeBlockWindowInterpretedCosted bits startBlock count =
      subLogDecodeBlockWindowCosted bits startBlock count := by
  induction count generalizing startBlock with
  | zero =>
      rfl
  | succ count ih =>
      simp [subLogDecodeBlockWindowInterpretedCosted,
        subLogDecodeBlockWindowCosted,
        subLogDecodeBlockByIndexInterpretedCosted_refines, ih]

/-- Interpreted reconstruction of one machine word from sub-log blocks. -/
def subLogMachineWordReadInterpretedCosted
    (bits : List Bool) (wordIndex : Nat) : Costed (List Bool) :=
  let wordSize := SuccinctRank.machineWordBits bits.length
  let start := wordIndex * wordSize
  let startBlock := start / fixedWeightSubLogChunkBlockSize bits.length
  Costed.bind
    (subLogDecodeBlockWindowInterpretedCosted bits startBlock
      fixedWeightSubLogDenseWindowBlockCount)
    fun decodedWindow =>
      Costed.pure
        (subLogMachineWordFromDecodedWindow bits wordIndex decodedWindow)

theorem subLogMachineWordReadInterpretedCosted_refines
    (bits : List Bool) (wordIndex : Nat) :
    subLogMachineWordReadInterpretedCosted bits wordIndex =
      subLogMachineWordReadCosted bits wordIndex := by
  unfold subLogMachineWordReadInterpretedCosted
    subLogMachineWordReadCosted
  simp [subLogDecodeBlockWindowInterpretedCosted_refines]

/-- Interpreted dense two-word select branch over sub-log decoded windows. -/
def subLogDenseTwoWordSelectInterpretedCosted
    (target : Bool) (bits : List Bool)
    (basePosition baseOccurrence q : Nat) : Costed (Option Nat) :=
  let wordSize := SuccinctRank.machineWordBits bits.length
  let firstWordIndex := basePosition / wordSize
  let firstWordStart := firstWordIndex * wordSize
  let firstOffset := basePosition - firstWordStart
  let localOccurrence := q - baseOccurrence
  Costed.bind
      (subLogMachineWordReadInterpretedCosted bits firstWordIndex)
      fun firstWord =>
    Costed.bind
      (SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankInterpretedCosted
        target firstWord firstOffset)
      fun beforeFirst =>
        Costed.bind
          (SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankInterpretedCosted
            target firstWord firstWord.length)
          fun uptoFirst =>
            let firstCount := uptoFirst - beforeFirst
            if localOccurrence < firstCount then
              Costed.map
                (fun local? =>
                  local?.map fun offset => firstWordStart + offset)
                (GenericSelect.wordSelectInterpretedCosted target firstWord
                  (beforeFirst + localOccurrence))
            else
              Costed.bind
                (subLogMachineWordReadInterpretedCosted bits
                  (firstWordIndex + 1))
                fun secondWord =>
                  Costed.map
                    (fun local? =>
                      local?.map fun offset =>
                        (firstWordIndex + 1) * wordSize + offset)
                    (GenericSelect.wordSelectInterpretedCosted target
                      secondWord (localOccurrence - firstCount))

theorem subLogDenseTwoWordSelectInterpretedCosted_refines
    (target : Bool) (bits : List Bool)
    (basePosition baseOccurrence q : Nat) :
    subLogDenseTwoWordSelectInterpretedCosted
        target bits basePosition baseOccurrence q =
      subLogDenseTwoWordSelectCosted
        target bits basePosition baseOccurrence q := by
  unfold subLogDenseTwoWordSelectInterpretedCosted
    subLogDenseTwoWordSelectCosted
  simp [subLogMachineWordReadInterpretedCosted_refines,
    SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankInterpretedCosted_refines_rankBoolWordPrefix,
    GenericSelect.wordSelectInterpretedCosted_refines_selectBoolWord]

/-! ### Trace-result select replay -/

def subLogSelectSuperTableTraceSegments :
    GenericSelect.SparseDenseEntryTableTraceSegmentBases where
  baseOccurrence := 0
  baseWordIndex := 1
  rankBefore := 2
  firstOffset := 3
  deadSegment := 20

def subLogSelectLocalTableTraceSegments :
    GenericSelect.SparseDenseEntryTableTraceSegmentBases where
  baseOccurrence := 4
  baseWordIndex := 5
  rankBefore := 6
  firstOffset := 7
  deadSegment := 20

def subLogSelectLongFlagRankBase : Nat := 8
def subLogSelectLongRelativeSegment : Nat := 11

def subLogSelectSparseDirectoryTraceSegments :
    GenericSelect.SparseExceptionDirectoryTraceSegmentBases where
  rankBase := 12
  relativeBase := 15
  deadSegment := 20

def subLogSelectCodeSegment : Nat := 16
def subLogSelectLengthSegment : Nat := 17
def subLogSelectClassSegment : Nat := 18
def subLogSelectDecoderSegment : Nat := 19
def subLogSelectDeadSegment : Nat := 20

/--
Concrete read-only store for the compressed/FID select trace replay.

Segments 0-15 contain the sparse-exception Clark routing tables; segments
16-19 contain the sub-log block code/length/class/shared-decoder stores used
by both the dense two-word branch and the final local block select.
-/
def subLogSelectFromPackedClarkRouteTraceReadStore
    (bits : List Bool) (target : Bool) : WordRAM.ReadStore where
  readWord? segment index :=
    let data := GenericSelect.sparseExceptionSelectData bits target
    match segment with
    | 0 => data.superTable.baseOccurrenceTable.wordRAMStore.readWord? 0 index
    | 1 => data.superTable.baseWordIndexTable.wordRAMStore.readWord? 0 index
    | 2 => data.superTable.rankBeforeTable.wordRAMStore.readWord? 0 index
    | 3 => data.superTable.firstOffsetTable.wordRAMStore.readWord? 0 index
    | 4 => data.localTable.baseOccurrenceTable.wordRAMStore.readWord? 0 index
    | 5 => data.localTable.baseWordIndexTable.wordRAMStore.readWord? 0 index
    | 6 => data.localTable.rankBeforeTable.wordRAMStore.readWord? 0 index
    | 7 => data.localTable.firstOffsetTable.wordRAMStore.readWord? 0 index
    | 8 => (data.longFlagRankData.rankRegisterWordRAMStore true).readWord? 0 index
    | 9 => (data.longFlagRankData.rankRegisterWordRAMStore true).readWord? 1 index
    | 10 => (data.longFlagRankData.rankRegisterWordRAMStore true).readWord? 2 index
    | 11 => data.longSuperRelativeTable.wordRAMStore.readWord? 0 index
    | 12 => (data.sparseDirectory.rankData.rankRegisterWordRAMStore true).readWord? 0 index
    | 13 => (data.sparseDirectory.rankData.rankRegisterWordRAMStore true).readWord? 1 index
    | 14 => (data.sparseDirectory.rankData.rankRegisterWordRAMStore true).readWord? 2 index
    | 15 => data.sparseDirectory.relativeTable.wordRAMStore.readWord? 0 index
    | 16 => (subLogCodeStore bits).wordRAMStore.readWord? 0 index
    | 17 => (subLogLenStore bits).wordRAMStore.readWord? 0 index
    | 18 => (subLogClassStore bits).wordRAMStore.readWord? 0 index
    | 19 =>
        (fixedWeightSubLogSharedDecoderStore bits).wordRAMStore.readWord?
          0 index
    | _ + 20 => none

private theorem subLogSelectTraceReadStore_code_read
    (bits : List Bool) (target : Bool) :
    forall localSegment index,
      (subLogSelectFromPackedClarkRouteTraceReadStore bits target).readWord?
          (WordRAM.singletonSegmentMap
            subLogSelectCodeSegment subLogSelectDeadSegment localSegment)
          index =
        (WordRAM.ReadStore.ofStore
          (subLogCodeStore bits).wordRAMStore).readWord?
          localSegment index := by
  intro localSegment index
  cases localSegment <;>
    simp [subLogSelectFromPackedClarkRouteTraceReadStore,
      subLogSelectCodeSegment, subLogSelectDeadSegment,
      WordRAM.singletonSegmentMap, WordRAM.TraceEvent.singletonSegmentMap,
      WordRAM.ReadStore.ofStore,
      SuccinctSpace.BoundedPayloadWordStore.wordRAMStore,
      SuccinctSpace.PayloadWordStore.wordRAMStore,
      WordRAM.Store.readWord?]

private theorem subLogSelectTraceReadStore_len_read
    (bits : List Bool) (target : Bool) :
    forall localSegment index,
      (subLogSelectFromPackedClarkRouteTraceReadStore bits target).readWord?
          (WordRAM.singletonSegmentMap
            subLogSelectLengthSegment subLogSelectDeadSegment localSegment)
          index =
        (WordRAM.ReadStore.ofStore
          (subLogLenStore bits).wordRAMStore).readWord?
          localSegment index := by
  intro localSegment index
  cases localSegment <;>
    simp [subLogSelectFromPackedClarkRouteTraceReadStore,
      subLogSelectLengthSegment, subLogSelectDeadSegment,
      WordRAM.singletonSegmentMap, WordRAM.TraceEvent.singletonSegmentMap,
      WordRAM.ReadStore.ofStore,
      SuccinctSpace.BoundedPayloadWordStore.wordRAMStore,
      SuccinctSpace.PayloadWordStore.wordRAMStore,
      WordRAM.Store.readWord?]

private theorem subLogSelectTraceReadStore_class_read
    (bits : List Bool) (target : Bool) :
    forall localSegment index,
      (subLogSelectFromPackedClarkRouteTraceReadStore bits target).readWord?
          (WordRAM.singletonSegmentMap
            subLogSelectClassSegment subLogSelectDeadSegment localSegment)
          index =
        (WordRAM.ReadStore.ofStore
          (subLogClassStore bits).wordRAMStore).readWord?
          localSegment index := by
  intro localSegment index
  cases localSegment <;>
    simp [subLogSelectFromPackedClarkRouteTraceReadStore,
      subLogSelectClassSegment, subLogSelectDeadSegment,
      WordRAM.singletonSegmentMap, WordRAM.TraceEvent.singletonSegmentMap,
      WordRAM.ReadStore.ofStore,
      SuccinctSpace.BoundedPayloadWordStore.wordRAMStore,
      SuccinctSpace.PayloadWordStore.wordRAMStore,
      WordRAM.Store.readWord?]

private theorem subLogSelectTraceReadStore_decoder_read
    (bits : List Bool) (target : Bool) :
    forall localSegment index,
      (subLogSelectFromPackedClarkRouteTraceReadStore bits target).readWord?
          (WordRAM.singletonSegmentMap
            subLogSelectDecoderSegment subLogSelectDeadSegment localSegment)
          index =
        (WordRAM.ReadStore.ofStore
          (fixedWeightSubLogSharedDecoderStore bits).wordRAMStore).readWord?
          localSegment index := by
  intro localSegment index
  cases localSegment <;>
    simp [subLogSelectFromPackedClarkRouteTraceReadStore,
      subLogSelectDecoderSegment, subLogSelectDeadSegment,
      WordRAM.singletonSegmentMap, WordRAM.TraceEvent.singletonSegmentMap,
      WordRAM.ReadStore.ofStore,
      SuccinctSpace.BoundedPayloadWordStore.wordRAMStore,
      SuccinctSpace.PayloadWordStore.wordRAMStore,
      WordRAM.Store.readWord?]

private theorem subLogSelectTraceReadStore_super_baseOccurrence_read
    (bits : List Bool) (target : Bool) :
    forall localSegment index,
      (subLogSelectFromPackedClarkRouteTraceReadStore bits target).readWord?
          (WordRAM.singletonSegmentMap
            subLogSelectSuperTableTraceSegments.baseOccurrence
            subLogSelectSuperTableTraceSegments.deadSegment localSegment)
          index =
        let data := GenericSelect.sparseExceptionSelectData bits target
        data.superTable.baseOccurrenceTable.wordRAMStore.readWord?
          localSegment index := by
  intro localSegment index
  cases localSegment <;>
    simp [subLogSelectFromPackedClarkRouteTraceReadStore,
      subLogSelectSuperTableTraceSegments,
      WordRAM.singletonSegmentMap, WordRAM.TraceEvent.singletonSegmentMap,
      SuccinctSpace.FixedWidthNatTable.wordRAMStore,
      SuccinctSpace.PayloadWordStore.wordRAMStore,
      WordRAM.Store.readWord?]

private theorem subLogSelectTraceReadStore_super_baseWordIndex_read
    (bits : List Bool) (target : Bool) :
    forall localSegment index,
      (subLogSelectFromPackedClarkRouteTraceReadStore bits target).readWord?
          (WordRAM.singletonSegmentMap
            subLogSelectSuperTableTraceSegments.baseWordIndex
            subLogSelectSuperTableTraceSegments.deadSegment localSegment)
          index =
        let data := GenericSelect.sparseExceptionSelectData bits target
        data.superTable.baseWordIndexTable.wordRAMStore.readWord?
          localSegment index := by
  intro localSegment index
  cases localSegment <;>
    simp [subLogSelectFromPackedClarkRouteTraceReadStore,
      subLogSelectSuperTableTraceSegments,
      WordRAM.singletonSegmentMap, WordRAM.TraceEvent.singletonSegmentMap,
      SuccinctSpace.FixedWidthNatTable.wordRAMStore,
      SuccinctSpace.PayloadWordStore.wordRAMStore,
      WordRAM.Store.readWord?]

private theorem subLogSelectTraceReadStore_super_rankBefore_read
    (bits : List Bool) (target : Bool) :
    forall localSegment index,
      (subLogSelectFromPackedClarkRouteTraceReadStore bits target).readWord?
          (WordRAM.singletonSegmentMap
            subLogSelectSuperTableTraceSegments.rankBefore
            subLogSelectSuperTableTraceSegments.deadSegment localSegment)
          index =
        let data := GenericSelect.sparseExceptionSelectData bits target
        data.superTable.rankBeforeTable.wordRAMStore.readWord?
          localSegment index := by
  intro localSegment index
  cases localSegment <;>
    simp [subLogSelectFromPackedClarkRouteTraceReadStore,
      subLogSelectSuperTableTraceSegments,
      WordRAM.singletonSegmentMap, WordRAM.TraceEvent.singletonSegmentMap,
      SuccinctSpace.FixedWidthNatTable.wordRAMStore,
      SuccinctSpace.PayloadWordStore.wordRAMStore,
      WordRAM.Store.readWord?]

private theorem subLogSelectTraceReadStore_super_firstOffset_read
    (bits : List Bool) (target : Bool) :
    forall localSegment index,
      (subLogSelectFromPackedClarkRouteTraceReadStore bits target).readWord?
          (WordRAM.singletonSegmentMap
            subLogSelectSuperTableTraceSegments.firstOffset
            subLogSelectSuperTableTraceSegments.deadSegment localSegment)
          index =
        let data := GenericSelect.sparseExceptionSelectData bits target
        data.superTable.firstOffsetTable.wordRAMStore.readWord?
          localSegment index := by
  intro localSegment index
  cases localSegment <;>
    simp [subLogSelectFromPackedClarkRouteTraceReadStore,
      subLogSelectSuperTableTraceSegments,
      WordRAM.singletonSegmentMap, WordRAM.TraceEvent.singletonSegmentMap,
      SuccinctSpace.FixedWidthNatTable.wordRAMStore,
      SuccinctSpace.PayloadWordStore.wordRAMStore,
      WordRAM.Store.readWord?]

private theorem subLogSelectTraceReadStore_local_baseOccurrence_read
    (bits : List Bool) (target : Bool) :
    forall localSegment index,
      (subLogSelectFromPackedClarkRouteTraceReadStore bits target).readWord?
          (WordRAM.singletonSegmentMap
            subLogSelectLocalTableTraceSegments.baseOccurrence
            subLogSelectLocalTableTraceSegments.deadSegment localSegment)
          index =
        let data := GenericSelect.sparseExceptionSelectData bits target
        data.localTable.baseOccurrenceTable.wordRAMStore.readWord?
          localSegment index := by
  intro localSegment index
  cases localSegment <;>
    simp [subLogSelectFromPackedClarkRouteTraceReadStore,
      subLogSelectLocalTableTraceSegments,
      WordRAM.singletonSegmentMap, WordRAM.TraceEvent.singletonSegmentMap,
      SuccinctSpace.FixedWidthNatTable.wordRAMStore,
      SuccinctSpace.PayloadWordStore.wordRAMStore,
      WordRAM.Store.readWord?]

private theorem subLogSelectTraceReadStore_local_baseWordIndex_read
    (bits : List Bool) (target : Bool) :
    forall localSegment index,
      (subLogSelectFromPackedClarkRouteTraceReadStore bits target).readWord?
          (WordRAM.singletonSegmentMap
            subLogSelectLocalTableTraceSegments.baseWordIndex
            subLogSelectLocalTableTraceSegments.deadSegment localSegment)
          index =
        let data := GenericSelect.sparseExceptionSelectData bits target
        data.localTable.baseWordIndexTable.wordRAMStore.readWord?
          localSegment index := by
  intro localSegment index
  cases localSegment <;>
    simp [subLogSelectFromPackedClarkRouteTraceReadStore,
      subLogSelectLocalTableTraceSegments,
      WordRAM.singletonSegmentMap, WordRAM.TraceEvent.singletonSegmentMap,
      SuccinctSpace.FixedWidthNatTable.wordRAMStore,
      SuccinctSpace.PayloadWordStore.wordRAMStore,
      WordRAM.Store.readWord?]

private theorem subLogSelectTraceReadStore_local_rankBefore_read
    (bits : List Bool) (target : Bool) :
    forall localSegment index,
      (subLogSelectFromPackedClarkRouteTraceReadStore bits target).readWord?
          (WordRAM.singletonSegmentMap
            subLogSelectLocalTableTraceSegments.rankBefore
            subLogSelectLocalTableTraceSegments.deadSegment localSegment)
          index =
        let data := GenericSelect.sparseExceptionSelectData bits target
        data.localTable.rankBeforeTable.wordRAMStore.readWord?
          localSegment index := by
  intro localSegment index
  cases localSegment <;>
    simp [subLogSelectFromPackedClarkRouteTraceReadStore,
      subLogSelectLocalTableTraceSegments,
      WordRAM.singletonSegmentMap, WordRAM.TraceEvent.singletonSegmentMap,
      SuccinctSpace.FixedWidthNatTable.wordRAMStore,
      SuccinctSpace.PayloadWordStore.wordRAMStore,
      WordRAM.Store.readWord?]

private theorem subLogSelectTraceReadStore_local_firstOffset_read
    (bits : List Bool) (target : Bool) :
    forall localSegment index,
      (subLogSelectFromPackedClarkRouteTraceReadStore bits target).readWord?
          (WordRAM.singletonSegmentMap
            subLogSelectLocalTableTraceSegments.firstOffset
            subLogSelectLocalTableTraceSegments.deadSegment localSegment)
          index =
        let data := GenericSelect.sparseExceptionSelectData bits target
        data.localTable.firstOffsetTable.wordRAMStore.readWord?
          localSegment index := by
  intro localSegment index
  cases localSegment <;>
    simp [subLogSelectFromPackedClarkRouteTraceReadStore,
      subLogSelectLocalTableTraceSegments,
      WordRAM.singletonSegmentMap, WordRAM.TraceEvent.singletonSegmentMap,
      SuccinctSpace.FixedWidthNatTable.wordRAMStore,
      SuccinctSpace.PayloadWordStore.wordRAMStore,
      WordRAM.Store.readWord?]

private theorem subLogSelectTraceReadStore_longFlagRank_read
    (bits : List Bool) (target : Bool) :
    forall localSegment index,
      (subLogSelectFromPackedClarkRouteTraceReadStore bits target).readWord?
          (WordRAM.tripleSegmentMap
            subLogSelectLongFlagRankBase subLogSelectDeadSegment localSegment)
          index =
        let data := GenericSelect.sparseExceptionSelectData bits target
        (data.longFlagRankData.rankRegisterWordRAMStore true).readWord?
          localSegment index := by
  intro localSegment index
  cases localSegment with
  | zero =>
      simp [subLogSelectFromPackedClarkRouteTraceReadStore,
        subLogSelectLongFlagRankBase,
        WordRAM.tripleSegmentMap, WordRAM.TraceEvent.tripleSegmentMap,
        WordRAM.Store.readWord?]
  | succ localSegment =>
      cases localSegment with
      | zero =>
          simp [subLogSelectFromPackedClarkRouteTraceReadStore,
            subLogSelectLongFlagRankBase,
            WordRAM.tripleSegmentMap, WordRAM.TraceEvent.tripleSegmentMap,
            WordRAM.Store.readWord?]
      | succ localSegment =>
          cases localSegment with
          | zero =>
              simp [subLogSelectFromPackedClarkRouteTraceReadStore,
                subLogSelectLongFlagRankBase,
                WordRAM.tripleSegmentMap,
                WordRAM.TraceEvent.tripleSegmentMap,
                WordRAM.Store.readWord?]
          | succ localSegment =>
              simp [subLogSelectFromPackedClarkRouteTraceReadStore,
                subLogSelectDeadSegment,
                WordRAM.tripleSegmentMap,
                WordRAM.TraceEvent.tripleSegmentMap,
                SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.rankRegisterWordRAMStore,
                WordRAM.Store.readWord?]

private theorem subLogSelectTraceReadStore_longRelative_read
    (bits : List Bool) (target : Bool) :
    forall localSegment index,
      (subLogSelectFromPackedClarkRouteTraceReadStore bits target).readWord?
          (WordRAM.singletonSegmentMap
            subLogSelectLongRelativeSegment subLogSelectDeadSegment
            localSegment)
          index =
        let data := GenericSelect.sparseExceptionSelectData bits target
        data.longSuperRelativeTable.wordRAMStore.readWord?
          localSegment index := by
  intro localSegment index
  cases localSegment <;>
    simp [subLogSelectFromPackedClarkRouteTraceReadStore,
      subLogSelectLongRelativeSegment, subLogSelectDeadSegment,
      WordRAM.singletonSegmentMap, WordRAM.TraceEvent.singletonSegmentMap,
      SuccinctSpace.FixedWidthNatTable.wordRAMStore,
      SuccinctSpace.PayloadWordStore.wordRAMStore,
      WordRAM.Store.readWord?]

private theorem subLogSelectTraceReadStore_sparseRank_read
    (bits : List Bool) (target : Bool) :
    forall localSegment index,
      (subLogSelectFromPackedClarkRouteTraceReadStore bits target).readWord?
          (WordRAM.tripleSegmentMap
            subLogSelectSparseDirectoryTraceSegments.rankBase
            subLogSelectSparseDirectoryTraceSegments.deadSegment localSegment)
          index =
        let data := GenericSelect.sparseExceptionSelectData bits target
        (data.sparseDirectory.rankData.rankRegisterWordRAMStore true).readWord?
          localSegment index := by
  intro localSegment index
  cases localSegment with
  | zero =>
      simp [subLogSelectFromPackedClarkRouteTraceReadStore,
        subLogSelectSparseDirectoryTraceSegments,
        WordRAM.tripleSegmentMap, WordRAM.TraceEvent.tripleSegmentMap,
        WordRAM.Store.readWord?]
  | succ localSegment =>
      cases localSegment with
      | zero =>
          simp [subLogSelectFromPackedClarkRouteTraceReadStore,
            subLogSelectSparseDirectoryTraceSegments,
            WordRAM.tripleSegmentMap, WordRAM.TraceEvent.tripleSegmentMap,
            WordRAM.Store.readWord?]
      | succ localSegment =>
          cases localSegment with
          | zero =>
              simp [subLogSelectFromPackedClarkRouteTraceReadStore,
                subLogSelectSparseDirectoryTraceSegments,
                WordRAM.tripleSegmentMap,
                WordRAM.TraceEvent.tripleSegmentMap,
                WordRAM.Store.readWord?]
          | succ localSegment =>
              simp [subLogSelectFromPackedClarkRouteTraceReadStore,
                subLogSelectSparseDirectoryTraceSegments,
                WordRAM.tripleSegmentMap,
                WordRAM.TraceEvent.tripleSegmentMap,
                SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.rankRegisterWordRAMStore,
                WordRAM.Store.readWord?]

private theorem subLogSelectTraceReadStore_sparseRelative_read
    (bits : List Bool) (target : Bool) :
    forall localSegment index,
      (subLogSelectFromPackedClarkRouteTraceReadStore bits target).readWord?
          (WordRAM.singletonSegmentMap
            subLogSelectSparseDirectoryTraceSegments.relativeBase
            subLogSelectSparseDirectoryTraceSegments.deadSegment localSegment)
          index =
        let data := GenericSelect.sparseExceptionSelectData bits target
        data.sparseDirectory.relativeTable.wordRAMStore.readWord?
          localSegment index := by
  intro localSegment index
  cases localSegment <;>
    simp [subLogSelectFromPackedClarkRouteTraceReadStore,
      subLogSelectSparseDirectoryTraceSegments,
      WordRAM.singletonSegmentMap, WordRAM.TraceEvent.singletonSegmentMap,
      SuccinctSpace.FixedWidthNatTable.wordRAMStore,
      SuccinctSpace.PayloadWordStore.wordRAMStore,
      WordRAM.Store.readWord?]

/-- Trace-result decode of one sub-log block by index. -/
def subLogDecodeBlockByIndexTraceResult
    (bits : List Bool) (_target : Bool) (blockIndex : Nat) :
    WordRAM.TraceResult (List Bool) :=
  WordRAM.TraceResult.bind
      (boundedWordReadTraceResultAtSegment
        subLogSelectCodeSegment subLogSelectDeadSegment
        (subLogCodeStore bits) blockIndex)
      fun code? =>
  WordRAM.TraceResult.bind
      (boundedWordReadTraceResultAtSegment
        subLogSelectLengthSegment subLogSelectDeadSegment
        (subLogLenStore bits) blockIndex)
      fun len? =>
  WordRAM.TraceResult.bind
      (boundedWordReadTraceResultAtSegment
        subLogSelectClassSegment subLogSelectDeadSegment
        (subLogClassStore bits) blockIndex)
      fun class? =>
  WordRAM.TraceResult.bind
      (boundedWordReadTraceResultAtSegment
        subLogSelectDecoderSegment subLogSelectDeadSegment
        (fixedWeightSubLogSharedDecoderStore bits)
        (fixedWeightSharedDecodeSlotFromReadValues [len?, class?] [code?]))
      fun decoded? =>
    WordRAM.TraceResult.pure (decoded?.getD [])

theorem subLogDecodeBlockByIndexTraceResult_refines_interpretedCosted
    (bits : List Bool) (target : Bool) (blockIndex : Nat) :
    (subLogDecodeBlockByIndexTraceResult
      bits target blockIndex).toCosted =
        subLogDecodeBlockByIndexInterpretedCosted bits blockIndex := by
  simp [subLogDecodeBlockByIndexTraceResult,
    subLogDecodeBlockByIndexInterpretedCosted,
    boundedWordReadTraceResultAtSegment_refines_interpretedCosted,
    subLogDecodeReadInterpretedCosted,
    WordRAM.TraceResult.bind_toCosted,
    WordRAM.TraceResult.pure_toCosted]

theorem subLogDecodeBlockByIndexTraceResult_matchesReadStore
    (bits : List Bool) (target : Bool) (blockIndex : Nat) :
    forall event,
      event ∈
          (subLogDecodeBlockByIndexTraceResult
            bits target blockIndex).trace ->
        event.matchesReadStore
          (subLogSelectFromPackedClarkRouteTraceReadStore bits target) := by
  unfold subLogDecodeBlockByIndexTraceResult
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      boundedWordReadTraceResultAtSegment_matchesReadStore
        subLogSelectCodeSegment subLogSelectDeadSegment
        (subLogCodeStore bits)
        (subLogSelectFromPackedClarkRouteTraceReadStore bits target)
        (subLogSelectTraceReadStore_code_read bits target)
        blockIndex
  · apply WordRAM.TraceResult.bind_trace_forall
    · exact
        boundedWordReadTraceResultAtSegment_matchesReadStore
          subLogSelectLengthSegment subLogSelectDeadSegment
          (subLogLenStore bits)
          (subLogSelectFromPackedClarkRouteTraceReadStore bits target)
          (subLogSelectTraceReadStore_len_read bits target)
          blockIndex
    · apply WordRAM.TraceResult.bind_trace_forall
      · exact
          boundedWordReadTraceResultAtSegment_matchesReadStore
            subLogSelectClassSegment subLogSelectDeadSegment
            (subLogClassStore bits)
            (subLogSelectFromPackedClarkRouteTraceReadStore bits target)
            (subLogSelectTraceReadStore_class_read bits target)
            blockIndex
      · apply WordRAM.TraceResult.bind_trace_forall
        · exact
            boundedWordReadTraceResultAtSegment_matchesReadStore
              subLogSelectDecoderSegment subLogSelectDeadSegment
              (fixedWeightSubLogSharedDecoderStore bits)
              (subLogSelectFromPackedClarkRouteTraceReadStore bits target)
              (subLogSelectTraceReadStore_decoder_read bits target)
              (fixedWeightSharedDecodeSlotFromReadValues [_, _] [_])
        · exact WordRAM.TraceResult.pure_trace_forall
            (fun event =>
              event.matchesReadStore
                (subLogSelectFromPackedClarkRouteTraceReadStore bits target))
            _

/-- Trace-result decode of a constant-size sub-log block window. -/
def subLogDecodeBlockWindowTraceResult
    (bits : List Bool) (target : Bool) (startBlock count : Nat) :
    WordRAM.TraceResult (List (List Bool)) :=
  match count with
  | 0 => WordRAM.TraceResult.pure []
  | count' + 1 =>
      WordRAM.TraceResult.bind
          (subLogDecodeBlockByIndexTraceResult bits target startBlock)
          fun block =>
        WordRAM.TraceResult.map
          (fun rest => block :: rest)
          (subLogDecodeBlockWindowTraceResult bits target
            (startBlock + 1) count')

theorem subLogDecodeBlockWindowTraceResult_refines_interpretedCosted
    (bits : List Bool) (target : Bool) (startBlock count : Nat) :
    (subLogDecodeBlockWindowTraceResult
      bits target startBlock count).toCosted =
        subLogDecodeBlockWindowInterpretedCosted
          bits startBlock count := by
  induction count generalizing startBlock with
  | zero =>
      rfl
  | succ count ih =>
      simp [subLogDecodeBlockWindowTraceResult,
        subLogDecodeBlockWindowInterpretedCosted,
        subLogDecodeBlockByIndexTraceResult_refines_interpretedCosted,
        ih, WordRAM.TraceResult.bind_toCosted,
        WordRAM.TraceResult.map_toCosted]

theorem subLogDecodeBlockWindowTraceResult_matchesReadStore
    (bits : List Bool) (target : Bool) (startBlock count : Nat) :
    forall event,
      event ∈
          (subLogDecodeBlockWindowTraceResult
            bits target startBlock count).trace ->
        event.matchesReadStore
          (subLogSelectFromPackedClarkRouteTraceReadStore bits target) := by
  induction count generalizing startBlock with
  | zero =>
      exact WordRAM.TraceResult.pure_trace_forall
        (fun event =>
          event.matchesReadStore
            (subLogSelectFromPackedClarkRouteTraceReadStore bits target)) []
  | succ count ih =>
      unfold subLogDecodeBlockWindowTraceResult
      apply WordRAM.TraceResult.bind_trace_forall
      · exact subLogDecodeBlockByIndexTraceResult_matchesReadStore
          bits target startBlock
      · apply WordRAM.TraceResult.map_trace_forall
        exact ih (startBlock + 1)

/-- Trace-result reconstruction of one machine word from sub-log blocks. -/
def subLogMachineWordReadTraceResult
    (bits : List Bool) (target : Bool) (wordIndex : Nat) :
    WordRAM.TraceResult (List Bool) :=
  let wordSize := SuccinctRank.machineWordBits bits.length
  let start := wordIndex * wordSize
  let startBlock := start / fixedWeightSubLogChunkBlockSize bits.length
  WordRAM.TraceResult.bind
    (subLogDecodeBlockWindowTraceResult bits target startBlock
      fixedWeightSubLogDenseWindowBlockCount)
    fun decodedWindow =>
      WordRAM.TraceResult.pure
        (subLogMachineWordFromDecodedWindow bits wordIndex decodedWindow)

theorem subLogMachineWordReadTraceResult_refines_interpretedCosted
    (bits : List Bool) (target : Bool) (wordIndex : Nat) :
    (subLogMachineWordReadTraceResult bits target wordIndex).toCosted =
      subLogMachineWordReadInterpretedCosted bits wordIndex := by
  simp [subLogMachineWordReadTraceResult,
    subLogMachineWordReadInterpretedCosted,
    subLogDecodeBlockWindowTraceResult_refines_interpretedCosted,
    WordRAM.TraceResult.bind_toCosted,
    WordRAM.TraceResult.pure_toCosted]

theorem subLogMachineWordReadTraceResult_matchesReadStore
    (bits : List Bool) (target : Bool) (wordIndex : Nat) :
    forall event,
      event ∈ (subLogMachineWordReadTraceResult bits target wordIndex).trace ->
        event.matchesReadStore
          (subLogSelectFromPackedClarkRouteTraceReadStore bits target) := by
  unfold subLogMachineWordReadTraceResult
  apply WordRAM.TraceResult.bind_trace_forall
  · exact subLogDecodeBlockWindowTraceResult_matchesReadStore
      bits target
      ((wordIndex * SuccinctRank.machineWordBits bits.length) /
        fixedWeightSubLogChunkBlockSize bits.length)
      fixedWeightSubLogDenseWindowBlockCount
  · exact WordRAM.TraceResult.pure_trace_forall
      (fun event =>
        event.matchesReadStore
          (subLogSelectFromPackedClarkRouteTraceReadStore bits target)) _

def subLogDenseTwoWordSelectTailTraceResult
    (target : Bool) (bits : List Bool)
    (wordSize firstWordIndex firstWordStart localOccurrence : Nat)
    (firstWord : List Bool) (beforeFirst uptoFirst : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  let firstCount := uptoFirst - beforeFirst
  if localOccurrence < firstCount then
    WordRAM.TraceResult.map
      (fun local? =>
        local?.map fun offset => firstWordStart + offset)
      (GenericSelect.wordSelectTraceResult target firstWord
        (beforeFirst + localOccurrence))
  else
    WordRAM.TraceResult.bind
      (subLogMachineWordReadTraceResult bits target (firstWordIndex + 1))
      fun secondWord =>
        WordRAM.TraceResult.map
          (fun local? =>
            local?.map fun offset =>
              (firstWordIndex + 1) * wordSize + offset)
          (GenericSelect.wordSelectTraceResult target
            secondWord (localOccurrence - firstCount))

theorem subLogDenseTwoWordSelectTailTraceResult_refines_interpretedCosted
    (target : Bool) (bits : List Bool)
    (wordSize firstWordIndex firstWordStart localOccurrence : Nat)
    (firstWord : List Bool) (beforeFirst uptoFirst : Nat) :
    (subLogDenseTwoWordSelectTailTraceResult
      target bits wordSize firstWordIndex firstWordStart
      localOccurrence firstWord beforeFirst uptoFirst).toCosted =
        (let firstCount := uptoFirst - beforeFirst
         if localOccurrence < firstCount then
           Costed.map
             (fun local? =>
               local?.map fun offset => firstWordStart + offset)
             (GenericSelect.wordSelectInterpretedCosted target firstWord
               (beforeFirst + localOccurrence))
         else
           Costed.bind
             (subLogMachineWordReadInterpretedCosted bits
               (firstWordIndex + 1))
             fun secondWord =>
               Costed.map
                 (fun local? =>
                   local?.map fun offset =>
                     (firstWordIndex + 1) * wordSize + offset)
                 (GenericSelect.wordSelectInterpretedCosted target
                   secondWord (localOccurrence - firstCount))) := by
  unfold subLogDenseTwoWordSelectTailTraceResult
  by_cases hlocal : localOccurrence < uptoFirst - beforeFirst
  · simp [hlocal,
      GenericSelect.wordSelectTraceResult_refines_interpretedCosted,
      WordRAM.TraceResult.map_toCosted]
  · simp [hlocal,
      subLogMachineWordReadTraceResult_refines_interpretedCosted,
      GenericSelect.wordSelectTraceResult_refines_interpretedCosted,
      WordRAM.TraceResult.bind_toCosted,
      WordRAM.TraceResult.map_toCosted]

theorem subLogDenseTwoWordSelectTailTraceResult_matchesReadStore
    (target : Bool) (bits : List Bool)
    (wordSize firstWordIndex firstWordStart localOccurrence : Nat)
    (firstWord : List Bool) (beforeFirst uptoFirst : Nat) :
    forall event,
      event ∈
          (subLogDenseTwoWordSelectTailTraceResult
            target bits wordSize firstWordIndex firstWordStart
            localOccurrence firstWord beforeFirst uptoFirst).trace ->
        event.matchesReadStore
          (subLogSelectFromPackedClarkRouteTraceReadStore bits target) := by
  unfold subLogDenseTwoWordSelectTailTraceResult
  by_cases hlocal : localOccurrence < uptoFirst - beforeFirst
  · intro event hmem
    exact
      GenericSelect.wordSelectTraceResult_matchesReadStore
        target firstWord (beforeFirst + localOccurrence)
        (subLogSelectFromPackedClarkRouteTraceReadStore bits target)
        event
        (by simpa [hlocal] using hmem)
  · intro event hmem
    simp [hlocal, WordRAM.TraceResult.bind] at hmem
    rcases hmem with hmem | hmem
    · exact subLogMachineWordReadTraceResult_matchesReadStore
        bits target (firstWordIndex + 1) event hmem
    · exact
        GenericSelect.wordSelectTraceResult_matchesReadStore
          target
          (subLogMachineWordReadTraceResult bits target
            (firstWordIndex + 1)).value
          (localOccurrence - (uptoFirst - beforeFirst))
          (subLogSelectFromPackedClarkRouteTraceReadStore bits target)
          event hmem

/-- Trace-result dense two-word select branch over sub-log decoded windows. -/
def subLogDenseTwoWordSelectTraceResult
    (target : Bool) (bits : List Bool)
    (basePosition baseOccurrence q : Nat) : WordRAM.TraceResult (Option Nat) :=
  let wordSize := SuccinctRank.machineWordBits bits.length
  let firstWordIndex := basePosition / wordSize
  let firstWordStart := firstWordIndex * wordSize
  let firstOffset := basePosition - firstWordStart
  let localOccurrence := q - baseOccurrence
  WordRAM.TraceResult.bind
      (subLogMachineWordReadTraceResult bits target firstWordIndex)
      fun firstWord =>
    WordRAM.TraceResult.bind
      (SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult
        target firstWord firstOffset)
      fun beforeFirst =>
        WordRAM.TraceResult.bind
          (SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult
            target firstWord firstWord.length)
          fun uptoFirst =>
            subLogDenseTwoWordSelectTailTraceResult
              target bits wordSize firstWordIndex firstWordStart
              localOccurrence firstWord beforeFirst uptoFirst

theorem subLogDenseTwoWordSelectTraceResult_refines_interpretedCosted
    (target : Bool) (bits : List Bool)
    (basePosition baseOccurrence q : Nat) :
    (subLogDenseTwoWordSelectTraceResult
      target bits basePosition baseOccurrence q).toCosted =
        subLogDenseTwoWordSelectInterpretedCosted
          target bits basePosition baseOccurrence q := by
  unfold subLogDenseTwoWordSelectTraceResult
    subLogDenseTwoWordSelectInterpretedCosted
  simp [subLogMachineWordReadTraceResult_refines_interpretedCosted,
    SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult_refines_interpretedCosted,
    subLogDenseTwoWordSelectTailTraceResult_refines_interpretedCosted,
    WordRAM.TraceResult.bind_toCosted]

theorem subLogDenseTwoWordSelectTraceResult_matchesReadStore
    (target : Bool) (bits : List Bool)
    (basePosition baseOccurrence q : Nat) :
    forall event,
      event ∈
          (subLogDenseTwoWordSelectTraceResult
            target bits basePosition baseOccurrence q).trace ->
        event.matchesReadStore
          (subLogSelectFromPackedClarkRouteTraceReadStore bits target) := by
  unfold subLogDenseTwoWordSelectTraceResult
  apply WordRAM.TraceResult.bind_trace_forall
  · exact subLogMachineWordReadTraceResult_matchesReadStore bits target
      (basePosition / SuccinctRank.machineWordBits bits.length)
  · apply WordRAM.TraceResult.bind_trace_forall
    · exact
        SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult_matchesReadStore
          target _ _
          (subLogSelectFromPackedClarkRouteTraceReadStore bits target)
    · apply WordRAM.TraceResult.bind_trace_forall
      · exact
          SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult_matchesReadStore
            target _ _
            (subLogSelectFromPackedClarkRouteTraceReadStore bits target)
      · exact
          subLogDenseTwoWordSelectTailTraceResult_matchesReadStore
            target bits (SuccinctRank.machineWordBits bits.length)
            (basePosition / SuccinctRank.machineWordBits bits.length)
            ((basePosition / SuccinctRank.machineWordBits bits.length) *
              SuccinctRank.machineWordBits bits.length)
            (q - baseOccurrence)
            (subLogMachineWordReadTraceResult bits target
              (basePosition /
                SuccinctRank.machineWordBits bits.length)).value
            (SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult
              target
              (subLogMachineWordReadTraceResult bits target
                (basePosition /
                  SuccinctRank.machineWordBits bits.length)).value
              (basePosition -
                (basePosition /
                    SuccinctRank.machineWordBits bits.length) *
                  SuccinctRank.machineWordBits bits.length)).value
            (SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult
              target
              (subLogMachineWordReadTraceResult bits target
                (basePosition /
                  SuccinctRank.machineWordBits bits.length)).value
              (subLogMachineWordReadTraceResult bits target
                (basePosition /
                  SuccinctRank.machineWordBits bits.length)).value.length).value

/-- Interpreted final local select from already-computed packed-Clark fields. -/
def subLogSelectWithFieldsInterpretedCosted
    (bits : List Bool) (target : Bool)
    (fields : FixedWeightSubLogClarkSelectRouteFields) :
    Costed (Option Nat) :=
  Costed.bind
      (boundedWordReadInterpretedCosted
        (subLogCodeStore bits) fields.blockIndex) fun code? =>
  Costed.bind
      (boundedWordReadInterpretedCosted
        (subLogLenStore bits) fields.blockIndex) fun len? =>
  Costed.bind
      (boundedWordReadInterpretedCosted
        (subLogClassStore bits) fields.blockIndex) fun class? =>
  Costed.bind
      (subLogDecodeReadInterpretedCosted bits
        (fixedWeightSharedDecodeSlotFromReadValues [len?, class?] [code?]))
      fun decoded? =>
    Costed.pure
      ((Succinct.select target
          (decoded?.getD []) fields.localOccurrence).map
        (fun offset => fields.blockStart + offset))

theorem subLogSelectWithFieldsInterpretedCosted_refines
    (bits : List Bool) (target : Bool)
    (fields : FixedWeightSubLogClarkSelectRouteFields) :
    subLogSelectWithFieldsInterpretedCosted bits target fields =
      subLogSelectWithFieldsCosted bits target fields := by
  unfold subLogSelectWithFieldsInterpretedCosted
    subLogSelectWithFieldsCosted
  simp [boundedWordReadInterpretedCosted_refines_readWordCosted,
    subLogDecodeReadInterpretedCosted_refines_subLogDecodeReadCosted]

/-- Trace-result final local select from already-computed packed-Clark fields. -/
def subLogSelectWithFieldsTraceResult
    (bits : List Bool) (target : Bool)
    (fields : FixedWeightSubLogClarkSelectRouteFields) :
    WordRAM.TraceResult (Option Nat) :=
  WordRAM.TraceResult.bind
      (boundedWordReadTraceResultAtSegment
        subLogSelectCodeSegment subLogSelectDeadSegment
        (subLogCodeStore bits) fields.blockIndex)
      fun code? =>
  WordRAM.TraceResult.bind
      (boundedWordReadTraceResultAtSegment
        subLogSelectLengthSegment subLogSelectDeadSegment
        (subLogLenStore bits) fields.blockIndex)
      fun len? =>
  WordRAM.TraceResult.bind
      (boundedWordReadTraceResultAtSegment
        subLogSelectClassSegment subLogSelectDeadSegment
        (subLogClassStore bits) fields.blockIndex)
      fun class? =>
  WordRAM.TraceResult.bind
      (boundedWordReadTraceResultAtSegment
        subLogSelectDecoderSegment subLogSelectDeadSegment
        (fixedWeightSubLogSharedDecoderStore bits)
        (fixedWeightSharedDecodeSlotFromReadValues [len?, class?] [code?]))
      fun decoded? =>
    WordRAM.TraceResult.pure
      ((Succinct.select target
          (decoded?.getD []) fields.localOccurrence).map
        (fun offset => fields.blockStart + offset))

theorem subLogSelectWithFieldsTraceResult_refines_interpretedCosted
    (bits : List Bool) (target : Bool)
    (fields : FixedWeightSubLogClarkSelectRouteFields) :
    (subLogSelectWithFieldsTraceResult bits target fields).toCosted =
      subLogSelectWithFieldsInterpretedCosted bits target fields := by
  simp [subLogSelectWithFieldsTraceResult,
    subLogSelectWithFieldsInterpretedCosted,
    boundedWordReadTraceResultAtSegment_refines_interpretedCosted,
    subLogDecodeReadInterpretedCosted,
    WordRAM.TraceResult.bind_toCosted,
    WordRAM.TraceResult.pure_toCosted]

theorem subLogSelectWithFieldsTraceResult_matchesReadStore
    (bits : List Bool) (target : Bool)
    (fields : FixedWeightSubLogClarkSelectRouteFields) :
    forall event,
      event ∈ (subLogSelectWithFieldsTraceResult bits target fields).trace ->
        event.matchesReadStore
          (subLogSelectFromPackedClarkRouteTraceReadStore bits target) := by
  unfold subLogSelectWithFieldsTraceResult
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      boundedWordReadTraceResultAtSegment_matchesReadStore
        subLogSelectCodeSegment subLogSelectDeadSegment
        (subLogCodeStore bits)
        (subLogSelectFromPackedClarkRouteTraceReadStore bits target)
        (subLogSelectTraceReadStore_code_read bits target)
        fields.blockIndex
  · apply WordRAM.TraceResult.bind_trace_forall
    · exact
        boundedWordReadTraceResultAtSegment_matchesReadStore
          subLogSelectLengthSegment subLogSelectDeadSegment
          (subLogLenStore bits)
          (subLogSelectFromPackedClarkRouteTraceReadStore bits target)
          (subLogSelectTraceReadStore_len_read bits target)
          fields.blockIndex
    · apply WordRAM.TraceResult.bind_trace_forall
      · exact
          boundedWordReadTraceResultAtSegment_matchesReadStore
            subLogSelectClassSegment subLogSelectDeadSegment
            (subLogClassStore bits)
            (subLogSelectFromPackedClarkRouteTraceReadStore bits target)
            (subLogSelectTraceReadStore_class_read bits target)
            fields.blockIndex
      · apply WordRAM.TraceResult.bind_trace_forall
        · exact
            boundedWordReadTraceResultAtSegment_matchesReadStore
              subLogSelectDecoderSegment subLogSelectDeadSegment
              (fixedWeightSubLogSharedDecoderStore bits)
              (subLogSelectFromPackedClarkRouteTraceReadStore bits target)
              (subLogSelectTraceReadStore_decoder_read bits target)
              (fixedWeightSharedDecodeSlotFromReadValues [_, _] [_])
        · exact WordRAM.TraceResult.pure_trace_forall
            (fun event =>
              event.matchesReadStore
                (subLogSelectFromPackedClarkRouteTraceReadStore bits target))
            _

/--
Interpreted packed-Clark select source.

This mirrors `subLogPackedClarkSelectCosted`, replacing every concrete table,
rank, sparse-directory, and dense-window leaf by its interpreted counterpart.
-/
def subLogPackedClarkSelectInterpretedCosted
    (bits : List Bool) (target : Bool) (idx : Nat) :
    Costed (Option Nat) :=
  let data := GenericSelect.sparseExceptionSelectData bits target
  let q := idx
  if idx < GenericSelect.occurrenceCount bits target then
    Costed.bind
      (data.superTable.readInterpretedCosted
        (GenericSelect.selectSuperSlot q data.superStride)) fun super? =>
      match super? with
      | none => Costed.pure none
      | some super =>
          if GenericSelect.relativeSplitSelectEntryIsMarked super then
            Costed.bind
              (data.longFlagRankData.rankInterpretedCosted true
                (GenericSelect.selectSuperSlot q data.superStride))
              fun exceptionRank =>
                GenericSelect.relativeOffsetReadInterpretedCosted
                  data.longSuperRelativeTable
                  (GenericSelect.relativeSplitSelectEntryBasePosition
                    data.wordSize super)
                  (GenericSelect.relativeSplitSelectLongCompactSlot
                    exceptionRank (q - super.baseOccurrence)
                    data.superStride)
          else
            let localSlot :=
              GenericSelect.relativeSplitSelectLocalSlot q data.superStride
                data.localSlotsPerSuper data.localStride super
            Costed.bind
              (data.localTable.readInterpretedCosted localSlot) fun loc? =>
              match loc? with
              | none => Costed.pure none
              | some loc =>
                  if GenericSelect.relativeSplitSelectEntryIsMarked loc then
                    data.sparseDirectory.readInterpretedCosted
                      (GenericSelect.relativeSplitSelectLocalBasePosition
                        data.wordSize super loc)
                      localSlot
                      (q -
                        GenericSelect.relativeSplitSelectLocalBaseOccurrence
                          super loc)
                  else
                    subLogDenseTwoWordSelectInterpretedCosted target bits
                      (GenericSelect.relativeSplitSelectLocalBasePosition
                        data.wordSize super loc)
                      (GenericSelect.relativeSplitSelectLocalBaseOccurrence
                        super loc) q
  else
    Costed.pure none

theorem subLogPackedClarkSelectInterpretedCosted_refines
    (bits : List Bool) (target : Bool) (idx : Nat) :
    subLogPackedClarkSelectInterpretedCosted bits target idx =
      subLogPackedClarkSelectCosted bits target idx := by
  unfold subLogPackedClarkSelectInterpretedCosted
    subLogPackedClarkSelectCosted
  let data := GenericSelect.sparseExceptionSelectData bits target
  by_cases hvalid : idx < GenericSelect.occurrenceCount bits target
  · simp [hvalid]
    rw [data.superTable.readInterpretedCosted_refines_readCosted
      (GenericSelect.selectSuperSlot idx data.superStride)]
    cases hsuper :
        (data.superTable.readCosted
          (GenericSelect.selectSuperSlot idx data.superStride)).value with
    | none =>
        simp [data, Costed.bind, Costed.pure, hsuper]
    | some super =>
        by_cases hlong :
            GenericSelect.relativeSplitSelectEntryIsMarked super = true
        · rw [data.longFlagRankData.rankInterpretedCosted_refines_rankCosted
            true (GenericSelect.selectSuperSlot idx data.superStride)]
          simp [Costed.bind, hsuper, hlong]
          rw [GenericSelect.relativeOffsetReadInterpretedCosted_refines]
          simp [data, hsuper, hlong]
        · let localSlot :=
            GenericSelect.relativeSplitSelectLocalSlot idx data.superStride
              data.localSlotsPerSuper data.localStride super
          simp [Costed.bind, hsuper, hlong]
          rw [data.localTable.readInterpretedCosted_refines_readCosted
            localSlot]
          cases hlocal :
              (data.localTable.readCosted localSlot).value with
          | none =>
              simp [data, Costed.pure, hsuper, hlong,
                localSlot, hlocal]
          | some loc =>
              by_cases hsparse :
                  GenericSelect.relativeSplitSelectEntryIsMarked loc = true
              · simp [hsparse]
                rw [data.sparseDirectory.readInterpretedCosted_refines_readCosted]
                simp [data, hsuper, hlong, localSlot,
                  hlocal, hsparse]
              · simp [hsparse]
                rw [subLogDenseTwoWordSelectInterpretedCosted_refines]
                simp [data, hsuper, hlong, localSlot,
                  hlocal, hsparse]
  · simp [hvalid, Costed.pure]

/-- Trace-result packed-Clark select source with the packed sub-log dense branch. -/
def subLogPackedClarkSelectTraceResult
    (bits : List Bool) (target : Bool) (idx : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  let data := GenericSelect.sparseExceptionSelectData bits target
  let q := idx
  if idx < GenericSelect.occurrenceCount bits target then
    WordRAM.TraceResult.bind
      (data.superTable.readTraceResultRelabeled
        subLogSelectSuperTableTraceSegments
        (GenericSelect.selectSuperSlot q data.superStride)) fun super? =>
      match super? with
      | none => WordRAM.TraceResult.pure none
      | some super =>
          if GenericSelect.relativeSplitSelectEntryIsMarked super then
            WordRAM.TraceResult.bind
              (WordRAM.TraceResult.relabelReadSegmentsWith
                (WordRAM.tripleSegmentMap
                  subLogSelectLongFlagRankBase subLogSelectDeadSegment)
                (data.longFlagRankData.rankTraceResult true
                  (GenericSelect.selectSuperSlot q data.superStride)))
              fun exceptionRank =>
                GenericSelect.relativeOffsetReadTraceResultRelabeled
                  subLogSelectLongRelativeSegment subLogSelectDeadSegment
                  data.longSuperRelativeTable
                  (GenericSelect.relativeSplitSelectEntryBasePosition
                    data.wordSize super)
                  (GenericSelect.relativeSplitSelectLongCompactSlot
                    exceptionRank (q - super.baseOccurrence)
                    data.superStride)
          else
            let localSlot :=
              GenericSelect.relativeSplitSelectLocalSlot q data.superStride
                data.localSlotsPerSuper data.localStride super
            WordRAM.TraceResult.bind
              (data.localTable.readTraceResultRelabeled
                subLogSelectLocalTableTraceSegments localSlot) fun loc? =>
              match loc? with
              | none => WordRAM.TraceResult.pure none
              | some loc =>
                  if GenericSelect.relativeSplitSelectEntryIsMarked loc then
                    data.sparseDirectory.readTraceResultRelabeled
                      subLogSelectSparseDirectoryTraceSegments
                      (GenericSelect.relativeSplitSelectLocalBasePosition
                        data.wordSize super loc)
                      localSlot
                      (q -
                        GenericSelect.relativeSplitSelectLocalBaseOccurrence
                          super loc)
                  else
                    subLogDenseTwoWordSelectTraceResult target bits
                      (GenericSelect.relativeSplitSelectLocalBasePosition
                        data.wordSize super loc)
                      (GenericSelect.relativeSplitSelectLocalBaseOccurrence
                        super loc) q
  else
    WordRAM.TraceResult.pure none

set_option linter.unusedSimpArgs false in
theorem subLogPackedClarkSelectTraceResult_refines_interpretedCosted
    (bits : List Bool) (target : Bool) (idx : Nat) :
    (subLogPackedClarkSelectTraceResult bits target idx).toCosted =
      subLogPackedClarkSelectInterpretedCosted bits target idx := by
  unfold subLogPackedClarkSelectTraceResult
    subLogPackedClarkSelectInterpretedCosted
  let data := GenericSelect.sparseExceptionSelectData bits target
  by_cases hvalid : idx < GenericSelect.occurrenceCount bits target
  · simp [data, hvalid, WordRAM.TraceResult.bind_toCosted,
      data.superTable.readTraceResultRelabeled_refines_interpretedCosted
        subLogSelectSuperTableTraceSegments
        (GenericSelect.selectSuperSlot idx data.superStride)]
    cases hsuper :
        (data.superTable.readInterpretedCosted
          (GenericSelect.selectSuperSlot idx data.superStride)).value with
    | none =>
        simp [data, Costed.bind, Costed.pure, hsuper]
    | some super =>
        by_cases hlong :
            GenericSelect.relativeSplitSelectEntryIsMarked super = true
        · simp [data, Costed.bind, hsuper, hlong,
            WordRAM.TraceResult.bind_toCosted,
            WordRAM.TraceResult.relabelReadSegmentsWith_toCosted,
            data.longFlagRankData.rankTraceResult_refines_rankInterpretedCosted,
            GenericSelect.relativeOffsetReadTraceResultRelabeled_refines_interpretedCosted]
        · let localSlot :=
            GenericSelect.relativeSplitSelectLocalSlot idx data.superStride
              data.localSlotsPerSuper data.localStride super
          simp [data, Costed.bind, hsuper, hlong,
            WordRAM.TraceResult.bind_toCosted,
            localSlot,
            data.localTable.readTraceResultRelabeled_refines_interpretedCosted
              subLogSelectLocalTableTraceSegments localSlot]
          cases hlocal :
              (data.localTable.readInterpretedCosted localSlot).value with
          | none =>
              have hlocalTrace :=
                data.localTable.readTraceResultRelabeled_refines_interpretedCosted
                  subLogSelectLocalTableTraceSegments localSlot
              have hlocalTraceValue :
                  (data.localTable.readTraceResultRelabeled
                    subLogSelectLocalTableTraceSegments localSlot).value =
                    none := by
                have hv := congrArg Costed.value hlocalTrace
                simpa [WordRAM.TraceResult.toCosted, hlocal] using hv
              have hlocalTraceCost :
                  (data.localTable.readTraceResultRelabeled
                    subLogSelectLocalTableTraceSegments localSlot).trace.length =
                    (data.localTable.readInterpretedCosted localSlot).cost := by
                simpa [WordRAM.TraceResult.toCosted,
                  WordRAM.TraceResult.steps] using
                  congrArg Costed.cost hlocalTrace
              simp [data, Costed.pure, hlocalTraceValue,
                hlocalTraceCost]
          | some loc =>
              have hlocalTrace :=
                data.localTable.readTraceResultRelabeled_refines_interpretedCosted
                  subLogSelectLocalTableTraceSegments localSlot
              have hlocalTraceValue :
                  (data.localTable.readTraceResultRelabeled
                    subLogSelectLocalTableTraceSegments localSlot).value =
                    some loc := by
                have hv := congrArg Costed.value hlocalTrace
                simpa [WordRAM.TraceResult.toCosted, hlocal] using hv
              have hlocalTraceCost :
                  (data.localTable.readTraceResultRelabeled
                    subLogSelectLocalTableTraceSegments localSlot).trace.length =
                    (data.localTable.readInterpretedCosted localSlot).cost := by
                simpa [WordRAM.TraceResult.toCosted,
                  WordRAM.TraceResult.steps] using
                  congrArg Costed.cost hlocalTrace
              by_cases hsparse :
                  GenericSelect.relativeSplitSelectEntryIsMarked loc = true
              · simp [data, Costed.bind, hlocal, hsparse, localSlot,
                  hlocalTraceValue, hlocalTraceCost]
                have hchild :=
                  data.sparseDirectory.readTraceResultRelabeled_refines_interpretedCosted
                    subLogSelectSparseDirectoryTraceSegments
                    (GenericSelect.relativeSplitSelectLocalBasePosition
                      data.wordSize super loc)
                    (GenericSelect.relativeSplitSelectLocalSlot idx
                      data.superStride data.localSlotsPerSuper
                      data.localStride super)
                    (idx -
                      GenericSelect.relativeSplitSelectLocalBaseOccurrence
                        super loc)
                constructor
                · simpa [WordRAM.TraceResult.toCosted] using
                    congrArg Costed.value hchild
                · simpa [WordRAM.TraceResult.toCosted,
                    WordRAM.TraceResult.steps] using
                    congrArg Costed.cost hchild
              · simp [data, Costed.bind, hlocal, hsparse, localSlot,
                  hlocalTraceValue, hlocalTraceCost]
                have hchild :=
                  subLogDenseTwoWordSelectTraceResult_refines_interpretedCosted
                    target bits
                    (GenericSelect.relativeSplitSelectLocalBasePosition
                      data.wordSize super loc)
                    (GenericSelect.relativeSplitSelectLocalBaseOccurrence
                      super loc) idx
                constructor
                · simpa [WordRAM.TraceResult.toCosted] using
                    congrArg Costed.value hchild
                · simpa [WordRAM.TraceResult.toCosted,
                    WordRAM.TraceResult.steps] using
                    congrArg Costed.cost hchild
  · simp [data, hvalid, WordRAM.TraceResult.pure_toCosted, Costed.pure]

theorem subLogPackedClarkSelectTraceResult_matchesReadStore
    (bits : List Bool) (target : Bool) (idx : Nat) :
    forall event,
      event ∈ (subLogPackedClarkSelectTraceResult bits target idx).trace ->
        event.matchesReadStore
          (subLogSelectFromPackedClarkRouteTraceReadStore bits target) := by
  unfold subLogPackedClarkSelectTraceResult
  let data := GenericSelect.sparseExceptionSelectData bits target
  by_cases hvalid : idx < GenericSelect.occurrenceCount bits target
  · intro event hmem
    simp [hvalid, WordRAM.TraceResult.bind] at hmem
    rcases hmem with hmem | hmem
    · exact
        data.superTable.readTraceResultRelabeled_matchesReadStore
          subLogSelectSuperTableTraceSegments
          (subLogSelectFromPackedClarkRouteTraceReadStore bits target)
          (by
            intro segment index
            simpa [data] using
              subLogSelectTraceReadStore_super_baseOccurrence_read
                bits target segment index)
          (by
            intro segment index
            simpa [data] using
              subLogSelectTraceReadStore_super_baseWordIndex_read
                bits target segment index)
          (by
            intro segment index
            simpa [data] using
              subLogSelectTraceReadStore_super_rankBefore_read
                bits target segment index)
          (by
            intro segment index
            simpa [data] using
              subLogSelectTraceReadStore_super_firstOffset_read
                bits target segment index)
          (GenericSelect.selectSuperSlot idx data.superStride)
          event hmem
    · cases hsuperValue :
        (data.superTable.readTraceResultRelabeled
          subLogSelectSuperTableTraceSegments
          (GenericSelect.selectSuperSlot idx data.superStride)).value with
      | none =>
          simp [data, hsuperValue] at hmem
      | some super =>
          by_cases hlong :
              GenericSelect.relativeSplitSelectEntryIsMarked super = true
          · simp [data, hsuperValue, hlong] at hmem
            rcases hmem with hmem | hmem
            · have hmemRelabeled :
                  event ∈
                    (WordRAM.TraceResult.relabelReadSegmentsWith
                      (WordRAM.tripleSegmentMap
                        subLogSelectLongFlagRankBase
                        subLogSelectDeadSegment)
                      (data.longFlagRankData.rankTraceResult true
                        (GenericSelect.selectSuperSlot idx
                          data.superStride))).trace := by
                simpa [WordRAM.TraceResult.relabelReadSegmentsWith] using
                  (List.mem_map.mpr hmem)
              exact
                WordRAM.TraceResult.relabelReadSegmentsWith_matchesReadStore
                  (data.longFlagRankData.rankTraceResult true
                    (GenericSelect.selectSuperSlot idx data.superStride))
                  (WordRAM.ReadStore.ofStore
                    (data.longFlagRankData.rankRegisterWordRAMStore true))
                  (subLogSelectFromPackedClarkRouteTraceReadStore
                    bits target)
                  (WordRAM.tripleSegmentMap
                    subLogSelectLongFlagRankBase
                    subLogSelectDeadSegment)
                  (by
                    intro segment index
                    simpa [data, WordRAM.ReadStore.ofStore] using
                      subLogSelectTraceReadStore_longFlagRank_read
                        bits target segment index)
                  (data.longFlagRankData.rankTraceResult_matchesReadStore
                    true
                    (GenericSelect.selectSuperSlot idx data.superStride))
                  event hmemRelabeled
            · exact
                GenericSelect.relativeOffsetReadTraceResultRelabeled_matchesReadStore
                  subLogSelectLongRelativeSegment
                  subLogSelectDeadSegment
                  data.longSuperRelativeTable
                  (subLogSelectFromPackedClarkRouteTraceReadStore
                    bits target)
                  (by
                    intro segment index
                    simpa [data] using
                      subLogSelectTraceReadStore_longRelative_read
                        bits target segment index)
                  (GenericSelect.relativeSplitSelectEntryBasePosition
                    data.wordSize super)
                  (GenericSelect.relativeSplitSelectLongCompactSlot
                    (data.longFlagRankData.rankTraceResult true
                      (GenericSelect.selectSuperSlot idx
                        data.superStride)).value
                    (idx - super.baseOccurrence)
                    data.superStride)
                  event hmem
          · simp [data, hsuperValue, hlong] at hmem
            let localSlot :=
              GenericSelect.relativeSplitSelectLocalSlot idx
                data.superStride data.localSlotsPerSuper
                data.localStride super
            rcases hmem with hmem | hmem
            · exact
                data.localTable.readTraceResultRelabeled_matchesReadStore
                  subLogSelectLocalTableTraceSegments
                  (subLogSelectFromPackedClarkRouteTraceReadStore
                    bits target)
                  (by
                    intro segment index
                    simpa [data] using
                      subLogSelectTraceReadStore_local_baseOccurrence_read
                        bits target segment index)
                  (by
                    intro segment index
                    simpa [data] using
                      subLogSelectTraceReadStore_local_baseWordIndex_read
                        bits target segment index)
                  (by
                    intro segment index
                    simpa [data] using
                      subLogSelectTraceReadStore_local_rankBefore_read
                        bits target segment index)
                  (by
                    intro segment index
                    simpa [data] using
                      subLogSelectTraceReadStore_local_firstOffset_read
                        bits target segment index)
                  localSlot event hmem
            · cases hlocalValue :
                (data.localTable.readTraceResultRelabeled
                  subLogSelectLocalTableTraceSegments localSlot).value with
              | none =>
                  simp [data, hlocalValue, localSlot] at hmem
              | some loc =>
                  by_cases hsparse :
                      GenericSelect.relativeSplitSelectEntryIsMarked loc =
                        true
                  · exact
                      data.sparseDirectory.readTraceResultRelabeled_matchesReadStore
                        subLogSelectSparseDirectoryTraceSegments
                        (subLogSelectFromPackedClarkRouteTraceReadStore
                          bits target)
                        (by
                          intro segment index
                          simpa [data] using
                            subLogSelectTraceReadStore_sparseRank_read
                              bits target segment index)
                        (by
                          intro segment index
                          simpa [data] using
                            subLogSelectTraceReadStore_sparseRelative_read
                              bits target segment index)
                        (GenericSelect.relativeSplitSelectLocalBasePosition
                          data.wordSize super loc)
                        localSlot
                        (idx -
                          GenericSelect.relativeSplitSelectLocalBaseOccurrence
                            super loc)
                        event
                        (by
                          simpa [data, hlocalValue, hsparse, localSlot]
                            using hmem)
                  · exact
                      subLogDenseTwoWordSelectTraceResult_matchesReadStore
                        target bits
                        (GenericSelect.relativeSplitSelectLocalBasePosition
                          data.wordSize super loc)
                        (GenericSelect.relativeSplitSelectLocalBaseOccurrence
                          super loc)
                        idx event
                        (by
                          simpa [data, hlocalValue, hsparse, localSlot]
                            using hmem)
  · intro event hmem
    simp [hvalid] at hmem

/-- Interpreted packed-Clark route-field read. -/
def fixedWeightSubLogPackedClarkSelectRouteFieldsInterpretedCosted
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    Costed (Option FixedWeightSubLogClarkSelectRouteFields) :=
  Costed.map
    (fun pos? =>
      pos?.map
        (fixedWeightSubLogSelectRouteFieldsOfPosition
          bits target occurrence))
    (subLogPackedClarkSelectInterpretedCosted bits target occurrence)

theorem fixedWeightSubLogPackedClarkSelectRouteFieldsInterpretedCosted_refines
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    fixedWeightSubLogPackedClarkSelectRouteFieldsInterpretedCosted
        bits target occurrence =
      fixedWeightSubLogPackedClarkSelectRouteFieldsCosted
        bits target occurrence := by
  unfold fixedWeightSubLogPackedClarkSelectRouteFieldsInterpretedCosted
    fixedWeightSubLogPackedClarkSelectRouteFieldsCosted
  rw [subLogPackedClarkSelectInterpretedCosted_refines]

/-- Trace-result packed-Clark route-field read. -/
def fixedWeightSubLogPackedClarkSelectRouteFieldsTraceResult
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    WordRAM.TraceResult (Option FixedWeightSubLogClarkSelectRouteFields) :=
  WordRAM.TraceResult.map
    (fun pos? =>
      pos?.map
        (fixedWeightSubLogSelectRouteFieldsOfPosition
          bits target occurrence))
    (subLogPackedClarkSelectTraceResult bits target occurrence)

theorem fixedWeightSubLogPackedClarkSelectRouteFieldsTraceResult_refines_interpretedCosted
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    (fixedWeightSubLogPackedClarkSelectRouteFieldsTraceResult
      bits target occurrence).toCosted =
        fixedWeightSubLogPackedClarkSelectRouteFieldsInterpretedCosted
          bits target occurrence := by
  simp [fixedWeightSubLogPackedClarkSelectRouteFieldsTraceResult,
    fixedWeightSubLogPackedClarkSelectRouteFieldsInterpretedCosted,
    subLogPackedClarkSelectTraceResult_refines_interpretedCosted,
    WordRAM.TraceResult.map_toCosted, Costed.map]

theorem fixedWeightSubLogPackedClarkSelectRouteFieldsTraceResult_matchesReadStore
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    forall event,
      event ∈
          (fixedWeightSubLogPackedClarkSelectRouteFieldsTraceResult
            bits target occurrence).trace ->
        event.matchesReadStore
          (subLogSelectFromPackedClarkRouteTraceReadStore bits target) := by
  unfold fixedWeightSubLogPackedClarkSelectRouteFieldsTraceResult
  apply WordRAM.TraceResult.map_trace_forall
  exact subLogPackedClarkSelectTraceResult_matchesReadStore
    bits target occurrence

/-- Interpreted select query for the public packed-Clark compressed/FID path. -/
def subLogSelectFromPackedClarkRouteInterpretedCosted
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    Costed (Option Nat) :=
  Costed.bind
    (fixedWeightSubLogPackedClarkSelectRouteFieldsInterpretedCosted
      bits target occurrence)
    fun fields? =>
      match fields? with
      | none => Costed.pure none
      | some fields =>
          subLogSelectWithFieldsInterpretedCosted bits target fields

theorem subLogSelectFromPackedClarkRouteInterpretedCosted_refines
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    subLogSelectFromPackedClarkRouteInterpretedCosted bits target occurrence =
      subLogSelectFromPackedClarkRouteCosted bits target occurrence := by
  unfold subLogSelectFromPackedClarkRouteInterpretedCosted
    subLogSelectFromPackedClarkRouteCosted
  rw [fixedWeightSubLogPackedClarkSelectRouteFieldsInterpretedCosted_refines]
  cases hfields :
      (fixedWeightSubLogPackedClarkSelectRouteFieldsCosted
        bits target occurrence).value with
  | none =>
      simp [Costed.bind, Costed.pure, hfields]
  | some fields =>
      simp [Costed.bind, hfields]
      rw [subLogSelectWithFieldsInterpretedCosted_refines]
      exact ⟨rfl, rfl⟩

/-- Trace-result select query for the public packed-Clark compressed/FID path. -/
def subLogSelectFromPackedClarkRouteTraceResult
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  WordRAM.TraceResult.bind
    (fixedWeightSubLogPackedClarkSelectRouteFieldsTraceResult
      bits target occurrence)
    fun fields? =>
      match fields? with
      | none => WordRAM.TraceResult.pure none
      | some fields =>
          subLogSelectWithFieldsTraceResult bits target fields

theorem subLogSelectFromPackedClarkRouteTraceResult_refines_interpretedCosted
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    (subLogSelectFromPackedClarkRouteTraceResult
      bits target occurrence).toCosted =
        subLogSelectFromPackedClarkRouteInterpretedCosted
          bits target occurrence := by
  unfold subLogSelectFromPackedClarkRouteTraceResult
    subLogSelectFromPackedClarkRouteInterpretedCosted
  rw [WordRAM.TraceResult.bind_toCosted]
  rw [fixedWeightSubLogPackedClarkSelectRouteFieldsTraceResult_refines_interpretedCosted]
  cases hfields :
      (fixedWeightSubLogPackedClarkSelectRouteFieldsInterpretedCosted
        bits target occurrence).value with
  | none =>
      simp [Costed.bind, Costed.pure, hfields,
        WordRAM.TraceResult.pure_toCosted]
  | some fields =>
      simp [Costed.bind, hfields]
      have hchild :=
        subLogSelectWithFieldsTraceResult_refines_interpretedCosted
          bits target fields
      constructor
      · simpa [WordRAM.TraceResult.toCosted] using
          congrArg Costed.value hchild
      · simpa [WordRAM.TraceResult.toCosted,
          WordRAM.TraceResult.steps] using
          congrArg Costed.cost hchild

theorem subLogSelectFromPackedClarkRouteTraceResult_matchesReadStore
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    forall event,
      event ∈
          (subLogSelectFromPackedClarkRouteTraceResult
            bits target occurrence).trace ->
        event.matchesReadStore
          (subLogSelectFromPackedClarkRouteTraceReadStore bits target) := by
  unfold subLogSelectFromPackedClarkRouteTraceResult
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      fixedWeightSubLogPackedClarkSelectRouteFieldsTraceResult_matchesReadStore
        bits target occurrence
  · cases hfields :
      (fixedWeightSubLogPackedClarkSelectRouteFieldsTraceResult
        bits target occurrence).value with
    | none =>
        simp
    | some fields =>
        simpa [hfields] using
          subLogSelectWithFieldsTraceResult_matchesReadStore
            bits target fields

theorem subLogSelectFromPackedClarkRouteTraceResult_event_read_or_primitive
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    forall event,
      event ∈
          (subLogSelectFromPackedClarkRouteTraceResult
            bits target occurrence).trace ->
        event.isReadWord \/ event.isWordPrimitive := by
  intro event _hmem
  exact WordRAM.TraceEvent.isReadWord_or_isWordPrimitive event

/--
Execution-story packet for the select leg of the compressed/FID sub-log path.

The trace first reads the charged packed-Clark route directory, then performs
the constant local fixed-weight block decode through code/length/class/shared
decoder payload reads.
-/
theorem subLogSelectFromPackedClarkRouteTraceResult_execution_story
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    (subLogSelectFromPackedClarkRouteTraceResult
      bits target occurrence).toCosted =
        subLogSelectFromPackedClarkRouteInterpretedCosted
          bits target occurrence /\
      (subLogSelectFromPackedClarkRouteTraceResult
        bits target occurrence).toCosted =
        subLogSelectFromPackedClarkRouteCosted bits target occurrence /\
      (forall event,
        event ∈
            (subLogSelectFromPackedClarkRouteTraceResult
              bits target occurrence).trace ->
          event.isReadWord \/ event.isWordPrimitive) /\
      (forall event,
        event ∈
            (subLogSelectFromPackedClarkRouteTraceResult
              bits target occurrence).trace ->
          event.matchesReadStore
            (subLogSelectFromPackedClarkRouteTraceReadStore bits target)) := by
  constructor
  · exact
      subLogSelectFromPackedClarkRouteTraceResult_refines_interpretedCosted
        bits target occurrence
  constructor
  · rw [subLogSelectFromPackedClarkRouteTraceResult_refines_interpretedCosted,
      subLogSelectFromPackedClarkRouteInterpretedCosted_refines]
  constructor
  · exact
      subLogSelectFromPackedClarkRouteTraceResult_event_read_or_primitive
        bits target occurrence
  · exact
      subLogSelectFromPackedClarkRouteTraceResult_matchesReadStore
        bits target occurrence

/-! ### Combined global payload-store replay -/

def subLogCompressedFIDGlobalAccessSegmentMap : Nat -> Nat
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | _ + 4 => 31

def subLogCompressedFIDGlobalRankSegmentMap : Nat -> Nat
  | 0 => 32
  | 1 => 33
  | 2 => 34
  | 3 => 35
  | 4 => 36
  | 5 => 37
  | _ + 6 => 63

def subLogCompressedFIDGlobalSelectSegmentMap : Nat -> Nat
  | 0 => 64
  | 1 => 65
  | 2 => 66
  | 3 => 67
  | 4 => 68
  | 5 => 69
  | 6 => 70
  | 7 => 71
  | 8 => 72
  | 9 => 73
  | 10 => 74
  | 11 => 75
  | 12 => 76
  | 13 => 77
  | 14 => 78
  | 15 => 79
  | 16 => 80
  | 17 => 81
  | 18 => 82
  | 19 => 83
  | _ + 20 => 95

/--
One target-indexed global store for the compressed/FID trace packets.

The access, rank, and select trace packets are relabeled into disjoint segment
ranges of this store.  The store is target-indexed because the current rank and
Clark-select routing payloads are target-specific; a target-independent packet
can be obtained later by duplicating the true/false target ranges.
-/
def subLogCompressedFIDTargetGlobalTraceReadStore
    (bits : List Bool) (target : Bool) : WordRAM.ReadStore where
  readWord? segment index :=
    match segment with
    | 0 => (subLogAccessTraceReadStore bits).readWord? 0 index
    | 1 => (subLogAccessTraceReadStore bits).readWord? 1 index
    | 2 => (subLogAccessTraceReadStore bits).readWord? 2 index
    | 3 => (subLogAccessTraceReadStore bits).readWord? 3 index
    | 31 => none
    | 32 => (subLogRankTraceReadStore bits target).readWord? 0 index
    | 33 => (subLogRankTraceReadStore bits target).readWord? 1 index
    | 34 => (subLogRankTraceReadStore bits target).readWord? 2 index
    | 35 => (subLogRankTraceReadStore bits target).readWord? 3 index
    | 36 => (subLogRankTraceReadStore bits target).readWord? 4 index
    | 37 => (subLogRankTraceReadStore bits target).readWord? 5 index
    | 63 => none
    | 64 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits target).readWord? 0 index
    | 65 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits target).readWord? 1 index
    | 66 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits target).readWord? 2 index
    | 67 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits target).readWord? 3 index
    | 68 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits target).readWord? 4 index
    | 69 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits target).readWord? 5 index
    | 70 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits target).readWord? 6 index
    | 71 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits target).readWord? 7 index
    | 72 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits target).readWord? 8 index
    | 73 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits target).readWord? 9 index
    | 74 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits target).readWord? 10 index
    | 75 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits target).readWord? 11 index
    | 76 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits target).readWord? 12 index
    | 77 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits target).readWord? 13 index
    | 78 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits target).readWord? 14 index
    | 79 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits target).readWord? 15 index
    | 80 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits target).readWord? 16 index
    | 81 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits target).readWord? 17 index
    | 82 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits target).readWord? 18 index
    | 83 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits target).readWord? 19 index
    | 95 => none
    | _ => none

private theorem subLogCompressedFIDTargetGlobalTraceReadStore_access_read
    (bits : List Bool) (target : Bool) :
    forall segment index,
      (subLogCompressedFIDTargetGlobalTraceReadStore bits target).readWord?
          (subLogCompressedFIDGlobalAccessSegmentMap segment) index =
        (subLogAccessTraceReadStore bits).readWord? segment index := by
  intro segment index
  match segment with
  | 0 =>
      simp [subLogCompressedFIDTargetGlobalTraceReadStore,
        subLogCompressedFIDGlobalAccessSegmentMap]
  | 1 =>
      simp [subLogCompressedFIDTargetGlobalTraceReadStore,
        subLogCompressedFIDGlobalAccessSegmentMap]
  | 2 =>
      simp [subLogCompressedFIDTargetGlobalTraceReadStore,
        subLogCompressedFIDGlobalAccessSegmentMap]
  | 3 =>
      simp [subLogCompressedFIDTargetGlobalTraceReadStore,
        subLogCompressedFIDGlobalAccessSegmentMap]
  | _ + 4 =>
      simp [subLogCompressedFIDTargetGlobalTraceReadStore,
        subLogCompressedFIDGlobalAccessSegmentMap,
        subLogAccessTraceReadStore]

private theorem subLogCompressedFIDTargetGlobalTraceReadStore_rank_read
    (bits : List Bool) (target : Bool) :
    forall segment index,
      (subLogCompressedFIDTargetGlobalTraceReadStore bits target).readWord?
          (subLogCompressedFIDGlobalRankSegmentMap segment) index =
        (subLogRankTraceReadStore bits target).readWord? segment index := by
  intro segment index
  match segment with
  | 0 =>
      simp [subLogCompressedFIDTargetGlobalTraceReadStore,
        subLogCompressedFIDGlobalRankSegmentMap]
  | 1 =>
      simp [subLogCompressedFIDTargetGlobalTraceReadStore,
        subLogCompressedFIDGlobalRankSegmentMap]
  | 2 =>
      simp [subLogCompressedFIDTargetGlobalTraceReadStore,
        subLogCompressedFIDGlobalRankSegmentMap]
  | 3 =>
      simp [subLogCompressedFIDTargetGlobalTraceReadStore,
        subLogCompressedFIDGlobalRankSegmentMap]
  | 4 =>
      simp [subLogCompressedFIDTargetGlobalTraceReadStore,
        subLogCompressedFIDGlobalRankSegmentMap]
  | 5 =>
      simp [subLogCompressedFIDTargetGlobalTraceReadStore,
        subLogCompressedFIDGlobalRankSegmentMap]
  | _ + 6 =>
      simp [subLogCompressedFIDTargetGlobalTraceReadStore,
        subLogCompressedFIDGlobalRankSegmentMap,
        subLogRankTraceReadStore]

private theorem subLogCompressedFIDTargetGlobalTraceReadStore_select_read
    (bits : List Bool) (target : Bool) :
    forall segment index,
      (subLogCompressedFIDTargetGlobalTraceReadStore bits target).readWord?
          (subLogCompressedFIDGlobalSelectSegmentMap segment) index =
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits target).readWord? segment index := by
  intro segment index
  match segment with
  | 0 =>
      rfl
  | 1 =>
      rfl
  | 2 =>
      rfl
  | 3 =>
      rfl
  | 4 =>
      rfl
  | 5 =>
      rfl
  | 6 =>
      rfl
  | 7 =>
      rfl
  | 8 =>
      rfl
  | 9 =>
      rfl
  | 10 =>
      rfl
  | 11 =>
      rfl
  | 12 =>
      rfl
  | 13 =>
      rfl
  | 14 =>
      rfl
  | 15 =>
      rfl
  | 16 =>
      rfl
  | 17 =>
      rfl
  | 18 =>
      rfl
  | 19 =>
      rfl
  | _ + 20 =>
      rfl

def subLogCompressedFIDGlobalAccessTraceResult
    (bits : List Bool) (i : Nat) : WordRAM.TraceResult (Option Bool) :=
  WordRAM.TraceResult.relabelReadSegmentsWith
    subLogCompressedFIDGlobalAccessSegmentMap
    (subLogAccessTraceResult bits i)

def subLogCompressedFIDGlobalRankTraceResult
    (bits : List Bool) (target : Bool) (pos : Nat) :
    WordRAM.TraceResult Nat :=
  WordRAM.TraceResult.relabelReadSegmentsWith
    subLogCompressedFIDGlobalRankSegmentMap
    (subLogRankTraceResult bits target pos)

def subLogCompressedFIDGlobalSelectTraceResult
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  WordRAM.TraceResult.relabelReadSegmentsWith
    subLogCompressedFIDGlobalSelectSegmentMap
    (subLogSelectFromPackedClarkRouteTraceResult bits target occurrence)

theorem subLogCompressedFIDTargetGlobalPayloadStore_execution_story
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
              (subLogCompressedFIDTargetGlobalTraceReadStore bits target))) /\
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
                  bits target))) /\
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
                  bits target)) := by
  constructor
  · intro i
    constructor
    · simp [subLogCompressedFIDGlobalAccessTraceResult,
        subLogAccessTraceResult_refines_interpretedCosted]
    constructor
    · simp [subLogCompressedFIDGlobalAccessTraceResult,
        subLogAccessTraceResult_refines_interpretedCosted,
        subLogAccessInterpretedCosted_refines_subLogAccessCosted]
    constructor
    · intro event _hmem
      exact WordRAM.TraceEvent.isReadWord_or_isWordPrimitive event
    · exact
        WordRAM.TraceResult.relabelReadSegmentsWith_matchesReadStore
          (subLogAccessTraceResult bits i)
          (subLogAccessTraceReadStore bits)
          (subLogCompressedFIDTargetGlobalTraceReadStore bits target)
          subLogCompressedFIDGlobalAccessSegmentMap
          (subLogCompressedFIDTargetGlobalTraceReadStore_access_read
            bits target)
          (subLogAccessTraceResult_matchesReadStore bits i)
  constructor
  · intro pos
    constructor
    · simp [subLogCompressedFIDGlobalRankTraceResult,
        subLogRankTraceResult_refines_interpretedCosted]
    constructor
    · simp [subLogCompressedFIDGlobalRankTraceResult,
        subLogRankTraceResult_refines_interpretedCosted,
        subLogRankInterpretedCosted_refines_subLogRankCosted]
    constructor
    · intro event _hmem
      exact WordRAM.TraceEvent.isReadWord_or_isWordPrimitive event
    · exact
        WordRAM.TraceResult.relabelReadSegmentsWith_matchesReadStore
          (subLogRankTraceResult bits target pos)
          (subLogRankTraceReadStore bits target)
          (subLogCompressedFIDTargetGlobalTraceReadStore bits target)
          subLogCompressedFIDGlobalRankSegmentMap
          (subLogCompressedFIDTargetGlobalTraceReadStore_rank_read
            bits target)
          (subLogRankTraceResult_matchesReadStore bits target pos)
  · intro occurrence
    constructor
    · simp [subLogCompressedFIDGlobalSelectTraceResult,
        subLogSelectFromPackedClarkRouteTraceResult_refines_interpretedCosted]
    constructor
    · simp [subLogCompressedFIDGlobalSelectTraceResult,
        subLogSelectFromPackedClarkRouteTraceResult_refines_interpretedCosted,
        subLogSelectFromPackedClarkRouteInterpretedCosted_refines]
    constructor
    · intro event _hmem
      exact WordRAM.TraceEvent.isReadWord_or_isWordPrimitive event
    · exact
        WordRAM.TraceResult.relabelReadSegmentsWith_matchesReadStore
          (subLogSelectFromPackedClarkRouteTraceResult
            bits target occurrence)
          (subLogSelectFromPackedClarkRouteTraceReadStore bits target)
          (subLogCompressedFIDTargetGlobalTraceReadStore bits target)
          subLogCompressedFIDGlobalSelectSegmentMap
          (subLogCompressedFIDTargetGlobalTraceReadStore_select_read
            bits target)
          (subLogSelectFromPackedClarkRouteTraceResult_matchesReadStore
            bits target occurrence)

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
