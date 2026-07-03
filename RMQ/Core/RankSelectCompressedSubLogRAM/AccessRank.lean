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


end RankSelectSpec

end RMQ
