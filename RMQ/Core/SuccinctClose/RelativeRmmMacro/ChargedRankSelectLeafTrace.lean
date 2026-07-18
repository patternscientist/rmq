import RMQ.Core.SuccinctClose.RelativeRmmMacro.ChargedRankSelectTrace
import RMQ.Core.GenericSelect.RAMStoreParam

/-!
# Charged chunked rank/select leaves: Word-RAM trace layer (B3 M4b)

Store-parametric (`WithStore`) trace twins of the four charged chunked
Costed leaves of `ChargedRankSelectLeaves.lean`, mirroring the accepted
route's trace evaluators (`rankTraceResult`, `denseTwoWordSelectTraceResult`,
`SparseExceptionDirectory.readTraceResult*`,
`SparseExceptionSelectData.selectTraceResult*` and their `WithStore` twins)
with every `wordRank`/`wordSelect` emission replaced by the charged chunk
folds of `ChargedRankSelectTrace.lean`.

The register-program presentation of the two-level rank seed is retired at
these leaves only: the three accepted sample/word reads are emitted directly
as `readWord` events of the supplied store (`bpChunkReadTraceResult` for the
decoded sample reads, the new `bpWordReadTraceResult` for the raw packed-word
read), followed by the segment-parameterized chunk-table rank fold.  Every
event of every twin is therefore a genuine `readWord` of the supplied store.

Surface per twin, in the M4a style:

* `_toCosted_of_agree` — under per-segment agreement with the honest
  component stores/tables, the trace twin's `Costed` projection is exactly
  the M3 chunked Costed twin;
* `_trace_forall` — parameterized event induction (chunk-table reads carry
  the row-count address bound; select-table reads additionally get an
  `_of_honestRank` bounded variant);
* `_matchesReadStore` / `_no_syntheticCostOnlyPrimitive`;
* `_store_parametric` — stores agreeing on the twin's segments produce the
  same value and trace.
-/

namespace RMQ

namespace SuccinctClose

/-! ## One raw payload-word read against a supplied store -/

/--
One charged raw payload-word read at a global segment: the emitted event
records the supplied store's word at that address, and the returned value is
that word itself (no decode) — the packed BP-code word read of the accepted
rank seed generalized to a supplied store.
-/
def bpWordReadTraceResult (store : WordRAM.ReadStore)
    (segment i : Nat) : WordRAM.TraceResult (Option (List Bool)) where
  value := store.readWord? segment i
  trace :=
    [WordRAM.TraceEvent.readWord segment i (store.readWord? segment i)]

theorem bpWordReadTraceResult_toCosted_of_agree
    {payload : List Bool}
    (pstore : SuccinctSpace.PayloadWordStore payload)
    {store : WordRAM.ReadStore} {segment : Nat}
    (hagree :
      forall address,
        store.readWord? segment address = pstore.words[address]?)
    (i : Nat) :
    (bpWordReadTraceResult store segment i).toCosted =
      pstore.readWordCosted i := by
  apply Costed.ext
  · show store.readWord? segment i = (pstore.readWordCosted i).value
    rw [hagree i]
    rfl
  · show (1 : Nat) = (pstore.readWordCosted i).cost
    simp

theorem bpWordReadTraceResult_trace_forall
    (store : WordRAM.ReadStore) (segment i : Nat)
    (P : WordRAM.TraceEvent -> Prop)
    (hread :
      P (WordRAM.TraceEvent.readWord segment i
        (store.readWord? segment i))) :
    forall event,
      List.Mem event (bpWordReadTraceResult store segment i).trace ->
        P event := by
  intro event hmem
  cases hmem with
  | head => exact hread
  | tail _ hmem' => cases hmem'

theorem bpWordReadTraceResult_matchesReadStore
    (store : WordRAM.ReadStore) (segment i : Nat) :
    forall event,
      List.Mem event (bpWordReadTraceResult store segment i).trace ->
        event.matchesReadStore store := by
  apply bpWordReadTraceResult_trace_forall
  rfl

theorem bpWordReadTraceResult_no_syntheticCostOnlyPrimitive
    (store : WordRAM.ReadStore) (segment i : Nat) :
    forall event,
      List.Mem event (bpWordReadTraceResult store segment i).trace ->
        Not event.isSyntheticCostOnlyPrimitive := by
  apply bpWordReadTraceResult_trace_forall
  simp [WordRAM.TraceEvent.isSyntheticCostOnlyPrimitive]

theorem bpWordReadTraceResult_store_parametric
    {storeA storeB : WordRAM.ReadStore} {segment : Nat}
    (hread :
      forall address,
        storeA.readWord? segment address =
          storeB.readWord? segment address)
    (i : Nat) :
    bpWordReadTraceResult storeA segment i =
      bpWordReadTraceResult storeB segment i := by
  unfold bpWordReadTraceResult
  rw [hread i]

/-! ## General event induction for the two-segment select fold -/

/--
General (unbounded select-address) event induction for the charged in-word
select fold at two segments, packaged at the `AtSegments` level.
-/
theorem bpChunkedWordSelectTraceResultAtSegmentsWithStore_trace_forall
    (store : WordRAM.ReadStore) (rankSegment selectSegment c : Nat)
    (target : Bool) (word : List Bool) (occurrence : Nat)
    (P : WordRAM.TraceEvent -> Prop)
    (hrank :
      forall address,
        address < bpFringeChunkRowCount c ->
        P (WordRAM.TraceEvent.readWord rankSegment address
          (store.readWord? rankSegment address)))
    (hsel :
      forall address,
        P (WordRAM.TraceEvent.readWord selectSegment address
          (store.readWord? selectSegment address))) :
    forall event,
      List.Mem event
          (bpChunkedWordSelectTraceResultAtSegmentsWithStore store
            rankSegment selectSegment c target word occurrence).trace ->
        P event := by
  exact
    bpChunkedWordSelectTraceFromWithStore_trace_forall store rankSegment
      selectSegment c target word P hrank hsel _ 0 occurrence

end SuccinctClose

/-! ## Chunked two-level rank seed as a supplied-store trace -/

namespace SuccinctRank

namespace TwoLevelPayloadLiveStoredWordRankData

/--
Store-parametric trace twin of `bpChunkedRankCosted`: the three accepted
sample/word reads are emitted as direct `readWord` events of the supplied
store at the caller's segments, and the trailing in-word rank is the charged
chunk-table fold at `chunkSegment`.
-/
def bpChunkedRankTraceResultWithStore
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordRankData
        bits superOverhead blockOverhead queryCost)
    (store : WordRAM.ReadStore)
    (superSegment blockSegment wordSegment chunkSegment c : Nat)
    (target : Bool) (pos : Nat) : WordRAM.TraceResult Nat :=
  WordRAM.TraceResult.bind
    (SuccinctClose.bpChunkReadTraceResult store superSegment
      (data.superIndex pos))
    fun super? =>
      WordRAM.TraceResult.bind
        (SuccinctClose.bpChunkReadTraceResult store blockSegment
          (data.wordIndex pos))
        fun delta? =>
          WordRAM.TraceResult.bind
            (SuccinctClose.bpWordReadTraceResult store wordSegment
              (data.wordIndex pos))
            fun word? =>
              match super?, delta?, word? with
              | some super, some delta, some word =>
                  WordRAM.TraceResult.map
                    (fun localRank => super + delta + localRank)
                    (SuccinctClose.bpChunkedWordRankTraceResultAtSegmentWithStore
                      store chunkSegment c target word
                      (data.wordOffset pos))
              | _, _, _ => WordRAM.TraceResult.pure 0

/--
Refinement under per-segment agreement with the accepted sample tables, the
packed word store, and the honest chunk table: the trace twin's `Costed`
projection is exactly the M3 chunked rank seed.
-/
theorem bpChunkedRankTraceResultWithStore_toCosted_of_agree
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordRankData
        bits superOverhead blockOverhead queryCost)
    {store : WordRAM.ReadStore}
    {superSegment blockSegment wordSegment chunkSegment c : Nat}
    {target : Bool}
    (hsuper :
      forall address,
        store.readWord? superSegment address =
          (data.superSampleWords target)[address]?)
    (hblock :
      forall address,
        store.readWord? blockSegment address =
          (data.blockSampleWords target)[address]?)
    (hword :
      forall address,
        store.readWord? wordSegment address =
          data.bitWords.store.words[address]?)
    (hchunk :
      forall address,
        store.readWord? chunkSegment address =
          (SuccinctClose.bpFringeChunkTable c).store.words[address]?)
    (pos : Nat) :
    (data.bpChunkedRankTraceResultWithStore store superSegment
        blockSegment wordSegment chunkSegment c target pos).toCosted =
      data.bpChunkedRankCosted c target pos := by
  cases target with
  | false =>
      have hsuper' :
          forall address,
            store.readWord? superSegment address =
              data.superTables.falseTable.store.words[address]? := hsuper
      have hblock' :
          forall address,
            store.readWord? blockSegment address =
              data.blockTables.falseTable.store.words[address]? := hblock
      unfold bpChunkedRankTraceResultWithStore bpChunkedRankCosted
      rw [WordRAM.TraceResult.bind_toCosted,
        SuccinctClose.bpChunkReadTraceResult_toCosted_of_agree
          data.superTables.falseTable hsuper']
      show
        Costed.bind
            (data.superTables.falseTable.readCosted (data.superIndex pos))
            _ =
          Costed.bind
            (data.superTables.falseTable.readCosted (data.superIndex pos))
            _
      congr 1
      funext super?
      rw [WordRAM.TraceResult.bind_toCosted,
        SuccinctClose.bpChunkReadTraceResult_toCosted_of_agree
          data.blockTables.falseTable hblock']
      show
        Costed.bind
            (data.blockTables.falseTable.readCosted (data.wordIndex pos))
            _ =
          Costed.bind
            (data.blockTables.falseTable.readCosted (data.wordIndex pos))
            _
      congr 1
      funext delta?
      rw [WordRAM.TraceResult.bind_toCosted,
        SuccinctClose.bpWordReadTraceResult_toCosted_of_agree
          data.bitWords.store hword]
      congr 1
      funext word?
      cases super? <;> cases delta? <;> cases word? <;>
        first
          | rfl
          | rw [WordRAM.TraceResult.map_toCosted,
              SuccinctClose.bpChunkedWordRankTraceResultAtSegmentWithStore_toCosted_of_agree
                (SuccinctClose.bpFringeChunkTable c) hchunk]
  | true =>
      have hsuper' :
          forall address,
            store.readWord? superSegment address =
              data.superTables.trueTable.store.words[address]? := hsuper
      have hblock' :
          forall address,
            store.readWord? blockSegment address =
              data.blockTables.trueTable.store.words[address]? := hblock
      unfold bpChunkedRankTraceResultWithStore bpChunkedRankCosted
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
        SuccinctClose.bpWordReadTraceResult_toCosted_of_agree
          data.bitWords.store hword]
      congr 1
      funext word?
      cases super? <;> cases delta? <;> cases word? <;>
        first
          | rfl
          | rw [WordRAM.TraceResult.map_toCosted,
              SuccinctClose.bpChunkedWordRankTraceResultAtSegmentWithStore_toCosted_of_agree
                (SuccinctClose.bpFringeChunkTable c) hchunk]

/--
Every event of the chunked rank seed is a `readWord` of the supplied store
at one of the three sample/word segments or a row-count-bounded slot of the
chunk-table segment.
-/
theorem bpChunkedRankTraceResultWithStore_trace_forall
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordRankData
        bits superOverhead blockOverhead queryCost)
    (store : WordRAM.ReadStore)
    (superSegment blockSegment wordSegment chunkSegment c : Nat)
    (target : Bool) (pos : Nat)
    (P : WordRAM.TraceEvent -> Prop)
    (hsuper :
      forall address,
        P (WordRAM.TraceEvent.readWord superSegment address
          (store.readWord? superSegment address)))
    (hblock :
      forall address,
        P (WordRAM.TraceEvent.readWord blockSegment address
          (store.readWord? blockSegment address)))
    (hword :
      forall address,
        P (WordRAM.TraceEvent.readWord wordSegment address
          (store.readWord? wordSegment address)))
    (hchunk :
      forall address,
        address < SuccinctClose.bpFringeChunkRowCount c ->
        P (WordRAM.TraceEvent.readWord chunkSegment address
          (store.readWord? chunkSegment address))) :
    forall event,
      List.Mem event
          (data.bpChunkedRankTraceResultWithStore store superSegment
            blockSegment wordSegment chunkSegment c target pos).trace ->
        P event := by
  unfold bpChunkedRankTraceResultWithStore
  apply WordRAM.TraceResult.bind_trace_forall
  · apply SuccinctClose.bpChunkReadTraceResult_trace_forall
    exact hsuper _
  · apply WordRAM.TraceResult.bind_trace_forall
    · apply SuccinctClose.bpChunkReadTraceResult_trace_forall
      exact hblock _
    · apply WordRAM.TraceResult.bind_trace_forall
      · apply SuccinctClose.bpWordReadTraceResult_trace_forall
        exact hword _
      · cases hsv :
            (SuccinctClose.bpChunkReadTraceResult store superSegment
              (data.superIndex pos)).value with
        | none =>
            cases hbv :
                (SuccinctClose.bpChunkReadTraceResult store blockSegment
                  (data.wordIndex pos)).value <;>
              cases hwv :
                (SuccinctClose.bpWordReadTraceResult store wordSegment
                  (data.wordIndex pos)).value <;>
              exact WordRAM.TraceResult.pure_trace_forall P 0
        | some super =>
            cases hbv :
                (SuccinctClose.bpChunkReadTraceResult store blockSegment
                  (data.wordIndex pos)).value with
            | none =>
                cases hwv :
                    (SuccinctClose.bpWordReadTraceResult store wordSegment
                      (data.wordIndex pos)).value <;>
                  exact WordRAM.TraceResult.pure_trace_forall P 0
            | some delta =>
                cases hwv :
                    (SuccinctClose.bpWordReadTraceResult store wordSegment
                      (data.wordIndex pos)).value with
                | none => exact WordRAM.TraceResult.pure_trace_forall P 0
                | some word =>
                    apply WordRAM.TraceResult.map_trace_forall
                    apply
                      SuccinctClose.bpChunkedWordRankTraceResultAtSegmentWithStore_trace_forall
                    exact hchunk

theorem bpChunkedRankTraceResultWithStore_matchesReadStore
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordRankData
        bits superOverhead blockOverhead queryCost)
    (store : WordRAM.ReadStore)
    (superSegment blockSegment wordSegment chunkSegment c : Nat)
    (target : Bool) (pos : Nat) :
    forall event,
      List.Mem event
          (data.bpChunkedRankTraceResultWithStore store superSegment
            blockSegment wordSegment chunkSegment c target pos).trace ->
        event.matchesReadStore store := by
  apply data.bpChunkedRankTraceResultWithStore_trace_forall
  · intro address
    rfl
  · intro address
    rfl
  · intro address
    rfl
  · intro address _hlt
    rfl

theorem bpChunkedRankTraceResultWithStore_no_syntheticCostOnlyPrimitive
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordRankData
        bits superOverhead blockOverhead queryCost)
    (store : WordRAM.ReadStore)
    (superSegment blockSegment wordSegment chunkSegment c : Nat)
    (target : Bool) (pos : Nat) :
    forall event,
      List.Mem event
          (data.bpChunkedRankTraceResultWithStore store superSegment
            blockSegment wordSegment chunkSegment c target pos).trace ->
        Not event.isSyntheticCostOnlyPrimitive := by
  apply data.bpChunkedRankTraceResultWithStore_trace_forall
  · intro address
    simp [WordRAM.TraceEvent.isSyntheticCostOnlyPrimitive]
  · intro address
    simp [WordRAM.TraceEvent.isSyntheticCostOnlyPrimitive]
  · intro address
    simp [WordRAM.TraceEvent.isSyntheticCostOnlyPrimitive]
  · intro address _hlt
    simp [WordRAM.TraceEvent.isSyntheticCostOnlyPrimitive]

theorem bpChunkedRankTraceResultWithStore_store_parametric
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordRankData
        bits superOverhead blockOverhead queryCost)
    {storeA storeB : WordRAM.ReadStore}
    {superSegment blockSegment wordSegment chunkSegment : Nat}
    (hsuper :
      forall address,
        storeA.readWord? superSegment address =
          storeB.readWord? superSegment address)
    (hblock :
      forall address,
        storeA.readWord? blockSegment address =
          storeB.readWord? blockSegment address)
    (hword :
      forall address,
        storeA.readWord? wordSegment address =
          storeB.readWord? wordSegment address)
    (hchunk :
      forall address,
        storeA.readWord? chunkSegment address =
          storeB.readWord? chunkSegment address)
    (c : Nat) (target : Bool) (pos : Nat) :
    data.bpChunkedRankTraceResultWithStore storeA superSegment
        blockSegment wordSegment chunkSegment c target pos =
      data.bpChunkedRankTraceResultWithStore storeB superSegment
        blockSegment wordSegment chunkSegment c target pos := by
  unfold bpChunkedRankTraceResultWithStore
  rw [SuccinctClose.bpChunkReadTraceResult_store_parametric hsuper]
  congr 1
  funext super?
  rw [SuccinctClose.bpChunkReadTraceResult_store_parametric hblock]
  congr 1
  funext delta?
  rw [SuccinctClose.bpWordReadTraceResult_store_parametric hword]
  congr 1
  funext word?
  cases super? <;> cases delta? <;> cases word? <;>
    first
      | rfl
      | (dsimp only
         rw [SuccinctClose.bpChunkedWordRankTraceResultAtSegmentWithStore_store_parametric
            hchunk])

end TwoLevelPayloadLiveStoredWordRankData

end SuccinctRank

namespace GenericSelect

open SuccinctSpace SuccinctRank

/-! ## Relative-offset read as a supplied-store trace -/

/--
Store-parametric relative-offset read: one charged table read at the
caller's segment, with the decoded offset shifted by `base`.
-/
def bpRelativeOffsetReadTraceResultWithStore (store : WordRAM.ReadStore)
    (segment base slot : Nat) : WordRAM.TraceResult (Option Nat) :=
  WordRAM.TraceResult.map
    (fun offset? => offset?.map (fun offset => base + offset))
    (SuccinctClose.bpChunkReadTraceResult store segment slot)

theorem bpRelativeOffsetReadTraceResultWithStore_toCosted_of_agree
    {entries : List Nat} {width : Nat}
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    {store : WordRAM.ReadStore} {segment : Nat}
    (hagree :
      forall address,
        store.readWord? segment address = table.store.words[address]?)
    (base slot : Nat) :
    (bpRelativeOffsetReadTraceResultWithStore store segment base
        slot).toCosted =
      relativeOffsetReadCosted table base slot := by
  unfold bpRelativeOffsetReadTraceResultWithStore
  rw [WordRAM.TraceResult.map_toCosted,
    SuccinctClose.bpChunkReadTraceResult_toCosted_of_agree table hagree]
  rfl

theorem bpRelativeOffsetReadTraceResultWithStore_trace_forall
    (store : WordRAM.ReadStore) (segment base slot : Nat)
    (P : WordRAM.TraceEvent -> Prop)
    (hread :
      forall address,
        P (WordRAM.TraceEvent.readWord segment address
          (store.readWord? segment address))) :
    forall event,
      List.Mem event
          (bpRelativeOffsetReadTraceResultWithStore store segment base
            slot).trace ->
        P event := by
  unfold bpRelativeOffsetReadTraceResultWithStore
  apply WordRAM.TraceResult.map_trace_forall
  apply SuccinctClose.bpChunkReadTraceResult_trace_forall
  exact hread _

theorem bpRelativeOffsetReadTraceResultWithStore_matchesReadStore
    (store : WordRAM.ReadStore) (segment base slot : Nat) :
    forall event,
      List.Mem event
          (bpRelativeOffsetReadTraceResultWithStore store segment base
            slot).trace ->
        event.matchesReadStore store := by
  apply bpRelativeOffsetReadTraceResultWithStore_trace_forall
  intro address
  rfl

theorem bpRelativeOffsetReadTraceResultWithStore_no_syntheticCostOnlyPrimitive
    (store : WordRAM.ReadStore) (segment base slot : Nat) :
    forall event,
      List.Mem event
          (bpRelativeOffsetReadTraceResultWithStore store segment base
            slot).trace ->
        Not event.isSyntheticCostOnlyPrimitive := by
  apply bpRelativeOffsetReadTraceResultWithStore_trace_forall
  intro address
  simp [WordRAM.TraceEvent.isSyntheticCostOnlyPrimitive]

theorem bpRelativeOffsetReadTraceResultWithStore_store_parametric
    {storeA storeB : WordRAM.ReadStore} {segment : Nat}
    (hread :
      forall address,
        storeA.readWord? segment address =
          storeB.readWord? segment address)
    (base slot : Nat) :
    bpRelativeOffsetReadTraceResultWithStore storeA segment base slot =
      bpRelativeOffsetReadTraceResultWithStore storeB segment base slot := by
  unfold bpRelativeOffsetReadTraceResultWithStore
  rw [SuccinctClose.bpChunkReadTraceResult_store_parametric hread]

/-! ## Chunked dense two-word select leaf as a supplied-store trace -/

set_option linter.unusedVariables false in
/--
Store-parametric trace twin of `bpChunkedDenseTwoWordSelectCosted`:
identical branch structure to the accepted dense leaf, with the packed-word
reads emitted against the supplied store and the two in-word ranks and the
in-word select replaced by the charged chunk folds.  The `bitWords`
parameter names the counted component store the word segment must agree
with (the agreement is consumed by the lemmas below); the executed reads
are genuine reads of the supplied store.
-/
def bpChunkedDenseTwoWordSelectTraceResultWithStore
    (bitWordSegment rankTableSegment selectTableSegment c : Nat)
    (target : Bool) {bits : List Bool} {wordSize : Nat}
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (store : WordRAM.ReadStore)
    (basePosition baseOccurrence q : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  let firstWordIndex := basePosition / wordSize
  let firstWordStart := firstWordIndex * wordSize
  let firstOffset := basePosition - firstWordStart
  let localOccurrence := q - baseOccurrence
  WordRAM.TraceResult.bind
    (SuccinctClose.bpWordReadTraceResult store bitWordSegment
      firstWordIndex)
    fun firstWord? =>
      match firstWord? with
      | none => WordRAM.TraceResult.pure none
      | some firstWord =>
          WordRAM.TraceResult.bind
            (SuccinctClose.bpChunkedWordRankTraceResultAtSegmentWithStore
              store rankTableSegment c target firstWord firstOffset)
            fun beforeFirst =>
              WordRAM.TraceResult.bind
                (SuccinctClose.bpChunkedWordRankTraceResultAtSegmentWithStore
                  store rankTableSegment c target firstWord
                  firstWord.length)
                fun uptoFirst =>
                  let firstCount := uptoFirst - beforeFirst
                  if localOccurrence < firstCount then
                    WordRAM.TraceResult.map
                      (fun local? =>
                        local?.map fun offset => firstWordStart + offset)
                      (SuccinctClose.bpChunkedWordSelectTraceResultAtSegmentsWithStore
                        store rankTableSegment selectTableSegment c target
                        firstWord (beforeFirst + localOccurrence))
                  else
                    WordRAM.TraceResult.bind
                      (SuccinctClose.bpWordReadTraceResult store
                        bitWordSegment (firstWordIndex + 1))
                      fun secondWord? =>
                        match secondWord? with
                        | none => WordRAM.TraceResult.pure none
                        | some secondWord =>
                            WordRAM.TraceResult.map
                              (fun local? =>
                                local?.map fun offset =>
                                  (firstWordIndex + 1) * wordSize + offset)
                              (SuccinctClose.bpChunkedWordSelectTraceResultAtSegmentsWithStore
                                store rankTableSegment selectTableSegment
                                c target secondWord
                                (localOccurrence - firstCount))

/--
Refinement under agreement with the packed word store and the honest
chunk/select tables: the trace twin's `Costed` projection is exactly the M3
chunked dense leaf.
-/
theorem bpChunkedDenseTwoWordSelectTraceResultWithStore_toCosted_of_agree
    {bitWordSegment rankTableSegment selectTableSegment c : Nat}
    {target : Bool} {bits : List Bool} {wordSize : Nat}
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    {store : WordRAM.ReadStore}
    (hword :
      forall address,
        store.readWord? bitWordSegment address =
          bitWords.store.words[address]?)
    (hchunk :
      forall address,
        store.readWord? rankTableSegment address =
          (SuccinctClose.bpFringeChunkTable c).store.words[address]?)
    (hsel :
      forall address,
        store.readWord? selectTableSegment address =
          (SuccinctClose.bpChunkSelectTable c target).store.words[address]?)
    (basePosition baseOccurrence q : Nat) :
    (bpChunkedDenseTwoWordSelectTraceResultWithStore bitWordSegment
        rankTableSegment selectTableSegment c target bitWords store
        basePosition baseOccurrence q).toCosted =
      bpChunkedDenseTwoWordSelectCosted c target bitWords basePosition
        baseOccurrence q := by
  simp only [bpChunkedDenseTwoWordSelectTraceResultWithStore,
    bpChunkedDenseTwoWordSelectCosted]
  rw [WordRAM.TraceResult.bind_toCosted,
    SuccinctClose.bpWordReadTraceResult_toCosted_of_agree bitWords.store
      hword]
  congr 1
  funext firstWord?
  cases firstWord? with
  | none => rfl
  | some firstWord =>
      rw [WordRAM.TraceResult.bind_toCosted,
        SuccinctClose.bpChunkedWordRankTraceResultAtSegmentWithStore_toCosted_of_agree
          (SuccinctClose.bpFringeChunkTable c) hchunk]
      congr 1
      funext beforeFirst
      rw [WordRAM.TraceResult.bind_toCosted,
        SuccinctClose.bpChunkedWordRankTraceResultAtSegmentWithStore_toCosted_of_agree
          (SuccinctClose.bpFringeChunkTable c) hchunk]
      congr 1
      funext uptoFirst
      by_cases hbranch : q - baseOccurrence < uptoFirst - beforeFirst
      · rw [if_pos hbranch, if_pos hbranch,
          WordRAM.TraceResult.map_toCosted,
          SuccinctClose.bpChunkedWordSelectTraceResultAtSegmentsWithStore_toCosted_of_agree
            (SuccinctClose.bpFringeChunkTable c)
            (SuccinctClose.bpChunkSelectTable c target) hchunk hsel]
      · rw [if_neg hbranch, if_neg hbranch,
          WordRAM.TraceResult.bind_toCosted,
          SuccinctClose.bpWordReadTraceResult_toCosted_of_agree
            bitWords.store hword]
        congr 1
        funext secondWord?
        cases secondWord? with
        | none => rfl
        | some secondWord =>
            rw [WordRAM.TraceResult.map_toCosted,
              SuccinctClose.bpChunkedWordSelectTraceResultAtSegmentsWithStore_toCosted_of_agree
                (SuccinctClose.bpFringeChunkTable c)
                (SuccinctClose.bpChunkSelectTable c target) hchunk hsel]

/--
General event induction for the chunked dense leaf: packed-word reads at the
word segment, row-count-bounded chunk-table reads, and select-table reads.
-/
theorem bpChunkedDenseTwoWordSelectTraceResultWithStore_trace_forall
    (bitWordSegment rankTableSegment selectTableSegment c : Nat)
    (target : Bool) {bits : List Bool} {wordSize : Nat}
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (store : WordRAM.ReadStore)
    (basePosition baseOccurrence q : Nat)
    (P : WordRAM.TraceEvent -> Prop)
    (hword :
      forall address,
        P (WordRAM.TraceEvent.readWord bitWordSegment address
          (store.readWord? bitWordSegment address)))
    (hchunk :
      forall address,
        address < SuccinctClose.bpFringeChunkRowCount c ->
        P (WordRAM.TraceEvent.readWord rankTableSegment address
          (store.readWord? rankTableSegment address)))
    (hsel :
      forall address,
        P (WordRAM.TraceEvent.readWord selectTableSegment address
          (store.readWord? selectTableSegment address))) :
    forall event,
      List.Mem event
          (bpChunkedDenseTwoWordSelectTraceResultWithStore bitWordSegment
            rankTableSegment selectTableSegment c target bitWords store
            basePosition baseOccurrence q).trace ->
        P event := by
  simp only [bpChunkedDenseTwoWordSelectTraceResultWithStore]
  apply WordRAM.TraceResult.bind_trace_forall
  · apply SuccinctClose.bpWordReadTraceResult_trace_forall
    exact hword _
  · cases hfw :
        (SuccinctClose.bpWordReadTraceResult store bitWordSegment
          (basePosition / wordSize)).value with
    | none => exact WordRAM.TraceResult.pure_trace_forall P none
    | some firstWord =>
        apply WordRAM.TraceResult.bind_trace_forall
        · exact
            SuccinctClose.bpChunkedWordRankTraceResultAtSegmentWithStore_trace_forall
              store rankTableSegment c target firstWord _ P hchunk
        · apply WordRAM.TraceResult.bind_trace_forall
          · exact
              SuccinctClose.bpChunkedWordRankTraceResultAtSegmentWithStore_trace_forall
                store rankTableSegment c target firstWord _ P hchunk
          · by_cases hbranch :
                q - baseOccurrence <
                  (SuccinctClose.bpChunkedWordRankTraceResultAtSegmentWithStore
                      store rankTableSegment c target firstWord
                      firstWord.length).value -
                    (SuccinctClose.bpChunkedWordRankTraceResultAtSegmentWithStore
                      store rankTableSegment c target firstWord
                      (basePosition -
                        basePosition / wordSize * wordSize)).value
            · rw [if_pos hbranch]
              apply WordRAM.TraceResult.map_trace_forall
              exact
                SuccinctClose.bpChunkedWordSelectTraceResultAtSegmentsWithStore_trace_forall
                  store rankTableSegment selectTableSegment c target
                  firstWord _ P hchunk hsel
            · rw [if_neg hbranch]
              apply WordRAM.TraceResult.bind_trace_forall
              · apply SuccinctClose.bpWordReadTraceResult_trace_forall
                exact hword _
              · cases hsw :
                    (SuccinctClose.bpWordReadTraceResult store
                      bitWordSegment
                      (basePosition / wordSize + 1)).value with
                | none => exact WordRAM.TraceResult.pure_trace_forall P none
                | some secondWord =>
                    apply WordRAM.TraceResult.map_trace_forall
                    exact
                      SuccinctClose.bpChunkedWordSelectTraceResultAtSegmentsWithStore_trace_forall
                        store rankTableSegment selectTableSegment c target
                        secondWord _ P hchunk hsel

/--
Bounded event induction under honest-rank-table agreement: select-segment
reads additionally carry the select-table row-count address bound.
-/
theorem bpChunkedDenseTwoWordSelectTraceResultWithStore_trace_forall_of_honestRank
    {bitWordSegment rankTableSegment selectTableSegment c : Nat}
    {store : WordRAM.ReadStore}
    (hagreeRank :
      forall address,
        store.readWord? rankTableSegment address =
          (SuccinctClose.bpFringeChunkTable c).store.words[address]?)
    (target : Bool) {bits : List Bool} {wordSize : Nat}
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (basePosition baseOccurrence q : Nat)
    (P : WordRAM.TraceEvent -> Prop)
    (hword :
      forall address,
        P (WordRAM.TraceEvent.readWord bitWordSegment address
          (store.readWord? bitWordSegment address)))
    (hchunk :
      forall address,
        address < SuccinctClose.bpFringeChunkRowCount c ->
        P (WordRAM.TraceEvent.readWord rankTableSegment address
          (store.readWord? rankTableSegment address)))
    (hsel :
      forall address,
        address < SuccinctClose.bpChunkSelectRowCount c ->
        P (WordRAM.TraceEvent.readWord selectTableSegment address
          (store.readWord? selectTableSegment address))) :
    forall event,
      List.Mem event
          (bpChunkedDenseTwoWordSelectTraceResultWithStore bitWordSegment
            rankTableSegment selectTableSegment c target bitWords store
            basePosition baseOccurrence q).trace ->
        P event := by
  simp only [bpChunkedDenseTwoWordSelectTraceResultWithStore]
  apply WordRAM.TraceResult.bind_trace_forall
  · apply SuccinctClose.bpWordReadTraceResult_trace_forall
    exact hword _
  · cases hfw :
        (SuccinctClose.bpWordReadTraceResult store bitWordSegment
          (basePosition / wordSize)).value with
    | none => exact WordRAM.TraceResult.pure_trace_forall P none
    | some firstWord =>
        apply WordRAM.TraceResult.bind_trace_forall
        · exact
            SuccinctClose.bpChunkedWordRankTraceResultAtSegmentWithStore_trace_forall
              store rankTableSegment c target firstWord _ P hchunk
        · apply WordRAM.TraceResult.bind_trace_forall
          · exact
              SuccinctClose.bpChunkedWordRankTraceResultAtSegmentWithStore_trace_forall
                store rankTableSegment c target firstWord _ P hchunk
          · by_cases hbranch :
                q - baseOccurrence <
                  (SuccinctClose.bpChunkedWordRankTraceResultAtSegmentWithStore
                      store rankTableSegment c target firstWord
                      firstWord.length).value -
                    (SuccinctClose.bpChunkedWordRankTraceResultAtSegmentWithStore
                      store rankTableSegment c target firstWord
                      (basePosition -
                        basePosition / wordSize * wordSize)).value
            · rw [if_pos hbranch]
              apply WordRAM.TraceResult.map_trace_forall
              exact
                SuccinctClose.bpChunkedWordSelectTraceResultAtSegmentsWithStore_trace_forall_of_honestRank
                  hagreeRank target firstWord _ P hchunk hsel
            · rw [if_neg hbranch]
              apply WordRAM.TraceResult.bind_trace_forall
              · apply SuccinctClose.bpWordReadTraceResult_trace_forall
                exact hword _
              · cases hsw :
                    (SuccinctClose.bpWordReadTraceResult store
                      bitWordSegment
                      (basePosition / wordSize + 1)).value with
                | none => exact WordRAM.TraceResult.pure_trace_forall P none
                | some secondWord =>
                    apply WordRAM.TraceResult.map_trace_forall
                    exact
                      SuccinctClose.bpChunkedWordSelectTraceResultAtSegmentsWithStore_trace_forall_of_honestRank
                        hagreeRank target secondWord _ P hchunk hsel

theorem bpChunkedDenseTwoWordSelectTraceResultWithStore_matchesReadStore
    (bitWordSegment rankTableSegment selectTableSegment c : Nat)
    (target : Bool) {bits : List Bool} {wordSize : Nat}
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (store : WordRAM.ReadStore)
    (basePosition baseOccurrence q : Nat) :
    forall event,
      List.Mem event
          (bpChunkedDenseTwoWordSelectTraceResultWithStore bitWordSegment
            rankTableSegment selectTableSegment c target bitWords store
            basePosition baseOccurrence q).trace ->
        event.matchesReadStore store := by
  apply bpChunkedDenseTwoWordSelectTraceResultWithStore_trace_forall
  · intro address
    rfl
  · intro address _hlt
    rfl
  · intro address
    rfl

theorem bpChunkedDenseTwoWordSelectTraceResultWithStore_no_syntheticCostOnlyPrimitive
    (bitWordSegment rankTableSegment selectTableSegment c : Nat)
    (target : Bool) {bits : List Bool} {wordSize : Nat}
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (store : WordRAM.ReadStore)
    (basePosition baseOccurrence q : Nat) :
    forall event,
      List.Mem event
          (bpChunkedDenseTwoWordSelectTraceResultWithStore bitWordSegment
            rankTableSegment selectTableSegment c target bitWords store
            basePosition baseOccurrence q).trace ->
        Not event.isSyntheticCostOnlyPrimitive := by
  apply bpChunkedDenseTwoWordSelectTraceResultWithStore_trace_forall
  · intro address
    simp [WordRAM.TraceEvent.isSyntheticCostOnlyPrimitive]
  · intro address _hlt
    simp [WordRAM.TraceEvent.isSyntheticCostOnlyPrimitive]
  · intro address
    simp [WordRAM.TraceEvent.isSyntheticCostOnlyPrimitive]

theorem bpChunkedDenseTwoWordSelectTraceResultWithStore_store_parametric
    {bitWordSegment rankTableSegment selectTableSegment : Nat}
    {storeA storeB : WordRAM.ReadStore}
    (hword :
      forall address,
        storeA.readWord? bitWordSegment address =
          storeB.readWord? bitWordSegment address)
    (hchunk :
      forall address,
        storeA.readWord? rankTableSegment address =
          storeB.readWord? rankTableSegment address)
    (hsel :
      forall address,
        storeA.readWord? selectTableSegment address =
          storeB.readWord? selectTableSegment address)
    (c : Nat) (target : Bool) {bits : List Bool} {wordSize : Nat}
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (basePosition baseOccurrence q : Nat) :
    bpChunkedDenseTwoWordSelectTraceResultWithStore bitWordSegment
        rankTableSegment selectTableSegment c target bitWords storeA
        basePosition baseOccurrence q =
      bpChunkedDenseTwoWordSelectTraceResultWithStore bitWordSegment
        rankTableSegment selectTableSegment c target bitWords storeB
        basePosition baseOccurrence q := by
  simp only [bpChunkedDenseTwoWordSelectTraceResultWithStore]
  rw [SuccinctClose.bpWordReadTraceResult_store_parametric hword]
  congr 1
  funext firstWord?
  cases firstWord? with
  | none => rfl
  | some firstWord =>
      dsimp only
      rw [SuccinctClose.bpChunkedWordRankTraceResultAtSegmentWithStore_store_parametric
        hchunk]
      congr 1
      funext beforeFirst
      rw [SuccinctClose.bpChunkedWordRankTraceResultAtSegmentWithStore_store_parametric
        hchunk]
      congr 1
      funext uptoFirst
      by_cases hbranch : q - baseOccurrence < uptoFirst - beforeFirst
      · rw [if_pos hbranch, if_pos hbranch,
          SuccinctClose.bpChunkedWordSelectTraceResultAtSegmentsWithStore_store_parametric
            hchunk hsel]
      · rw [if_neg hbranch, if_neg hbranch,
          SuccinctClose.bpWordReadTraceResult_store_parametric hword]
        congr 1
        funext secondWord?
        cases secondWord? with
        | none => rfl
        | some secondWord =>
            dsimp only
            rw [SuccinctClose.bpChunkedWordSelectTraceResultAtSegmentsWithStore_store_parametric
              hchunk hsel]

/-! ## Chunked sparse-exception directory leaf as a supplied-store trace -/

namespace SparseExceptionDirectory

/--
Store-parametric trace twin of `SparseExceptionDirectory.bpChunkedReadCosted`:
the chunked rank seed at the layout's rank segments plus one relative-table
read at the layout's relative segment.
-/
def bpChunkedReadTraceResultWithStore
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      SparseExceptionDirectory
        bits target rankSuperOverhead rankBlockOverhead)
    (layout : SparseExceptionDirectoryTraceSegmentBases)
    (chunkSegment : Nat) (store : WordRAM.ReadStore) (c : Nat)
    (base localSlot localOccurrence : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  WordRAM.TraceResult.bind
    (directory.rankData.bpChunkedRankTraceResultWithStore store
      layout.rankBase (layout.rankBase + 1) (layout.rankBase + 2)
      chunkSegment c true localSlot)
    fun exceptionRank =>
      bpRelativeOffsetReadTraceResultWithStore store layout.relativeBase
        base
        (relativeSplitSelectSparseCompactSlot exceptionRank
          localOccurrence directory.localStride)

theorem bpChunkedReadTraceResultWithStore_toCosted_of_agree
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      SparseExceptionDirectory
        bits target rankSuperOverhead rankBlockOverhead)
    {layout : SparseExceptionDirectoryTraceSegmentBases}
    {chunkSegment : Nat} {store : WordRAM.ReadStore} {c : Nat}
    (hsuper :
      forall address,
        store.readWord? layout.rankBase address =
          (directory.rankData.superSampleWords true)[address]?)
    (hblock :
      forall address,
        store.readWord? (layout.rankBase + 1) address =
          (directory.rankData.blockSampleWords true)[address]?)
    (hword :
      forall address,
        store.readWord? (layout.rankBase + 2) address =
          directory.rankData.bitWords.store.words[address]?)
    (hchunk :
      forall address,
        store.readWord? chunkSegment address =
          (SuccinctClose.bpFringeChunkTable c).store.words[address]?)
    (hrelative :
      forall address,
        store.readWord? layout.relativeBase address =
          directory.relativeTable.store.words[address]?)
    (base localSlot localOccurrence : Nat) :
    (directory.bpChunkedReadTraceResultWithStore layout chunkSegment
        store c base localSlot localOccurrence).toCosted =
      directory.bpChunkedReadCosted c base localSlot localOccurrence := by
  unfold bpChunkedReadTraceResultWithStore bpChunkedReadCosted
  rw [WordRAM.TraceResult.bind_toCosted,
    directory.rankData.bpChunkedRankTraceResultWithStore_toCosted_of_agree
      hsuper hblock hword hchunk]
  congr 1
  funext exceptionRank
  exact
    bpRelativeOffsetReadTraceResultWithStore_toCosted_of_agree
      directory.relativeTable hrelative base _

theorem bpChunkedReadTraceResultWithStore_trace_forall
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      SparseExceptionDirectory
        bits target rankSuperOverhead rankBlockOverhead)
    (layout : SparseExceptionDirectoryTraceSegmentBases)
    (chunkSegment : Nat) (store : WordRAM.ReadStore) (c : Nat)
    (base localSlot localOccurrence : Nat)
    (P : WordRAM.TraceEvent -> Prop)
    (hrank :
      forall event,
        List.Mem event
            (directory.rankData.bpChunkedRankTraceResultWithStore store
              layout.rankBase (layout.rankBase + 1) (layout.rankBase + 2)
              chunkSegment c true localSlot).trace ->
          P event)
    (hrelative :
      forall slot event,
        List.Mem event
            (bpRelativeOffsetReadTraceResultWithStore store
              layout.relativeBase base slot).trace ->
          P event) :
    forall event,
      List.Mem event
          (directory.bpChunkedReadTraceResultWithStore layout chunkSegment
            store c base localSlot localOccurrence).trace ->
        P event := by
  unfold bpChunkedReadTraceResultWithStore
  apply WordRAM.TraceResult.bind_trace_forall
  · exact hrank
  · exact hrelative _

theorem bpChunkedReadTraceResultWithStore_matchesReadStore
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      SparseExceptionDirectory
        bits target rankSuperOverhead rankBlockOverhead)
    (layout : SparseExceptionDirectoryTraceSegmentBases)
    (chunkSegment : Nat) (store : WordRAM.ReadStore) (c : Nat)
    (base localSlot localOccurrence : Nat) :
    forall event,
      List.Mem event
          (directory.bpChunkedReadTraceResultWithStore layout chunkSegment
            store c base localSlot localOccurrence).trace ->
        event.matchesReadStore store := by
  apply directory.bpChunkedReadTraceResultWithStore_trace_forall
  · exact
      directory.rankData.bpChunkedRankTraceResultWithStore_matchesReadStore
        store layout.rankBase (layout.rankBase + 1) (layout.rankBase + 2)
        chunkSegment c true localSlot
  · intro slot
    exact
      bpRelativeOffsetReadTraceResultWithStore_matchesReadStore store
        layout.relativeBase base slot

theorem bpChunkedReadTraceResultWithStore_no_syntheticCostOnlyPrimitive
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      SparseExceptionDirectory
        bits target rankSuperOverhead rankBlockOverhead)
    (layout : SparseExceptionDirectoryTraceSegmentBases)
    (chunkSegment : Nat) (store : WordRAM.ReadStore) (c : Nat)
    (base localSlot localOccurrence : Nat) :
    forall event,
      List.Mem event
          (directory.bpChunkedReadTraceResultWithStore layout chunkSegment
            store c base localSlot localOccurrence).trace ->
        Not event.isSyntheticCostOnlyPrimitive := by
  apply directory.bpChunkedReadTraceResultWithStore_trace_forall
  · exact
      directory.rankData.bpChunkedRankTraceResultWithStore_no_syntheticCostOnlyPrimitive
        store layout.rankBase (layout.rankBase + 1) (layout.rankBase + 2)
        chunkSegment c true localSlot
  · intro slot
    exact
      bpRelativeOffsetReadTraceResultWithStore_no_syntheticCostOnlyPrimitive
        store layout.relativeBase base slot

theorem bpChunkedReadTraceResultWithStore_store_parametric
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      SparseExceptionDirectory
        bits target rankSuperOverhead rankBlockOverhead)
    {layout : SparseExceptionDirectoryTraceSegmentBases}
    {chunkSegment : Nat} {storeA storeB : WordRAM.ReadStore}
    (hsuper :
      forall address,
        storeA.readWord? layout.rankBase address =
          storeB.readWord? layout.rankBase address)
    (hblock :
      forall address,
        storeA.readWord? (layout.rankBase + 1) address =
          storeB.readWord? (layout.rankBase + 1) address)
    (hword :
      forall address,
        storeA.readWord? (layout.rankBase + 2) address =
          storeB.readWord? (layout.rankBase + 2) address)
    (hchunk :
      forall address,
        storeA.readWord? chunkSegment address =
          storeB.readWord? chunkSegment address)
    (hrelative :
      forall address,
        storeA.readWord? layout.relativeBase address =
          storeB.readWord? layout.relativeBase address)
    (c : Nat) (base localSlot localOccurrence : Nat) :
    directory.bpChunkedReadTraceResultWithStore layout chunkSegment
        storeA c base localSlot localOccurrence =
      directory.bpChunkedReadTraceResultWithStore layout chunkSegment
        storeB c base localSlot localOccurrence := by
  unfold bpChunkedReadTraceResultWithStore
  rw [directory.rankData.bpChunkedRankTraceResultWithStore_store_parametric
    hsuper hblock hword hchunk]
  congr 1
  funext exceptionRank
  exact
    bpRelativeOffsetReadTraceResultWithStore_store_parametric hrelative
      base _

end SparseExceptionDirectory

/-! ## Chunked accepted select-close execution as a supplied-store trace -/

namespace SparseExceptionSelectData

/--
Store-parametric trace twin of
`SparseExceptionSelectData.bpChunkedSelectCosted`: identical routing to the
accepted select-close trace, with the flag ranks and the dense leaf replaced
by the chunked twins.  The super/local entry-table reads are the accepted
store-parametric evaluators unchanged; chunk-table reads land at
`chunkSegment` and select-table reads at `selectTableSegment`.
-/
def bpChunkedSelectTraceResultWithStore
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      SparseExceptionSelectData
        bits target rankSuperOverhead rankBlockOverhead)
    (layout : SparseExceptionSelectTraceSegmentLayout)
    (chunkSegment selectTableSegment : Nat)
    (store : WordRAM.ReadStore) (c : Nat)
    (idx : Nat) : WordRAM.TraceResult (Option Nat) :=
  let q := data.queryOccurrence idx
  if idx < occurrenceCount bits target then
    WordRAM.TraceResult.bind
      (data.superTable.readTraceResultRelabeledWithStore
        layout.superTable store
        (selectSuperSlot q data.superStride)) fun super? =>
      match super? with
      | none => WordRAM.TraceResult.pure none
      | some super =>
          if relativeSplitSelectEntryIsMarked super then
            WordRAM.TraceResult.bind
              (data.longFlagRankData.bpChunkedRankTraceResultWithStore
                store layout.longFlagRankBase
                (layout.longFlagRankBase + 1)
                (layout.longFlagRankBase + 2) chunkSegment c true
                (selectSuperSlot q data.superStride))
              fun exceptionRank =>
                bpRelativeOffsetReadTraceResultWithStore store
                  layout.longRelativeBase
                  (relativeSplitSelectEntryBasePosition
                    data.wordSize super)
                  (relativeSplitSelectLongCompactSlot
                    exceptionRank (q - super.baseOccurrence)
                    data.superStride)
          else
            let localSlot :=
              relativeSplitSelectLocalSlot q data.superStride
                data.localSlotsPerSuper data.localStride super
            WordRAM.TraceResult.bind
              (data.localTable.readTraceResultRelabeledWithStore
                layout.localTable store localSlot) fun loc? =>
              match loc? with
              | none => WordRAM.TraceResult.pure none
              | some loc =>
                  if relativeSplitSelectEntryIsMarked loc then
                    data.sparseDirectory.bpChunkedReadTraceResultWithStore
                      layout.sparseDirectory chunkSegment store c
                      (relativeSplitSelectLocalBasePosition
                        data.wordSize super loc)
                      localSlot
                      (q -
                        relativeSplitSelectLocalBaseOccurrence
                          super loc)
                  else
                    bpChunkedDenseTwoWordSelectTraceResultWithStore
                      layout.bitWordBase chunkSegment selectTableSegment
                      c target data.bitWords store
                      (relativeSplitSelectLocalBasePosition
                        data.wordSize super loc)
                      (relativeSplitSelectLocalBaseOccurrence
                        super loc) q
  else
    WordRAM.TraceResult.pure none

/--
Refinement under the pullback agreements for the accepted entry tables and
per-segment agreements for the rank samples, relative tables, packed words,
and the honest chunk/select tables: the trace twin's `Costed` projection is
exactly the M3 chunked select-close execution.
-/
theorem bpChunkedSelectTraceResultWithStore_toCosted_of_agree
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      SparseExceptionSelectData
        bits target rankSuperOverhead rankBlockOverhead)
    {layout : SparseExceptionSelectTraceSegmentLayout}
    {chunkSegment selectTableSegment : Nat}
    {store : WordRAM.ReadStore} {c : Nat}
    (hsuperBaseOcc :
      store.pullback
          (WordRAM.singletonSegmentMap layout.superTable.baseOccurrence
            layout.superTable.deadSegment) =
        WordRAM.ReadStore.ofStore
          data.superTable.baseOccurrenceTable.wordRAMStore)
    (hsuperBaseWord :
      store.pullback
          (WordRAM.singletonSegmentMap layout.superTable.baseWordIndex
            layout.superTable.deadSegment) =
        WordRAM.ReadStore.ofStore
          data.superTable.baseWordIndexTable.wordRAMStore)
    (hsuperRankBefore :
      store.pullback
          (WordRAM.singletonSegmentMap layout.superTable.rankBefore
            layout.superTable.deadSegment) =
        WordRAM.ReadStore.ofStore
          data.superTable.rankBeforeTable.wordRAMStore)
    (hsuperFirstOffset :
      store.pullback
          (WordRAM.singletonSegmentMap layout.superTable.firstOffset
            layout.superTable.deadSegment) =
        WordRAM.ReadStore.ofStore
          data.superTable.firstOffsetTable.wordRAMStore)
    (hlocalBaseOcc :
      store.pullback
          (WordRAM.singletonSegmentMap layout.localTable.baseOccurrence
            layout.localTable.deadSegment) =
        WordRAM.ReadStore.ofStore
          data.localTable.baseOccurrenceTable.wordRAMStore)
    (hlocalBaseWord :
      store.pullback
          (WordRAM.singletonSegmentMap layout.localTable.baseWordIndex
            layout.localTable.deadSegment) =
        WordRAM.ReadStore.ofStore
          data.localTable.baseWordIndexTable.wordRAMStore)
    (hlocalRankBefore :
      store.pullback
          (WordRAM.singletonSegmentMap layout.localTable.rankBefore
            layout.localTable.deadSegment) =
        WordRAM.ReadStore.ofStore
          data.localTable.rankBeforeTable.wordRAMStore)
    (hlocalFirstOffset :
      store.pullback
          (WordRAM.singletonSegmentMap layout.localTable.firstOffset
            layout.localTable.deadSegment) =
        WordRAM.ReadStore.ofStore
          data.localTable.firstOffsetTable.wordRAMStore)
    (hlongSuper :
      forall address,
        store.readWord? layout.longFlagRankBase address =
          (data.longFlagRankData.superSampleWords true)[address]?)
    (hlongBlock :
      forall address,
        store.readWord? (layout.longFlagRankBase + 1) address =
          (data.longFlagRankData.blockSampleWords true)[address]?)
    (hlongWord :
      forall address,
        store.readWord? (layout.longFlagRankBase + 2) address =
          data.longFlagRankData.bitWords.store.words[address]?)
    (hlongRelative :
      forall address,
        store.readWord? layout.longRelativeBase address =
          data.longSuperRelativeTable.store.words[address]?)
    (hsparseSuper :
      forall address,
        store.readWord? layout.sparseDirectory.rankBase address =
          (data.sparseDirectory.rankData.superSampleWords true)[address]?)
    (hsparseBlock :
      forall address,
        store.readWord? (layout.sparseDirectory.rankBase + 1) address =
          (data.sparseDirectory.rankData.blockSampleWords true)[address]?)
    (hsparseWord :
      forall address,
        store.readWord? (layout.sparseDirectory.rankBase + 2) address =
          data.sparseDirectory.rankData.bitWords.store.words[address]?)
    (hsparseRelative :
      forall address,
        store.readWord? layout.sparseDirectory.relativeBase address =
          data.sparseDirectory.relativeTable.store.words[address]?)
    (hbit :
      forall address,
        store.readWord? layout.bitWordBase address =
          data.bitWords.store.words[address]?)
    (hchunk :
      forall address,
        store.readWord? chunkSegment address =
          (SuccinctClose.bpFringeChunkTable c).store.words[address]?)
    (hsel :
      forall address,
        store.readWord? selectTableSegment address =
          (SuccinctClose.bpChunkSelectTable c target).store.words[address]?)
    (idx : Nat) :
    (data.bpChunkedSelectTraceResultWithStore layout chunkSegment
        selectTableSegment store c idx).toCosted =
      data.bpChunkedSelectCosted c idx := by
  have hsuperT :
      forall slot,
        (data.superTable.readTraceResultRelabeledWithStore
            layout.superTable store slot).toCosted =
          data.superTable.readCosted slot := by
    intro slot
    rw [data.superTable.readTraceResultRelabeledWithStore_eq_of_pullback
      hsuperBaseOcc hsuperBaseWord hsuperRankBefore hsuperFirstOffset
      slot]
    rw [data.superTable.readTraceResultRelabeled_refines_interpretedCosted
      layout.superTable slot]
    exact data.superTable.readInterpretedCosted_refines_readCosted slot
  have hlocalT :
      forall slot,
        (data.localTable.readTraceResultRelabeledWithStore
            layout.localTable store slot).toCosted =
          data.localTable.readCosted slot := by
    intro slot
    rw [data.localTable.readTraceResultRelabeledWithStore_eq_of_pullback
      hlocalBaseOcc hlocalBaseWord hlocalRankBefore hlocalFirstOffset
      slot]
    rw [data.localTable.readTraceResultRelabeled_refines_interpretedCosted
      layout.localTable slot]
    exact data.localTable.readInterpretedCosted_refines_readCosted slot
  simp only [bpChunkedSelectTraceResultWithStore, bpChunkedSelectCosted]
  by_cases hvalid : idx < occurrenceCount bits target
  · rw [if_pos hvalid, if_pos hvalid,
      WordRAM.TraceResult.bind_toCosted, hsuperT]
    congr 1
    funext super?
    cases super? with
    | none => rfl
    | some super =>
        dsimp only
        by_cases hmark : relativeSplitSelectEntryIsMarked super = true
        · rw [if_pos hmark, if_pos hmark,
            WordRAM.TraceResult.bind_toCosted,
            data.longFlagRankData.bpChunkedRankTraceResultWithStore_toCosted_of_agree
              hlongSuper hlongBlock hlongWord hchunk]
          congr 1
          funext exceptionRank
          exact
            bpRelativeOffsetReadTraceResultWithStore_toCosted_of_agree
              data.longSuperRelativeTable hlongRelative _ _
        · rw [if_neg hmark, if_neg hmark,
            WordRAM.TraceResult.bind_toCosted, hlocalT]
          congr 1
          funext loc?
          cases loc? with
          | none => rfl
          | some loc =>
              dsimp only
              by_cases hsparse :
                  relativeSplitSelectEntryIsMarked loc = true
              · rw [if_pos hsparse, if_pos hsparse]
                exact
                  data.sparseDirectory.bpChunkedReadTraceResultWithStore_toCosted_of_agree
                    hsparseSuper hsparseBlock hsparseWord hchunk
                    hsparseRelative _ _ _
              · rw [if_neg hsparse, if_neg hsparse]
                exact
                  bpChunkedDenseTwoWordSelectTraceResultWithStore_toCosted_of_agree
                    data.bitWords hbit hchunk hsel _ _ _
  · rw [if_neg hvalid, if_neg hvalid]
    rfl

/--
General event induction for the chunked select-close trace, parameterized by
component handlers exactly as the accepted
`selectTraceResultRelabeled_trace_forall`.
-/
theorem bpChunkedSelectTraceResultWithStore_trace_forall
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      SparseExceptionSelectData
        bits target rankSuperOverhead rankBlockOverhead)
    (layout : SparseExceptionSelectTraceSegmentLayout)
    (chunkSegment selectTableSegment : Nat)
    (store : WordRAM.ReadStore) (c : Nat) (idx : Nat)
    (P : WordRAM.TraceEvent -> Prop)
    (hsuper :
      forall slot event,
        List.Mem event
            (data.superTable.readTraceResultRelabeledWithStore
              layout.superTable store slot).trace ->
          P event)
    (hlongRank :
      forall slot event,
        List.Mem event
            (data.longFlagRankData.bpChunkedRankTraceResultWithStore
              store layout.longFlagRankBase (layout.longFlagRankBase + 1)
              (layout.longFlagRankBase + 2) chunkSegment c true
              slot).trace ->
          P event)
    (hlongRelative :
      forall base slot event,
        List.Mem event
            (bpRelativeOffsetReadTraceResultWithStore store
              layout.longRelativeBase base slot).trace ->
          P event)
    (hlocal :
      forall slot event,
        List.Mem event
            (data.localTable.readTraceResultRelabeledWithStore
              layout.localTable store slot).trace ->
          P event)
    (hsparse :
      forall base localSlot localOccurrence event,
        List.Mem event
            (data.sparseDirectory.bpChunkedReadTraceResultWithStore
              layout.sparseDirectory chunkSegment store c base localSlot
              localOccurrence).trace ->
          P event)
    (hdense :
      forall basePosition baseOccurrence q event,
        List.Mem event
            (bpChunkedDenseTwoWordSelectTraceResultWithStore
              layout.bitWordBase chunkSegment selectTableSegment c target
              data.bitWords store basePosition baseOccurrence q).trace ->
          P event) :
    forall event,
      List.Mem event
          (data.bpChunkedSelectTraceResultWithStore layout chunkSegment
            selectTableSegment store c idx).trace ->
        P event := by
  simp only [bpChunkedSelectTraceResultWithStore]
  by_cases hvalid : idx < occurrenceCount bits target
  · rw [if_pos hvalid]
    apply WordRAM.TraceResult.bind_trace_forall
    · exact hsuper _
    · cases hsuperValue :
        (data.superTable.readTraceResultRelabeledWithStore
          layout.superTable store
          (selectSuperSlot (data.queryOccurrence idx)
            data.superStride)).value with
      | none => exact WordRAM.TraceResult.pure_trace_forall P none
      | some super =>
          dsimp only
          by_cases hlong : relativeSplitSelectEntryIsMarked super = true
          · rw [if_pos hlong]
            apply WordRAM.TraceResult.bind_trace_forall
            · exact hlongRank _
            · exact hlongRelative _ _
          · rw [if_neg hlong]
            apply WordRAM.TraceResult.bind_trace_forall
            · exact hlocal _
            · cases hlocalValue :
                (data.localTable.readTraceResultRelabeledWithStore
                  layout.localTable store
                  (relativeSplitSelectLocalSlot
                    (data.queryOccurrence idx) data.superStride
                    data.localSlotsPerSuper data.localStride
                    super)).value with
              | none => exact WordRAM.TraceResult.pure_trace_forall P none
              | some loc =>
                  dsimp only
                  by_cases hsparseBranch :
                      relativeSplitSelectEntryIsMarked loc = true
                  · rw [if_pos hsparseBranch]
                    exact hsparse _ _ _
                  · rw [if_neg hsparseBranch]
                    exact hdense _ _ _
  · rw [if_neg hvalid]
    exact WordRAM.TraceResult.pure_trace_forall P none

theorem bpChunkedSelectTraceResultWithStore_matchesReadStore
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      SparseExceptionSelectData
        bits target rankSuperOverhead rankBlockOverhead)
    (layout : SparseExceptionSelectTraceSegmentLayout)
    (chunkSegment selectTableSegment : Nat)
    (store : WordRAM.ReadStore) (c : Nat) (idx : Nat) :
    forall event,
      List.Mem event
          (data.bpChunkedSelectTraceResultWithStore layout chunkSegment
            selectTableSegment store c idx).trace ->
        event.matchesReadStore store := by
  apply data.bpChunkedSelectTraceResultWithStore_trace_forall
  · intro slot
    exact
      data.superTable.readTraceResultRelabeledWithStore_matchesReadStore
        layout.superTable store slot
  · intro slot
    exact
      data.longFlagRankData.bpChunkedRankTraceResultWithStore_matchesReadStore
        store layout.longFlagRankBase (layout.longFlagRankBase + 1)
        (layout.longFlagRankBase + 2) chunkSegment c true slot
  · intro base slot
    exact
      bpRelativeOffsetReadTraceResultWithStore_matchesReadStore store
        layout.longRelativeBase base slot
  · intro slot
    exact
      data.localTable.readTraceResultRelabeledWithStore_matchesReadStore
        layout.localTable store slot
  · intro base localSlot localOccurrence
    exact
      data.sparseDirectory.bpChunkedReadTraceResultWithStore_matchesReadStore
        layout.sparseDirectory chunkSegment store c base localSlot
        localOccurrence
  · intro basePosition baseOccurrence q
    exact
      bpChunkedDenseTwoWordSelectTraceResultWithStore_matchesReadStore
        layout.bitWordBase chunkSegment selectTableSegment c target
        data.bitWords store basePosition baseOccurrence q

theorem bpChunkedSelectTraceResultWithStore_no_syntheticCostOnlyPrimitive
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      SparseExceptionSelectData
        bits target rankSuperOverhead rankBlockOverhead)
    (layout : SparseExceptionSelectTraceSegmentLayout)
    (chunkSegment selectTableSegment : Nat)
    (store : WordRAM.ReadStore) (c : Nat) (idx : Nat) :
    forall event,
      List.Mem event
          (data.bpChunkedSelectTraceResultWithStore layout chunkSegment
            selectTableSegment store c idx).trace ->
        Not event.isSyntheticCostOnlyPrimitive := by
  apply data.bpChunkedSelectTraceResultWithStore_trace_forall
  · intro slot
    exact
      data.superTable.readTraceResultRelabeledWithStore_no_syntheticCostOnlyPrimitive
        layout.superTable store slot
  · intro slot
    exact
      data.longFlagRankData.bpChunkedRankTraceResultWithStore_no_syntheticCostOnlyPrimitive
        store layout.longFlagRankBase (layout.longFlagRankBase + 1)
        (layout.longFlagRankBase + 2) chunkSegment c true slot
  · intro base slot
    exact
      bpRelativeOffsetReadTraceResultWithStore_no_syntheticCostOnlyPrimitive
        store layout.longRelativeBase base slot
  · intro slot
    exact
      data.localTable.readTraceResultRelabeledWithStore_no_syntheticCostOnlyPrimitive
        layout.localTable store slot
  · intro base localSlot localOccurrence
    exact
      data.sparseDirectory.bpChunkedReadTraceResultWithStore_no_syntheticCostOnlyPrimitive
        layout.sparseDirectory chunkSegment store c base localSlot
        localOccurrence
  · intro basePosition baseOccurrence q
    exact
      bpChunkedDenseTwoWordSelectTraceResultWithStore_no_syntheticCostOnlyPrimitive
        layout.bitWordBase chunkSegment selectTableSegment c target
        data.bitWords store basePosition baseOccurrence q

theorem bpChunkedSelectTraceResultWithStore_store_parametric
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      SparseExceptionSelectData
        bits target rankSuperOverhead rankBlockOverhead)
    {layout : SparseExceptionSelectTraceSegmentLayout}
    {chunkSegment selectTableSegment : Nat}
    {storeA storeB : WordRAM.ReadStore}
    (hsuperBaseOcc :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap layout.superTable.baseOccurrence
              layout.superTable.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap layout.superTable.baseOccurrence
              layout.superTable.deadSegment segment) index)
    (hsuperBaseWord :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap layout.superTable.baseWordIndex
              layout.superTable.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap layout.superTable.baseWordIndex
              layout.superTable.deadSegment segment) index)
    (hsuperRankBefore :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap layout.superTable.rankBefore
              layout.superTable.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap layout.superTable.rankBefore
              layout.superTable.deadSegment segment) index)
    (hsuperFirstOffset :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap layout.superTable.firstOffset
              layout.superTable.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap layout.superTable.firstOffset
              layout.superTable.deadSegment segment) index)
    (hlocalBaseOcc :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap layout.localTable.baseOccurrence
              layout.localTable.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap layout.localTable.baseOccurrence
              layout.localTable.deadSegment segment) index)
    (hlocalBaseWord :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap layout.localTable.baseWordIndex
              layout.localTable.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap layout.localTable.baseWordIndex
              layout.localTable.deadSegment segment) index)
    (hlocalRankBefore :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap layout.localTable.rankBefore
              layout.localTable.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap layout.localTable.rankBefore
              layout.localTable.deadSegment segment) index)
    (hlocalFirstOffset :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap layout.localTable.firstOffset
              layout.localTable.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap layout.localTable.firstOffset
              layout.localTable.deadSegment segment) index)
    (hlongSuper :
      forall address,
        storeA.readWord? layout.longFlagRankBase address =
          storeB.readWord? layout.longFlagRankBase address)
    (hlongBlock :
      forall address,
        storeA.readWord? (layout.longFlagRankBase + 1) address =
          storeB.readWord? (layout.longFlagRankBase + 1) address)
    (hlongWord :
      forall address,
        storeA.readWord? (layout.longFlagRankBase + 2) address =
          storeB.readWord? (layout.longFlagRankBase + 2) address)
    (hlongRelative :
      forall address,
        storeA.readWord? layout.longRelativeBase address =
          storeB.readWord? layout.longRelativeBase address)
    (hsparseSuper :
      forall address,
        storeA.readWord? layout.sparseDirectory.rankBase address =
          storeB.readWord? layout.sparseDirectory.rankBase address)
    (hsparseBlock :
      forall address,
        storeA.readWord? (layout.sparseDirectory.rankBase + 1) address =
          storeB.readWord? (layout.sparseDirectory.rankBase + 1) address)
    (hsparseWord :
      forall address,
        storeA.readWord? (layout.sparseDirectory.rankBase + 2) address =
          storeB.readWord? (layout.sparseDirectory.rankBase + 2) address)
    (hsparseRelative :
      forall address,
        storeA.readWord? layout.sparseDirectory.relativeBase address =
          storeB.readWord? layout.sparseDirectory.relativeBase address)
    (hbit :
      forall address,
        storeA.readWord? layout.bitWordBase address =
          storeB.readWord? layout.bitWordBase address)
    (hchunk :
      forall address,
        storeA.readWord? chunkSegment address =
          storeB.readWord? chunkSegment address)
    (hsel :
      forall address,
        storeA.readWord? selectTableSegment address =
          storeB.readWord? selectTableSegment address)
    (c : Nat) (idx : Nat) :
    data.bpChunkedSelectTraceResultWithStore layout chunkSegment
        selectTableSegment storeA c idx =
      data.bpChunkedSelectTraceResultWithStore layout chunkSegment
        selectTableSegment storeB c idx := by
  simp only [bpChunkedSelectTraceResultWithStore]
  by_cases hvalid : idx < occurrenceCount bits target
  · rw [if_pos hvalid, if_pos hvalid,
      data.superTable.readTraceResultRelabeledWithStore_store_parametric
        hsuperBaseOcc hsuperBaseWord hsuperRankBefore hsuperFirstOffset]
    congr 1
    funext super?
    cases super? with
    | none => rfl
    | some super =>
        dsimp only
        by_cases hmark : relativeSplitSelectEntryIsMarked super = true
        · rw [if_pos hmark, if_pos hmark,
            data.longFlagRankData.bpChunkedRankTraceResultWithStore_store_parametric
              hlongSuper hlongBlock hlongWord hchunk]
          congr 1
          funext exceptionRank
          exact
            bpRelativeOffsetReadTraceResultWithStore_store_parametric
              hlongRelative _ _
        · rw [if_neg hmark, if_neg hmark,
            data.localTable.readTraceResultRelabeledWithStore_store_parametric
              hlocalBaseOcc hlocalBaseWord hlocalRankBefore
              hlocalFirstOffset]
          congr 1
          funext loc?
          cases loc? with
          | none => rfl
          | some loc =>
              dsimp only
              by_cases hsparseBranch :
                  relativeSplitSelectEntryIsMarked loc = true
              · rw [if_pos hsparseBranch, if_pos hsparseBranch]
                exact
                  data.sparseDirectory.bpChunkedReadTraceResultWithStore_store_parametric
                    hsparseSuper hsparseBlock hsparseWord hchunk
                    hsparseRelative c _ _ _
              · rw [if_neg hsparseBranch, if_neg hsparseBranch]
                exact
                  bpChunkedDenseTwoWordSelectTraceResultWithStore_store_parametric
                    hbit hchunk hsel c target data.bitWords _ _ _
  · rw [if_neg hvalid, if_neg hvalid]

end SparseExceptionSelectData

end GenericSelect

end RMQ
