import RMQ.Core.SuccinctClose.RelativeRmmMacro.ChargedFringeTrace
import RMQ.Core.SuccinctClose.RelativeRmmMacro.ChargedSameBlockChunks

/-!
# Charged chunked same-block close trace (Option B, B6)

Structural `WordRAM.TraceResult` twins of `ChargedSameBlockChunks.lean`.
The trace is the four accepted window-word reads at segment `0` followed by
one chunk-table read per visited chunk at `fringeSegment` — the SAME segment
and the SAME `bpFringeChunkTable` the B2 cross-block fringe already reads, so
no new store region, payload component, or capacity obligation arises.

Every declaration here mirrors its
`bpChunkedLeft/RightFringeCandidateSeededTraceResultAtSegment` counterpart in
`ChargedFringeTrace.lean`, instantiated at the same-block range
(`start := leftClose + 1`, `count := rightClose - leftClose + 1`) and
composed with the accepted `bpCandidateClose?` projection.
-/

namespace RMQ

namespace SuccinctClose

open SuccinctSpace

namespace ConcreteCompactBPCloseLCADirectory

/-! ## Charged chunked same-block close at one global segment -/

/--
Charged chunked same-block close trace: the accepted four window-word reads
at segment `0`, then one chunk-table read per visited chunk at
`fringeSegment`, then the accepted `bpCandidateClose?` projection.
-/
def bpChunkedSameBlockCloseSeededTraceResultAtSegment
    (shape : Cartesian.CartesianShape) (fringeSegment : Nat)
    (blockSize leftClose rightClose seed : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  let c := bpFringeChunkBits shape.bpCode.length
  let base := localBPWindowBase shape blockSize leftClose
  let start := leftClose + 1
  let count := rightClose - leftClose + 1
  let relLo := start - base
  let relHi := start + count - 1 - base
  WordRAM.TraceResult.bind
    (localBPWindowBitsTraceResult shape blockSize leftClose)
    (fun window =>
      WordRAM.TraceResult.map
        (fun st => bpCandidateClose? (bpFringeCandGlobal base seed start st.2))
        (bpFringeChunkFoldTraceResultAtSegment (bpFringeChunkTable c)
          fringeSegment c window seed relLo relHi
          (Nat.min (relHi / c + 1) 33)))

/-- Store-parameterized charged chunked same-block close trace. -/
def bpChunkedSameBlockCloseSeededTraceResultAtSegmentWithStore
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (fringeSegment : Nat)
    (blockSize leftClose rightClose seed : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  let c := bpFringeChunkBits shape.bpCode.length
  let base := localBPWindowBase shape blockSize leftClose
  let start := leftClose + 1
  let count := rightClose - leftClose + 1
  let relLo := start - base
  let relHi := start + count - 1 - base
  WordRAM.TraceResult.bind
    (localBPWindowBitsTraceResultWithStore shape store blockSize leftClose)
    (fun window =>
      WordRAM.TraceResult.map
        (fun st => bpCandidateClose? (bpFringeCandGlobal base seed start st.2))
        (bpFringeChunkFoldTraceResultAtSegmentWithStore store
          fringeSegment c window seed relLo relHi
          (Nat.min (relHi / c + 1) 33)))

/-- The same-block trace refines the charged same-block Costed leaf. -/
theorem bpChunkedSameBlockCloseSeededTraceResultAtSegment_refines
    (shape : Cartesian.CartesianShape) (fringeSegment : Nat)
    (blockSize leftClose rightClose seed : Nat) :
    (bpChunkedSameBlockCloseSeededTraceResultAtSegment
        shape fringeSegment blockSize leftClose rightClose seed).toCosted =
      bpChunkedSameBlockCloseSeededCosted shape blockSize leftClose
        rightClose seed := by
  unfold bpChunkedSameBlockCloseSeededTraceResultAtSegment
    bpChunkedSameBlockCloseSeededCosted
  simp only [WordRAM.TraceResult.bind_toCosted,
    WordRAM.TraceResult.map_toCosted,
    localBPWindowBitsTraceResult_toCosted,
    bpFringeChunkFoldTraceResultAtSegment_toCosted]

/--
Every same-block trace event is either one of the accepted window-word reads
or a `readWord fringeSegment address` at an in-range chunk-table slot.
-/
theorem bpChunkedSameBlockCloseSeededTraceResultAtSegment_trace_forall
    (shape : Cartesian.CartesianShape) (fringeSegment : Nat)
    (blockSize leftClose rightClose seed : Nat)
    (P : WordRAM.TraceEvent -> Prop)
    (hbp :
      forall event,
        List.Mem event
          (localBPWindowBitsTraceResult shape blockSize leftClose).trace ->
          P event)
    (hfringe :
      forall address,
        address <
          bpFringeChunkRowCount (bpFringeChunkBits shape.bpCode.length) ->
        P (WordRAM.TraceEvent.readWord fringeSegment address
          (bpFringeChunkTable
            (bpFringeChunkBits shape.bpCode.length)).store.words[address]?)) :
    forall event,
      List.Mem event
          (bpChunkedSameBlockCloseSeededTraceResultAtSegment
            shape fringeSegment blockSize leftClose rightClose seed).trace ->
        P event := by
  unfold bpChunkedSameBlockCloseSeededTraceResultAtSegment
  apply WordRAM.TraceResult.bind_trace_forall
  · exact hbp
  · apply WordRAM.TraceResult.map_trace_forall
    exact
      bpFringeChunkFoldTraceResultAtSegment_trace_forall
        (bpFringeChunkTable (bpFringeChunkBits shape.bpCode.length))
        fringeSegment _ _ seed _ _ _ P hfringe

theorem bpChunkedSameBlockCloseSeededTraceResultAtSegment_matchesReadStore
    (shape : Cartesian.CartesianShape) (fringeSegment : Nat)
    (blockSize leftClose rightClose seed : Nat)
    (store : WordRAM.ReadStore)
    (hbpCode :
      forall index,
        store.readWord? 0 index =
          (SuccinctSpace.chunkPayloadWords
            (SuccinctRank.machineWordBits shape.bpCode.length)
            shape.bpCode).toArray[index]?)
    (hfringe :
      forall address,
        store.readWord? fringeSegment address =
          (bpFringeChunkTable
            (bpFringeChunkBits shape.bpCode.length)).store.words[address]?) :
    forall event,
      List.Mem event
          (bpChunkedSameBlockCloseSeededTraceResultAtSegment
            shape fringeSegment blockSize leftClose rightClose seed).trace ->
        event.matchesReadStore store := by
  apply bpChunkedSameBlockCloseSeededTraceResultAtSegment_trace_forall
  · exact
      localBPWindowBitsTraceResult_matchesReadStore shape blockSize
        leftClose store hbpCode
  · intro address _hlt
    show store.readWord? fringeSegment address = _
    exact hfringe address

theorem bpChunkedSameBlockCloseSeededTraceResultAtSegment_no_syntheticCostOnlyPrimitive
    (shape : Cartesian.CartesianShape) (fringeSegment : Nat)
    (blockSize leftClose rightClose seed : Nat) :
    forall event,
      List.Mem event
          (bpChunkedSameBlockCloseSeededTraceResultAtSegment
            shape fringeSegment blockSize leftClose rightClose seed).trace ->
        Not event.isSyntheticCostOnlyPrimitive := by
  apply bpChunkedSameBlockCloseSeededTraceResultAtSegment_trace_forall
  · exact
      localBPWindowBitsTraceResult_no_syntheticCostOnlyPrimitive shape
        blockSize leftClose
  · intro address _hlt
    simp [WordRAM.TraceEvent.isSyntheticCostOnlyPrimitive]

/-! ## Supplied-store twins -/

theorem bpChunkedSameBlockCloseSeededTraceResultAtSegmentWithStore_eq_of_agree
    {shape : Cartesian.CartesianShape} {store : WordRAM.ReadStore}
    {fringeSegment : Nat}
    (hbpCode :
      forall index,
        store.readWord? 0 index =
          (SuccinctSpace.chunkPayloadWords
            (SuccinctRank.machineWordBits shape.bpCode.length)
            shape.bpCode).toArray[index]?)
    (hfringe :
      forall address,
        store.readWord? fringeSegment address =
          (bpFringeChunkTable
            (bpFringeChunkBits shape.bpCode.length)).store.words[address]?)
    (blockSize leftClose rightClose seed : Nat) :
    bpChunkedSameBlockCloseSeededTraceResultAtSegmentWithStore
        shape store fringeSegment blockSize leftClose rightClose seed =
      bpChunkedSameBlockCloseSeededTraceResultAtSegment
        shape fringeSegment blockSize leftClose rightClose seed := by
  unfold bpChunkedSameBlockCloseSeededTraceResultAtSegmentWithStore
    bpChunkedSameBlockCloseSeededTraceResultAtSegment
  rw [localBPWindowBitsTraceResultWithStore_eq_of_agree hbpCode]
  simp only [bpFringeChunkFoldTraceResultAtSegmentWithStore_eq_of_agree
    (bpFringeChunkTable (bpFringeChunkBits shape.bpCode.length)) hfringe]

theorem bpChunkedSameBlockCloseSeededTraceResultAtSegmentWithStore_store_parametric
    (shape : Cartesian.CartesianShape)
    {storeA storeB : WordRAM.ReadStore} {fringeSegment : Nat}
    (hbp :
      forall index,
        storeA.readWord? 0 index = storeB.readWord? 0 index)
    (hfringe :
      forall address,
        storeA.readWord? fringeSegment address =
          storeB.readWord? fringeSegment address)
    (blockSize leftClose rightClose seed : Nat) :
    bpChunkedSameBlockCloseSeededTraceResultAtSegmentWithStore
        shape storeA fringeSegment blockSize leftClose rightClose seed =
      bpChunkedSameBlockCloseSeededTraceResultAtSegmentWithStore
        shape storeB fringeSegment blockSize leftClose rightClose seed := by
  unfold bpChunkedSameBlockCloseSeededTraceResultAtSegmentWithStore
  rw [localBPWindowBitsTraceResultWithStore_store_parametric shape hbp]
  simp only [bpFringeChunkFoldTraceResultAtSegmentWithStore_store_parametric
    hfringe]

theorem bpChunkedSameBlockCloseSeededTraceResultAtSegmentWithStore_matchesReadStore
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (fringeSegment blockSize leftClose rightClose seed : Nat) :
    forall event,
      List.Mem event
          (bpChunkedSameBlockCloseSeededTraceResultAtSegmentWithStore
            shape store fringeSegment blockSize leftClose rightClose
            seed).trace ->
        event.matchesReadStore store := by
  unfold bpChunkedSameBlockCloseSeededTraceResultAtSegmentWithStore
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      localBPWindowBitsTraceResultWithStore_matchesReadStore
        shape store blockSize leftClose
  · apply WordRAM.TraceResult.map_trace_forall
    exact
      bpFringeChunkFoldTraceResultAtSegmentWithStore_matchesReadStore
        store fringeSegment _ _ seed _ _ _

theorem bpChunkedSameBlockCloseSeededTraceResultAtSegmentWithStore_no_syntheticCostOnlyPrimitive
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (fringeSegment blockSize leftClose rightClose seed : Nat) :
    forall event,
      List.Mem event
          (bpChunkedSameBlockCloseSeededTraceResultAtSegmentWithStore
            shape store fringeSegment blockSize leftClose rightClose
            seed).trace ->
        Not event.isSyntheticCostOnlyPrimitive := by
  unfold bpChunkedSameBlockCloseSeededTraceResultAtSegmentWithStore
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      localBPWindowBitsTraceResultWithStore_no_syntheticCostOnlyPrimitive
        shape store blockSize leftClose
  · apply WordRAM.TraceResult.map_trace_forall
    exact
      bpFringeChunkFoldTraceResultAtSegmentWithStore_no_syntheticCostOnlyPrimitive
        store fringeSegment _ _ seed _ _ _

/-! ## Decoded twins (rank seed threaded exactly as on the accepted route) -/

/--
Charged chunked same-block close trace with the directory rank seed threaded
exactly as `localBPSameBlockCloseDecodedTraceResultWithRankSeed` threads it.
-/
def bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegment
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (fringeSegment : Nat)
    (blockSize leftClose rightClose : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  WordRAM.TraceResult.bind
    (localBPSeedFromRankCloseTraceResult
      shape rankCloseTrace blockSize leftClose)
    fun seed =>
      bpChunkedSameBlockCloseSeededTraceResultAtSegment
        shape fringeSegment blockSize leftClose rightClose seed

/-- Store-parameterized decoded charged same-block close trace. -/
def bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegmentWithStore
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (fringeSegment : Nat)
    (store : WordRAM.ReadStore)
    (blockSize leftClose rightClose : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  WordRAM.TraceResult.bind
    (localBPSeedFromRankCloseTraceResult
      shape rankCloseTrace blockSize leftClose)
    fun seed =>
      bpChunkedSameBlockCloseSeededTraceResultAtSegmentWithStore
        shape store fringeSegment blockSize leftClose rightClose seed

theorem bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegment_refines
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (rankCloseCosted : Nat -> Costed Nat)
    (fringeSegment : Nat)
    (blockSize leftClose rightClose : Nat)
    (hrank :
      forall pos, (rankCloseTrace pos).toCosted = rankCloseCosted pos) :
    (bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegment
      shape rankCloseTrace fringeSegment blockSize leftClose
      rightClose).toCosted =
      bpChunkedSameBlockCloseDecodedCostedWithRankSeed
        shape rankCloseCosted blockSize leftClose rightClose := by
  simp [bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegment,
    bpChunkedSameBlockCloseDecodedCostedWithRankSeed,
    localBPSeedFromRankCloseTraceResult_refines,
    bpChunkedSameBlockCloseSeededTraceResultAtSegment_refines, hrank]

theorem bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegmentWithStore_eq_of_agree
    {shape : Cartesian.CartesianShape} {store : WordRAM.ReadStore}
    {fringeSegment : Nat}
    (hbpCode :
      forall index,
        store.readWord? 0 index =
          (SuccinctSpace.chunkPayloadWords
            (SuccinctRank.machineWordBits shape.bpCode.length)
            shape.bpCode).toArray[index]?)
    (hfringe :
      forall address,
        store.readWord? fringeSegment address =
          (bpFringeChunkTable
            (bpFringeChunkBits shape.bpCode.length)).store.words[address]?)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (blockSize leftClose rightClose : Nat) :
    bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegmentWithStore
        shape rankCloseTrace fringeSegment store blockSize leftClose
        rightClose =
      bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegment
        shape rankCloseTrace fringeSegment blockSize leftClose rightClose := by
  unfold
    bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegmentWithStore
    bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegment
  simp only
    [bpChunkedSameBlockCloseSeededTraceResultAtSegmentWithStore_eq_of_agree
      hbpCode hfringe]

theorem bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegmentWithStore_store_parametric
    (shape : Cartesian.CartesianShape)
    {storeA storeB : WordRAM.ReadStore} {fringeSegment : Nat}
    (hbp :
      forall index,
        storeA.readWord? 0 index = storeB.readWord? 0 index)
    (hfringe :
      forall address,
        storeA.readWord? fringeSegment address =
          storeB.readWord? fringeSegment address)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (blockSize leftClose rightClose : Nat) :
    bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegmentWithStore
        shape rankCloseTrace fringeSegment storeA blockSize leftClose
        rightClose =
      bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegmentWithStore
        shape rankCloseTrace fringeSegment storeB blockSize leftClose
        rightClose := by
  unfold
    bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegmentWithStore
  simp only
    [bpChunkedSameBlockCloseSeededTraceResultAtSegmentWithStore_store_parametric
      shape hbp hfringe]

end ConcreteCompactBPCloseLCADirectory

end SuccinctClose

end RMQ
