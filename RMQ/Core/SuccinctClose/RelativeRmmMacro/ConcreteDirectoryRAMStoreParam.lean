import RMQ.Core.SuccinctClose.RelativeRmmMacro.ConcreteDirectoryRAM
import RMQ.Core.WordRAM.ReadStoreEval

/-!
# Store-parametric compact LCA-close evaluators

Store-parameterized (`WithStore`) twins of the structural trace evaluators
behind the all-size compact LCA-close leg.  Every BP-code payload read takes
both its value and its trace-event word from a supplied `WordRAM.ReadStore` at
segment `0`, mirroring the zero-block store-parametric leaf already present in
`ConcreteDirectoryRAM.lean`.  The rank seed stays an abstract
`Nat -> WordRAM.TraceResult Nat` parameter, so callers can supply the
store-parametric final false-rank leaf.
-/

namespace RMQ

namespace SuccinctClose

namespace ConcreteCompactBPCloseLCADirectory

/-- Store-parameterized BP-code payload word read at global segment `0`. -/
def bpCodeWordReadTraceResultWithStore
    (store : WordRAM.ReadStore) (index : Nat) :
    WordRAM.TraceResult (List (List Bool)) where
  value := readStorePayloadWordValue store 0 index
  trace := [WordRAM.TraceEvent.readWord 0 index (store.readWord? 0 index)]

theorem bpCodeWordReadTraceResultWithStore_eq_of_agree
    {shape : Cartesian.CartesianShape} {store : WordRAM.ReadStore}
    (hbpCode :
      forall index,
        store.readWord? 0 index =
          (SuccinctSpace.chunkPayloadWords
            (SuccinctRank.machineWordBits shape.bpCode.length)
            shape.bpCode).toArray[index]?)
    (index : Nat) :
    bpCodeWordReadTraceResultWithStore store index =
      bpCodeWordReadTraceResult shape index := by
  cases harr :
      (SuccinctSpace.chunkPayloadWords
        (SuccinctRank.machineWordBits shape.bpCode.length)
        shape.bpCode).toArray[index]? <;>
    simp [bpCodeWordReadTraceResultWithStore, bpCodeWordReadTraceResult,
      bpCodeReadWordTraceEvent, readStorePayloadWordValue,
      payloadWordReadOfGet?, hbpCode index, harr]

theorem bpCodeWordReadTraceResultWithStore_store_parametric
    {storeA storeB : WordRAM.ReadStore}
    (hread :
      forall index,
        storeA.readWord? 0 index = storeB.readWord? 0 index)
    (index : Nat) :
    bpCodeWordReadTraceResultWithStore storeA index =
      bpCodeWordReadTraceResultWithStore storeB index := by
  unfold bpCodeWordReadTraceResultWithStore readStorePayloadWordValue
  rw [hread index]

theorem bpCodeWordReadTraceResultWithStore_matchesReadStore
    (store : WordRAM.ReadStore) (index : Nat) :
    forall event,
      event ∈ (bpCodeWordReadTraceResultWithStore store index).trace ->
        event.matchesReadStore store := by
  intro event hmem
  simp [bpCodeWordReadTraceResultWithStore] at hmem
  subst event
  rfl

/-- Store-parameterized four-word local BP block read. -/
def localBPBlockWordsTraceResultWithStore
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (blockSize close : Nat) : WordRAM.TraceResult (List (List Bool)) :=
  let wordSize := SuccinctRank.machineWordBits shape.bpCode.length
  let firstWord :=
    blockStartOf blockSize (blockOfClose blockSize close) / wordSize
  WordRAM.TraceResult.bind (bpCodeWordReadTraceResultWithStore store firstWord)
    fun w0 =>
      WordRAM.TraceResult.bind
        (bpCodeWordReadTraceResultWithStore store (firstWord + 1))
        fun w1 =>
          WordRAM.TraceResult.bind
            (bpCodeWordReadTraceResultWithStore store (firstWord + 2))
            fun w2 =>
              WordRAM.TraceResult.map
                (fun w3 => w0 ++ w1 ++ w2 ++ w3)
                (bpCodeWordReadTraceResultWithStore store (firstWord + 3))

theorem localBPBlockWordsTraceResultWithStore_eq_of_agree
    {shape : Cartesian.CartesianShape} {store : WordRAM.ReadStore}
    (hbpCode :
      forall index,
        store.readWord? 0 index =
          (SuccinctSpace.chunkPayloadWords
            (SuccinctRank.machineWordBits shape.bpCode.length)
            shape.bpCode).toArray[index]?)
    (blockSize close : Nat) :
    localBPBlockWordsTraceResultWithStore shape store blockSize close =
      localBPBlockWordsTraceResult shape blockSize close := by
  unfold localBPBlockWordsTraceResultWithStore localBPBlockWordsTraceResult
  simp only [bpCodeWordReadTraceResultWithStore_eq_of_agree hbpCode]

theorem localBPBlockWordsTraceResultWithStore_store_parametric
    (shape : Cartesian.CartesianShape)
    {storeA storeB : WordRAM.ReadStore}
    (hread :
      forall index,
        storeA.readWord? 0 index = storeB.readWord? 0 index)
    (blockSize close : Nat) :
    localBPBlockWordsTraceResultWithStore shape storeA blockSize close =
      localBPBlockWordsTraceResultWithStore shape storeB blockSize close := by
  unfold localBPBlockWordsTraceResultWithStore
  simp only [bpCodeWordReadTraceResultWithStore_store_parametric hread]

theorem localBPBlockWordsTraceResultWithStore_matchesReadStore
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (blockSize close : Nat) :
    forall event,
      event ∈
          (localBPBlockWordsTraceResultWithStore
            shape store blockSize close).trace ->
        event.matchesReadStore store := by
  unfold localBPBlockWordsTraceResultWithStore
  apply WordRAM.TraceResult.bind_trace_forall
  · exact bpCodeWordReadTraceResultWithStore_matchesReadStore store _
  · apply WordRAM.TraceResult.bind_trace_forall
    · exact bpCodeWordReadTraceResultWithStore_matchesReadStore store _
    · apply WordRAM.TraceResult.bind_trace_forall
      · exact bpCodeWordReadTraceResultWithStore_matchesReadStore store _
      · apply WordRAM.TraceResult.map_trace_forall
        exact bpCodeWordReadTraceResultWithStore_matchesReadStore store _

/-- Store-parameterized local BP window bits. -/
def localBPWindowBitsTraceResultWithStore
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (blockSize close : Nat) : WordRAM.TraceResult (List Bool) :=
  WordRAM.TraceResult.map SuccinctSpace.flattenPayloadWords
    (localBPBlockWordsTraceResultWithStore shape store blockSize close)

theorem localBPWindowBitsTraceResultWithStore_eq_of_agree
    {shape : Cartesian.CartesianShape} {store : WordRAM.ReadStore}
    (hbpCode :
      forall index,
        store.readWord? 0 index =
          (SuccinctSpace.chunkPayloadWords
            (SuccinctRank.machineWordBits shape.bpCode.length)
            shape.bpCode).toArray[index]?)
    (blockSize close : Nat) :
    localBPWindowBitsTraceResultWithStore shape store blockSize close =
      localBPWindowBitsTraceResult shape blockSize close := by
  unfold localBPWindowBitsTraceResultWithStore localBPWindowBitsTraceResult
  rw [localBPBlockWordsTraceResultWithStore_eq_of_agree hbpCode]

theorem localBPWindowBitsTraceResultWithStore_store_parametric
    (shape : Cartesian.CartesianShape)
    {storeA storeB : WordRAM.ReadStore}
    (hread :
      forall index,
        storeA.readWord? 0 index = storeB.readWord? 0 index)
    (blockSize close : Nat) :
    localBPWindowBitsTraceResultWithStore shape storeA blockSize close =
      localBPWindowBitsTraceResultWithStore shape storeB blockSize close := by
  unfold localBPWindowBitsTraceResultWithStore
  rw [localBPBlockWordsTraceResultWithStore_store_parametric shape hread]

theorem localBPWindowBitsTraceResultWithStore_matchesReadStore
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (blockSize close : Nat) :
    forall event,
      event ∈
          (localBPWindowBitsTraceResultWithStore
            shape store blockSize close).trace ->
        event.matchesReadStore store := by
  unfold localBPWindowBitsTraceResultWithStore
  apply WordRAM.TraceResult.map_trace_forall
  exact
    localBPBlockWordsTraceResultWithStore_matchesReadStore
      shape store blockSize close

/-- Store-parameterized seeded same-block local BP decoder. -/
def localBPSameBlockCloseSeededTraceResultWithStore
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (blockSize leftClose rightClose seed : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  let base := localBPWindowBase shape blockSize leftClose
  let start := leftClose + 1
  let count := rightClose - leftClose + 1
  WordRAM.TraceResult.map
    (fun window =>
      bpCandidateClose?
        (some
          (localBPSeededPrefixRangeMinExcess window seed base start count,
            localBPSeededPrefixRangeArgMinPrefixPos window seed base
              start count)))
    (localBPWindowBitsTraceResultWithStore shape store blockSize leftClose)

theorem localBPSameBlockCloseSeededTraceResultWithStore_eq_of_agree
    {shape : Cartesian.CartesianShape} {store : WordRAM.ReadStore}
    (hbpCode :
      forall index,
        store.readWord? 0 index =
          (SuccinctSpace.chunkPayloadWords
            (SuccinctRank.machineWordBits shape.bpCode.length)
            shape.bpCode).toArray[index]?)
    (blockSize leftClose rightClose seed : Nat) :
    localBPSameBlockCloseSeededTraceResultWithStore
        shape store blockSize leftClose rightClose seed =
      localBPSameBlockCloseSeededTraceResult
        shape blockSize leftClose rightClose seed := by
  unfold localBPSameBlockCloseSeededTraceResultWithStore
    localBPSameBlockCloseSeededTraceResult
  rw [localBPWindowBitsTraceResultWithStore_eq_of_agree hbpCode]

theorem localBPSameBlockCloseSeededTraceResultWithStore_store_parametric
    (shape : Cartesian.CartesianShape)
    {storeA storeB : WordRAM.ReadStore}
    (hread :
      forall index,
        storeA.readWord? 0 index = storeB.readWord? 0 index)
    (blockSize leftClose rightClose seed : Nat) :
    localBPSameBlockCloseSeededTraceResultWithStore
        shape storeA blockSize leftClose rightClose seed =
      localBPSameBlockCloseSeededTraceResultWithStore
        shape storeB blockSize leftClose rightClose seed := by
  unfold localBPSameBlockCloseSeededTraceResultWithStore
  rw [localBPWindowBitsTraceResultWithStore_store_parametric shape hread]

theorem localBPSameBlockCloseSeededTraceResultWithStore_matchesReadStore
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (blockSize leftClose rightClose seed : Nat) :
    forall event,
      event ∈
          (localBPSameBlockCloseSeededTraceResultWithStore
            shape store blockSize leftClose rightClose seed).trace ->
        event.matchesReadStore store := by
  unfold localBPSameBlockCloseSeededTraceResultWithStore
  apply WordRAM.TraceResult.map_trace_forall
  exact
    localBPWindowBitsTraceResultWithStore_matchesReadStore
      shape store blockSize leftClose

/-- Store-parameterized same-block close decoder with an abstract rank seed. -/
def localBPSameBlockCloseDecodedTraceResultWithRankSeedWithStore
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (store : WordRAM.ReadStore)
    (blockSize leftClose rightClose : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  WordRAM.TraceResult.bind
    (localBPSeedFromRankCloseTraceResult
      shape rankCloseTrace blockSize leftClose)
    fun seed =>
      localBPSameBlockCloseSeededTraceResultWithStore
        shape store blockSize leftClose rightClose seed

theorem localBPSameBlockCloseDecodedTraceResultWithRankSeedWithStore_eq_of_agree
    {shape : Cartesian.CartesianShape}
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    {store : WordRAM.ReadStore}
    (hbpCode :
      forall index,
        store.readWord? 0 index =
          (SuccinctSpace.chunkPayloadWords
            (SuccinctRank.machineWordBits shape.bpCode.length)
            shape.bpCode).toArray[index]?)
    (blockSize leftClose rightClose : Nat) :
    localBPSameBlockCloseDecodedTraceResultWithRankSeedWithStore
        shape rankCloseTrace store blockSize leftClose rightClose =
      localBPSameBlockCloseDecodedTraceResultWithRankSeed
        shape rankCloseTrace blockSize leftClose rightClose := by
  unfold localBPSameBlockCloseDecodedTraceResultWithRankSeedWithStore
    localBPSameBlockCloseDecodedTraceResultWithRankSeed
  simp only [localBPSameBlockCloseSeededTraceResultWithStore_eq_of_agree
    hbpCode]

theorem localBPSameBlockCloseDecodedTraceResultWithRankSeedWithStore_store_parametric
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    {storeA storeB : WordRAM.ReadStore}
    (hread :
      forall index,
        storeA.readWord? 0 index = storeB.readWord? 0 index)
    (blockSize leftClose rightClose : Nat) :
    localBPSameBlockCloseDecodedTraceResultWithRankSeedWithStore
        shape rankCloseTrace storeA blockSize leftClose rightClose =
      localBPSameBlockCloseDecodedTraceResultWithRankSeedWithStore
        shape rankCloseTrace storeB blockSize leftClose rightClose := by
  unfold localBPSameBlockCloseDecodedTraceResultWithRankSeedWithStore
  simp only [localBPSameBlockCloseSeededTraceResultWithStore_store_parametric
    shape hread]

theorem localBPSameBlockCloseDecodedTraceResultWithRankSeedWithStore_matchesReadStore
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (store : WordRAM.ReadStore)
    (blockSize leftClose rightClose : Nat)
    (hrank :
      forall pos event,
        List.Mem event (rankCloseTrace pos).trace ->
          event.matchesReadStore store) :
    forall event,
      event ∈
          (localBPSameBlockCloseDecodedTraceResultWithRankSeedWithStore
            shape rankCloseTrace store blockSize leftClose rightClose).trace ->
        event.matchesReadStore store := by
  unfold localBPSameBlockCloseDecodedTraceResultWithRankSeedWithStore
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      localBPSeedFromRankCloseTraceResult_trace_forall
        shape rankCloseTrace blockSize leftClose
        (fun event => event.matchesReadStore store) hrank
  · exact
      localBPSameBlockCloseSeededTraceResultWithStore_matchesReadStore
        shape store blockSize leftClose rightClose _

end ConcreteCompactBPCloseLCADirectory

end SuccinctClose

end RMQ
