import RMQ.Core.SuccinctClose.RelativeRmmMacro.ChargedFringeTrace
import RMQ.Core.SuccinctClose.RelativeRmmMacro.ChargedSameBlockChunks

/-!
# Canonical LCA-close dispatchers on the charged chunked fringe route

The canonical close/LCA dispatchers (`canonicalLcaCloseCostedWithRankSeed`
and its structural trace / supplied-store twins) moved here from
`ConcreteDirectoryRAM.lean` / `ConcreteDirectoryRAMStoreParam.lean` with one
change: the cross-block branch now calls the charged chunked fringe
consumers (`bpChunkedCrossBlockClose...`), so every endpoint-fringe
min-excess/argmin computation on the canonical route is paid for by
chunk-table reads at the fringe segment.  The historical event-silent
consumers (`canonicalCrossBlockCloseCostedWithRankSeed` and its trace twins)
are unchanged upstream; exactness of the swapped route is recovered through
the committed exact-value substitution theorems.

The structural trace dispatcher gains one `fringeSegment : Nat` parameter in
the house `AtSegments` style; the final layer instantiates it with the
global fringe chunk-table segment.
-/

namespace RMQ

namespace SuccinctClose

namespace ConcreteCompactBPCloseLCADirectory

open SuccinctSpace

/-- Canonical all-size close/LCA dispatcher on the chunked fringe route. -/
def canonicalLcaCloseCostedWithRankSeed
    (shape : Cartesian.CartesianShape)
    (rankCloseCosted : Nat -> Costed Nat)
    (leftClose rightClose : Nat) : Costed (Option Nat) :=
  let blockSize := canonicalBPRelativeSummaryBlockSizeRaw shape
  if blockOfClose blockSize leftClose =
      blockOfClose blockSize rightClose then
    localBPSameBlockCloseDecodedCostedWithRankSeed
      shape rankCloseCosted blockSize leftClose rightClose
  else
    bpChunkedCrossBlockCloseCostedWithRankSeed
      shape rankCloseCosted leftClose rightClose

/--
All-size structural close/LCA trace on the chunked fringe route.  The
endpoint rank seeds and same-block decoder are unchanged; the cross-block
branch charges its fringe chunk-table reads at `fringeSegment`.
-/
def lcaCloseTraceResultWithRankSeedAllSizeStructural
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (fringeSegment : Nat)
    (_sameBlockSegment : Nat)
    (leftClose rightClose : Nat) : WordRAM.TraceResult (Option Nat) :=
  let blockSize := canonicalBPRelativeSummaryBlockSizeRaw shape
  if blockOfClose blockSize leftClose =
      blockOfClose blockSize rightClose then
    localBPSameBlockCloseDecodedTraceResultWithRankSeed
      shape rankCloseTrace blockSize leftClose rightClose
  else
    bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegments
      shape rankCloseTrace segments fringeSegment leftClose rightClose

theorem lcaCloseTraceResultWithRankSeedAllSizeStructural_refines
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (rankCloseCosted : Nat -> Costed Nat)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (fringeSegment : Nat)
    (sameBlockSegment : Nat)
    (leftClose rightClose : Nat)
    (hrank :
      forall pos, (rankCloseTrace pos).toCosted = rankCloseCosted pos) :
    (lcaCloseTraceResultWithRankSeedAllSizeStructural
      shape rankCloseTrace segments fringeSegment sameBlockSegment
      leftClose rightClose).toCosted =
      canonicalLcaCloseCostedWithRankSeed
        shape rankCloseCosted leftClose rightClose := by
  let blockSize := canonicalBPRelativeSummaryBlockSizeRaw shape
  by_cases hsame :
      blockOfClose blockSize leftClose =
        blockOfClose blockSize rightClose
  case pos =>
    simp [lcaCloseTraceResultWithRankSeedAllSizeStructural,
      canonicalLcaCloseCostedWithRankSeed, blockSize, hsame,
      localBPSameBlockCloseDecodedTraceResultWithRankSeed_refines, hrank]
  case neg =>
    simp [lcaCloseTraceResultWithRankSeedAllSizeStructural,
      canonicalLcaCloseCostedWithRankSeed, blockSize, hsame,
      bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegments_refines,
      hrank]

/--
Transitional close/LCA cost cap for the chunked route.  Unlike the retired
event-silent route, the chunked cross-block branch charges up to `2 * 37`
fringe reads, so the transitional cap is recovered through the principled
interior bound and therefore requires the genuine close-position bounds.
-/
theorem canonicalLcaCloseCostedWithRankSeed_cost_le
    (shape : Cartesian.CartesianShape)
    (rankCloseCosted : Nat -> Costed Nat)
    (leftClose rightClose rankCost : Nat)
    (hleftCloseBound : leftClose < shape.bpCode.length)
    (hrightCloseBound : rightClose < shape.bpCode.length)
    (hrankCost : forall pos, (rankCloseCosted pos).cost <= rankCost) :
    (canonicalLcaCloseCostedWithRankSeed
      shape rankCloseCosted leftClose rightClose).cost <=
        canonicalCompactBPCloseQueryCostWithRankSeed rankCost := by
  let blockSize := canonicalBPRelativeSummaryBlockSizeRaw shape
  by_cases hsame :
      blockOfClose blockSize leftClose =
        blockOfClose blockSize rightClose
  case pos =>
    have hlocal :=
      localBPSameBlockCloseDecodedCostedWithRankSeed_cost_le
        shape rankCloseCosted blockSize leftClose rightClose rankCost
        hrankCost
    have hcap :
        rankCost + 4 <=
          canonicalCompactBPCloseQueryCostWithRankSeed rankCost := by
      unfold canonicalCompactBPCloseQueryCostWithRankSeed
      omega
    exact Nat.le_trans
      (by
        simpa [canonicalLcaCloseCostedWithRankSeed, blockSize, hsame] using
          hlocal)
      hcap
  case neg =>
    have hchunked :=
      bpChunkedCrossBlockCloseCostedWithRankSeed_cost_le_principled
        shape rankCloseCosted leftClose rightClose rankCost
        hleftCloseBound hrightCloseBound hrankCost
    have hcap :
        bpChunkedPrincipledBPCloseChargedTraceCostWithRankSeed rankCost <=
          canonicalCompactBPCloseQueryCostWithRankSeed rankCost := by
      unfold bpChunkedPrincipledBPCloseChargedTraceCostWithRankSeed
        bpChunkedEndpointFringeChargedTraceCost
        canonicalCompactBPCloseQueryCostWithRankSeed
        canonicalRelativeRmmPrincipledInteriorChargedTraceCost
        canonicalRelativeRmmInteriorQueryCost
      omega
    exact Nat.le_trans
      (by
        simpa [canonicalLcaCloseCostedWithRankSeed, blockSize, hsame] using
          hchunked)
      hcap

/-- The chunked all-size close/LCA execution obeys the chunked U3 cap. -/
theorem canonicalLcaCloseCostedWithRankSeed_cost_le_principled
    (shape : Cartesian.CartesianShape)
    (rankCloseCosted : Nat -> Costed Nat)
    (leftClose rightClose rankCost : Nat)
    (hleftCloseBound : leftClose < shape.bpCode.length)
    (hrightCloseBound : rightClose < shape.bpCode.length)
    (hrankCost : forall pos, (rankCloseCosted pos).cost <= rankCost) :
    (canonicalLcaCloseCostedWithRankSeed
      shape rankCloseCosted leftClose rightClose).cost <=
        bpChunkedPrincipledBPCloseChargedTraceCostWithRankSeed rankCost := by
  let blockSize := canonicalBPRelativeSummaryBlockSizeRaw shape
  by_cases hsame :
      blockOfClose blockSize leftClose = blockOfClose blockSize rightClose
  case pos =>
    have hlocal :=
      localBPSameBlockCloseDecodedCostedWithRankSeed_cost_le
        shape rankCloseCosted blockSize leftClose rightClose rankCost
        hrankCost
    have hcap :
        rankCost + 4 <=
          bpChunkedPrincipledBPCloseChargedTraceCostWithRankSeed rankCost := by
      unfold bpChunkedPrincipledBPCloseChargedTraceCostWithRankSeed
      unfold bpChunkedEndpointFringeChargedTraceCost
      unfold canonicalRelativeRmmPrincipledInteriorChargedTraceCost
      omega
    exact Nat.le_trans
      (by
        simpa [canonicalLcaCloseCostedWithRankSeed, blockSize, hsame] using
          hlocal)
      hcap
  case neg =>
    simpa [canonicalLcaCloseCostedWithRankSeed, blockSize, hsame] using
      bpChunkedCrossBlockCloseCostedWithRankSeed_cost_le_principled
        shape rankCloseCosted leftClose rightClose rankCost
        hleftCloseBound hrightCloseBound hrankCost

/-- Chunked all-size close/LCA execution is exact for every valid RMQ query. -/
theorem canonicalLcaCloseCostedWithRankSeed_exact_of_query
    {shape : Cartesian.CartesianShape}
    (rankCloseCosted : Nat -> Costed Nat)
    {left len leftClose rightClose answerClose : Nat}
    (hrankExact :
      forall pos,
        (rankCloseCosted pos).erase =
          Succinct.rankPrefix false shape.bpCode pos)
    (hlen : 0 < len)
    (hbound : left + len <= shape.size)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder? shape
          (scanWindow shape.representative left len) =
        some answerClose) :
    (canonicalLcaCloseCostedWithRankSeed
      shape rankCloseCosted leftClose rightClose).erase =
        some answerClose := by
  let blockSize := canonicalBPRelativeSummaryBlockSizeRaw shape
  have hsizePos : 0 < shape.size := by omega
  have hblockSizePos : 0 < blockSize := by
    simpa [blockSize] using
      canonicalBPRelativeSummaryBlockSizeRaw_pos shape
  have hblockSizeLeTwo :
      blockSize <=
        2 * SuccinctRank.machineWordBits shape.bpCode.length := by
    simpa [blockSize] using
      canonicalBPRelativeSummaryBlockSizeRaw_le_two_machine_of_size_pos
        (shape := shape) hsizePos
  have hblockSizeLeThree :
      blockSize <=
        3 * SuccinctRank.machineWordBits shape.bpCode.length := by
    omega
  by_cases hsame :
      blockOfClose blockSize leftClose =
        blockOfClose blockSize rightClose
  case pos =>
    simpa [canonicalLcaCloseCostedWithRankSeed, blockSize, hsame] using
      localBPSameBlockCloseDecodedCostedWithRankSeed_exact_of_query_same_block
        (shape := shape) (rankCloseCosted := rankCloseCosted)
        (blockSize := blockSize) (left := left) (len := len)
        (leftClose := leftClose) (rightClose := rightClose)
        (answerClose := answerClose)
        hrankExact hblockSizePos hblockSizeLeThree hsame
        hlen hbound hleft hright hanswer
  case neg =>
    have hbetween :=
      answerClose_between_endpoint_closes
        (shape := shape) (left := left) (len := len)
        (leftClose := leftClose) (rightClose := rightClose)
        (answerClose := answerClose)
        hlen hleft hright hanswer
    have hblockLe :
        blockOfClose blockSize leftClose <=
          blockOfClose blockSize rightClose := by
      unfold blockOfClose
      exact Nat.div_le_div_right (Nat.le_trans hbetween.1 hbetween.2)
    have hcross :
        blockOfClose blockSize leftClose <
          blockOfClose blockSize rightClose := by
      omega
    have hvalue :=
      bpChunkedCrossBlockCloseCostedWithRankSeed_value_eq
        (shape := shape) (rankCloseCosted := rankCloseCosted)
        (left := left) (len := len)
        hrankExact hlen hbound hleft hright
        (by simpa [blockSize] using hcross)
    have haccepted :=
      canonicalCrossBlockCloseCostedWithRankSeed_exact_of_query
        rankCloseCosted hrankExact hlen hbound hleft hright hanswer
        (by simpa [blockSize] using hcross)
    have hchunked :
        (bpChunkedCrossBlockCloseCostedWithRankSeed
          shape rankCloseCosted leftClose rightClose).erase =
          some answerClose := by
      show (bpChunkedCrossBlockCloseCostedWithRankSeed
        shape rankCloseCosted leftClose rightClose).value = some answerClose
      rw [hvalue]
      exact haccepted
    simpa [canonicalLcaCloseCostedWithRankSeed, blockSize, hsame] using
      hchunked

theorem lcaCloseTraceResultWithRankSeedAllSizeStructural_trace_forall
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (fringeSegment : Nat)
    (sameBlockSegment : Nat)
    (leftClose rightClose : Nat)
    (P : WordRAM.TraceEvent -> Prop)
    (hrank :
      forall pos event,
        List.Mem event (rankCloseTrace pos).trace -> P event)
    (hbp :
      forall blockSize close event,
        List.Mem event
          (localBPWindowBitsTraceResult shape blockSize close).trace ->
          P event)
    (hfringeLeft :
      forall blockSize close seed event,
        List.Mem event
          (bpChunkedLeftFringeCandidateSeededTraceResultAtSegment
            shape fringeSegment blockSize close seed).trace ->
          P event)
    (hfringeRight :
      forall blockSize close seed event,
        List.Mem event
          (bpChunkedRightFringeCandidateSeededTraceResultAtSegment
            shape fringeSegment blockSize close seed).trace ->
          P event)
    (hinterior :
      forall startBlock count event,
        List.Mem event
          (concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructural
            shape segments startBlock count).trace ->
          P event) :
    forall event,
      List.Mem event
          (lcaCloseTraceResultWithRankSeedAllSizeStructural
            shape rankCloseTrace segments fringeSegment sameBlockSegment
            leftClose rightClose).trace ->
        P event := by
  let blockSize := canonicalBPRelativeSummaryBlockSizeRaw shape
  by_cases hsame :
      blockOfClose blockSize leftClose =
        blockOfClose blockSize rightClose
  case pos =>
    simpa [lcaCloseTraceResultWithRankSeedAllSizeStructural, blockSize,
      hsame] using
      localBPSameBlockCloseDecodedTraceResultWithRankSeed_trace_forall
        shape rankCloseTrace blockSize leftClose rightClose P hrank
        (hbp blockSize leftClose)
  case neg =>
    simpa [lcaCloseTraceResultWithRankSeedAllSizeStructural, blockSize,
      hsame] using
      bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegments_trace_forall
        shape rankCloseTrace segments fringeSegment leftClose rightClose P
        hrank hfringeLeft hfringeRight hinterior

theorem lcaCloseTraceResultWithRankSeedAllSizeStructural_no_syntheticCostOnlyPrimitive
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (fringeSegment : Nat)
    (sameBlockSegment : Nat)
    (leftClose rightClose : Nat)
    (hrank :
      forall pos event,
        List.Mem event (rankCloseTrace pos).trace ->
          ¬ event.isSyntheticCostOnlyPrimitive) :
    forall event,
      List.Mem event
          (lcaCloseTraceResultWithRankSeedAllSizeStructural
            shape rankCloseTrace segments fringeSegment sameBlockSegment
            leftClose rightClose).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  exact
    lcaCloseTraceResultWithRankSeedAllSizeStructural_trace_forall
      shape rankCloseTrace segments fringeSegment sameBlockSegment
      leftClose rightClose
      (fun event => ¬ event.isSyntheticCostOnlyPrimitive)
      hrank
      (fun blockSize close =>
        localBPWindowBitsTraceResult_no_syntheticCostOnlyPrimitive
          shape blockSize close)
      (fun blockSize close seed =>
        bpChunkedLeftFringeCandidateSeededTraceResultAtSegment_no_syntheticCostOnlyPrimitive
          shape fringeSegment blockSize close seed)
      (fun blockSize close seed =>
        bpChunkedRightFringeCandidateSeededTraceResultAtSegment_no_syntheticCostOnlyPrimitive
          shape fringeSegment blockSize close seed)
      (fun startBlock count =>
        concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructural_no_syntheticCostOnlyPrimitive
          shape segments startBlock count)

theorem lcaCloseTraceResultWithRankSeedAllSizeStructural_matchesReadStore
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (fringeSegment : Nat)
    (sameBlockSegment : Nat)
    (leftClose rightClose : Nat)
    (store : WordRAM.ReadStore)
    (hrank :
      forall pos event,
        List.Mem event (rankCloseTrace pos).trace ->
          event.matchesReadStore store)
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
    (hinterior :
      forall startBlock count event,
        List.Mem event
          (concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructural
            shape segments startBlock count).trace ->
          event.matchesReadStore store) :
    forall event,
      List.Mem event
          (lcaCloseTraceResultWithRankSeedAllSizeStructural
            shape rankCloseTrace segments fringeSegment sameBlockSegment
            leftClose rightClose).trace ->
        event.matchesReadStore store := by
  exact
    lcaCloseTraceResultWithRankSeedAllSizeStructural_trace_forall
      shape rankCloseTrace segments fringeSegment sameBlockSegment
      leftClose rightClose
      (fun event => event.matchesReadStore store)
      hrank
      (fun blockSize close =>
        localBPWindowBitsTraceResult_matchesReadStore
          shape blockSize close store hbpCode)
      (fun blockSize close seed =>
        bpChunkedLeftFringeCandidateSeededTraceResultAtSegment_matchesReadStore
          shape fringeSegment blockSize close seed store hbpCode hfringe)
      (fun blockSize close seed =>
        bpChunkedRightFringeCandidateSeededTraceResultAtSegment_matchesReadStore
          shape fringeSegment blockSize close seed store hbpCode hfringe)
      hinterior

/-! ## Supplied-store dispatcher -/

/-- Canonical supplied-store LCA-close route on the chunked fringe. -/
def lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (fringeSegment : Nat)
    (store : WordRAM.ReadStore)
    (_sameBlockSegment : Nat)
    (leftClose rightClose : Nat) : WordRAM.TraceResult (Option Nat) :=
  let blockSize := canonicalBPRelativeSummaryBlockSizeRaw shape
  if blockOfClose blockSize leftClose =
      blockOfClose blockSize rightClose then
    localBPSameBlockCloseDecodedTraceResultWithRankSeedWithStore
      shape rankCloseTrace store blockSize leftClose rightClose
  else
    bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
      shape rankCloseTrace segments fringeSegment store leftClose
      rightClose

theorem lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore_eq_of_agree
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (segments : BPRelativeRmmInteriorTraceSegments)
    {fringeSegment : Nat}
    {store : WordRAM.ReadStore}
    (sameBlockSegment leftClose rightClose : Nat)
    (hbpCode :
      forall index,
        store.readWord? 0 index =
          (SuccinctSpace.chunkPayloadWords
            (SuccinctRank.machineWordBits shape.bpCode.length)
            shape.bpCode).toArray[index]?)
    (hcomponent :
      forall address,
        store.readWord? segments.canonicalComponent address =
          (canonicalRelativeRmmInteriorComponentStore shape).store.words[address]?)
    (hfringe :
      forall address,
        store.readWord? fringeSegment address =
          (bpFringeChunkTable
            (bpFringeChunkBits shape.bpCode.length)).store.words[address]?) :
    lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore
        shape rankCloseTrace segments fringeSegment store sameBlockSegment
        leftClose rightClose =
      lcaCloseTraceResultWithRankSeedAllSizeStructural
        shape rankCloseTrace segments fringeSegment sameBlockSegment
        leftClose rightClose := by
  unfold lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore
  unfold lcaCloseTraceResultWithRankSeedAllSizeStructural
  let blockSize := canonicalBPRelativeSummaryBlockSizeRaw shape
  by_cases hsame :
      blockOfClose blockSize leftClose =
        blockOfClose blockSize rightClose
  case pos =>
    simp [blockSize, hsame,
      localBPSameBlockCloseDecodedTraceResultWithRankSeedWithStore_eq_of_agree
        rankCloseTrace hbpCode]
  case neg =>
    simp [blockSize, hsame,
      bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore_eq_of_agree
        shape rankCloseTrace segments hbpCode hcomponent hfringe]

theorem lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore_refines_of_agree
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (rankCloseCosted : Nat -> Costed Nat)
    (segments : BPRelativeRmmInteriorTraceSegments)
    {fringeSegment : Nat}
    {store : WordRAM.ReadStore}
    (sameBlockSegment leftClose rightClose : Nat)
    (hbpCode :
      forall index,
        store.readWord? 0 index =
          (SuccinctSpace.chunkPayloadWords
            (SuccinctRank.machineWordBits shape.bpCode.length)
            shape.bpCode).toArray[index]?)
    (hcomponent :
      forall address,
        store.readWord? segments.canonicalComponent address =
          (canonicalRelativeRmmInteriorComponentStore shape).store.words[address]?)
    (hfringe :
      forall address,
        store.readWord? fringeSegment address =
          (bpFringeChunkTable
            (bpFringeChunkBits shape.bpCode.length)).store.words[address]?)
    (hrank :
      forall pos, (rankCloseTrace pos).toCosted = rankCloseCosted pos) :
    (lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore
      shape rankCloseTrace segments fringeSegment store sameBlockSegment
      leftClose rightClose).toCosted =
      canonicalLcaCloseCostedWithRankSeed
        shape rankCloseCosted leftClose rightClose := by
  rw [lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore_eq_of_agree
    shape rankCloseTrace segments sameBlockSegment leftClose rightClose
    hbpCode hcomponent hfringe]
  exact
    lcaCloseTraceResultWithRankSeedAllSizeStructural_refines
      shape rankCloseTrace rankCloseCosted segments fringeSegment
      sameBlockSegment leftClose rightClose hrank

theorem lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore_store_parametric
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (segments : BPRelativeRmmInteriorTraceSegments)
    {fringeSegment : Nat}
    {storeA storeB : WordRAM.ReadStore}
    (sameBlockSegment leftClose rightClose : Nat)
    (hbpCode :
      forall index, storeA.readWord? 0 index = storeB.readWord? 0 index)
    (hcomponent :
      forall address,
        storeA.readWord? segments.canonicalComponent address =
          storeB.readWord? segments.canonicalComponent address)
    (hfringe :
      forall address,
        storeA.readWord? fringeSegment address =
          storeB.readWord? fringeSegment address) :
    lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore
        shape rankCloseTrace segments fringeSegment storeA sameBlockSegment
        leftClose rightClose =
      lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore
        shape rankCloseTrace segments fringeSegment storeB sameBlockSegment
        leftClose rightClose := by
  unfold lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore
  let blockSize := canonicalBPRelativeSummaryBlockSizeRaw shape
  by_cases hsame :
      blockOfClose blockSize leftClose =
        blockOfClose blockSize rightClose
  case pos =>
    simp [blockSize, hsame,
      localBPSameBlockCloseDecodedTraceResultWithRankSeedWithStore_store_parametric
        shape rankCloseTrace hbpCode]
  case neg =>
    simp [blockSize, hsame,
      bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore_store_parametric
        shape rankCloseTrace segments hbpCode hcomponent hfringe]

theorem lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore_matchesReadStore
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (fringeSegment : Nat)
    (store : WordRAM.ReadStore)
    (sameBlockSegment leftClose rightClose : Nat)
    (hrank :
      forall pos event,
        List.Mem event (rankCloseTrace pos).trace ->
          event.matchesReadStore store) :
    forall event,
      List.Mem event
          (lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore
            shape rankCloseTrace segments fringeSegment store
            sameBlockSegment leftClose rightClose).trace ->
        event.matchesReadStore store := by
  unfold lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore
  let blockSize := canonicalBPRelativeSummaryBlockSizeRaw shape
  by_cases hsame :
      blockOfClose blockSize leftClose =
        blockOfClose blockSize rightClose
  case pos =>
    simpa [blockSize, hsame] using
      localBPSameBlockCloseDecodedTraceResultWithRankSeedWithStore_matchesReadStore
        shape rankCloseTrace store blockSize leftClose rightClose hrank
  case neg =>
    simpa [blockSize, hsame] using
      bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore_matchesReadStore
        shape rankCloseTrace segments fringeSegment store leftClose
        rightClose hrank

theorem lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore_no_syntheticCostOnlyPrimitive
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (fringeSegment : Nat)
    (store : WordRAM.ReadStore)
    (sameBlockSegment leftClose rightClose : Nat)
    (hrank :
      forall pos event,
        List.Mem event (rankCloseTrace pos).trace ->
          Not event.isSyntheticCostOnlyPrimitive) :
    forall event,
      List.Mem event
          (lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore
            shape rankCloseTrace segments fringeSegment store
            sameBlockSegment leftClose rightClose).trace ->
        Not event.isSyntheticCostOnlyPrimitive := by
  unfold lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore
  let blockSize := canonicalBPRelativeSummaryBlockSizeRaw shape
  by_cases hsame :
      blockOfClose blockSize leftClose =
        blockOfClose blockSize rightClose
  case pos =>
    simpa [blockSize, hsame] using
      localBPSameBlockCloseDecodedTraceResultWithRankSeedWithStore_no_syntheticCostOnlyPrimitive
        shape rankCloseTrace store blockSize leftClose rightClose hrank
  case neg =>
    simpa [blockSize, hsame] using
      bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore_no_syntheticCostOnlyPrimitive
        shape rankCloseTrace segments fringeSegment store leftClose
        rightClose hrank

end ConcreteCompactBPCloseLCADirectory

end SuccinctClose

end RMQ
