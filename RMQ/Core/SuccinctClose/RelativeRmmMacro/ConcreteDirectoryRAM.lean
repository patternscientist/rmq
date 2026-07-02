import RMQ.Core.SuccinctClose.RelativeRmmMacro.ConcreteDirectory
import RMQ.Core.SuccinctClose.EndpointFringe.InteriorCandidate.InteriorRAM
import RMQ.Core.SuccinctSpace.RankSelectRAM

/-!
# Word-RAM rank-seed bridge for compact BP close/LCA

This module connects the concrete compact close/LCA directory to the
interpreter-backed stored-word rank leaf.  The existing seeded close wrapper is
kept unchanged; the rank callback it consumes is now built directly from
`PayloadLiveStoredWordRankData.rankProgramClamped` and the corresponding
payload-only Word-RAM store.
-/

namespace RMQ
namespace SuccinctClose

open SuccinctSpace
open RMQ.WordRAM.Register

namespace ConcreteCompactBPCloseLCADirectory

/-- The chunked BP payload store used by local BP decoder traces. -/
def bpCodeWordStore (shape : Cartesian.CartesianShape) :
    SuccinctSpace.BoundedPayloadWordStore shape.bpCode
      (SuccinctRank.machineWordBits shape.bpCode.length) :=
  SuccinctSpace.BoundedPayloadWordStore.ofChunks shape.bpCode
    (SuccinctRank.machineWordBits_pos shape.bpCode.length)

/-- Trace event for reading one BP payload word from the chunked BP code. -/
def bpCodeReadWordTraceEvent
    (shape : Cartesian.CartesianShape) (index : Nat) : WordRAM.TraceEvent :=
  WordRAM.TraceEvent.readWord 0 index
    ((SuccinctSpace.chunkPayloadWords
      (SuccinctRank.machineWordBits shape.bpCode.length)
      shape.bpCode).toArray[index]?)

/-- A payload-word trace for one BP code word. -/
def bpCodeWordReadTraceResult
    (shape : Cartesian.CartesianShape) (index : Nat) :
    WordRAM.TraceResult (List (List Bool)) where
  value :=
    payloadWordReadOfGet?
      (SuccinctSpace.chunkPayloadWords
        (SuccinctRank.machineWordBits shape.bpCode.length)
        shape.bpCode).toArray index
  trace := [bpCodeReadWordTraceEvent shape index]

theorem bpCodeWordReadTraceResult_value
    (shape : Cartesian.CartesianShape) (index : Nat) :
    (bpCodeWordReadTraceResult shape index).value =
      payloadWordReadOfGet?
        (SuccinctSpace.chunkPayloadWords
          (SuccinctRank.machineWordBits shape.bpCode.length)
          shape.bpCode).toArray index := by
  rfl

theorem bpCodeWordReadTraceResult_event_value
    (shape : Cartesian.CartesianShape) (index : Nat) :
    (bpCodeReadWordTraceEvent shape index) =
      WordRAM.TraceEvent.readWord 0 index
      (SuccinctSpace.chunkPayloadWords
        (SuccinctRank.machineWordBits shape.bpCode.length)
        shape.bpCode).toArray[index]? := by
  rfl

/--
Trace-preserving read of the four BP payload words that cover a local BP block.

Missing boundary words contribute no payload word to the value but still count
as one attempted payload read in the trace.
-/
def localBPBlockWordsTraceResult
    (shape : Cartesian.CartesianShape)
    (blockSize close : Nat) : WordRAM.TraceResult (List (List Bool)) :=
  let wordSize := SuccinctRank.machineWordBits shape.bpCode.length
  let firstWord :=
    blockStartOf blockSize (blockOfClose blockSize close) / wordSize
  WordRAM.TraceResult.bind (bpCodeWordReadTraceResult shape firstWord)
    fun w0 =>
      WordRAM.TraceResult.bind
        (bpCodeWordReadTraceResult shape (firstWord + 1))
        fun w1 =>
          WordRAM.TraceResult.bind
            (bpCodeWordReadTraceResult shape (firstWord + 2))
            fun w2 =>
              WordRAM.TraceResult.map
                (fun w3 => w0 ++ w1 ++ w2 ++ w3)
                (bpCodeWordReadTraceResult shape (firstWord + 3))

theorem flatten_localBPBlockWordsTraceResult_value
    (shape : Cartesian.CartesianShape)
    (blockSize close : Nat) :
    SuccinctSpace.flattenPayloadWords
        (localBPBlockWordsTraceResult shape blockSize close).value =
      SuccinctSpace.flattenPayloadWords
        (localBPBlockWordsRead shape blockSize close) := by
  unfold localBPBlockWordsTraceResult localBPBlockWordsRead
    bpCodeWordReadTraceResult bpCodeWordReadsAt payloadWordReadOfGet?
  simp [WordRAM.TraceResult.bind, WordRAM.TraceResult.map,
    WordRAM.TraceResult.pure, SuccinctSpace.flattenPayloadWords_append]

theorem localBPBlockWordsTraceResult_cost
    (shape : Cartesian.CartesianShape)
    (blockSize close : Nat) :
    (localBPBlockWordsTraceResult shape blockSize close).trace.length = 4 := by
  unfold localBPBlockWordsTraceResult bpCodeWordReadTraceResult
  simp [WordRAM.TraceResult.bind, WordRAM.TraceResult.map,
    WordRAM.TraceResult.pure]

/-- Trace-preserving local BP window bits, derived from four payload reads. -/
def localBPWindowBitsTraceResult
    (shape : Cartesian.CartesianShape)
    (blockSize close : Nat) : WordRAM.TraceResult (List Bool) :=
  WordRAM.TraceResult.map SuccinctSpace.flattenPayloadWords
    (localBPBlockWordsTraceResult shape blockSize close)

theorem localBPWindowBitsTraceResult_value
    (shape : Cartesian.CartesianShape)
    (blockSize close : Nat) :
    (localBPWindowBitsTraceResult shape blockSize close).value =
      localBPWindowBits shape blockSize close := by
  unfold localBPWindowBitsTraceResult
  rw [WordRAM.TraceResult.map_value]
  rw [flatten_localBPBlockWordsTraceResult_value]
  exact (localBPWindowBits_eq_flatten_localBPBlockWordsRead
    shape blockSize close).symm

theorem localBPWindowBitsTraceResult_cost
    (shape : Cartesian.CartesianShape)
    (blockSize close : Nat) :
    (localBPWindowBitsTraceResult shape blockSize close).trace.length = 4 := by
  unfold localBPWindowBitsTraceResult
  simp [localBPBlockWordsTraceResult_cost]

/-- Structural trace for the seeded left endpoint-fringe decoder. -/
def localBPLeftFringeCandidateSeededTraceResult
    (shape : Cartesian.CartesianShape)
    (blockSize leftClose seed : Nat) :
    WordRAM.TraceResult (Option (Nat × Nat)) :=
  let base := localBPWindowBase shape blockSize leftClose
  let count :=
    blockStartOf blockSize (blockOfClose blockSize leftClose) +
      blockSize - leftClose
  WordRAM.TraceResult.map
    (fun window =>
      some
        (localBPSeededPrefixRangeMinExcess window seed base
          (leftClose + 1) count,
          localBPSeededPrefixRangeArgMinPrefixPos window seed base
            (leftClose + 1) count))
    (localBPWindowBitsTraceResult shape blockSize leftClose)

theorem localBPLeftFringeCandidateSeededTraceResult_refines
    (shape : Cartesian.CartesianShape)
    (blockSize leftClose seed : Nat) :
    (localBPLeftFringeCandidateSeededTraceResult
      shape blockSize leftClose seed).toCosted =
      localBPLeftFringeCandidateSeededCosted
        shape blockSize leftClose seed := by
  apply Costed.ext
  · unfold localBPLeftFringeCandidateSeededTraceResult
      localBPLeftFringeCandidateSeededCosted
    simp [WordRAM.TraceResult.map_toCosted, Costed.map,
      localBPWindowBitsTraceResult_value]
  · unfold localBPLeftFringeCandidateSeededTraceResult
      localBPLeftFringeCandidateSeededCosted
    simp [WordRAM.TraceResult.map_toCosted, Costed.map,
      localBPWindowBitsTraceResult_cost]

/-- Structural trace for the seeded right endpoint-fringe decoder. -/
def localBPRightFringeCandidateSeededTraceResult
    (shape : Cartesian.CartesianShape)
    (blockSize rightClose seed : Nat) :
    WordRAM.TraceResult (Option (Nat × Nat)) :=
  let base := localBPWindowBase shape blockSize rightClose
  let start := blockStartOf blockSize (blockOfClose blockSize rightClose)
  let count := rightClose - start + 2
  WordRAM.TraceResult.map
    (fun window =>
      some
        (localBPSeededPrefixRangeMinExcess window seed base start count,
          localBPSeededPrefixRangeArgMinPrefixPos window seed base start count))
    (localBPWindowBitsTraceResult shape blockSize rightClose)

theorem localBPRightFringeCandidateSeededTraceResult_refines
    (shape : Cartesian.CartesianShape)
    (blockSize rightClose seed : Nat) :
    (localBPRightFringeCandidateSeededTraceResult
      shape blockSize rightClose seed).toCosted =
      localBPRightFringeCandidateSeededCosted
        shape blockSize rightClose seed := by
  apply Costed.ext
  · unfold localBPRightFringeCandidateSeededTraceResult
      localBPRightFringeCandidateSeededCosted
    simp [WordRAM.TraceResult.map_toCosted, Costed.map,
      localBPWindowBitsTraceResult_value]
  · unfold localBPRightFringeCandidateSeededTraceResult
      localBPRightFringeCandidateSeededCosted
    simp [WordRAM.TraceResult.map_toCosted, Costed.map,
      localBPWindowBitsTraceResult_cost]

/-- Structural trace for the seeded same-block local BP decoder. -/
def localBPSameBlockCloseSeededTraceResult
    (shape : Cartesian.CartesianShape)
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
    (localBPWindowBitsTraceResult shape blockSize leftClose)

theorem localBPSameBlockCloseSeededTraceResult_refines
    (shape : Cartesian.CartesianShape)
    (blockSize leftClose rightClose seed : Nat) :
    (localBPSameBlockCloseSeededTraceResult
      shape blockSize leftClose rightClose seed).toCosted =
      localBPSameBlockCloseSeededCosted
        shape blockSize leftClose rightClose seed := by
  apply Costed.ext
  · unfold localBPSameBlockCloseSeededTraceResult
      localBPSameBlockCloseSeededCosted
    simp [WordRAM.TraceResult.map_toCosted, Costed.map,
      localBPWindowBitsTraceResult_value,
      localBPWindowBits_eq_flatten_localBPBlockWordsRead]
  · unfold localBPSameBlockCloseSeededTraceResult
      localBPSameBlockCloseSeededCosted
    simp [WordRAM.TraceResult.map_toCosted, Costed.map,
      localBPWindowBitsTraceResult_cost]

/--
Large-regime concrete replay of the relative-rmM interior range-minimum query.

The abstract interior-directory record is intentionally too weak to support
this theorem, because it can be inhabited by proof-only oracles.  This function
therefore targets the canonical built directory and mirrors its two-level
payload-table construction directly.
-/
def concreteBPRelativeRmmInteriorRangeMinTraceResultOfSizeGe
    (shape : Cartesian.CartesianShape)
    (_hsize : 2 ^ 128 <= shape.size)
    (startBlock count : Nat) : WordRAM.TraceResult (Option (Nat × Nat)) :=
  let summary := concreteBPRelativeMinMaxArgSummaryTable_canonical shape
  let localTable := concreteBPRelativeRmmInteriorLocalTable shape
  let globalTable := concreteBPRelativeRmmInteriorGlobalTable shape
  bpTwoLevelInteriorCandidateTraceResult localTable globalTable summary
    startBlock count

theorem concreteBPRelativeRmmInteriorRangeMinTraceResultOfSizeGe_refines
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (startBlock count : Nat) :
    (concreteBPRelativeRmmInteriorRangeMinTraceResultOfSizeGe
      shape hsize startBlock count).toCosted =
      (concreteBPRelativeRmmInteriorDirectory shape).rangeMinCosted
        startBlock count := by
  unfold concreteBPRelativeRmmInteriorRangeMinTraceResultOfSizeGe
  unfold concreteBPRelativeRmmInteriorDirectory
  simp [hsize, bpTwoLevelInteriorCandidateTraceResult_refines]

/-- Interpreted false-rank callback for the BP close seed. -/
def interpretedRankCloseCosted
    {shape : Cartesian.CartesianShape} {rankOverhead : Nat}
    (rankData : PayloadLiveStoredWordRankData shape.bpCode rankOverhead)
    (pos : Nat) : Costed Nat :=
  (((rankData.rankProgramClamped false pos).eval
    (rankData.rankWordRAMStore false)).toCosted)

theorem interpretedRankCloseCosted_refines_rankCostedClamped
    {shape : Cartesian.CartesianShape} {rankOverhead : Nat}
    (rankData : PayloadLiveStoredWordRankData shape.bpCode rankOverhead)
    (pos : Nat) :
    interpretedRankCloseCosted rankData pos =
      rankData.rankCostedClamped false pos := by
  exact rankData.rankProgramClamped_refines_rankCostedClamped false pos

theorem interpretedRankCloseCosted_cost_le_three
    {shape : Cartesian.CartesianShape} {rankOverhead : Nat}
    (rankData : PayloadLiveStoredWordRankData shape.bpCode rankOverhead)
    (pos : Nat) :
    (interpretedRankCloseCosted rankData pos).cost <= 3 := by
  rw [interpretedRankCloseCosted_refines_rankCostedClamped
    (rankData := rankData) (pos := pos)]
  exact rankData.rankCostedClamped_cost_le_three false pos

theorem interpretedRankCloseCosted_exact
    {shape : Cartesian.CartesianShape} {rankOverhead : Nat}
    (rankData : PayloadLiveStoredWordRankData shape.bpCode rankOverhead)
    (pos : Nat) :
    (interpretedRankCloseCosted rankData pos).erase =
      Succinct.rankPrefix false shape.bpCode pos := by
  rw [interpretedRankCloseCosted_refines_rankCostedClamped
    (rankData := rankData) (pos := pos)]
  exact rankData.rankCostedClamped_exact false pos

/--
Register-interpreted false-rank callback for the BP close seed.

Unlike `interpretedRankCloseCosted`, the queried position is read from a
natural register before the sample and bit-word addresses are computed.
-/
def registerRankCloseCosted
    {shape : Cartesian.CartesianShape} {rankOverhead : Nat}
    (rankData : PayloadLiveStoredWordRankData shape.bpCode rankOverhead)
    (pos : Nat) : Costed Nat :=
  (((rankData.rankRegProgram false (NatExpr.reg 0)).eval
    (rankData.rankWordRAMStore false)
    (RegFile.withNat1 pos)).toCosted)

theorem registerRankCloseCosted_refines_interpretedRankCloseCosted
    {shape : Cartesian.CartesianShape} {rankOverhead : Nat}
    (rankData : PayloadLiveStoredWordRankData shape.bpCode rankOverhead)
    (pos : Nat) :
    registerRankCloseCosted rankData pos =
      interpretedRankCloseCosted rankData pos := by
  unfold registerRankCloseCosted interpretedRankCloseCosted
  exact
    rankData.rankRegProgram_refines_rankProgramClamped false
      (NatExpr.reg 0) (RegFile.withNat1 pos)

theorem registerRankCloseCosted_cost_le_three
    {shape : Cartesian.CartesianShape} {rankOverhead : Nat}
    (rankData : PayloadLiveStoredWordRankData shape.bpCode rankOverhead)
    (pos : Nat) :
    (registerRankCloseCosted rankData pos).cost <= 3 := by
  rw [registerRankCloseCosted_refines_interpretedRankCloseCosted
    (rankData := rankData) (pos := pos)]
  exact interpretedRankCloseCosted_cost_le_three
    (rankData := rankData) (pos := pos)

theorem registerRankCloseCosted_exact
    {shape : Cartesian.CartesianShape} {rankOverhead : Nat}
    (rankData : PayloadLiveStoredWordRankData shape.bpCode rankOverhead)
    (pos : Nat) :
    (registerRankCloseCosted rankData pos).erase =
      Succinct.rankPrefix false shape.bpCode pos := by
  rw [registerRankCloseCosted_refines_interpretedRankCloseCosted
    (rankData := rankData) (pos := pos)]
  exact interpretedRankCloseCosted_exact
    (rankData := rankData) (pos := pos)

/-- Register-program trace for the false-rank callback used by close seeds. -/
def registerRankCloseTraceResult
    {shape : Cartesian.CartesianShape} {rankOverhead : Nat}
    (rankData : PayloadLiveStoredWordRankData shape.bpCode rankOverhead)
    (pos : Nat) : WordRAM.TraceResult Nat :=
  WordRAM.TraceResult.ofResult
    (((rankData.rankRegProgram false (NatExpr.reg 0)).eval
      (rankData.rankWordRAMStore false)
      (RegFile.withNat1 pos)))

theorem registerRankCloseTraceResult_refines_registerRankCloseCosted
    {shape : Cartesian.CartesianShape} {rankOverhead : Nat}
    (rankData : PayloadLiveStoredWordRankData shape.bpCode rankOverhead)
    (pos : Nat) :
    (registerRankCloseTraceResult rankData pos).toCosted =
      registerRankCloseCosted rankData pos := by
  rfl

/-- Trace-preserving version of `localBPSeedFromRankCloseCosted`. -/
def localBPSeedFromRankCloseTraceResult
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (blockSize close : Nat) : WordRAM.TraceResult Nat :=
  let base := localBPWindowBase shape blockSize close
  WordRAM.TraceResult.map
    (fun rankFalse => localBPSeedFromRankFalse base rankFalse)
    (rankCloseTrace base)

theorem localBPSeedFromRankCloseTraceResult_refines
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (rankCloseCosted : Nat -> Costed Nat)
    (blockSize close : Nat)
    (hrank :
      forall pos, (rankCloseTrace pos).toCosted = rankCloseCosted pos) :
    (localBPSeedFromRankCloseTraceResult
      shape rankCloseTrace blockSize close).toCosted =
      localBPSeedFromRankCloseCosted
        shape rankCloseCosted blockSize close := by
  simp [localBPSeedFromRankCloseTraceResult,
    localBPSeedFromRankCloseCosted, hrank]

/--
Trace-preserving same-block close decoder.

The rank seed and bounded local BP decoder are both replayed as structural
traces over payload reads.
-/
def localBPSameBlockCloseDecodedTraceResultWithRankSeed
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (blockSize leftClose rightClose : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  WordRAM.TraceResult.bind
    (localBPSeedFromRankCloseTraceResult
      shape rankCloseTrace blockSize leftClose)
    fun seed =>
      localBPSameBlockCloseSeededTraceResult
        shape blockSize leftClose rightClose seed

theorem localBPSameBlockCloseDecodedTraceResultWithRankSeed_refines
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (rankCloseCosted : Nat -> Costed Nat)
    (blockSize leftClose rightClose : Nat)
    (hrank :
      forall pos, (rankCloseTrace pos).toCosted = rankCloseCosted pos) :
    (localBPSameBlockCloseDecodedTraceResultWithRankSeed
      shape rankCloseTrace blockSize leftClose rightClose).toCosted =
      localBPSameBlockCloseDecodedCostedWithRankSeed
        shape rankCloseCosted blockSize leftClose rightClose := by
  simp [localBPSameBlockCloseDecodedTraceResultWithRankSeed,
    localBPSameBlockCloseDecodedCostedWithRankSeed,
    localBPSeedFromRankCloseTraceResult_refines,
    localBPSameBlockCloseSeededTraceResult_refines, hrank]

/--
Trace-preserving cross-block close decoder.

The two endpoint seed rank reads and endpoint-fringe decoders are structural
traces.  The interior relative-rmM query remains the existing charged decoder
leaf.
-/
def crossBlockCloseTraceResultWithRankSeed
    {shape : Cartesian.CartesianShape}
    (directory : ConcreteCompactBPCloseLCADirectory shape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (leftClose rightClose : Nat) : WordRAM.TraceResult (Option Nat) :=
  let blockSize := canonicalBPRelativeSummaryBlockSize shape
  let leftBlock := blockOfClose blockSize leftClose
  let rightBlock := blockOfClose blockSize rightClose
  WordRAM.TraceResult.bind
    (localBPSeedFromRankCloseTraceResult
      shape rankCloseTrace blockSize leftClose)
    fun leftSeed =>
      WordRAM.TraceResult.bind
        (localBPLeftFringeCandidateSeededTraceResult
          shape blockSize leftClose leftSeed)
        fun left? =>
          WordRAM.TraceResult.bind
            (if leftBlock + 1 < rightBlock then
              WordRAM.TraceResult.ofCosted
                (directory.interior.rangeMinCosted (leftBlock + 1)
                  (rightBlock - leftBlock - 1))
            else
              WordRAM.TraceResult.pure none)
            fun middle? =>
              WordRAM.TraceResult.bind
                (localBPSeedFromRankCloseTraceResult
                  shape rankCloseTrace blockSize rightClose)
                fun rightSeed =>
                  WordRAM.TraceResult.map
                    (fun right? =>
                      bpCandidateClose?
                        (bpCandidateMerge3? left? middle? right?))
                    (localBPRightFringeCandidateSeededTraceResult
                      shape blockSize rightClose rightSeed)

theorem crossBlockCloseTraceResultWithRankSeed_refines
    {shape : Cartesian.CartesianShape}
    (directory : ConcreteCompactBPCloseLCADirectory shape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (rankCloseCosted : Nat -> Costed Nat)
    (leftClose rightClose : Nat)
    (hrank :
      forall pos, (rankCloseTrace pos).toCosted = rankCloseCosted pos) :
    (directory.crossBlockCloseTraceResultWithRankSeed
      rankCloseTrace leftClose rightClose).toCosted =
      directory.crossBlockCloseCostedWithRankSeed
        rankCloseCosted leftClose rightClose := by
  unfold crossBlockCloseTraceResultWithRankSeed
  unfold crossBlockCloseCostedWithRankSeed
  let blockSize := canonicalBPRelativeSummaryBlockSize shape
  by_cases hmiddle :
      blockOfClose blockSize leftClose + 1 <
        blockOfClose blockSize rightClose
  · simp [localBPSeedFromRankCloseTraceResult_refines, hrank,
      localBPLeftFringeCandidateSeededTraceResult_refines,
      localBPRightFringeCandidateSeededTraceResult_refines,
      blockSize, hmiddle]
  · simp [localBPSeedFromRankCloseTraceResult_refines, hrank,
      localBPLeftFringeCandidateSeededTraceResult_refines,
      localBPRightFringeCandidateSeededTraceResult_refines,
      blockSize, hmiddle]

/--
Concrete large-regime cross-block close decoder with a structural interior
relative-rmM trace.
-/
def crossBlockCloseTraceResultWithRankSeedOfSizeGe
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (hsize : 2 ^ 128 <= shape.size)
    (leftClose rightClose : Nat) : WordRAM.TraceResult (Option Nat) :=
  let blockSize := canonicalBPRelativeSummaryBlockSize shape
  let leftBlock := blockOfClose blockSize leftClose
  let rightBlock := blockOfClose blockSize rightClose
  WordRAM.TraceResult.bind
    (localBPSeedFromRankCloseTraceResult
      shape rankCloseTrace blockSize leftClose)
    fun leftSeed =>
      WordRAM.TraceResult.bind
        (localBPLeftFringeCandidateSeededTraceResult
          shape blockSize leftClose leftSeed)
        fun left? =>
          WordRAM.TraceResult.bind
            (if leftBlock + 1 < rightBlock then
              concreteBPRelativeRmmInteriorRangeMinTraceResultOfSizeGe
                shape hsize (leftBlock + 1)
                (rightBlock - leftBlock - 1)
            else
              WordRAM.TraceResult.pure none)
            fun middle? =>
              WordRAM.TraceResult.bind
                (localBPSeedFromRankCloseTraceResult
                  shape rankCloseTrace blockSize rightClose)
                fun rightSeed =>
                  WordRAM.TraceResult.map
                    (fun right? =>
                      bpCandidateClose?
                        (bpCandidateMerge3? left? middle? right?))
                    (localBPRightFringeCandidateSeededTraceResult
                      shape blockSize rightClose rightSeed)

/- theorem crossBlockCloseTraceResultWithRankSeedOfSizeGe_refines
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (rankCloseCosted : Nat -> Costed Nat)
    (hsize : 2 ^ 128 <= shape.size)
    (leftClose rightClose : Nat)
    (hrank :
      forall pos, (rankCloseTrace pos).toCosted = rankCloseCosted pos) :
    (crossBlockCloseTraceResultWithRankSeedOfSizeGe
      shape rankCloseTrace hsize leftClose rightClose).toCosted =
      ConcreteCompactBPCloseLCADirectory.crossBlockCloseCostedWithRankSeed
        (concreteCompactBPCloseLCADirectory shape)
        rankCloseCosted leftClose rightClose := by
  unfold crossBlockCloseTraceResultWithRankSeedOfSizeGe
  unfold ConcreteCompactBPCloseLCADirectory.crossBlockCloseCostedWithRankSeed
  let blockSize := canonicalBPRelativeSummaryBlockSize shape
  by_cases hmiddle :
      blockOfClose blockSize leftClose + 1 <
        blockOfClose blockSize rightClose
  Â· simp [localBPSeedFromRankCloseTraceResult_refines, hrank,
      localBPLeftFringeCandidateSeededTraceResult_refines,
      localBPRightFringeCandidateSeededTraceResult_refines,
      concreteBPRelativeRmmInteriorRangeMinTraceResultOfSizeGe_refines,
      blockSize, hmiddle]
  Â· simp [localBPSeedFromRankCloseTraceResult_refines, hrank,
      localBPLeftFringeCandidateSeededTraceResult_refines,
      localBPRightFringeCandidateSeededTraceResult_refines,
      blockSize, hmiddle]
-/

theorem crossBlockCloseTraceResultWithRankSeedOfSizeGe_refines
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (rankCloseCosted : Nat -> Costed Nat)
    (hsize : 2 ^ 128 <= shape.size)
    (leftClose rightClose : Nat)
    (hrank :
      forall pos, (rankCloseTrace pos).toCosted = rankCloseCosted pos) :
    (crossBlockCloseTraceResultWithRankSeedOfSizeGe
      shape rankCloseTrace hsize leftClose rightClose).toCosted =
      ConcreteCompactBPCloseLCADirectory.crossBlockCloseCostedWithRankSeed
        (concreteCompactBPCloseLCADirectory shape)
        rankCloseCosted leftClose rightClose := by
  unfold crossBlockCloseTraceResultWithRankSeedOfSizeGe
  unfold ConcreteCompactBPCloseLCADirectory.crossBlockCloseCostedWithRankSeed
  let blockSize := canonicalBPRelativeSummaryBlockSize shape
  by_cases hmiddle :
      blockOfClose blockSize leftClose + 1 <
        blockOfClose blockSize rightClose
  case pos =>
    simp [localBPSeedFromRankCloseTraceResult_refines, hrank,
      localBPLeftFringeCandidateSeededTraceResult_refines,
      localBPRightFringeCandidateSeededTraceResult_refines,
      concreteBPRelativeRmmInteriorRangeMinTraceResultOfSizeGe_refines,
      concreteCompactBPCloseLCADirectory, blockSize, hmiddle]
  case neg =>
    simp [localBPSeedFromRankCloseTraceResult_refines, hrank,
      localBPLeftFringeCandidateSeededTraceResult_refines,
      localBPRightFringeCandidateSeededTraceResult_refines,
      blockSize, hmiddle]

/--
Trace-preserving compact close/LCA query.

The rank-seed reads and bounded local BP endpoint decoders are structural
Word-RAM traces. The zero-block fallback and relative-rmM interior query remain
charged decoder leaves.
-/
def lcaCloseTraceResultWithRankSeed
    {shape : Cartesian.CartesianShape}
    (directory : ConcreteCompactBPCloseLCADirectory shape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (leftClose rightClose : Nat) : WordRAM.TraceResult (Option Nat) :=
  let blockSize := canonicalBPRelativeSummaryBlockSize shape
  if blockSize = 0 then
    WordRAM.TraceResult.ofCosted
      (localBPSameBlockCloseCosted shape leftClose rightClose)
  else if blockOfClose blockSize leftClose =
      blockOfClose blockSize rightClose then
    localBPSameBlockCloseDecodedTraceResultWithRankSeed
      shape rankCloseTrace blockSize leftClose rightClose
  else
    directory.crossBlockCloseTraceResultWithRankSeed
      rankCloseTrace leftClose rightClose

theorem lcaCloseTraceResultWithRankSeed_refines
    {shape : Cartesian.CartesianShape}
    (directory : ConcreteCompactBPCloseLCADirectory shape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (rankCloseCosted : Nat -> Costed Nat)
    (leftClose rightClose : Nat)
    (hrank :
      forall pos, (rankCloseTrace pos).toCosted = rankCloseCosted pos) :
    (directory.lcaCloseTraceResultWithRankSeed
      rankCloseTrace leftClose rightClose).toCosted =
      directory.lcaCloseCostedWithRankSeed
        rankCloseCosted leftClose rightClose := by
  by_cases hzero : canonicalBPRelativeSummaryBlockSize shape = 0
  · simp [lcaCloseTraceResultWithRankSeed, lcaCloseCostedWithRankSeed,
      hzero]
  · by_cases hsame :
      blockOfClose (canonicalBPRelativeSummaryBlockSize shape) leftClose =
        blockOfClose (canonicalBPRelativeSummaryBlockSize shape) rightClose
    · simp [lcaCloseTraceResultWithRankSeed, lcaCloseCostedWithRankSeed,
        hzero, hsame,
        localBPSameBlockCloseDecodedTraceResultWithRankSeed_refines,
        hrank]
    · simp [lcaCloseTraceResultWithRankSeed, lcaCloseCostedWithRankSeed,
        hzero, hsame, crossBlockCloseTraceResultWithRankSeed_refines,
        hrank]

/--
Concrete large-regime compact close/LCA query trace.

The large-regime hypothesis routes through the positive dispatch, so the
zero-block semantic fallback is not part of this replay.  The cross-block case
uses the concrete interior relative-rmM trace.
-/
def lcaCloseTraceResultWithRankSeedOfSizeGe
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (hsize : 2 ^ 128 <= shape.size)
    (leftClose rightClose : Nat) : WordRAM.TraceResult (Option Nat) :=
  let blockSize := canonicalBPRelativeSummaryBlockSize shape
  if blockOfClose blockSize leftClose =
      blockOfClose blockSize rightClose then
    localBPSameBlockCloseDecodedTraceResultWithRankSeed
      shape rankCloseTrace blockSize leftClose rightClose
  else
    crossBlockCloseTraceResultWithRankSeedOfSizeGe
      shape rankCloseTrace hsize leftClose rightClose

/- theorem lcaCloseTraceResultWithRankSeedOfSizeGe_refines
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (rankCloseCosted : Nat -> Costed Nat)
    (hsize : 2 ^ 128 <= shape.size)
    (leftClose rightClose : Nat)
    (hrank :
      forall pos, (rankCloseTrace pos).toCosted = rankCloseCosted pos) :
    (lcaCloseTraceResultWithRankSeedOfSizeGe
      shape rankCloseTrace hsize leftClose rightClose).toCosted =
      ConcreteCompactBPCloseLCADirectory.lcaCloseCostedWithRankSeed
        (concreteCompactBPCloseLCADirectory shape)
        rankCloseCosted leftClose rightClose := by
  have hdispatch :=
    ConcreteCompactBPCloseLCADirectory.lcaCloseCostedWithRankSeed_eq_positive_dispatch_of_size_ge
      (concreteCompactBPCloseLCADirectory shape)
      rankCloseCosted leftClose rightClose hsize
  rw [hdispatch]
  by_cases hsame :
      blockOfClose (canonicalBPRelativeSummaryBlockSize shape) leftClose =
        blockOfClose (canonicalBPRelativeSummaryBlockSize shape) rightClose
  Â· simp [lcaCloseTraceResultWithRankSeedOfSizeGe, hsame,
      localBPSameBlockCloseDecodedTraceResultWithRankSeed_refines,
      hrank]
  Â· simp [lcaCloseTraceResultWithRankSeedOfSizeGe, hsame,
      crossBlockCloseTraceResultWithRankSeedOfSizeGe_refines,
      hrank]
-/

theorem lcaCloseTraceResultWithRankSeedOfSizeGe_refines
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (rankCloseCosted : Nat -> Costed Nat)
    (hsize : 2 ^ 128 <= shape.size)
    (leftClose rightClose : Nat)
    (hrank :
      forall pos, (rankCloseTrace pos).toCosted = rankCloseCosted pos) :
    (lcaCloseTraceResultWithRankSeedOfSizeGe
      shape rankCloseTrace hsize leftClose rightClose).toCosted =
      ConcreteCompactBPCloseLCADirectory.lcaCloseCostedWithRankSeed
        (concreteCompactBPCloseLCADirectory shape)
        rankCloseCosted leftClose rightClose := by
  have hdispatch :=
    ConcreteCompactBPCloseLCADirectory.lcaCloseCostedWithRankSeed_eq_positive_dispatch_of_size_ge
      (concreteCompactBPCloseLCADirectory shape)
      rankCloseCosted leftClose rightClose hsize
  rw [hdispatch]
  by_cases hsame :
      blockOfClose (canonicalBPRelativeSummaryBlockSize shape) leftClose =
        blockOfClose (canonicalBPRelativeSummaryBlockSize shape) rightClose
  case pos =>
    simp [lcaCloseTraceResultWithRankSeedOfSizeGe, hsame,
      localBPSameBlockCloseDecodedTraceResultWithRankSeed_refines,
      hrank]
  case neg =>
    simp [lcaCloseTraceResultWithRankSeedOfSizeGe, hsame,
      crossBlockCloseTraceResultWithRankSeedOfSizeGe_refines,
      concreteCompactBPCloseLCADirectory, hrank]

/-- Compact close/LCA query using the interpreted false-rank seed callback. -/
def lcaCloseCostedWithInterpretedRankSeed
    {shape : Cartesian.CartesianShape}
    (directory : ConcreteCompactBPCloseLCADirectory shape)
    {rankOverhead : Nat}
    (rankData : PayloadLiveStoredWordRankData shape.bpCode rankOverhead)
    (leftClose rightClose : Nat) : Costed (Option Nat) :=
  directory.lcaCloseCostedWithRankSeed
    (fun pos => interpretedRankCloseCosted rankData pos)
    leftClose rightClose

theorem lcaCloseCostedWithInterpretedRankSeed_refines_lcaCloseCostedWithRankSeed
    {shape : Cartesian.CartesianShape}
    (directory : ConcreteCompactBPCloseLCADirectory shape)
    {rankOverhead : Nat}
    (rankData : PayloadLiveStoredWordRankData shape.bpCode rankOverhead)
    (leftClose rightClose : Nat) :
    directory.lcaCloseCostedWithInterpretedRankSeed rankData leftClose
        rightClose =
      directory.lcaCloseCostedWithRankSeed
        (fun pos => rankData.rankCostedClamped false pos)
        leftClose rightClose := by
  have hfun :
      (fun pos => interpretedRankCloseCosted rankData pos) =
        (fun pos => rankData.rankCostedClamped false pos) := by
    funext pos
    exact interpretedRankCloseCosted_refines_rankCostedClamped
      (rankData := rankData) (pos := pos)
  simp [lcaCloseCostedWithInterpretedRankSeed, hfun]

theorem lcaCloseCostedWithInterpretedRankSeed_cost_le
    {shape : Cartesian.CartesianShape}
    (directory : ConcreteCompactBPCloseLCADirectory shape)
    {rankOverhead : Nat}
    (rankData : PayloadLiveStoredWordRankData shape.bpCode rankOverhead)
    (leftClose rightClose : Nat) :
    (directory.lcaCloseCostedWithInterpretedRankSeed rankData leftClose
        rightClose).cost <=
      concreteCompactBPCloseQueryCostWithRankSeed 3 := by
  unfold lcaCloseCostedWithInterpretedRankSeed
  exact
    directory.lcaCloseCostedWithRankSeed_cost_le
      (fun pos => interpretedRankCloseCosted rankData pos)
      leftClose rightClose 3
      (by
        intro pos
        exact interpretedRankCloseCosted_cost_le_three
          (rankData := rankData) (pos := pos))

theorem lcaCloseCostedWithInterpretedRankSeed_exact_of_query
    {shape : Cartesian.CartesianShape}
    (directory : ConcreteCompactBPCloseLCADirectory shape)
    {rankOverhead : Nat}
    (rankData : PayloadLiveStoredWordRankData shape.bpCode rankOverhead)
    {left len leftClose rightClose answerClose : Nat}
    (hlen : 0 < len)
    (hbound : left + len <= shape.size)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder? shape
          (scanWindow shape.representative left len) =
        some answerClose) :
    (directory.lcaCloseCostedWithInterpretedRankSeed rankData leftClose
        rightClose).erase =
      some answerClose := by
  unfold lcaCloseCostedWithInterpretedRankSeed
  exact
    directory.lcaCloseCostedWithRankSeed_exact_of_query
      (fun pos => interpretedRankCloseCosted rankData pos)
      (by
        intro pos
        exact interpretedRankCloseCosted_exact
          (rankData := rankData) (pos := pos))
      hlen hbound hleft hright hanswer

theorem lcaCloseCostedWithInterpretedRankSeed_profile
    {shape : Cartesian.CartesianShape}
    (directory : ConcreteCompactBPCloseLCADirectory shape)
    {rankOverhead : Nat}
    (rankData : PayloadLiveStoredWordRankData shape.bpCode rankOverhead) :
    (forall leftClose rightClose,
      (directory.lcaCloseCostedWithInterpretedRankSeed rankData leftClose
        rightClose).cost <=
          concreteCompactBPCloseQueryCostWithRankSeed 3) /\
      (forall {left len leftClose rightClose answerClose : Nat},
        0 < len ->
          left + len <= shape.size ->
            bpCloseOfInorder? shape left = some leftClose ->
              bpCloseOfInorder? shape (left + len - 1) =
                  some rightClose ->
                bpCloseOfInorder? shape
                    (scanWindow shape.representative left len) =
                  some answerClose ->
                  (directory.lcaCloseCostedWithInterpretedRankSeed rankData
                    leftClose rightClose).erase =
                    some answerClose) := by
  constructor
  next =>
    intro leftClose rightClose
    exact directory.lcaCloseCostedWithInterpretedRankSeed_cost_le
      rankData leftClose rightClose
  next =>
    intro left len leftClose rightClose answerClose hlen hbound hleft hright
      hanswer
    exact directory.lcaCloseCostedWithInterpretedRankSeed_exact_of_query
      rankData hlen hbound hleft hright hanswer

end ConcreteCompactBPCloseLCADirectory

end SuccinctClose
end RMQ
