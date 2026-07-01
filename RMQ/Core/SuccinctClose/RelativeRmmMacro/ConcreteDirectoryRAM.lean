import RMQ.Core.SuccinctClose.RelativeRmmMacro.ConcreteDirectory
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

The rank seed is replayed structurally; the bounded local BP decoder remains the
existing charged decoder leaf.
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
      WordRAM.TraceResult.ofCosted
        (localBPSameBlockCloseSeededCosted shape blockSize leftClose
          rightClose seed)

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
    localBPSeedFromRankCloseTraceResult_refines, hrank]

/--
Trace-preserving cross-block close decoder.

The two endpoint seed rank reads are structural traces; the endpoint-fringe
and interior relative-rmM query leaves remain the existing charged decoders.
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
        (WordRAM.TraceResult.ofCosted
          (localBPLeftFringeCandidateSeededCosted shape blockSize leftClose
            leftSeed))
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
                    (WordRAM.TraceResult.ofCosted
                      (localBPRightFringeCandidateSeededCosted shape
                        blockSize rightClose rightSeed))

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
      blockSize, hmiddle]
  · simp [localBPSeedFromRankCloseTraceResult_refines, hrank,
      blockSize, hmiddle]

/--
Trace-preserving compact close/LCA query.

The rank-seed reads are structural Word-RAM traces. The zero-block fallback,
bounded same-block local decoder, endpoint-fringe decoders, and relative-rmM
interior query are still charged decoder leaves.
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
