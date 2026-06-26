import RMQ.Core.SuccinctClose.RelativeRmmMacro.LocalBPDecoder

/-!
# Concrete compact BP close/LCA directory

Split implementation layer for the relative-rmM BP close/LCA macro. Public
declarations stay in the historical RMQ.SuccinctCloseProposal namespace.
-/

namespace RMQ
namespace SuccinctCloseProposal

open SuccinctSpace

structure ConcreteCompactBPCloseLCADirectory
    (shape : Cartesian.CartesianShape) where
  interior :
    PayloadLiveBPRelativeRmmInteriorDirectory shape
      (canonicalBPRelativeSummaryBlockSize shape)
      (canonicalBPRelativeSummaryBlockCount shape)
      (concreteBPRelativeRmmInteriorDirectoryPayloadLength shape)
      concreteBPRelativeRmmInteriorQueryCost
  payload : List Bool
  payload_eq_interior : payload = interior.payload

namespace ConcreteCompactBPCloseLCADirectory

def payloadWordsRead
    {shape : Cartesian.CartesianShape}
    (directory : ConcreteCompactBPCloseLCADirectory shape)
    (leftClose rightClose : Nat) : List (List Bool) :=
  let blockSize := canonicalBPRelativeSummaryBlockSize shape
  let leftBlock := blockOfClose blockSize leftClose
  let rightBlock := blockOfClose blockSize rightClose
  localBPBlockWordsRead shape blockSize leftClose ++
    (if leftBlock = rightBlock then
      []
    else if leftBlock + 1 < rightBlock then
      directory.interior.payloadWordsRead (leftBlock + 1)
        (rightBlock - leftBlock - 1)
    else
      []) ++
      localBPBlockWordsRead shape blockSize rightClose

def crossBlockCloseCosted
    {shape : Cartesian.CartesianShape}
    (directory : ConcreteCompactBPCloseLCADirectory shape)
    (leftClose rightClose : Nat) : Costed (Option Nat) :=
  let blockSize := canonicalBPRelativeSummaryBlockSize shape
  let leftBlock := blockOfClose blockSize leftClose
  let rightBlock := blockOfClose blockSize rightClose
  Costed.bind
    (localBPSeedFromRankFalseCosted shape blockSize leftClose)
    fun leftSeed =>
      Costed.bind
        (localBPLeftFringeCandidateSeededCosted shape blockSize leftClose
          leftSeed)
        fun left? =>
          Costed.bind
            (if leftBlock + 1 < rightBlock then
              directory.interior.rangeMinCosted (leftBlock + 1)
                (rightBlock - leftBlock - 1)
            else
              Costed.pure none)
            fun middle? =>
              Costed.bind
                (localBPSeedFromRankFalseCosted shape blockSize rightClose)
                fun rightSeed =>
                  Costed.map
                    (fun right? =>
                      bpCandidateClose?
                        (bpCandidateMerge3? left? middle? right?))
                    (localBPRightFringeCandidateSeededCosted shape blockSize
                      rightClose rightSeed)

def crossBlockCloseCostedWithRankSeed
    {shape : Cartesian.CartesianShape}
    (directory : ConcreteCompactBPCloseLCADirectory shape)
    (rankCloseCosted : Nat -> Costed Nat)
    (leftClose rightClose : Nat) : Costed (Option Nat) :=
  let blockSize := canonicalBPRelativeSummaryBlockSize shape
  let leftBlock := blockOfClose blockSize leftClose
  let rightBlock := blockOfClose blockSize rightClose
  Costed.bind
    (localBPSeedFromRankCloseCosted shape rankCloseCosted blockSize leftClose)
    fun leftSeed =>
      Costed.bind
        (localBPLeftFringeCandidateSeededCosted shape blockSize leftClose
          leftSeed)
        fun left? =>
          Costed.bind
            (if leftBlock + 1 < rightBlock then
              directory.interior.rangeMinCosted (leftBlock + 1)
                (rightBlock - leftBlock - 1)
            else
              Costed.pure none)
            fun middle? =>
              Costed.bind
                (localBPSeedFromRankCloseCosted shape rankCloseCosted
                  blockSize rightClose)
                fun rightSeed =>
                  Costed.map
                    (fun right? =>
                      bpCandidateClose?
                        (bpCandidateMerge3? left? middle? right?))
                    (localBPRightFringeCandidateSeededCosted shape blockSize
                      rightClose rightSeed)

def lcaCloseCosted
    {shape : Cartesian.CartesianShape}
    (directory : ConcreteCompactBPCloseLCADirectory shape)
    (leftClose rightClose : Nat) : Costed (Option Nat) :=
  let blockSize := canonicalBPRelativeSummaryBlockSize shape
  if blockSize = 0 then
    localBPSameBlockCloseCosted shape leftClose rightClose
  else if blockOfClose blockSize leftClose =
      blockOfClose blockSize rightClose then
    localBPSameBlockCloseDecodedCosted shape blockSize leftClose rightClose
  else
    directory.crossBlockCloseCosted leftClose rightClose

def lcaCloseCostedWithRankSeed
    {shape : Cartesian.CartesianShape}
    (directory : ConcreteCompactBPCloseLCADirectory shape)
    (rankCloseCosted : Nat -> Costed Nat)
    (leftClose rightClose : Nat) : Costed (Option Nat) :=
  let blockSize := canonicalBPRelativeSummaryBlockSize shape
  if blockSize = 0 then
    localBPSameBlockCloseCosted shape leftClose rightClose
  else if blockOfClose blockSize leftClose =
      blockOfClose blockSize rightClose then
    localBPSameBlockCloseDecodedCostedWithRankSeed shape rankCloseCosted
      blockSize leftClose rightClose
  else
    directory.crossBlockCloseCostedWithRankSeed rankCloseCosted leftClose
      rightClose

theorem lcaCloseCostedWithRankSeed_eq_positive_dispatch
    {shape : Cartesian.CartesianShape}
    (directory : ConcreteCompactBPCloseLCADirectory shape)
    (rankCloseCosted : Nat -> Costed Nat)
    (leftClose rightClose : Nat)
    (hblockSize : 0 < canonicalBPRelativeSummaryBlockSize shape) :
    directory.lcaCloseCostedWithRankSeed rankCloseCosted leftClose
        rightClose =
      if blockOfClose (canonicalBPRelativeSummaryBlockSize shape) leftClose =
          blockOfClose (canonicalBPRelativeSummaryBlockSize shape)
            rightClose then
        localBPSameBlockCloseDecodedCostedWithRankSeed shape rankCloseCosted
          (canonicalBPRelativeSummaryBlockSize shape) leftClose rightClose
      else
        directory.crossBlockCloseCostedWithRankSeed rankCloseCosted leftClose
          rightClose := by
  unfold lcaCloseCostedWithRankSeed
  simp [Nat.ne_of_gt hblockSize]

theorem lcaCloseCostedWithRankSeed_eq_positive_dispatch_of_size_ge
    {shape : Cartesian.CartesianShape}
    (directory : ConcreteCompactBPCloseLCADirectory shape)
    (rankCloseCosted : Nat -> Costed Nat)
    (leftClose rightClose : Nat)
    (hsize : 2 ^ 128 <= shape.size) :
    directory.lcaCloseCostedWithRankSeed rankCloseCosted leftClose
        rightClose =
      if blockOfClose (canonicalBPRelativeSummaryBlockSize shape) leftClose =
          blockOfClose (canonicalBPRelativeSummaryBlockSize shape)
            rightClose then
        localBPSameBlockCloseDecodedCostedWithRankSeed shape rankCloseCosted
          (canonicalBPRelativeSummaryBlockSize shape) leftClose rightClose
      else
        directory.crossBlockCloseCostedWithRankSeed rankCloseCosted leftClose
          rightClose :=
  directory.lcaCloseCostedWithRankSeed_eq_positive_dispatch
    rankCloseCosted leftClose rightClose
    (canonicalBPRelativeSummaryBlockSize_pos_of_size_ge hsize)

theorem crossBlockCloseCosted_cost_le
    {shape : Cartesian.CartesianShape}
    (directory : ConcreteCompactBPCloseLCADirectory shape)
    (leftClose rightClose : Nat) :
    (directory.crossBlockCloseCosted leftClose rightClose).cost <=
      concreteCompactBPCloseQueryCost := by
  unfold crossBlockCloseCosted concreteCompactBPCloseQueryCost
  have hleftSeed :=
    localBPSeedFromRankFalseCosted_cost_le shape
      (canonicalBPRelativeSummaryBlockSize shape) leftClose
  have hleft :=
    localBPLeftFringeCandidateSeededCosted_cost_le shape
      (canonicalBPRelativeSummaryBlockSize shape) leftClose
      (localBPSeedFromRankFalseCosted shape
        (canonicalBPRelativeSummaryBlockSize shape) leftClose).value
  have hrightSeed :=
    localBPSeedFromRankFalseCosted_cost_le shape
      (canonicalBPRelativeSummaryBlockSize shape) rightClose
  have hright :=
    localBPRightFringeCandidateSeededCosted_cost_le shape
      (canonicalBPRelativeSummaryBlockSize shape) rightClose
      (localBPSeedFromRankFalseCosted shape
        (canonicalBPRelativeSummaryBlockSize shape) rightClose).value
  have hmiddle :
      (if blockOfClose (canonicalBPRelativeSummaryBlockSize shape)
            leftClose + 1 <
            blockOfClose (canonicalBPRelativeSummaryBlockSize shape)
              rightClose then
          directory.interior.rangeMinCosted
            (blockOfClose (canonicalBPRelativeSummaryBlockSize shape)
                leftClose + 1)
            (blockOfClose (canonicalBPRelativeSummaryBlockSize shape)
                rightClose -
              blockOfClose (canonicalBPRelativeSummaryBlockSize shape)
                leftClose - 1)
        else
          Costed.pure none).cost <=
        concreteBPRelativeRmmInteriorQueryCost := by
    by_cases hgap :
        blockOfClose (canonicalBPRelativeSummaryBlockSize shape)
            leftClose + 1 <
          blockOfClose (canonicalBPRelativeSummaryBlockSize shape)
            rightClose
    · simp [hgap]
      exact directory.interior.rangeMin_cost_le
        (blockOfClose (canonicalBPRelativeSummaryBlockSize shape)
            leftClose + 1)
        (blockOfClose (canonicalBPRelativeSummaryBlockSize shape)
            rightClose -
          blockOfClose (canonicalBPRelativeSummaryBlockSize shape)
            leftClose - 1)
    · simp [hgap, Costed.pure]
  simp [Costed.bind, Costed.map] at hleftSeed hleft hmiddle hrightSeed hright ⊢
  omega

theorem crossBlockCloseCostedWithRankSeed_cost_le
    {shape : Cartesian.CartesianShape}
    (directory : ConcreteCompactBPCloseLCADirectory shape)
    (rankCloseCosted : Nat -> Costed Nat)
    (leftClose rightClose rankCost : Nat)
    (hrankCost : forall pos, (rankCloseCosted pos).cost <= rankCost) :
    (directory.crossBlockCloseCostedWithRankSeed rankCloseCosted leftClose
        rightClose).cost <=
      concreteCompactBPCloseQueryCostWithRankSeed rankCost := by
  unfold crossBlockCloseCostedWithRankSeed
    concreteCompactBPCloseQueryCostWithRankSeed
  have hleftSeed :=
    localBPSeedFromRankCloseCosted_cost_le shape rankCloseCosted
      (canonicalBPRelativeSummaryBlockSize shape) leftClose rankCost
      hrankCost
  have hleft :=
    localBPLeftFringeCandidateSeededCosted_cost_le shape
      (canonicalBPRelativeSummaryBlockSize shape) leftClose
      (localBPSeedFromRankCloseCosted shape rankCloseCosted
        (canonicalBPRelativeSummaryBlockSize shape) leftClose).value
  have hrightSeed :=
    localBPSeedFromRankCloseCosted_cost_le shape rankCloseCosted
      (canonicalBPRelativeSummaryBlockSize shape) rightClose rankCost
      hrankCost
  have hright :=
    localBPRightFringeCandidateSeededCosted_cost_le shape
      (canonicalBPRelativeSummaryBlockSize shape) rightClose
      (localBPSeedFromRankCloseCosted shape rankCloseCosted
        (canonicalBPRelativeSummaryBlockSize shape) rightClose).value
  have hmiddle :
      (if blockOfClose (canonicalBPRelativeSummaryBlockSize shape)
            leftClose + 1 <
            blockOfClose (canonicalBPRelativeSummaryBlockSize shape)
              rightClose then
          directory.interior.rangeMinCosted
            (blockOfClose (canonicalBPRelativeSummaryBlockSize shape)
                leftClose + 1)
            (blockOfClose (canonicalBPRelativeSummaryBlockSize shape)
                rightClose -
              blockOfClose (canonicalBPRelativeSummaryBlockSize shape)
                leftClose - 1)
        else
          Costed.pure none).cost <=
        concreteBPRelativeRmmInteriorQueryCost := by
    by_cases hgap :
        blockOfClose (canonicalBPRelativeSummaryBlockSize shape)
            leftClose + 1 <
          blockOfClose (canonicalBPRelativeSummaryBlockSize shape)
            rightClose
    · simp [hgap]
      exact directory.interior.rangeMin_cost_le
        (blockOfClose (canonicalBPRelativeSummaryBlockSize shape)
            leftClose + 1)
        (blockOfClose (canonicalBPRelativeSummaryBlockSize shape)
            rightClose -
          blockOfClose (canonicalBPRelativeSummaryBlockSize shape)
            leftClose - 1)
    · simp [hgap, Costed.pure]
  simp [Costed.bind, Costed.map] at hleftSeed hleft hmiddle hrightSeed hright ⊢
  omega

theorem lcaCloseCosted_cost_le
    {shape : Cartesian.CartesianShape}
    (directory : ConcreteCompactBPCloseLCADirectory shape)
    (leftClose rightClose : Nat) :
    (directory.lcaCloseCosted leftClose rightClose).cost <=
      concreteCompactBPCloseQueryCost := by
  unfold lcaCloseCosted
  by_cases hzero : canonicalBPRelativeSummaryBlockSize shape = 0
  · simp [hzero]
    have hlocal :=
      localBPSameBlockCloseCosted_cost_le shape leftClose rightClose
    unfold concreteCompactBPCloseQueryCost
    omega
  · simp [hzero]
    by_cases hsame :
        blockOfClose (canonicalBPRelativeSummaryBlockSize shape) leftClose =
          blockOfClose (canonicalBPRelativeSummaryBlockSize shape) rightClose
    · simp [hsame]
      have hlocal :=
        localBPSameBlockCloseDecodedCosted_cost_le shape
          (canonicalBPRelativeSummaryBlockSize shape) leftClose rightClose
      unfold concreteCompactBPCloseQueryCost
      omega
    · simp [hsame]
      exact directory.crossBlockCloseCosted_cost_le leftClose rightClose

theorem lcaCloseCostedWithRankSeed_cost_le
    {shape : Cartesian.CartesianShape}
    (directory : ConcreteCompactBPCloseLCADirectory shape)
    (rankCloseCosted : Nat -> Costed Nat)
    (leftClose rightClose rankCost : Nat)
    (hrankCost : forall pos, (rankCloseCosted pos).cost <= rankCost) :
    (directory.lcaCloseCostedWithRankSeed rankCloseCosted leftClose
        rightClose).cost <=
      concreteCompactBPCloseQueryCostWithRankSeed rankCost := by
  unfold lcaCloseCostedWithRankSeed
  by_cases hzero : canonicalBPRelativeSummaryBlockSize shape = 0
  · simp [hzero]
    have hlocal :=
      localBPSameBlockCloseCosted_cost_le shape leftClose rightClose
    unfold concreteCompactBPCloseQueryCostWithRankSeed
    omega
  · simp [hzero]
    by_cases hsame :
        blockOfClose (canonicalBPRelativeSummaryBlockSize shape) leftClose =
          blockOfClose (canonicalBPRelativeSummaryBlockSize shape) rightClose
    · simp [hsame]
      have hlocal :=
        localBPSameBlockCloseDecodedCostedWithRankSeed_cost_le shape
          rankCloseCosted
          (canonicalBPRelativeSummaryBlockSize shape) leftClose rightClose
          rankCost hrankCost
      unfold concreteCompactBPCloseQueryCostWithRankSeed
      omega
    · simp [hsame]
      exact
        directory.crossBlockCloseCostedWithRankSeed_cost_le rankCloseCosted
          leftClose rightClose rankCost hrankCost

theorem crossBlockCloseCosted_erase_decoded
    {shape : Cartesian.CartesianShape}
    (directory : ConcreteCompactBPCloseLCADirectory shape)
    {leftClose rightClose : Nat}
    (hleftFringe :
      (localBPLeftFringeCandidateSeededCosted shape
          (canonicalBPRelativeSummaryBlockSize shape) leftClose
          (localBPSeedFromRankFalseCosted shape
            (canonicalBPRelativeSummaryBlockSize shape) leftClose).value).value =
        (localBPLeftFringeCandidateCosted shape
          (canonicalBPRelativeSummaryBlockSize shape) leftClose).value)
    (hrightFringe :
      (localBPRightFringeCandidateSeededCosted shape
          (canonicalBPRelativeSummaryBlockSize shape) rightClose
          (localBPSeedFromRankFalseCosted shape
            (canonicalBPRelativeSummaryBlockSize shape) rightClose).value).value =
        (localBPRightFringeCandidateCosted shape
          (canonicalBPRelativeSummaryBlockSize shape) rightClose).value)
    (hrightBlock :
      blockOfClose (canonicalBPRelativeSummaryBlockSize shape) rightClose <=
        canonicalBPRelativeSummaryBlockCount shape) :
    (directory.crossBlockCloseCosted leftClose rightClose).erase =
      bpCandidateClose?
        (bpCandidateMerge3?
          (some
            (bpPrefixRangeMinExcess shape (leftClose + 1)
              (blockStartOf (canonicalBPRelativeSummaryBlockSize shape)
                  (blockOfClose (canonicalBPRelativeSummaryBlockSize shape)
                    leftClose) +
                canonicalBPRelativeSummaryBlockSize shape - leftClose),
              bpPrefixRangeArgMinPrefixPos shape (leftClose + 1)
                (blockStartOf (canonicalBPRelativeSummaryBlockSize shape)
                    (blockOfClose
                      (canonicalBPRelativeSummaryBlockSize shape)
                      leftClose) +
                  canonicalBPRelativeSummaryBlockSize shape - leftClose)))
          (if blockOfClose (canonicalBPRelativeSummaryBlockSize shape)
                leftClose + 1 <
                blockOfClose (canonicalBPRelativeSummaryBlockSize shape)
                  rightClose then
              some
                (bpRangeMinExcess shape
                  (canonicalBPRelativeSummaryBlockSize shape)
                  (blockOfClose
                    (canonicalBPRelativeSummaryBlockSize shape)
                    leftClose + 1)
                  (blockOfClose
                      (canonicalBPRelativeSummaryBlockSize shape)
                      rightClose -
                    blockOfClose
                      (canonicalBPRelativeSummaryBlockSize shape)
                      leftClose - 1),
                  bpRangeArgMinPrefixPos shape
                    (canonicalBPRelativeSummaryBlockSize shape)
                    (blockOfClose
                      (canonicalBPRelativeSummaryBlockSize shape)
                      leftClose + 1)
                    (blockOfClose
                        (canonicalBPRelativeSummaryBlockSize shape)
                        rightClose -
                      blockOfClose
                        (canonicalBPRelativeSummaryBlockSize shape)
                        leftClose - 1))
            else
              none)
          (some
            (bpPrefixRangeMinExcess shape
              (blockStartOf (canonicalBPRelativeSummaryBlockSize shape)
                (blockOfClose (canonicalBPRelativeSummaryBlockSize shape)
                  rightClose))
              (rightClose -
                  blockStartOf (canonicalBPRelativeSummaryBlockSize shape)
                    (blockOfClose
                      (canonicalBPRelativeSummaryBlockSize shape)
                      rightClose) +
                2),
              bpPrefixRangeArgMinPrefixPos shape
                (blockStartOf (canonicalBPRelativeSummaryBlockSize shape)
                  (blockOfClose
                    (canonicalBPRelativeSummaryBlockSize shape)
                    rightClose))
                (rightClose -
                    blockStartOf (canonicalBPRelativeSummaryBlockSize shape)
                      (blockOfClose
                        (canonicalBPRelativeSummaryBlockSize shape)
                        rightClose) +
                  2)))) := by
  let blockSize := canonicalBPRelativeSummaryBlockSize shape
  let leftBlock := blockOfClose blockSize leftClose
  let rightBlock := blockOfClose blockSize rightClose
  unfold crossBlockCloseCosted
  by_cases hgap : leftBlock + 1 < rightBlock
  · have hmiddle :
        (directory.interior.rangeMinCosted (leftBlock + 1)
            (rightBlock - leftBlock - 1)).value =
          some
            (bpRangeMinExcess shape blockSize (leftBlock + 1)
              (rightBlock - leftBlock - 1),
              bpRangeArgMinPrefixPos shape blockSize (leftBlock + 1)
                (rightBlock - leftBlock - 1)) := by
      have hcount : 0 < rightBlock - leftBlock - 1 := by
        omega
      have hbound :
          leftBlock + 1 + (rightBlock - leftBlock - 1) <=
            canonicalBPRelativeSummaryBlockCount shape := by
        have hsum :
            leftBlock + 1 + (rightBlock - leftBlock - 1) =
              rightBlock := by
          omega
        rw [hsum]
        exact hrightBlock
      simpa [Costed.erase, blockSize, leftBlock, rightBlock] using
        directory.interior.rangeMin_exact hcount hbound
    simp [Costed.bind, Costed.map, Costed.erase,
      localBPLeftFringeCandidateCosted,
      localBPRightFringeCandidateCosted, hleftFringe, hrightFringe, hgap, hmiddle,
      blockSize, leftBlock, rightBlock]
  · simp [Costed.bind, Costed.map, Costed.erase, Costed.pure,
      localBPLeftFringeCandidateCosted,
      localBPRightFringeCandidateCosted, hleftFringe, hrightFringe, hgap,
      blockSize, leftBlock, rightBlock]

theorem crossBlockCloseCostedWithRankSeed_erase_decoded
    {shape : Cartesian.CartesianShape}
    (directory : ConcreteCompactBPCloseLCADirectory shape)
    (rankCloseCosted : Nat -> Costed Nat)
    {leftClose rightClose : Nat}
    (hleftFringe :
      (localBPLeftFringeCandidateSeededCosted shape
          (canonicalBPRelativeSummaryBlockSize shape) leftClose
          (localBPSeedFromRankCloseCosted shape rankCloseCosted
            (canonicalBPRelativeSummaryBlockSize shape) leftClose).value).value =
        (localBPLeftFringeCandidateCosted shape
          (canonicalBPRelativeSummaryBlockSize shape) leftClose).value)
    (hrightFringe :
      (localBPRightFringeCandidateSeededCosted shape
          (canonicalBPRelativeSummaryBlockSize shape) rightClose
          (localBPSeedFromRankCloseCosted shape rankCloseCosted
            (canonicalBPRelativeSummaryBlockSize shape) rightClose).value).value =
        (localBPRightFringeCandidateCosted shape
          (canonicalBPRelativeSummaryBlockSize shape) rightClose).value)
    (hrightBlock :
      blockOfClose (canonicalBPRelativeSummaryBlockSize shape) rightClose <=
        canonicalBPRelativeSummaryBlockCount shape) :
    (directory.crossBlockCloseCostedWithRankSeed rankCloseCosted leftClose
        rightClose).erase =
      bpCandidateClose?
        (bpCandidateMerge3?
          (some
            (bpPrefixRangeMinExcess shape (leftClose + 1)
              (blockStartOf (canonicalBPRelativeSummaryBlockSize shape)
                  (blockOfClose (canonicalBPRelativeSummaryBlockSize shape)
                    leftClose) +
                canonicalBPRelativeSummaryBlockSize shape - leftClose),
              bpPrefixRangeArgMinPrefixPos shape (leftClose + 1)
                (blockStartOf (canonicalBPRelativeSummaryBlockSize shape)
                    (blockOfClose
                      (canonicalBPRelativeSummaryBlockSize shape)
                      leftClose) +
                  canonicalBPRelativeSummaryBlockSize shape - leftClose)))
          (if blockOfClose (canonicalBPRelativeSummaryBlockSize shape)
                leftClose + 1 <
                blockOfClose (canonicalBPRelativeSummaryBlockSize shape)
                  rightClose then
              some
                (bpRangeMinExcess shape
                  (canonicalBPRelativeSummaryBlockSize shape)
                  (blockOfClose
                    (canonicalBPRelativeSummaryBlockSize shape)
                    leftClose + 1)
                  (blockOfClose
                      (canonicalBPRelativeSummaryBlockSize shape)
                      rightClose -
                    blockOfClose
                      (canonicalBPRelativeSummaryBlockSize shape)
                      leftClose - 1),
                  bpRangeArgMinPrefixPos shape
                    (canonicalBPRelativeSummaryBlockSize shape)
                    (blockOfClose
                      (canonicalBPRelativeSummaryBlockSize shape)
                      leftClose + 1)
                    (blockOfClose
                        (canonicalBPRelativeSummaryBlockSize shape)
                        rightClose -
                      blockOfClose
                        (canonicalBPRelativeSummaryBlockSize shape)
                        leftClose - 1))
            else
              none)
          (some
            (bpPrefixRangeMinExcess shape
              (blockStartOf (canonicalBPRelativeSummaryBlockSize shape)
                (blockOfClose (canonicalBPRelativeSummaryBlockSize shape)
                  rightClose))
              (rightClose -
                  blockStartOf (canonicalBPRelativeSummaryBlockSize shape)
                    (blockOfClose
                      (canonicalBPRelativeSummaryBlockSize shape)
                      rightClose) +
                2),
              bpPrefixRangeArgMinPrefixPos shape
                (blockStartOf (canonicalBPRelativeSummaryBlockSize shape)
                  (blockOfClose
                    (canonicalBPRelativeSummaryBlockSize shape)
                    rightClose))
                (rightClose -
                    blockStartOf (canonicalBPRelativeSummaryBlockSize shape)
                      (blockOfClose
                        (canonicalBPRelativeSummaryBlockSize shape)
                        rightClose) +
                  2)))) := by
  let blockSize := canonicalBPRelativeSummaryBlockSize shape
  let leftBlock := blockOfClose blockSize leftClose
  let rightBlock := blockOfClose blockSize rightClose
  unfold crossBlockCloseCostedWithRankSeed
  by_cases hgap : leftBlock + 1 < rightBlock
  · have hmiddle :
        (directory.interior.rangeMinCosted (leftBlock + 1)
            (rightBlock - leftBlock - 1)).value =
          some
            (bpRangeMinExcess shape blockSize (leftBlock + 1)
              (rightBlock - leftBlock - 1),
              bpRangeArgMinPrefixPos shape blockSize (leftBlock + 1)
                (rightBlock - leftBlock - 1)) := by
      have hcount : 0 < rightBlock - leftBlock - 1 := by
        omega
      have hbound :
          leftBlock + 1 + (rightBlock - leftBlock - 1) <=
            canonicalBPRelativeSummaryBlockCount shape := by
        have hsum :
            leftBlock + 1 + (rightBlock - leftBlock - 1) =
              rightBlock := by
          omega
        rw [hsum]
        exact hrightBlock
      simpa [Costed.erase, blockSize, leftBlock, rightBlock] using
        directory.interior.rangeMin_exact hcount hbound
    simp [Costed.bind, Costed.map, Costed.erase,
      localBPLeftFringeCandidateCosted,
      localBPRightFringeCandidateCosted, hleftFringe, hrightFringe, hgap, hmiddle,
      blockSize, leftBlock, rightBlock]
  · simp [Costed.bind, Costed.map, Costed.erase, Costed.pure,
      localBPLeftFringeCandidateCosted,
      localBPRightFringeCandidateCosted, hleftFringe, hrightFringe, hgap,
      blockSize, leftBlock, rightBlock]

theorem crossBlockCloseCosted_exact_of_query
    {shape : Cartesian.CartesianShape}
    (directory : ConcreteCompactBPCloseLCADirectory shape)
    {left len leftClose rightClose answerClose : Nat}
    (hlen : 0 < len)
    (hbound : left + len <= shape.size)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder? shape
          (scanWindow shape.representative left len) =
        some answerClose)
    (hcross :
      blockOfClose (canonicalBPRelativeSummaryBlockSize shape) leftClose <
        blockOfClose (canonicalBPRelativeSummaryBlockSize shape)
          rightClose) :
    (directory.crossBlockCloseCosted leftClose rightClose).erase =
      some answerClose := by
  by_cases hactive : canonicalBPRelativeMinMaxArgSummaryTableActive shape
  ·
    let blockSize := canonicalBPRelativeSummaryBlockSize shape
    have hleftCloseBound := bpCloseOfInorder?_bounds shape hleft
    have hrightCloseBound := bpCloseOfInorder?_bounds shape hright
    have hrightBlockLe :=
      canonicalBPRelativeSummary_blockOfClose_le_blockCount_of_active
        (shape := shape) hactive hrightCloseBound
    have hsizePos : 0 < shape.size := by omega
    have hblockSizeLeTwo :
        blockSize <=
          2 * SuccinctRankProposal.machineWordBits shape.bpCode.length := by
      simpa [blockSize] using
        canonicalBPRelativeSummaryBlockSize_le_two_machine_of_size_pos
          (shape := shape) hsizePos
    have hblockSizeLeThree :
        blockSize <=
          3 * SuccinctRankProposal.machineWordBits shape.bpCode.length := by
      omega
    have hblockCountLen :
        canonicalBPRelativeSummaryBlockCount shape *
            canonicalBPRelativeSummaryBlockSize shape <=
          shape.bpCode.length := by
      simpa [canonicalBPRelativeSummaryBlockCount,
        canonicalBPRelativeSummaryBlockSize, hactive] using hactive.1
    have hleftBaseBlock :
        localBPWindowBase shape blockSize leftClose <=
          blockStartOf blockSize (blockOfClose blockSize leftClose) :=
      localBPWindowBase_le_blockStart shape blockSize leftClose
    have hleftBaseClose :
        localBPWindowBase shape blockSize leftClose <= leftClose := by
      exact Nat.le_trans hleftBaseBlock blockStartOf_blockOfClose_le
    have hleftBaseLen :
        localBPWindowBase shape blockSize leftClose <= shape.bpCode.length := by
      omega
    have hleftStartBase :
        localBPWindowBase shape blockSize leftClose <= leftClose + 1 := by
      omega
    have hleftInside :
        leftClose <
          blockStartOf blockSize (blockOfClose blockSize leftClose) +
            blockSize := by
      exact close_lt_blockStartOf_blockOfClose_add
        (blockSize := blockSize) (close := leftClose)
        (by simpa [blockSize, canonicalBPRelativeSummaryBlockSize, hactive]
          using canonicalBPRelativeSummaryBlockSizeRaw_pos shape)
    have hleftEndWidth :
        blockStartOf blockSize (blockOfClose blockSize leftClose) +
            blockSize <=
          localBPWindowBase shape blockSize leftClose +
            4 * SuccinctRankProposal.machineWordBits shape.bpCode.length :=
      localBPWindow_block_end_le_four_words shape blockSize leftClose
        hblockSizeLeThree
    have hleftSuccLeRight :
        blockOfClose blockSize leftClose + 1 <=
          blockOfClose blockSize rightClose := by
      exact Nat.succ_le_of_lt (by simpa [blockSize] using hcross)
    have hleftSuccLeCount :
        blockOfClose blockSize leftClose + 1 <=
          canonicalBPRelativeSummaryBlockCount shape := by
      exact Nat.le_trans hleftSuccLeRight (by simpa [blockSize] using hrightBlockLe)
    have hleftEndLen :
        blockStartOf blockSize (blockOfClose blockSize leftClose) +
            blockSize <= shape.bpCode.length := by
      have hmul :=
        Nat.mul_le_mul_right blockSize hleftSuccLeCount
      have hmulLen :
          (blockOfClose blockSize leftClose + 1) * blockSize <=
            shape.bpCode.length := by
        exact Nat.le_trans hmul (by simpa [blockSize] using hblockCountLen)
      have hmulLen' :
          blockSize + blockOfClose blockSize leftClose * blockSize <=
            shape.bpCode.length := by
        calc
          blockSize + blockOfClose blockSize leftClose * blockSize =
              (blockOfClose blockSize leftClose + 1) * blockSize := by
                rw [Nat.add_mul, Nat.one_mul]
                omega
          _ <= shape.bpCode.length := hmulLen
      simpa [blockStartOf, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        hmulLen'
    have hleftEndCovered :
        blockStartOf blockSize (blockOfClose blockSize leftClose) +
            blockSize <=
          localBPWindowBase shape blockSize leftClose +
            (localBPWindowBits shape blockSize leftClose).length := by
      exact localBPWindowBits_covers_of_le_width
        (shape := shape) (blockSize := blockSize) (close := leftClose)
        (pos :=
          blockStartOf blockSize (blockOfClose blockSize leftClose) +
            blockSize)
        (by omega) hleftEndLen hleftEndWidth
    have hleftSeed :
        (localBPSeedFromRankFalseCosted shape blockSize leftClose).value =
          localBPSeedExcess shape blockSize leftClose := by
      simpa [Costed.erase] using
        localBPSeedFromRankFalseCosted_eq_localBPSeedExcess
          shape blockSize leftClose hleftBaseLen
    have hleftFringe :
        (localBPLeftFringeCandidateSeededCosted shape blockSize leftClose
            (localBPSeedFromRankFalseCosted shape blockSize leftClose).value).value =
          (localBPLeftFringeCandidateCosted shape blockSize leftClose).value := by
      rw [hleftSeed]
      simpa [Costed.erase] using
        localBPLeftFringeCandidateSeededCosted_eq_semantic
          (shape := shape) (blockSize := blockSize)
          (leftClose := leftClose)
          hleftBaseLen hleftStartBase hleftEndCovered hleftInside
    have hrightBaseBlock :
        localBPWindowBase shape blockSize rightClose <=
          blockStartOf blockSize (blockOfClose blockSize rightClose) :=
      localBPWindowBase_le_blockStart shape blockSize rightClose
    have hrightInside :
        blockStartOf blockSize (blockOfClose blockSize rightClose) <=
          rightClose :=
      blockStartOf_blockOfClose_le
    have hrightBaseLen :
        localBPWindowBase shape blockSize rightClose <= shape.bpCode.length := by
      omega
    have hrightEndLen : rightClose + 1 <= shape.bpCode.length := by
      omega
    have hrightBlockEndWidth :
        blockStartOf blockSize (blockOfClose blockSize rightClose) +
            blockSize <=
          localBPWindowBase shape blockSize rightClose +
            4 * SuccinctRankProposal.machineWordBits shape.bpCode.length :=
      localBPWindow_block_end_le_four_words shape blockSize rightClose
        hblockSizeLeThree
    have hrightEndWidth :
        rightClose + 1 <=
          localBPWindowBase shape blockSize rightClose +
            4 * SuccinctRankProposal.machineWordBits shape.bpCode.length := by
      have hrightInsideStrict :
          rightClose <
            blockStartOf blockSize (blockOfClose blockSize rightClose) +
              blockSize := by
        exact close_lt_blockStartOf_blockOfClose_add
          (blockSize := blockSize) (close := rightClose)
          (by simpa [blockSize, canonicalBPRelativeSummaryBlockSize, hactive]
            using canonicalBPRelativeSummaryBlockSizeRaw_pos shape)
      omega
    have hrightEndCovered :
        rightClose + 1 <=
          localBPWindowBase shape blockSize rightClose +
            (localBPWindowBits shape blockSize rightClose).length := by
      exact localBPWindowBits_covers_of_le_width
        (shape := shape) (blockSize := blockSize) (close := rightClose)
        (pos := rightClose + 1)
        (by omega) hrightEndLen hrightEndWidth
    have hrightSeed :
        (localBPSeedFromRankFalseCosted shape blockSize rightClose).value =
          localBPSeedExcess shape blockSize rightClose := by
      simpa [Costed.erase] using
        localBPSeedFromRankFalseCosted_eq_localBPSeedExcess
          shape blockSize rightClose hrightBaseLen
    have hrightFringe :
        (localBPRightFringeCandidateSeededCosted shape blockSize rightClose
            (localBPSeedFromRankFalseCosted shape blockSize rightClose).value).value =
          (localBPRightFringeCandidateCosted shape blockSize rightClose).value := by
      rw [hrightSeed]
      simpa [Costed.erase] using
        localBPRightFringeCandidateSeededCosted_eq_semantic
          (shape := shape) (blockSize := blockSize)
          (rightClose := rightClose)
          hrightBaseLen hrightBaseBlock hrightInside hrightEndCovered
    have hdecoded :=
      directory.crossBlockCloseCosted_erase_decoded
        (by simpa [blockSize] using hleftFringe)
        (by simpa [blockSize] using hrightFringe)
        hrightBlockLe
    rw [hdecoded]
    have hsemantic :=
      answerClose_prefix_leftmost_min_excess_of_query
        (shape := shape) (start := left) (len := len)
        (leftClose := leftClose) (rightClose := rightClose)
        (answerClose := answerClose)
        hlen hbound hleft hright hanswer
    have hblockSize :
        0 < canonicalBPRelativeSummaryBlockSize shape := by
      simpa [canonicalBPRelativeSummaryBlockSize, hactive] using
        canonicalBPRelativeSummaryBlockSizeRaw_pos shape
    have hmerge :=
      bpRelativeRmmCandidateMerge_exact_of_query_semantics_no_block_bounds
        (shape := shape)
        (blockSize := canonicalBPRelativeSummaryBlockSize shape)
        (left := left) (len := len) (leftClose := leftClose)
        (rightClose := rightClose) (answerClose := answerClose)
        hlen hleft hright hanswer hblockSize hcross
        hsemantic.1 hsemantic.2
    simp [hmerge, bpCandidateClose?]
  · have hblockZero :
        canonicalBPRelativeSummaryBlockSize shape = 0 := by
      simp [canonicalBPRelativeSummaryBlockSize, hactive]
    have hfalse : False := by
      simp [hblockZero, blockOfClose] at hcross
    exact False.elim hfalse

theorem crossBlockCloseCostedWithRankSeed_exact_of_query
    {shape : Cartesian.CartesianShape}
    (directory : ConcreteCompactBPCloseLCADirectory shape)
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
        some answerClose)
    (hcross :
      blockOfClose (canonicalBPRelativeSummaryBlockSize shape) leftClose <
        blockOfClose (canonicalBPRelativeSummaryBlockSize shape)
          rightClose) :
    (directory.crossBlockCloseCostedWithRankSeed rankCloseCosted leftClose
        rightClose).erase =
      some answerClose := by
  by_cases hactive : canonicalBPRelativeMinMaxArgSummaryTableActive shape
  ·
    let blockSize := canonicalBPRelativeSummaryBlockSize shape
    have hleftCloseBound := bpCloseOfInorder?_bounds shape hleft
    have hrightCloseBound := bpCloseOfInorder?_bounds shape hright
    have hrightBlockLe :=
      canonicalBPRelativeSummary_blockOfClose_le_blockCount_of_active
        (shape := shape) hactive hrightCloseBound
    have hsizePos : 0 < shape.size := by omega
    have hblockSizeLeTwo :
        blockSize <=
          2 * SuccinctRankProposal.machineWordBits shape.bpCode.length := by
      simpa [blockSize] using
        canonicalBPRelativeSummaryBlockSize_le_two_machine_of_size_pos
          (shape := shape) hsizePos
    have hblockSizeLeThree :
        blockSize <=
          3 * SuccinctRankProposal.machineWordBits shape.bpCode.length := by
      omega
    have hblockCountLen :
        canonicalBPRelativeSummaryBlockCount shape *
            canonicalBPRelativeSummaryBlockSize shape <=
          shape.bpCode.length := by
      simpa [canonicalBPRelativeSummaryBlockCount,
        canonicalBPRelativeSummaryBlockSize, hactive] using hactive.1
    have hleftBaseBlock :
        localBPWindowBase shape blockSize leftClose <=
          blockStartOf blockSize (blockOfClose blockSize leftClose) :=
      localBPWindowBase_le_blockStart shape blockSize leftClose
    have hleftBaseClose :
        localBPWindowBase shape blockSize leftClose <= leftClose := by
      exact Nat.le_trans hleftBaseBlock blockStartOf_blockOfClose_le
    have hleftBaseLen :
        localBPWindowBase shape blockSize leftClose <= shape.bpCode.length := by
      omega
    have hleftStartBase :
        localBPWindowBase shape blockSize leftClose <= leftClose + 1 := by
      omega
    have hleftInside :
        leftClose <
          blockStartOf blockSize (blockOfClose blockSize leftClose) +
            blockSize := by
      exact close_lt_blockStartOf_blockOfClose_add
        (blockSize := blockSize) (close := leftClose)
        (by simpa [blockSize, canonicalBPRelativeSummaryBlockSize, hactive]
          using canonicalBPRelativeSummaryBlockSizeRaw_pos shape)
    have hleftEndWidth :
        blockStartOf blockSize (blockOfClose blockSize leftClose) +
            blockSize <=
          localBPWindowBase shape blockSize leftClose +
            4 * SuccinctRankProposal.machineWordBits shape.bpCode.length :=
      localBPWindow_block_end_le_four_words shape blockSize leftClose
        hblockSizeLeThree
    have hleftSuccLeRight :
        blockOfClose blockSize leftClose + 1 <=
          blockOfClose blockSize rightClose := by
      exact Nat.succ_le_of_lt (by simpa [blockSize] using hcross)
    have hleftSuccLeCount :
        blockOfClose blockSize leftClose + 1 <=
          canonicalBPRelativeSummaryBlockCount shape := by
      exact Nat.le_trans hleftSuccLeRight (by simpa [blockSize] using hrightBlockLe)
    have hleftEndLen :
        blockStartOf blockSize (blockOfClose blockSize leftClose) +
            blockSize <= shape.bpCode.length := by
      have hmul :=
        Nat.mul_le_mul_right blockSize hleftSuccLeCount
      have hmulLen :
          (blockOfClose blockSize leftClose + 1) * blockSize <=
            shape.bpCode.length := by
        exact Nat.le_trans hmul (by simpa [blockSize] using hblockCountLen)
      have hmulLen' :
          blockSize + blockOfClose blockSize leftClose * blockSize <=
            shape.bpCode.length := by
        calc
          blockSize + blockOfClose blockSize leftClose * blockSize =
              (blockOfClose blockSize leftClose + 1) * blockSize := by
                rw [Nat.add_mul, Nat.one_mul]
                omega
          _ <= shape.bpCode.length := hmulLen
      simpa [blockStartOf, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        hmulLen'
    have hleftEndCovered :
        blockStartOf blockSize (blockOfClose blockSize leftClose) +
            blockSize <=
          localBPWindowBase shape blockSize leftClose +
            (localBPWindowBits shape blockSize leftClose).length := by
      exact localBPWindowBits_covers_of_le_width
        (shape := shape) (blockSize := blockSize) (close := leftClose)
        (pos :=
          blockStartOf blockSize (blockOfClose blockSize leftClose) +
            blockSize)
        (by omega) hleftEndLen hleftEndWidth
    have hleftSeed :
        (localBPSeedFromRankCloseCosted shape rankCloseCosted blockSize
            leftClose).value =
          localBPSeedExcess shape blockSize leftClose := by
      simpa [Costed.erase] using
        localBPSeedFromRankCloseCosted_eq_localBPSeedExcess
          shape rankCloseCosted blockSize leftClose hrankExact hleftBaseLen
    have hleftFringe :
        (localBPLeftFringeCandidateSeededCosted shape blockSize leftClose
            (localBPSeedFromRankCloseCosted shape rankCloseCosted blockSize
              leftClose).value).value =
          (localBPLeftFringeCandidateCosted shape blockSize leftClose).value := by
      rw [hleftSeed]
      simpa [Costed.erase] using
        localBPLeftFringeCandidateSeededCosted_eq_semantic
          (shape := shape) (blockSize := blockSize)
          (leftClose := leftClose)
          hleftBaseLen hleftStartBase hleftEndCovered hleftInside
    have hrightBaseBlock :
        localBPWindowBase shape blockSize rightClose <=
          blockStartOf blockSize (blockOfClose blockSize rightClose) :=
      localBPWindowBase_le_blockStart shape blockSize rightClose
    have hrightInside :
        blockStartOf blockSize (blockOfClose blockSize rightClose) <=
          rightClose :=
      blockStartOf_blockOfClose_le
    have hrightBaseLen :
        localBPWindowBase shape blockSize rightClose <= shape.bpCode.length := by
      omega
    have hrightEndLen : rightClose + 1 <= shape.bpCode.length := by
      omega
    have hrightBlockEndWidth :
        blockStartOf blockSize (blockOfClose blockSize rightClose) +
            blockSize <=
          localBPWindowBase shape blockSize rightClose +
            4 * SuccinctRankProposal.machineWordBits shape.bpCode.length :=
      localBPWindow_block_end_le_four_words shape blockSize rightClose
        hblockSizeLeThree
    have hrightEndWidth :
        rightClose + 1 <=
          localBPWindowBase shape blockSize rightClose +
            4 * SuccinctRankProposal.machineWordBits shape.bpCode.length := by
      have hrightInsideStrict :
          rightClose <
            blockStartOf blockSize (blockOfClose blockSize rightClose) +
              blockSize := by
        exact close_lt_blockStartOf_blockOfClose_add
          (blockSize := blockSize) (close := rightClose)
          (by simpa [blockSize, canonicalBPRelativeSummaryBlockSize, hactive]
            using canonicalBPRelativeSummaryBlockSizeRaw_pos shape)
      omega
    have hrightEndCovered :
        rightClose + 1 <=
          localBPWindowBase shape blockSize rightClose +
            (localBPWindowBits shape blockSize rightClose).length := by
      exact localBPWindowBits_covers_of_le_width
        (shape := shape) (blockSize := blockSize) (close := rightClose)
        (pos := rightClose + 1)
        (by omega) hrightEndLen hrightEndWidth
    have hrightSeed :
        (localBPSeedFromRankCloseCosted shape rankCloseCosted blockSize
            rightClose).value =
          localBPSeedExcess shape blockSize rightClose := by
      simpa [Costed.erase] using
        localBPSeedFromRankCloseCosted_eq_localBPSeedExcess
          shape rankCloseCosted blockSize rightClose hrankExact hrightBaseLen
    have hrightFringe :
        (localBPRightFringeCandidateSeededCosted shape blockSize rightClose
            (localBPSeedFromRankCloseCosted shape rankCloseCosted blockSize
              rightClose).value).value =
          (localBPRightFringeCandidateCosted shape blockSize rightClose).value := by
      rw [hrightSeed]
      simpa [Costed.erase] using
        localBPRightFringeCandidateSeededCosted_eq_semantic
          (shape := shape) (blockSize := blockSize)
          (rightClose := rightClose)
          hrightBaseLen hrightBaseBlock hrightInside hrightEndCovered
    have hdecoded :=
      directory.crossBlockCloseCostedWithRankSeed_erase_decoded
        rankCloseCosted
        (by simpa [blockSize] using hleftFringe)
        (by simpa [blockSize] using hrightFringe)
        hrightBlockLe
    rw [hdecoded]
    have hsemantic :=
      answerClose_prefix_leftmost_min_excess_of_query
        (shape := shape) (start := left) (len := len)
        (leftClose := leftClose) (rightClose := rightClose)
        (answerClose := answerClose)
        hlen hbound hleft hright hanswer
    have hblockSize :
        0 < canonicalBPRelativeSummaryBlockSize shape := by
      simpa [canonicalBPRelativeSummaryBlockSize, hactive] using
        canonicalBPRelativeSummaryBlockSizeRaw_pos shape
    have hmerge :=
      bpRelativeRmmCandidateMerge_exact_of_query_semantics_no_block_bounds
        (shape := shape)
        (blockSize := canonicalBPRelativeSummaryBlockSize shape)
        (left := left) (len := len) (leftClose := leftClose)
        (rightClose := rightClose) (answerClose := answerClose)
        hlen hleft hright hanswer hblockSize hcross
        hsemantic.1 hsemantic.2
    simp [hmerge, bpCandidateClose?]
  · have hblockZero :
        canonicalBPRelativeSummaryBlockSize shape = 0 := by
      simp [canonicalBPRelativeSummaryBlockSize, hactive]
    have hfalse : False := by
      simp [hblockZero, blockOfClose] at hcross
    exact False.elim hfalse

theorem lcaCloseCosted_exact_of_query
    {shape : Cartesian.CartesianShape}
    (directory : ConcreteCompactBPCloseLCADirectory shape)
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
    (directory.lcaCloseCosted leftClose rightClose).erase =
      some answerClose := by
  unfold lcaCloseCosted
  by_cases hzero : canonicalBPRelativeSummaryBlockSize shape = 0
  · simp [hzero]
    exact
      localBPSameBlockCloseCosted_exact hlen hbound hleft hright hanswer
  · simp [hzero]
    by_cases hsame :
        blockOfClose (canonicalBPRelativeSummaryBlockSize shape) leftClose =
          blockOfClose (canonicalBPRelativeSummaryBlockSize shape)
            rightClose
    · simp [hsame]
      by_cases hactive :
          canonicalBPRelativeMinMaxArgSummaryTableActive shape
      · have hsizePos : 0 < shape.size := by omega
        have hblockSizePos :
            0 < canonicalBPRelativeSummaryBlockSize shape := by
          simpa [canonicalBPRelativeSummaryBlockSize, hactive] using
            canonicalBPRelativeSummaryBlockSizeRaw_pos shape
        have hblockSizeLeTwo :
            canonicalBPRelativeSummaryBlockSize shape <=
              2 * SuccinctRankProposal.machineWordBits shape.bpCode.length := by
          exact
            canonicalBPRelativeSummaryBlockSize_le_two_machine_of_size_pos
              (shape := shape) hsizePos
        have hblockSizeLeThree :
            canonicalBPRelativeSummaryBlockSize shape <=
              3 * SuccinctRankProposal.machineWordBits shape.bpCode.length := by
          omega
        exact
          localBPSameBlockCloseDecodedCosted_exact_of_query_same_block
            (shape := shape)
            (blockSize := canonicalBPRelativeSummaryBlockSize shape)
            (left := left) (len := len)
            (leftClose := leftClose) (rightClose := rightClose)
            (answerClose := answerClose)
            hblockSizePos hblockSizeLeThree hsame
            hlen hbound hleft hright hanswer
      · have hblockZero :
            canonicalBPRelativeSummaryBlockSize shape = 0 := by
          simp [canonicalBPRelativeSummaryBlockSize, hactive]
        exact False.elim (hzero hblockZero)
    · simp [hsame]
      have hbetween :=
        answerClose_between_endpoint_closes
          (shape := shape) (left := left) (len := len)
          (leftClose := leftClose) (rightClose := rightClose)
          (answerClose := answerClose)
          hlen hleft hright hanswer
      have hblockLe :
          blockOfClose (canonicalBPRelativeSummaryBlockSize shape) leftClose <=
            blockOfClose (canonicalBPRelativeSummaryBlockSize shape)
              rightClose := by
        unfold blockOfClose
        exact Nat.div_le_div_right (Nat.le_trans hbetween.1 hbetween.2)
      have hcross :
          blockOfClose (canonicalBPRelativeSummaryBlockSize shape) leftClose <
            blockOfClose (canonicalBPRelativeSummaryBlockSize shape)
              rightClose := by
        omega
      exact
        directory.crossBlockCloseCosted_exact_of_query hlen hbound
          hleft hright hanswer hcross

theorem lcaCloseCostedWithRankSeed_exact_of_query
    {shape : Cartesian.CartesianShape}
    (directory : ConcreteCompactBPCloseLCADirectory shape)
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
    (directory.lcaCloseCostedWithRankSeed rankCloseCosted leftClose
        rightClose).erase =
      some answerClose := by
  unfold lcaCloseCostedWithRankSeed
  by_cases hzero : canonicalBPRelativeSummaryBlockSize shape = 0
  · simp [hzero]
    exact
      localBPSameBlockCloseCosted_exact hlen hbound hleft hright hanswer
  · simp [hzero]
    by_cases hsame :
        blockOfClose (canonicalBPRelativeSummaryBlockSize shape) leftClose =
          blockOfClose (canonicalBPRelativeSummaryBlockSize shape)
            rightClose
    · simp [hsame]
      by_cases hactive :
          canonicalBPRelativeMinMaxArgSummaryTableActive shape
      · have hsizePos : 0 < shape.size := by omega
        have hblockSizePos :
            0 < canonicalBPRelativeSummaryBlockSize shape := by
          simpa [canonicalBPRelativeSummaryBlockSize, hactive] using
            canonicalBPRelativeSummaryBlockSizeRaw_pos shape
        have hblockSizeLeTwo :
            canonicalBPRelativeSummaryBlockSize shape <=
              2 * SuccinctRankProposal.machineWordBits shape.bpCode.length := by
          exact
            canonicalBPRelativeSummaryBlockSize_le_two_machine_of_size_pos
              (shape := shape) hsizePos
        have hblockSizeLeThree :
            canonicalBPRelativeSummaryBlockSize shape <=
              3 * SuccinctRankProposal.machineWordBits shape.bpCode.length := by
          omega
        exact
          localBPSameBlockCloseDecodedCostedWithRankSeed_exact_of_query_same_block
            (shape := shape) (rankCloseCosted := rankCloseCosted)
            (blockSize := canonicalBPRelativeSummaryBlockSize shape)
            (left := left) (len := len)
            (leftClose := leftClose) (rightClose := rightClose)
            (answerClose := answerClose)
            hrankExact hblockSizePos hblockSizeLeThree hsame
            hlen hbound hleft hright hanswer
      · have hblockZero :
            canonicalBPRelativeSummaryBlockSize shape = 0 := by
          simp [canonicalBPRelativeSummaryBlockSize, hactive]
        exact False.elim (hzero hblockZero)
    · simp [hsame]
      have hbetween :=
        answerClose_between_endpoint_closes
          (shape := shape) (left := left) (len := len)
          (leftClose := leftClose) (rightClose := rightClose)
          (answerClose := answerClose)
          hlen hleft hright hanswer
      have hblockLe :
          blockOfClose (canonicalBPRelativeSummaryBlockSize shape) leftClose <=
            blockOfClose (canonicalBPRelativeSummaryBlockSize shape)
              rightClose := by
        unfold blockOfClose
        exact Nat.div_le_div_right (Nat.le_trans hbetween.1 hbetween.2)
      have hcross :
          blockOfClose (canonicalBPRelativeSummaryBlockSize shape) leftClose <
            blockOfClose (canonicalBPRelativeSummaryBlockSize shape)
              rightClose := by
        omega
      exact
        directory.crossBlockCloseCostedWithRankSeed_exact_of_query
          rankCloseCosted hrankExact hlen hbound
          hleft hright hanswer hcross

theorem lcaCloseCostedWithRankSeed_exact_of_query_of_size_ge
    {shape : Cartesian.CartesianShape}
    (directory : ConcreteCompactBPCloseLCADirectory shape)
    (rankCloseCosted : Nat -> Costed Nat)
    {left len leftClose rightClose answerClose : Nat}
    (hsize : 2 ^ 128 <= shape.size)
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
    (directory.lcaCloseCostedWithRankSeed rankCloseCosted leftClose
        rightClose).erase =
      some answerClose := by
  have hdispatch :=
    directory.lcaCloseCostedWithRankSeed_eq_positive_dispatch_of_size_ge
      rankCloseCosted leftClose rightClose hsize
  rw [hdispatch]
  exact
    (by
      have hexact :=
        directory.lcaCloseCostedWithRankSeed_exact_of_query
          rankCloseCosted hrankExact hlen hbound hleft hright hanswer
      rw [hdispatch] at hexact
      exact hexact)

theorem read_words_length_le_machine
    {shape : Cartesian.CartesianShape}
    (directory : ConcreteCompactBPCloseLCADirectory shape)
    {leftClose rightClose : Nat} {word : List Bool}
    (hmem : word ∈ directory.payloadWordsRead leftClose rightClose) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  unfold payloadWordsRead at hmem
  simp only [List.mem_append] at hmem
  rcases hmem with hhead | hrightMem
  · rcases hhead with hleftMem | hmiddleMem
    · exact
        localBPBlockWordsRead_length_le_machine shape
          (canonicalBPRelativeSummaryBlockSize shape) leftClose hleftMem
    · by_cases hsame :
        blockOfClose (canonicalBPRelativeSummaryBlockSize shape) leftClose =
          blockOfClose (canonicalBPRelativeSummaryBlockSize shape)
            rightClose
      · simp [hsame] at hmiddleMem
      · simp only [hsame, if_false] at hmiddleMem
        by_cases hgap :
            blockOfClose (canonicalBPRelativeSummaryBlockSize shape)
                leftClose + 1 <
              blockOfClose (canonicalBPRelativeSummaryBlockSize shape)
                rightClose
        · simp [hgap] at hmiddleMem
          exact directory.interior.read_words_length_le_machine hmiddleMem
        · simp [hgap] at hmiddleMem
  · exact
      localBPBlockWordsRead_length_le_machine shape
        (canonicalBPRelativeSummaryBlockSize shape) rightClose hrightMem

end ConcreteCompactBPCloseLCADirectory

def concreteCompactBPCloseLCADirectory
    (shape : Cartesian.CartesianShape) :
    ConcreteCompactBPCloseLCADirectory shape where
  interior := concreteBPRelativeRmmInteriorDirectory shape
  payload := (concreteBPRelativeRmmInteriorDirectory shape).payload
  payload_eq_interior := rfl

theorem concreteCompactBPCloseLCADirectory_profile_of_size_ge
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size) :
    let directory := concreteCompactBPCloseLCADirectory shape
    directory.payload.length <= compactBPCloseOverhead shape.size /\
      SuccinctSpace.LittleOLinear compactBPCloseOverhead /\
      (forall leftClose rightClose,
        (directory.lcaCloseCosted leftClose rightClose).cost <=
          concreteCompactBPCloseQueryCost) /\
      (forall {left len leftClose rightClose answerClose : Nat},
        0 < len ->
          left + len <= shape.size ->
            bpCloseOfInorder? shape left = some leftClose ->
              bpCloseOfInorder? shape (left + len - 1) =
                  some rightClose ->
                bpCloseOfInorder? shape
                    (scanWindow shape.representative left len) =
                  some answerClose ->
                  (directory.lcaCloseCosted leftClose rightClose).erase =
                    some answerClose) /\
      forall {leftClose rightClose : Nat} {word : List Bool},
        word ∈ directory.payloadWordsRead leftClose rightClose ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  let directory := concreteCompactBPCloseLCADirectory shape
  have hinterior :=
    concreteBPRelativeRmmInteriorDirectory_profile shape hsize
  rcases hinterior with
    ⟨_hlittleInterior, hpayloadInterior, _hcostInterior,
      _hexactInterior, _hreadInterior⟩
  have hnotSmall : ¬ shape.size < 2 ^ 128 := by omega
  exact
    ⟨by
      simpa [directory, concreteCompactBPCloseLCADirectory,
        compactBPCloseOverhead, hnotSmall] using hpayloadInterior,
    compactBPCloseOverhead_littleO,
    by
      intro leftClose rightClose
      exact directory.lcaCloseCosted_cost_le leftClose rightClose,
    by
      intro left len leftClose rightClose answerClose hlen hbound
        hleft hright hanswer
      exact
        directory.lcaCloseCosted_exact_of_query hlen hbound
          hleft hright hanswer,
    by
      intro leftClose rightClose word hmem
      exact directory.read_words_length_le_machine hmem⟩

theorem concreteCompactBPCloseLCADirectory_profile
    (shape : Cartesian.CartesianShape) :
    let directory := concreteCompactBPCloseLCADirectory shape
    directory.payload.length <= compactBPCloseOverhead shape.size /\
      SuccinctSpace.LittleOLinear compactBPCloseOverhead /\
      (forall leftClose rightClose,
        (directory.lcaCloseCosted leftClose rightClose).cost <=
          concreteCompactBPCloseQueryCost) /\
      (forall {left len leftClose rightClose answerClose : Nat},
        0 < len ->
          left + len <= shape.size ->
            bpCloseOfInorder? shape left = some leftClose ->
              bpCloseOfInorder? shape (left + len - 1) =
                  some rightClose ->
                bpCloseOfInorder? shape
                    (scanWindow shape.representative left len) =
                  some answerClose ->
                  (directory.lcaCloseCosted leftClose rightClose).erase =
                    some answerClose) /\
      forall {leftClose rightClose : Nat} {word : List Bool},
        word ∈ directory.payloadWordsRead leftClose rightClose ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  let directory := concreteCompactBPCloseLCADirectory shape
  have hpayload :
      directory.payload.length <= compactBPCloseOverhead shape.size := by
    by_cases hsize : 2 ^ 128 <= shape.size
    · exact
        (concreteCompactBPCloseLCADirectory_profile_of_size_ge
          shape hsize).1
    · have hsmall : shape.size < 2 ^ 128 := Nat.lt_of_not_ge hsize
      have hpayloadEq :
          directory.payload.length =
            concreteBPRelativeRmmInteriorDirectoryPayloadLength shape := by
        simp [directory, concreteCompactBPCloseLCADirectory,
          (concreteBPRelativeRmmInteriorDirectory shape).payload_length_eq]
      have hshape :
          shape ∈ Cartesian.shapesOfSize shape.size :=
        Cartesian.shapeOfSize_mem_shapesOfSize
          (cartesianShape_shapeOfSize_self shape)
      have hpayloadMem :
          concreteBPRelativeRmmInteriorDirectoryPayloadLength shape ∈
            (Cartesian.shapesOfSize shape.size).map
              (fun shape =>
                concreteBPRelativeRmmInteriorDirectoryPayloadLength shape) :=
        List.mem_map.mpr ⟨shape, hshape, rfl⟩
      have hmax := le_natListMax_of_mem hpayloadMem
      simpa [compactBPCloseOverhead, hsmall, hpayloadEq] using hmax
  exact
    ⟨hpayload,
    compactBPCloseOverhead_littleO,
    by
      intro leftClose rightClose
      exact directory.lcaCloseCosted_cost_le leftClose rightClose,
    by
      intro left len leftClose rightClose answerClose hlen hbound
        hleft hright hanswer
      exact
        directory.lcaCloseCosted_exact_of_query hlen hbound
          hleft hright hanswer,
    by
      intro leftClose rightClose word hmem
      exact directory.read_words_length_le_machine hmem⟩

def payloadLiveRelativeRmmBPCloseMacroOfInterior
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead middleQueryCost : Nat}
    (leftFringe :
      PayloadLiveBPPrefixRangeArgMinWitnessTable shape fieldWidth
        leftOverhead (endpointLeftFringeRanges blockSize blockCount))
    (interior :
      PayloadLiveBPRelativeRmmInteriorDirectory shape blockSize blockCount
        interiorOverhead middleQueryCost)
    (rightFringe :
      PayloadLiveBPPrefixRangeArgMinWitnessTable shape fieldWidth
        rightOverhead (endpointRightFringeRanges blockSize blockCount))
    (hblockSize : 0 < blockSize)
    (hmachine :
      fieldWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length) :
    PayloadLiveRelativeRmmBPCloseMacro shape blockSize blockCount
      (leftOverhead + interiorOverhead + rightOverhead) middleQueryCost where
  payload := leftFringe.payload ++ interior.payload ++ rightFringe.payload
  payload_length_eq := by
    simp [leftFringe.payload_length, interior.payload_length_eq,
      rightFringe.payload_length]
    omega
  payloadWordsRead := fun leftClose rightClose =>
    let leftSlot := endpointFringeSlot blockSize leftClose
    let rightSlot := endpointFringeSlot blockSize rightClose
    let startBlock := blockOfClose blockSize leftClose + 1
    let count :=
      blockOfClose blockSize rightClose -
        blockOfClose blockSize leftClose - 1
    payloadWordReadOfGet? leftFringe.minTable.store.words leftSlot ++
      payloadWordReadOfGet? leftFringe.argTable.store.words leftSlot ++
        (if blockOfClose blockSize leftClose + 1 <
            blockOfClose blockSize rightClose then
          interior.payloadWordsRead startBlock count
        else
          []) ++
          payloadWordReadOfGet? rightFringe.minTable.store.words
            rightSlot ++
            payloadWordReadOfGet? rightFringe.argTable.store.words
              rightSlot
  leftFringeCosted := fun leftClose =>
    leftFringe.rangeWitnessCosted (endpointFringeSlot blockSize leftClose)
  rightFringeCosted := fun rightClose =>
    rightFringe.rangeWitnessCosted (endpointFringeSlot blockSize rightClose)
  interiorRmmCosted := fun leftClose rightClose =>
    interior.rangeMinCosted (blockOfClose blockSize leftClose + 1)
      (blockOfClose blockSize rightClose -
        blockOfClose blockSize leftClose - 1)
  leftFringe_cost_le_two := by
    intro leftClose
    exact leftFringe.rangeWitnessCosted_cost_le_two
      (endpointFringeSlot blockSize leftClose)
  rightFringe_cost_le_two := by
    intro rightClose
    exact rightFringe.rangeWitnessCosted_cost_le_two
      (endpointFringeSlot blockSize rightClose)
  interiorRmm_cost_le := by
    intro leftClose rightClose
    exact interior.rangeMin_cost_le
      (blockOfClose blockSize leftClose + 1)
      (blockOfClose blockSize rightClose -
        blockOfClose blockSize leftClose - 1)
  leftFringe_exact := by
    intro leftClose hleftBlock
    have hmin :
        (bpPrefixRangeMinExcessEntries shape
          (endpointLeftFringeRanges blockSize blockCount))[
            endpointFringeSlot blockSize leftClose]? =
          some
            (bpPrefixRangeMinExcess shape (leftClose + 1)
              (blockStartOf blockSize
                  (blockOfClose blockSize leftClose) +
                blockSize - leftClose)) :=
      endpointLeftFringeMinExcessEntries_get?_of_close_bounds
        hblockSize
        hleftBlock
    have harg :
        (bpPrefixRangeArgMinPrefixPosEntries shape
          (endpointLeftFringeRanges blockSize blockCount))[
            endpointFringeSlot blockSize leftClose]? =
          some
            (bpPrefixRangeArgMinPrefixPos shape (leftClose + 1)
              (blockStartOf blockSize
                  (blockOfClose blockSize leftClose) +
                blockSize - leftClose)) :=
      endpointLeftFringeArgMinEntries_get?_of_close_bounds
        hblockSize
        hleftBlock
    simpa [Costed.erase, hmin, harg] using
      leftFringe.rangeWitnessCosted_erase
        (endpointFringeSlot blockSize leftClose)
  rightFringe_exact := by
    intro rightClose hrightBlock
    have hmin :
        (bpPrefixRangeMinExcessEntries shape
          (endpointRightFringeRanges blockSize blockCount))[
            endpointFringeSlot blockSize rightClose]? =
          some
            (bpPrefixRangeMinExcess shape
              (blockStartOf blockSize (blockOfClose blockSize rightClose))
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2)) :=
      endpointRightFringeMinExcessEntries_get?_of_close_bounds
        hblockSize hrightBlock
    have harg :
        (bpPrefixRangeArgMinPrefixPosEntries shape
          (endpointRightFringeRanges blockSize blockCount))[
            endpointFringeSlot blockSize rightClose]? =
          some
            (bpPrefixRangeArgMinPrefixPos shape
              (blockStartOf blockSize (blockOfClose blockSize rightClose))
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2)) :=
      endpointRightFringeArgMinEntries_get?_of_close_bounds
        hblockSize hrightBlock
    simpa [Costed.erase, hmin, harg] using
      rightFringe.rangeWitnessCosted_erase
        (endpointFringeSlot blockSize rightClose)
  interiorRmm_exact := by
    intro leftClose rightClose hleftBlock hrightBlock hgap
    have hcount :
        0 <
          blockOfClose blockSize rightClose -
            blockOfClose blockSize leftClose - 1 := by
      omega
    have hbound :
        blockOfClose blockSize leftClose + 1 +
            (blockOfClose blockSize rightClose -
              blockOfClose blockSize leftClose - 1) <=
          blockCount := by
      omega
    exact interior.rangeMin_exact hcount hbound
  read_words_length_le_machine := by
    intro leftClose rightClose word hmem
    have hleft := leftFringe.read_words_length_le_machine hmachine
    have hright := rightFringe.read_words_length_le_machine hmachine
    have hmid :
        forall {startBlock count : Nat} {word : List Bool},
          word ∈ interior.payloadWordsRead startBlock count ->
            word.length <=
              SuccinctRankProposal.machineWordBits shape.bpCode.length :=
      interior.read_words_length_le_machine
    dsimp only at hmem
    simp only [List.mem_append] at hmem
    rcases hmem with hmem | hrightArg
    · rcases hmem with hmem | hrightMin
      · rcases hmem with hmem | hmiddle
        · rcases hmem with hleftMin | hleftArg
          · exact payloadWordReadOfGet?_length_le hleft.1 hleftMin
          · exact payloadWordReadOfGet?_length_le hleft.2 hleftArg
        · by_cases hgap :
            blockOfClose blockSize leftClose + 1 <
              blockOfClose blockSize rightClose
          · simp [hgap] at hmiddle
            exact hmid hmiddle
          · simp [hgap] at hmiddle
      · exact payloadWordReadOfGet?_length_le hright.1 hrightMin
    · exact payloadWordReadOfGet?_length_le hright.2 hrightArg

theorem payloadLiveRelativeRmmBPCloseMacroOfInterior_profile
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead middleQueryCost : Nat}
    (leftFringe :
      PayloadLiveBPPrefixRangeArgMinWitnessTable shape fieldWidth
        leftOverhead (endpointLeftFringeRanges blockSize blockCount))
    (interior :
      PayloadLiveBPRelativeRmmInteriorDirectory shape blockSize blockCount
        interiorOverhead middleQueryCost)
    (rightFringe :
      PayloadLiveBPPrefixRangeArgMinWitnessTable shape fieldWidth
        rightOverhead (endpointRightFringeRanges blockSize blockCount))
    (hblockSize : 0 < blockSize)
    (hmachine :
      fieldWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length) :
    let component :=
      payloadLiveRelativeRmmBPCloseMacroOfInterior
        leftFringe interior rightFringe hblockSize hmachine
    component.payload.length =
        leftOverhead + interiorOverhead + rightOverhead /\
      (forall leftClose rightClose,
        (component.lcaCloseCosted leftClose rightClose).cost <=
          4 + middleQueryCost) /\
      (forall {left len leftClose rightClose answerClose : Nat},
        0 < len ->
          left + len <= shape.size ->
            bpCloseOfInorder? shape left = some leftClose ->
              bpCloseOfInorder? shape (left + len - 1) =
                  some rightClose ->
                bpCloseOfInorder? shape
                    (scanWindow shape.representative left len) =
                  some answerClose ->
                  blockOfClose blockSize leftClose < blockCount ->
                    blockOfClose blockSize rightClose < blockCount ->
                      blockOfClose blockSize leftClose <
                        blockOfClose blockSize rightClose ->
                        (component.lcaCloseCosted
                          leftClose rightClose).erase =
                          some answerClose) /\
        forall {leftClose rightClose : Nat} {word : List Bool},
          word ∈ component.payloadWordsRead leftClose rightClose ->
            word.length <=
              SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  let component :=
    payloadLiveRelativeRmmBPCloseMacroOfInterior
      leftFringe interior rightFringe hblockSize hmachine
  have hprofile := component.profile
  constructor
  · exact hprofile.1
  constructor
  · exact hprofile.2
  constructor
  · intro left len leftClose rightClose answerClose hlen hbound hleft
      hright hanswer hleftBlock hrightBlock hcross
    exact
      component.lcaCloseCosted_exact_of_query_cross_block
        hlen hbound hleft hright hanswer hblockSize hleftBlock
        hrightBlock hcross
  · intro leftClose rightClose word hmem
    exact component.read_words_length_le_machine hmem

def concretePayloadLiveRelativeRmmBPCloseMacroPayloadLength
    (shape : Cartesian.CartesianShape) : Nat :=
  2 * ((endpointLeftFringeRanges
          (canonicalBPRelativeSummaryBlockSize shape)
          (canonicalBPRelativeSummaryBlockCount shape)).length *
        SuccinctRankProposal.machineWordBits shape.bpCode.length) +
    concreteBPRelativeRmmInteriorDirectoryPayloadLength shape +
      2 * ((endpointRightFringeRanges
          (canonicalBPRelativeSummaryBlockSize shape)
          (canonicalBPRelativeSummaryBlockCount shape)).length *
        SuccinctRankProposal.machineWordBits shape.bpCode.length)

def concretePayloadLiveRelativeRmmBPCloseMacroOverhead
    (shape : Cartesian.CartesianShape) : Nat :=
  2 * ((endpointLeftFringeRanges
          (canonicalBPRelativeSummaryBlockSize shape)
          (canonicalBPRelativeSummaryBlockCount shape)).length *
        SuccinctRankProposal.machineWordBits shape.bpCode.length) +
    concreteBPRelativeRmmInteriorOverhead shape.size +
      2 * ((endpointRightFringeRanges
          (canonicalBPRelativeSummaryBlockSize shape)
          (canonicalBPRelativeSummaryBlockCount shape)).length *
        SuccinctRankProposal.machineWordBits shape.bpCode.length)

def concretePayloadLiveRelativeRmmBPCloseMacro
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size) :
    PayloadLiveRelativeRmmBPCloseMacro shape
      (canonicalBPRelativeSummaryBlockSize shape)
      (canonicalBPRelativeSummaryBlockCount shape)
      (concretePayloadLiveRelativeRmmBPCloseMacroPayloadLength shape)
      concreteBPRelativeRmmInteriorQueryCost := by
  let fieldWidth := SuccinctRankProposal.machineWordBits shape.bpCode.length
  let leftFringe :=
    concreteBPPrefixRangeArgMinWitnessTable shape fieldWidth
      (endpointLeftFringeRanges
        (canonicalBPRelativeSummaryBlockSize shape)
        (canonicalBPRelativeSummaryBlockCount shape))
      (by
        simpa [fieldWidth, canonicalBPRelativeSummarySuperWidth] using
          canonicalBPRelativeSummary_superWidth_bound shape)
  let rightFringe :=
    concreteBPPrefixRangeArgMinWitnessTable shape fieldWidth
      (endpointRightFringeRanges
        (canonicalBPRelativeSummaryBlockSize shape)
        (canonicalBPRelativeSummaryBlockCount shape))
      (by
        simpa [fieldWidth, canonicalBPRelativeSummarySuperWidth] using
          canonicalBPRelativeSummary_superWidth_bound shape)
  let interior := concreteBPRelativeRmmInteriorDirectory shape
  have hparams :=
    concreteBPRelativeRmmInteriorDirectory_parameter_profile_of_size_ge
      shape hsize
  rcases hparams with
    ⟨hblockSizeEq, _hblocksPerSuperEq, _hblockCountEq,
      _hsuperCountEq, _hrelativeWidthEq, _hlittleO, _hactive,
      hrawBlockSizePos, _hrawBlocksPerSuperPos, _hrawBlockCountPos,
      _hcover, _hcountLe, _hrelativeMachine, _hsummaryPayload,
      _hsummaryExact, _hbaselineRead, _hminRead, _hmaxRead,
      _hargRead⟩
  have hblockSize :
      0 < canonicalBPRelativeSummaryBlockSize shape := by
    rw [hblockSizeEq]
    exact hrawBlockSizePos
  exact
    payloadLiveRelativeRmmBPCloseMacroOfInterior
      leftFringe interior rightFringe hblockSize (Nat.le_refl fieldWidth)

theorem concretePayloadLiveRelativeRmmBPCloseMacro_profile
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size) :
    let component := concretePayloadLiveRelativeRmmBPCloseMacro shape hsize
    component.payload.length <=
        concretePayloadLiveRelativeRmmBPCloseMacroOverhead shape /\
      (forall leftClose rightClose,
        (component.lcaCloseCosted leftClose rightClose).cost <=
          4 + concreteBPRelativeRmmInteriorQueryCost) /\
      (forall {left len leftClose rightClose answerClose : Nat},
        0 < len ->
          left + len <= shape.size ->
            bpCloseOfInorder? shape left = some leftClose ->
              bpCloseOfInorder? shape (left + len - 1) =
                  some rightClose ->
                bpCloseOfInorder? shape
                    (scanWindow shape.representative left len) =
                  some answerClose ->
                  blockOfClose (canonicalBPRelativeSummaryBlockSize shape)
                      leftClose <
                    canonicalBPRelativeSummaryBlockCount shape ->
                    blockOfClose (canonicalBPRelativeSummaryBlockSize shape)
                        rightClose <
                      canonicalBPRelativeSummaryBlockCount shape ->
                      blockOfClose (canonicalBPRelativeSummaryBlockSize shape)
                          leftClose <
                        blockOfClose
                          (canonicalBPRelativeSummaryBlockSize shape)
                          rightClose ->
                        (component.lcaCloseCosted
                          leftClose rightClose).erase =
                          some answerClose) /\
        forall {leftClose rightClose : Nat} {word : List Bool},
          word ∈ component.payloadWordsRead leftClose rightClose ->
            word.length <=
              SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  let fieldWidth := SuccinctRankProposal.machineWordBits shape.bpCode.length
  let leftFringe :=
    concreteBPPrefixRangeArgMinWitnessTable shape fieldWidth
      (endpointLeftFringeRanges
        (canonicalBPRelativeSummaryBlockSize shape)
        (canonicalBPRelativeSummaryBlockCount shape))
      (by
        simpa [fieldWidth, canonicalBPRelativeSummarySuperWidth] using
          canonicalBPRelativeSummary_superWidth_bound shape)
  let rightFringe :=
    concreteBPPrefixRangeArgMinWitnessTable shape fieldWidth
      (endpointRightFringeRanges
        (canonicalBPRelativeSummaryBlockSize shape)
        (canonicalBPRelativeSummaryBlockCount shape))
      (by
        simpa [fieldWidth, canonicalBPRelativeSummarySuperWidth] using
          canonicalBPRelativeSummary_superWidth_bound shape)
  let interior := concreteBPRelativeRmmInteriorDirectory shape
  have hparams :=
    concreteBPRelativeRmmInteriorDirectory_parameter_profile_of_size_ge
      shape hsize
  rcases hparams with
    ⟨hblockSizeEq, _hblocksPerSuperEq, _hblockCountEq,
      _hsuperCountEq, _hrelativeWidthEq, _hlittleO, _hactive,
      hrawBlockSizePos, _hrawBlocksPerSuperPos, _hrawBlockCountPos,
      _hcover, _hcountLe, _hrelativeMachine, _hsummaryPayload,
      _hsummaryExact, _hbaselineRead, _hminRead, _hmaxRead,
      _hargRead⟩
  have hblockSize :
      0 < canonicalBPRelativeSummaryBlockSize shape := by
    rw [hblockSizeEq]
    exact hrawBlockSizePos
  have hcomponentProfile :=
    payloadLiveRelativeRmmBPCloseMacroOfInterior_profile
      leftFringe interior rightFringe hblockSize
      (Nat.le_refl fieldWidth)
  have hinteriorProfile :=
    concreteBPRelativeRmmInteriorDirectory_profile shape hsize
  let component := concretePayloadLiveRelativeRmmBPCloseMacro shape hsize
  rcases hcomponentProfile with
    ⟨_hpayload, _hcost, _hexact, _hread⟩
  rcases hinteriorProfile with
    ⟨_hinteriorLittleO, hinteriorPayload, _hinteriorCost,
      _hinteriorExact, _hinteriorRead⟩
  have hinteriorPayloadLength :
      concreteBPRelativeRmmInteriorDirectoryPayloadLength shape <=
        concreteBPRelativeRmmInteriorOverhead shape.size := by
    have hp := hinteriorPayload
    rw [(concreteBPRelativeRmmInteriorDirectory shape).payload_length_eq] at hp
    exact hp
  constructor
  · rw [(concretePayloadLiveRelativeRmmBPCloseMacro
        shape hsize).payload_length]
    unfold concretePayloadLiveRelativeRmmBPCloseMacroOverhead
      concretePayloadLiveRelativeRmmBPCloseMacroPayloadLength
    omega
  constructor
  · intro leftClose rightClose
    exact
      (concretePayloadLiveRelativeRmmBPCloseMacro
        shape hsize).lcaCloseCosted_cost_le leftClose rightClose
  constructor
  · intro left len leftClose rightClose answerClose hlen hbound hleft
      hright hanswer hleftBlock hrightBlock hcross
    exact
      (concretePayloadLiveRelativeRmmBPCloseMacro
        shape hsize).lcaCloseCosted_exact_of_query_cross_block
          hlen hbound hleft hright hanswer hblockSize hleftBlock
          hrightBlock hcross
  · intro leftClose rightClose word hmem
    exact
      (concretePayloadLiveRelativeRmmBPCloseMacro
        shape hsize).read_words_length_le_machine hmem

end SuccinctCloseProposal
end RMQ
