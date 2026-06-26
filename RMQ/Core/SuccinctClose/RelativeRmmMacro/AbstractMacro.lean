import RMQ.Core.SuccinctClose.EndpointFringe

/-!
# Abstract relative-rmM close macro contract

Split implementation layer for the relative-rmM BP close/LCA macro. Public
declarations stay in the historical RMQ.SuccinctCloseProposal namespace.
-/

namespace RMQ
namespace SuccinctCloseProposal

open SuccinctSpace


open SuccinctSpace

/-!
## Relative rmM-style close macro interface

The guarded endpoint-fringe directory above is exact, but its concrete macro
payload still contains a dense `interiorBlockPairRanges blockCount` table.  The
next surface below isolates the query-side contract needed from a compact
Navarro-Sadakane/rmM-style macro: endpoint repairs and the middle full-block
range are charged candidate reads, while the middle candidate is supplied by a
relative summary navigator rather than an all-pairs block table.
-/

/--
Payload-live relative-rmM macro for cross-block BP close/LCA queries.

The payload layout is intentionally abstract here because the concrete
relative/log-log summary builder is a separate component.  The query contract is
not abstract: `lcaCloseCosted` is built from three charged candidate reads, and
the semantic exactness theorem below consumes their decoded range-witness facts
plus the global `bpRelativeRmmCandidateMerge_exact` merge theorem.
-/
structure PayloadLiveRelativeRmmBPCloseMacro
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount overhead middleQueryCost : Nat) where
  payload : List Bool
  payload_length_eq : payload.length = overhead
  payloadWordsRead : Nat -> Nat -> List (List Bool)
  leftFringeCosted : Nat -> Costed (Option (Nat × Nat))
  rightFringeCosted : Nat -> Costed (Option (Nat × Nat))
  interiorRmmCosted : Nat -> Nat -> Costed (Option (Nat × Nat))
  leftFringe_cost_le_two :
    forall leftClose,
      (leftFringeCosted leftClose).cost <= 2
  rightFringe_cost_le_two :
    forall rightClose,
      (rightFringeCosted rightClose).cost <= 2
  interiorRmm_cost_le :
    forall leftClose rightClose,
      (interiorRmmCosted leftClose rightClose).cost <= middleQueryCost
  leftFringe_exact :
    forall {leftClose : Nat},
      blockOfClose blockSize leftClose < blockCount ->
        (leftFringeCosted leftClose).erase =
          some
            (bpPrefixRangeMinExcess shape (leftClose + 1)
              (blockStartOf blockSize
                  (blockOfClose blockSize leftClose) +
                blockSize - leftClose),
              bpPrefixRangeArgMinPrefixPos shape (leftClose + 1)
                (blockStartOf blockSize
                    (blockOfClose blockSize leftClose) +
                  blockSize - leftClose))
  rightFringe_exact :
    forall {rightClose : Nat},
      blockOfClose blockSize rightClose < blockCount ->
        (rightFringeCosted rightClose).erase =
          some
            (bpPrefixRangeMinExcess shape
              (blockStartOf blockSize
                (blockOfClose blockSize rightClose))
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2),
              bpPrefixRangeArgMinPrefixPos shape
                (blockStartOf blockSize
                  (blockOfClose blockSize rightClose))
                (rightClose -
                    blockStartOf blockSize
                      (blockOfClose blockSize rightClose) +
                  2))
  interiorRmm_exact :
    forall {leftClose rightClose : Nat},
      blockOfClose blockSize leftClose < blockCount ->
        blockOfClose blockSize rightClose < blockCount ->
          blockOfClose blockSize leftClose + 1 <
              blockOfClose blockSize rightClose ->
            (interiorRmmCosted leftClose rightClose).erase =
              some
                (bpRangeMinExcess shape blockSize
                  (blockOfClose blockSize leftClose + 1)
                  (blockOfClose blockSize rightClose -
                    blockOfClose blockSize leftClose - 1),
                  bpRangeArgMinPrefixPos shape blockSize
                    (blockOfClose blockSize leftClose + 1)
                    (blockOfClose blockSize rightClose -
                      blockOfClose blockSize leftClose - 1))
  read_words_length_le_machine :
    forall {leftClose rightClose : Nat} {word : List Bool},
      word ∈ payloadWordsRead leftClose rightClose ->
        word.length <=
          SuccinctRank.machineWordBits shape.bpCode.length

namespace PayloadLiveRelativeRmmBPCloseMacro

def interiorCandidateCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount overhead middleQueryCost : Nat}
    (component :
      PayloadLiveRelativeRmmBPCloseMacro shape blockSize blockCount
        overhead middleQueryCost)
    (leftClose rightClose : Nat) : Costed (Option (Nat × Nat)) :=
  if blockOfClose blockSize leftClose + 1 <
      blockOfClose blockSize rightClose then
    component.interiorRmmCosted leftClose rightClose
  else
    Costed.pure none

def lcaCloseCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount overhead middleQueryCost : Nat}
    (component :
      PayloadLiveRelativeRmmBPCloseMacro shape blockSize blockCount
        overhead middleQueryCost)
    (leftClose rightClose : Nat) : Costed (Option Nat) :=
  Costed.bind (component.leftFringeCosted leftClose) fun left? =>
    Costed.bind (component.interiorCandidateCosted leftClose rightClose)
      fun middle? =>
        Costed.map
          (fun right? =>
            bpCandidateClose? (bpCandidateMerge3? left? middle? right?))
          (component.rightFringeCosted rightClose)

theorem payload_length
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount overhead middleQueryCost : Nat}
    (component :
      PayloadLiveRelativeRmmBPCloseMacro shape blockSize blockCount
        overhead middleQueryCost) :
    component.payload.length = overhead := by
  exact component.payload_length_eq

theorem interiorCandidateCosted_cost_le
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount overhead middleQueryCost : Nat}
    (component :
      PayloadLiveRelativeRmmBPCloseMacro shape blockSize blockCount
        overhead middleQueryCost)
    (leftClose rightClose : Nat) :
    (component.interiorCandidateCosted leftClose rightClose).cost <=
      middleQueryCost := by
  unfold interiorCandidateCosted
  by_cases hgap :
      blockOfClose blockSize leftClose + 1 <
        blockOfClose blockSize rightClose
  · simp [hgap]
    exact component.interiorRmm_cost_le leftClose rightClose
  · simp [hgap, Costed.pure]

theorem lcaCloseCosted_cost_le
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount overhead middleQueryCost : Nat}
    (component :
      PayloadLiveRelativeRmmBPCloseMacro shape blockSize blockCount
        overhead middleQueryCost)
    (leftClose rightClose : Nat) :
    (component.lcaCloseCosted leftClose rightClose).cost <=
      4 + middleQueryCost := by
  unfold lcaCloseCosted
  have hleft := component.leftFringe_cost_le_two leftClose
  have hmiddle :=
    component.interiorCandidateCosted_cost_le leftClose rightClose
  have hright := component.rightFringe_cost_le_two rightClose
  simp [Costed.bind, Costed.map]
  omega

theorem lcaCloseCosted_erase_decoded
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount overhead middleQueryCost leftClose rightClose : Nat}
    (component :
      PayloadLiveRelativeRmmBPCloseMacro shape blockSize blockCount
        overhead middleQueryCost)
    (hleftBlock :
      blockOfClose blockSize leftClose < blockCount)
    (hrightBlock :
      blockOfClose blockSize rightClose < blockCount) :
    (component.lcaCloseCosted leftClose rightClose).erase =
      bpCandidateClose?
        (bpCandidateMerge3?
          (some
            (bpPrefixRangeMinExcess shape (leftClose + 1)
              (blockStartOf blockSize
                  (blockOfClose blockSize leftClose) +
                blockSize - leftClose),
              bpPrefixRangeArgMinPrefixPos shape (leftClose + 1)
                (blockStartOf blockSize
                    (blockOfClose blockSize leftClose) +
                  blockSize - leftClose)))
          (if blockOfClose blockSize leftClose + 1 <
                blockOfClose blockSize rightClose then
              some
                (bpRangeMinExcess shape blockSize
                  (blockOfClose blockSize leftClose + 1)
                  (blockOfClose blockSize rightClose -
                    blockOfClose blockSize leftClose - 1),
                  bpRangeArgMinPrefixPos shape blockSize
                    (blockOfClose blockSize leftClose + 1)
                    (blockOfClose blockSize rightClose -
                      blockOfClose blockSize leftClose - 1))
            else
              none)
          (some
            (bpPrefixRangeMinExcess shape
              (blockStartOf blockSize
                (blockOfClose blockSize rightClose))
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2),
              bpPrefixRangeArgMinPrefixPos shape
                (blockStartOf blockSize
                  (blockOfClose blockSize rightClose))
                (rightClose -
                    blockStartOf blockSize
                      (blockOfClose blockSize rightClose) +
                  2)))) := by
  have hleft :
      (component.leftFringeCosted leftClose).value =
        some
          (bpPrefixRangeMinExcess shape (leftClose + 1)
            (blockStartOf blockSize
                (blockOfClose blockSize leftClose) +
              blockSize - leftClose),
            bpPrefixRangeArgMinPrefixPos shape (leftClose + 1)
              (blockStartOf blockSize
                  (blockOfClose blockSize leftClose) +
                blockSize - leftClose)) := by
    simpa [Costed.erase] using component.leftFringe_exact hleftBlock
  have hright :
      (component.rightFringeCosted rightClose).value =
        some
          (bpPrefixRangeMinExcess shape
            (blockStartOf blockSize
              (blockOfClose blockSize rightClose))
            (rightClose -
                blockStartOf blockSize
                  (blockOfClose blockSize rightClose) +
              2),
            bpPrefixRangeArgMinPrefixPos shape
              (blockStartOf blockSize
                (blockOfClose blockSize rightClose))
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2)) := by
    simpa [Costed.erase] using component.rightFringe_exact hrightBlock
  unfold lcaCloseCosted interiorCandidateCosted
  by_cases hgap :
      blockOfClose blockSize leftClose + 1 <
        blockOfClose blockSize rightClose
  · have hmiddle :
        (component.interiorRmmCosted leftClose rightClose).value =
          some
            (bpRangeMinExcess shape blockSize
              (blockOfClose blockSize leftClose + 1)
              (blockOfClose blockSize rightClose -
                blockOfClose blockSize leftClose - 1),
              bpRangeArgMinPrefixPos shape blockSize
                (blockOfClose blockSize leftClose + 1)
                (blockOfClose blockSize rightClose -
                  blockOfClose blockSize leftClose - 1)) := by
      simpa [Costed.erase] using
        component.interiorRmm_exact hleftBlock hrightBlock hgap
    simp [Costed.bind, Costed.map, Costed.erase, hleft, hright,
      hmiddle, hgap]
  · simp [Costed.bind, Costed.map, Costed.erase, Costed.pure,
      hleft, hright, hgap]

theorem lcaCloseCosted_exact_of_query_semantics_cross_block
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount overhead middleQueryCost : Nat}
    (component :
      PayloadLiveRelativeRmmBPCloseMacro shape blockSize blockCount
        overhead middleQueryCost)
    {left len leftClose rightClose answerClose : Nat}
    (hlen : 0 < len)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder? shape
          (scanWindow shape.representative left len) =
        some answerClose)
    (hblockSize : 0 < blockSize)
    (hleftBlock :
      blockOfClose blockSize leftClose < blockCount)
    (hrightBlock :
      blockOfClose blockSize rightClose < blockCount)
    (hcross :
      blockOfClose blockSize leftClose <
        blockOfClose blockSize rightClose)
    (hmin :
      forall {pos : Nat},
        leftClose + 1 <= pos ->
          pos < rightClose + 2 ->
            bpExcessAt shape (answerClose + 1) <=
              bpExcessAt shape pos)
    (hleftmost :
      forall {pos : Nat},
        leftClose + 1 <= pos ->
          pos < answerClose + 1 ->
            bpExcessAt shape (answerClose + 1) <
              bpExcessAt shape pos) :
    (component.lcaCloseCosted leftClose rightClose).erase =
      some answerClose := by
  rw [component.lcaCloseCosted_erase_decoded hleftBlock hrightBlock]
  have hmerge :=
    bpRelativeRmmCandidateMerge_exact_of_query_semantics
      (hlen := hlen) hleft hright hanswer hblockSize
      hleftBlock hrightBlock hcross hmin hleftmost
  simp [hmerge, bpCandidateClose?]

theorem lcaCloseCosted_exact_of_query_cross_block
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount overhead middleQueryCost : Nat}
    (component :
      PayloadLiveRelativeRmmBPCloseMacro shape blockSize blockCount
        overhead middleQueryCost)
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
    (hblockSize : 0 < blockSize)
    (hleftBlock :
      blockOfClose blockSize leftClose < blockCount)
    (hrightBlock :
      blockOfClose blockSize rightClose < blockCount)
    (hcross :
      blockOfClose blockSize leftClose <
        blockOfClose blockSize rightClose) :
    (component.lcaCloseCosted leftClose rightClose).erase =
      some answerClose := by
  have hsemantic :=
    answerClose_prefix_leftmost_min_excess_of_query
      (shape := shape) (start := left) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      (answerClose := answerClose)
      hlen hbound hleft hright hanswer
  exact
    component.lcaCloseCosted_exact_of_query_semantics_cross_block
      hlen hleft hright hanswer hblockSize hleftBlock hrightBlock
      hcross hsemantic.1 hsemantic.2

theorem profile
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount overhead middleQueryCost : Nat}
    (component :
      PayloadLiveRelativeRmmBPCloseMacro shape blockSize blockCount
        overhead middleQueryCost) :
    component.payload.length = overhead /\
      (forall leftClose rightClose,
        (component.lcaCloseCosted leftClose rightClose).cost <=
          4 + middleQueryCost) := by
  exact ⟨component.payload_length, component.lcaCloseCosted_cost_le⟩

end PayloadLiveRelativeRmmBPCloseMacro

end SuccinctCloseProposal
end RMQ
