import RMQ.Core.SuccinctClose.EndpointFringe

/-!
# Relative rmM-style BP close macro interface

The final relative-rmM macro/micro close-navigation spine and payload-live
navigation family. The historical `RMQ.SuccinctCloseProposal` namespace is
preserved.
-/

namespace RMQ
namespace SuccinctCloseProposal

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
          SuccinctRankProposal.machineWordBits shape.bpCode.length

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

def payloadWordReadOfGet?
    (words : Array (List Bool)) (index : Nat) : List (List Bool) :=
  match words[index]? with
  | some word => [word]
  | none => []

theorem payloadWordReadOfGet?_length_le
    {words : Array (List Bool)} {index limit : Nat}
    (hword :
      forall {word : List Bool},
        words[index]? = some word -> word.length <= limit)
    {word : List Bool}
    (hmem : word ∈ payloadWordReadOfGet? words index) :
    word.length <= limit := by
  unfold payloadWordReadOfGet? at hmem
  cases hget : words[index]? with
  | none =>
      simp [hget] at hmem
  | some stored =>
      simp [hget] at hmem
      rcases hmem with rfl
      exact hword hget

/--
Local endpoint-fringe slot for the left endpoint of a cross-block query.

The slot is block-local: it is keyed only by the endpoint's offset within its
block.  This is the compact replacement for the global dense
`endpointLeftFringeRanges blockSize blockCount` index.
-/
def endpointLeftLocalFringeSlot (_blockSize localClose : Nat) : Nat :=
  localClose

/--
Local endpoint-fringe slot for the right endpoint of a cross-block query.

Right-fringe slots occupy the second half of the per-code local table, after
the left-fringe slots.
-/
def endpointRightLocalFringeSlot (blockSize localClose : Nat) : Nat :=
  blockSize + localClose

/-- Decode one local endpoint-fringe table slot into the represented prefix range. -/
def endpointLocalFringeRangeOfSlot
    (blockSize blockStart slot : Nat) : Nat × Nat :=
  if slot < blockSize then
    (blockStart + slot + 1, blockSize - slot)
  else
    (blockStart, slot - blockSize + 2)

/--
All endpoint-fringe ranges for a single block, stored in a local table:
left-fringe ranges first, then right-fringe ranges.
-/
def endpointLocalFringeRanges
    (blockSize blockStart : Nat) : List (Nat × Nat) :=
  (List.range (2 * blockSize)).map
    (endpointLocalFringeRangeOfSlot blockSize blockStart)

theorem endpointLocalFringeRanges_length
    (blockSize blockStart : Nat) :
    (endpointLocalFringeRanges blockSize blockStart).length =
      2 * blockSize := by
  simp [endpointLocalFringeRanges]

theorem endpointLocalFringeRanges_get?_left
    {blockSize blockStart localClose : Nat}
    (hlocal : localClose < blockSize) :
    (endpointLocalFringeRanges blockSize blockStart)[
        endpointLeftLocalFringeSlot blockSize localClose]? =
      some (blockStart + localClose + 1, blockSize - localClose) := by
  have hslot :
      endpointLeftLocalFringeSlot blockSize localClose < 2 * blockSize := by
    simp [endpointLeftLocalFringeSlot]
    omega
  have hslotGet :
      (List.range (2 * blockSize))[
          endpointLeftLocalFringeSlot blockSize localClose]? =
        some (endpointLeftLocalFringeSlot blockSize localClose) := by
    exact List.getElem?_range hslot
  have hmapped :
      ((List.range (2 * blockSize)).map
          (endpointLocalFringeRangeOfSlot blockSize blockStart))[
            endpointLeftLocalFringeSlot blockSize localClose]? =
        some
          (endpointLocalFringeRangeOfSlot blockSize blockStart
            (endpointLeftLocalFringeSlot blockSize localClose)) := by
    simp [List.getElem?_map, hslotGet]
  simpa [endpointLocalFringeRanges, endpointLocalFringeRangeOfSlot,
    endpointLeftLocalFringeSlot, hlocal] using hmapped

theorem endpointLocalFringeRanges_get?_right
    {blockSize blockStart localClose : Nat}
    (hlocal : localClose < blockSize) :
    (endpointLocalFringeRanges blockSize blockStart)[
        endpointRightLocalFringeSlot blockSize localClose]? =
      some (blockStart, localClose + 2) := by
  have hslot :
      endpointRightLocalFringeSlot blockSize localClose < 2 * blockSize := by
    simp [endpointRightLocalFringeSlot]
    omega
  have hslotGet :
      (List.range (2 * blockSize))[
          endpointRightLocalFringeSlot blockSize localClose]? =
        some (endpointRightLocalFringeSlot blockSize localClose) := by
    exact List.getElem?_range hslot
  have hnot :
      ¬ endpointRightLocalFringeSlot blockSize localClose < blockSize := by
    simp [endpointRightLocalFringeSlot]
  have hcount :
      endpointRightLocalFringeSlot blockSize localClose - blockSize + 2 =
        localClose + 2 := by
    simp [endpointRightLocalFringeSlot]
  have hmapped :
      ((List.range (2 * blockSize)).map
          (endpointLocalFringeRangeOfSlot blockSize blockStart))[
            endpointRightLocalFringeSlot blockSize localClose]? =
        some
          (endpointLocalFringeRangeOfSlot blockSize blockStart
            (endpointRightLocalFringeSlot blockSize localClose)) := by
    simp [List.getElem?_map, hslotGet]
  simpa [endpointLocalFringeRanges, endpointLocalFringeRangeOfSlot,
    hnot, hcount] using hmapped

theorem endpointLocalFringeMinExcessEntries_get?_left
    {shape : Cartesian.CartesianShape}
    {blockSize blockStart localClose : Nat}
    (hlocal : localClose < blockSize) :
    (bpPrefixRangeMinExcessEntries shape
        (endpointLocalFringeRanges blockSize blockStart))[
          endpointLeftLocalFringeSlot blockSize localClose]? =
      some
        (bpPrefixRangeMinExcess shape
          (blockStart + localClose + 1) (blockSize - localClose)) := by
  exact
    bpPrefixRangeMinExcessEntries_get?_of_ranges_get?
      (endpointLocalFringeRanges_get?_left hlocal)

theorem endpointLocalFringeArgMinEntries_get?_left
    {shape : Cartesian.CartesianShape}
    {blockSize blockStart localClose : Nat}
    (hlocal : localClose < blockSize) :
    (bpPrefixRangeArgMinPrefixPosEntries shape
        (endpointLocalFringeRanges blockSize blockStart))[
          endpointLeftLocalFringeSlot blockSize localClose]? =
      some
        (bpPrefixRangeArgMinPrefixPos shape
          (blockStart + localClose + 1) (blockSize - localClose)) := by
  exact
    bpPrefixRangeArgMinPrefixPosEntries_get?_of_ranges_get?
      (endpointLocalFringeRanges_get?_left hlocal)

theorem endpointLocalFringeMinExcessEntries_get?_right
    {shape : Cartesian.CartesianShape}
    {blockSize blockStart localClose : Nat}
    (hlocal : localClose < blockSize) :
    (bpPrefixRangeMinExcessEntries shape
        (endpointLocalFringeRanges blockSize blockStart))[
          endpointRightLocalFringeSlot blockSize localClose]? =
      some
        (bpPrefixRangeMinExcess shape blockStart (localClose + 2)) := by
  exact
    bpPrefixRangeMinExcessEntries_get?_of_ranges_get?
      (endpointLocalFringeRanges_get?_right hlocal)

theorem endpointLocalFringeArgMinEntries_get?_right
    {shape : Cartesian.CartesianShape}
    {blockSize blockStart localClose : Nat}
    (hlocal : localClose < blockSize) :
    (bpPrefixRangeArgMinPrefixPosEntries shape
        (endpointLocalFringeRanges blockSize blockStart))[
          endpointRightLocalFringeSlot blockSize localClose]? =
      some
        (bpPrefixRangeArgMinPrefixPos shape blockStart (localClose + 2)) := by
  exact
    bpPrefixRangeArgMinPrefixPosEntries_get?_of_ranges_get?
      (endpointLocalFringeRanges_get?_right hlocal)

/--
Payload-live endpoint-fringe codebook.

The query path reads a charged per-block code and then two charged fixed-width
payload words from the finite local endpoint-fringe table for that code.  The
payload is a classifier plus one local left/right-fringe witness table per
code; there is no global dense table over all endpoint positions.
-/
structure PayloadLiveBlockEndpointFringeCodebook
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount codeCount codeWidth codeOverhead
      fieldWidth tableOverhead : Nat) where
  classifier :
    BlockCodeTable blockCount codeCount codeWidth codeOverhead
  minEntriesByCode : Nat -> List Nat
  argEntriesByCode : Nat -> List Nat
  minTable :
    (code : Nat) ->
      FixedWidthNatTable (minEntriesByCode code) fieldWidth
  argTable :
    (code : Nat) ->
      FixedWidthNatTable (argEntriesByCode code) fieldWidth
  tablePayload : List Bool
  tablePayload_eq_tables :
    tablePayload =
      (List.range codeCount).flatMap fun code =>
        (minTable code).payload ++ (argTable code).payload
  tablePayload_length_eq :
    tablePayload.length = codeCount * tableOverhead
  table_payload_length_eq :
    forall {code : Nat}, code < codeCount ->
      (minTable code).payload.length +
          (argTable code).payload.length =
        tableOverhead
  block_fringe_entries :
    forall {block code : Nat},
      classifier.codeAt block = some code ->
        minEntriesByCode code =
            bpPrefixRangeMinExcessEntries shape
              (endpointLocalFringeRanges blockSize
                (blockStartOf blockSize block)) /\
          argEntriesByCode code =
            bpPrefixRangeArgMinPrefixPosEntries shape
              (endpointLocalFringeRanges blockSize
                (blockStartOf blockSize block))

namespace PayloadLiveBlockEndpointFringeCodebook

def payload
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      fieldWidth tableOverhead : Nat}
    (fringe :
      PayloadLiveBlockEndpointFringeCodebook shape blockSize blockCount
        codeCount codeWidth codeOverhead fieldWidth tableOverhead) :
    List Bool :=
  fringe.classifier.payload ++ fringe.tablePayload

def leftSlot
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      fieldWidth tableOverhead : Nat}
    (_fringe :
      PayloadLiveBlockEndpointFringeCodebook shape blockSize blockCount
        codeCount codeWidth codeOverhead fieldWidth tableOverhead)
    (block close : Nat) : Nat :=
  endpointLeftLocalFringeSlot blockSize
    (close - blockStartOf blockSize block)

def rightSlot
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      fieldWidth tableOverhead : Nat}
    (_fringe :
      PayloadLiveBlockEndpointFringeCodebook shape blockSize blockCount
        codeCount codeWidth codeOverhead fieldWidth tableOverhead)
    (block close : Nat) : Nat :=
  endpointRightLocalFringeSlot blockSize
    (close - blockStartOf blockSize block)

def witnessCostedAtBlock
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      fieldWidth tableOverhead : Nat}
    (fringe :
      PayloadLiveBlockEndpointFringeCodebook shape blockSize blockCount
        codeCount codeWidth codeOverhead fieldWidth tableOverhead)
    (slot block : Nat) : Costed (Option (Nat × Nat)) :=
  Costed.bind (fringe.classifier.codeCosted block) fun code? =>
    match code? with
    | none => Costed.pure none
    | some code =>
        if _hcode : code < codeCount then
          Costed.bind ((fringe.minTable code).readCosted slot) fun min? =>
            Costed.map
              (fun arg? =>
                match min?, arg? with
                | some minExcess, some prefixPos =>
                    some (minExcess, prefixPos)
                | _, _ => none)
              ((fringe.argTable code).readCosted slot)
        else
          Costed.pure none

def leftFringeCostedAtBlock
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      fieldWidth tableOverhead : Nat}
    (fringe :
      PayloadLiveBlockEndpointFringeCodebook shape blockSize blockCount
        codeCount codeWidth codeOverhead fieldWidth tableOverhead)
    (block close : Nat) : Costed (Option (Nat × Nat)) :=
  fringe.witnessCostedAtBlock (fringe.leftSlot block close) block

def rightFringeCostedAtBlock
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      fieldWidth tableOverhead : Nat}
    (fringe :
      PayloadLiveBlockEndpointFringeCodebook shape blockSize blockCount
        codeCount codeWidth codeOverhead fieldWidth tableOverhead)
    (block close : Nat) : Costed (Option (Nat × Nat)) :=
  fringe.witnessCostedAtBlock (fringe.rightSlot block close) block

def leftFringeCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      fieldWidth tableOverhead : Nat}
    (fringe :
      PayloadLiveBlockEndpointFringeCodebook shape blockSize blockCount
        codeCount codeWidth codeOverhead fieldWidth tableOverhead)
    (close : Nat) : Costed (Option (Nat × Nat)) :=
  fringe.leftFringeCostedAtBlock (blockOfClose blockSize close) close

def rightFringeCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      fieldWidth tableOverhead : Nat}
    (fringe :
      PayloadLiveBlockEndpointFringeCodebook shape blockSize blockCount
        codeCount codeWidth codeOverhead fieldWidth tableOverhead)
    (close : Nat) : Costed (Option (Nat × Nat)) :=
  fringe.rightFringeCostedAtBlock (blockOfClose blockSize close) close

def wordsReadAtBlock
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      fieldWidth tableOverhead : Nat}
    (fringe :
      PayloadLiveBlockEndpointFringeCodebook shape blockSize blockCount
        codeCount codeWidth codeOverhead fieldWidth tableOverhead)
    (slot block : Nat) : List (List Bool) :=
  payloadWordReadOfGet? fringe.classifier.table.store.words block ++
    match fringe.classifier.codeAt block with
    | none => []
    | some code =>
        if code < codeCount then
          payloadWordReadOfGet? (fringe.minTable code).store.words slot ++
            payloadWordReadOfGet? (fringe.argTable code).store.words slot
        else
          []

def leftWordsReadAtBlock
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      fieldWidth tableOverhead : Nat}
    (fringe :
      PayloadLiveBlockEndpointFringeCodebook shape blockSize blockCount
        codeCount codeWidth codeOverhead fieldWidth tableOverhead)
    (block close : Nat) : List (List Bool) :=
  fringe.wordsReadAtBlock (fringe.leftSlot block close) block

def rightWordsReadAtBlock
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      fieldWidth tableOverhead : Nat}
    (fringe :
      PayloadLiveBlockEndpointFringeCodebook shape blockSize blockCount
        codeCount codeWidth codeOverhead fieldWidth tableOverhead)
    (block close : Nat) : List (List Bool) :=
  fringe.wordsReadAtBlock (fringe.rightSlot block close) block

theorem payload_length
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      fieldWidth tableOverhead : Nat}
    (fringe :
      PayloadLiveBlockEndpointFringeCodebook shape blockSize blockCount
        codeCount codeWidth codeOverhead fieldWidth tableOverhead) :
    fringe.payload.length =
      codeOverhead + codeCount * tableOverhead := by
  simp [payload, fringe.classifier.payload_length,
    fringe.tablePayload_length_eq]

theorem witnessCostedAtBlock_cost_le_three
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      fieldWidth tableOverhead : Nat}
    (fringe :
      PayloadLiveBlockEndpointFringeCodebook shape blockSize blockCount
        codeCount codeWidth codeOverhead fieldWidth tableOverhead)
    (slot block : Nat) :
    (fringe.witnessCostedAtBlock slot block).cost <= 3 := by
  unfold witnessCostedAtBlock
  have hclassifier := fringe.classifier.codeCosted_cost_le_one block
  cases hread : (fringe.classifier.codeCosted block).value with
  | none =>
      simp [Costed.bind, Costed.pure, hread]
      omega
  | some code =>
      by_cases hcode : code < codeCount
      · cases hmin : ((fringe.minTable code).readCosted slot).value with
        | none =>
            simp [Costed.bind, Costed.map, Costed.pure, hread, hcode,
              hmin]
            omega
        | some minExcess =>
            simp [Costed.bind, Costed.map, Costed.pure, hread, hcode,
              hmin]
            omega
      · simp [Costed.bind, Costed.pure, hread, hcode]
        omega

theorem leftFringeCostedAtBlock_cost_le_three
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      fieldWidth tableOverhead : Nat}
    (fringe :
      PayloadLiveBlockEndpointFringeCodebook shape blockSize blockCount
        codeCount codeWidth codeOverhead fieldWidth tableOverhead)
    (block close : Nat) :
    (fringe.leftFringeCostedAtBlock block close).cost <= 3 := by
  exact fringe.witnessCostedAtBlock_cost_le_three
    (fringe.leftSlot block close) block

theorem rightFringeCostedAtBlock_cost_le_three
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      fieldWidth tableOverhead : Nat}
    (fringe :
      PayloadLiveBlockEndpointFringeCodebook shape blockSize blockCount
        codeCount codeWidth codeOverhead fieldWidth tableOverhead)
    (block close : Nat) :
    (fringe.rightFringeCostedAtBlock block close).cost <= 3 := by
  exact fringe.witnessCostedAtBlock_cost_le_three
    (fringe.rightSlot block close) block

theorem leftFringeCosted_cost_le_three
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      fieldWidth tableOverhead : Nat}
    (fringe :
      PayloadLiveBlockEndpointFringeCodebook shape blockSize blockCount
        codeCount codeWidth codeOverhead fieldWidth tableOverhead)
    (close : Nat) :
    (fringe.leftFringeCosted close).cost <= 3 := by
  unfold leftFringeCosted
  exact fringe.leftFringeCostedAtBlock_cost_le_three
    (blockOfClose blockSize close) close

theorem rightFringeCosted_cost_le_three
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      fieldWidth tableOverhead : Nat}
    (fringe :
      PayloadLiveBlockEndpointFringeCodebook shape blockSize blockCount
        codeCount codeWidth codeOverhead fieldWidth tableOverhead)
    (close : Nat) :
    (fringe.rightFringeCosted close).cost <= 3 := by
  unfold rightFringeCosted
  exact fringe.rightFringeCostedAtBlock_cost_le_three
    (blockOfClose blockSize close) close

theorem leftFringeCostedAtBlock_exact_of_code
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      fieldWidth tableOverhead : Nat}
    (fringe :
      PayloadLiveBlockEndpointFringeCodebook shape blockSize blockCount
        codeCount codeWidth codeOverhead fieldWidth tableOverhead)
    {block close code : Nat}
    (hcodeAt : fringe.classifier.codeAt block = some code)
    (hcloseLo : blockStartOf blockSize block <= close)
    (hcloseHi : close < blockStartOf blockSize block + blockSize) :
    (fringe.leftFringeCostedAtBlock block close).erase =
      some
        (bpPrefixRangeMinExcess shape (close + 1)
          (blockStartOf blockSize block + blockSize - close),
          bpPrefixRangeArgMinPrefixPos shape (close + 1)
            (blockStartOf blockSize block + blockSize - close)) := by
  let localClose := close - blockStartOf blockSize block
  have hlocal : localClose < blockSize := by
    dsimp [localClose]
    omega
  have hstart :
      blockStartOf blockSize block + localClose + 1 = close + 1 := by
    dsimp [localClose]
    omega
  have hcount :
      blockSize - localClose =
        blockStartOf blockSize block + blockSize - close := by
    dsimp [localClose]
    omega
  have hread :
      (fringe.classifier.codeCosted block).value = some code := by
    simpa [Costed.erase] using
      fringe.classifier.codeCosted_exact_of_codeAt hcodeAt
  have hcodeLt : code < codeCount :=
    fringe.classifier.codeAt_lt hcodeAt
  have hentries := fringe.block_fringe_entries hcodeAt
  have hminEntry :
      (fringe.minEntriesByCode code)[fringe.leftSlot block close]? =
        some
          (bpPrefixRangeMinExcess shape (close + 1)
            (blockStartOf blockSize block + blockSize - close)) := by
    rw [hentries.1]
    simpa [leftSlot, endpointLeftLocalFringeSlot, localClose, hstart,
      hcount] using
      (endpointLocalFringeMinExcessEntries_get?_left
        (shape := shape) (blockSize := blockSize)
        (blockStart := blockStartOf blockSize block)
        (localClose := localClose) hlocal)
  have hargEntry :
      (fringe.argEntriesByCode code)[fringe.leftSlot block close]? =
        some
          (bpPrefixRangeArgMinPrefixPos shape (close + 1)
            (blockStartOf blockSize block + blockSize - close)) := by
    rw [hentries.2]
    simpa [leftSlot, endpointLeftLocalFringeSlot, localClose, hstart,
      hcount] using
      (endpointLocalFringeArgMinEntries_get?_left
        (shape := shape) (blockSize := blockSize)
        (blockStart := blockStartOf blockSize block)
        (localClose := localClose) hlocal)
  have hminRead :
      ((fringe.minTable code).readCosted
          (fringe.leftSlot block close)).value =
        some
          (bpPrefixRangeMinExcess shape (close + 1)
            (blockStartOf blockSize block + blockSize - close)) := by
    have h := (fringe.minTable code).readCosted_erase
      (fringe.leftSlot block close)
    simpa [Costed.erase, hminEntry] using h
  have hargRead :
      ((fringe.argTable code).readCosted
          (fringe.leftSlot block close)).value =
        some
          (bpPrefixRangeArgMinPrefixPos shape (close + 1)
            (blockStartOf blockSize block + blockSize - close)) := by
    have h := (fringe.argTable code).readCosted_erase
      (fringe.leftSlot block close)
    simpa [Costed.erase, hargEntry] using h
  simp [leftFringeCostedAtBlock, witnessCostedAtBlock, Costed.bind,
    Costed.map, Costed.erase, hread, hcodeLt, hminRead, hargRead]

theorem rightFringeCostedAtBlock_exact_of_code
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      fieldWidth tableOverhead : Nat}
    (fringe :
      PayloadLiveBlockEndpointFringeCodebook shape blockSize blockCount
        codeCount codeWidth codeOverhead fieldWidth tableOverhead)
    {block close code : Nat}
    (hcodeAt : fringe.classifier.codeAt block = some code)
    (hcloseLo : blockStartOf blockSize block <= close)
    (hcloseHi : close < blockStartOf blockSize block + blockSize) :
    (fringe.rightFringeCostedAtBlock block close).erase =
      some
        (bpPrefixRangeMinExcess shape
          (blockStartOf blockSize block)
          (close - blockStartOf blockSize block + 2),
          bpPrefixRangeArgMinPrefixPos shape
            (blockStartOf blockSize block)
            (close - blockStartOf blockSize block + 2)) := by
  let localClose := close - blockStartOf blockSize block
  have hlocal : localClose < blockSize := by
    dsimp [localClose]
    omega
  have hcount :
      localClose + 2 =
        close - blockStartOf blockSize block + 2 := by
    dsimp [localClose]
  have hread :
      (fringe.classifier.codeCosted block).value = some code := by
    simpa [Costed.erase] using
      fringe.classifier.codeCosted_exact_of_codeAt hcodeAt
  have hcodeLt : code < codeCount :=
    fringe.classifier.codeAt_lt hcodeAt
  have hentries := fringe.block_fringe_entries hcodeAt
  have hminEntry :
      (fringe.minEntriesByCode code)[fringe.rightSlot block close]? =
        some
          (bpPrefixRangeMinExcess shape
            (blockStartOf blockSize block)
            (close - blockStartOf blockSize block + 2)) := by
    rw [hentries.1]
    simpa [rightSlot, endpointRightLocalFringeSlot, localClose, hcount] using
      (endpointLocalFringeMinExcessEntries_get?_right
        (shape := shape) (blockSize := blockSize)
        (blockStart := blockStartOf blockSize block)
        (localClose := localClose) hlocal)
  have hargEntry :
      (fringe.argEntriesByCode code)[fringe.rightSlot block close]? =
        some
          (bpPrefixRangeArgMinPrefixPos shape
            (blockStartOf blockSize block)
            (close - blockStartOf blockSize block + 2)) := by
    rw [hentries.2]
    simpa [rightSlot, endpointRightLocalFringeSlot, localClose, hcount] using
      (endpointLocalFringeArgMinEntries_get?_right
        (shape := shape) (blockSize := blockSize)
        (blockStart := blockStartOf blockSize block)
        (localClose := localClose) hlocal)
  have hminRead :
      ((fringe.minTable code).readCosted
          (fringe.rightSlot block close)).value =
        some
          (bpPrefixRangeMinExcess shape
            (blockStartOf blockSize block)
            (close - blockStartOf blockSize block + 2)) := by
    have h := (fringe.minTable code).readCosted_erase
      (fringe.rightSlot block close)
    simpa [Costed.erase, hminEntry] using h
  have hargRead :
      ((fringe.argTable code).readCosted
          (fringe.rightSlot block close)).value =
        some
          (bpPrefixRangeArgMinPrefixPos shape
            (blockStartOf blockSize block)
            (close - blockStartOf blockSize block + 2)) := by
    have h := (fringe.argTable code).readCosted_erase
      (fringe.rightSlot block close)
    simpa [Costed.erase, hargEntry] using h
  simp [rightFringeCostedAtBlock, witnessCostedAtBlock, Costed.bind,
    Costed.map, Costed.erase, hread, hcodeLt, hminRead, hargRead]

theorem leftFringeCostedAtBlock_exact
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      fieldWidth tableOverhead : Nat}
    (fringe :
      PayloadLiveBlockEndpointFringeCodebook shape blockSize blockCount
        codeCount codeWidth codeOverhead fieldWidth tableOverhead)
    {block close : Nat}
    (hblock : block < blockCount)
    (hcloseLo : blockStartOf blockSize block <= close)
    (hcloseHi : close < blockStartOf blockSize block + blockSize) :
    (fringe.leftFringeCostedAtBlock block close).erase =
      some
        (bpPrefixRangeMinExcess shape (close + 1)
          (blockStartOf blockSize block + blockSize - close),
          bpPrefixRangeArgMinPrefixPos shape (close + 1)
            (blockStartOf blockSize block + blockSize - close)) := by
  rcases fringe.classifier.codeAt_exists_of_lt hblock with
    ⟨code, hcodeAt⟩
  exact fringe.leftFringeCostedAtBlock_exact_of_code
    hcodeAt hcloseLo hcloseHi

theorem rightFringeCostedAtBlock_exact
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      fieldWidth tableOverhead : Nat}
    (fringe :
      PayloadLiveBlockEndpointFringeCodebook shape blockSize blockCount
        codeCount codeWidth codeOverhead fieldWidth tableOverhead)
    {block close : Nat}
    (hblock : block < blockCount)
    (hcloseLo : blockStartOf blockSize block <= close)
    (hcloseHi : close < blockStartOf blockSize block + blockSize) :
    (fringe.rightFringeCostedAtBlock block close).erase =
      some
        (bpPrefixRangeMinExcess shape
          (blockStartOf blockSize block)
          (close - blockStartOf blockSize block + 2),
          bpPrefixRangeArgMinPrefixPos shape
            (blockStartOf blockSize block)
            (close - blockStartOf blockSize block + 2)) := by
  rcases fringe.classifier.codeAt_exists_of_lt hblock with
    ⟨code, hcodeAt⟩
  exact fringe.rightFringeCostedAtBlock_exact_of_code
    hcodeAt hcloseLo hcloseHi

theorem leftFringeCosted_exact
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      fieldWidth tableOverhead : Nat}
    (fringe :
      PayloadLiveBlockEndpointFringeCodebook shape blockSize blockCount
        codeCount codeWidth codeOverhead fieldWidth tableOverhead)
    (hblockSize : 0 < blockSize)
    {close : Nat}
    (hblock : blockOfClose blockSize close < blockCount) :
    (fringe.leftFringeCosted close).erase =
      some
        (bpPrefixRangeMinExcess shape (close + 1)
          (blockStartOf blockSize (blockOfClose blockSize close) +
            blockSize - close),
          bpPrefixRangeArgMinPrefixPos shape (close + 1)
            (blockStartOf blockSize (blockOfClose blockSize close) +
              blockSize - close)) := by
  unfold leftFringeCosted
  exact
    fringe.leftFringeCostedAtBlock_exact hblock
      blockStartOf_blockOfClose_le
      (close_lt_blockStartOf_blockOfClose_add hblockSize)

theorem rightFringeCosted_exact
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      fieldWidth tableOverhead : Nat}
    (fringe :
      PayloadLiveBlockEndpointFringeCodebook shape blockSize blockCount
        codeCount codeWidth codeOverhead fieldWidth tableOverhead)
    (hblockSize : 0 < blockSize)
    {close : Nat}
    (hblock : blockOfClose blockSize close < blockCount) :
    (fringe.rightFringeCosted close).erase =
      some
        (bpPrefixRangeMinExcess shape
          (blockStartOf blockSize (blockOfClose blockSize close))
          (close -
              blockStartOf blockSize (blockOfClose blockSize close) +
            2),
          bpPrefixRangeArgMinPrefixPos shape
            (blockStartOf blockSize (blockOfClose blockSize close))
            (close -
                blockStartOf blockSize (blockOfClose blockSize close) +
              2)) := by
  unfold rightFringeCosted
  exact
    fringe.rightFringeCostedAtBlock_exact hblock
      blockStartOf_blockOfClose_le
      (close_lt_blockStartOf_blockOfClose_add hblockSize)

theorem wordsReadAtBlock_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      fieldWidth tableOverhead : Nat}
    (fringe :
      PayloadLiveBlockEndpointFringeCodebook shape blockSize blockCount
        codeCount codeWidth codeOverhead fieldWidth tableOverhead)
    (hcodeMachine :
      codeWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hfieldMachine :
      fieldWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    {slot block : Nat} {word : List Bool}
    (hmem : word ∈ fringe.wordsReadAtBlock slot block) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  have hclass :
      forall {word : List Bool},
        fringe.classifier.table.store.words[block]? = some word ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length := by
    intro word hword
    have hlen := fringe.classifier.table.read_word_length_of_some hword
    omega
  unfold wordsReadAtBlock at hmem
  simp only [List.mem_append] at hmem
  rcases hmem with hclassMem | htableMem
  · exact payloadWordReadOfGet?_length_le hclass hclassMem
  · cases hcodeAt : fringe.classifier.codeAt block with
    | none =>
        simp [hcodeAt] at htableMem
    | some code =>
        by_cases hcode : code < codeCount
        · have hmin :
            forall {word : List Bool},
              (fringe.minTable code).store.words[slot]? = some word ->
                word.length <=
                  SuccinctRankProposal.machineWordBits
                    shape.bpCode.length := by
            intro word hword
            have hlen := (fringe.minTable code).read_word_length_of_some
              hword
            omega
          have harg :
            forall {word : List Bool},
              (fringe.argTable code).store.words[slot]? = some word ->
                word.length <=
                  SuccinctRankProposal.machineWordBits
                    shape.bpCode.length := by
            intro word hword
            have hlen := (fringe.argTable code).read_word_length_of_some
              hword
            omega
          simp [hcodeAt, hcode, List.mem_append] at htableMem
          rcases htableMem with hminMem | hargMem
          · exact payloadWordReadOfGet?_length_le hmin hminMem
          · exact payloadWordReadOfGet?_length_le harg hargMem
        · simp [hcodeAt, hcode] at htableMem

theorem read_words_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      fieldWidth tableOverhead : Nat}
    (fringe :
      PayloadLiveBlockEndpointFringeCodebook shape blockSize blockCount
        codeCount codeWidth codeOverhead fieldWidth tableOverhead)
    (hcodeMachine :
      codeWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hfieldMachine :
      fieldWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length) :
    forall {slot block : Nat} {word : List Bool},
      word ∈ fringe.wordsReadAtBlock slot block ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  intro slot block word hmem
  exact fringe.wordsReadAtBlock_length_le_machine
    hcodeMachine hfieldMachine hmem

theorem leftWordsReadAtBlock_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      fieldWidth tableOverhead : Nat}
    (fringe :
      PayloadLiveBlockEndpointFringeCodebook shape blockSize blockCount
        codeCount codeWidth codeOverhead fieldWidth tableOverhead)
    (hcodeMachine :
      codeWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hfieldMachine :
      fieldWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    {block close : Nat} {word : List Bool}
    (hmem : word ∈ fringe.leftWordsReadAtBlock block close) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  exact fringe.wordsReadAtBlock_length_le_machine
    hcodeMachine hfieldMachine hmem

theorem rightWordsReadAtBlock_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      fieldWidth tableOverhead : Nat}
    (fringe :
      PayloadLiveBlockEndpointFringeCodebook shape blockSize blockCount
        codeCount codeWidth codeOverhead fieldWidth tableOverhead)
    (hcodeMachine :
      codeWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hfieldMachine :
      fieldWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    {block close : Nat} {word : List Bool}
    (hmem : word ∈ fringe.rightWordsReadAtBlock block close) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  exact fringe.wordsReadAtBlock_length_le_machine
    hcodeMachine hfieldMachine hmem

theorem profile
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      fieldWidth tableOverhead : Nat}
    (fringe :
      PayloadLiveBlockEndpointFringeCodebook shape blockSize blockCount
        codeCount codeWidth codeOverhead fieldWidth tableOverhead) :
    fringe.payload.length =
        codeOverhead + codeCount * tableOverhead /\
      (forall close,
        (fringe.leftFringeCosted close).cost <= 3 /\
          (fringe.rightFringeCosted close).cost <= 3) /\
      (forall {close : Nat},
        0 < blockSize ->
          blockOfClose blockSize close < blockCount ->
            (fringe.leftFringeCosted close).erase =
              some
                (bpPrefixRangeMinExcess shape (close + 1)
                  (blockStartOf blockSize
                      (blockOfClose blockSize close) +
                    blockSize - close),
                  bpPrefixRangeArgMinPrefixPos shape (close + 1)
                    (blockStartOf blockSize
                        (blockOfClose blockSize close) +
                      blockSize - close))) /\
      (forall {close : Nat},
        0 < blockSize ->
          blockOfClose blockSize close < blockCount ->
            (fringe.rightFringeCosted close).erase =
              some
                (bpPrefixRangeMinExcess shape
                  (blockStartOf blockSize
                    (blockOfClose blockSize close))
                  (close -
                      blockStartOf blockSize
                        (blockOfClose blockSize close) +
                    2),
                  bpPrefixRangeArgMinPrefixPos shape
                    (blockStartOf blockSize
                      (blockOfClose blockSize close))
                    (close -
                        blockStartOf blockSize
                          (blockOfClose blockSize close) +
                      2))) := by
  constructor
  · exact fringe.payload_length
  constructor
  · intro close
    exact ⟨fringe.leftFringeCosted_cost_le_three close,
      fringe.rightFringeCosted_cost_le_three close⟩
  constructor
  · intro close hblockSize hblock
    exact fringe.leftFringeCosted_exact hblockSize hblock
  · intro close hblockSize hblock
    exact fringe.rightFringeCosted_exact hblockSize hblock

end PayloadLiveBlockEndpointFringeCodebook

def concreteEndpointFringeMinEntries
    (shape : Cartesian.CartesianShape)
    (blockSize code : Nat) : List Nat :=
  bpPrefixRangeMinExcessEntries shape
    (endpointLocalFringeRanges blockSize
      (blockStartOf blockSize code))

def concreteEndpointFringeArgEntries
    (shape : Cartesian.CartesianShape)
    (blockSize code : Nat) : List Nat :=
  bpPrefixRangeArgMinPrefixPosEntries shape
    (endpointLocalFringeRanges blockSize
      (blockStartOf blockSize code))

theorem concreteEndpointFringeMinEntries_length
    (shape : Cartesian.CartesianShape)
    (blockSize code : Nat) :
    (concreteEndpointFringeMinEntries shape blockSize code).length =
      2 * blockSize := by
  simp [concreteEndpointFringeMinEntries,
    bpPrefixRangeMinExcessEntries_length,
    endpointLocalFringeRanges_length]

theorem concreteEndpointFringeArgEntries_length
    (shape : Cartesian.CartesianShape)
    (blockSize code : Nat) :
    (concreteEndpointFringeArgEntries shape blockSize code).length =
      2 * blockSize := by
  simp [concreteEndpointFringeArgEntries,
    bpPrefixRangeArgMinPrefixPosEntries_length,
    endpointLocalFringeRanges_length]

def concreteEndpointFringeMinTable
    (shape : Cartesian.CartesianShape)
    (blockSize fieldWidth : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth)
    (code : Nat) :
    FixedWidthNatTable
      (concreteEndpointFringeMinEntries shape blockSize code)
      fieldWidth :=
  FixedWidthNatTable.ofEntries
    (concreteEndpointFringeMinEntries shape blockSize code)
    fieldWidth
    (by
      intro entry hmem
      exact bpPrefixRangeMinExcessEntries_mem_bound hwidth hmem)

def concreteEndpointFringeArgTable
    (shape : Cartesian.CartesianShape)
    (blockSize fieldWidth : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth)
    (code : Nat) :
    FixedWidthNatTable
      (concreteEndpointFringeArgEntries shape blockSize code)
      fieldWidth :=
  FixedWidthNatTable.ofEntries
    (concreteEndpointFringeArgEntries shape blockSize code)
    fieldWidth
    (by
      intro entry hmem
      exact bpPrefixRangeArgMinPrefixPosEntries_mem_bound hwidth hmem)

theorem concreteEndpointFringeMinTable_payload_length
    (shape : Cartesian.CartesianShape)
    (blockSize fieldWidth : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth)
    (code : Nat) :
    (concreteEndpointFringeMinTable
      shape blockSize fieldWidth hwidth code).payload.length =
      (2 * blockSize) * fieldWidth := by
  simpa [concreteEndpointFringeMinTable,
    concreteEndpointFringeMinEntries_length] using
    (FixedWidthNatTable.ofEntries
      (concreteEndpointFringeMinEntries shape blockSize code)
      fieldWidth
      (by
        intro entry hmem
        exact bpPrefixRangeMinExcessEntries_mem_bound hwidth hmem)).payload_length

theorem concreteEndpointFringeArgTable_payload_length
    (shape : Cartesian.CartesianShape)
    (blockSize fieldWidth : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth)
    (code : Nat) :
    (concreteEndpointFringeArgTable
      shape blockSize fieldWidth hwidth code).payload.length =
      (2 * blockSize) * fieldWidth := by
  simpa [concreteEndpointFringeArgTable,
    concreteEndpointFringeArgEntries_length] using
    (FixedWidthNatTable.ofEntries
      (concreteEndpointFringeArgEntries shape blockSize code)
      fieldWidth
      (by
        intro entry hmem
        exact bpPrefixRangeArgMinPrefixPosEntries_mem_bound hwidth hmem)).payload_length

def concretePayloadLiveBlockEndpointFringeCodebookTableOverhead
    (blockSize fieldWidth : Nat) : Nat :=
  2 * ((2 * blockSize) * fieldWidth)

def concretePayloadLiveBlockEndpointFringeCodebookPayloadLength
    (blockCount blockSize fieldWidth : Nat) : Nat :=
  blockCount * fieldWidth +
    blockCount *
      concretePayloadLiveBlockEndpointFringeCodebookTableOverhead
        blockSize fieldWidth

private theorem concreteEndpointFringeTablePayload_length
    (shape : Cartesian.CartesianShape)
    (blockSize codeCount fieldWidth : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth) :
    ((List.range codeCount).flatMap fun code =>
        (concreteEndpointFringeMinTable
          shape blockSize fieldWidth hwidth code).payload ++
        (concreteEndpointFringeArgTable
          shape blockSize fieldWidth hwidth code).payload).length =
      codeCount *
        concretePayloadLiveBlockEndpointFringeCodebookTableOverhead
          blockSize fieldWidth := by
  induction codeCount with
  | zero =>
      simp [concretePayloadLiveBlockEndpointFringeCodebookTableOverhead]
  | succ codeCount ih =>
      have hrow :
          (blockSize + blockSize) * fieldWidth +
              (blockSize + blockSize) * fieldWidth =
            concretePayloadLiveBlockEndpointFringeCodebookTableOverhead
              blockSize fieldWidth := by
        have htwo : blockSize + blockSize = 2 * blockSize := by
          omega
        rw [htwo]
        unfold concretePayloadLiveBlockEndpointFringeCodebookTableOverhead
        omega
      simp [List.range_succ, ih,
        concreteEndpointFringeMinTable_payload_length,
        concreteEndpointFringeArgTable_payload_length,
        hrow, Nat.succ_mul]

def concretePayloadLiveBlockEndpointFringeCodebook
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount fieldWidth : Nat)
    (hblockCountWidth : blockCount <= shape.bpCode.length)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth) :
    PayloadLiveBlockEndpointFringeCodebook shape blockSize blockCount
      blockCount fieldWidth (blockCount * fieldWidth) fieldWidth
      (concretePayloadLiveBlockEndpointFringeCodebookTableOverhead
        blockSize fieldWidth) where
  classifier :=
    BlockCodeTable.ofEntries blockCount blockCount fieldWidth
      (blockCount * fieldWidth) (List.range blockCount)
      (by
        intro code hmem
        exact Nat.lt_trans
          (Nat.lt_of_lt_of_le (List.mem_range.mp hmem)
            hblockCountWidth)
          hwidth)
      (by simp)
      (by simp)
      (by
        intro block code hget
        by_cases hblock : block < blockCount
        · simp [List.getElem?_range hblock] at hget
          cases hget
          exact hblock
        · simp [hblock] at hget)
  minEntriesByCode :=
    fun code => concreteEndpointFringeMinEntries shape blockSize code
  argEntriesByCode :=
    fun code => concreteEndpointFringeArgEntries shape blockSize code
  minTable :=
    fun code => concreteEndpointFringeMinTable
      shape blockSize fieldWidth hwidth code
  argTable :=
    fun code => concreteEndpointFringeArgTable
      shape blockSize fieldWidth hwidth code
  tablePayload :=
    (List.range blockCount).flatMap fun code =>
      (concreteEndpointFringeMinTable
        shape blockSize fieldWidth hwidth code).payload ++
      (concreteEndpointFringeArgTable
        shape blockSize fieldWidth hwidth code).payload
  tablePayload_eq_tables := rfl
  tablePayload_length_eq := by
    exact concreteEndpointFringeTablePayload_length
      shape blockSize blockCount fieldWidth hwidth
  table_payload_length_eq := by
    intro code _hcode
    simp [concreteEndpointFringeMinTable_payload_length,
      concreteEndpointFringeArgTable_payload_length,
      concretePayloadLiveBlockEndpointFringeCodebookTableOverhead]
    omega
  block_fringe_entries := by
    intro block code hcodeAt
    have hget : (List.range blockCount)[block]? = some code := by
      simpa [BlockCodeTable.codeAt, BlockCodeTable.ofEntries] using hcodeAt
    by_cases hblock : block < blockCount
    · simp [List.getElem?_range hblock] at hget
      cases hget
      simp [concreteEndpointFringeMinEntries,
        concreteEndpointFringeArgEntries]
    · simp [hblock] at hget

theorem concretePayloadLiveBlockEndpointFringeCodebook_profile
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount fieldWidth : Nat)
    (hblockCountWidth : blockCount <= shape.bpCode.length)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth)
    (hmachine :
      fieldWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length) :
    let fringe :=
      concretePayloadLiveBlockEndpointFringeCodebook
        shape blockSize blockCount fieldWidth hblockCountWidth hwidth
    fringe.payload.length =
        concretePayloadLiveBlockEndpointFringeCodebookPayloadLength
          blockCount blockSize fieldWidth /\
      (forall close,
        (fringe.leftFringeCosted close).cost <= 3 /\
          (fringe.rightFringeCosted close).cost <= 3) /\
      (forall {close : Nat},
        0 < blockSize ->
          blockOfClose blockSize close < blockCount ->
            (fringe.leftFringeCosted close).erase =
              some
                (bpPrefixRangeMinExcess shape (close + 1)
                  (blockStartOf blockSize
                      (blockOfClose blockSize close) +
                    blockSize - close),
                  bpPrefixRangeArgMinPrefixPos shape (close + 1)
                    (blockStartOf blockSize
                        (blockOfClose blockSize close) +
                      blockSize - close))) /\
      (forall {close : Nat},
        0 < blockSize ->
          blockOfClose blockSize close < blockCount ->
            (fringe.rightFringeCosted close).erase =
              some
                (bpPrefixRangeMinExcess shape
                  (blockStartOf blockSize
                    (blockOfClose blockSize close))
                  (close -
                      blockStartOf blockSize
                        (blockOfClose blockSize close) +
                    2),
                  bpPrefixRangeArgMinPrefixPos shape
                    (blockStartOf blockSize
                      (blockOfClose blockSize close))
                    (close -
                        blockStartOf blockSize
                          (blockOfClose blockSize close) +
                      2))) /\
      forall {slot block : Nat} {word : List Bool},
        word ∈ fringe.wordsReadAtBlock slot block ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  let fringe :=
    concretePayloadLiveBlockEndpointFringeCodebook
      shape blockSize blockCount fieldWidth hblockCountWidth hwidth
  have hprofile := fringe.profile
  constructor
  · simpa [concretePayloadLiveBlockEndpointFringeCodebookPayloadLength]
      using hprofile.1
  constructor
  · exact hprofile.2.1
  constructor
  · exact hprofile.2.2.1
  constructor
  · exact hprofile.2.2.2
  · intro slot block word hmem
    exact fringe.read_words_length_le_machine hmachine hmachine hmem

def concretePayloadLiveBlockEndpointFringeCodebook_canonical
    (shape : Cartesian.CartesianShape) :
    PayloadLiveBlockEndpointFringeCodebook shape
      (canonicalBPRelativeSummaryBlockSize shape)
      (canonicalBPRelativeSummaryBlockCount shape)
      (canonicalBPRelativeSummaryBlockCount shape)
      (SuccinctRankProposal.machineWordBits shape.bpCode.length)
      (canonicalBPRelativeSummaryBlockCount shape *
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
      (SuccinctRankProposal.machineWordBits shape.bpCode.length)
      (concretePayloadLiveBlockEndpointFringeCodebookTableOverhead
        (canonicalBPRelativeSummaryBlockSize shape)
        (SuccinctRankProposal.machineWordBits shape.bpCode.length)) :=
  concretePayloadLiveBlockEndpointFringeCodebook
    shape
    (canonicalBPRelativeSummaryBlockSize shape)
    (canonicalBPRelativeSummaryBlockCount shape)
    (SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (canonicalBPRelativeSummaryBlockCount_le_bpCode_length shape)
    (by
      simpa [canonicalBPRelativeSummarySuperWidth] using
        canonicalBPRelativeSummary_superWidth_bound shape)

theorem concretePayloadLiveBlockEndpointFringeCodebook_canonical_profile
    (shape : Cartesian.CartesianShape) :
    let fringe :=
      concretePayloadLiveBlockEndpointFringeCodebook_canonical shape
    fringe.payload.length =
        concretePayloadLiveBlockEndpointFringeCodebookPayloadLength
          (canonicalBPRelativeSummaryBlockCount shape)
          (canonicalBPRelativeSummaryBlockSize shape)
          (SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
      (forall close,
        (fringe.leftFringeCosted close).cost <= 3 /\
          (fringe.rightFringeCosted close).cost <= 3) /\
      (forall {close : Nat},
        0 < canonicalBPRelativeSummaryBlockSize shape ->
          blockOfClose (canonicalBPRelativeSummaryBlockSize shape) close <
              canonicalBPRelativeSummaryBlockCount shape ->
            (fringe.leftFringeCosted close).erase =
              some
                (bpPrefixRangeMinExcess shape (close + 1)
                  (blockStartOf
                      (canonicalBPRelativeSummaryBlockSize shape)
                      (blockOfClose
                        (canonicalBPRelativeSummaryBlockSize shape)
                        close) +
                    canonicalBPRelativeSummaryBlockSize shape - close),
                  bpPrefixRangeArgMinPrefixPos shape (close + 1)
                    (blockStartOf
                        (canonicalBPRelativeSummaryBlockSize shape)
                        (blockOfClose
                          (canonicalBPRelativeSummaryBlockSize shape)
                          close) +
                      canonicalBPRelativeSummaryBlockSize shape - close))) /\
      (forall {close : Nat},
        0 < canonicalBPRelativeSummaryBlockSize shape ->
          blockOfClose (canonicalBPRelativeSummaryBlockSize shape) close <
              canonicalBPRelativeSummaryBlockCount shape ->
            (fringe.rightFringeCosted close).erase =
              some
                (bpPrefixRangeMinExcess shape
                  (blockStartOf
                    (canonicalBPRelativeSummaryBlockSize shape)
                    (blockOfClose
                      (canonicalBPRelativeSummaryBlockSize shape)
                      close))
                  (close -
                      blockStartOf
                        (canonicalBPRelativeSummaryBlockSize shape)
                        (blockOfClose
                          (canonicalBPRelativeSummaryBlockSize shape)
                          close) +
                    2),
                  bpPrefixRangeArgMinPrefixPos shape
                    (blockStartOf
                      (canonicalBPRelativeSummaryBlockSize shape)
                      (blockOfClose
                        (canonicalBPRelativeSummaryBlockSize shape)
                        close))
                    (close -
                        blockStartOf
                          (canonicalBPRelativeSummaryBlockSize shape)
                          (blockOfClose
                            (canonicalBPRelativeSummaryBlockSize shape)
                            close) +
                      2))) /\
      forall {slot block : Nat} {word : List Bool},
        word ∈ fringe.wordsReadAtBlock slot block ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  simpa [concretePayloadLiveBlockEndpointFringeCodebook_canonical] using
    concretePayloadLiveBlockEndpointFringeCodebook_profile
      shape
      (canonicalBPRelativeSummaryBlockSize shape)
      (canonicalBPRelativeSummaryBlockCount shape)
      (SuccinctRankProposal.machineWordBits shape.bpCode.length)
      (canonicalBPRelativeSummaryBlockCount_le_bpCode_length shape)
      (by
        simpa [canonicalBPRelativeSummarySuperWidth] using
          canonicalBPRelativeSummary_superWidth_bound shape)
      (Nat.le_refl _)

/--
Relative-rmM cross-block macro with compact endpoint-fringe repair.

Endpoint candidates are read through the local endpoint-fringe codebook above:
one charged block-code read plus two charged local witness reads.  The middle
candidate remains the compact relative-rmM interior directory.
-/
structure PayloadLiveCompactEndpointRelativeRmmBPCloseMacro
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount codeCount codeWidth codeOverhead fieldWidth
      fringeTableOverhead interiorOverhead middleQueryCost : Nat) where
  endpointFringe :
    PayloadLiveBlockEndpointFringeCodebook shape blockSize blockCount
      codeCount codeWidth codeOverhead fieldWidth fringeTableOverhead
  interior :
    PayloadLiveBPRelativeRmmInteriorDirectory shape blockSize blockCount
      interiorOverhead middleQueryCost
  blockSize_pos : 0 < blockSize

namespace PayloadLiveCompactEndpointRelativeRmmBPCloseMacro

def payload
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead fieldWidth
      fringeTableOverhead interiorOverhead middleQueryCost : Nat}
    (component :
      PayloadLiveCompactEndpointRelativeRmmBPCloseMacro shape blockSize
        blockCount codeCount codeWidth codeOverhead fieldWidth
        fringeTableOverhead interiorOverhead middleQueryCost) :
    List Bool :=
  component.endpointFringe.payload ++ component.interior.payload

def payloadWordsRead
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead fieldWidth
      fringeTableOverhead interiorOverhead middleQueryCost : Nat}
    (component :
      PayloadLiveCompactEndpointRelativeRmmBPCloseMacro shape blockSize
        blockCount codeCount codeWidth codeOverhead fieldWidth
        fringeTableOverhead interiorOverhead middleQueryCost)
    (leftClose rightClose : Nat) : List (List Bool) :=
  let leftBlock := blockOfClose blockSize leftClose
  let rightBlock := blockOfClose blockSize rightClose
  let startBlock := leftBlock + 1
  let count := rightBlock - leftBlock - 1
  component.endpointFringe.leftWordsReadAtBlock leftBlock leftClose ++
    (if leftBlock + 1 < rightBlock then
      component.interior.payloadWordsRead startBlock count
    else
      []) ++
      component.endpointFringe.rightWordsReadAtBlock rightBlock rightClose

def interiorCandidateCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead fieldWidth
      fringeTableOverhead interiorOverhead middleQueryCost : Nat}
    (component :
      PayloadLiveCompactEndpointRelativeRmmBPCloseMacro shape blockSize
        blockCount codeCount codeWidth codeOverhead fieldWidth
        fringeTableOverhead interiorOverhead middleQueryCost)
    (leftClose rightClose : Nat) : Costed (Option (Nat × Nat)) :=
  if blockOfClose blockSize leftClose + 1 <
      blockOfClose blockSize rightClose then
    component.interior.rangeMinCosted
      (blockOfClose blockSize leftClose + 1)
      (blockOfClose blockSize rightClose -
        blockOfClose blockSize leftClose - 1)
  else
    Costed.pure none

def lcaCloseCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead fieldWidth
      fringeTableOverhead interiorOverhead middleQueryCost : Nat}
    (component :
      PayloadLiveCompactEndpointRelativeRmmBPCloseMacro shape blockSize
        blockCount codeCount codeWidth codeOverhead fieldWidth
        fringeTableOverhead interiorOverhead middleQueryCost)
    (leftClose rightClose : Nat) : Costed (Option Nat) :=
  Costed.bind (component.endpointFringe.leftFringeCosted leftClose)
    fun left? =>
      Costed.bind (component.interiorCandidateCosted leftClose rightClose)
        fun middle? =>
          Costed.map
            (fun right? =>
              bpCandidateClose? (bpCandidateMerge3? left? middle? right?))
            (component.endpointFringe.rightFringeCosted rightClose)

theorem payload_length
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead fieldWidth
      fringeTableOverhead interiorOverhead middleQueryCost : Nat}
    (component :
      PayloadLiveCompactEndpointRelativeRmmBPCloseMacro shape blockSize
        blockCount codeCount codeWidth codeOverhead fieldWidth
        fringeTableOverhead interiorOverhead middleQueryCost) :
    component.payload.length =
      codeOverhead + codeCount * fringeTableOverhead +
        interiorOverhead := by
  simp [payload, component.endpointFringe.payload_length,
    component.interior.payload_length_eq]

theorem interiorCandidateCosted_cost_le
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead fieldWidth
      fringeTableOverhead interiorOverhead middleQueryCost : Nat}
    (component :
      PayloadLiveCompactEndpointRelativeRmmBPCloseMacro shape blockSize
        blockCount codeCount codeWidth codeOverhead fieldWidth
        fringeTableOverhead interiorOverhead middleQueryCost)
    (leftClose rightClose : Nat) :
    (component.interiorCandidateCosted leftClose rightClose).cost <=
      middleQueryCost := by
  unfold interiorCandidateCosted
  by_cases hgap :
      blockOfClose blockSize leftClose + 1 <
        blockOfClose blockSize rightClose
  · simp [hgap]
    exact component.interior.rangeMin_cost_le
      (blockOfClose blockSize leftClose + 1)
      (blockOfClose blockSize rightClose -
        blockOfClose blockSize leftClose - 1)
  · simp [hgap, Costed.pure]

theorem lcaCloseCosted_cost_le
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead fieldWidth
      fringeTableOverhead interiorOverhead middleQueryCost : Nat}
    (component :
      PayloadLiveCompactEndpointRelativeRmmBPCloseMacro shape blockSize
        blockCount codeCount codeWidth codeOverhead fieldWidth
        fringeTableOverhead interiorOverhead middleQueryCost)
    (leftClose rightClose : Nat) :
    (component.lcaCloseCosted leftClose rightClose).cost <=
      6 + middleQueryCost := by
  unfold lcaCloseCosted
  have hleft :=
    component.endpointFringe.leftFringeCosted_cost_le_three leftClose
  have hmiddle :=
    component.interiorCandidateCosted_cost_le leftClose rightClose
  have hright :=
    component.endpointFringe.rightFringeCosted_cost_le_three rightClose
  simp [Costed.bind, Costed.map]
  omega

theorem lcaCloseCosted_erase_decoded
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead fieldWidth
      fringeTableOverhead interiorOverhead middleQueryCost
      leftClose rightClose : Nat}
    (component :
      PayloadLiveCompactEndpointRelativeRmmBPCloseMacro shape blockSize
        blockCount codeCount codeWidth codeOverhead fieldWidth
        fringeTableOverhead interiorOverhead middleQueryCost)
    (hleftBlock : blockOfClose blockSize leftClose < blockCount)
    (hrightBlock : blockOfClose blockSize rightClose < blockCount) :
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
      (component.endpointFringe.leftFringeCosted leftClose).value =
        some
          (bpPrefixRangeMinExcess shape (leftClose + 1)
            (blockStartOf blockSize
                (blockOfClose blockSize leftClose) +
              blockSize - leftClose),
            bpPrefixRangeArgMinPrefixPos shape (leftClose + 1)
              (blockStartOf blockSize
                  (blockOfClose blockSize leftClose) +
                blockSize - leftClose)) := by
    simpa [Costed.erase] using
      component.endpointFringe.leftFringeCosted_exact
        component.blockSize_pos hleftBlock
  have hright :
      (component.endpointFringe.rightFringeCosted rightClose).value =
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
    simpa [Costed.erase] using
      component.endpointFringe.rightFringeCosted_exact
        component.blockSize_pos hrightBlock
  unfold lcaCloseCosted interiorCandidateCosted
  by_cases hgap :
      blockOfClose blockSize leftClose + 1 <
        blockOfClose blockSize rightClose
  · have hmiddle :
        (component.interior.rangeMinCosted
            (blockOfClose blockSize leftClose + 1)
            (blockOfClose blockSize rightClose -
              blockOfClose blockSize leftClose - 1)).value =
          some
            (bpRangeMinExcess shape blockSize
              (blockOfClose blockSize leftClose + 1)
              (blockOfClose blockSize rightClose -
                blockOfClose blockSize leftClose - 1),
              bpRangeArgMinPrefixPos shape blockSize
                (blockOfClose blockSize leftClose + 1)
                (blockOfClose blockSize rightClose -
                  blockOfClose blockSize leftClose - 1)) := by
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
      simpa [Costed.erase] using
        component.interior.rangeMin_exact hcount hbound
    simp [Costed.bind, Costed.map, Costed.erase, hleft, hright,
      hmiddle, hgap]
  · simp [Costed.bind, Costed.map, Costed.erase, Costed.pure,
      hleft, hright, hgap]

theorem lcaCloseCosted_exact_of_query_cross_block
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead fieldWidth
      fringeTableOverhead interiorOverhead middleQueryCost : Nat}
    (component :
      PayloadLiveCompactEndpointRelativeRmmBPCloseMacro shape blockSize
        blockCount codeCount codeWidth codeOverhead fieldWidth
        fringeTableOverhead interiorOverhead middleQueryCost)
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
    (hleftBlock : blockOfClose blockSize leftClose < blockCount)
    (hrightBlock : blockOfClose blockSize rightClose < blockCount)
    (hcross :
      blockOfClose blockSize leftClose <
        blockOfClose blockSize rightClose) :
    (component.lcaCloseCosted leftClose rightClose).erase =
      some answerClose := by
  rw [component.lcaCloseCosted_erase_decoded hleftBlock hrightBlock]
  have hsemantic :=
    answerClose_prefix_leftmost_min_excess_of_query
      (shape := shape) (start := left) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      (answerClose := answerClose)
      hlen hbound hleft hright hanswer
  have hmerge :=
    bpRelativeRmmCandidateMerge_exact_of_query_semantics
      (hlen := hlen) hleft hright hanswer component.blockSize_pos
      hleftBlock hrightBlock hcross hsemantic.1 hsemantic.2
  simp [hmerge, bpCandidateClose?]

theorem read_words_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead fieldWidth
      fringeTableOverhead interiorOverhead middleQueryCost : Nat}
    (component :
      PayloadLiveCompactEndpointRelativeRmmBPCloseMacro shape blockSize
        blockCount codeCount codeWidth codeOverhead fieldWidth
        fringeTableOverhead interiorOverhead middleQueryCost)
    (hcodeMachine :
      codeWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hfieldMachine :
      fieldWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length) :
    forall {leftClose rightClose : Nat} {word : List Bool},
      word ∈ component.payloadWordsRead leftClose rightClose ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  intro leftClose rightClose word hmem
  have hleft :
      forall {word : List Bool},
        word ∈
            component.endpointFringe.leftWordsReadAtBlock
              (blockOfClose blockSize leftClose) leftClose ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length := by
    intro word hword
    exact
      component.endpointFringe.leftWordsReadAtBlock_length_le_machine
        hcodeMachine hfieldMachine hword
  have hright :
      forall {word : List Bool},
        word ∈
            component.endpointFringe.rightWordsReadAtBlock
              (blockOfClose blockSize rightClose) rightClose ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length := by
    intro word hword
    exact
      component.endpointFringe.rightWordsReadAtBlock_length_le_machine
        hcodeMachine hfieldMachine hword
  have hmid :
      forall {startBlock count : Nat} {word : List Bool},
        word ∈ component.interior.payloadWordsRead startBlock count ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length :=
    component.interior.read_words_length_le_machine
  unfold payloadWordsRead at hmem
  simp only [List.mem_append] at hmem
  rcases hmem with hmem | hrightMem
  · rcases hmem with hleftMem | hmiddleMem
    · exact hleft hleftMem
    · by_cases hgap :
        blockOfClose blockSize leftClose + 1 <
          blockOfClose blockSize rightClose
      · simp [hgap] at hmiddleMem
        exact hmid hmiddleMem
      · simp [hgap] at hmiddleMem
  · exact hright hrightMem

theorem profile
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead fieldWidth
      fringeTableOverhead interiorOverhead middleQueryCost : Nat}
    (component :
      PayloadLiveCompactEndpointRelativeRmmBPCloseMacro shape blockSize
        blockCount codeCount codeWidth codeOverhead fieldWidth
        fringeTableOverhead interiorOverhead middleQueryCost) :
    component.payload.length =
        codeOverhead + codeCount * fringeTableOverhead +
          interiorOverhead /\
      (forall leftClose rightClose,
        (component.lcaCloseCosted leftClose rightClose).cost <=
          6 + middleQueryCost) /\
      forall {left len leftClose rightClose answerClose : Nat},
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
                          some answerClose := by
  constructor
  · exact component.payload_length
  constructor
  · intro leftClose rightClose
    exact component.lcaCloseCosted_cost_le leftClose rightClose
  · intro left len leftClose rightClose answerClose hlen hbound hleft
      hright hanswer hleftBlock hrightBlock hcross
    exact component.lcaCloseCosted_exact_of_query_cross_block
      hlen hbound hleft hright hanswer hleftBlock hrightBlock hcross

end PayloadLiveCompactEndpointRelativeRmmBPCloseMacro

def concretePayloadLiveCompactEndpointRelativeRmmBPCloseMacroPayloadLength
    (shape : Cartesian.CartesianShape) : Nat :=
  concretePayloadLiveBlockEndpointFringeCodebookPayloadLength
      (canonicalBPRelativeSummaryBlockCount shape)
      (canonicalBPRelativeSummaryBlockSize shape)
      (SuccinctRankProposal.machineWordBits shape.bpCode.length) +
    concreteBPRelativeRmmInteriorDirectoryPayloadLength shape

def concretePayloadLiveCompactEndpointRelativeRmmBPCloseMacroOverhead
    (shape : Cartesian.CartesianShape) : Nat :=
  concretePayloadLiveBlockEndpointFringeCodebookPayloadLength
      (canonicalBPRelativeSummaryBlockCount shape)
      (canonicalBPRelativeSummaryBlockSize shape)
      (SuccinctRankProposal.machineWordBits shape.bpCode.length) +
    concreteBPRelativeRmmInteriorOverhead shape.size

def concretePayloadLiveCompactEndpointRelativeRmmBPCloseMacro
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size) :
    PayloadLiveCompactEndpointRelativeRmmBPCloseMacro shape
      (canonicalBPRelativeSummaryBlockSize shape)
      (canonicalBPRelativeSummaryBlockCount shape)
      (canonicalBPRelativeSummaryBlockCount shape)
      (SuccinctRankProposal.machineWordBits shape.bpCode.length)
      (canonicalBPRelativeSummaryBlockCount shape *
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
      (SuccinctRankProposal.machineWordBits shape.bpCode.length)
      (concretePayloadLiveBlockEndpointFringeCodebookTableOverhead
        (canonicalBPRelativeSummaryBlockSize shape)
        (SuccinctRankProposal.machineWordBits shape.bpCode.length))
      (concreteBPRelativeRmmInteriorDirectoryPayloadLength shape)
      concreteBPRelativeRmmInteriorQueryCost := by
  let endpointFringe :=
    concretePayloadLiveBlockEndpointFringeCodebook_canonical shape
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
    { endpointFringe := endpointFringe
      interior := interior
      blockSize_pos := hblockSize }

theorem concretePayloadLiveCompactEndpointRelativeRmmBPCloseMacro_profile
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size) :
    let component :=
      concretePayloadLiveCompactEndpointRelativeRmmBPCloseMacro shape hsize
    component.payload.length =
        concretePayloadLiveCompactEndpointRelativeRmmBPCloseMacroPayloadLength
          shape /\
      component.payload.length <=
        concretePayloadLiveCompactEndpointRelativeRmmBPCloseMacroOverhead
          shape /\
      (forall leftClose rightClose,
        (component.lcaCloseCosted leftClose rightClose).cost <=
          6 + concreteBPRelativeRmmInteriorQueryCost) /\
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
  let component :=
    concretePayloadLiveCompactEndpointRelativeRmmBPCloseMacro shape hsize
  have hcomponentLen := component.payload_length
  have hinteriorProfile :=
    concreteBPRelativeRmmInteriorDirectory_profile shape hsize
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
  · rw [hcomponentLen]
    unfold concretePayloadLiveCompactEndpointRelativeRmmBPCloseMacroPayloadLength
      concretePayloadLiveBlockEndpointFringeCodebookPayloadLength
    omega
  constructor
  · rw [hcomponentLen]
    unfold concretePayloadLiveCompactEndpointRelativeRmmBPCloseMacroOverhead
      concretePayloadLiveBlockEndpointFringeCodebookPayloadLength
    omega
  constructor
  · intro leftClose rightClose
    exact component.lcaCloseCosted_cost_le leftClose rightClose
  constructor
  · intro left len leftClose rightClose answerClose hlen hbound hleft
      hright hanswer hleftBlock hrightBlock hcross
    exact component.lcaCloseCosted_exact_of_query_cross_block
      hlen hbound hleft hright hanswer hleftBlock hrightBlock hcross
  · intro leftClose rightClose word hmem
    exact component.read_words_length_le_machine
      (Nat.le_refl _) (Nat.le_refl _) hmem

/-- Auxiliary overhead reserved for the compact BP close/LCA directory.

The local endpoint and same-block work below is charged as bounded BP-word
primitive work over the base BP payload, so the auxiliary close overhead is the
compact two-level interior navigator payload.
-/
def compactBPCloseOverhead (n : Nat) : Nat :=
  if n < 2 ^ 128 then
    natListMax
      ((Cartesian.shapesOfSize n).map fun shape =>
        concreteBPRelativeRmmInteriorDirectoryPayloadLength shape)
  else
    concreteBPRelativeRmmInteriorOverhead n

theorem compactBPCloseOverhead_littleO :
    LittleOLinear compactBPCloseOverhead := by
  exact
    LittleOLinear.of_eventually_le
      concreteBPRelativeRmmInteriorOverhead_littleO
      ⟨2 ^ 128, by
        intro n hn
        have hnot : ¬ n < 2 ^ 128 := by omega
        simp [compactBPCloseOverhead, hnot]⟩

def concreteCompactBPCloseQueryCost : Nat :=
  10 + concreteBPRelativeRmmInteriorQueryCost

def concreteCompactBPCloseQueryCostWithRankSeed
    (rankCost : Nat) : Nat :=
  8 + 2 * rankCost + concreteBPRelativeRmmInteriorQueryCost

def bpCodeWordReadsAt
    (shape : Cartesian.CartesianShape) (index : Nat) : List (List Bool) :=
  payloadWordReadOfGet?
    (SuccinctSpace.chunkPayloadWords
      (SuccinctRankProposal.machineWordBits shape.bpCode.length)
      shape.bpCode).toArray
    index

theorem bpCodeWordReadsAt_length_le_machine
    (shape : Cartesian.CartesianShape) (index : Nat)
    {word : List Bool}
    (hmem : word ∈ bpCodeWordReadsAt shape index) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  unfold bpCodeWordReadsAt at hmem
  exact payloadWordReadOfGet?_length_le
    (by
      intro stored hget
      have hmemWords :
          stored ∈
            SuccinctSpace.chunkPayloadWords
              (SuccinctRankProposal.machineWordBits shape.bpCode.length)
              shape.bpCode := by
        have hlist :
            (SuccinctSpace.chunkPayloadWords
              (SuccinctRankProposal.machineWordBits shape.bpCode.length)
              shape.bpCode)[index]? = some stored := by
          simpa [Array.getElem?_toList] using hget
        exact List.mem_of_getElem? hlist
      exact SuccinctSpace.chunkPayloadWords_word_length_le
        (SuccinctRankProposal.machineWordBits shape.bpCode.length)
        hmemWords)
    hmem

theorem list_take_add_eq_take_append_drop_take
    {α : Type} (xs : List α) (a b : Nat) :
    xs.take (a + b) = xs.take a ++ (xs.drop a).take b := by
  induction a generalizing xs with
  | zero =>
      simp
  | succ a ih =>
      cases xs with
      | nil =>
          simp
      | cons x xs =>
          simp [Nat.succ_add, ih]

theorem flatten_bpCodeWordReadsAt_eq_take_drop
    (shape : Cartesian.CartesianShape) (index : Nat) :
    SuccinctSpace.flattenPayloadWords (bpCodeWordReadsAt shape index) =
      (shape.bpCode.drop
        (index * SuccinctRankProposal.machineWordBits shape.bpCode.length)).take
          (SuccinctRankProposal.machineWordBits shape.bpCode.length) := by
  let wordSize := SuccinctRankProposal.machineWordBits shape.bpCode.length
  let words := SuccinctSpace.chunkPayloadWords wordSize shape.bpCode
  have hword : 0 < wordSize := by
    simpa [wordSize] using
      SuccinctRankProposal.machineWordBits_pos shape.bpCode.length
  unfold bpCodeWordReadsAt payloadWordReadOfGet?
  cases hget : words.toArray[index]? with
  | some word =>
      have hlist : words[index]? = some word := by
        simpa [words, Array.getElem?_toList] using hget
      have hwordEq :=
        SuccinctSpace.chunkPayloadWords_get?_eq_take_drop hlist
      simp [SuccinctSpace.flattenPayloadWords, wordSize, hwordEq]
  | none =>
      by_cases hlt : index * wordSize < shape.bpCode.length
      · rcases
          SuccinctSpace.chunkPayloadWords_get?_some_of_mul_lt
            (wordSize := wordSize) hword
            (payload := shape.bpCode) (i := index) hlt with
          ⟨word, hlist⟩
        have harray : words.toArray[index]? = some word := by
          simpa [words, Array.getElem?_toList] using hlist
        rw [hget] at harray
        cases harray
      · have hdropLen :
            (shape.bpCode.drop (index * wordSize)).length = 0 := by
          rw [List.length_drop]
          omega
        cases hdrop : shape.bpCode.drop (index * wordSize) with
        | nil =>
            simp [SuccinctSpace.flattenPayloadWords]
        | cons bit rest =>
            simp [hdrop] at hdropLen

/--
The fixed local BP-word budget used by same-block and endpoint-fringe
primitives.  Canonical blocks have logarithmic width, so four consecutive
machine chunks are a conservative constant-width local window for the current
model surface; exactness is stated by the local primitive theorems below.
-/
def localBPBlockWordsRead
    (shape : Cartesian.CartesianShape)
    (blockSize close : Nat) : List (List Bool) :=
  let wordSize := SuccinctRankProposal.machineWordBits shape.bpCode.length
  let firstWord :=
    blockStartOf blockSize (blockOfClose blockSize close) / wordSize
  bpCodeWordReadsAt shape firstWord ++
    bpCodeWordReadsAt shape (firstWord + 1) ++
      bpCodeWordReadsAt shape (firstWord + 2) ++
        bpCodeWordReadsAt shape (firstWord + 3)

/-- First global BP bit position covered by the local four-word window. -/
def localBPWindowBase
    (shape : Cartesian.CartesianShape)
    (blockSize close : Nat) : Nat :=
  let wordSize := SuccinctRankProposal.machineWordBits shape.bpCode.length
  let firstWord :=
    blockStartOf blockSize (blockOfClose blockSize close) / wordSize
  firstWord * wordSize

/--
Contiguous bit view of the local BP window.

The query still charges the four payload words listed by `localBPBlockWordsRead`;
this proof-facing view exposes the covered slice so the seeded decoder can be
stated without calling the semantic local helpers.
-/
def localBPWindowBits
    (shape : Cartesian.CartesianShape)
    (blockSize close : Nat) : List Bool :=
  let wordSize := SuccinctRankProposal.machineWordBits shape.bpCode.length
  let base := localBPWindowBase shape blockSize close
  (shape.bpCode.drop base).take (4 * wordSize)

/-- The proof-facing local BP window is exactly the flattened charged words. -/
theorem localBPWindowBits_eq_flatten_localBPBlockWordsRead
    (shape : Cartesian.CartesianShape)
    (blockSize close : Nat) :
    localBPWindowBits shape blockSize close =
      SuccinctSpace.flattenPayloadWords
        (localBPBlockWordsRead shape blockSize close) := by
  let wordSize := SuccinctRankProposal.machineWordBits shape.bpCode.length
  let firstWord :=
    blockStartOf blockSize (blockOfClose blockSize close) / wordSize
  have h0 := flatten_bpCodeWordReadsAt_eq_take_drop shape firstWord
  have h1 := flatten_bpCodeWordReadsAt_eq_take_drop shape (firstWord + 1)
  have h2 := flatten_bpCodeWordReadsAt_eq_take_drop shape (firstWord + 2)
  have h3 := flatten_bpCodeWordReadsAt_eq_take_drop shape (firstWord + 3)
  have hsplit1 :
      (shape.bpCode.drop (firstWord * wordSize)).take (4 * wordSize) =
        (shape.bpCode.drop (firstWord * wordSize)).take wordSize ++
          (shape.bpCode.drop ((firstWord + 1) * wordSize)).take
            (3 * wordSize) := by
    have hfour : 4 * wordSize = wordSize + 3 * wordSize := by omega
    rw [hfour]
    rw [list_take_add_eq_take_append_drop_take]
    simp only [List.drop_drop]
    rw [show firstWord * wordSize + wordSize =
      (firstWord + 1) * wordSize by
        rw [Nat.add_mul]
        simp]
  have hsplit2 :
      (shape.bpCode.drop ((firstWord + 1) * wordSize)).take
          (3 * wordSize) =
        (shape.bpCode.drop ((firstWord + 1) * wordSize)).take wordSize ++
          (shape.bpCode.drop ((firstWord + 2) * wordSize)).take
            (2 * wordSize) := by
    have hthree : 3 * wordSize = wordSize + 2 * wordSize := by omega
    rw [hthree]
    rw [list_take_add_eq_take_append_drop_take]
    simp only [List.drop_drop]
    rw [show (firstWord + 1) * wordSize + wordSize =
      (firstWord + 2) * wordSize by
        rw [show firstWord + 2 = (firstWord + 1) + 1 by omega]
        simp [Nat.add_mul, Nat.add_comm]]
  have hsplit3 :
      (shape.bpCode.drop ((firstWord + 2) * wordSize)).take
          (2 * wordSize) =
        (shape.bpCode.drop ((firstWord + 2) * wordSize)).take wordSize ++
          (shape.bpCode.drop ((firstWord + 3) * wordSize)).take wordSize := by
    have htwo : 2 * wordSize = wordSize + wordSize := by omega
    rw [htwo]
    rw [list_take_add_eq_take_append_drop_take]
    simp only [List.drop_drop]
    rw [show (firstWord + 2) * wordSize + wordSize =
      (firstWord + 3) * wordSize by
        rw [show firstWord + 3 = (firstWord + 2) + 1 by omega]
        simp [Nat.add_mul, Nat.add_comm]]
  have hwindow :
      localBPWindowBits shape blockSize close =
        (shape.bpCode.drop (firstWord * wordSize)).take
          (4 * wordSize) := by
    simp [localBPWindowBits, localBPWindowBase, wordSize, firstWord]
  have h0w :
      SuccinctSpace.flattenPayloadWords (bpCodeWordReadsAt shape firstWord) =
        (shape.bpCode.drop (firstWord * wordSize)).take wordSize := by
    simpa [wordSize] using h0
  have h1w :
      SuccinctSpace.flattenPayloadWords
          (bpCodeWordReadsAt shape (1 + firstWord)) =
        (shape.bpCode.drop ((firstWord + 1) * wordSize)).take wordSize := by
    simpa [wordSize, Nat.add_comm] using h1
  have h2w :
      SuccinctSpace.flattenPayloadWords
          (bpCodeWordReadsAt shape (2 + firstWord)) =
        (shape.bpCode.drop ((firstWord + 2) * wordSize)).take wordSize := by
    simpa [wordSize, Nat.add_comm] using h2
  have h3w :
      SuccinctSpace.flattenPayloadWords
          (bpCodeWordReadsAt shape (3 + firstWord)) =
        (shape.bpCode.drop ((firstWord + 3) * wordSize)).take wordSize := by
    simpa [wordSize, Nat.add_comm] using h3
  rw [hwindow, hsplit1, hsplit2, hsplit3]
  simp [localBPBlockWordsRead, SuccinctSpace.flattenPayloadWords_append,
    h0w, h1w, h2w, h3w, wordSize, firstWord, Nat.add_comm]

/-- Read a global BP bit through the local window when it falls in range. -/
def localBPWindowGet?
    (shape : Cartesian.CartesianShape)
    (blockSize close globalPos : Nat) : Option Bool :=
  let base := localBPWindowBase shape blockSize close
  if base <= globalPos then
    (localBPWindowBits shape blockSize close)[globalPos - base]?
  else
    none

theorem localBPWindowBits_length_le
    (shape : Cartesian.CartesianShape)
    (blockSize close : Nat) :
    (localBPWindowBits shape blockSize close).length <=
      4 * SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  simp [localBPWindowBits, List.length_take]
  exact Nat.min_le_left _ _

/--
When the block size is zero, all closes have the same `blockOfClose`, so the
same-block test alone gives no endpoint coverage guarantee for a four-word
local BP window.
-/
theorem zeroBlockSameBlock_does_not_imply_localBPWindowCoverage
    (shape : Cartesian.CartesianShape)
    {rightClose : Nat}
    (hwide :
      4 * SuccinctRankProposal.machineWordBits shape.bpCode.length <
        rightClose + 1) :
    blockOfClose 0 0 = blockOfClose 0 rightClose /\
      ¬ rightClose + 1 <=
        localBPWindowBase shape 0 0 +
          (localBPWindowBits shape 0 0).length := by
  constructor
  · simp [blockOfClose]
  · intro hcovered
    have hlen := localBPWindowBits_length_le shape 0 0
    have hbase : localBPWindowBase shape 0 0 = 0 := by
      simp [localBPWindowBase, blockStartOf]
    omega

theorem localBPWindowGet?_eq_bpCode_get?
    {shape : Cartesian.CartesianShape}
    {blockSize close globalPos : Nat}
    (hcovered :
      localBPWindowBase shape blockSize close <= globalPos /\
        globalPos <
          localBPWindowBase shape blockSize close +
            4 * SuccinctRankProposal.machineWordBits shape.bpCode.length) :
    localBPWindowGet? shape blockSize close globalPos =
      shape.bpCode[globalPos]? := by
  unfold localBPWindowGet? localBPWindowBits
  simp only [hcovered.1, ↓reduceIte]
  have hoff :
      globalPos - localBPWindowBase shape blockSize close <
        4 * SuccinctRankProposal.machineWordBits shape.bpCode.length := by
    omega
  rw [List.getElem?_take]
  simp [hoff]
  have hpos :
      localBPWindowBase shape blockSize close +
          (globalPos - localBPWindowBase shape blockSize close) =
        globalPos := by
    omega
  rw [hpos]

/--
Reading a bit from the flattened charged local BP words agrees with the global
BP code whenever the requested position lies in the four-word local window.
-/
theorem localBPBlockWordsRead_get?_eq_bpCode_get?
    {shape : Cartesian.CartesianShape}
    {blockSize close globalPos : Nat}
    (hcovered :
      localBPWindowBase shape blockSize close <= globalPos /\
        globalPos <
          localBPWindowBase shape blockSize close +
            4 * SuccinctRankProposal.machineWordBits shape.bpCode.length) :
    (SuccinctSpace.flattenPayloadWords
        (localBPBlockWordsRead shape blockSize close))[
          globalPos - localBPWindowBase shape blockSize close]? =
      shape.bpCode[globalPos]? := by
  have hget :=
    localBPWindowGet?_eq_bpCode_get?
      (shape := shape) (blockSize := blockSize) (close := close)
      (globalPos := globalPos) hcovered
  simpa [localBPWindowGet?, hcovered.1,
    localBPWindowBits_eq_flatten_localBPBlockWordsRead shape blockSize close]
    using hget

theorem localBPWindowBits_end_le_bpCode_length
    (shape : Cartesian.CartesianShape)
    (blockSize close : Nat)
    (hbase :
      localBPWindowBase shape blockSize close <= shape.bpCode.length) :
    localBPWindowBase shape blockSize close +
        (localBPWindowBits shape blockSize close).length <=
      shape.bpCode.length := by
  simp [localBPWindowBits, List.length_take, List.length_drop]
  omega

theorem localBPWindowBase_le_blockStart
    (shape : Cartesian.CartesianShape)
    (blockSize close : Nat) :
    localBPWindowBase shape blockSize close <=
      blockStartOf blockSize (blockOfClose blockSize close) := by
  unfold localBPWindowBase
  let wordSize := SuccinctRankProposal.machineWordBits shape.bpCode.length
  let start := blockStartOf blockSize (blockOfClose blockSize close)
  have hdiv := Nat.div_add_mod start wordSize
  have hcomm : start / wordSize * wordSize =
      wordSize * (start / wordSize) := by
    exact Nat.mul_comm (start / wordSize) wordSize
  change start / wordSize * wordSize <= start
  omega

theorem localBPWindow_block_end_le_four_words
    (shape : Cartesian.CartesianShape)
    (blockSize close : Nat)
    (hblockSize :
      blockSize <=
        3 * SuccinctRankProposal.machineWordBits shape.bpCode.length) :
    blockStartOf blockSize (blockOfClose blockSize close) + blockSize <=
      localBPWindowBase shape blockSize close +
        4 * SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  unfold localBPWindowBase
  let wordSize := SuccinctRankProposal.machineWordBits shape.bpCode.length
  let start := blockStartOf blockSize (blockOfClose blockSize close)
  have hword : 0 < wordSize := by
    simpa [wordSize] using
      SuccinctRankProposal.machineWordBits_pos shape.bpCode.length
  have hdiv := Nat.div_add_mod start wordSize
  have hmod := Nat.mod_lt start hword
  have hcomm : start / wordSize * wordSize =
      wordSize * (start / wordSize) := by
    exact Nat.mul_comm (start / wordSize) wordSize
  change start + blockSize <= start / wordSize * wordSize + 4 * wordSize
  omega

theorem localBPWindowBits_covers_of_le_width
    {shape : Cartesian.CartesianShape}
    {blockSize close pos : Nat}
    (hbasePos :
      localBPWindowBase shape blockSize close <= pos)
    (hposLen : pos <= shape.bpCode.length)
    (hposWidth :
      pos <=
        localBPWindowBase shape blockSize close +
          4 * SuccinctRankProposal.machineWordBits shape.bpCode.length) :
    pos <=
      localBPWindowBase shape blockSize close +
        (localBPWindowBits shape blockSize close).length := by
  let base := localBPWindowBase shape blockSize close
  let width := 4 * SuccinctRankProposal.machineWordBits shape.bpCode.length
  have hbaseLen : base <= shape.bpCode.length := by omega
  have hoffLen : pos - base <= shape.bpCode.length - base := by omega
  have hoffWidth : pos - base <= width := by omega
  have hoff :
      pos - base <= Nat.min width (shape.bpCode.length - base) :=
    Nat.le_min.mpr ⟨hoffWidth, hoffLen⟩
  have hposEq : base + (pos - base) = pos := by omega
  simp [localBPWindowBits, List.length_take, List.length_drop]
  omega

/-- Absolute BP excess at the base of the local window. -/
def localBPSeedExcess
    (shape : Cartesian.CartesianShape)
    (blockSize close : Nat) : Nat :=
  bpExcessAt shape (localBPWindowBase shape blockSize close)

/--
Recover the base excess from a stored close-rank seed at the same prefix
position.  When the base is in range and the seed is the false-rank at the
base, this is equal to `localBPSeedExcess`.
-/
def localBPSeedFromRankFalse
    (base falseRankAtBase : Nat) : Nat :=
  base - 2 * falseRankAtBase

theorem rankPrefix_true_add_false_eq_of_le_length
    {bits : List Bool} {limit : Nat}
    (hlimit : limit <= bits.length) :
    Succinct.rankPrefix true bits limit +
        Succinct.rankPrefix false bits limit =
      limit := by
  induction bits generalizing limit with
  | nil =>
      have hzero : limit = 0 := by
        simpa using hlimit
      subst limit
      simp [Succinct.rankPrefix]
  | cons bit rest ih =>
      cases limit with
      | zero =>
          simp [Succinct.rankPrefix]
      | succ limit =>
          have htail : limit <= rest.length := by
            simp at hlimit
            omega
          have hrec := ih htail
          cases bit <;> simp [Succinct.rankPrefix] <;> omega

theorem localBPSeedFromRankFalse_eq_localBPSeedExcess
    (shape : Cartesian.CartesianShape)
    (blockSize close : Nat)
    (hbase :
      localBPWindowBase shape blockSize close <= shape.bpCode.length) :
    localBPSeedFromRankFalse
        (localBPWindowBase shape blockSize close)
        (Succinct.rankPrefix false shape.bpCode
          (localBPWindowBase shape blockSize close)) =
      localBPSeedExcess shape blockSize close := by
  unfold localBPSeedFromRankFalse localBPSeedExcess bpExcessAt
  have hsum :=
    rankPrefix_true_add_false_eq_of_le_length
      (bits := shape.bpCode)
      (limit := localBPWindowBase shape blockSize close) hbase
  have hnonneg := bpExcessAt_prefix_nonnegative shape hbase
  omega

/-- Explicit modeled read of the false-rank seed at the local BP window base. -/
def localBPSeedFromRankFalseCosted
    (shape : Cartesian.CartesianShape)
    (blockSize close : Nat) : Costed Nat :=
  let base := localBPWindowBase shape blockSize close
  { value :=
      localBPSeedFromRankFalse base
        (Succinct.rankPrefix false shape.bpCode base)
    cost := 1 }

theorem localBPSeedFromRankFalseCosted_cost_le
    (shape : Cartesian.CartesianShape)
    (blockSize close : Nat) :
    (localBPSeedFromRankFalseCosted shape blockSize close).cost <= 1 := by
  simp [localBPSeedFromRankFalseCosted]

theorem localBPSeedFromRankFalseCosted_eq_localBPSeedExcess
    (shape : Cartesian.CartesianShape)
    (blockSize close : Nat)
    (hbase :
      localBPWindowBase shape blockSize close <= shape.bpCode.length) :
    (localBPSeedFromRankFalseCosted shape blockSize close).erase =
      localBPSeedExcess shape blockSize close := by
  simpa [localBPSeedFromRankFalseCosted, Costed.erase] using
    localBPSeedFromRankFalse_eq_localBPSeedExcess
      shape blockSize close hbase

/-- Seed read routed through a supplied rank-close callback. -/
def localBPSeedFromRankCloseCosted
    (shape : Cartesian.CartesianShape)
    (rankCloseCosted : Nat -> Costed Nat)
    (blockSize close : Nat) : Costed Nat :=
  let base := localBPWindowBase shape blockSize close
  Costed.map (fun rankFalse => localBPSeedFromRankFalse base rankFalse)
    (rankCloseCosted base)

theorem localBPSeedFromRankCloseCosted_cost_le
    (shape : Cartesian.CartesianShape)
    (rankCloseCosted : Nat -> Costed Nat)
    (blockSize close rankCost : Nat)
    (hrankCost : forall pos, (rankCloseCosted pos).cost <= rankCost) :
    (localBPSeedFromRankCloseCosted shape rankCloseCosted blockSize close).cost <=
      rankCost := by
  unfold localBPSeedFromRankCloseCosted
  simp [Costed.map, Costed.bind, Costed.pure]
  exact hrankCost (localBPWindowBase shape blockSize close)

theorem localBPSeedFromRankCloseCosted_eq_localBPSeedExcess
    (shape : Cartesian.CartesianShape)
    (rankCloseCosted : Nat -> Costed Nat)
    (blockSize close : Nat)
    (hrankExact :
      forall pos,
        (rankCloseCosted pos).erase =
          Succinct.rankPrefix false shape.bpCode pos)
    (hbase :
      localBPWindowBase shape blockSize close <= shape.bpCode.length) :
    (localBPSeedFromRankCloseCosted shape rankCloseCosted blockSize close).erase =
      localBPSeedExcess shape blockSize close := by
  let base := localBPWindowBase shape blockSize close
  have hrank :
      (rankCloseCosted base).value =
        Succinct.rankPrefix false shape.bpCode base := by
    simpa [Costed.erase] using hrankExact base
  have hseed :=
    localBPSeedFromRankFalse_eq_localBPSeedExcess
      shape blockSize close hbase
  simpa [localBPSeedFromRankCloseCosted, Costed.map, Costed.bind,
    Costed.pure, Costed.erase, base, hrank] using hseed

/--
The local BP bits alone do not determine the absolute BP-excess seed at the
window base.

The fringe helpers return absolute `(excess, prefixPos)` candidates so that
they can be merged with the interior candidate. Two identical local windows can
have different prefix excess before the window, hence a decoder that is given
only `localBPWindowBits` still needs a charged/stored seed such as base excess
or equivalent rank metadata.
-/
theorem localBPWindowBits_alone_does_not_determine_base_excess :
    exists prefixA prefixB window : List Bool,
      List.take window.length
          (List.drop prefixA.length (prefixA ++ window)) =
        List.take window.length
          (List.drop prefixB.length (prefixB ++ window)) /\
      (Succinct.rankPrefix true (prefixA ++ window) prefixA.length -
          Succinct.rankPrefix false (prefixA ++ window) prefixA.length) ≠
        (Succinct.rankPrefix true (prefixB ++ window) prefixB.length -
          Succinct.rankPrefix false (prefixB ++ window) prefixB.length) := by
  refine ⟨[], [true], [false], ?_, ?_⟩
  · decide
  · decide

def localBPSeededExcessAt
    (window : List Bool) (seed base globalPos : Nat) : Nat :=
  let sample := Nat.min globalPos (base + window.length)
  seed +
      Succinct.rankPrefix true window (sample - base) -
    Succinct.rankPrefix false window (sample - base)

theorem localBPSeededExcessAt_eq_bpExcessAt
    {shape : Cartesian.CartesianShape}
    {blockSize close globalPos : Nat}
    (hbase :
      localBPWindowBase shape blockSize close <= shape.bpCode.length)
    (hpos :
      localBPWindowBase shape blockSize close <= globalPos)
    (hcovered :
      globalPos <=
        localBPWindowBase shape blockSize close +
          (localBPWindowBits shape blockSize close).length) :
    localBPSeededExcessAt
        (localBPWindowBits shape blockSize close)
        (localBPSeedExcess shape blockSize close)
        (localBPWindowBase shape blockSize close)
        globalPos =
      bpExcessAt shape globalPos := by
  let base := localBPWindowBase shape blockSize close
  let width := 4 * SuccinctRankProposal.machineWordBits shape.bpCode.length
  have hend :
      base + (localBPWindowBits shape blockSize close).length <=
        shape.bpCode.length := by
    simpa [base] using
      localBPWindowBits_end_le_bpCode_length shape blockSize close hbase
  have hposLen : globalPos <= shape.bpCode.length := by
    omega
  have hsample :
      Nat.min globalPos
          (base + (localBPWindowBits shape blockSize close).length) =
        globalPos := by
    exact Nat.min_eq_left (by simpa [base] using hcovered)
  have hsample' :
      Nat.min globalPos
          (localBPWindowBase shape blockSize close +
            (localBPWindowBits shape blockSize close).length) =
        globalPos := by
    simpa [base] using hsample
  have hoffWindow :
      globalPos - base <=
        (localBPWindowBits shape blockSize close).length := by
    omega
  have htrueLocal :
      Succinct.rankPrefix true
          (localBPWindowBits shape blockSize close)
          (globalPos - base) =
        Succinct.rankPrefix true shape.bpCode globalPos -
          Succinct.rankPrefix true shape.bpCode base := by
    have htake :
        Succinct.rankPrefix true
            ((shape.bpCode.drop base).take width)
            (globalPos - base) =
          Succinct.rankPrefix true (shape.bpCode.drop base)
            (globalPos - base) := by
      apply Succinct.rankPrefix_take_eq_of_le
      simpa [localBPWindowBits, base, width] using hoffWindow
    have hdrop :=
      Succinct.rankPrefix_drop_eq_sub_of_le
        true shape.bpCode hpos hposLen
    simpa [localBPWindowBits, base, width] using htake.trans hdrop
  have hfalseLocal :
      Succinct.rankPrefix false
          (localBPWindowBits shape blockSize close)
          (globalPos - base) =
        Succinct.rankPrefix false shape.bpCode globalPos -
          Succinct.rankPrefix false shape.bpCode base := by
    have htake :
        Succinct.rankPrefix false
            ((shape.bpCode.drop base).take width)
            (globalPos - base) =
          Succinct.rankPrefix false (shape.bpCode.drop base)
            (globalPos - base) := by
      apply Succinct.rankPrefix_take_eq_of_le
      simpa [localBPWindowBits, base, width] using hoffWindow
    have hdrop :=
      Succinct.rankPrefix_drop_eq_sub_of_le
        false shape.bpCode hpos hposLen
    simpa [localBPWindowBits, base, width] using htake.trans hdrop
  have hbaseNonneg := bpExcessAt_prefix_nonnegative shape hbase
  have hposNonneg := bpExcessAt_prefix_nonnegative shape hposLen
  have htrueMono :
      Succinct.rankPrefix true shape.bpCode base <=
        Succinct.rankPrefix true shape.bpCode globalPos :=
    Succinct.rankPrefix_mono_limit true shape.bpCode hpos
  have hfalseMono :
      Succinct.rankPrefix false shape.bpCode base <=
        Succinct.rankPrefix false shape.bpCode globalPos :=
    Succinct.rankPrefix_mono_limit false shape.bpCode hpos
  have hbaseNonneg' :
      Succinct.rankPrefix false shape.bpCode base <=
        Succinct.rankPrefix true shape.bpCode base := by
    simpa [base] using hbaseNonneg
  have hseed :
      localBPSeedExcess shape blockSize close =
        Succinct.rankPrefix true shape.bpCode base -
          Succinct.rankPrefix false shape.bpCode base := by
    simp [localBPSeedExcess, bpExcessAt, base]
  unfold localBPSeededExcessAt bpExcessAt
  simp [hsample', base, hseed, htrueLocal, hfalseLocal]
  change
    (Succinct.rankPrefix true shape.bpCode base -
          Succinct.rankPrefix false shape.bpCode base) +
        (Succinct.rankPrefix true shape.bpCode globalPos -
          Succinct.rankPrefix true shape.bpCode base) -
      (Succinct.rankPrefix false shape.bpCode globalPos -
        Succinct.rankPrefix false shape.bpCode base) =
    Succinct.rankPrefix true shape.bpCode globalPos -
      Succinct.rankPrefix false shape.bpCode globalPos
  omega

def localBPSeededBetterPrefixPos
    (window : List Bool) (seed base left right : Nat) : Nat :=
  if localBPSeededExcessAt window seed base right <
      localBPSeededExcessAt window seed base left then
    right
  else
    left

theorem localBPSeededBetterPrefixPos_bounds
    {window : List Bool} {seed base left right : Nat}
    (hleftBase : base <= left)
    (hleftCovered : left <= base + window.length)
    (hrightBase : base <= right)
    (hrightCovered : right <= base + window.length) :
    base <= localBPSeededBetterPrefixPos window seed base left right /\
      localBPSeededBetterPrefixPos window seed base left right <=
        base + window.length := by
  unfold localBPSeededBetterPrefixPos
  by_cases hlt :
      localBPSeededExcessAt window seed base right <
        localBPSeededExcessAt window seed base left
  · simp [hlt, hrightBase, hrightCovered]
  · simp [hlt, hleftBase, hleftCovered]

theorem localBPSeededBetterPrefixPos_eq_bpBetterArgMinPrefixPos
    {shape : Cartesian.CartesianShape}
    {blockSize close left right : Nat}
    (hbase :
      localBPWindowBase shape blockSize close <= shape.bpCode.length)
    (hleftBase :
      localBPWindowBase shape blockSize close <= left)
    (hleftCovered :
      left <=
        localBPWindowBase shape blockSize close +
          (localBPWindowBits shape blockSize close).length)
    (hrightBase :
      localBPWindowBase shape blockSize close <= right)
    (hrightCovered :
      right <=
        localBPWindowBase shape blockSize close +
          (localBPWindowBits shape blockSize close).length) :
    localBPSeededBetterPrefixPos
        (localBPWindowBits shape blockSize close)
        (localBPSeedExcess shape blockSize close)
        (localBPWindowBase shape blockSize close)
        left right =
      bpBetterArgMinPrefixPos shape left right := by
  have hleft :=
    localBPSeededExcessAt_eq_bpExcessAt
      (shape := shape) (blockSize := blockSize) (close := close)
      (globalPos := left) hbase hleftBase hleftCovered
  have hright :=
    localBPSeededExcessAt_eq_bpExcessAt
      (shape := shape) (blockSize := blockSize) (close := close)
      (globalPos := right) hbase hrightBase hrightCovered
  unfold localBPSeededBetterPrefixPos bpBetterArgMinPrefixPos
  rw [hleft, hright]

def localBPSeededPrefixRangeArgMinPrefixPosFrom
    (window : List Bool) (seed base : Nat) :
    Nat -> Nat -> Nat -> Nat
  | _pos, 0, best => best
  | pos, steps + 1, best =>
      let sample := Nat.min pos (base + window.length)
      let best' := localBPSeededBetterPrefixPos window seed base best sample
      localBPSeededPrefixRangeArgMinPrefixPosFrom window seed base
        (pos + 1) steps best'

theorem localBPSeededPrefixRangeArgMinPrefixPosFrom_bounds
    {window : List Bool} {seed base pos steps best : Nat}
    (hposBase : base <= pos)
    (hcovered : pos + steps <= base + window.length + 1)
    (hbestBase : base <= best)
    (hbestCovered : best <= base + window.length) :
    base <=
        localBPSeededPrefixRangeArgMinPrefixPosFrom window seed base
          pos steps best /\
      localBPSeededPrefixRangeArgMinPrefixPosFrom window seed base
          pos steps best <=
        base + window.length := by
  induction steps generalizing pos best with
  | zero =>
      simp [localBPSeededPrefixRangeArgMinPrefixPosFrom,
        hbestBase, hbestCovered]
  | succ steps ih =>
      have hposCovered : pos <= base + window.length := by
        omega
      have hsample :
          Nat.min pos (base + window.length) = pos := by
        exact Nat.min_eq_left hposCovered
      have hbetterBounds :=
        localBPSeededBetterPrefixPos_bounds
          (window := window) (seed := seed) (base := base)
          (left := best) (right := pos)
          hbestBase hbestCovered hposBase hposCovered
      have htail :
          pos + 1 + steps <= base + window.length + 1 := by
        omega
      simpa [localBPSeededPrefixRangeArgMinPrefixPosFrom, hsample] using
        ih (pos := pos + 1)
          (best := localBPSeededBetterPrefixPos window seed base best pos)
          (by omega) htail hbetterBounds.1 hbetterBounds.2

theorem localBPSeededPrefixRangeArgMinPrefixPosFrom_eq_bpPrefixRangeArgMinPrefixPosFrom
    {shape : Cartesian.CartesianShape}
    {blockSize close pos steps best : Nat}
    (hbase :
      localBPWindowBase shape blockSize close <= shape.bpCode.length)
    (hposBase :
      localBPWindowBase shape blockSize close <= pos)
    (hcovered :
      pos + steps <=
        localBPWindowBase shape blockSize close +
          (localBPWindowBits shape blockSize close).length + 1)
    (hbestBase :
      localBPWindowBase shape blockSize close <= best)
    (hbestCovered :
      best <=
        localBPWindowBase shape blockSize close +
          (localBPWindowBits shape blockSize close).length) :
    localBPSeededPrefixRangeArgMinPrefixPosFrom
        (localBPWindowBits shape blockSize close)
        (localBPSeedExcess shape blockSize close)
        (localBPWindowBase shape blockSize close)
        pos steps best =
      bpPrefixRangeArgMinPrefixPosFrom shape pos steps best := by
  induction steps generalizing pos best with
  | zero =>
      simp [localBPSeededPrefixRangeArgMinPrefixPosFrom,
        bpPrefixRangeArgMinPrefixPosFrom]
  | succ steps ih =>
      let base := localBPWindowBase shape blockSize close
      let window := localBPWindowBits shape blockSize close
      have hend :
          base + window.length <= shape.bpCode.length := by
        simpa [base, window] using
          localBPWindowBits_end_le_bpCode_length shape blockSize close hbase
      have hcoveredLocal :
          pos + (steps + 1) <= base + window.length + 1 := by
        simpa [base, window, Nat.add_assoc] using hcovered
      have hbestBaseLocal : base <= best := by
        simpa [base] using hbestBase
      have hbestCoveredLocal : best <= base + window.length := by
        simpa [base, window] using hbestCovered
      have hposCovered : pos <= base + window.length := by
        omega
      have hposLen : pos <= shape.bpCode.length := by
        omega
      have hsampleLocal :
          Nat.min pos (base + window.length) = pos :=
        Nat.min_eq_left hposCovered
      have hsampleSemantic :
          Nat.min pos shape.bpCode.length = pos :=
        Nat.min_eq_left hposLen
      have hbetter :=
        localBPSeededBetterPrefixPos_eq_bpBetterArgMinPrefixPos
          (shape := shape) (blockSize := blockSize) (close := close)
          (left := best) (right := pos)
          hbase hbestBase hbestCovered
          (by simpa [base] using hposBase)
          (by simpa [base, window] using hposCovered)
      have hbest'Base :
          base <= bpBetterArgMinPrefixPos shape best pos := by
        unfold bpBetterArgMinPrefixPos
        by_cases hlt : bpExcessAt shape pos < bpExcessAt shape best
        · simp [hlt]
          exact hposBase
        · simp [hlt]
          exact hbestBaseLocal
      have hbest'Covered :
          bpBetterArgMinPrefixPos shape best pos <= base + window.length := by
        unfold bpBetterArgMinPrefixPos
        by_cases hlt : bpExcessAt shape pos < bpExcessAt shape best
        · simp [hlt, hposCovered]
        · simp [hlt]
          exact hbestCoveredLocal
      have htail :
          pos + 1 + steps <= base + window.length + 1 := by
        omega
      have hrec :=
        ih (pos := pos + 1)
          (best := bpBetterArgMinPrefixPos shape best pos)
          (by simpa [base] using (show base <= pos + 1 by omega))
          (by simpa [base, window] using htail)
          (by simpa [base] using hbest'Base)
          (by simpa [base, window] using hbest'Covered)
      simp [localBPSeededPrefixRangeArgMinPrefixPosFrom,
        bpPrefixRangeArgMinPrefixPosFrom, base, window, hsampleLocal,
        hsampleSemantic, hbetter, hrec]

def localBPSeededPrefixRangeArgMinPrefixPos
    (window : List Bool) (seed base start count : Nat) : Nat :=
  match count with
  | 0 => Nat.min start (base + window.length)
  | steps + 1 =>
      localBPSeededPrefixRangeArgMinPrefixPosFrom window seed base
        (start + 1) steps (Nat.min start (base + window.length))

def localBPSeededPrefixRangeMinExcess
    (window : List Bool) (seed base start count : Nat) : Nat :=
  localBPSeededExcessAt window seed base
    (localBPSeededPrefixRangeArgMinPrefixPos window seed base start count)

theorem localBPSeededPrefixRangeArgMinPrefixPos_bounds_of_pos
    {window : List Bool} {seed base start count : Nat}
    (hcount : 0 < count)
    (hstartBase : base <= start)
    (hcovered : start + count <= base + window.length + 1) :
    base <=
        localBPSeededPrefixRangeArgMinPrefixPos window seed base
          start count /\
      localBPSeededPrefixRangeArgMinPrefixPos window seed base
          start count <=
        base + window.length := by
  cases count with
  | zero =>
      omega
  | succ steps =>
      have hstartCovered : start <= base + window.length := by
        omega
      have hsampleLocal :
          Nat.min start (base + window.length) = start :=
        Nat.min_eq_left hstartCovered
      have htail :
          start + 1 + steps <= base + window.length + 1 := by
        omega
      simpa [localBPSeededPrefixRangeArgMinPrefixPos, hsampleLocal] using
        localBPSeededPrefixRangeArgMinPrefixPosFrom_bounds
          (window := window) (seed := seed) (base := base)
          (pos := start + 1) (steps := steps) (best := start)
          (by omega) htail hstartBase hstartCovered

theorem localBPSeededPrefixRangeArgMinPrefixPos_eq_bpPrefixRangeArgMinPrefixPos_of_pos
    {shape : Cartesian.CartesianShape}
    {blockSize close start count : Nat}
    (hcount : 0 < count)
    (hbase :
      localBPWindowBase shape blockSize close <= shape.bpCode.length)
    (hstartBase :
      localBPWindowBase shape blockSize close <= start)
    (hcovered :
      start + count <=
        localBPWindowBase shape blockSize close +
          (localBPWindowBits shape blockSize close).length + 1) :
    localBPSeededPrefixRangeArgMinPrefixPos
        (localBPWindowBits shape blockSize close)
        (localBPSeedExcess shape blockSize close)
        (localBPWindowBase shape blockSize close)
        start count =
      bpPrefixRangeArgMinPrefixPos shape start count := by
  cases count with
  | zero =>
      omega
  | succ steps =>
      let base := localBPWindowBase shape blockSize close
      let window := localBPWindowBits shape blockSize close
      have hend :
          base + window.length <= shape.bpCode.length := by
        simpa [base, window] using
          localBPWindowBits_end_le_bpCode_length shape blockSize close hbase
      have hcoveredLocal :
          start + (steps + 1) <= base + window.length + 1 := by
        simpa [base, window, Nat.add_assoc] using hcovered
      have hstartCovered : start <= base + window.length := by
        omega
      have hstartLen : start <= shape.bpCode.length := by
        omega
      have hsampleLocal :
          Nat.min start (base + window.length) = start :=
        Nat.min_eq_left hstartCovered
      have hsampleSemantic :
          Nat.min start shape.bpCode.length = start :=
        Nat.min_eq_left hstartLen
      have htail :
          start + 1 + steps <= base + window.length + 1 := by
        omega
      have hfrom :=
        localBPSeededPrefixRangeArgMinPrefixPosFrom_eq_bpPrefixRangeArgMinPrefixPosFrom
          (shape := shape) (blockSize := blockSize) (close := close)
          (pos := start + 1) (steps := steps) (best := start)
          hbase
          (by simpa [base] using (show base <= start + 1 by omega))
          (by simpa [base, window] using htail)
          hstartBase
          (by simpa [base, window] using hstartCovered)
      simp [localBPSeededPrefixRangeArgMinPrefixPos,
        bpPrefixRangeArgMinPrefixPos, base, window, hsampleLocal,
        hsampleSemantic, hfrom]

theorem localBPSeededPrefixRangeMinExcess_eq_bpPrefixRangeMinExcess_of_pos
    {shape : Cartesian.CartesianShape}
    {blockSize close start count : Nat}
    (hcount : 0 < count)
    (hbase :
      localBPWindowBase shape blockSize close <= shape.bpCode.length)
    (hstartBase :
      localBPWindowBase shape blockSize close <= start)
    (hcovered :
      start + count <=
        localBPWindowBase shape blockSize close +
          (localBPWindowBits shape blockSize close).length + 1) :
    localBPSeededPrefixRangeMinExcess
        (localBPWindowBits shape blockSize close)
        (localBPSeedExcess shape blockSize close)
        (localBPWindowBase shape blockSize close)
        start count =
      bpPrefixRangeMinExcess shape start count := by
  have harg :=
    localBPSeededPrefixRangeArgMinPrefixPos_eq_bpPrefixRangeArgMinPrefixPos_of_pos
      (shape := shape) (blockSize := blockSize) (close := close)
      (start := start) (count := count)
      hcount hbase hstartBase hcovered
  have hbounds :=
    localBPSeededPrefixRangeArgMinPrefixPos_bounds_of_pos
      (window := localBPWindowBits shape blockSize close)
      (seed := localBPSeedExcess shape blockSize close)
      (base := localBPWindowBase shape blockSize close)
      (start := start) (count := count)
      hcount hstartBase hcovered
  have hexcess :=
    localBPSeededExcessAt_eq_bpExcessAt
      (shape := shape) (blockSize := blockSize) (close := close)
      (globalPos :=
        localBPSeededPrefixRangeArgMinPrefixPos
          (localBPWindowBits shape blockSize close)
          (localBPSeedExcess shape blockSize close)
          (localBPWindowBase shape blockSize close)
          start count)
      hbase hbounds.1 hbounds.2
  simpa [localBPSeededPrefixRangeMinExcess, bpPrefixRangeMinExcess,
    harg] using hexcess

def localBPLeftFringeCandidateSeededCosted
    (shape : Cartesian.CartesianShape)
    (blockSize leftClose seed : Nat) : Costed (Option (Nat × Nat)) :=
  let window := localBPWindowBits shape blockSize leftClose
  let base := localBPWindowBase shape blockSize leftClose
  let count :=
    blockStartOf blockSize (blockOfClose blockSize leftClose) +
      blockSize - leftClose
  { value :=
      some
        (localBPSeededPrefixRangeMinExcess window seed base
          (leftClose + 1) count,
          localBPSeededPrefixRangeArgMinPrefixPos window seed base
            (leftClose + 1) count)
    cost := 4 }

def localBPRightFringeCandidateSeededCosted
    (shape : Cartesian.CartesianShape)
    (blockSize rightClose seed : Nat) : Costed (Option (Nat × Nat)) :=
  let window := localBPWindowBits shape blockSize rightClose
  let base := localBPWindowBase shape blockSize rightClose
  let start := blockStartOf blockSize (blockOfClose blockSize rightClose)
  let count := rightClose - start + 2
  { value :=
      some
        (localBPSeededPrefixRangeMinExcess window seed base start count,
          localBPSeededPrefixRangeArgMinPrefixPos window seed base start count)
    cost := 4 }

theorem localBPBlockWordsRead_length_le_machine
    (shape : Cartesian.CartesianShape)
    (blockSize close : Nat)
    {word : List Bool}
    (hmem : word ∈ localBPBlockWordsRead shape blockSize close) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  simp [localBPBlockWordsRead, List.mem_append] at hmem
  rcases hmem with hmem | hmem | hmem | hmem
  · exact bpCodeWordReadsAt_length_le_machine shape _ hmem
  · exact bpCodeWordReadsAt_length_le_machine shape _ hmem
  · exact bpCodeWordReadsAt_length_le_machine shape _ hmem
  · exact bpCodeWordReadsAt_length_le_machine shape _ hmem

theorem localBPLeftFringeCandidateSeededCosted_cost_le
    (shape : Cartesian.CartesianShape)
    (blockSize leftClose seed : Nat) :
    (localBPLeftFringeCandidateSeededCosted shape blockSize leftClose seed).cost <=
      4 := by
  simp [localBPLeftFringeCandidateSeededCosted]

theorem localBPRightFringeCandidateSeededCosted_cost_le
    (shape : Cartesian.CartesianShape)
    (blockSize rightClose seed : Nat) :
    (localBPRightFringeCandidateSeededCosted shape blockSize rightClose seed).cost <=
      4 := by
  simp [localBPRightFringeCandidateSeededCosted]

def localBPSameBlockCloseSeededCosted
    (shape : Cartesian.CartesianShape)
    (blockSize leftClose rightClose seed : Nat) : Costed (Option Nat) :=
  let window :=
    SuccinctSpace.flattenPayloadWords
      (localBPBlockWordsRead shape blockSize leftClose)
  let base := localBPWindowBase shape blockSize leftClose
  let start := leftClose + 1
  let count := rightClose - leftClose + 1
  { value :=
      bpCandidateClose?
        (some
          (localBPSeededPrefixRangeMinExcess window seed base start count,
            localBPSeededPrefixRangeArgMinPrefixPos window seed base
              start count))
    cost := 4 }

def localBPSameBlockCloseDecodedCosted
    (shape : Cartesian.CartesianShape)
    (blockSize leftClose rightClose : Nat) : Costed (Option Nat) :=
  Costed.bind
    (localBPSeedFromRankFalseCosted shape blockSize leftClose)
    fun seed =>
      localBPSameBlockCloseSeededCosted shape blockSize leftClose rightClose
        seed

def localBPSameBlockCloseDecodedCostedWithRankSeed
    (shape : Cartesian.CartesianShape)
    (rankCloseCosted : Nat -> Costed Nat)
    (blockSize leftClose rightClose : Nat) : Costed (Option Nat) :=
  Costed.bind
    (localBPSeedFromRankCloseCosted shape rankCloseCosted blockSize leftClose)
    fun seed =>
      localBPSameBlockCloseSeededCosted shape blockSize leftClose rightClose
        seed

theorem localBPSameBlockCloseSeededCosted_cost_le
    (shape : Cartesian.CartesianShape)
    (blockSize leftClose rightClose seed : Nat) :
    (localBPSameBlockCloseSeededCosted shape blockSize leftClose rightClose
        seed).cost <= 4 := by
  simp [localBPSameBlockCloseSeededCosted]

theorem localBPSameBlockCloseDecodedCosted_cost_le
    (shape : Cartesian.CartesianShape)
    (blockSize leftClose rightClose : Nat) :
    (localBPSameBlockCloseDecodedCosted shape blockSize leftClose
        rightClose).cost <= 5 := by
  simp [localBPSameBlockCloseDecodedCosted, Costed.bind,
    localBPSeedFromRankFalseCosted, localBPSameBlockCloseSeededCosted]

theorem localBPSameBlockCloseDecodedCostedWithRankSeed_cost_le
    (shape : Cartesian.CartesianShape)
    (rankCloseCosted : Nat -> Costed Nat)
    (blockSize leftClose rightClose rankCost : Nat)
    (hrankCost : forall pos, (rankCloseCosted pos).cost <= rankCost) :
    (localBPSameBlockCloseDecodedCostedWithRankSeed shape rankCloseCosted
        blockSize leftClose rightClose).cost <= rankCost + 4 := by
  unfold localBPSameBlockCloseDecodedCostedWithRankSeed
  have hseed :=
    localBPSeedFromRankCloseCosted_cost_le shape rankCloseCosted blockSize
      leftClose rankCost hrankCost
  have hlocal :=
    localBPSameBlockCloseSeededCosted_cost_le shape blockSize leftClose
      rightClose
      (localBPSeedFromRankCloseCosted shape rankCloseCosted blockSize
        leftClose).value
  simp [Costed.bind] at hseed hlocal ⊢
  omega

theorem localBPSameBlockCloseSeededCosted_eq_semantic
    {shape : Cartesian.CartesianShape}
    {blockSize leftClose rightClose : Nat}
    (hbase :
      localBPWindowBase shape blockSize leftClose <= shape.bpCode.length)
    (hstartBase :
      localBPWindowBase shape blockSize leftClose <= leftClose + 1)
    (hrightCovered :
      rightClose + 1 <=
        localBPWindowBase shape blockSize leftClose +
          (localBPWindowBits shape blockSize leftClose).length)
    (hordered : leftClose <= rightClose) :
    (localBPSameBlockCloseSeededCosted shape blockSize leftClose rightClose
        (localBPSeedExcess shape blockSize leftClose)).erase =
      bpCandidateClose?
        (some
          (bpPrefixRangeMinExcess shape (leftClose + 1)
            (rightClose - leftClose + 1),
            bpPrefixRangeArgMinPrefixPos shape (leftClose + 1)
              (rightClose - leftClose + 1))) := by
  let start := leftClose + 1
  let count := rightClose - leftClose + 1
  have hcount : 0 < count := by
    omega
  have hcovered :
      start + count <=
        localBPWindowBase shape blockSize leftClose +
          (localBPWindowBits shape blockSize leftClose).length + 1 := by
    simp [start, count]
    omega
  have hmin :=
    localBPSeededPrefixRangeMinExcess_eq_bpPrefixRangeMinExcess_of_pos
      (shape := shape) (blockSize := blockSize) (close := leftClose)
      (start := start) (count := count)
      hcount hbase (by simpa [start] using hstartBase) hcovered
  have harg :=
    localBPSeededPrefixRangeArgMinPrefixPos_eq_bpPrefixRangeArgMinPrefixPos_of_pos
      (shape := shape) (blockSize := blockSize) (close := leftClose)
      (start := start) (count := count)
      hcount hbase (by simpa [start] using hstartBase) hcovered
  have hwindow :=
    localBPWindowBits_eq_flatten_localBPBlockWordsRead
      shape blockSize leftClose
  have hminFlat :
      localBPSeededPrefixRangeMinExcess
          (SuccinctSpace.flattenPayloadWords
            (localBPBlockWordsRead shape blockSize leftClose))
          (localBPSeedExcess shape blockSize leftClose)
          (localBPWindowBase shape blockSize leftClose)
          start count =
        bpPrefixRangeMinExcess shape start count := by
    simpa [← hwindow] using hmin
  have hargFlat :
      localBPSeededPrefixRangeArgMinPrefixPos
          (SuccinctSpace.flattenPayloadWords
            (localBPBlockWordsRead shape blockSize leftClose))
          (localBPSeedExcess shape blockSize leftClose)
          (localBPWindowBase shape blockSize leftClose)
          start count =
        bpPrefixRangeArgMinPrefixPos shape start count := by
    simpa [← hwindow] using harg
  simp [localBPSameBlockCloseSeededCosted, start, count, hminFlat,
    hargFlat]

theorem localBPSameBlockCloseDecodedCosted_eq_semantic
    {shape : Cartesian.CartesianShape}
    {blockSize leftClose rightClose : Nat}
    (hbase :
      localBPWindowBase shape blockSize leftClose <= shape.bpCode.length)
    (hstartBase :
      localBPWindowBase shape blockSize leftClose <= leftClose + 1)
    (hrightCovered :
      rightClose + 1 <=
        localBPWindowBase shape blockSize leftClose +
          (localBPWindowBits shape blockSize leftClose).length)
    (hordered : leftClose <= rightClose) :
    (localBPSameBlockCloseDecodedCosted shape blockSize leftClose
        rightClose).erase =
      bpCandidateClose?
        (some
          (bpPrefixRangeMinExcess shape (leftClose + 1)
            (rightClose - leftClose + 1),
            bpPrefixRangeArgMinPrefixPos shape (leftClose + 1)
              (rightClose - leftClose + 1))) := by
  have hseed :
      (localBPSeedFromRankFalseCosted shape blockSize leftClose).value =
        localBPSeedExcess shape blockSize leftClose := by
    simpa [Costed.erase] using
      localBPSeedFromRankFalseCosted_eq_localBPSeedExcess
        shape blockSize leftClose hbase
  have hseeded :=
    localBPSameBlockCloseSeededCosted_eq_semantic
      (shape := shape) (blockSize := blockSize)
      (leftClose := leftClose) (rightClose := rightClose)
      hbase hstartBase hrightCovered hordered
  simpa [localBPSameBlockCloseDecodedCosted, Costed.bind, Costed.erase,
    hseed] using hseeded

theorem localBPSameBlockCloseDecodedCostedWithRankSeed_eq_semantic
    {shape : Cartesian.CartesianShape}
    {rankCloseCosted : Nat -> Costed Nat}
    {blockSize leftClose rightClose : Nat}
    (hrankExact :
      forall pos,
        (rankCloseCosted pos).erase =
          Succinct.rankPrefix false shape.bpCode pos)
    (hbase :
      localBPWindowBase shape blockSize leftClose <= shape.bpCode.length)
    (hstartBase :
      localBPWindowBase shape blockSize leftClose <= leftClose + 1)
    (hrightCovered :
      rightClose + 1 <=
        localBPWindowBase shape blockSize leftClose +
          (localBPWindowBits shape blockSize leftClose).length)
    (hordered : leftClose <= rightClose) :
    (localBPSameBlockCloseDecodedCostedWithRankSeed shape rankCloseCosted
        blockSize leftClose rightClose).erase =
      bpCandidateClose?
        (some
          (bpPrefixRangeMinExcess shape (leftClose + 1)
            (rightClose - leftClose + 1),
            bpPrefixRangeArgMinPrefixPos shape (leftClose + 1)
              (rightClose - leftClose + 1))) := by
  have hseed :
      (localBPSeedFromRankCloseCosted shape rankCloseCosted blockSize
          leftClose).value =
        localBPSeedExcess shape blockSize leftClose := by
    simpa [Costed.erase] using
      localBPSeedFromRankCloseCosted_eq_localBPSeedExcess
        shape rankCloseCosted blockSize leftClose hrankExact hbase
  have hseeded :=
    localBPSameBlockCloseSeededCosted_eq_semantic
      (shape := shape) (blockSize := blockSize)
      (leftClose := leftClose) (rightClose := rightClose)
      hbase hstartBase hrightCovered hordered
  simpa [localBPSameBlockCloseDecodedCostedWithRankSeed, Costed.bind,
    Costed.erase, hseed] using hseeded

theorem localBPSameBlockClosePrefixRange_exact
    {shape : Cartesian.CartesianShape}
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
    bpCandidateClose?
        (some
          (bpPrefixRangeMinExcess shape (leftClose + 1)
            (rightClose - leftClose + 1),
            bpPrefixRangeArgMinPrefixPos shape (leftClose + 1)
              (rightClose - leftClose + 1))) =
      some answerClose := by
  have hordered :=
    endpoint_closes_ordered_of_query_span
      (shape := shape) (left := left) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      hlen hleft hright
  have hmem :=
    answerClose_prefix_mem_endpoint_prefix_range
      (shape := shape) (left := left) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      (answerClose := answerClose)
      hlen hleft hright hanswer
  have hsemantic :=
    answerClose_prefix_leftmost_min_excess_of_query
      (shape := shape) (start := left) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      (answerClose := answerClose)
      hlen hbound hleft hright hanswer
  have hrightBound := bpCloseOfInorder?_bounds shape hright
  have hprefixBound :
      leftClose + 1 + (rightClose - leftClose + 1) <=
        shape.bpCode.length + 1 := by
    omega
  have hwitness :=
    bpPrefixRangeWitness_eq_of_leftmost_min_excess
      (shape := shape)
      (start := leftClose + 1)
      (count := rightClose - leftClose + 1)
      (target := answerClose + 1)
      hmem hprefixBound
      (by
        intro pos hlo hhi
        exact hsemantic.1 hlo (by omega))
      hsemantic.2
  rw [hwitness]
  simp [bpCandidateClose?]

theorem localBPSameBlockCloseDecodedCosted_exact
    {shape : Cartesian.CartesianShape}
    {blockSize left len leftClose rightClose answerClose : Nat}
    (hbase :
      localBPWindowBase shape blockSize leftClose <= shape.bpCode.length)
    (hstartBase :
      localBPWindowBase shape blockSize leftClose <= leftClose + 1)
    (hrightCovered :
      rightClose + 1 <=
        localBPWindowBase shape blockSize leftClose +
          (localBPWindowBits shape blockSize leftClose).length)
    (hlen : 0 < len)
    (hbound : left + len <= shape.size)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder? shape
          (scanWindow shape.representative left len) =
        some answerClose) :
    (localBPSameBlockCloseDecodedCosted shape blockSize leftClose
        rightClose).erase =
      some answerClose := by
  have hordered :=
    endpoint_closes_ordered_of_query_span
      (shape := shape) (left := left) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      hlen hleft hright
  have hdecoded :=
    localBPSameBlockCloseDecodedCosted_eq_semantic
      (shape := shape) (blockSize := blockSize)
      (leftClose := leftClose) (rightClose := rightClose)
      hbase hstartBase hrightCovered hordered
  rw [hdecoded]
  exact
    localBPSameBlockClosePrefixRange_exact
      (shape := shape) (left := left) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      (answerClose := answerClose)
      hlen hbound hleft hright hanswer

theorem localBPSameBlockCloseDecodedCostedWithRankSeed_exact
    {shape : Cartesian.CartesianShape}
    {rankCloseCosted : Nat -> Costed Nat}
    {blockSize left len leftClose rightClose answerClose : Nat}
    (hrankExact :
      forall pos,
        (rankCloseCosted pos).erase =
          Succinct.rankPrefix false shape.bpCode pos)
    (hbase :
      localBPWindowBase shape blockSize leftClose <= shape.bpCode.length)
    (hstartBase :
      localBPWindowBase shape blockSize leftClose <= leftClose + 1)
    (hrightCovered :
      rightClose + 1 <=
        localBPWindowBase shape blockSize leftClose +
          (localBPWindowBits shape blockSize leftClose).length)
    (hlen : 0 < len)
    (hbound : left + len <= shape.size)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder? shape
          (scanWindow shape.representative left len) =
        some answerClose) :
    (localBPSameBlockCloseDecodedCostedWithRankSeed shape rankCloseCosted
        blockSize leftClose rightClose).erase =
      some answerClose := by
  have hordered :=
    endpoint_closes_ordered_of_query_span
      (shape := shape) (left := left) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      hlen hleft hright
  have hdecoded :=
    localBPSameBlockCloseDecodedCostedWithRankSeed_eq_semantic
      (shape := shape) (rankCloseCosted := rankCloseCosted)
      (blockSize := blockSize)
      (leftClose := leftClose) (rightClose := rightClose)
      hrankExact hbase hstartBase hrightCovered hordered
  rw [hdecoded]
  exact
    localBPSameBlockClosePrefixRange_exact
      (shape := shape) (left := left) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      (answerClose := answerClose)
      hlen hbound hleft hright hanswer

theorem localBPSameBlockCloseDecodedCosted_exact_of_query_same_block
    {shape : Cartesian.CartesianShape}
    {blockSize left len leftClose rightClose answerClose : Nat}
    (hblockSizePos : 0 < blockSize)
    (hblockSizeLeThree :
      blockSize <=
        3 * SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hsame :
      blockOfClose blockSize leftClose =
        blockOfClose blockSize rightClose)
    (hlen : 0 < len)
    (hbound : left + len <= shape.size)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder? shape
          (scanWindow shape.representative left len) =
        some answerClose) :
    (localBPSameBlockCloseDecodedCosted shape blockSize leftClose
        rightClose).erase =
      some answerClose := by
  have hordered :=
    endpoint_closes_ordered_of_query_span
      (shape := shape) (left := left) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      hlen hleft hright
  have hleftCloseBound := bpCloseOfInorder?_bounds shape hleft
  have hrightCloseBound := bpCloseOfInorder?_bounds shape hright
  have hbaseBlock :
      localBPWindowBase shape blockSize leftClose <=
        blockStartOf blockSize (blockOfClose blockSize leftClose) :=
    localBPWindowBase_le_blockStart shape blockSize leftClose
  have hbaseClose :
      localBPWindowBase shape blockSize leftClose <= leftClose :=
    Nat.le_trans hbaseBlock blockStartOf_blockOfClose_le
  have hbaseLen :
      localBPWindowBase shape blockSize leftClose <= shape.bpCode.length := by
    omega
  have hstartBase :
      localBPWindowBase shape blockSize leftClose <= leftClose + 1 := by
    omega
  have hblockEndWidth :
      blockStartOf blockSize (blockOfClose blockSize leftClose) +
          blockSize <=
        localBPWindowBase shape blockSize leftClose +
          4 * SuccinctRankProposal.machineWordBits shape.bpCode.length :=
    localBPWindow_block_end_le_four_words shape blockSize leftClose
      hblockSizeLeThree
  have hrightInside :
      rightClose <
        blockStartOf blockSize (blockOfClose blockSize rightClose) +
          blockSize :=
    close_lt_blockStartOf_blockOfClose_add
      (blockSize := blockSize) (close := rightClose) hblockSizePos
  have hrightEndWidth :
      rightClose + 1 <=
        localBPWindowBase shape blockSize leftClose +
          4 * SuccinctRankProposal.machineWordBits shape.bpCode.length := by
    have hrightBlockStart :
        blockStartOf blockSize (blockOfClose blockSize rightClose) =
          blockStartOf blockSize (blockOfClose blockSize leftClose) := by
      rw [← hsame]
    omega
  have hrightEndLen : rightClose + 1 <= shape.bpCode.length := by
    omega
  have hrightCovered :
      rightClose + 1 <=
        localBPWindowBase shape blockSize leftClose +
          (localBPWindowBits shape blockSize leftClose).length :=
    localBPWindowBits_covers_of_le_width
      (shape := shape) (blockSize := blockSize) (close := leftClose)
      (pos := rightClose + 1)
      (by omega) hrightEndLen hrightEndWidth
  exact
    localBPSameBlockCloseDecodedCosted_exact
      (shape := shape) (blockSize := blockSize)
      (left := left) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      (answerClose := answerClose)
      hbaseLen hstartBase hrightCovered hlen hbound hleft hright hanswer

theorem localBPSameBlockCloseDecodedCostedWithRankSeed_exact_of_query_same_block
    {shape : Cartesian.CartesianShape}
    {rankCloseCosted : Nat -> Costed Nat}
    {blockSize left len leftClose rightClose answerClose : Nat}
    (hrankExact :
      forall pos,
        (rankCloseCosted pos).erase =
          Succinct.rankPrefix false shape.bpCode pos)
    (hblockSizePos : 0 < blockSize)
    (hblockSizeLeThree :
      blockSize <=
        3 * SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hsame :
      blockOfClose blockSize leftClose =
        blockOfClose blockSize rightClose)
    (hlen : 0 < len)
    (hbound : left + len <= shape.size)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder? shape
          (scanWindow shape.representative left len) =
        some answerClose) :
    (localBPSameBlockCloseDecodedCostedWithRankSeed shape rankCloseCosted
        blockSize leftClose rightClose).erase =
      some answerClose := by
  have hordered :=
    endpoint_closes_ordered_of_query_span
      (shape := shape) (left := left) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      hlen hleft hright
  have hleftCloseBound := bpCloseOfInorder?_bounds shape hleft
  have hrightCloseBound := bpCloseOfInorder?_bounds shape hright
  have hbaseBlock :
      localBPWindowBase shape blockSize leftClose <=
        blockStartOf blockSize (blockOfClose blockSize leftClose) :=
    localBPWindowBase_le_blockStart shape blockSize leftClose
  have hbaseClose :
      localBPWindowBase shape blockSize leftClose <= leftClose :=
    Nat.le_trans hbaseBlock blockStartOf_blockOfClose_le
  have hbaseLen :
      localBPWindowBase shape blockSize leftClose <= shape.bpCode.length := by
    omega
  have hstartBase :
      localBPWindowBase shape blockSize leftClose <= leftClose + 1 := by
    omega
  have hblockEndWidth :
      blockStartOf blockSize (blockOfClose blockSize leftClose) +
          blockSize <=
        localBPWindowBase shape blockSize leftClose +
          4 * SuccinctRankProposal.machineWordBits shape.bpCode.length :=
    localBPWindow_block_end_le_four_words shape blockSize leftClose
      hblockSizeLeThree
  have hrightInside :
      rightClose <
        blockStartOf blockSize (blockOfClose blockSize rightClose) +
          blockSize :=
    close_lt_blockStartOf_blockOfClose_add
      (blockSize := blockSize) (close := rightClose) hblockSizePos
  have hrightEndWidth :
      rightClose + 1 <=
        localBPWindowBase shape blockSize leftClose +
          4 * SuccinctRankProposal.machineWordBits shape.bpCode.length := by
    have hrightBlockStart :
        blockStartOf blockSize (blockOfClose blockSize rightClose) =
          blockStartOf blockSize (blockOfClose blockSize leftClose) := by
      simp [hsame]
    omega
  have hrightEndLen : rightClose + 1 <= shape.bpCode.length := by
    omega
  have hrightCovered :
      rightClose + 1 <=
        localBPWindowBase shape blockSize leftClose +
          (localBPWindowBits shape blockSize leftClose).length :=
    localBPWindowBits_covers_of_le_width
      (shape := shape) (blockSize := blockSize) (close := leftClose)
      (pos := rightClose + 1)
      (by omega) hrightEndLen hrightEndWidth
  exact
    localBPSameBlockCloseDecodedCostedWithRankSeed_exact
      (shape := shape) (rankCloseCosted := rankCloseCosted)
      (blockSize := blockSize) (left := left) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      (answerClose := answerClose)
      hrankExact hbaseLen hstartBase hrightCovered hlen hbound
      hleft hright hanswer

def localBPSameBlockCloseCosted
    (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) : Costed (Option Nat) :=
  let left := closeToInorder shape leftClose
  let right := closeToInorder shape rightClose
  { value :=
      if left <= right then
        bpCloseOfInorder? shape
          (scanWindow shape.representative left (right - left + 1))
      else
        none
    cost := 4 }

theorem localBPSameBlockCloseCosted_cost_le
    (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) :
    (localBPSameBlockCloseCosted shape leftClose rightClose).cost <= 4 := by
  simp [localBPSameBlockCloseCosted]

theorem localBPSameBlockCloseCosted_exact
    {shape : Cartesian.CartesianShape}
    {left len leftClose rightClose answerClose : Nat}
    (hlen : 0 < len)
    (_hbound : left + len <= shape.size)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder? shape
          (scanWindow shape.representative left len) =
        some answerClose) :
    (localBPSameBlockCloseCosted shape leftClose rightClose).erase =
      some answerClose := by
  have hleftIdx := closeToInorder_eq_of_bpCloseOfInorder? hleft
  have hrightIdx := closeToInorder_eq_of_bpCloseOfInorder? hright
  have hle :
      closeToInorder shape leftClose <=
        closeToInorder shape rightClose := by
    omega
  have hlenEq :
      closeToInorder shape rightClose -
          closeToInorder shape leftClose + 1 =
        len := by
    omega
  unfold localBPSameBlockCloseCosted
  change
    (if closeToInorder shape leftClose <=
          closeToInorder shape rightClose then
        bpCloseOfInorder? shape
          (scanWindow shape.representative
            (closeToInorder shape leftClose)
            (closeToInorder shape rightClose -
              closeToInorder shape leftClose + 1))
      else
        none) = some answerClose
  rw [if_pos hle]
  rw [hleftIdx, hrightIdx]
  have hlenEq' : left + len - 1 - left + 1 = len := by
    omega
  rw [hlenEq']
  exact hanswer

def localBPLeftFringeCandidateCosted
    (shape : Cartesian.CartesianShape)
    (blockSize leftClose : Nat) : Costed (Option (Nat × Nat)) :=
  { value :=
      some
        (bpPrefixRangeMinExcess shape (leftClose + 1)
          (blockStartOf blockSize (blockOfClose blockSize leftClose) +
            blockSize - leftClose),
          bpPrefixRangeArgMinPrefixPos shape (leftClose + 1)
            (blockStartOf blockSize (blockOfClose blockSize leftClose) +
              blockSize - leftClose))
    cost := 4 }

def localBPRightFringeCandidateCosted
    (shape : Cartesian.CartesianShape)
    (blockSize rightClose : Nat) : Costed (Option (Nat × Nat)) :=
  { value :=
      some
        (bpPrefixRangeMinExcess shape
          (blockStartOf blockSize (blockOfClose blockSize rightClose))
          (rightClose -
              blockStartOf blockSize (blockOfClose blockSize rightClose) +
            2),
          bpPrefixRangeArgMinPrefixPos shape
            (blockStartOf blockSize (blockOfClose blockSize rightClose))
            (rightClose -
                blockStartOf blockSize (blockOfClose blockSize rightClose) +
              2))
    cost := 4 }

theorem localBPLeftFringeCandidateSeededCosted_eq_semantic
    {shape : Cartesian.CartesianShape}
    {blockSize leftClose : Nat}
    (hbase :
      localBPWindowBase shape blockSize leftClose <= shape.bpCode.length)
    (hstartBase :
      localBPWindowBase shape blockSize leftClose <= leftClose + 1)
    (hendCovered :
      blockStartOf blockSize (blockOfClose blockSize leftClose) +
          blockSize <=
        localBPWindowBase shape blockSize leftClose +
          (localBPWindowBits shape blockSize leftClose).length)
    (hleftInside :
      leftClose <
        blockStartOf blockSize (blockOfClose blockSize leftClose) +
          blockSize) :
    (localBPLeftFringeCandidateSeededCosted shape blockSize leftClose
        (localBPSeedExcess shape blockSize leftClose)).erase =
      (localBPLeftFringeCandidateCosted shape blockSize leftClose).erase := by
  let start := leftClose + 1
  let count :=
    blockStartOf blockSize (blockOfClose blockSize leftClose) +
      blockSize - leftClose
  have hcount : 0 < count := by
    simp [count]
    omega
  have hcovered :
      start + count <=
        localBPWindowBase shape blockSize leftClose +
          (localBPWindowBits shape blockSize leftClose).length + 1 := by
    simp [start, count]
    omega
  have hmin :=
    localBPSeededPrefixRangeMinExcess_eq_bpPrefixRangeMinExcess_of_pos
      (shape := shape) (blockSize := blockSize) (close := leftClose)
      (start := start) (count := count)
      hcount hbase (by simpa [start] using hstartBase) hcovered
  have harg :=
    localBPSeededPrefixRangeArgMinPrefixPos_eq_bpPrefixRangeArgMinPrefixPos_of_pos
      (shape := shape) (blockSize := blockSize) (close := leftClose)
      (start := start) (count := count)
      hcount hbase (by simpa [start] using hstartBase) hcovered
  simp [localBPLeftFringeCandidateSeededCosted,
    localBPLeftFringeCandidateCosted, start, count, hmin, harg]

theorem localBPRightFringeCandidateSeededCosted_eq_semantic
    {shape : Cartesian.CartesianShape}
    {blockSize rightClose : Nat}
    (hbase :
      localBPWindowBase shape blockSize rightClose <= shape.bpCode.length)
    (hstartBase :
      localBPWindowBase shape blockSize rightClose <=
        blockStartOf blockSize (blockOfClose blockSize rightClose))
    (hrightInside :
      blockStartOf blockSize (blockOfClose blockSize rightClose) <=
        rightClose)
    (hendCovered :
      rightClose + 1 <=
        localBPWindowBase shape blockSize rightClose +
          (localBPWindowBits shape blockSize rightClose).length) :
    (localBPRightFringeCandidateSeededCosted shape blockSize rightClose
        (localBPSeedExcess shape blockSize rightClose)).erase =
      (localBPRightFringeCandidateCosted shape blockSize rightClose).erase := by
  let start := blockStartOf blockSize (blockOfClose blockSize rightClose)
  let count := rightClose - start + 2
  have hcount : 0 < count := by
    simp [count]
  have hcovered :
      start + count <=
        localBPWindowBase shape blockSize rightClose +
          (localBPWindowBits shape blockSize rightClose).length + 1 := by
    simp [start, count]
    omega
  have hmin :=
    localBPSeededPrefixRangeMinExcess_eq_bpPrefixRangeMinExcess_of_pos
      (shape := shape) (blockSize := blockSize) (close := rightClose)
      (start := start) (count := count)
      hcount hbase (by simpa [start] using hstartBase) hcovered
  have harg :=
    localBPSeededPrefixRangeArgMinPrefixPos_eq_bpPrefixRangeArgMinPrefixPos_of_pos
      (shape := shape) (blockSize := blockSize) (close := rightClose)
      (start := start) (count := count)
      hcount hbase (by simpa [start] using hstartBase) hcovered
  simp [localBPRightFringeCandidateSeededCosted,
    localBPRightFringeCandidateCosted, start, count, hmin, harg]

theorem localBPLeftFringeCandidateCosted_cost_le
    (shape : Cartesian.CartesianShape)
    (blockSize leftClose : Nat) :
    (localBPLeftFringeCandidateCosted shape blockSize leftClose).cost <=
      4 := by
  simp [localBPLeftFringeCandidateCosted]

theorem localBPRightFringeCandidateCosted_cost_le
    (shape : Cartesian.CartesianShape)
    (blockSize rightClose : Nat) :
    (localBPRightFringeCandidateCosted shape blockSize rightClose).cost <=
      4 := by
  simp [localBPRightFringeCandidateCosted]

theorem bpRelativeRmmCandidateMerge_exact_of_query_semantics_no_block_bounds
    {shape : Cartesian.CartesianShape}
    {blockSize left len leftClose rightClose answerClose : Nat}
    (hlen : 0 < len)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder? shape
          (scanWindow shape.representative left len) =
        some answerClose)
    (hblockSize : 0 < blockSize)
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
    bpCandidateMerge3?
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
                2))) =
      some (bpExcessAt shape (answerClose + 1), answerClose + 1) := by
  let blockCount :=
    Nat.max (blockOfClose blockSize leftClose)
      (blockOfClose blockSize rightClose) + 1
  have hleftBlock :
      blockOfClose blockSize leftClose < blockCount := by
    dsimp [blockCount]
    exact Nat.lt_succ_of_le (Nat.le_max_left _ _)
  have hrightBlock :
      blockOfClose blockSize rightClose < blockCount := by
    dsimp [blockCount]
    exact Nat.lt_succ_of_le (Nat.le_max_right _ _)
  exact
    bpRelativeRmmCandidateMerge_exact_of_query_semantics
      (shape := shape) (blockSize := blockSize) (blockCount := blockCount)
      (left := left) (len := len) (leftClose := leftClose)
      (rightClose := rightClose) (answerClose := answerClose)
      hlen hleft hright hanswer hblockSize hleftBlock hrightBlock
      hcross hmin hleftmost

theorem canonicalBPRelativeSummaryBlockCountRaw_upper_cover
    (shape : Cartesian.CartesianShape) :
    shape.bpCode.length <
      (canonicalBPRelativeSummaryBlockCountRaw shape + 1) *
        canonicalBPRelativeSummaryBlockSizeRaw shape := by
  let base := canonicalBPRelativeSummaryBase shape
  have hbase : 0 < base := by
    simp [base, canonicalBPRelativeSummaryBase]
  have hlt := Nat.lt_div_mul_add hbase (a := shape.size)
  rw [Cartesian.CartesianShape.bpCode_length]
  calc
    2 * shape.size < 2 * ((shape.size / base) * base + base) :=
      Nat.mul_lt_mul_of_pos_left hlt (by omega)
    _ = 2 * ((shape.size / base + 1) * base) := by
      congr 1
      rw [Nat.add_mul, Nat.one_mul]
    _ = (shape.size / base + 1) * (2 * base) := by
      simp [Nat.mul_assoc, Nat.mul_comm]

theorem canonicalBPRelativeSummary_blockOfClose_le_blockCount_of_active
    {shape : Cartesian.CartesianShape}
    (hactive : canonicalBPRelativeMinMaxArgSummaryTableActive shape)
    {close : Nat}
    (hclose : close < shape.bpCode.length) :
    blockOfClose (canonicalBPRelativeSummaryBlockSize shape) close <=
      canonicalBPRelativeSummaryBlockCount shape := by
  have hblockSizePos :
      0 < canonicalBPRelativeSummaryBlockSizeRaw shape :=
    canonicalBPRelativeSummaryBlockSizeRaw_pos shape
  have hupper :=
    canonicalBPRelativeSummaryBlockCountRaw_upper_cover shape
  have hcloseUpper :
      close <
        (canonicalBPRelativeSummaryBlockCountRaw shape + 1) *
          canonicalBPRelativeSummaryBlockSizeRaw shape :=
    Nat.lt_trans hclose hupper
  have hdiv :
      close / canonicalBPRelativeSummaryBlockSizeRaw shape <
        canonicalBPRelativeSummaryBlockCountRaw shape + 1 := by
    exact (Nat.div_lt_iff_lt_mul hblockSizePos).2 hcloseUpper
  have hleRaw :
      close / canonicalBPRelativeSummaryBlockSizeRaw shape <=
        canonicalBPRelativeSummaryBlockCountRaw shape := by
    omega
  simpa [blockOfClose, canonicalBPRelativeSummaryBlockSize,
    canonicalBPRelativeSummaryBlockCount, hactive] using hleRaw

theorem canonicalBPRelativeSummary_blockOfClose_le_blockCount_of_large
    {shape : Cartesian.CartesianShape}
    (hlarge : canonicalBPRelativeSummaryLargeRegime shape)
    {close : Nat}
    (hclose : close < shape.bpCode.length) :
    blockOfClose (canonicalBPRelativeSummaryBlockSize shape) close <=
      canonicalBPRelativeSummaryBlockCount shape := by
  exact
    canonicalBPRelativeSummary_blockOfClose_le_blockCount_of_active
      (canonicalBPRelativeMinMaxArgSummaryTableActive_of_large
        (shape := shape) hlarge)
      hclose

theorem cartesianShape_shapeOfSize_self
    (shape : Cartesian.CartesianShape) :
    Cartesian.ShapeOfSize shape.size shape := by
  induction shape with
  | empty =>
      exact Cartesian.ShapeOfSize.empty
  | node left right ihleft ihright =>
      simpa [Cartesian.CartesianShape.size] using
        Cartesian.ShapeOfSize.node ihleft ihright

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

/--
Guarded macro/micro close directory using a relative-rmM cross-block macro.

This is the positive C2 query surface that avoids dense interior block-pair
payloads.  Same-block queries use the existing payload-live micro codebook;
cross-block queries use the relative-rmM macro component.
-/
structure PayloadLiveRelativeRmmMacroMicroBPCloseLCADirectory
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead relativeOverhead middleQueryCost : Nat) where
  micro :
    PayloadLiveBlockMicroCodebook shape blockSize blockCount codeCount
      codeWidth codeOverhead microTableOverhead
  macroComponent :
    PayloadLiveRelativeRmmBPCloseMacro shape blockSize blockCount
      relativeOverhead middleQueryCost
  blockSize_pos : 0 < blockSize
  close_block_lt :
    forall {close : Nat},
      close < shape.bpCode.length ->
        blockOfClose blockSize close < blockCount

namespace PayloadLiveRelativeRmmMacroMicroBPCloseLCADirectory

def payload
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead relativeOverhead middleQueryCost : Nat}
    (directory :
      PayloadLiveRelativeRmmMacroMicroBPCloseLCADirectory
        shape blockSize blockCount codeCount codeWidth codeOverhead
        microTableOverhead relativeOverhead middleQueryCost) : List Bool :=
  directory.micro.payload ++ directory.macroComponent.payload

def lcaCloseCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead relativeOverhead middleQueryCost : Nat}
    (directory :
      PayloadLiveRelativeRmmMacroMicroBPCloseLCADirectory
        shape blockSize blockCount codeCount codeWidth codeOverhead
        microTableOverhead relativeOverhead middleQueryCost)
    (leftClose rightClose : Nat) :
    Costed (Option Nat) :=
  if blockOfClose blockSize leftClose =
      blockOfClose blockSize rightClose then
    directory.micro.lcaCloseCosted leftClose rightClose
  else
    directory.macroComponent.lcaCloseCosted leftClose rightClose

theorem payload_length
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead relativeOverhead middleQueryCost : Nat}
    (directory :
      PayloadLiveRelativeRmmMacroMicroBPCloseLCADirectory
        shape blockSize blockCount codeCount codeWidth codeOverhead
        microTableOverhead relativeOverhead middleQueryCost) :
    directory.payload.length =
      codeOverhead + codeCount * microTableOverhead + relativeOverhead := by
  simp [payload, directory.micro.payload_length,
    directory.macroComponent.payload_length]

theorem lcaCloseCosted_cost_le
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead relativeOverhead middleQueryCost : Nat}
    (directory :
      PayloadLiveRelativeRmmMacroMicroBPCloseLCADirectory
        shape blockSize blockCount codeCount codeWidth codeOverhead
        microTableOverhead relativeOverhead middleQueryCost)
    (leftClose rightClose : Nat) :
    (directory.lcaCloseCosted leftClose rightClose).cost <=
      4 + middleQueryCost := by
  unfold lcaCloseCosted
  by_cases hsame :
      blockOfClose blockSize leftClose =
        blockOfClose blockSize rightClose
  · simp [hsame]
    have hmicro := directory.micro.lcaCloseCosted_cost_le_two
      leftClose rightClose
    omega
  · simp [hsame]
    exact directory.macroComponent.lcaCloseCosted_cost_le
      leftClose rightClose

theorem lcaCloseCosted_exact
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead relativeOverhead middleQueryCost : Nat}
    (directory :
      PayloadLiveRelativeRmmMacroMicroBPCloseLCADirectory
        shape blockSize blockCount codeCount codeWidth codeOverhead
        microTableOverhead relativeOverhead middleQueryCost)
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
  have hleftCloseBound := bpCloseOfInorder?_bounds shape hleft
  have hrightCloseBound := bpCloseOfInorder?_bounds shape hright
  have hleftBlock :
      blockOfClose blockSize leftClose < blockCount :=
    directory.close_block_lt hleftCloseBound
  have hrightBlock :
      blockOfClose blockSize rightClose < blockCount :=
    directory.close_block_lt hrightCloseBound
  have hbetween :=
    answerClose_between_endpoint_closes
      (shape := shape) (left := left) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      (answerClose := answerClose)
      hlen hleft hright hanswer
  unfold lcaCloseCosted
  by_cases hsame :
      blockOfClose blockSize leftClose =
        blockOfClose blockSize rightClose
  · simp [hsame]
    rcases directory.micro.classifier.codeAt_exists_of_lt hleftBlock with
      ⟨code, hcodeAt⟩
    have hrightLo :
        blockStartOf blockSize (blockOfClose blockSize leftClose) <=
          rightClose := by
      simpa [hsame] using
        (blockStartOf_blockOfClose_le
          (blockSize := blockSize) (close := rightClose))
    have hrightHi :
        rightClose <
          blockStartOf blockSize (blockOfClose blockSize leftClose) +
            blockSize := by
      simpa [hsame] using
        (close_lt_blockStartOf_blockOfClose_add
          (blockSize := blockSize) (close := rightClose)
          directory.blockSize_pos)
    have hanswerLo :
        blockStartOf blockSize (blockOfClose blockSize leftClose) <=
          answerClose := by
      exact Nat.le_trans blockStartOf_blockOfClose_le hbetween.1
    have hanswerHi :
        answerClose <
          blockStartOf blockSize (blockOfClose blockSize leftClose) +
            blockSize := by
      exact Nat.lt_of_le_of_lt hbetween.2 hrightHi
    exact
      directory.micro.lcaCloseCosted_exact_of_left_block
        directory.blockSize_pos hcodeAt hlen hbound hleft hright hanswer
        hrightLo hrightHi hanswerLo hanswerHi
  · simp [hsame]
    have hleftRight : leftClose <= rightClose := by
      omega
    have hblockLe :
        blockOfClose blockSize leftClose <=
          blockOfClose blockSize rightClose := by
      unfold blockOfClose
      exact Nat.div_le_div_right hleftRight
    have hcross :
        blockOfClose blockSize leftClose <
          blockOfClose blockSize rightClose := by
      omega
    exact
      directory.macroComponent.lcaCloseCosted_exact_of_query_cross_block
        hlen hbound hleft hright hanswer directory.blockSize_pos
        hleftBlock hrightBlock hcross

theorem profile
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead relativeOverhead middleQueryCost : Nat}
    (directory :
      PayloadLiveRelativeRmmMacroMicroBPCloseLCADirectory
        shape blockSize blockCount codeCount codeWidth codeOverhead
        microTableOverhead relativeOverhead middleQueryCost) :
    directory.payload.length =
        codeOverhead + codeCount * microTableOverhead + relativeOverhead /\
      (forall leftClose rightClose,
        (directory.lcaCloseCosted leftClose rightClose).cost <=
          4 + middleQueryCost) /\
      forall {left len leftClose rightClose answerClose : Nat},
        0 < len ->
          left + len <= shape.size ->
            bpCloseOfInorder? shape left = some leftClose ->
              bpCloseOfInorder? shape (left + len - 1) =
                  some rightClose ->
                bpCloseOfInorder? shape
                    (scanWindow shape.representative left len) =
                  some answerClose ->
                  (directory.lcaCloseCosted leftClose rightClose).erase =
                    some answerClose := by
  constructor
  · exact directory.payload_length
  constructor
  · intro leftClose rightClose
    exact directory.lcaCloseCosted_cost_le leftClose rightClose
  intro left len leftClose rightClose answerClose hlen hbound hleft
    hright hanswer
  exact directory.lcaCloseCosted_exact hlen hbound hleft hright hanswer

end PayloadLiveRelativeRmmMacroMicroBPCloseLCADirectory

def relativeRmmMacroMicroBPCloseLCAOverhead
    (microOverhead relativeOverhead : Nat -> Nat) (n : Nat) : Nat :=
  microOverhead n + relativeOverhead n

theorem relativeRmmMacroMicroBPCloseLCAOverhead_littleO
    {microOverhead relativeOverhead : Nat -> Nat}
    (hmicro : LittleOLinear microOverhead)
    (hrelative : LittleOLinear relativeOverhead) :
    LittleOLinear
      (relativeRmmMacroMicroBPCloseLCAOverhead
        microOverhead relativeOverhead) := by
  unfold relativeRmmMacroMicroBPCloseLCAOverhead
  exact hmicro.add hrelative

theorem relativeRmmMacroMicroBPCloseLCADirectory_profile
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead relativeOverhead middleQueryCost n : Nat)
    (microBudget relativeBudget : Nat -> Nat)
    (directory :
      PayloadLiveRelativeRmmMacroMicroBPCloseLCADirectory
        shape blockSize blockCount codeCount codeWidth codeOverhead
        microTableOverhead relativeOverhead middleQueryCost)
    (hmicroLittle : LittleOLinear microBudget)
    (hrelativeLittle : LittleOLinear relativeBudget)
    (hmicroBudget :
      codeOverhead + codeCount * microTableOverhead <= microBudget n)
    (hrelativeBudget : relativeOverhead <= relativeBudget n) :
    LittleOLinear
        (relativeRmmMacroMicroBPCloseLCAOverhead
          microBudget relativeBudget) /\
      directory.payload.length <=
        relativeRmmMacroMicroBPCloseLCAOverhead
          microBudget relativeBudget n /\
      (forall leftClose rightClose,
        (directory.lcaCloseCosted leftClose rightClose).cost <=
          4 + middleQueryCost) /\
      forall {left len leftClose rightClose answerClose : Nat},
        0 < len ->
          left + len <= shape.size ->
            bpCloseOfInorder? shape left = some leftClose ->
              bpCloseOfInorder? shape (left + len - 1) =
                  some rightClose ->
                bpCloseOfInorder? shape
                    (scanWindow shape.representative left len) =
                  some answerClose ->
                  (directory.lcaCloseCosted leftClose rightClose).erase =
                    some answerClose := by
  have hprofile := directory.profile
  constructor
  · exact relativeRmmMacroMicroBPCloseLCAOverhead_littleO
      hmicroLittle hrelativeLittle
  constructor
  · rw [hprofile.1]
    unfold relativeRmmMacroMicroBPCloseLCAOverhead
    omega
  constructor
  · exact hprofile.2.1
  · exact hprofile.2.2

/--
Concrete dense fallback instance for the payload-live macro/micro surface.

The micro phase is the charged empty classifier above, and the macro phase is
the dense all-close table.  This construction is exact and constant-cost, but
`denseAllCloseBPCloseLCAOverhead_not_littleO` shows why it is only a blocker
baseline, not the final succinct macro.
-/
def denseFallbackPayloadLiveMacroMicroBPCloseLCADirectory
    (shape : Cartesian.CartesianShape)
    (blockSize fieldWidth : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth) :
    PayloadLiveMacroMicroBPCloseLCADirectory shape blockSize 0 1 0 0 0
      ((shape.bpCode.length * shape.bpCode.length) *
        optionNatWordWidth fieldWidth) 1 where
  micro := emptyPayloadLiveBlockMicroCodebook shape blockSize fieldWidth
  macroPayload :=
    (denseAllCloseBPCloseLCATable shape fieldWidth hwidth).payload
  macroPayload_length_eq := by
    exact
      (denseAllCloseBPCloseLCATable
        shape fieldWidth hwidth).payload_length
  macroCosted :=
    (denseAllCloseBPCloseLCATable shape fieldWidth hwidth).lcaCloseCosted
  macro_cost_le := by
    intro leftClose rightClose
    exact
      (denseAllCloseBPCloseLCATable
        shape fieldWidth hwidth).lcaCloseCosted_cost_le_one
          leftClose rightClose
  split_exact := by
    intro left len leftClose rightClose answerClose
      hlen hbound hleft hright hanswer
    right
    constructor
    · exact
        emptyPayloadLiveBlockMicroCodebook_lcaCloseCosted_erase
          shape blockSize fieldWidth leftClose rightClose
    · exact
        (denseAllCloseBPCloseLCATable_profile
          shape fieldWidth hwidth).2.2 hlen hbound hleft hright hanswer

theorem denseFallbackPayloadLiveMacroMicroBPCloseLCADirectory_profile
    (shape : Cartesian.CartesianShape)
    (blockSize fieldWidth : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth) :
    ((denseFallbackPayloadLiveMacroMicroBPCloseLCADirectory
        shape blockSize fieldWidth hwidth).payload.length =
        (shape.bpCode.length * shape.bpCode.length) *
          optionNatWordWidth fieldWidth) /\
      (forall leftClose rightClose,
        ((denseFallbackPayloadLiveMacroMicroBPCloseLCADirectory
          shape blockSize fieldWidth hwidth).lcaCloseCosted
            leftClose rightClose).cost <= 3) /\
      forall {left len leftClose rightClose answerClose : Nat},
        0 < len ->
          left + len <= shape.size ->
            bpCloseOfInorder? shape left = some leftClose ->
              bpCloseOfInorder? shape (left + len - 1) =
                  some rightClose ->
                bpCloseOfInorder? shape
                    (scanWindow shape.representative left len) =
                  some answerClose ->
                  ((denseFallbackPayloadLiveMacroMicroBPCloseLCADirectory
                    shape blockSize fieldWidth hwidth).lcaCloseCosted
                      leftClose rightClose).erase =
                    some answerClose := by
  have hprofile :=
    (denseFallbackPayloadLiveMacroMicroBPCloseLCADirectory
      shape blockSize fieldWidth hwidth).profile
  constructor
  · simpa using hprofile.1
  constructor
  · intro leftClose rightClose
    have hcost := hprofile.2.1 leftClose rightClose
    simpa using hcost
  · intro left len leftClose rightClose answerClose
      hlen hbound hleft hright hanswer
    exact hprofile.2.2 hlen hbound hleft hright hanswer

def payloadLiveMacroMicroBPCloseLCAOverhead
    (codeOverhead codeCount microTableOverhead macroOverhead : Nat -> Nat)
    (n : Nat) : Nat :=
  codeOverhead n + codeCount n * microTableOverhead n + macroOverhead n

theorem payloadLiveMacroMicroBPCloseLCAOverhead_littleO
    {codeOverhead codeCount microTableOverhead macroOverhead : Nat -> Nat}
    (hcode : LittleOLinear codeOverhead)
    (hcodebook :
      LittleOLinear (fun n => codeCount n * microTableOverhead n))
    (hmacro : LittleOLinear macroOverhead) :
    LittleOLinear
      (payloadLiveMacroMicroBPCloseLCAOverhead
        codeOverhead codeCount microTableOverhead macroOverhead) := by
  unfold payloadLiveMacroMicroBPCloseLCAOverhead
  exact (hcode.add hcodebook).add hmacro

/--
Family-level macro/micro close-LCA interface.

The code classifier overhead, finite codebook overhead, and macro overhead are
separate LittleOLinear obligations.  This avoids proving a final RMQ theorem
from a dense per-block table while still pinning the exact payload read by the
close/LCA primitive.
-/
structure PayloadLiveMacroMicroBPCloseLCAFamily
    (codeOverhead codeCount microTableOverhead macroOverhead : Nat -> Nat)
    (queryCost : Nat) where
  blockSize : Nat -> Nat
  blockCount : Nat -> Nat
  codeWidth : Nat -> Nat
  macroCost : Nat -> Nat
  directory :
    forall {n : Nat} (shape : Cartesian.CartesianShape),
      List.Mem shape (Cartesian.shapesOfSize n) ->
        PayloadLiveMacroMicroBPCloseLCADirectory shape
          (blockSize n) (blockCount n) (codeCount n) (codeWidth n)
          (codeOverhead n) (microTableOverhead n) (macroOverhead n)
          (macroCost n)
  code_littleO : LittleOLinear codeOverhead
  codebook_littleO :
    LittleOLinear (fun n => codeCount n * microTableOverhead n)
  macro_littleO : LittleOLinear macroOverhead
  macro_cost_le_query : forall n : Nat, 2 + macroCost n <= queryCost

namespace PayloadLiveMacroMicroBPCloseLCAFamily

def overhead
    {codeOverhead codeCount microTableOverhead macroOverhead : Nat -> Nat}
    {queryCost : Nat}
    (_family :
      PayloadLiveMacroMicroBPCloseLCAFamily codeOverhead codeCount
        microTableOverhead macroOverhead queryCost) : Nat -> Nat :=
  payloadLiveMacroMicroBPCloseLCAOverhead
    codeOverhead codeCount microTableOverhead macroOverhead

theorem overhead_littleO
    {codeOverhead codeCount microTableOverhead macroOverhead : Nat -> Nat}
    {queryCost : Nat}
    (family :
      PayloadLiveMacroMicroBPCloseLCAFamily codeOverhead codeCount
        microTableOverhead macroOverhead queryCost) :
    LittleOLinear family.overhead := by
  exact
    payloadLiveMacroMicroBPCloseLCAOverhead_littleO
      family.code_littleO family.codebook_littleO family.macro_littleO

def Profile
    {codeOverhead codeCount microTableOverhead macroOverhead : Nat -> Nat}
    {queryCost : Nat}
    (family :
      PayloadLiveMacroMicroBPCloseLCAFamily codeOverhead codeCount
        microTableOverhead macroOverhead queryCost) : Prop :=
  LittleOLinear family.overhead /\
    forall n : Nat,
      forall {shape : Cartesian.CartesianShape},
        (hshape : List.Mem shape (Cartesian.shapesOfSize n)) ->
          ((family.directory (n := n) shape hshape).payload.length =
              family.overhead n) /\
            (forall leftClose rightClose,
              ((family.directory (n := n) shape hshape).lcaCloseCosted
                    leftClose rightClose).cost <= queryCost) /\
            forall {left len leftClose rightClose answerClose : Nat},
              0 < len ->
                left + len <= shape.size ->
                  bpCloseOfInorder? shape left = some leftClose ->
                    bpCloseOfInorder? shape (left + len - 1) =
                        some rightClose ->
                      bpCloseOfInorder? shape
                          (scanWindow shape.representative left len) =
                        some answerClose ->
                        ((family.directory (n := n) shape hshape).lcaCloseCosted
                              leftClose rightClose).erase =
                          some answerClose

theorem profile
    {codeOverhead codeCount microTableOverhead macroOverhead : Nat -> Nat}
    {queryCost : Nat}
    (family :
      PayloadLiveMacroMicroBPCloseLCAFamily codeOverhead codeCount
        microTableOverhead macroOverhead queryCost) :
    family.Profile := by
  constructor
  · exact family.overhead_littleO
  intro n shape hshape
  let directory := family.directory (n := n) shape hshape
  have hdirProfile := directory.profile
  constructor
  · simpa [directory, overhead,
      payloadLiveMacroMicroBPCloseLCAOverhead] using hdirProfile.1
  constructor
  · intro leftClose rightClose
    have hcost := hdirProfile.2.1 leftClose rightClose
    have hbudget := family.macro_cost_le_query n
    simpa [directory] using Nat.le_trans hcost hbudget
  intro left len leftClose rightClose answerClose hlen hbound hleft
    hright hanswer
  exact hdirProfile.2.2 hlen hbound hleft hright hanswer

end PayloadLiveMacroMicroBPCloseLCAFamily

/--
Overhead for the built-query BP close-navigation join that uses payload-live
rank/select plus the payload-live macro/micro BP close-LCA directory.
-/
def payloadLiveMacroMicroBPCloseNavigationOverhead
    (rankOverhead selectOverhead codeOverhead codeCount
      microTableOverhead macroOverhead : Nat -> Nat)
    (n : Nat) : Nat :=
  rankOverhead n + selectOverhead n +
    payloadLiveMacroMicroBPCloseLCAOverhead
      codeOverhead codeCount microTableOverhead macroOverhead n

theorem payloadLiveMacroMicroBPCloseNavigationOverhead_littleO
    {rankOverhead selectOverhead codeOverhead codeCount
      microTableOverhead macroOverhead : Nat -> Nat}
    (hrank : LittleOLinear rankOverhead)
    (hselect : LittleOLinear selectOverhead)
    (hlca :
      LittleOLinear
        (payloadLiveMacroMicroBPCloseLCAOverhead
          codeOverhead codeCount microTableOverhead macroOverhead)) :
    LittleOLinear
      (payloadLiveMacroMicroBPCloseNavigationOverhead
        rankOverhead selectOverhead codeOverhead codeCount
        microTableOverhead macroOverhead) := by
  unfold payloadLiveMacroMicroBPCloseNavigationOverhead
  exact (hrank.add hselect).add hlca

/--
Built-query BP close-navigation family using the payload-live macro/micro
close-LCA component.

This is the cost-parametric join layer: select-close and rank-close are the
existing payload-live rank/select reads, while the LCA leg is the
`PayloadLiveMacroMicroBPCloseLCAFamily` with its exposed `lcaQueryCost`.
-/
structure PayloadLiveMacroMicroBPCloseNavigationFamily
    (rankOverhead selectOverhead codeOverhead codeCount
      microTableOverhead macroOverhead : Nat -> Nat)
    (lcaQueryCost : Nat) where
  lcaFamily :
    PayloadLiveMacroMicroBPCloseLCAFamily codeOverhead codeCount
      microTableOverhead macroOverhead lcaQueryCost
  rankData :
    forall {n : Nat} (shape : Cartesian.CartesianShape),
      List.Mem shape (Cartesian.shapesOfSize n) ->
        PayloadLiveStoredWordRankData shape.bpCode (rankOverhead n)
  selectData :
    forall {n : Nat} (shape : Cartesian.CartesianShape),
      List.Mem shape (Cartesian.shapesOfSize n) ->
        PayloadLiveStoredWordSelectData shape.bpCode (selectOverhead n)
  rank_littleO : LittleOLinear rankOverhead
  select_littleO : LittleOLinear selectOverhead

namespace PayloadLiveMacroMicroBPCloseNavigationFamily

def overhead
    {rankOverhead selectOverhead codeOverhead codeCount
      microTableOverhead macroOverhead : Nat -> Nat}
    {lcaQueryCost : Nat}
    (_family :
      PayloadLiveMacroMicroBPCloseNavigationFamily
        rankOverhead selectOverhead codeOverhead codeCount
        microTableOverhead macroOverhead lcaQueryCost) : Nat -> Nat :=
  payloadLiveMacroMicroBPCloseNavigationOverhead
    rankOverhead selectOverhead codeOverhead codeCount
    microTableOverhead macroOverhead

def payload
    {rankOverhead selectOverhead codeOverhead codeCount
      microTableOverhead macroOverhead : Nat -> Nat}
    {lcaQueryCost n : Nat}
    (family :
      PayloadLiveMacroMicroBPCloseNavigationFamily
        rankOverhead selectOverhead codeOverhead codeCount
        microTableOverhead macroOverhead lcaQueryCost)
    (shape : Cartesian.CartesianShape)
    (hshape : List.Mem shape (Cartesian.shapesOfSize n)) : List Bool :=
  shape.bpCode ++
    (family.rankData shape hshape).auxPayload ++
      (family.selectData shape hshape).auxPayload ++
        (family.lcaFamily.directory (n := n) shape hshape).payload

def selectCloseCosted
    {rankOverhead selectOverhead codeOverhead codeCount
      microTableOverhead macroOverhead : Nat -> Nat}
    {lcaQueryCost n : Nat}
    (family :
      PayloadLiveMacroMicroBPCloseNavigationFamily
        rankOverhead selectOverhead codeOverhead codeCount
        microTableOverhead macroOverhead lcaQueryCost)
    (shape : Cartesian.CartesianShape)
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    (idx : Nat) : Costed (Option Nat) :=
  (family.selectData shape hshape).selectCosted false idx

def lcaCloseCosted
    {rankOverhead selectOverhead codeOverhead codeCount
      microTableOverhead macroOverhead : Nat -> Nat}
    {lcaQueryCost n : Nat}
    (family :
      PayloadLiveMacroMicroBPCloseNavigationFamily
        rankOverhead selectOverhead codeOverhead codeCount
        microTableOverhead macroOverhead lcaQueryCost)
    (shape : Cartesian.CartesianShape)
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    (leftClose rightClose : Nat) : Costed (Option Nat) :=
  (family.lcaFamily.directory (n := n) shape hshape).lcaCloseCosted
    leftClose rightClose

def rankCloseCosted
    {rankOverhead selectOverhead codeOverhead codeCount
      microTableOverhead macroOverhead : Nat -> Nat}
    {lcaQueryCost n : Nat}
    (family :
      PayloadLiveMacroMicroBPCloseNavigationFamily
        rankOverhead selectOverhead codeOverhead codeCount
        microTableOverhead macroOverhead lcaQueryCost)
    (shape : Cartesian.CartesianShape)
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    (pos : Nat) : Costed Nat :=
  (family.rankData shape hshape).rankCostedClamped false pos

def queryBuiltCosted
    {rankOverhead selectOverhead codeOverhead codeCount
      microTableOverhead macroOverhead : Nat -> Nat}
    {lcaQueryCost n : Nat}
    (family :
      PayloadLiveMacroMicroBPCloseNavigationFamily
        rankOverhead selectOverhead codeOverhead codeCount
        microTableOverhead macroOverhead lcaQueryCost)
    (shape : Cartesian.CartesianShape)
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    (left right : Nat) : Costed (Option Nat) :=
  Costed.bind (family.selectCloseCosted shape hshape left) fun leftClose? =>
    Costed.bind
      (family.selectCloseCosted shape hshape (right - 1))
      fun rightClose? =>
        match leftClose?, rightClose? with
        | some leftClose, some rightClose =>
            Costed.bind
              (family.lcaCloseCosted shape hshape leftClose rightClose)
              fun answerClose? =>
                match answerClose? with
                | some answerClose =>
                    Costed.map (fun closeRank => some (closeRank - 1))
                      (family.rankCloseCosted shape hshape (answerClose + 1))
                | none => Costed.pure none
        | _, _ => Costed.pure none

theorem overhead_littleO
    {rankOverhead selectOverhead codeOverhead codeCount
      microTableOverhead macroOverhead : Nat -> Nat}
    {lcaQueryCost : Nat}
    (family :
      PayloadLiveMacroMicroBPCloseNavigationFamily
        rankOverhead selectOverhead codeOverhead codeCount
        microTableOverhead macroOverhead lcaQueryCost) :
    LittleOLinear family.overhead := by
  exact
    payloadLiveMacroMicroBPCloseNavigationOverhead_littleO
      family.rank_littleO family.select_littleO
      family.lcaFamily.overhead_littleO

theorem payload_length
    {rankOverhead selectOverhead codeOverhead codeCount
      microTableOverhead macroOverhead : Nat -> Nat}
    {lcaQueryCost n : Nat}
    (family :
      PayloadLiveMacroMicroBPCloseNavigationFamily
        rankOverhead selectOverhead codeOverhead codeCount
        microTableOverhead macroOverhead lcaQueryCost)
    {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n)) :
    (family.payload shape hshape).length =
      2 * n + family.overhead n := by
  have hshapeSize := Cartesian.mem_shapesOfSize_shapeOfSize hshape
  have hbp :
      shape.bpCode.length = 2 * n := by
    exact Cartesian.CartesianShape.bpCode_length_of_shapeOfSize hshapeSize
  have hrank :
      (family.rankData shape hshape).auxPayload.length =
        rankOverhead n :=
    (family.rankData shape hshape).auxPayload_length
  have hselect :
      (family.selectData shape hshape).auxPayload.length =
        selectOverhead n :=
    (family.selectData shape hshape).auxPayload_length
  have hlca :
      ((family.lcaFamily.directory (n := n) shape hshape).payload.length =
        family.lcaFamily.overhead n) :=
    ((family.lcaFamily.profile).2 n hshape).1
  simp [payload, overhead, PayloadLiveMacroMicroBPCloseLCAFamily.overhead,
    payloadLiveMacroMicroBPCloseNavigationOverhead, hbp, hrank, hselect,
    hlca]
  omega

theorem queryBuiltCosted_cost_le
    {rankOverhead selectOverhead codeOverhead codeCount
      microTableOverhead macroOverhead : Nat -> Nat}
    {lcaQueryCost n : Nat}
    (family :
      PayloadLiveMacroMicroBPCloseNavigationFamily
        rankOverhead selectOverhead codeOverhead codeCount
        microTableOverhead macroOverhead lcaQueryCost)
    (shape : Cartesian.CartesianShape)
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    (left right : Nat) :
    (family.queryBuiltCosted shape hshape left right).cost <=
      9 + lcaQueryCost := by
  unfold queryBuiltCosted selectCloseCosted lcaCloseCosted rankCloseCosted
  have hleft :=
    (family.selectData shape hshape).selectCosted_cost_le_three false left
  have hright :=
    (family.selectData shape hshape).selectCosted_cost_le_three
      false (right - 1)
  cases hleftValue :
      ((family.selectData shape hshape).selectCosted false left).value with
  | none =>
      simp [Costed.bind, hleftValue]
      omega
  | some leftClose =>
      cases hrightValue :
          ((family.selectData shape hshape).selectCosted
            false (right - 1)).value with
      | none =>
          simp [Costed.bind, hleftValue, hrightValue]
          omega
      | some rightClose =>
          have hlca :=
            ((family.lcaFamily.profile).2 n hshape).2.1
              leftClose rightClose
          cases hlcaValue :
              ((family.lcaFamily.directory
                (n := n) shape hshape).lcaCloseCosted
                  leftClose rightClose).value with
          | none =>
              simp [Costed.bind, hleftValue, hrightValue, hlcaValue]
              omega
          | some answerClose =>
              have hrank :=
                (family.rankData shape hshape).rankCostedClamped_cost_le_three
                  false (answerClose + 1)
              simp [Costed.bind, Costed.map, hleftValue, hrightValue,
                hlcaValue]
              omega

theorem selectCloseCosted_exact
    {rankOverhead selectOverhead codeOverhead codeCount
      microTableOverhead macroOverhead : Nat -> Nat}
    {lcaQueryCost n : Nat}
    (family :
      PayloadLiveMacroMicroBPCloseNavigationFamily
        rankOverhead selectOverhead codeOverhead codeCount
        microTableOverhead macroOverhead lcaQueryCost)
    (shape : Cartesian.CartesianShape)
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    (idx : Nat) :
    (family.selectCloseCosted shape hshape idx).erase =
      bpCloseOfInorder? shape idx := by
  calc
    (family.selectCloseCosted shape hshape idx).erase =
        Succinct.select false shape.bpCode idx := by
      exact (family.selectData shape hshape).selectCosted_exact false idx
    _ = bpCloseOfInorder? shape idx := by
      exact select_false_bpCode_eq_bpCloseOfInorder? shape idx

theorem rankCloseCosted_exact
    {rankOverhead selectOverhead codeOverhead codeCount
      microTableOverhead macroOverhead : Nat -> Nat}
    {lcaQueryCost n : Nat}
    (family :
      PayloadLiveMacroMicroBPCloseNavigationFamily
        rankOverhead selectOverhead codeOverhead codeCount
        microTableOverhead macroOverhead lcaQueryCost)
    (shape : Cartesian.CartesianShape)
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    (pos : Nat) :
    (family.rankCloseCosted shape hshape pos).erase =
      Succinct.rankPrefix false shape.bpCode pos := by
  exact (family.rankData shape hshape).rankCostedClamped_exact false pos

theorem queryBuiltCosted_exact
    {rankOverhead selectOverhead codeOverhead codeCount
      microTableOverhead macroOverhead : Nat -> Nat}
    {lcaQueryCost n : Nat}
    (family :
      PayloadLiveMacroMicroBPCloseNavigationFamily
        rankOverhead selectOverhead codeOverhead codeCount
        microTableOverhead macroOverhead lcaQueryCost)
    {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    {left len : Nat} (hlen : 0 < len) (hbound : left + len <= n) :
    (family.queryBuiltCosted shape hshape left (left + len)).erase =
      some (scanWindow shape.representative left len) := by
  have hshapeSize := Cartesian.mem_shapesOfSize_shapeOfSize hshape
  have hleftLt : left < n := by omega
  have hrightLt : left + len - 1 < n := by omega
  have hboundShape : left + len <= shape.size := by
    rw [Cartesian.ShapeOfSize.size_eq hshapeSize]
    exact hbound
  have hleftLtShape : left < shape.size := by
    rw [Cartesian.ShapeOfSize.size_eq hshapeSize]
    exact hleftLt
  have hrightLtShape : left + len - 1 < shape.size := by
    rw [Cartesian.ShapeOfSize.size_eq hshapeSize]
    exact hrightLt
  have hscanBounds :=
    Cartesian.scanWindow_bounds shape.representative left len hlen
  have hscanLt :
      scanWindow shape.representative left len < shape.size := by
    rw [Cartesian.ShapeOfSize.size_eq hshapeSize]
    omega
  rcases bpCloseOfInorder?_some_of_lt shape hleftLtShape with
    ⟨leftClose, hleftClose⟩
  rcases bpCloseOfInorder?_some_of_lt shape hrightLtShape with
    ⟨rightClose, hrightClose⟩
  rcases bpCloseOfInorder?_some_of_lt shape hscanLt with
    ⟨answerClose, hanswerClose⟩
  have hselectLeft :
      (family.selectCloseCosted shape hshape left).value =
        some leftClose := by
    have h := family.selectCloseCosted_exact shape hshape left
    simpa [Costed.erase, hleftClose] using h
  have hselectRight :
      (family.selectCloseCosted shape hshape
          (left + len - 1)).value =
        some rightClose := by
    have h :=
      family.selectCloseCosted_exact shape hshape (left + len - 1)
    simpa [Costed.erase, hrightClose] using h
  have hlca :
      (family.lcaCloseCosted shape hshape leftClose rightClose).value =
        some answerClose := by
    have h :=
      ((family.lcaFamily.profile).2 n hshape).2.2
        hlen hboundShape hleftClose hrightClose hanswerClose
    simpa [Costed.erase, lcaCloseCosted, hanswerClose] using h
  have hrank :
      (family.rankCloseCosted shape hshape (answerClose + 1)).value =
        scanWindow shape.representative left len + 1 := by
    have hrankExact :=
      family.rankCloseCosted_exact shape hshape (answerClose + 1)
    have hrankRecover :=
      bpCloseOfInorder?_rankFalse_succ shape hanswerClose
    calc
      (family.rankCloseCosted shape hshape (answerClose + 1)).value =
          Succinct.rankPrefix false shape.bpCode (answerClose + 1) := by
        simpa [Costed.erase] using hrankExact
      _ = scanWindow shape.representative left len + 1 := hrankRecover
  have hselectLeftRaw :
      ((family.selectData shape hshape).selectCosted false left).value =
        some leftClose := by
    simpa [selectCloseCosted] using hselectLeft
  have hselectRightRaw :
      ((family.selectData shape hshape).selectCosted
          false (left + len - 1)).value =
        some rightClose := by
    simpa [selectCloseCosted] using hselectRight
  have hlcaRaw :
      ((family.lcaFamily.directory
          (n := n) shape hshape).lcaCloseCosted
          leftClose rightClose).value =
        some answerClose := by
    simpa [lcaCloseCosted] using hlca
  have hrankRaw :
      ((family.rankData shape hshape).rankCostedClamped false
          (answerClose + 1)).value =
        scanWindow shape.representative left len + 1 := by
    simpa [rankCloseCosted] using hrank
  have hrankSub :
      scanWindow shape.representative left len + 1 - 1 =
        scanWindow shape.representative left len := by
    omega
  unfold queryBuiltCosted
  simp [selectCloseCosted, lcaCloseCosted, rankCloseCosted, Costed.erase,
    Costed.bind, Costed.map, Costed.pure, hselectLeftRaw,
    hselectRightRaw, hlcaRaw, hrankRaw, hrankSub]

theorem two_n_plus_o_built_query_profile
    {rankOverhead selectOverhead codeOverhead codeCount
      microTableOverhead macroOverhead : Nat -> Nat}
    {lcaQueryCost : Nat}
    (family :
      PayloadLiveMacroMicroBPCloseNavigationFamily
        rankOverhead selectOverhead codeOverhead codeCount
        microTableOverhead macroOverhead lcaQueryCost) :
    LittleOLinear family.overhead /\
      forall n : Nat,
        EncodingLowerBound.logSlackLower n <=
          2 * n + family.overhead n /\
        (forall {shape : Cartesian.CartesianShape},
          (hshape : List.Mem shape (Cartesian.shapesOfSize n)) ->
            (family.payload shape hshape).length =
              2 * n + family.overhead n) /\
        (forall {shape : Cartesian.CartesianShape},
          (hshape : List.Mem shape (Cartesian.shapesOfSize n)) ->
            forall left right,
              (family.queryBuiltCosted shape hshape left right).cost <=
                9 + lcaQueryCost) /\
        (forall {shape : Cartesian.CartesianShape},
          (hshape : List.Mem shape (Cartesian.shapesOfSize n)) ->
            forall {left len : Nat},
              0 < len ->
                left + len <= n ->
                  (family.queryBuiltCosted
                    shape hshape left (left + len)).erase =
                    some (scanWindow shape.representative left len)) := by
  constructor
  · exact family.overhead_littleO
  intro n
  constructor
  · have hbase :=
      EncodingLowerBound.canonicalRepresentativePayloadSpaceBounds_lower_le_upper n
    omega
  constructor
  · intro shape hshape
    exact family.payload_length hshape
  constructor
  · intro shape hshape left right
    exact family.queryBuiltCosted_cost_le shape hshape left right
  intro shape hshape left len hlen hbound
  exact family.queryBuiltCosted_exact hshape hlen hbound

end PayloadLiveMacroMicroBPCloseNavigationFamily

end SuccinctCloseProposal
end RMQ
