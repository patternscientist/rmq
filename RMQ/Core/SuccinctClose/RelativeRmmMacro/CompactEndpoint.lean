import RMQ.Core.SuccinctClose.RelativeRmmMacro.EndpointCodebook

/-!
# Compact endpoint-fringe relative-rmM macro

Split implementation layer for the relative-rmM BP close/LCA macro. Public
declarations stay in the historical RMQ.SuccinctCloseProposal namespace.
-/

namespace RMQ
namespace SuccinctCloseProposal

open SuccinctSpace

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

end SuccinctCloseProposal
end RMQ
