import RMQ.Core.SuccinctClose.EndpointFringe.EndpointMacro.RangeMacro.RelativeMerge

/-!
# Concrete endpoint-fringe range macro profiles

Split from `RMQ.Core.SuccinctClose.EndpointFringe.EndpointMacro.RangeMacro`.
Public declarations keep the historical `RMQ.SuccinctCloseProposal` namespace.
-/

namespace RMQ
namespace SuccinctCloseProposal

open SuccinctSpace

def concreteBPEndpointFringeRangeMacro
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount fieldWidth : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth) :
    PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
      fieldWidth
      (2 * ((endpointLeftFringeRanges blockSize blockCount).length *
        fieldWidth))
      (2 * ((interiorBlockPairRanges blockCount).length * fieldWidth))
      (2 * ((endpointRightFringeRanges blockSize blockCount).length *
        fieldWidth)) where
  leftFringe :=
    concreteBPPrefixRangeArgMinWitnessTable shape fieldWidth
      (endpointLeftFringeRanges blockSize blockCount) hwidth
  interior :=
    concreteBPRangeArgMinWitnessTable shape blockSize fieldWidth
      (interiorBlockPairRanges blockCount) hwidth
  rightFringe :=
    concreteBPPrefixRangeArgMinWitnessTable shape fieldWidth
      (endpointRightFringeRanges blockSize blockCount) hwidth

theorem concreteBPEndpointFringeRangeMacro_profile
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount fieldWidth : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth) :
    let component :=
      concreteBPEndpointFringeRangeMacro
        shape blockSize blockCount fieldWidth hwidth
    component.payload.length =
        2 * ((blockCount * blockSize) * fieldWidth) +
          2 * ((blockCount * blockCount) * fieldWidth) +
          2 * ((blockCount * blockSize) * fieldWidth) /\
      forall leftClose rightClose,
        (component.lcaCloseCosted leftClose rightClose).cost <= 6 /\
          (component.lcaCloseCosted leftClose rightClose).erase =
            bpCandidateClose?
              (bpCandidateMerge3?
                (match
                  (bpPrefixRangeMinExcessEntries shape
                    (endpointLeftFringeRanges blockSize blockCount))[
                      endpointFringeSlot blockSize leftClose]?,
                  (bpPrefixRangeArgMinPrefixPosEntries shape
                    (endpointLeftFringeRanges blockSize blockCount))[
                      endpointFringeSlot blockSize leftClose]? with
                | some minExcess, some prefixPos =>
                    some (minExcess, prefixPos)
                | _, _ => none)
                (if blockOfClose blockSize leftClose + 1 <
                    blockOfClose blockSize rightClose then
                  match
                    (bpRangeMinExcessEntries shape blockSize
                      (interiorBlockPairRanges blockCount))[
                        component.interiorIndex leftClose rightClose]?,
                    (bpRangeArgMinPrefixPosEntries shape blockSize
                      (interiorBlockPairRanges blockCount))[
                        component.interiorIndex leftClose rightClose]? with
                  | some minExcess, some prefixPos =>
                      some (minExcess, prefixPos)
                  | _, _ => none
                else
                  none)
                (match
                  (bpPrefixRangeMinExcessEntries shape
                    (endpointRightFringeRanges blockSize blockCount))[
                      endpointFringeSlot blockSize rightClose]?,
                  (bpPrefixRangeArgMinPrefixPosEntries shape
                    (endpointRightFringeRanges blockSize blockCount))[
                      endpointFringeSlot blockSize rightClose]? with
                | some minExcess, some prefixPos =>
                    some (minExcess, prefixPos)
                | _, _ => none)) := by
  let component :=
    concreteBPEndpointFringeRangeMacro
      shape blockSize blockCount fieldWidth hwidth
  have hprofile := component.profile
  constructor
  · simpa [component, concreteBPEndpointFringeRangeMacro,
      endpointLeftFringeRanges_length, endpointRightFringeRanges_length,
      interiorBlockPairRanges_length] using hprofile.1
  · exact hprofile.2

theorem concreteBPEndpointFringeRangeMacro_sampled_profile
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount fieldWidth slots n : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth)
    (hbudget :
      2 * ((blockCount * blockSize) * fieldWidth) +
          2 * ((blockCount * blockCount) * fieldWidth) +
          2 * ((blockCount * blockSize) * fieldWidth) <=
        sampledDirectoryOverhead slots n) :
    let component :=
      concreteBPEndpointFringeRangeMacro
        shape blockSize blockCount fieldWidth hwidth
    LittleOLinear (sampledDirectoryOverhead slots) /\
      component.payload.length <= sampledDirectoryOverhead slots n /\
      forall leftClose rightClose,
        (component.lcaCloseCosted leftClose rightClose).cost <= 6 /\
          (component.lcaCloseCosted leftClose rightClose).erase =
            bpCandidateClose?
              (bpCandidateMerge3?
                (match
                  (bpPrefixRangeMinExcessEntries shape
                    (endpointLeftFringeRanges blockSize blockCount))[
                      endpointFringeSlot blockSize leftClose]?,
                  (bpPrefixRangeArgMinPrefixPosEntries shape
                    (endpointLeftFringeRanges blockSize blockCount))[
                      endpointFringeSlot blockSize leftClose]? with
                | some minExcess, some prefixPos =>
                    some (minExcess, prefixPos)
                | _, _ => none)
                (if blockOfClose blockSize leftClose + 1 <
                    blockOfClose blockSize rightClose then
                  match
                    (bpRangeMinExcessEntries shape blockSize
                      (interiorBlockPairRanges blockCount))[
                        component.interiorIndex leftClose rightClose]?,
                    (bpRangeArgMinPrefixPosEntries shape blockSize
                      (interiorBlockPairRanges blockCount))[
                        component.interiorIndex leftClose rightClose]? with
                  | some minExcess, some prefixPos =>
                      some (minExcess, prefixPos)
                  | _, _ => none
                else
                  none)
                (match
                  (bpPrefixRangeMinExcessEntries shape
                    (endpointRightFringeRanges blockSize blockCount))[
                      endpointFringeSlot blockSize rightClose]?,
                  (bpPrefixRangeArgMinPrefixPosEntries shape
                    (endpointRightFringeRanges blockSize blockCount))[
                      endpointFringeSlot blockSize rightClose]? with
                | some minExcess, some prefixPos =>
                    some (minExcess, prefixPos)
                | _, _ => none)) := by
  let component :=
    concreteBPEndpointFringeRangeMacro
      shape blockSize blockCount fieldWidth hwidth
  have hprofile :=
    concreteBPEndpointFringeRangeMacro_profile
      shape blockSize blockCount fieldWidth hwidth
  constructor
  · exact sampledDirectoryOverhead_littleO slots
  constructor
  · rw [hprofile.1]
    exact hbudget
  · exact hprofile.2

theorem concreteBPEndpointFringeRangeMacro_sampled_query_profile
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount fieldWidth slots n : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth)
    (hbudget :
      2 * ((blockCount * blockSize) * fieldWidth) +
          2 * ((blockCount * blockCount) * fieldWidth) +
          2 * ((blockCount * blockSize) * fieldWidth) <=
        sampledDirectoryOverhead slots n) :
    let component :=
      concreteBPEndpointFringeRangeMacro
        shape blockSize blockCount fieldWidth hwidth
    LittleOLinear (sampledDirectoryOverhead slots) /\
      component.payload.length <= sampledDirectoryOverhead slots n /\
      (forall leftClose rightClose,
        (component.lcaCloseCosted leftClose rightClose).cost <= 6) /\
      forall {left len leftClose rightClose answerClose : Nat},
        0 < len ->
          left + len <= shape.size ->
            bpCloseOfInorder? shape left = some leftClose ->
              bpCloseOfInorder? shape (left + len - 1) =
                  some rightClose ->
                bpCloseOfInorder? shape
                    (scanWindow shape.representative left len) =
                  some answerClose ->
                  0 < blockSize ->
                    blockOfClose blockSize leftClose < blockCount ->
                      blockOfClose blockSize rightClose < blockCount ->
                        blockOfClose blockSize leftClose <
                            blockOfClose blockSize rightClose ->
                          (component.lcaCloseCosted
                            leftClose rightClose).erase =
                            some answerClose := by
  let component :=
    concreteBPEndpointFringeRangeMacro
      shape blockSize blockCount fieldWidth hwidth
  have hprofile :=
    (component.profile_cross_block_exact)
  have hpayload :=
    (concreteBPEndpointFringeRangeMacro_profile
      shape blockSize blockCount fieldWidth hwidth).1
  constructor
  · exact sampledDirectoryOverhead_littleO slots
  constructor
  · rw [hpayload]
    exact hbudget
  constructor
  · exact hprofile.2.1
  · exact hprofile.2.2

theorem concreteBPEndpointFringeRangeMacro_read_words_length_le_machine
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount fieldWidth : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth)
    (hmachine :
      fieldWidth <=
        SuccinctRank.machineWordBits shape.bpCode.length) :
    let component :=
      concreteBPEndpointFringeRangeMacro
        shape blockSize blockCount fieldWidth hwidth
    (forall {rangeIndex : Nat} {word : List Bool},
      component.leftFringe.minTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRank.machineWordBits shape.bpCode.length) /\
    (forall {rangeIndex : Nat} {word : List Bool},
      component.leftFringe.argTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRank.machineWordBits shape.bpCode.length) /\
    (forall {rangeIndex : Nat} {word : List Bool},
      component.interior.minTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRank.machineWordBits shape.bpCode.length) /\
    (forall {rangeIndex : Nat} {word : List Bool},
      component.interior.argTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRank.machineWordBits shape.bpCode.length) /\
    (forall {rangeIndex : Nat} {word : List Bool},
      component.rightFringe.minTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRank.machineWordBits shape.bpCode.length) /\
    (forall {rangeIndex : Nat} {word : List Bool},
      component.rightFringe.argTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRank.machineWordBits shape.bpCode.length) := by
  exact
    PayloadLiveBPEndpointFringeRangeMacro.read_words_length_le_machine
      (concreteBPEndpointFringeRangeMacro
        shape blockSize blockCount fieldWidth hwidth) hmachine

end SuccinctCloseProposal
end RMQ
