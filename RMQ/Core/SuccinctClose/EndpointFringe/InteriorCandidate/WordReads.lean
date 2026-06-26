import RMQ.Core.SuccinctClose.EndpointFringe.InteriorCandidate.RelativeScan

/-!
# Endpoint-fringe interior candidate word-read accounting

Split from `RMQ.Core.SuccinctClose.EndpointFringe.InteriorCandidate`.
Public declarations keep the historical `RMQ.SuccinctCloseProposal` namespace.
-/

namespace RMQ
namespace SuccinctCloseProposal

open SuccinctSpace

def localSparseOffsetWordRead
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      offsetWidth overhead : Nat}
    (offsetTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount levelCount offsetWidth overhead)
    (macroIdx localStart level : Nat) : List (List Bool) :=
  PayloadLiveBPRelativeMinMaxArgSummaryTable.optionWordList
    (offsetTable.table.store.words[
      bpLocalSparseCellSlot macroSize levelCount macroIdx localStart level]?)

theorem localSparseOffsetWordRead_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      offsetWidth overhead macroIdx localStart level : Nat}
    (offsetTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount levelCount offsetWidth overhead)
    (hmachine :
      offsetWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    {word : List Bool}
    (hmem :
      word ∈
        localSparseOffsetWordRead offsetTable macroIdx localStart level) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  have hsome :=
    PayloadLiveBPRelativeMinMaxArgSummaryTable.mem_optionWordList hmem
  exact offsetTable.read_word_length_le_machine hmachine hsome

def globalSparseBlockWordRead
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      blockWidth overhead : Nat}
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount levelCount blockWidth overhead)
    (macroStart level : Nat) : List (List Bool) :=
  PayloadLiveBPRelativeMinMaxArgSummaryTable.optionWordList
    (globalTable.table.store.words[
      bpGlobalSparseCellSlot macroCount macroStart level]?)

theorem globalSparseBlockWordRead_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      blockWidth overhead macroStart level : Nat}
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount levelCount blockWidth overhead)
    (hmachine :
      blockWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    {word : List Bool}
    (hmem :
      word ∈ globalSparseBlockWordRead globalTable macroStart level) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  have hsome :=
    PayloadLiveBPRelativeMinMaxArgSummaryTable.mem_optionWordList hmem
  exact globalTable.read_word_length_le_machine hmachine hsome

def localSpanCandidateWordsRead
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      offsetWidth localOverhead blocksPerSuper superCount
      superWidth relativeWidth summaryOverhead : Nat}
    (offsetTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount levelCount offsetWidth localOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (macroIdx localStart level : Nat) : List (List Bool) :=
  let offset :=
    bpLocalSparseCellOffset shape blockSize blockCount macroSize macroIdx
      localStart level
  localSparseOffsetWordRead offsetTable macroIdx localStart level ++
    summary.summaryCandidateWordsRead (macroIdx * macroSize + offset)

theorem localSpanCandidateWordsRead_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      offsetWidth localOverhead blocksPerSuper superCount
      superWidth relativeWidth summaryOverhead
      macroIdx localStart level : Nat}
    (offsetTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount levelCount offsetWidth localOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (hoffsetMachine :
      offsetWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hsuperMachine :
      superWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hrelativeMachine :
      relativeWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    {word : List Bool}
    (hmem :
      word ∈
        localSpanCandidateWordsRead offsetTable summary macroIdx localStart
          level) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  simp [localSpanCandidateWordsRead, List.mem_append] at hmem
  rcases hmem with hlocal | hsummary
  · exact
      localSparseOffsetWordRead_length_le_machine
        offsetTable hoffsetMachine hlocal
  · exact
      summary.summaryCandidateWordsRead_length_le_machine
        hsuperMachine hrelativeMachine hsummary

def globalSpanCandidateWordsRead
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      blockWidth globalOverhead blocksPerSuper superCount
      superWidth relativeWidth summaryOverhead : Nat}
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount levelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (macroStart level : Nat) : List (List Bool) :=
  let block :=
    bpGlobalSparseCellBlock shape blockSize blockCount macroSize macroCount
      macroStart level
  globalSparseBlockWordRead globalTable macroStart level ++
    summary.summaryCandidateWordsRead block

theorem globalSpanCandidateWordsRead_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      blockWidth globalOverhead blocksPerSuper superCount
      superWidth relativeWidth summaryOverhead macroStart level : Nat}
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount levelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (hblockMachine :
      blockWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hsuperMachine :
      superWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hrelativeMachine :
      relativeWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    {word : List Bool}
    (hmem :
      word ∈ globalSpanCandidateWordsRead globalTable summary macroStart
        level) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  simp [globalSpanCandidateWordsRead, List.mem_append] at hmem
  rcases hmem with hglobal | hsummary
  · exact
      globalSparseBlockWordRead_length_le_machine
        globalTable hblockMachine hglobal
  · exact
      summary.summaryCandidateWordsRead_length_le_machine
        hsuperMachine hrelativeMachine hsummary

def localTwoSpanCandidateWordsRead
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      offsetWidth localOverhead blocksPerSuper superCount
      superWidth relativeWidth summaryOverhead : Nat}
    (offsetTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount levelCount offsetWidth localOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (macroIdx localStart count : Nat) : List (List Bool) :=
  let level := Nat.log2 count
  let span := bpSparseLogSpan count
  localSpanCandidateWordsRead offsetTable summary macroIdx localStart level ++
    localSpanCandidateWordsRead offsetTable summary macroIdx
      (localStart + count - span) level

theorem localTwoSpanCandidateWordsRead_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      offsetWidth localOverhead blocksPerSuper superCount
      superWidth relativeWidth summaryOverhead
      macroIdx localStart count : Nat}
    (offsetTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount levelCount offsetWidth localOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (hoffsetMachine :
      offsetWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hsuperMachine :
      superWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hrelativeMachine :
      relativeWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    {word : List Bool}
    (hmem :
      word ∈
        localTwoSpanCandidateWordsRead offsetTable summary macroIdx
          localStart count) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  simp [localTwoSpanCandidateWordsRead, List.mem_append] at hmem
  rcases hmem with hleft | hright
  · exact
      localSpanCandidateWordsRead_length_le_machine offsetTable summary
        hoffsetMachine hsuperMachine hrelativeMachine hleft
  · exact
      localSpanCandidateWordsRead_length_le_machine offsetTable summary
        hoffsetMachine hsuperMachine hrelativeMachine hright

def globalTwoSpanCandidateWordsRead
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      blockWidth globalOverhead blocksPerSuper superCount
      superWidth relativeWidth summaryOverhead : Nat}
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount levelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (macroStart macroSpanCount : Nat) : List (List Bool) :=
  let level := Nat.log2 macroSpanCount
  let span := bpSparseLogSpan macroSpanCount
  globalSpanCandidateWordsRead globalTable summary macroStart level ++
    globalSpanCandidateWordsRead globalTable summary
      (macroStart + macroSpanCount - span) level

theorem globalTwoSpanCandidateWordsRead_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      blockWidth globalOverhead blocksPerSuper superCount
      superWidth relativeWidth summaryOverhead
      macroStart macroSpanCount : Nat}
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount levelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (hblockMachine :
      blockWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hsuperMachine :
      superWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hrelativeMachine :
      relativeWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    {word : List Bool}
    (hmem :
      word ∈
        globalTwoSpanCandidateWordsRead globalTable summary macroStart
          macroSpanCount) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  simp [globalTwoSpanCandidateWordsRead, List.mem_append] at hmem
  rcases hmem with hleft | hright
  · exact
      globalSpanCandidateWordsRead_length_le_machine globalTable summary
        hblockMachine hsuperMachine hrelativeMachine hleft
  · exact
      globalSpanCandidateWordsRead_length_le_machine globalTable summary
        hblockMachine hsuperMachine hrelativeMachine hright

def bpTwoLevelAdjacentMacroCandidateWordsRead
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount localLevelCount
      offsetWidth localOverhead blocksPerSuper superCount superWidth
      relativeWidth summaryOverhead : Nat}
    (localTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount localLevelCount offsetWidth localOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (macroStart localStart rightCount : Nat) : List (List Bool) :=
  let leftCount := macroSize - localStart
  localTwoSpanCandidateWordsRead localTable summary macroStart localStart
      leftCount ++
    localTwoSpanCandidateWordsRead localTable summary (macroStart + 1) 0
      rightCount

theorem bpTwoLevelAdjacentMacroCandidateWordsRead_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount localLevelCount
      offsetWidth localOverhead blocksPerSuper superCount superWidth
      relativeWidth summaryOverhead macroStart localStart rightCount : Nat}
    (localTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount localLevelCount offsetWidth localOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (hoffsetMachine :
      offsetWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hsuperMachine :
      superWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hrelativeMachine :
      relativeWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    {word : List Bool}
    (hmem :
      word ∈
        bpTwoLevelAdjacentMacroCandidateWordsRead localTable summary
          macroStart localStart rightCount) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  simp [bpTwoLevelAdjacentMacroCandidateWordsRead, List.mem_append] at hmem
  rcases hmem with hleft | hright
  · exact
      localTwoSpanCandidateWordsRead_length_le_machine localTable summary
        hoffsetMachine hsuperMachine hrelativeMachine hleft
  · exact
      localTwoSpanCandidateWordsRead_length_le_machine localTable summary
        hoffsetMachine hsuperMachine hrelativeMachine hright

def bpTwoLevelLeftMiddleMacroCandidateWordsRead
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount localLevelCount
      offsetWidth localOverhead globalLevelCount blockWidth globalOverhead
      blocksPerSuper superCount superWidth relativeWidth
      summaryOverhead : Nat}
    (localTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount localLevelCount offsetWidth localOverhead)
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount globalLevelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (macroStart localStart middleMacroCount : Nat) : List (List Bool) :=
  let leftCount := macroSize - localStart
  localTwoSpanCandidateWordsRead localTable summary macroStart localStart
      leftCount ++
    globalTwoSpanCandidateWordsRead globalTable summary (macroStart + 1)
      middleMacroCount

theorem bpTwoLevelLeftMiddleMacroCandidateWordsRead_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount localLevelCount
      offsetWidth localOverhead globalLevelCount blockWidth globalOverhead
      blocksPerSuper superCount superWidth relativeWidth summaryOverhead
      macroStart localStart middleMacroCount : Nat}
    (localTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount localLevelCount offsetWidth localOverhead)
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount globalLevelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (hoffsetMachine :
      offsetWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hblockMachine :
      blockWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hsuperMachine :
      superWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hrelativeMachine :
      relativeWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    {word : List Bool}
    (hmem :
      word ∈
        bpTwoLevelLeftMiddleMacroCandidateWordsRead localTable globalTable
          summary macroStart localStart middleMacroCount) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  simp [bpTwoLevelLeftMiddleMacroCandidateWordsRead, List.mem_append] at hmem
  rcases hmem with hleft | hmiddle
  · exact
      localTwoSpanCandidateWordsRead_length_le_machine localTable summary
        hoffsetMachine hsuperMachine hrelativeMachine hleft
  · exact
      globalTwoSpanCandidateWordsRead_length_le_machine globalTable summary
        hblockMachine hsuperMachine hrelativeMachine hmiddle

def bpTwoLevelCrossMacroCandidateWordsRead
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount localLevelCount
      offsetWidth localOverhead globalLevelCount blockWidth globalOverhead
      blocksPerSuper superCount superWidth relativeWidth
      summaryOverhead : Nat}
    (localTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount localLevelCount offsetWidth localOverhead)
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount globalLevelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (macroStart localStart middleMacroCount rightCount : Nat) :
    List (List Bool) :=
  let leftCount := macroSize - localStart
  let rightMacroStart := macroStart + 1 + middleMacroCount
  localTwoSpanCandidateWordsRead localTable summary macroStart localStart
      leftCount ++
    globalTwoSpanCandidateWordsRead globalTable summary (macroStart + 1)
      middleMacroCount ++
    localTwoSpanCandidateWordsRead localTable summary rightMacroStart 0
      rightCount

theorem bpTwoLevelCrossMacroCandidateWordsRead_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount localLevelCount
      offsetWidth localOverhead globalLevelCount blockWidth globalOverhead
      blocksPerSuper superCount superWidth relativeWidth
      summaryOverhead macroStart localStart middleMacroCount
      rightCount : Nat}
    (localTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount localLevelCount offsetWidth localOverhead)
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount globalLevelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (hoffsetMachine :
      offsetWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hblockMachine :
      blockWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hsuperMachine :
      superWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hrelativeMachine :
      relativeWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    {word : List Bool}
    (hmem :
      word ∈
        bpTwoLevelCrossMacroCandidateWordsRead localTable globalTable
          summary macroStart localStart middleMacroCount rightCount) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  simp [bpTwoLevelCrossMacroCandidateWordsRead, List.mem_append] at hmem
  rcases hmem with hleft | hmiddle | hright
  · exact
      localTwoSpanCandidateWordsRead_length_le_machine localTable summary
        hoffsetMachine hsuperMachine hrelativeMachine hleft
  · exact
      globalTwoSpanCandidateWordsRead_length_le_machine globalTable summary
        hblockMachine hsuperMachine hrelativeMachine hmiddle
  · exact
      localTwoSpanCandidateWordsRead_length_le_machine localTable summary
        hoffsetMachine hsuperMachine hrelativeMachine hright

end SuccinctCloseProposal
end RMQ
