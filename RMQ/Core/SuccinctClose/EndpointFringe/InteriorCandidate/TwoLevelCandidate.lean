import RMQ.Core.SuccinctClose.EndpointFringe.InteriorCandidate.WordReads

/-!
# Endpoint-fringe two-level interior candidate

Split from `RMQ.Core.SuccinctClose.EndpointFringe.InteriorCandidate`.
Public declarations keep the canonical `RMQ.SuccinctClose` namespace.
-/

namespace RMQ
namespace SuccinctClose

open SuccinctSpace

def bpTwoLevelInteriorCandidateCosted
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
    (startBlock count : Nat) : Costed (Option (Nat × Nat)) :=
  let macroStart := startBlock / macroSize
  let localStart := startBlock % macroSize
  if count = 0 then
    Costed.pure none
  else if count <= macroSize - localStart then
    localTable.twoSpanCandidateCosted summary macroStart localStart count
  else
    let leftCount := macroSize - localStart
    let remaining := count - leftCount
    let middleMacroCount := remaining / macroSize
    let rightCount := remaining % macroSize
    if middleMacroCount = 0 then
      bpTwoLevelAdjacentMacroCandidateCosted localTable summary
        macroStart localStart rightCount
    else if rightCount = 0 then
      bpTwoLevelLeftMiddleMacroCandidateCosted localTable globalTable
        summary macroStart localStart middleMacroCount
    else
      bpTwoLevelCrossMacroCandidateCosted localTable globalTable summary
        macroStart localStart middleMacroCount rightCount

theorem bpTwoLevelInteriorCandidateCosted_cost_le_thirty
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
    (startBlock count : Nat) :
    (bpTwoLevelInteriorCandidateCosted localTable globalTable summary
      startBlock count).cost <= 30 := by
  unfold bpTwoLevelInteriorCandidateCosted
  by_cases hcount : count = 0
  · simp [hcount, Costed.pure]
  · simp [hcount]
    by_cases hwithin : count <= macroSize - startBlock % macroSize
    · simp [hwithin]
      have hlocal :=
        localTable.twoSpanCandidateCosted_cost_le_ten summary
          (startBlock / macroSize) (startBlock % macroSize) count
      omega
    · simp only [hwithin, if_false]
      by_cases hmiddle :
          macroSize = 0 ∨
            count - (macroSize - startBlock % macroSize) < macroSize
      · simp [hmiddle]
        have hadj :=
          bpTwoLevelAdjacentMacroCandidateCosted_cost_le_twenty
            localTable summary (startBlock / macroSize)
            (startBlock % macroSize)
            ((count - (macroSize - startBlock % macroSize)) % macroSize)
        omega
      · simp [hmiddle]
        by_cases hright :
            (count - (macroSize - startBlock % macroSize)) % macroSize = 0
        · simp only [hright, if_true]
          have hleftMiddle :=
            bpTwoLevelLeftMiddleMacroCandidateCosted_cost_le_twenty
              localTable globalTable summary (startBlock / macroSize)
              (startBlock % macroSize)
              ((count - (macroSize - startBlock % macroSize)) / macroSize)
          omega
        · simp only [hright, if_false]
          exact
            bpTwoLevelCrossMacroCandidateCosted_cost_le_thirty
              localTable globalTable summary (startBlock / macroSize)
              (startBlock % macroSize)
              ((count - (macroSize - startBlock % macroSize)) / macroSize)
              ((count - (macroSize - startBlock % macroSize)) %
                macroSize)

def bpTwoLevelInteriorCandidateWordsRead
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
    (startBlock count : Nat) : List (List Bool) :=
  let macroStart := startBlock / macroSize
  let localStart := startBlock % macroSize
  if count = 0 then
    []
  else if count <= macroSize - localStart then
    localTwoSpanCandidateWordsRead localTable summary macroStart localStart
      count
  else
    let leftCount := macroSize - localStart
    let remaining := count - leftCount
    let middleMacroCount := remaining / macroSize
    let rightCount := remaining % macroSize
    if middleMacroCount = 0 then
      bpTwoLevelAdjacentMacroCandidateWordsRead localTable summary
        macroStart localStart rightCount
    else if rightCount = 0 then
      bpTwoLevelLeftMiddleMacroCandidateWordsRead localTable globalTable
        summary macroStart localStart middleMacroCount
    else
      bpTwoLevelCrossMacroCandidateWordsRead localTable globalTable summary
        macroStart localStart middleMacroCount rightCount

theorem bpTwoLevelInteriorCandidateWordsRead_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount localLevelCount
      offsetWidth localOverhead globalLevelCount blockWidth globalOverhead
      blocksPerSuper superCount superWidth relativeWidth summaryOverhead
      startBlock count : Nat}
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
        SuccinctRank.machineWordBits shape.bpCode.length)
    (hblockMachine :
      blockWidth <=
        SuccinctRank.machineWordBits shape.bpCode.length)
    (hsuperMachine :
      superWidth <=
        SuccinctRank.machineWordBits shape.bpCode.length)
    (hrelativeMachine :
      relativeWidth <=
        SuccinctRank.machineWordBits shape.bpCode.length)
    {word : List Bool}
    (hmem :
      word ∈
        bpTwoLevelInteriorCandidateWordsRead localTable globalTable summary
          startBlock count) :
    word.length <=
      SuccinctRank.machineWordBits shape.bpCode.length := by
  unfold bpTwoLevelInteriorCandidateWordsRead at hmem
  by_cases hcount : count = 0
  · simp [hcount] at hmem
  · simp only [hcount, if_false] at hmem
    by_cases hwithin : count <= macroSize - startBlock % macroSize
    · simp [hwithin] at hmem
      exact
        localTwoSpanCandidateWordsRead_length_le_machine localTable summary
          hoffsetMachine hsuperMachine hrelativeMachine hmem
    · simp only [hwithin, if_false] at hmem
      by_cases hmiddle :
          macroSize = 0 ∨
            count - (macroSize - startBlock % macroSize) < macroSize
      · simp [hmiddle] at hmem
        exact
          bpTwoLevelAdjacentMacroCandidateWordsRead_length_le_machine
            localTable summary hoffsetMachine hsuperMachine
            hrelativeMachine hmem
      · simp [hmiddle] at hmem
        by_cases hright :
            (count - (macroSize - startBlock % macroSize)) % macroSize = 0
        · simp only [hright, if_true] at hmem
          exact
            bpTwoLevelLeftMiddleMacroCandidateWordsRead_length_le_machine
              localTable globalTable summary hoffsetMachine hblockMachine
              hsuperMachine hrelativeMachine hmem
        · simp only [hright, if_false] at hmem
          exact
            bpTwoLevelCrossMacroCandidateWordsRead_length_le_machine
              localTable globalTable summary hoffsetMachine hblockMachine
              hsuperMachine hrelativeMachine hmem

theorem bpTwoLevelInteriorCandidateCosted_erase_exact
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount localLevelCount
      offsetWidth localOverhead globalLevelCount blockWidth globalOverhead
      blocksPerSuper superCount superWidth relativeWidth
      summaryOverhead startBlock count : Nat}
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
    (hmacroSize : 0 < macroSize)
    (hcount : 0 < count)
    (hbound : startBlock + count <= blockCount)
    (hmacroRange :
      forall {block : Nat}, block < blockCount ->
        block / macroSize < macroCount)
    (hmacroCover : blockCount <= macroCount * macroSize)
    (hlocalLevel :
      forall {localCount : Nat}, 0 < localCount ->
        localCount <= macroSize ->
          Nat.log2 localCount < localLevelCount)
    (hglobalLevel :
      forall {macroSpanCount : Nat}, 0 < macroSpanCount ->
        macroSpanCount <= macroCount ->
        Nat.log2 macroSpanCount < globalLevelCount)
    (hblocks : 0 < blocksPerSuper)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hsuperCount :
      forall {block : Nat}, block < blockCount ->
        block / blocksPerSuper < superCount) :
    (bpTwoLevelInteriorCandidateCosted localTable globalTable summary
      startBlock count).erase =
      some
        (bpRangeMinExcess shape blockSize startBlock count,
          bpRangeArgMinPrefixPos shape blockSize startBlock count) := by
  let macroStart := startBlock / macroSize
  let localStart := startBlock % macroSize
  let leftCount := macroSize - localStart
  have hlocalStart : localStart < macroSize := by
    exact Nat.mod_lt startBlock hmacroSize
  have hstartEq : macroStart * macroSize + localStart = startBlock := by
    simpa [macroStart, localStart, Nat.mul_comm] using
      Nat.div_add_mod startBlock macroSize
  have hstartLt : startBlock < blockCount := by
    omega
  have hmacroStart : macroStart < macroCount := by
    simpa [macroStart] using hmacroRange hstartLt
  have hnotCount : ¬ count = 0 := by
    omega
  unfold bpTwoLevelInteriorCandidateCosted
  simp only [hnotCount, if_false]
  by_cases hwithin : count <= macroSize - startBlock % macroSize
  · have hlocalCount :
        startBlock % macroSize + count <= macroSize := by
      omega
    have hcountLeMacro : count <= macroSize := by
      omega
    have hlevel : Nat.log2 count < localLevelCount :=
      hlocalLevel hcount hcountLeMacro
    have hblockCount :
        (startBlock / macroSize) * macroSize +
            startBlock % macroSize + count <= blockCount := by
      simpa [macroStart, localStart, hstartEq] using hbound
    have hexact :=
      localTable.twoSpanCandidateCosted_erase_rangeWitness_exact
        summary hcount hmacroStart hlevel hlocalStart hlocalCount
        hblockCount hblocks hcover hsuperCount
    simp only [hwithin, if_true]
    simpa [macroStart, localStart, hstartEq] using hexact
  · simp only [hwithin, if_false]
    have hleftCount : 0 < leftCount := by
      unfold leftCount localStart
      omega
    have hleftLt : leftCount < count := by
      unfold leftCount localStart
      omega
    let remaining := count - leftCount
    let middleMacroCount := remaining / macroSize
    let rightCount := remaining % macroSize
    have hremainingPos : 0 < remaining := by
      unfold remaining
      omega
    have hcountEq : count = leftCount + remaining := by
      unfold remaining
      omega
    have hleftEnd :
        macroStart * macroSize + localStart + leftCount =
          (macroStart + 1) * macroSize := by
      have hsucc :
          macroStart * macroSize + macroSize =
            (macroStart + 1) * macroSize := by
        simpa using (Nat.succ_mul macroStart macroSize).symm
      unfold leftCount
      omega
    have hstartCountEq :
        startBlock + count =
          macroStart * macroSize + localStart + leftCount + remaining := by
      omega
    have hremainingDivMod :
        remaining = middleMacroCount * macroSize + rightCount := by
      unfold middleMacroCount rightCount
      simpa [Nat.mul_comm] using
        (Nat.div_add_mod remaining macroSize).symm
    by_cases hmiddleSmall : macroSize = 0 ∨ remaining < macroSize
    · have hremainingLt : remaining < macroSize := by
        rcases hmiddleSmall with hzero | hlt
        · omega
        · exact hlt
      have hmiddleZero : middleMacroCount = 0 := by
        unfold middleMacroCount
        exact Nat.div_eq_of_lt hremainingLt
      have hrightEq : rightCount = remaining := by
        unfold rightCount
        exact Nat.mod_eq_of_lt hremainingLt
      have hrightCount : 0 < rightCount := by
        simpa [hrightEq] using hremainingPos
      have hrightLe : rightCount <= macroSize := by
        omega
      have hrightLevel :
          Nat.log2 rightCount < localLevelCount :=
        hlocalLevel hrightCount hrightLe
      have hrightBlockCount :
          (macroStart + 1) * macroSize + rightCount <= blockCount := by
        have hend :
            startBlock + count =
              (macroStart + 1) * macroSize + rightCount := by
          calc
            startBlock + count =
                macroStart * macroSize + localStart + leftCount +
                  remaining := hstartCountEq
            _ = (macroStart + 1) * macroSize + remaining := by
                omega
            _ = (macroStart + 1) * macroSize + rightCount := by
                simp [hrightEq]
        omega
      have hrightMacro : macroStart + 1 < macroCount := by
        have hrightStartLt :
            (macroStart + 1) * macroSize < blockCount := by
          omega
        have hidx := hmacroRange hrightStartLt
        have hdiv :
            ((macroStart + 1) * macroSize) / macroSize =
              macroStart + 1 := by
          simpa [Nat.mul_comm] using
            Nat.mul_div_right (macroStart + 1) hmacroSize
        simpa [hdiv] using hidx
      have htotalBlockCount :
          macroStart * macroSize + localStart + leftCount + rightCount <=
            blockCount := by
        have hend :
            macroStart * macroSize + localStart + leftCount + rightCount =
              startBlock + count := by
          omega
        omega
      have hexact :=
        bpTwoLevelAdjacentMacroCandidateCosted_erase_exact
          localTable summary hmacroSize hlocalStart hrightCount hrightLe
          (hlocalLevel hleftCount (by omega)) hrightLevel hmacroStart
          hrightMacro htotalBlockCount hblocks hcover hsuperCount
      have hmiddleSmall' :
          macroSize = 0 ∨
            count - (macroSize - startBlock % macroSize) < macroSize := by
        simpa [remaining, leftCount, localStart] using hmiddleSmall
      have hcountAdjacent :
          (macroSize - localStart) + rightCount = count := by
        omega
      simpa [hmiddleSmall', macroStart, localStart, rightCount,
        remaining, leftCount, hstartEq, hcountAdjacent] using hexact
    · have hnotRemainingLt : ¬ remaining < macroSize := by
        intro hlt
        exact hmiddleSmall (Or.inr hlt)
      have hmacroLeRemaining : macroSize <= remaining := by
        exact Nat.le_of_not_gt hnotRemainingLt
      have hmiddleCount : 0 < middleMacroCount := by
        unfold middleMacroCount
        exact Nat.div_pos hmacroLeRemaining hmacroSize
      have hmiddleSmall' :
          ¬ (macroSize = 0 ∨
            count - (macroSize - startBlock % macroSize) < macroSize) := by
        simpa [remaining, leftCount, localStart] using hmiddleSmall
      by_cases hrightZero : rightCount = 0
      · have hremainingEq :
            remaining = middleMacroCount * macroSize := by
          simpa [hrightZero] using hremainingDivMod
        have hendMul :
            startBlock + count =
              (macroStart + 1 + middleMacroCount) * macroSize := by
          calc
            startBlock + count =
                macroStart * macroSize + localStart + leftCount +
                  remaining := hstartCountEq
            _ = (macroStart + 1) * macroSize + remaining := by
                omega
            _ =
                (macroStart + 1) * macroSize +
                  middleMacroCount * macroSize := by
                omega
            _ = (macroStart + 1 + middleMacroCount) * macroSize := by
                rw [← Nat.add_mul]
        have hmiddleEnd :
            macroStart + 1 + middleMacroCount <= macroCount := by
          have hmulLe :
              (macroStart + 1 + middleMacroCount) * macroSize <=
                macroCount * macroSize := by
            have hendBound :
                (macroStart + 1 + middleMacroCount) * macroSize <=
                  blockCount := by
              simpa [hendMul] using hbound
            exact Nat.le_trans hendBound hmacroCover
          have hmulLe' :
              macroSize * (macroStart + 1 + middleMacroCount) <=
                macroSize * macroCount := by
            simpa [Nat.mul_comm] using hmulLe
          exact Nat.le_of_mul_le_mul_left hmulLe' hmacroSize
        have hmiddleLevel :
            Nat.log2 middleMacroCount < globalLevelCount :=
          hglobalLevel hmiddleCount
            (by
              have hprefix :
                  middleMacroCount <=
                    macroStart + 1 + middleMacroCount := by
                simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
                  Nat.le_add_right middleMacroCount (macroStart + 1)
              exact Nat.le_trans hprefix hmiddleEnd)
        have htotalBlockCount :
            macroStart * macroSize + localStart + leftCount +
                middleMacroCount * macroSize <= blockCount := by
          have hend :
              macroStart * macroSize + localStart + leftCount +
                  middleMacroCount * macroSize =
                startBlock + count := by
            omega
          omega
        have hexact :=
          bpTwoLevelLeftMiddleMacroCandidateCosted_erase_exact
            localTable globalTable summary hmacroSize hlocalStart
            hmiddleCount (hlocalLevel hleftCount (by omega))
            hmiddleLevel hmacroStart hmiddleEnd htotalBlockCount
            hblocks hcover hsuperCount
        have hrightZero' :
            (count - (macroSize - startBlock % macroSize)) %
                macroSize = 0 := by
          simpa [rightCount, remaining, leftCount, localStart] using
            hrightZero
        have hcountLeftMiddle :
            (macroSize - localStart) + middleMacroCount * macroSize =
              count := by
          omega
        simpa [hmiddleSmall', hrightZero', macroStart, localStart,
          middleMacroCount, remaining, leftCount, hstartEq,
          hcountLeftMiddle] using hexact
      · have hrightCountPos : 0 < rightCount := by
          cases hright : rightCount with
          | zero =>
              exact False.elim (hrightZero hright)
          | succ k =>
              omega
        have hrightLe : rightCount <= macroSize := by
          have hrightLt : rightCount < macroSize := by
            unfold rightCount
            exact Nat.mod_lt remaining hmacroSize
          omega
        have hrightLevel :
            Nat.log2 rightCount < localLevelCount :=
          hlocalLevel hrightCountPos hrightLe
        have hrightMacro :
            macroStart + 1 + middleMacroCount < macroCount := by
          have hrightStartLt :
              (macroStart + 1 + middleMacroCount) * macroSize <
                blockCount := by
            have hend :
                startBlock + count =
                  (macroStart + 1 + middleMacroCount) * macroSize +
                    rightCount := by
              calc
                startBlock + count =
                    macroStart * macroSize + localStart + leftCount +
                      remaining := hstartCountEq
                _ = (macroStart + 1) * macroSize + remaining := by
                    omega
                _ =
                    (macroStart + 1) * macroSize +
                      (middleMacroCount * macroSize + rightCount) := by
                    omega
                _ =
                    (macroStart + 1 + middleMacroCount) * macroSize +
                      rightCount := by
                    calc
                      (macroStart + 1) * macroSize +
                          (middleMacroCount * macroSize + rightCount) =
                        ((macroStart + 1) * macroSize +
                            middleMacroCount * macroSize) + rightCount := by
                          omega
                      _ =
                        (macroStart + 1 + middleMacroCount) * macroSize +
                          rightCount := by
                          rw [← Nat.add_mul]
            omega
          have hidx := hmacroRange hrightStartLt
          have hdiv :
              ((macroStart + 1 + middleMacroCount) * macroSize) /
                  macroSize =
                macroStart + 1 + middleMacroCount := by
            simpa [Nat.mul_comm] using
              Nat.mul_div_right
                (macroStart + 1 + middleMacroCount) hmacroSize
          simpa [hdiv] using hidx
        have hmiddleLevel :
            Nat.log2 middleMacroCount < globalLevelCount :=
          hglobalLevel hmiddleCount
            (by
              have hprefix :
                  middleMacroCount <=
                    macroStart + 1 + middleMacroCount := by
                simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
                  Nat.le_add_right middleMacroCount (macroStart + 1)
              exact Nat.le_trans hprefix (Nat.le_of_lt hrightMacro))
        have htotalBlockCount :
            macroStart * macroSize + localStart + leftCount +
                middleMacroCount * macroSize + rightCount <= blockCount := by
          have hend :
              macroStart * macroSize + localStart + leftCount +
                  middleMacroCount * macroSize + rightCount =
                startBlock + count := by
            omega
          omega
        have hexact :=
          bpTwoLevelCrossMacroCandidateCosted_erase_exact
            localTable globalTable summary hmacroSize hlocalStart
            hmiddleCount hrightCountPos hrightLe
            (hlocalLevel hleftCount (by omega)) hmiddleLevel
            hrightLevel hmacroStart hrightMacro htotalBlockCount
            hblocks hcover hsuperCount
        have hrightZero' :
            ¬ (count - (macroSize - startBlock % macroSize)) %
                macroSize = 0 := by
          intro hzero
          exact hrightZero
            (by
              simpa [rightCount, remaining, leftCount, localStart] using
                hzero)
        have hcountCross :
            (macroSize - localStart) +
                middleMacroCount * macroSize + rightCount = count := by
          omega
        simpa [hmiddleSmall', hrightZero', macroStart, localStart,
          middleMacroCount, rightCount, remaining, leftCount, hstartEq,
          hcountCross] using hexact

theorem concreteBPTwoLevelCrossMacroCandidate_profile
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount localLevelCount
      offsetWidth globalLevelCount blockWidth blocksPerSuper superCount
      superWidth relativeWidth summaryOverhead : Nat}
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (hoffsetWidth : macroSize < 2 ^ offsetWidth)
    (hmacroSize : 0 < macroSize)
    (hblockWidth : blockCount < 2 ^ blockWidth)
    (hoffsetMachine :
      offsetWidth <=
        SuccinctRank.machineWordBits shape.bpCode.length)
    (hblockMachine :
      blockWidth <=
        SuccinctRank.machineWordBits shape.bpCode.length)
    (hsuperMachine :
      superWidth <=
        SuccinctRank.machineWordBits shape.bpCode.length)
    (hrelativeMachine :
      relativeWidth <=
        SuccinctRank.machineWordBits shape.bpCode.length)
    (hblocks : 0 < blocksPerSuper)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hsuperCount :
      forall {block : Nat}, block < blockCount ->
        block / blocksPerSuper < superCount) :
    let localTable :=
      concreteBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount localLevelCount offsetWidth hoffsetWidth
    let globalTable :=
      concreteBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount globalLevelCount blockWidth hmacroSize
        hblockWidth
    localTable.payload.length =
        (macroCount * (localLevelCount * macroSize)) * offsetWidth /\
      globalTable.payload.length =
        (globalLevelCount * macroCount) * blockWidth /\
      (forall macroStart localStart middleMacroCount rightCount,
        (bpTwoLevelCrossMacroCandidateCosted localTable globalTable summary
          macroStart localStart middleMacroCount rightCount).cost <= 30) /\
      (forall {macroStart localStart middleMacroCount rightCount : Nat},
        localStart < macroSize ->
          0 < middleMacroCount ->
            0 < rightCount ->
              rightCount <= macroSize ->
                Nat.log2 (macroSize - localStart) < localLevelCount ->
                  Nat.log2 middleMacroCount < globalLevelCount ->
                    Nat.log2 rightCount < localLevelCount ->
                      macroStart < macroCount ->
                        macroStart + 1 + middleMacroCount < macroCount ->
                          macroStart * macroSize + localStart +
                              (macroSize - localStart) +
                              middleMacroCount * macroSize + rightCount <=
                            blockCount ->
                            (bpTwoLevelCrossMacroCandidateCosted
                              localTable globalTable summary macroStart
                              localStart middleMacroCount rightCount).erase =
                              some
                                (bpRangeMinExcess shape blockSize
                                  (macroStart * macroSize + localStart)
                                  ((macroSize - localStart) +
                                    middleMacroCount * macroSize +
                                      rightCount),
                                  bpRangeArgMinPrefixPos shape blockSize
                                    (macroStart * macroSize + localStart)
                                    ((macroSize - localStart) +
                                      middleMacroCount * macroSize +
                                        rightCount))) /\
      forall {macroStart localStart middleMacroCount rightCount : Nat}
          {word : List Bool},
        word ∈
          bpTwoLevelCrossMacroCandidateWordsRead localTable globalTable
            summary macroStart localStart middleMacroCount rightCount ->
          word.length <=
            SuccinctRank.machineWordBits shape.bpCode.length := by
  intro localTable globalTable
  constructor
  · exact localTable.payload_length
  constructor
  · exact globalTable.payload_length
  constructor
  · intro macroStart localStart middleMacroCount rightCount
    exact
      bpTwoLevelCrossMacroCandidateCosted_cost_le_thirty
        localTable globalTable summary macroStart localStart
        middleMacroCount rightCount
  constructor
  · intro macroStart localStart middleMacroCount rightCount
      hlocalStart hmiddleCount hrightCount hrightLe hleftLevel
      hmiddleLevel hrightLevel hmacroStart hrightMacro hblockCount
    exact
      bpTwoLevelCrossMacroCandidateCosted_erase_exact
        localTable globalTable summary hmacroSize hlocalStart
        hmiddleCount hrightCount hrightLe hleftLevel hmiddleLevel
        hrightLevel hmacroStart hrightMacro hblockCount hblocks hcover
        hsuperCount
  · intro macroStart localStart middleMacroCount rightCount word hmem
    exact
      bpTwoLevelCrossMacroCandidateWordsRead_length_le_machine
        localTable globalTable summary hoffsetMachine hblockMachine
        hsuperMachine hrelativeMachine hmem


end SuccinctClose
end RMQ
