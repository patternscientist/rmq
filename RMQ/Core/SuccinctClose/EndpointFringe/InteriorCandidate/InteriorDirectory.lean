import RMQ.Core.SuccinctClose.EndpointFringe.InteriorCandidate.TwoLevelCandidate
import RMQ.Core.SuccinctSpace.MachineChunkedTableProgram
import RMQ.Core.SuccinctClose.EndpointFringe.PrefixRange.SparseLevelTable

/-!
# Endpoint-fringe relative-rmM interior directory

Split from `RMQ.Core.SuccinctClose.EndpointFringe.InteriorCandidate`.
Public declarations keep the canonical `RMQ.SuccinctClose` namespace.
-/

namespace RMQ
namespace SuccinctClose

open SuccinctSpace

private def interiorPayloadWordReadOfGet?
    (words : Array (List Bool)) (index : Nat) : List (List Bool) :=
  match words[index]? with
  | some word => [word]
  | none => []

private theorem interiorPayloadWordReadOfGet?_length_le
    {n : Nat}
    {words : Array (List Bool)}
    (hwords :
      forall {index : Nat} {word : List Bool},
        words[index]? = some word ->
          word.length <= SuccinctRank.machineWordBits n)
    {index : Nat} {word : List Bool}
    (hmem : word ∈ interiorPayloadWordReadOfGet? words index) :
    word.length <= SuccinctRank.machineWordBits n := by
  unfold interiorPayloadWordReadOfGet? at hmem
  cases hget : words[index]? with
  | none =>
      simp [hget] at hmem
  | some stored =>
      simp [hget] at hmem
      subst word
      exact hwords hget

/--
Interior full-block range-minimum directory for the relative-rmM close layer.

This interface is deliberately narrow: a concrete implementation has to expose
one charged `rangeMinCosted` path whose erasure is the leftmost block-minimum
candidate over the requested complete-block range.  The compact C2 target must
instantiate this with a constant `queryCost`; the scan instance below is kept
only as a diagnostic replacement target.
-/
structure PayloadLiveBPRelativeRmmInteriorDirectory
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount overhead queryCost : Nat) where
  payload : List Bool
  payload_length_eq : payload.length = overhead
  payloadWordsRead : Nat -> Nat -> List (List Bool)
  rangeMinCosted : Nat -> Nat -> Costed (Option (Nat × Nat))
  rangeMin_cost_le :
    forall startBlock count,
      (rangeMinCosted startBlock count).cost <= queryCost
  rangeMin_exact :
    forall {startBlock count : Nat},
      0 < count ->
        startBlock + count <= blockCount ->
          (rangeMinCosted startBlock count).erase =
            some
              (bpRangeMinExcess shape blockSize startBlock count,
                bpRangeArgMinPrefixPos shape blockSize startBlock count)
  read_words_length_le_machine :
    forall {startBlock count : Nat} {word : List Bool},
      word ∈ payloadWordsRead startBlock count ->
        word.length <=
          SuccinctRank.machineWordBits shape.bpCode.length

namespace PayloadLiveBPRelativeRmmInteriorDirectory

theorem profile
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount overhead queryCost : Nat}
    (directory :
      PayloadLiveBPRelativeRmmInteriorDirectory shape blockSize blockCount
        overhead queryCost) :
    directory.payload.length = overhead /\
      (forall startBlock count,
        (directory.rangeMinCosted startBlock count).cost <= queryCost) /\
      (forall {startBlock count : Nat},
        0 < count ->
          startBlock + count <= blockCount ->
            (directory.rangeMinCosted startBlock count).erase =
              some
                (bpRangeMinExcess shape blockSize startBlock count,
                  bpRangeArgMinPrefixPos shape blockSize startBlock count)) /\
      forall {startBlock count : Nat} {word : List Bool},
        word ∈ directory.payloadWordsRead startBlock count ->
          word.length <=
            SuccinctRank.machineWordBits shape.bpCode.length := by
  exact ⟨directory.payload_length_eq, directory.rangeMin_cost_le,
    directory.rangeMin_exact, directory.read_words_length_le_machine⟩

end PayloadLiveBPRelativeRmmInteriorDirectory

/--
Proof-only range-min oracle used to document a target-shape obstruction.

This is intentionally *not* a compact C2 construction: it answers by directly
calling the semantic reference functions and charges a constant without reading
payload bits.  The theorem below records why `concreteBPRelativeRmmInteriorDirectory_profile`
cannot be closed merely by exposing the abstract `PayloadLiveBPRelativeRmmInteriorDirectory`
record and invoking its generic `.profile`.
-/
def proofOnlyBPRelativeRmmInteriorDirectory
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount : Nat) :
    PayloadLiveBPRelativeRmmInteriorDirectory shape blockSize blockCount
      0 1 where
  payload := []
  payload_length_eq := rfl
  payloadWordsRead := fun _ _ => []
  rangeMinCosted := fun startBlock count =>
    { value :=
        if 0 < count ∧ startBlock + count <= blockCount then
          some
            (bpRangeMinExcess shape blockSize startBlock count,
              bpRangeArgMinPrefixPos shape blockSize startBlock count)
        else
          none
      cost := 1 }
  rangeMin_cost_le := by
    intro startBlock count
    simp
  rangeMin_exact := by
    intro startBlock count hcount hbound
    have hcond : 0 < count ∧ startBlock + count <= blockCount :=
      ⟨hcount, hbound⟩
    simp [hcond]
  read_words_length_le_machine := by
    intro startBlock count word hmem
    cases hmem

theorem payloadLiveBPRelativeRmmInteriorDirectory_profile_allows_proof_only_oracle
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount : Nat) :
    let directory :=
      proofOnlyBPRelativeRmmInteriorDirectory shape blockSize blockCount
    directory.payload.length = 0 /\
      (forall startBlock count,
        (directory.rangeMinCosted startBlock count).cost <= 1) /\
      (forall {startBlock count : Nat},
        0 < count ->
          startBlock + count <= blockCount ->
            (directory.rangeMinCosted startBlock count).erase =
              some
                (bpRangeMinExcess shape blockSize startBlock count,
                  bpRangeArgMinPrefixPos shape blockSize startBlock count)) /\
      forall {startBlock count : Nat} {word : List Bool},
        word ∈ directory.payloadWordsRead startBlock count ->
          word.length <=
            SuccinctRank.machineWordBits shape.bpCode.length := by
  exact
    (proofOnlyBPRelativeRmmInteriorDirectory
      shape blockSize blockCount).profile

namespace PayloadLiveBPRelativeMinMaxArgSummaryTable

def boundedRangeScanCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (startBlock count : Nat) : Costed (Option (Nat × Nat)) :=
  if startBlock + count <= blockCount then
    table.rangeScanCosted startBlock count
  else
    Costed.pure none

theorem boundedRangeScanCosted_cost_le_blockCount
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (startBlock count : Nat) :
    (table.boundedRangeScanCosted startBlock count).cost <=
      4 * blockCount := by
  unfold boundedRangeScanCosted
  by_cases hbound : startBlock + count <= blockCount
  · simp [hbound]
    have hcost := table.rangeScanCosted_cost_le startBlock count
    have hcount : count <= blockCount := by omega
    have hmul : 4 * count <= 4 * blockCount :=
      Nat.mul_le_mul_left 4 hcount
    exact Nat.le_trans hcost hmul
  · simp [hbound, Costed.pure]

theorem div_lt_succ_div_of_lt
    {block blocksPerSuper blockCount : Nat}
    (hblock : block < blockCount) :
    block / blocksPerSuper < blockCount / blocksPerSuper + 1 := by
  have hle : block / blocksPerSuper <= blockCount / blocksPerSuper := by
    exact Nat.div_le_div_right (Nat.le_of_lt hblock)
  omega

theorem boundedRangeScanCosted_erase_exact
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead startBlock count : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (hblocks : 0 < blocksPerSuper)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hsuperCount :
      forall {block : Nat}, block < blockCount ->
        block / blocksPerSuper < superCount)
    (hcount : 0 < count)
    (hbound : startBlock + count <= blockCount) :
    (table.boundedRangeScanCosted startBlock count).erase =
      some
        (bpRangeMinExcess shape blockSize startBlock count,
          bpRangeArgMinPrefixPos shape blockSize startBlock count) := by
  unfold boundedRangeScanCosted
  simp [hbound]
  exact
    table.rangeScanCosted_erase_exact hblocks hcover hcount
      (by
        intro offset hoffset
        omega)
      (by
        intro offset hoffset
        exact hsuperCount (by omega))

def summaryRangeScanFromWordsRead
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead) :
    Nat -> Nat -> List (List Bool)
  | _block, 0 => []
  | block, steps + 1 =>
      table.summaryCandidateWordsRead block ++
        table.summaryRangeScanFromWordsRead (block + 1) steps

def summaryRangeScanWordsRead
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (startBlock count : Nat) : List (List Bool) :=
  match count with
  | 0 => []
  | steps + 1 =>
      table.summaryCandidateWordsRead startBlock ++
        table.summaryRangeScanFromWordsRead (startBlock + 1) steps

def boundedSummaryRangeScanWordsRead
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (startBlock count : Nat) : List (List Bool) :=
  if startBlock + count <= blockCount then
    table.summaryRangeScanWordsRead startBlock count
  else
    []

theorem summaryRangeScanFromWordsRead_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead block steps : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (hsuperMachine :
      superWidth <=
        SuccinctRank.machineWordBits shape.bpCode.length)
    (hrelativeMachine :
      relativeWidth <=
        SuccinctRank.machineWordBits shape.bpCode.length)
    {word : List Bool}
    (hmem :
      word ∈ table.summaryRangeScanFromWordsRead block steps) :
    word.length <=
      SuccinctRank.machineWordBits shape.bpCode.length := by
  induction steps generalizing block with
  | zero =>
      simp [summaryRangeScanFromWordsRead] at hmem
  | succ steps ih =>
      simp [summaryRangeScanFromWordsRead, List.mem_append] at hmem
      rcases hmem with hhead | htail
      · exact
          table.summaryCandidateWordsRead_length_le_machine
            hsuperMachine hrelativeMachine hhead
      · exact ih (block := block + 1) htail

theorem summaryRangeScanWordsRead_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead startBlock count : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (hsuperMachine :
      superWidth <=
        SuccinctRank.machineWordBits shape.bpCode.length)
    (hrelativeMachine :
      relativeWidth <=
        SuccinctRank.machineWordBits shape.bpCode.length)
    {word : List Bool}
    (hmem : word ∈ table.summaryRangeScanWordsRead startBlock count) :
    word.length <=
      SuccinctRank.machineWordBits shape.bpCode.length := by
  unfold summaryRangeScanWordsRead at hmem
  cases count with
  | zero =>
      simp at hmem
  | succ steps =>
      simp [List.mem_append] at hmem
      rcases hmem with hhead | htail
      · exact
          table.summaryCandidateWordsRead_length_le_machine
            hsuperMachine hrelativeMachine hhead
      · exact
          table.summaryRangeScanFromWordsRead_length_le_machine
            hsuperMachine hrelativeMachine htail

theorem boundedSummaryRangeScanWordsRead_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead startBlock count : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (hsuperMachine :
      superWidth <=
        SuccinctRank.machineWordBits shape.bpCode.length)
    (hrelativeMachine :
      relativeWidth <=
        SuccinctRank.machineWordBits shape.bpCode.length)
    {word : List Bool}
    (hmem :
      word ∈ table.boundedSummaryRangeScanWordsRead startBlock count) :
    word.length <=
      SuccinctRank.machineWordBits shape.bpCode.length := by
  unfold boundedSummaryRangeScanWordsRead at hmem
  by_cases hbound : startBlock + count <= blockCount
  · simp [hbound] at hmem
    exact
      table.summaryRangeScanWordsRead_length_le_machine
        hsuperMachine hrelativeMachine hmem
  · simp [hbound] at hmem

def scanInteriorDirectory
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (hblocks : 0 < blocksPerSuper)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hsuperCount :
      forall {block : Nat}, block < blockCount ->
        block / blocksPerSuper < superCount) :
    PayloadLiveBPRelativeRmmInteriorDirectory shape blockSize blockCount
      overhead (4 * blockCount) where
  payload := table.payload
  payload_length_eq := table.payload_length
  payloadWordsRead := fun _ _ => []
  rangeMinCosted := table.boundedRangeScanCosted
  rangeMin_cost_le := table.boundedRangeScanCosted_cost_le_blockCount
  rangeMin_exact := by
    intro startBlock count hcount hbound
    exact table.boundedRangeScanCosted_erase_exact hblocks hcover
      hsuperCount hcount hbound
  read_words_length_le_machine := by
    intro startBlock count word hmem
    cases hmem

theorem scanInteriorDirectory_profile
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (hblocks : 0 < blocksPerSuper)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hsuperCount :
      forall {block : Nat}, block < blockCount ->
        block / blocksPerSuper < superCount) :
    let directory :=
      table.scanInteriorDirectory hblocks hcover hsuperCount
    directory.payload.length = overhead /\
      (forall startBlock count,
        (directory.rangeMinCosted startBlock count).cost <=
          4 * blockCount) /\
      (forall {startBlock count : Nat},
        0 < count ->
          startBlock + count <= blockCount ->
            (directory.rangeMinCosted startBlock count).erase =
              some
                (bpRangeMinExcess shape blockSize startBlock count,
                  bpRangeArgMinPrefixPos shape blockSize startBlock count)) /\
      forall {startBlock count : Nat} {word : List Bool},
        word ∈ directory.payloadWordsRead startBlock count ->
          word.length <=
            SuccinctRank.machineWordBits shape.bpCode.length := by
  exact
    (table.scanInteriorDirectory hblocks hcover hsuperCount).profile

end PayloadLiveBPRelativeMinMaxArgSummaryTable

theorem canonicalBPRelativeSummary_block_div_lt_superCount
    {shape : Cartesian.CartesianShape} {block : Nat}
    (hblock : block < canonicalBPRelativeSummaryBlockCount shape) :
    block / canonicalBPRelativeSummaryBlocksPerSuper shape <
      canonicalBPRelativeSummarySuperCount shape := by
  by_cases hactive :
      canonicalBPRelativeMinMaxArgSummaryTableActive shape
  · have hdiv :
        block / canonicalBPRelativeSummaryBlocksPerSuperRaw shape <
          canonicalBPRelativeSummaryBlockCountRaw shape /
              canonicalBPRelativeSummaryBlocksPerSuperRaw shape + 1 :=
      have hblockRaw :
          block < canonicalBPRelativeSummaryBlockCountRaw shape := by
        simpa [canonicalBPRelativeSummaryBlockCount, hactive] using hblock
      PayloadLiveBPRelativeMinMaxArgSummaryTable.div_lt_succ_div_of_lt
        (blockCount := canonicalBPRelativeSummaryBlockCountRaw shape)
        hblockRaw
    simpa [canonicalBPRelativeSummaryBlockCount,
      canonicalBPRelativeSummaryBlocksPerSuper,
      canonicalBPRelativeSummarySuperCount,
      canonicalBPRelativeSummarySuperCountRaw, hactive] using hdiv
  · simp [canonicalBPRelativeSummaryBlockCount, hactive] at hblock

def concreteBPRelativeRmmInteriorLocalTable
    (shape : Cartesian.CartesianShape) :
    PayloadLiveBPLocalSparseOffsetTable shape
      (canonicalBPRelativeSummaryBlockSize shape)
      (canonicalBPRelativeSummaryBlockCount shape)
      (concreteBPRelativeRmmInteriorMacroSize shape)
      (concreteBPRelativeRmmInteriorMacroCount shape)
      (concreteBPRelativeRmmInteriorLevelCount shape)
      (concreteBPRelativeRmmInteriorOffsetWidth shape)
      (((concreteBPRelativeRmmInteriorMacroCount shape) *
          ((concreteBPRelativeRmmInteriorLevelCount shape) *
            (concreteBPRelativeRmmInteriorMacroSize shape))) *
        (concreteBPRelativeRmmInteriorOffsetWidth shape)) :=
  concreteBPLocalSparseOffsetTable shape
    (canonicalBPRelativeSummaryBlockSize shape)
    (canonicalBPRelativeSummaryBlockCount shape)
    (concreteBPRelativeRmmInteriorMacroSize shape)
    (concreteBPRelativeRmmInteriorMacroCount shape)
    (concreteBPRelativeRmmInteriorLevelCount shape)
    (concreteBPRelativeRmmInteriorOffsetWidth shape)
    (concreteBPRelativeRmmInteriorOffsetWidth_capacity shape)

def concreteBPRelativeRmmInteriorGlobalTable
    (shape : Cartesian.CartesianShape) :
    PayloadLiveBPGlobalSparseBlockTable shape
      (canonicalBPRelativeSummaryBlockSize shape)
      (canonicalBPRelativeSummaryBlockCount shape)
      (concreteBPRelativeRmmInteriorMacroSize shape)
      (concreteBPRelativeRmmInteriorMacroCount shape)
      (concreteBPRelativeRmmInteriorGlobalLevelCount shape)
      (concreteBPRelativeRmmInteriorBlockWidth shape)
      (((concreteBPRelativeRmmInteriorGlobalLevelCount shape) *
          (concreteBPRelativeRmmInteriorMacroCount shape)) *
        (concreteBPRelativeRmmInteriorBlockWidth shape)) :=
  concreteBPGlobalSparseBlockTable shape
    (canonicalBPRelativeSummaryBlockSize shape)
    (canonicalBPRelativeSummaryBlockCount shape)
    (concreteBPRelativeRmmInteriorMacroSize shape)
    (concreteBPRelativeRmmInteriorMacroCount shape)
    (concreteBPRelativeRmmInteriorGlobalLevelCount shape)
    (concreteBPRelativeRmmInteriorBlockWidth shape)
    (concreteBPRelativeRmmInteriorMacroSize_pos shape)
    (concreteBPRelativeRmmInteriorBlockWidth_capacity shape)

theorem concreteBPRelativeRmmInteriorLocalTable_payload_le_budget_of_ready
    (shape : Cartesian.CartesianShape)
    (hready : concreteBPRelativeRmmInteriorReady shape) :
    (concreteBPRelativeRmmInteriorLocalTable shape).payload.length <=
      logLogSquaredSampledDirectoryOverhead
        concreteBPRelativeRmmInteriorLocalOffsetSlots shape.size := by
  let base := canonicalBPRelativeSummaryBase shape
  let logBase := Nat.log2 base + 1
  let blockCount := canonicalBPRelativeSummaryBlockCount shape
  let macroCount := concreteBPRelativeRmmInteriorMacroCount shape
  let macroSize := concreteBPRelativeRmmInteriorMacroSize shape
  let levelCount := concreteBPRelativeRmmInteriorLevelCount shape
  let offsetWidth := concreteBPRelativeRmmInteriorOffsetWidth shape
  have hactive :=
    concreteBPRelativeRmmInteriorReady_active hready
  have hmacroCells :
      macroCount * macroSize <= 2 * blockCount := by
    simpa [macroCount, macroSize, blockCount] using
      concreteBPRelativeRmmInteriorMacroCover_le_two_blockCount_of_ready
        hready
  have hoffset :
      offsetWidth <= 5 * logBase := by
    simpa [offsetWidth, logBase] using
      concreteBPRelativeRmmInteriorOffsetWidth_le_five_logBase shape
  have hlevel :
      levelCount <= 5 * logBase := by
    simpa [levelCount, concreteBPRelativeRmmInteriorLevelCount,
      offsetWidth] using hoffset
  have hlevelOffset :
      levelCount * offsetWidth <=
        (5 * logBase) * (5 * logBase) :=
    Nat.mul_le_mul hlevel hoffset
  have hactual :
      (macroCount * (levelCount * macroSize)) * offsetWidth <=
        (2 * blockCount) * ((5 * logBase) * (5 * logBase)) := by
    have hmul := Nat.mul_le_mul hmacroCells hlevelOffset
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul
  have hbudgetNorm :
      (2 * blockCount) * ((5 * logBase) * (5 * logBase)) <=
        64 * (blockCount * (logBase * logBase)) := by
    let cell := logBase * (logBase * blockCount)
    have hle :
        50 * cell <= 64 * cell :=
      Nat.mul_le_mul_right cell
        (by decide : 50 <= 64)
    calc
      (2 * blockCount) * ((5 * logBase) * (5 * logBase)) =
          2 * (5 * (5 * cell)) := by
        simp [cell, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      _ = 50 * cell := by
        omega
      _ <= 64 * cell := hle
      _ = 64 * (blockCount * (logBase * logBase)) := by
        simp [cell, Nat.mul_assoc, Nat.mul_comm]
  have hpayload :=
    (concreteBPRelativeRmmInteriorLocalTable shape).payload_length
  rw [hpayload]
  exact Nat.le_trans hactual
    (by
      simpa [logLogSquaredSampledDirectoryOverhead,
        concreteBPRelativeRmmInteriorLocalOffsetSlots,
        canonicalBPRelativeSummaryBlockCount,
        canonicalBPRelativeSummaryBlockCountRaw,
        canonicalBPRelativeSummaryBase, blockCount, base, logBase, hactive,
        Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hbudgetNorm)

theorem concreteBPRelativeRmmInteriorLocalTable_payload_le_budget_of_size_ge
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size) :
    (concreteBPRelativeRmmInteriorLocalTable shape).payload.length <=
      logLogSquaredSampledDirectoryOverhead
        concreteBPRelativeRmmInteriorLocalOffsetSlots shape.size := by
  exact
    concreteBPRelativeRmmInteriorLocalTable_payload_le_budget_of_ready
      shape (concreteBPRelativeRmmInteriorReady_of_size_ge shape hsize)

theorem concreteBPRelativeRmmInteriorGlobalTable_payload_le_budget_of_ready
    (shape : Cartesian.CartesianShape)
    (hready : concreteBPRelativeRmmInteriorReady shape) :
    (concreteBPRelativeRmmInteriorGlobalTable shape).payload.length <=
      logLogSampledDirectoryOverhead
        concreteBPRelativeRmmInteriorGlobalMacroSlots shape.size := by
  let base := canonicalBPRelativeSummaryBase shape
  let logBase := Nat.log2 base + 1
  let blockCount := canonicalBPRelativeSummaryBlockCount shape
  let macroCount := concreteBPRelativeRmmInteriorMacroCount shape
  let macroSize := concreteBPRelativeRmmInteriorMacroSize shape
  let levelCount := concreteBPRelativeRmmInteriorGlobalLevelCount shape
  let blockWidth := concreteBPRelativeRmmInteriorBlockWidth shape
  have hactive :=
    concreteBPRelativeRmmInteriorReady_active hready
  have hbasePos : 0 < base := by
    simp [base, canonicalBPRelativeSummaryBase]
  have hlogPos : 1 <= logBase := by
    simp [logBase]
  have hmacroCells :
      macroCount * macroSize <= 2 * blockCount := by
    simpa [macroCount, macroSize, blockCount] using
      concreteBPRelativeRmmInteriorMacroCover_le_two_blockCount_of_ready
        hready
  have hmacroCellsBase :
      macroCount * (base * base) <= 2 * blockCount := by
    simpa [macroCount, macroSize, blockCount,
      concreteBPRelativeRmmInteriorMacroSize, base,
      canonicalBPRelativeSummaryBase, Nat.mul_assoc, Nat.mul_left_comm,
      Nat.mul_comm] using hmacroCells
  have hlevel :
      levelCount <= base + 1 := by
    simpa [levelCount, base] using
      concreteBPRelativeRmmInteriorGlobalLevelCount_le_base_succ_of_ready
        hready
  have hwidth :
      blockWidth <= base := by
    simpa [blockWidth, base] using
      concreteBPRelativeRmmInteriorBlockWidth_le_base_of_ready hready
  have hlevelWidth :
      levelCount * blockWidth <= (base + 1) * base :=
    Nat.mul_le_mul hlevel hwidth
  have hbasePair :
      (base + 1) * base <= 2 * (base * base) := by
    have hbaseLeSquare : base <= base * base := by
      calc
        base = 1 * base := by simp
        _ <= base * base :=
          Nat.mul_le_mul_right base (by exact hbasePos)
    calc
      (base + 1) * base = base * base + base := by
        rw [Nat.mul_comm, Nat.mul_add, Nat.mul_one]
      _ <= base * base + base * base :=
        Nat.add_le_add_left hbaseLeSquare (base * base)
      _ = 2 * (base * base) := by
        omega
  have hmacroPair :
      macroCount * ((base + 1) * base) <= 4 * blockCount := by
    have hleft :=
      Nat.mul_le_mul_left macroCount hbasePair
    have hright :=
      Nat.mul_le_mul_left 2 hmacroCellsBase
    exact Nat.le_trans hleft
      (by
        calc
          macroCount * (2 * (base * base)) =
              2 * (macroCount * (base * base)) := by
            simp [Nat.mul_assoc, Nat.mul_comm]
          _ <= 2 * (2 * blockCount) := hright
          _ = 4 * blockCount := by
            omega)
  have hactual :
      (levelCount * macroCount) * blockWidth <=
        4 * blockCount := by
    have hmul :=
      Nat.mul_le_mul_left macroCount hlevelWidth
    exact Nat.le_trans
      (by
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
          hmul)
      hmacroPair
  have hbudgetNorm :
      4 * blockCount <= 32 * (blockCount * logBase) := by
    have hblockLog : blockCount <= blockCount * logBase := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left blockCount hlogPos
    have hfourLog : 4 * blockCount <= 4 * (blockCount * logBase) :=
      Nat.mul_le_mul_left 4 hblockLog
    have hfourLe :
        4 * (blockCount * logBase) <=
          32 * (blockCount * logBase) :=
      Nat.mul_le_mul_right (blockCount * logBase)
        (by decide : 4 <= 32)
    exact Nat.le_trans hfourLog hfourLe
  have hpayload :=
    (concreteBPRelativeRmmInteriorGlobalTable shape).payload_length
  rw [hpayload]
  exact Nat.le_trans hactual
    (by
      simpa [logLogSampledDirectoryOverhead,
        concreteBPRelativeRmmInteriorGlobalMacroSlots,
        canonicalBPRelativeSummaryBlockCount,
        canonicalBPRelativeSummaryBlockCountRaw,
        canonicalBPRelativeSummaryBase, blockCount, base, logBase, hactive,
        Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hbudgetNorm)

theorem concreteBPRelativeRmmInteriorGlobalTable_payload_le_budget_of_size_ge
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size) :
    (concreteBPRelativeRmmInteriorGlobalTable shape).payload.length <=
      logLogSampledDirectoryOverhead
        concreteBPRelativeRmmInteriorGlobalMacroSlots shape.size := by
  exact
    concreteBPRelativeRmmInteriorGlobalTable_payload_le_budget_of_ready
      shape (concreteBPRelativeRmmInteriorReady_of_size_ge shape hsize)

/--
Legacy diagnostic slot for the retired all-pairs interior witness table. The
public all-size compact-close interior route no longer dispatches to this
table; it uses Ready/two-level replay, active bounded summary scan, or inactive
pure-none replay instead.
-/
def finiteSmallInteriorRangeSlot
    (blockCount startBlock count : Nat) : Nat :=
  if 0 < count /\ startBlock + count <= blockCount then
    densePairSlot (blockCount + 1) startBlock count
  else
    (blockCount + 1) * (blockCount + 1)

def finiteSmallInteriorRanges (blockCount : Nat) : List (Nat × Nat) :=
    (List.range ((blockCount + 1) * (blockCount + 1))).map fun slot =>
    (slot / (blockCount + 1), slot % (blockCount + 1))

theorem finiteSmallInteriorRanges_get?_of_valid
    {blockCount startBlock count : Nat}
    (hcount : 0 < count)
    (hbound : startBlock + count <= blockCount) :
    (finiteSmallInteriorRanges blockCount)[
        finiteSmallInteriorRangeSlot blockCount startBlock count]? =
      some (startBlock, count) := by
  have hstart : startBlock < blockCount + 1 := by omega
  have hcountLt : count < blockCount + 1 := by omega
  have hslot :
      densePairSlot (blockCount + 1) startBlock count <
        (blockCount + 1) * (blockCount + 1) :=
    densePairSlot_lt hstart hcountLt
  have hslotGet :
      (List.range ((blockCount + 1) * (blockCount + 1)))[
          densePairSlot (blockCount + 1) startBlock count]? =
        some (densePairSlot (blockCount + 1) startBlock count) := by
    exact List.getElem?_range hslot
  have hdiv :
      densePairSlot (blockCount + 1) startBlock count /
          (blockCount + 1) =
        startBlock :=
    densePairSlot_div hcountLt
  have hmod :
      densePairSlot (blockCount + 1) startBlock count %
          (blockCount + 1) =
        count :=
    densePairSlot_mod hcountLt
  have hcond :
      0 < count /\ startBlock + count <= blockCount := ⟨hcount, hbound⟩
  simp [finiteSmallInteriorRanges, finiteSmallInteriorRangeSlot, hcond,
    List.getElem?_map, hslotGet, hdiv, hmod]

def concreteBPFiniteSmallInteriorRangeMinTable
    (shape : Cartesian.CartesianShape) :
    PayloadLiveBPRangeArgMinWitnessTable shape
      (canonicalBPRelativeSummaryBlockSize shape)
      (SuccinctRank.machineWordBits shape.bpCode.length)
      (2 *
        ((finiteSmallInteriorRanges
            (canonicalBPRelativeSummaryBlockCount shape)).length *
          SuccinctRank.machineWordBits shape.bpCode.length))
      (finiteSmallInteriorRanges
        (canonicalBPRelativeSummaryBlockCount shape)) :=
  concreteBPRangeArgMinWitnessTable shape
    (canonicalBPRelativeSummaryBlockSize shape)
    (SuccinctRank.machineWordBits shape.bpCode.length)
    (finiteSmallInteriorRanges
      (canonicalBPRelativeSummaryBlockCount shape))
    (by
      simpa [SuccinctRank.machineWordBits] using
        (Nat.lt_log2_self (n := shape.bpCode.length)))

theorem concreteBPFiniteSmallInteriorRangeMinTable_exact
    (shape : Cartesian.CartesianShape)
    {startBlock count : Nat}
    (hcount : 0 < count)
    (hbound :
      startBlock + count <=
        canonicalBPRelativeSummaryBlockCount shape) :
    ((concreteBPFiniteSmallInteriorRangeMinTable shape).rangeWitnessCosted
        (finiteSmallInteriorRangeSlot
          (canonicalBPRelativeSummaryBlockCount shape)
          startBlock count)).erase =
      some
        (bpRangeMinExcess shape
          (canonicalBPRelativeSummaryBlockSize shape) startBlock count,
          bpRangeArgMinPrefixPos shape
            (canonicalBPRelativeSummaryBlockSize shape) startBlock count) := by
  let blockCount := canonicalBPRelativeSummaryBlockCount shape
  let blockSize := canonicalBPRelativeSummaryBlockSize shape
  let slot := finiteSmallInteriorRangeSlot blockCount startBlock count
  let ranges := finiteSmallInteriorRanges blockCount
  have hget :
      ranges[slot]? = some (startBlock, count) := by
    simpa [blockCount, slot, ranges] using
      finiteSmallInteriorRanges_get?_of_valid
        (blockCount := blockCount) (startBlock := startBlock)
        (count := count) hcount (by simpa [blockCount] using hbound)
  have hmin :
      (bpRangeMinExcessEntries shape blockSize ranges)[slot]? =
        some (bpRangeMinExcess shape blockSize startBlock count) := by
    exact bpRangeMinExcessEntries_get?_of_ranges_get?
      (shape := shape) (blockSize := blockSize) hget
  have harg :
      (bpRangeArgMinPrefixPosEntries shape blockSize ranges)[slot]? =
        some (bpRangeArgMinPrefixPos shape blockSize startBlock count) := by
    exact bpRangeArgMinPrefixPosEntries_get?_of_ranges_get?
      (shape := shape) (blockSize := blockSize) hget
  simpa [concreteBPFiniteSmallInteriorRangeMinTable, blockCount, blockSize,
    slot, ranges, hmin, harg] using
    (concreteBPFiniteSmallInteriorRangeMinTable shape).rangeWitnessCosted_erase
      slot

theorem concreteBPRelativeRmmInterior_size_lt_readyThreshold_of_not_ready
    {shape : Cartesian.CartesianShape}
    (hnotReady : ¬ concreteBPRelativeRmmInteriorReady shape) :
    shape.size < concreteBPRelativeRmmInteriorReadyThreshold := by
  exact Nat.lt_of_not_ge (by
    intro hsize
    exact hnotReady
      (concreteBPRelativeRmmInteriorReady_of_size_ge_readyThreshold
        shape hsize))

theorem concreteBPRelativeRmmInterior_size_lt_of_not_ready
    {shape : Cartesian.CartesianShape}
    (hnotReady : ¬ concreteBPRelativeRmmInteriorReady shape) :
    shape.size < 2 ^ 128 := by
  have hsmall :=
    concreteBPRelativeRmmInterior_size_lt_readyThreshold_of_not_ready
      hnotReady
  have hthreshold : concreteBPRelativeRmmInteriorReadyThreshold <= 2 ^ 128 := by
    unfold concreteBPRelativeRmmInteriorReadyThreshold
    exact Nat.pow_le_pow_right (by omega : 0 < 2) (by omega)
  exact Nat.lt_of_lt_of_le hsmall hthreshold

theorem canonicalBPRelativeSummaryBlockSize_eq_zero_of_not_active
    {shape : Cartesian.CartesianShape}
    (hnotActive :
      ¬ canonicalBPRelativeMinMaxArgSummaryTableActive shape) :
    canonicalBPRelativeSummaryBlockSize shape = 0 := by
  simp [canonicalBPRelativeSummaryBlockSize, hnotActive]

theorem canonicalBPRelativeSummaryBlockCount_eq_zero_of_not_active
    {shape : Cartesian.CartesianShape}
    (hnotActive :
      ¬ canonicalBPRelativeMinMaxArgSummaryTableActive shape) :
    canonicalBPRelativeSummaryBlockCount shape = 0 := by
  simp [canonicalBPRelativeSummaryBlockCount, hnotActive]

theorem canonicalBPRelativeSummaryBlockCount_le_size_of_active
    {shape : Cartesian.CartesianShape}
    (hactive : canonicalBPRelativeMinMaxArgSummaryTableActive shape) :
    canonicalBPRelativeSummaryBlockCount shape <= shape.size := by
  have hraw :
      canonicalBPRelativeSummaryBlockCountRaw shape <= shape.size := by
    unfold canonicalBPRelativeSummaryBlockCountRaw
    exact Nat.div_le_self _ _
  simpa [canonicalBPRelativeSummaryBlockCount, hactive] using hraw

theorem concreteBPRelativeRmmInteriorSummaryPayload_le_overhead_of_active
    {shape : Cartesian.CartesianShape}
    (hactive : canonicalBPRelativeMinMaxArgSummaryTableActive shape) :
    (concreteBPRelativeMinMaxArgSummaryTable_canonical shape).payload.length <=
      concreteBPRelativeRmmInteriorOverhead shape.size := by
  have hsummary :=
    concreteBPRelativeMinMaxArgSummaryTable_canonical_compact_payload_profile_of_active
      shape hactive
  have hle :
      compactBPCloseSummaryPayloadOverhead
          canonicalBPRelativeSummaryBlockSlots 0 0
          canonicalBPRelativeSummarySuperSlots shape.size <=
        concreteBPRelativeRmmInteriorOverhead shape.size := by
    unfold concreteBPRelativeRmmInteriorOverhead
    omega
  exact Nat.le_trans hsummary.2.2.2.2.2.2.1 hle

theorem concreteBPRelativeRmmInteriorSmallScanCost_le_activeNotReadySmallScanQueryCost
    {shape : Cartesian.CartesianShape}
    (hactive : canonicalBPRelativeMinMaxArgSummaryTableActive shape)
    (hnotReady : ¬ concreteBPRelativeRmmInteriorReady shape) :
    4 * canonicalBPRelativeSummaryBlockCount shape <=
      concreteBPRelativeRmmInteriorActiveNotReadySmallScanQueryCost := by
  have hcountLt :=
    concreteBPRelativeRmmInteriorBlockCount_lt_macroSize_of_active_not_ready
      hactive hnotReady
  have hmacroLe :=
    concreteBPRelativeRmmInteriorMacroSize_le_activeNotReadyBlockBound_of_active_not_ready
      hactive hnotReady
  have hmacroLe' :
      concreteBPRelativeRmmInteriorMacroSize shape <= 121 := by
    simpa [concreteBPRelativeRmmInteriorActiveNotReadyBaseBound] using
      hmacroLe
  have hblockLe :
      canonicalBPRelativeSummaryBlockCount shape <= 120 := by
    omega
  simpa [concreteBPRelativeRmmInteriorActiveNotReadySmallScanQueryCost,
    concreteBPRelativeRmmInteriorActiveNotReadyBaseBound] using
    Nat.mul_le_mul_left 4 hblockLe

theorem concreteBPRelativeRmmInteriorSmallScanCost_le_threshold
    {shape : Cartesian.CartesianShape}
    (hactive : canonicalBPRelativeMinMaxArgSummaryTableActive shape)
    (hnotReady : ¬ concreteBPRelativeRmmInteriorReady shape) :
    4 * canonicalBPRelativeSummaryBlockCount shape <=
      concreteBPRelativeRmmInteriorSmallScanQueryCost := by
  exact Nat.le_trans
    (concreteBPRelativeRmmInteriorSmallScanCost_le_activeNotReadySmallScanQueryCost
      hactive hnotReady)
    concreteBPRelativeRmmInteriorActiveNotReadySmallScanQueryCost_le_smallScanQueryCost

def concreteBPRelativeRmmInteriorDirectoryPayloadLength
    (shape : Cartesian.CartesianShape) : Nat :=
  let base :=
    (concreteBPRelativeMinMaxArgSummaryTable_canonical shape).payload.length +
      (concreteBPRelativeRmmInteriorLocalTable shape).payload.length +
        (concreteBPRelativeRmmInteriorGlobalTable shape).payload.length
  if concreteBPRelativeRmmInteriorReady shape then
    base
  else if canonicalBPRelativeMinMaxArgSummaryTableActive shape then
    (concreteBPRelativeMinMaxArgSummaryTable_canonical shape).payload.length
  else
    0

theorem concreteBPRelativeRmmInteriorDirectoryPayloadLength_eq_summary_of_active_not_ready
    {shape : Cartesian.CartesianShape}
    (hactive : canonicalBPRelativeMinMaxArgSummaryTableActive shape)
    (hnotReady : ¬ concreteBPRelativeRmmInteriorReady shape) :
    concreteBPRelativeRmmInteriorDirectoryPayloadLength shape =
      (concreteBPRelativeMinMaxArgSummaryTable_canonical
        shape).payload.length := by
  simp [concreteBPRelativeRmmInteriorDirectoryPayloadLength, hnotReady,
    hactive]

theorem concreteBPRelativeRmmInteriorDirectoryPayloadLength_eq_zero_of_not_active
    {shape : Cartesian.CartesianShape}
    (hnotActive :
      ¬ canonicalBPRelativeMinMaxArgSummaryTableActive shape) :
    concreteBPRelativeRmmInteriorDirectoryPayloadLength shape = 0 := by
  have hnotReady : ¬ concreteBPRelativeRmmInteriorReady shape := by
    intro hready
    exact hnotActive (concreteBPRelativeRmmInteriorReady_active hready)
  simp [concreteBPRelativeRmmInteriorDirectoryPayloadLength, hnotReady,
    hnotActive]

/--
Canonical payload-live relative interior directory backed by B's charged
relative min/max/arg summary table plus the two-level local/global sparse
navigator.
-/
def concreteBPRelativeRmmInteriorDirectory
    (shape : Cartesian.CartesianShape) :
    PayloadLiveBPRelativeRmmInteriorDirectory shape
      (canonicalBPRelativeSummaryBlockSize shape)
      (canonicalBPRelativeSummaryBlockCount shape)
      (concreteBPRelativeRmmInteriorDirectoryPayloadLength shape)
      concreteBPRelativeRmmInteriorQueryCost := by
  let table := concreteBPRelativeMinMaxArgSummaryTable_canonical shape
  let localTable := concreteBPRelativeRmmInteriorLocalTable shape
  let globalTable := concreteBPRelativeRmmInteriorGlobalTable shape
  by_cases hready : concreteBPRelativeRmmInteriorReady shape
  · exact
      { payload := table.payload ++ localTable.payload ++ globalTable.payload
        payload_length_eq := by
          simp [concreteBPRelativeRmmInteriorDirectoryPayloadLength,
            localTable, globalTable, table, hready, Nat.add_assoc]
        payloadWordsRead := fun startBlock count =>
          bpTwoLevelInteriorCandidateWordsRead localTable globalTable table
            startBlock count
        rangeMinCosted := fun startBlock count =>
          bpTwoLevelInteriorCandidateCosted localTable globalTable table
            startBlock count
        rangeMin_cost_le := by
          intro startBlock count
          have hcost :=
            bpTwoLevelInteriorCandidateCosted_cost_le_thirty
              localTable globalTable table startBlock count
          exact Nat.le_trans
            (by
              simpa [concreteBPRelativeRmmInteriorReadyQueryCost] using
                hcost)
            concreteBPRelativeRmmInteriorReadyQueryCost_le_queryCost
        rangeMin_exact := by
          intro startBlock count hcount hbound
          exact
            bpTwoLevelInteriorCandidateCosted_erase_exact
              localTable globalTable table
              (concreteBPRelativeRmmInteriorMacroSize_pos shape)
              hcount hbound
              (by
                intro block hblock
                exact
                  PayloadLiveBPRelativeMinMaxArgSummaryTable.div_lt_succ_div_of_lt
                    (blockCount := canonicalBPRelativeSummaryBlockCount shape)
                    hblock)
              (by
                have hmacroSize :=
                  concreteBPRelativeRmmInteriorMacroSize_pos shape
                have hlt :=
                  Nat.lt_div_mul_add hmacroSize
                    (a := canonicalBPRelativeSummaryBlockCount shape)
                have hlt' : canonicalBPRelativeSummaryBlockCount shape <
                    (canonicalBPRelativeSummaryBlockCount shape /
                        concreteBPRelativeRmmInteriorMacroSize shape + 1) *
                      concreteBPRelativeRmmInteriorMacroSize shape := by
                  simpa [Nat.add_mul, Nat.mul_add, Nat.add_assoc,
                    Nat.add_comm, Nat.add_left_comm] using hlt
                have hle : canonicalBPRelativeSummaryBlockCount shape <=
                    (canonicalBPRelativeSummaryBlockCount shape /
                        concreteBPRelativeRmmInteriorMacroSize shape + 1) *
                      concreteBPRelativeRmmInteriorMacroSize shape :=
                  Nat.le_of_lt hlt'
                simpa [concreteBPRelativeRmmInteriorMacroCount] using hle)
              (by
                intro localCount hlocalPos hlocalLe
                have hcap :
                    localCount <
                      2 ^ concreteBPRelativeRmmInteriorLevelCount shape := by
                  have hmacroCap :=
                    concreteBPRelativeRmmInteriorOffsetWidth_capacity shape
                  unfold concreteBPRelativeRmmInteriorLevelCount
                  exact Nat.lt_of_le_of_lt hlocalLe hmacroCap
                have hsucc :=
                  natLog2_succ_le_of_pos_lt_pow hlocalPos hcap
                omega)
              (by
                intro macroSpanCount hspanPos hspanLe
                have hcap :
                    macroSpanCount <
                      2 ^
                        concreteBPRelativeRmmInteriorGlobalLevelCount shape := by
                  exact
                    Nat.lt_of_le_of_lt hspanLe
                      (concreteBPRelativeRmmInteriorGlobalLevelCount_capacity
                        shape)
                have hsucc :=
                  natLog2_succ_le_of_pos_lt_pow hspanPos hcap
                omega)
              (canonicalBPRelativeSummary_blocksPerSuper_pos shape)
              (canonicalBPRelativeSummary_cover shape)
              (by
                intro block hblock
                exact
                  canonicalBPRelativeSummary_block_div_lt_superCount
                    (shape := shape) hblock)
        read_words_length_le_machine := by
          intro startBlock count word hmem
          have hbudget :=
            concreteBPRelativeRmmInteriorDirectory_twoLevel_budget_profile_of_ready
              shape hready
          rcases hbudget with
            ⟨_hlittle, _hbudgetEq, _hpayloadBudget, _hactive,
              _hoffsetCapacity, hrelativeMachine, hblockCapacity,
              _hsummaryExact, _hbaselineRead, _hminRead, _hmaxRead,
              _hargRead⟩
          have hoffsetMachine :
              concreteBPRelativeRmmInteriorOffsetWidth shape <=
                SuccinctRank.machineWordBits shape.bpCode.length := by
            have hactive :=
              concreteBPRelativeRmmInteriorReady_active hready
            have hspan :
                2 * bpSuperblockSpan
                    (canonicalBPRelativeSummaryBlockSizeRaw shape)
                    (canonicalBPRelativeSummaryBlocksPerSuperRaw shape) <
                  2 ^ canonicalBPRelativeSummaryRelativeWidthRaw shape := by
              simpa [canonicalBPRelativeSummaryBlockSize,
                canonicalBPRelativeSummaryBlocksPerSuper,
                canonicalBPRelativeSummaryRelativeWidth, hactive] using
                canonicalBPRelativeSummary_relativeWidth_bound shape
            let base := canonicalBPRelativeSummaryBase shape
            have hbasePos : 0 < base := by
              simp [base, canonicalBPRelativeSummaryBase]
            have hbaseSqPos : 0 < base * base :=
              Nat.mul_pos hbasePos hbasePos
            have hmacroLtSpan :
                concreteBPRelativeRmmInteriorMacroSize shape <
                  2 * bpSuperblockSpan
                    (canonicalBPRelativeSummaryBlockSizeRaw shape)
                    (canonicalBPRelativeSummaryBlocksPerSuperRaw shape) := by
              have hlt4 :
                  1 * (base * base) < 4 * (base * base) := by
                exact Nat.mul_lt_mul_of_pos_right (by decide : 1 < 4)
                  hbaseSqPos
              have htwoTwo :
                  2 * (2 * (base * base)) = 4 * (base * base) := by
                omega
              rw [← htwoTwo] at hlt4
              simpa [base, concreteBPRelativeRmmInteriorMacroSize,
                canonicalBPRelativeSummaryBlockSizeRaw,
                canonicalBPRelativeSummaryBlocksPerSuperRaw,
                bpSuperblockSpan, Nat.mul_assoc, Nat.mul_left_comm,
                Nat.mul_comm] using hlt4
            have hmacroRel :
                concreteBPRelativeRmmInteriorMacroSize shape <
                  2 ^ canonicalBPRelativeSummaryRelativeWidthRaw shape :=
              Nat.lt_trans hmacroLtSpan hspan
            have hoffsetRel :
                concreteBPRelativeRmmInteriorOffsetWidth shape <=
                  canonicalBPRelativeSummaryRelativeWidthRaw shape := by
              unfold concreteBPRelativeRmmInteriorOffsetWidth
              unfold SuccinctRank.machineWordBits
              exact
                natLog2_succ_le_of_pos_lt_pow
                  (concreteBPRelativeRmmInteriorMacroSize_pos shape)
                  hmacroRel
            exact Nat.le_trans hoffsetRel hrelativeMachine
          have hblockMachine :
              concreteBPRelativeRmmInteriorBlockWidth shape <=
                SuccinctRank.machineWordBits shape.bpCode.length := by
            unfold concreteBPRelativeRmmInteriorBlockWidth
            unfold SuccinctRank.machineWordBits
            exact
              natLog2_succ_le_of_pos_lt_pow
                (by
                  have hcountPos :
                      0 < canonicalBPRelativeSummaryBlockCount shape := by
                    exact
                      canonicalBPRelativeSummaryBlockCount_pos_of_ready
                        hready
                  exact hcountPos)
                (by
                  simpa [concreteBPRelativeRmmInteriorBlockWidth,
                    SuccinctRank.machineWordBits,
                    canonicalBPRelativeSummaryBlockCount, _hactive] using
                    hblockCapacity)
          exact
            bpTwoLevelInteriorCandidateWordsRead_length_le_machine
              localTable globalTable table hoffsetMachine hblockMachine
              (canonicalBPRelativeSummary_superWidth_machine shape)
              (canonicalBPRelativeSummary_relativeWidth_machine shape)
              hmem }
  · by_cases hactive :
        canonicalBPRelativeMinMaxArgSummaryTableActive shape
    · exact
        { payload := table.payload
          payload_length_eq := by
            simp [concreteBPRelativeRmmInteriorDirectoryPayloadLength,
              table, hready, hactive]
          payloadWordsRead := fun startBlock count =>
            table.boundedSummaryRangeScanWordsRead startBlock count
          rangeMinCosted := fun startBlock count =>
            table.boundedRangeScanCosted startBlock count
          rangeMin_cost_le := by
            intro startBlock count
            have hcost :=
              table.boundedRangeScanCosted_cost_le_blockCount
                startBlock count
            have hscan :=
              concreteBPRelativeRmmInteriorSmallScanCost_le_activeNotReadySmallScanQueryCost
                hactive hready
            exact Nat.le_trans hcost
              (Nat.le_trans hscan
                (Nat.le_trans
                  concreteBPRelativeRmmInteriorActiveNotReadySmallScanQueryCost_le_smallScanQueryCost
                  concreteBPRelativeRmmInteriorSmallScanQueryCost_le_queryCost))
          rangeMin_exact := by
            intro startBlock count hcount hbound
            exact table.boundedRangeScanCosted_erase_exact
              (canonicalBPRelativeSummary_blocksPerSuper_pos shape)
              (canonicalBPRelativeSummary_cover shape)
              (by
                intro block hblock
                exact
                  canonicalBPRelativeSummary_block_div_lt_superCount
                    (shape := shape) hblock)
              hcount hbound
          read_words_length_le_machine := by
            intro startBlock count word hmem
            exact
              table.boundedSummaryRangeScanWordsRead_length_le_machine
                (canonicalBPRelativeSummary_superWidth_machine shape)
                (canonicalBPRelativeSummary_relativeWidth_machine shape)
                hmem }
    · exact
        { payload := []
          payload_length_eq := by
            simp [concreteBPRelativeRmmInteriorDirectoryPayloadLength,
              hready, hactive]
          payloadWordsRead := fun _ _ => []
          rangeMinCosted := fun _ _ => Costed.pure none
          rangeMin_cost_le := by
            intro startBlock count
            simp [Costed.pure]
          rangeMin_exact := by
            intro startBlock count hcount hbound
            have hzero :=
              canonicalBPRelativeSummaryBlockCount_eq_zero_of_not_active
                hactive
            omega
          read_words_length_le_machine := by
            intro startBlock count word hmem
            simp at hmem }

theorem concreteBPRelativeRmmInteriorDirectory_rangeMinCosted_cost_le_of_ready
    (shape : Cartesian.CartesianShape)
    (hready : concreteBPRelativeRmmInteriorReady shape)
    (startBlock count : Nat) :
    ((concreteBPRelativeRmmInteriorDirectory shape).rangeMinCosted
      startBlock count).cost <=
        concreteBPRelativeRmmInteriorReadyQueryCost := by
  unfold concreteBPRelativeRmmInteriorDirectory
  simp [hready, concreteBPRelativeRmmInteriorReadyQueryCost,
    bpTwoLevelInteriorCandidateCosted_cost_le_thirty]

theorem concreteBPRelativeRmmInteriorDirectory_rangeMinCosted_cost_le_of_active_not_ready
    (shape : Cartesian.CartesianShape)
    (hactive : canonicalBPRelativeMinMaxArgSummaryTableActive shape)
    (hnotReady : ¬ concreteBPRelativeRmmInteriorReady shape)
    (startBlock count : Nat) :
    ((concreteBPRelativeRmmInteriorDirectory shape).rangeMinCosted
      startBlock count).cost <=
        concreteBPRelativeRmmInteriorActiveNotReadySmallScanQueryCost := by
  unfold concreteBPRelativeRmmInteriorDirectory
  simp [hnotReady, hactive]
  exact Nat.le_trans
    ((concreteBPRelativeMinMaxArgSummaryTable_canonical shape).boundedRangeScanCosted_cost_le_blockCount
      startBlock count)
    (concreteBPRelativeRmmInteriorSmallScanCost_le_activeNotReadySmallScanQueryCost
      hactive hnotReady)

theorem concreteBPRelativeRmmInteriorDirectory_profile_of_ready
    (shape : Cartesian.CartesianShape)
    (hready : concreteBPRelativeRmmInteriorReady shape) :
    let directory := concreteBPRelativeRmmInteriorDirectory shape
    LittleOLinear concreteBPRelativeRmmInteriorOverhead /\
      directory.payload.length <=
        concreteBPRelativeRmmInteriorOverhead shape.size /\
      (forall startBlock count,
        (directory.rangeMinCosted startBlock count).cost <=
          concreteBPRelativeRmmInteriorQueryCost) /\
      (forall {startBlock count : Nat},
        0 < count ->
          startBlock + count <=
            canonicalBPRelativeSummaryBlockCount shape ->
            (directory.rangeMinCosted startBlock count).erase =
              some
                (bpRangeMinExcess shape
                  (canonicalBPRelativeSummaryBlockSize shape)
                  startBlock count,
                  bpRangeArgMinPrefixPos shape
                    (canonicalBPRelativeSummaryBlockSize shape)
                    startBlock count)) /\
      forall {startBlock count : Nat} {word : List Bool},
        word ∈ directory.payloadWordsRead startBlock count ->
          word.length <=
            SuccinctRank.machineWordBits shape.bpCode.length := by
  let directory := concreteBPRelativeRmmInteriorDirectory shape
  let table := concreteBPRelativeMinMaxArgSummaryTable_canonical shape
  let localTable := concreteBPRelativeRmmInteriorLocalTable shape
  let globalTable := concreteBPRelativeRmmInteriorGlobalTable shape
  let localOffsetBudget :=
    logLogSquaredSampledDirectoryOverhead
      concreteBPRelativeRmmInteriorLocalOffsetSlots shape.size
  let globalMacroBudget :=
    logLogSampledDirectoryOverhead
      concreteBPRelativeRmmInteriorGlobalMacroSlots shape.size
  let topRoutingBudget :=
    sampledDirectoryOverhead concreteBPRelativeRmmInteriorTopSlots shape.size
  have hbudget :=
    concreteBPRelativeRmmInteriorDirectory_twoLevel_budget_profile_of_ready
      shape hready
  rcases hbudget with
    ⟨hlittle, _hbudgetEq, hpayloadReserve, _hactive, _hoffsetCapacity,
      _hrelativeMachine, _hblockCapacity, _hsummaryExact, _hbaselineRead,
      _hminRead, _hmaxRead, _hargRead⟩
  have hlocalPayload :
      localTable.payload.length <= localOffsetBudget := by
    simpa [localTable, localOffsetBudget] using
      concreteBPRelativeRmmInteriorLocalTable_payload_le_budget_of_ready
        shape hready
  have hglobalPayload :
      globalTable.payload.length <= globalMacroBudget := by
    simpa [globalTable, globalMacroBudget] using
      concreteBPRelativeRmmInteriorGlobalTable_payload_le_budget_of_ready
        shape hready
  have hpayload :
      concreteBPRelativeRmmInteriorDirectoryPayloadLength shape <=
        concreteBPRelativeRmmInteriorOverhead shape.size := by
    have hsum :
        table.payload.length + localTable.payload.length +
            globalTable.payload.length <=
          table.payload.length + localOffsetBudget +
            globalMacroBudget + topRoutingBudget := by
      omega
    exact Nat.le_trans
      (by
        simpa [concreteBPRelativeRmmInteriorDirectoryPayloadLength,
          table, localTable, globalTable, hready, Nat.add_assoc] using
          hsum)
      hpayloadReserve
  have hdir := directory.profile
  exact
    ⟨hlittle,
      by
        rw [hdir.1]
        exact hpayload,
      hdir.2.1, hdir.2.2.1, hdir.2.2.2⟩

theorem concreteBPRelativeRmmInteriorDirectory_profile_allSize_structural
    (shape : Cartesian.CartesianShape) :
    let directory := concreteBPRelativeRmmInteriorDirectory shape
    LittleOLinear concreteBPRelativeRmmInteriorOverhead /\
      directory.payload.length <=
        concreteBPRelativeRmmInteriorOverhead shape.size /\
      (forall startBlock count,
        (directory.rangeMinCosted startBlock count).cost <=
          concreteBPRelativeRmmInteriorQueryCost) /\
      (forall {startBlock count : Nat},
        0 < count ->
          startBlock + count <=
            canonicalBPRelativeSummaryBlockCount shape ->
            (directory.rangeMinCosted startBlock count).erase =
              some
                (bpRangeMinExcess shape
                  (canonicalBPRelativeSummaryBlockSize shape)
                  startBlock count,
                  bpRangeArgMinPrefixPos shape
                    (canonicalBPRelativeSummaryBlockSize shape)
                    startBlock count)) /\
      forall {startBlock count : Nat} {word : List Bool},
        word ∈ directory.payloadWordsRead startBlock count ->
          word.length <=
            SuccinctRank.machineWordBits shape.bpCode.length := by
  let directory := concreteBPRelativeRmmInteriorDirectory shape
  have hdir := directory.profile
  have hpayload :
      directory.payload.length <=
        concreteBPRelativeRmmInteriorOverhead shape.size := by
    by_cases hready : concreteBPRelativeRmmInteriorReady shape
    · exact
        (concreteBPRelativeRmmInteriorDirectory_profile_of_ready
          shape hready).2.1
    · by_cases hactive :
          canonicalBPRelativeMinMaxArgSummaryTableActive shape
      · have hsummary :=
          concreteBPRelativeRmmInteriorSummaryPayload_le_overhead_of_active
            hactive
        rw [hdir.1]
        simpa [concreteBPRelativeRmmInteriorDirectoryPayloadLength,
          hready, hactive] using hsummary
      · rw [hdir.1]
        simp [concreteBPRelativeRmmInteriorDirectoryPayloadLength,
          hready, hactive]
  exact
    ⟨concreteBPRelativeRmmInteriorOverhead_littleO,
      hpayload, hdir.2.1, hdir.2.2.1, hdir.2.2.2⟩

theorem concreteBPRelativeRmmInteriorDirectory_profile_of_size_ge
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size) :
    let directory := concreteBPRelativeRmmInteriorDirectory shape
    LittleOLinear concreteBPRelativeRmmInteriorOverhead /\
      directory.payload.length <=
        concreteBPRelativeRmmInteriorOverhead shape.size /\
      (forall startBlock count,
        (directory.rangeMinCosted startBlock count).cost <=
          concreteBPRelativeRmmInteriorQueryCost) /\
      (forall {startBlock count : Nat},
        0 < count ->
          startBlock + count <=
            canonicalBPRelativeSummaryBlockCount shape ->
            (directory.rangeMinCosted startBlock count).erase =
              some
                (bpRangeMinExcess shape
                  (canonicalBPRelativeSummaryBlockSize shape)
                  startBlock count,
                  bpRangeArgMinPrefixPos shape
                    (canonicalBPRelativeSummaryBlockSize shape)
                    startBlock count)) /\
      forall {startBlock count : Nat} {word : List Bool},
        word ∈ directory.payloadWordsRead startBlock count ->
          word.length <=
            SuccinctRank.machineWordBits shape.bpCode.length := by
  exact
    concreteBPRelativeRmmInteriorDirectory_profile_of_ready
      shape (concreteBPRelativeRmmInteriorReady_of_size_ge shape hsize)

theorem concreteBPRelativeRmmInteriorDirectory_profile
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size) :
    let directory := concreteBPRelativeRmmInteriorDirectory shape
    LittleOLinear concreteBPRelativeRmmInteriorOverhead /\
      directory.payload.length <=
        concreteBPRelativeRmmInteriorOverhead shape.size /\
      (forall startBlock count,
        (directory.rangeMinCosted startBlock count).cost <=
          concreteBPRelativeRmmInteriorQueryCost) /\
      (forall {startBlock count : Nat},
        0 < count ->
          startBlock + count <=
            canonicalBPRelativeSummaryBlockCount shape ->
            (directory.rangeMinCosted startBlock count).erase =
              some
                (bpRangeMinExcess shape
                  (canonicalBPRelativeSummaryBlockSize shape)
                  startBlock count,
                  bpRangeArgMinPrefixPos shape
                    (canonicalBPRelativeSummaryBlockSize shape)
                    startBlock count)) /\
      forall {startBlock count : Nat} {word : List Bool},
        word ∈ directory.payloadWordsRead startBlock count ->
          word.length <=
            SuccinctRank.machineWordBits shape.bpCode.length := by
  exact concreteBPRelativeRmmInteriorDirectory_profile_of_size_ge shape hsize

/-!
## Total canonical-layout interior directory

The U2 directory below instantiates the two-level rmM hierarchy directly from
`RelativeRmm.canonicalLayout` for every shape. Small layouts degenerate
through the same macro arithmetic; there is no readiness dispatch.
-/

def canonicalRelativeRmmSummaryTable
    (shape : Cartesian.CartesianShape) :
    let layout := RelativeRmm.canonicalLayout shape
    PayloadLiveBPRelativeMinMaxArgSummaryTable shape
      layout.blockSize layout.blocksPerSuper layout.blockCount
      layout.superSampleCount (layout.superWidth shape) layout.relativeWidth
      (layout.superSampleCount * layout.superWidth shape +
        3 * (layout.blockCount * layout.relativeWidth)) := by
  let layout := RelativeRmm.canonicalLayout shape
  have hvalid := RelativeRmm.canonicalLayout_valid shape
  exact concreteBPRelativeMinMaxArgSummaryTable shape
    layout.blockSize layout.blocksPerSuper layout.blockCount
    layout.superSampleCount (layout.superWidth shape) layout.relativeWidth
    hvalid.blocksPerSuper_pos hvalid.fullBlocks_fit
    (SuccinctRank.self_lt_two_pow_machineWordBits shape.bpCode.length)
    hvalid.superSpan_fits hvalid.blockOffset_fits

def canonicalRelativeRmmInteriorLocalTable
    (shape : Cartesian.CartesianShape) :
    let layout := RelativeRmm.canonicalLayout shape
    PayloadLiveBPLocalSparseOffsetTable shape layout.blockSize
      layout.blockCount layout.macroSize layout.macroSampleCount
      layout.levelCount layout.offsetWidth
      ((layout.macroSampleCount * (layout.levelCount * layout.macroSize)) *
        layout.offsetWidth) := by
  let layout := RelativeRmm.canonicalLayout shape
  exact concreteBPLocalSparseOffsetTable shape layout.blockSize
    layout.blockCount layout.macroSize layout.macroSampleCount
    layout.levelCount layout.offsetWidth
    (SuccinctRank.self_lt_two_pow_machineWordBits layout.macroSize)

def canonicalRelativeRmmInteriorGlobalTable
    (shape : Cartesian.CartesianShape) :
    let layout := RelativeRmm.canonicalLayout shape
    PayloadLiveBPGlobalSparseBlockTable shape layout.blockSize
      layout.blockCount layout.macroSize layout.macroSampleCount
      layout.globalLevelCount layout.blockAddressWidth
      ((layout.globalLevelCount * layout.macroSampleCount) *
        layout.blockAddressWidth) := by
  let layout := RelativeRmm.canonicalLayout shape
  have hvalid := RelativeRmm.canonicalLayout_valid shape
  exact concreteBPGlobalSparseBlockTable shape layout.blockSize
    layout.blockCount layout.macroSize layout.macroSampleCount
    layout.globalLevelCount layout.blockAddressWidth hvalid.macroSize_pos
    (SuccinctRank.self_lt_two_pow_machineWordBits layout.blockCount)

/-!
### Charged sparse-level tables (B7)

Two instantiations of the generic count-indexed level/span table
(`SparseLevelTable.lean`).  The accepted interior execution presents local
counts bounded by `layout.macroSize`
(`canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation`) and global
counts bounded by `layout.macroSampleCount`
(`canonicalRelativeRmmMachineGlobalTwoSpanCandidateComputation`), so each
table's domain covers exactly the values that actually occur.  Sized
separately rather than merged, so each budget can be dominated by the
envelope its companion sparse table already uses (DD-20260718-013).
-/

/-- Charged level/span table for local counts (`count <= macroSize`). -/
def canonicalRelativeRmmInteriorLocalLevelTable
    (shape : Cartesian.CartesianShape) :
    PayloadLiveBPSparseLevelTable
      (bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize)
      (bpSparseLevelTableOverhead
        (bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize)) :=
  bpSparseLevelTable (RelativeRmm.canonicalLayout shape).macroSize

/-- Charged level/span table for global counts
(`macroSpanCount <= macroSampleCount`). -/
def canonicalRelativeRmmInteriorGlobalLevelTable
    (shape : Cartesian.CartesianShape) :
    PayloadLiveBPSparseLevelTable
      (bpSparseLevelDomain
        (RelativeRmm.canonicalLayout shape).macroSampleCount)
      (bpSparseLevelTableOverhead
        (bpSparseLevelDomain
          (RelativeRmm.canonicalLayout shape).macroSampleCount)) :=
  bpSparseLevelTable (RelativeRmm.canonicalLayout shape).macroSampleCount

/-- Counted size of the two charged level tables. -/
def canonicalRelativeRmmInteriorLevelTableOverhead
    (shape : Cartesian.CartesianShape) : Nat :=
  bpSparseLevelTableOverhead
      (bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize) +
    bpSparseLevelTableOverhead
      (bpSparseLevelDomain
        (RelativeRmm.canonicalLayout shape).macroSampleCount)

theorem canonicalRelativeRmmInteriorLocalLevelTable_payload_length
    (shape : Cartesian.CartesianShape) :
    (canonicalRelativeRmmInteriorLocalLevelTable shape).payload.length =
      bpSparseLevelTableOverhead
        (bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize) :=
  (canonicalRelativeRmmInteriorLocalLevelTable shape).payload_length

theorem canonicalRelativeRmmInteriorGlobalLevelTable_payload_length
    (shape : Cartesian.CartesianShape) :
    (canonicalRelativeRmmInteriorGlobalLevelTable shape).payload.length =
      bpSparseLevelTableOverhead
        (bpSparseLevelDomain
          (RelativeRmm.canonicalLayout shape).macroSampleCount) :=
  (canonicalRelativeRmmInteriorGlobalLevelTable shape).payload_length

def canonicalRelativeRmmInteriorDirectoryPayloadLength
    (shape : Cartesian.CartesianShape) : Nat :=
  (canonicalRelativeRmmSummaryTable shape).payload.length +
    (canonicalRelativeRmmInteriorLocalTable shape).payload.length +
      (canonicalRelativeRmmInteriorGlobalTable shape).payload.length +
        (canonicalRelativeRmmInteriorLocalLevelTable shape).payload.length +
          (canonicalRelativeRmmInteriorGlobalLevelTable shape).payload.length


/-- Machine-word stores for the four summary fields in payload order. -/
def canonicalRelativeRmmSummaryMachineStore
    (shape : Cartesian.CartesianShape) :
    let table := canonicalRelativeRmmSummaryTable shape
    BoundedPayloadWordStore
      (table.baselineTable.payload ++
        (table.minRelTable.payload ++
          (table.maxRelTable.payload ++ table.argOffsetTable.payload)))
      (SuccinctRank.machineWordBits shape.bpCode.length) := by
  let table := canonicalRelativeRmmSummaryTable shape
  let hword := SuccinctRank.machineWordBits_pos shape.bpCode.length
  exact
    BoundedPayloadWordStore.append (table.baselineTable.machineStore hword)
      (BoundedPayloadWordStore.append (table.minRelTable.machineStore hword)
        (BoundedPayloadWordStore.append (table.maxRelTable.machineStore hword)
          (table.argOffsetTable.machineStore hword)))

def canonicalRelativeRmmLocalMachineStore
    (shape : Cartesian.CartesianShape) :
    let table := canonicalRelativeRmmInteriorLocalTable shape
    BoundedPayloadWordStore table.table.payload
      (SuccinctRank.machineWordBits shape.bpCode.length) := by
  let table := canonicalRelativeRmmInteriorLocalTable shape
  let hword := SuccinctRank.machineWordBits_pos shape.bpCode.length
  exact table.table.machineStore hword

def canonicalRelativeRmmGlobalMachineStore
    (shape : Cartesian.CartesianShape) :
    let table := canonicalRelativeRmmInteriorGlobalTable shape
    BoundedPayloadWordStore table.table.payload
      (SuccinctRank.machineWordBits shape.bpCode.length) := by
  let table := canonicalRelativeRmmInteriorGlobalTable shape
  let hword := SuccinctRank.machineWordBits_pos shape.bpCode.length
  exact table.table.machineStore hword

/-- Machine-word store for the charged local level/span table (B7). -/
def canonicalRelativeRmmLocalLevelMachineStore
    (shape : Cartesian.CartesianShape) :
    let table := canonicalRelativeRmmInteriorLocalLevelTable shape
    BoundedPayloadWordStore table.table.payload
      (SuccinctRank.machineWordBits shape.bpCode.length) := by
  let table := canonicalRelativeRmmInteriorLocalLevelTable shape
  let hword := SuccinctRank.machineWordBits_pos shape.bpCode.length
  exact table.table.machineStore hword

/-- Machine-word store for the charged global level/span table (B7). -/
def canonicalRelativeRmmGlobalLevelMachineStore
    (shape : Cartesian.CartesianShape) :
    let table := canonicalRelativeRmmInteriorGlobalLevelTable shape
    BoundedPayloadWordStore table.table.payload
      (SuccinctRank.machineWordBits shape.bpCode.length) := by
  let table := canonicalRelativeRmmInteriorGlobalLevelTable shape
  let hword := SuccinctRank.machineWordBits_pos shape.bpCode.length
  exact table.table.machineStore hword

/--
One canonical bounded store for all eight fixed-width tables, in counted
directory-payload order: baseline, relative minimum, relative maximum,
arg-min offset, local sparse offset, global sparse block, local charged
level/span, global charged level/span.
-/
def canonicalRelativeRmmInteriorComponentStore
    (shape : Cartesian.CartesianShape) :
    let summary := canonicalRelativeRmmSummaryTable shape
    let localTable := canonicalRelativeRmmInteriorLocalTable shape
    let globalTable := canonicalRelativeRmmInteriorGlobalTable shape
    let localLevel := canonicalRelativeRmmInteriorLocalLevelTable shape
    let globalLevel := canonicalRelativeRmmInteriorGlobalLevelTable shape
    BoundedPayloadWordStore
      (((((summary.baselineTable.payload ++
          (summary.minRelTable.payload ++
            (summary.maxRelTable.payload ++ summary.argOffsetTable.payload))) ++
        localTable.table.payload) ++ globalTable.table.payload) ++
        localLevel.table.payload) ++ globalLevel.table.payload)
      (SuccinctRank.machineWordBits shape.bpCode.length) := by
  exact
    BoundedPayloadWordStore.append
      (BoundedPayloadWordStore.append
        (BoundedPayloadWordStore.append
          (BoundedPayloadWordStore.append
            (canonicalRelativeRmmSummaryMachineStore shape)
            (canonicalRelativeRmmLocalMachineStore shape))
          (canonicalRelativeRmmGlobalMachineStore shape))
        (canonicalRelativeRmmLocalLevelMachineStore shape))
      (canonicalRelativeRmmGlobalLevelMachineStore shape)

/-- Explicit flat word offsets for the eight directory components. -/
structure CanonicalRelativeRmmInteriorComponentOffsets where
  baseline : Nat
  minRel : Nat
  maxRel : Nat
  argOffset : Nat
  localOffset : Nat
  globalBlock : Nat
  localLevel : Nat
  globalLevel : Nat
  deadAddress : Nat
deriving Repr, DecidableEq

def canonicalRelativeRmmInteriorComponentOffsets
    (shape : Cartesian.CartesianShape) :
    CanonicalRelativeRmmInteriorComponentOffsets :=
  let hword := SuccinctRank.machineWordBits_pos shape.bpCode.length
  let summary := canonicalRelativeRmmSummaryTable shape
  let baselineWords :=
    (summary.baselineTable.machineStore hword).store.words.size
  let minRelWords :=
    (summary.minRelTable.machineStore hword).store.words.size
  let maxRelWords :=
    (summary.maxRelTable.machineStore hword).store.words.size
  let argOffsetWords :=
    (summary.argOffsetTable.machineStore hword).store.words.size
  let localWords :=
    (canonicalRelativeRmmLocalMachineStore shape).store.words.size
  let globalWords :=
    (canonicalRelativeRmmGlobalMachineStore shape).store.words.size
  let localLevelWords :=
    (canonicalRelativeRmmLocalLevelMachineStore shape).store.words.size
  { baseline := 0
    minRel := baselineWords
    maxRel := baselineWords + minRelWords
    argOffset := baselineWords + minRelWords + maxRelWords
    localOffset := baselineWords + minRelWords + maxRelWords + argOffsetWords
    globalBlock :=
      baselineWords + minRelWords + maxRelWords + argOffsetWords + localWords
    localLevel :=
      baselineWords + minRelWords + maxRelWords + argOffsetWords + localWords +
        globalWords
    globalLevel :=
      baselineWords + minRelWords + maxRelWords + argOffsetWords + localWords +
        globalWords + localLevelWords
    deadAddress :=
      (canonicalRelativeRmmInteriorComponentStore shape).store.words.size }

theorem canonicalRelativeRmmInteriorComponentStore_flattens_payload
    (shape : Cartesian.CartesianShape) :
    flattenPayloadWords
        (canonicalRelativeRmmInteriorComponentStore
          shape).store.words.toList =
      (canonicalRelativeRmmSummaryTable shape).payload ++
        (canonicalRelativeRmmInteriorLocalTable shape).payload ++
          (canonicalRelativeRmmInteriorGlobalTable shape).payload ++
            (canonicalRelativeRmmInteriorLocalLevelTable shape).payload ++
              (canonicalRelativeRmmInteriorGlobalLevelTable shape).payload := by
  simpa [PayloadLiveBPRelativeMinMaxArgSummaryTable.payload,
    PayloadLiveBPLocalSparseOffsetTable.payload,
    PayloadLiveBPGlobalSparseBlockTable.payload,
    PayloadLiveBPSparseLevelTable.payload] using
    (canonicalRelativeRmmInteriorComponentStore shape).erases

theorem canonicalRelativeRmmInteriorComponentStore_words_toList
    (shape : Cartesian.CartesianShape) :
    (canonicalRelativeRmmInteriorComponentStore shape).store.words.toList =
      let hword := SuccinctRank.machineWordBits_pos shape.bpCode.length
      let summary := canonicalRelativeRmmSummaryTable shape
      (summary.baselineTable.machineStore hword).store.words.toList ++
        (summary.minRelTable.machineStore hword).store.words.toList ++
          (summary.maxRelTable.machineStore hword).store.words.toList ++
            (summary.argOffsetTable.machineStore hword).store.words.toList ++
              ((canonicalRelativeRmmInteriorLocalTable
                shape).table.machineStore hword).store.words.toList ++
                ((canonicalRelativeRmmInteriorGlobalTable
                  shape).table.machineStore hword).store.words.toList ++
                  ((canonicalRelativeRmmInteriorLocalLevelTable
                    shape).table.machineStore hword).store.words.toList ++
                    ((canonicalRelativeRmmInteriorGlobalLevelTable
                      shape).table.machineStore hword).store.words.toList := by
  simp [canonicalRelativeRmmInteriorComponentStore,
    canonicalRelativeRmmSummaryMachineStore,
    canonicalRelativeRmmLocalMachineStore,
    canonicalRelativeRmmGlobalMachineStore,
    canonicalRelativeRmmLocalLevelMachineStore,
    canonicalRelativeRmmGlobalLevelMachineStore,
    BoundedPayloadWordStore.append]

theorem canonicalRelativeRmmInteriorComponentStore_words_size_eq
    (shape : Cartesian.CartesianShape) :
    (canonicalRelativeRmmInteriorComponentStore shape).store.words.size =
      let hword := SuccinctRank.machineWordBits_pos shape.bpCode.length
      let summary := canonicalRelativeRmmSummaryTable shape
      (summary.baselineTable.machineStore hword).store.words.size +
        ((summary.minRelTable.machineStore hword).store.words.size +
          ((summary.maxRelTable.machineStore hword).store.words.size +
            ((summary.argOffsetTable.machineStore hword).store.words.size +
              (((canonicalRelativeRmmInteriorLocalTable
                shape).table.machineStore hword).store.words.size +
                (((canonicalRelativeRmmInteriorGlobalTable
                  shape).table.machineStore hword).store.words.size +
                  (((canonicalRelativeRmmInteriorLocalLevelTable
                    shape).table.machineStore hword).store.words.size +
                    ((canonicalRelativeRmmInteriorGlobalLevelTable
                      shape).table.machineStore hword).store.words.size)))))) := by
  have h := congrArg List.length
    (canonicalRelativeRmmInteriorComponentStore_words_toList shape)
  simpa using h

theorem canonicalRelativeRmmInteriorComponentStore_words_bounded
    (shape : Cartesian.CartesianShape)
    {word : List Bool}
    (hmem :
      List.Mem word
        (canonicalRelativeRmmInteriorComponentStore
          shape).store.words.toList) :
    word.length <= SuccinctRank.machineWordBits shape.bpCode.length :=
  (canonicalRelativeRmmInteriorComponentStore shape).word_length_le hmem
def canonicalRelativeRmmInteriorLogicalWordsRead
    (shape : Cartesian.CartesianShape) (startBlock count : Nat) :
    List (List Bool) :=
  bpTwoLevelInteriorCandidateWordsRead
    (canonicalRelativeRmmInteriorLocalTable shape)
    (canonicalRelativeRmmInteriorGlobalTable shape)
    (canonicalRelativeRmmSummaryTable shape) startBlock count

/-- Every logical rmM cell is represented by consecutive machine chunks. -/
def canonicalRelativeRmmInteriorWordsRead
    (shape : Cartesian.CartesianShape) (startBlock count : Nat) :
    List (List Bool) :=
  (canonicalRelativeRmmInteriorLogicalWordsRead shape startBlock count).flatMap
    (SuccinctSpace.chunkPayloadWords
      (SuccinctRank.machineWordBits shape.bpCode.length))

def canonicalRelativeRmmMachineReadNatCosted
    {entries : List Nat} {width : Nat}
    (shape : Cartesian.CartesianShape)
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (i : Nat) : Costed (Option Nat) :=
  table.machineReadCosted
    (SuccinctRank.machineWordBits_pos shape.bpCode.length) i

@[simp] theorem canonicalRelativeRmmMachineReadNatCosted_erase
    {entries : List Nat} {width : Nat}
    (shape : Cartesian.CartesianShape)
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (i : Nat) :
    (canonicalRelativeRmmMachineReadNatCosted shape table i).erase =
      (table.readCosted i).erase := by
  exact table.machineReadCosted_erase
    (SuccinctRank.machineWordBits_pos shape.bpCode.length) i

def canonicalRelativeRmmMachineSummaryCosted
    (shape : Cartesian.CartesianShape) (block : Nat) :
    Costed (Option (Nat × Nat × Nat × Nat)) :=
  let layout := RelativeRmm.canonicalLayout shape
  let table := canonicalRelativeRmmSummaryTable shape
  Costed.bind
    (canonicalRelativeRmmMachineReadNatCosted shape table.baselineTable
      (block / layout.blocksPerSuper)) fun baseline? =>
    Costed.bind
      (canonicalRelativeRmmMachineReadNatCosted shape table.minRelTable block)
      fun minRel? =>
      Costed.bind
        (canonicalRelativeRmmMachineReadNatCosted shape table.maxRelTable block)
        fun maxRel? =>
        Costed.map
          (fun argOffset? =>
            match baseline?, minRel?, maxRel?, argOffset? with
            | some baseline, some minRel, some maxRel, some argOffset =>
                some (baseline, minRel, maxRel, argOffset)
            | _, _, _, _ => none)
          (canonicalRelativeRmmMachineReadNatCosted shape table.argOffsetTable
            block)

def canonicalRelativeRmmMachineMinCandidateCosted
    (shape : Cartesian.CartesianShape) (block : Nat) :
    Costed (Option (Nat × Nat)) :=
  let layout := RelativeRmm.canonicalLayout shape
  Costed.map
    (fun summary? =>
      summary?.map
        (bpRelativeSummaryMinCandidate layout.blockSize
          layout.blocksPerSuper block))
    (canonicalRelativeRmmMachineSummaryCosted shape block)

def canonicalRelativeRmmMachineLocalSpanCandidateCosted
    (shape : Cartesian.CartesianShape)
    (macroIdx localStart level : Nat) :
    Costed (Option (Nat × Nat)) :=
  let layout := RelativeRmm.canonicalLayout shape
  let table := canonicalRelativeRmmInteriorLocalTable shape
  Costed.bind
    (canonicalRelativeRmmMachineReadNatCosted shape table.table
      (bpLocalSparseCellSlot layout.macroSize layout.levelCount
        macroIdx localStart level)) fun offset? =>
    match offset? with
    | some offset =>
        canonicalRelativeRmmMachineMinCandidateCosted shape
          (macroIdx * layout.macroSize + offset)
    | none => Costed.pure none

def canonicalRelativeRmmMachineGlobalSpanCandidateCosted
    (shape : Cartesian.CartesianShape)
    (macroStart level : Nat) :
    Costed (Option (Nat × Nat)) :=
  let layout := RelativeRmm.canonicalLayout shape
  let table := canonicalRelativeRmmInteriorGlobalTable shape
  Costed.bind
    (canonicalRelativeRmmMachineReadNatCosted shape table.table
      (bpGlobalSparseCellSlot layout.macroSampleCount
        macroStart level)) fun block? =>
    match block? with
    | some block =>
        canonicalRelativeRmmMachineMinCandidateCosted shape block
    | none => Costed.pure none

/--
The level and the span are READ from the charged level table rather than
recomputed by `Nat.log2` / `2 ^ Nat.log2`.  One charged read per two-span
call delivers both, unpacked by constant-divisor div/mod.
-/
def canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted
    (shape : Cartesian.CartesianShape)
    (macroIdx localStart count : Nat) :
    Costed (Option (Nat × Nat)) :=
  let domain :=
    bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize
  Costed.bind
    (canonicalRelativeRmmMachineReadNatCosted shape
      (canonicalRelativeRmmInteriorLocalLevelTable shape).table count)
    fun cell? =>
    match cell? with
    | some cell =>
        let level := cell / domain
        let span := cell % domain
        let rightLocalStart := localStart + count - span
        Costed.bind
          (canonicalRelativeRmmMachineLocalSpanCandidateCosted shape
            macroIdx localStart level) fun left? =>
          Costed.map (fun right? => bpCandidateMerge? left? right?)
            (canonicalRelativeRmmMachineLocalSpanCandidateCosted shape
              macroIdx rightLocalStart level)
    | none => Costed.pure none

/-- Global twin of `canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted`. -/
def canonicalRelativeRmmMachineGlobalTwoSpanCandidateCosted
    (shape : Cartesian.CartesianShape)
    (macroStart macroSpanCount : Nat) :
    Costed (Option (Nat × Nat)) :=
  let domain :=
    bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSampleCount
  Costed.bind
    (canonicalRelativeRmmMachineReadNatCosted shape
      (canonicalRelativeRmmInteriorGlobalLevelTable shape).table macroSpanCount)
    fun cell? =>
    match cell? with
    | some cell =>
        let level := cell / domain
        let spanMacros := cell % domain
        let rightMacroStart := macroStart + macroSpanCount - spanMacros
        Costed.bind
          (canonicalRelativeRmmMachineGlobalSpanCandidateCosted shape
            macroStart level) fun left? =>
          Costed.map (fun right? => bpCandidateMerge? left? right?)
            (canonicalRelativeRmmMachineGlobalSpanCandidateCosted shape
              rightMacroStart level)
    | none => Costed.pure none

def canonicalRelativeRmmMachineAdjacentMacroCandidateCosted
    (shape : Cartesian.CartesianShape)
    (macroStart localStart rightCount : Nat) :
    Costed (Option (Nat × Nat)) :=
  let layout := RelativeRmm.canonicalLayout shape
  let leftCount := layout.macroSize - localStart
  Costed.bind
    (canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted shape
      macroStart localStart leftCount) fun left? =>
    Costed.map (fun right? => bpCandidateMerge? left? right?)
      (canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted shape
        (macroStart + 1) 0 rightCount)

def canonicalRelativeRmmMachineLeftMiddleMacroCandidateCosted
    (shape : Cartesian.CartesianShape)
    (macroStart localStart middleMacroCount : Nat) :
    Costed (Option (Nat × Nat)) :=
  let layout := RelativeRmm.canonicalLayout shape
  let leftCount := layout.macroSize - localStart
  Costed.bind
    (canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted shape
      macroStart localStart leftCount) fun left? =>
    Costed.map (fun middle? => bpCandidateMerge? left? middle?)
      (canonicalRelativeRmmMachineGlobalTwoSpanCandidateCosted shape
        (macroStart + 1) middleMacroCount)

def canonicalRelativeRmmMachineCrossMacroCandidateCosted
    (shape : Cartesian.CartesianShape)
    (macroStart localStart middleMacroCount rightCount : Nat) :
    Costed (Option (Nat × Nat)) :=
  let layout := RelativeRmm.canonicalLayout shape
  let leftCount := layout.macroSize - localStart
  let rightMacroStart := macroStart + 1 + middleMacroCount
  Costed.bind
    (canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted shape
      macroStart localStart leftCount) fun left? =>
    Costed.bind
      (canonicalRelativeRmmMachineGlobalTwoSpanCandidateCosted shape
        (macroStart + 1) middleMacroCount) fun middle? =>
      Costed.map
        (fun right? => bpCandidateMerge3? left? middle? right?)
        (canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted shape
          rightMacroStart 0 rightCount)

def canonicalRelativeRmmInteriorQueryCost : Nat := 264

/--
The U3 all-size cap for the physical reads performed by the accepted U2
interior program.  Controller arithmetic and branching remain uncharged.

TIGHT AND ATTAINED.  The cap was widened `30 -> 33` by commit A ahead of the
charged sparse-level swap, so that the whole-query literal migration
`207 -> 210` and the sparse-level store extension could land as two
separately green commits rather than one unreviewable one.  The swap has now
landed and the headroom is CONSUMED: the maximizing cross-macro branch makes
three two-span calls, each charging one sparse-level read, and attains
exactly `33` in
`canonicalRelativeRmmInteriorRangeMinCosted_cost_le_thirty_three_literal_of_size_ge_four_of_bounded`.

The announced-slack theorem that recorded the staging compromise has been
DELETED, as its own docstring required: its `route <= 30` conjunct is false
once the level reads are reachable.
-/
def canonicalRelativeRmmPrincipledInteriorChargedTraceCost : Nat := 33

def canonicalRelativeRmmInteriorRangeMinCosted
    (shape : Cartesian.CartesianShape) (startBlock count : Nat) :
    Costed (Option (Prod Nat Nat)) :=
  let layout := RelativeRmm.canonicalLayout shape
  let macroStart := startBlock / layout.macroSize
  let localStart := startBlock % layout.macroSize
  if count = 0 then
    Costed.pure none
  else if count <= layout.macroSize - localStart then
    canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted shape
      macroStart localStart count
  else
    let leftCount := layout.macroSize - localStart
    let remaining := count - leftCount
    let middleMacroCount := remaining / layout.macroSize
    let rightCount := remaining % layout.macroSize
    if middleMacroCount = 0 then
      canonicalRelativeRmmMachineAdjacentMacroCandidateCosted shape
        macroStart localStart rightCount
    else if rightCount = 0 then
      canonicalRelativeRmmMachineLeftMiddleMacroCandidateCosted shape
        macroStart localStart middleMacroCount
    else
      canonicalRelativeRmmMachineCrossMacroCandidateCosted shape
        macroStart localStart middleMacroCount rightCount

@[simp] theorem canonicalRelativeRmmMachineSummaryCosted_refines
    (shape : Cartesian.CartesianShape) (block : Nat) :
    (canonicalRelativeRmmMachineSummaryCosted shape block).erase =
      ((canonicalRelativeRmmSummaryTable shape).summaryCosted block).erase := by
  simp [canonicalRelativeRmmMachineSummaryCosted,
    PayloadLiveBPRelativeMinMaxArgSummaryTable.summaryCosted,
    Costed.erase_bind, Costed.map]
  rfl

@[simp] theorem canonicalRelativeRmmMachineMinCandidateCosted_refines
    (shape : Cartesian.CartesianShape) (block : Nat) :
    (canonicalRelativeRmmMachineMinCandidateCosted shape block).erase =
      ((canonicalRelativeRmmSummaryTable shape).minCandidateCosted block).erase := by
  simp [canonicalRelativeRmmMachineMinCandidateCosted,
    PayloadLiveBPRelativeMinMaxArgSummaryTable.minCandidateCosted, Costed.map]

@[simp] theorem canonicalRelativeRmmMachineLocalSpanCandidateCosted_refines
    (shape : Cartesian.CartesianShape)
    (macroIdx localStart level : Nat) :
    (canonicalRelativeRmmMachineLocalSpanCandidateCosted shape
      macroIdx localStart level).erase =
      ((canonicalRelativeRmmInteriorLocalTable shape).spanCandidateCosted
        (canonicalRelativeRmmSummaryTable shape)
        macroIdx localStart level).erase := by
  unfold canonicalRelativeRmmMachineLocalSpanCandidateCosted
  unfold PayloadLiveBPLocalSparseOffsetTable.spanCandidateCosted
  rw [Costed.erase_bind, Costed.erase_bind]
  rw [canonicalRelativeRmmMachineReadNatCosted_erase]
  unfold PayloadLiveBPLocalSparseOffsetTable.readOffsetCosted
  generalize hvalue :
    ((canonicalRelativeRmmInteriorLocalTable shape).table.readCosted
      (bpLocalSparseCellSlot
        (RelativeRmm.canonicalLayout shape).macroSize
        (RelativeRmm.canonicalLayout shape).levelCount
        macroIdx localStart level)).erase = value
  cases value <;> simp [Costed.pure]

@[simp] theorem canonicalRelativeRmmMachineGlobalSpanCandidateCosted_refines
    (shape : Cartesian.CartesianShape)
    (macroStart level : Nat) :
    (canonicalRelativeRmmMachineGlobalSpanCandidateCosted shape
      macroStart level).erase =
      ((canonicalRelativeRmmInteriorGlobalTable shape).spanCandidateCosted
        (canonicalRelativeRmmSummaryTable shape)
        macroStart level).erase := by
  unfold canonicalRelativeRmmMachineGlobalSpanCandidateCosted
  unfold PayloadLiveBPGlobalSparseBlockTable.spanCandidateCosted
  rw [Costed.erase_bind, Costed.erase_bind]
  rw [canonicalRelativeRmmMachineReadNatCosted_erase]
  unfold PayloadLiveBPGlobalSparseBlockTable.readBlockCosted
  generalize hvalue :
    ((canonicalRelativeRmmInteriorGlobalTable shape).table.readCosted
      (bpGlobalSparseCellSlot
        (RelativeRmm.canonicalLayout shape).macroSampleCount
        macroStart level)).erase = value
  cases value <;> simp [Costed.pure]

/--
THE LEVEL VALUE-EQUIVALENCE, local instance.  The charged read reproduces the
level and the span that the accepted specification computes silently, under the
route's own domain hypothesis `count <= macroSize` - the same hypothesis the
interior dispatcher already derives from its branch guards.
-/
@[simp] theorem canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted_refines
    (shape : Cartesian.CartesianShape)
    (macroIdx localStart count : Nat)
    (hcount : count <= (RelativeRmm.canonicalLayout shape).macroSize) :
    (canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted shape
      macroIdx localStart count).erase =
      ((canonicalRelativeRmmInteriorLocalTable shape).twoSpanCandidateCosted
        (canonicalRelativeRmmSummaryTable shape)
        macroIdx localStart count).erase := by
  have hlt : count <
      bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize :=
    bpSparseLevelDomain_covers hcount
  have hdom : 2 <=
      bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize :=
    two_le_bpSparseLevelDomain _
  have hdiv := bpSparseLevelCell_div hdom hlt
  have hmod := bpSparseLevelCell_mod hdom hlt
  unfold canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted
  rw [Costed.erase_bind, canonicalRelativeRmmMachineReadNatCosted_erase,
    FixedWidthNatTable.readCosted_erase]
  simp only [bpSparseLevelEntries_getElem? hlt, hdiv, hmod]
  simp [PayloadLiveBPLocalSparseOffsetTable.twoSpanCandidateCosted,
    Costed.erase_bind, Costed.map]

/--
THE LEVEL VALUE-EQUIVALENCE, global instance.  Global twin of
`canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted_refines`.
-/
@[simp] theorem canonicalRelativeRmmMachineGlobalTwoSpanCandidateCosted_refines
    (shape : Cartesian.CartesianShape)
    (macroStart count : Nat)
    (hcount : count <= (RelativeRmm.canonicalLayout shape).macroSampleCount) :
    (canonicalRelativeRmmMachineGlobalTwoSpanCandidateCosted shape
      macroStart count).erase =
      ((canonicalRelativeRmmInteriorGlobalTable shape).twoSpanCandidateCosted
        (canonicalRelativeRmmSummaryTable shape)
        macroStart count).erase := by
  have hlt : count <
      bpSparseLevelDomain
        (RelativeRmm.canonicalLayout shape).macroSampleCount :=
    bpSparseLevelDomain_covers hcount
  have hdom : 2 <=
      bpSparseLevelDomain
        (RelativeRmm.canonicalLayout shape).macroSampleCount :=
    two_le_bpSparseLevelDomain _
  have hdiv := bpSparseLevelCell_div hdom hlt
  have hmod := bpSparseLevelCell_mod hdom hlt
  unfold canonicalRelativeRmmMachineGlobalTwoSpanCandidateCosted
  rw [Costed.erase_bind, canonicalRelativeRmmMachineReadNatCosted_erase,
    FixedWidthNatTable.readCosted_erase]
  simp only [bpSparseLevelEntries_getElem? hlt, hdiv, hmod]
  simp [PayloadLiveBPGlobalSparseBlockTable.twoSpanCandidateCosted,
    Costed.erase_bind, Costed.map]

@[simp] theorem canonicalRelativeRmmMachineAdjacentMacroCandidateCosted_refines
    (shape : Cartesian.CartesianShape)
    (macroStart localStart rightCount : Nat)
    (hright : rightCount <= (RelativeRmm.canonicalLayout shape).macroSize) :
    (canonicalRelativeRmmMachineAdjacentMacroCandidateCosted shape
      macroStart localStart rightCount).erase =
      (bpTwoLevelAdjacentMacroCandidateCosted
        (canonicalRelativeRmmInteriorLocalTable shape)
        (canonicalRelativeRmmSummaryTable shape)
        macroStart localStart rightCount).erase := by
  simp [canonicalRelativeRmmMachineAdjacentMacroCandidateCosted,
    bpTwoLevelAdjacentMacroCandidateCosted, Costed.erase_bind, Costed.map,
    canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted_refines shape
      (macroStart + 1) 0 rightCount hright]

@[simp] theorem canonicalRelativeRmmMachineLeftMiddleMacroCandidateCosted_refines
    (shape : Cartesian.CartesianShape)
    (macroStart localStart middleMacroCount : Nat)
    (hmiddle : middleMacroCount <=
      (RelativeRmm.canonicalLayout shape).macroSampleCount) :
    (canonicalRelativeRmmMachineLeftMiddleMacroCandidateCosted shape
      macroStart localStart middleMacroCount).erase =
      (bpTwoLevelLeftMiddleMacroCandidateCosted
        (canonicalRelativeRmmInteriorLocalTable shape)
        (canonicalRelativeRmmInteriorGlobalTable shape)
        (canonicalRelativeRmmSummaryTable shape)
        macroStart localStart middleMacroCount).erase := by
  simp [canonicalRelativeRmmMachineLeftMiddleMacroCandidateCosted,
    bpTwoLevelLeftMiddleMacroCandidateCosted, Costed.erase_bind, Costed.map,
    canonicalRelativeRmmMachineGlobalTwoSpanCandidateCosted_refines shape
      (macroStart + 1) middleMacroCount hmiddle]

@[simp] theorem canonicalRelativeRmmMachineCrossMacroCandidateCosted_refines
    (shape : Cartesian.CartesianShape)
    (macroStart localStart middleMacroCount rightCount : Nat)
    (hmiddle : middleMacroCount <=
      (RelativeRmm.canonicalLayout shape).macroSampleCount)
    (hright : rightCount <= (RelativeRmm.canonicalLayout shape).macroSize) :
    (canonicalRelativeRmmMachineCrossMacroCandidateCosted shape
      macroStart localStart middleMacroCount rightCount).erase =
      (bpTwoLevelCrossMacroCandidateCosted
        (canonicalRelativeRmmInteriorLocalTable shape)
        (canonicalRelativeRmmInteriorGlobalTable shape)
        (canonicalRelativeRmmSummaryTable shape)
        macroStart localStart middleMacroCount rightCount).erase := by
  simp [canonicalRelativeRmmMachineCrossMacroCandidateCosted,
    bpTwoLevelCrossMacroCandidateCosted, Costed.erase_bind, Costed.map,
    canonicalRelativeRmmMachineGlobalTwoSpanCandidateCosted_refines shape
      (macroStart + 1) middleMacroCount hmiddle,
    canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted_refines shape
      (macroStart + 1 + middleMacroCount) 0 rightCount hright]


def canonicalRelativeRmmMachineReadNatComputation
    {entries : List Nat} {width : Nat}
    (shape : Cartesian.CartesianShape)
    (table : FixedWidthNatTable entries width)
    (base i : Nat) : FlatStoreComputation (Option Nat) :=
  table.machineReadComputationAt
    (SuccinctRank.machineWordBits shape.bpCode.length) base
    (canonicalRelativeRmmInteriorComponentOffsets shape).deadAddress i

theorem canonicalRelativeRmmMachineReadNatComputation_footprint_le_dead
    (shape : Cartesian.CartesianShape)
    {entries : List Nat} {width : Nat}
    (table : FixedWidthNatTable entries width)
    (base i : Nat)
    (hbase :
      base +
          (table.machineStore
            (SuccinctRank.machineWordBits_pos shape.bpCode.length)).store.words.size <=
        (canonicalRelativeRmmInteriorComponentOffsets shape).deadAddress) :
    (canonicalRelativeRmmMachineReadNatComputation shape table base i)
      |>.FootprintWithin
        (fun address =>
          address <=
            (canonicalRelativeRmmInteriorComponentOffsets shape).deadAddress) := by
  intro store address hmem
  rcases table.machineReadComputationAt_footprint_live_or_dead
      (SuccinctRank.machineWordBits_pos shape.bpCode.length)
      store base
      (canonicalRelativeRmmInteriorComponentOffsets shape).deadAddress
      i address hmem with hlive | hdead
  · omega
  · omega

theorem canonicalRelativeRmmBaselineReadComputation_footprint_le_dead
    (shape : Cartesian.CartesianShape) (i : Nat) :
    (canonicalRelativeRmmMachineReadNatComputation shape
      (canonicalRelativeRmmSummaryTable shape).baselineTable
      (canonicalRelativeRmmInteriorComponentOffsets shape).baseline i)
      |>.FootprintWithin
        (fun address =>
          address <=
            (canonicalRelativeRmmInteriorComponentOffsets shape).deadAddress) := by
  apply canonicalRelativeRmmMachineReadNatComputation_footprint_le_dead
  simp [canonicalRelativeRmmInteriorComponentOffsets,
    canonicalRelativeRmmInteriorComponentStore_words_size_eq] <;> omega

theorem canonicalRelativeRmmMinRelReadComputation_footprint_le_dead
    (shape : Cartesian.CartesianShape) (i : Nat) :
    (canonicalRelativeRmmMachineReadNatComputation shape
      (canonicalRelativeRmmSummaryTable shape).minRelTable
      (canonicalRelativeRmmInteriorComponentOffsets shape).minRel i)
      |>.FootprintWithin
        (fun address =>
          address <=
            (canonicalRelativeRmmInteriorComponentOffsets shape).deadAddress) := by
  apply canonicalRelativeRmmMachineReadNatComputation_footprint_le_dead
  simp [canonicalRelativeRmmInteriorComponentOffsets,
    canonicalRelativeRmmInteriorComponentStore_words_size_eq] <;> omega

theorem canonicalRelativeRmmMaxRelReadComputation_footprint_le_dead
    (shape : Cartesian.CartesianShape) (i : Nat) :
    (canonicalRelativeRmmMachineReadNatComputation shape
      (canonicalRelativeRmmSummaryTable shape).maxRelTable
      (canonicalRelativeRmmInteriorComponentOffsets shape).maxRel i)
      |>.FootprintWithin
        (fun address =>
          address <=
            (canonicalRelativeRmmInteriorComponentOffsets shape).deadAddress) := by
  apply canonicalRelativeRmmMachineReadNatComputation_footprint_le_dead
  simp [canonicalRelativeRmmInteriorComponentOffsets,
    canonicalRelativeRmmInteriorComponentStore_words_size_eq] <;> omega

theorem canonicalRelativeRmmArgOffsetReadComputation_footprint_le_dead
    (shape : Cartesian.CartesianShape) (i : Nat) :
    (canonicalRelativeRmmMachineReadNatComputation shape
      (canonicalRelativeRmmSummaryTable shape).argOffsetTable
      (canonicalRelativeRmmInteriorComponentOffsets shape).argOffset i)
      |>.FootprintWithin
        (fun address =>
          address <=
            (canonicalRelativeRmmInteriorComponentOffsets shape).deadAddress) := by
  apply canonicalRelativeRmmMachineReadNatComputation_footprint_le_dead
  simp [canonicalRelativeRmmInteriorComponentOffsets,
    canonicalRelativeRmmInteriorComponentStore_words_size_eq] <;> omega

theorem canonicalRelativeRmmLocalReadComputation_footprint_le_dead
    (shape : Cartesian.CartesianShape) (i : Nat) :
    (canonicalRelativeRmmMachineReadNatComputation shape
      (canonicalRelativeRmmInteriorLocalTable shape).table
      (canonicalRelativeRmmInteriorComponentOffsets shape).localOffset i)
      |>.FootprintWithin
        (fun address =>
          address <=
            (canonicalRelativeRmmInteriorComponentOffsets shape).deadAddress) := by
  apply canonicalRelativeRmmMachineReadNatComputation_footprint_le_dead
  simp [canonicalRelativeRmmInteriorComponentOffsets,
    canonicalRelativeRmmInteriorComponentStore_words_size_eq,
    canonicalRelativeRmmLocalMachineStore] <;> omega

theorem canonicalRelativeRmmGlobalReadComputation_footprint_le_dead
    (shape : Cartesian.CartesianShape) (i : Nat) :
    (canonicalRelativeRmmMachineReadNatComputation shape
      (canonicalRelativeRmmInteriorGlobalTable shape).table
      (canonicalRelativeRmmInteriorComponentOffsets shape).globalBlock i)
      |>.FootprintWithin
        (fun address =>
          address <=
            (canonicalRelativeRmmInteriorComponentOffsets shape).deadAddress) := by
  apply canonicalRelativeRmmMachineReadNatComputation_footprint_le_dead
  simp [canonicalRelativeRmmInteriorComponentOffsets,
    canonicalRelativeRmmInteriorComponentStore_words_size_eq,
    canonicalRelativeRmmLocalMachineStore] <;> omega

theorem canonicalRelativeRmmLocalLevelReadComputation_footprint_le_dead
    (shape : Cartesian.CartesianShape) (i : Nat) :
    (canonicalRelativeRmmMachineReadNatComputation shape
      (canonicalRelativeRmmInteriorLocalLevelTable shape).table
      (canonicalRelativeRmmInteriorComponentOffsets shape).localLevel i)
      |>.FootprintWithin
        (fun address =>
          address <=
            (canonicalRelativeRmmInteriorComponentOffsets shape).deadAddress) := by
  apply canonicalRelativeRmmMachineReadNatComputation_footprint_le_dead
  simp [canonicalRelativeRmmInteriorComponentOffsets,
    canonicalRelativeRmmInteriorComponentStore_words_size_eq,
    canonicalRelativeRmmLocalMachineStore,
    canonicalRelativeRmmGlobalMachineStore,
    canonicalRelativeRmmLocalLevelMachineStore] <;> omega

theorem canonicalRelativeRmmGlobalLevelReadComputation_footprint_le_dead
    (shape : Cartesian.CartesianShape) (i : Nat) :
    (canonicalRelativeRmmMachineReadNatComputation shape
      (canonicalRelativeRmmInteriorGlobalLevelTable shape).table
      (canonicalRelativeRmmInteriorComponentOffsets shape).globalLevel i)
      |>.FootprintWithin
        (fun address =>
          address <=
            (canonicalRelativeRmmInteriorComponentOffsets shape).deadAddress) := by
  apply canonicalRelativeRmmMachineReadNatComputation_footprint_le_dead
  simp [canonicalRelativeRmmInteriorComponentOffsets,
    canonicalRelativeRmmInteriorComponentStore_words_size_eq,
    canonicalRelativeRmmLocalMachineStore,
    canonicalRelativeRmmGlobalMachineStore,
    canonicalRelativeRmmLocalLevelMachineStore] <;> omega

def canonicalRelativeRmmMachineSummaryComputation
    (shape : Cartesian.CartesianShape) (block : Nat) :
    FlatStoreComputation (Option (Prod Nat (Prod Nat (Prod Nat Nat)))) :=
  let layout := RelativeRmm.canonicalLayout shape
  let table := canonicalRelativeRmmSummaryTable shape
  let offsets := canonicalRelativeRmmInteriorComponentOffsets shape
  FlatStoreComputation.bind
    (canonicalRelativeRmmMachineReadNatComputation shape table.baselineTable
      offsets.baseline (block / layout.blocksPerSuper)) fun baseline =>
    FlatStoreComputation.bind
      (canonicalRelativeRmmMachineReadNatComputation shape table.minRelTable
        offsets.minRel block) fun minRel =>
      FlatStoreComputation.bind
        (canonicalRelativeRmmMachineReadNatComputation shape table.maxRelTable
          offsets.maxRel block) fun maxRel =>
        FlatStoreComputation.map
          (fun argOffset =>
            match baseline, minRel, maxRel, argOffset with
            | some b, some mn, some mx, some arg => some (b, mn, mx, arg)
            | _, _, _, _ => none)
          (canonicalRelativeRmmMachineReadNatComputation
            shape table.argOffsetTable offsets.argOffset block)

def canonicalRelativeRmmMachineMinCandidateComputation
    (shape : Cartesian.CartesianShape) (block : Nat) :
    FlatStoreComputation (Option (Prod Nat Nat)) :=
  let layout := RelativeRmm.canonicalLayout shape
  FlatStoreComputation.map
    (fun summary =>
      summary.map
        (bpRelativeSummaryMinCandidate layout.blockSize
          layout.blocksPerSuper block))
    (canonicalRelativeRmmMachineSummaryComputation shape block)

def canonicalRelativeRmmMachineLocalSpanCandidateComputation
    (shape : Cartesian.CartesianShape)
    (macroIdx localStart level : Nat) :
    FlatStoreComputation (Option (Prod Nat Nat)) :=
  let layout := RelativeRmm.canonicalLayout shape
  let table := canonicalRelativeRmmInteriorLocalTable shape
  let offsets := canonicalRelativeRmmInteriorComponentOffsets shape
  FlatStoreComputation.bind
    (canonicalRelativeRmmMachineReadNatComputation shape table.table
      offsets.localOffset
      (bpLocalSparseCellSlot layout.macroSize layout.levelCount
        macroIdx localStart level)) fun offset =>
    match offset with
    | some value =>
        canonicalRelativeRmmMachineMinCandidateComputation shape
          (macroIdx * layout.macroSize + value)
    | none => FlatStoreComputation.pure none

def canonicalRelativeRmmMachineGlobalSpanCandidateComputation
    (shape : Cartesian.CartesianShape)
    (macroStart level : Nat) :
    FlatStoreComputation (Option (Prod Nat Nat)) :=
  let layout := RelativeRmm.canonicalLayout shape
  let table := canonicalRelativeRmmInteriorGlobalTable shape
  let offsets := canonicalRelativeRmmInteriorComponentOffsets shape
  FlatStoreComputation.bind
    (canonicalRelativeRmmMachineReadNatComputation shape table.table
      offsets.globalBlock
      (bpGlobalSparseCellSlot layout.macroSampleCount
        macroStart level)) fun block =>
    match block with
    | some value =>
        canonicalRelativeRmmMachineMinCandidateComputation shape value
    | none => FlatStoreComputation.pure none

/--
Executed twin of `canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted`:
the level and the span come from one charged read of the level table region
of the interior component store.
-/
def canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation
    (shape : Cartesian.CartesianShape)
    (macroIdx localStart count : Nat) :
    FlatStoreComputation (Option (Prod Nat Nat)) :=
  let domain :=
    bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize
  let offsets := canonicalRelativeRmmInteriorComponentOffsets shape
  FlatStoreComputation.bind
    (canonicalRelativeRmmMachineReadNatComputation shape
      (canonicalRelativeRmmInteriorLocalLevelTable shape).table
      offsets.localLevel count) fun cell =>
    match cell with
    | some value =>
        let level := value / domain
        let span := value % domain
        let rightLocalStart := localStart + count - span
        FlatStoreComputation.bind
          (canonicalRelativeRmmMachineLocalSpanCandidateComputation
            shape macroIdx localStart level) fun left =>
          FlatStoreComputation.map (fun right => bpCandidateMerge? left right)
            (canonicalRelativeRmmMachineLocalSpanCandidateComputation
              shape macroIdx rightLocalStart level)
    | none => FlatStoreComputation.pure none

/-- Global twin of `canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation`. -/
def canonicalRelativeRmmMachineGlobalTwoSpanCandidateComputation
    (shape : Cartesian.CartesianShape)
    (macroStart macroSpanCount : Nat) :
    FlatStoreComputation (Option (Prod Nat Nat)) :=
  let domain :=
    bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSampleCount
  let offsets := canonicalRelativeRmmInteriorComponentOffsets shape
  FlatStoreComputation.bind
    (canonicalRelativeRmmMachineReadNatComputation shape
      (canonicalRelativeRmmInteriorGlobalLevelTable shape).table
      offsets.globalLevel macroSpanCount) fun cell =>
    match cell with
    | some value =>
        let level := value / domain
        let spanMacros := value % domain
        let rightMacroStart := macroStart + macroSpanCount - spanMacros
        FlatStoreComputation.bind
          (canonicalRelativeRmmMachineGlobalSpanCandidateComputation
            shape macroStart level) fun left =>
          FlatStoreComputation.map (fun right => bpCandidateMerge? left right)
            (canonicalRelativeRmmMachineGlobalSpanCandidateComputation
              shape rightMacroStart level)
    | none => FlatStoreComputation.pure none

def canonicalRelativeRmmMachineAdjacentMacroCandidateComputation
    (shape : Cartesian.CartesianShape)
    (macroStart localStart rightCount : Nat) :
    FlatStoreComputation (Option (Prod Nat Nat)) :=
  let layout := RelativeRmm.canonicalLayout shape
  let leftCount := layout.macroSize - localStart
  FlatStoreComputation.bind
    (canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation
      shape macroStart localStart leftCount) fun left =>
    FlatStoreComputation.map (fun right => bpCandidateMerge? left right)
      (canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation
        shape (macroStart + 1) 0 rightCount)

def canonicalRelativeRmmMachineLeftMiddleMacroCandidateComputation
    (shape : Cartesian.CartesianShape)
    (macroStart localStart middleMacroCount : Nat) :
    FlatStoreComputation (Option (Prod Nat Nat)) :=
  let layout := RelativeRmm.canonicalLayout shape
  let leftCount := layout.macroSize - localStart
  FlatStoreComputation.bind
    (canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation
      shape macroStart localStart leftCount) fun left =>
    FlatStoreComputation.map (fun middle => bpCandidateMerge? left middle)
      (canonicalRelativeRmmMachineGlobalTwoSpanCandidateComputation
        shape (macroStart + 1) middleMacroCount)

def canonicalRelativeRmmMachineCrossMacroCandidateComputation
    (shape : Cartesian.CartesianShape)
    (macroStart localStart middleMacroCount rightCount : Nat) :
    FlatStoreComputation (Option (Prod Nat Nat)) :=
  let layout := RelativeRmm.canonicalLayout shape
  let leftCount := layout.macroSize - localStart
  let rightMacroStart := macroStart + 1 + middleMacroCount
  FlatStoreComputation.bind
    (canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation
      shape macroStart localStart leftCount) fun left =>
    FlatStoreComputation.bind
      (canonicalRelativeRmmMachineGlobalTwoSpanCandidateComputation
        shape (macroStart + 1) middleMacroCount) fun middle =>
      FlatStoreComputation.map
        (fun right => bpCandidateMerge3? left middle right)
        (canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation
          shape rightMacroStart 0 rightCount)

def canonicalRelativeRmmInteriorRangeMinComputation
    (shape : Cartesian.CartesianShape) (startBlock count : Nat) :
    FlatStoreComputation (Option (Prod Nat Nat)) :=
  let layout := RelativeRmm.canonicalLayout shape
  let macroStart := startBlock / layout.macroSize
  let localStart := startBlock % layout.macroSize
  if count = 0 then
    FlatStoreComputation.pure none
  else if count <= layout.macroSize - localStart then
    canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation
      shape macroStart localStart count
  else
    let leftCount := layout.macroSize - localStart
    let remaining := count - leftCount
    let middleMacroCount := remaining / layout.macroSize
    let rightCount := remaining % layout.macroSize
    if middleMacroCount = 0 then
      canonicalRelativeRmmMachineAdjacentMacroCandidateComputation
        shape macroStart localStart rightCount
    else if rightCount = 0 then
      canonicalRelativeRmmMachineLeftMiddleMacroCandidateComputation
        shape macroStart localStart middleMacroCount
    else
      canonicalRelativeRmmMachineCrossMacroCandidateComputation
        shape macroStart localStart middleMacroCount rightCount

theorem canonicalRelativeRmmMachineSummaryComputation_footprint_le_dead
    (shape : Cartesian.CartesianShape) (block : Nat) :
    (canonicalRelativeRmmMachineSummaryComputation shape block)
      |>.FootprintWithin
        (fun address =>
          address <=
            (canonicalRelativeRmmInteriorComponentOffsets shape).deadAddress) := by
  unfold canonicalRelativeRmmMachineSummaryComputation
  apply FlatStoreComputation.bind_footprintWithin
  · exact canonicalRelativeRmmBaselineReadComputation_footprint_le_dead shape _
  · intro baseline
    apply FlatStoreComputation.bind_footprintWithin
    · exact canonicalRelativeRmmMinRelReadComputation_footprint_le_dead shape _
    · intro minRel
      apply FlatStoreComputation.bind_footprintWithin
      · exact canonicalRelativeRmmMaxRelReadComputation_footprint_le_dead shape _
      · intro maxRel
        apply FlatStoreComputation.map_footprintWithin
        exact canonicalRelativeRmmArgOffsetReadComputation_footprint_le_dead shape _

theorem canonicalRelativeRmmMachineMinCandidateComputation_footprint_le_dead
    (shape : Cartesian.CartesianShape) (block : Nat) :
    (canonicalRelativeRmmMachineMinCandidateComputation shape block)
      |>.FootprintWithin
        (fun address =>
          address <=
            (canonicalRelativeRmmInteriorComponentOffsets shape).deadAddress) := by
  unfold canonicalRelativeRmmMachineMinCandidateComputation
  apply FlatStoreComputation.map_footprintWithin
  exact canonicalRelativeRmmMachineSummaryComputation_footprint_le_dead shape block

theorem canonicalRelativeRmmMachineLocalSpanCandidateComputation_footprint_le_dead
    (shape : Cartesian.CartesianShape)
    (macroIdx localStart level : Nat) :
    (canonicalRelativeRmmMachineLocalSpanCandidateComputation
      shape macroIdx localStart level)
      |>.FootprintWithin
        (fun address =>
          address <=
            (canonicalRelativeRmmInteriorComponentOffsets shape).deadAddress) := by
  unfold canonicalRelativeRmmMachineLocalSpanCandidateComputation
  apply FlatStoreComputation.bind_footprintWithin
  · exact canonicalRelativeRmmLocalReadComputation_footprint_le_dead shape _
  · intro offset
    cases offset with
    | none => exact FlatStoreComputation.pure_footprintWithin _ _
    | some value =>
        exact canonicalRelativeRmmMachineMinCandidateComputation_footprint_le_dead
          shape _

theorem canonicalRelativeRmmMachineGlobalSpanCandidateComputation_footprint_le_dead
    (shape : Cartesian.CartesianShape)
    (macroStart level : Nat) :
    (canonicalRelativeRmmMachineGlobalSpanCandidateComputation
      shape macroStart level)
      |>.FootprintWithin
        (fun address =>
          address <=
            (canonicalRelativeRmmInteriorComponentOffsets shape).deadAddress) := by
  unfold canonicalRelativeRmmMachineGlobalSpanCandidateComputation
  apply FlatStoreComputation.bind_footprintWithin
  · exact canonicalRelativeRmmGlobalReadComputation_footprint_le_dead shape _
  · intro block
    cases block with
    | none => exact FlatStoreComputation.pure_footprintWithin _ _
    | some value =>
        exact canonicalRelativeRmmMachineMinCandidateComputation_footprint_le_dead
          shape _

theorem canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation_footprint_le_dead
    (shape : Cartesian.CartesianShape)
    (macroIdx localStart count : Nat) :
    (canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation
      shape macroIdx localStart count)
      |>.FootprintWithin
        (fun address =>
          address <=
            (canonicalRelativeRmmInteriorComponentOffsets shape).deadAddress) := by
  unfold canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation
  apply FlatStoreComputation.bind_footprintWithin
  · exact canonicalRelativeRmmLocalLevelReadComputation_footprint_le_dead shape _
  · intro cell?
    cases cell? with
    | none => exact FlatStoreComputation.pure_footprintWithin _ _
    | some cell =>
        apply FlatStoreComputation.bind_footprintWithin
        · exact
            canonicalRelativeRmmMachineLocalSpanCandidateComputation_footprint_le_dead
              shape _ _ _
        · intro left
          apply FlatStoreComputation.map_footprintWithin
          exact
            canonicalRelativeRmmMachineLocalSpanCandidateComputation_footprint_le_dead
              shape _ _ _

theorem canonicalRelativeRmmMachineGlobalTwoSpanCandidateComputation_footprint_le_dead
    (shape : Cartesian.CartesianShape)
    (macroStart macroSpanCount : Nat) :
    (canonicalRelativeRmmMachineGlobalTwoSpanCandidateComputation
      shape macroStart macroSpanCount)
      |>.FootprintWithin
        (fun address =>
          address <=
            (canonicalRelativeRmmInteriorComponentOffsets shape).deadAddress) := by
  unfold canonicalRelativeRmmMachineGlobalTwoSpanCandidateComputation
  apply FlatStoreComputation.bind_footprintWithin
  · exact canonicalRelativeRmmGlobalLevelReadComputation_footprint_le_dead shape _
  · intro cell?
    cases cell? with
    | none => exact FlatStoreComputation.pure_footprintWithin _ _
    | some cell =>
        apply FlatStoreComputation.bind_footprintWithin
        · exact
            canonicalRelativeRmmMachineGlobalSpanCandidateComputation_footprint_le_dead
              shape _ _
        · intro left
          apply FlatStoreComputation.map_footprintWithin
          exact
            canonicalRelativeRmmMachineGlobalSpanCandidateComputation_footprint_le_dead
              shape _ _

theorem canonicalRelativeRmmMachineAdjacentMacroCandidateComputation_footprint_le_dead
    (shape : Cartesian.CartesianShape)
    (macroStart localStart rightCount : Nat) :
    (canonicalRelativeRmmMachineAdjacentMacroCandidateComputation
      shape macroStart localStart rightCount)
      |>.FootprintWithin
        (fun address =>
          address <=
            (canonicalRelativeRmmInteriorComponentOffsets shape).deadAddress) := by
  unfold canonicalRelativeRmmMachineAdjacentMacroCandidateComputation
  apply FlatStoreComputation.bind_footprintWithin
  · exact
      canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation_footprint_le_dead
        shape _ _ _
  · intro left
    apply FlatStoreComputation.map_footprintWithin
    exact
      canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation_footprint_le_dead
        shape _ _ _

theorem canonicalRelativeRmmMachineLeftMiddleMacroCandidateComputation_footprint_le_dead
    (shape : Cartesian.CartesianShape)
    (macroStart localStart middleMacroCount : Nat) :
    (canonicalRelativeRmmMachineLeftMiddleMacroCandidateComputation
      shape macroStart localStart middleMacroCount)
      |>.FootprintWithin
        (fun address =>
          address <=
            (canonicalRelativeRmmInteriorComponentOffsets shape).deadAddress) := by
  unfold canonicalRelativeRmmMachineLeftMiddleMacroCandidateComputation
  apply FlatStoreComputation.bind_footprintWithin
  · exact
      canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation_footprint_le_dead
        shape _ _ _
  · intro left
    apply FlatStoreComputation.map_footprintWithin
    exact
      canonicalRelativeRmmMachineGlobalTwoSpanCandidateComputation_footprint_le_dead
        shape _ _

theorem canonicalRelativeRmmMachineCrossMacroCandidateComputation_footprint_le_dead
    (shape : Cartesian.CartesianShape)
    (macroStart localStart middleMacroCount rightCount : Nat) :
    (canonicalRelativeRmmMachineCrossMacroCandidateComputation
      shape macroStart localStart middleMacroCount rightCount)
      |>.FootprintWithin
        (fun address =>
          address <=
            (canonicalRelativeRmmInteriorComponentOffsets shape).deadAddress) := by
  unfold canonicalRelativeRmmMachineCrossMacroCandidateComputation
  apply FlatStoreComputation.bind_footprintWithin
  · exact
      canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation_footprint_le_dead
        shape _ _ _
  · intro left
    apply FlatStoreComputation.bind_footprintWithin
    · exact
        canonicalRelativeRmmMachineGlobalTwoSpanCandidateComputation_footprint_le_dead
          shape _ _
    · intro middle
      apply FlatStoreComputation.map_footprintWithin
      exact
        canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation_footprint_le_dead
          shape _ _ _

theorem canonicalRelativeRmmInteriorRangeMinComputation_footprint_le_dead
    (shape : Cartesian.CartesianShape) (startBlock count : Nat) :
    (canonicalRelativeRmmInteriorRangeMinComputation shape startBlock count)
      |>.FootprintWithin
        (fun address =>
          address <=
            (canonicalRelativeRmmInteriorComponentOffsets shape).deadAddress) := by
  unfold canonicalRelativeRmmInteriorRangeMinComputation
  split
  · exact FlatStoreComputation.pure_footprintWithin _ _
  · dsimp only
    split
    · exact
        canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation_footprint_le_dead
          shape _ _ _
    · split
      · exact
          canonicalRelativeRmmMachineAdjacentMacroCandidateComputation_footprint_le_dead
            shape _ _ _
      · split
        · exact
            canonicalRelativeRmmMachineLeftMiddleMacroCandidateComputation_footprint_le_dead
              shape _ _ _
        · exact
            canonicalRelativeRmmMachineCrossMacroCandidateComputation_footprint_le_dead
              shape _ _ _ _

def canonicalRelativeRmmInteriorRangeMinExecutionWithRead
    (shape : Cartesian.CartesianShape) (store : FlatWordStore)
    (startBlock count : Nat) : FlatStoreExecution (Option (Prod Nat Nat)) :=
  (canonicalRelativeRmmInteriorRangeMinComputation
    shape startBlock count).run store

def canonicalRelativeRmmInteriorRangeMinCostedWithRead
    (shape : Cartesian.CartesianShape) (store : FlatWordStore)
    (startBlock count : Nat) : Costed (Option (Prod Nat Nat)) :=
  (canonicalRelativeRmmInteriorRangeMinExecutionWithRead
    shape store startBlock count).toCosted

def canonicalRelativeRmmInteriorRangeFootprintWithRead
    (shape : Cartesian.CartesianShape) (store : FlatWordStore)
    (startBlock count : Nat) : List Nat :=
  (canonicalRelativeRmmInteriorRangeMinExecutionWithRead
    shape store startBlock count).footprint

def canonicalRelativeRmmInteriorRangeMinExecutionWithStore
    (shape : Cartesian.CartesianShape) (store : Array (List Bool))
    (startBlock count : Nat) : FlatStoreExecution (Option (Prod Nat Nat)) :=
  canonicalRelativeRmmInteriorRangeMinExecutionWithRead
    shape (FlatWordStore.ofArray store) startBlock count

def canonicalRelativeRmmInteriorRangeMinCostedWithStore
    (shape : Cartesian.CartesianShape) (store : Array (List Bool))
    (startBlock count : Nat) : Costed (Option (Prod Nat Nat)) :=
  canonicalRelativeRmmInteriorRangeMinCostedWithRead
    shape (FlatWordStore.ofArray store) startBlock count

def canonicalRelativeRmmInteriorRangeFootprintWithStore
    (shape : Cartesian.CartesianShape) (store : Array (List Bool))
    (startBlock count : Nat) : List Nat :=
  canonicalRelativeRmmInteriorRangeFootprintWithRead
    shape (FlatWordStore.ofArray store) startBlock count

/--
Pre-execution address universe for the canonical interior machine.  It covers
the input bits, valid block operands, every live component word, and the
inclusive one-past-end dead address.
-/
def canonicalRelativeRmmInteriorReviewerCapacity
    (shape : Cartesian.CartesianShape) : Nat :=
  Nat.max shape.bpCode.length
    (Nat.max (RelativeRmm.canonicalLayout shape).blockCount
      (canonicalRelativeRmmInteriorComponentStore shape).store.words.size)

def canonicalRelativeRmmInteriorReviewerWordBits
    (shape : Cartesian.CartesianShape) : Nat :=
  SuccinctRank.machineWordBits
    (canonicalRelativeRmmInteriorReviewerCapacity shape)

theorem canonicalRelativeRmmInteriorRangeFootprint_address_le_dead
    (shape : Cartesian.CartesianShape) (store : FlatWordStore)
    (startBlock count address : Nat)
    (hmem :
      List.Mem address
        (canonicalRelativeRmmInteriorRangeFootprintWithRead
          shape store startBlock count)) :
    address <=
      (canonicalRelativeRmmInteriorComponentOffsets shape).deadAddress := by
  exact
    canonicalRelativeRmmInteriorRangeMinComputation_footprint_le_dead
      shape startBlock count store address hmem

theorem canonicalRelativeRmmInteriorRangeFootprint_live_or_dead
    (shape : Cartesian.CartesianShape) (store : FlatWordStore)
    (startBlock count address : Nat)
    (hmem :
      List.Mem address
        (canonicalRelativeRmmInteriorRangeFootprintWithRead
          shape store startBlock count)) :
    address <
        (canonicalRelativeRmmInteriorComponentStore shape).store.words.size \/
      address =
        (canonicalRelativeRmmInteriorComponentOffsets shape).deadAddress := by
  have hle :=
    canonicalRelativeRmmInteriorRangeFootprint_address_le_dead
      shape store startBlock count address hmem
  have hdead :
      (canonicalRelativeRmmInteriorComponentOffsets shape).deadAddress =
        (canonicalRelativeRmmInteriorComponentStore shape).store.words.size := by
    rfl
  rw [hdead] at hle
  rcases Nat.lt_or_eq_of_le hle with hlt | heq
  · exact Or.inl hlt
  · exact Or.inr (by simpa [hdead] using heq)

theorem canonicalRelativeRmmInteriorDeadAddress_fits_reviewerWordBits
    (shape : Cartesian.CartesianShape) :
    (canonicalRelativeRmmInteriorComponentOffsets shape).deadAddress <
      2 ^ canonicalRelativeRmmInteriorReviewerWordBits shape := by
  exact Nat.lt_of_le_of_lt
    (show
      (canonicalRelativeRmmInteriorComponentOffsets shape).deadAddress <=
        canonicalRelativeRmmInteriorReviewerCapacity shape by
      unfold canonicalRelativeRmmInteriorReviewerCapacity
      rw [show
        (canonicalRelativeRmmInteriorComponentOffsets shape).deadAddress =
          (canonicalRelativeRmmInteriorComponentStore shape).store.words.size by rfl]
      exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
    (SuccinctRank.self_lt_two_pow_machineWordBits _)

theorem canonicalRelativeRmmInteriorRangeFootprint_address_fits_reviewerWordBits
    (shape : Cartesian.CartesianShape) (store : FlatWordStore)
    (startBlock count address : Nat)
    (hmem :
      List.Mem address
        (canonicalRelativeRmmInteriorRangeFootprintWithRead
          shape store startBlock count)) :
    address < 2 ^ canonicalRelativeRmmInteriorReviewerWordBits shape := by
  exact Nat.lt_of_le_of_lt
    (canonicalRelativeRmmInteriorRangeFootprint_address_le_dead
      shape store startBlock count address hmem)
    (canonicalRelativeRmmInteriorDeadAddress_fits_reviewerWordBits shape)

theorem canonicalRelativeRmmInteriorValidQuery_operands_fit_reviewerWordBits
    (shape : Cartesian.CartesianShape) {startBlock count : Nat}
    (hbound :
      startBlock + count <=
        (RelativeRmm.canonicalLayout shape).blockCount) :
    startBlock < 2 ^ canonicalRelativeRmmInteriorReviewerWordBits shape /\
      count < 2 ^ canonicalRelativeRmmInteriorReviewerWordBits shape /\
      startBlock + count <
        2 ^ canonicalRelativeRmmInteriorReviewerWordBits shape := by
  have hblocks :
      (RelativeRmm.canonicalLayout shape).blockCount <=
        canonicalRelativeRmmInteriorReviewerCapacity shape := by
    exact Nat.le_trans
      (Nat.le_max_left
        (RelativeRmm.canonicalLayout shape).blockCount
        (canonicalRelativeRmmInteriorComponentStore shape).store.words.size)
      (Nat.le_max_right _ _)
  have hcap :
      canonicalRelativeRmmInteriorReviewerCapacity shape <
        2 ^ canonicalRelativeRmmInteriorReviewerWordBits shape :=
    SuccinctRank.self_lt_two_pow_machineWordBits _
  omega

theorem canonicalRelativeRmmInteriorRangeFootprint_address_fits_threshold_boundary
    (shape : Cartesian.CartesianShape) (store : FlatWordStore)
    (startBlock count address : Nat)
    (_hboundary :
      shape.size = concreteBPRelativeRmmInteriorReadyThreshold \/
        shape.size + 1 = concreteBPRelativeRmmInteriorReadyThreshold)
    (hmem :
      List.Mem address
        (canonicalRelativeRmmInteriorRangeFootprintWithRead
          shape store startBlock count)) :
    address < 2 ^ canonicalRelativeRmmInteriorReviewerWordBits shape :=
  canonicalRelativeRmmInteriorRangeFootprint_address_fits_reviewerWordBits
    shape store startBlock count address hmem

/-- Kernel-checked empty-shape specialization of the total address theorem. -/
theorem canonicalRelativeRmmInteriorRangeFootprint_empty_kernel_checked
    (store : FlatWordStore) (address : Nat)
    (hmem :
      List.Mem address
        (canonicalRelativeRmmInteriorRangeFootprintWithRead
          Cartesian.CartesianShape.empty store 0 0)) :
    address <
      2 ^ canonicalRelativeRmmInteriorReviewerWordBits
        Cartesian.CartesianShape.empty :=
  canonicalRelativeRmmInteriorRangeFootprint_address_fits_reviewerWordBits
    Cartesian.CartesianShape.empty store 0 0 address hmem

/-- Kernel-checked singleton-shape specialization. -/
theorem canonicalRelativeRmmInteriorRangeFootprint_singleton_kernel_checked
    (store : FlatWordStore) (address : Nat)
    (hmem :
      List.Mem address
        (canonicalRelativeRmmInteriorRangeFootprintWithRead
          (Cartesian.CartesianShape.node
            Cartesian.CartesianShape.empty Cartesian.CartesianShape.empty)
          store 0 0)) :
    address <
      2 ^ canonicalRelativeRmmInteriorReviewerWordBits
        (Cartesian.CartesianShape.node
          Cartesian.CartesianShape.empty Cartesian.CartesianShape.empty) :=
  canonicalRelativeRmmInteriorRangeFootprint_address_fits_reviewerWordBits
    (Cartesian.CartesianShape.node
      Cartesian.CartesianShape.empty Cartesian.CartesianShape.empty)
    store 0 0 address hmem

/-- Kernel-checked size-two specialization. -/
theorem canonicalRelativeRmmInteriorRangeFootprint_sizeTwo_kernel_checked
    (store : FlatWordStore) (address : Nat)
    (hmem :
      List.Mem address
        (canonicalRelativeRmmInteriorRangeFootprintWithRead
          (Cartesian.CartesianShape.node
            (Cartesian.CartesianShape.node
              Cartesian.CartesianShape.empty Cartesian.CartesianShape.empty)
            Cartesian.CartesianShape.empty)
          store 0 1)) :
    address <
      2 ^ canonicalRelativeRmmInteriorReviewerWordBits
        (Cartesian.CartesianShape.node
          (Cartesian.CartesianShape.node
            Cartesian.CartesianShape.empty Cartesian.CartesianShape.empty)
          Cartesian.CartesianShape.empty) :=
  canonicalRelativeRmmInteriorRangeFootprint_address_fits_reviewerWordBits
    (Cartesian.CartesianShape.node
      (Cartesian.CartesianShape.node
        Cartesian.CartesianShape.empty Cartesian.CartesianShape.empty)
      Cartesian.CartesianShape.empty)
    store 0 1 address hmem
theorem canonicalRelativeRmmBaselineReadComputation_refines

    (shape : Cartesian.CartesianShape) (i : Nat) :
    ((canonicalRelativeRmmMachineReadNatComputation shape
        (canonicalRelativeRmmSummaryTable shape).baselineTable
        (canonicalRelativeRmmInteriorComponentOffsets shape).baseline i).run
      (canonicalRelativeRmmInteriorComponentStore shape).store.words).toCosted =
      canonicalRelativeRmmMachineReadNatCosted shape
        (canonicalRelativeRmmSummaryTable shape).baselineTable i := by
  unfold canonicalRelativeRmmMachineReadNatComputation
  unfold canonicalRelativeRmmMachineReadNatCosted
  apply FixedWidthNatTable.machineReadComputationAt_refines_machineReadCosted
  case hsegment =>
    intro localAddress hlocal
    have hlist :
        (canonicalRelativeRmmInteriorComponentStore
          shape).store.words.toList[localAddress]? =
        ((canonicalRelativeRmmSummaryTable shape).baselineTable.machineStore
          (SuccinctRank.machineWordBits_pos
            shape.bpCode.length)).store.words.toList[localAddress]? := by
      rw [canonicalRelativeRmmInteriorComponentStore_words_toList]
      simp [List.getElem?_append, hlocal]
    simpa [canonicalRelativeRmmInteriorComponentOffsets,
      Array.getElem?_toList] using hlist
  case hdead =>
    simp [canonicalRelativeRmmInteriorComponentOffsets]
theorem canonicalRelativeRmmMinRelReadComputation_refines
    (shape : Cartesian.CartesianShape) (i : Nat) :
    ((canonicalRelativeRmmMachineReadNatComputation shape
        (canonicalRelativeRmmSummaryTable shape).minRelTable
        (canonicalRelativeRmmInteriorComponentOffsets shape).minRel i).run
      (canonicalRelativeRmmInteriorComponentStore shape).store.words).toCosted =
      canonicalRelativeRmmMachineReadNatCosted shape
        (canonicalRelativeRmmSummaryTable shape).minRelTable i := by
  unfold canonicalRelativeRmmMachineReadNatComputation
  unfold canonicalRelativeRmmMachineReadNatCosted
  apply FixedWidthNatTable.machineReadComputationAt_refines_machineReadCosted
  case hsegment =>
    intro localAddress hlocal
    have hlist :
        (canonicalRelativeRmmInteriorComponentStore
          shape).store.words.toList[
            (canonicalRelativeRmmInteriorComponentOffsets shape).minRel +
              localAddress]? =
        ((canonicalRelativeRmmSummaryTable shape).minRelTable.machineStore
          (SuccinctRank.machineWordBits_pos
            shape.bpCode.length)).store.words.toList[localAddress]? := by
      rw [canonicalRelativeRmmInteriorComponentStore_words_toList]
      simp [canonicalRelativeRmmInteriorComponentOffsets,
        List.getElem?_append, hlocal] <;> omega
    simpa [Array.getElem?_toList] using hlist
  case hdead =>
    simp [canonicalRelativeRmmInteriorComponentOffsets]

theorem canonicalRelativeRmmMaxRelReadComputation_refines
    (shape : Cartesian.CartesianShape) (i : Nat) :
    ((canonicalRelativeRmmMachineReadNatComputation shape
        (canonicalRelativeRmmSummaryTable shape).maxRelTable
        (canonicalRelativeRmmInteriorComponentOffsets shape).maxRel i).run
      (canonicalRelativeRmmInteriorComponentStore shape).store.words).toCosted =
      canonicalRelativeRmmMachineReadNatCosted shape
        (canonicalRelativeRmmSummaryTable shape).maxRelTable i := by
  unfold canonicalRelativeRmmMachineReadNatComputation
  unfold canonicalRelativeRmmMachineReadNatCosted
  apply FixedWidthNatTable.machineReadComputationAt_refines_machineReadCosted
  case hsegment =>
    intro localAddress hlocal
    have hlist :
        (canonicalRelativeRmmInteriorComponentStore
          shape).store.words.toList[
            (canonicalRelativeRmmInteriorComponentOffsets shape).maxRel +
              localAddress]? =
        ((canonicalRelativeRmmSummaryTable shape).maxRelTable.machineStore
          (SuccinctRank.machineWordBits_pos
            shape.bpCode.length)).store.words.toList[localAddress]? := by
      let hword := SuccinctRank.machineWordBits_pos shape.bpCode.length
      let summary := canonicalRelativeRmmSummaryTable shape
      let baselineWords :=
        (summary.baselineTable.machineStore hword).store.words.toList
      let minRelWords :=
        (summary.minRelTable.machineStore hword).store.words.toList
      let maxRelWords :=
        (summary.maxRelTable.machineStore hword).store.words.toList
      let argWords :=
        (summary.argOffsetTable.machineStore hword).store.words.toList
      let localWords :=
        ((canonicalRelativeRmmInteriorLocalTable
          shape).table.machineStore hword).store.words.toList
      let globalWords :=
        ((canonicalRelativeRmmInteriorGlobalTable
          shape).table.machineStore hword).store.words.toList
      let localLevelWords :=
        ((canonicalRelativeRmmInteriorLocalLevelTable
          shape).table.machineStore hword).store.words.toList
      let globalLevelWords :=
        ((canonicalRelativeRmmInteriorGlobalLevelTable
          shape).table.machineStore hword).store.words.toList
      have hmiddle :
          ((baselineWords ++ minRelWords) ++ maxRelWords ++
            (argWords ++ localWords ++ globalWords ++ localLevelWords ++
              globalLevelWords))[
              (baselineWords ++ minRelWords).length + localAddress]? =
            maxRelWords[localAddress]? :=
        List.getElem?_append_middle_of_lt
          (baselineWords ++ minRelWords) maxRelWords
          (argWords ++ localWords ++ globalWords ++ localLevelWords ++
            globalLevelWords) localAddress hlocal
      rw [canonicalRelativeRmmInteriorComponentStore_words_toList]
      simpa [hword, summary, baselineWords, minRelWords, maxRelWords,
        argWords, localWords, globalWords, localLevelWords, globalLevelWords,
        canonicalRelativeRmmInteriorComponentOffsets,
        List.length_append, List.append_assoc, Nat.add_assoc] using hmiddle
    simpa [Array.getElem?_toList] using hlist
  case hdead =>
    simp [canonicalRelativeRmmInteriorComponentOffsets]

theorem canonicalRelativeRmmArgOffsetReadComputation_refines
    (shape : Cartesian.CartesianShape) (i : Nat) :
    ((canonicalRelativeRmmMachineReadNatComputation shape
        (canonicalRelativeRmmSummaryTable shape).argOffsetTable
        (canonicalRelativeRmmInteriorComponentOffsets shape).argOffset i).run
      (canonicalRelativeRmmInteriorComponentStore shape).store.words).toCosted =
      canonicalRelativeRmmMachineReadNatCosted shape
        (canonicalRelativeRmmSummaryTable shape).argOffsetTable i := by
  unfold canonicalRelativeRmmMachineReadNatComputation
  unfold canonicalRelativeRmmMachineReadNatCosted
  apply FixedWidthNatTable.machineReadComputationAt_refines_machineReadCosted
  case hsegment =>
    intro localAddress hlocal
    have hlist :
        (canonicalRelativeRmmInteriorComponentStore
          shape).store.words.toList[
            (canonicalRelativeRmmInteriorComponentOffsets shape).argOffset +
              localAddress]? =
        ((canonicalRelativeRmmSummaryTable shape).argOffsetTable.machineStore
          (SuccinctRank.machineWordBits_pos
            shape.bpCode.length)).store.words.toList[localAddress]? := by
      let hword := SuccinctRank.machineWordBits_pos shape.bpCode.length
      let summary := canonicalRelativeRmmSummaryTable shape
      let baselineWords :=
        (summary.baselineTable.machineStore hword).store.words.toList
      let minRelWords :=
        (summary.minRelTable.machineStore hword).store.words.toList
      let maxRelWords :=
        (summary.maxRelTable.machineStore hword).store.words.toList
      let argWords :=
        (summary.argOffsetTable.machineStore hword).store.words.toList
      let localWords :=
        ((canonicalRelativeRmmInteriorLocalTable
          shape).table.machineStore hword).store.words.toList
      let globalWords :=
        ((canonicalRelativeRmmInteriorGlobalTable
          shape).table.machineStore hword).store.words.toList
      let localLevelWords :=
        ((canonicalRelativeRmmInteriorLocalLevelTable
          shape).table.machineStore hword).store.words.toList
      let globalLevelWords :=
        ((canonicalRelativeRmmInteriorGlobalLevelTable
          shape).table.machineStore hword).store.words.toList
      have hmiddle :
          (((baselineWords ++ minRelWords) ++ maxRelWords) ++ argWords ++
            (localWords ++ globalWords ++ localLevelWords ++
              globalLevelWords))[
              ((baselineWords ++ minRelWords) ++ maxRelWords).length +
                localAddress]? = argWords[localAddress]? :=
        List.getElem?_append_middle_of_lt
          ((baselineWords ++ minRelWords) ++ maxRelWords) argWords
          (localWords ++ globalWords ++ localLevelWords ++ globalLevelWords)
          localAddress hlocal
      rw [canonicalRelativeRmmInteriorComponentStore_words_toList]
      simpa [hword, summary, baselineWords, minRelWords, maxRelWords,
        argWords, localWords, globalWords, localLevelWords, globalLevelWords,
        canonicalRelativeRmmInteriorComponentOffsets,
        List.length_append, List.append_assoc, Nat.add_assoc] using hmiddle
    simpa [Array.getElem?_toList] using hlist
  case hdead =>
    simp [canonicalRelativeRmmInteriorComponentOffsets]

theorem canonicalRelativeRmmLocalReadComputation_refines
    (shape : Cartesian.CartesianShape) (i : Nat) :
    ((canonicalRelativeRmmMachineReadNatComputation shape
        (canonicalRelativeRmmInteriorLocalTable shape).table
        (canonicalRelativeRmmInteriorComponentOffsets shape).localOffset i).run
      (canonicalRelativeRmmInteriorComponentStore shape).store.words).toCosted =
      canonicalRelativeRmmMachineReadNatCosted shape
        (canonicalRelativeRmmInteriorLocalTable shape).table i := by
  unfold canonicalRelativeRmmMachineReadNatComputation
  unfold canonicalRelativeRmmMachineReadNatCosted
  apply FixedWidthNatTable.machineReadComputationAt_refines_machineReadCosted
  case hsegment =>
    intro localAddress hlocal
    have hlist :
        (canonicalRelativeRmmInteriorComponentStore
          shape).store.words.toList[
            (canonicalRelativeRmmInteriorComponentOffsets shape).localOffset +
              localAddress]? =
        ((canonicalRelativeRmmInteriorLocalTable shape).table.machineStore
          (SuccinctRank.machineWordBits_pos
            shape.bpCode.length)).store.words.toList[localAddress]? := by
      let hword := SuccinctRank.machineWordBits_pos shape.bpCode.length
      let summary := canonicalRelativeRmmSummaryTable shape
      let baselineWords :=
        (summary.baselineTable.machineStore hword).store.words.toList
      let minRelWords :=
        (summary.minRelTable.machineStore hword).store.words.toList
      let maxRelWords :=
        (summary.maxRelTable.machineStore hword).store.words.toList
      let argWords :=
        (summary.argOffsetTable.machineStore hword).store.words.toList
      let localWords :=
        ((canonicalRelativeRmmInteriorLocalTable
          shape).table.machineStore hword).store.words.toList
      let globalWords :=
        ((canonicalRelativeRmmInteriorGlobalTable
          shape).table.machineStore hword).store.words.toList
      let localLevelWords :=
        ((canonicalRelativeRmmInteriorLocalLevelTable
          shape).table.machineStore hword).store.words.toList
      let globalLevelWords :=
        ((canonicalRelativeRmmInteriorGlobalLevelTable
          shape).table.machineStore hword).store.words.toList
      have hmiddle :
          ((((baselineWords ++ minRelWords) ++ maxRelWords) ++ argWords) ++
            localWords ++ (globalWords ++ localLevelWords ++
              globalLevelWords))[
              (((baselineWords ++ minRelWords) ++ maxRelWords) ++
                argWords).length + localAddress]? =
            localWords[localAddress]? :=
        List.getElem?_append_middle_of_lt
          (((baselineWords ++ minRelWords) ++ maxRelWords) ++ argWords)
          localWords (globalWords ++ localLevelWords ++ globalLevelWords)
          localAddress hlocal
      rw [canonicalRelativeRmmInteriorComponentStore_words_toList]
      simpa [hword, summary, baselineWords, minRelWords, maxRelWords,
        argWords, localWords, globalWords, localLevelWords, globalLevelWords,
        canonicalRelativeRmmInteriorComponentOffsets,
        canonicalRelativeRmmLocalMachineStore,
        List.length_append, List.append_assoc, Nat.add_assoc] using hmiddle
    simpa [Array.getElem?_toList] using hlist
  case hdead =>
    simp [canonicalRelativeRmmInteriorComponentOffsets]

theorem canonicalRelativeRmmGlobalReadComputation_refines
    (shape : Cartesian.CartesianShape) (i : Nat) :
    ((canonicalRelativeRmmMachineReadNatComputation shape
        (canonicalRelativeRmmInteriorGlobalTable shape).table
        (canonicalRelativeRmmInteriorComponentOffsets shape).globalBlock i).run
      (canonicalRelativeRmmInteriorComponentStore shape).store.words).toCosted =
      canonicalRelativeRmmMachineReadNatCosted shape
        (canonicalRelativeRmmInteriorGlobalTable shape).table i := by
  unfold canonicalRelativeRmmMachineReadNatComputation
  unfold canonicalRelativeRmmMachineReadNatCosted
  apply FixedWidthNatTable.machineReadComputationAt_refines_machineReadCosted
  case hsegment =>
    intro localAddress hlocal
    have hlist :
        (canonicalRelativeRmmInteriorComponentStore
          shape).store.words.toList[
            (canonicalRelativeRmmInteriorComponentOffsets shape).globalBlock +
              localAddress]? =
        ((canonicalRelativeRmmInteriorGlobalTable shape).table.machineStore
          (SuccinctRank.machineWordBits_pos
            shape.bpCode.length)).store.words.toList[localAddress]? := by
      let hword := SuccinctRank.machineWordBits_pos shape.bpCode.length
      let summary := canonicalRelativeRmmSummaryTable shape
      let baselineWords :=
        (summary.baselineTable.machineStore hword).store.words.toList
      let minRelWords :=
        (summary.minRelTable.machineStore hword).store.words.toList
      let maxRelWords :=
        (summary.maxRelTable.machineStore hword).store.words.toList
      let argWords :=
        (summary.argOffsetTable.machineStore hword).store.words.toList
      let localWords :=
        ((canonicalRelativeRmmInteriorLocalTable
          shape).table.machineStore hword).store.words.toList
      let globalWords :=
        ((canonicalRelativeRmmInteriorGlobalTable
          shape).table.machineStore hword).store.words.toList
      let localLevelWords :=
        ((canonicalRelativeRmmInteriorLocalLevelTable
          shape).table.machineStore hword).store.words.toList
      let globalLevelWords :=
        ((canonicalRelativeRmmInteriorGlobalLevelTable
          shape).table.machineStore hword).store.words.toList
      have hmiddle :
          (((((baselineWords ++ minRelWords) ++ maxRelWords) ++ argWords) ++
            localWords) ++ globalWords ++
              (localLevelWords ++ globalLevelWords))[
              ((((baselineWords ++ minRelWords) ++ maxRelWords) ++ argWords) ++
                localWords).length + localAddress]? =
            globalWords[localAddress]? :=
        List.getElem?_append_middle_of_lt
          ((((baselineWords ++ minRelWords) ++ maxRelWords) ++ argWords) ++
            localWords) globalWords (localLevelWords ++ globalLevelWords)
          localAddress hlocal
      rw [canonicalRelativeRmmInteriorComponentStore_words_toList]
      simpa [hword, summary, baselineWords, minRelWords, maxRelWords,
        argWords, localWords, globalWords, localLevelWords, globalLevelWords,
        canonicalRelativeRmmInteriorComponentOffsets,
        canonicalRelativeRmmLocalMachineStore,
        List.length_append, List.append_assoc, Nat.add_assoc] using hmiddle
    simpa [Array.getElem?_toList] using hlist
  case hdead =>
    simp [canonicalRelativeRmmInteriorComponentOffsets]

theorem canonicalRelativeRmmLocalLevelReadComputation_refines
    (shape : Cartesian.CartesianShape) (i : Nat) :
    ((canonicalRelativeRmmMachineReadNatComputation shape
        (canonicalRelativeRmmInteriorLocalLevelTable shape).table
        (canonicalRelativeRmmInteriorComponentOffsets shape).localLevel i).run
      (canonicalRelativeRmmInteriorComponentStore shape).store.words).toCosted =
      canonicalRelativeRmmMachineReadNatCosted shape
        (canonicalRelativeRmmInteriorLocalLevelTable shape).table i := by
  unfold canonicalRelativeRmmMachineReadNatComputation
  unfold canonicalRelativeRmmMachineReadNatCosted
  apply FixedWidthNatTable.machineReadComputationAt_refines_machineReadCosted
  case hsegment =>
    intro localAddress hlocal
    have hlist :
        (canonicalRelativeRmmInteriorComponentStore
          shape).store.words.toList[
            (canonicalRelativeRmmInteriorComponentOffsets shape).localLevel +
              localAddress]? =
        ((canonicalRelativeRmmInteriorLocalLevelTable shape).table.machineStore
          (SuccinctRank.machineWordBits_pos
            shape.bpCode.length)).store.words.toList[localAddress]? := by
      let hword := SuccinctRank.machineWordBits_pos shape.bpCode.length
      let summary := canonicalRelativeRmmSummaryTable shape
      let baselineWords :=
        (summary.baselineTable.machineStore hword).store.words.toList
      let minRelWords :=
        (summary.minRelTable.machineStore hword).store.words.toList
      let maxRelWords :=
        (summary.maxRelTable.machineStore hword).store.words.toList
      let argWords :=
        (summary.argOffsetTable.machineStore hword).store.words.toList
      let localWords :=
        ((canonicalRelativeRmmInteriorLocalTable
          shape).table.machineStore hword).store.words.toList
      let globalWords :=
        ((canonicalRelativeRmmInteriorGlobalTable
          shape).table.machineStore hword).store.words.toList
      let localLevelWords :=
        ((canonicalRelativeRmmInteriorLocalLevelTable
          shape).table.machineStore hword).store.words.toList
      let globalLevelWords :=
        ((canonicalRelativeRmmInteriorGlobalLevelTable
          shape).table.machineStore hword).store.words.toList
      have hmiddle :
          ((((((baselineWords ++ minRelWords) ++ maxRelWords) ++ argWords) ++
            localWords) ++ globalWords) ++ localLevelWords ++
              globalLevelWords)[
              (((((baselineWords ++ minRelWords) ++ maxRelWords) ++ argWords) ++
                localWords) ++ globalWords).length + localAddress]? =
            localLevelWords[localAddress]? :=
        List.getElem?_append_middle_of_lt
          (((((baselineWords ++ minRelWords) ++ maxRelWords) ++ argWords) ++
            localWords) ++ globalWords) localLevelWords globalLevelWords
          localAddress hlocal
      rw [canonicalRelativeRmmInteriorComponentStore_words_toList]
      simpa [hword, summary, baselineWords, minRelWords, maxRelWords,
        argWords, localWords, globalWords, localLevelWords, globalLevelWords,
        canonicalRelativeRmmInteriorComponentOffsets,
        canonicalRelativeRmmLocalMachineStore,
        canonicalRelativeRmmGlobalMachineStore,
        List.length_append, List.append_assoc, Nat.add_assoc] using hmiddle
    simpa [Array.getElem?_toList] using hlist
  case hdead =>
    simp [canonicalRelativeRmmInteriorComponentOffsets]

theorem canonicalRelativeRmmGlobalLevelReadComputation_refines
    (shape : Cartesian.CartesianShape) (i : Nat) :
    ((canonicalRelativeRmmMachineReadNatComputation shape
        (canonicalRelativeRmmInteriorGlobalLevelTable shape).table
        (canonicalRelativeRmmInteriorComponentOffsets shape).globalLevel i).run
      (canonicalRelativeRmmInteriorComponentStore shape).store.words).toCosted =
      canonicalRelativeRmmMachineReadNatCosted shape
        (canonicalRelativeRmmInteriorGlobalLevelTable shape).table i := by
  unfold canonicalRelativeRmmMachineReadNatComputation
  unfold canonicalRelativeRmmMachineReadNatCosted
  apply FixedWidthNatTable.machineReadComputationAt_refines_machineReadCosted
  case hsegment =>
    intro localAddress hlocal
    have hlist :
        (canonicalRelativeRmmInteriorComponentStore
          shape).store.words.toList[
            (canonicalRelativeRmmInteriorComponentOffsets shape).globalLevel +
              localAddress]? =
        ((canonicalRelativeRmmInteriorGlobalLevelTable shape).table.machineStore
          (SuccinctRank.machineWordBits_pos
            shape.bpCode.length)).store.words.toList[localAddress]? := by
      let hword := SuccinctRank.machineWordBits_pos shape.bpCode.length
      let summary := canonicalRelativeRmmSummaryTable shape
      let baselineWords :=
        (summary.baselineTable.machineStore hword).store.words.toList
      let minRelWords :=
        (summary.minRelTable.machineStore hword).store.words.toList
      let maxRelWords :=
        (summary.maxRelTable.machineStore hword).store.words.toList
      let argWords :=
        (summary.argOffsetTable.machineStore hword).store.words.toList
      let localWords :=
        ((canonicalRelativeRmmInteriorLocalTable
          shape).table.machineStore hword).store.words.toList
      let globalWords :=
        ((canonicalRelativeRmmInteriorGlobalTable
          shape).table.machineStore hword).store.words.toList
      let localLevelWords :=
        ((canonicalRelativeRmmInteriorLocalLevelTable
          shape).table.machineStore hword).store.words.toList
      let globalLevelWords :=
        ((canonicalRelativeRmmInteriorGlobalLevelTable
          shape).table.machineStore hword).store.words.toList
      have hmiddle :
          (((((((baselineWords ++ minRelWords) ++ maxRelWords) ++ argWords) ++
            localWords) ++ globalWords) ++ localLevelWords) ++
              globalLevelWords ++ [])[
              ((((((baselineWords ++ minRelWords) ++ maxRelWords) ++ argWords) ++
                localWords) ++ globalWords) ++ localLevelWords).length +
                  localAddress]? =
            globalLevelWords[localAddress]? :=
        List.getElem?_append_middle_of_lt
          ((((((baselineWords ++ minRelWords) ++ maxRelWords) ++ argWords) ++
            localWords) ++ globalWords) ++ localLevelWords) globalLevelWords []
          localAddress hlocal
      rw [canonicalRelativeRmmInteriorComponentStore_words_toList]
      simpa [hword, summary, baselineWords, minRelWords, maxRelWords,
        argWords, localWords, globalWords, localLevelWords, globalLevelWords,
        canonicalRelativeRmmInteriorComponentOffsets,
        canonicalRelativeRmmLocalMachineStore,
        canonicalRelativeRmmGlobalMachineStore,
        canonicalRelativeRmmLocalLevelMachineStore,
        List.length_append, List.append_assoc, Nat.add_assoc] using hmiddle
    simpa [Array.getElem?_toList] using hlist
  case hdead =>
    simp [canonicalRelativeRmmInteriorComponentOffsets]

theorem canonicalRelativeRmmMachineSummaryComputation_refines
    (shape : Cartesian.CartesianShape) (block : Nat) :
    ((canonicalRelativeRmmMachineSummaryComputation shape block).run
      (canonicalRelativeRmmInteriorComponentStore shape).store.words).toCosted =
      canonicalRelativeRmmMachineSummaryCosted shape block := by
  unfold canonicalRelativeRmmMachineSummaryComputation
  unfold canonicalRelativeRmmMachineSummaryCosted
  simp only [FlatStoreComputation.bind_run_toCosted,
    FlatStoreComputation.map_run_toCosted,
    canonicalRelativeRmmBaselineReadComputation_refines,
    canonicalRelativeRmmMinRelReadComputation_refines,
    canonicalRelativeRmmMaxRelReadComputation_refines,
    canonicalRelativeRmmArgOffsetReadComputation_refines]

theorem canonicalRelativeRmmMachineMinCandidateComputation_refines
    (shape : Cartesian.CartesianShape) (block : Nat) :
    ((canonicalRelativeRmmMachineMinCandidateComputation shape block).run
      (canonicalRelativeRmmInteriorComponentStore shape).store.words).toCosted =
      canonicalRelativeRmmMachineMinCandidateCosted shape block := by
  unfold canonicalRelativeRmmMachineMinCandidateComputation
  unfold canonicalRelativeRmmMachineMinCandidateCosted
  simp only [FlatStoreComputation.map_run_toCosted,
    canonicalRelativeRmmMachineSummaryComputation_refines]

theorem canonicalRelativeRmmMachineLocalSpanCandidateComputation_refines
    (shape : Cartesian.CartesianShape)
    (macroIdx localStart level : Nat) :
    ((canonicalRelativeRmmMachineLocalSpanCandidateComputation
        shape macroIdx localStart level).run
      (canonicalRelativeRmmInteriorComponentStore shape).store.words).toCosted =
      canonicalRelativeRmmMachineLocalSpanCandidateCosted
        shape macroIdx localStart level := by
  unfold canonicalRelativeRmmMachineLocalSpanCandidateComputation
  unfold canonicalRelativeRmmMachineLocalSpanCandidateCosted
  rw [FlatStoreComputation.bind_run_toCosted]
  rw [canonicalRelativeRmmLocalReadComputation_refines]
  generalize hread :
    canonicalRelativeRmmMachineReadNatCosted shape
      (canonicalRelativeRmmInteriorLocalTable shape).table
      (bpLocalSparseCellSlot
        (RelativeRmm.canonicalLayout shape).macroSize
        (RelativeRmm.canonicalLayout shape).levelCount
        macroIdx localStart level) = read
  simp only [RelativeRmm.canonicalLayout, RelativeRmm.Layout.macroSize,
    RelativeRmm.Layout.levelCount, RelativeRmm.Layout.offsetWidth] at hread
  simp only [RelativeRmm.canonicalLayout, RelativeRmm.Layout.macroSize,
    RelativeRmm.Layout.levelCount, RelativeRmm.Layout.offsetWidth]
  cases read with
  | mk value cost =>
      cases value with
      | none =>
          rw [hread]
          rfl
      | some offset =>
          rw [hread]
          have hmin :=
            canonicalRelativeRmmMachineMinCandidateComputation_refines
              shape
              (macroIdx *
                (canonicalBPRelativeSummaryBlocksPerSuperRaw shape *
                  canonicalBPRelativeSummaryBlocksPerSuperRaw shape) +
                offset)
          have houter :=
            congrArg
              (fun next : Costed (Option (Prod Nat Nat)) =>
                Costed.bind
                  ({ value := some offset, cost := cost } : Costed (Option Nat))
                  (fun _ => next)) hmin
          simpa [Costed.bind] using houter

theorem canonicalRelativeRmmMachineGlobalSpanCandidateComputation_refines
    (shape : Cartesian.CartesianShape)
    (macroStart level : Nat) :
    ((canonicalRelativeRmmMachineGlobalSpanCandidateComputation
        shape macroStart level).run
      (canonicalRelativeRmmInteriorComponentStore shape).store.words).toCosted =
      canonicalRelativeRmmMachineGlobalSpanCandidateCosted
        shape macroStart level := by
  unfold canonicalRelativeRmmMachineGlobalSpanCandidateComputation
  unfold canonicalRelativeRmmMachineGlobalSpanCandidateCosted
  rw [FlatStoreComputation.bind_run_toCosted]
  rw [canonicalRelativeRmmGlobalReadComputation_refines]
  generalize hread :
    canonicalRelativeRmmMachineReadNatCosted shape
      (canonicalRelativeRmmInteriorGlobalTable shape).table
      (bpGlobalSparseCellSlot
        (RelativeRmm.canonicalLayout shape).macroSampleCount
        macroStart level) = read
  simp only [RelativeRmm.canonicalLayout,
    RelativeRmm.Layout.macroSampleCount,
    RelativeRmm.Layout.macroSize] at hread
  simp only [RelativeRmm.canonicalLayout,
    RelativeRmm.Layout.macroSampleCount, RelativeRmm.Layout.macroSize]
  cases read with
  | mk value cost =>
      cases value with
      | none =>
          rw [hread]
          rfl
      | some block =>
          rw [hread]
          have hmin :=
            canonicalRelativeRmmMachineMinCandidateComputation_refines
              shape block
          have houter :=
            congrArg
              (fun next : Costed (Option (Prod Nat Nat)) =>
                Costed.bind
                  ({ value := some block, cost := cost } : Costed (Option Nat))
                  (fun _ => next)) hmin
          simpa [Costed.bind] using houter

theorem canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation_refines
    (shape : Cartesian.CartesianShape)
    (macroIdx localStart count : Nat) :
    ((canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation
        shape macroIdx localStart count).run
      (canonicalRelativeRmmInteriorComponentStore shape).store.words).toCosted =
      canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted
        shape macroIdx localStart count := by
  unfold canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation
  unfold canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted
  rw [FlatStoreComputation.bind_run_toCosted,
    canonicalRelativeRmmLocalLevelReadComputation_refines]
  apply congrArg
  funext cell?
  cases cell? with
  | none => rfl
  | some cell =>
      simp only [FlatStoreComputation.bind_run_toCosted,
        FlatStoreComputation.map_run_toCosted,
        canonicalRelativeRmmMachineLocalSpanCandidateComputation_refines]

theorem canonicalRelativeRmmMachineGlobalTwoSpanCandidateComputation_refines
    (shape : Cartesian.CartesianShape)
    (macroStart count : Nat) :
    ((canonicalRelativeRmmMachineGlobalTwoSpanCandidateComputation
        shape macroStart count).run
      (canonicalRelativeRmmInteriorComponentStore shape).store.words).toCosted =
      canonicalRelativeRmmMachineGlobalTwoSpanCandidateCosted
        shape macroStart count := by
  unfold canonicalRelativeRmmMachineGlobalTwoSpanCandidateComputation
  unfold canonicalRelativeRmmMachineGlobalTwoSpanCandidateCosted
  rw [FlatStoreComputation.bind_run_toCosted,
    canonicalRelativeRmmGlobalLevelReadComputation_refines]
  apply congrArg
  funext cell?
  cases cell? with
  | none => rfl
  | some cell =>
      simp only [FlatStoreComputation.bind_run_toCosted,
        FlatStoreComputation.map_run_toCosted,
        canonicalRelativeRmmMachineGlobalSpanCandidateComputation_refines]

theorem canonicalRelativeRmmMachineAdjacentMacroCandidateComputation_refines
    (shape : Cartesian.CartesianShape)
    (macroStart localStart rightCount : Nat) :
    ((canonicalRelativeRmmMachineAdjacentMacroCandidateComputation
        shape macroStart localStart rightCount).run
      (canonicalRelativeRmmInteriorComponentStore shape).store.words).toCosted =
      canonicalRelativeRmmMachineAdjacentMacroCandidateCosted
        shape macroStart localStart rightCount := by
  unfold canonicalRelativeRmmMachineAdjacentMacroCandidateComputation
  unfold canonicalRelativeRmmMachineAdjacentMacroCandidateCosted
  simp only [FlatStoreComputation.bind_run_toCosted,
    FlatStoreComputation.map_run_toCosted,
    canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation_refines]

theorem canonicalRelativeRmmMachineLeftMiddleMacroCandidateComputation_refines
    (shape : Cartesian.CartesianShape)
    (macroStart localStart middleMacroCount : Nat) :
    ((canonicalRelativeRmmMachineLeftMiddleMacroCandidateComputation
        shape macroStart localStart middleMacroCount).run
      (canonicalRelativeRmmInteriorComponentStore shape).store.words).toCosted =
      canonicalRelativeRmmMachineLeftMiddleMacroCandidateCosted
        shape macroStart localStart middleMacroCount := by
  unfold canonicalRelativeRmmMachineLeftMiddleMacroCandidateComputation
  unfold canonicalRelativeRmmMachineLeftMiddleMacroCandidateCosted
  simp only [FlatStoreComputation.bind_run_toCosted,
    FlatStoreComputation.map_run_toCosted,
    canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation_refines,
    canonicalRelativeRmmMachineGlobalTwoSpanCandidateComputation_refines]

theorem canonicalRelativeRmmMachineCrossMacroCandidateComputation_refines
    (shape : Cartesian.CartesianShape)
    (macroStart localStart middleMacroCount rightCount : Nat) :
    ((canonicalRelativeRmmMachineCrossMacroCandidateComputation
        shape macroStart localStart middleMacroCount rightCount).run
      (canonicalRelativeRmmInteriorComponentStore shape).store.words).toCosted =
      canonicalRelativeRmmMachineCrossMacroCandidateCosted
        shape macroStart localStart middleMacroCount rightCount := by
  unfold canonicalRelativeRmmMachineCrossMacroCandidateComputation
  unfold canonicalRelativeRmmMachineCrossMacroCandidateCosted
  simp only [FlatStoreComputation.bind_run_toCosted,
    FlatStoreComputation.map_run_toCosted,
    canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation_refines,
    canonicalRelativeRmmMachineGlobalTwoSpanCandidateComputation_refines]

theorem canonicalRelativeRmmInteriorRangeMinCostedWithStore_eq_current
    (shape : Cartesian.CartesianShape) (startBlock count : Nat) :
    canonicalRelativeRmmInteriorRangeMinCostedWithStore shape
        (canonicalRelativeRmmInteriorComponentStore shape).store.words
        startBlock count =
      canonicalRelativeRmmInteriorRangeMinCosted shape startBlock count := by
  unfold canonicalRelativeRmmInteriorRangeMinCostedWithStore
  unfold canonicalRelativeRmmInteriorRangeMinCostedWithRead
  unfold canonicalRelativeRmmInteriorRangeMinExecutionWithRead
  unfold canonicalRelativeRmmInteriorRangeMinComputation
  unfold canonicalRelativeRmmInteriorRangeMinCosted
  by_cases hcount : count = 0
  case pos =>
    simpa [hcount] using
      (FlatStoreComputation.pure_run_toCosted
        (none : Option (Prod Nat Nat))
        (canonicalRelativeRmmInteriorComponentStore shape).store.words)
  case neg =>
    simp only [hcount, if_false]
    by_cases hwithin :
        count <= (RelativeRmm.canonicalLayout shape).macroSize -
          startBlock % (RelativeRmm.canonicalLayout shape).macroSize
    case pos =>
      simp only [hwithin, if_true]
      exact canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation_refines
        shape
        (startBlock / (RelativeRmm.canonicalLayout shape).macroSize)
        (startBlock % (RelativeRmm.canonicalLayout shape).macroSize)
        count
    case neg =>
      simp only [hwithin, if_false]
      by_cases hmiddle :
          (count -
              ((RelativeRmm.canonicalLayout shape).macroSize -
                startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) /
              (RelativeRmm.canonicalLayout shape).macroSize = 0
      case pos =>
        simp only [hmiddle, if_true]
        exact
          canonicalRelativeRmmMachineAdjacentMacroCandidateComputation_refines
            shape
            (startBlock / (RelativeRmm.canonicalLayout shape).macroSize)
            (startBlock % (RelativeRmm.canonicalLayout shape).macroSize)
            ((count -
              ((RelativeRmm.canonicalLayout shape).macroSize -
                startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) %
              (RelativeRmm.canonicalLayout shape).macroSize)
      case neg =>
        simp only [hmiddle, if_false]
        by_cases hright :
            (count -
                ((RelativeRmm.canonicalLayout shape).macroSize -
                  startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) %
                (RelativeRmm.canonicalLayout shape).macroSize = 0
        case pos =>
          simp only [hright, if_true]
          exact
            canonicalRelativeRmmMachineLeftMiddleMacroCandidateComputation_refines
              shape
              (startBlock / (RelativeRmm.canonicalLayout shape).macroSize)
              (startBlock % (RelativeRmm.canonicalLayout shape).macroSize)
              ((count -
                ((RelativeRmm.canonicalLayout shape).macroSize -
                  startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) /
                (RelativeRmm.canonicalLayout shape).macroSize)
        case neg =>
          simp only [hright, if_false]
          exact
            canonicalRelativeRmmMachineCrossMacroCandidateComputation_refines
              shape
              (startBlock / (RelativeRmm.canonicalLayout shape).macroSize)
              (startBlock % (RelativeRmm.canonicalLayout shape).macroSize)
              ((count -
                ((RelativeRmm.canonicalLayout shape).macroSize -
                  startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) /
                (RelativeRmm.canonicalLayout shape).macroSize)
              ((count -
                ((RelativeRmm.canonicalLayout shape).macroSize -
                  startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) %
                (RelativeRmm.canonicalLayout shape).macroSize)

def canonicalRelativeRmmInteriorRangePhysicalWordsReadWithStore
    (shape : Cartesian.CartesianShape) (store : Array (List Bool))
    (startBlock count : Nat) : List (List Bool) :=
  (canonicalRelativeRmmInteriorRangeMinExecutionWithStore
    shape store startBlock count).reads.filterMap Prod.snd

theorem canonicalRelativeRmmInteriorRangeFootprint_recorded
    (shape : Cartesian.CartesianShape) (store : Array (List Bool))
    (startBlock count : Nat) :
    canonicalRelativeRmmInteriorRangeFootprintWithStore
        shape store startBlock count =
      (canonicalRelativeRmmInteriorRangeMinExecutionWithStore
        shape store startBlock count).reads.map Prod.fst := rfl

theorem canonicalRelativeRmmInteriorRangeMinExecutionWithStore_eq_of_agree
    (shape : Cartesian.CartesianShape)
    (storeA storeB : Array (List Bool))
    (startBlock count : Nat)
    (hagrees :
      forall address,
        List.Mem address
            (canonicalRelativeRmmInteriorRangeFootprintWithStore
              shape storeA startBlock count) ->
          storeA[address]? = storeB[address]?) :
    canonicalRelativeRmmInteriorRangeMinExecutionWithStore
        shape storeA startBlock count =
      canonicalRelativeRmmInteriorRangeMinExecutionWithStore
        shape storeB startBlock count := by
  exact
    (canonicalRelativeRmmInteriorRangeMinComputation
      shape startBlock count).footprint_determines storeA storeB hagrees

theorem canonicalRelativeRmmInteriorRangeMinCostedWithStore_eq_of_agree
    (shape : Cartesian.CartesianShape)
    (storeA storeB : Array (List Bool))
    (startBlock count : Nat)
    (hagrees :
      forall address,
        List.Mem address
            (canonicalRelativeRmmInteriorRangeFootprintWithStore
              shape storeA startBlock count) ->
          storeA[address]? = storeB[address]?) :
    canonicalRelativeRmmInteriorRangeMinCostedWithStore
        shape storeA startBlock count =
      canonicalRelativeRmmInteriorRangeMinCostedWithStore
        shape storeB startBlock count := by
  exact congrArg FlatStoreExecution.toCosted
    (canonicalRelativeRmmInteriorRangeMinExecutionWithStore_eq_of_agree
      shape storeA storeB startBlock count hagrees)

theorem canonicalRelativeRmmInteriorRangeRead_matches_store
    (shape : Cartesian.CartesianShape) (store : Array (List Bool))
    (startBlock count address : Nat) (word : Option (List Bool))
    (hread :
      List.Mem (address, word)
        (canonicalRelativeRmmInteriorRangeMinExecutionWithStore
          shape store startBlock count).reads) :
    store[address]? = word := by
  exact
    (canonicalRelativeRmmInteriorRangeMinComputation
      shape startBlock count).reads_match_store store address word hread

theorem canonicalRelativeRmmInteriorRange_successful_read_backed
    (shape : Cartesian.CartesianShape)
    (startBlock count address : Nat) (word : List Bool)
    (hread :
      List.Mem (address, some word)
        (canonicalRelativeRmmInteriorRangeMinExecutionWithStore shape
          (canonicalRelativeRmmInteriorComponentStore shape).store.words
          startBlock count).reads) :
    address <
        (canonicalRelativeRmmInteriorComponentStore shape).store.words.size /\
      List.Mem word
        (canonicalRelativeRmmInteriorComponentStore shape).store.words.toList /\
      flattenPayloadWords
          (canonicalRelativeRmmInteriorComponentStore
            shape).store.words.toList =
        (canonicalRelativeRmmSummaryTable shape).payload ++
          (canonicalRelativeRmmInteriorLocalTable shape).payload ++
            (canonicalRelativeRmmInteriorGlobalTable shape).payload ++
              (canonicalRelativeRmmInteriorLocalLevelTable shape).payload ++
                (canonicalRelativeRmmInteriorGlobalLevelTable shape).payload := by
  have hmatch :=
    canonicalRelativeRmmInteriorRangeRead_matches_store
      shape (canonicalRelativeRmmInteriorComponentStore shape).store.words
      startBlock count address (some word) hread
  have hlist :
      (canonicalRelativeRmmInteriorComponentStore
        shape).store.words.toList[address]? = some word := by
    simpa [Array.getElem?_toList] using hmatch
  have hlt : address <
      (canonicalRelativeRmmInteriorComponentStore shape).store.words.size := by
    exact (List.getElem?_eq_some_iff.mp hlist).1
  exact And.intro hlt
    (And.intro (List.mem_of_getElem? hlist)
      (canonicalRelativeRmmInteriorComponentStore_flattens_payload shape))

theorem canonicalRelativeRmmInteriorRange_returned_word_bounded
    (shape : Cartesian.CartesianShape)
    (startBlock count address : Nat) (word : List Bool)
    (hread :
      List.Mem (address, some word)
        (canonicalRelativeRmmInteriorRangeMinExecutionWithStore shape
          (canonicalRelativeRmmInteriorComponentStore shape).store.words
          startBlock count).reads) :
    word.length <= SuccinctRank.machineWordBits shape.bpCode.length := by
  exact canonicalRelativeRmmInteriorComponentStore_words_bounded shape
    (canonicalRelativeRmmInteriorRange_successful_read_backed
      shape startBlock count address word hread).2.1

theorem canonicalRelativeRmmInteriorRange_returned_word_bounded_reviewer
    (shape : Cartesian.CartesianShape)
    (startBlock count address : Nat) (word : List Bool)
    (hread :
      List.Mem (address, some word)
        (canonicalRelativeRmmInteriorRangeMinExecutionWithStore shape
          (canonicalRelativeRmmInteriorComponentStore shape).store.words
          startBlock count).reads) :
    word.length <= canonicalRelativeRmmInteriorReviewerWordBits shape := by
  exact Nat.le_trans
    (canonicalRelativeRmmInteriorRange_returned_word_bounded
      shape startBlock count address word hread)
    (SuccinctRank.machineWordBits_mono_le
      (Nat.le_max_left shape.bpCode.length
        (Nat.max (RelativeRmm.canonicalLayout shape).blockCount
          (canonicalRelativeRmmInteriorComponentStore shape).store.words.size)))

theorem canonicalRelativeRmmInteriorRange_cost_eq_footprint_length
    (shape : Cartesian.CartesianShape) (store : Array (List Bool))
    (startBlock count : Nat) :
    (canonicalRelativeRmmInteriorRangeMinCostedWithStore
      shape store startBlock count).cost =
      (canonicalRelativeRmmInteriorRangeFootprintWithStore
        shape store startBlock count).length := by
  simp [canonicalRelativeRmmInteriorRangeMinCostedWithStore,
    canonicalRelativeRmmInteriorRangeMinCostedWithRead,
    canonicalRelativeRmmInteriorRangeFootprintWithStore,
    canonicalRelativeRmmInteriorRangeFootprintWithRead,
    canonicalRelativeRmmInteriorRangeMinExecutionWithRead,
    FlatStoreExecution.footprint]
/--
The charged interior route agrees with the accepted logical specification.

CARRIES `hbound`, the route's own boundedness hypothesis, because the charged
sparse-level reads are only equivalent to the silent `Nat.log2` computation on
arguments inside the table's domain.  Every obligation is discharged from the
branch guards plus `hbound`, with no new hypothesis introduced: the
within-macro guard gives `count <= macroSize` directly, a right count is a
remainder modulo `macroSize`, and a middle macro count is a quotient of
something bounded by `blockCount`, hence at most
`macroSampleCount = blockCount / macroSize + 1`.
-/
theorem canonicalRelativeRmmInteriorRangeMinCosted_refines_logical
    (shape : Cartesian.CartesianShape) (startBlock count : Nat)
    (hbound : startBlock + count <=
      (RelativeRmm.canonicalLayout shape).blockCount) :
    (canonicalRelativeRmmInteriorRangeMinCosted shape startBlock count).erase =
      (bpTwoLevelInteriorCandidateCosted
        (canonicalRelativeRmmInteriorLocalTable shape)
        (canonicalRelativeRmmInteriorGlobalTable shape)
        (canonicalRelativeRmmSummaryTable shape)
        startBlock count).erase := by
  have hvalid := RelativeRmm.canonicalLayout_valid shape
  have hmacroPos : 0 < (RelativeRmm.canonicalLayout shape).macroSize :=
    hvalid.macroSize_pos
  have hsample :
      (RelativeRmm.canonicalLayout shape).macroSampleCount =
        (RelativeRmm.canonicalLayout shape).blockCount /
          (RelativeRmm.canonicalLayout shape).macroSize + 1 := by
    simp [RelativeRmm.Layout.macroSampleCount]
  have hquot : forall k : Nat, k <= count ->
      k / (RelativeRmm.canonicalLayout shape).macroSize <=
        (RelativeRmm.canonicalLayout shape).macroSampleCount := by
    intro k hk
    have hkb : k <= (RelativeRmm.canonicalLayout shape).blockCount := by omega
    have hdiv : k / (RelativeRmm.canonicalLayout shape).macroSize <=
        (RelativeRmm.canonicalLayout shape).blockCount /
          (RelativeRmm.canonicalLayout shape).macroSize :=
      Nat.div_le_div_right hkb
    omega
  have hrem : forall k : Nat,
      k % (RelativeRmm.canonicalLayout shape).macroSize <=
        (RelativeRmm.canonicalLayout shape).macroSize :=
    fun k => Nat.le_of_lt (Nat.mod_lt k hmacroPos)
  unfold canonicalRelativeRmmInteriorRangeMinCosted
    bpTwoLevelInteriorCandidateCosted
  by_cases hcount : count = 0
  · simp [hcount, Costed.pure]
  · simp only [hcount, if_false]
    by_cases hwithin :
        count <=
          (RelativeRmm.canonicalLayout shape).macroSize -
            startBlock % (RelativeRmm.canonicalLayout shape).macroSize
    · simp only [hwithin, if_true]
      exact canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted_refines
        shape
        (startBlock / (RelativeRmm.canonicalLayout shape).macroSize)
        (startBlock % (RelativeRmm.canonicalLayout shape).macroSize)
        count
        (Nat.le_trans hwithin (Nat.sub_le _ _))
    · simp only [hwithin, if_false]
      by_cases hmiddle :
          (count -
              ((RelativeRmm.canonicalLayout shape).macroSize -
                startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) /
              (RelativeRmm.canonicalLayout shape).macroSize = 0
      · simp only [hmiddle, if_true]
        exact canonicalRelativeRmmMachineAdjacentMacroCandidateCosted_refines
          shape
          (startBlock / (RelativeRmm.canonicalLayout shape).macroSize)
          (startBlock % (RelativeRmm.canonicalLayout shape).macroSize)
          ((count -
              ((RelativeRmm.canonicalLayout shape).macroSize -
                startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) %
            (RelativeRmm.canonicalLayout shape).macroSize)
          (hrem _)
      · simp only [hmiddle, if_false]
        by_cases hright :
            (count -
                ((RelativeRmm.canonicalLayout shape).macroSize -
                  startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) %
                (RelativeRmm.canonicalLayout shape).macroSize = 0
        · simp only [hright, if_true]
          exact
            canonicalRelativeRmmMachineLeftMiddleMacroCandidateCosted_refines
              shape
              (startBlock / (RelativeRmm.canonicalLayout shape).macroSize)
              (startBlock % (RelativeRmm.canonicalLayout shape).macroSize)
              ((count -
                  ((RelativeRmm.canonicalLayout shape).macroSize -
                    startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) /
                (RelativeRmm.canonicalLayout shape).macroSize)
              (hquot _ (Nat.sub_le _ _))
        · simp only [hright, if_false]
          exact canonicalRelativeRmmMachineCrossMacroCandidateCosted_refines
            shape
            (startBlock / (RelativeRmm.canonicalLayout shape).macroSize)
            (startBlock % (RelativeRmm.canonicalLayout shape).macroSize)
            ((count -
                ((RelativeRmm.canonicalLayout shape).macroSize -
                  startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) /
              (RelativeRmm.canonicalLayout shape).macroSize)
            ((count -
                ((RelativeRmm.canonicalLayout shape).macroSize -
                  startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) %
              (RelativeRmm.canonicalLayout shape).macroSize)
            (hquot _ (Nat.sub_le _ _)) (hrem _)

theorem canonicalRelativeRmmRelativeWidth_le_seven_machine
    (shape : Cartesian.CartesianShape) :
    (RelativeRmm.canonicalLayout shape).relativeWidth <=
      7 * SuccinctRank.machineWordBits shape.bpCode.length := by
  have hsize :
      shape.size <= shape.bpCode.length := by
    rw [Cartesian.CartesianShape.bpCode_length]
    omega
  have hmono :
      SuccinctRank.machineWordBits shape.size <=
        SuccinctRank.machineWordBits shape.bpCode.length :=
    SuccinctRank.machineWordBits_mono_le hsize
  have hnested := SuccinctRank.nestedMachineWordBits_le_succ shape.size
  have hword := SuccinctRank.machineWordBits_pos shape.bpCode.length
  change
    2 * SuccinctRank.machineWordBits
          (SuccinctRank.machineWordBits shape.size) + 3 <=
      7 * SuccinctRank.machineWordBits shape.bpCode.length
  omega

theorem canonicalRelativeRmmOffsetWidth_le_seven_machine
    (shape : Cartesian.CartesianShape) :
    (RelativeRmm.canonicalLayout shape).offsetWidth <=
      7 * SuccinctRank.machineWordBits shape.bpCode.length := by
  have hsize :
      shape.size <= shape.bpCode.length := by
    rw [Cartesian.CartesianShape.bpCode_length]
    omega
  have hmono :
      SuccinctRank.machineWordBits shape.size <=
        SuccinctRank.machineWordBits shape.bpCode.length :=
    SuccinctRank.machineWordBits_mono_le hsize
  have hnested := SuccinctRank.nestedMachineWordBits_le_succ shape.size
  have hsquare :=
    SuccinctRank.machineWordBits_mul_self_log_bound
      (SuccinctRank.machineWordBits shape.size)
  have hword := SuccinctRank.machineWordBits_pos shape.bpCode.length
  change
    SuccinctRank.machineWordBits
        (SuccinctRank.machineWordBits shape.size *
          SuccinctRank.machineWordBits shape.size) <=
      7 * SuccinctRank.machineWordBits shape.bpCode.length
  omega

theorem canonicalRelativeRmmBlockWidth_le_seven_machine
    (shape : Cartesian.CartesianShape) :
    (RelativeRmm.canonicalLayout shape).blockAddressWidth <=
      7 * SuccinctRank.machineWordBits shape.bpCode.length := by
  have hcount :
      (RelativeRmm.canonicalLayout shape).blockCount <=
        shape.bpCode.length := by
    exact canonicalBPRelativeSummaryBlockCountRaw_le_bpCode_length shape
  have hmono := SuccinctRank.machineWordBits_mono_le hcount
  have hword := SuccinctRank.machineWordBits_pos shape.bpCode.length
  simpa [RelativeRmm.Layout.blockAddressWidth] using
    Nat.le_trans hmono (by omega :
      SuccinctRank.machineWordBits shape.bpCode.length <=
        7 * SuccinctRank.machineWordBits shape.bpCode.length)

private theorem u3_nat_succ_lt_two_pow_of_two_le
    (k : Nat) (hk : 2 <= k) :
    k + 1 < 2 ^ k := by
  induction k with
  | zero => omega
  | succ k ih =>
      by_cases hkone : k = 1
      · subst k
        decide
      · have hktwo : 2 <= k := by omega
        have hprev := ih hktwo
        rw [Nat.pow_succ]
        omega

private theorem u3_machineWordBits_lt_self_of_three_le
    {n : Nat} (hn : 3 <= n) :
    SuccinctRank.machineWordBits n < n := by
  have hnzero : Not (n = 0) := by omega
  have hk : 2 <= n - 1 := by omega
  have hpow : n < 2 ^ (n - 1) := by
    have h := u3_nat_succ_lt_two_pow_of_two_le (n - 1) hk
    have hn : n - 1 + 1 = n := by omega
    simpa [hn] using h
  have hlog : Nat.log2 n < n - 1 :=
    (Nat.log2_lt hnzero).2 hpow
  simp only [SuccinctRank.machineWordBits]
  omega

/--
For every nonempty shape, doubling the input into the BP code buys at least one
additional bit beyond the canonical `log n` base.  This is the width fact used
by the all-size U3 read accounting; it is not an activation threshold.
-/
theorem canonicalRelativeRmmBase_succ_le_machine_of_size_pos
    {shape : Cartesian.CartesianShape} (hsize : 0 < shape.size) :
    canonicalBPRelativeSummaryBase shape + 1 <=
      SuccinctRank.machineWordBits shape.bpCode.length := by
  have hpowSelf : 2 ^ Nat.log2 shape.size <= shape.size :=
    Nat.log2_self_le (Nat.ne_of_gt hsize)
  have hpowDouble :
      2 ^ (Nat.log2 shape.size + 1) <= 2 * shape.size := by
    have hscaled := Nat.mul_le_mul_left 2 hpowSelf
    simpa [Nat.pow_succ, Nat.mul_comm] using hscaled
  have hlogDouble :
      Nat.log2 shape.size + 1 <= Nat.log2 (2 * shape.size) :=
    natLog2_ge_of_pow_le hpowDouble
  rw [Cartesian.CartesianShape.bpCode_length]
  simp only [canonicalBPRelativeSummaryBase,
    SuccinctRank.machineWordBits]
  omega

/--
Once an interior query is reachable, the canonical relative field is strictly
shorter than two physical words.  The premise is derived below from the actual
cross-block execution, not used for public dispatch.
-/
theorem canonicalRelativeRmmRelativeWidth_lt_two_machine_of_size_ge_four
    {shape : Cartesian.CartesianShape} (hsize : 4 <= shape.size) :
    (RelativeRmm.canonicalLayout shape).relativeWidth <
      2 * SuccinctRank.machineWordBits shape.bpCode.length := by
  have hlog : 2 <= Nat.log2 shape.size :=
    natLog2_ge_of_pow_le (by simpa using hsize)
  have hbaseThree :
      3 <= SuccinctRank.machineWordBits shape.size := by
    simp only [SuccinctRank.machineWordBits]
    omega
  have hnested :=
    u3_machineWordBits_lt_self_of_three_le hbaseThree
  have hmachine :=
    canonicalRelativeRmmBase_succ_le_machine_of_size_pos
      (shape := shape) (by omega)
  have hmachine' :
      SuccinctRank.machineWordBits shape.size + 1 <=
        SuccinctRank.machineWordBits shape.bpCode.length := by
    simpa [canonicalBPRelativeSummaryBase,
      SuccinctRank.machineWordBits] using hmachine
  change
    2 * SuccinctRank.machineWordBits
          (SuccinctRank.machineWordBits shape.size) + 3 <
      2 * SuccinctRank.machineWordBits shape.bpCode.length
  omega

/-- The canonical local-offset field is no wider than a relative summary field. -/
theorem canonicalRelativeRmmOffsetWidth_le_relativeWidth
    (shape : Cartesian.CartesianShape) :
    (RelativeRmm.canonicalLayout shape).offsetWidth <=
      (RelativeRmm.canonicalLayout shape).relativeWidth := by
  let base := canonicalBPRelativeSummaryBase shape
  have hbasePos : 0 < base := by
    simp [base, canonicalBPRelativeSummaryBase]
  have hfour :=
    four_mul_square_lt_two_pow_two_log_succ_add_three base
  have hsquare :
      base * base < 2 ^ (2 * (Nat.log2 base + 1) + 3) := by
    exact Nat.lt_of_le_of_lt (by omega) hfour
  have hlog :=
    natLog2_succ_le_of_pos_lt_pow
      (Nat.mul_pos hbasePos hbasePos) hsquare
  simpa [RelativeRmm.Layout.offsetWidth,
    RelativeRmm.Layout.macroSize, RelativeRmm.canonicalLayout,
    canonicalBPRelativeSummaryBlocksPerSuperRaw,
    canonicalBPRelativeSummaryRelativeWidthRaw, base,
    SuccinctRank.machineWordBits] using hlog

/-- The canonical global block address fits in one physical machine word. -/
theorem canonicalRelativeRmmBlockWidth_le_machine
    (shape : Cartesian.CartesianShape) :
    (RelativeRmm.canonicalLayout shape).blockAddressWidth <=
      SuccinctRank.machineWordBits shape.bpCode.length := by
  have hcount :
      (RelativeRmm.canonicalLayout shape).blockCount <=
        shape.bpCode.length :=
    canonicalBPRelativeSummaryBlockCountRaw_le_bpCode_length shape
  simpa [RelativeRmm.Layout.blockAddressWidth] using
    SuccinctRank.machineWordBits_mono_le hcount

/-- A fixed-width canonical entry below two words costs at most two reads. -/
theorem canonicalRelativeRmmMachineReadNatCosted_cost_le_two
    {entries : List Nat} {width : Nat}
    {shape : Cartesian.CartesianShape}
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (hwidth : width <
      2 * SuccinctRank.machineWordBits shape.bpCode.length)
    (i : Nat) :
    (canonicalRelativeRmmMachineReadNatCosted shape table i).cost <= 2 := by
  let wordSize := SuccinctRank.machineWordBits shape.bpCode.length
  have hwordSize : 0 < wordSize :=
    SuccinctRank.machineWordBits_pos shape.bpCode.length
  have hdiv : width / wordSize < 2 := by
    apply (Nat.div_lt_iff_lt_mul hwordSize).2
    simpa [wordSize, Nat.mul_comm] using hwidth
  unfold canonicalRelativeRmmMachineReadNatCosted
  unfold SuccinctSpace.FixedWidthNatTable.machineReadCosted
  rw [SuccinctSpace.FixedWidthNatTable.machineReadCostedWithStore_cost]
  by_cases hvalid : i < entries.length
  · rw [if_pos hvalid]
    change
      (SuccinctSpace.fixedWidthNatTableMachineFootprint
        width wordSize i).length <= 2
    simp [SuccinctSpace.fixedWidthNatTableMachineFootprint,
      SuccinctSpace.fixedWidthNatTableMachineChunkCount]
    split <;> omega
  · rw [if_neg hvalid]
    omega

/-- A canonical fixed-width entry fitting in one word costs at most one read. -/
theorem canonicalRelativeRmmMachineReadNatCosted_cost_le_one
    {entries : List Nat} {width : Nat}
    {shape : Cartesian.CartesianShape}
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (hwidth : width <=
      SuccinctRank.machineWordBits shape.bpCode.length)
    (i : Nat) :
    (canonicalRelativeRmmMachineReadNatCosted shape table i).cost <= 1 := by
  let wordSize := SuccinctRank.machineWordBits shape.bpCode.length
  have hwordSize : 0 < wordSize :=
    SuccinctRank.machineWordBits_pos shape.bpCode.length
  have hdiv : width / wordSize <= 1 := by
    exact Nat.div_le_of_le_mul (by
      simpa [wordSize, Nat.mul_comm] using hwidth)
  unfold canonicalRelativeRmmMachineReadNatCosted
  unfold SuccinctSpace.FixedWidthNatTable.machineReadCosted
  rw [SuccinctSpace.FixedWidthNatTable.machineReadCostedWithStore_cost]
  by_cases hvalid : i < entries.length
  · rw [if_pos hvalid]
    change
      (SuccinctSpace.fixedWidthNatTableMachineFootprint
        width wordSize i).length <= 1
    by_cases hrem : width % wordSize = 0
    · unfold SuccinctSpace.fixedWidthNatTableMachineFootprint
      rw [SuccinctSpace.consecutiveWordIndices_length]
      simp [SuccinctSpace.fixedWidthNatTableMachineChunkCount, hrem]
      exact hdiv
    · have hlt : width < wordSize := by
        by_cases hlt : width < wordSize
        · exact hlt
        · have heq : width = wordSize := by omega
          subst width
          simp at hrem
      have hquot : width / wordSize = 0 := Nat.div_eq_of_lt hlt
      unfold SuccinctSpace.fixedWidthNatTableMachineFootprint
      rw [SuccinctSpace.consecutiveWordIndices_length]
      simp [SuccinctSpace.fixedWidthNatTableMachineChunkCount, hrem, hquot]
  · simp [hvalid]

/--
A positive-width canonical field that fits in one modeled machine word emits
exactly one physical read.  This statement deliberately does not need an
in-range premise: the fixed-width machine table charges its canonical
out-of-range read as one word as well.  Successful-read premises are kept
separate below, where they control whether the sparse-table consumer proceeds.
-/
theorem canonicalRelativeRmmMachineReadNatCosted_cost_eq_one
    {entries : List Nat} {width : Nat}
    {shape : Cartesian.CartesianShape}
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (hwidthPos : 0 < width)
    (hwidth : width <=
      SuccinctRank.machineWordBits shape.bpCode.length)
    (i : Nat) :
    (canonicalRelativeRmmMachineReadNatCosted shape table i).cost = 1 := by
  let wordSize := SuccinctRank.machineWordBits shape.bpCode.length
  have hwordSize : 0 < wordSize :=
    SuccinctRank.machineWordBits_pos shape.bpCode.length
  unfold canonicalRelativeRmmMachineReadNatCosted
  unfold SuccinctSpace.FixedWidthNatTable.machineReadCosted
  rw [SuccinctSpace.FixedWidthNatTable.machineReadCostedWithStore_cost]
  change (if i < entries.length then
      (SuccinctSpace.fixedWidthNatTableMachineFootprint width wordSize i).length
    else 1) = 1
  by_cases hvalid : i < entries.length
  · rw [if_pos hvalid]
    unfold SuccinctSpace.fixedWidthNatTableMachineFootprint
    rw [SuccinctSpace.consecutiveWordIndices_length]
    by_cases heq : width = wordSize
    · subst width
      simp [SuccinctSpace.fixedWidthNatTableMachineChunkCount, hwordSize]
    · have hlt : width < wordSize := by
        change width <= wordSize at hwidth
        omega
      have hdiv : width / wordSize = 0 := Nat.div_eq_of_lt hlt
      have hmod : width % wordSize ≠ 0 := by
        rw [Nat.mod_eq_of_lt hlt]
        exact Nat.ne_of_gt hwidthPos
      simp [SuccinctSpace.fixedWidthNatTableMachineChunkCount, hdiv, hmod]
  · rw [if_neg hvalid]

/--
Crossing a canonical macro boundary forces enough real block capacity that the
relative summary field itself fits in one machine word.  This is a structural
consequence of the queried layout, not a public size-regime test.
-/
theorem canonicalRelativeRmmRelativeWidth_le_machine_of_macroSize_lt_blockCount
    {shape : Cartesian.CartesianShape}
    (hmacro :
      (RelativeRmm.canonicalLayout shape).macroSize <
        (RelativeRmm.canonicalLayout shape).blockCount) :
    (RelativeRmm.canonicalLayout shape).relativeWidth <=
      SuccinctRank.machineWordBits shape.bpCode.length := by
  let base := canonicalBPRelativeSummaryBase shape
  have hbasePos : 0 < base := by
    simp [base, canonicalBPRelativeSummaryBase]
  have hmacroRaw : base * base < shape.size / base := by
    simpa [base] using hmacro
  have hcube : base * (base * base) < shape.size := by
    have hsucc : base * base + 1 <= shape.size / base := by omega
    have hscaled : (base * base + 1) * base <= shape.size :=
      (Nat.le_div_iff_mul_le hbasePos).mp hsucc
    have hstrict : (base * base) * base < (base * base + 1) * base :=
      Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self (base * base)) hbasePos
    exact Nat.lt_of_lt_of_le
      (by simpa [Nat.mul_assoc] using hstrict) hscaled
  have hsizePos : 0 < shape.size := by omega
  have hsizePow : shape.size < 2 ^ base := by
    simpa [base, canonicalBPRelativeSummaryBase,
      SuccinctRank.machineWordBits] using
      SuccinctRank.self_lt_two_pow_machineWordBits shape.size
  have hcubePow : base * (base * base) < 2 ^ base :=
    Nat.lt_trans hcube hsizePow
  have hbaseTen : 10 <= base := by
    by_cases hten : 10 <= base
    · exact hten
    · have hbaseLt : base < 10 := by omega
      have hcases :
          base = 1 ∨ base = 2 ∨ base = 3 ∨ base = 4 ∨ base = 5 ∨
            base = 6 ∨ base = 7 ∨ base = 8 ∨ base = 9 := by
        omega
      rcases hcases with h | h | h | h | h | h | h | h | h <;>
        simp_all <;> omega
  have hmachine :=
    canonicalRelativeRmmBase_succ_le_machine_of_size_pos
      (shape := shape) hsizePos
  by_cases hbaseSixteen : 16 <= base
  · have hrelative :=
      canonicalBPRelativeSummaryRelativeWidthRaw_le_base_of_base_ge_16
        (shape := shape) (by simpa [base] using hbaseSixteen)
    exact Nat.le_trans (by simpa [base] using hrelative) (by omega)
  · have hsmall :
        2 * (Nat.log2 base + 1) + 3 <= base + 1 := by
      have hbaseLt : base < 16 := by omega
      have hlog : Nat.log2 base + 1 <= 4 :=
        natLog2_succ_le_of_pos_lt_pow hbasePos (by simpa using hbaseLt)
      omega
    change 2 * (Nat.log2 base + 1) + 3 <=
      SuccinctRank.machineWordBits shape.bpCode.length
    exact Nat.le_trans hsmall (by simpa [base] using hmachine)

/-! ### Charged sparse-level table: stored width against the machine word

The charged level/span table is read ONCE per two-span call, and that read is
one machine word only if the stored width fits one.  The four theorems below
settle the fit for EVERY shape, not for a sampled table of sizes.

The two `_of_macro_crossing` theorems carry the reachability hypothesis
`macroSize < blockCount`, which is exactly what the interior dispatcher
already derives before it can reach a cross-macro two-span call (see
`canonicalRelativeRmmInteriorRangeMinCosted_cost_le_...`, where `hcross` and
`hbound` produce `hmacro`).  The hypothesis is NOT a size threshold introduced
for convenience: at small shapes the fit genuinely fails (at `size = 4` the
stored width is 6 against a 4-bit machine word), and macro crossing is
precisely what is unreachable there.  The two unconditional theorems cover the
remaining branches, where the read is charged at the `cost_le_eight` rate and
the interior cap has ample headroom.
-/

/--
CORE WIDTH HELPER.  Any exponent dominating the packed product bounds the
stored width.  Every fit below feeds this one lemma.
-/
private theorem bpSparseLevelWidth_le_of_prod_lt_two_pow
    {domain m : Nat} (hpos : 0 < domain)
    (hprod : domain * (Nat.log2 domain + 1) < 2 ^ m) :
    bpSparseLevelWidth domain <= m := by
  have hprodPos : 0 < domain * (Nat.log2 domain + 1) :=
    Nat.mul_pos hpos (Nat.succ_pos _)
  simpa [bpSparseLevelWidth] using
    natLog2_succ_le_of_pos_lt_pow hprodPos hprod

/-- A domain below `2 ^ m` has stored width at most `m + m`. -/
private theorem bpSparseLevelWidth_le_two_mul_of_lt_two_pow
    {domain m : Nat} (hpos : 0 < domain) (hlt : domain < 2 ^ m) :
    bpSparseLevelWidth domain <= m + m := by
  have hpowPos : 0 < 2 ^ m := Nat.pow_pos (by omega : 0 < 2)
  have hlogLe : Nat.log2 domain + 1 <= m :=
    natLog2_succ_le_of_pos_lt_pow hpos hlt
  have hmLe : m <= 2 ^ m := Nat.le_of_lt (Nat.lt_two_pow_self)
  have hprod : domain * (Nat.log2 domain + 1) < 2 ^ m * 2 ^ m :=
    Nat.mul_lt_mul_of_lt_of_le hlt (Nat.le_trans hlogLe hmLe) hpowPos
  exact bpSparseLevelWidth_le_of_prod_lt_two_pow hpos
    (by simpa [Nat.pow_add] using hprod)

/-- The canonical base never exceeds the physical machine word. -/
private theorem canonicalRelativeRmmBase_le_machine
    (shape : Cartesian.CartesianShape) :
    canonicalBPRelativeSummaryBase shape <=
      SuccinctRank.machineWordBits shape.bpCode.length := by
  have hmono :
      SuccinctRank.machineWordBits shape.size <=
        SuccinctRank.machineWordBits shape.bpCode.length :=
    SuccinctRank.machineWordBits_mono_le
      (by rw [Cartesian.CartesianShape.bpCode_length]; omega)
  simpa [canonicalBPRelativeSummaryBase, SuccinctRank.machineWordBits] using
    hmono

/-- Local domain `base*base + 2` sits below `2 ^ (base+base+1)`. -/
private theorem bpSparseLevelWidth_square_domain_le
    (base : Nat) (hbase : 0 < base) :
    bpSparseLevelWidth (bpSparseLevelDomain (base * base)) <=
      (base + base + 1) + (base + base + 1) := by
  have hD : bpSparseLevelDomain (base * base) = base * base + 2 := rfl
  have hb2 : base < 2 ^ base := Nat.lt_two_pow_self
  have hpowPos : 0 < 2 ^ base := Nat.pow_pos (by omega)
  have hsq : base * base < 2 ^ base * 2 ^ base :=
    Nat.mul_lt_mul_of_lt_of_le hb2 (Nat.le_of_lt hb2) hpowPos
  have hsq' : base * base < 2 ^ (base + base) := by
    simpa [Nat.pow_add] using hsq
  have htwo2 : 2 <= 2 ^ (base + base) := by
    have h : 2 ^ 1 <= 2 ^ (base + base) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    simpa using h
  have hsucc : 2 ^ (base + base + 1) = 2 ^ (base + base) * 2 := by
    rw [Nat.pow_succ]
  have hlt : bpSparseLevelDomain (base * base) < 2 ^ (base + base + 1) := by
    rw [hD, hsucc]; omega
  have hpos : 0 < bpSparseLevelDomain (base * base) := by rw [hD]; omega
  exact bpSparseLevelWidth_le_two_mul_of_lt_two_pow hpos hlt

/-- UNCONDITIONAL FIT, local instance. -/
theorem bpSparseLevelLocalWidth_le_seven_machine
    (shape : Cartesian.CartesianShape) :
    bpSparseLevelWidth
        (bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize) <=
      7 * SuccinctRank.machineWordBits shape.bpCode.length := by
  have hmacroSize : (RelativeRmm.canonicalLayout shape).macroSize
      = canonicalBPRelativeSummaryBase shape *
          canonicalBPRelativeSummaryBase shape := rfl
  have hbasePos : 0 < canonicalBPRelativeSummaryBase shape := by
    simp [canonicalBPRelativeSummaryBase]
  have hw := canonicalRelativeRmmBase_le_machine shape
  have hwpos := SuccinctRank.machineWordBits_pos shape.bpCode.length
  rw [hmacroSize]
  have hmain := bpSparseLevelWidth_square_domain_le _ hbasePos
  omega

/-- UNCONDITIONAL FIT, global instance. -/
theorem bpSparseLevelGlobalWidth_le_seven_machine
    (shape : Cartesian.CartesianShape) :
    bpSparseLevelWidth
        (bpSparseLevelDomain
          (RelativeRmm.canonicalLayout shape).macroSampleCount) <=
      7 * SuccinctRank.machineWordBits shape.bpCode.length := by
  have hwpos := SuccinctRank.machineWordBits_pos shape.bpCode.length
  have hself := SuccinctRank.self_lt_two_pow_machineWordBits shape.bpCode.length
  have hcode : shape.bpCode.length = 2 * shape.size :=
    Cartesian.CartesianShape.bpCode_length shape
  have hsizeLt :
      shape.size < 2 ^ SuccinctRank.machineWordBits shape.bpCode.length := by
    omega
  have hsample :
      (RelativeRmm.canonicalLayout shape).macroSampleCount <=
        shape.size + 1 := by
    have hblock : (RelativeRmm.canonicalLayout shape).blockCount <= shape.size :=
      Nat.div_le_self _ _
    have hdiv :
        (RelativeRmm.canonicalLayout shape).blockCount /
            (RelativeRmm.canonicalLayout shape).macroSize <=
          (RelativeRmm.canonicalLayout shape).blockCount :=
      Nat.div_le_self _ _
    have heq : (RelativeRmm.canonicalLayout shape).macroSampleCount =
        (RelativeRmm.canonicalLayout shape).blockCount /
          (RelativeRmm.canonicalLayout shape).macroSize + 1 := rfl
    omega
  have hstep :
      2 ^ (SuccinctRank.machineWordBits shape.bpCode.length + 2) =
        2 ^ SuccinctRank.machineWordBits shape.bpCode.length * 2 * 2 := by
    rw [Nat.pow_succ, Nat.pow_succ]
  have hD : bpSparseLevelDomain
      (RelativeRmm.canonicalLayout shape).macroSampleCount =
    (RelativeRmm.canonicalLayout shape).macroSampleCount + 2 := rfl
  have hlt :
      bpSparseLevelDomain
          (RelativeRmm.canonicalLayout shape).macroSampleCount <
        2 ^ (SuccinctRank.machineWordBits shape.bpCode.length + 2) := by
    rw [hD, hstep]; omega
  have hpos :
      0 < bpSparseLevelDomain
        (RelativeRmm.canonicalLayout shape).macroSampleCount := by
    rw [hD]; omega
  have hmain := bpSparseLevelWidth_le_two_mul_of_lt_two_pow hpos hlt
  omega


/-- Macro crossing forces a genuine cube of real block capacity. -/
private theorem canonicalRelativeRmmBase_cube_lt_size_of_macro_crossing
    {shape : Cartesian.CartesianShape}
    (hmacro : (RelativeRmm.canonicalLayout shape).macroSize <
        (RelativeRmm.canonicalLayout shape).blockCount) :
    canonicalBPRelativeSummaryBase shape *
        (canonicalBPRelativeSummaryBase shape *
          canonicalBPRelativeSummaryBase shape) < shape.size := by
  have hbasePos : 0 < canonicalBPRelativeSummaryBase shape := by
    simp [canonicalBPRelativeSummaryBase]
  have hmacroRaw : canonicalBPRelativeSummaryBase shape *
      canonicalBPRelativeSummaryBase shape <
        shape.size / canonicalBPRelativeSummaryBase shape := hmacro
  have hsucc : canonicalBPRelativeSummaryBase shape *
      canonicalBPRelativeSummaryBase shape + 1 <=
        shape.size / canonicalBPRelativeSummaryBase shape := by omega
  have hscaled : (canonicalBPRelativeSummaryBase shape *
      canonicalBPRelativeSummaryBase shape + 1) *
        canonicalBPRelativeSummaryBase shape <= shape.size :=
    (Nat.le_div_iff_mul_le hbasePos).mp hsucc
  have hstrict : (canonicalBPRelativeSummaryBase shape *
      canonicalBPRelativeSummaryBase shape) *
        canonicalBPRelativeSummaryBase shape <
      (canonicalBPRelativeSummaryBase shape *
        canonicalBPRelativeSummaryBase shape + 1) *
        canonicalBPRelativeSummaryBase shape :=
    Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self _) hbasePos
  exact Nat.lt_of_lt_of_le (by simpa [Nat.mul_assoc] using hstrict) hscaled

private theorem canonicalRelativeRmmSize_lt_two_pow_base
    (shape : Cartesian.CartesianShape) :
    shape.size < 2 ^ canonicalBPRelativeSummaryBase shape := by
  simpa [canonicalBPRelativeSummaryBase] using
    (Nat.lt_log2_self (n := shape.size))

private theorem canonicalRelativeRmmBase_ten_le_of_macro_crossing
    {shape : Cartesian.CartesianShape}
    (hmacro : (RelativeRmm.canonicalLayout shape).macroSize <
        (RelativeRmm.canonicalLayout shape).blockCount) :
    10 <= canonicalBPRelativeSummaryBase shape := by
  have hcube := canonicalRelativeRmmBase_cube_lt_size_of_macro_crossing hmacro
  have hsize := canonicalRelativeRmmSize_lt_two_pow_base shape
  have hcubePow : canonicalBPRelativeSummaryBase shape *
      (canonicalBPRelativeSummaryBase shape *
        canonicalBPRelativeSummaryBase shape) <
      2 ^ canonicalBPRelativeSummaryBase shape := by omega
  by_cases hten : 10 <= canonicalBPRelativeSummaryBase shape
  · exact hten
  · exfalso
    have hbasePos : 0 < canonicalBPRelativeSummaryBase shape := by
      simp [canonicalBPRelativeSummaryBase]
    have hcases : canonicalBPRelativeSummaryBase shape = 1 ∨
        canonicalBPRelativeSummaryBase shape = 2 ∨
        canonicalBPRelativeSummaryBase shape = 3 ∨
        canonicalBPRelativeSummaryBase shape = 4 ∨
        canonicalBPRelativeSummaryBase shape = 5 ∨
        canonicalBPRelativeSummaryBase shape = 6 ∨
        canonicalBPRelativeSummaryBase shape = 7 ∨
        canonicalBPRelativeSummaryBase shape = 8 ∨
        canonicalBPRelativeSummaryBase shape = 9 := by omega
    rcases hcases with h | h | h | h | h | h | h | h | h <;>
      rw [h] at hcubePow <;> simp_all <;> omega

/-- TIGHT FIT ARITHMETIC, local: domain `base*base + 2` in one word. -/
private theorem bpSparseLevelWidth_square_domain_le_succ
    {base : Nat} (hbase : 10 <= base)
    (hcube : base * (base * base) < 2 ^ base) :
    bpSparseLevelWidth (bpSparseLevelDomain (base * base)) <= base + 1 := by
  have hD : bpSparseLevelDomain (base * base) = base * base + 2 := rfl
  have hbb : 100 <= base * base := by
    have h := Nat.mul_le_mul hbase hbase
    omega
  have hten : 10 * (base * base) <= base * (base * base) :=
    Nat.mul_le_mul_right (base * base) hbase
  have hpos : 0 < bpSparseLevelDomain (base * base) := by rw [hD]; omega
  have hDlt : bpSparseLevelDomain (base * base) < 2 ^ base := by rw [hD]; omega
  have hlog : Nat.log2 (bpSparseLevelDomain (base * base)) + 1 <= base :=
    natLog2_succ_le_of_pos_lt_pow hpos hDlt
  have hmul : bpSparseLevelDomain (base * base) *
      (Nat.log2 (bpSparseLevelDomain (base * base)) + 1) <=
      bpSparseLevelDomain (base * base) * base :=
    Nat.mul_le_mul_left _ hlog
  have hexp : bpSparseLevelDomain (base * base) * base =
      base * (base * base) + 2 * base := by
    rw [hD, Nat.add_mul, Nat.mul_assoc]
  have h2b : 2 * base <= base * (base * base) := by
    have h1 : 2 * base <= base * base :=
      Nat.mul_le_mul_right base (by omega : 2 <= base)
    have h2 : 1 * (base * base) <= base * (base * base) :=
      Nat.mul_le_mul_right (base * base) (by omega : 1 <= base)
    omega
  have hsucc : 2 ^ (base + 1) = 2 ^ base * 2 := by rw [Nat.pow_succ]
  have hprod : bpSparseLevelDomain (base * base) *
      (Nat.log2 (bpSparseLevelDomain (base * base)) + 1) < 2 ^ (base + 1) := by
    rw [hsucc]; omega
  exact bpSparseLevelWidth_le_of_prod_lt_two_pow hpos hprod

/-- TIGHT FIT ARITHMETIC, global: sample domain in one word. -/
private theorem bpSparseLevelWidth_sample_domain_le_succ
    {base x size : Nat} (hbase : 10 <= base)
    (hcube : base * (base * base) < 2 ^ base)
    (hsize : size < 2 ^ base)
    (hbx : base * x <= size) :
    bpSparseLevelWidth (bpSparseLevelDomain (x + 1)) <= base + 1 := by
  have hD : bpSparseLevelDomain (x + 1) = x + 3 := rfl
  have hbb : 100 <= base * base := by
    have h := Nat.mul_le_mul hbase hbase
    omega
  have hten : 10 * (base * base) <= base * (base * base) :=
    Nat.mul_le_mul_right (base * base) hbase
  have h10x : 10 * x <= base * x := Nat.mul_le_mul_right x hbase
  have hpos : 0 < bpSparseLevelDomain (x + 1) := by rw [hD]; omega
  have hDlt : bpSparseLevelDomain (x + 1) < 2 ^ base := by rw [hD]; omega
  have hlog : Nat.log2 (bpSparseLevelDomain (x + 1)) + 1 <= base :=
    natLog2_succ_le_of_pos_lt_pow hpos hDlt
  have hmul : bpSparseLevelDomain (x + 1) *
      (Nat.log2 (bpSparseLevelDomain (x + 1)) + 1) <=
      bpSparseLevelDomain (x + 1) * base :=
    Nat.mul_le_mul_left _ hlog
  have hexp : bpSparseLevelDomain (x + 1) * base = x * base + 3 * base := by
    rw [hD, Nat.add_mul]
  have hcomm : x * base = base * x := Nat.mul_comm x base
  have h3b : 3 * base <= base * (base * base) := by
    have h1 : 3 * base <= (base * base) * base :=
      Nat.mul_le_mul_right base (by omega : 3 <= base * base)
    have h2 : (base * base) * base = base * (base * base) := by
      rw [Nat.mul_assoc]
    omega
  have hsucc : 2 ^ (base + 1) = 2 ^ base * 2 := by rw [Nat.pow_succ]
  have hprod : bpSparseLevelDomain (x + 1) *
      (Nat.log2 (bpSparseLevelDomain (x + 1)) + 1) < 2 ^ (base + 1) := by
    rw [hsucc]; omega
  exact bpSparseLevelWidth_le_of_prod_lt_two_pow hpos hprod


/-- ALL-SIZE FIT, local instance, under the route's own macro-crossing guard. -/
theorem bpSparseLevelLocalWidth_le_machine_of_macro_crossing
    {shape : Cartesian.CartesianShape}
    (hmacro : (RelativeRmm.canonicalLayout shape).macroSize <
        (RelativeRmm.canonicalLayout shape).blockCount) :
    bpSparseLevelWidth
        (bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize) <=
      SuccinctRank.machineWordBits shape.bpCode.length := by
  have hmacroSize : (RelativeRmm.canonicalLayout shape).macroSize
      = canonicalBPRelativeSummaryBase shape *
          canonicalBPRelativeSummaryBase shape := rfl
  have hten := canonicalRelativeRmmBase_ten_le_of_macro_crossing hmacro
  have hcube := canonicalRelativeRmmBase_cube_lt_size_of_macro_crossing hmacro
  have hsizePow := canonicalRelativeRmmSize_lt_two_pow_base shape
  have hcubePow : canonicalBPRelativeSummaryBase shape *
      (canonicalBPRelativeSummaryBase shape *
        canonicalBPRelativeSummaryBase shape) <
      2 ^ canonicalBPRelativeSummaryBase shape := by omega
  have hsizePos : 0 < shape.size := by omega
  have hmachine := canonicalRelativeRmmBase_succ_le_machine_of_size_pos (shape := shape) hsizePos
  rw [hmacroSize]
  exact Nat.le_trans
    (bpSparseLevelWidth_square_domain_le_succ hten hcubePow) hmachine

/-- ALL-SIZE FIT, global instance, under the route's own macro-crossing guard. -/
theorem bpSparseLevelGlobalWidth_le_machine_of_macro_crossing
    {shape : Cartesian.CartesianShape}
    (hmacro : (RelativeRmm.canonicalLayout shape).macroSize <
        (RelativeRmm.canonicalLayout shape).blockCount) :
    bpSparseLevelWidth
        (bpSparseLevelDomain
          (RelativeRmm.canonicalLayout shape).macroSampleCount) <=
      SuccinctRank.machineWordBits shape.bpCode.length := by
  have hten := canonicalRelativeRmmBase_ten_le_of_macro_crossing hmacro
  have hcube := canonicalRelativeRmmBase_cube_lt_size_of_macro_crossing hmacro
  have hsizePow := canonicalRelativeRmmSize_lt_two_pow_base shape
  have hcubePow : canonicalBPRelativeSummaryBase shape *
      (canonicalBPRelativeSummaryBase shape *
        canonicalBPRelativeSummaryBase shape) <
      2 ^ canonicalBPRelativeSummaryBase shape := by omega
  have hsizePos : 0 < shape.size := by omega
  have hmachine := canonicalRelativeRmmBase_succ_le_machine_of_size_pos (shape := shape) hsizePos
  have hsample : (RelativeRmm.canonicalLayout shape).macroSampleCount =
      shape.size / (canonicalBPRelativeSummaryBase shape *
        (canonicalBPRelativeSummaryBase shape *
          canonicalBPRelativeSummaryBase shape)) + 1 := by
    show shape.size / canonicalBPRelativeSummaryBase shape /
        (canonicalBPRelativeSummaryBase shape *
          canonicalBPRelativeSummaryBase shape) + 1 = _
    rw [Nat.div_div_eq_div_mul]
  have hbasePos : 0 < canonicalBPRelativeSummaryBase shape := by omega
  have hsqPos : 0 < canonicalBPRelativeSummaryBase shape *
      canonicalBPRelativeSummaryBase shape := Nat.mul_pos hbasePos hbasePos
  have hNle : canonicalBPRelativeSummaryBase shape <=
      canonicalBPRelativeSummaryBase shape *
        (canonicalBPRelativeSummaryBase shape *
          canonicalBPRelativeSummaryBase shape) :=
    Nat.le_mul_of_pos_right _ hsqPos
  have hNdiv := Nat.mul_div_le shape.size
    (canonicalBPRelativeSummaryBase shape *
      (canonicalBPRelativeSummaryBase shape *
        canonicalBPRelativeSummaryBase shape))
  have hbx : canonicalBPRelativeSummaryBase shape *
      (shape.size / (canonicalBPRelativeSummaryBase shape *
        (canonicalBPRelativeSummaryBase shape *
          canonicalBPRelativeSummaryBase shape))) <= shape.size :=
    Nat.le_trans (Nat.mul_le_mul_right _ hNle) hNdiv
  rw [hsample]
  exact Nat.le_trans
    (bpSparseLevelWidth_sample_domain_le_succ hten hcubePow hsizePow hbx)
    hmachine

theorem canonicalRelativeRmmMachineReadNatCosted_cost_le_eight
    {entries : List Nat} {width : Nat}
    {shape : Cartesian.CartesianShape}
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (hwidth : width <=
      7 * SuccinctRank.machineWordBits shape.bpCode.length)
    (i : Nat) :
    (canonicalRelativeRmmMachineReadNatCosted shape table i).cost <= 8 := by
  let wordSize := SuccinctRank.machineWordBits shape.bpCode.length
  have hwordSize : 0 < wordSize :=
    SuccinctRank.machineWordBits_pos shape.bpCode.length
  have hdiv : width / wordSize <= 7 := by
    apply Nat.div_le_of_le_mul
    simpa [Nat.mul_comm, wordSize] using hwidth
  unfold canonicalRelativeRmmMachineReadNatCosted
  unfold SuccinctSpace.FixedWidthNatTable.machineReadCosted
  rw [SuccinctSpace.FixedWidthNatTable.machineReadCostedWithStore_cost]
  by_cases hvalid : i < entries.length
  · rw [if_pos hvalid]
    change
      (SuccinctSpace.fixedWidthNatTableMachineFootprint width wordSize i).length <= 8
    simp [SuccinctSpace.fixedWidthNatTableMachineFootprint,
      SuccinctSpace.fixedWidthNatTableMachineChunkCount]
    split <;> omega
  · rw [if_neg hvalid]
    omega

theorem costed_bind_cost_le
    {α β : Type} (x : Costed α) (f : α -> Costed β)
    {a b : Nat} (hx : x.cost <= a)
    (hf : forall value, (f value).cost <= b) :
    (Costed.bind x f).cost <= a + b := by
  exact Nat.add_le_add hx (hf x.value)

theorem canonicalRelativeRmmMachineSummaryCosted_cost_le_thirty_two
    (shape : Cartesian.CartesianShape) (block : Nat) :
    (canonicalRelativeRmmMachineSummaryCosted shape block).cost <= 32 := by
  let baselineRead :=
    canonicalRelativeRmmMachineReadNatCosted shape
      (canonicalRelativeRmmSummaryTable shape).baselineTable
      (block / (RelativeRmm.canonicalLayout shape).blocksPerSuper)
  let minRead :=
    canonicalRelativeRmmMachineReadNatCosted shape
      (canonicalRelativeRmmSummaryTable shape).minRelTable block
  let maxRead :=
    canonicalRelativeRmmMachineReadNatCosted shape
      (canonicalRelativeRmmSummaryTable shape).maxRelTable block
  let argRead :=
    canonicalRelativeRmmMachineReadNatCosted shape
      (canonicalRelativeRmmSummaryTable shape).argOffsetTable block
  have hsuper :
      (RelativeRmm.canonicalLayout shape).superWidth shape <=
        7 * SuccinctRank.machineWordBits shape.bpCode.length := by
    simp [RelativeRmm.Layout.superWidth]
    have hpos := SuccinctRank.machineWordBits_pos shape.bpCode.length
    omega
  have hrelative :=
    canonicalRelativeRmmRelativeWidth_le_seven_machine shape
  have hb : baselineRead.cost <= 8 :=
    canonicalRelativeRmmMachineReadNatCosted_cost_le_eight
      (canonicalRelativeRmmSummaryTable shape).baselineTable hsuper
      (block / (RelativeRmm.canonicalLayout shape).blocksPerSuper)
  have hmin : minRead.cost <= 8 :=
    canonicalRelativeRmmMachineReadNatCosted_cost_le_eight
      (canonicalRelativeRmmSummaryTable shape).minRelTable hrelative block
  have hmax : maxRead.cost <= 8 :=
    canonicalRelativeRmmMachineReadNatCosted_cost_le_eight
      (canonicalRelativeRmmSummaryTable shape).maxRelTable hrelative block
  have harg : argRead.cost <= 8 :=
    canonicalRelativeRmmMachineReadNatCosted_cost_le_eight
      (canonicalRelativeRmmSummaryTable shape).argOffsetTable hrelative block
  have h3 (baseline? minRel? maxRel? : Option Nat) :
      (Costed.map
        (fun argOffset? =>
          match baseline?, minRel?, maxRel?, argOffset? with
          | some baseline, some minRel, some maxRel, some argOffset =>
              some (baseline, minRel, maxRel, argOffset)
          | _, _, _, _ => none) argRead).cost <= 8 := by
    simpa [Costed.map] using harg
  have h2 (baseline? minRel? : Option Nat) :
      (Costed.bind maxRead fun maxRel? =>
        Costed.map
          (fun argOffset? =>
            match baseline?, minRel?, maxRel?, argOffset? with
            | some baseline, some minRel, some maxRel, some argOffset =>
                some (baseline, minRel, maxRel, argOffset)
            | _, _, _, _ => none) argRead).cost <= 16 := by
    exact costed_bind_cost_le _ _ hmax (fun maxRel? => h3 _ _ maxRel?)
  have h1 (baseline? : Option Nat) :
      (Costed.bind minRead fun minRel? =>
        Costed.bind maxRead fun maxRel? =>
          Costed.map
            (fun argOffset? =>
              match baseline?, minRel?, maxRel?, argOffset? with
              | some baseline, some minRel, some maxRel, some argOffset =>
                  some (baseline, minRel, maxRel, argOffset)
              | _, _, _, _ => none) argRead).cost <= 24 := by
    exact costed_bind_cost_le _ _ hmin (fun minRel? => h2 _ minRel?)
  have hall :=
    costed_bind_cost_le baselineRead
      (fun baseline? =>
        Costed.bind minRead fun minRel? =>
          Costed.bind maxRead fun maxRel? =>
            Costed.map
              (fun argOffset? =>
                match baseline?, minRel?, maxRel?, argOffset? with
                | some baseline, some minRel, some maxRel, some argOffset =>
                    some (baseline, minRel, maxRel, argOffset)
                | _, _, _, _ => none) argRead)
      hb h1
  simpa [canonicalRelativeRmmMachineSummaryCosted, baselineRead,
    minRead, maxRead, argRead] using hall

theorem canonicalRelativeRmmMachineMinCandidateCosted_cost_le_thirty_two
    (shape : Cartesian.CartesianShape) (block : Nat) :
    (canonicalRelativeRmmMachineMinCandidateCosted shape block).cost <= 32 := by
  simpa [canonicalRelativeRmmMachineMinCandidateCosted, Costed.map] using
    canonicalRelativeRmmMachineSummaryCosted_cost_le_thirty_two shape block

theorem canonicalRelativeRmmMachineLocalSpanCandidateCosted_cost_le_forty
    (shape : Cartesian.CartesianShape)
    (macroIdx localStart level : Nat) :
    (canonicalRelativeRmmMachineLocalSpanCandidateCosted shape
      macroIdx localStart level).cost <= 40 := by
  let read :=
    canonicalRelativeRmmMachineReadNatCosted shape
      (canonicalRelativeRmmInteriorLocalTable shape).table
      (bpLocalSparseCellSlot
        (RelativeRmm.canonicalLayout shape).macroSize
        (RelativeRmm.canonicalLayout shape).levelCount
        macroIdx localStart level)
  have hread : read.cost <= 8 :=
    canonicalRelativeRmmMachineReadNatCosted_cost_le_eight
      (canonicalRelativeRmmInteriorLocalTable shape).table
      (canonicalRelativeRmmOffsetWidth_le_seven_machine shape)
      (bpLocalSparseCellSlot
        (RelativeRmm.canonicalLayout shape).macroSize
        (RelativeRmm.canonicalLayout shape).levelCount
        macroIdx localStart level)
  have htail : forall offset?,
      (match offset? with
      | some offset =>
          canonicalRelativeRmmMachineMinCandidateCosted shape
            (macroIdx * (RelativeRmm.canonicalLayout shape).macroSize + offset)
      | none => Costed.pure none).cost <= 32 := by
    intro offset?
    cases offset? with
    | none => simp [Costed.pure]
    | some offset =>
        exact
          canonicalRelativeRmmMachineMinCandidateCosted_cost_le_thirty_two
            shape
            (macroIdx * (RelativeRmm.canonicalLayout shape).macroSize + offset)
  have hall := costed_bind_cost_le read
    (fun offset? =>
      match offset? with
      | some offset =>
          canonicalRelativeRmmMachineMinCandidateCosted shape
            (macroIdx * (RelativeRmm.canonicalLayout shape).macroSize + offset)
      | none => Costed.pure none)
    hread htail
  simpa [canonicalRelativeRmmMachineLocalSpanCandidateCosted, read] using hall

theorem canonicalRelativeRmmMachineGlobalSpanCandidateCosted_cost_le_forty
    (shape : Cartesian.CartesianShape)
    (macroStart level : Nat) :
    (canonicalRelativeRmmMachineGlobalSpanCandidateCosted shape
      macroStart level).cost <= 40 := by
  let read :=
    canonicalRelativeRmmMachineReadNatCosted shape
      (canonicalRelativeRmmInteriorGlobalTable shape).table
      (bpGlobalSparseCellSlot
        (RelativeRmm.canonicalLayout shape).macroSampleCount
        macroStart level)
  have hread : read.cost <= 8 :=
    canonicalRelativeRmmMachineReadNatCosted_cost_le_eight
      (canonicalRelativeRmmInteriorGlobalTable shape).table
      (canonicalRelativeRmmBlockWidth_le_seven_machine shape)
      (bpGlobalSparseCellSlot
        (RelativeRmm.canonicalLayout shape).macroSampleCount
        macroStart level)
  have htail : forall block?,
      (match block? with
      | some block => canonicalRelativeRmmMachineMinCandidateCosted shape block
      | none => Costed.pure none).cost <= 32 := by
    intro block?
    cases block? with
    | none => simp [Costed.pure]
    | some block =>
        exact
          canonicalRelativeRmmMachineMinCandidateCosted_cost_le_thirty_two
            shape block
  have hall := costed_bind_cost_le read
    (fun block? =>
      match block? with
      | some block => canonicalRelativeRmmMachineMinCandidateCosted shape block
      | none => Costed.pure none)
    hread htail
  simpa [canonicalRelativeRmmMachineGlobalSpanCandidateCosted, read] using hall

/--
Generic all-size cap.  The charged level read is bounded unconditionally at the
`cost_le_eight` rate, via `bpSparseLevelLocalWidth_le_seven_machine`: no branch
guard is available here, so no `hmacro` fit may be assumed.
-/
theorem canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted_cost_le_eighty_eight
    (shape : Cartesian.CartesianShape)
    (macroIdx localStart count : Nat) :
    (canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted shape
      macroIdx localStart count).cost <= 88 := by
  let domain :=
    bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize
  let read :=
    canonicalRelativeRmmMachineReadNatCosted shape
      (canonicalRelativeRmmInteriorLocalLevelTable shape).table count
  have hread : read.cost <= 8 :=
    canonicalRelativeRmmMachineReadNatCosted_cost_le_eight
      (canonicalRelativeRmmInteriorLocalLevelTable shape).table
      (bpSparseLevelLocalWidth_le_seven_machine shape) count
  have htail : forall cell?,
      (match cell? with
      | some cell =>
          Costed.bind
            (canonicalRelativeRmmMachineLocalSpanCandidateCosted shape
              macroIdx localStart (cell / domain)) fun left? =>
            Costed.map (fun right? => bpCandidateMerge? left? right?)
              (canonicalRelativeRmmMachineLocalSpanCandidateCosted shape
                macroIdx (localStart + count - cell % domain) (cell / domain))
      | none => Costed.pure none).cost <= 80 := by
    intro cell?
    cases cell? with
    | none => simp [Costed.pure]
    | some cell =>
        exact costed_bind_cost_le _ _
          (canonicalRelativeRmmMachineLocalSpanCandidateCosted_cost_le_forty
            shape macroIdx localStart (cell / domain))
          (fun _ => by
            simpa [Costed.map] using
              canonicalRelativeRmmMachineLocalSpanCandidateCosted_cost_le_forty
                shape macroIdx (localStart + count - cell % domain)
                (cell / domain))
  have hall := costed_bind_cost_le read
    (fun cell? =>
      match cell? with
      | some cell =>
          Costed.bind
            (canonicalRelativeRmmMachineLocalSpanCandidateCosted shape
              macroIdx localStart (cell / domain)) fun left? =>
            Costed.map (fun right? => bpCandidateMerge? left? right?)
              (canonicalRelativeRmmMachineLocalSpanCandidateCosted shape
                macroIdx (localStart + count - cell % domain) (cell / domain))
      | none => Costed.pure none)
    hread htail
  simpa [canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted, read, domain]
    using hall

/-- Global twin of the generic all-size two-span cap. -/
theorem canonicalRelativeRmmMachineGlobalTwoSpanCandidateCosted_cost_le_eighty_eight
    (shape : Cartesian.CartesianShape)
    (macroStart count : Nat) :
    (canonicalRelativeRmmMachineGlobalTwoSpanCandidateCosted shape
      macroStart count).cost <= 88 := by
  let domain :=
    bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSampleCount
  let read :=
    canonicalRelativeRmmMachineReadNatCosted shape
      (canonicalRelativeRmmInteriorGlobalLevelTable shape).table count
  have hread : read.cost <= 8 :=
    canonicalRelativeRmmMachineReadNatCosted_cost_le_eight
      (canonicalRelativeRmmInteriorGlobalLevelTable shape).table
      (bpSparseLevelGlobalWidth_le_seven_machine shape) count
  have htail : forall cell?,
      (match cell? with
      | some cell =>
          Costed.bind
            (canonicalRelativeRmmMachineGlobalSpanCandidateCosted shape
              macroStart (cell / domain)) fun left? =>
            Costed.map (fun right? => bpCandidateMerge? left? right?)
              (canonicalRelativeRmmMachineGlobalSpanCandidateCosted shape
                (macroStart + count - cell % domain) (cell / domain))
      | none => Costed.pure none).cost <= 80 := by
    intro cell?
    cases cell? with
    | none => simp [Costed.pure]
    | some cell =>
        exact costed_bind_cost_le _ _
          (canonicalRelativeRmmMachineGlobalSpanCandidateCosted_cost_le_forty
            shape macroStart (cell / domain))
          (fun _ => by
            simpa [Costed.map] using
              canonicalRelativeRmmMachineGlobalSpanCandidateCosted_cost_le_forty
                shape (macroStart + count - cell % domain) (cell / domain))
  have hall := costed_bind_cost_le read
    (fun cell? =>
      match cell? with
      | some cell =>
          Costed.bind
            (canonicalRelativeRmmMachineGlobalSpanCandidateCosted shape
              macroStart (cell / domain)) fun left? =>
            Costed.map (fun right? => bpCandidateMerge? left? right?)
              (canonicalRelativeRmmMachineGlobalSpanCandidateCosted shape
                (macroStart + count - cell % domain) (cell / domain))
      | none => Costed.pure none)
    hread htail
  simpa [canonicalRelativeRmmMachineGlobalTwoSpanCandidateCosted, read, domain]
    using hall

theorem canonicalRelativeRmmMachineAdjacentMacroCandidateCosted_cost_le
    (shape : Cartesian.CartesianShape)
    (macroStart localStart rightCount : Nat) :
    (canonicalRelativeRmmMachineAdjacentMacroCandidateCosted shape
      macroStart localStart rightCount).cost <= 176 := by
  let left :=
    canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted shape
      macroStart localStart
      ((RelativeRmm.canonicalLayout shape).macroSize - localStart)
  let right :=
    canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted shape
      (macroStart + 1) 0 rightCount
  have hleft : left.cost <= 88 :=
    canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted_cost_le_eighty_eight
      shape macroStart localStart
      ((RelativeRmm.canonicalLayout shape).macroSize - localStart)
  have hright : right.cost <= 88 :=
    canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted_cost_le_eighty_eight
      shape (macroStart + 1) 0 rightCount
  have hall := costed_bind_cost_le left
    (fun left? => Costed.map (fun right? => bpCandidateMerge? left? right?)
      right)
    hleft (fun _ => by simpa [Costed.map] using hright)
  simpa [canonicalRelativeRmmMachineAdjacentMacroCandidateCosted,
    left, right] using hall

theorem canonicalRelativeRmmMachineLeftMiddleMacroCandidateCosted_cost_le
    (shape : Cartesian.CartesianShape)
    (macroStart localStart middleMacroCount : Nat) :
    (canonicalRelativeRmmMachineLeftMiddleMacroCandidateCosted shape
      macroStart localStart middleMacroCount).cost <= 176 := by
  let left :=
    canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted shape
      macroStart localStart
      ((RelativeRmm.canonicalLayout shape).macroSize - localStart)
  let middle :=
    canonicalRelativeRmmMachineGlobalTwoSpanCandidateCosted shape
      (macroStart + 1) middleMacroCount
  have hleft : left.cost <= 88 :=
    canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted_cost_le_eighty_eight
      shape macroStart localStart
      ((RelativeRmm.canonicalLayout shape).macroSize - localStart)
  have hmiddle : middle.cost <= 88 :=
    canonicalRelativeRmmMachineGlobalTwoSpanCandidateCosted_cost_le_eighty_eight
      shape (macroStart + 1) middleMacroCount
  have hall := costed_bind_cost_le left
    (fun left? => Costed.map (fun middle? => bpCandidateMerge? left? middle?)
      middle)
    hleft (fun _ => by simpa [Costed.map] using hmiddle)
  simpa [canonicalRelativeRmmMachineLeftMiddleMacroCandidateCosted,
    left, middle] using hall

theorem canonicalRelativeRmmMachineCrossMacroCandidateCosted_cost_le
    (shape : Cartesian.CartesianShape)
    (macroStart localStart middleMacroCount rightCount : Nat) :
    (canonicalRelativeRmmMachineCrossMacroCandidateCosted shape
      macroStart localStart middleMacroCount rightCount).cost <= 264 := by
  let left :=
    canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted shape
      macroStart localStart
      ((RelativeRmm.canonicalLayout shape).macroSize - localStart)
  let middle :=
    canonicalRelativeRmmMachineGlobalTwoSpanCandidateCosted shape
      (macroStart + 1) middleMacroCount
  let right :=
    canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted shape
      (macroStart + 1 + middleMacroCount) 0 rightCount
  have hleft : left.cost <= 88 :=
    canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted_cost_le_eighty_eight
      shape macroStart localStart
      ((RelativeRmm.canonicalLayout shape).macroSize - localStart)
  have hmiddle : middle.cost <= 88 :=
    canonicalRelativeRmmMachineGlobalTwoSpanCandidateCosted_cost_le_eighty_eight
      shape (macroStart + 1) middleMacroCount
  have hright : right.cost <= 88 :=
    canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted_cost_le_eighty_eight
      shape (macroStart + 1 + middleMacroCount) 0 rightCount
  have htail : forall left?,
      (Costed.bind middle fun middle? =>
        Costed.map (fun right? => bpCandidateMerge3? left? middle? right?)
          right).cost <= 176 := by
    intro left?
    exact costed_bind_cost_le _ _ hmiddle
      (fun _ => by simpa [Costed.map] using hright)
  have hall := costed_bind_cost_le left
    (fun left? =>
      Costed.bind middle fun middle? =>
        Costed.map (fun right? => bpCandidateMerge3? left? middle? right?)
          right)
    hleft htail
  simpa [canonicalRelativeRmmMachineCrossMacroCandidateCosted,
    left, middle, right] using hall

theorem canonicalRelativeRmmInteriorRangeMinCosted_cost_le
    (shape : Cartesian.CartesianShape) (startBlock count : Nat) :
    (canonicalRelativeRmmInteriorRangeMinCosted shape startBlock count).cost <=
      canonicalRelativeRmmInteriorQueryCost := by
  unfold canonicalRelativeRmmInteriorRangeMinCosted
  by_cases hcount : count = 0
  · simp [hcount, canonicalRelativeRmmInteriorQueryCost, Costed.pure]
  · simp only [hcount, if_false]
    by_cases hwithin :
        count <=
          (RelativeRmm.canonicalLayout shape).macroSize -
            startBlock % (RelativeRmm.canonicalLayout shape).macroSize
    · simp only [hwithin, if_true]
      exact Nat.le_trans
        (canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted_cost_le_eighty_eight
          shape
          (startBlock / (RelativeRmm.canonicalLayout shape).macroSize)
          (startBlock % (RelativeRmm.canonicalLayout shape).macroSize)
          count) (by simp [canonicalRelativeRmmInteriorQueryCost])
    · simp only [hwithin, if_false]
      by_cases hmiddle :
          (count -
              ((RelativeRmm.canonicalLayout shape).macroSize -
                startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) /
              (RelativeRmm.canonicalLayout shape).macroSize = 0
      · simp only [hmiddle, if_true]
        exact Nat.le_trans
          (canonicalRelativeRmmMachineAdjacentMacroCandidateCosted_cost_le
            shape
            (startBlock / (RelativeRmm.canonicalLayout shape).macroSize)
            (startBlock % (RelativeRmm.canonicalLayout shape).macroSize)
            ((count -
                ((RelativeRmm.canonicalLayout shape).macroSize -
                  startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) %
              (RelativeRmm.canonicalLayout shape).macroSize))
          (by simp [canonicalRelativeRmmInteriorQueryCost])
      · simp only [hmiddle, if_false]
        by_cases hright :
            (count -
                ((RelativeRmm.canonicalLayout shape).macroSize -
                  startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) %
                (RelativeRmm.canonicalLayout shape).macroSize = 0
        · simp only [hright, if_true]
          exact Nat.le_trans
            (canonicalRelativeRmmMachineLeftMiddleMacroCandidateCosted_cost_le
              shape
              (startBlock / (RelativeRmm.canonicalLayout shape).macroSize)
              (startBlock % (RelativeRmm.canonicalLayout shape).macroSize)
              ((count -
                  ((RelativeRmm.canonicalLayout shape).macroSize -
                    startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) /
                (RelativeRmm.canonicalLayout shape).macroSize))
            (by simp [canonicalRelativeRmmInteriorQueryCost])
        · simp only [hright, if_false]
          exact
            canonicalRelativeRmmMachineCrossMacroCandidateCosted_cost_le
              shape
              (startBlock / (RelativeRmm.canonicalLayout shape).macroSize)
              (startBlock % (RelativeRmm.canonicalLayout shape).macroSize)
              ((count -
                  ((RelativeRmm.canonicalLayout shape).macroSize -
                    startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) /
                (RelativeRmm.canonicalLayout shape).macroSize)
              ((count -
                  ((RelativeRmm.canonicalLayout shape).macroSize -
                    startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) %
                (RelativeRmm.canonicalLayout shape).macroSize)

/-- Exact charged-read decomposition of one summary-cell execution. -/
theorem canonicalRelativeRmmMachineSummaryCosted_cost_eq
    (shape : Cartesian.CartesianShape) (block : Nat) :
    (canonicalRelativeRmmMachineSummaryCosted shape block).cost =
      (canonicalRelativeRmmMachineReadNatCosted shape
        (canonicalRelativeRmmSummaryTable shape).baselineTable
        (block / (RelativeRmm.canonicalLayout shape).blocksPerSuper)).cost +
      (canonicalRelativeRmmMachineReadNatCosted shape
        (canonicalRelativeRmmSummaryTable shape).minRelTable block).cost +
      (canonicalRelativeRmmMachineReadNatCosted shape
        (canonicalRelativeRmmSummaryTable shape).maxRelTable block).cost +
      (canonicalRelativeRmmMachineReadNatCosted shape
        (canonicalRelativeRmmSummaryTable shape).argOffsetTable block).cost := by
  simp [canonicalRelativeRmmMachineSummaryCosted, Costed.bind, Costed.map,
    Nat.add_assoc]

/-- A canonical summary costs one baseline word plus three two-word fields. -/
theorem canonicalRelativeRmmMachineSummaryCosted_cost_le_seven_of_size_ge_four
    (shape : Cartesian.CartesianShape) (hsize : 4 <= shape.size)
    (block : Nat) :
    (canonicalRelativeRmmMachineSummaryCosted shape block).cost <= 7 := by
  have hsuper :
      (RelativeRmm.canonicalLayout shape).superWidth shape <=
        SuccinctRank.machineWordBits shape.bpCode.length := by
    simp [RelativeRmm.Layout.superWidth]
  have hrelative :=
    canonicalRelativeRmmRelativeWidth_lt_two_machine_of_size_ge_four
      (shape := shape) hsize
  have hb := canonicalRelativeRmmMachineReadNatCosted_cost_le_one
    (canonicalRelativeRmmSummaryTable shape).baselineTable hsuper
    (block / (RelativeRmm.canonicalLayout shape).blocksPerSuper)
  have hmin := canonicalRelativeRmmMachineReadNatCosted_cost_le_two
    (canonicalRelativeRmmSummaryTable shape).minRelTable hrelative block
  have hmax := canonicalRelativeRmmMachineReadNatCosted_cost_le_two
    (canonicalRelativeRmmSummaryTable shape).maxRelTable hrelative block
  have harg := canonicalRelativeRmmMachineReadNatCosted_cost_le_two
    (canonicalRelativeRmmSummaryTable shape).argOffsetTable hrelative block
  rw [canonicalRelativeRmmMachineSummaryCosted_cost_eq]
  omega

/-- In a genuine macro-crossing layout all four summary fields are one word. -/
theorem canonicalRelativeRmmMachineSummaryCosted_cost_le_four_of_macro_crossing
    (shape : Cartesian.CartesianShape)
    (hmacro :
      (RelativeRmm.canonicalLayout shape).macroSize <
        (RelativeRmm.canonicalLayout shape).blockCount)
    (block : Nat) :
    (canonicalRelativeRmmMachineSummaryCosted shape block).cost <= 4 := by
  have hsuper :
      (RelativeRmm.canonicalLayout shape).superWidth shape <=
        SuccinctRank.machineWordBits shape.bpCode.length := by
    simp [RelativeRmm.Layout.superWidth]
  have hrelative :=
    canonicalRelativeRmmRelativeWidth_le_machine_of_macroSize_lt_blockCount
      (shape := shape) hmacro
  have hb := canonicalRelativeRmmMachineReadNatCosted_cost_le_one
    (canonicalRelativeRmmSummaryTable shape).baselineTable hsuper
    (block / (RelativeRmm.canonicalLayout shape).blocksPerSuper)
  have hmin := canonicalRelativeRmmMachineReadNatCosted_cost_le_one
    (canonicalRelativeRmmSummaryTable shape).minRelTable hrelative block
  have hmax := canonicalRelativeRmmMachineReadNatCosted_cost_le_one
    (canonicalRelativeRmmSummaryTable shape).maxRelTable hrelative block
  have harg := canonicalRelativeRmmMachineReadNatCosted_cost_le_one
    (canonicalRelativeRmmSummaryTable shape).argOffsetTable hrelative block
  rw [canonicalRelativeRmmMachineSummaryCosted_cost_eq]
  omega

theorem canonicalRelativeRmmMachineMinCandidateCosted_cost_le_seven_of_size_ge_four
    (shape : Cartesian.CartesianShape) (hsize : 4 <= shape.size)
    (block : Nat) :
    (canonicalRelativeRmmMachineMinCandidateCosted shape block).cost <= 7 := by
  simpa [canonicalRelativeRmmMachineMinCandidateCosted, Costed.map] using
    canonicalRelativeRmmMachineSummaryCosted_cost_le_seven_of_size_ge_four
      shape hsize block

theorem canonicalRelativeRmmMachineMinCandidateCosted_cost_le_four_of_macro_crossing
    (shape : Cartesian.CartesianShape)
    (hmacro :
      (RelativeRmm.canonicalLayout shape).macroSize <
        (RelativeRmm.canonicalLayout shape).blockCount)
    (block : Nat) :
    (canonicalRelativeRmmMachineMinCandidateCosted shape block).cost <= 4 := by
  simpa [canonicalRelativeRmmMachineMinCandidateCosted, Costed.map] using
    canonicalRelativeRmmMachineSummaryCosted_cost_le_four_of_macro_crossing
      shape hmacro block

theorem canonicalRelativeRmmMachineLocalSpanCandidateCosted_cost_le_nine_of_size_ge_four
    (shape : Cartesian.CartesianShape) (hsize : 4 <= shape.size)
    (macroIdx localStart level : Nat) :
    (canonicalRelativeRmmMachineLocalSpanCandidateCosted shape
      macroIdx localStart level).cost <= 9 := by
  let read := canonicalRelativeRmmMachineReadNatCosted shape
    (canonicalRelativeRmmInteriorLocalTable shape).table
    (bpLocalSparseCellSlot
      (RelativeRmm.canonicalLayout shape).macroSize
      (RelativeRmm.canonicalLayout shape).levelCount
      macroIdx localStart level)
  have hoffset :
      (RelativeRmm.canonicalLayout shape).offsetWidth <
        2 * SuccinctRank.machineWordBits shape.bpCode.length :=
    Nat.lt_of_le_of_lt (canonicalRelativeRmmOffsetWidth_le_relativeWidth shape)
      (canonicalRelativeRmmRelativeWidth_lt_two_machine_of_size_ge_four
        (shape := shape) hsize)
  have hread : read.cost <= 2 :=
    canonicalRelativeRmmMachineReadNatCosted_cost_le_two
      (canonicalRelativeRmmInteriorLocalTable shape).table hoffset _
  have htail : forall offset?,
      (match offset? with
      | some offset => canonicalRelativeRmmMachineMinCandidateCosted shape
          (macroIdx * (RelativeRmm.canonicalLayout shape).macroSize + offset)
      | none => Costed.pure none).cost <= 7 := by
    intro offset?
    cases offset? with
    | none => simp [Costed.pure]
    | some offset =>
        exact canonicalRelativeRmmMachineMinCandidateCosted_cost_le_seven_of_size_ge_four
          shape hsize _
  simpa [canonicalRelativeRmmMachineLocalSpanCandidateCosted, read] using
    costed_bind_cost_le read _ hread htail

theorem canonicalRelativeRmmMachineGlobalSpanCandidateCosted_cost_le_eight_of_size_ge_four
    (shape : Cartesian.CartesianShape) (hsize : 4 <= shape.size)
    (macroStart level : Nat) :
    (canonicalRelativeRmmMachineGlobalSpanCandidateCosted shape
      macroStart level).cost <= 8 := by
  let read := canonicalRelativeRmmMachineReadNatCosted shape
    (canonicalRelativeRmmInteriorGlobalTable shape).table
    (bpGlobalSparseCellSlot
      (RelativeRmm.canonicalLayout shape).macroSampleCount macroStart level)
  have hread : read.cost <= 1 :=
    canonicalRelativeRmmMachineReadNatCosted_cost_le_one
      (canonicalRelativeRmmInteriorGlobalTable shape).table
      (canonicalRelativeRmmBlockWidth_le_machine shape) _
  have htail : forall block?,
      (match block? with
      | some block => canonicalRelativeRmmMachineMinCandidateCosted shape block
      | none => Costed.pure none).cost <= 7 := by
    intro block?
    cases block? with
    | none => simp [Costed.pure]
    | some block =>
        exact canonicalRelativeRmmMachineMinCandidateCosted_cost_le_seven_of_size_ge_four
          shape hsize block
  simpa [canonicalRelativeRmmMachineGlobalSpanCandidateCosted, read] using
    costed_bind_cost_le read _ hread htail

theorem canonicalRelativeRmmMachineLocalSpanCandidateCosted_cost_le_five_of_macro_crossing
    (shape : Cartesian.CartesianShape)
    (hmacro :
      (RelativeRmm.canonicalLayout shape).macroSize <
        (RelativeRmm.canonicalLayout shape).blockCount)
    (macroIdx localStart level : Nat) :
    (canonicalRelativeRmmMachineLocalSpanCandidateCosted shape
      macroIdx localStart level).cost <= 5 := by
  let read := canonicalRelativeRmmMachineReadNatCosted shape
    (canonicalRelativeRmmInteriorLocalTable shape).table
    (bpLocalSparseCellSlot
      (RelativeRmm.canonicalLayout shape).macroSize
      (RelativeRmm.canonicalLayout shape).levelCount
      macroIdx localStart level)
  have hrelative :=
    canonicalRelativeRmmRelativeWidth_le_machine_of_macroSize_lt_blockCount
      (shape := shape) hmacro
  have hoffset := Nat.le_trans
    (canonicalRelativeRmmOffsetWidth_le_relativeWidth shape) hrelative
  have hread : read.cost <= 1 :=
    canonicalRelativeRmmMachineReadNatCosted_cost_le_one
      (canonicalRelativeRmmInteriorLocalTable shape).table hoffset _
  have htail : forall offset?,
      (match offset? with
      | some offset => canonicalRelativeRmmMachineMinCandidateCosted shape
          (macroIdx * (RelativeRmm.canonicalLayout shape).macroSize + offset)
      | none => Costed.pure none).cost <= 4 := by
    intro offset?
    cases offset? with
    | none => simp [Costed.pure]
    | some offset =>
        exact canonicalRelativeRmmMachineMinCandidateCosted_cost_le_four_of_macro_crossing
          shape hmacro _
  simpa [canonicalRelativeRmmMachineLocalSpanCandidateCosted, read] using
    costed_bind_cost_le read _ hread htail

theorem canonicalRelativeRmmMachineGlobalSpanCandidateCosted_cost_le_five_of_macro_crossing
    (shape : Cartesian.CartesianShape)
    (hmacro :
      (RelativeRmm.canonicalLayout shape).macroSize <
        (RelativeRmm.canonicalLayout shape).blockCount)
    (macroStart level : Nat) :
    (canonicalRelativeRmmMachineGlobalSpanCandidateCosted shape
      macroStart level).cost <= 5 := by
  let read := canonicalRelativeRmmMachineReadNatCosted shape
    (canonicalRelativeRmmInteriorGlobalTable shape).table
    (bpGlobalSparseCellSlot
      (RelativeRmm.canonicalLayout shape).macroSampleCount macroStart level)
  have hread : read.cost <= 1 :=
    canonicalRelativeRmmMachineReadNatCosted_cost_le_one
      (canonicalRelativeRmmInteriorGlobalTable shape).table
      (canonicalRelativeRmmBlockWidth_le_machine shape) _
  have htail : forall block?,
      (match block? with
      | some block => canonicalRelativeRmmMachineMinCandidateCosted shape block
      | none => Costed.pure none).cost <= 4 := by
    intro block?
    cases block? with
    | none => simp [Costed.pure]
    | some block =>
        exact canonicalRelativeRmmMachineMinCandidateCosted_cost_le_four_of_macro_crossing
          shape hmacro block
  simpa [canonicalRelativeRmmMachineGlobalSpanCandidateCosted, read] using
    costed_bind_cost_le read _ hread htail

/-- Every summary field is a positive one-word field under macro crossing. -/
theorem canonicalRelativeRmmMachineSummaryCosted_cost_eq_four_of_macro_crossing
    (shape : Cartesian.CartesianShape)
    (hmacro :
      (RelativeRmm.canonicalLayout shape).macroSize <
        (RelativeRmm.canonicalLayout shape).blockCount)
    (block : Nat) :
    (canonicalRelativeRmmMachineSummaryCosted shape block).cost = 4 := by
  have hsuperPos :
      0 < (RelativeRmm.canonicalLayout shape).superWidth shape := by
    exact SuccinctRank.machineWordBits_pos shape.bpCode.length
  have hrelativePos :
      0 < (RelativeRmm.canonicalLayout shape).relativeWidth :=
    (RelativeRmm.canonicalLayout_valid shape).relativeWidth_pos
  have hsuper :
      (RelativeRmm.canonicalLayout shape).superWidth shape <=
        SuccinctRank.machineWordBits shape.bpCode.length := by
    simp [RelativeRmm.Layout.superWidth]
  have hrelative :=
    canonicalRelativeRmmRelativeWidth_le_machine_of_macroSize_lt_blockCount
      (shape := shape) hmacro
  have hb := canonicalRelativeRmmMachineReadNatCosted_cost_eq_one
    (canonicalRelativeRmmSummaryTable shape).baselineTable hsuperPos hsuper
    (block / (RelativeRmm.canonicalLayout shape).blocksPerSuper)
  have hmin := canonicalRelativeRmmMachineReadNatCosted_cost_eq_one
    (canonicalRelativeRmmSummaryTable shape).minRelTable hrelativePos hrelative
    block
  have hmax := canonicalRelativeRmmMachineReadNatCosted_cost_eq_one
    (canonicalRelativeRmmSummaryTable shape).maxRelTable hrelativePos hrelative
    block
  have harg := canonicalRelativeRmmMachineReadNatCosted_cost_eq_one
    (canonicalRelativeRmmSummaryTable shape).argOffsetTable hrelativePos
    hrelative block
  rw [canonicalRelativeRmmMachineSummaryCosted_cost_eq, hb, hmin, hmax, harg]

theorem canonicalRelativeRmmMachineMinCandidateCosted_cost_eq_four_of_macro_crossing
    (shape : Cartesian.CartesianShape)
    (hmacro :
      (RelativeRmm.canonicalLayout shape).macroSize <
        (RelativeRmm.canonicalLayout shape).blockCount)
    (block : Nat) :
    (canonicalRelativeRmmMachineMinCandidateCosted shape block).cost = 4 := by
  simpa [canonicalRelativeRmmMachineMinCandidateCosted, Costed.map] using
    canonicalRelativeRmmMachineSummaryCosted_cost_eq_four_of_macro_crossing
      shape hmacro block

/-- A live local sparse cell followed by its summary costs exactly five reads. -/
theorem canonicalRelativeRmmMachineLocalSpanCandidateCosted_cost_eq_five
    (shape : Cartesian.CartesianShape)
    (hmacroCrossing :
      (RelativeRmm.canonicalLayout shape).macroSize <
        (RelativeRmm.canonicalLayout shape).blockCount)
    (macroIdx localStart level : Nat)
    (hmacro : macroIdx <
      (RelativeRmm.canonicalLayout shape).macroSampleCount)
    (hlevel : level < (RelativeRmm.canonicalLayout shape).levelCount)
    (hlocal : localStart < (RelativeRmm.canonicalLayout shape).macroSize) :
    (canonicalRelativeRmmMachineLocalSpanCandidateCosted shape
      macroIdx localStart level).cost = 5 := by
  let layout := RelativeRmm.canonicalLayout shape
  let read := canonicalRelativeRmmMachineReadNatCosted shape
    (canonicalRelativeRmmInteriorLocalTable shape).table
    (bpLocalSparseCellSlot layout.macroSize layout.levelCount
      macroIdx localStart level)
  let offset :=
    bpLocalSparseCellOffset shape layout.blockSize layout.blockCount
      layout.macroSize macroIdx localStart level
  have hreadValue : read.value = some offset := by
    change read.erase = some offset
    unfold read
    rw [canonicalRelativeRmmMachineReadNatCosted_erase]
    simpa [PayloadLiveBPLocalSparseOffsetTable.readOffsetCosted,
      layout, offset] using
      (canonicalRelativeRmmInteriorLocalTable shape).readOffsetCosted_erase_of_valid
        hmacro hlevel hlocal
  have hoffsetPos : 0 < layout.offsetWidth := by
    exact SuccinctRank.machineWordBits_pos layout.macroSize
  have hrelative :=
    canonicalRelativeRmmRelativeWidth_le_machine_of_macroSize_lt_blockCount
      (shape := shape) hmacroCrossing
  have hoffset := Nat.le_trans
    (canonicalRelativeRmmOffsetWidth_le_relativeWidth shape) hrelative
  have hreadCost : read.cost = 1 := by
    exact canonicalRelativeRmmMachineReadNatCosted_cost_eq_one
      (canonicalRelativeRmmInteriorLocalTable shape).table
      hoffsetPos hoffset _
  have hsummary :
      (canonicalRelativeRmmMachineMinCandidateCosted shape
        (macroIdx * layout.macroSize + offset)).cost = 4 :=
    canonicalRelativeRmmMachineMinCandidateCosted_cost_eq_four_of_macro_crossing
      shape hmacroCrossing _
  change (Costed.bind read fun offset? =>
    match offset? with
    | some offset => canonicalRelativeRmmMachineMinCandidateCosted shape
        (macroIdx * layout.macroSize + offset)
    | none => Costed.pure none).cost = 5
  rw [Costed.cost_bind, hreadValue, hreadCost, hsummary]

/-- A live global sparse cell followed by its summary costs exactly five reads. -/
theorem canonicalRelativeRmmMachineGlobalSpanCandidateCosted_cost_eq_five
    (shape : Cartesian.CartesianShape)
    (hmacroCrossing :
      (RelativeRmm.canonicalLayout shape).macroSize <
        (RelativeRmm.canonicalLayout shape).blockCount)
    (macroStart level : Nat)
    (hlevel : level <
      (RelativeRmm.canonicalLayout shape).globalLevelCount)
    (hmacro : macroStart <
      (RelativeRmm.canonicalLayout shape).macroSampleCount) :
    (canonicalRelativeRmmMachineGlobalSpanCandidateCosted shape
      macroStart level).cost = 5 := by
  let layout := RelativeRmm.canonicalLayout shape
  let read := canonicalRelativeRmmMachineReadNatCosted shape
    (canonicalRelativeRmmInteriorGlobalTable shape).table
    (bpGlobalSparseCellSlot layout.macroSampleCount macroStart level)
  let block :=
    bpGlobalSparseCellBlock shape layout.blockSize layout.blockCount
      layout.macroSize layout.macroSampleCount macroStart level
  have hreadValue : read.value = some block := by
    change read.erase = some block
    unfold read
    rw [canonicalRelativeRmmMachineReadNatCosted_erase]
    simpa [PayloadLiveBPGlobalSparseBlockTable.readBlockCosted,
      layout, block] using
      (canonicalRelativeRmmInteriorGlobalTable shape).readBlockCosted_erase_of_valid
        hlevel hmacro
  have hblockPos : 0 < layout.blockAddressWidth := by
    exact SuccinctRank.machineWordBits_pos layout.blockCount
  have hblockWidth := canonicalRelativeRmmBlockWidth_le_machine shape
  have hreadCost : read.cost = 1 := by
    exact canonicalRelativeRmmMachineReadNatCosted_cost_eq_one
      (canonicalRelativeRmmInteriorGlobalTable shape).table
      hblockPos hblockWidth _
  have hsummary :
      (canonicalRelativeRmmMachineMinCandidateCosted shape block).cost = 4 :=
    canonicalRelativeRmmMachineMinCandidateCosted_cost_eq_four_of_macro_crossing
      shape hmacroCrossing block
  change (Costed.bind read fun block? =>
    match block? with
    | some block => canonicalRelativeRmmMachineMinCandidateCosted shape block
    | none => Costed.pure none).cost = 5
  rw [Costed.cost_bind, hreadValue, hreadCost, hsummary]

/--
Within-macro branch.  Only `4 <= shape.size` is available here - no macro
crossing - so the charged level read is bounded at the unconditional
`cost_le_eight` rate.  The branch has ample headroom under the interior cap:
`26 <= 33`.
-/
theorem canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted_cost_le_twenty_six_of_size_ge_four
    (shape : Cartesian.CartesianShape) (hsize : 4 <= shape.size)
    (macroIdx localStart count : Nat) :
    (canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted shape
      macroIdx localStart count).cost <= 26 := by
  let domain :=
    bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize
  let read :=
    canonicalRelativeRmmMachineReadNatCosted shape
      (canonicalRelativeRmmInteriorLocalLevelTable shape).table count
  have hread : read.cost <= 8 :=
    canonicalRelativeRmmMachineReadNatCosted_cost_le_eight
      (canonicalRelativeRmmInteriorLocalLevelTable shape).table
      (bpSparseLevelLocalWidth_le_seven_machine shape) count
  have htail : forall cell?,
      (match cell? with
      | some cell =>
          Costed.bind
            (canonicalRelativeRmmMachineLocalSpanCandidateCosted shape
              macroIdx localStart (cell / domain)) fun left? =>
            Costed.map (fun right? => bpCandidateMerge? left? right?)
              (canonicalRelativeRmmMachineLocalSpanCandidateCosted shape
                macroIdx (localStart + count - cell % domain) (cell / domain))
      | none => Costed.pure none).cost <= 18 := by
    intro cell?
    cases cell? with
    | none => simp [Costed.pure]
    | some cell =>
        exact costed_bind_cost_le _ _
          (canonicalRelativeRmmMachineLocalSpanCandidateCosted_cost_le_nine_of_size_ge_four
            shape hsize _ _ _)
          (fun _ => by
            simpa [Costed.map] using
              canonicalRelativeRmmMachineLocalSpanCandidateCosted_cost_le_nine_of_size_ge_four
                shape hsize macroIdx (localStart + count - cell % domain)
                (cell / domain))
  have hall := costed_bind_cost_le read
    (fun cell? =>
      match cell? with
      | some cell =>
          Costed.bind
            (canonicalRelativeRmmMachineLocalSpanCandidateCosted shape
              macroIdx localStart (cell / domain)) fun left? =>
            Costed.map (fun right? => bpCandidateMerge? left? right?)
              (canonicalRelativeRmmMachineLocalSpanCandidateCosted shape
                macroIdx (localStart + count - cell % domain) (cell / domain))
      | none => Costed.pure none)
    hread htail
  simpa [canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted, read, domain]
    using hall

/--
THE MAXIMIZING-BRANCH LEAF.  Under macro crossing the charged level read fits
in ONE machine word (`bpSparseLevelLocalWidth_le_machine_of_macro_crossing`),
so it costs exactly one charged event: `1 + 5 + 5 = 11`.  This is the read
that enters the accounting and moves the route literal.
-/
theorem canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted_cost_le_eleven_of_macro_crossing
    (shape : Cartesian.CartesianShape)
    (hmacro :
      (RelativeRmm.canonicalLayout shape).macroSize <
        (RelativeRmm.canonicalLayout shape).blockCount)
    (macroIdx localStart count : Nat) :
    (canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted shape
      macroIdx localStart count).cost <= 11 := by
  let domain :=
    bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize
  let read :=
    canonicalRelativeRmmMachineReadNatCosted shape
      (canonicalRelativeRmmInteriorLocalLevelTable shape).table count
  have hread : read.cost <= 1 :=
    canonicalRelativeRmmMachineReadNatCosted_cost_le_one
      (canonicalRelativeRmmInteriorLocalLevelTable shape).table
      (bpSparseLevelLocalWidth_le_machine_of_macro_crossing hmacro) count
  have htail : forall cell?,
      (match cell? with
      | some cell =>
          Costed.bind
            (canonicalRelativeRmmMachineLocalSpanCandidateCosted shape
              macroIdx localStart (cell / domain)) fun left? =>
            Costed.map (fun right? => bpCandidateMerge? left? right?)
              (canonicalRelativeRmmMachineLocalSpanCandidateCosted shape
                macroIdx (localStart + count - cell % domain) (cell / domain))
      | none => Costed.pure none).cost <= 10 := by
    intro cell?
    cases cell? with
    | none => simp [Costed.pure]
    | some cell =>
        exact costed_bind_cost_le _ _
          (canonicalRelativeRmmMachineLocalSpanCandidateCosted_cost_le_five_of_macro_crossing
            shape hmacro _ _ _)
          (fun _ => by
            simpa [Costed.map] using
              canonicalRelativeRmmMachineLocalSpanCandidateCosted_cost_le_five_of_macro_crossing
                shape hmacro macroIdx (localStart + count - cell % domain)
                (cell / domain))
  have hall := costed_bind_cost_le read
    (fun cell? =>
      match cell? with
      | some cell =>
          Costed.bind
            (canonicalRelativeRmmMachineLocalSpanCandidateCosted shape
              macroIdx localStart (cell / domain)) fun left? =>
            Costed.map (fun right? => bpCandidateMerge? left? right?)
              (canonicalRelativeRmmMachineLocalSpanCandidateCosted shape
                macroIdx (localStart + count - cell % domain) (cell / domain))
      | none => Costed.pure none)
    hread htail
  simpa [canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted, read, domain]
    using hall

/-- Global twin of the maximizing-branch leaf: `1 + 5 + 5 = 11`. -/
theorem canonicalRelativeRmmMachineGlobalTwoSpanCandidateCosted_cost_le_eleven_of_macro_crossing
    (shape : Cartesian.CartesianShape)
    (hmacro :
      (RelativeRmm.canonicalLayout shape).macroSize <
        (RelativeRmm.canonicalLayout shape).blockCount)
    (macroStart count : Nat) :
    (canonicalRelativeRmmMachineGlobalTwoSpanCandidateCosted shape
      macroStart count).cost <= 11 := by
  let domain :=
    bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSampleCount
  let read :=
    canonicalRelativeRmmMachineReadNatCosted shape
      (canonicalRelativeRmmInteriorGlobalLevelTable shape).table count
  have hread : read.cost <= 1 :=
    canonicalRelativeRmmMachineReadNatCosted_cost_le_one
      (canonicalRelativeRmmInteriorGlobalLevelTable shape).table
      (bpSparseLevelGlobalWidth_le_machine_of_macro_crossing hmacro) count
  have htail : forall cell?,
      (match cell? with
      | some cell =>
          Costed.bind
            (canonicalRelativeRmmMachineGlobalSpanCandidateCosted shape
              macroStart (cell / domain)) fun left? =>
            Costed.map (fun right? => bpCandidateMerge? left? right?)
              (canonicalRelativeRmmMachineGlobalSpanCandidateCosted shape
                (macroStart + count - cell % domain) (cell / domain))
      | none => Costed.pure none).cost <= 10 := by
    intro cell?
    cases cell? with
    | none => simp [Costed.pure]
    | some cell =>
        exact costed_bind_cost_le _ _
          (canonicalRelativeRmmMachineGlobalSpanCandidateCosted_cost_le_five_of_macro_crossing
            shape hmacro _ _)
          (fun _ => by
            simpa [Costed.map] using
              canonicalRelativeRmmMachineGlobalSpanCandidateCosted_cost_le_five_of_macro_crossing
                shape hmacro (macroStart + count - cell % domain)
                (cell / domain))
  have hall := costed_bind_cost_le read
    (fun cell? =>
      match cell? with
      | some cell =>
          Costed.bind
            (canonicalRelativeRmmMachineGlobalSpanCandidateCosted shape
              macroStart (cell / domain)) fun left? =>
            Costed.map (fun right? => bpCandidateMerge? left? right?)
              (canonicalRelativeRmmMachineGlobalSpanCandidateCosted shape
                (macroStart + count - cell % domain) (cell / domain))
      | none => Costed.pure none)
    hread htail
  simpa [canonicalRelativeRmmMachineGlobalTwoSpanCandidateCosted, read, domain]
    using hall

/-- A live count-one local two-span call performs `1 + 5 + 5` reads. -/
theorem canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted_cost_eq_eleven_of_one
    (shape : Cartesian.CartesianShape)
    (hmacroCrossing :
      (RelativeRmm.canonicalLayout shape).macroSize <
        (RelativeRmm.canonicalLayout shape).blockCount)
    (macroIdx localStart : Nat)
    (hmacro : macroIdx <
      (RelativeRmm.canonicalLayout shape).macroSampleCount)
    (hlocal : localStart <
      (RelativeRmm.canonicalLayout shape).macroSize) :
    (canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted shape
      macroIdx localStart 1).cost = 11 := by
  let layout := RelativeRmm.canonicalLayout shape
  let domain := bpSparseLevelDomain layout.macroSize
  let read := canonicalRelativeRmmMachineReadNatCosted shape
    (canonicalRelativeRmmInteriorLocalLevelTable shape).table 1
  have honeLt : 1 < domain := by
    have := two_le_bpSparseLevelDomain layout.macroSize
    simpa [domain] using this
  have hreadValue : read.value = some 1 := by
    change read.erase = some 1
    unfold read
    rw [canonicalRelativeRmmMachineReadNatCosted_erase,
      SuccinctSpace.FixedWidthNatTable.readCosted_erase]
    change (bpSparseLevelEntries domain)[1]? = some 1
    rw [bpSparseLevelEntries_getElem? honeLt]
    have hlog : Nat.log2 1 = 0 := by
      have hpow : (1 : Nat) < 2 ^ (1 : Nat) := by simp
      have hlt : Nat.log2 1 < 1 :=
        (Nat.log2_lt (by omega : Not ((1 : Nat) = 0))).2 hpow
      omega
    simp [bpSparseLevelCell, bpSparseLogSpan, hlog]
  have hwidthPos : 0 < bpSparseLevelWidth domain := by
    simp [bpSparseLevelWidth]
  have hwidth : bpSparseLevelWidth domain <=
      SuccinctRank.machineWordBits shape.bpCode.length := by
    simpa [domain, layout] using
      bpSparseLevelLocalWidth_le_machine_of_macro_crossing hmacroCrossing
  have hreadCost : read.cost = 1 := by
    exact canonicalRelativeRmmMachineReadNatCosted_cost_eq_one
      (canonicalRelativeRmmInteriorLocalLevelTable shape).table
      hwidthPos hwidth 1
  have hlevelPos : 0 < layout.levelCount := by
    exact SuccinctRank.machineWordBits_pos layout.macroSize
  have hleft :=
    canonicalRelativeRmmMachineLocalSpanCandidateCosted_cost_eq_five
      shape hmacroCrossing macroIdx localStart 0 hmacro hlevelPos hlocal
  have hright := hleft
  have hdiv : 1 / domain = 0 := Nat.div_eq_of_lt honeLt
  have hmod : 1 % domain = 1 := Nat.mod_eq_of_lt honeLt
  have hrightStart : localStart + 1 - 1 = localStart := by omega
  change (Costed.bind read fun cell? =>
    match cell? with
    | some cell =>
        Costed.bind
          (canonicalRelativeRmmMachineLocalSpanCandidateCosted shape
            macroIdx localStart (cell / domain)) fun left? =>
          Costed.map (fun right? => bpCandidateMerge? left? right?)
            (canonicalRelativeRmmMachineLocalSpanCandidateCosted shape
              macroIdx (localStart + 1 - cell % domain) (cell / domain))
    | none => Costed.pure none).cost = 11
  rw [Costed.cost_bind, hreadValue]
  simp only [hdiv, hmod]
  rw [hrightStart, Costed.cost_bind, Costed.map_cost, hreadCost, hleft]

/-- A live count-one global two-span call performs `1 + 5 + 5` reads. -/
theorem canonicalRelativeRmmMachineGlobalTwoSpanCandidateCosted_cost_eq_eleven_of_one
    (shape : Cartesian.CartesianShape)
    (hmacroCrossing :
      (RelativeRmm.canonicalLayout shape).macroSize <
        (RelativeRmm.canonicalLayout shape).blockCount)
    (macroStart : Nat)
    (hmacro : macroStart <
      (RelativeRmm.canonicalLayout shape).macroSampleCount) :
    (canonicalRelativeRmmMachineGlobalTwoSpanCandidateCosted shape
      macroStart 1).cost = 11 := by
  let layout := RelativeRmm.canonicalLayout shape
  let domain := bpSparseLevelDomain layout.macroSampleCount
  let read := canonicalRelativeRmmMachineReadNatCosted shape
    (canonicalRelativeRmmInteriorGlobalLevelTable shape).table 1
  have honeLt : 1 < domain := by
    have := two_le_bpSparseLevelDomain layout.macroSampleCount
    simpa [domain] using this
  have hreadValue : read.value = some 1 := by
    change read.erase = some 1
    unfold read
    rw [canonicalRelativeRmmMachineReadNatCosted_erase,
      SuccinctSpace.FixedWidthNatTable.readCosted_erase]
    change (bpSparseLevelEntries domain)[1]? = some 1
    rw [bpSparseLevelEntries_getElem? honeLt]
    have hlog : Nat.log2 1 = 0 := by
      have hpow : (1 : Nat) < 2 ^ (1 : Nat) := by simp
      have hlt : Nat.log2 1 < 1 :=
        (Nat.log2_lt (by omega : Not ((1 : Nat) = 0))).2 hpow
      omega
    simp [bpSparseLevelCell, bpSparseLogSpan, hlog]
  have hwidthPos : 0 < bpSparseLevelWidth domain := by
    simp [bpSparseLevelWidth]
  have hwidth : bpSparseLevelWidth domain <=
      SuccinctRank.machineWordBits shape.bpCode.length := by
    simpa [domain, layout] using
      bpSparseLevelGlobalWidth_le_machine_of_macro_crossing hmacroCrossing
  have hreadCost : read.cost = 1 := by
    exact canonicalRelativeRmmMachineReadNatCosted_cost_eq_one
      (canonicalRelativeRmmInteriorGlobalLevelTable shape).table
      hwidthPos hwidth 1
  have hlevelPos : 0 < layout.globalLevelCount := by
    exact SuccinctRank.machineWordBits_pos layout.macroSampleCount
  have hleft :=
    canonicalRelativeRmmMachineGlobalSpanCandidateCosted_cost_eq_five
      shape hmacroCrossing macroStart 0 hlevelPos hmacro
  have hright := hleft
  have hdiv : 1 / domain = 0 := Nat.div_eq_of_lt honeLt
  have hmod : 1 % domain = 1 := Nat.mod_eq_of_lt honeLt
  have hrightStart : macroStart + 1 - 1 = macroStart := by omega
  change (Costed.bind read fun cell? =>
    match cell? with
    | some cell =>
        Costed.bind
          (canonicalRelativeRmmMachineGlobalSpanCandidateCosted shape
            macroStart (cell / domain)) fun left? =>
          Costed.map (fun right? => bpCandidateMerge? left? right?)
            (canonicalRelativeRmmMachineGlobalSpanCandidateCosted shape
              (macroStart + 1 - cell % domain) (cell / domain))
    | none => Costed.pure none).cost = 11
  rw [Costed.cost_bind, hreadValue]
  simp only [hdiv, hmod]
  rw [hrightStart, Costed.cost_bind, Costed.map_cost, hreadCost, hleft]

theorem canonicalRelativeRmmMachineAdjacentMacroCandidateCosted_cost_le_twenty_two_of_macro_crossing
    (shape : Cartesian.CartesianShape)
    (hmacro :
      (RelativeRmm.canonicalLayout shape).macroSize <
        (RelativeRmm.canonicalLayout shape).blockCount)
    (macroStart localStart rightCount : Nat) :
    (canonicalRelativeRmmMachineAdjacentMacroCandidateCosted shape
      macroStart localStart rightCount).cost <= 22 := by
  let left := canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted shape
    macroStart localStart
    ((RelativeRmm.canonicalLayout shape).macroSize - localStart)
  let right := canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted shape
    (macroStart + 1) 0 rightCount
  have hleft : left.cost <= 11 :=
    canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted_cost_le_eleven_of_macro_crossing
      shape hmacro _ _ _
  have hright : right.cost <= 11 :=
    canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted_cost_le_eleven_of_macro_crossing
      shape hmacro _ _ _
  have hall := costed_bind_cost_le left
    (fun left? => Costed.map (fun right? => bpCandidateMerge? left? right?) right)
    hleft (fun _ => by simpa [Costed.map] using hright)
  simpa [canonicalRelativeRmmMachineAdjacentMacroCandidateCosted,
    left, right] using hall

theorem canonicalRelativeRmmMachineLeftMiddleMacroCandidateCosted_cost_le_twenty_two_of_macro_crossing
    (shape : Cartesian.CartesianShape)
    (hmacro :
      (RelativeRmm.canonicalLayout shape).macroSize <
        (RelativeRmm.canonicalLayout shape).blockCount)
    (macroStart localStart middleMacroCount : Nat) :
    (canonicalRelativeRmmMachineLeftMiddleMacroCandidateCosted shape
      macroStart localStart middleMacroCount).cost <= 22 := by
  let left := canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted shape
    macroStart localStart
    ((RelativeRmm.canonicalLayout shape).macroSize - localStart)
  let middle := canonicalRelativeRmmMachineGlobalTwoSpanCandidateCosted shape
    (macroStart + 1) middleMacroCount
  have hleft : left.cost <= 11 :=
    canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted_cost_le_eleven_of_macro_crossing
      shape hmacro _ _ _
  have hmiddle : middle.cost <= 11 :=
    canonicalRelativeRmmMachineGlobalTwoSpanCandidateCosted_cost_le_eleven_of_macro_crossing
      shape hmacro _ _
  have hall := costed_bind_cost_le left
    (fun left? => Costed.map (fun middle? => bpCandidateMerge? left? middle?) middle)
    hleft (fun _ => by simpa [Costed.map] using hmiddle)
  simpa [canonicalRelativeRmmMachineLeftMiddleMacroCandidateCosted,
    left, middle] using hall

theorem canonicalRelativeRmmMachineCrossMacroCandidateCosted_cost_le_thirty_three_of_macro_crossing
    (shape : Cartesian.CartesianShape)
    (hmacro :
      (RelativeRmm.canonicalLayout shape).macroSize <
        (RelativeRmm.canonicalLayout shape).blockCount)
    (macroStart localStart middleMacroCount rightCount : Nat) :
    (canonicalRelativeRmmMachineCrossMacroCandidateCosted shape
      macroStart localStart middleMacroCount rightCount).cost <= 33 := by
  let left := canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted shape
    macroStart localStart
    ((RelativeRmm.canonicalLayout shape).macroSize - localStart)
  let middle := canonicalRelativeRmmMachineGlobalTwoSpanCandidateCosted shape
    (macroStart + 1) middleMacroCount
  let right := canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted shape
    (macroStart + 1 + middleMacroCount) 0 rightCount
  have hleft : left.cost <= 11 :=
    canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted_cost_le_eleven_of_macro_crossing
      shape hmacro _ _ _
  have hmiddle : middle.cost <= 11 :=
    canonicalRelativeRmmMachineGlobalTwoSpanCandidateCosted_cost_le_eleven_of_macro_crossing
      shape hmacro _ _
  have hright : right.cost <= 11 :=
    canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted_cost_le_eleven_of_macro_crossing
      shape hmacro _ _ _
  have htail : forall left?,
      (Costed.bind middle fun middle? =>
        Costed.map (fun right? => bpCandidateMerge3? left? middle? right?) right).cost <= 22 := by
    intro left?
    exact costed_bind_cost_le _ _ hmiddle
      (fun _ => by simpa [Costed.map] using hright)
  have hall := costed_bind_cost_le left
    (fun left? => Costed.bind middle fun middle? =>
      Costed.map (fun right? => bpCandidateMerge3? left? middle? right?) right)
    hleft htail
  simpa [canonicalRelativeRmmMachineCrossMacroCandidateCosted,
    left, middle, right] using hall

/-!
### Canonical exact-cost witness for the charged sparse-level route

The right-spine witness below is deliberately a real Cartesian shape, with an
ordinary `List Int` representative.  Its list-facing window `[1704, 3469)`
selects closes `3409` and `6937`; the accepted cross-block consumer therefore
passes the interior range `(startBlock, count) = (143, 146)`.  That range takes
the cross-macro branch with parameters `(0, 143, 1, 1)` and performs three
successful eleven-read two-span calls.
-/

def canonicalRelativeRmmInteriorCost33RightSpine :
    Nat -> Cartesian.CartesianShape
  | 0 => .empty
  | n + 1 => .node .empty (canonicalRelativeRmmInteriorCost33RightSpine n)

theorem canonicalRelativeRmmInteriorCost33RightSpine_size (n : Nat) :
    (canonicalRelativeRmmInteriorCost33RightSpine n).size = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [canonicalRelativeRmmInteriorCost33RightSpine,
        Cartesian.CartesianShape.size, ih]
      omega

def canonicalRelativeRmmInteriorCost33WitnessShape :
    Cartesian.CartesianShape :=
  canonicalRelativeRmmInteriorCost33RightSpine 3469

def canonicalRelativeRmmInteriorCost33WitnessInput : List Int :=
  canonicalRelativeRmmInteriorCost33WitnessShape.representative

theorem canonicalRelativeRmmInteriorCost33WitnessShape_size :
    canonicalRelativeRmmInteriorCost33WitnessShape.size = 3469 := by
  exact canonicalRelativeRmmInteriorCost33RightSpine_size 3469

theorem canonicalRelativeRmmInteriorCost33WitnessInput_length :
    canonicalRelativeRmmInteriorCost33WitnessInput.length = 3469 := by
  simp [canonicalRelativeRmmInteriorCost33WitnessInput,
    Cartesian.CartesianShape.representative_length,
    canonicalRelativeRmmInteriorCost33WitnessShape_size]

theorem canonicalRelativeRmmInteriorCost33WitnessInput_shape :
    Cartesian.shape canonicalRelativeRmmInteriorCost33WitnessInput =
      canonicalRelativeRmmInteriorCost33WitnessShape := by
  simp [canonicalRelativeRmmInteriorCost33WitnessInput,
    Cartesian.CartesianShape.shape_representative]

theorem canonicalRelativeRmmInteriorCost33RightSpine_close
    (n i : Nat) (hi : i < n) :
    SuccinctSpace.bpCloseOfInorder?
        (canonicalRelativeRmmInteriorCost33RightSpine n) i =
      some (2 * i + 1) := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
      by_cases hzero : i = 0
      · subst i
        simp [canonicalRelativeRmmInteriorCost33RightSpine,
          SuccinctSpace.bpCloseOfInorder?, Cartesian.CartesianShape.size,
          Cartesian.CartesianShape.bpCode]
      · have hpos : 0 < i := Nat.pos_of_ne_zero hzero
        have htail : i - 1 < n := by omega
        have ih' := ih (i - 1) htail
        simp [canonicalRelativeRmmInteriorCost33RightSpine,
          SuccinctSpace.bpCloseOfInorder?, Cartesian.CartesianShape.size,
          Cartesian.CartesianShape.bpCode, hzero, ih']
        omega

theorem canonicalRelativeRmmInteriorCost33Witness_closes :
    SuccinctSpace.bpCloseOfInorder?
        canonicalRelativeRmmInteriorCost33WitnessShape 1704 = some 3409 /\
      SuccinctSpace.bpCloseOfInorder?
        canonicalRelativeRmmInteriorCost33WitnessShape 3468 = some 6937 := by
  constructor
  · simpa [canonicalRelativeRmmInteriorCost33WitnessShape] using
      canonicalRelativeRmmInteriorCost33RightSpine_close 3469 1704 (by omega)
  · simpa [canonicalRelativeRmmInteriorCost33WitnessShape] using
      canonicalRelativeRmmInteriorCost33RightSpine_close 3469 3468 (by omega)

/-- The numeral geometry used by the reachable tightness family. -/
theorem canonicalRelativeRmmInteriorCost33Layout_of_size_eq
    (shape : Cartesian.CartesianShape) (hsize : shape.size = 3469) :
    (RelativeRmm.canonicalLayout shape).blockSize = 24 /\
      (RelativeRmm.canonicalLayout shape).blocksPerSuper = 12 /\
      (RelativeRmm.canonicalLayout shape).blockCount = 289 /\
      (RelativeRmm.canonicalLayout shape).macroSize = 144 /\
      (RelativeRmm.canonicalLayout shape).macroSampleCount = 3 := by
  simp only [RelativeRmm.canonicalLayout,
    RelativeRmm.Layout.macroSize, RelativeRmm.Layout.macroSampleCount,
    canonicalBPRelativeSummaryBlockSizeRaw,
    canonicalBPRelativeSummaryBlocksPerSuperRaw,
    canonicalBPRelativeSummaryBlockCountRaw,
    canonicalBPRelativeSummaryBase]
  rw [hsize]
  have hlower : 11 <= Nat.log2 3469 :=
    (Nat.le_log2 (by decide : Not ((3469 : Nat) = 0))).2 (by decide)
  have hupper : Nat.log2 3469 < 12 :=
    (Nat.log2_lt (by decide : Not ((3469 : Nat) = 0))).2 (by decide)
  have hlog : Nat.log2 3469 = 11 := by omega
  rw [hlog]
  decide

/-- The accepted interior dispatcher takes the three-leaf cross-macro route. -/
theorem canonicalRelativeRmmInteriorCost33_dispatch_of_size_eq
    (shape : Cartesian.CartesianShape) (hsize : shape.size = 3469) :
    canonicalRelativeRmmInteriorRangeMinCosted shape 143 146 =
      canonicalRelativeRmmMachineCrossMacroCandidateCosted shape 0 143 1 1 := by
  have hgeometry := canonicalRelativeRmmInteriorCost33Layout_of_size_eq shape hsize
  rcases hgeometry with ⟨_, _, _, hmacroSize, _⟩
  simp [canonicalRelativeRmmInteriorRangeMinCosted, hmacroSize]

/--
Every canonical shape of the witness size has the same exact operational
count.  The proof composes three successful count-one two-span calls; it does
not reduce the shape's payload or infer equality from the public upper bound.
-/
theorem canonicalRelativeRmmInteriorCost33_cost_eq_of_size_eq
    (shape : Cartesian.CartesianShape) (hsize : shape.size = 3469) :
    (canonicalRelativeRmmInteriorRangeMinCosted shape 143 146).cost = 33 := by
  have hgeometry := canonicalRelativeRmmInteriorCost33Layout_of_size_eq shape hsize
  rcases hgeometry with ⟨_, _, hblockCount, hmacroSize, hmacroCount⟩
  have hcrossing :
      (RelativeRmm.canonicalLayout shape).macroSize <
        (RelativeRmm.canonicalLayout shape).blockCount := by omega
  have hleft :=
    canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted_cost_eq_eleven_of_one
      shape hcrossing 0 143 (by omega) (by omega)
  have hmiddle :=
    canonicalRelativeRmmMachineGlobalTwoSpanCandidateCosted_cost_eq_eleven_of_one
      shape hcrossing 1 (by omega)
  have hright :=
    canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted_cost_eq_eleven_of_one
      shape hcrossing 2 0 (by omega) (by omega)
  rw [canonicalRelativeRmmInteriorCost33_dispatch_of_size_eq shape hsize]
  unfold canonicalRelativeRmmMachineCrossMacroCandidateCosted
  simp only [Costed.cost_bind, Costed.map_cost]
  simp [hmacroSize, hleft, hmiddle, hright]

/--
The canonical accepted interior object itself reaches the advertised cap.
This is equality on the live evaluator, not an upper-bound proof.
-/
theorem canonicalRelativeRmmInteriorCost33Witness_exact :
    (canonicalRelativeRmmInteriorRangeMinCosted
      canonicalRelativeRmmInteriorCost33WitnessShape 143 146).cost = 33 := by
  exact canonicalRelativeRmmInteriorCost33_cost_eq_of_size_eq
    canonicalRelativeRmmInteriorCost33WitnessShape
    canonicalRelativeRmmInteriorCost33WitnessShape_size

/-- The retired `cost <= 30` claim fails on that identical canonical object. -/
theorem canonicalRelativeRmmInteriorCost33Witness_not_cost_le_thirty :
    Not ((canonicalRelativeRmmInteriorRangeMinCosted
      canonicalRelativeRmmInteriorCost33WitnessShape 143 146).cost <= 30) := by
  rw [canonicalRelativeRmmInteriorCost33Witness_exact]
  omega

/-- The same exact count holds on the canonical concatenated component store. -/
theorem canonicalRelativeRmmInteriorCost33Witness_store_exact :
    (canonicalRelativeRmmInteriorRangeMinCostedWithStore
      canonicalRelativeRmmInteriorCost33WitnessShape
      (canonicalRelativeRmmInteriorComponentStore
        canonicalRelativeRmmInteriorCost33WitnessShape).store.words
      143 146).cost = 33 := by
  rw [canonicalRelativeRmmInteriorRangeMinCostedWithStore_eq_current]
  exact canonicalRelativeRmmInteriorCost33Witness_exact

/-- Its recorded physical footprint contains exactly the same 33 reads. -/
theorem canonicalRelativeRmmInteriorCost33Witness_footprint_length :
    (canonicalRelativeRmmInteriorRangeFootprintWithStore
      canonicalRelativeRmmInteriorCost33WitnessShape
      (canonicalRelativeRmmInteriorComponentStore
        canonicalRelativeRmmInteriorCost33WitnessShape).store.words
      143 146).length = 33 := by
  rw [<- canonicalRelativeRmmInteriorRange_cost_eq_footprint_length]
  exact canonicalRelativeRmmInteriorCost33Witness_store_exact

/--
The accepted U2 interior execution costs at most thirty-three charged
primitive events on every positive bounded range.  The only use of
`4 <= shape.size` is the all-size width fact in the within-macro branch;
public dispatch remains uniform and contains no activation threshold.

THE VALUE IS ATTAINED, not slack.  The maximizing cross-macro branch performs
three two-span calls, each of which now reads the charged sparse-level table
once (`11 = 1 + 5 + 5`), so `3 * 11 = 33` and the final step is a bare `exact`
against the branch bound with no `Nat.le_trans` widening.  The three units
over the pre-swap `30` are exactly the three charged level reads.
-/
theorem canonicalRelativeRmmInteriorRangeMinCosted_cost_le_thirty_three_literal_of_size_ge_four_of_bounded
    (shape : Cartesian.CartesianShape) (hsize : 4 <= shape.size)
    (startBlock count : Nat)
    (hbound : startBlock + count <=
      (RelativeRmm.canonicalLayout shape).blockCount) :
    (canonicalRelativeRmmInteriorRangeMinCosted shape startBlock count).cost <=
      33 := by
  let layout := RelativeRmm.canonicalLayout shape
  unfold canonicalRelativeRmmInteriorRangeMinCosted
  by_cases hcount : count = 0
  · simp [hcount, Costed.pure]
  · simp only [hcount, if_false]
    by_cases hwithin : count <=
        (RelativeRmm.canonicalLayout shape).macroSize -
          startBlock % (RelativeRmm.canonicalLayout shape).macroSize
    · simp only [hwithin, if_true]
      exact Nat.le_trans
        (canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted_cost_le_twenty_six_of_size_ge_four
          shape hsize _ _ count)
        (by simp)
    · have hvalid := RelativeRmm.canonicalLayout_valid shape
      have hwithin' :
          ¬ count <= layout.macroSize - startBlock % layout.macroSize := by
        simpa [layout] using hwithin
      have hmodLt : startBlock % layout.macroSize < layout.macroSize :=
        Nat.mod_lt startBlock hvalid.macroSize_pos
      have hmodLe : startBlock % layout.macroSize <= startBlock :=
        Nat.mod_le startBlock layout.macroSize
      have hcross : layout.macroSize < startBlock + count := by
        omega
      have hmacro : layout.macroSize < layout.blockCount :=
        Nat.lt_of_lt_of_le hcross (by simpa [layout] using hbound)
      simp only [hwithin, if_false]
      by_cases hmiddle :
          (count -
              ((RelativeRmm.canonicalLayout shape).macroSize -
                startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) /
              (RelativeRmm.canonicalLayout shape).macroSize = 0
      · simp only [hmiddle, if_true]
        exact Nat.le_trans
          (canonicalRelativeRmmMachineAdjacentMacroCandidateCosted_cost_le_twenty_two_of_macro_crossing
            shape (by simpa [layout] using hmacro) _ _ _)
          (by simp)
      · simp only [hmiddle, if_false]
        by_cases hright :
            (count -
                ((RelativeRmm.canonicalLayout shape).macroSize -
                  startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) %
                (RelativeRmm.canonicalLayout shape).macroSize = 0
        · simp only [hright, if_true]
          exact Nat.le_trans
            (canonicalRelativeRmmMachineLeftMiddleMacroCandidateCosted_cost_le_twenty_two_of_macro_crossing
              shape (by simpa [layout] using hmacro) _ _ _)
            (by simp)
        · simp only [hright, if_false]
          exact canonicalRelativeRmmMachineCrossMacroCandidateCosted_cost_le_thirty_three_of_macro_crossing
            shape (by simpa [layout] using hmacro) _ _ _ _

/--
The accepted U2 interior execution respects the declared all-size interior
cap.  Stated against the cap FIELD rather than against a literal, so every
consumer of the cap keeps working across a recharge; the tight literal
content lives in the `_literal` theorem above.

At this commit the step is `33 <= 33` and therefore TIGHT.  The announced-slack
theorem that recorded the staging compromise has been deleted: its `30 < cap`
conjunct is unprovable now that the charged sparse-level reads are reachable.
-/
theorem canonicalRelativeRmmInteriorRangeMinCosted_cost_le_thirty_of_size_ge_four_of_bounded
    (shape : Cartesian.CartesianShape) (hsize : 4 <= shape.size)
    (startBlock count : Nat)
    (hbound : startBlock + count <=
      (RelativeRmm.canonicalLayout shape).blockCount) :
    (canonicalRelativeRmmInteriorRangeMinCosted shape startBlock count).cost <=
      canonicalRelativeRmmPrincipledInteriorChargedTraceCost :=
  Nat.le_trans
    (canonicalRelativeRmmInteriorRangeMinCosted_cost_le_thirty_three_literal_of_size_ge_four_of_bounded
      shape hsize startBlock count hbound)
    (by simp [canonicalRelativeRmmPrincipledInteriorChargedTraceCost])

/-
RETIRED AT THE CHARGED SPARSE-LEVEL SWAP.

`canonicalRelativeRmmPrincipledInteriorChargedTraceCost_announced_slack_of_size_ge_four_of_bounded`
stood here.  It announced that the declared cap STRICTLY exceeded what the
route needed (`route <= 30` and `30 < cap = 33`), which was the checked
statement of commit A's staging compromise.

It is DELETED rather than weakened, exactly as its own docstring required.
The swap made its first conjunct false: the maximizing cross-macro branch now
performs three charged sparse-level reads and attains `33`, so `route <= 30`
is no longer provable.  The cap is tight again, and
`canonicalRelativeRmmInteriorRangeMinCosted_cost_le_thirty_three_literal_of_size_ge_four_of_bounded`
carries the tight content.
-/

theorem canonicalRelativeRmmInteriorRangeMinCosted_erase_exact
    {shape : Cartesian.CartesianShape} {startBlock count : Nat}
    (hcount : 0 < count)
    (hbound : startBlock + count <=
      (RelativeRmm.canonicalLayout shape).blockCount) :
    (canonicalRelativeRmmInteriorRangeMinCosted shape startBlock count).erase =
      some
        (bpRangeMinExcess shape
          (RelativeRmm.canonicalLayout shape).blockSize startBlock count,
          bpRangeArgMinPrefixPos shape
            (RelativeRmm.canonicalLayout shape).blockSize startBlock count) := by
  let layout := RelativeRmm.canonicalLayout shape
  have hvalid := RelativeRmm.canonicalLayout_valid shape
  have hmacroCover :
      layout.blockCount <= layout.macroSampleCount * layout.macroSize := by
    have hlt := Nat.lt_div_mul_add hvalid.macroSize_pos
      (a := layout.blockCount)
    have hlt' : layout.blockCount <
        (layout.blockCount / layout.macroSize + 1) * layout.macroSize := by
      simpa [Nat.add_mul, Nat.mul_add, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using hlt
    exact Nat.le_of_lt
      (by simpa [RelativeRmm.Layout.macroSampleCount] using hlt')
  have hsuperIndex : forall {block : Nat}, block < layout.blockCount ->
      block / layout.blocksPerSuper < layout.superSampleCount := by
    intro block hblock
    exact PayloadLiveBPRelativeMinMaxArgSummaryTable.div_lt_succ_div_of_lt
      (blockCount := layout.blockCount) hblock
  have hexact := bpTwoLevelInteriorCandidateCosted_erase_exact
    (canonicalRelativeRmmInteriorLocalTable shape)
    (canonicalRelativeRmmInteriorGlobalTable shape)
    (canonicalRelativeRmmSummaryTable shape)
    hvalid.macroSize_pos hcount (by simpa [layout] using hbound)
    (by
      intro block hblock
      exact PayloadLiveBPRelativeMinMaxArgSummaryTable.div_lt_succ_div_of_lt
        (blockCount := layout.blockCount) hblock)
    hmacroCover
    (by
      intro localCount hlocalPos hlocalLe
      have hcap : localCount < 2 ^ layout.levelCount :=
        Nat.lt_of_le_of_lt hlocalLe
          (SuccinctRank.self_lt_two_pow_machineWordBits layout.macroSize)
      have hsucc := natLog2_succ_le_of_pos_lt_pow hlocalPos hcap
      simpa [RelativeRmm.Layout.levelCount,
        RelativeRmm.Layout.offsetWidth] using hsucc)
    (by
      intro macroSpanCount hspanPos hspanLe
      have hcap : macroSpanCount < 2 ^ layout.globalLevelCount :=
        Nat.lt_of_le_of_lt hspanLe
          (SuccinctRank.self_lt_two_pow_machineWordBits
            layout.macroSampleCount)
      have hsucc := natLog2_succ_le_of_pos_lt_pow hspanPos hcap
      simpa [RelativeRmm.Layout.globalLevelCount] using hsucc)
    hvalid.blocksPerSuper_pos hvalid.fullBlocks_fit hsuperIndex
  rw [canonicalRelativeRmmInteriorRangeMinCosted_refines_logical shape startBlock count hbound]
  simpa [layout] using hexact

theorem canonicalRelativeRmmInteriorWordsRead_length_le_machine
    {shape : Cartesian.CartesianShape} {startBlock count : Nat}
    {word : List Bool}
    (hmem : List.Mem word
      (canonicalRelativeRmmInteriorWordsRead shape startBlock count)) :
    word.length <= SuccinctRank.machineWordBits shape.bpCode.length := by
  unfold canonicalRelativeRmmInteriorWordsRead at hmem
  cases List.mem_flatMap.mp hmem with
  | intro logicalWord hrest =>
      exact SuccinctSpace.chunkPayloadWords_word_length_le
        (SuccinctRank.machineWordBits shape.bpCode.length) hrest.2


theorem canonicalRelativeRmmInteriorRangeMinCostedWithStore_cost_le
    (shape : Cartesian.CartesianShape) (startBlock count : Nat) :
    (canonicalRelativeRmmInteriorRangeMinCostedWithStore shape
      (canonicalRelativeRmmInteriorComponentStore shape).store.words
      startBlock count).cost <= canonicalRelativeRmmInteriorQueryCost := by
  rw [canonicalRelativeRmmInteriorRangeMinCostedWithStore_eq_current]
  exact canonicalRelativeRmmInteriorRangeMinCosted_cost_le
    shape startBlock count

theorem canonicalRelativeRmmInteriorRangeMinCostedWithStore_cost_le_thirty_of_size_ge_four_of_bounded
    (shape : Cartesian.CartesianShape) (hsize : 4 <= shape.size)
    (startBlock count : Nat)
    (hbound : startBlock + count <=
      (RelativeRmm.canonicalLayout shape).blockCount) :
    (canonicalRelativeRmmInteriorRangeMinCostedWithStore shape
      (canonicalRelativeRmmInteriorComponentStore shape).store.words
      startBlock count).cost <=
        canonicalRelativeRmmPrincipledInteriorChargedTraceCost := by
  rw [canonicalRelativeRmmInteriorRangeMinCostedWithStore_eq_current]
  exact
    canonicalRelativeRmmInteriorRangeMinCosted_cost_le_thirty_of_size_ge_four_of_bounded
      shape hsize startBlock count hbound

theorem canonicalRelativeRmmInteriorRangeMinCostedWithStore_erase_exact
    {shape : Cartesian.CartesianShape} {startBlock count : Nat}
    (hcount : 0 < count)
    (hbound : startBlock + count <=
      (RelativeRmm.canonicalLayout shape).blockCount) :
    (canonicalRelativeRmmInteriorRangeMinCostedWithStore shape
      (canonicalRelativeRmmInteriorComponentStore shape).store.words
      startBlock count).erase =
      some
        (bpRangeMinExcess shape
          (RelativeRmm.canonicalLayout shape).blockSize startBlock count,
          bpRangeArgMinPrefixPos shape
            (RelativeRmm.canonicalLayout shape).blockSize startBlock count) := by
  rw [canonicalRelativeRmmInteriorRangeMinCostedWithStore_eq_current]
  exact canonicalRelativeRmmInteriorRangeMinCosted_erase_exact hcount hbound

/-- The exact-cost store-backed witness returns the accepted leftmost candidate. -/
theorem canonicalRelativeRmmInteriorCost33Witness_store_erase_exact :
    (canonicalRelativeRmmInteriorRangeMinCostedWithStore
      canonicalRelativeRmmInteriorCost33WitnessShape
      (canonicalRelativeRmmInteriorComponentStore
        canonicalRelativeRmmInteriorCost33WitnessShape).store.words
      143 146).erase =
      some
        (bpRangeMinExcess canonicalRelativeRmmInteriorCost33WitnessShape
          (RelativeRmm.canonicalLayout
            canonicalRelativeRmmInteriorCost33WitnessShape).blockSize 143 146,
          bpRangeArgMinPrefixPos canonicalRelativeRmmInteriorCost33WitnessShape
            (RelativeRmm.canonicalLayout
              canonicalRelativeRmmInteriorCost33WitnessShape).blockSize
            143 146) := by
  apply canonicalRelativeRmmInteriorRangeMinCostedWithStore_erase_exact
  · omega
  · have hgeometry := canonicalRelativeRmmInteriorCost33Layout_of_size_eq
      canonicalRelativeRmmInteriorCost33WitnessShape
      canonicalRelativeRmmInteriorCost33WitnessShape_size
    omega

/-! ### Sparse-level returned-value dependency witness (B7) -/

/--
`INV-VALUE-DEPENDENCY`, on one identical object and query.  The canonical and
dropped executions both issue the charged local-level read at the same
physical address.  The canonical store returns the accepted range-minimum
candidate, while changing only that read word to `none` changes the returned
interior value to `none`; this is value dependence, not merely trace
dependence.
-/
theorem canonicalRelativeRmmInteriorCost33LocalLevelDrop_changes_returned_candidate :
    let shape := canonicalRelativeRmmInteriorCost33WitnessShape
    let canonicalStore : FlatWordStore :=
      FlatWordStore.ofArray
        (canonicalRelativeRmmInteriorComponentStore shape).store.words
    let address :=
      (canonicalRelativeRmmInteriorComponentOffsets shape).localLevel + 1
    let droppedStore : FlatWordStore := fun queriedAddress =>
      if queriedAddress = address then none else canonicalStore queriedAddress
    let canonicalRun :=
      canonicalRelativeRmmInteriorRangeMinExecutionWithRead
        shape canonicalStore 0 1
    let droppedRun :=
      canonicalRelativeRmmInteriorRangeMinExecutionWithRead
        shape droppedStore 0 1
    (address, canonicalStore address) ∈ canonicalRun.reads ∧
      (address, none) ∈ droppedRun.reads ∧
      canonicalRun.value =
        some
          (bpRangeMinExcess shape
            (RelativeRmm.canonicalLayout shape).blockSize 0 1,
            bpRangeArgMinPrefixPos shape
              (RelativeRmm.canonicalLayout shape).blockSize 0 1) ∧
      droppedRun.value = none ∧
      canonicalRun.value ≠ droppedRun.value := by
  let shape := canonicalRelativeRmmInteriorCost33WitnessShape
  let canonicalStore : FlatWordStore :=
    FlatWordStore.ofArray
      (canonicalRelativeRmmInteriorComponentStore shape).store.words
  let address :=
    (canonicalRelativeRmmInteriorComponentOffsets shape).localLevel + 1
  let droppedStore : FlatWordStore := fun queriedAddress =>
    if queriedAddress = address then none else canonicalStore queriedAddress
  let canonicalRun :=
    canonicalRelativeRmmInteriorRangeMinExecutionWithRead
      shape canonicalStore 0 1
  let droppedRun :=
    canonicalRelativeRmmInteriorRangeMinExecutionWithRead
      shape droppedStore 0 1
  have hgeometry := canonicalRelativeRmmInteriorCost33Layout_of_size_eq
    shape canonicalRelativeRmmInteriorCost33WitnessShape_size
  have hmacro : (RelativeRmm.canonicalLayout shape).macroSize = 144 :=
    hgeometry.2.2.2.1
  have hblockCount : (RelativeRmm.canonicalLayout shape).blockCount = 289 :=
    hgeometry.2.2.1
  have hbpLength : shape.bpCode.length = 6938 := by
    rw [Cartesian.CartesianShape.bpCode_length]
    have hsize : shape.size = 3469 := by
      simpa [shape] using
        canonicalRelativeRmmInteriorCost33WitnessShape_size
    omega
  have hwordSize : SuccinctRank.machineWordBits shape.bpCode.length = 13 := by
    rw [SuccinctRank.machineWordBits, hbpLength]
    have hlower : 12 <= Nat.log2 6938 :=
      (Nat.le_log2 (by decide : Not ((6938 : Nat) = 0))).2 (by decide)
    have hupper : Nat.log2 6938 < 13 :=
      (Nat.log2_lt (by decide : Not ((6938 : Nat) = 0))).2 (by decide)
    omega
  have hwidth :
      bpSparseLevelWidth
          (bpSparseLevelDomain
            (RelativeRmm.canonicalLayout shape).macroSize) = 11 := by
    rw [hmacro]
    unfold bpSparseLevelDomain bpSparseLevelWidth
    have h146Lower : 7 <= Nat.log2 146 :=
      (Nat.le_log2 (by decide : Not ((146 : Nat) = 0))).2 (by decide)
    have h146Upper : Nat.log2 146 < 8 :=
      (Nat.log2_lt (by decide : Not ((146 : Nat) = 0))).2 (by decide)
    have h146 : Nat.log2 146 = 7 := by omega
    rw [h146]
    have hprod : 146 * (7 + 1) = 1168 := by decide
    rw [hprod]
    have h1168Lower : 10 <= Nat.log2 1168 :=
      (Nat.le_log2 (by decide : Not ((1168 : Nat) = 0))).2 (by decide)
    have h1168Upper : Nat.log2 1168 < 11 :=
      (Nat.log2_lt (by decide : Not ((1168 : Nat) = 0))).2 (by decide)
    omega
  have hchunk :
      fixedWidthNatTableMachineChunkCount
          (bpSparseLevelWidth
            (bpSparseLevelDomain
              (RelativeRmm.canonicalLayout shape).macroSize))
          (SuccinctRank.machineWordBits shape.bpCode.length) = 1 := by
    rw [hwidth, hwordSize]
    decide
  have hchunkConcrete :
      fixedWidthNatTableMachineChunkCount
          (bpSparseLevelWidth (bpSparseLevelDomain 144))
          (SuccinctRank.machineWordBits
            canonicalRelativeRmmInteriorCost33WitnessShape.bpCode.length) = 1 := by
    simpa [shape, hmacro] using hchunk
  have hchunk146 :
      fixedWidthNatTableMachineChunkCount
          (bpSparseLevelWidth 146)
          (SuccinctRank.machineWordBits
            canonicalRelativeRmmInteriorCost33WitnessShape.bpCode.length) = 1 := by
    simpa [bpSparseLevelDomain] using hchunkConcrete
  have hlevelAddresses :
      (if 1 <
          bpSparseLevelDomain
            (RelativeRmm.canonicalLayout shape).macroSize then
        fixedWidthNatTableMachineFootprintAt
          (canonicalRelativeRmmInteriorComponentOffsets shape).localLevel
          (bpSparseLevelWidth
            (bpSparseLevelDomain
              (RelativeRmm.canonicalLayout shape).macroSize))
          (SuccinctRank.machineWordBits shape.bpCode.length) 1
      else
        [(canonicalRelativeRmmInteriorComponentOffsets shape).deadAddress]) =
        [address] := by
    rw [hmacro]
    simp [bpSparseLevelDomain, hchunk146,
      fixedWidthNatTableMachineFootprintAt,
      fixedWidthNatTableMachineFootprint, consecutiveWordIndices,
      address, shape]
  have hfirstRead (store : FlatWordStore) :
      (address, store address) ∈
        ((canonicalRelativeRmmMachineReadNatComputation shape
          (canonicalRelativeRmmInteriorLocalLevelTable shape).table
          (canonicalRelativeRmmInteriorComponentOffsets shape).localLevel
          1).run store).reads := by
    unfold canonicalRelativeRmmMachineReadNatComputation
    simp only [FixedWidthNatTable.machineReadComputationAt,
      FlatStoreComputation.map_run_reads,
      FlatStoreComputation.readMany_run_reads,
      bpSparseLevelEntries_length]
    rw [hlevelAddresses]
    simp
  have htwoRead (store : FlatWordStore) :
      (address, store address) ∈
        ((canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation
          shape 0 0 1).run store).reads := by
    unfold canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation
    simp only [FlatStoreComputation.bind_run,
      FlatStoreExecution.append]
    apply List.mem_append_left
    simpa using hfirstRead store
  have hread (store : FlatWordStore) :
      (address, store address) ∈
        (canonicalRelativeRmmInteriorRangeMinExecutionWithRead
          shape store 0 1).reads := by
    simpa [canonicalRelativeRmmInteriorRangeMinExecutionWithRead,
      canonicalRelativeRmmInteriorRangeMinComputation, hmacro] using
      htwoRead store
  have hcanonicalValue :
      canonicalRun.value =
        some
          (bpRangeMinExcess shape
            (RelativeRmm.canonicalLayout shape).blockSize 0 1,
            bpRangeArgMinPrefixPos shape
              (RelativeRmm.canonicalLayout shape).blockSize 0 1) := by
    have hexact :=
      canonicalRelativeRmmInteriorRangeMinCostedWithStore_erase_exact
        (shape := shape) (startBlock := 0) (count := 1)
        (by omega) (by omega)
    simpa [canonicalRun, canonicalStore,
      canonicalRelativeRmmInteriorRangeMinCostedWithStore,
      canonicalRelativeRmmInteriorRangeMinCostedWithRead,
      canonicalRelativeRmmInteriorRangeMinExecutionWithStore] using hexact
  have hdroppedAddress : droppedStore address = none := by
    simp [droppedStore]
  have hfirstDropped :
      ((canonicalRelativeRmmMachineReadNatComputation shape
        (canonicalRelativeRmmInteriorLocalLevelTable shape).table
        (canonicalRelativeRmmInteriorComponentOffsets shape).localLevel
        1).run droppedStore).value = none := by
    unfold canonicalRelativeRmmMachineReadNatComputation
    simp only [FixedWidthNatTable.machineReadComputationAt,
      FlatStoreComputation.map_run_value,
      FlatStoreComputation.readMany_run_value,
      bpSparseLevelEntries_length]
    rw [hlevelAddresses]
    simp [fixedWidthNatTableMachineDecode, collectPayloadWords,
      hdroppedAddress]
  have htwoDropped :
      ((canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation
        shape 0 0 1).run droppedStore).value = none := by
    unfold canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation
    simp [FlatStoreComputation.bind, FlatStoreExecution.append,
      hfirstDropped]
  have hdroppedValue : droppedRun.value = none := by
    simpa [droppedRun,
      canonicalRelativeRmmInteriorRangeMinExecutionWithRead,
      canonicalRelativeRmmInteriorRangeMinComputation, hmacro] using
      htwoDropped
  refine ⟨?_, ?_, hcanonicalValue, hdroppedValue, ?_⟩
  · simpa [canonicalRun] using hread canonicalStore
  · simpa [droppedRun, hdroppedAddress] using hread droppedStore
  · rw [hcanonicalValue, hdroppedValue]
    simp

theorem canonicalRelativeRmmInteriorRangePhysicalWordsRead_length_le_machine
    {shape : Cartesian.CartesianShape} {startBlock count : Nat}
    {word : List Bool}
    (hmem :
      List.Mem word
        (canonicalRelativeRmmInteriorRangePhysicalWordsReadWithStore shape
          (canonicalRelativeRmmInteriorComponentStore shape).store.words
          startBlock count)) :
    word.length <= SuccinctRank.machineWordBits shape.bpCode.length := by
  unfold canonicalRelativeRmmInteriorRangePhysicalWordsReadWithStore at hmem
  cases List.mem_filterMap.mp hmem with
  | intro read hrest =>
      cases hrest with
      | intro hread hvalue =>
          cases read with
          | mk address wordOption =>
              cases wordOption with
              | none =>
                  simp at hvalue
              | some stored =>
                  simp at hvalue
                  subst stored
                  exact
                    canonicalRelativeRmmInteriorRange_returned_word_bounded
                      shape startBlock count address word hread
def canonicalRelativeRmmInteriorDirectory
    (shape : Cartesian.CartesianShape) :
    PayloadLiveBPRelativeRmmInteriorDirectory shape
      (RelativeRmm.canonicalLayout shape).blockSize
      (RelativeRmm.canonicalLayout shape).blockCount
      (canonicalRelativeRmmInteriorDirectoryPayloadLength shape)
      canonicalRelativeRmmInteriorQueryCost where
  payload :=
    (canonicalRelativeRmmSummaryTable shape).payload ++
      (canonicalRelativeRmmInteriorLocalTable shape).payload ++
        (canonicalRelativeRmmInteriorGlobalTable shape).payload ++
          (canonicalRelativeRmmInteriorLocalLevelTable shape).payload ++
            (canonicalRelativeRmmInteriorGlobalLevelTable shape).payload
  payload_length_eq := by
    simp [canonicalRelativeRmmInteriorDirectoryPayloadLength,
      Nat.add_assoc]
  payloadWordsRead := fun startBlock count =>
    canonicalRelativeRmmInteriorRangePhysicalWordsReadWithStore shape
      (canonicalRelativeRmmInteriorComponentStore shape).store.words
      startBlock count
  rangeMinCosted := fun startBlock count =>
    canonicalRelativeRmmInteriorRangeMinCostedWithStore shape
      (canonicalRelativeRmmInteriorComponentStore shape).store.words
      startBlock count
  rangeMin_cost_le :=
    canonicalRelativeRmmInteriorRangeMinCostedWithStore_cost_le shape
  rangeMin_exact := by
    intro startBlock count hcount hbound
    exact canonicalRelativeRmmInteriorRangeMinCostedWithStore_erase_exact
      hcount hbound
  read_words_length_le_machine := by
    intro startBlock count word hmem
    exact
      canonicalRelativeRmmInteriorRangePhysicalWordsRead_length_le_machine hmem

theorem canonicalRelativeRmmInteriorDirectory_rangeMinCosted_erase_exact
    {shape : Cartesian.CartesianShape} {startBlock count : Nat}
    (hcount : 0 < count)
    (hbound : startBlock + count <=
      (RelativeRmm.canonicalLayout shape).blockCount) :
    ((canonicalRelativeRmmInteriorDirectory shape).rangeMinCosted
        startBlock count).erase =
      some
        (bpRangeMinExcess shape
          (RelativeRmm.canonicalLayout shape).blockSize startBlock count,
          bpRangeArgMinPrefixPos shape
            (RelativeRmm.canonicalLayout shape).blockSize
            startBlock count) := by
  exact (canonicalRelativeRmmInteriorDirectory shape).rangeMin_exact
    hcount hbound

private theorem nat_succ_square_le_four_mul_two_pow_all_size (q : Nat) :
    (q + 1) * (q + 1) <= 4 * 2 ^ q := by
  by_cases hlarge : 6 <= q
  case pos =>
    have hsq := nat_succ_square_le_two_pow_of_six_le q hlarge
    exact Nat.le_trans hsq (by
      have hpos : 0 < 2 ^ q := Nat.pow_pos (by omega : 0 < 2)
      omega)
  case neg =>
    have hcases :
        q = 0 \/ q = 1 \/ q = 2 \/ q = 3 \/ q = 4 \/ q = 5 := by
      omega
    rcases hcases with hq | hq | hq | hq | hq | hq <;>
      subst q <;> decide

private theorem nat_log2_one_eq_zero : Nat.log2 1 = 0 := by
  have hpow : (1 : Nat) < 2 ^ (1 : Nat) := by simp
  have hlt : Nat.log2 1 < 1 :=
    (Nat.log2_lt (by omega : Not ((1 : Nat) = 0))).2 hpow
  omega

private theorem machineWordBits_le_self_of_pos
    {n : Nat} (hn : 0 < n) :
    SuccinctRank.machineWordBits n <= n := by
  unfold SuccinctRank.machineWordBits
  by_cases hone : n = 1
  case pos =>
    subst n
    simp [nat_log2_one_eq_zero]
  case neg =>
    have hn_ne : Not (n = 0) := by omega
    have hpow : n < 2 ^ n := by
      have hsucc := SuccinctSpace.nat_succ_le_two_pow n
      omega
    have hlog_lt : Nat.log2 n < n :=
      (Nat.log2_lt hn_ne).2 hpow
    omega

private theorem machineWordBits_sq_le_four_mul_self_of_pos
    {n : Nat} (hn : 0 < n) :
    SuccinctRank.machineWordBits n *
        SuccinctRank.machineWordBits n <= 4 * n := by
  let q := Nat.log2 n
  have hn_ne : Not (n = 0) := by omega
  have hpow : 2 ^ q <= n := by
    simpa [q] using Nat.log2_self_le hn_ne
  have hsq : (q + 1) * (q + 1) <= 4 * 2 ^ q :=
    nat_succ_square_le_four_mul_two_pow_all_size q
  exact Nat.le_trans
    (by
      simpa [q, SuccinctRank.machineWordBits] using hsq)
    (Nat.mul_le_mul_left 4 hpow)

private theorem nat_succ_cube_le_eight_mul_two_pow_all_size (q : Nat) :
    (q + 1) * ((q + 1) * (q + 1)) <= 8 * 2 ^ q := by
  by_cases hlarge : 11 <= q
  case pos =>
    exact Nat.le_trans
      (nat_succ_cube_le_two_pow_of_11_le q hlarge)
      (by omega)
  case neg =>
    have hcases :
        q = 0 \/ q = 1 \/ q = 2 \/ q = 3 \/ q = 4 \/ q = 5 \/
          q = 6 \/ q = 7 \/ q = 8 \/ q = 9 \/ q = 10 := by
      omega
    rcases hcases with hq | hq | hq | hq | hq | hq |
      hq | hq | hq | hq | hq <;> subst q <;> decide

private theorem machineWordBits_cube_le_eight_mul_self_of_pos
    {n : Nat} (hn : 0 < n) :
    SuccinctRank.machineWordBits n *
        (SuccinctRank.machineWordBits n *
          SuccinctRank.machineWordBits n) <= 8 * n := by
  let q := Nat.log2 n
  have hcube := nat_succ_cube_le_eight_mul_two_pow_all_size q
  have hpow : 2 ^ q <= n := by
    simpa [q] using Nat.log2_self_le (Nat.ne_of_gt hn)
  change (q + 1) * ((q + 1) * (q + 1)) <= 8 * n
  exact Nat.le_trans hcube (Nat.mul_le_mul_left 8 hpow)
private theorem one_lt_two_pow_of_pos_local {k : Nat} (hk : 0 < k) :
    1 < 2 ^ k := by
  cases k with
  | zero => omega
  | succ k =>
      have hpos : 0 < 2 ^ k := Nat.pow_pos (by omega : 0 < 2)
      simp [Nat.pow_succ]
      omega


private theorem machineWordBits_two_mul_le_two_mul (n : Nat) :
    SuccinctRank.machineWordBits (2 * n) <=
      2 * SuccinctRank.machineWordBits n := by
  by_cases hn : n = 0
  case pos =>
    subst n
    simp [SuccinctRank.machineWordBits]
  case neg =>
    let w := SuccinctRank.machineWordBits n
    have hwpos : 0 < w := by
      simpa [w] using SuccinctRank.machineWordBits_pos n
    have hnlt : n < 2 ^ w := by
      simpa [w] using SuccinctRank.self_lt_two_pow_machineWordBits n
    have htwo : 2 <= 2 ^ w := by
      have hone := one_lt_two_pow_of_pos_local hwpos
      omega
    have hscale : 2 * n < 2 * 2 ^ w :=
      Nat.mul_lt_mul_of_pos_left hnlt (by omega)
    have hright : 2 * 2 ^ w <= 2 ^ w * 2 ^ w :=
      Nat.mul_le_mul_right (2 ^ w) htwo
    have hpowEq : 2 ^ w * 2 ^ w = 2 ^ (2 * w) := by
      calc
        2 ^ w * 2 ^ w = 2 ^ (w + w) := (Nat.pow_add 2 w w).symm
        _ = 2 ^ (2 * w) := by congr 1 <;> omega
    have hlt : 2 * n < 2 ^ (2 * w) := by
      calc
        2 * n < 2 * 2 ^ w := hscale
        _ <= 2 ^ w * 2 ^ w := hright
        _ = 2 ^ (2 * w) := hpowEq
    have hbits : Nat.log2 (2 * n) + 1 <= 2 * w :=
      natLog2_succ_le_of_pos_lt_pow (by omega) hlt
    simpa [SuccinctRank.machineWordBits, w] using hbits

/-- Adding the sparse-level domain slack costs at most two doublings of the
word width (B7). Used to keep the charged level tables' contribution linear
in `machineWordBits n` rather than in the domain itself. -/
private theorem machineWordBits_add_two_le_four_mul_of_pos
    {x : Nat} (hx : 0 < x) :
    SuccinctRank.machineWordBits (x + 2) <=
      4 * SuccinctRank.machineWordBits x := by
  have hle : x + 2 <= 2 * (2 * x) := by omega
  calc
    SuccinctRank.machineWordBits (x + 2)
        <= SuccinctRank.machineWordBits (2 * (2 * x)) :=
      SuccinctRank.machineWordBits_mono_le hle
    _ <= 2 * SuccinctRank.machineWordBits (2 * x) :=
      machineWordBits_two_mul_le_two_mul (2 * x)
    _ <= 2 * (2 * SuccinctRank.machineWordBits x) :=
      Nat.mul_le_mul_left 2 (machineWordBits_two_mul_le_two_mul x)
    _ = 4 * SuccinctRank.machineWordBits x := by omega

/--
THE WIDTH BRIDGE (B7).  The tightened stored width never exceeds the
square-domain width this module's space accounting was originally written
against.  Every space bound below is therefore inherited rather than re-derived:
a narrower cell can only make the table smaller.
-/
private theorem bpSparseLevelWidth_le_square_width
    {domain : Nat} (hpos : 0 < domain) :
    bpSparseLevelWidth domain <= Nat.log2 (domain * domain) + 1 := by
  have hlog : Nat.log2 domain + 1 <= domain := by
    have h := machineWordBits_le_self_of_pos hpos
    simpa [SuccinctRank.machineWordBits] using h
  have hmul : domain * (Nat.log2 domain + 1) <= domain * domain :=
    Nat.mul_le_mul_left domain hlog
  have hmono := SuccinctRank.machineWordBits_mono_le hmul
  simpa [bpSparseLevelWidth, SuccinctRank.machineWordBits] using hmono

/-- The charged sparse-level width on a domain `x + 2` is linear in
`machineWordBits x` (B7). -/
private theorem sparseLevelWidth_add_two_le_of_pos
    {x : Nat} (hx : 0 < x) :
    bpSparseLevelWidth (x + 2) <=
      8 * SuccinctRank.machineWordBits x + 1 := by
  have hbridge : bpSparseLevelWidth (x + 2) <=
      Nat.log2 ((x + 2) * (x + 2)) + 1 :=
    bpSparseLevelWidth_le_square_width (by omega)
  have hmul :
      SuccinctRank.machineWordBits ((x + 2) * (x + 2)) <=
        2 * SuccinctRank.machineWordBits (x + 2) + 1 :=
    SuccinctRank.machineWordBits_mul_self_log_bound (x + 2)
  have hadd := machineWordBits_add_two_le_four_mul_of_pos hx
  have hgoal :
      SuccinctRank.machineWordBits ((x + 2) * (x + 2)) <=
        8 * SuccinctRank.machineWordBits x + 1 := by
    omega
  exact Nat.le_trans hbridge
    (by simpa [SuccinctRank.machineWordBits] using hgoal)

def canonicalRelativeRmmInteriorRawPayloadOverhead (n : Nat) : Nat :=
  let base := Nat.log2 n + 1
  let blockCount := n / base
  let relativeWidth := 2 * (Nat.log2 base + 1) + 3
  let superCount := blockCount / base + 1
  let superWidth := SuccinctRank.machineWordBits (2 * n)
  let macroSize := base * base
  let macroCount := blockCount / macroSize + 1
  let offsetWidth := SuccinctRank.machineWordBits macroSize
  let globalLevelCount := SuccinctRank.machineWordBits macroCount
  let blockAddressWidth := SuccinctRank.machineWordBits blockCount
  let localLevelDomain := macroSize + 2
  let globalLevelDomain := macroCount + 2
  (superCount * superWidth + 3 * (blockCount * relativeWidth)) +
    ((macroCount * (offsetWidth * macroSize)) * offsetWidth) +
      ((globalLevelCount * macroCount) * blockAddressWidth) +
        (localLevelDomain * bpSparseLevelWidth localLevelDomain) +
          (globalLevelDomain * bpSparseLevelWidth globalLevelDomain)

/--
The pre-B7 (legacy-shaped) part of the raw interior payload overhead: the
summary, local sparse and global sparse regions.  Split out so that the
`LittleOLinear` argument can dominate it by the legacy envelope while the
charged level tables are dominated separately (B7).
-/
def canonicalRelativeRmmInteriorLegacyPartOverhead (n : Nat) : Nat :=
  let base := Nat.log2 n + 1
  let blockCount := n / base
  let relativeWidth := 2 * (Nat.log2 base + 1) + 3
  let superCount := blockCount / base + 1
  let superWidth := SuccinctRank.machineWordBits (2 * n)
  let macroSize := base * base
  let macroCount := blockCount / macroSize + 1
  let offsetWidth := SuccinctRank.machineWordBits macroSize
  let globalLevelCount := SuccinctRank.machineWordBits macroCount
  let blockAddressWidth := SuccinctRank.machineWordBits blockCount
  (superCount * superWidth + 3 * (blockCount * relativeWidth)) +
    ((macroCount * (offsetWidth * macroSize)) * offsetWidth) +
      ((globalLevelCount * macroCount) * blockAddressWidth)

/--
The charged sparse-level table part of the raw interior payload overhead,
expressed as a closed form in `n` (B7).  This is the `shape`-free twin of
`canonicalRelativeRmmInteriorLevelTableOverhead`.
-/
def canonicalRelativeRmmInteriorLevelPartOverhead (n : Nat) : Nat :=
  let base := Nat.log2 n + 1
  let blockCount := n / base
  let macroSize := base * base
  let macroCount := blockCount / macroSize + 1
  let localLevelDomain := macroSize + 2
  let globalLevelDomain := macroCount + 2
  (localLevelDomain * bpSparseLevelWidth localLevelDomain) +
    (globalLevelDomain * bpSparseLevelWidth globalLevelDomain)

theorem canonicalRelativeRmmInteriorRawPayloadOverhead_eq_parts (n : Nat) :
    canonicalRelativeRmmInteriorRawPayloadOverhead n =
      canonicalRelativeRmmInteriorLegacyPartOverhead n +
        canonicalRelativeRmmInteriorLevelPartOverhead n := by
  simp [canonicalRelativeRmmInteriorRawPayloadOverhead,
    canonicalRelativeRmmInteriorLegacyPartOverhead,
    canonicalRelativeRmmInteriorLevelPartOverhead, Nat.add_assoc]

theorem canonicalRelativeRmmInteriorRawPayloadOverhead_le_linear (n : Nat) :
    canonicalRelativeRmmInteriorRawPayloadOverhead n <= 527 * (n + 1) := by
  by_cases hn : n = 0
  case pos =>
    subst n
    have hlog9 : Nat.log2 9 <= 3 := by
      have hlt : Nat.log2 9 < 4 :=
        (Nat.log2_lt (by omega : Not ((9 : Nat) = 0))).2 (by decide)
      omega
    have hw3 : bpSparseLevelWidth 3 <= 4 := by
      have hbridge : bpSparseLevelWidth 3 <= Nat.log2 (3 * 3) + 1 :=
        bpSparseLevelWidth_le_square_width (by omega)
      simp only [show (3 : Nat) * 3 = 9 from rfl] at hbridge
      omega
    simp [canonicalRelativeRmmInteriorRawPayloadOverhead,
      SuccinctRank.machineWordBits, nat_log2_one_eq_zero]
    omega
  case neg =>
    have hnpos : 0 < n := by omega
    let w := SuccinctRank.machineWordBits n
    let e := SuccinctRank.machineWordBits w
    let b := n / w
    let sw := SuccinctRank.machineWordBits (2 * n)
    let s := b / w + 1
    let r := 2 * e + 3
    let M := w * w
    let m := b / M + 1
    let o := SuccinctRank.machineWordBits M
    let g := SuccinctRank.machineWordBits m
    let a := SuccinctRank.machineWordBits b
    have hwpos : 0 < w := by
      simpa [w] using SuccinctRank.machineWordBits_pos n
    have hwle : w <= n := machineWordBits_le_self_of_pos hnpos
    have hele : e <= w := machineWordBits_le_self_of_pos hwpos
    have hwsq : w * w <= 4 * n :=
      machineWordBits_sq_le_four_mul_self_of_pos hnpos
    have hwcube : w * (w * w) <= 8 * n :=
      machineWordBits_cube_le_eight_mul_self_of_pos hnpos
    have hbw : b * w <= n := by
      simpa [b] using Nat.div_mul_le_self n w
    have hble : b <= n := by
      simpa [b] using Nat.div_le_self n w
    have hsw : sw <= 2 * w := by
      simpa [sw, w] using machineWordBits_two_mul_le_two_mul n
    have hr : r <= 5 * w := by
      simp only [r]
      omega
    have hsdiv : (b / w) * w <= b := Nat.div_mul_le_self b w
    have hsCore : (b / w) * w + w <= 2 * n := by omega
    have hsuper : s * sw <= 4 * n := by
      calc
        s * sw <= s * (2 * w) := Nat.mul_le_mul_left s hsw
        _ = 2 * ((b / w) * w + w) := by
          simp [s, Nat.mul_add, Nat.mul_left_comm, Nat.mul_comm]
        _ <= 2 * (2 * n) := Nat.mul_le_mul_left 2 hsCore
        _ = 4 * n := by omega
    have hrel : 3 * (b * r) <= 15 * n := by
      calc
        3 * (b * r) <= 3 * (b * (5 * w)) :=
          Nat.mul_le_mul_left 3 (Nat.mul_le_mul_left b hr)
        _ = 15 * (b * w) := by
          simp [Nat.mul_left_comm, Nat.mul_comm]
          omega
        _ <= 15 * n := Nat.mul_le_mul_left 15 hbw
    have hsummary : s * sw + 3 * (b * r) <= 19 * n := by
      omega
    have hoBound : o <= 2 * e + 1 := by
      simpa [o, M, e, w] using
        SuccinctRank.machineWordBits_mul_self_log_bound w
    have heSq : e * e <= 4 * w := by
      simpa [e] using machineWordBits_sq_le_four_mul_self_of_pos hwpos
    have hoSqRaw : o * o <= (2 * e + 1) * (2 * e + 1) :=
      Nat.mul_le_mul hoBound hoBound
    have htwoSq : (2 * e) * (2 * e) = 4 * (e * e) := by
      simp [Nat.mul_left_comm, Nat.mul_comm]
      omega
    have hExpand : (2 * e + 1) * (2 * e + 1) =
        4 * (e * e) + 4 * e + 1 := by
      calc
        (2 * e + 1) * (2 * e + 1) =
            (2 * e) * (2 * e) + (2 * e) + (2 * e) + 1 := by
          simp [Nat.add_mul, Nat.mul_add, Nat.add_assoc]
        _ = 4 * (e * e) + 4 * e + 1 := by rw [htwoSq]; omega
    have hoSq : o * o <= 21 * w := by
      calc
        o * o <= (2 * e + 1) * (2 * e + 1) := hoSqRaw
        _ = 4 * (e * e) + 4 * e + 1 := hExpand
        _ <= 21 * w := by omega
    have hmM : m * M <= b + M := by
      have hdiv := Nat.div_mul_le_self b M
      calc
        m * M = (b / M) * M + M := by simp [m, Nat.add_mul]
        _ <= b + M := Nat.add_le_add_right hdiv M
    have hMw : M * w <= 8 * n := by
      simpa [M, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hwcube
    have hsumw : (b + M) * w <= 9 * n := by
      calc
        (b + M) * w = b * w + M * w := Nat.add_mul b M w
        _ <= n + 8 * n := Nat.add_le_add hbw hMw
        _ = 9 * n := by omega
    have hlocal : (m * (o * M)) * o <= 189 * n := by
      calc
        (m * (o * M)) * o = (m * M) * (o * o) := by
          simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
        _ <= (m * M) * (21 * w) :=
          Nat.mul_le_mul_left (m * M) hoSq
        _ = 21 * ((m * M) * w) := by
          simp [Nat.mul_assoc, Nat.mul_comm]
        _ <= 21 * ((b + M) * w) :=
          Nat.mul_le_mul_left 21 (Nat.mul_le_mul_right w hmM)
        _ <= 21 * (9 * n) := Nat.mul_le_mul_left 21 hsumw
        _ = 189 * n := by omega
    have hmle : m <= n + 1 := by
      have hdiv : b / M <= b := Nat.div_le_self b M
      simp only [m]
      omega
    have hgle : g <= 2 * w := by
      have hm2n : m <= 2 * n := by omega
      exact Nat.le_trans
        (by
          simpa [g, sw] using
            SuccinctRank.machineWordBits_mono_le hm2n)
        hsw
    have hale : a <= w := by
      simpa [a, w] using SuccinctRank.machineWordBits_mono_le hble
    have hmM5 : m * M <= 5 * n := by omega
    have hglobal : (g * m) * a <= 10 * n := by
      calc
        (g * m) * a <= ((2 * w) * m) * w :=
          Nat.mul_le_mul (Nat.mul_le_mul_right m hgle) hale
        _ = 2 * (m * M) := by
          simp [M, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
        _ <= 2 * (5 * n) := Nat.mul_le_mul_left 2 hmM5
        _ = 10 * n := by omega
    -- B7: the two charged sparse-level tables.  The loose `m * M <= 5 * n`
    -- is enough for the GLOBAL level term, but NOT for the local one: it
    -- would only give `M <= 5 * n` and hence `~ n log n`.  The local term
    -- is closed with the tight cube bound `M * w = w ^ 3 <= 8 * n` instead.
    have hMpos : 0 < M := Nat.mul_pos hwpos hwpos
    have hmpos : 0 < m := Nat.succ_pos (b / M)
    have hlocalWidth : bpSparseLevelWidth (M + 2) <= 16 * w + 9 := by
      have hraw := sparseLevelWidth_add_two_le_of_pos (x := M) hMpos
      have ho : SuccinctRank.machineWordBits M <= 2 * e + 1 := hoBound
      have hew : e <= w := hele
      omega
    have hglobalWidth : bpSparseLevelWidth (m + 2) <= 16 * w + 1 := by
      have hraw := sparseLevelWidth_add_two_le_of_pos (x := m) hmpos
      have hg : SuccinctRank.machineWordBits m <= 2 * w := hgle
      omega
    have hmw : m * w <= 5 * n := by
      calc
        m * w <= m * (w * w) := Nat.mul_le_mul_left m (Nat.le_mul_of_pos_left w hwpos)
        _ = m * M := by simp [M]
        _ <= 5 * n := hmM5
    have hlocalLevel :
        (M + 2) * (bpSparseLevelWidth (M + 2)) <= 196 * n + 18 := by
      calc
        (M + 2) * (bpSparseLevelWidth (M + 2))
            <= (M + 2) * (16 * w + 9) :=
          Nat.mul_le_mul_left (M + 2) hlocalWidth
        _ = 16 * (M * w) + 9 * M + 32 * w + 18 := by
          simp [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm]
          omega
        _ <= 16 * (8 * n) + 9 * (4 * n) + 32 * n + 18 := by
          have h1 : M * w <= 8 * n := hMw
          have h2 : M <= 4 * n := by simpa [M] using hwsq
          have h3 : w <= n := hwle
          omega
        _ = 196 * n + 18 := by omega
    have hglobalLevel :
        (m + 2) * (bpSparseLevelWidth (m + 2)) <= 113 * n + 3 := by
      calc
        (m + 2) * (bpSparseLevelWidth (m + 2))
            <= (m + 2) * (16 * w + 1) :=
          Nat.mul_le_mul_left (m + 2) hglobalWidth
        _ = 16 * (m * w) + m + 32 * w + 2 := by
          simp [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm]
          omega
        _ <= 16 * (5 * n) + (n + 1) + 32 * n + 2 := by
          have h3 : w <= n := hwle
          omega
        _ = 113 * n + 3 := by omega
    change (s * sw + 3 * (b * r)) + (m * (o * M)) * o +
      (g * m) * a +
      ((M + 2) * (bpSparseLevelWidth (M + 2))) +
      ((m + 2) * (bpSparseLevelWidth (m + 2))) <= 527 * (n + 1)
    omega

theorem canonicalRelativeRmmInteriorDirectory_payload_length_eq_raw
    (shape : Cartesian.CartesianShape) :
    (canonicalRelativeRmmInteriorDirectory shape).payload.length =
      canonicalRelativeRmmInteriorRawPayloadOverhead shape.size := by
  rw [(canonicalRelativeRmmInteriorDirectory shape).payload_length_eq]
  unfold canonicalRelativeRmmInteriorDirectoryPayloadLength
  rw [(canonicalRelativeRmmSummaryTable shape).payload_length]
  rw [(canonicalRelativeRmmInteriorLocalTable shape).payload_length]
  rw [(canonicalRelativeRmmInteriorGlobalTable shape).payload_length]
  rw [canonicalRelativeRmmInteriorLocalLevelTable_payload_length]
  rw [canonicalRelativeRmmInteriorGlobalLevelTable_payload_length]
  simp [canonicalRelativeRmmInteriorRawPayloadOverhead,
    bpSparseLevelTableOverhead, bpSparseLevelDomain, bpSparseLevelWidth,
    RelativeRmm.canonicalLayout, RelativeRmm.Layout.superSampleCount,
    RelativeRmm.Layout.superWidth, RelativeRmm.Layout.macroSize,
    RelativeRmm.Layout.macroSampleCount, RelativeRmm.Layout.offsetWidth,
    RelativeRmm.Layout.levelCount, RelativeRmm.Layout.globalLevelCount,
    RelativeRmm.Layout.blockAddressWidth,
    canonicalBPRelativeSummaryBlockSizeRaw,
    canonicalBPRelativeSummaryBlocksPerSuperRaw,
    canonicalBPRelativeSummaryBlockCountRaw,
    canonicalBPRelativeSummaryRelativeWidthRaw,
    canonicalBPRelativeSummaryBase,
    Cartesian.CartesianShape.bpCode_length,
    Nat.add_assoc, Nat.mul_assoc]

def canonicalRelativeRmmInteriorOverhead (n : Nat) : Nat :=
  canonicalRelativeRmmInteriorRawPayloadOverhead n

theorem canonicalRelativeRmmInteriorDirectory_payload_length_eq_legacy_of_compactReady
    {shape : Cartesian.CartesianShape}
    (hready : (RelativeRmm.canonicalLayout shape).CompactReady shape) :
    (canonicalRelativeRmmInteriorDirectory shape).payload.length =
      (concreteBPRelativeRmmInteriorDirectory shape).payload.length +
        canonicalRelativeRmmInteriorLevelTableOverhead shape := by
  let layout := RelativeRmm.canonicalLayout shape
  have hlegacyReady :=
    (RelativeRmm.canonicalLayout_compactReady_iff_legacyReady shape).mp hready
  have hsummary :
      (canonicalRelativeRmmSummaryTable shape).payload.length =
        (concreteBPRelativeMinMaxArgSummaryTable_canonical shape).payload.length := by
    calc
      (canonicalRelativeRmmSummaryTable shape).payload.length =
          layout.superSampleCount * layout.superWidth shape +
            3 * (layout.blockCount * layout.relativeWidth) := by
        simpa [layout] using
          (canonicalRelativeRmmSummaryTable shape).payload_length
      _ = canonicalBPRelativeSummarySuperCount shape *
            canonicalBPRelativeSummarySuperWidth shape +
          3 * (canonicalBPRelativeSummaryBlockCount shape *
            canonicalBPRelativeSummaryRelativeWidth shape) := by
        rw [RelativeRmm.legacy_superCount_eq_canonical_of_compactReady
          hready]
        rw [RelativeRmm.legacy_blockCount_eq_canonical_of_compactReady
          hready]
        rw [RelativeRmm.legacy_relativeWidth_eq_canonical_of_compactReady
          hready]
        rfl
      _ =
          (concreteBPRelativeMinMaxArgSummaryTable_canonical
            shape).payload.length := by
        exact
          (concreteBPRelativeMinMaxArgSummaryTable_canonical
            shape).payload_length.symm
  have hlocal :
      (canonicalRelativeRmmInteriorLocalTable shape).payload.length =
        (concreteBPRelativeRmmInteriorLocalTable shape).payload.length := by
    calc
      (canonicalRelativeRmmInteriorLocalTable shape).payload.length =
          (layout.macroSampleCount *
              (layout.levelCount * layout.macroSize)) *
            layout.offsetWidth := by
        simpa [layout] using
          (canonicalRelativeRmmInteriorLocalTable shape).payload_length
      _ = (concreteBPRelativeRmmInteriorMacroCount shape *
              (concreteBPRelativeRmmInteriorLevelCount shape *
                concreteBPRelativeRmmInteriorMacroSize shape)) *
            concreteBPRelativeRmmInteriorOffsetWidth shape := by
        rw [RelativeRmm.legacy_macroCount_eq_canonical_of_compactReady
          hready]
        rw [RelativeRmm.legacy_levelCount_eq_canonical_of_compactReady
          hready]
        rw [RelativeRmm.legacy_macroSize_eq_canonical_of_compactReady
          hready]
        rw [RelativeRmm.legacy_offsetWidth_eq_canonical_of_compactReady
          hready]
      _ = (concreteBPRelativeRmmInteriorLocalTable
            shape).payload.length := by
        exact (concreteBPRelativeRmmInteriorLocalTable
          shape).payload_length.symm
  have hglobal :
      (canonicalRelativeRmmInteriorGlobalTable shape).payload.length =
        (concreteBPRelativeRmmInteriorGlobalTable shape).payload.length := by
    calc
      (canonicalRelativeRmmInteriorGlobalTable shape).payload.length =
          (layout.globalLevelCount * layout.macroSampleCount) *
            layout.blockAddressWidth := by
        simpa [layout] using
          (canonicalRelativeRmmInteriorGlobalTable shape).payload_length
      _ = (concreteBPRelativeRmmInteriorGlobalLevelCount shape *
              concreteBPRelativeRmmInteriorMacroCount shape) *
            concreteBPRelativeRmmInteriorBlockWidth shape := by
        rw [RelativeRmm.legacy_globalLevelCount_eq_canonical_of_compactReady
          hready]
        rw [RelativeRmm.legacy_macroCount_eq_canonical_of_compactReady
          hready]
        rw [RelativeRmm.legacy_blockAddressWidth_eq_canonical_of_compactReady
          hready]
      _ = (concreteBPRelativeRmmInteriorGlobalTable
            shape).payload.length := by
        exact (concreteBPRelativeRmmInteriorGlobalTable
          shape).payload_length.symm
  rw [(canonicalRelativeRmmInteriorDirectory shape).payload_length_eq]
  rw [(concreteBPRelativeRmmInteriorDirectory shape).payload_length_eq]
  simp [canonicalRelativeRmmInteriorDirectoryPayloadLength,
    concreteBPRelativeRmmInteriorDirectoryPayloadLength, hlegacyReady,
    hsummary, hlocal, hglobal,
    canonicalRelativeRmmInteriorLevelTableOverhead,
    canonicalRelativeRmmInteriorLocalLevelTable_payload_length,
    canonicalRelativeRmmInteriorGlobalLevelTable_payload_length,
    Nat.add_assoc]


/-- The `shape`-indexed level-table overhead agrees with its closed form in
`n` (B7).  This is the bridge that lets the two space-accounting statements
(one in `shape`, one in `n`) be combined. -/
theorem canonicalRelativeRmmInteriorLevelTableOverhead_eq_levelPart
    (shape : Cartesian.CartesianShape) :
    canonicalRelativeRmmInteriorLevelTableOverhead shape =
      canonicalRelativeRmmInteriorLevelPartOverhead shape.size := by
  simp [canonicalRelativeRmmInteriorLevelTableOverhead,
    canonicalRelativeRmmInteriorLevelPartOverhead,
    bpSparseLevelTableOverhead, bpSparseLevelDomain, bpSparseLevelWidth,
    RelativeRmm.canonicalLayout, RelativeRmm.Layout.macroSize,
    RelativeRmm.Layout.macroSampleCount,
    canonicalBPRelativeSummaryBlockSizeRaw,
    canonicalBPRelativeSummaryBlocksPerSuperRaw,
    canonicalBPRelativeSummaryBlockCountRaw,
    canonicalBPRelativeSummaryBase,
    Nat.add_assoc]

/-- Cubic-in-`log` envelope for the charged level tables (B7).

The local table contributes `~ log^2 n * log log n` and the global table
`~ n / log^2 n`; both are dominated by
`81 * (log2 n + 1)^3 + 9 * (n / (log2 n + 1)) + 21` from `n >= 2` on. -/
private theorem levelPart_envelope_arith
    {base q x : Nat}
    (hbase2 : 2 <= base)
    (hmwb : SuccinctRank.machineWordBits (x + 1) <= base)
    (hchain : base * x <= q) :
    (base * base + 2) *
        (bpSparseLevelWidth (base * base + 2)) +
      (x + 1 + 2) *
        (bpSparseLevelWidth (x + 1 + 2)) <=
      81 * (base * (base * base)) + (9 * q + 21) := by
  have hbasepos : 0 < base := by omega
  have hsq4 : 4 <= base * base := by
    have := Nat.mul_le_mul hbase2 hbase2
    omega
  have hMpos : 0 < base * base := by omega
  -- local level table: width is linear in `base`, domain is `~ base^2`
  have hwidthL :
      bpSparseLevelWidth (base * base + 2) <= 25 * base := by
    have h1 := sparseLevelWidth_add_two_le_of_pos hMpos
    have h2 := SuccinctRank.machineWordBits_mul_self_log_bound base
    have h3 := machineWordBits_le_self_of_pos hbasepos
    omega
  have hdomL : base * base + 2 <= 2 * (base * base) := by omega
  have hlocal :
      (base * base + 2) *
          (bpSparseLevelWidth (base * base + 2)) <=
        50 * (base * (base * base)) := by
    have hmul := Nat.mul_le_mul hdomL hwidthL
    have hexp :
        2 * (base * base) * (25 * base) = 50 * (base * (base * base)) := by
      simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    exact Nat.le_trans hmul (Nat.le_of_eq hexp)
  -- global level table: width is linear in `base`, domain is `~ n / base^3`
  have hwidthG :
      bpSparseLevelWidth (x + 1 + 2) <= 9 * base := by
    have h1 := sparseLevelWidth_add_two_le_of_pos (show 0 < x + 1 by omega)
    omega
  have hglobal :
      (x + 1 + 2) * (bpSparseLevelWidth (x + 1 + 2)) <=
        9 * (base * x) + 27 * base := by
    have hmul := Nat.mul_le_mul_left (x + 1 + 2) hwidthG
    have hexp : (x + 1 + 2) * (9 * base) = 9 * (base * x) + 27 * base := by
      simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.add_mul,
        Nat.mul_add]
      omega
    omega
  have hbc : base <= base * (base * base) := by
    have h1 : 1 <= base * base := by omega
    have := Nat.mul_le_mul_left base h1
    omega
  omega

private theorem levelPartOverhead_le_envelope
    {n : Nat} (hn : 2 <= n) :
    canonicalRelativeRmmInteriorLevelPartOverhead n <=
      81 * ((Nat.log2 n + 1) * ((Nat.log2 n + 1) * (Nat.log2 n + 1))) +
        (9 * (n / (Nat.log2 n + 1)) + 21) := by
  have hbase2 : 2 <= Nat.log2 n + 1 := by
    have hne : Not (n = 0) := by omega
    have hpow : 2 ^ 1 <= n := by simpa using hn
    have hlog := (Nat.le_log2 hne).2 hpow
    omega
  have hchain :
      (Nat.log2 n + 1) *
          (n / (Nat.log2 n + 1) /
            ((Nat.log2 n + 1) * (Nat.log2 n + 1))) <=
        n / (Nat.log2 n + 1) := by
    have hrw :=
      Nat.div_div_eq_div_mul (n / (Nat.log2 n + 1)) (Nat.log2 n + 1)
        (Nat.log2 n + 1)
    have hstep :
        n / (Nat.log2 n + 1) / (Nat.log2 n + 1) / (Nat.log2 n + 1) *
            (Nat.log2 n + 1) <=
          n / (Nat.log2 n + 1) / (Nat.log2 n + 1) :=
      Nat.div_mul_le_self _ _
    have hstep2 :
        n / (Nat.log2 n + 1) / (Nat.log2 n + 1) <= n / (Nat.log2 n + 1) :=
      Nat.div_le_self _ _
    rw [← hrw, Nat.mul_comm (Nat.log2 n + 1)]
    exact Nat.le_trans hstep hstep2
  have hmn :
      n / (Nat.log2 n + 1) / ((Nat.log2 n + 1) * (Nat.log2 n + 1)) + 1 <= n := by
    have htwo :
        2 * (n / (Nat.log2 n + 1) /
            ((Nat.log2 n + 1) * (Nat.log2 n + 1))) <=
          (Nat.log2 n + 1) *
            (n / (Nat.log2 n + 1) /
              ((Nat.log2 n + 1) * (Nat.log2 n + 1))) :=
      Nat.mul_le_mul_right _ hbase2
    have hself : n / (Nat.log2 n + 1) <= n := Nat.div_le_self _ _
    omega
  have hmwb :
      SuccinctRank.machineWordBits
          (n / (Nat.log2 n + 1) /
            ((Nat.log2 n + 1) * (Nat.log2 n + 1)) + 1) <=
        Nat.log2 n + 1 := by
    have h2 := SuccinctRank.machineWordBits_mono_le hmn
    have h3 : SuccinctRank.machineWordBits n = Nat.log2 n + 1 := by
      simp [SuccinctRank.machineWordBits]
    omega
  simp only [canonicalRelativeRmmInteriorLevelPartOverhead]
  exact levelPart_envelope_arith hbase2 hmwb hchain

private theorem littleOLinear_log2_succ_cube :
    LittleOLinear
      (fun n => (Nat.log2 n + 1) * ((Nat.log2 n + 1) * (Nat.log2 n + 1))) := by
  intro scale _hscale
  rcases SuccinctSpace.eventually_scale_log2_succ_cube_le_self scale with
    ⟨threshold, hthreshold⟩
  exact ⟨threshold, hthreshold⟩

theorem canonicalRelativeRmmInteriorLevelPartOverhead_littleO :
    LittleOLinear canonicalRelativeRmmInteriorLevelPartOverhead := by
  apply LittleOLinear.of_eventually_le
    (LittleOLinear.add_const 21
      (LittleOLinear.add
        (LittleOLinear.mul_left 81 littleOLinear_log2_succ_cube)
        (LittleOLinear.mul_left 9 littleOLinear_id_div_log2_succ)))
  exact ⟨2, by
    intro n hn
    have h := levelPartOverhead_le_envelope hn
    omega⟩

theorem canonicalRelativeRmmInteriorLegacyPartOverhead_littleO :
    LittleOLinear canonicalRelativeRmmInteriorLegacyPartOverhead := by
  apply LittleOLinear.of_eventually_le
    concreteBPRelativeRmmInteriorOverhead_littleO
  refine ⟨concreteBPRelativeRmmInteriorReadyThreshold, ?_⟩
  intro n hn
  let shape : Cartesian.CartesianShape :=
    Cartesian.shape (List.replicate n (0 : Int))
  have hsize : shape.size = n := by
    simp [shape, Cartesian.shape_size]
  have hready :
      concreteBPRelativeRmmInteriorReady shape := by
    apply concreteBPRelativeRmmInteriorReady_of_size_ge_readyThreshold
    simpa [hsize] using hn
  have hcompact :
      (RelativeRmm.canonicalLayout shape).CompactReady shape :=
    (RelativeRmm.canonicalLayout_compactReady_iff_legacyReady shape).mpr
      hready
  have heq :=
    canonicalRelativeRmmInteriorDirectory_payload_length_eq_legacy_of_compactReady
      hcompact
  have hlegacy :=
    (concreteBPRelativeRmmInteriorDirectory_profile_of_ready shape hready).2.1
  rw [canonicalRelativeRmmInteriorDirectory_payload_length_eq_raw] at heq
  rw [canonicalRelativeRmmInteriorLevelTableOverhead_eq_levelPart] at heq
  rw [canonicalRelativeRmmInteriorRawPayloadOverhead_eq_parts] at heq
  rw [hsize] at heq
  -- `heq` now reads
  --   legacyPart n + levelPart n = legacyPayload + levelPart n
  have hcancel :
      canonicalRelativeRmmInteriorLegacyPartOverhead n =
        (concreteBPRelativeRmmInteriorDirectory shape).payload.length := by
    omega
  calc
    canonicalRelativeRmmInteriorLegacyPartOverhead n =
        (concreteBPRelativeRmmInteriorDirectory shape).payload.length :=
      hcancel
    _ <= concreteBPRelativeRmmInteriorOverhead shape.size := hlegacy
    _ = concreteBPRelativeRmmInteriorOverhead n := by rw [hsize]

theorem canonicalRelativeRmmInteriorRawPayloadOverhead_littleO :
    LittleOLinear canonicalRelativeRmmInteriorRawPayloadOverhead := by
  have hsum :=
    LittleOLinear.add
      canonicalRelativeRmmInteriorLegacyPartOverhead_littleO
      canonicalRelativeRmmInteriorLevelPartOverhead_littleO
  apply LittleOLinear.of_le hsum
  intro n
  exact Nat.le_of_eq (canonicalRelativeRmmInteriorRawPayloadOverhead_eq_parts n)

theorem canonicalRelativeRmmInteriorOverhead_littleO :
    LittleOLinear canonicalRelativeRmmInteriorOverhead := by
  simpa [canonicalRelativeRmmInteriorOverhead] using
    canonicalRelativeRmmInteriorRawPayloadOverhead_littleO

theorem canonicalRelativeRmmInteriorDirectory_payload_le_overhead
    (shape : Cartesian.CartesianShape) :
    (canonicalRelativeRmmInteriorDirectory shape).payload.length <=
      canonicalRelativeRmmInteriorOverhead shape.size := by
  rw [canonicalRelativeRmmInteriorDirectory_payload_length_eq_raw]
  simp [canonicalRelativeRmmInteriorOverhead]

theorem canonicalRelativeRmmInteriorWordsRead_reconstruct_logical
    (shape : Cartesian.CartesianShape) (startBlock count : Nat) :
    SuccinctSpace.flattenPayloadWords
        (canonicalRelativeRmmInteriorWordsRead shape startBlock count) =
      SuccinctSpace.flattenPayloadWords
        (canonicalRelativeRmmInteriorLogicalWordsRead
          shape startBlock count) := by
  unfold canonicalRelativeRmmInteriorWordsRead
  generalize canonicalRelativeRmmInteriorLogicalWordsRead
      shape startBlock count = words
  induction words with
  | nil =>
      simp [SuccinctSpace.flattenPayloadWords]
  | cons head tail ih =>
      change SuccinctSpace.flattenPayloadWords
          (SuccinctSpace.chunkPayloadWords
              (SuccinctRank.machineWordBits shape.bpCode.length) head ++
            tail.flatMap (SuccinctSpace.chunkPayloadWords
              (SuccinctRank.machineWordBits shape.bpCode.length))) =
        head ++ SuccinctSpace.flattenPayloadWords tail
      rw [SuccinctSpace.flattenPayloadWords_append]
      rw [SuccinctSpace.flattenPayloadWords_chunkPayloadWords
        (SuccinctRank.machineWordBits_pos shape.bpCode.length) head]
      rw [ih]


structure CanonicalRelativeRmmInteriorStoreProfile
    (shape : Cartesian.CartesianShape) : Prop where
  component_flattens :
    flattenPayloadWords
        (canonicalRelativeRmmInteriorComponentStore
          shape).store.words.toList =
      (canonicalRelativeRmmSummaryTable shape).payload ++
        (canonicalRelativeRmmInteriorLocalTable shape).payload ++
          (canonicalRelativeRmmInteriorGlobalTable shape).payload ++
            (canonicalRelativeRmmInteriorLocalLevelTable shape).payload ++
              (canonicalRelativeRmmInteriorGlobalLevelTable shape).payload
  canonical_execution_eq :
    forall startBlock count,
      canonicalRelativeRmmInteriorRangeMinCostedWithStore shape
          (canonicalRelativeRmmInteriorComponentStore shape).store.words
          startBlock count =
        canonicalRelativeRmmInteriorRangeMinCosted shape startBlock count
  agreement_determines_result_cost :
    forall storeA storeB startBlock count,
      (forall address,
        List.Mem address
            (canonicalRelativeRmmInteriorRangeFootprintWithStore
              shape storeA startBlock count) ->
          storeA[address]? = storeB[address]?) ->
        canonicalRelativeRmmInteriorRangeMinCostedWithStore
            shape storeA startBlock count =
          canonicalRelativeRmmInteriorRangeMinCostedWithStore
            shape storeB startBlock count
  successful_read_backed :
    forall {startBlock count address : Nat} {word : List Bool},
      0 < count ->
      startBlock + count <=
        (RelativeRmm.canonicalLayout shape).blockCount ->
      List.Mem (address, some word)
        (canonicalRelativeRmmInteriorRangeMinExecutionWithStore shape
          (canonicalRelativeRmmInteriorComponentStore shape).store.words
          startBlock count).reads ->
      address <
          (canonicalRelativeRmmInteriorComponentStore shape).store.words.size /\
        List.Mem word
          (canonicalRelativeRmmInteriorComponentStore
            shape).store.words.toList
  returned_words_bounded :
    forall {startBlock count address : Nat} {word : List Bool},
      List.Mem (address, some word)
        (canonicalRelativeRmmInteriorRangeMinExecutionWithStore shape
          (canonicalRelativeRmmInteriorComponentStore shape).store.words
          startBlock count).reads ->
      word.length <= SuccinctRank.machineWordBits shape.bpCode.length
  returned_words_bounded_reviewer :
    forall {startBlock count address : Nat} {word : List Bool},
      List.Mem (address, some word)
        (canonicalRelativeRmmInteriorRangeMinExecutionWithStore shape
          (canonicalRelativeRmmInteriorComponentStore shape).store.words
          startBlock count).reads ->
      word.length <= canonicalRelativeRmmInteriorReviewerWordBits shape
  footprint_addresses_bounded :
    forall store startBlock count address,
      List.Mem address
        (canonicalRelativeRmmInteriorRangeFootprintWithStore
          shape store startBlock count) ->
      address < 2 ^ canonicalRelativeRmmInteriorReviewerWordBits shape
  valid_query_operands_bounded :
    forall {startBlock count},
      startBlock + count <=
        (RelativeRmm.canonicalLayout shape).blockCount ->
      startBlock < 2 ^ canonicalRelativeRmmInteriorReviewerWordBits shape /\
        count < 2 ^ canonicalRelativeRmmInteriorReviewerWordBits shape /\
        startBlock + count <
          2 ^ canonicalRelativeRmmInteriorReviewerWordBits shape
  footprint_recorded :
    forall store startBlock count,
      canonicalRelativeRmmInteriorRangeFootprintWithStore
          shape store startBlock count =
        (canonicalRelativeRmmInteriorRangeMinExecutionWithStore
          shape store startBlock count).reads.map Prod.fst
  cost_eq_footprint_length :
    forall store startBlock count,
      (canonicalRelativeRmmInteriorRangeMinCostedWithStore
        shape store startBlock count).cost =
        (canonicalRelativeRmmInteriorRangeFootprintWithStore
          shape store startBlock count).length

def canonicalRelativeRmmInteriorStoreProfile
    (shape : Cartesian.CartesianShape) :
    CanonicalRelativeRmmInteriorStoreProfile shape where
  component_flattens :=
    canonicalRelativeRmmInteriorComponentStore_flattens_payload shape
  canonical_execution_eq :=
    canonicalRelativeRmmInteriorRangeMinCostedWithStore_eq_current shape
  agreement_determines_result_cost := by
    intro storeA storeB startBlock count hagrees
    exact canonicalRelativeRmmInteriorRangeMinCostedWithStore_eq_of_agree
      shape storeA storeB startBlock count hagrees
  successful_read_backed := by
    intro startBlock count address word hcount hbound hread
    have hbacked :=
      canonicalRelativeRmmInteriorRange_successful_read_backed
        shape startBlock count address word hread
    exact And.intro hbacked.1 hbacked.2.1
  returned_words_bounded := by
    intro startBlock count address word hread
    exact canonicalRelativeRmmInteriorRange_returned_word_bounded
      shape startBlock count address word hread
  returned_words_bounded_reviewer := by
    intro startBlock count address word hread
    exact canonicalRelativeRmmInteriorRange_returned_word_bounded_reviewer
      shape startBlock count address word hread
  footprint_addresses_bounded := by
    intro store startBlock count address hmem
    exact
      canonicalRelativeRmmInteriorRangeFootprint_address_fits_reviewerWordBits
        shape (FlatWordStore.ofArray store) startBlock count address hmem
  valid_query_operands_bounded :=
    canonicalRelativeRmmInteriorValidQuery_operands_fit_reviewerWordBits shape
  footprint_recorded :=
    canonicalRelativeRmmInteriorRangeFootprint_recorded shape
  cost_eq_footprint_length :=
    canonicalRelativeRmmInteriorRange_cost_eq_footprint_length shape
theorem canonicalRelativeRmmInteriorDirectory_profile_allSize
    (shape : Cartesian.CartesianShape) :
    let directory := canonicalRelativeRmmInteriorDirectory shape
    LittleOLinear canonicalRelativeRmmInteriorOverhead /\
      directory.payload.length <=
        canonicalRelativeRmmInteriorOverhead shape.size /\
      (forall startBlock count,
        (directory.rangeMinCosted startBlock count).cost <=
          canonicalRelativeRmmInteriorQueryCost) /\
      (forall {startBlock count : Nat},
        0 < count ->
          startBlock + count <=
            (RelativeRmm.canonicalLayout shape).blockCount ->
            (directory.rangeMinCosted startBlock count).erase =
              some
                (bpRangeMinExcess shape
                  (RelativeRmm.canonicalLayout shape).blockSize
                  startBlock count,
                  bpRangeArgMinPrefixPos shape
                    (RelativeRmm.canonicalLayout shape).blockSize
                    startBlock count)) /\
      (forall {startBlock count : Nat} {word : List Bool},
        List.Mem word (directory.payloadWordsRead startBlock count) ->
          word.length <=
            SuccinctRank.machineWordBits shape.bpCode.length) /\
      CanonicalRelativeRmmInteriorStoreProfile shape := by
  let directory := canonicalRelativeRmmInteriorDirectory shape
  have hprofile := directory.profile
  exact And.intro canonicalRelativeRmmInteriorOverhead_littleO
    (And.intro
      (canonicalRelativeRmmInteriorDirectory_payload_le_overhead shape)
      (And.intro hprofile.2.1
        (And.intro hprofile.2.2.1
          (And.intro hprofile.2.2.2 (canonicalRelativeRmmInteriorStoreProfile shape)))))

theorem canonicalRelativeRmmInteriorDirectory_agrees_with_legacy_of_compactReady
    {shape : Cartesian.CartesianShape}
    (hready : (RelativeRmm.canonicalLayout shape).CompactReady shape)
    {startBlock count : Nat}
    (hcount : 0 < count)
    (hbound : startBlock + count <=
      (RelativeRmm.canonicalLayout shape).blockCount) :
    ((canonicalRelativeRmmInteriorDirectory shape).rangeMinCosted
        startBlock count).erase =
      ((concreteBPRelativeRmmInteriorDirectory shape).rangeMinCosted
        startBlock count).erase := by
  have hlegacyReady :=
    (RelativeRmm.canonicalLayout_compactReady_iff_legacyReady shape).mp hready
  have hblockCount :=
    RelativeRmm.legacy_blockCount_eq_canonical_of_compactReady hready
  have hblockSize :=
    RelativeRmm.legacy_blockSize_eq_canonical_of_compactReady hready
  have hlegacyBound :
      startBlock + count <= canonicalBPRelativeSummaryBlockCount shape := by
    simpa [hblockCount] using hbound
  have hcanonical :=
    canonicalRelativeRmmInteriorDirectory_rangeMinCosted_erase_exact
      hcount hbound
  have hlegacy :=
    (concreteBPRelativeRmmInteriorDirectory shape).rangeMin_exact
      hcount hlegacyBound
  rw [hcanonical, hlegacy]
  simp [hblockSize]

theorem concreteBPRelativeMinMaxArgSummaryTable_canonical_interior_scan_not_constant
    (shape : Cartesian.CartesianShape)
    (hblockSize : 0 < canonicalBPRelativeSummaryBlockSize shape) :
    let table := concreteBPRelativeMinMaxArgSummaryTable_canonical shape
    ¬ exists queryCost : Nat,
      forall leftClose rightClose : Nat,
        (table.interiorScanCosted leftClose rightClose).cost <=
          queryCost := by
  exact
    PayloadLiveBPRelativeMinMaxArgSummaryTable.interiorScanCosted_no_uniform_constant
      (concreteBPRelativeMinMaxArgSummaryTable_canonical shape)
      hblockSize


end SuccinctClose
end RMQ
