import RMQ.Core.SuccinctClose.EndpointFringe.InteriorCandidate.TwoLevelCandidate

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

theorem concreteBPRelativeRmmInteriorSmallScanCost_le_threshold
    {shape : Cartesian.CartesianShape}
    (hactive : canonicalBPRelativeMinMaxArgSummaryTableActive shape)
    (hnotReady : ¬ concreteBPRelativeRmmInteriorReady shape) :
    4 * canonicalBPRelativeSummaryBlockCount shape <=
      concreteBPRelativeRmmInteriorSmallScanQueryCost := by
  have hcountLe :=
    canonicalBPRelativeSummaryBlockCount_le_size_of_active hactive
  have hsizeLt :=
    concreteBPRelativeRmmInterior_size_lt_readyThreshold_of_not_ready
      hnotReady
  unfold concreteBPRelativeRmmInteriorSmallScanQueryCost
  exact Nat.mul_le_mul_left 4 (by omega)

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
              concreteBPRelativeRmmInteriorSmallScanCost_le_threshold
                hactive hready
            exact Nat.le_trans hcost
              (Nat.le_trans hscan
                concreteBPRelativeRmmInteriorSmallScanQueryCost_le_queryCost)
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
