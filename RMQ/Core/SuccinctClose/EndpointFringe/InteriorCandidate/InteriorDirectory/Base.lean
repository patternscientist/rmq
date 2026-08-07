import RMQ.Core.SuccinctClose.EndpointFringe.InteriorCandidate.TwoLevelCandidate
import RMQ.Core.SuccinctSpace.MachineChunkedTableProgram
import RMQ.Core.SuccinctClose.EndpointFringe.PrefixRange.SparseLevelTable

/-!
# Interior directory: construction and core layout

Part of `RMQ.Core.SuccinctClose.EndpointFringe.InteriorCandidate.InteriorDirectory`, which remains the module downstream code imports.
Public declarations keep the canonical `RMQ.SuccinctClose` namespace.
-/

namespace RMQ
namespace SuccinctClose

open SuccinctSpace

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


end SuccinctClose
end RMQ
