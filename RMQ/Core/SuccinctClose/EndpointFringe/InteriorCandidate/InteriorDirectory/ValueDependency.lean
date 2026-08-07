import RMQ.Core.SuccinctClose.EndpointFringe.InteriorCandidate.InteriorDirectory.SparseLevelWidth

/-!
# Interior directory: sparse-level returned-value dependency (B7)

Part of `RMQ.Core.SuccinctClose.EndpointFringe.InteriorCandidate.InteriorDirectory`, which remains the module downstream code imports.
Public declarations keep the canonical `RMQ.SuccinctClose` namespace.
-/

namespace RMQ
namespace SuccinctClose

open SuccinctSpace

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
