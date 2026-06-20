import RMQ.Core.TableModel
import RMQ.Impl.RecursiveHybridCost
import RMQ.Impl.SparseTableMemoCost

/-!
# Fischer-Heun microtable cost profile

This module packages the two exact finite facts that drive the Fischer-Heun
microtable story:

* raw shape lookup follows one decision path, so its cost is at most
  `blockSize + 1`;
* a block of size `blockSize` ranges over exactly `shapeCount blockSize`
  Cartesian signatures;
* the Catalan envelope `shapeCount b <= 4^b` turns the exact count into a
  square-root table-budget corollary when `4*b <= log2 n`.

The corollary is stated without introducing a separate square-root function:
`rawShapeTableCount b * rawShapeTableCount b <= n`.
-/

namespace RMQ

namespace FischerHeun

/-- Unit-cost bound for one raw local microtable lookup. -/
def rawLookupCostBound (blockSize : Nat) : Nat :=
  blockSize + 1

/-- Number of distinct shape-indexed local tables for this block size. -/
def rawShapeTableCount (blockSize : Nat) : Nat :=
  (Cartesian.shapeUniverse blockSize).length

/-- Number of local half-open query slots if each shape table is materialized. -/
def localQuerySlotBudget (blockSize : Nat) : Nat :=
  blockSize * (blockSize + 1) / 2

/-- Total slots in the exact shape-indexed microtable universe. -/
def rawMicrotableSlotBudget (blockSize : Nat) : Nat :=
  rawShapeTableCount blockSize * localQuerySlotBudget blockSize

/-- Standard Catalan-envelope target used by the Fischer-Heun table-count proof. -/
def shapeCountEnvelope (blockSize : Nat) : Nat :=
  4 ^ blockSize

theorem rawShapeTableCount_eq_shapeCount (blockSize : Nat) :
    rawShapeTableCount blockSize = Cartesian.shapeCount blockSize := by
  simp [rawShapeTableCount, Cartesian.shapeUniverse_length]

theorem rawMicrotableSlotBudget_eq_shapeCount_mul
    (blockSize : Nat) :
    rawMicrotableSlotBudget blockSize =
      Cartesian.shapeCount blockSize * localQuerySlotBudget blockSize := by
  simp [rawMicrotableSlotBudget, rawShapeTableCount_eq_shapeCount]

theorem rawMicrotableSlotBudget_le_of_local_slots_le_shape_count
    {blockSize n : Nat}
    (hslots : localQuerySlotBudget blockSize <= rawShapeTableCount blockSize)
    (hsquare :
      rawShapeTableCount blockSize * rawShapeTableCount blockSize <= n) :
    rawMicrotableSlotBudget blockSize <= n := by
  unfold rawMicrotableSlotBudget
  exact Nat.le_trans
    (Nat.mul_le_mul_left (rawShapeTableCount blockSize) hslots)
    hsquare

theorem rawLookupCosted_cost_le_bound
    (xs : List Int) (start blockSize left right : Nat) :
    (Cartesian.rawMicrotableLookupCosted xs start blockSize left right).cost <=
      rawLookupCostBound blockSize := by
  simpa [rawLookupCostBound] using
    Cartesian.rawMicrotableLookupCosted_cost_le
      xs start blockSize left right

/--
Combined cost/count certificate for the raw shape microtable profile.

This is the exact finite form of the Fischer-Heun microtable premise: lookup is
linear in block size, and the number of shape tables is `shapeCount blockSize`.
-/
theorem rawMicrotable_cost_count_profile
    (xs : List Int) (start blockSize left right : Nat) :
    (Cartesian.rawMicrotableLookupCosted xs start blockSize left right).cost <=
        rawLookupCostBound blockSize /\
      rawShapeTableCount blockSize = Cartesian.shapeCount blockSize := by
  exact ⟨rawLookupCosted_cost_le_bound xs start blockSize left right,
    rawShapeTableCount_eq_shapeCount blockSize⟩

theorem rawShapeTableCount_le_envelope
    (blockSize : Nat)
    (hcat : Cartesian.shapeCount blockSize <= shapeCountEnvelope blockSize) :
    rawShapeTableCount blockSize <= shapeCountEnvelope blockSize := by
  simpa [rawShapeTableCount_eq_shapeCount] using hcat

theorem rawShapeTableCount_le_shapeCountEnvelope (blockSize : Nat) :
    rawShapeTableCount blockSize <= shapeCountEnvelope blockSize := by
  exact rawShapeTableCount_le_envelope blockSize
    (by
      simpa [shapeCountEnvelope] using
        Cartesian.shapeCount_le_four_pow blockSize)

/--
Squared form of the eventual `O(sqrt n)` table-count corollary.

Once the Catalan envelope `shapeCount b <= 4^b` and the block-size choice
`(4^b)^2 <= n` are supplied, the number of shape tables fits a square-root
budget, stated without introducing a separate square-root function.
-/
theorem rawShapeTableCount_square_le_of_envelope_square
    {blockSize n : Nat}
    (hcat : Cartesian.shapeCount blockSize <= shapeCountEnvelope blockSize)
    (hbudget : shapeCountEnvelope blockSize * shapeCountEnvelope blockSize <= n) :
    rawShapeTableCount blockSize * rawShapeTableCount blockSize <= n := by
  have htable := rawShapeTableCount_le_envelope blockSize hcat
  exact Nat.le_trans (Nat.mul_le_mul htable htable) hbudget

/--
Fischer-Heun square-root table-count corollary, stated without introducing a
separate square-root function: if the block-size choice makes the Catalan
envelope square fit under `n`, then the exact raw shape-table count does too.
-/
theorem rawShapeTableCount_square_le_of_envelope_budget
    {blockSize n : Nat}
    (hbudget :
      shapeCountEnvelope blockSize * shapeCountEnvelope blockSize <= n) :
    rawShapeTableCount blockSize * rawShapeTableCount blockSize <= n := by
  exact rawShapeTableCount_square_le_of_envelope_square
    (blockSize := blockSize) (n := n)
    (by
      simpa [shapeCountEnvelope] using
        Cartesian.shapeCount_le_four_pow blockSize)
    hbudget

theorem shapeCountEnvelope_eq_two_pow_two_mul (blockSize : Nat) :
    shapeCountEnvelope blockSize = 2 ^ (2 * blockSize) := by
  simp [shapeCountEnvelope]
  calc
    4 ^ blockSize = (2 ^ 2) ^ blockSize := by
      simp
    _ = 2 ^ (2 * blockSize) := by
      rw [← Nat.pow_mul]

theorem shapeCountEnvelope_square_eq_two_pow_four_mul
    (blockSize : Nat) :
    shapeCountEnvelope blockSize * shapeCountEnvelope blockSize =
      2 ^ (4 * blockSize) := by
  rw [shapeCountEnvelope_eq_two_pow_two_mul, ← Nat.pow_add]
  congr
  omega

theorem shapeCountEnvelope_square_le_of_four_mul_le_log2
    {blockSize n : Nat}
    (hn : 0 < n) (hlog : 4 * blockSize <= Nat.log2 n) :
    shapeCountEnvelope blockSize * shapeCountEnvelope blockSize <= n := by
  rw [shapeCountEnvelope_square_eq_two_pow_four_mul]
  have hmono : 2 ^ (4 * blockSize) <= 2 ^ Nat.log2 n := by
    exact Nat.pow_le_pow_right (by omega) hlog
  have hself : 2 ^ Nat.log2 n <= n := Nat.log2_self_le (by omega)
  exact Nat.le_trans hmono hself

/--
Base-2-log version of the square-root table-count corollary. Since
`shapeCount b <= 4^b`, the squared budget is discharged by
`4*b <= log2 n`.
-/
theorem rawShapeTableCount_square_le_of_four_mul_le_log2
    {blockSize n : Nat}
    (hn : 0 < n) (hlog : 4 * blockSize <= Nat.log2 n) :
    rawShapeTableCount blockSize * rawShapeTableCount blockSize <= n := by
  exact rawShapeTableCount_square_le_of_envelope_budget
    (shapeCountEnvelope_square_le_of_four_mul_le_log2
      (blockSize := blockSize) (n := n) hn hlog)

/--
Canonical Fischer-Heun block size for the cost proof: one quarter of the
base-2 logarithm of the input length.
-/
def canonicalBlockSize (xs : List Int) : Nat :=
  Nat.log2 xs.length / 4

theorem canonicalBlockSize_four_mul_le_log2 (xs : List Int) :
    4 * canonicalBlockSize xs <= Nat.log2 xs.length := by
  unfold canonicalBlockSize
  simpa [Nat.mul_comm] using Nat.div_mul_le_self (Nat.log2 xs.length) 4

private theorem nat_le_two_pow (n : Nat) :
    n <= 2 ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Nat.pow_succ]
      have hpos : 1 <= 2 ^ n := Nat.succ_le_of_lt (Nat.pow_pos (by omega))
      omega

private theorem nat_succ_le_two_pow (n : Nat) :
    n + 1 <= 2 ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Nat.pow_succ]
      have hpos : 1 <= 2 ^ n := Nat.succ_le_of_lt (Nat.pow_pos (by omega))
      omega

theorem localQuerySlotBudget_le_shapeCountEnvelope (b : Nat) :
    localQuerySlotBudget b <= shapeCountEnvelope b := by
  unfold localQuerySlotBudget
  rw [shapeCountEnvelope_eq_two_pow_two_mul]
  have hb := nat_le_two_pow b
  have hsucc := nat_succ_le_two_pow b
  have hmul : b * (b + 1) <= 2 ^ b * 2 ^ b :=
    Nat.mul_le_mul hb hsucc
  have hdiv : b * (b + 1) / 2 <= b * (b + 1) :=
    Nat.div_le_self _ _
  have hpow : 2 ^ b * 2 ^ b = 2 ^ (2 * b) := by
    rw [← Nat.pow_add]
    congr
    omega
  exact Nat.le_trans hdiv (Nat.le_trans hmul (Nat.le_of_eq hpow))

theorem rawMicrotableSlotBudget_le_shapeCountEnvelope_square (b : Nat) :
    rawMicrotableSlotBudget b <= shapeCountEnvelope b * shapeCountEnvelope b := by
  unfold rawMicrotableSlotBudget
  exact Nat.mul_le_mul
    (rawShapeTableCount_le_shapeCountEnvelope b)
    (localQuerySlotBudget_le_shapeCountEnvelope b)

theorem rawMicrotableSlotBudget_le_length_of_four_mul_le_log2
    {xs : List Int} {b : Nat}
    (hpos : 0 < xs.length)
    (hlog : 4 * b <= Nat.log2 xs.length) :
    rawMicrotableSlotBudget b <= xs.length := by
  exact Nat.le_trans
    (rawMicrotableSlotBudget_le_shapeCountEnvelope_square b)
    (shapeCountEnvelope_square_le_of_four_mul_le_log2
      (blockSize := b) (n := xs.length) hpos hlog)

theorem rawMicrotableSlotBudget_canonical_le_length
    (xs : List Int) (hpos : 0 < xs.length) :
    rawMicrotableSlotBudget (canonicalBlockSize xs) <= xs.length := by
  exact rawMicrotableSlotBudget_le_length_of_four_mul_le_log2
    (xs := xs) (b := canonicalBlockSize xs) hpos
    (canonicalBlockSize_four_mul_le_log2 xs)

private theorem log2_le_of_lt_pow_succ {n k : Nat}
    (h : n < 2 ^ (k + 1)) :
    Nat.log2 n <= k := by
  by_cases hzero : n = 0
  · simp [hzero]
  · by_cases hle : Nat.log2 n <= k
    · exact hle
    have hk : k + 1 <= Nat.log2 n := by omega
    have hmono : 2 ^ (k + 1) <= 2 ^ Nat.log2 n := by
      exact Nat.pow_le_pow_right (by omega) hk
    have hself : 2 ^ Nat.log2 n <= n := Nat.log2_self_le hzero
    have : 2 ^ (k + 1) <= n := Nat.le_trans hmono hself
    omega

private theorem div_lt_pow_of_lt_pow_add_four
    {n b k : Nat} (hb : 16 <= b) (hn : n < 2 ^ (k + 4)) :
    n / b < 2 ^ k := by
  by_cases hlt : n / b < 2 ^ k
  · exact hlt
  have hq : 2 ^ k <= n / b := Nat.le_of_not_gt hlt
  have hqmul : 2 ^ k * b <= (n / b) * b :=
    Nat.mul_le_mul_right b hq
  have hdivmul : (n / b) * b <= n :=
    Nat.div_mul_le_self n b
  have hbmul : 2 ^ k * 16 <= 2 ^ k * b :=
    Nat.mul_le_mul_left (2 ^ k) hb
  have hpow : 2 ^ k * 16 = 2 ^ (k + 4) := by
    rw [Nat.pow_add]
  have : 2 ^ (k + 4) <= n := by
    rw [← hpow]
    exact Nat.le_trans hbmul (Nat.le_trans hqmul hdivmul)
  omega

theorem summaryLog_canonical_le_four_mul
    (xs : List Int) (hb : 16 <= canonicalBlockSize xs) :
    Nat.log2 (blockMinSummary xs (canonicalBlockSize xs)).length <=
      4 * canonicalBlockSize xs := by
  let l := Nat.log2 xs.length
  let b := canonicalBlockSize xs
  have hb' : 16 <= b := by simpa [b] using hb
  have hlog_lt : l < b * 4 + 4 := by
    have h := Nat.lt_div_mul_add (by omega : 0 < 4) (a := l)
    simpa [b, canonicalBlockSize, Nat.mul_comm] using h
  have hlog_succ : l + 1 <= 4 * b + 4 := by
    omega
  have hlen_lt_log : xs.length < 2 ^ (l + 1) := by
    simpa [l] using (Nat.lt_log2_self (n := xs.length))
  have hpow_le : 2 ^ (l + 1) <= 2 ^ (4 * b + 4) := by
    exact Nat.pow_le_pow_right (by omega) hlog_succ
  have hlen_lt : xs.length < 2 ^ (4 * b + 4) :=
    Nat.lt_of_lt_of_le hlen_lt_log hpow_le
  have hsummary_len :
      (blockMinSummary xs b).length = xs.length / b := by
    simp [blockMinSummary_length, compressedLength]
  have hdiv_lt : xs.length / b < 2 ^ (4 * b) :=
    div_lt_pow_of_lt_pow_add_four (n := xs.length) (b := b)
      (k := 4 * b) hb' hlen_lt
  have hdiv_lt_succ : xs.length / b < 2 ^ (4 * b + 1) := by
    have hpow_mono : 2 ^ (4 * b) <= 2 ^ (4 * b + 1) := by
      exact Nat.pow_le_pow_right (by omega) (by omega)
    exact Nat.lt_of_lt_of_le hdiv_lt hpow_mono
  have htarget := log2_le_of_lt_pow_succ
    (n := xs.length / b) (k := 4 * b) hdiv_lt_succ
  simpa [b, hsummary_len] using htarget

theorem canonicalBlockSize_pos_length_of_ge_sixteen
    {xs : List Int} (hb : 16 <= canonicalBlockSize xs) :
    0 < xs.length := by
  by_cases hpos : 0 < xs.length
  · exact hpos
  have hzero : xs.length = 0 := Nat.eq_zero_of_not_pos hpos
  simp [canonicalBlockSize, hzero] at hb

def summarySparseBuildCost (xs : List Int) (b : Nat) : Nat :=
  SparseTable.memoBuildSparseTableCost (blockMinSummary xs b)

theorem blockMinSummary_length_mul_le_length
    (xs : List Int) (b : Nat) :
    (blockMinSummary xs b).length * b <= xs.length := by
  rw [blockMinSummary_length]
  unfold compressedLength
  exact Nat.div_mul_le_self xs.length b

theorem blockMinSummary_length_le_length
    (xs : List Int) (b : Nat) :
    (blockMinSummary xs b).length <= xs.length := by
  rw [blockMinSummary_length]
  unfold compressedLength
  exact Nat.div_le_self xs.length b

theorem summarySparseBuildCost_le_thirteen_mul_length
    (xs : List Int) (b : Nat)
    (hlog : Nat.log2 (blockMinSummary xs b).length <= 4 * b) :
    summarySparseBuildCost xs b <= 13 * xs.length := by
  unfold summarySparseBuildCost
  rw [SparseTable.memoBuildSparseTableCost_eq_log]
  by_cases hzero : (blockMinSummary xs b).length = 0
  · simp [hzero]
  · simp [hzero]
    let m := (blockMinSummary xs b).length
    have hm_le_n : m <= xs.length := by
      exact blockMinSummary_length_le_length xs b
    have hmb_le_n : m * b <= xs.length := by
      exact blockMinSummary_length_mul_le_length xs b
    have hterm :
        Nat.log2 m * (m * SparseTable.memoNextCellCost) <= 12 * xs.length := by
      have hlog' : Nat.log2 m <= 4 * b := by
        simpa [m] using hlog
      have hcell : SparseTable.memoNextCellCost = 3 := by
        rfl
      rw [hcell]
      have hmul1 :
          Nat.log2 m * (m * 3) <= (4 * b) * (m * 3) :=
        Nat.mul_le_mul_right (m * 3) hlog'
      have hmul2 : (4 * b) * (m * 3) = 12 * (m * b) := by
        ac_rfl
      have hmul3 : 12 * (m * b) <= 12 * xs.length :=
        Nat.mul_le_mul_left 12 hmb_le_n
      exact Nat.le_trans hmul1 (by simpa [hmul2] using hmul3)
    have hterm_actual :
        Nat.log2 (blockMinSummary xs b).length *
            ((blockMinSummary xs b).length * SparseTable.memoNextCellCost) <=
          12 * xs.length := by
      simpa [m] using hterm
    have hsum := Nat.add_le_add hm_le_n hterm_actual
    exact Nat.le_trans hsum (by omega)

/--
RAM/unit-cost indexed-access model: a stored local microtable query reads the
block signature and then the shape/query slot, one modeled indexed read each.
-/
def storedMicrotableLookupCost : Nat :=
  TableModel.indexedReadCost + TableModel.indexedReadCost

/--
Query cost for a supplied Fischer-Heun state: two stored local microtable
lookups for boundary blocks, one supplied sparse-table query over full-block
summaries, and two candidate combines.
-/
def suppliedQueryCost
    (xs : List Int) (b left right : Nat) : Nat :=
  if _h : ValidRange xs left right /\ 0 < b then
    storedMicrotableLookupCost + 7 + storedMicrotableLookupCost + 2
  else
    1

theorem suppliedQueryCost_le_thirteen
    (xs : List Int) (b left right : Nat) :
    suppliedQueryCost xs b left right <= 13 := by
  unfold suppliedQueryCost
  by_cases h : ValidRange xs left right /\ 0 < b
  · rw [dif_pos h]
    simp [storedMicrotableLookupCost, TableModel.indexedReadCost]
  · rw [dif_neg h]
    omega

/--
End-to-end preprocessing budget for the assembled Fischer-Heun structure:
materialized shape microtables, block-minimum summary construction, and the
memoized sparse table over block summaries.
-/
def buildCost (xs : List Int) (b : Nat) : Nat :=
  rawMicrotableSlotBudget b +
    (RecursiveHybrid.blockMinSummaryBuildCost xs b +
      summarySparseBuildCost xs b)

theorem buildCost_le_fifteen_mul_length
    (xs : List Int) (b : Nat)
    (hmicro : rawMicrotableSlotBudget b <= xs.length)
    (hsummaryLog :
      Nat.log2 (blockMinSummary xs b).length <= 4 * b) :
    buildCost xs b <= 15 * xs.length := by
  unfold buildCost
  have hsummaryBuild :
      RecursiveHybrid.blockMinSummaryBuildCost xs b <= xs.length :=
    RecursiveHybrid.blockMinSummaryBuildCost_le_length xs b
  have hsparse :
      summarySparseBuildCost xs b <= 13 * xs.length :=
    summarySparseBuildCost_le_thirteen_mul_length xs b hsummaryLog
  have hsum :
      rawMicrotableSlotBudget b +
          (RecursiveHybrid.blockMinSummaryBuildCost xs b +
            summarySparseBuildCost xs b) <=
        xs.length + (xs.length + 13 * xs.length) :=
    Nat.add_le_add hmicro (Nat.add_le_add hsummaryBuild hsparse)
  exact Nat.le_trans hsum (by omega)

theorem buildCost_le_fifteen_mul_length_of_shape_budget
    (xs : List Int) (b : Nat)
    (hslots : localQuerySlotBudget b <= rawShapeTableCount b)
    (hsquare : rawShapeTableCount b * rawShapeTableCount b <= xs.length)
    (hsummaryLog :
      Nat.log2 (blockMinSummary xs b).length <= 4 * b) :
    buildCost xs b <= 15 * xs.length := by
  exact buildCost_le_fifteen_mul_length xs b
    (rawMicrotableSlotBudget_le_of_local_slots_le_shape_count
      hslots hsquare)
    hsummaryLog

theorem buildCost_linear_under_budget :
    exists c,
      forall xs b,
        rawMicrotableSlotBudget b <= xs.length ->
          Nat.log2 (blockMinSummary xs b).length <= 4 * b ->
            buildCost xs b <= c * xs.length := by
  exact ⟨15, buildCost_le_fifteen_mul_length⟩

theorem suppliedQueryCost_constant :
    exists c,
      forall xs b left right,
        suppliedQueryCost xs b left right <= c := by
  exact ⟨13, suppliedQueryCost_le_thirteen⟩

/--
Assembled Fischer-Heun cost profile. Under the finite-table budget for the
materialized microtables and the log-row budget for the summary sparse table,
preprocessing is linear in the input length and supplied queries are constant
time in the RAM/unit-cost indexed-access model named above.
-/
theorem linearBuild_constantQuery_profile :
    exists buildC queryC,
      forall xs b,
        rawMicrotableSlotBudget b <= xs.length ->
          Nat.log2 (blockMinSummary xs b).length <= 4 * b ->
            buildCost xs b <= buildC * xs.length /\
              forall left right,
                suppliedQueryCost xs b left right <= queryC := by
  refine ⟨15, 13, ?_⟩
  intro xs b hm hlog
  exact ⟨buildCost_le_fifteen_mul_length xs b hm hlog,
    fun left right => suppliedQueryCost_le_thirteen xs b left right⟩

theorem linearBuild_constantQuery_profile_of_shape_budget :
    exists buildC queryC,
      forall xs b,
        localQuerySlotBudget b <= rawShapeTableCount b ->
          rawShapeTableCount b * rawShapeTableCount b <= xs.length ->
            Nat.log2 (blockMinSummary xs b).length <= 4 * b ->
              buildCost xs b <= buildC * xs.length /\
                forall left right,
                  suppliedQueryCost xs b left right <= queryC := by
  refine ⟨15, 13, ?_⟩
  intro xs b hslots hsquare hlog
  exact ⟨buildCost_le_fifteen_mul_length_of_shape_budget
      xs b hslots hsquare hlog,
    fun left right => suppliedQueryCost_le_thirteen xs b left right⟩

/--
Canonical-block-size Fischer-Heun profile. For inputs large enough that the
quarter-log block size is at least `16`, the canonical choice discharges the
microtable budget and summary sparse-table log-row budget automatically.
-/
theorem linearBuild_constantQuery_profile_canonical :
    exists buildC queryC,
      forall xs,
        16 <= canonicalBlockSize xs ->
          buildCost xs (canonicalBlockSize xs) <= buildC * xs.length /\
            forall left right,
              suppliedQueryCost xs (canonicalBlockSize xs) left right <=
                queryC := by
  refine ⟨15, 13, ?_⟩
  intro xs hb
  have hpos := canonicalBlockSize_pos_length_of_ge_sixteen (xs := xs) hb
  have hmicro := rawMicrotableSlotBudget_canonical_le_length xs hpos
  have hsummary := summaryLog_canonical_le_four_mul xs hb
  exact ⟨buildCost_le_fifteen_mul_length xs (canonicalBlockSize xs)
      hmicro hsummary,
    fun left right => suppliedQueryCost_le_thirteen xs (canonicalBlockSize xs)
      left right⟩

end FischerHeun

end RMQ
