import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
# EG-CP-F01 / EG-CP-F11 : small-size behavior and the exact model split

This file pins the small-size behavior that `EG-CP-F01-HEADER-SCHEMA`
explicitly names, and locates every threshold in the route that it can reach
with a checked theorem.

Nothing under `RMQ/` is modified.
-/

namespace RMQ
namespace PackedHeaderSmall

open RMQ.Cartesian
open RMQ.SuccinctClose

/-! ## 0. A kernel-usable `Nat.log2` evaluator

`Nat.log2` is defined by well-founded recursion, so `decide` cannot reduce it.
Every literal value below is produced by this lemma instead. -/

theorem log2_lit {n k : Nat} (hlo : 2 ^ k <= n) (hhi : n < 2 ^ (k + 1)) :
    Nat.log2 n = k := by
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have hn : n ≠ 0 := by omega
  have h1 : k <= Nat.log2 n := (Nat.le_log2 hn).mpr hlo
  have h2 : Nat.log2 n < k + 1 := (Nat.log2_lt hn).mpr hhi
  omega

theorem log2_zero : Nat.log2 0 = 0 := by
  unfold Nat.log2; simp

theorem log2_one : Nat.log2 1 = 0 := log2_lit (by decide) (by decide)

/-- `Nat.log2 (2 * n) = Nat.log2 n + 1` for positive `n`; FALSE at `n = 0`. -/
theorem log2_two_mul_of_pos {n : Nat} (hn : 0 < n) :
    Nat.log2 (2 * n) = Nat.log2 n + 1 := by
  have hn' : n ≠ 0 := by omega
  have hlo : 2 ^ Nat.log2 n <= n := Nat.log2_self_le hn'
  have hhi : n < 2 ^ (Nat.log2 n + 1) := Nat.lt_log2_self
  have p1 : (2 : Nat) ^ (Nat.log2 n + 1) = 2 ^ Nat.log2 n * 2 := Nat.pow_succ 2 _
  have p2 : (2 : Nat) ^ (Nat.log2 n + 1 + 1) = 2 ^ (Nat.log2 n + 1) * 2 :=
    Nat.pow_succ 2 _
  exact log2_lit (by omega) (by omega)

/-! ## 1. The frozen word width `w(n)` and the K = 1 header

`w(n)` is `SuccinctRank.machineWordBits (2 * n)`, the route's own BP-close rank
word size (`RMQ/Core/SuccinctFinal.lean:767-769` composed with
`Cartesian.CartesianShape.bpCode_length`). -/

def frozenWordWidth (n : Nat) : Nat := SuccinctRank.machineWordBits (2 * n)

theorem frozenWordWidth_closed_form (n : Nat) :
    frozenWordWidth n = Nat.log2 (2 * n) + 1 := rfl

/-- The K = 1 header: one field, the size `n`. -/
def headerArity : Nat := 1

def headerFieldValue (n : Nat) : Nat := n

/-- Header length in bits: `K` fields of `w(n)` bits each. -/
def headerBitsLength (n : Nat) : Nat := headerArity * frozenWordWidth n

/-- Header length in `w(n)`-bit cells. -/
def headerCells (n : Nat) : Nat := (headerBitsLength n + frozenWordWidth n - 1) / frozenWordWidth n

theorem frozenWordWidth_pos (n : Nat) : 0 < frozenWordWidth n := by
  simp [frozenWordWidth, SuccinctRank.machineWordBits]

/-- ALL SIZES, including `0` and `1`: the header occupies exactly one cell. -/
theorem headerCells_eq_one (n : Nat) : headerCells n = 1 := by
  have h := frozenWordWidth_pos n
  have key : (frozenWordWidth n + frozenWordWidth n - 1) / frozenWordWidth n = 1 :=
    Nat.div_eq_of_lt_le (by omega) (by omega)
  simpa [headerCells, headerBitsLength, headerArity] using key

/-- ALL SIZES: the single header field's value fits strictly inside its width,
so there is no `n` at which the header overflows its cell. -/
theorem headerFieldValue_lt_two_pow (n : Nat) :
    headerFieldValue n < 2 ^ frozenWordWidth n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [headerFieldValue, frozenWordWidth, SuccinctRank.machineWordBits]
  · have : n < 2 ^ (Nat.log2 n + 1) := Nat.lt_log2_self
    have hw : frozenWordWidth n = Nat.log2 n + 2 := by
      simp [frozenWordWidth, SuccinctRank.machineWordBits, log2_two_mul_of_pos hn]
    have hmono : (2 : Nat) ^ (Nat.log2 n + 1) <= 2 ^ (Nat.log2 n + 2) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    simp only [headerFieldValue, hw]
    omega

/-! ### Small-size pins for the header -/

theorem frozenWordWidth_zero : frozenWordWidth 0 = 1 := by
  simp [frozenWordWidth, SuccinctRank.machineWordBits]

theorem frozenWordWidth_one : frozenWordWidth 1 = 2 := by
  simp [frozenWordWidth, SuccinctRank.machineWordBits, log2_lit (n := 2) (k := 1) (by decide) (by decide)]

theorem headerBitsLength_zero : headerBitsLength 0 = 1 := by
  simp [headerBitsLength, headerArity, frozenWordWidth_zero]

theorem headerBitsLength_one : headerBitsLength 1 = 2 := by
  simp [headerBitsLength, headerArity, frozenWordWidth_one]

/-- `n = 0`: a one-bit cell holding the value `0`. -/
theorem header_zero_fits : headerFieldValue 0 < 2 ^ frozenWordWidth 0 := by
  simp [headerFieldValue, frozenWordWidth_zero]

/-- `n = 1`: a two-bit cell holding the value `1`. -/
theorem header_one_fits : headerFieldValue 1 < 2 ^ frozenWordWidth 1 := by
  simp [headerFieldValue, frozenWordWidth_one]

/-- The header contains no size-dependent branch: `headerCells` is the constant
`1` and `headerBitsLength` is the single total function `w`, with no case split.
Stated as: the header cell count agrees at every pair of sizes. -/
theorem headerCells_no_small_split (m n : Nat) : headerCells m = headerCells n := by
  rw [headerCells_eq_one, headerCells_eq_one]

/-! ## 2. K = 3 would NOT be one-cell-per-field

If `EG-CP-F01` declines to pad the two content-dependent select regions and
instead stores their bases, those fields range over the existing `n`-only
budgets.  Those budgets exceed `2 ^ w(n)`, so such a field does NOT fit in one
`w(n)`-bit cell and costs at least two probes. -/

theorem sparse_budget_at_1024 :
    SuccinctSelect.sparseExceptionRelativeTableOverhead 1024 = 262656 := by
  have h1 : Nat.log2 (2 * 1024) = 11 := log2_lit (by decide) (by decide)
  have h2 : Nat.log2 12 = 3 := log2_lit (by decide) (by decide)
  simp [SuccinctSelect.sparseExceptionRelativeTableOverhead,
    SuccinctSpace.idDivLogLogOverhead, h1, h2]

theorem frozenWordWidth_1024 : frozenWordWidth 1024 = 12 := by
  have h1 : Nat.log2 (2 * 1024) = 11 := log2_lit (by decide) (by decide)
  simp [frozenWordWidth, SuccinctRank.machineWordBits, h1]

/-- A `K = 3` header field carrying the sparse-exception base does not fit in
one `w(n)`-bit cell at `n = 1024`: the budget is `262656`, the cell holds values
below `2 ^ 12 = 4096`. -/
theorem sparse_budget_exceeds_one_cell_at_1024 :
    2 ^ frozenWordWidth 1024 <=
      SuccinctSelect.sparseExceptionRelativeTableOverhead 1024 := by
  rw [frozenWordWidth_1024, sparse_budget_at_1024]
  decide

/-! ## 3. `canonicalBPRelativeMinMaxArgSummaryTableActive` : the exact split

`Active` is size-only: every component is a function of `shape.size` and of
`shape.bpCode.length = 2 * shape.size`.  Its sixth conjunct is the binding one. -/

/-- The sixth conjunct of `Active`, extracted. -/
theorem active_relativeWidth_le {shape : CartesianShape}
    (h : canonicalBPRelativeMinMaxArgSummaryTableActive shape) :
    2 * (Nat.log2 (Nat.log2 shape.size + 1) + 1) + 3 <=
      Nat.log2 (2 * shape.size) + 1 := by
  have h6 := h.2.2.2.2.2
  simpa [canonicalBPRelativeSummaryRelativeWidthRaw, canonicalBPRelativeSummaryBase,
    SuccinctRank.machineWordBits, CartesianShape.bpCode_length] using h6

/-- **ALL sizes below 512**: the relative min/max/arg summary table is INACTIVE,
for every Cartesian shape, with no content hypothesis. -/
theorem not_active_of_size_lt_512 {shape : CartesianShape}
    (hsize : shape.size < 512) :
    ¬ canonicalBPRelativeMinMaxArgSummaryTableActive shape := by
  intro hactive
  have h6 := active_relativeWidth_le hactive
  rcases Nat.eq_zero_or_pos shape.size with hz | hp
  · rw [hz] at h6
    rw [log2_zero] at h6
    rw [log2_one] at h6
    simp at h6
  · have hlog2 : Nat.log2 (2 * shape.size) = Nat.log2 shape.size + 1 :=
      log2_two_mul_of_pos hp
    rw [hlog2] at h6
    have hne : shape.size ≠ 0 := by omega
    have h512 : (2 : Nat) ^ 9 = 512 := by decide
    have hlt : Nat.log2 shape.size < 9 :=
      (Nat.log2_lt hne).mpr (by rw [h512]; exact hsize)
    -- finite case analysis on `a = Nat.log2 shape.size` in `[0, 8]`
    obtain ⟨a, ha⟩ : ∃ a, Nat.log2 shape.size = a := ⟨_, rfl⟩
    rw [ha] at h6 hlt
    have hcases : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/
        a = 7 \/ a = 8 := by omega
    have e1 : Nat.log2 1 = 0 := log2_one
    have e2 : Nat.log2 2 = 1 := log2_lit (by decide) (by decide)
    have e3 : Nat.log2 3 = 1 := log2_lit (by decide) (by decide)
    have e4 : Nat.log2 4 = 2 := log2_lit (by decide) (by decide)
    have e5 : Nat.log2 5 = 2 := log2_lit (by decide) (by decide)
    have e6 : Nat.log2 6 = 2 := log2_lit (by decide) (by decide)
    have e7 : Nat.log2 7 = 2 := log2_lit (by decide) (by decide)
    have e8 : Nat.log2 8 = 3 := log2_lit (by decide) (by decide)
    have e9 : Nat.log2 9 = 3 := log2_lit (by decide) (by decide)
    rcases hcases with h | h | h | h | h | h | h | h | h <;>
      rw [h] at h6 <;>
      simp [e1, e2, e3, e4, e5, e6, e7, e8, e9] at h6
    all_goals omega

/-! ### The gated geometry is DEGENERATE below 512 -/

theorem blockSize_eq_zero_of_size_lt_512 {shape : CartesianShape}
    (hsize : shape.size < 512) :
    canonicalBPRelativeSummaryBlockSize shape = 0 := by
  simp [canonicalBPRelativeSummaryBlockSize, not_active_of_size_lt_512 hsize]

theorem blockCount_eq_zero_of_size_lt_512 {shape : CartesianShape}
    (hsize : shape.size < 512) :
    canonicalBPRelativeSummaryBlockCount shape = 0 := by
  simp [canonicalBPRelativeSummaryBlockCount, not_active_of_size_lt_512 hsize]

theorem superCount_eq_zero_of_size_lt_512 {shape : CartesianShape}
    (hsize : shape.size < 512) :
    canonicalBPRelativeSummarySuperCount shape = 0 := by
  simp [canonicalBPRelativeSummarySuperCount, not_active_of_size_lt_512 hsize]

theorem blocksPerSuper_eq_one_of_size_lt_512 {shape : CartesianShape}
    (hsize : shape.size < 512) :
    canonicalBPRelativeSummaryBlocksPerSuper shape = 1 := by
  simp [canonicalBPRelativeSummaryBlocksPerSuper, not_active_of_size_lt_512 hsize]

theorem interiorPayloadLength_eq_zero_of_size_lt_512 {shape : CartesianShape}
    (hsize : shape.size < 512) :
    concreteBPRelativeRmmInteriorDirectoryPayloadLength shape = 0 :=
  concreteBPRelativeRmmInteriorDirectoryPayloadLength_eq_zero_of_not_active
    (not_active_of_size_lt_512 hsize)

theorem not_ready_of_size_lt_512 {shape : CartesianShape}
    (hsize : shape.size < 512) :
    ¬ concreteBPRelativeRmmInteriorReady shape := by
  intro hready
  exact not_active_of_size_lt_512 hsize (concreteBPRelativeRmmInteriorReady_active hready)

/-! ### At size exactly 512 the table is ACTIVE : the divergence, exactly -/

theorem log2_512 : Nat.log2 512 = 9 := log2_lit (by decide) (by decide)
theorem log2_1024 : Nat.log2 1024 = 10 := log2_lit (by decide) (by decide)
theorem log2_10 : Nat.log2 10 = 3 := log2_lit (by decide) (by decide)

theorem active_at_512 {shape : CartesianShape} (hsize : shape.size = 512) :
    canonicalBPRelativeMinMaxArgSummaryTableActive shape := by
  have hbp : shape.bpCode.length = 1024 := by
    rw [CartesianShape.bpCode_length, hsize]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [canonicalBPRelativeSummaryBase, canonicalBPRelativeSummaryBlockSizeRaw,
      canonicalBPRelativeSummaryBlocksPerSuperRaw, canonicalBPRelativeSummaryBlockCountRaw,
      canonicalBPRelativeSummarySuperCountRaw, canonicalBPRelativeSummarySuperWidth,
      canonicalBPRelativeSummaryRelativeWidthRaw, canonicalBPRelativeSummarySuperSlots,
      canonicalBPRelativeSummaryBlockSlots, bpSuperblockSpan,
      SuccinctSpace.sampledDirectoryOverhead, SuccinctSpace.logLogSampledDirectoryOverhead,
      SuccinctRank.machineWordBits, hsize, hbp, log2_512, log2_1024, log2_10]

theorem blockSize_at_512 {shape : CartesianShape} (hsize : shape.size = 512) :
    canonicalBPRelativeSummaryBlockSize shape = 20 := by
  simp [canonicalBPRelativeSummaryBlockSize, active_at_512 hsize,
    canonicalBPRelativeSummaryBlockSizeRaw, canonicalBPRelativeSummaryBase, hsize, log2_512]

theorem blockCount_at_512 {shape : CartesianShape} (hsize : shape.size = 512) :
    canonicalBPRelativeSummaryBlockCount shape = 51 := by
  simp [canonicalBPRelativeSummaryBlockCount, active_at_512 hsize,
    canonicalBPRelativeSummaryBlockCountRaw, canonicalBPRelativeSummaryBase, hsize, log2_512]

theorem blocksPerSuper_at_512 {shape : CartesianShape} (hsize : shape.size = 512) :
    canonicalBPRelativeSummaryBlocksPerSuper shape = 10 := by
  simp [canonicalBPRelativeSummaryBlocksPerSuper, active_at_512 hsize,
    canonicalBPRelativeSummaryBlocksPerSuperRaw, canonicalBPRelativeSummaryBase, hsize, log2_512]

/-- **THE MODEL SPLIT, exactly.**  At `n = 511` the summary block size is `0`
and at `n = 512` it is `20`, for every shape of that size. -/
theorem model_split_at_512
    (small large : CartesianShape) (hs : small.size = 511) (hl : large.size = 512) :
    canonicalBPRelativeSummaryBlockSize small = 0 /\
      canonicalBPRelativeSummaryBlockSize large = 20 :=
  ⟨blockSize_eq_zero_of_size_lt_512 (by omega), blockSize_at_512 hl⟩

/-! ### Non-vacuity: shapes of every size exist -/

def spine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | n + 1 => CartesianShape.node (spine n) CartesianShape.empty

theorem spine_size (n : Nat) : (spine n).size = n := by
  induction n with
  | zero => rfl
  | succ k ih => simp [spine, CartesianShape.size, ih, CartesianShape.size]

/-! ### PHYSICAL consequence: four store segments are EMPTY below 512

`RMQ/Core/SuccinctFinal/RAM/FlatPayload.lean:881-943` proves the same four facts
under a `¬ Active` hypothesis; here that hypothesis is discharged by size alone. -/

theorem summaryBaselineWords_empty_of_size_lt_512 {shape : CartesianShape}
    (hsize : shape.size < 512) :
    (concreteBPRelativeMinMaxArgSummaryTable_canonical shape).baselineTable.store.words
      = #[] := by
  simp [concreteBPRelativeMinMaxArgSummaryTable_canonical,
    concreteBPRelativeMinMaxArgSummaryTable, canonicalBPRelativeSummaryBlockCount,
    canonicalBPRelativeSummarySuperCount, bpSuperblockBaselineEntries,
    SuccinctSpace.FixedWidthNatTable.ofEntries,
    SuccinctSpace.FixedWidthNatTable.ofEncodedWords,
    not_active_of_size_lt_512 hsize]

theorem summaryMinRelWords_empty_of_size_lt_512 {shape : CartesianShape}
    (hsize : shape.size < 512) :
    (concreteBPRelativeMinMaxArgSummaryTable_canonical shape).minRelTable.store.words
      = #[] := by
  simp [concreteBPRelativeMinMaxArgSummaryTable_canonical,
    concreteBPRelativeMinMaxArgSummaryTable, canonicalBPRelativeSummaryBlockCount,
    canonicalBPRelativeSummarySuperCount, bpBlockRelativeMinExcessEntries,
    SuccinctSpace.FixedWidthNatTable.ofEntries,
    SuccinctSpace.FixedWidthNatTable.ofEncodedWords,
    not_active_of_size_lt_512 hsize]

theorem summaryMaxRelWords_empty_of_size_lt_512 {shape : CartesianShape}
    (hsize : shape.size < 512) :
    (concreteBPRelativeMinMaxArgSummaryTable_canonical shape).maxRelTable.store.words
      = #[] := by
  simp [concreteBPRelativeMinMaxArgSummaryTable_canonical,
    concreteBPRelativeMinMaxArgSummaryTable, canonicalBPRelativeSummaryBlockCount,
    canonicalBPRelativeSummarySuperCount, bpBlockRelativeMaxExcessEntries,
    SuccinctSpace.FixedWidthNatTable.ofEntries,
    SuccinctSpace.FixedWidthNatTable.ofEncodedWords,
    not_active_of_size_lt_512 hsize]

theorem summaryArgOffsetWords_empty_of_size_lt_512 {shape : CartesianShape}
    (hsize : shape.size < 512) :
    (concreteBPRelativeMinMaxArgSummaryTable_canonical shape).argOffsetTable.store.words
      = #[] := by
  simp [concreteBPRelativeMinMaxArgSummaryTable_canonical,
    concreteBPRelativeMinMaxArgSummaryTable, canonicalBPRelativeSummaryBlockCount,
    canonicalBPRelativeSummarySuperCount, bpBlockArgMinLocalOffsetEntries,
    SuccinctSpace.FixedWidthNatTable.ofEntries,
    SuccinctSpace.FixedWidthNatTable.ofEncodedWords,
    not_active_of_size_lt_512 hsize]

/-! ### Boundary shapes: `n = 0` and `n = 1` are unique -/

/-- `EG-CP-F11` "empty representation": size `0` pins the shape completely. -/
theorem size_zero_iff_empty (shape : CartesianShape) :
    shape.size = 0 ↔ shape = CartesianShape.empty := by
  constructor
  · intro h
    cases shape with
    | empty => rfl
    | node l r => simp [CartesianShape.size] at h
  · intro h; subst h; rfl

/-- `EG-CP-F11` "singleton": size `1` pins the shape completely. -/
theorem size_one_iff_singleton (shape : CartesianShape) :
    shape.size = 1 ↔ shape = CartesianShape.node CartesianShape.empty CartesianShape.empty := by
  constructor
  · intro h
    cases shape with
    | empty => simp [CartesianShape.size] at h
    | node l r =>
        simp [CartesianShape.size] at h
        have hl : l.size = 0 := by omega
        have hr : r.size = 0 := by omega
        rw [(size_zero_iff_empty l).mp hl, (size_zero_iff_empty r).mp hr]
  · intro h; subst h; rfl

/-- At `n = 0` the frozen cell is ONE BIT wide.  Uniform, but extreme: this is
the smallest cell the packed model ever allocates. -/
theorem frozenWordWidth_zero_is_one_bit : frozenWordWidth 0 = 1 := frozenWordWidth_zero

theorem log2_mono {a b : Nat} (h : a <= b) : Nat.log2 a <= Nat.log2 b := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · rw [ha, log2_zero]; omega
  · have hane : a ≠ 0 := by omega
    have hbne : b ≠ 0 := by omega
    exact (Nat.le_log2 hbne).mpr (Nat.le_trans (Nat.log2_self_le hane) h)

theorem frozenWordWidth_mono {m n : Nat} (h : m <= n) :
    frozenWordWidth m <= frozenWordWidth n := by
  simp only [frozenWordWidth, SuccinctRank.machineWordBits]
  have := log2_mono (a := 2 * m) (b := 2 * n) (by omega)
  omega

/-! ## 4. `concreteBPRelativeRmmInteriorReady` is NOT monotone in `n`

`Ready` is `Active` plus `base * base <= blockCount`.  Both are size-only, and
the second conjunct is not monotone because `base` jumps at powers of two. -/

theorem ready_iff {shape : CartesianShape} :
    concreteBPRelativeRmmInteriorReady shape ↔
      (canonicalBPRelativeMinMaxArgSummaryTableActive shape /\
        (Nat.log2 shape.size + 1) * (Nat.log2 shape.size + 1) <=
          shape.size / (Nat.log2 shape.size + 1)) := by
  constructor
  · rintro ⟨hactive, hle⟩
    refine ⟨hactive, ?_⟩
    simpa [concreteBPRelativeRmmInteriorMacroSize, canonicalBPRelativeSummaryBase,
      canonicalBPRelativeSummaryBlockCount, canonicalBPRelativeSummaryBlockCountRaw,
      hactive] using hle
  · rintro ⟨hactive, hle⟩
    refine ⟨hactive, ?_⟩
    simpa [concreteBPRelativeRmmInteriorMacroSize, canonicalBPRelativeSummaryBase,
      canonicalBPRelativeSummaryBlockCount, canonicalBPRelativeSummaryBlockCountRaw,
      hactive] using hle

theorem active_of_size_eq {shape : CartesianShape} {n : Nat} (hsize : shape.size = n)
    (hn : 512 <= n) (hn2 : n < 1024) :
    canonicalBPRelativeMinMaxArgSummaryTableActive shape := by
  have hbp : shape.bpCode.length = 2 * n := by
    rw [CartesianShape.bpCode_length, hsize]
  have hlog : Nat.log2 n = 9 := log2_lit (by simpa using hn) (by simpa using hn2)
  have hlog2 : Nat.log2 (2 * n) = 10 := log2_lit (by simp; omega) (by simp; omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [canonicalBPRelativeSummaryBase, canonicalBPRelativeSummaryBlockSizeRaw,
      canonicalBPRelativeSummaryBlocksPerSuperRaw, canonicalBPRelativeSummaryBlockCountRaw,
      canonicalBPRelativeSummarySuperCountRaw, canonicalBPRelativeSummarySuperWidth,
      canonicalBPRelativeSummaryRelativeWidthRaw, canonicalBPRelativeSummarySuperSlots,
      canonicalBPRelativeSummaryBlockSlots, bpSuperblockSpan,
      SuccinctSpace.sampledDirectoryOverhead, SuccinctSpace.logLogSampledDirectoryOverhead,
      SuccinctRank.machineWordBits, hsize, hbp, hlog, hlog2, log2_10] <;>
    omega

theorem ready_at_1000 {shape : CartesianShape} (hsize : shape.size = 1000) :
    concreteBPRelativeRmmInteriorReady shape := by
  have hlog : Nat.log2 1000 = 9 := log2_lit (by decide) (by decide)
  refine ready_iff.mpr ⟨active_of_size_eq hsize (by omega) (by omega), ?_⟩
  rw [hsize, hlog]
  decide

theorem not_ready_at_999 {shape : CartesianShape} (hsize : shape.size = 999) :
    ¬ concreteBPRelativeRmmInteriorReady shape := by
  have hlog : Nat.log2 999 = 9 := log2_lit (by decide) (by decide)
  intro hready
  have h := (ready_iff.mp hready).2
  rw [hsize, hlog] at h
  omega

theorem ready_at_1023 {shape : CartesianShape} (hsize : shape.size = 1023) :
    concreteBPRelativeRmmInteriorReady shape := by
  have hlog : Nat.log2 1023 = 9 := log2_lit (by decide) (by decide)
  refine ready_iff.mpr ⟨active_of_size_eq hsize (by omega) (by omega), ?_⟩
  rw [hsize, hlog]
  decide

theorem not_ready_at_1024 {shape : CartesianShape} (hsize : shape.size = 1024) :
    ¬ concreteBPRelativeRmmInteriorReady shape := by
  intro hready
  have h := (ready_iff.mp hready).2
  rw [hsize, log2_1024] at h
  omega

theorem not_ready_at_1330 {shape : CartesianShape} (hsize : shape.size = 1330) :
    ¬ concreteBPRelativeRmmInteriorReady shape := by
  have hlog : Nat.log2 1330 = 10 := log2_lit (by decide) (by decide)
  intro hready
  have h := (ready_iff.mp hready).2
  rw [hsize, hlog] at h
  omega

/-! ### The THIRD arm: active but not ready, at `n = 512` -/

theorem not_ready_at_512 {shape : CartesianShape} (hsize : shape.size = 512) :
    ¬ concreteBPRelativeRmmInteriorReady shape := by
  intro hready
  have h := (ready_iff.mp hready).2
  rw [hsize, log2_512] at h
  omega

/-- At `n = 512` the interior directory payload is the summary table ALONE:
neither the `n < 512` empty arm nor the `n >= 1000` full arm. -/
theorem interiorPayloadLength_summary_only_at_512
    {shape : CartesianShape} (hsize : shape.size = 512) :
    concreteBPRelativeRmmInteriorDirectoryPayloadLength shape =
      (concreteBPRelativeMinMaxArgSummaryTable_canonical shape).payload.length :=
  concreteBPRelativeRmmInteriorDirectoryPayloadLength_eq_summary_of_active_not_ready
    (active_at_512 hsize) (not_ready_at_512 hsize)

/-- **NON-MONOTONE**: ready at 1023, NOT ready at 1024, and not ready again all
the way to 1330.  This is a second, independent model split. -/
theorem ready_not_monotone
    (a b : CartesianShape) (ha : a.size = 1023) (hb : b.size = 1024) :
    concreteBPRelativeRmmInteriorReady a /\ ¬ concreteBPRelativeRmmInteriorReady b :=
  ⟨ready_at_1023 ha, not_ready_at_1024 hb⟩

/-! ## 5. `superIsLong` cannot fire below bit-length 10977

`superIsLong bits target slot` is `decide (superLongSpan bits.length < superSpan ...)`
and `superSpan <= bits.length`, so `superLongSpan m < m` is NECESSARY. -/

open RMQ.GenericSelect in
theorem superLongSpan_ge_at_10976 : 10976 <= GenericSelect.superLongSpan 10976 := by
  have h1 : Nat.log2 10976 = 13 := log2_lit (by decide) (by decide)
  have h2 : Nat.log2 14 = 3 := log2_lit (by decide) (by decide)
  simp [GenericSelect.superLongSpan, GenericSelect.superStride, GenericSelect.wordBits,
    GenericSelect.ell, SuccinctRank.machineWordBits, h1, h2]

open RMQ.GenericSelect in
theorem superLongSpan_lt_at_10977 : GenericSelect.superLongSpan 10977 < 10977 := by
  have h1 : Nat.log2 10977 = 13 := log2_lit (by decide) (by decide)
  have h2 : Nat.log2 14 = 3 := log2_lit (by decide) (by decide)
  simp [GenericSelect.superLongSpan, GenericSelect.superStride, GenericSelect.wordBits,
    GenericSelect.ell, SuccinctRank.machineWordBits, h1, h2]

theorem superLongSpan_closed (m : Nat) :
    GenericSelect.superLongSpan m =
      (Nat.log2 m + 1) * (Nat.log2 m + 1) * (Nat.log2 m + 1) *
        (Nat.log2 (Nat.log2 m + 1) + 1) := rfl

/-- For every bit length at most `10976` the long-span threshold is at least the
whole bit vector, so `superIsLong` cannot fire.  Proved, not assumed. -/
theorem superLongSpan_ge_self_of_le {m : Nat} (hm : m <= 10976) :
    m <= GenericSelect.superLongSpan m := by
  rw [superLongSpan_closed]
  rcases Nat.eq_zero_or_pos m with hz | hp
  · omega
  · have hne : m ≠ 0 := by omega
    have h14 : (2 : Nat) ^ 14 = 16384 := by decide
    have hlt : Nat.log2 m < 14 := (Nat.log2_lt hne).mpr (by rw [h14]; omega)
    have hub : m < 2 ^ (Nat.log2 m + 1) := Nat.lt_log2_self
    obtain ⟨k, hk⟩ : ∃ k, Nat.log2 m = k := ⟨_, rfl⟩
    rw [hk] at hlt hub ⊢
    have e1 : Nat.log2 1 = 0 := log2_one
    have e2 : Nat.log2 2 = 1 := log2_lit (by decide) (by decide)
    have e3 : Nat.log2 3 = 1 := log2_lit (by decide) (by decide)
    have e4 : Nat.log2 4 = 2 := log2_lit (by decide) (by decide)
    have e5 : Nat.log2 5 = 2 := log2_lit (by decide) (by decide)
    have e6 : Nat.log2 6 = 2 := log2_lit (by decide) (by decide)
    have e7 : Nat.log2 7 = 2 := log2_lit (by decide) (by decide)
    have e8 : Nat.log2 8 = 3 := log2_lit (by decide) (by decide)
    have e9 : Nat.log2 9 = 3 := log2_lit (by decide) (by decide)
    have e10 : Nat.log2 10 = 3 := log2_lit (by decide) (by decide)
    have e11 : Nat.log2 11 = 3 := log2_lit (by decide) (by decide)
    have e12 : Nat.log2 12 = 3 := log2_lit (by decide) (by decide)
    have e13 : Nat.log2 13 = 3 := log2_lit (by decide) (by decide)
    have e14 : Nat.log2 14 = 3 := log2_lit (by decide) (by decide)
    have hcases : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/
        k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 := by omega
    rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
      subst h <;>
      simp [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14] at hub ⊢
    all_goals omega

/-- `superIsLong` is FALSE at every in-range super slot whenever the bit length
is at most `10976`.  On a BP code the bit length is `2 * n`, so this covers
every input of size `n <= 5488`. -/
theorem superIsLong_false_of_bitlength_le
    {bits : List Bool} {target : Bool} {superSlot : Nat}
    (hlen : bits.length <= 10976)
    (hslot : superSlot < GenericSelect.superSlotCount bits target) :
    GenericSelect.superIsLong bits target superSlot = false := by
  have hgap := GenericSelect.superSpan_le_next_gap bits target hslot
  have hnext := GenericSelect.position_le_length bits target
    (GenericSelect.superBaseOccurrence bits.length (superSlot + 1))
  have hlong := superLongSpan_ge_self_of_le hlen
  simp [GenericSelect.superIsLong]
  omega

/-- Same statement phrased on the route's BP code. -/
theorem superIsLong_false_of_size_le_5488
    {shape : CartesianShape} {target : Bool} {superSlot : Nat}
    (hsize : shape.size <= 5488)
    (hslot : superSlot < GenericSelect.superSlotCount shape.bpCode target) :
    GenericSelect.superIsLong shape.bpCode target superSlot = false := by
  refine superIsLong_false_of_bitlength_le ?_ hslot
  rw [CartesianShape.bpCode_length]
  omega

/-! ## 6. Sanity: the width function has no small-size branch at all -/

theorem frozenWordWidth_small :
    frozenWordWidth 0 = 1 /\ frozenWordWidth 1 = 2 /\ frozenWordWidth 2 = 3 := by
  refine ⟨frozenWordWidth_zero, frozenWordWidth_one, ?_⟩
  have h : Nat.log2 4 = 2 := log2_lit (by decide) (by decide)
  simp [frozenWordWidth, SuccinctRank.machineWordBits, h]


/-! ############ ADVERSARIAL AUDIT ADDITIONS (aud_) ############ -/

/-! ### A1. Do the "all size" theorems really instantiate at 0 and 1? -/

theorem aud_headerCells_0 : headerCells 0 = 1 := headerCells_eq_one 0
theorem aud_headerCells_1 : headerCells 1 = 1 := headerCells_eq_one 1
theorem aud_fieldFits_0 : headerFieldValue 0 < 2 ^ frozenWordWidth 0 :=
  headerFieldValue_lt_two_pow 0
theorem aud_fieldFits_1 : headerFieldValue 1 < 2 ^ frozenWordWidth 1 :=
  headerFieldValue_lt_two_pow 1
theorem aud_split_0_1 : headerCells 0 = headerCells 1 := headerCells_no_small_split 0 1

/-! ### A2. The contract's THIRD required width inequality (:308-311),
`w(n) <= K_w * (Nat.log2 (n + 1) + 1)`, is ABSENT from the lane's file.
It is true with the literal `K_w = 2`; here is the proof. -/

theorem aud_frozenWordWidth_le_logBound (n : Nat) :
    frozenWordWidth n <= 2 * (Nat.log2 (n + 1) + 1) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [frozenWordWidth, SuccinctRank.machineWordBits, log2_zero, log2_one]
  · have hw : frozenWordWidth n = Nat.log2 n + 2 := by
      simp [frozenWordWidth, SuccinctRank.machineWordBits, log2_two_mul_of_pos hn]
    have hmono : Nat.log2 n <= Nat.log2 (n + 1) := log2_mono (by omega)
    omega

/-- The contract's first two inequalities, restated on the frozen width. -/
theorem aud_one_le_w (n : Nat) : 1 <= frozenWordWidth n := frozenWordWidth_pos n
theorem aud_n_lt_two_pow_w (n : Nat) : n < 2 ^ frozenWordWidth n :=
  headerFieldValue_lt_two_pow n

/-! ### A3. The LOAD-BEARING LINK the lane's file never states: is the invented
`frozenWordWidth` actually the route's own word size? -/

theorem aud_frozenWordWidth_eq_route (shape : CartesianShape) :
    SuccinctFinal.builtRelativeSplitBPCloseRankWordSize shape
      = frozenWordWidth shape.size := by
  simp [SuccinctFinal.builtRelativeSplitBPCloseRankWordSize, frozenWordWidth,
    CartesianShape.bpCode_length]

/-! ### A4. Are the padding budgets PROVED upper bounds, unconditionally? -/

theorem aud_sparse_budget_is_proved_bound (shape : CartesianShape) :
    (SuccinctSelect.builtRelativeSplitFalseSelectSparseExceptionRelativeTable
        shape).payload.length <=
      SuccinctSelect.sparseExceptionRelativeTableOverhead shape.size :=
  SuccinctSelect.builtRelativeSplitFalseSelectSparseExceptionRelativeTable_payload_le_overhead
    shape

theorem aud_long_budget_is_proved_bound (shape : CartesianShape) :
    (SuccinctSelect.builtRelativeSplitFalseSelectLongSuperRelativeTable
        shape).payload.length <=
      SuccinctSelect.compactLongSuperRelativeTableOverhead shape.size :=
  SuccinctSelect.compactLongSuperRelativeTable_payload_le_overhead shape

/-! ### A5. WHAT PADDING TO THOSE BUDGETS COSTS.
The lane recommends `K = 1` + padding and never prices it.  The sparse budget
is `512 * (2n / loglog (2n)) + 512`, which EXCEEDS `n` for every `n` whose
`loglog (2n)` is at most `1024` -- i.e. for every `n < 2 ^ (2 ^ 1023)`. -/

theorem aud_sparse_budget_ge_self (n : Nat)
    (hd : Nat.log2 (Nat.log2 (2 * n) + 1) + 1 <= 1024) :
    n <= SuccinctSelect.sparseExceptionRelativeTableOverhead n := by
  obtain ⟨d, hdef⟩ : ∃ d, Nat.log2 (Nat.log2 (2 * n) + 1) + 1 = d := ⟨_, rfl⟩
  rw [hdef] at hd
  have hdpos : 0 < d := by omega
  have hstep : 2 * n / 1024 <= 2 * n / d := Nat.div_le_div_left hd hdpos
  have hhalf : 2 * n / 1024 = n / 512 := by
    have : (2 : Nat) * n / (2 * 512) = n / 512 := Nat.mul_div_mul_left n 512 (by omega)
    simpa using this
  have hfloor : n - 511 <= 512 * (n / 512) := by
    have h := Nat.div_add_mod n 512
    have hm : n % 512 < 512 := Nat.mod_lt _ (by omega)
    omega
  have hscale : 512 * (n / 512) <= 512 * (2 * n / d) := by
    rw [← hhalf]; exact Nat.mul_le_mul_left 512 hstep
  simp only [SuccinctSelect.sparseExceptionRelativeTableOverhead,
    SuccinctSpace.idDivLogLogOverhead, hdef]
  omega

/-- Concrete: at `n = 1024` the sparse-region padding alone would allocate
`262656` bits, i.e. more than `128` times the whole `2n = 2048`-bit payload. -/
theorem aud_sparse_padding_vs_payload_1024 :
    128 * (2 * 1024) <= SuccinctSelect.sparseExceptionRelativeTableOverhead 1024 := by
  rw [sparse_budget_at_1024]; decide

/-- And the region it would pad is provably EMPTY at that size, because
`superIsLong` cannot fire below `n = 5489`. -/
theorem aud_long_region_empty_at_1024
    {shape : CartesianShape} {target : Bool} {superSlot : Nat}
    (hsize : shape.size = 1024)
    (hslot : superSlot < GenericSelect.superSlotCount shape.bpCode target) :
    GenericSelect.superIsLong shape.bpCode target superSlot = false :=
  superIsLong_false_of_size_le_5488 (by omega) hslot

/-! ### A6. Is `superIsLong_false_of_bitlength_le` VACUOUS?  Its hypothesis
`superSlot < superSlotCount bits target` must be satisfiable on real BP codes. -/

theorem aud_superIsLong_instance_nonvacuous
    {shape : CartesianShape} {target : Bool}
    (hsize : shape.size <= 5488)
    (hpos : 0 < GenericSelect.superSlotCount shape.bpCode target) :
    GenericSelect.superIsLong shape.bpCode target 0 = false :=
  superIsLong_false_of_size_le_5488 hsize hpos

/-! ### A7. Is `n = 0` really a "degenerate arm", or is there simply NO VALID
QUERY at `n = 0`?  `RMQ.ValidRange` (RMQ/Core/Spec.lean:14) is half-open. -/

theorem aud_no_valid_query_at_size_zero (xs : List Int) (hxs : xs.length = 0)
    (left right : Nat) : ¬ RMQ.ValidRange xs left right := by
  rintro ⟨h1, h2⟩; omega

/-- The lane's `q = (0, n)` queries ARE valid for every `n >= 1`, so the
failed-read observation is not an artifact of an out-of-range endpoint. -/
theorem aud_zero_n_is_valid (xs : List Int) (hpos : 0 < xs.length) :
    RMQ.ValidRange xs 0 xs.length := ⟨hpos, Nat.le_refl _⟩

/-! ### A8. The residual the lane names.  Closing it settles CONJUNCT 6 only;
conjuncts 1-5 of `Active` for all `n >= 512` remain scan-only. -/

theorem aud_two_k_add_four_le_two_pow {k : Nat} (hk : 4 <= k) : 2 * k + 4 <= 2 ^ k := by
  induction k with
  | zero => omega
  | succ m ih =>
      rcases Nat.lt_or_ge m 4 with hm | hm
      · have hm3 : m = 3 := by omega
        subst hm3
        decide
      · have := ih (by omega)
        have hpow : (2 : Nat) ^ (m + 1) = 2 ^ m * 2 := Nat.pow_succ 2 m
        omega

/-- `2 * Nat.log2 (a + 1) + 3 <= a` for every `a >= 9`.  This is exactly the
sixth conjunct of `Active` after substituting `a = Nat.log2 n`. -/
theorem aud_conjunct6_residual {a : Nat} (ha : 9 <= a) :
    2 * Nat.log2 (a + 1) + 3 <= a := by
  have hne : a + 1 ≠ 0 := by omega
  have hle : 2 ^ Nat.log2 (a + 1) <= a + 1 := Nat.log2_self_le hne
  rcases Nat.lt_or_ge (Nat.log2 (a + 1)) 4 with hk | hk
  · -- log2 (a+1) <= 3, so 2 * 3 + 3 = 9 <= a
    omega
  · have := aud_two_k_add_four_le_two_pow hk
    omega

/-! ### A9. What "Active for all n >= 512" would still need: the other five
conjuncts.  Only conjunct 3 is provable this cheaply; 1, 2, 4, 5 are not
addressed by the lane at all beyond an `#eval` scan of `[0, 70000)`. -/

theorem aud_conjunct3_all_sizes (shape : CartesianShape) :
    canonicalBPRelativeSummaryBlockSizeRaw shape <
      2 ^ canonicalBPRelativeSummaryRelativeWidthRaw shape := by
  simp only [canonicalBPRelativeSummaryBlockSizeRaw,
    canonicalBPRelativeSummaryRelativeWidthRaw, canonicalBPRelativeSummaryBase]
  obtain ⟨a, hA⟩ : ∃ a, Nat.log2 shape.size = a := ⟨_, rfl⟩
  rw [hA]
  obtain ⟨k, hK⟩ : ∃ k, Nat.log2 (a + 1) = k := ⟨_, rfl⟩
  have hlt : a + 1 < 2 ^ (Nat.log2 (a + 1) + 1) := Nat.lt_log2_self
  rw [hK] at hlt ⊢
  have hpow : (2 : Nat) * 2 ^ (k + 1) = 2 ^ (k + 2) := by
    rw [Nat.pow_succ, Nat.pow_succ]; omega
  have hmono : (2 : Nat) ^ (k + 2) <= 2 ^ (2 * (k + 1) + 3) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  omega

#print axioms aud_headerCells_0
#print axioms aud_fieldFits_0
#print axioms aud_fieldFits_1
#print axioms aud_frozenWordWidth_le_logBound
#print axioms aud_frozenWordWidth_eq_route
#print axioms aud_sparse_budget_is_proved_bound
#print axioms aud_long_budget_is_proved_bound
#print axioms aud_sparse_budget_ge_self
#print axioms aud_sparse_padding_vs_payload_1024
#print axioms aud_long_region_empty_at_1024
#print axioms aud_superIsLong_instance_nonvacuous
#print axioms aud_no_valid_query_at_size_zero
#print axioms aud_zero_n_is_valid
#print axioms aud_conjunct6_residual
#print axioms aud_conjunct3_all_sizes

end PackedHeaderSmall
end RMQ
