import RMQ.Core.SuccinctSpace.Asymptotics

/-!
# Two-level sampled-layout budget (reusable `o(n)` accounting)

A reusable packaging of the "scale-matched, two-level layout" accounting that
succinct directories rely on, isolated so that spokes (plain rank/select,
compressed/FID rank/select, BP navigation) consume one lemma instead of
re-deriving the `o(n)` bound and re-hitting the *uniform-width* / *single-level*
obstructions recorded in `docs/DESIGN_FRONTIER_OBSTRUCTIONS.md`.

Two pieces, both phrased against the existing `SuccinctSpace.LittleOLinear`
predicate (`scale * f n <= n` eventually, i.e. genuine little-o of `n`):

1. **Route/sample side.** `twoLevelLayoutOverhead` — a superblock level stored at
   full machine-word width but with few entries, plus a block level stored at a
   narrow `log log`-scale width with many entries — is `LittleOLinear`. This is
   the positive counterpart of
   `RankSelectPublic.noFixedWeightAmbientTableRAMLogChunkRouteDirectoryFamilyRouteWidthClassLength`:
   the two levels must use two *different* widths; storing both at the wide route
   width is linear.

2. **Shared-table side.** `subLogBlockSize n = floor (log2 n / 2)` makes the
   universal in-block decode/rank table's row count `2 ^ B` satisfy
   `(2 ^ B)^2 <= n`, i.e. at most `sqrt n` rows. This is the structural reason a
   single shared decode table can be `o(n)`. Contrast a *full*-log block, whose
   row count is `2 ^ (log2 n + 1) >= n` — exactly what
   `RankSelectPublic.noFixedWeightLogChunkDenseDecoderLittleO` rules out. So the
   dense-decoder obstruction is removed by *shrinking the block*, not by a new
   table design.
-/

namespace RMQ

namespace SuccinctSpace

/--
Two-level layout overhead: `superSlots` superblock fields at full sampled-directory
width plus `blockSlots` block fields at the narrow `log log` width.
-/
def twoLevelLayoutOverhead (superSlots blockSlots : Nat) (n : Nat) : Nat :=
  sampledDirectoryOverhead superSlots n +
    logLogSampledDirectoryOverhead blockSlots n

/-- The two-level layout overhead is `o(n)`: the reusable route/sample accounting
harness. A single instance serves any two-level succinct directory. -/
theorem twoLevelLayoutOverhead_littleO (superSlots blockSlots : Nat) :
    LittleOLinear (twoLevelLayoutOverhead superSlots blockSlots) := by
  unfold twoLevelLayoutOverhead
  exact (sampledDirectoryOverhead_littleO superSlots).add
    (logLogSampledDirectoryOverhead_littleO blockSlots)

/-- Sub-log in-block decode unit: half the bit length. -/
def subLogBlockSize (n : Nat) : Nat := Nat.log2 n / 2

/--
Structural crux of the compressed-FID fix: with a sub-log block, the universal
decode/rank table's row count `2 ^ subLogBlockSize n` has square at most `n`
(so it is at most `sqrt n`). This is why a single shared table can be `o(n)`,
unlike at a full-log block where the row count is already `>= n`.
-/
theorem two_pow_subLogBlockSize_sq_le (n : Nat) (hn : 1 <= n) :
    2 ^ subLogBlockSize n * 2 ^ subLogBlockSize n <= n := by
  have hpow : 2 ^ Nat.log2 n <= n := Nat.log2_self_le (by omega)
  have hsum : subLogBlockSize n + subLogBlockSize n <= Nat.log2 n := by
    unfold subLogBlockSize; omega
  calc
    2 ^ subLogBlockSize n * 2 ^ subLogBlockSize n
        = 2 ^ (subLogBlockSize n + subLogBlockSize n) := by
          rw [Nat.pow_add]
    _ <= 2 ^ Nat.log2 n := Nat.pow_le_pow_right (by omega) hsum
    _ <= n := hpow

/--
The sub-log universal-table row count is `o(n)`: `n ↦ 2 ^ subLogBlockSize n` is
`LittleOLinear`. This is the positive theorem the dense-decoder obstruction asked
for — a single shared decode table over sub-log blocks fits in `o(n)` bits-worth
of rows, whereas a full-log block forces `>= n` rows.
-/
theorem subLogBlockTableRows_littleO :
    LittleOLinear (fun n => 2 ^ subLogBlockSize n) := by
  intro scale hscale
  refine ⟨2 ^ (2 * scale) + 1, ?_⟩
  intro n hn
  have hle : 2 ^ (2 * scale) <= n := Nat.le_trans (Nat.le_succ _) hn
  have hn1 : 1 <= n := Nat.le_trans (Nat.le_add_left 1 _) hn
  have hsq := two_pow_subLogBlockSize_sq_le n hn1
  have hlog : 2 * scale <= Nat.log2 n := by
    rcases Nat.lt_or_ge (Nat.log2 n) (2 * scale) with hlt | hge
    · exfalso
      have h2 : 2 ^ (Nat.log2 n + 1) <= 2 ^ (2 * scale) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have h3 : n < 2 ^ (Nat.log2 n + 1) := Nat.lt_log2_self
      exact Nat.lt_irrefl n (Nat.lt_of_lt_of_le h3 (Nat.le_trans h2 hle))
    · exact hge
  have hscaleB : scale <= subLogBlockSize n := by
    unfold subLogBlockSize; omega
  have hscalePow : scale <= 2 ^ subLogBlockSize n :=
    Nat.le_trans hscaleB (nat_le_two_pow _)
  calc scale * 2 ^ subLogBlockSize n
      <= 2 ^ subLogBlockSize n * 2 ^ subLogBlockSize n :=
        Nat.mul_le_mul hscalePow (Nat.le_refl _)
    _ <= n := hsq

end SuccinctSpace

end RMQ
