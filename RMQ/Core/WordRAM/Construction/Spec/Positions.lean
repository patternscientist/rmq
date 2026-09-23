import RMQ.Core.GenericSelect.Slots

/-!
# PRE-1 S1: one-pass occurrence positions and running ranks

Machine-free specification layer (outside the builder firewall). The access
directories are defined through `Succinct.select` (via `GenericSelect.position`)
and `Succinct.rankPrefix`, each of which rescans the bit list. A linear builder
makes one left-to-right pass instead. This module defines that pass as pure
functions and proves it equal to the reference, for every bit list and target:

* `occurrencePositionsFrom`/`selectFrom_scan`: the list of target positions met
  by the scan is exactly `selectFrom` at every occurrence index;
* `positionFill`/`positionFill_spec`/`position_eq_positionFill`: a scan with a
  running occurrence counter that stores the current position into slot
  `counter` fills slot `k` with `GenericSelect.position bits target k` for
  every `k < occurrenceCount`, and leaves every other slot untouched (the
  reference clamp `bits.length` for `k ≥ occurrenceCount` is a separate store);
* `runningRanksFrom`/`rankPrefix_running`: the running counter after `p`
  positions is `rankPrefix target bits p`;
* `rankSampleFill`/`rankSampleFill_spec`: a scan that stores the running
  counter into slot `q / stride` at every position `q` divisible by `stride`
  (the end position included) fills slot `w` with `rankPrefix target bits
  (w * stride)` exactly when `w * stride ≤ bits.length`; the three canonical
  rank-sample entry lists are maps of such fills
  (`rankSampleEntries_eq_fill`, `canonicalSuperRankEntries_eq_fill`,
  `canonicalBlockRankEntries_eq_fill`, the last one subtracting the saved
  super-boundary sample).

The machine never calls any function of this module; these are the equality
specifications its loop invariants target.
-/

namespace RMQ.SuccinctFinal.PackedConstruction.Spec

open RMQ.Succinct

/-! ## Occurrence positions -/

/-- Positions (counted from `base`) of the `target` bits, in scan order. -/
def occurrencePositionsFrom (target : Bool) : List Bool → Nat → List Nat
  | [], _ => []
  | bit :: rest, base =>
      if bit = target then base :: occurrencePositionsFrom target rest (base + 1)
      else occurrencePositionsFrom target rest (base + 1)

/-- **Select scan.** `selectFrom` is indexing into the one-pass position list. -/
theorem selectFrom_scan (target : Bool) :
    ∀ (bits : List Bool) (base occurrence : Nat),
      selectFrom target bits base occurrence =
        (occurrencePositionsFrom target bits base)[occurrence]?
  | [], base, occurrence => rfl
  | bit :: rest, base, occurrence => by
      by_cases hbit : bit = target
      · cases occurrence with
        | zero => simp [selectFrom, occurrencePositionsFrom, hbit]
        | succ k =>
            simp only [selectFrom, occurrencePositionsFrom, hbit, if_true,
              Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, List.getElem?_cons_succ]
            exact selectFrom_scan target rest (base + 1) k
      · simp only [selectFrom, occurrencePositionsFrom, hbit, if_false]
        exact selectFrom_scan target rest (base + 1) occurrence

theorem occurrencePositionsFrom_length (target : Bool) :
    ∀ (bits : List Bool) (base : Nat),
      (occurrencePositionsFrom target bits base).length =
        rankPrefix target bits bits.length
  | [], base => by simp [occurrencePositionsFrom, rankPrefix_nil]
  | bit :: rest, base => by
      have ih := occurrencePositionsFrom_length target rest (base + 1)
      by_cases hbit : bit = target
      · simp only [occurrencePositionsFrom, hbit, if_true, List.length_cons, ih,
          List.length_cons, rankPrefix]
        omega
      · simp only [occurrencePositionsFrom, hbit, if_false, ih, List.length_cons, rankPrefix]
        omega

/-- The reference `position` (select with the `bits.length` clamp) from the scan. -/
theorem position_eq_scan (bits : List Bool) (target : Bool) (k : Nat) :
    GenericSelect.position bits target k =
      ((occurrencePositionsFrom target bits 0)[k]?).getD bits.length := by
  unfold GenericSelect.position select
  rw [selectFrom_scan]

/-- A scan with a running occurrence counter `c` at position `p` that stores `p`
into slot `c` at each `target` bit. -/
def positionFill (target : Bool) : List Bool → Nat → Nat → (Nat → Nat) → Nat → Nat
  | [], _, _, arr => arr
  | bit :: rest, p, c, arr =>
      if bit = target then
        positionFill target rest (p + 1) (c + 1) (fun i => if i = c then p else arr i)
      else positionFill target rest (p + 1) c arr

theorem positionFill_general (target : Bool) :
    ∀ (bits : List Bool) (p c : Nat) (arr : Nat → Nat) (k : Nat),
      positionFill target bits p c arr k =
        if c ≤ k then ((occurrencePositionsFrom target bits p)[k - c]?).getD (arr k)
        else arr k
  | [], p, c, arr, k => by simp [positionFill, occurrencePositionsFrom]
  | bit :: rest, p, c, arr, k => by
      have ih := positionFill_general target rest
      by_cases hbit : bit = target
      · simp only [positionFill, occurrencePositionsFrom, hbit, if_true]
        rw [ih]
        by_cases hkc : k = c
        · subst hkc
          have hnot : ¬ (k + 1 ≤ k) := by omega
          simp [hnot]
        · by_cases hlt : c < k
          · have h1 : c + 1 ≤ k := hlt
            have h2 : k - c = (k - (c + 1)) + 1 := by omega
            simp [h1, Nat.le_of_lt hlt, hkc, h2]
          · have h1 : ¬ c + 1 ≤ k := by omega
            have h2 : ¬ c ≤ k := by omega
            simp [h1, h2, hkc]
      · simp only [positionFill, occurrencePositionsFrom, hbit, if_false]
        exact ih (p + 1) c arr k

/-- **Position fill.** Scanning all of `bits` from position 0 with counter 0
fills slot `k` with the reference position for every occurrence index below the
occurrence count, and leaves every other slot unchanged. -/
theorem positionFill_spec (bits : List Bool) (target : Bool) (arr : Nat → Nat) (k : Nat) :
    positionFill target bits 0 0 arr k =
      if k < GenericSelect.occurrenceCount bits target then
        GenericSelect.position bits target k
      else arr k := by
  rw [positionFill_general, position_eq_scan]
  simp only [Nat.zero_le, if_true, Nat.sub_zero]
  have hlen := occurrencePositionsFrom_length target bits 0
  unfold GenericSelect.occurrenceCount
  by_cases hk : k < rankPrefix target bits bits.length
  · have hk' : k < (occurrencePositionsFrom target bits 0).length := by omega
    simp [hk, List.getElem?_eq_getElem hk']
  · have hk' : (occurrencePositionsFrom target bits 0).length ≤ k := by omega
    simp [hk, List.getElem?_eq_none hk']

/-- The reference clamp beyond the occurrence count. -/
theorem position_of_occurrenceCount_le (bits : List Bool) (target : Bool) {k : Nat}
    (hk : GenericSelect.occurrenceCount bits target ≤ k) :
    GenericSelect.position bits target k = bits.length := by
  rw [position_eq_scan]
  have hlen := occurrencePositionsFrom_length target bits 0
  unfold GenericSelect.occurrenceCount at hk
  have hk' : (occurrencePositionsFrom target bits 0).length ≤ k := by omega
  simp [List.getElem?_eq_none hk']

/-- **Clamped position from the fill.** Every reference call
`GenericSelect.position bits target k` (the directory entries also call it at
occurrence indices at or beyond the occurrence count) is one comparison with the
occurrence count followed by either the filled slot or the constant
`bits.length`, so the entry arithmetic over positions is O(1) per call. -/
theorem position_eq_fill_or_length (bits : List Bool) (target : Bool) (arr : Nat → Nat)
    (k : Nat) :
    GenericSelect.position bits target k =
      if k < GenericSelect.occurrenceCount bits target then positionFill target bits 0 0 arr k
      else bits.length := by
  by_cases hk : k < GenericSelect.occurrenceCount bits target
  · rw [if_pos hk, positionFill_spec, if_pos hk]
  · rw [if_neg hk, position_of_occurrenceCount_le bits target (by omega)]

/-! ## Running ranks -/

/-- The running counter values before each position and at the end, starting
from `c`. -/
def runningRanksFrom (target : Bool) : List Bool → Nat → List Nat
  | [], c => [c]
  | bit :: rest, c => c :: runningRanksFrom target rest (c + if bit = target then 1 else 0)

theorem runningRanksFrom_length (target : Bool) :
    ∀ (bits : List Bool) (c : Nat), (runningRanksFrom target bits c).length = bits.length + 1
  | [], c => rfl
  | bit :: rest, c => by
      simp [runningRanksFrom, runningRanksFrom_length target rest]

/-- **Running rank.** After `p ≤ bits.length` scan positions the counter started
at `c` holds `c + rankPrefix target bits p`. -/
theorem rankPrefix_running (target : Bool) :
    ∀ (bits : List Bool) (c p : Nat), p ≤ bits.length →
      (runningRanksFrom target bits c)[p]? = some (c + rankPrefix target bits p)
  | [], c, p, hp => by
      have : p = 0 := by simpa using hp
      subst this
      simp [runningRanksFrom, rankPrefix_zero]
  | bit :: rest, c, 0, _ => by simp [runningRanksFrom, rankPrefix_zero]
  | bit :: rest, c, p + 1, hp => by
      have hp' : p ≤ rest.length := by simpa using hp
      simp only [runningRanksFrom, List.getElem?_cons_succ]
      rw [rankPrefix_running target rest _ p hp']
      simp only [rankPrefix, Option.some.injEq]
      omega

/-- A scan that, at every position `q` divisible by `stride` (the end position
included), stores the running counter into slot `q / stride`. -/
def rankSampleFill (target : Bool) (stride : Nat) :
    List Bool → Nat → Nat → (Nat → Nat) → Nat → Nat
  | [], p, c, arr =>
      if p % stride = 0 then (fun i => if i = p / stride then c else arr i) else arr
  | bit :: rest, p, c, arr =>
      rankSampleFill target stride rest (p + 1) (c + if bit = target then 1 else 0)
        (if p % stride = 0 then (fun i => if i = p / stride then c else arr i) else arr)

theorem sample_slot_iff {stride : Nat} (hs : 0 < stride) (p w : Nat) :
    (p % stride = 0 ∧ p / stride = w) ↔ p = w * stride := by
  constructor
  · rintro ⟨hmod, hdiv⟩
    have h := Nat.div_add_mod p stride
    rw [hmod, hdiv, Nat.add_zero, Nat.mul_comm] at h
    exact h.symm
  · rintro rfl
    exact ⟨Nat.mul_mod_left w stride, Nat.mul_div_cancel w hs⟩

theorem update_slot_apply {stride : Nat} (hs : 0 < stride) (p c w : Nat) (arr : Nat → Nat) :
    (if p % stride = 0 then (fun i => if i = p / stride then c else arr i) else arr) w =
      if p = w * stride then c else arr w := by
  by_cases h : p = w * stride
  · subst h
    have hm : w * stride % stride = 0 := Nat.mul_mod_left w stride
    have hd : w * stride / stride = w := Nat.mul_div_cancel w hs
    simp [hm, hd]
  · by_cases hm : p % stride = 0
    · have hne : ¬ w = p / stride := by
        intro hw
        exact h ((sample_slot_iff hs p w).mp ⟨hm, hw.symm⟩)
      simp [hm, hne, h]
    · simp [hm, h]

theorem rankSampleFill_general (target : Bool) {stride : Nat} (hs : 0 < stride) :
    ∀ (bits : List Bool) (p c : Nat) (arr : Nat → Nat) (w : Nat),
      rankSampleFill target stride bits p c arr w =
        if p ≤ w * stride ∧ w * stride ≤ p + bits.length then
          c + rankPrefix target bits (w * stride - p)
        else arr w
  | [], p, c, arr, w => by
      simp only [rankSampleFill, List.length_nil, Nat.add_zero]
      rw [update_slot_apply hs]
      by_cases h : p = w * stride
      · subst h
        simp [rankPrefix_zero]
      · have : ¬ (p ≤ w * stride ∧ w * stride ≤ p) := by omega
        simp [h, this]
  | bit :: rest, p, c, arr, w => by
      simp only [rankSampleFill]
      rw [rankSampleFill_general target hs rest, update_slot_apply hs]
      simp only [List.length_cons]
      by_cases heq : p = w * stride
      · subst heq
        have h1 : ¬ (w * stride + 1 ≤ w * stride ∧
            w * stride ≤ w * stride + 1 + rest.length) := by omega
        have h2 : w * stride ≤ w * stride ∧ w * stride ≤ w * stride + (rest.length + 1) := by
          omega
        simp [h1, h2, rankPrefix_zero]
      · by_cases hlt : w * stride < p
        · have h1 : ¬ (p + 1 ≤ w * stride ∧ w * stride ≤ p + 1 + rest.length) := by omega
          have h2 : ¬ (p ≤ w * stride ∧ w * stride ≤ p + (rest.length + 1)) := by omega
          simp [h1, h2, heq]
        · have hgt : p + 1 ≤ w * stride := by omega
          by_cases hend : w * stride ≤ p + 1 + rest.length
          · have h2 : p ≤ w * stride ∧ w * stride ≤ p + (rest.length + 1) := by omega
            have hsub : w * stride - p = (w * stride - (p + 1)) + 1 := by omega
            simp only [hgt, hend, and_self, if_true, h2, hsub, rankPrefix]
            omega
          · have h2 : ¬ (p ≤ w * stride ∧ w * stride ≤ p + (rest.length + 1)) := by omega
            simp [hend, h2, heq]

/-- **Sampled running rank.** Scanning all of `bits` from position 0 with
counter 0 fills slot `w` with `rankPrefix target bits (w * stride)` whenever
`w * stride ≤ bits.length` and leaves every other slot unchanged. -/
theorem rankSampleFill_spec (target : Bool) {stride : Nat} (hs : 0 < stride)
    (bits : List Bool) (arr : Nat → Nat) (w : Nat) :
    rankSampleFill target stride bits 0 0 arr w =
      if w * stride ≤ bits.length then rankPrefix target bits (w * stride) else arr w := by
  rw [rankSampleFill_general target hs]
  simp

theorem mul_le_of_le_div' {w len stride : Nat} (hs : 0 < stride) (h : w ≤ len / stride) :
    w * stride ≤ len :=
  (Nat.le_div_iff_mul_le hs).mp h

/-- The reference word-boundary rank samples are one sampled fill. -/
theorem rankSampleEntries_eq_fill (target : Bool) (bits : List Bool) {wordSize : Nat}
    (hw : 0 < wordSize) (arr : Nat → Nat) :
    SuccinctRank.rankSampleEntries target bits wordSize =
      (List.range (bits.length / wordSize + 1)).map
        (rankSampleFill target wordSize bits 0 0 arr) := by
  unfold SuccinctRank.rankSampleEntries
  apply List.map_congr_left
  intro i hi
  have hi' : i ≤ bits.length / wordSize := by
    have := List.mem_range.mp hi
    omega
  rw [rankSampleFill_spec target hw, if_pos (mul_le_of_le_div' hw hi')]

/-- The canonical super samples are a sampled fill at stride
`blocksPerSuper * wordSize`. -/
theorem canonicalSuperRankEntries_eq_fill (target : Bool) (bits : List Bool)
    {wordSize blocksPerSuper : Nat} (hw : 0 < wordSize) (hb : 0 < blocksPerSuper)
    (arr : Nat → Nat) :
    SuccinctRank.canonicalSuperRankEntries target bits wordSize blocksPerSuper =
      (List.range (bits.length / wordSize / blocksPerSuper + 1)).map
        (rankSampleFill target (blocksPerSuper * wordSize) bits 0 0 arr) := by
  unfold SuccinctRank.canonicalSuperRankEntries
  apply List.map_congr_left
  intro s hs
  have hpos : 0 < blocksPerSuper * wordSize := Nat.mul_pos hb hw
  have hs' : s ≤ bits.length / (blocksPerSuper * wordSize) := by
    have := List.mem_range.mp hs
    rw [Nat.div_div_eq_div_mul, Nat.mul_comm wordSize] at this
    omega
  rw [rankSampleFill_spec target hpos, if_pos (mul_le_of_le_div' hpos hs'), Nat.mul_assoc]

/-- The canonical block samples are the word-boundary fill minus the saved
super-boundary fill. -/
theorem canonicalBlockRankEntries_eq_fill (target : Bool) (bits : List Bool)
    {wordSize blocksPerSuper : Nat} (hw : 0 < wordSize) (hb : 0 < blocksPerSuper)
    (arr arr' : Nat → Nat) :
    SuccinctRank.canonicalBlockRankEntries target bits wordSize blocksPerSuper =
      (List.range (bits.length / wordSize + 1)).map
        (fun w => rankSampleFill target wordSize bits 0 0 arr w -
          rankSampleFill target (blocksPerSuper * wordSize) bits 0 0 arr'
            (w / blocksPerSuper)) := by
  unfold SuccinctRank.canonicalBlockRankEntries
  apply List.map_congr_left
  intro w hwmem
  have hpos : 0 < blocksPerSuper * wordSize := Nat.mul_pos hb hw
  have hw' : w ≤ bits.length / wordSize := by
    have := List.mem_range.mp hwmem
    omega
  have hwle : w * wordSize ≤ bits.length := mul_le_of_le_div' hw hw'
  have hsuper : w / blocksPerSuper * (blocksPerSuper * wordSize) ≤ bits.length := by
    have h1 : w / blocksPerSuper * blocksPerSuper ≤ w := Nat.div_mul_le_self w blocksPerSuper
    have h2 := Nat.mul_le_mul_right wordSize h1
    rw [← Nat.mul_assoc]
    omega
  rw [rankSampleFill_spec target hw, if_pos hwle, rankSampleFill_spec target hpos,
    if_pos hsuper, Nat.mul_assoc]

end RMQ.SuccinctFinal.PackedConstruction.Spec
