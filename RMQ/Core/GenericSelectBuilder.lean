import RMQ.Core.GenericSelectParams
import RMQ.Core.GenericSelectPrimitives
import RMQ.Core.RankSelectSpec

/-!
# Generic select directory: builder foundation (Tier 2, layer 1)

Generic `(bits : List Bool) (target : Bool)` analogues of the foundational
`builtRectangularFalseSelect*` counts, slot arithmetic, and super-entry
construction from `SuccinctSelectProposal`.

Layering note (validated while scoping): the *slot arithmetic* layer
(`localSlotsPerSuper`, `localSlotInSuperOfGlobal`, `localBaseOccurrence`)
depends on the shape only through the strides, so it is a function of the bit
length `n` alone.  Only the *count* (`occurrenceCount`/`superSlotCount`) and
*entry/position* layers read the bits and fix a `target`.
-/

namespace RMQ.GenericSelect

open RMQ.SuccinctSelectProposal SuccinctSpace SuccinctRankProposal

/-- Number of `target` occurrences in `bits` (the select domain size). -/
def occurrenceCount (bits : List Bool) (target : Bool) : Nat :=
  RMQ.Succinct.rankPrefix target bits bits.length

/-- Number of super slots: `ceil (occurrenceCount / superStride)`. -/
def superSlotCount (bits : List Bool) (target : Bool) : Nat :=
  falseSelectCeilDiv (occurrenceCount bits target) (superStride bits.length)

/-- Local slots reserved per super interval (a function of `n` alone). -/
def localSlotsPerSuper (n : Nat) : Nat :=
  falseSelectLocalSlotsPerSuper (superStride n) (localStride n)

/-- Total local slots. -/
def localSlotCount (bits : List Bool) (target : Bool) : Nat :=
  superSlotCount bits target * localSlotsPerSuper bits.length

theorem localSlotsPerSuper_pos (n : Nat) : 0 < localSlotsPerSuper n := by
  unfold localSlotsPerSuper falseSelectLocalSlotsPerSuper
  exact Nat.div_pos
    (by have := superStride_pos n; omega)
    (localStride_pos n)

/-- Local slot index within its super interval (function of `n`). -/
def localSlotInSuperOfGlobal (n globalLocalSlot : Nat) : Nat :=
  globalLocalSlot -
    (globalLocalSlot / localSlotsPerSuper n) * localSlotsPerSuper n

/-- Base occurrence of a global local slot (function of `n`). -/
def localBaseOccurrence (n globalLocalSlot : Nat) : Nat :=
  let superSlot := globalLocalSlot / localSlotsPerSuper n
  let localSlotInSuper := localSlotInSuperOfGlobal n globalLocalSlot
  superSlot * superStride n + localSlotInSuper * localStride n

theorem localBaseOccurrence_mod (n globalLocalSlot : Nat) :
    localBaseOccurrence n globalLocalSlot =
      (globalLocalSlot / localSlotsPerSuper n) * superStride n +
        (globalLocalSlot % localSlotsPerSuper n) * localStride n := by
  unfold localBaseOccurrence localSlotInSuperOfGlobal
  rw [Nat.mod_eq_sub_div_mul]

/-- Position of the `occurrence`-th `target` bit, clamped to `bits.length`. -/
def position (bits : List Bool) (target : Bool) (occurrence : Nat) : Nat :=
  (RMQ.Succinct.select target bits occurrence).getD bits.length

/-- The BP `false`-specialised occurrence count is the `target := false`
instance over `shape.bpCode`. -/
theorem falseSelectOccurrenceCount_eq (shape : Cartesian.CartesianShape) :
    falseSelectOccurrenceCount shape = occurrenceCount shape.bpCode false :=
  rfl

/-! ## Span / dense-sparse classification layer -/

/-- End occurrence of a local block (exclusive), clamped to the occurrence count. -/
def localEndOccurrence (bits : List Bool) (target : Bool)
    (globalLocalSlot : Nat) : Nat :=
  Nat.min
    (localBaseOccurrence bits.length globalLocalSlot + localStride bits.length)
    (occurrenceCount bits target)

/-- Position span covered by a local block. -/
def localSpan (bits : List Bool) (target : Bool) (globalLocalSlot : Nat) : Nat :=
  let baseOccurrence := localBaseOccurrence bits.length globalLocalSlot
  let endOccurrence := localEndOccurrence bits target globalLocalSlot
  position bits target (endOccurrence - 1) + 1 - position bits target baseOccurrence

/-- A local block is sparse when its position span exceeds one word. -/
def localIsSparse (bits : List Bool) (target : Bool) (globalLocalSlot : Nat) :
    Bool :=
  decide (wordBits bits.length < localSpan bits target globalLocalSlot)

/-- Base occurrence of a super interval (function of `n`). -/
def superBaseOccurrence (n superSlot : Nat) : Nat :=
  superSlot * superStride n

/-- End occurrence of a super interval (exclusive), clamped. -/
def superEndOccurrence (bits : List Bool) (target : Bool) (superSlot : Nat) :
    Nat :=
  Nat.min
    (superBaseOccurrence bits.length superSlot + superStride bits.length)
    (occurrenceCount bits target)

/-- Position span covered by a super interval. -/
def superSpan (bits : List Bool) (target : Bool) (superSlot : Nat) : Nat :=
  let baseOccurrence := superBaseOccurrence bits.length superSlot
  let endOccurrence := superEndOccurrence bits target superSlot
  position bits target (endOccurrence - 1) + 1 - position bits target baseOccurrence

/-- A super interval is "long"/sparse when its span exceeds the long threshold. -/
def superIsLong (bits : List Bool) (target : Bool) (superSlot : Nat) : Bool :=
  decide (superLongSpan bits.length < superSpan bits target superSlot)

/-- The super slot owning a global local slot (function of `n`). -/
def localSuperSlot (n globalLocalSlot : Nat) : Nat :=
  globalLocalSlot / localSlotsPerSuper n

/-- End occurrence of a local block inside a short (dense) super (exclusive). -/
def shortSuperLocalEndOccurrence (bits : List Bool) (target : Bool)
    (globalLocalSlot : Nat) : Nat :=
  Nat.min
    (localBaseOccurrence bits.length globalLocalSlot + localStride bits.length)
    (superEndOccurrence bits target
      (localSuperSlot bits.length globalLocalSlot))

/-- Position span of a local block inside a short super. -/
def shortSuperLocalSpan (bits : List Bool) (target : Bool)
    (globalLocalSlot : Nat) : Nat :=
  let baseOccurrence := localBaseOccurrence bits.length globalLocalSlot
  let endOccurrence := shortSuperLocalEndOccurrence bits target globalLocalSlot
  position bits target (endOccurrence - 1) + 1 - position bits target baseOccurrence

/-! ## Position arithmetic backbone (generic over `Succinct.select`)

All of these mirror the BP `builtRelativeSplitFalseSelectPosition_*` lemmas with
`shape.bpCode -> bits`, `false -> target`, `falseSelectOccurrenceCount ->
occurrenceCount`; the underlying facts (`select_index_mono`,
`select_exists_of_lt_rankPrefix`, `select_none_of_rankPrefix_length_le`,
`Succinct.select_bounds`) are already generic over `(bits, target)`.
-/

theorem select_exists_of_lt_occurrenceCount
    (bits : List Bool) (target : Bool) {occurrence : Nat}
    (hocc : occurrence < occurrenceCount bits target) :
    ∃ pos, RMQ.Succinct.select target bits occurrence = some pos := by
  simpa [occurrenceCount] using
    select_exists_of_lt_rankPrefix
      (target := target) (bits := bits)
      (occurrence := occurrence) (limit := bits.length) hocc

theorem position_eq_of_select
    (bits : List Bool) (target : Bool) {occurrence pos : Nat}
    (hselect : RMQ.Succinct.select target bits occurrence = some pos) :
    position bits target occurrence = pos := by
  simp [position, hselect]

theorem position_eq_length_of_count_le
    (bits : List Bool) (target : Bool) {occurrence : Nat}
    (hcount : occurrenceCount bits target <= occurrence) :
    position bits target occurrence = bits.length := by
  unfold position
  have hnone : RMQ.Succinct.select target bits occurrence = none :=
    select_none_of_rankPrefix_length_le (target := target)
      (bits := bits) (occurrence := occurrence)
      (by simpa [occurrenceCount] using hcount)
  simp [hnone]

theorem position_mono
    (bits : List Bool) (target : Bool) {lo hi : Nat} (hle : lo <= hi) :
    position bits target lo <= position bits target hi := by
  by_cases hhi : hi < occurrenceCount bits target
  · have hlo : lo < occurrenceCount bits target := by omega
    rcases select_exists_of_lt_occurrenceCount bits target hlo with
      ⟨loPos, hloSelect⟩
    rcases select_exists_of_lt_occurrenceCount bits target hhi with
      ⟨hiPos, hhiSelect⟩
    have hmono : loPos <= hiPos :=
      select_index_mono (target := target) (bits := bits)
        (lo := lo) (hi := hi) hle hloSelect hhiSelect
    rw [position_eq_of_select bits target hloSelect]
    rw [position_eq_of_select bits target hhiSelect]
    exact hmono
  · have hhiCount : occurrenceCount bits target <= hi := by omega
    rw [position_eq_length_of_count_le bits target hhiCount]
    by_cases hlo : lo < occurrenceCount bits target
    · rcases select_exists_of_lt_occurrenceCount bits target hlo with
        ⟨loPos, hloSelect⟩
      rw [position_eq_of_select bits target hloSelect]
      exact Nat.le_of_lt (RMQ.Succinct.select_bounds hloSelect)
    · have hloCount : occurrenceCount bits target <= lo := by omega
      rw [position_eq_length_of_count_le bits target hloCount]
      exact Nat.le_refl _

theorem position_le_length
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    position bits target occurrence <= bits.length := by
  unfold position
  cases hselect : RMQ.Succinct.select target bits occurrence with
  | none => simp
  | some pos =>
      have hpos : pos < bits.length := RMQ.Succinct.select_bounds hselect
      simp
      omega

theorem position_lt_length_of_lt_count
    (bits : List Bool) (target : Bool) {occurrence : Nat}
    (hocc : occurrence < occurrenceCount bits target) :
    position bits target occurrence < bits.length := by
  rcases select_exists_of_lt_occurrenceCount bits target hocc with
    ⟨pos, hselect⟩
  rw [position_eq_of_select bits target hselect]
  exact RMQ.Succinct.select_bounds hselect

/-! ## Super-level `o(n)` counting (the "few long supers" argument)

Generic port of `builtRelativeSplitFalseSelectLongSuperSpanSum_*`: the sum of
spans of "long" super intervals is bounded by the total bit length, so the
number of long (sparse-exception) supers is `o(n)`.  Bottoms out in
`position_mono` / `select_index_(strict_)mono`; no BP structure. -/

theorem superBaseOccurrence_lt_count
    (bits : List Bool) (target : Bool) {superSlot : Nat}
    (hslot : superSlot < superSlotCount bits target) :
    superBaseOccurrence bits.length superSlot < occurrenceCount bits target := by
  simpa [superSlotCount, superBaseOccurrence] using
    falseSelectCeilDiv_slot_mul_lt
      (n := occurrenceCount bits target)
      (stride := superStride bits.length)
      (slot := superSlot)
      (superStride_pos bits.length) hslot

theorem superEndOccurrence_le_count
    (bits : List Bool) (target : Bool) (superSlot : Nat) :
    superEndOccurrence bits target superSlot <= occurrenceCount bits target := by
  unfold superEndOccurrence
  exact Nat.min_le_right _ _

theorem superEndOccurrence_pos
    (bits : List Bool) (target : Bool) {superSlot : Nat}
    (hslot : superSlot < superSlotCount bits target) :
    0 < superEndOccurrence bits target superSlot := by
  have hbaseCount := superBaseOccurrence_lt_count bits target hslot
  have hstride := superStride_pos bits.length
  unfold superEndOccurrence
  exact Nat.lt_min.mpr ⟨by omega, by omega⟩

theorem superEndOccurrence_le_next_base
    (bits : List Bool) (target : Bool) (superSlot : Nat) :
    superEndOccurrence bits target superSlot <=
      superBaseOccurrence bits.length (superSlot + 1) := by
  unfold superEndOccurrence superBaseOccurrence
  have hleft :
      Nat.min
          (superSlot * superStride bits.length + superStride bits.length)
          (occurrenceCount bits target) <=
        superSlot * superStride bits.length + superStride bits.length :=
    Nat.min_le_left _ _
  simpa [Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using hleft

theorem superBaseOccurrence_le_next_base (n superSlot : Nat) :
    superBaseOccurrence n superSlot <= superBaseOccurrence n (superSlot + 1) := by
  unfold superBaseOccurrence
  exact Nat.mul_le_mul_right (superStride n) (Nat.le_succ superSlot)

theorem superBase_lt_end_of_base_lt_count
    (bits : List Bool) (target : Bool) (superSlot : Nat)
    (hbaseCount :
      superBaseOccurrence bits.length superSlot < occurrenceCount bits target) :
    superBaseOccurrence bits.length superSlot <
      superEndOccurrence bits target superSlot := by
  have hstride := superStride_pos bits.length
  unfold superEndOccurrence
  exact Nat.lt_min.mpr ⟨by omega, hbaseCount⟩

theorem superSpan_le_next_gap
    (bits : List Bool) (target : Bool) {superSlot : Nat}
    (hslot : superSlot < superSlotCount bits target) :
    superSpan bits target superSlot <=
      position bits target (superBaseOccurrence bits.length (superSlot + 1)) -
        position bits target (superBaseOccurrence bits.length superSlot) := by
  let base := superBaseOccurrence bits.length superSlot
  let endOcc := superEndOccurrence bits target superSlot
  let next := superBaseOccurrence bits.length (superSlot + 1)
  let basePos := position bits target base
  let lastPos := position bits target (endOcc - 1)
  let nextPos := position bits target next
  have hbaseCount : base < occurrenceCount bits target := by
    simpa [base] using superBaseOccurrence_lt_count bits target hslot
  have hendCount : endOcc <= occurrenceCount bits target := by
    simpa [endOcc] using superEndOccurrence_le_count bits target superSlot
  have hendPos : 0 < endOcc := by
    simpa [endOcc] using superEndOccurrence_pos bits target hslot
  have hendNext : endOcc <= next := by
    simpa [endOcc, next] using
      superEndOccurrence_le_next_base bits target superSlot
  have hbaseNext : base <= next := by
    simpa [base, next] using
      superBaseOccurrence_le_next_base bits.length superSlot
  have hbaseEnd : base < endOcc := by
    simpa [base, endOcc] using
      superBase_lt_end_of_base_lt_count bits target superSlot hbaseCount
  have hlastCount : endOcc - 1 < occurrenceCount bits target := by omega
  rcases select_exists_of_lt_occurrenceCount bits target hbaseCount with
    ⟨baseWitness, hbaseSelect⟩
  rcases select_exists_of_lt_occurrenceCount bits target hlastCount with
    ⟨lastWitness, hlastSelect⟩
  have hbaseEq : basePos = baseWitness := by
    simpa [basePos] using position_eq_of_select bits target hbaseSelect
  have hlastEq : lastPos = lastWitness := by
    simpa [lastPos] using position_eq_of_select bits target hlastSelect
  have hbaseLast : baseWitness <= lastWitness :=
    select_index_mono (target := target) (bits := bits)
      (lo := base) (hi := endOcc - 1)
      (posLo := baseWitness) (posHi := lastWitness)
      (by omega) hbaseSelect hlastSelect
  have hlastNext : lastWitness + 1 <= nextPos := by
    by_cases hnextCount : next < occurrenceCount bits target
    · rcases select_exists_of_lt_occurrenceCount bits target hnextCount with
        ⟨nextWitness, hnextSelect⟩
      have hstrict : lastWitness < nextWitness :=
        select_index_strict_mono (target := target) (bits := bits)
          (lo := endOcc - 1) (hi := next)
          (posLo := lastWitness) (posHi := nextWitness)
          (by omega) hlastSelect hnextSelect
      have hnextEq : nextPos = nextWitness := by
        simpa [nextPos] using position_eq_of_select bits target hnextSelect
      rw [hnextEq]; omega
    · have hnextCountLe : occurrenceCount bits target <= next := by omega
      have hnextEq : nextPos = bits.length := by
        simpa [nextPos] using
          position_eq_length_of_count_le bits target hnextCountLe
      have hlastBounds : lastWitness < bits.length :=
        RMQ.Succinct.select_bounds hlastSelect
      rw [hnextEq]; omega
  unfold superSpan
  change lastPos + 1 - basePos <= nextPos - basePos
  rw [hlastEq, hbaseEq]
  omega

/-- Sum of spans of long super intervals among the first `slotCount`. -/
def longSuperSpanSum (bits : List Bool) (target : Bool) (slotCount : Nat) : Nat :=
  (List.range slotCount).map
    (fun superSlot =>
      if superIsLong bits target superSlot then
        superSpan bits target superSlot
      else 0)
    |>.sum

theorem longSuperSpanSum_prefix_le_position
    (bits : List Bool) (target : Bool) {slotCount : Nat}
    (hslotCount : slotCount <= superSlotCount bits target) :
    longSuperSpanSum bits target slotCount <=
      position bits target (superBaseOccurrence bits.length slotCount) := by
  induction slotCount with
  | zero =>
      simp [longSuperSpanSum, superBaseOccurrence, position]
  | succ slotCount ih =>
      have hprefix : slotCount <= superSlotCount bits target := by omega
      have hslot : slotCount < superSlotCount bits target := by omega
      have ih' := ih hprefix
      let prefixSum := longSuperSpanSum bits target slotCount
      let span :=
        if superIsLong bits target slotCount then
          superSpan bits target slotCount
        else 0
      let basePos := position bits target (superBaseOccurrence bits.length slotCount)
      let nextPos :=
        position bits target (superBaseOccurrence bits.length (slotCount + 1))
      have ihPrefix : prefixSum <= basePos := by
        simpa [prefixSum, basePos] using ih'
      have hgap : span <= nextPos - basePos := by
        by_cases hlong : superIsLong bits target slotCount = true
        · have hspanGap : superSpan bits target slotCount <= nextPos - basePos := by
            simpa [basePos, nextPos] using superSpan_le_next_gap bits target hslot
          simpa [span, hlong] using hspanGap
        · have hfalse : superIsLong bits target slotCount = false := by
            cases h : superIsLong bits target slotCount
            · rfl
            · contradiction
          simp [span, hfalse]
      have hbaseNext :
          superBaseOccurrence bits.length slotCount <=
            superBaseOccurrence bits.length (slotCount + 1) :=
        superBaseOccurrence_le_next_base bits.length slotCount
      have hposMono : basePos <= nextPos := by
        simpa [basePos, nextPos] using position_mono bits target hbaseNext
      unfold longSuperSpanSum
      rw [List.range_succ, List.map_append, natList_sum_append]
      simp
      change prefixSum + span <= nextPos
      omega

theorem longSuperSpanSum_le_length
    (bits : List Bool) (target : Bool) :
    longSuperSpanSum bits target (superSlotCount bits target) <= bits.length := by
  have hprefix :=
    longSuperSpanSum_prefix_le_position bits target (Nat.le_refl _)
  have hocc :
      occurrenceCount bits target <=
        superSlotCount bits target * superStride bits.length := by
    simpa [superSlotCount] using
      falseSelectCeilDiv_mul_ge_of_pos
        (n := occurrenceCount bits target)
        (stride := superStride bits.length)
        (superStride_pos bits.length)
  have hbase :
      occurrenceCount bits target <=
        superBaseOccurrence bits.length (superSlotCount bits target) := by
    simpa [superBaseOccurrence] using hocc
  have hpos :
      position bits target
          (superBaseOccurrence bits.length (superSlotCount bits target)) =
        bits.length :=
    position_eq_length_of_count_le bits target hbase
  rwa [hpos] at hprefix

/-! ## Long-super exception count is `o(n)`

`longFlagBits` marks which supers are long.  The number of long supers times the
long-span threshold is bounded by the span sum, hence by `bits.length` -- so the
explicit long-super table (one block per long super) is `o(n)`. -/

/-- Per-super "is long" flag vector. -/
def longSuperFlagBits (bits : List Bool) (target : Bool) : List Bool :=
  (List.range (superSlotCount bits target)).map (superIsLong bits target)

theorem longSuperFlagBits_get?
    (bits : List Bool) (target : Bool) {superSlot : Nat}
    (hslot : superSlot < superSlotCount bits target) :
    (longSuperFlagBits bits target)[superSlot]? =
      some (superIsLong bits target superSlot) := by
  simp [longSuperFlagBits, List.getElem?_map, List.getElem?_range hslot]

theorem longSuperExceptionCount_mul_superLongSpan_le_spanSum
    (bits : List Bool) (target : Bool) {n : Nat}
    (hn : n <= superSlotCount bits target) :
    RMQ.Succinct.rankPrefix true (longSuperFlagBits bits target) n *
        superLongSpan bits.length <=
      longSuperSpanSum bits target n := by
  induction n with
  | zero =>
      simp [RMQ.Succinct.rankPrefix, longSuperSpanSum]
  | succ n ih =>
      have hn' : n <= superSlotCount bits target := by omega
      have hslot : n < superSlotCount bits target := by omega
      have hget := longSuperFlagBits_get? bits target (superSlot := n) hslot
      have hrank :=
        rankPrefix_succ_eq_of_get?
          (target := true) (bits := longSuperFlagBits bits target)
          (n := n) hget
      have ih' := ih hn'
      unfold longSuperSpanSum
      rw [List.range_succ]
      rw [List.map_append, natList_sum_append]
      simp [hrank]
      by_cases hlong : superIsLong bits target n = true
      · have hspan : superLongSpan bits.length <= superSpan bits target n := by
          unfold superIsLong at hlong
          by_cases hlt : superLongSpan bits.length < superSpan bits target n
          · omega
          · simp [hlt] at hlong
        simp [hlong]
        have hadd := Nat.add_le_add ih' hspan
        simpa [longSuperSpanSum, Nat.add_mul, Nat.one_mul, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm] using hadd
      · have hfalse : superIsLong bits target n = false := by
          cases h : superIsLong bits target n
          · rfl
          · contradiction
        simp [hfalse]
        exact ih'

theorem longSuperExceptionCount_mul_superLongSpan_le_length
    (bits : List Bool) (target : Bool) :
    RMQ.Succinct.rankPrefix true (longSuperFlagBits bits target)
          (superSlotCount bits target) *
        superLongSpan bits.length <=
      bits.length :=
  Nat.le_trans
    (longSuperExceptionCount_mul_superLongSpan_le_spanSum bits target
      (Nat.le_refl _))
    (longSuperSpanSum_le_length bits target)

/-! ## Local-base-occurrence monotonicity (n-only arithmetic)

Deferred from the foundation layer; needed for the local-level span counting. -/

theorem localBaseOccurrence_lt_superBoundary (n globalLocalSlot : Nat) :
    localBaseOccurrence n globalLocalSlot <
      (globalLocalSlot / localSlotsPerSuper n) * superStride n + superStride n := by
  let slots := localSlotsPerSuper n
  let ss := superStride n
  let ls := localStride n
  let q := globalLocalSlot / slots
  let r := globalLocalSlot % slots
  have hslots : 0 < slots := localSlotsPerSuper_pos n
  have hlocal : 0 < ls := localStride_pos n
  have hr : r < slots := Nat.mod_lt _ hslots
  have hbase : localBaseOccurrence n globalLocalSlot = q * ss + r * ls := by
    simpa [q, r, slots, ss, ls] using localBaseOccurrence_mod n globalLocalSlot
  have hceil : (r + 1) * ls <= ss + ls - 1 := by
    have hle : r + 1 <= slots := by omega
    have hleDiv : r + 1 <= (ss + ls - 1) / ls := by
      simpa [slots, ss, ls, localSlotsPerSuper, falseSelectLocalSlotsPerSuper]
        using hle
    exact Nat.mul_le_of_le_div ls (r + 1) (ss + ls - 1) hleDiv
  have hrLocal : r * ls < ss := by
    rw [Nat.add_mul, Nat.one_mul] at hceil
    omega
  rw [hbase]
  simpa [q, slots, ss] using
    (by omega : q * ss + r * ls < q * ss + ss)

theorem localBaseOccurrence_le_next_base (n globalLocalSlot : Nat) :
    localBaseOccurrence n globalLocalSlot <=
      localBaseOccurrence n (globalLocalSlot + 1) := by
  let slots := localSlotsPerSuper n
  let ss := superStride n
  let ls := localStride n
  let q := globalLocalSlot / slots
  let r := globalLocalSlot % slots
  have hslots : 0 < slots := localSlotsPerSuper_pos n
  have hlocal : 0 < ls := localStride_pos n
  have hr : r < slots := Nat.mod_lt _ hslots
  have hdecomp : globalLocalSlot = q * slots + r := by
    have h := Nat.div_add_mod globalLocalSlot slots
    simpa [q, r, Nat.mul_comm] using h.symm
  have hbase : localBaseOccurrence n globalLocalSlot = q * ss + r * ls := by
    simpa [q, r, slots, ss, ls] using localBaseOccurrence_mod n globalLocalSlot
  by_cases hnextLocal : r + 1 < slots
  · have hn1 : globalLocalSlot + 1 = q * slots + (r + 1) := by omega
    have hdiv : (globalLocalSlot + 1) / slots = q := by
      calc
        (globalLocalSlot + 1) / slots =
            (q * slots + (r + 1)) / slots := by rw [hn1]
        _ = ((r + 1) + slots * q) / slots := by
              rw [Nat.mul_comm, Nat.add_comm]
        _ = (r + 1) / slots + q := by
              exact Nat.add_mul_div_left (r + 1) q hslots
        _ = q := by
              rw [Nat.div_eq_of_lt hnextLocal]; omega
    have hmod : (globalLocalSlot + 1) % slots = r + 1 := by
      calc
        (globalLocalSlot + 1) % slots =
            (q * slots + (r + 1)) % slots := by rw [hn1]
        _ = r + 1 := by exact Nat.mul_add_mod_of_lt hnextLocal
    have hnext :
        localBaseOccurrence n (globalLocalSlot + 1) = q * ss + (r + 1) * ls := by
      rw [localBaseOccurrence_mod]
      simp [q, slots, ss, ls, hdiv, hmod]
    rw [hbase, hnext]
    rw [Nat.add_mul, Nat.one_mul]
    omega
  · have hlast : r + 1 = slots := by omega
    have hn1 : globalLocalSlot + 1 = (q + 1) * slots := by
      rw [hdecomp, Nat.add_mul, Nat.one_mul]; omega
    have hdiv : (globalLocalSlot + 1) / slots = q + 1 := by
      rw [hn1]; exact Nat.mul_div_left (q + 1) hslots
    have hmod : (globalLocalSlot + 1) % slots = 0 := by
      rw [hn1]; exact Nat.mul_mod_left (q + 1) slots
    have hnext :
        localBaseOccurrence n (globalLocalSlot + 1) = (q + 1) * ss := by
      rw [localBaseOccurrence_mod]
      simp [q, slots, ss, hdiv, hmod]
    have hboundary := localBaseOccurrence_lt_superBoundary n globalLocalSlot
    rw [hnext]
    rw [Nat.add_mul, Nat.one_mul]
    simpa [q, slots, ss] using Nat.le_of_lt hboundary

/-! ## Short-super local boundary lemmas (for local-level `o(n)` counting) -/

theorem occurrenceCount_pos_of_local_slot
    (bits : List Bool) (target : Bool) {globalLocalSlot : Nat}
    (hslot : globalLocalSlot < localSlotCount bits target) :
    0 < occurrenceCount bits target := by
  by_cases hpos : 0 < occurrenceCount bits target
  · exact hpos
  · have hcountZero : occurrenceCount bits target = 0 := by omega
    have hsuperZero : superSlotCount bits target = 0 := by
      unfold superSlotCount falseSelectCeilDiv
      rw [hcountZero]
      have hstride := superStride_pos bits.length
      have hlt : superStride bits.length - 1 < superStride bits.length :=
        Nat.pred_lt (Nat.ne_of_gt hstride)
      simpa using Nat.div_eq_of_lt hlt
    have hlocalZero : localSlotCount bits target = 0 := by
      simp [localSlotCount, hsuperZero]
    omega

theorem shortSuperLocalEndOccurrence_le_count
    (bits : List Bool) (target : Bool) (globalLocalSlot : Nat) :
    shortSuperLocalEndOccurrence bits target globalLocalSlot <=
      occurrenceCount bits target := by
  unfold shortSuperLocalEndOccurrence
  exact Nat.le_trans (Nat.min_le_right _ _) (by
    unfold superEndOccurrence
    exact Nat.min_le_right _ _)

theorem shortSuperLocalEndOccurrence_pos
    (bits : List Bool) (target : Bool) {globalLocalSlot : Nat}
    (hslot : globalLocalSlot < localSlotCount bits target) :
    0 < shortSuperLocalEndOccurrence bits target globalLocalSlot := by
  have hcountPos := occurrenceCount_pos_of_local_slot bits target hslot
  have hlocalPos := localStride_pos bits.length
  have hsuperStridePos := superStride_pos bits.length
  have hsuperEndPos :
      0 < superEndOccurrence bits target
        (localSuperSlot bits.length globalLocalSlot) := by
    unfold superEndOccurrence superBaseOccurrence
    exact Nat.lt_min.mpr ⟨by omega, hcountPos⟩
  unfold shortSuperLocalEndOccurrence
  exact Nat.lt_min.mpr ⟨by omega, hsuperEndPos⟩

theorem shortSuperLocalBase_lt_end_of_base_lt_count
    (bits : List Bool) (target : Bool) (globalLocalSlot : Nat)
    (hbaseCount :
      localBaseOccurrence bits.length globalLocalSlot <
        occurrenceCount bits target) :
    localBaseOccurrence bits.length globalLocalSlot <
      shortSuperLocalEndOccurrence bits target globalLocalSlot := by
  have hlocalPos := localStride_pos bits.length
  have hboundary :=
    localBaseOccurrence_lt_superBoundary bits.length globalLocalSlot
  have hsuperEnd :
      localBaseOccurrence bits.length globalLocalSlot <
        superEndOccurrence bits target
          (localSuperSlot bits.length globalLocalSlot) := by
    unfold superEndOccurrence superBaseOccurrence localSuperSlot
    exact Nat.lt_min.mpr ⟨by simpa using hboundary, hbaseCount⟩
  unfold shortSuperLocalEndOccurrence
  exact Nat.lt_min.mpr ⟨by omega, hsuperEnd⟩

/-! ## Local-level `o(n)` span counting -/

theorem finalLocalBaseOccurrence (bits : List Bool) (target : Bool) :
    localBaseOccurrence bits.length (localSlotCount bits target) =
      superSlotCount bits target * superStride bits.length := by
  let slots := localSlotsPerSuper bits.length
  let superCount := superSlotCount bits target
  have hslots : 0 < slots := localSlotsPerSuper_pos bits.length
  have hdiv : (localSlotCount bits target) / slots = superCount := by
    simp [localSlotCount, superCount, slots, Nat.mul_div_left, hslots]
  have hmod : (localSlotCount bits target) % slots = 0 := by
    simp [localSlotCount, slots, Nat.mul_mod_left]
  rw [localBaseOccurrence_mod]
  change
    ((localSlotCount bits target) / slots) * superStride bits.length +
      ((localSlotCount bits target) % slots) * localStride bits.length =
      superCount * superStride bits.length
  rw [hdiv, hmod]
  simp [superCount]

theorem shortSuperLocalEndOccurrence_le_next_base
    (bits : List Bool) (target : Bool) (globalLocalSlot : Nat) :
    shortSuperLocalEndOccurrence bits target globalLocalSlot <=
      localBaseOccurrence bits.length (globalLocalSlot + 1) := by
  let slots := localSlotsPerSuper bits.length
  let ss := superStride bits.length
  let ls := localStride bits.length
  let q := globalLocalSlot / slots
  let r := globalLocalSlot % slots
  have hslots : 0 < slots := localSlotsPerSuper_pos bits.length
  have hr : r < slots := Nat.mod_lt _ hslots
  have hdecomp : globalLocalSlot = q * slots + r := by
    have h := Nat.div_add_mod globalLocalSlot slots
    simpa [q, r, Nat.mul_comm] using h.symm
  have hbase :
      localBaseOccurrence bits.length globalLocalSlot = q * ss + r * ls := by
    simpa [q, r, slots, ss, ls] using localBaseOccurrence_mod bits.length globalLocalSlot
  have hendBase :
      shortSuperLocalEndOccurrence bits target globalLocalSlot <=
        localBaseOccurrence bits.length globalLocalSlot + ls := by
    unfold shortSuperLocalEndOccurrence
    exact Nat.min_le_left _ _
  have hendSuper :
      shortSuperLocalEndOccurrence bits target globalLocalSlot <= q * ss + ss := by
    have hsuperEnd :
        superEndOccurrence bits target
            (localSuperSlot bits.length globalLocalSlot) <= q * ss + ss := by
      unfold superEndOccurrence superBaseOccurrence localSuperSlot
      exact Nat.min_le_left _ _
    exact Nat.le_trans (Nat.min_le_right _ _)
      (by simpa [q, slots, ss] using hsuperEnd)
  by_cases hnextLocal : r + 1 < slots
  · have hn1 : globalLocalSlot + 1 = q * slots + (r + 1) := by omega
    have hdiv : (globalLocalSlot + 1) / slots = q := by
      calc
        (globalLocalSlot + 1) / slots =
            (q * slots + (r + 1)) / slots := by rw [hn1]
        _ = ((r + 1) + slots * q) / slots := by rw [Nat.mul_comm, Nat.add_comm]
        _ = (r + 1) / slots + q := by exact Nat.add_mul_div_left (r + 1) q hslots
        _ = q := by rw [Nat.div_eq_of_lt hnextLocal]; omega
    have hmod : (globalLocalSlot + 1) % slots = r + 1 := by
      calc
        (globalLocalSlot + 1) % slots =
            (q * slots + (r + 1)) % slots := by rw [hn1]
        _ = r + 1 := by exact Nat.mul_add_mod_of_lt hnextLocal
    have hnext :
        localBaseOccurrence bits.length (globalLocalSlot + 1) =
          q * ss + (r + 1) * ls := by
      rw [localBaseOccurrence_mod]
      simp [q, slots, ss, ls, hdiv, hmod]
    rw [hnext]
    have h := hendBase
    rw [hbase] at h
    simpa [Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using h
  · have hlast : r + 1 = slots := by omega
    have hn1 : globalLocalSlot + 1 = (q + 1) * slots := by
      rw [hdecomp, Nat.add_mul, Nat.one_mul]; omega
    have hdiv : (globalLocalSlot + 1) / slots = q + 1 := by
      rw [hn1]; exact Nat.mul_div_left (q + 1) hslots
    have hmod : (globalLocalSlot + 1) % slots = 0 := by
      rw [hn1]; exact Nat.mul_mod_left (q + 1) slots
    have hnext :
        localBaseOccurrence bits.length (globalLocalSlot + 1) = (q + 1) * ss := by
      rw [localBaseOccurrence_mod]
      simp [q, slots, ss, hdiv, hmod]
    rw [hnext]
    have h := hendSuper
    simpa [Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using h

theorem shortSuperLocalSpan_le_next_gap
    (bits : List Bool) (target : Bool) {globalLocalSlot : Nat}
    (hslot : globalLocalSlot < localSlotCount bits target) :
    shortSuperLocalSpan bits target globalLocalSlot <=
      position bits target (localBaseOccurrence bits.length (globalLocalSlot + 1)) -
        position bits target (localBaseOccurrence bits.length globalLocalSlot) := by
  let base := localBaseOccurrence bits.length globalLocalSlot
  let endOcc := shortSuperLocalEndOccurrence bits target globalLocalSlot
  let next := localBaseOccurrence bits.length (globalLocalSlot + 1)
  let basePos := position bits target base
  let lastPos := position bits target (endOcc - 1)
  let nextPos := position bits target next
  have hendCount : endOcc <= occurrenceCount bits target := by
    simpa [endOcc] using shortSuperLocalEndOccurrence_le_count bits target globalLocalSlot
  have hendPos : 0 < endOcc := by
    simpa [endOcc] using shortSuperLocalEndOccurrence_pos bits target hslot
  have hendNext : endOcc <= next := by
    simpa [endOcc, next] using
      shortSuperLocalEndOccurrence_le_next_base bits target globalLocalSlot
  have hbaseNext : base <= next := by
    simpa [base, next] using localBaseOccurrence_le_next_base bits.length globalLocalSlot
  have hlastCount : endOcc - 1 < occurrenceCount bits target := by omega
  rcases select_exists_of_lt_occurrenceCount bits target hlastCount with
    ⟨lastWitness, hlastSelect⟩
  have hlastEq : lastPos = lastWitness := by
    simpa [lastPos] using position_eq_of_select bits target hlastSelect
  have hlastBounds : lastWitness < bits.length := RMQ.Succinct.select_bounds hlastSelect
  by_cases hbaseCount : base < occurrenceCount bits target
  · have hbaseEnd : base < endOcc := by
      simpa [base, endOcc] using
        shortSuperLocalBase_lt_end_of_base_lt_count bits target globalLocalSlot hbaseCount
    rcases select_exists_of_lt_occurrenceCount bits target hbaseCount with
      ⟨baseWitness, hbaseSelect⟩
    have hbaseEq : basePos = baseWitness := by
      simpa [basePos] using position_eq_of_select bits target hbaseSelect
    have hbaseLast : baseWitness <= lastWitness :=
      select_index_mono (target := target) (bits := bits)
        (lo := base) (hi := endOcc - 1)
        (posLo := baseWitness) (posHi := lastWitness)
        (by omega) hbaseSelect hlastSelect
    have hlastNext : lastWitness + 1 <= nextPos := by
      by_cases hnextCount : next < occurrenceCount bits target
      · rcases select_exists_of_lt_occurrenceCount bits target hnextCount with
          ⟨nextWitness, hnextSelect⟩
        have hstrict : lastWitness < nextWitness :=
          select_index_strict_mono (target := target) (bits := bits)
            (lo := endOcc - 1) (hi := next)
            (posLo := lastWitness) (posHi := nextWitness)
            (by omega) hlastSelect hnextSelect
        have hnextEq : nextPos = nextWitness := by
          simpa [nextPos] using position_eq_of_select bits target hnextSelect
        rw [hnextEq]; omega
      · have hnextCountLe : occurrenceCount bits target <= next := by omega
        have hnextEq : nextPos = bits.length := by
          simpa [nextPos] using position_eq_length_of_count_le bits target hnextCountLe
        rw [hnextEq]; omega
    unfold shortSuperLocalSpan
    change lastPos + 1 - basePos <= nextPos - basePos
    rw [hlastEq, hbaseEq]
    omega
  · have hbaseCountLe : occurrenceCount bits target <= base := by omega
    have hnextCountLe : occurrenceCount bits target <= next :=
      Nat.le_trans hbaseCountLe hbaseNext
    have hbaseEq : basePos = bits.length := by
      simpa [basePos] using position_eq_length_of_count_le bits target hbaseCountLe
    have hnextEq : nextPos = bits.length := by
      simpa [nextPos] using position_eq_length_of_count_le bits target hnextCountLe
    unfold shortSuperLocalSpan
    change lastPos + 1 - basePos <= nextPos - basePos
    rw [hlastEq, hbaseEq, hnextEq]
    omega

/-- Sum of spans of local blocks among the first `slotCount`. -/
def shortSuperLocalSpanSum (bits : List Bool) (target : Bool) (slotCount : Nat) :
    Nat :=
  (List.range slotCount).map (shortSuperLocalSpan bits target) |>.sum

theorem shortSuperLocalSpanSum_prefix_le_position
    (bits : List Bool) (target : Bool) {slotCount : Nat}
    (hslotCount : slotCount <= localSlotCount bits target) :
    shortSuperLocalSpanSum bits target slotCount <=
      position bits target (localBaseOccurrence bits.length slotCount) := by
  induction slotCount with
  | zero =>
      simp [shortSuperLocalSpanSum, localBaseOccurrence, position]
  | succ slotCount ih =>
      have hprefix : slotCount <= localSlotCount bits target := by omega
      have hslot : slotCount < localSlotCount bits target := by omega
      have ih' := ih hprefix
      let prefixSum := shortSuperLocalSpanSum bits target slotCount
      let span := shortSuperLocalSpan bits target slotCount
      let basePos := position bits target (localBaseOccurrence bits.length slotCount)
      let nextPos :=
        position bits target (localBaseOccurrence bits.length (slotCount + 1))
      have ihPrefix : prefixSum <= basePos := by
        simpa [prefixSum, basePos] using ih'
      have hgap : span <= nextPos - basePos := by
        simpa [span, basePos, nextPos] using
          shortSuperLocalSpan_le_next_gap bits target hslot
      have hbaseNext :
          localBaseOccurrence bits.length slotCount <=
            localBaseOccurrence bits.length (slotCount + 1) :=
        localBaseOccurrence_le_next_base bits.length slotCount
      have hposMono : basePos <= nextPos := by
        simpa [basePos, nextPos] using position_mono bits target hbaseNext
      unfold shortSuperLocalSpanSum
      rw [List.range_succ, List.map_append, natList_sum_append]
      simp
      change prefixSum + span <= nextPos
      omega

theorem shortSuperLocalSpanSum_le_length (bits : List Bool) (target : Bool) :
    shortSuperLocalSpanSum bits target (localSlotCount bits target) <= bits.length := by
  have hprefix :=
    shortSuperLocalSpanSum_prefix_le_position bits target (Nat.le_refl _)
  have hocc :
      occurrenceCount bits target <=
        superSlotCount bits target * superStride bits.length := by
    simpa [superSlotCount] using
      falseSelectCeilDiv_mul_ge_of_pos
        (n := occurrenceCount bits target)
        (stride := superStride bits.length)
        (superStride_pos bits.length)
  have hbase :
      occurrenceCount bits target <=
        localBaseOccurrence bits.length (localSlotCount bits target) := by
    rw [finalLocalBaseOccurrence]; exact hocc
  have hpos :
      position bits target
          (localBaseOccurrence bits.length (localSlotCount bits target)) =
        bits.length :=
    position_eq_length_of_count_le bits target hbase
  rwa [hpos] at hprefix

/-! ## Local sparse-exception count is `o(n)`

A local block is a sparse exception when its super is short (not long) and its
span exceeds one word.  Each such block contributes at least `wordBits` to the
local span sum, so the number of sparse-exception blocks times `wordBits` is
bounded by `bits.length`. -/

/-- A local block needing explicit (sparse) treatment within a short super. -/
def localIsSparseException (bits : List Bool) (target : Bool)
    (globalLocalSlot : Nat) : Bool :=
  (! superIsLong bits target (localSuperSlot bits.length globalLocalSlot)) &&
    decide (wordBits bits.length < shortSuperLocalSpan bits target globalLocalSlot)

theorem localIsSparseException_true_short
    (bits : List Bool) (target : Bool) (globalLocalSlot : Nat)
    (hflag : localIsSparseException bits target globalLocalSlot = true) :
    superIsLong bits target (localSuperSlot bits.length globalLocalSlot) = false /\
      wordBits bits.length < shortSuperLocalSpan bits target globalLocalSlot := by
  unfold localIsSparseException at hflag
  cases hlong :
      superIsLong bits target (localSuperSlot bits.length globalLocalSlot) with
  | true => simp [hlong] at hflag
  | false =>
      refine ⟨rfl, ?_⟩
      simpa [hlong] using hflag

/-- Per-local-slot "is sparse exception" flag vector. -/
def sparseExceptionFlagBits (bits : List Bool) (target : Bool) : List Bool :=
  (List.range (localSlotCount bits target)).map (localIsSparseException bits target)

theorem sparseExceptionFlagBits_length (bits : List Bool) (target : Bool) :
    (sparseExceptionFlagBits bits target).length =
      localSlotCount bits target := by
  simp [sparseExceptionFlagBits]

theorem sparseExceptionFlagBits_get?
    (bits : List Bool) (target : Bool) {globalLocalSlot : Nat}
    (hslot : globalLocalSlot < localSlotCount bits target) :
    (sparseExceptionFlagBits bits target)[globalLocalSlot]? =
      some (localIsSparseException bits target globalLocalSlot) := by
  simp [sparseExceptionFlagBits, List.getElem?_map, List.getElem?_range hslot]

theorem sparseExceptionCount_wordBits_le_spanSum
    (bits : List Bool) (target : Bool) {n : Nat}
    (hn : n <= localSlotCount bits target) :
    RMQ.Succinct.rankPrefix true (sparseExceptionFlagBits bits target) n *
        wordBits bits.length <=
      shortSuperLocalSpanSum bits target n := by
  induction n with
  | zero =>
      simp [RMQ.Succinct.rankPrefix, shortSuperLocalSpanSum]
  | succ n ih =>
      have hn' : n <= localSlotCount bits target := by omega
      have hslot : n < localSlotCount bits target := by omega
      have hget := sparseExceptionFlagBits_get? bits target (globalLocalSlot := n) hslot
      have hrank :=
        rankPrefix_succ_eq_of_get?
          (target := true) (bits := sparseExceptionFlagBits bits target)
          (n := n) hget
      have ih' := ih hn'
      rw [hrank]
      unfold shortSuperLocalSpanSum
      rw [List.range_succ, List.map_append, natList_sum_append]
      simp
      by_cases hflag : localIsSparseException bits target n = true
      · have hspanLt := (localIsSparseException_true_short bits target n hflag).2
        have hwordLe :
            wordBits bits.length <= shortSuperLocalSpan bits target n := by omega
        have hcalc :
            (RMQ.Succinct.rankPrefix true (sparseExceptionFlagBits bits target) n
                + 1) * wordBits bits.length <=
              shortSuperLocalSpanSum bits target n +
                shortSuperLocalSpan bits target n := by
          rw [Nat.add_mul]
          simp
          omega
        simpa [hflag, shortSuperLocalSpanSum, Nat.add_mul, Nat.mul_comm,
          Nat.mul_left_comm, Nat.mul_assoc] using hcalc
      · have hfalse : localIsSparseException bits target n = false := by
          cases h : localIsSparseException bits target n
          · rfl
          · contradiction
        simpa [hfalse, shortSuperLocalSpanSum] using
          Nat.le_trans ih'
            (Nat.le_add_right (shortSuperLocalSpanSum bits target n)
              (shortSuperLocalSpan bits target n))

theorem sparseExceptionCount_wordBits_le_length
    (bits : List Bool) (target : Bool) :
    RMQ.Succinct.rankPrefix true (sparseExceptionFlagBits bits target)
          (localSlotCount bits target) *
        wordBits bits.length <=
      bits.length :=
  Nat.le_trans
    (sparseExceptionCount_wordBits_le_spanSum bits target (Nat.le_refl _))
    (shortSuperLocalSpanSum_le_length bits target)

/-! ## Entry / table data layer (Tier 2 back half)

Generic ports of the BP `builtRelativeSplitFalseSelect{Super,Local}Entr*`,
relative tables, field widths, and the Jacobson flag-rank directories over the
classification flag vectors.  Each is the `shape.bpCode -> bits`,
`false -> target` re-index of the corresponding `SuccinctSelectProposal` def. -/

/-- Super-sample dense-local entry: base occurrence at a super-stride boundary,
its word index/offset, and a `rankBefore` flag marking long supers. -/
def superEntry (bits : List Bool) (target : Bool) (superSlot : Nat) :
    SparseDenseFalseSelectDenseLocalEntry :=
  let baseOccurrence := superSlot * superStride bits.length
  let basePosition := position bits target baseOccurrence
  let wordSize := wordBits bits.length
  { baseOccurrence := baseOccurrence
    baseWordIndex := basePosition / wordSize
    rankBefore := if superIsLong bits target superSlot then 1 else 0
    firstOffset := basePosition - (basePosition / wordSize) * wordSize }

def superEntries (bits : List Bool) (target : Bool) :
    List SparseDenseFalseSelectDenseLocalEntry :=
  (List.range (superSlotCount bits target)).map (superEntry bits target)

theorem superEntries_length (bits : List Bool) (target : Bool) :
    (superEntries bits target).length = superSlotCount bits target := by
  simp [superEntries]

theorem superEntries_get? (bits : List Bool) (target : Bool) {superSlot : Nat}
    (hslot : superSlot < superSlotCount bits target) :
    (superEntries bits target)[superSlot]? =
      some (superEntry bits target superSlot) := by
  simp [superEntries, List.getElem?_map, List.getElem?_range hslot]

/-- A compact local entry carries real data iff its super is short (dense) and
its base occurrence is in range. -/
def compactLocalEntryIsLive (bits : List Bool) (target : Bool)
    (globalLocalSlot : Nat) : Bool :=
  (! superIsLong bits target (localSuperSlot bits.length globalLocalSlot)) &&
    decide (localBaseOccurrence bits.length globalLocalSlot <
      occurrenceCount bits target)

/-- Compact dense-local entry, stored relative to its owning super's base. -/
def localEntry (bits : List Bool) (target : Bool) (globalLocalSlot : Nat) :
    SparseDenseFalseSelectDenseLocalEntry :=
  if compactLocalEntryIsLive bits target globalLocalSlot then
    let superSlot := localSuperSlot bits.length globalLocalSlot
    let superBaseOcc := superSlot * superStride bits.length
    let superBasePosition := position bits target superBaseOcc
    let baseOccurrence := localBaseOccurrence bits.length globalLocalSlot
    let basePosition := position bits target baseOccurrence
    let wordSize := wordBits bits.length
    { baseOccurrence := baseOccurrence - superBaseOcc
      baseWordIndex := basePosition / wordSize - superBasePosition / wordSize
      rankBefore :=
        if localIsSparseException bits target globalLocalSlot then 1 else 0
      firstOffset := basePosition - (basePosition / wordSize) * wordSize }
  else
    { baseOccurrence := 0
      baseWordIndex := 0
      rankBefore := 0
      firstOffset := 0 }

def localEntries (bits : List Bool) (target : Bool) :
    List SparseDenseFalseSelectDenseLocalEntry :=
  (List.range (localSlotCount bits target)).map (localEntry bits target)

theorem localEntries_length (bits : List Bool) (target : Bool) :
    (localEntries bits target).length = localSlotCount bits target := by
  simp [localEntries]

theorem localEntries_get? (bits : List Bool) (target : Bool)
    {globalLocalSlot : Nat}
    (hslot : globalLocalSlot < localSlotCount bits target) :
    (localEntries bits target)[globalLocalSlot]? =
      some (localEntry bits target globalLocalSlot) := by
  simp [localEntries, List.getElem?_map, List.getElem?_range hslot]

/-- Per-local-slot "is sparse" flag vector. -/
def sparseFlagBits (bits : List Bool) (target : Bool) : List Bool :=
  (List.range (localSlotCount bits target)).map (localIsSparse bits target)

theorem sparseFlagBits_length (bits : List Bool) (target : Bool) :
    (sparseFlagBits bits target).length = localSlotCount bits target := by
  simp [sparseFlagBits]

theorem sparseFlagBits_get? (bits : List Bool) (target : Bool)
    {globalLocalSlot : Nat}
    (hslot : globalLocalSlot < localSlotCount bits target) :
    (sparseFlagBits bits target)[globalLocalSlot]? =
      some (localIsSparse bits target globalLocalSlot) := by
  simp [sparseFlagBits, List.getElem?_map, List.getElem?_range hslot]

/-! ### Jacobson flag-rank directory (generic over the flag-bit list)

The BP `builtRelativeSplitFalseSelect{Long,Sparse,SparseException}FlagRank*`
directories are three copies of the same two-level payload-live rank
construction over different flag vectors.  We factor them into a single
`flagRank*` family parameterized by the flag-bit list; the three BP directories
become instantiations at `longSuperFlagBits`, `sparseFlagBits`, and
`sparseExceptionFlagBits`. -/

/-- Payload-word size of a flag-rank directory: `machineWordBits` of the flag
vector's length. -/
def flagRankWordSize (flagBits : List Bool) : Nat :=
  SuccinctRankProposal.machineWordBits flagBits.length

def flagRankBlocksPerSuper (flagBits : List Bool) : Nat :=
  flagRankWordSize flagBits

def flagRankBlockWidth (flagBits : List Bool) : Nat :=
  SuccinctRankProposal.machineWordBits
    (flagRankBlocksPerSuper flagBits * flagRankWordSize flagBits)

theorem flagRankWordSize_pos (flagBits : List Bool) :
    0 < flagRankWordSize flagBits := by
  simp [flagRankWordSize, SuccinctRankProposal.machineWordBits_pos]

theorem flagRankBlocksPerSuper_pos (flagBits : List Bool) :
    0 < flagRankBlocksPerSuper flagBits := by
  simpa [flagRankBlocksPerSuper] using flagRankWordSize_pos flagBits

theorem flagBits_length_lt_rank_word_pow (flagBits : List Bool) :
    flagBits.length < 2 ^ flagRankWordSize flagBits := by
  simpa [flagRankWordSize, SuccinctRankProposal.machineWordBits] using
    (Nat.lt_log2_self (n := flagBits.length))

theorem flagRankBlockSpan_lt_pow (flagBits : List Bool) :
    flagRankBlocksPerSuper flagBits * flagRankWordSize flagBits <
      2 ^ flagRankBlockWidth flagBits := by
  simpa [flagRankBlockWidth, SuccinctRankProposal.machineWordBits] using
    (Nat.lt_log2_self
      (n := flagRankBlocksPerSuper flagBits * flagRankWordSize flagBits))

def flagRankSuperOverhead (flagBits : List Bool) : Nat :=
  (SuccinctRankProposal.canonicalSuperRankSampleTables
    flagBits (flagRankWordSize flagBits) (flagRankBlocksPerSuper flagBits)
    (flagRankWordSize flagBits)
    (flagBits_length_lt_rank_word_pow flagBits)).payload.length

def flagRankBlockOverhead (flagBits : List Bool) : Nat :=
  (SuccinctRankProposal.canonicalBlockRankSampleTablesOfLocalSpan
    flagBits (flagRankWordSize flagBits) (flagRankBlocksPerSuper flagBits)
    (flagRankBlockWidth flagBits)
    (flagRankBlocksPerSuper_pos flagBits)
    (flagRankBlockSpan_lt_pow flagBits)).payload.length

/-- The two-level payload-live rank directory over `flagBits`. -/
def flagRankData (flagBits : List Bool) :
    SuccinctRankProposal.TwoLevelPayloadLiveStoredWordRankData
      flagBits (flagRankSuperOverhead flagBits)
      (flagRankBlockOverhead flagBits) 4 :=
  SuccinctRankProposal.canonicalTwoLevelRankDataOfChunksExactLocalBlock
    flagBits
    (flagRankWordSize_pos flagBits)
    (by simp [flagRankWordSize])
    (flagRankBlocksPerSuper_pos flagBits)
    (flagBits_length_lt_rank_word_pow flagBits)
    (flagRankBlockSpan_lt_pow flagBits)
    (by omega)

theorem flagRankData_profile (flagBits : List Bool) :
    let data := flagRankData flagBits
    data.auxPayload.length =
        flagRankSuperOverhead flagBits + flagRankBlockOverhead flagBits /\
      data.wordSize <=
        SuccinctRankProposal.machineWordBits flagBits.length /\
      SuccinctSpace.flattenPayloadWords data.bitWords.store.words.toList =
        flagBits /\
      (forall {word : List Bool},
        List.Mem word data.bitWords.store.words.toList ->
          word.length <=
            SuccinctRankProposal.machineWordBits flagBits.length) /\
      forall target pos,
        (data.rankCosted target pos).cost <= 4 /\
          (data.rankCosted target pos).erase =
            RMQ.Succinct.rankPrefix target flagBits pos := by
  exact
    SuccinctRankProposal.canonicalTwoLevelRankDataOfChunksExactLocalBlock_profile
      flagBits
      (flagRankWordSize_pos flagBits)
      (by simp [flagRankWordSize])
      (flagRankBlocksPerSuper_pos flagBits)
      (flagBits_length_lt_rank_word_pow flagBits)
      (flagRankBlockSpan_lt_pow flagBits)
      (by omega)

/-- Effective local slots are capped by the number of actual target
occurrences.  This is the generic version of the BP sparse-exception effective
flag prefix. -/
def sparseExceptionEffectiveLocalSlotCount
    (bits : List Bool) (target : Bool) : Nat :=
  Nat.min (localSlotCount bits target) (occurrenceCount bits target)

def sparseExceptionEffectiveFlagBits
    (bits : List Bool) (target : Bool) : List Bool :=
  (List.range (sparseExceptionEffectiveLocalSlotCount bits target)).map
    (localIsSparseException bits target)

theorem sparseExceptionEffectiveFlagBits_length
    (bits : List Bool) (target : Bool) :
    (sparseExceptionEffectiveFlagBits bits target).length =
      sparseExceptionEffectiveLocalSlotCount bits target := by
  simp [sparseExceptionEffectiveFlagBits]

theorem sparseExceptionEffectiveLocalSlotCount_le_full
    (bits : List Bool) (target : Bool) :
    sparseExceptionEffectiveLocalSlotCount bits target <=
      localSlotCount bits target := by
  unfold sparseExceptionEffectiveLocalSlotCount
  exact Nat.min_le_left _ _

theorem sparseExceptionEffectiveLocalSlotCount_le_count
    (bits : List Bool) (target : Bool) :
    sparseExceptionEffectiveLocalSlotCount bits target <=
      occurrenceCount bits target := by
  unfold sparseExceptionEffectiveLocalSlotCount
  exact Nat.min_le_right _ _

theorem sparseExceptionEffectiveFlagBits_length_le_length
    (bits : List Bool) (target : Bool) :
    (sparseExceptionEffectiveFlagBits bits target).length <= bits.length := by
  have hlen :
      (sparseExceptionEffectiveFlagBits bits target).length <=
        occurrenceCount bits target := by
    rw [sparseExceptionEffectiveFlagBits_length]
    exact sparseExceptionEffectiveLocalSlotCount_le_count bits target
  exact Nat.le_trans hlen
    (by
      simpa [occurrenceCount] using
        RMQ.Succinct.rankPrefix_le_length target bits bits.length)

theorem sparseExceptionEffectiveFlagBits_get?
    (bits : List Bool) (target : Bool) {globalLocalSlot : Nat}
    (hslot :
      globalLocalSlot <
        sparseExceptionEffectiveLocalSlotCount bits target) :
    (sparseExceptionEffectiveFlagBits bits target)[globalLocalSlot]? =
      some (localIsSparseException bits target globalLocalSlot) := by
  simp [sparseExceptionEffectiveFlagBits, List.getElem?_map,
    List.getElem?_range hslot]

theorem sparseExceptionEffectiveFlagBits_prefix_eq
    (bits : List Bool) (target : Bool) {globalLocalSlot : Nat}
    (hslot :
      globalLocalSlot <=
        sparseExceptionEffectiveLocalSlotCount bits target) :
    RMQ.Succinct.rankPrefix true
        (sparseExceptionEffectiveFlagBits bits target) globalLocalSlot =
      RMQ.Succinct.rankPrefix true
        (sparseExceptionFlagBits bits target) globalLocalSlot := by
  have htake :
      sparseExceptionEffectiveFlagBits bits target =
        (sparseExceptionFlagBits bits target).take
          (sparseExceptionEffectiveLocalSlotCount bits target) := by
    apply List.ext_getElem?
    intro i
    by_cases hi :
        i < sparseExceptionEffectiveLocalSlotCount bits target
    · have hfull : i < localSlotCount bits target := by
        exact Nat.lt_of_lt_of_le hi
          (sparseExceptionEffectiveLocalSlotCount_le_full bits target)
      simp [sparseExceptionEffectiveFlagBits, sparseExceptionFlagBits,
        List.getElem?_map, List.getElem?_range hfull, hi]
    · have heff :
          (sparseExceptionEffectiveFlagBits bits target)[i]? = none := by
        rw [List.getElem?_eq_none_iff]
        simp [sparseExceptionEffectiveFlagBits, Nat.le_of_not_gt hi]
      have htakeNone :
          ((sparseExceptionFlagBits bits target).take
            (sparseExceptionEffectiveLocalSlotCount bits target))[i]? =
            none := by
        rw [List.getElem?_eq_none_iff]
        simp [List.length_take, sparseExceptionFlagBits_length,
          sparseExceptionEffectiveLocalSlotCount_le_full bits target,
          Nat.le_of_not_gt hi]
      rw [heff, htakeNone]
  rw [htake]
  exact
    RMQ.Succinct.rankPrefix_take_eq_of_le
      true (sparseExceptionFlagBits bits target)
      (n := sparseExceptionEffectiveLocalSlotCount bits target)
      (limit := globalLocalSlot)
      (by
        rw [List.length_take]
        rw [sparseExceptionFlagBits_length]
        exact Nat.le_min.mpr
          ⟨hslot,
            Nat.le_trans hslot
              (sparseExceptionEffectiveLocalSlotCount_le_full bits target)⟩)

def sparseExceptionEffectiveFlagRankWordSize
    (bits : List Bool) (target : Bool) : Nat :=
  SuccinctRankProposal.machineWordBits
    (sparseExceptionEffectiveFlagBits bits target).length

def sparseExceptionEffectiveFlagRankBlocksPerSuper
    (_bits : List Bool) (_target : Bool) : Nat := 1

def sparseExceptionEffectiveFlagRankBlockWidth
    (bits : List Bool) (target : Bool) : Nat :=
  sparseExceptionEffectiveFlagRankWordSize bits target

theorem sparseExceptionEffectiveFlagRankWordSize_pos
    (bits : List Bool) (target : Bool) :
    0 < sparseExceptionEffectiveFlagRankWordSize bits target := by
  simp [sparseExceptionEffectiveFlagRankWordSize,
    SuccinctRankProposal.machineWordBits_pos]

theorem sparseExceptionEffectiveFlagRankWordSize_le_machine
    (bits : List Bool) (target : Bool) :
    sparseExceptionEffectiveFlagRankWordSize bits target <=
      SuccinctRankProposal.machineWordBits bits.length := by
  unfold sparseExceptionEffectiveFlagRankWordSize
  exact SuccinctRankProposal.machineWordBits_mono_le
    (sparseExceptionEffectiveFlagBits_length_le_length bits target)

theorem sparseExceptionEffectiveFlagRankBlocksPerSuper_pos
    (bits : List Bool) (target : Bool) :
    0 < sparseExceptionEffectiveFlagRankBlocksPerSuper bits target := by
  simp [sparseExceptionEffectiveFlagRankBlocksPerSuper]

theorem sparseExceptionEffectiveFlagBits_length_lt_rank_word_pow
    (bits : List Bool) (target : Bool) :
    (sparseExceptionEffectiveFlagBits bits target).length <
      2 ^ sparseExceptionEffectiveFlagRankWordSize bits target := by
  simpa [sparseExceptionEffectiveFlagRankWordSize,
    SuccinctRankProposal.machineWordBits] using
    (Nat.lt_log2_self
      (n := (sparseExceptionEffectiveFlagBits bits target).length))

theorem sparseExceptionEffectiveFlagRankBlockSpan_lt_pow
    (bits : List Bool) (target : Bool) :
    sparseExceptionEffectiveFlagRankBlocksPerSuper bits target *
        sparseExceptionEffectiveFlagRankWordSize bits target <
      2 ^ sparseExceptionEffectiveFlagRankBlockWidth bits target := by
  have hword :
      sparseExceptionEffectiveFlagRankWordSize bits target <
        2 ^ sparseExceptionEffectiveFlagRankWordSize bits target := by
    have hsucc :=
      SuccinctSpace.nat_succ_le_two_pow
        (sparseExceptionEffectiveFlagRankWordSize bits target)
    omega
  simpa [sparseExceptionEffectiveFlagRankBlocksPerSuper,
    sparseExceptionEffectiveFlagRankBlockWidth] using hword

def sparseExceptionEffectiveFlagRankSuperOverhead
    (bits : List Bool) (target : Bool) : Nat :=
  (SuccinctRankProposal.canonicalSuperRankSampleTables
    (sparseExceptionEffectiveFlagBits bits target)
    (sparseExceptionEffectiveFlagRankWordSize bits target)
    (sparseExceptionEffectiveFlagRankBlocksPerSuper bits target)
    (sparseExceptionEffectiveFlagRankWordSize bits target)
    (sparseExceptionEffectiveFlagBits_length_lt_rank_word_pow
      bits target)).payload.length

def sparseExceptionEffectiveFlagRankBlockOverhead
    (bits : List Bool) (target : Bool) : Nat :=
  (SuccinctRankProposal.canonicalBlockRankSampleTablesOfLocalSpan
    (sparseExceptionEffectiveFlagBits bits target)
    (sparseExceptionEffectiveFlagRankWordSize bits target)
    (sparseExceptionEffectiveFlagRankBlocksPerSuper bits target)
    (sparseExceptionEffectiveFlagRankBlockWidth bits target)
    (sparseExceptionEffectiveFlagRankBlocksPerSuper_pos bits target)
    (sparseExceptionEffectiveFlagRankBlockSpan_lt_pow bits target)).payload.length

def sparseExceptionEffectiveFlagRankData
    (bits : List Bool) (target : Bool) :
    SuccinctRankProposal.TwoLevelPayloadLiveStoredWordRankData
      (sparseExceptionEffectiveFlagBits bits target)
      (sparseExceptionEffectiveFlagRankSuperOverhead bits target)
      (sparseExceptionEffectiveFlagRankBlockOverhead bits target)
      4 :=
  SuccinctRankProposal.canonicalTwoLevelRankDataOfChunksExactLocalBlock
    (sparseExceptionEffectiveFlagBits bits target)
    (sparseExceptionEffectiveFlagRankWordSize_pos bits target)
    (by
      simp [sparseExceptionEffectiveFlagRankWordSize,
        SuccinctRankProposal.machineWordBits])
    (sparseExceptionEffectiveFlagRankBlocksPerSuper_pos bits target)
    (sparseExceptionEffectiveFlagBits_length_lt_rank_word_pow bits target)
    (sparseExceptionEffectiveFlagRankBlockSpan_lt_pow bits target)
    (Nat.le_refl 4)

theorem sparseExceptionEffectiveFlagRankData_profile
    (bits : List Bool) (target : Bool) :
    let data := sparseExceptionEffectiveFlagRankData bits target
    data.auxPayload.length =
        sparseExceptionEffectiveFlagRankSuperOverhead bits target +
          sparseExceptionEffectiveFlagRankBlockOverhead bits target /\
      data.wordSize <= SuccinctRankProposal.machineWordBits bits.length /\
      data.superWidth <= SuccinctRankProposal.machineWordBits bits.length /\
      data.blockWidth <= SuccinctRankProposal.machineWordBits bits.length /\
      SuccinctSpace.flattenPayloadWords data.bitWords.store.words.toList =
        sparseExceptionEffectiveFlagBits bits target /\
      (forall {word : List Bool},
        List.Mem word data.bitWords.store.words.toList ->
          word.length <= SuccinctRankProposal.machineWordBits bits.length) /\
      forall rankTarget pos,
        (data.rankCosted rankTarget pos).cost <= 4 /\
          (data.rankCosted rankTarget pos).erase =
            RMQ.Succinct.rankPrefix rankTarget
              (sparseExceptionEffectiveFlagBits bits target) pos := by
  have hprofile :=
    SuccinctRankProposal.canonicalTwoLevelRankDataOfChunksExactLocalBlock_profile
      (sparseExceptionEffectiveFlagBits bits target)
      (sparseExceptionEffectiveFlagRankWordSize_pos bits target)
      (by
        simp [sparseExceptionEffectiveFlagRankWordSize,
          SuccinctRankProposal.machineWordBits])
      (sparseExceptionEffectiveFlagRankBlocksPerSuper_pos bits target)
      (sparseExceptionEffectiveFlagBits_length_lt_rank_word_pow bits target)
      (sparseExceptionEffectiveFlagRankBlockSpan_lt_pow bits target)
      (Nat.le_refl 4)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hprofile.1
  · simpa [sparseExceptionEffectiveFlagRankData] using
      (sparseExceptionEffectiveFlagRankWordSize_le_machine bits target)
  · simpa [sparseExceptionEffectiveFlagRankData] using
      (sparseExceptionEffectiveFlagRankWordSize_le_machine bits target)
  · simpa [sparseExceptionEffectiveFlagRankData,
      sparseExceptionEffectiveFlagRankBlockWidth] using
      (sparseExceptionEffectiveFlagRankWordSize_le_machine bits target)
  · exact hprofile.2.2.1
  · intro word hmem
    exact Nat.le_trans (hprofile.2.2.2.1 hmem)
      (SuccinctRankProposal.machineWordBits_mono_le
        (sparseExceptionEffectiveFlagBits_length_le_length bits target))
  · exact hprofile.2.2.2.2

theorem localStride_le_superStride (n : Nat) :
    localStride n <= superStride n := by
  let w := wordBits n
  have hw_pos : 0 < w := by
    simpa [w] using wordBits_pos n
  have hlocal_le_word : localStride n <= w := by
    unfold localStride
    exact Nat.max_le.2
      ⟨by simpa [w] using hw_pos,
        Nat.div_le_self w (ell n * ell n)⟩
  have hword_le_square : w <= w * w := by
    simpa using Nat.mul_le_mul_left w (by omega : 1 <= w)
  exact Nat.le_trans hlocal_le_word
    (by simpa [w, superStride] using hword_le_square)

theorem wordBits_le_two_mul_localStride_mul_ell_sq (n : Nat) :
    wordBits n <= 2 * localStride n * (ell n * ell n) := by
  let w := wordBits n
  let e := ell n
  let denom := e * e
  let q := w / denom
  let stride := localStride n
  have he_pos : 0 < e := by
    simpa [e] using ell_pos n
  have hdenom_pos : 0 < denom := Nat.mul_pos he_pos he_pos
  have hlt : w < q * denom + denom := by
    simpa [q, denom] using Nat.lt_div_mul_add hdenom_pos (a := w)
  have hsucc_le : q + 1 <= 2 * stride := by
    have hstride_def : stride = max 1 q := by
      simp [stride, q, denom, e, w, localStride, ell]
    by_cases hq : q = 0
    · have hstride_ge : 1 <= stride := by
        rw [hstride_def]
        exact Nat.le_max_left 1 q
      omega
    · have hq_pos : 0 < q := Nat.pos_of_ne_zero hq
      have hstride : stride = q := by
        rw [hstride_def]
        exact Nat.max_eq_right (by omega)
      rw [hstride]
      omega
  have hmul : (q + 1) * denom <= 2 * stride * denom := by
    simpa [Nat.mul_assoc] using Nat.mul_le_mul_right denom hsucc_le
  have hle : w <= (q + 1) * denom := by
    rw [Nat.add_mul, Nat.one_mul]
    exact Nat.le_of_lt hlt
  exact Nat.le_trans hle
    (by
      simpa [w, e, denom, stride, q, Nat.mul_assoc,
        Nat.mul_left_comm, Nat.mul_comm] using hmul)

theorem localSlotCount_mul_localStride_le_const_length
    (bits : List Bool) (target : Bool) :
    localSlotCount bits target * localStride bits.length <=
      10 * bits.length := by
  let count := occurrenceCount bits target
  let superStrideV := superStride bits.length
  let localStrideV := localStride bits.length
  let superCount := superSlotCount bits target
  let slots := localSlotsPerSuper bits.length
  by_cases hcount : count = 0
  · have hsuperCount : superCount = 0 := by
      unfold superCount superSlotCount falseSelectCeilDiv
      rw [show occurrenceCount bits target = 0 by simpa [count] using hcount]
      have hstride_pos : 0 < superStrideV := by
        simpa [superStrideV] using superStride_pos bits.length
      have hpred_lt : superStrideV - 1 < superStrideV :=
        Nat.pred_lt (Nat.ne_of_gt hstride_pos)
      simpa [superStrideV] using Nat.div_eq_of_lt hpred_lt
    simp [localSlotCount, superCount, hsuperCount]
  · have hcount_pos : 0 < count := Nat.pos_of_ne_zero hcount
    have hn_pos : 0 < bits.length := by
      have hcountLe : count <= bits.length := by
        simpa [count, occurrenceCount] using
          RMQ.Succinct.rankPrefix_le_length target bits bits.length
      omega
    have hcount_le_len : count <= bits.length := by
      simpa [count, occurrenceCount] using
        RMQ.Succinct.rankPrefix_le_length target bits bits.length
    have hsuperStride_le :
        superStrideV <= 4 * bits.length := by
      have hsq :=
        machineWordBits_sq_le_four_mul_self_of_pos
          (n := bits.length) hn_pos
      simpa [superStrideV, superStride, wordBits] using hsq
    have hsuperCountMul :
        superCount * superStrideV <= count + superStrideV := by
      simpa [superCount, count, superStrideV, superSlotCount] using
        falseSelectCeilDiv_mul_le_add count superStrideV
    have hslotsMul :
        slots * localStrideV <= superStrideV + localStrideV := by
      simpa [slots, superStrideV, localStrideV, localSlotsPerSuper] using
        falseSelectLocalSlotsPerSuper_mul_localStride_le_add
          superStrideV localStrideV
    have hlocal_le_super : localStrideV <= superStrideV := by
      simpa [localStrideV, superStrideV] using
        localStride_le_superStride bits.length
    have hslotsMul' : slots * localStrideV <= 2 * superStrideV := by
      omega
    have hlocalPayload :
        localSlotCount bits target * localStride bits.length <=
          2 * (superCount * superStrideV) := by
      have hmul := Nat.mul_le_mul_left superCount hslotsMul'
      simpa [localSlotCount, superCount, slots, localStrideV,
        superStrideV, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul
    have hsuperBudget :
        2 * (superCount * superStrideV) <= 10 * bits.length := by
      have hscaled := Nat.mul_le_mul_left 2 hsuperCountMul
      have hbudget : 2 * (count + superStrideV) <=
          10 * bits.length := by
        omega
      exact Nat.le_trans
        (by
          simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
            hscaled)
        hbudget
    exact Nat.le_trans hlocalPayload hsuperBudget

theorem payload_le_logLogCubedSampledDirectoryOverhead_of_mul_wordBits_le
    {n payload scale : Nat}
    (hmul :
      payload * wordBits n <=
        scale * n * (ell n * (ell n * ell n))) :
    payload <=
      SuccinctSpace.logLogCubedSampledDirectoryOverhead (2 * scale) n := by
  let w := wordBits n
  let e := ell n
  let e3 := e * (e * e)
  have hw_pos : 0 < w := by
    simpa [w] using wordBits_pos n
  by_cases hn : n = 0
  · have hzeroMul : payload * w = 0 := by
      have hle0 : payload * w <= 0 := by
        simpa [w, e, e3, hn, wordBits, ell] using hmul
      omega
    have hpayload : payload = 0 := by
      cases payload with
      | zero => rfl
      | succ payload =>
          have hpos : 0 < (payload + 1) * w :=
            Nat.mul_pos (by omega) hw_pos
          omega
    simp [SuccinctSpace.logLogCubedSampledDirectoryOverhead,
      hpayload, hn]
  · have hnPos : 0 < n := Nat.pos_of_ne_zero hn
    have hwordLeN : w <= n := by
      simpa [w, wordBits] using machineWordBits_le_self_of_pos hnPos
    let q := n / w
    have hqPos : 0 < q := Nat.div_pos hwordLeN hw_pos
    have hnLt : n < q * w + w := by
      simpa [q] using Nat.lt_div_mul_add hw_pos (a := n)
    have hnLeQ : n <= 2 * q * w := by
      have hsucc : q + 1 <= 2 * q := by omega
      have hleSucc : n <= (q + 1) * w := by
        rw [Nat.add_mul, Nat.one_mul]
        exact Nat.le_of_lt hnLt
      have hmul := Nat.mul_le_mul_right w hsucc
      exact Nat.le_trans hleSucc
        (by
          simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul)
    have hbudget :
        scale * n * e3 <= (2 * scale) * (q * e3) * w := by
      have hscaled := Nat.mul_le_mul_left scale hnLeQ
      have hell := Nat.mul_le_mul_right e3 hscaled
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hell
    have hpayloadWord :
        payload * w <= (2 * scale) * (q * e3) * w := by
      exact Nat.le_trans
        (by
          simpa [w, e, e3, Nat.mul_assoc, Nat.mul_left_comm,
            Nat.mul_comm] using hmul)
        hbudget
    have hpayloadWordLeft :
        w * payload <= w * ((2 * scale) * (q * e3)) := by
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
        hpayloadWord
    have hpayloadLe : payload <= (2 * scale) * (q * e3) :=
      Nat.le_of_mul_le_mul_left hpayloadWordLeft hw_pos
    have hpayloadLe' :
        payload <= scale * (q * (e * (e * (e * 2)))) := by
      simpa [e3, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
        hpayloadLe
    simpa [SuccinctSpace.logLogCubedSampledDirectoryOverhead,
      w, e, q, wordBits, ell, SuccinctRankProposal.machineWordBits,
      Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hpayloadLe'

theorem sparseExceptionEffectiveFlagBits_length_mul_wordBits_le
    (bits : List Bool) (target : Bool) :
    (sparseExceptionEffectiveFlagBits bits target).length *
        wordBits bits.length <=
      20 * ((ell bits.length * (ell bits.length * ell bits.length)) *
        bits.length) := by
  let flagLen := (sparseExceptionEffectiveFlagBits bits target).length
  let m := localSlotCount bits target
  let w := wordBits bits.length
  let stride := localStride bits.length
  let e := ell bits.length
  let e2 := e * e
  let e3 := e * (e * e)
  let n := bits.length
  have heOne : 1 <= e := by
    simpa [e] using ell_pos bits.length
  have hflagLe : flagLen <= m := by
    simpa [flagLen, m, sparseExceptionEffectiveFlagBits_length] using
      sparseExceptionEffectiveLocalSlotCount_le_full bits target
  have hslots : m * stride <= 10 * n := by
    simpa [m, stride, n] using
      localSlotCount_mul_localStride_le_const_length bits target
  have hwordLower : w <= 2 * stride * e2 := by
    simpa [w, stride, e, e2, Nat.mul_assoc, Nat.mul_left_comm,
      Nat.mul_comm] using
      wordBits_le_two_mul_localStride_mul_ell_sq bits.length
  have hmul : flagLen * w <= 20 * (e3 * n) := by
    calc
      flagLen * w <= m * w := by
        exact Nat.mul_le_mul_right w hflagLe
      _ <= m * (2 * stride * e2) := by
        exact Nat.mul_le_mul_left m hwordLower
      _ = 2 * (m * stride) * e2 := by
        simp [Nat.mul_left_comm, Nat.mul_comm]
      _ <= 2 * (10 * n) * e2 := by
        have hscaled := Nat.mul_le_mul_left 2 hslots
        exact Nat.mul_le_mul_right e2 hscaled
      _ <= 20 * (e3 * n) := by
        have he2Le : e2 <= e3 := by
          have hmul := Nat.mul_le_mul_left e2 heOne
          simpa [e2, e3, Nat.mul_left_comm, Nat.mul_comm] using hmul
        have hright := Nat.mul_le_mul_left (20 * n) he2Le
        calc
          2 * (10 * n) * e2 = 20 * n * e2 := by
            simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
          _ <= 20 * n * e3 := by
            simpa using hright
          _ = 20 * (e3 * n) := by
            simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  simpa [flagLen, w, e, e3, n, Nat.mul_assoc, Nat.mul_left_comm,
    Nat.mul_comm] using hmul

theorem sparseExceptionEffectiveFlagBits_length_le_overhead
    (bits : List Bool) (target : Bool) :
    (sparseExceptionEffectiveFlagBits bits target).length <=
      SuccinctSpace.logLogCubedSampledDirectoryOverhead 40 bits.length := by
  let flagLen := (sparseExceptionEffectiveFlagBits bits target).length
  let w := wordBits bits.length
  let e := ell bits.length
  let e3 := e * (e * e)
  let n := bits.length
  exact
    payload_le_logLogCubedSampledDirectoryOverhead_of_mul_wordBits_le
      (n := bits.length) (payload := flagLen) (scale := 20)
      (by
        simpa [flagLen, w, e, e3, n, Nat.mul_assoc,
          Nat.mul_left_comm, Nat.mul_comm] using
          sparseExceptionEffectiveFlagBits_length_mul_wordBits_le bits target)

theorem sparseExceptionEffectiveFlagRankData_auxPayload_le_overhead
    (bits : List Bool) (target : Bool) :
    (sparseExceptionEffectiveFlagRankData bits target).auxPayload.length <=
      SuccinctSpace.logLogCubedSampledDirectoryOverhead 192 bits.length + 16 := by
  let flagBits := sparseExceptionEffectiveFlagBits bits target
  let flagLen := flagBits.length
  let rankWord := sparseExceptionEffectiveFlagRankWordSize bits target
  let w := wordBits bits.length
  let e := ell bits.length
  let e3 := e * (e * e)
  let n := bits.length
  let data := sparseExceptionEffectiveFlagRankData bits target
  have hrankWordPos : 0 < rankWord := by
    simpa [rankWord] using
      sparseExceptionEffectiveFlagRankWordSize_pos bits target
  have hrankWordLeW : rankWord <= w := by
    simpa [rankWord, w, wordBits] using
      sparseExceptionEffectiveFlagRankWordSize_le_machine bits target
  have hauxEq :
      data.auxPayload.length =
        sparseExceptionEffectiveFlagRankSuperOverhead bits target +
          sparseExceptionEffectiveFlagRankBlockOverhead bits target := by
    have hprofile := sparseExceptionEffectiveFlagRankData_profile bits target
    simpa [data] using hprofile.1
  have hsuperLe :
      sparseExceptionEffectiveFlagRankSuperOverhead bits target <=
        2 * (flagLen + rankWord) := by
    unfold sparseExceptionEffectiveFlagRankSuperOverhead
    rw [SuccinctRankProposal.canonicalSuperRankSampleTables_payload_length]
    have hentryLen :
        (SuccinctRankProposal.canonicalSuperRankEntries true flagBits
            rankWord
            (sparseExceptionEffectiveFlagRankBlocksPerSuper
              bits target)).length =
          flagLen / rankWord + 1 := by
      simp [SuccinctRankProposal.canonicalSuperRankEntries, flagBits,
        flagLen, rankWord,
        sparseExceptionEffectiveFlagRankBlocksPerSuper]
    have hentryLenFalse :
        (SuccinctRankProposal.canonicalSuperRankEntries false flagBits
            rankWord
            (sparseExceptionEffectiveFlagRankBlocksPerSuper
              bits target)).length =
          flagLen / rankWord + 1 := by
      simp [SuccinctRankProposal.canonicalSuperRankEntries, flagBits,
        flagLen, rankWord,
        sparseExceptionEffectiveFlagRankBlocksPerSuper]
    rw [hentryLen, hentryLenFalse]
    have hdiv : flagLen / rankWord * rankWord <= flagLen :=
      Nat.div_mul_le_self flagLen rankWord
    calc
      (flagLen / rankWord + 1) * rankWord +
          (flagLen / rankWord + 1) * rankWord <=
        (flagLen + rankWord) + (flagLen + rankWord) := by
          have hone :
              (flagLen / rankWord + 1) * rankWord <=
                flagLen + rankWord := by
            rw [Nat.add_mul, Nat.one_mul]
            exact Nat.add_le_add_right hdiv rankWord
          exact Nat.add_le_add hone hone
      _ = 2 * (flagLen + rankWord) := by omega
  have hblockLe :
      sparseExceptionEffectiveFlagRankBlockOverhead bits target <=
        2 * (flagLen + rankWord) := by
    unfold sparseExceptionEffectiveFlagRankBlockOverhead
    rw [SuccinctRankProposal.canonicalBlockRankSampleTablesOfLocalSpan_payload_length]
    have hentryLen :
        (SuccinctRankProposal.canonicalBlockRankEntries true flagBits
            rankWord
            (sparseExceptionEffectiveFlagRankBlocksPerSuper
              bits target)).length =
          flagLen / rankWord + 1 := by
      simp [SuccinctRankProposal.canonicalBlockRankEntries, flagBits,
        flagLen, rankWord]
    have hentryLenFalse :
        (SuccinctRankProposal.canonicalBlockRankEntries false flagBits
            rankWord
            (sparseExceptionEffectiveFlagRankBlocksPerSuper
              bits target)).length =
          flagLen / rankWord + 1 := by
      simp [SuccinctRankProposal.canonicalBlockRankEntries, flagBits,
        flagLen, rankWord]
    rw [hentryLen, hentryLenFalse]
    have hdiv : flagLen / rankWord * rankWord <= flagLen :=
      Nat.div_mul_le_self flagLen rankWord
    calc
      (flagLen / rankWord + 1) * rankWord +
          (flagLen / rankWord + 1) * rankWord <=
        (flagLen + rankWord) + (flagLen + rankWord) := by
          have hone :
              (flagLen / rankWord + 1) * rankWord <=
                flagLen + rankWord := by
            rw [Nat.add_mul, Nat.one_mul]
            exact Nat.add_le_add_right hdiv rankWord
          exact Nat.add_le_add hone hone
      _ = 2 * (flagLen + rankWord) := by omega
  have hauxLe : data.auxPayload.length <= 4 * (flagLen + rankWord) := by
    rw [hauxEq]
    calc
      sparseExceptionEffectiveFlagRankSuperOverhead bits target +
          sparseExceptionEffectiveFlagRankBlockOverhead bits target <=
        2 * (flagLen + rankWord) + 2 * (flagLen + rankWord) :=
          Nat.add_le_add hsuperLe hblockLe
      _ = 4 * (flagLen + rankWord) := by omega
  by_cases hnZero : n = 0
  · have hflagZero : flagLen = 0 := by
      have hlen := sparseExceptionEffectiveFlagBits_length bits target
      have hcountZero :
          sparseExceptionEffectiveLocalSlotCount bits target = 0 := by
        have hoccZero : occurrenceCount bits target = 0 := by
          have hoccLe :
              occurrenceCount bits target <= bits.length := by
            simpa [occurrenceCount] using
              RMQ.Succinct.rankPrefix_le_length target bits bits.length
          omega
        unfold sparseExceptionEffectiveLocalSlotCount
        simp [hoccZero]
      simpa [flagBits, flagLen, hcountZero] using hlen
    have hw : w = 1 := by
      simp [w, wordBits, SuccinctRankProposal.machineWordBits, n, hnZero]
    have hrankSmall : rankWord <= 1 := by
      simpa [hw] using hrankWordLeW
    have hauxSmall : data.auxPayload.length <= 4 := by
      have h := hauxLe
      rw [hflagZero] at h
      omega
    exact Nat.le_trans hauxSmall (by omega)
  have hflagMul :
      flagLen * w <= 20 * (e3 * n) := by
    simpa [flagBits, flagLen, w, e, e3, n, Nat.mul_assoc,
      Nat.mul_left_comm, Nat.mul_comm] using
      sparseExceptionEffectiveFlagBits_length_mul_wordBits_le bits target
  have hrankMul :
      rankWord * w <= 4 * (e3 * n) := by
    have hwSq : w * w <= 4 * n := by
      have hnPos : 0 < n := Nat.pos_of_ne_zero hnZero
      simpa [w, wordBits, n] using
        machineWordBits_sq_le_four_mul_self_of_pos hnPos
    have hrankW : rankWord * w <= w * w :=
      Nat.mul_le_mul_right w hrankWordLeW
    have he3One : 1 <= e3 := by
      have he : 1 <= e := by simpa [e] using ell_pos bits.length
      have h1 := Nat.mul_le_mul he (Nat.mul_le_mul he he)
      simpa [e3] using h1
    calc
      rankWord * w <= w * w := hrankW
      _ <= 4 * n := hwSq
      _ <= 4 * (e3 * n) := by
        have hmul := Nat.mul_le_mul_right n he3One
        have hscaled := Nat.mul_le_mul_left 4 hmul
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hscaled
  have hauxMul :
      data.auxPayload.length * w <= 96 * (e3 * n) := by
    calc
      data.auxPayload.length * w <=
          4 * (flagLen + rankWord) * w := by
            exact Nat.mul_le_mul_right w hauxLe
      _ = 4 * (flagLen * w + rankWord * w) := by
            simp [Nat.add_mul, Nat.mul_assoc]
      _ <= 4 * (20 * (e3 * n) + 4 * (e3 * n)) := by
            exact Nat.mul_le_mul_left 4
              (Nat.add_le_add hflagMul hrankMul)
      _ = 96 * (e3 * n) := by
            let t := e3 * n
            change 4 * (20 * t + 4 * t) = 96 * t
            omega
  exact
    Nat.le_trans
      (payload_le_logLogCubedSampledDirectoryOverhead_of_mul_wordBits_le
        (n := bits.length) (payload := data.auxPayload.length) (scale := 96)
        (by
          simpa [w, e, e3, n, Nat.mul_assoc, Nat.mul_left_comm,
            Nat.mul_comm] using hauxMul))
      (Nat.le_add_right _ _)

/-! ### Relative-offset tables for long supers and sparse locals -/

/-- Relative offsets stored explicitly for a single long super (empty for short
supers). -/
def longSuperRelativeEntriesForSlot (bits : List Bool) (target : Bool)
    (superSlot : Nat) : List Nat :=
  if superIsLong bits target superSlot then
    let baseOccurrence := superBaseOccurrence bits.length superSlot
    let basePosition := position bits target baseOccurrence
    relativeOffsetsOrZero target bits baseOccurrence (superStride bits.length)
      (superEndOccurrence bits target superSlot) basePosition
  else
    []

def longSuperRelativeEntries (bits : List Bool) (target : Bool) : List Nat :=
  (List.range (superSlotCount bits target)).flatMap
    (longSuperRelativeEntriesForSlot bits target)

/-- Each relative offset fits in a machine word over `bits.length`. -/
def longSuperRelativeWidth (bits : List Bool) : Nat :=
  SuccinctRankProposal.machineWordBits bits.length

theorem longSuperRelativeEntriesForSlot_length
    (bits : List Bool) (target : Bool) (superSlot : Nat) :
    (longSuperRelativeEntriesForSlot bits target superSlot).length =
      if superIsLong bits target superSlot then superStride bits.length
      else 0 := by
  by_cases hlong : superIsLong bits target superSlot = true
  · simp [longSuperRelativeEntriesForSlot, hlong, relativeOffsetsOrZero_length]
  · have hfalse : superIsLong bits target superSlot = false := by
      cases h : superIsLong bits target superSlot
      · rfl
      · contradiction
    simp [longSuperRelativeEntriesForSlot, hfalse]

theorem longSuperRelativeFlatMap_length
    (bits : List Bool) (target : Bool) {n : Nat}
    (hn : n <= superSlotCount bits target) :
    ((List.range n).flatMap
        (longSuperRelativeEntriesForSlot bits target)).length =
      RMQ.Succinct.rankPrefix true (longSuperFlagBits bits target) n *
        superStride bits.length := by
  induction n with
  | zero =>
      simp [RMQ.Succinct.rankPrefix]
  | succ n ih =>
      have hn' : n <= superSlotCount bits target := by omega
      have hslot : n < superSlotCount bits target := by omega
      have hget := longSuperFlagBits_get? bits target (superSlot := n) hslot
      have hrank :=
        rankPrefix_succ_eq_of_get? (target := true)
          (bits := longSuperFlagBits bits target) (n := n) hget
      have hprefix :
          (List.map
              (List.length ∘ longSuperRelativeEntriesForSlot bits target)
              (List.range n)).sum =
            RMQ.Succinct.rankPrefix true (longSuperFlagBits bits target) n *
              superStride bits.length := by
        simpa [List.length_flatMap, Function.comp] using ih hn'
      rw [List.range_succ, List.flatMap_append]
      simp [List.flatMap, longSuperRelativeEntriesForSlot_length, hrank]
      by_cases hlong : superIsLong bits target n = true
      · rw [hprefix]; simp [hlong, Nat.add_mul, Nat.add_comm]
      · have hfalse : superIsLong bits target n = false := by
          cases h : superIsLong bits target n
          · rfl
          · contradiction
        rw [hprefix]; simp [hfalse]

theorem longSuperRelativeEntries_length (bits : List Bool) (target : Bool) :
    (longSuperRelativeEntries bits target).length =
      RMQ.Succinct.rankPrefix true (longSuperFlagBits bits target)
          (superSlotCount bits target) *
        superStride bits.length := by
  simpa [longSuperRelativeEntries] using
    longSuperRelativeFlatMap_length bits target (Nat.le_refl _)

theorem longSuperRelativeEntries_decompose
    (bits : List Bool) (target : Bool) {superSlot : Nat}
    (hslot : superSlot < superSlotCount bits target) :
    longSuperRelativeEntries bits target =
      ((List.range superSlot).flatMap
        (longSuperRelativeEntriesForSlot bits target)) ++
      longSuperRelativeEntriesForSlot bits target superSlot ++
      (((List.range
            (superSlotCount bits target - superSlot - 1)).map
          (fun offset => superSlot + Nat.succ offset)).flatMap
        (longSuperRelativeEntriesForSlot bits target)) := by
  unfold longSuperRelativeEntries
  let tailCount := superSlotCount bits target - superSlot - 1
  have hcount :
      superSlotCount bits target =
        superSlot + (1 + tailCount) := by
    simp [tailCount]
    omega
  calc
    (List.range (superSlotCount bits target)).flatMap
        (longSuperRelativeEntriesForSlot bits target) =
      (List.range (superSlot + (1 + tailCount))).flatMap
        (longSuperRelativeEntriesForSlot bits target) := by
        rw [hcount]
    _ =
      ((List.range superSlot ++
          (List.range (1 + tailCount)).map
            (fun offset => superSlot + offset)).flatMap
        (longSuperRelativeEntriesForSlot bits target)) := by
        rw [List.range_add]
    _ =
      ((List.range superSlot).flatMap
        (longSuperRelativeEntriesForSlot bits target)) ++
      ((List.range (1 + tailCount)).map
          (fun offset => superSlot + offset)).flatMap
        (longSuperRelativeEntriesForSlot bits target) := by
        simp [List.flatMap_append]
    _ =
      ((List.range superSlot).flatMap
        (longSuperRelativeEntriesForSlot bits target)) ++
      longSuperRelativeEntriesForSlot bits target superSlot ++
      (((List.range tailCount).map
          (fun offset => superSlot + Nat.succ offset)).flatMap
        (longSuperRelativeEntriesForSlot bits target)) := by
        have hsucc : 1 + tailCount = tailCount + 1 := by omega
        rw [hsucc, List.range_succ_eq_map]
        simp [List.map, List.flatMap, List.map_map]
        apply congrArg List.flatten
        apply List.map_congr_left
        intro offset _hmem
        rfl

theorem longSuperRelativeEntries_lookup_exact
    (bits : List Bool) (target : Bool)
    {superSlot localOccurrence pos : Nat}
    (hslot : superSlot < superSlotCount bits target)
    (hlong : superIsLong bits target superSlot = true)
    (hocc : localOccurrence < superStride bits.length)
    (hend :
      superBaseOccurrence bits.length superSlot + localOccurrence <
        superEndOccurrence bits target superSlot)
    (hselect :
      RMQ.Succinct.select target bits
          (superBaseOccurrence bits.length superSlot + localOccurrence) =
        some pos) :
    (longSuperRelativeEntries bits target)[
        RMQ.Succinct.rankPrefix true
          (longSuperFlagBits bits target)
          superSlot *
            superStride bits.length +
          localOccurrence]? =
      some
        (pos -
          position bits target
            (superBaseOccurrence bits.length superSlot)) := by
  let pre :=
    (List.range superSlot).flatMap
      (longSuperRelativeEntriesForSlot bits target)
  let slotEntries :=
    longSuperRelativeEntriesForSlot bits target superSlot
  let post :=
    ((List.range
        (superSlotCount bits target - superSlot - 1)).map
      (fun offset => superSlot + Nat.succ offset)).flatMap
        (longSuperRelativeEntriesForSlot bits target)
  have hentries :
      longSuperRelativeEntries bits target =
        pre ++ slotEntries ++ post := by
    simpa [pre, slotEntries, post] using
      longSuperRelativeEntries_decompose bits target hslot
  have hpre :
      pre.length =
        RMQ.Succinct.rankPrefix true
          (longSuperFlagBits bits target)
          superSlot *
            superStride bits.length := by
    simpa [pre] using
      longSuperRelativeFlatMap_length bits target (Nat.le_of_lt hslot)
  have hslotEntries :
      slotEntries =
        relativeOffsetsOrZero target bits
          (superBaseOccurrence bits.length superSlot)
          (superStride bits.length)
          (superEndOccurrence bits target superSlot)
          (position bits target
            (superBaseOccurrence bits.length superSlot)) := by
    simp [slotEntries, longSuperRelativeEntriesForSlot, hlong]
  have hslotLen :
      localOccurrence < slotEntries.length := by
    rw [longSuperRelativeEntriesForSlot_length]
    simp [hlong]
    exact hocc
  have hidx :
      RMQ.Succinct.rankPrefix true
          (longSuperFlagBits bits target)
          superSlot *
            superStride bits.length +
          localOccurrence =
        pre.length + localOccurrence := by
    simp [hpre]
  rw [hentries, hidx]
  rw [List.append_assoc]
  rw [List.getElem?_append_right (by omega)]
  have hsub :
      pre.length + localOccurrence - pre.length =
        localOccurrence := by
    omega
  rw [hsub]
  rw [List.getElem?_append_left hslotLen]
  rw [hslotEntries]
  exact
    relativeOffsetsOrZero_lookup_exact
      (target := target)
      (bits := bits)
      (baseOccurrence := superBaseOccurrence bits.length superSlot)
      (count := superStride bits.length)
      (endOccurrence := superEndOccurrence bits target superSlot)
      (basePosition :=
        position bits target
          (superBaseOccurrence bits.length superSlot))
      (localOccurrence := localOccurrence)
      (pos := pos)
      hocc hend hselect

theorem longSuperRelativeEntries_mem_lt_width
    {bits : List Bool} {target : Bool} {entry : Nat}
    (hmem : List.Mem entry (longSuperRelativeEntries bits target)) :
    entry < 2 ^ longSuperRelativeWidth bits := by
  unfold longSuperRelativeEntries at hmem
  rcases List.mem_flatMap.mp hmem with ⟨superSlot, _hslotMem, hentryMem⟩
  by_cases hlong : superIsLong bits target superSlot = true
  · have hmemOffsets :
        List.Mem entry
          (relativeOffsetsOrZero target bits
            (superBaseOccurrence bits.length superSlot)
            (superStride bits.length)
            (superEndOccurrence bits target superSlot)
            (position bits target
              (superBaseOccurrence bits.length superSlot))) := by
      simpa [longSuperRelativeEntriesForSlot, hlong] using hentryMem
    rcases relativeOffsetsOrZero_mem_cases hmemOffsets with hzero | hsome
    · subst entry
      exact Nat.pow_pos (by omega : 0 < 2)
    · rcases hsome with ⟨offset, pos, _hoff, _hend, hselect, hentry⟩
      have hposLen : pos < bits.length := RMQ.Succinct.select_bounds hselect
      have hentryLen : entry < bits.length := by rw [hentry]; omega
      exact Nat.lt_trans hentryLen
        (by
          simpa [longSuperRelativeWidth, SuccinctRankProposal.machineWordBits]
            using (Nat.lt_log2_self (n := bits.length)))
  · have hfalse : superIsLong bits target superSlot = false := by
      cases h : superIsLong bits target superSlot
      · rfl
      · contradiction
    simp [longSuperRelativeEntriesForSlot, hfalse] at hentryMem

def longSuperRelativeTable (bits : List Bool) (target : Bool) :
    SuccinctSpace.FixedWidthNatTable
      (longSuperRelativeEntries bits target) (longSuperRelativeWidth bits) :=
  SuccinctSpace.FixedWidthNatTable.ofEntries
    (longSuperRelativeEntries bits target) (longSuperRelativeWidth bits)
    (by
      intro entry hmem
      exact longSuperRelativeEntries_mem_lt_width hmem)

theorem longSuperRelativeTable_payload_length
    (bits : List Bool) (target : Bool) :
    (longSuperRelativeTable bits target).payload.length =
      RMQ.Succinct.rankPrefix true (longSuperFlagBits bits target)
          (superSlotCount bits target) *
        superStride bits.length * longSuperRelativeWidth bits := by
  rw [(longSuperRelativeTable bits target).payload_length_eq]
  rw [longSuperRelativeEntries_length]

/-- The long-super relative table's payload, scaled by `ell`, is bounded by the
long-super span sum — the o(n) counting bridge. -/
theorem longSuperRelativeTable_payload_mul_ell_le_spanSum
    (bits : List Bool) (target : Bool) :
    (longSuperRelativeTable bits target).payload.length * ell bits.length <=
      longSuperSpanSum bits target (superSlotCount bits target) := by
  have hcount :=
    longSuperExceptionCount_mul_superLongSpan_le_spanSum bits target
      (Nat.le_refl _)
  rw [longSuperRelativeTable_payload_length]
  simpa [longSuperRelativeWidth, superLongSpan, wordBits,
    Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hcount

/-- Relative positions stored explicitly for a single sparse local block. -/
def sparseRelativeEntriesForSlot (bits : List Bool) (target : Bool)
    (globalLocalSlot : Nat) : List Nat :=
  if localIsSparse bits target globalLocalSlot then
    let baseOccurrence := localBaseOccurrence bits.length globalLocalSlot
    let basePosition := position bits target baseOccurrence
    (selectPositions target bits baseOccurrence (localStride bits.length)).map
      (fun pos => pos - basePosition)
  else
    []

def sparseRelativeEntries (bits : List Bool) (target : Bool) : List Nat :=
  (List.range (localSlotCount bits target)).flatMap
    (sparseRelativeEntriesForSlot bits target)

theorem sparseRelativeEntriesForSlot_length
    (bits : List Bool) (target : Bool) (globalLocalSlot : Nat) :
    (sparseRelativeEntriesForSlot bits target globalLocalSlot).length =
      if localIsSparse bits target globalLocalSlot then localStride bits.length
      else 0 := by
  by_cases hsparse : localIsSparse bits target globalLocalSlot = true
  · simp [sparseRelativeEntriesForSlot, hsparse, selectPositions_length]
  · have hfalse : localIsSparse bits target globalLocalSlot = false := by
      cases h : localIsSparse bits target globalLocalSlot
      · rfl
      · contradiction
    simp [sparseRelativeEntriesForSlot, hfalse]

theorem sparseRelativeEntries_mem_lt_word_pow
    {bits : List Bool} {target : Bool} {entry : Nat}
    (hmem : List.Mem entry (sparseRelativeEntries bits target)) :
    entry < 2 ^ wordBits bits.length := by
  unfold sparseRelativeEntries at hmem
  rcases List.mem_flatMap.mp hmem with ⟨globalLocalSlot, _hslotMem, hentryMem⟩
  unfold sparseRelativeEntriesForSlot at hentryMem
  by_cases hsparse : localIsSparse bits target globalLocalSlot = true
  · simp [hsparse] at hentryMem
    rcases hentryMem with ⟨pos, hposMem, hentryEq⟩
    subst entry
    have hposLe : pos <= bits.length := selectPositions_mem_le_length hposMem
    have hlenLt : bits.length < 2 ^ wordBits bits.length := by
      simpa [wordBits, SuccinctRankProposal.machineWordBits] using
        (Nat.lt_log2_self (n := bits.length))
    omega
  · simp [hsparse] at hentryMem

def sparseRelativeTable (bits : List Bool) (target : Bool) :
    SuccinctSpace.FixedWidthNatTable
      (sparseRelativeEntries bits target) (wordBits bits.length) :=
  SuccinctSpace.FixedWidthNatTable.ofEntries
    (sparseRelativeEntries bits target) (wordBits bits.length)
    (by
      intro entry hmem
      exact sparseRelativeEntries_mem_lt_word_pow hmem)

theorem sparseRelativeTable_payload_length (bits : List Bool) (target : Bool) :
    (sparseRelativeTable bits target).payload.length =
      (sparseRelativeEntries bits target).length * wordBits bits.length :=
  (sparseRelativeTable bits target).payload_length_eq

/-! ### Field widths and fixed-width dense-local entry tables -/

theorem occurrenceCount_le_length (bits : List Bool) (target : Bool) :
    occurrenceCount bits target <= bits.length :=
  RMQ.Succinct.rankPrefix_le_length target bits bits.length

theorem occurrence_lt_count_of_select
    {bits : List Bool} {target : Bool} {occurrence pos : Nat}
    (hselect : RMQ.Succinct.select target bits occurrence = some pos) :
    occurrence < occurrenceCount bits target := by
  have hsucc := rankPrefix_succ_of_select hselect
  have hpos : pos < bits.length := RMQ.Succinct.select_bounds hselect
  have hmono :
      RMQ.Succinct.rankPrefix target bits (pos + 1) <=
        RMQ.Succinct.rankPrefix target bits bits.length :=
    RMQ.Succinct.rankPrefix_mono_limit target bits (Nat.succ_le_of_lt hpos)
  rw [hsucc] at hmono
  have hcount : occurrence + 1 <= occurrenceCount bits target := hmono
  omega

theorem superIsLong_false_span_le
    (bits : List Bool) (target : Bool) {superSlot : Nat}
    (hshort : superIsLong bits target superSlot = false) :
    superSpan bits target superSlot <= superLongSpan bits.length := by
  unfold superIsLong at hshort
  simp at hshort
  omega

/-- In a short (dense) super, any selected position lies within `superLongSpan`
of a local base — the key fact bounding the relative local word-index field. -/
theorem selected_offset_lt_superLongSpan
    (bits : List Bool) (target : Bool) (superSlot : Nat)
    {localBaseOcc q pos : Nat}
    (hshort : superIsLong bits target superSlot = false)
    (hsuperBase : superBaseOccurrence bits.length superSlot <= localBaseOcc)
    (hlocalBase : localBaseOcc <= q)
    (hqEnd : q < superEndOccurrence bits target superSlot)
    (hselect : RMQ.Succinct.select target bits q = some pos) :
    pos - position bits target localBaseOcc < superLongSpan bits.length := by
  let superBase := superBaseOccurrence bits.length superSlot
  let superEnd := superEndOccurrence bits target superSlot
  have hqCount : q < occurrenceCount bits target :=
    occurrence_lt_count_of_select hselect
  have hlocalCount : localBaseOcc < occurrenceCount bits target := by omega
  have hsuperCount : superBase < occurrenceCount bits target := by omega
  rcases select_exists_of_lt_occurrenceCount bits target hlocalCount with
    ⟨localBasePos, hlocalSelect⟩
  rcases select_exists_of_lt_occurrenceCount bits target hsuperCount with
    ⟨superBasePos, hsuperSelect⟩
  have hsuperEndLeCount : superEnd <= occurrenceCount bits target :=
    Nat.min_le_right _ _
  have hsuperEndPos : 0 < superEnd := by omega
  have hlastCount : superEnd - 1 < occurrenceCount bits target := by omega
  rcases select_exists_of_lt_occurrenceCount bits target hlastCount with
    ⟨lastPos, hlastSelect⟩
  have hsuperBasePos_le_localBasePos : superBasePos <= localBasePos :=
    select_index_mono (target := target) (bits := bits)
      (lo := superBase) (hi := localBaseOcc)
      (by simpa [superBase] using hsuperBase) hsuperSelect hlocalSelect
  have hlocalBasePos_le_pos : localBasePos <= pos :=
    select_index_mono (target := target) (bits := bits)
      (lo := localBaseOcc) (hi := q) hlocalBase hlocalSelect hselect
  have hqLeLast : q <= superEnd - 1 := by omega
  have hpos_le_last : pos <= lastPos :=
    select_index_mono (target := target) (bits := bits)
      (lo := q) (hi := superEnd - 1) hqLeLast hselect hlastSelect
  have hspanLe := superIsLong_false_span_le bits target hshort
  have hsuperSelectRaw :
      RMQ.Succinct.select target bits
          (superSlot * superStride bits.length) = some superBasePos := by
    simpa [superBase, superBaseOccurrence] using hsuperSelect
  have hlastSelectRaw :
      RMQ.Succinct.select target bits
          ((superSlot * superStride bits.length + superStride bits.length).min
              (occurrenceCount bits target) - 1) = some lastPos := by
    simpa [superEnd, superEndOccurrence, superBaseOccurrence] using hlastSelect
  have hspanEq :
      superSpan bits target superSlot = lastPos + 1 - superBasePos := by
    simp [superSpan, superBaseOccurrence, superEndOccurrence, position,
      hsuperSelectRaw, hlastSelectRaw]
  rw [hspanEq] at hspanLe
  have hlocalPosEq : position bits target localBaseOcc = localBasePos :=
    position_eq_of_select bits target hlocalSelect
  rw [hlocalPosEq]
  have hoffLt : pos - localBasePos < lastPos + 1 - superBasePos := by omega
  omega

/-- Super-entry field width: a full machine word over `bits.length`. -/
def superFieldWidth (bits : List Bool) : Nat := wordBits bits.length

theorem superEntries_mem_fields_lt_width
    {bits : List Bool} {target : Bool}
    {entry : SparseDenseFalseSelectDenseLocalEntry}
    (hmem : List.Mem entry (superEntries bits target)) :
    entry.baseOccurrence < 2 ^ superFieldWidth bits /\
      entry.baseWordIndex < 2 ^ superFieldWidth bits /\
        entry.rankBefore < 2 ^ superFieldWidth bits /\
          entry.firstOffset < 2 ^ superFieldWidth bits := by
  rcases List.mem_map.mp hmem with ⟨superSlot, hslotMem, rfl⟩
  have hslot : superSlot < superSlotCount bits target :=
    List.mem_range.mp hslotMem
  let wordSize := wordBits bits.length
  let baseOccurrence := superBaseOccurrence bits.length superSlot
  let basePosition := position bits target baseOccurrence
  have hwordPos : 0 < wordSize := by
    simpa [wordSize] using wordBits_pos bits.length
  have hbaseCount : baseOccurrence < occurrenceCount bits target := by
    simpa [baseOccurrence] using superBaseOccurrence_lt_count bits target hslot
  have hbaseLen : baseOccurrence < bits.length :=
    Nat.lt_of_lt_of_le hbaseCount (occurrenceCount_le_length bits target)
  have hlenPow : bits.length < 2 ^ wordSize := by
    simpa [wordSize, wordBits, SuccinctRankProposal.machineWordBits] using
      (Nat.lt_log2_self (n := bits.length))
  have hbasePow : baseOccurrence < 2 ^ wordSize := Nat.lt_trans hbaseLen hlenPow
  have hpositionLen : basePosition <= bits.length := by
    simpa [basePosition] using position_le_length bits target baseOccurrence
  have hwordIndexPow : basePosition / wordSize < 2 ^ wordSize := by
    have hdivLe : basePosition / wordSize <= basePosition := Nat.div_le_self _ _
    exact Nat.lt_of_le_of_lt (Nat.le_trans hdivLe hpositionLen) hlenPow
  have hmarkPow :
      (if superIsLong bits target superSlot then 1 else 0) < 2 ^ wordSize := by
    by_cases hlong : superIsLong bits target superSlot = true
    · simp [hlong, one_lt_two_pow_of_pos hwordPos]
    · have hfalse : superIsLong bits target superSlot = false := by
        cases h : superIsLong bits target superSlot
        · rfl
        · contradiction
      simp [hfalse, Nat.pow_pos (by omega : 0 < 2)]
  have hoffsetLtWord :
      basePosition - basePosition / wordSize * wordSize < wordSize := by
    simpa [Nat.mod_eq_sub_div_mul] using Nat.mod_lt basePosition hwordPos
  have hoffsetPow :
      basePosition - basePosition / wordSize * wordSize < 2 ^ wordSize :=
    Nat.lt_trans hoffsetLtWord
      (by
        have hsucc := SuccinctSpace.nat_succ_le_two_pow wordSize
        omega)
  simpa [superEntry, superFieldWidth, wordSize, baseOccurrence, basePosition]
    using ⟨hbasePow, hwordIndexPow, hmarkPow, hoffsetPow⟩

def superTable (bits : List Bool) (target : Bool) :
    FixedWidthSparseDenseFalseSelectDenseLocalEntryTable
      (superEntries bits target) (superFieldWidth bits) :=
  FixedWidthSparseDenseFalseSelectDenseLocalEntryTable.ofEntries
    (superEntries bits target) (superFieldWidth bits)
    (by
      intro entry hmem
      exact superEntries_mem_fields_lt_width hmem)

/-- Local-entry field width: a machine word over `min bits.length superLongSpan`
(local entries store values relative to their owning super, so a short-super
word suffices). -/
def sparseExceptionRelativeWidth (bits : List Bool) : Nat :=
  SuccinctRankProposal.machineWordBits
    (Nat.min bits.length (superLongSpan bits.length))

def localFieldWidth (bits : List Bool) : Nat := sparseExceptionRelativeWidth bits

theorem sparseExceptionRelativeWidth_le_four_ell (bits : List Bool) :
    sparseExceptionRelativeWidth bits <= 4 * ell bits.length := by
  let w := wordBits bits.length
  let e := ell bits.length
  let m := Nat.min bits.length (superLongSpan bits.length)
  by_cases hm : m = 0
  · have hell_pos : 0 < e := by
      simpa [e] using ell_pos bits.length
    simp [sparseExceptionRelativeWidth, SuccinctRankProposal.machineWordBits,
      m, hm, ell]
    omega
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hw_pos : 0 < w := by
      simpa [w] using wordBits_pos bits.length
    have he_pos : 0 < e := by
      simpa [e] using ell_pos bits.length
    have hw_lt_pow : w < 2 ^ e := by
      simpa [w, e, ell, wordBits, SuccinctRankProposal.machineWordBits] using
        (Nat.lt_log2_self (n := w))
    have hw_le_pow : w <= 2 ^ e := Nat.le_of_lt hw_lt_pow
    have he_le_pow : e <= 2 ^ e := SuccinctSpace.nat_le_two_pow e
    have hww_le : w * w <= 2 ^ e * 2 ^ e :=
      Nat.mul_le_mul hw_le_pow hw_le_pow
    have hww_pos : 0 < w * w := Nat.mul_pos hw_pos hw_pos
    have hwww_lt_step : (w * w) * w < (w * w) * 2 ^ e :=
      Nat.mul_lt_mul_of_pos_left hw_lt_pow hww_pos
    have hwww_le_step :
        (w * w) * 2 ^ e <= (2 ^ e * 2 ^ e) * 2 ^ e :=
      Nat.mul_le_mul_right (2 ^ e) hww_le
    have hwww_lt : w * w * w < 2 ^ e * 2 ^ e * 2 ^ e := by
      exact Nat.lt_of_lt_of_le
        (by simpa [Nat.mul_assoc] using hwww_lt_step)
        (by simpa [Nat.mul_assoc] using hwww_le_step)
    have hleft_lt :
        (w * w * w) * e < (2 ^ e * 2 ^ e * 2 ^ e) * e :=
      Nat.mul_lt_mul_of_pos_right hwww_lt he_pos
    have hright_le :
        (2 ^ e * 2 ^ e * 2 ^ e) * e <=
          (2 ^ e * 2 ^ e * 2 ^ e) * 2 ^ e :=
      Nat.mul_le_mul_left (2 ^ e * 2 ^ e * 2 ^ e) he_le_pow
    have hpows : (2 ^ e * 2 ^ e * 2 ^ e) * 2 ^ e = 2 ^ (4 * e) := by
      calc
        (2 ^ e * 2 ^ e * 2 ^ e) * 2 ^ e =
            (((2 ^ e * 2 ^ e) * 2 ^ e) * 2 ^ e) := by
              simp [Nat.mul_assoc]
        _ = ((2 ^ (e + e) * 2 ^ e) * 2 ^ e) := by
              rw [← Nat.pow_add]
        _ = (2 ^ (e + e + e) * 2 ^ e) := by
              rw [← Nat.pow_add]
        _ = 2 ^ (e + e + e + e) := by
              rw [← Nat.pow_add]
        _ = 2 ^ (4 * e) := by
              congr 1
              omega
    have hsuper_lt : superLongSpan bits.length < 2 ^ (4 * e) := by
      have hraw : (w * w * w) * e < 2 ^ (4 * e) := by
        have h := Nat.lt_of_lt_of_le hleft_lt hright_le
        rwa [hpows] at h
      simpa [superLongSpan, superStride, w, e, Nat.mul_assoc,
        Nat.mul_left_comm, Nat.mul_comm] using hraw
    have hm_lt : m < 2 ^ (4 * e) :=
      Nat.lt_of_le_of_lt (Nat.min_le_right _ _) hsuper_lt
    have hlog := natLog2_succ_le_of_pos_lt_pow hmpos hm_lt
    simpa [sparseExceptionRelativeWidth,
      SuccinctRankProposal.machineWordBits, m, e] using hlog

theorem ell_square_le_sixtyFour_wordBits (n : Nat) :
    ell n * ell n <= 64 * wordBits n := by
  let w := wordBits n
  let q := Nat.log2 w
  have hw_pos : 0 < w := by
    simpa [w] using wordBits_pos n
  by_cases hlarge : 6 <= q
  · have hw_ne : w ≠ 0 := by omega
    have hsq : (q + 1) * (q + 1) <= w :=
      Nat.le_trans
        (nat_succ_square_le_two_pow_of_six_le q hlarge)
        (Nat.log2_self_le hw_ne)
    have hw_le : w <= 64 * w := by omega
    exact Nat.le_trans
      (by simpa [q, w, ell] using hsq)
      hw_le
  · have hq_le : q <= 5 := by omega
    have hell_le : ell n <= 6 := by
      simpa [ell, q, w] using Nat.succ_le_succ hq_le
    have hell_square_le : ell n * ell n <= 6 * 6 :=
      Nat.mul_le_mul hell_le hell_le
    have hconst : 6 * 6 <= 64 * w := by omega
    exact Nat.le_trans hell_square_le hconst

theorem sparseException_localStride_mul_width_mul_ell_le_const_wordBits
    (bits : List Bool) :
    localStride bits.length * sparseExceptionRelativeWidth bits *
        ell bits.length <=
      512 * wordBits bits.length := by
  let w := wordBits bits.length
  let e := ell bits.length
  let denom := e * e
  let q := w / denom
  let stride := localStride bits.length
  let width := sparseExceptionRelativeWidth bits
  have hstride : stride <= q + 1 := by
    have hmax : max 1 q <= q + 1 :=
      Nat.max_le.2 ⟨Nat.succ_pos q, Nat.le_succ q⟩
    simpa [stride, q, denom, w, e, localStride, ell] using hmax
  have hwidth : width <= 4 * e := by
    simpa [width, e] using sparseExceptionRelativeWidth_le_four_ell bits
  have hfirst :
      stride * width * e <= (q + 1) * (4 * e) * e := by
    have hmul := Nat.mul_le_mul hstride hwidth
    exact Nat.mul_le_mul_right e hmul
  have hqdenom : q * denom <= w := Nat.div_mul_le_self w denom
  have hqdenom_succ : (q + 1) * denom <= w + denom := by
    calc
      (q + 1) * denom = q * denom + denom := by
        rw [Nat.add_mul]
        simp
      _ <= w + denom := Nat.add_le_add_right hqdenom denom
  have hell_square : denom <= 64 * w := by
    simpa [denom, e, w] using ell_square_le_sixtyFour_wordBits bits.length
  have hqdenom_budget : 4 * ((q + 1) * denom) <= 512 * w := by
    have hsum : w + denom <= 65 * w := by omega
    have hsucc_le : (q + 1) * denom <= 65 * w :=
      Nat.le_trans hqdenom_succ hsum
    have hmul := Nat.mul_le_mul_left 4 hsucc_le
    omega
  have hright : (q + 1) * (4 * e) * e <= 512 * w := by
    have hrewrite :
        (q + 1) * (4 * e) * e = 4 * ((q + 1) * denom) := by
      simp [denom, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    simpa [hrewrite] using hqdenom_budget
  exact Nat.le_trans hfirst hright

theorem localEntries_mem_fields_lt_width
    {bits : List Bool} {target : Bool}
    {entry : SparseDenseFalseSelectDenseLocalEntry}
    (hmem : List.Mem entry (localEntries bits target)) :
    entry.baseOccurrence < 2 ^ localFieldWidth bits /\
      entry.baseWordIndex < 2 ^ localFieldWidth bits /\
        entry.rankBefore < 2 ^ localFieldWidth bits /\
          entry.firstOffset < 2 ^ localFieldWidth bits := by
  rcases List.mem_map.mp hmem with ⟨globalLocalSlot, _hslotMem, rfl⟩
  let superSlot := localSuperSlot bits.length globalLocalSlot
  let superBase := superBaseOccurrence bits.length superSlot
  let base := localBaseOccurrence bits.length globalLocalSlot
  let superPos := position bits target superBase
  let basePos := position bits target base
  let wordSize := wordBits bits.length
  let longSpan := superLongSpan bits.length
  let relWidth := localFieldWidth bits
  have hwordPos : 0 < wordSize := by
    simpa [wordSize] using wordBits_pos bits.length
  have hellPos : 0 < ell bits.length := ell_pos bits.length
  have hrelPos : 0 < relWidth := by
    simp [relWidth, localFieldWidth, sparseExceptionRelativeWidth,
      SuccinctRankProposal.machineWordBits_pos]
  have hpowPos : 0 < 2 ^ relWidth := Nat.pow_pos (by omega : 0 < 2)
  have hfield_of_lt_min :
      forall {x : Nat}, x < bits.length -> x < longSpan -> x < 2 ^ relWidth := by
    intro x hbp hlong
    have hmin : x < Nat.min bits.length (superLongSpan bits.length) :=
      Nat.lt_min.mpr ⟨hbp, by simpa [longSpan] using hlong⟩
    simpa [relWidth, localFieldWidth, sparseExceptionRelativeWidth] using
      lt_two_pow_machineWordBits_of_lt hmin
  by_cases hlive : compactLocalEntryIsLive bits target globalLocalSlot = true
  · have hliveFacts :
        superIsLong bits target superSlot = false /\
          base < occurrenceCount bits target := by
      unfold compactLocalEntryIsLive at hlive
      by_cases hlong : superIsLong bits target superSlot = true
      · simp [superSlot, hlong] at hlive
      · have hfalse : superIsLong bits target superSlot = false := by
          cases h : superIsLong bits target superSlot
          · rfl
          · contradiction
        simp [superSlot, hfalse] at hlive
        exact ⟨hfalse, hlive⟩
    rcases hliveFacts with ⟨hshort, hbaseCount⟩
    have hsuperBaseLeBase : superBase <= base := by
      simp [superBase, base, superSlot, superBaseOccurrence, localSuperSlot,
        localBaseOccurrence, localSlotInSuperOfGlobal]
    have hbaseBoundary :
        base < superBase + superStride bits.length := by
      simpa [base, superBase, superSlot, superBaseOccurrence, localSuperSlot]
        using localBaseOccurrence_lt_superBoundary bits.length globalLocalSlot
    have hbaseEnd : base < superEndOccurrence bits target superSlot := by
      unfold superEndOccurrence
      exact Nat.lt_min.mpr
        ⟨by simpa [superBase, superBaseOccurrence] using hbaseBoundary,
          hbaseCount⟩
    have hbaseBp : base < bits.length :=
      Nat.lt_of_lt_of_le hbaseCount (occurrenceCount_le_length bits target)
    have hdeltaBp : base - superBase < bits.length := by omega
    have hstrideLeLong : superStride bits.length <= longSpan := by
      have hwordOne : 1 <= wordSize := by omega
      have hellOne : 1 <= ell bits.length := by omega
      have h1 :
          superStride bits.length <= superStride bits.length * wordSize := by
        simpa using Nat.mul_le_mul_left (superStride bits.length) hwordOne
      have h2 :
          superStride bits.length * wordSize <=
            superStride bits.length * wordSize * ell bits.length := by
        simpa using
          Nat.mul_le_mul_left (superStride bits.length * wordSize) hellOne
      exact Nat.le_trans h1 (by
        simpa [longSpan, superLongSpan, superStride, wordSize,
          Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h2)
    have hdeltaLong : base - superBase < longSpan := by
      have hdeltaStride : base - superBase < superStride bits.length := by omega
      exact Nat.lt_of_lt_of_le hdeltaStride hstrideLeLong
    have hbaseField : base - superBase < 2 ^ relWidth :=
      hfield_of_lt_min hdeltaBp hdeltaLong
    have hsuperCount : superBase < occurrenceCount bits target := by omega
    have hbasePosLt : basePos < bits.length := by
      simpa [basePos] using position_lt_length_of_lt_count bits target hbaseCount
    have hsuperPosLt : superPos < bits.length := by
      simpa [superPos] using
        position_lt_length_of_lt_count bits target hsuperCount
    have hposMono : superPos <= basePos := by
      simpa [superPos, basePos] using position_mono bits target hsuperBaseLeBase
    have hindexDeltaLe :
        basePos / wordSize - superPos / wordSize <= basePos - superPos :=
      nat_div_sub_div_le_sub hwordPos hposMono
    have hindexBp :
        basePos / wordSize - superPos / wordSize < bits.length := by
      have hdivLe : basePos / wordSize <= basePos := Nat.div_le_self _ _
      omega
    rcases select_exists_of_lt_occurrenceCount bits target hbaseCount with
      ⟨baseWitness, hbaseSelect⟩
    have hbasePosEq : basePos = baseWitness := by
      simpa [basePos] using position_eq_of_select bits target hbaseSelect
    have hoffLongWitness : baseWitness - superPos < longSpan := by
      have hraw :=
        selected_offset_lt_superLongSpan bits target superSlot
          (localBaseOcc := superBase) (q := base) (pos := baseWitness)
          hshort (by simp [superBase]) hsuperBaseLeBase hbaseEnd hbaseSelect
      simpa [superPos, superBase, longSpan] using hraw
    have hoffLong : basePos - superPos < longSpan := by
      simpa [hbasePosEq] using hoffLongWitness
    have hindexLong :
        basePos / wordSize - superPos / wordSize < longSpan :=
      Nat.lt_of_le_of_lt hindexDeltaLe hoffLong
    have hindexField :
        basePos / wordSize - superPos / wordSize < 2 ^ relWidth :=
      hfield_of_lt_min hindexBp hindexLong
    have hmarkField :
        (if localIsSparseException bits target globalLocalSlot then 1 else 0) <
          2 ^ relWidth := by
      by_cases hflag : localIsSparseException bits target globalLocalSlot = true
      · have hone : 1 < 2 ^ relWidth := one_lt_two_pow_of_pos hrelPos
        simpa [hflag] using hone
      · have hfalse :
            localIsSparseException bits target globalLocalSlot = false := by
          cases h : localIsSparseException bits target globalLocalSlot
          · rfl
          · contradiction
        simp [hfalse, hpowPos]
    have hoffsetLtWord :
        basePos - basePos / wordSize * wordSize < wordSize := by
      simpa [Nat.mod_eq_sub_div_mul] using Nat.mod_lt basePos hwordPos
    have hbpLenPos : 0 < bits.length := by omega
    have hwordLeBp : wordSize <= bits.length := by
      simpa [wordSize, wordBits] using machineWordBits_le_self_of_pos hbpLenPos
    have hwordLeLong : wordSize <= longSpan := by
      have hwordOne : 1 <= wordSize := by omega
      have hellOne : 1 <= ell bits.length := by omega
      have hleStride :
          wordSize <= superStride bits.length * wordSize := by
        have hmul :=
          Nat.mul_le_mul_right wordSize
            (show 1 <= superStride bits.length from superStride_pos bits.length)
        simpa [Nat.mul_comm] using hmul
      have hleLong :
          superStride bits.length * wordSize <= longSpan := by
        have hmul :=
          Nat.mul_le_mul_left (superStride bits.length * wordSize) hellOne
        simpa [longSpan, superLongSpan, superStride, wordSize,
          Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul
      exact Nat.le_trans hleStride hleLong
    have hoffsetBp :
        basePos - basePos / wordSize * wordSize < bits.length :=
      Nat.lt_of_lt_of_le hoffsetLtWord hwordLeBp
    have hoffsetLong :
        basePos - basePos / wordSize * wordSize < longSpan :=
      Nat.lt_of_lt_of_le hoffsetLtWord hwordLeLong
    have hoffsetField :
        basePos - basePos / wordSize * wordSize < 2 ^ relWidth :=
      hfield_of_lt_min hoffsetBp hoffsetLong
    simpa [localEntry, hlive, localFieldWidth, relWidth, superSlot, superBase,
      base, superPos, basePos, wordSize] using
      ⟨hbaseField, hindexField, hmarkField, hoffsetField⟩
  · have hfalse : compactLocalEntryIsLive bits target globalLocalSlot = false := by
      cases h : compactLocalEntryIsLive bits target globalLocalSlot
      · rfl
      · exact False.elim (hlive h)
    have htuple :
        0 < 2 ^ relWidth /\ 0 < 2 ^ relWidth /\
          0 < 2 ^ relWidth /\ 0 < 2 ^ relWidth :=
      ⟨hpowPos, hpowPos, hpowPos, hpowPos⟩
    simpa [localEntry, hfalse, localFieldWidth, relWidth] using htuple

def localTable (bits : List Bool) (target : Bool) :
    FixedWidthSparseDenseFalseSelectDenseLocalEntryTable
      (localEntries bits target) (localFieldWidth bits) :=
  FixedWidthSparseDenseFalseSelectDenseLocalEntryTable.ofEntries
    (localEntries bits target) (localFieldWidth bits)
    (by
      intro entry hmem
      exact localEntries_mem_fields_lt_width hmem)

/-! ### Sparse-exception relative table (relative offsets within long supers) -/

/-- Relative positions stored explicitly for a single sparse-exception local
block (a sparse local inside a short super). -/
def sparseExceptionRelativeEntriesForSlot (bits : List Bool) (target : Bool)
    (globalLocalSlot : Nat) : List Nat :=
  if localIsSparseException bits target globalLocalSlot then
    let superSlot := localSuperSlot bits.length globalLocalSlot
    let baseOccurrence := localBaseOccurrence bits.length globalLocalSlot
    let basePosition := position bits target baseOccurrence
    relativeOffsetsOrZero target bits baseOccurrence (localStride bits.length)
      (superEndOccurrence bits target superSlot) basePosition
  else
    []

theorem sparseExceptionRelativeEntriesForSlot_length
    (bits : List Bool) (target : Bool) (globalLocalSlot : Nat) :
    (sparseExceptionRelativeEntriesForSlot bits target globalLocalSlot).length =
      if localIsSparseException bits target globalLocalSlot then
        localStride bits.length
      else
        0 := by
  by_cases hflag : localIsSparseException bits target globalLocalSlot = true
  · simp [sparseExceptionRelativeEntriesForSlot, hflag,
      relativeOffsetsOrZero_length]
  · have hfalse :
        localIsSparseException bits target globalLocalSlot = false := by
      cases h : localIsSparseException bits target globalLocalSlot
      · rfl
      · contradiction
    simp [sparseExceptionRelativeEntriesForSlot, hfalse]

def sparseExceptionRelativeEntries (bits : List Bool) (target : Bool) :
    List Nat :=
  (List.range (localSlotCount bits target)).flatMap
    (sparseExceptionRelativeEntriesForSlot bits target)

theorem sparseExceptionRelativePrefix_length
    (bits : List Bool) (target : Bool) {n : Nat}
    (hn : n <= localSlotCount bits target) :
    ((List.range n).flatMap
        (sparseExceptionRelativeEntriesForSlot bits target)).length =
      RMQ.Succinct.rankPrefix true (sparseExceptionFlagBits bits target) n *
        localStride bits.length := by
  induction n with
  | zero =>
      simp [RMQ.Succinct.rankPrefix]
  | succ n ih =>
      have hn' : n <= localSlotCount bits target := by omega
      have hslot : n < localSlotCount bits target := by omega
      have hget :=
        sparseExceptionFlagBits_get? bits target (globalLocalSlot := n) hslot
      have hrank :=
        rankPrefix_succ_eq_of_get?
          (target := true) (bits := sparseExceptionFlagBits bits target)
          (n := n) hget
      have hprefix :
          (List.map
              (List.length ∘
                sparseExceptionRelativeEntriesForSlot bits target)
              (List.range n)).sum =
            RMQ.Succinct.rankPrefix true (sparseExceptionFlagBits bits target) n *
              localStride bits.length := by
        simpa [List.length_flatMap, Function.comp] using ih hn'
      rw [List.range_succ]
      rw [List.flatMap_append]
      simp [List.flatMap, sparseExceptionRelativeEntriesForSlot_length, hrank]
      by_cases hflag : localIsSparseException bits target n = true
      · rw [hprefix]
        simp [hflag, Nat.add_mul, Nat.add_comm]
      · have hfalse : localIsSparseException bits target n = false := by
          cases h : localIsSparseException bits target n
          · rfl
          · contradiction
        rw [hprefix]
        simp [hfalse]

theorem sparseExceptionRelativeEntries_length
    (bits : List Bool) (target : Bool) :
    (sparseExceptionRelativeEntries bits target).length =
      RMQ.Succinct.rankPrefix true (sparseExceptionFlagBits bits target)
        (localSlotCount bits target) *
        localStride bits.length := by
  simpa [sparseExceptionRelativeEntries] using
    sparseExceptionRelativePrefix_length bits target (Nat.le_refl _)

theorem sparseExceptionRelativeEntries_decompose
    (bits : List Bool) (target : Bool) {globalLocalSlot : Nat}
    (hslot :
      globalLocalSlot < localSlotCount bits target) :
    sparseExceptionRelativeEntries bits target =
      ((List.range globalLocalSlot).flatMap
        (sparseExceptionRelativeEntriesForSlot bits target)) ++
      sparseExceptionRelativeEntriesForSlot bits target
        globalLocalSlot ++
      (((List.range
            (localSlotCount bits target - globalLocalSlot - 1)).map
          (fun offset => globalLocalSlot + Nat.succ offset)).flatMap
        (sparseExceptionRelativeEntriesForSlot bits target)) := by
  unfold sparseExceptionRelativeEntries
  let tailCount := localSlotCount bits target - globalLocalSlot - 1
  have hcount :
      localSlotCount bits target =
        globalLocalSlot + (1 + tailCount) := by
    simp [tailCount]
    omega
  calc
    (List.range (localSlotCount bits target)).flatMap
        (sparseExceptionRelativeEntriesForSlot bits target) =
      (List.range (globalLocalSlot + (1 + tailCount))).flatMap
        (sparseExceptionRelativeEntriesForSlot bits target) := by
        rw [hcount]
    _ =
      ((List.range globalLocalSlot ++
          (List.range (1 + tailCount)).map
            (fun offset => globalLocalSlot + offset)).flatMap
        (sparseExceptionRelativeEntriesForSlot bits target)) := by
        rw [List.range_add]
    _ =
      ((List.range globalLocalSlot).flatMap
        (sparseExceptionRelativeEntriesForSlot bits target)) ++
      ((List.range (1 + tailCount)).map
          (fun offset => globalLocalSlot + offset)).flatMap
        (sparseExceptionRelativeEntriesForSlot bits target) := by
        simp [List.flatMap_append]
    _ =
      ((List.range globalLocalSlot).flatMap
        (sparseExceptionRelativeEntriesForSlot bits target)) ++
      sparseExceptionRelativeEntriesForSlot bits target
        globalLocalSlot ++
      (((List.range tailCount).map
          (fun offset => globalLocalSlot + Nat.succ offset)).flatMap
        (sparseExceptionRelativeEntriesForSlot bits target)) := by
        have hsucc : 1 + tailCount = tailCount + 1 := by omega
        rw [hsucc, List.range_succ_eq_map]
        simp [List.map, List.flatMap, List.map_map]
        apply congrArg List.flatten
        apply List.map_congr_left
        intro offset _hmem
        rfl

theorem sparseExceptionRelativeEntries_lookup_exact
    (bits : List Bool) (target : Bool)
    {globalLocalSlot localOccurrence pos : Nat}
    (hslot :
      globalLocalSlot < localSlotCount bits target)
    (hflag :
      localIsSparseException bits target globalLocalSlot = true)
    (hocc :
      localOccurrence < localStride bits.length)
    (hend :
      localBaseOccurrence bits.length globalLocalSlot + localOccurrence <
        superEndOccurrence bits target
          (localSuperSlot bits.length globalLocalSlot))
    (hselect :
      RMQ.Succinct.select target bits
          (localBaseOccurrence bits.length globalLocalSlot + localOccurrence) =
        some pos) :
    (sparseExceptionRelativeEntries bits target)[
        RMQ.Succinct.rankPrefix true
          (sparseExceptionFlagBits bits target)
          globalLocalSlot *
            localStride bits.length +
          localOccurrence]? =
      some
        (pos -
          position bits target
            (localBaseOccurrence bits.length globalLocalSlot)) := by
  let pre :=
    (List.range globalLocalSlot).flatMap
      (sparseExceptionRelativeEntriesForSlot bits target)
  let slotEntries :=
    sparseExceptionRelativeEntriesForSlot bits target globalLocalSlot
  let post :=
    ((List.range
        (localSlotCount bits target - globalLocalSlot - 1)).map
      (fun offset => globalLocalSlot + Nat.succ offset)).flatMap
        (sparseExceptionRelativeEntriesForSlot bits target)
  have hentries :
      sparseExceptionRelativeEntries bits target =
        pre ++ slotEntries ++ post := by
    simpa [pre, slotEntries, post] using
      sparseExceptionRelativeEntries_decompose
        bits target hslot
  have hpre :
      pre.length =
        RMQ.Succinct.rankPrefix true
          (sparseExceptionFlagBits bits target)
          globalLocalSlot *
            localStride bits.length := by
    simpa [pre] using
      sparseExceptionRelativePrefix_length bits target (Nat.le_of_lt hslot)
  have hslotEntries :
      slotEntries =
        relativeOffsetsOrZero target bits
          (localBaseOccurrence bits.length globalLocalSlot)
          (localStride bits.length)
          (superEndOccurrence bits target
            (localSuperSlot bits.length globalLocalSlot))
          (position bits target
            (localBaseOccurrence bits.length globalLocalSlot)) := by
    simp [slotEntries,
      sparseExceptionRelativeEntriesForSlot, hflag]
  have hslotLen :
      localOccurrence < slotEntries.length := by
    rw [sparseExceptionRelativeEntriesForSlot_length]
    simp [hflag]
    exact hocc
  have hidx :
      RMQ.Succinct.rankPrefix true
          (sparseExceptionFlagBits bits target)
          globalLocalSlot *
            localStride bits.length +
          localOccurrence =
        pre.length + localOccurrence := by
    simp [hpre]
  rw [hentries, hidx]
  rw [List.append_assoc]
  rw [List.getElem?_append_right (by omega)]
  have hsub :
      pre.length + localOccurrence - pre.length =
        localOccurrence := by
    omega
  rw [hsub]
  rw [List.getElem?_append_left hslotLen]
  rw [hslotEntries]
  exact
    relativeOffsetsOrZero_lookup_exact
      (target := target)
      (bits := bits)
      (baseOccurrence :=
        localBaseOccurrence bits.length globalLocalSlot)
      (count := localStride bits.length)
      (endOccurrence :=
        superEndOccurrence bits target
          (localSuperSlot bits.length globalLocalSlot))
      (basePosition :=
        position bits target
          (localBaseOccurrence bits.length globalLocalSlot))
      (localOccurrence := localOccurrence)
      (pos := pos)
      hocc hend hselect

theorem sparseExceptionRelativeEntriesForSlot_mem_lt_width
    (bits : List Bool) (target : Bool) {globalLocalSlot entry : Nat}
    (hmem :
      List.Mem entry
        (sparseExceptionRelativeEntriesForSlot bits target globalLocalSlot)) :
    entry < 2 ^ sparseExceptionRelativeWidth bits := by
  by_cases hflag : localIsSparseException bits target globalLocalSlot = true
  · let superSlot := localSuperSlot bits.length globalLocalSlot
    let localBase := localBaseOccurrence bits.length globalLocalSlot
    let localBasePosition := position bits target localBase
    have hshort :=
      (localIsSparseException_true_short bits target globalLocalSlot hflag).1
    have hmemOffsets :
        List.Mem entry
          (relativeOffsetsOrZero target bits localBase (localStride bits.length)
            (superEndOccurrence bits target superSlot) localBasePosition) := by
      simpa [sparseExceptionRelativeEntriesForSlot, hflag, superSlot, localBase,
        localBasePosition] using hmem
    rcases relativeOffsetsOrZero_mem_cases hmemOffsets with hzero | hsome
    · subst entry
      exact Nat.pow_pos (by omega : 0 < 2)
    · rcases hsome with ⟨offset, pos, _hoff, hqEnd, hselect, hentry⟩
      have hsuperBase :
          superBaseOccurrence bits.length superSlot <= localBase := by
        simp [superSlot, localBase, superBaseOccurrence, localSuperSlot,
          localBaseOccurrence]
      have hoffSuper : pos - localBasePosition < superLongSpan bits.length := by
        simpa [localBase, localBasePosition, superSlot] using
          selected_offset_lt_superLongSpan bits target superSlot hshort
            hsuperBase (by omega) hqEnd hselect
      have hposLen : pos < bits.length := RMQ.Succinct.select_bounds hselect
      have hentryLen : entry < bits.length := by rw [hentry]; omega
      have hentrySuper : entry < superLongSpan bits.length := by
        rw [hentry]; exact hoffSuper
      have hentryMin :
          entry < Nat.min bits.length (superLongSpan bits.length) :=
        Nat.lt_min.mpr ⟨hentryLen, hentrySuper⟩
      exact Nat.lt_trans hentryMin
        (by
          simpa [sparseExceptionRelativeWidth,
            SuccinctRankProposal.machineWordBits] using
            (Nat.lt_log2_self
              (n := Nat.min bits.length (superLongSpan bits.length))))
  · have hfalse : localIsSparseException bits target globalLocalSlot = false := by
      cases h : localIsSparseException bits target globalLocalSlot
      · rfl
      · contradiction
    simp [sparseExceptionRelativeEntriesForSlot, hfalse] at hmem
    cases hmem

theorem sparseExceptionRelativeEntries_mem_lt_width
    (bits : List Bool) (target : Bool) {entry : Nat}
    (hmem : List.Mem entry (sparseExceptionRelativeEntries bits target)) :
    entry < 2 ^ sparseExceptionRelativeWidth bits := by
  unfold sparseExceptionRelativeEntries at hmem
  rcases List.mem_flatMap.mp hmem with ⟨globalLocalSlot, _hslot, hentry⟩
  exact sparseExceptionRelativeEntriesForSlot_mem_lt_width bits target hentry

def sparseExceptionRelativeTable (bits : List Bool) (target : Bool) :
    SuccinctSpace.FixedWidthNatTable
      (sparseExceptionRelativeEntries bits target)
      (sparseExceptionRelativeWidth bits) :=
  SuccinctSpace.FixedWidthNatTable.ofEntries
    (sparseExceptionRelativeEntries bits target)
    (sparseExceptionRelativeWidth bits)
    (by
      intro entry hmem
      exact sparseExceptionRelativeEntries_mem_lt_width bits target hmem)

theorem sparseExceptionRelativeTable_payload_length
    (bits : List Bool) (target : Bool) :
    (sparseExceptionRelativeTable bits target).payload.length =
      (sparseExceptionRelativeEntries bits target).length *
        sparseExceptionRelativeWidth bits :=
  (sparseExceptionRelativeTable bits target).payload_length_eq

theorem sparseExceptionRelativeTable_payload_expanded_length
    (bits : List Bool) (target : Bool) :
    (sparseExceptionRelativeTable bits target).payload.length =
      RMQ.Succinct.rankPrefix true (sparseExceptionFlagBits bits target)
        (localSlotCount bits target) *
        localStride bits.length *
        sparseExceptionRelativeWidth bits := by
  rw [sparseExceptionRelativeTable_payload_length,
    sparseExceptionRelativeEntries_length]

theorem sparseExceptionRelativeTable_payload_mul_ell_le_const_spanSum
    (bits : List Bool) (target : Bool) :
    (sparseExceptionRelativeTable bits target).payload.length *
        ell bits.length <=
      512 * shortSuperLocalSpanSum bits target
        (localSlotCount bits target) := by
  let count :=
    RMQ.Succinct.rankPrefix true (sparseExceptionFlagBits bits target)
      (localSlotCount bits target)
  let stride := localStride bits.length
  let width := sparseExceptionRelativeWidth bits
  let e := ell bits.length
  let w := wordBits bits.length
  let spanSum := shortSuperLocalSpanSum bits target (localSlotCount bits target)
  have hpayload :
      (sparseExceptionRelativeTable bits target).payload.length =
        count * stride * width := by
    simpa [count, stride, width] using
      sparseExceptionRelativeTable_payload_expanded_length bits target
  have hcodec : stride * width * e <= 512 * w := by
    simpa [stride, width, e, w] using
      sparseException_localStride_mul_width_mul_ell_le_const_wordBits bits
  have hpayloadEll :
      count * stride * width * e <= count * (512 * w) := by
    have hmul := Nat.mul_le_mul_left count hcodec
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul
  have hcountWord : count * w <= spanSum := by
    simpa [count, w, spanSum] using
      sparseExceptionCount_wordBits_le_spanSum bits target (Nat.le_refl _)
  have hcountScaled : count * (512 * w) <= 512 * spanSum := by
    have hmul := Nat.mul_le_mul_left 512 hcountWord
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul
  rw [hpayload]
  exact Nat.le_trans hpayloadEll hcountScaled

/-- `o(n)` budget for the sparse-exception relative table, fed the bit length
directly. -/
def sparseExceptionRelativeTableOverhead (n : Nat) : Nat :=
  SuccinctSpace.idDivLogLogOverhead 512 n + 512

theorem sparseExceptionRelativeTableOverhead_littleO :
    SuccinctSpace.LittleOLinear sparseExceptionRelativeTableOverhead := by
  unfold sparseExceptionRelativeTableOverhead
  exact (SuccinctSpace.idDivLogLogOverhead_littleO 512).add_const 512

theorem sparseExceptionRelativeTable_payload_le_overhead_of_spanSum_le_length
    (bits : List Bool) (target : Bool)
    (hspan :
      shortSuperLocalSpanSum bits target (localSlotCount bits target) <=
        bits.length) :
    (sparseExceptionRelativeTable bits target).payload.length <=
      sparseExceptionRelativeTableOverhead bits.length := by
  let payload := (sparseExceptionRelativeTable bits target).payload.length
  let e := ell bits.length
  let n := bits.length
  have he_pos : 0 < e := by
    simpa [e] using ell_pos bits.length
  have hpayloadEll : payload * e <= 512 * n := by
    have hscaled :=
      sparseExceptionRelativeTable_payload_mul_ell_le_const_spanSum bits target
    have hspanScaled :
        512 * shortSuperLocalSpanSum bits target
              (localSlotCount bits target) <=
          512 * n := by
      exact Nat.mul_le_mul_left 512 (by simpa [n] using hspan)
    exact Nat.le_trans (by simpa [payload, e] using hscaled) hspanScaled
  let overheadLen := 512 * (n / e) + 512
  have hn_lt : n < n / e * e + e :=
    Nat.lt_div_mul_add he_pos (a := n)
  have hscaledStrict : 512 * n < overheadLen * e := by
    have hmul := Nat.mul_lt_mul_of_pos_left hn_lt (by decide : 0 < 512)
    simpa [overheadLen, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm,
      Nat.left_distrib, Nat.right_distrib] using hmul
  have hpayloadStrict : payload * e < overheadLen * e :=
    Nat.lt_of_le_of_lt hpayloadEll hscaledStrict
  have hpayloadStrictLeft : e * payload < e * overheadLen := by
    simpa [Nat.mul_comm] using hpayloadStrict
  have hpayloadLe : payload <= overheadLen :=
    Nat.le_of_mul_le_mul_left (Nat.le_of_lt hpayloadStrictLeft) he_pos
  simpa [payload, overheadLen, sparseExceptionRelativeTableOverhead,
    SuccinctSpace.idDivLogLogOverhead, e, n, ell, wordBits,
    SuccinctRankProposal.machineWordBits] using hpayloadLe

theorem sparseExceptionRelativeTable_payload_le_overhead
    (bits : List Bool) (target : Bool) :
    (sparseExceptionRelativeTable bits target).payload.length <=
      sparseExceptionRelativeTableOverhead bits.length := by
  exact
    sparseExceptionRelativeTable_payload_le_overhead_of_spanSum_le_length
      bits target (shortSuperLocalSpanSum_le_length bits target)

def canonicalSparseExceptionDirectoryOverhead (n : Nat) : Nat :=
  SuccinctSpace.logLogCubedSampledDirectoryOverhead 40 n +
    (SuccinctSpace.logLogCubedSampledDirectoryOverhead 192 n + 16) +
      sparseExceptionRelativeTableOverhead n

theorem canonicalSparseExceptionDirectoryOverhead_littleO :
    SuccinctSpace.LittleOLinear
      canonicalSparseExceptionDirectoryOverhead := by
  unfold canonicalSparseExceptionDirectoryOverhead
  have hflags :
      SuccinctSpace.LittleOLinear
        (SuccinctSpace.logLogCubedSampledDirectoryOverhead 40) :=
    SuccinctSpace.logLogCubedSampledDirectoryOverhead_littleO 40
  have hrank :
      SuccinctSpace.LittleOLinear
        (fun n =>
          SuccinctSpace.logLogCubedSampledDirectoryOverhead 192 n + 16) :=
    (SuccinctSpace.logLogCubedSampledDirectoryOverhead_littleO 192).add_const 16
  exact (hflags.add hrank).add sparseExceptionRelativeTableOverhead_littleO

theorem fixedWidthNatTable_word_length_le_of_mem
    {entries : List Nat} {width n : Nat}
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (hwidth : width <= SuccinctRankProposal.machineWordBits n)
    {word : List Bool}
    (hmem : List.Mem word table.store.words.toList) :
    word.length <= SuccinctRankProposal.machineWordBits n := by
  rcases (List.mem_iff_getElem?.mp hmem) with ⟨i, hgetList⟩
  have hget : table.store.words[i]? = some word := by
    simpa [Array.getElem?_toList] using hgetList
  rw [table.read_word_length_of_some hget]
  exact hwidth

theorem sparseExceptionRelativeWidth_le_machine (bits : List Bool) :
    sparseExceptionRelativeWidth bits <=
      SuccinctRankProposal.machineWordBits bits.length := by
  unfold sparseExceptionRelativeWidth
  exact SuccinctRankProposal.machineWordBits_mono_le
    (Nat.min_le_left bits.length (superLongSpan bits.length))

structure SparseExceptionDirectory
    (bits : List Bool) (target : Bool)
    (rankSuperOverhead rankBlockOverhead : Nat) where
  localStride : Nat
  localStride_pos : 0 < localStride
  flagBits : List Bool
  rankData :
    SuccinctRankProposal.TwoLevelPayloadLiveStoredWordRankData
      flagBits rankSuperOverhead rankBlockOverhead 4
  relativeEntries : List Nat
  relativeWidth : Nat
  relativeTable :
    SuccinctSpace.FixedWidthNatTable relativeEntries relativeWidth
  rank_wordSize_le_machine :
    rankData.wordSize <=
      SuccinctRankProposal.machineWordBits bits.length
  rank_superWidth_le_machine :
    rankData.superWidth <=
      SuccinctRankProposal.machineWordBits bits.length
  rank_blockWidth_le_machine :
    rankData.blockWidth <=
      SuccinctRankProposal.machineWordBits bits.length
  relativeWidth_le_machine :
    relativeWidth <=
      SuccinctRankProposal.machineWordBits bits.length
  payload_length_le_overhead :
    flagBits.length + rankData.auxPayload.length +
        relativeTable.payload.length <=
      canonicalSparseExceptionDirectoryOverhead bits.length

namespace SparseExceptionDirectory

def payload
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      SparseExceptionDirectory
        bits target rankSuperOverhead rankBlockOverhead) :
    List Bool :=
  directory.flagBits ++ directory.rankData.auxPayload ++
    directory.relativeTable.payload

theorem payload_length_le_canonical
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      SparseExceptionDirectory
        bits target rankSuperOverhead rankBlockOverhead) :
    directory.payload.length <=
      canonicalSparseExceptionDirectoryOverhead bits.length := by
  simpa [payload, Nat.add_assoc] using
    directory.payload_length_le_overhead

def readWords
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      SparseExceptionDirectory
        bits target rankSuperOverhead rankBlockOverhead) :
    List (List Bool) :=
  directory.rankData.superTables.trueTable.store.words.toList ++
    directory.rankData.superTables.falseTable.store.words.toList ++
      directory.rankData.blockTables.trueTable.store.words.toList ++
        directory.rankData.blockTables.falseTable.store.words.toList ++
          directory.rankData.bitWords.store.words.toList ++
            directory.relativeTable.store.words.toList

def readCosted
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      SparseExceptionDirectory
        bits target rankSuperOverhead rankBlockOverhead)
    (base localSlot localOccurrence : Nat) :
    Costed (Option Nat) :=
  Costed.bind (directory.rankData.rankCosted true localSlot)
    fun exceptionRank =>
      relativeOffsetReadCosted directory.relativeTable base
        (relativeSplitFalseSelectSparseCompactSlot
          exceptionRank localOccurrence directory.localStride)

theorem readCosted_cost_le_five
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      SparseExceptionDirectory
        bits target rankSuperOverhead rankBlockOverhead)
    (base localSlot localOccurrence : Nat) :
    (directory.readCosted base localSlot localOccurrence).cost <= 5 := by
  unfold readCosted relativeOffsetReadCosted
  have hrank :=
    directory.rankData.rankCosted_cost_le_four true localSlot
  have hrelative :=
    directory.relativeTable.readCosted_cost_le_one
      (relativeSplitFalseSelectSparseCompactSlot
        (directory.rankData.rankCosted true localSlot).value
        localOccurrence directory.localStride)
  simp [Costed.bind, Costed.map] at *
  omega

theorem readCosted_exact
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      SparseExceptionDirectory
        bits target rankSuperOverhead rankBlockOverhead)
    (base localSlot localOccurrence : Nat) :
    (directory.readCosted base localSlot localOccurrence).erase =
      (directory.relativeEntries[
          relativeSplitFalseSelectSparseCompactSlot
            (RMQ.Succinct.rankPrefix true directory.flagBits localSlot)
            localOccurrence directory.localStride]?).map
        (fun offset => base + offset) := by
  have hrank :=
    directory.rankData.rankCosted_exact true localSlot
  change (directory.rankData.rankCosted true localSlot).value =
      RMQ.Succinct.rankPrefix true directory.flagBits localSlot at hrank
  let slot :=
    relativeSplitFalseSelectSparseCompactSlot
      (RMQ.Succinct.rankPrefix true directory.flagBits localSlot)
      localOccurrence directory.localStride
  have hread :
      (directory.relativeTable.readCosted slot).value =
        directory.relativeEntries[slot]? := by
    simpa [Costed.erase] using
      directory.relativeTable.readCosted_erase slot
  unfold readCosted relativeOffsetReadCosted
  simp [Costed.bind, Costed.map, Costed.erase, hrank, slot, hread]

theorem read_words_length_le_machine
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      SparseExceptionDirectory
        bits target rankSuperOverhead rankBlockOverhead)
    {word : List Bool}
    (hmem : List.Mem word directory.readWords) :
    word.length <=
      SuccinctRankProposal.machineWordBits bits.length := by
  rw [readWords] at hmem
  rcases List.mem_append.mp hmem with hprefix0 | hrelative
  · rcases List.mem_append.mp hprefix0 with hprefix1 | hflagWord
    · rcases List.mem_append.mp hprefix1 with hprefix2 | hblockFalse
      · rcases List.mem_append.mp hprefix2 with hprefix3 | hblockTrue
        · rcases List.mem_append.mp hprefix3 with hsuperTrue | hsuperFalse
          · exact
              fixedWidthNatTable_word_length_le_of_mem
                directory.rankData.superTables.trueTable
                directory.rank_superWidth_le_machine hsuperTrue
          · exact
              fixedWidthNatTable_word_length_le_of_mem
                directory.rankData.superTables.falseTable
                directory.rank_superWidth_le_machine hsuperFalse
        · exact
            fixedWidthNatTable_word_length_le_of_mem
              directory.rankData.blockTables.trueTable
              directory.rank_blockWidth_le_machine hblockTrue
      · exact
          fixedWidthNatTable_word_length_le_of_mem
            directory.rankData.blockTables.falseTable
            directory.rank_blockWidth_le_machine hblockFalse
    · exact Nat.le_trans
        (directory.rankData.bitWords.word_length_le hflagWord)
        directory.rank_wordSize_le_machine
  · exact
      fixedWidthNatTable_word_length_le_of_mem
        directory.relativeTable
        directory.relativeWidth_le_machine hrelative

theorem profile
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      SparseExceptionDirectory
        bits target rankSuperOverhead rankBlockOverhead) :
    directory.payload.length <=
        canonicalSparseExceptionDirectoryOverhead bits.length /\
      (forall base localSlot localOccurrence,
        (directory.readCosted
          base localSlot localOccurrence).cost <= 5) /\
      (forall base localSlot localOccurrence,
        (directory.readCosted base localSlot localOccurrence).erase =
          (directory.relativeEntries[
              relativeSplitFalseSelectSparseCompactSlot
                (RMQ.Succinct.rankPrefix true directory.flagBits localSlot)
                localOccurrence directory.localStride]?).map
            (fun offset => base + offset)) /\
      forall {word : List Bool},
        List.Mem word directory.readWords ->
          word.length <=
            SuccinctRankProposal.machineWordBits bits.length := by
  exact
    ⟨directory.payload_length_le_canonical,
      directory.readCosted_cost_le_five,
      directory.readCosted_exact,
      fun {word} hmem => directory.read_words_length_le_machine hmem⟩

end SparseExceptionDirectory

def sparseExceptionDirectory
    (bits : List Bool) (target : Bool) :
    SparseExceptionDirectory
      bits target
      (sparseExceptionEffectiveFlagRankSuperOverhead bits target)
      (sparseExceptionEffectiveFlagRankBlockOverhead bits target) where
  localStride := localStride bits.length
  localStride_pos := localStride_pos bits.length
  flagBits := sparseExceptionEffectiveFlagBits bits target
  rankData := sparseExceptionEffectiveFlagRankData bits target
  relativeEntries := sparseExceptionRelativeEntries bits target
  relativeWidth := sparseExceptionRelativeWidth bits
  relativeTable := sparseExceptionRelativeTable bits target
  rank_wordSize_le_machine := by
    exact (sparseExceptionEffectiveFlagRankData_profile bits target).2.1
  rank_superWidth_le_machine := by
    exact (sparseExceptionEffectiveFlagRankData_profile bits target).2.2.1
  rank_blockWidth_le_machine := by
    exact (sparseExceptionEffectiveFlagRankData_profile bits target).2.2.2.1
  relativeWidth_le_machine :=
    sparseExceptionRelativeWidth_le_machine bits
  payload_length_le_overhead := by
    have hflags :=
      sparseExceptionEffectiveFlagBits_length_le_overhead bits target
    have hrank :=
      sparseExceptionEffectiveFlagRankData_auxPayload_le_overhead bits target
    have hrelative :=
      sparseExceptionRelativeTable_payload_le_overhead bits target
    simp [canonicalSparseExceptionDirectoryOverhead] at hflags hrank hrelative ⊢
    omega

theorem sparseExceptionDirectory_readCosted_lookup_exact
    (bits : List Bool) (target : Bool)
    {globalLocalSlot localOccurrence pos : Nat}
    (hslot :
      globalLocalSlot < localSlotCount bits target)
    (heff :
      globalLocalSlot <
        sparseExceptionEffectiveLocalSlotCount bits target)
    (hflag :
      localIsSparseException bits target globalLocalSlot = true)
    (hocc :
      localOccurrence < localStride bits.length)
    (hend :
      localBaseOccurrence bits.length globalLocalSlot + localOccurrence <
        superEndOccurrence bits target
          (localSuperSlot bits.length globalLocalSlot))
    (hselect :
      RMQ.Succinct.select target bits
          (localBaseOccurrence bits.length globalLocalSlot + localOccurrence) =
        some pos) :
    ((sparseExceptionDirectory bits target).readCosted
      (position bits target
        (localBaseOccurrence bits.length globalLocalSlot))
      globalLocalSlot localOccurrence).erase =
      some
        (position bits target
            (localBaseOccurrence bits.length globalLocalSlot) +
          (pos -
            position bits target
              (localBaseOccurrence bits.length globalLocalSlot))) := by
  have hread :=
    (sparseExceptionDirectory bits target).readCosted_exact
      (position bits target
        (localBaseOccurrence bits.length globalLocalSlot))
      globalLocalSlot localOccurrence
  rw [hread]
  change
    Option.map
      (fun offset =>
        position bits target
            (localBaseOccurrence bits.length globalLocalSlot) +
          offset)
      ((sparseExceptionRelativeEntries bits target)[
          relativeSplitFalseSelectSparseCompactSlot
            (RMQ.Succinct.rankPrefix true
              (sparseExceptionEffectiveFlagBits bits target)
              globalLocalSlot)
            localOccurrence
            (localStride bits.length)]?) =
      some
        (position bits target
            (localBaseOccurrence bits.length globalLocalSlot) +
          (pos -
            position bits target
              (localBaseOccurrence bits.length globalLocalSlot)))
  have hprefix :=
    sparseExceptionEffectiveFlagBits_prefix_eq
      bits target (globalLocalSlot := globalLocalSlot) (Nat.le_of_lt heff)
  rw [hprefix]
  have hlookup :=
    sparseExceptionRelativeEntries_lookup_exact
      bits target hslot hflag hocc hend hselect
  rw [relativeSplitFalseSelectSparseCompactSlot]
  rw [hlookup]
  rfl

/-! ### Long-super relative table is `o(n)` -/

/-- `o(n)` budget for the long-super relative table: `n / loglog n + 1`. Fed the
bit length `n` directly (the BP original fed `2 * size` only because its argument
was `shape.size`). -/
def longSuperRelativeTableOverhead (n : Nat) : Nat :=
  SuccinctSpace.idDivLogLogOverhead 1 n + 1

theorem longSuperRelativeTableOverhead_littleO :
    SuccinctSpace.LittleOLinear longSuperRelativeTableOverhead := by
  unfold longSuperRelativeTableOverhead
  exact (SuccinctSpace.idDivLogLogOverhead_littleO 1).add_const 1

theorem longSuperRelativeTable_payload_le_overhead
    (bits : List Bool) (target : Bool) :
    (longSuperRelativeTable bits target).payload.length <=
      longSuperRelativeTableOverhead bits.length := by
  let payload := (longSuperRelativeTable bits target).payload.length
  let ellV := ell bits.length
  let n := bits.length
  have hell_pos : 0 < ellV := ell_pos bits.length
  have hpayloadEll : payload * ellV <= n := by
    have hscaled := longSuperRelativeTable_payload_mul_ell_le_spanSum bits target
    exact Nat.le_trans (by simpa [payload, ellV] using hscaled)
      (by simpa [n] using longSuperSpanSum_le_length bits target)
  let overheadLen := n / ellV + 1
  have hn_lt : n < n / ellV * ellV + ellV := Nat.lt_div_mul_add hell_pos (a := n)
  have hscaledStrict : n < overheadLen * ellV := by
    simpa [overheadLen, Nat.add_mul, Nat.one_mul, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using hn_lt
  have hpayloadStrict : payload * ellV < overheadLen * ellV :=
    Nat.lt_of_le_of_lt hpayloadEll hscaledStrict
  have hpayloadStrictLeft : ellV * payload < ellV * overheadLen := by
    simpa [Nat.mul_comm] using hpayloadStrict
  have hpayloadLe : payload <= overheadLen :=
    Nat.le_of_mul_le_mul_left (Nat.le_of_lt hpayloadStrictLeft) hell_pos
  simpa [payload, overheadLen, longSuperRelativeTableOverhead,
    SuccinctSpace.idDivLogLogOverhead, ellV, n, ell, wordBits,
    SuccinctRankProposal.machineWordBits] using hpayloadLe

theorem superTable_payload_le_overhead
    (bits : List Bool) (target : Bool) :
    (superTable bits target).payload.length <=
      SuccinctSpace.logLogCubedSampledDirectoryOverhead
        40 bits.length := by
  let payload := (superTable bits target).payload.length
  let superCount := superSlotCount bits target
  let w := wordBits bits.length
  let stride := superStride bits.length
  let e := ell bits.length
  let e3 := e * (e * e)
  let n := bits.length
  have he3One : 1 <= e3 := by
    have he : 1 <= e := by simpa [e] using ell_pos bits.length
    have hmul := Nat.mul_le_mul he (Nat.mul_le_mul he he)
    simpa [e3] using hmul
  have hpayload :
      payload = 4 * (superCount * w) := by
    have hlen := (superTable bits target).payload_length
    simp [payload, superCount, w, superTable, superFieldWidth,
      sparseDenseFalseSelectDenseLocalEntryMultiwordPayloadBudget,
      superEntries_length] at hlen ⊢
    omega
  by_cases hnZero : n = 0
  · have hcountZero : occurrenceCount bits target = 0 := by
      have hcountLe : occurrenceCount bits target <= n := by
        simpa [n] using occurrenceCount_le_length bits target
      omega
    have hsuperZero : superCount = 0 := by
      unfold superCount superSlotCount falseSelectCeilDiv
      rw [hcountZero]
      have hstride_pos : 0 < stride := by
        simpa [stride] using superStride_pos bits.length
      have hpred_lt : stride - 1 < stride :=
        Nat.pred_lt (Nat.ne_of_gt hstride_pos)
      simpa [stride] using Nat.div_eq_of_lt hpred_lt
    simp [payload, hpayload, hsuperZero,
      SuccinctSpace.logLogCubedSampledDirectoryOverhead]
  · have hnPos : 0 < n := Nat.pos_of_ne_zero hnZero
    have hcountLe : occurrenceCount bits target <= n := by
      simpa [n] using occurrenceCount_le_length bits target
    have hstrideLe : stride <= 4 * n := by
      have hsq :=
        machineWordBits_sq_le_four_mul_self_of_pos
          (n := bits.length) hnPos
      simpa [stride, w, n, superStride, wordBits] using hsq
    have hsuperCountMul :
        superCount * stride <= occurrenceCount bits target + stride := by
      simpa [superCount, stride, superSlotCount] using
        falseSelectCeilDiv_mul_le_add
          (occurrenceCount bits target) stride
    have hpayloadMul :
        payload * w <= 20 * (e3 * n) := by
      rw [hpayload]
      calc
        4 * (superCount * w) * w =
            4 * (superCount * stride) := by
              simp [stride, w, superStride, Nat.mul_left_comm, Nat.mul_comm]
        _ <= 4 * (occurrenceCount bits target + stride) := by
              exact Nat.mul_le_mul_left 4 hsuperCountMul
        _ <= 4 * (n + 4 * n) := by
              exact Nat.mul_le_mul_left 4
                (Nat.add_le_add hcountLe hstrideLe)
        _ = 20 * n := by omega
        _ <= 20 * (e3 * n) := by
              have hmul := Nat.mul_le_mul_right n he3One
              have hscaled := Nat.mul_le_mul_left 20 hmul
              simpa [Nat.mul_assoc, Nat.mul_left_comm,
                Nat.mul_comm] using hscaled
    exact
      payload_le_logLogCubedSampledDirectoryOverhead_of_mul_wordBits_le
        (n := bits.length) (payload := payload) (scale := 20)
        (by
          simpa [w, e, e3, n, Nat.mul_assoc,
            Nat.mul_left_comm, Nat.mul_comm] using hpayloadMul)

theorem localTable_payload_le_overhead
    (bits : List Bool) (target : Bool) :
    (localTable bits target).payload.length <=
      SuccinctSpace.logLogCubedSampledDirectoryOverhead
        640 bits.length := by
  let payload := (localTable bits target).payload.length
  let m := localSlotCount bits target
  let relWidth := localFieldWidth bits
  let w := wordBits bits.length
  let stride := localStride bits.length
  let e := ell bits.length
  let e2 := e * e
  let e3 := e * (e * e)
  let n := bits.length
  have hpayload :
      payload = 4 * (m * relWidth) := by
    have hlen := (localTable bits target).payload_length
    simp [payload, m, relWidth, localTable, localFieldWidth,
      sparseDenseFalseSelectDenseLocalEntryMultiwordPayloadBudget,
      localEntries_length] at hlen ⊢
    omega
  have hslots :
      m * stride <= 10 * n := by
    simpa [m, stride, n] using
      localSlotCount_mul_localStride_le_const_length bits target
  have hwidth : relWidth <= 4 * e := by
    simpa [relWidth, e, localFieldWidth] using
      sparseExceptionRelativeWidth_le_four_ell bits
  have hwordLower :
      w <= 2 * stride * e2 := by
    simpa [w, stride, e, e2, Nat.mul_assoc, Nat.mul_left_comm,
      Nat.mul_comm] using
      wordBits_le_two_mul_localStride_mul_ell_sq bits.length
  have hcore :
      m * relWidth * w <= 80 * (e3 * n) := by
    calc
      m * relWidth * w <=
          m * relWidth * (2 * stride * e2) := by
            exact Nat.mul_le_mul_left (m * relWidth) hwordLower
      _ = 2 * (m * stride) * relWidth * e2 := by
            simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      _ = 2 * ((m * stride) * relWidth) * e2 := by
            simp [Nat.mul_assoc]
      _ <= 2 * ((10 * n) * (4 * e)) * e2 := by
            have hmul := Nat.mul_le_mul hslots hwidth
            have hmul2 := Nat.mul_le_mul_left 2 hmul
            have hmul3 := Nat.mul_le_mul_right e2 hmul2
            exact hmul3
      _ = 2 * (10 * n) * (4 * e) * e2 := by
            simp [Nat.mul_assoc]
      _ = 80 * (e3 * n) := by
            calc
              2 * (10 * n) * (4 * e) * e2 =
                  n * (4 * (20 * (e * e2))) := by
                    simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
              _ = n * (80 * (e * e2)) := by
                    have hconst :
                        4 * (20 * (e * e2)) = 80 * (e * e2) := by
                      omega
                    rw [hconst]
              _ = 80 * (e3 * n) := by
                    simp [e2, e3, Nat.mul_left_comm, Nat.mul_comm]
  have hpayloadMul :
      payload * w <= 320 * (e3 * n) := by
    rw [hpayload]
    have hmul := Nat.mul_le_mul_left 4 hcore
    calc
      4 * (m * relWidth) * w <=
          4 * (80 * (e3 * n)) := by
            simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul
      _ = 320 * (e3 * n) := by
            let t := e3 * n
            change 4 * (80 * t) = 320 * t
            omega
  exact
    payload_le_logLogCubedSampledDirectoryOverhead_of_mul_wordBits_le
      (n := bits.length) (payload := payload) (scale := 320)
      (by
        simpa [payload, w, e, e3, n, Nat.mul_assoc,
          Nat.mul_left_comm, Nat.mul_comm] using hpayloadMul)

theorem longSuperFlagBits_length (bits : List Bool) (target : Bool) :
    (longSuperFlagBits bits target).length =
      superSlotCount bits target := by
  simp [longSuperFlagBits]

theorem longSuperFlagBits_length_le_length
    (bits : List Bool) (target : Bool) :
    (longSuperFlagBits bits target).length <= bits.length := by
  by_cases hcount : occurrenceCount bits target = 0
  · have hsuperZero : superSlotCount bits target = 0 := by
      unfold superSlotCount falseSelectCeilDiv
      rw [hcount]
      have hstride_pos : 0 < superStride bits.length :=
        superStride_pos bits.length
      have hpred_lt :
          superStride bits.length - 1 < superStride bits.length :=
        Nat.pred_lt (Nat.ne_of_gt hstride_pos)
      simpa using Nat.div_eq_of_lt hpred_lt
    simp [longSuperFlagBits_length, hsuperZero]
  · have hcountPos : 0 < occurrenceCount bits target := Nat.pos_of_ne_zero hcount
    have hsuperLeCount :
        superSlotCount bits target <= occurrenceCount bits target := by
      exact
        falseSelectCeilDiv_le_self_of_pos
          (n := occurrenceCount bits target)
          (stride := superStride bits.length)
          hcountPos (superStride_pos bits.length)
    have hcountLe := occurrenceCount_le_length bits target
    rw [longSuperFlagBits_length]
    exact Nat.le_trans hsuperLeCount hcountLe

theorem longSuperFlagBits_length_mul_wordBits_le
    (bits : List Bool) (target : Bool) :
    (longSuperFlagBits bits target).length * wordBits bits.length <=
      5 * ((ell bits.length * (ell bits.length * ell bits.length)) *
        bits.length) := by
  let flagLen := (longSuperFlagBits bits target).length
  let superCount := superSlotCount bits target
  let w := wordBits bits.length
  let stride := superStride bits.length
  let e := ell bits.length
  let e3 := e * (e * e)
  let n := bits.length
  have he3One : 1 <= e3 := by
    have he : 1 <= e := by simpa [e] using ell_pos bits.length
    have hmul := Nat.mul_le_mul he (Nat.mul_le_mul he he)
    simpa [e3] using hmul
  by_cases hnZero : n = 0
  · have hcountZero : occurrenceCount bits target = 0 := by
      have hcountLe : occurrenceCount bits target <= n := by
        simpa [n] using occurrenceCount_le_length bits target
      omega
    have hsuperZero : superCount = 0 := by
      unfold superCount superSlotCount falseSelectCeilDiv
      rw [hcountZero]
      have hstride_pos : 0 < stride := by
        simpa [stride] using superStride_pos bits.length
      have hpred_lt : stride - 1 < stride :=
        Nat.pred_lt (Nat.ne_of_gt hstride_pos)
      simpa [stride] using Nat.div_eq_of_lt hpred_lt
    have hsuperZeroRaw : superSlotCount bits target = 0 := by
      simpa [superCount] using hsuperZero
    have hflagZero : flagLen = 0 := by
      rw [show flagLen = (longSuperFlagBits bits target).length by rfl,
        longSuperFlagBits_length, hsuperZeroRaw]
    rw [show (longSuperFlagBits bits target).length = flagLen by rfl,
      hflagZero]
    simp [n, hnZero]
  · have hnPos : 0 < n := Nat.pos_of_ne_zero hnZero
    have hcountLe : occurrenceCount bits target <= n := by
      simpa [n] using occurrenceCount_le_length bits target
    have hstrideLe : stride <= 4 * n := by
      have hsq :=
        machineWordBits_sq_le_four_mul_self_of_pos
          (n := bits.length) hnPos
      simpa [stride, w, n, superStride, wordBits] using hsq
    have hsuperCountMul :
        superCount * stride <= occurrenceCount bits target + stride := by
      simpa [superCount, stride, superSlotCount] using
        falseSelectCeilDiv_mul_le_add
          (occurrenceCount bits target) stride
    have hflagMul :
        flagLen * w <= 5 * n := by
      have hflagLen : flagLen = superCount := by
        simpa [flagLen] using
          longSuperFlagBits_length bits target
      have hwordLeStride : w <= stride := by
        have hwPos : 0 < w := by
          simpa [w] using wordBits_pos bits.length
        simp [stride, w, superStride]
        exact Nat.le_mul_of_pos_left w hwPos
      calc
        flagLen * w = superCount * w := by rw [hflagLen]
        _ <= superCount * stride := by
              exact Nat.mul_le_mul_left superCount hwordLeStride
        _ <= occurrenceCount bits target + stride :=
              hsuperCountMul
        _ <= n + 4 * n := Nat.add_le_add hcountLe hstrideLe
        _ = 5 * n := by omega
    have hscaled :
        5 * n <= 5 * (e3 * n) := by
      have hmul := Nat.mul_le_mul_right n he3One
      have hscaled := Nat.mul_le_mul_left 5 hmul
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hscaled
    exact Nat.le_trans hflagMul (by
      simpa [flagLen, w, e, e3, n, Nat.mul_assoc,
        Nat.mul_left_comm, Nat.mul_comm] using hscaled)

theorem longSuperFlagBits_length_le_overhead
    (bits : List Bool) (target : Bool) :
    (longSuperFlagBits bits target).length <=
      SuccinctSpace.logLogCubedSampledDirectoryOverhead
        40 bits.length := by
  exact
    payload_le_logLogCubedSampledDirectoryOverhead_of_mul_wordBits_le
      (n := bits.length)
      (payload := (longSuperFlagBits bits target).length)
      (scale := 20)
      (by
        have h :=
          longSuperFlagBits_length_mul_wordBits_le bits target
        have hscale :
            5 * ((ell bits.length * (ell bits.length * ell bits.length)) *
                bits.length) <=
              20 * bits.length *
                (ell bits.length * (ell bits.length * ell bits.length)) := by
          have hraw :
              5 * ((ell bits.length * (ell bits.length * ell bits.length)) *
                  bits.length) <=
                20 * ((ell bits.length * (ell bits.length * ell bits.length)) *
                  bits.length) :=
            Nat.mul_le_mul_right _ (by omega : (5 : Nat) <= 20)
          simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hraw
        exact Nat.le_trans h hscale)

def longFlagRankWordSize (bits : List Bool) (target : Bool) : Nat :=
  SuccinctRankProposal.machineWordBits
    (longSuperFlagBits bits target).length

def longFlagRankBlocksPerSuper (_bits : List Bool) (_target : Bool) : Nat := 1

def longFlagRankBlockWidth (bits : List Bool) (target : Bool) : Nat :=
  longFlagRankWordSize bits target

theorem longFlagRankWordSize_pos
    (bits : List Bool) (target : Bool) :
    0 < longFlagRankWordSize bits target := by
  simp [longFlagRankWordSize, SuccinctRankProposal.machineWordBits_pos]

theorem longFlagRankWordSize_le_machine
    (bits : List Bool) (target : Bool) :
    longFlagRankWordSize bits target <=
      SuccinctRankProposal.machineWordBits bits.length := by
  unfold longFlagRankWordSize
  exact SuccinctRankProposal.machineWordBits_mono_le
    (longSuperFlagBits_length_le_length bits target)

theorem longFlagRankBlocksPerSuper_pos
    (bits : List Bool) (target : Bool) :
    0 < longFlagRankBlocksPerSuper bits target := by
  simp [longFlagRankBlocksPerSuper]

theorem longSuperFlagBits_length_lt_rank_word_pow
    (bits : List Bool) (target : Bool) :
    (longSuperFlagBits bits target).length <
      2 ^ longFlagRankWordSize bits target := by
  simpa [longFlagRankWordSize, SuccinctRankProposal.machineWordBits] using
    (Nat.lt_log2_self (n := (longSuperFlagBits bits target).length))

theorem longFlagRankBlockSpan_lt_pow
    (bits : List Bool) (target : Bool) :
    longFlagRankBlocksPerSuper bits target *
        longFlagRankWordSize bits target <
      2 ^ longFlagRankBlockWidth bits target := by
  have hsucc :=
    SuccinctSpace.nat_succ_le_two_pow
      (longFlagRankWordSize bits target)
  simpa [longFlagRankBlocksPerSuper, longFlagRankBlockWidth] using
    (by omega :
      longFlagRankWordSize bits target <
        2 ^ longFlagRankWordSize bits target)

def longFlagRankSuperOverhead (bits : List Bool) (target : Bool) : Nat :=
  (SuccinctRankProposal.canonicalSuperRankSampleTables
    (longSuperFlagBits bits target)
    (longFlagRankWordSize bits target)
    (longFlagRankBlocksPerSuper bits target)
    (longFlagRankWordSize bits target)
    (longSuperFlagBits_length_lt_rank_word_pow bits target)).payload.length

def longFlagRankBlockOverhead (bits : List Bool) (target : Bool) : Nat :=
  (SuccinctRankProposal.canonicalBlockRankSampleTablesOfLocalSpan
    (longSuperFlagBits bits target)
    (longFlagRankWordSize bits target)
    (longFlagRankBlocksPerSuper bits target)
    (longFlagRankBlockWidth bits target)
    (longFlagRankBlocksPerSuper_pos bits target)
    (longFlagRankBlockSpan_lt_pow bits target)).payload.length

def longFlagRankData (bits : List Bool) (target : Bool) :
    SuccinctRankProposal.TwoLevelPayloadLiveStoredWordRankData
      (longSuperFlagBits bits target)
      (longFlagRankSuperOverhead bits target)
      (longFlagRankBlockOverhead bits target)
      4 :=
  SuccinctRankProposal.canonicalTwoLevelRankDataOfChunksExactLocalBlock
    (longSuperFlagBits bits target)
    (longFlagRankWordSize_pos bits target)
    (by simp [longFlagRankWordSize])
    (longFlagRankBlocksPerSuper_pos bits target)
    (longSuperFlagBits_length_lt_rank_word_pow bits target)
    (longFlagRankBlockSpan_lt_pow bits target)
    (by omega)

theorem longFlagRankData_profile
    (bits : List Bool) (target : Bool) :
    let data := longFlagRankData bits target
    data.auxPayload.length =
        longFlagRankSuperOverhead bits target +
          longFlagRankBlockOverhead bits target /\
      data.wordSize <=
        SuccinctRankProposal.machineWordBits
          (longSuperFlagBits bits target).length /\
      SuccinctSpace.flattenPayloadWords data.bitWords.store.words.toList =
        longSuperFlagBits bits target /\
      (forall {word : List Bool},
        List.Mem word data.bitWords.store.words.toList ->
          word.length <=
            SuccinctRankProposal.machineWordBits
              (longSuperFlagBits bits target).length) /\
      forall rankTarget pos,
        (data.rankCosted rankTarget pos).cost <= 4 /\
          (data.rankCosted rankTarget pos).erase =
            RMQ.Succinct.rankPrefix rankTarget
              (longSuperFlagBits bits target) pos := by
  exact
    SuccinctRankProposal.canonicalTwoLevelRankDataOfChunksExactLocalBlock_profile
      (longSuperFlagBits bits target)
      (longFlagRankWordSize_pos bits target)
      (by simp [longFlagRankWordSize])
      (longFlagRankBlocksPerSuper_pos bits target)
      (longSuperFlagBits_length_lt_rank_word_pow bits target)
      (longFlagRankBlockSpan_lt_pow bits target)
      (by omega)

theorem longFlagRankData_auxPayload_le_overhead
    (bits : List Bool) (target : Bool) :
    (longFlagRankData bits target).auxPayload.length <=
      SuccinctSpace.logLogCubedSampledDirectoryOverhead 192 bits.length + 16 := by
  let flagBits := longSuperFlagBits bits target
  let flagLen := flagBits.length
  let rankWord := flagRankWordSize flagBits
  let w := wordBits bits.length
  let e := ell bits.length
  let e3 := e * (e * e)
  let n := bits.length
  let data := longFlagRankData bits target
  have hrankWordPos : 0 < rankWord := by
    simpa [rankWord, flagBits] using longFlagRankWordSize_pos bits target
  have hrankWordLeW : rankWord <= w := by
    simpa [rankWord, w, flagBits, wordBits] using
      longFlagRankWordSize_le_machine bits target
  have hauxEq :
      data.auxPayload.length =
        longFlagRankSuperOverhead bits target +
          longFlagRankBlockOverhead bits target := by
    have hprofile := longFlagRankData_profile bits target
    simpa [data] using hprofile.1
  have hsuperLe :
      longFlagRankSuperOverhead bits target <=
        2 * (flagLen + rankWord) := by
    unfold longFlagRankSuperOverhead
    rw [SuccinctRankProposal.canonicalSuperRankSampleTables_payload_length]
    have hentryLen :
        (SuccinctRankProposal.canonicalSuperRankEntries true flagBits
            rankWord
            (longFlagRankBlocksPerSuper bits target)).length =
          flagLen / rankWord + 1 := by
      simp [SuccinctRankProposal.canonicalSuperRankEntries, flagBits,
        flagLen, rankWord, longFlagRankBlocksPerSuper]
    have hentryLenFalse :
        (SuccinctRankProposal.canonicalSuperRankEntries false flagBits
            rankWord
            (longFlagRankBlocksPerSuper bits target)).length =
          flagLen / rankWord + 1 := by
      simp [SuccinctRankProposal.canonicalSuperRankEntries, flagBits,
        flagLen, rankWord, longFlagRankBlocksPerSuper]
    change
      (SuccinctRankProposal.canonicalSuperRankEntries true flagBits rankWord
            (longFlagRankBlocksPerSuper bits target)).length * rankWord +
        (SuccinctRankProposal.canonicalSuperRankEntries false flagBits rankWord
            (longFlagRankBlocksPerSuper bits target)).length * rankWord <=
      2 * (flagLen + rankWord)
    rw [hentryLen, hentryLenFalse]
    have hdiv : flagLen / rankWord * rankWord <= flagLen :=
      Nat.div_mul_le_self flagLen rankWord
    calc
      (flagLen / rankWord + 1) * rankWord +
          (flagLen / rankWord + 1) * rankWord <=
        (flagLen + rankWord) + (flagLen + rankWord) := by
          have hone :
              (flagLen / rankWord + 1) * rankWord <=
                flagLen + rankWord := by
            rw [Nat.add_mul, Nat.one_mul]
            exact Nat.add_le_add_right hdiv rankWord
          exact Nat.add_le_add hone hone
      _ = 2 * (flagLen + rankWord) := by omega
  have hblockLe :
      longFlagRankBlockOverhead bits target <=
        2 * (flagLen + rankWord) := by
    unfold longFlagRankBlockOverhead
    rw [SuccinctRankProposal.canonicalBlockRankSampleTablesOfLocalSpan_payload_length]
    have hentryLen :
        (SuccinctRankProposal.canonicalBlockRankEntries true flagBits
            rankWord
            (longFlagRankBlocksPerSuper bits target)).length =
          flagLen / rankWord + 1 := by
      simp [SuccinctRankProposal.canonicalBlockRankEntries, flagBits,
        flagLen, rankWord, longFlagRankBlocksPerSuper]
    have hentryLenFalse :
        (SuccinctRankProposal.canonicalBlockRankEntries false flagBits
            rankWord
            (longFlagRankBlocksPerSuper bits target)).length =
          flagLen / rankWord + 1 := by
      simp [SuccinctRankProposal.canonicalBlockRankEntries, flagBits,
        flagLen, rankWord, longFlagRankBlocksPerSuper]
    change
      (SuccinctRankProposal.canonicalBlockRankEntries true flagBits rankWord
            (longFlagRankBlocksPerSuper bits target)).length * rankWord +
        (SuccinctRankProposal.canonicalBlockRankEntries false flagBits rankWord
            (longFlagRankBlocksPerSuper bits target)).length * rankWord <=
      2 * (flagLen + rankWord)
    rw [hentryLen, hentryLenFalse]
    have hdiv : flagLen / rankWord * rankWord <= flagLen :=
      Nat.div_mul_le_self flagLen rankWord
    calc
      (flagLen / rankWord + 1) * rankWord +
          (flagLen / rankWord + 1) * rankWord <=
        (flagLen + rankWord) + (flagLen + rankWord) := by
          have hone :
              (flagLen / rankWord + 1) * rankWord <=
                flagLen + rankWord := by
            rw [Nat.add_mul, Nat.one_mul]
            exact Nat.add_le_add_right hdiv rankWord
          exact Nat.add_le_add hone hone
      _ = 2 * (flagLen + rankWord) := by omega
  have hauxLe : data.auxPayload.length <= 4 * (flagLen + rankWord) := by
    rw [hauxEq]
    calc
      longFlagRankSuperOverhead bits target +
          longFlagRankBlockOverhead bits target <=
        2 * (flagLen + rankWord) + 2 * (flagLen + rankWord) :=
          Nat.add_le_add hsuperLe hblockLe
      _ = 4 * (flagLen + rankWord) := by omega
  by_cases hnZero : n = 0
  · have hflagZero : flagLen = 0 := by
      have hlen := longSuperFlagBits_length_le_length bits target
      simpa [flagBits, flagLen, n, hnZero] using hlen
    have hw : w = 1 := by
      simp [w, wordBits, SuccinctRankProposal.machineWordBits, n, hnZero]
    have hrankSmall : rankWord <= 1 := by
      simpa [hw] using hrankWordLeW
    have hauxSmall : data.auxPayload.length <= 4 := by
      have h := hauxLe
      rw [hflagZero] at h
      omega
    exact Nat.le_trans hauxSmall (by omega)
  have hflagMul :
      flagLen * w <= 5 * (e3 * n) := by
    simpa [flagBits, flagLen, w, e, e3, n, Nat.mul_assoc,
      Nat.mul_left_comm, Nat.mul_comm] using
      longSuperFlagBits_length_mul_wordBits_le bits target
  have hrankMul :
      rankWord * w <= 4 * (e3 * n) := by
    have hwSq : w * w <= 4 * n := by
      have hnPos : 0 < n := Nat.pos_of_ne_zero hnZero
      simpa [w, wordBits, n] using
        machineWordBits_sq_le_four_mul_self_of_pos hnPos
    have hrankW : rankWord * w <= w * w :=
      Nat.mul_le_mul_right w hrankWordLeW
    have he3One : 1 <= e3 := by
      have he : 1 <= e := by simpa [e] using ell_pos bits.length
      have h1 := Nat.mul_le_mul he (Nat.mul_le_mul he he)
      simpa [e3] using h1
    calc
      rankWord * w <= w * w := hrankW
      _ <= 4 * n := hwSq
      _ <= 4 * (e3 * n) := by
        have hmul := Nat.mul_le_mul_right n he3One
        have hscaled := Nat.mul_le_mul_left 4 hmul
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hscaled
  have hauxMul :
      data.auxPayload.length * w <= 36 * (e3 * n) := by
    calc
      data.auxPayload.length * w <=
          4 * (flagLen + rankWord) * w := by
            exact Nat.mul_le_mul_right w hauxLe
      _ = 4 * (flagLen * w + rankWord * w) := by
            simp [Nat.add_mul, Nat.mul_assoc]
      _ <= 4 * (5 * (e3 * n) + 4 * (e3 * n)) := by
            exact Nat.mul_le_mul_left 4
              (Nat.add_le_add hflagMul hrankMul)
      _ = 36 * (e3 * n) := by
            let t := e3 * n
            change 4 * (5 * t + 4 * t) = 36 * t
            omega
  have hauxMulWide :
      data.auxPayload.length * w <= 96 * (e3 * n) := by
    exact Nat.le_trans hauxMul
      (Nat.mul_le_mul_right _ (by omega : (36 : Nat) <= 96))
  exact
    Nat.le_trans
      (payload_le_logLogCubedSampledDirectoryOverhead_of_mul_wordBits_le
        (n := bits.length) (payload := data.auxPayload.length) (scale := 96)
        (by
          simpa [w, e, e3, n, Nat.mul_assoc, Nat.mul_left_comm,
            Nat.mul_comm] using hauxMulWide))
      (Nat.le_add_right _ _)

def canonicalSparseExceptionSelectOverhead (n : Nat) : Nat :=
  SuccinctSpace.logLogCubedSampledDirectoryOverhead 40 n +
    SuccinctSpace.logLogCubedSampledDirectoryOverhead 40 n +
      (SuccinctSpace.logLogCubedSampledDirectoryOverhead 192 n + 16) +
        longSuperRelativeTableOverhead n +
          SuccinctSpace.logLogCubedSampledDirectoryOverhead 640 n +
            canonicalSparseExceptionDirectoryOverhead n

theorem canonicalSparseExceptionSelectOverhead_littleO :
    SuccinctSpace.LittleOLinear canonicalSparseExceptionSelectOverhead := by
  unfold canonicalSparseExceptionSelectOverhead
  have hsuper :
      SuccinctSpace.LittleOLinear
        (SuccinctSpace.logLogCubedSampledDirectoryOverhead 40) :=
    SuccinctSpace.logLogCubedSampledDirectoryOverhead_littleO 40
  have hflags :
      SuccinctSpace.LittleOLinear
        (SuccinctSpace.logLogCubedSampledDirectoryOverhead 40) :=
    SuccinctSpace.logLogCubedSampledDirectoryOverhead_littleO 40
  have hrank :
      SuccinctSpace.LittleOLinear
        (fun n =>
          SuccinctSpace.logLogCubedSampledDirectoryOverhead 192 n + 16) :=
    (SuccinctSpace.logLogCubedSampledDirectoryOverhead_littleO 192).add_const 16
  have hlocal :
      SuccinctSpace.LittleOLinear
        (SuccinctSpace.logLogCubedSampledDirectoryOverhead 640) :=
    SuccinctSpace.logLogCubedSampledDirectoryOverhead_littleO 640
  exact
    (((((hsuper.add hflags).add hrank).add
      longSuperRelativeTableOverhead_littleO).add hlocal).add
      canonicalSparseExceptionDirectoryOverhead_littleO)

theorem superEntries_missing_exact
    (bits : List Bool) (target : Bool) (q : Nat)
    (hmissing :
      (superEntries bits target)[
          falseSelectSuperSlot q
            (superStride bits.length)]? = none) :
    RMQ.Succinct.select target bits q = none := by
  cases hselect :
      RMQ.Succinct.select target bits q with
  | none =>
      rfl
  | some pos =>
      have hocc : q < occurrenceCount bits target :=
        occurrence_lt_count_of_select hselect
      have hslotMul :
          (q / superStride bits.length) *
              superStride bits.length <
            occurrenceCount bits target := by
        have hmul :=
          Nat.div_mul_le_self q (superStride bits.length)
        omega
      have hslot :
          falseSelectSuperSlot q
              (superStride bits.length) <
            superSlotCount bits target := by
        unfold falseSelectSuperSlot superSlotCount
        by_cases hlt :
            q / superStride bits.length <
              falseSelectCeilDiv (occurrenceCount bits target)
                (superStride bits.length)
        · exact hlt
        · have hceilLe :
              falseSelectCeilDiv (occurrenceCount bits target)
                  (superStride bits.length) <=
                q / superStride bits.length :=
            Nat.le_of_not_gt hlt
          have hmulLe :=
            Nat.mul_le_mul_right (superStride bits.length) hceilLe
          have hceilGe :=
            falseSelectCeilDiv_mul_ge_of_pos
              (n := occurrenceCount bits target)
              (stride := superStride bits.length)
              (superStride_pos bits.length)
          exact False.elim (by omega)
      have hget :=
        superEntries_get? bits target hslot
      rw [hget] at hmissing
      simp at hmissing

theorem superEntry_marked_eq_long
    (bits : List Bool) (target : Bool) (superSlot : Nat) :
    relativeSplitFalseSelectEntryIsMarked
      (superEntry bits target superSlot) =
        superIsLong bits target superSlot := by
  unfold superEntry
  by_cases hlong :
      superIsLong bits target superSlot = true
  · simp [relativeSplitFalseSelectEntryIsMarked, hlong]
  · have hfalse :
        superIsLong bits target superSlot = false := by
      cases h :
          superIsLong bits target superSlot
      · rfl
      · contradiction
    simp [relativeSplitFalseSelectEntryIsMarked, hfalse]

theorem longExplicit_exact
    (bits : List Bool) (target : Bool) (q : Nat)
    (super : SparseDenseFalseSelectDenseLocalEntry)
    (hsuper :
      (superEntries bits target)[
          falseSelectSuperSlot q
            (superStride bits.length)]? = some super)
    (hvalid : q < occurrenceCount bits target)
    (hlong :
      relativeSplitFalseSelectEntryIsMarked super = true) :
    ((longSuperRelativeEntries bits target)[
        relativeSplitFalseSelectLongCompactSlot
          (RMQ.Succinct.rankPrefix true
            (longSuperFlagBits bits target)
            (falseSelectSuperSlot q
              (superStride bits.length)))
          (q - super.baseOccurrence)
          (superStride bits.length)]?).map
      (fun offset =>
        relativeSplitFalseSelectEntryBasePosition
            (wordBits bits.length) super +
          offset) =
      RMQ.Succinct.select target bits q := by
  let superSlot :=
    falseSelectSuperSlot q (superStride bits.length)
  have hslot : superSlot < superSlotCount bits target := by
    have hlen := (List.getElem?_eq_some_iff.mp hsuper).1
    simpa [superSlot, superEntries_length] using hlen
  have hbuilt :=
    superEntries_get? bits target (superSlot := superSlot) hslot
  have hsuperEq :
      super = superEntry bits target superSlot := by
    rw [hbuilt] at hsuper
    exact (Option.some.inj hsuper).symm
  subst super
  have hlongBuilt :
      superIsLong bits target superSlot = true := by
    have hmark :=
      superEntry_marked_eq_long bits target superSlot
    rw [hmark] at hlong
    exact hlong
  have hbaseLeQ :
      superBaseOccurrence bits.length superSlot <= q := by
    have hmul :=
      Nat.div_mul_le_self q (superStride bits.length)
    simpa [superSlot, falseSelectSuperSlot, superBaseOccurrence]
      using hmul
  have hqLtBaseStride :
      q <
        superBaseOccurrence bits.length superSlot +
          superStride bits.length := by
    have hstride := superStride_pos bits.length
    have hlt :=
      Nat.lt_div_mul_add hstride (a := q)
    simpa [superSlot, falseSelectSuperSlot, superBaseOccurrence,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hlt
  have hlocalOcc :
      q - superBaseOccurrence bits.length superSlot <
        superStride bits.length := by
    omega
  have hend :
      superBaseOccurrence bits.length superSlot +
          (q - superBaseOccurrence bits.length superSlot) <
        superEndOccurrence bits target superSlot := by
    have hqEq :
        superBaseOccurrence bits.length superSlot +
            (q - superBaseOccurrence bits.length superSlot) = q := by
      omega
    rw [hqEq]
    unfold superEndOccurrence
    exact Nat.lt_min.mpr ⟨hqLtBaseStride, hvalid⟩
  rcases select_exists_of_lt_occurrenceCount
      bits target hvalid with ⟨pos, hselect⟩
  have hqEqLocal :
      superBaseOccurrence bits.length superSlot +
          (q - superBaseOccurrence bits.length superSlot) = q := by
    omega
  have hselectLocal :
      RMQ.Succinct.select target bits
          (superBaseOccurrence bits.length superSlot +
            (q - superBaseOccurrence bits.length superSlot)) =
        some pos := by
    simpa [hqEqLocal] using hselect
  have hlookup :=
    longSuperRelativeEntries_lookup_exact
      bits target (superSlot := superSlot)
      (localOccurrence :=
        q - superBaseOccurrence bits.length superSlot)
      (pos := pos) hslot hlongBuilt hlocalOcc hend hselectLocal
  have hbasePos :
      relativeSplitFalseSelectEntryBasePosition
          (wordBits bits.length)
          (superEntry bits target superSlot) =
        position bits target
          (superBaseOccurrence bits.length superSlot) := by
    unfold relativeSplitFalseSelectEntryBasePosition superEntry
    let baseOccurrence := superSlot * superStride bits.length
    let basePosition := position bits target baseOccurrence
    let wordSize := wordBits bits.length
    have hmod :
        basePosition / wordSize * wordSize +
            (basePosition - basePosition / wordSize * wordSize) =
          basePosition := by
      have hle := Nat.div_mul_le_self basePosition wordSize
      omega
    simpa [baseOccurrence, basePosition, wordSize,
      superBaseOccurrence, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using hmod
  have hbaseLePos :
      position bits target
          (superBaseOccurrence bits.length superSlot) <= pos := by
    have hsuperCount :
        superBaseOccurrence bits.length superSlot <
          occurrenceCount bits target := by
      omega
    rcases select_exists_of_lt_occurrenceCount
        bits target hsuperCount with ⟨basePos, hbaseSelect⟩
    have hmono :=
      select_index_mono (target := target) (bits := bits)
        (lo := superBaseOccurrence bits.length superSlot)
        (hi := q)
        (posLo := basePos) (posHi := pos)
        hbaseLeQ hbaseSelect hselect
    have hbaseEq :
        position bits target
            (superBaseOccurrence bits.length superSlot) = basePos :=
      position_eq_of_select bits target hbaseSelect
    rwa [hbaseEq]
  have hposEq :
      position bits target
          (superBaseOccurrence bits.length superSlot) +
        (pos -
          position bits target
            (superBaseOccurrence bits.length superSlot)) = pos := by
    omega
  have hqueryLookup :
      (longSuperRelativeEntries bits target)[
          relativeSplitFalseSelectLongCompactSlot
            (RMQ.Succinct.rankPrefix true
              (longSuperFlagBits bits target)
              (falseSelectSuperSlot q
                (superStride bits.length)))
            (q - (superEntry bits target superSlot).baseOccurrence)
            (superStride bits.length)]? =
        some
          (pos -
            position bits target
              (superBaseOccurrence bits.length superSlot)) := by
    simpa [relativeSplitFalseSelectLongCompactSlot, superEntry,
      superBaseOccurrence, superSlot] using hlookup
  rw [hselect]
  rw [hqueryLookup]
  simp [hbasePos, hposEq]

theorem localSlot_facts
    (bits : List Bool) (target : Bool) (q : Nat)
    (super : SparseDenseFalseSelectDenseLocalEntry)
    (hsuper :
      (superEntries bits target)[
          falseSelectSuperSlot q
            (superStride bits.length)]? = some super)
    (hvalid : q < occurrenceCount bits target)
    (hshort :
      relativeSplitFalseSelectEntryIsMarked super = false) :
    let localSlot :=
      relativeSplitFalseSelectLocalSlot q
        (superStride bits.length)
        (localSlotsPerSuper bits.length)
        (localStride bits.length) super
    localSlot < localSlotCount bits target /\
      localSlot <
        sparseExceptionEffectiveLocalSlotCount bits target /\
      compactLocalEntryIsLive bits target localSlot = true /\
      localSuperSlot bits.length localSlot =
        falseSelectSuperSlot q
          (superStride bits.length) /\
      localBaseOccurrence bits.length localSlot <= q /\
      q <
        localBaseOccurrence bits.length localSlot +
          localStride bits.length := by
  let superSlot :=
    falseSelectSuperSlot q (superStride bits.length)
  let slots := localSlotsPerSuper bits.length
  let superStrideV := superStride bits.length
  let localStrideV := localStride bits.length
  have hslot : superSlot < superSlotCount bits target := by
    have hlen := (List.getElem?_eq_some_iff.mp hsuper).1
    simpa [superSlot, superEntries_length] using hlen
  have hbuilt :=
    superEntries_get? bits target (superSlot := superSlot) hslot
  have hsuperEq :
      super = superEntry bits target superSlot := by
    rw [hbuilt] at hsuper
    exact (Option.some.inj hsuper).symm
  subst super
  have hshortBuilt :
      superIsLong bits target superSlot = false := by
    have hmark :=
      superEntry_marked_eq_long bits target superSlot
    rw [hmark] at hshort
    exact hshort
  have hbaseLeQ :
      superSlot * superStrideV <= q := by
    have hmul := Nat.div_mul_le_self q superStrideV
    simpa [superSlot, falseSelectSuperSlot, superStrideV] using hmul
  have hqLtBaseStride :
      q < superSlot * superStrideV + superStrideV := by
    have hstride := superStride_pos bits.length
    have hlt := Nat.lt_div_mul_add hstride (a := q)
    simpa [superSlot, falseSelectSuperSlot, superStrideV,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hlt
  let localInSuper := (q - superSlot * superStrideV) / localStrideV
  have hlocalStridePos : 0 < localStrideV := by
    simpa [localStrideV] using localStride_pos bits.length
  have hslotsPos : 0 < slots := by
    simpa [slots] using localSlotsPerSuper_pos bits.length
  have hlocalInSuperLt : localInSuper < slots := by
    by_cases hlt : localInSuper < slots
    case pos =>
      exact hlt
    case neg =>
      have hle : slots <= localInSuper := Nat.le_of_not_gt hlt
      have hslotsMul :
          slots * localStrideV <= localInSuper * localStrideV :=
        Nat.mul_le_mul_right localStrideV hle
      have hdivMul :
          localInSuper * localStrideV <=
            q - superSlot * superStrideV := by
        simpa [localInSuper] using
          Nat.div_mul_le_self
            (q - superSlot * superStrideV) localStrideV
      have hcap :
          superStrideV <= slots * localStrideV := by
        simpa [slots, superStrideV, localStrideV, localSlotsPerSuper] using
          (falseSelectLocalSlotsPerSuper_mul_localStride_ge_superStride
            (superStride := superStride bits.length)
            (localStride := localStride bits.length)
            (localStride_pos bits.length))
      exact False.elim (by omega)
  let localSlot := superSlot * slots + localInSuper
  have hlocalSlotEq :
      relativeSplitFalseSelectLocalSlot q
          (superStride bits.length)
          (localSlotsPerSuper bits.length)
          (localStride bits.length)
          (superEntry bits target superSlot) =
        localSlot := by
    simp [relativeSplitFalseSelectLocalSlot,
      relativeSplitFalseSelectLocalSlotInSuper,
      superEntry, superSlot, slots, superStrideV, localStrideV,
      localSlot, localInSuper, falseSelectSuperSlot]
  have hlocalSlotLt :
      localSlot < localSlotCount bits target := by
    have hnext :
        superSlot * slots + localInSuper <
          (superSlot + 1) * slots := by
      rw [Nat.add_mul, Nat.one_mul]
      omega
    have hle :
        (superSlot + 1) * slots <=
          superSlotCount bits target * slots := by
      exact Nat.mul_le_mul_right slots (by omega)
    simpa [localSlot, localSlotCount, slots, Nat.mul_assoc] using
      Nat.lt_of_lt_of_le hnext hle
  have hsuperSlotOfLocal :
      localSuperSlot bits.length localSlot = superSlot := by
    unfold localSuperSlot
    calc
      (localSlot / localSlotsPerSuper bits.length) =
          (localInSuper + slots * superSlot) / slots := by
            simp [localSlot, slots, Nat.mul_comm, Nat.add_comm]
      _ = localInSuper / slots + superSlot := by
            exact Nat.add_mul_div_left localInSuper superSlot hslotsPos
      _ = superSlot := by
            rw [Nat.div_eq_of_lt hlocalInSuperLt]
            simp
  have hlocalRemainder :
      localSlot -
          localSuperSlot bits.length localSlot *
            localSlotsPerSuper bits.length =
        localInSuper := by
    rw [hsuperSlotOfLocal]
    simp [localSlot, slots]
  have hlocalDiv :
      localSlot / localSlotsPerSuper bits.length =
        superSlot := by
    simpa [localSuperSlot] using hsuperSlotOfLocal
  have hlocalRemainderRaw :
      localSlot - superSlot * localSlotsPerSuper bits.length =
        localInSuper := by
    simpa [hsuperSlotOfLocal] using hlocalRemainder
  have hbaseEq :
      localBaseOccurrence bits.length localSlot =
        superSlot * superStrideV + localInSuper * localStrideV := by
    unfold localBaseOccurrence localSlotInSuperOfGlobal
    rw [hlocalDiv]
    rw [hlocalRemainderRaw]
  have hdivMul :
      localInSuper * localStrideV <=
        q - superSlot * superStrideV := by
    simpa [localInSuper] using
      Nat.div_mul_le_self (q - superSlot * superStrideV) localStrideV
  have hbaseLocalLeQ :
      localBaseOccurrence bits.length localSlot <= q := by
    rw [hbaseEq]
    omega
  have hslotsLeSuperStride :
      slots <= superStrideV := by
    simpa [slots, superStrideV, localStrideV, localSlotsPerSuper] using
      (falseSelectLocalSlotsPerSuper_le_superStride
        (hsuper := superStride_pos bits.length)
        (hlocal := localStride_pos bits.length))
  have hlocalSlotLeBase :
      localSlot <=
        localBaseOccurrence bits.length localSlot := by
    have hslotPart :
        superSlot * slots <= superSlot * superStrideV :=
      Nat.mul_le_mul_left superSlot hslotsLeSuperStride
    have hlocalStrideOne : 1 <= localStrideV := by omega
    have hlocalPart :
        localInSuper <= localInSuper * localStrideV := by
      simpa using Nat.mul_le_mul_left localInSuper hlocalStrideOne
    rw [hbaseEq]
    simp [localSlot]
    omega
  have hlocalSlotLtCount :
      localSlot < occurrenceCount bits target := by
    exact Nat.lt_of_le_of_lt
      (Nat.le_trans hlocalSlotLeBase hbaseLocalLeQ) hvalid
  have hlocalSlotLtEffective :
      localSlot <
        sparseExceptionEffectiveLocalSlotCount bits target := by
    unfold sparseExceptionEffectiveLocalSlotCount
    exact Nat.lt_min.mpr ⟨hlocalSlotLt, hlocalSlotLtCount⟩
  have hdeltaLtNext :
      q - superSlot * superStrideV <
        localInSuper * localStrideV + localStrideV := by
    simpa [localInSuper, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using
      Nat.lt_div_mul_add hlocalStridePos
        (a := q - superSlot * superStrideV)
  have hqLtLocalEnd :
      q <
        localBaseOccurrence bits.length localSlot +
          localStride bits.length := by
    rw [hbaseEq]
    simpa [localStrideV] using (by omega :
      q < superSlot * superStrideV + localInSuper * localStrideV +
        localStrideV)
  have hbaseCount :
      localBaseOccurrence bits.length localSlot <
        occurrenceCount bits target := by
    omega
  have hlive :
      compactLocalEntryIsLive bits target localSlot = true := by
    unfold compactLocalEntryIsLive
    simp [hsuperSlotOfLocal, hshortBuilt, hbaseCount]
  rw [hlocalSlotEq]
  exact
    ⟨hlocalSlotLt, hlocalSlotLtEffective, hlive, hsuperSlotOfLocal,
      hbaseLocalLeQ, hqLtLocalEnd⟩

theorem localEntry_marked_eq_flag
    (bits : List Bool) (target : Bool) (globalLocalSlot : Nat) :
    relativeSplitFalseSelectEntryIsMarked
      (localEntry bits target globalLocalSlot) =
        (compactLocalEntryIsLive bits target globalLocalSlot &&
          localIsSparseException bits target globalLocalSlot) := by
  unfold localEntry
  by_cases hlive :
      compactLocalEntryIsLive bits target globalLocalSlot = true
  · by_cases hflag :
        localIsSparseException bits target globalLocalSlot = true
    · simp [relativeSplitFalseSelectEntryIsMarked, hlive, hflag]
    · have hfalse :
          localIsSparseException bits target globalLocalSlot = false := by
        cases h :
            localIsSparseException bits target globalLocalSlot
        · rfl
        · contradiction
      simp [relativeSplitFalseSelectEntryIsMarked, hlive, hfalse]
  · have hfalse :
        compactLocalEntryIsLive bits target globalLocalSlot = false := by
      cases h :
          compactLocalEntryIsLive bits target globalLocalSlot
      · rfl
      · exact False.elim (hlive h)
    simp [relativeSplitFalseSelectEntryIsMarked, hfalse]

theorem localBaseOccurrence_exact
    (bits : List Bool) (target : Bool) (globalLocalSlot : Nat)
    (hlive :
      compactLocalEntryIsLive bits target globalLocalSlot = true) :
    relativeSplitFalseSelectLocalBaseOccurrence
      (superEntry bits target
        (globalLocalSlot / localSlotsPerSuper bits.length))
      (localEntry bits target globalLocalSlot) =
      localBaseOccurrence bits.length globalLocalSlot := by
  let superBase :=
    globalLocalSlot / localSlotsPerSuper bits.length *
      superStride bits.length
  let base := localBaseOccurrence bits.length globalLocalSlot
  have hbase_ge : superBase <= base := by
    simp [superBase, base, localBaseOccurrence,
      localSlotInSuperOfGlobal]
  simp [relativeSplitFalseSelectLocalBaseOccurrence,
    superEntry, localEntry, hlive, localSuperSlot]
  omega

theorem localBasePosition_exact
    (bits : List Bool) (target : Bool) (globalLocalSlot : Nat)
    (hlive :
      compactLocalEntryIsLive bits target globalLocalSlot = true) :
    relativeSplitFalseSelectLocalBasePosition
      (wordBits bits.length)
      (superEntry bits target
        (globalLocalSlot / localSlotsPerSuper bits.length))
      (localEntry bits target globalLocalSlot) =
      position bits target (localBaseOccurrence bits.length globalLocalSlot) := by
  let superSlot := globalLocalSlot / localSlotsPerSuper bits.length
  let superBase := superSlot * superStride bits.length
  let base := localBaseOccurrence bits.length globalLocalSlot
  let superPos := position bits target superBase
  let basePos := position bits target base
  let wordSize := wordBits bits.length
  have hbase_ge : superBase <= base := by
    simp [superBase, base, superSlot, localBaseOccurrence,
      localSlotInSuperOfGlobal]
  have hposMono : superPos <= basePos := by
    simpa [superPos, basePos] using
      position_mono bits target hbase_ge
  have hdivMono :
      superPos / wordSize <= basePos / wordSize := by
    exact Nat.div_le_div_right hposMono
  have hmod :
      basePos / wordSize * wordSize +
          (basePos - basePos / wordSize * wordSize) =
        basePos := by
    have hle := Nat.div_mul_le_self basePos wordSize
    omega
  have hwordIndexEq :
      superPos / wordSize +
          (basePos / wordSize - superPos / wordSize) =
        basePos / wordSize := by
    omega
  have hassembled :
      (superPos / wordSize +
          (basePos / wordSize - superPos / wordSize)) * wordSize +
          (basePos - basePos / wordSize * wordSize) =
        basePos := by
    rw [hwordIndexEq]
    exact hmod
  simpa [relativeSplitFalseSelectLocalBasePosition,
    superEntry, localEntry, hlive, localSuperSlot,
    superSlot, superBase, base, superPos, basePos, wordSize]
    using hassembled

theorem localEntries_missing_exact
    (bits : List Bool) (target : Bool) (q : Nat)
    (super : SparseDenseFalseSelectDenseLocalEntry)
    (hsuper :
      (superEntries bits target)[
          falseSelectSuperSlot q
            (superStride bits.length)]? = some super)
    (hvalid : q < occurrenceCount bits target)
    (hshort :
      relativeSplitFalseSelectEntryIsMarked super = false)
    (hmissing :
      (localEntries bits target)[
          relativeSplitFalseSelectLocalSlot q
            (superStride bits.length)
            (localSlotsPerSuper bits.length)
            (localStride bits.length) super]? =
        none) :
    RMQ.Succinct.select target bits q = none := by
  let localSlot :=
    relativeSplitFalseSelectLocalSlot q
      (superStride bits.length)
      (localSlotsPerSuper bits.length)
      (localStride bits.length) super
  have hfacts :=
    localSlot_facts bits target q super hsuper hvalid hshort
  rcases hfacts with
    ⟨hlocalSlotLt, _heff, _hlive, _hsameSuper,
      _hbaseLe, _hend⟩
  have hget :=
    localEntries_get? bits target
      (globalLocalSlot := localSlot) hlocalSlotLt
  have hmissingLocal :
      (localEntries bits target)[localSlot]? = none := by
    simpa [localSlot] using hmissing
  rw [hget] at hmissingLocal
  cases hmissingLocal

theorem sparseCompact_exact
    (bits : List Bool) (target : Bool) (q : Nat)
    (super loc : SparseDenseFalseSelectDenseLocalEntry)
    (hsuper :
      (superEntries bits target)[
          falseSelectSuperSlot q
            (superStride bits.length)]? = some super)
    (hvalid : q < occurrenceCount bits target)
    (hshort :
      relativeSplitFalseSelectEntryIsMarked super = false)
    (hlocal :
      (localEntries bits target)[
          relativeSplitFalseSelectLocalSlot q
            (superStride bits.length)
            (localSlotsPerSuper bits.length)
            (localStride bits.length) super]? =
        some loc)
    (hsparse :
      relativeSplitFalseSelectEntryIsMarked loc = true) :
    ((sparseExceptionDirectory bits target).readCosted
      (relativeSplitFalseSelectLocalBasePosition
        (wordBits bits.length) super loc)
      (relativeSplitFalseSelectLocalSlot q
        (superStride bits.length)
        (localSlotsPerSuper bits.length)
        (localStride bits.length) super)
      (q - relativeSplitFalseSelectLocalBaseOccurrence super loc)).erase =
      RMQ.Succinct.select target bits q := by
  let superSlot :=
    falseSelectSuperSlot q (superStride bits.length)
  have hsuperSlotLt :
      superSlot < superSlotCount bits target := by
    have hlen := (List.getElem?_eq_some_iff.mp hsuper).1
    simpa [superSlot, superEntries_length] using hlen
  have hbuiltSuper :=
    superEntries_get? bits target (superSlot := superSlot) hsuperSlotLt
  have hsuperEq :
      super = superEntry bits target superSlot := by
    rw [hbuiltSuper] at hsuper
    exact (Option.some.inj hsuper).symm
  subst super
  let localSlot :=
    relativeSplitFalseSelectLocalSlot q
      (superStride bits.length)
      (localSlotsPerSuper bits.length)
      (localStride bits.length)
      (superEntry bits target superSlot)
  have hfacts :=
    localSlot_facts bits target q
      (superEntry bits target superSlot)
      hsuper hvalid hshort
  rcases hfacts with
    ⟨hlocalSlotLt, heff, hlive, hsameSuper,
      hbaseLe, hqLtLocalEnd⟩
  have hlocalGet :=
    localEntries_get? bits target
      (globalLocalSlot := localSlot) hlocalSlotLt
  have hlocalAtSlot :
      (localEntries bits target)[localSlot]? = some loc := by
    simpa [localSlot] using hlocal
  rw [hlocalGet] at hlocalAtSlot
  have hlocEq :
      loc = localEntry bits target localSlot := by
    exact (Option.some.inj hlocalAtSlot).symm
  subst loc
  have hmark :=
    localEntry_marked_eq_flag bits target localSlot
  rw [hmark] at hsparse
  have hflag :
      localIsSparseException bits target localSlot = true := by
    have hpair :
        compactLocalEntryIsLive bits target localSlot = true /\
          localIsSparseException bits target localSlot = true := by
      simpa using hsparse
    exact hpair.2
  have hsameSuperSlot :
      localSuperSlot bits.length localSlot = superSlot := by
    simpa [superSlot] using hsameSuper
  have hlocalDiv :
      localSlot / localSlotsPerSuper bits.length = superSlot := by
    simpa [localSuperSlot] using hsameSuperSlot
  have hbaseOcc0 :=
    localBaseOccurrence_exact bits target localSlot hlive
  have hbaseOcc :
      relativeSplitFalseSelectLocalBaseOccurrence
        (superEntry bits target superSlot)
        (localEntry bits target localSlot) =
        localBaseOccurrence bits.length localSlot := by
    simpa [hlocalDiv] using hbaseOcc0
  have hbasePos0 :=
    localBasePosition_exact bits target localSlot hlive
  have hbasePos :
      relativeSplitFalseSelectLocalBasePosition
        (wordBits bits.length)
        (superEntry bits target superSlot)
        (localEntry bits target localSlot) =
        position bits target
          (localBaseOccurrence bits.length localSlot) := by
    simpa [hlocalDiv] using hbasePos0
  have hbaseLeLocal :
      localBaseOccurrence bits.length localSlot <= q := by
    simpa [localSlot] using hbaseLe
  have hqLtLocalEndLocal :
      q <
        localBaseOccurrence bits.length localSlot +
          localStride bits.length := by
    simpa [localSlot] using hqLtLocalEnd
  have hlocalOcc :
      q - localBaseOccurrence bits.length localSlot <
        localStride bits.length := by
    omega
  have hqEq :
      localBaseOccurrence bits.length localSlot +
          (q - localBaseOccurrence bits.length localSlot) =
        q := by
    omega
  have hbaseLeSuper :
      superSlot * superStride bits.length <= q := by
    have hmul :=
      Nat.div_mul_le_self q (superStride bits.length)
    simpa [superSlot, falseSelectSuperSlot] using hmul
  have hqLtBaseStride :
      q <
        superSlot * superStride bits.length +
          superStride bits.length := by
    have hstride := superStride_pos bits.length
    have hlt := Nat.lt_div_mul_add hstride (a := q)
    simpa [superSlot, falseSelectSuperSlot,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hlt
  have hqLtSuperEnd :
      q < superEndOccurrence bits target superSlot := by
    unfold superEndOccurrence superBaseOccurrence
    exact Nat.lt_min.mpr ⟨hqLtBaseStride, hvalid⟩
  have hend :
      localBaseOccurrence bits.length localSlot +
          (q - localBaseOccurrence bits.length localSlot) <
        superEndOccurrence bits target
          (localSuperSlot bits.length localSlot) := by
    rw [hqEq, hsameSuperSlot]
    exact hqLtSuperEnd
  rcases select_exists_of_lt_occurrenceCount
      bits target hvalid with ⟨pos, hselect⟩
  have hselectLocal :
      RMQ.Succinct.select target bits
          (localBaseOccurrence bits.length localSlot +
            (q - localBaseOccurrence bits.length localSlot)) =
        some pos := by
    simpa [hqEq] using hselect
  have hread :=
    sparseExceptionDirectory_readCosted_lookup_exact
      bits target hlocalSlotLt heff hflag hlocalOcc hend hselectLocal
  have hbaseCount :
      localBaseOccurrence bits.length localSlot <
        occurrenceCount bits target := by
    omega
  rcases select_exists_of_lt_occurrenceCount
      bits target hbaseCount with ⟨basePos, hbaseSelect⟩
  have hbaseLePos :
      position bits target
          (localBaseOccurrence bits.length localSlot) <= pos := by
    have hmono :=
      select_index_mono (target := target) (bits := bits)
        (lo := localBaseOccurrence bits.length localSlot)
        (hi := q) (posLo := basePos) (posHi := pos)
        hbaseLeLocal hbaseSelect hselect
    have hbaseEqPos :
        position bits target
            (localBaseOccurrence bits.length localSlot) = basePos :=
      position_eq_of_select bits target hbaseSelect
    rwa [hbaseEqPos]
  have hposEq :
      position bits target
          (localBaseOccurrence bits.length localSlot) +
        (pos -
          position bits target
            (localBaseOccurrence bits.length localSlot)) =
        pos := by
    omega
  rw [hselect]
  simpa [localSlot, hbaseOcc, hbasePos, hposEq] using hread

theorem selected_lt_shortLocalBase_plus_span
    (bits : List Bool) (target : Bool)
    {globalLocalSlot q pos : Nat}
    (hbaseLe :
      localBaseOccurrence bits.length globalLocalSlot <= q)
    (hqEnd :
      q < shortSuperLocalEndOccurrence bits target globalLocalSlot)
    (hselect :
      RMQ.Succinct.select target bits q = some pos) :
    pos <
      position bits target
          (localBaseOccurrence bits.length globalLocalSlot) +
        shortSuperLocalSpan bits target globalLocalSlot := by
  let base := localBaseOccurrence bits.length globalLocalSlot
  let endOcc := shortSuperLocalEndOccurrence bits target globalLocalSlot
  let basePos := position bits target base
  let lastPos := position bits target (endOcc - 1)
  have hqCount : q < occurrenceCount bits target :=
    occurrence_lt_count_of_select hselect
  have hbaseCount : base < occurrenceCount bits target := by
    omega
  rcases select_exists_of_lt_occurrenceCount
      bits target hbaseCount with ⟨baseWitness, hbaseSelect⟩
  have hbaseEq :
      basePos = baseWitness := by
    simpa [basePos, base] using
      position_eq_of_select bits target hbaseSelect
  have hbaseLePos : baseWitness <= pos :=
    select_index_mono (target := target) (bits := bits)
      (lo := base) (hi := q) (posLo := baseWitness)
      (posHi := pos) hbaseLe hbaseSelect hselect
  have hendCount : endOcc <= occurrenceCount bits target := by
    simpa [endOcc] using
      shortSuperLocalEndOccurrence_le_count bits target globalLocalSlot
  have hendPos : 0 < endOcc := by
    omega
  have hlastCount : endOcc - 1 < occurrenceCount bits target := by
    omega
  rcases select_exists_of_lt_occurrenceCount
      bits target hlastCount with ⟨lastWitness, hlastSelect⟩
  have hlastEq :
      lastPos = lastWitness := by
    simpa [lastPos, endOcc] using
      position_eq_of_select bits target hlastSelect
  have hqLeLast : q <= endOcc - 1 := by
    omega
  have hposLeLast : pos <= lastWitness :=
    select_index_mono (target := target) (bits := bits)
      (lo := q) (hi := endOcc - 1) (posLo := pos)
      (posHi := lastWitness) hqLeLast hselect hlastSelect
  unfold shortSuperLocalSpan
  change pos < basePos + (lastPos + 1 - basePos)
  rw [hbaseEq, hlastEq]
  omega

theorem dense_exact
    (bits : List Bool) (target : Bool) (q : Nat)
    (super loc : SparseDenseFalseSelectDenseLocalEntry)
    (hsuper :
      (superEntries bits target)[
          falseSelectSuperSlot q
            (superStride bits.length)]? = some super)
    (hvalid : q < occurrenceCount bits target)
    (hshort :
      relativeSplitFalseSelectEntryIsMarked super = false)
    (hlocal :
      (localEntries bits target)[
          relativeSplitFalseSelectLocalSlot q
            (superStride bits.length)
            (localSlotsPerSuper bits.length)
            (localStride bits.length) super]? =
        some loc)
    (hdense :
      relativeSplitFalseSelectEntryIsMarked loc = false) :
    (denseTwoWordSelectCosted target
      (SuccinctSpace.BoundedPayloadWordStore.ofChunks
        bits (wordBits_pos bits.length))
      (relativeSplitFalseSelectLocalBasePosition
        (wordBits bits.length) super loc)
      (relativeSplitFalseSelectLocalBaseOccurrence super loc) q).erase =
      RMQ.Succinct.select target bits q := by
  let superSlot :=
    falseSelectSuperSlot q (superStride bits.length)
  have hsuperSlotLt :
      superSlot < superSlotCount bits target := by
    have hlen := (List.getElem?_eq_some_iff.mp hsuper).1
    simpa [superSlot, superEntries_length] using hlen
  have hbuiltSuper :=
    superEntries_get? bits target (superSlot := superSlot) hsuperSlotLt
  have hsuperEq :
      super = superEntry bits target superSlot := by
    rw [hbuiltSuper] at hsuper
    exact (Option.some.inj hsuper).symm
  subst super
  let localSlot :=
    relativeSplitFalseSelectLocalSlot q
      (superStride bits.length)
      (localSlotsPerSuper bits.length)
      (localStride bits.length)
      (superEntry bits target superSlot)
  have hfacts :=
    localSlot_facts bits target q
      (superEntry bits target superSlot)
      hsuper hvalid hshort
  rcases hfacts with
    ⟨hlocalSlotLt, _heff, hlive, hsameSuper,
      hbaseLe, hqLtLocalEnd⟩
  have hlocalGet :=
    localEntries_get? bits target
      (globalLocalSlot := localSlot) hlocalSlotLt
  have hlocalAtSlot :
      (localEntries bits target)[localSlot]? = some loc := by
    simpa [localSlot] using hlocal
  rw [hlocalGet] at hlocalAtSlot
  have hlocEq :
      loc = localEntry bits target localSlot := by
    exact (Option.some.inj hlocalAtSlot).symm
  subst loc
  have hmark :=
    localEntry_marked_eq_flag bits target localSlot
  rw [hmark] at hdense
  have hliveLocal :
      compactLocalEntryIsLive bits target localSlot = true := by
    simpa [localSlot] using hlive
  have hflagFalse :
      localIsSparseException bits target localSlot = false := by
    cases hflag :
        localIsSparseException bits target localSlot
    · rfl
    · have hmarkedTrue :
          (compactLocalEntryIsLive bits target localSlot &&
            localIsSparseException bits target localSlot) = true := by
        simp [hliveLocal, hflag]
      rw [hmarkedTrue] at hdense
      cases hdense
  have hsameSuperSlot :
      localSuperSlot bits.length localSlot = superSlot := by
    simpa [superSlot] using hsameSuper
  have hlocalDiv :
      localSlot / localSlotsPerSuper bits.length = superSlot := by
    simpa [localSuperSlot] using hsameSuperSlot
  have hbaseOcc0 :=
    localBaseOccurrence_exact bits target localSlot hliveLocal
  have hbaseOcc :
      relativeSplitFalseSelectLocalBaseOccurrence
        (superEntry bits target superSlot)
        (localEntry bits target localSlot) =
        localBaseOccurrence bits.length localSlot := by
    simpa [hlocalDiv] using hbaseOcc0
  have hbasePos0 :=
    localBasePosition_exact bits target localSlot hliveLocal
  have hbasePos :
      relativeSplitFalseSelectLocalBasePosition
        (wordBits bits.length)
        (superEntry bits target superSlot)
        (localEntry bits target localSlot) =
        position bits target
          (localBaseOccurrence bits.length localSlot) := by
    simpa [hlocalDiv] using hbasePos0
  have hbaseLeLocal :
      localBaseOccurrence bits.length localSlot <= q := by
    simpa [localSlot] using hbaseLe
  have hqLtLocalEndLocal :
      q <
        localBaseOccurrence bits.length localSlot +
          localStride bits.length := by
    simpa [localSlot] using hqLtLocalEnd
  have hbaseLeSuper :
      superSlot * superStride bits.length <= q := by
    have hmul :=
      Nat.div_mul_le_self q (superStride bits.length)
    simpa [superSlot, falseSelectSuperSlot] using hmul
  have hqLtBaseStride :
      q <
        superSlot * superStride bits.length +
          superStride bits.length := by
    have hstride := superStride_pos bits.length
    have hlt := Nat.lt_div_mul_add hstride (a := q)
    simpa [superSlot, falseSelectSuperSlot,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hlt
  have hqLtSuperEnd :
      q < superEndOccurrence bits target superSlot := by
    unfold superEndOccurrence superBaseOccurrence
    exact Nat.lt_min.mpr ⟨hqLtBaseStride, hvalid⟩
  have hqLtShortEnd :
      q <
        shortSuperLocalEndOccurrence bits target localSlot := by
    unfold shortSuperLocalEndOccurrence
    exact Nat.lt_min.mpr
      ⟨hqLtLocalEndLocal, by
        simpa [hsameSuperSlot] using hqLtSuperEnd⟩
  have hlocalSpanLeWord :
      shortSuperLocalSpan bits target localSlot <=
        wordBits bits.length := by
    unfold localIsSparseException at hflagFalse
    have hshortBuilt :
        superIsLong bits target superSlot = false := by
      have hsuperMark :=
        superEntry_marked_eq_long bits target superSlot
      rw [hsuperMark] at hshort
      exact hshort
    have hshortAtLocal :
        superIsLong bits target
            (localSuperSlot bits.length localSlot) = false := by
      rw [hsameSuperSlot]
      exact hshortBuilt
    rw [hshortAtLocal] at hflagFalse
    simp only [Bool.not_false, Bool.true_and] at hflagFalse
    by_cases hlt :
        wordBits bits.length <
          shortSuperLocalSpan bits target localSlot
    · have hdec :
          decide
              (wordBits bits.length <
                shortSuperLocalSpan bits target localSlot) = true := by
        simp [hlt]
      rw [hdec] at hflagFalse
      cases hflagFalse
    · exact Nat.le_of_not_gt hlt
  rcases select_exists_of_lt_occurrenceCount
      bits target hvalid with ⟨pos, hselect⟩
  have hposLtLocalSpan :=
    selected_lt_shortLocalBase_plus_span
      bits target hbaseLeLocal hqLtShortEnd hselect
  have hposSpanBuilt :
      pos <
        position bits target
            (localBaseOccurrence bits.length localSlot) +
          wordBits bits.length := by
    omega
  have hbaseCount :
      localBaseOccurrence bits.length localSlot <
        occurrenceCount bits target := by
    omega
  rcases select_exists_of_lt_occurrenceCount
      bits target hbaseCount with ⟨basePos, hbaseSelect⟩
  have hbaseEqPos :
      position bits target
          (localBaseOccurrence bits.length localSlot) = basePos :=
    position_eq_of_select bits target hbaseSelect
  have hbaseSelectEntry :
      RMQ.Succinct.select target bits
          (relativeSplitFalseSelectLocalBaseOccurrence
            (superEntry bits target superSlot)
            (localEntry bits target localSlot)) =
        some
          (relativeSplitFalseSelectLocalBasePosition
            (wordBits bits.length)
            (superEntry bits target superSlot)
            (localEntry bits target localSlot)) := by
    simpa [hbaseOcc, hbasePos, hbaseEqPos] using hbaseSelect
  have hbaseLeEntry :
      relativeSplitFalseSelectLocalBaseOccurrence
          (superEntry bits target superSlot)
          (localEntry bits target localSlot) <= q := by
    simpa [hbaseOcc] using hbaseLeLocal
  have hposSpanEntry :
      pos <
        relativeSplitFalseSelectLocalBasePosition
            (wordBits bits.length)
            (superEntry bits target superSlot)
            (localEntry bits target localSlot) +
          wordBits bits.length := by
    simpa [hbasePos] using hposSpanBuilt
  have hdenseFacts :
      DenseLocalPayloadRoutingFacts
        target bits (wordBits bits.length)
        (relativeSplitFalseSelectLocalBasePosition
          (wordBits bits.length)
          (superEntry bits target superSlot)
          (localEntry bits target localSlot))
        (relativeSplitFalseSelectLocalBaseOccurrence
          (superEntry bits target superSlot)
          (localEntry bits target localSlot)) q :=
    denseLocalPayloadRoutingFacts_of_selected_span
      (hwordSize := wordBits_pos bits.length)
      hbaseSelectEntry hselect hbaseLeEntry hposSpanEntry
  have haligned :
      FalseSelectAlignedBitWords bits
        (wordBits bits.length)
        (SuccinctSpace.BoundedPayloadWordStore.ofChunks
          bits (wordBits_pos bits.length)) :=
    falseSelectAlignedBitWords_ofChunks bits
      (wordBits_pos bits.length)
  simpa [localSlot] using
    denseTwoWordSelectCosted_exact_of_payload_routing_facts
      target haligned hdenseFacts

structure SparseExceptionSelectData
    (bits : List Bool) (target : Bool)
    (rankSuperOverhead rankBlockOverhead : Nat) where
  wordSize : Nat
  wordSize_pos : 0 < wordSize
  wordSize_le_machine :
    wordSize <= SuccinctRankProposal.machineWordBits bits.length
  superStride : Nat
  superStride_pos : 0 < superStride
  localStride : Nat
  localStride_pos : 0 < localStride
  localSlotsPerSuper : Nat
  superEntries : List SparseDenseFalseSelectDenseLocalEntry
  longFlagBits : List Bool
  longFlagRankSuperOverhead : Nat
  longFlagRankBlockOverhead : Nat
  longFlagRankData :
    SuccinctRankProposal.TwoLevelPayloadLiveStoredWordRankData
      longFlagBits longFlagRankSuperOverhead longFlagRankBlockOverhead 4
  longFlagRank_wordSize_le_machine :
    longFlagRankData.wordSize <=
      SuccinctRankProposal.machineWordBits bits.length
  longFlagRank_superWidth_le_machine :
    longFlagRankData.superWidth <=
      SuccinctRankProposal.machineWordBits bits.length
  longFlagRank_blockWidth_le_machine :
    longFlagRankData.blockWidth <=
      SuccinctRankProposal.machineWordBits bits.length
  longSuperRelativeEntries : List Nat
  localEntries : List SparseDenseFalseSelectDenseLocalEntry
  superFieldWidth : Nat
  longSuperRelativeWidth : Nat
  localFieldWidth : Nat
  superTable :
    FixedWidthSparseDenseFalseSelectDenseLocalEntryTable
      superEntries superFieldWidth
  longSuperRelativeTable :
    SuccinctSpace.FixedWidthNatTable
      longSuperRelativeEntries longSuperRelativeWidth
  localTable :
    FixedWidthSparseDenseFalseSelectDenseLocalEntryTable
      localEntries localFieldWidth
  sparseDirectory :
    SparseExceptionDirectory
      bits target rankSuperOverhead rankBlockOverhead
  bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize
  super_read_words_length_le_machine :
    FixedWidthSparseDenseFalseSelectDenseLocalEntryTable.ReadWordsLengthLeMachine
      superTable bits.length
  long_read_words_length_le_machine :
    forall {i : Nat} {word : List Bool},
      longSuperRelativeTable.store.words[i]? = some word ->
        word.length <= SuccinctRankProposal.machineWordBits bits.length
  local_read_words_length_le_machine :
    FixedWidthSparseDenseFalseSelectDenseLocalEntryTable.ReadWordsLengthLeMachine
      localTable bits.length
  payload_length_le_overhead :
    (superTable.payload ++ longFlagBits ++
      longFlagRankData.auxPayload ++ longSuperRelativeTable.payload ++
        localTable.payload ++ sparseDirectory.payload).length <=
        canonicalSparseExceptionSelectOverhead bits.length
  super_missing_exact :
    forall q,
      superEntries[falseSelectSuperSlot q superStride]? = none ->
        RMQ.Succinct.select target bits q = none
  long_explicit_exact :
    forall q super,
      superEntries[falseSelectSuperSlot q superStride]? = some super ->
      q < occurrenceCount bits target ->
      relativeSplitFalseSelectEntryIsMarked super = true ->
        (longSuperRelativeEntries[
            relativeSplitFalseSelectLongCompactSlot
              (RMQ.Succinct.rankPrefix true longFlagBits
                (falseSelectSuperSlot q superStride))
              (q - super.baseOccurrence) superStride]?).map
          (fun offset =>
            relativeSplitFalseSelectEntryBasePosition wordSize super +
              offset) =
          RMQ.Succinct.select target bits q
  local_missing_exact :
    forall q super,
      superEntries[falseSelectSuperSlot q superStride]? = some super ->
      q < occurrenceCount bits target ->
      relativeSplitFalseSelectEntryIsMarked super = false ->
      localEntries[
          relativeSplitFalseSelectLocalSlot q superStride
            localSlotsPerSuper localStride super]? = none ->
        RMQ.Succinct.select target bits q = none
  sparse_compact_exact :
    forall q super loc,
      superEntries[falseSelectSuperSlot q superStride]? = some super ->
      q < occurrenceCount bits target ->
      relativeSplitFalseSelectEntryIsMarked super = false ->
      localEntries[
          relativeSplitFalseSelectLocalSlot q superStride
            localSlotsPerSuper localStride super]? = some loc ->
      relativeSplitFalseSelectEntryIsMarked loc = true ->
        (sparseDirectory.readCosted
          (relativeSplitFalseSelectLocalBasePosition wordSize super loc)
          (relativeSplitFalseSelectLocalSlot q superStride
            localSlotsPerSuper localStride super)
          (q - relativeSplitFalseSelectLocalBaseOccurrence super loc)).erase =
          RMQ.Succinct.select target bits q
  dense_exact :
    forall q super loc,
      superEntries[falseSelectSuperSlot q superStride]? = some super ->
      q < occurrenceCount bits target ->
      relativeSplitFalseSelectEntryIsMarked super = false ->
      localEntries[
          relativeSplitFalseSelectLocalSlot q superStride
            localSlotsPerSuper localStride super]? = some loc ->
      relativeSplitFalseSelectEntryIsMarked loc = false ->
        (denseTwoWordSelectCosted target bitWords
          (relativeSplitFalseSelectLocalBasePosition wordSize super loc)
          (relativeSplitFalseSelectLocalBaseOccurrence super loc) q).erase =
          RMQ.Succinct.select target bits q

namespace SparseExceptionSelectData

def payload
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      SparseExceptionSelectData
        bits target rankSuperOverhead rankBlockOverhead) :
    List Bool :=
  data.superTable.payload ++ data.longFlagBits ++
    data.longFlagRankData.auxPayload ++
      data.longSuperRelativeTable.payload ++
        data.localTable.payload ++ data.sparseDirectory.payload

def longFlagRankReadWords
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      SparseExceptionSelectData
        bits target rankSuperOverhead rankBlockOverhead) :
    List (List Bool) :=
  (((data.longFlagRankData.superTables.trueTable.store.words.toList ++
      data.longFlagRankData.superTables.falseTable.store.words.toList) ++
    data.longFlagRankData.blockTables.trueTable.store.words.toList ++
      data.longFlagRankData.blockTables.falseTable.store.words.toList) ++
        data.longFlagRankData.bitWords.store.words.toList)

def readWords
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      SparseExceptionSelectData
        bits target rankSuperOverhead rankBlockOverhead) :
    List (List Bool) :=
  data.superTable.readWords ++
    data.longFlagRankReadWords ++
      data.longSuperRelativeTable.store.words.toList ++
        data.localTable.readWords ++
          data.sparseDirectory.readWords ++
            data.bitWords.store.words.toList

def queryOccurrence
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (_data :
      SparseExceptionSelectData
        bits target rankSuperOverhead rankBlockOverhead)
    (idx : Nat) : Nat :=
  idx

def selectCosted
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      SparseExceptionSelectData
        bits target rankSuperOverhead rankBlockOverhead)
    (idx : Nat) : Costed (Option Nat) :=
  let q := data.queryOccurrence idx
  if idx < occurrenceCount bits target then
    Costed.bind
      (data.superTable.readCosted
        (falseSelectSuperSlot q data.superStride)) fun super? =>
      match super? with
      | none => Costed.pure none
      | some super =>
          if relativeSplitFalseSelectEntryIsMarked super then
            Costed.bind
              (data.longFlagRankData.rankCosted true
                (falseSelectSuperSlot q data.superStride))
              fun exceptionRank =>
                relativeOffsetReadCosted data.longSuperRelativeTable
                  (relativeSplitFalseSelectEntryBasePosition
                    data.wordSize super)
                  (relativeSplitFalseSelectLongCompactSlot
                    exceptionRank (q - super.baseOccurrence)
                    data.superStride)
          else
            let localSlot :=
              relativeSplitFalseSelectLocalSlot q data.superStride
                data.localSlotsPerSuper data.localStride super
            Costed.bind (data.localTable.readCosted localSlot) fun loc? =>
              match loc? with
              | none => Costed.pure none
              | some loc =>
                  if relativeSplitFalseSelectEntryIsMarked loc then
                    data.sparseDirectory.readCosted
                      (relativeSplitFalseSelectLocalBasePosition
                        data.wordSize super loc)
                      localSlot
                      (q -
                        relativeSplitFalseSelectLocalBaseOccurrence
                          super loc)
                  else
                    denseTwoWordSelectCosted target data.bitWords
                      (relativeSplitFalseSelectLocalBasePosition
                        data.wordSize super loc)
                      (relativeSplitFalseSelectLocalBaseOccurrence
                        super loc) q
  else
    Costed.pure none

theorem payload_length_le_canonical
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      SparseExceptionSelectData
        bits target rankSuperOverhead rankBlockOverhead) :
    data.payload.length <=
      canonicalSparseExceptionSelectOverhead bits.length := by
  simpa [payload] using data.payload_length_le_overhead

theorem selectCosted_cost_le
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      SparseExceptionSelectData
        bits target rankSuperOverhead rankBlockOverhead) (idx : Nat) :
    (data.selectCosted idx).cost <=
      sparseDenseFalseSelectQueryCost := by
  unfold selectCosted queryOccurrence sparseDenseFalseSelectQueryCost
  by_cases hvalid : idx < occurrenceCount bits target
  case pos =>
    cases hsuperValue :
        (data.superTable.readCosted
          (falseSelectSuperSlot
            idx data.superStride)).value with
    | none =>
        simp [Costed.bind, Costed.pure, hvalid, hsuperValue] <;> omega
    | some super =>
        by_cases hlong :
            relativeSplitFalseSelectEntryIsMarked super = true
        case pos =>
          have hrankCost :=
            data.longFlagRankData.rankCosted_cost_le true
              (falseSelectSuperSlot
                idx data.superStride)
          have hlongCost :
              (data.longSuperRelativeTable.readCosted
                (relativeSplitFalseSelectLongCompactSlot
                  (data.longFlagRankData.rankCosted true
                    (falseSelectSuperSlot
                      idx data.superStride)).value
                  (idx - super.baseOccurrence)
                  data.superStride)).cost <= 1 := by
            exact data.longSuperRelativeTable.readCosted_cost_le_one _
          simp [relativeOffsetReadCosted, Costed.bind, Costed.map,
            Costed.pure, hvalid, hsuperValue, hlong] <;> omega
        case neg =>
          let localSlot :=
            relativeSplitFalseSelectLocalSlot
              idx data.superStride
              data.localSlotsPerSuper data.localStride super
          cases hlocalValue :
              (data.localTable.readCosted localSlot).value with
          | none =>
              simp [Costed.bind, Costed.pure, hvalid, hsuperValue, hlong,
                localSlot, hlocalValue] <;> omega
          | some loc =>
              by_cases hsparse :
                  relativeSplitFalseSelectEntryIsMarked loc = true
              case pos =>
                have hsparseCost :
                  (data.sparseDirectory.readCosted
                    (relativeSplitFalseSelectLocalBasePosition
                      data.wordSize super loc)
                    (relativeSplitFalseSelectLocalSlot
                      idx data.superStride
                      data.localSlotsPerSuper data.localStride super)
                    (idx -
                      relativeSplitFalseSelectLocalBaseOccurrence super loc)).cost
                      <= 5 := by
                  simpa [localSlot] using
                    data.sparseDirectory.readCosted_cost_le_five
                      (relativeSplitFalseSelectLocalBasePosition
                      data.wordSize super loc)
                      localSlot
                      (idx -
                        relativeSplitFalseSelectLocalBaseOccurrence super loc)
                simp [Costed.bind, hvalid, hsuperValue, hlong, localSlot,
                  hlocalValue, hsparse] <;> omega
              case neg =>
                have hdenseCost :=
                  denseTwoWordSelectCosted_cost_le_five target
                    data.bitWords
                    (relativeSplitFalseSelectLocalBasePosition
                      data.wordSize super loc)
                    (relativeSplitFalseSelectLocalBaseOccurrence
                      super loc) idx
                simp [Costed.bind, hvalid, hsuperValue, hlong, localSlot,
                  hlocalValue, hsparse] <;> omega
  case neg =>
    simp [Costed.pure, hvalid]

theorem selectCosted_exact
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      SparseExceptionSelectData
        bits target rankSuperOverhead rankBlockOverhead) (idx : Nat) :
    (data.selectCosted idx).erase =
      RMQ.Succinct.select target bits idx := by
  let q := idx
  unfold selectCosted queryOccurrence
  dsimp only
  by_cases hvalid : idx < occurrenceCount bits target
  case pos =>
    have hvalidQ : q < occurrenceCount bits target := by
      simpa [q] using hvalid
    cases hsuper :
        data.superEntries[
          falseSelectSuperSlot
            idx data.superStride]? with
    | none =>
        have hsuperQ :
            data.superEntries[
                falseSelectSuperSlot q data.superStride]? =
              none := by
          simpa [q] using hsuper
        simp [hvalid, hsuper, Costed.erase_bind,
          FixedWidthSparseDenseFalseSelectDenseLocalEntryTable.readCosted_erase]
        exact (data.super_missing_exact q hsuperQ).symm
    | some super =>
        have hsuperQ :
            data.superEntries[
                falseSelectSuperSlot q data.superStride]? =
              some super := by
          simpa [q] using hsuper
        by_cases hlong :
            relativeSplitFalseSelectEntryIsMarked super = true
        case pos =>
          have hrank :=
            data.longFlagRankData.rankCosted_exact true
              (falseSelectSuperSlot
                idx data.superStride)
          simp [hvalid, hsuper, hlong, relativeOffsetReadCosted,
            Costed.erase_bind, Costed.erase_map,
            FixedWidthSparseDenseFalseSelectDenseLocalEntryTable.readCosted_erase,
            SuccinctSpace.FixedWidthNatTable.readCosted_erase, hrank]
          simpa [q] using
            data.long_explicit_exact q super hsuperQ hvalidQ hlong
        case neg =>
          let localSlot :=
            relativeSplitFalseSelectLocalSlot
              idx data.superStride
              data.localSlotsPerSuper data.localStride super
          have hlongFalse :
              relativeSplitFalseSelectEntryIsMarked super = false := by
            cases hmark : relativeSplitFalseSelectEntryIsMarked super
            case false =>
              rfl
            case true =>
              exact False.elim (hlong hmark)
          cases hlocal :
              data.localEntries[localSlot]? with
          | none =>
              simp [hvalid, hsuper, hlong, localSlot, hlocal,
                Costed.erase_bind,
                FixedWidthSparseDenseFalseSelectDenseLocalEntryTable.readCosted_erase]
              have hlocal' :
                data.localEntries[
                    relativeSplitFalseSelectLocalSlot q data.superStride
                      data.localSlotsPerSuper data.localStride super]? =
                  none := by
                simpa [q, localSlot] using hlocal
              exact (data.local_missing_exact q super hsuperQ hvalidQ hlongFalse
                hlocal').symm
          | some loc =>
              by_cases hsparse :
                  relativeSplitFalseSelectEntryIsMarked loc = true
              case pos =>
                simp [hvalid, hsuper, hlong, localSlot, hlocal,
                  Costed.erase_bind,
                  FixedWidthSparseDenseFalseSelectDenseLocalEntryTable.readCosted_erase]
                have hlocal' :
                    data.localEntries[
                        relativeSplitFalseSelectLocalSlot q data.superStride
                        data.localSlotsPerSuper data.localStride super]? =
                      some loc := by
                  simpa [q, localSlot] using hlocal
                simp [hsparse]
                simpa [q] using
                  data.sparse_compact_exact q super loc hsuperQ hvalidQ
                    hlongFalse hlocal' hsparse
              case neg =>
                have hsparseFalse :
                    relativeSplitFalseSelectEntryIsMarked loc = false := by
                  cases hmark : relativeSplitFalseSelectEntryIsMarked loc
                  case false =>
                    rfl
                  case true =>
                    exact False.elim (hsparse hmark)
                simp [hvalid, hsuper, hlong, localSlot, hlocal,
                  Costed.erase_bind,
                  FixedWidthSparseDenseFalseSelectDenseLocalEntryTable.readCosted_erase]
                have hlocal' :
                    data.localEntries[
                        relativeSplitFalseSelectLocalSlot q data.superStride
                        data.localSlotsPerSuper data.localStride super]? =
                      some loc := by
                  simpa [q, localSlot] using hlocal
                simp [hsparse]
                simpa [q] using
                  data.dense_exact q super loc hsuperQ hvalidQ hlongFalse
                    hlocal' hsparseFalse
  case neg =>
    simp [hvalid, Costed.pure]
    exact
      (select_none_of_rankPrefix_length_le
        (target := target) (bits := bits) (occurrence := idx)
        (by
          simpa [occurrenceCount] using Nat.le_of_not_gt hvalid)).symm

theorem longFlagRank_read_word_length_le_machine
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      SparseExceptionSelectData
        bits target rankSuperOverhead rankBlockOverhead)
    {word : List Bool}
    (hmem : List.Mem word data.longFlagRankReadWords) :
    word.length <=
      SuccinctRankProposal.machineWordBits bits.length := by
  rw [longFlagRankReadWords] at hmem
  cases List.mem_append.mp hmem with
  | inl hsampleMem =>
      cases List.mem_append.mp hsampleMem with
      | inl hsamplePrefix =>
          cases List.mem_append.mp hsamplePrefix with
          | inl hsuperMem =>
              cases List.mem_append.mp hsuperMem with
              | inl hsuperTrueMem =>
                  cases (List.mem_iff_getElem?.mp hsuperTrueMem) with
                  | intro i hgetList =>
                    have hget :
                        data.longFlagRankData.superTables.trueTable.store.words[i]? =
                          some word := by
                      simpa [Array.getElem?_toList] using hgetList
                    rw [data.longFlagRankData.superTables.trueTable.read_word_length_of_some
                      hget]
                    exact data.longFlagRank_superWidth_le_machine
              | inr hsuperFalseMem =>
                  cases (List.mem_iff_getElem?.mp hsuperFalseMem) with
                  | intro i hgetList =>
                    have hget :
                        data.longFlagRankData.superTables.falseTable.store.words[i]? =
                          some word := by
                      simpa [Array.getElem?_toList] using hgetList
                    rw [data.longFlagRankData.superTables.falseTable.read_word_length_of_some
                      hget]
                    exact data.longFlagRank_superWidth_le_machine
          | inr hblockTrueMem =>
              cases (List.mem_iff_getElem?.mp hblockTrueMem) with
              | intro i hgetList =>
                have hget :
                    data.longFlagRankData.blockTables.trueTable.store.words[i]? =
                      some word := by
                  simpa [Array.getElem?_toList] using hgetList
                rw [data.longFlagRankData.blockTables.trueTable.read_word_length_of_some
                  hget]
                exact data.longFlagRank_blockWidth_le_machine
      | inr hblockFalseMem =>
          cases (List.mem_iff_getElem?.mp hblockFalseMem) with
          | intro i hgetList =>
            have hget :
                data.longFlagRankData.blockTables.falseTable.store.words[i]? =
                  some word := by
              simpa [Array.getElem?_toList] using hgetList
            rw [data.longFlagRankData.blockTables.falseTable.read_word_length_of_some
              hget]
            exact data.longFlagRank_blockWidth_le_machine
  | inr hflagMem =>
      exact Nat.le_trans
        (data.longFlagRankData.bitWords.word_length_le hflagMem)
        data.longFlagRank_wordSize_le_machine

theorem read_word_length_le_machine
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      SparseExceptionSelectData
        bits target rankSuperOverhead rankBlockOverhead)
    {word : List Bool}
    (hmem : List.Mem word data.readWords) :
    word.length <=
      SuccinctRankProposal.machineWordBits bits.length := by
  rw [readWords] at hmem
  cases List.mem_append.mp hmem with
  | inl hprefix0 =>
      cases List.mem_append.mp hprefix0 with
      | inl hprefix1 =>
          cases List.mem_append.mp hprefix1 with
          | inl hprefix2 =>
              cases List.mem_append.mp hprefix2 with
              | inl hsuperOrRank =>
                  cases List.mem_append.mp hsuperOrRank with
                  | inl hsuperMem =>
                      exact data.superTable.read_word_length_le_machine
                        data.super_read_words_length_le_machine hsuperMem
                  | inr hrankMem =>
                      exact data.longFlagRank_read_word_length_le_machine
                        hrankMem
              | inr hlongMem =>
                  cases (List.mem_iff_getElem?.mp hlongMem) with
                  | intro i hgetList =>
                    have hget :
                        data.longSuperRelativeTable.store.words[i]? =
                          some word := by
                      simpa [Array.getElem?_toList] using hgetList
                    exact data.long_read_words_length_le_machine hget
          | inr hlocalMem =>
              exact data.localTable.read_word_length_le_machine
                data.local_read_words_length_le_machine hlocalMem
      | inr hsparseMem =>
          exact data.sparseDirectory.read_words_length_le_machine hsparseMem
  | inr hbitsMem =>
      exact Nat.le_trans (data.bitWords.word_length_le hbitsMem)
        data.wordSize_le_machine

theorem profile
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      SparseExceptionSelectData
        bits target rankSuperOverhead rankBlockOverhead) :
    data.payload.length <=
        canonicalSparseExceptionSelectOverhead bits.length /\
      SuccinctSpace.LittleOLinear canonicalSparseExceptionSelectOverhead /\
      (forall idx,
        (data.selectCosted idx).cost <= sparseDenseFalseSelectQueryCost) /\
      (forall idx,
        (data.selectCosted idx).erase =
          RMQ.Succinct.select target bits idx) /\
      forall {word : List Bool},
        List.Mem word data.readWords ->
          word.length <=
            SuccinctRankProposal.machineWordBits bits.length := by
  exact
    ⟨data.payload_length_le_canonical,
      canonicalSparseExceptionSelectOverhead_littleO,
      data.selectCosted_cost_le,
      data.selectCosted_exact,
      fun {word} hmem => data.read_word_length_le_machine hmem⟩

def toChargedSelectPositionSource
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      SparseExceptionSelectData
        bits target rankSuperOverhead rankBlockOverhead) :
    ChargedSelectPositionSource target bits
      canonicalSparseExceptionSelectOverhead
      sparseDenseFalseSelectQueryCost :=
  let payloadBits := SparseExceptionSelectData.payload data
  let words := SparseExceptionSelectData.readWords data
  let query := SparseExceptionSelectData.selectCosted data
  let hpayload :
      payloadBits.length <=
        canonicalSparseExceptionSelectOverhead bits.length := by
    simpa [payloadBits] using payload_length_le_canonical data
  { domainSize := bits.length
    payload := payloadBits
    readWords := words
    selectPositionCosted := query
    payload_length_le := hpayload
    overhead_littleO :=
      canonicalSparseExceptionSelectOverhead_littleO
    selectPositionCosted_cost_le := by
      intro idx
      simpa [query] using selectCosted_cost_le data idx
    selectPositionCosted_exact := by
      intro idx
      simpa [query] using selectCosted_exact data idx
    read_word_length_le_machine := by
      intro word hmem
      simpa [words] using read_word_length_le_machine data hmem }

end SparseExceptionSelectData

def sparseExceptionSelectData (bits : List Bool) (target : Bool) :
    SparseExceptionSelectData bits target
      (sparseExceptionEffectiveFlagRankSuperOverhead bits target)
      (sparseExceptionEffectiveFlagRankBlockOverhead bits target) where
  wordSize := wordBits bits.length
  wordSize_pos := wordBits_pos bits.length
  wordSize_le_machine := by
    simp [wordBits]
  superStride := superStride bits.length
  superStride_pos := superStride_pos bits.length
  localStride := localStride bits.length
  localStride_pos := localStride_pos bits.length
  localSlotsPerSuper := localSlotsPerSuper bits.length
  superEntries := superEntries bits target
  longFlagBits := longSuperFlagBits bits target
  longFlagRankSuperOverhead := longFlagRankSuperOverhead bits target
  longFlagRankBlockOverhead := longFlagRankBlockOverhead bits target
  longFlagRankData := longFlagRankData bits target
  longFlagRank_wordSize_le_machine := by
    have hprofile := longFlagRankData_profile bits target
    exact Nat.le_trans hprofile.2.1
      (longFlagRankWordSize_le_machine bits target)
  longFlagRank_superWidth_le_machine := by
    simpa [longFlagRankData] using
      longFlagRankWordSize_le_machine bits target
  longFlagRank_blockWidth_le_machine := by
    simpa [longFlagRankData, longFlagRankBlockWidth] using
      longFlagRankWordSize_le_machine bits target
  longSuperRelativeEntries := longSuperRelativeEntries bits target
  localEntries := localEntries bits target
  superFieldWidth := superFieldWidth bits
  longSuperRelativeWidth := longSuperRelativeWidth bits
  localFieldWidth := localFieldWidth bits
  superTable := superTable bits target
  longSuperRelativeTable := longSuperRelativeTable bits target
  localTable := localTable bits target
  sparseDirectory := sparseExceptionDirectory bits target
  bitWords :=
    SuccinctSpace.BoundedPayloadWordStore.ofChunks
      bits (wordBits_pos bits.length)
  super_read_words_length_le_machine := by
    exact
      (superTable bits target).readWordsLengthLeMachine
        (by simp [superFieldWidth, wordBits])
  long_read_words_length_le_machine := by
    intro i word hget
    rw [(longSuperRelativeTable bits target).read_word_length_of_some hget]
    simp [longSuperRelativeWidth]
  local_read_words_length_le_machine := by
    exact
      (localTable bits target).readWordsLengthLeMachine
        (by
          simpa [localFieldWidth] using
            sparseExceptionRelativeWidth_le_machine bits)
  payload_length_le_overhead := by
    have hsuper := superTable_payload_le_overhead bits target
    have hflags := longSuperFlagBits_length_le_overhead bits target
    have hrank := longFlagRankData_auxPayload_le_overhead bits target
    have hlong := longSuperRelativeTable_payload_le_overhead bits target
    have hlocal := localTable_payload_le_overhead bits target
    have hsparse :=
      (sparseExceptionDirectory bits target).payload_length_le_canonical
    let A := (superTable bits target).payload.length
    let B := (longSuperFlagBits bits target).length
    let C := (longFlagRankData bits target).auxPayload.length
    let D := (longSuperRelativeTable bits target).payload.length
    let E := (localTable bits target).payload.length
    let F := (sparseExceptionDirectory bits target).payload.length
    let OA :=
      SuccinctSpace.logLogCubedSampledDirectoryOverhead 40 bits.length
    let OB :=
      SuccinctSpace.logLogCubedSampledDirectoryOverhead 40 bits.length
    let OC :=
      SuccinctSpace.logLogCubedSampledDirectoryOverhead 192 bits.length + 16
    let OD := longSuperRelativeTableOverhead bits.length
    let OE :=
      SuccinctSpace.logLogCubedSampledDirectoryOverhead 640 bits.length
    let OF := canonicalSparseExceptionDirectoryOverhead bits.length
    have hsum :
        A + B + C + D + E + F <=
          OA + OB + OC + OD + OE + OF := by
      have hA : A <= OA := by simpa [A, OA] using hsuper
      have hB : B <= OB := by simpa [B, OB] using hflags
      have hC : C <= OC := by simpa [C, OC] using hrank
      have hD : D <= OD := by simpa [D, OD] using hlong
      have hE : E <= OE := by simpa [E, OE] using hlocal
      have hF : F <= OF := by simpa [F, OF] using hsparse
      omega
    simpa [A, B, C, D, E, F, OA, OB, OC, OD, OE, OF,
      canonicalSparseExceptionSelectOverhead, List.length_append,
      Nat.add_assoc] using hsum
  super_missing_exact := superEntries_missing_exact bits target
  long_explicit_exact := longExplicit_exact bits target
  local_missing_exact := localEntries_missing_exact bits target
  sparse_compact_exact := sparseCompact_exact bits target
  dense_exact := dense_exact bits target

theorem sparseExceptionSelectData_profile
    (bits : List Bool) (target : Bool) :
    let data := sparseExceptionSelectData bits target
    data.payload.length <=
        canonicalSparseExceptionSelectOverhead bits.length /\
      SuccinctSpace.LittleOLinear canonicalSparseExceptionSelectOverhead /\
      (forall idx,
        (data.selectCosted idx).cost <= sparseDenseFalseSelectQueryCost) /\
      (forall idx,
        (data.selectCosted idx).erase =
          RMQ.Succinct.select target bits idx) /\
      forall {word : List Bool},
        List.Mem word data.readWords ->
          word.length <=
            SuccinctRankProposal.machineWordBits bits.length := by
  intro data
  exact data.profile

def sparseExceptionSelectSource (bits : List Bool) (target : Bool) :
    ChargedSelectPositionSource target bits
      canonicalSparseExceptionSelectOverhead
      sparseDenseFalseSelectQueryCost :=
  (sparseExceptionSelectData bits target).toChargedSelectPositionSource

theorem sparseExceptionSelectSource_profile
    (bits : List Bool) (target : Bool) :
    let source := sparseExceptionSelectSource bits target
    source.payload.length <=
        canonicalSparseExceptionSelectOverhead source.domainSize /\
      SuccinctSpace.LittleOLinear canonicalSparseExceptionSelectOverhead /\
      (forall idx,
        (source.selectPositionCosted idx).cost <=
          sparseDenseFalseSelectQueryCost) /\
      (forall idx,
        (source.selectPositionCosted idx).erase =
          RMQ.Succinct.select target bits idx) /\
      forall {word : List Bool},
        List.Mem word source.readWords ->
          word.length <=
            SuccinctRankProposal.machineWordBits bits.length := by
  intro source
  exact
    ⟨source.payload_length_le, source.overhead_littleO,
      source.selectPositionCosted_cost_le,
      source.selectPositionCosted_exact,
      fun {word} hmem => source.read_word_length_le_machine hmem⟩

/--
Uniform modeled query bound for the public Jacobson/Clark bitvector adapter.

Rank comes from the concrete Jacobson two-level directory (`<= 4` ticks), while
select comes from the sparse/dense Clark source (`<= sparseDenseFalseSelectQueryCost`).
-/
def jacobsonClarkRankSelectQueryCost : Nat :=
  Nat.max 4 sparseDenseFalseSelectQueryCost

/--
Auxiliary payload budget for a plain bitvector rank/select family using
Jacobson rank plus independent Clark select sources for `false` and `true`.

The stored `n` input bits are counted by `RankSelectSpec`; this function counts
only the auxiliary rank/select directories.
-/
def jacobsonClarkRankSelectOverhead (n : Nat) : Nat :=
  SuccinctRankProposal.jacobsonRankOverhead n +
    canonicalSparseExceptionSelectOverhead n +
      canonicalSparseExceptionSelectOverhead n

theorem jacobsonClarkRankSelectOverhead_littleO :
    SuccinctSpace.LittleOLinear jacobsonClarkRankSelectOverhead := by
  simpa [jacobsonClarkRankSelectOverhead] using
    (SuccinctRankProposal.jacobsonRankOverhead_littleO.add
      canonicalSparseExceptionSelectOverhead_littleO).add
        canonicalSparseExceptionSelectOverhead_littleO

/--
Concrete auxiliary payload prefix read by the public adapter: Jacobson rank
metadata followed by the two Clark sparse/dense select payloads.
-/
def jacobsonClarkRankSelectAuxPayload (bits : List Bool) : List Bool :=
  (SuccinctRankProposal.jacobsonRankData bits).auxPayload ++
    (sparseExceptionSelectSource bits false).payload ++
      (sparseExceptionSelectSource bits true).payload

theorem jacobsonClarkRankSelectAuxPayload_length_le
    (bits : List Bool) :
    (jacobsonClarkRankSelectAuxPayload bits).length <=
      jacobsonClarkRankSelectOverhead bits.length := by
  have hrankEq :
      (SuccinctRankProposal.jacobsonRankData bits).auxPayload.length =
        SuccinctRankProposal.jacobsonRankOverhead bits.length := by
    have hprofile := SuccinctRankProposal.jacobsonRankData_profile bits
    simpa [SuccinctRankProposal.jacobsonRankOverhead,
      SuccinctRankProposal.twoLevelRankOverhead] using hprofile.1
  have hfalse :
      (sparseExceptionSelectSource bits false).payload.length <=
        canonicalSparseExceptionSelectOverhead bits.length := by
    have h :=
      (sparseExceptionSelectSource bits false).payload_length_le
    simpa [sparseExceptionSelectSource,
      SparseExceptionSelectData.toChargedSelectPositionSource] using h
  have htrue :
      (sparseExceptionSelectSource bits true).payload.length <=
        canonicalSparseExceptionSelectOverhead bits.length := by
    have h :=
      (sparseExceptionSelectSource bits true).payload_length_le
    simpa [sparseExceptionSelectSource,
      SparseExceptionSelectData.toChargedSelectPositionSource] using h
  simp [jacobsonClarkRankSelectAuxPayload,
    jacobsonClarkRankSelectOverhead, List.length_append]
  omega

/--
Published auxiliary payload padded to the clean `o(n)` overhead expression.
The padding is inert: queries below call the concrete rank/select components,
not a semantic oracle over the padded bits.
-/
def jacobsonClarkRankSelectPaddedAuxPayload
    (bits : List Bool) : List Bool :=
  let payload := jacobsonClarkRankSelectAuxPayload bits
  payload ++
    List.replicate
      (jacobsonClarkRankSelectOverhead bits.length - payload.length) false

@[simp] theorem jacobsonClarkRankSelectPaddedAuxPayload_length
    (bits : List Bool) :
    (jacobsonClarkRankSelectPaddedAuxPayload bits).length =
      jacobsonClarkRankSelectOverhead bits.length := by
  have hle := jacobsonClarkRankSelectAuxPayload_length_le bits
  simp [jacobsonClarkRankSelectPaddedAuxPayload]
  omega

/--
Rank/select directory that combines the concrete Jacobson rank builder with
two concrete generic Clark select sources, one per bit value.
-/
def jacobsonClarkRankSelectDirectory (bits : List Bool) :
    SuccinctSpace.RankSelectDirectory bits
      (jacobsonClarkRankSelectOverhead bits.length)
      jacobsonClarkRankSelectQueryCost where
  Aux := Unit
  buildAux := ()
  encodeAux := fun _ => jacobsonClarkRankSelectPaddedAuxPayload bits
  rankCosted := fun _ target pos =>
    (SuccinctRankProposal.jacobsonRankData bits).rankCosted target pos
  selectCosted := fun _ target occurrence =>
    match target with
    | false =>
        (sparseExceptionSelectSource bits false).selectPositionCosted
          occurrence
    | true =>
        (sparseExceptionSelectSource bits true).selectPositionCosted
          occurrence
  aux_length_eq := by
    exact jacobsonClarkRankSelectPaddedAuxPayload_length bits
  rank_cost_le := by
    intro target pos
    exact Nat.le_trans
      ((SuccinctRankProposal.jacobsonRankData bits).rankCosted_cost_le
        target pos)
      (by
        unfold jacobsonClarkRankSelectQueryCost
        exact Nat.le_max_left 4 sparseDenseFalseSelectQueryCost)
  select_cost_le := by
    intro target occurrence
    cases target
    · let source := sparseExceptionSelectSource bits false
      exact Nat.le_trans
        (source.selectPositionCosted_cost_le occurrence)
        (by
          unfold jacobsonClarkRankSelectQueryCost
          exact Nat.le_max_right 4 sparseDenseFalseSelectQueryCost)
    · let source := sparseExceptionSelectSource bits true
      exact Nat.le_trans
        (source.selectPositionCosted_cost_le occurrence)
        (by
          unfold jacobsonClarkRankSelectQueryCost
          exact Nat.le_max_right 4 sparseDenseFalseSelectQueryCost)
  rank_exact := by
    intro target pos
    exact (SuccinctRankProposal.jacobsonRankData bits).rankCosted_exact
      target pos
  select_exact := by
    intro target occurrence
    cases target
    · exact
        (sparseExceptionSelectSource bits false).selectPositionCosted_exact
          occurrence
    · exact
        (sparseExceptionSelectSource bits true).selectPositionCosted_exact
          occurrence

theorem jacobsonClarkRankSelectDirectory_profile
    (bits : List Bool) :
    let directory := jacobsonClarkRankSelectDirectory bits
    directory.auxPayload.length =
        jacobsonClarkRankSelectOverhead bits.length /\
      (forall target pos,
        (directory.rankQueryCosted target pos).cost <=
            jacobsonClarkRankSelectQueryCost /\
          (directory.rankQueryCosted target pos).erase =
            RMQ.Succinct.rankPrefix target bits pos) /\
      (forall target occurrence,
        (directory.selectQueryCosted target occurrence).cost <=
            jacobsonClarkRankSelectQueryCost /\
          (directory.selectQueryCosted target occurrence).erase =
            RMQ.Succinct.select target bits occurrence) := by
  exact
          ⟨(jacobsonClarkRankSelectDirectory bits).auxPayload_length,
      by
        intro target pos
        let directory := jacobsonClarkRankSelectDirectory bits
        exact
          ⟨directory.rankQueryCosted_cost_le target pos,
            directory.rankQueryCosted_erase target pos⟩,
      by
        intro target occurrence
        let directory := jacobsonClarkRankSelectDirectory bits
        exact
          ⟨directory.selectQueryCosted_cost_le target occurrence,
            directory.selectQueryCosted_erase target occurrence⟩⟩

/--
Full public bitvector rank/select/access directory: stored input bits provide
`access`, Jacobson provides `rank`, and the generic Clark sources provide
`select false` and `select true`.
-/
def jacobsonClarkBitVectorRankSelectDirectory (bits : List Bool) :
    RankSelectSpec.BitVectorRankSelectDirectory bits
      (jacobsonClarkRankSelectOverhead bits.length)
      jacobsonClarkRankSelectQueryCost :=
  RankSelectSpec.BitVectorRankSelectDirectory.ofRankSelectDirectoryWithStoredBits
    (jacobsonClarkRankSelectDirectory bits)
    (by
      unfold jacobsonClarkRankSelectQueryCost
      exact Nat.le_trans (by omega : 1 <= 4)
        (Nat.le_max_left 4 sparseDenseFalseSelectQueryCost))

theorem jacobsonClarkBitVectorRankSelectDirectory_profile
    (bits : List Bool) :
    let directory := jacobsonClarkBitVectorRankSelectDirectory bits
    directory.payload.length =
        bits.length + jacobsonClarkRankSelectOverhead bits.length /\
      (forall i,
        (directory.accessQueryCosted i).cost <=
            jacobsonClarkRankSelectQueryCost /\
          (directory.accessQueryCosted i).erase = bits[i]?) /\
      (forall target pos,
        (directory.rankQueryCosted target pos).cost <=
            jacobsonClarkRankSelectQueryCost /\
          (directory.rankQueryCosted target pos).erase =
            RMQ.Succinct.rankPrefix target bits pos) /\
      (forall target occurrence,
        (directory.selectQueryCosted target occurrence).cost <=
            jacobsonClarkRankSelectQueryCost /\
          (directory.selectQueryCosted target occurrence).erase =
            RMQ.Succinct.select target bits occurrence) := by
  exact (jacobsonClarkBitVectorRankSelectDirectory bits).profile

theorem sparseExceptionSelectSource_rankSelectSpec_adapter_profile
    (bits : List Bool) :
    let directory := jacobsonClarkBitVectorRankSelectDirectory bits
    directory.payload.length =
        bits.length + jacobsonClarkRankSelectOverhead bits.length /\
      (forall i,
        (directory.accessQueryCosted i).cost <=
            jacobsonClarkRankSelectQueryCost /\
          (directory.accessQueryCosted i).erase = bits[i]?) /\
      (forall target pos,
        (directory.rankQueryCosted target pos).cost <=
            jacobsonClarkRankSelectQueryCost /\
          (directory.rankQueryCosted target pos).erase =
            RMQ.Succinct.rankPrefix target bits pos) /\
      (forall target occurrence,
        (directory.selectQueryCosted target occurrence).cost <=
            jacobsonClarkRankSelectQueryCost /\
          (directory.selectQueryCosted target occurrence).erase =
            RMQ.Succinct.select target bits occurrence) := by
  exact jacobsonClarkBitVectorRankSelectDirectory_profile bits

/-- Public plain-bitvector family: `n + o(n)` payload and constant-time queries. -/
def jacobsonClarkRankSelectFamily :
    RankSelectSpec.BitVectorRankSelectFamily
      jacobsonClarkRankSelectOverhead
      jacobsonClarkRankSelectQueryCost where
  directory := jacobsonClarkBitVectorRankSelectDirectory
  overhead_littleO := jacobsonClarkRankSelectOverhead_littleO

theorem jacobsonClarkRankSelectFamily_n_plus_o_constant_query_profile :
    SuccinctSpace.LittleOLinear jacobsonClarkRankSelectOverhead /\
      forall bits : List Bool,
        let directory := jacobsonClarkRankSelectFamily.directory bits
        (directory.payload.length =
          bits.length + jacobsonClarkRankSelectOverhead bits.length) /\
          (forall i,
            (directory.accessQueryCosted i).cost <=
                jacobsonClarkRankSelectQueryCost /\
              (directory.accessQueryCosted i).erase =
                bits[i]?) /\
          (forall target pos,
            (directory.rankQueryCosted target pos).cost <=
                jacobsonClarkRankSelectQueryCost /\
              (directory.rankQueryCosted target pos).erase =
                RMQ.Succinct.rankPrefix target bits pos) /\
          (forall target occurrence,
            (directory.selectQueryCosted target occurrence).cost <=
                jacobsonClarkRankSelectQueryCost /\
              (directory.selectQueryCosted target occurrence).erase =
                RMQ.Succinct.select target bits occurrence) := by
  exact
    jacobsonClarkRankSelectFamily.n_plus_o_constant_query_profile

end RMQ.GenericSelect
