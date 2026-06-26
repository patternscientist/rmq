import RMQ.Core.GenericSelect.Params
import RMQ.Core.GenericSelect.Primitives

/-!
# Generic select slot/span counting layer

Generic `(bits : List Bool) (target : Bool)` occurrence counts, slot
arithmetic, span classification, and sparse-exception counting lemmas.

Layering note (validated while scoping): the *slot arithmetic* layer
(`localSlotsPerSuper`, `localSlotInSuperOfGlobal`, `localBaseOccurrence`)
depends on the shape only through the strides, so it is a function of the bit
length `n` alone.  Only the *count* (`occurrenceCount`/`superSlotCount`) and
*entry/position* layers read the bits and fix a `target`.
-/

namespace RMQ.GenericSelect

open SuccinctSpace SuccinctRank

/-- Number of `target` occurrences in `bits` (the select domain size). -/
def occurrenceCount (bits : List Bool) (target : Bool) : Nat :=
  RMQ.Succinct.rankPrefix target bits bits.length

/-- Number of super slots: `ceil (occurrenceCount / superStride)`. -/
def superSlotCount (bits : List Bool) (target : Bool) : Nat :=
  selectCeilDiv (occurrenceCount bits target) (superStride bits.length)

/-- Local slots reserved per super interval (a function of `n` alone). -/
def localSlotsPerSuper (n : Nat) : Nat :=
  selectLocalSlotsPerSuper (superStride n) (localStride n)

/-- Total local slots. -/
def localSlotCount (bits : List Bool) (target : Bool) : Nat :=
  superSlotCount bits target * localSlotsPerSuper bits.length

theorem localSlotsPerSuper_pos (n : Nat) : 0 < localSlotsPerSuper n := by
  unfold localSlotsPerSuper selectLocalSlotsPerSuper
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

These lemmas give the target-parametric position arithmetic used by the
sparse-exception select construction. The underlying facts
(`select_index_mono`, `select_exists_of_lt_rankPrefix`,
`select_none_of_rankPrefix_length_le`, `Succinct.select_bounds`) are already
generic over `(bits, target)`.
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

Generic port of the older long-super span-sum lemmas: the sum of
spans of "long" super intervals is bounded by the total bit length, so the
number of long (sparse-exception) supers is `o(n)`.  Bottoms out in
`position_mono` / `select_index_(strict_)mono`; no BP structure. -/

theorem superBaseOccurrence_lt_count
    (bits : List Bool) (target : Bool) {superSlot : Nat}
    (hslot : superSlot < superSlotCount bits target) :
    superBaseOccurrence bits.length superSlot < occurrenceCount bits target := by
  simpa [superSlotCount, superBaseOccurrence] using
    selectCeilDiv_slot_mul_lt
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
      selectCeilDiv_mul_ge_of_pos
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
      simpa [slots, ss, ls, localSlotsPerSuper, selectLocalSlotsPerSuper]
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
      unfold superSlotCount selectCeilDiv
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
      selectCeilDiv_mul_ge_of_pos
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

end RMQ.GenericSelect
