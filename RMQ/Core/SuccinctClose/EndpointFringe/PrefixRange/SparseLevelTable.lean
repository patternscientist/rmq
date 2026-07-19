import RMQ.Core.SuccinctClose.EndpointFringe.PrefixRange.SparseArgMin

/-!
# Charged sparse-table level/span table (B7)

The accepted interior execution binds its sparse-table level by
`Nat.log2 count` and its span by `bpSparseLogSpan count = 2 ^ Nat.log2 count`
on a RUNTIME-derived count, emitting no trace events
(`InteriorDirectory.lean:2117`, `:2131`, `SparseArgMin.lean:599`).  Both are
`Theta(log n)` recursions, and the level reaches an accepted read address
through `bpLocalSparseCellSlot` / `bpGlobalSparseCellSlot`, so both are
algorithmic work rather than representation artifacts and must be charged.

This module supplies the charged replacement as ONE GENERIC count-indexed
table, to be instantiated twice: once for local counts (`count <= macroSize`)
and once for global counts (`macroSpanCount <= macroSampleCount`).  Cell `i`
packs BOTH values,

  `bpSparseLogSpan i + domain * Nat.log2 i`,

so the level is recovered by division and the span by remainder: one charged
read plus constant-divisor arithmetic, the same arithmetic the accepted route
already performs on `startBlock`.  Charging the level alone would leave
`bpSparseLogSpan`, a second `Theta(log n)` recursion, silent at the same site.

The domain is `bound + 2` for the relevant count bound.  The `+ 2` (rather
than `+ 1`) keeps `2 <= domain` at degenerate shapes, which the packing bound
needs because `bpSparseLogSpan 0 = 1`.

See DD-20260718-012 (mechanism) and DD-20260718-013 (executed sites, the
tight interior cap, and the two-instantiation sizing).
-/

namespace RMQ

namespace SuccinctClose

open SuccinctSpace

/-- Domain of a charged sparse-level table covering counts up to `bound`. -/
def bpSparseLevelDomain (bound : Nat) : Nat := bound + 2

theorem two_le_bpSparseLevelDomain (bound : Nat) :
    2 <= bpSparseLevelDomain bound := by
  unfold bpSparseLevelDomain
  omega

/-- Every count the route can present is strictly inside the domain. -/
theorem bpSparseLevelDomain_covers {bound count : Nat} (hcount : count <= bound) :
    count < bpSparseLevelDomain bound := by
  unfold bpSparseLevelDomain
  omega

/-- Packed cell: the span in the low part, the level in the high part. -/
def bpSparseLevelCell (domain i : Nat) : Nat :=
  bpSparseLogSpan i + domain * Nat.log2 i

/-! ## The two projections are exact on the reachable domain -/

theorem bpSparseLogSpan_lt_of_lt
    {i domain : Nat} (hdomain : 2 <= domain) (hi : i < domain) :
    bpSparseLogSpan i < domain := by
  rcases Nat.eq_zero_or_pos i with hzero | hpos
  · subst hzero
    have hone : bpSparseLogSpan 0 = 1 := by
      unfold bpSparseLogSpan
      simp
    omega
  · have hle : bpSparseLogSpan i <= i := bpSparseLogSpan_le_self hpos
    omega

theorem log2_lt_of_lt {i domain : Nat} (hi : i < domain) :
    Nat.log2 i < domain := by
  have hle : Nat.log2 i <= i := Nat.log2_le_self i
  omega

/-- THE LEVEL PROJECTION: division recovers exactly `Nat.log2`. -/
theorem bpSparseLevelCell_div
    {i domain : Nat} (hdomain : 2 <= domain) (hi : i < domain) :
    bpSparseLevelCell domain i / domain = Nat.log2 i := by
  have hspan : bpSparseLogSpan i < domain :=
    bpSparseLogSpan_lt_of_lt hdomain hi
  have hpos : 0 < domain := by omega
  unfold bpSparseLevelCell
  rw [Nat.add_mul_div_left _ _ hpos]
  rw [Nat.div_eq_of_lt hspan]
  omega

/-- THE SPAN PROJECTION: remainder recovers exactly `bpSparseLogSpan`. -/
theorem bpSparseLevelCell_mod
    {i domain : Nat} (hdomain : 2 <= domain) (hi : i < domain) :
    bpSparseLevelCell domain i % domain = bpSparseLogSpan i := by
  have hspan : bpSparseLogSpan i < domain :=
    bpSparseLogSpan_lt_of_lt hdomain hi
  unfold bpSparseLevelCell
  rw [Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt hspan

/--
THE TIGHT PACKING BOUND.  The stored level is `Nat.log2 i` with `i < domain`,
so it is bounded by `Nat.log2 domain`, NOT by `domain`.  Bounding the cell by
`domain * domain` (as this module originally did) over-states the level's range
exponentially and makes the stored width roughly twice what the packing needs.
That slack is not free: it pushes the entry past one machine word on reachable
shapes and so would cost a second charged read per level lookup.  See the
width-fit lemmas in `InteriorDirectory.lean`, which are what force this bound
to be the honest one.
-/
theorem bpSparseLevelCell_lt
    {i domain : Nat} (hdomain : 2 <= domain) (hi : i < domain) :
    bpSparseLevelCell domain i < domain * (Nat.log2 domain + 1) := by
  have hspan : bpSparseLogSpan i < domain :=
    bpSparseLogSpan_lt_of_lt hdomain hi
  have hlevel : Nat.log2 i <= Nat.log2 domain := by
    have hmono : SuccinctRank.machineWordBits i <=
        SuccinctRank.machineWordBits domain :=
      SuccinctRank.machineWordBits_mono_le (Nat.le_of_lt hi)
    simpa [SuccinctRank.machineWordBits] using hmono
  have hstep : domain * Nat.log2 i <= domain * Nat.log2 domain :=
    Nat.mul_le_mul_left domain hlevel
  have hexpand : domain * (Nat.log2 domain + 1)
      = domain * Nat.log2 domain + domain := by
    rw [Nat.mul_add, Nat.mul_one]
  unfold bpSparseLevelCell
  omega

/-! ## The counted table -/

/-- Reference entries of a charged sparse-level table. -/
def bpSparseLevelEntries (domain : Nat) : List Nat :=
  (List.range domain).map (bpSparseLevelCell domain)

theorem bpSparseLevelEntries_length (domain : Nat) :
    (bpSparseLevelEntries domain).length = domain := by
  unfold bpSparseLevelEntries
  simp

theorem bpSparseLevelEntries_getElem?
    {domain i : Nat} (hi : i < domain) :
    (bpSparseLevelEntries domain)[i]? = some (bpSparseLevelCell domain i) := by
  unfold bpSparseLevelEntries
  rw [List.getElem?_map, List.getElem?_range hi]
  rfl

/--
Stored width: exactly enough for every packed cell, against the TIGHT packing
bound `bpSparseLevelCell_lt`.  Widening this to `Nat.log2 (domain * domain) + 1`
still types, but costs a second machine word per read on reachable shapes.
-/
def bpSparseLevelWidth (domain : Nat) : Nat :=
  Nat.log2 (domain * (Nat.log2 domain + 1)) + 1

theorem bpSparseLevelEntries_lt_two_pow
    {domain entry : Nat} (hdomain : 2 <= domain)
    (hmem : List.Mem entry (bpSparseLevelEntries domain)) :
    entry < 2 ^ bpSparseLevelWidth domain := by
  unfold bpSparseLevelEntries at hmem
  rcases List.mem_map.mp hmem with ⟨i, hi, rfl⟩
  have hilt : i < domain := List.mem_range.mp hi
  have hcell := bpSparseLevelCell_lt hdomain hilt
  have hpow : domain * (Nat.log2 domain + 1)
      < 2 ^ bpSparseLevelWidth domain := by
    unfold bpSparseLevelWidth
    exact Nat.lt_log2_self
  omega

/-- Payload-live charged sparse-level table. -/
structure PayloadLiveBPSparseLevelTable (domain overhead : Nat) where
  table : FixedWidthNatTable (bpSparseLevelEntries domain)
    (bpSparseLevelWidth domain)
  payload_length_eq : table.payload.length = overhead

namespace PayloadLiveBPSparseLevelTable

def payload {domain overhead : Nat}
    (levelTable : PayloadLiveBPSparseLevelTable domain overhead) : List Bool :=
  levelTable.table.payload

theorem payload_length {domain overhead : Nat}
    (levelTable : PayloadLiveBPSparseLevelTable domain overhead) :
    levelTable.payload.length = overhead :=
  levelTable.payload_length_eq

/-- The single charged read: one packed cell carrying level and span. -/
def readCellCosted {domain overhead : Nat}
    (levelTable : PayloadLiveBPSparseLevelTable domain overhead)
    (count : Nat) : Costed (Option Nat) :=
  levelTable.table.readCosted count

theorem readCellCosted_cost {domain overhead : Nat}
    (levelTable : PayloadLiveBPSparseLevelTable domain overhead)
    (count : Nat) : (levelTable.readCellCosted count).cost = 1 := by
  unfold readCellCosted
  simp

theorem readCellCosted_cost_le_one {domain overhead : Nat}
    (levelTable : PayloadLiveBPSparseLevelTable domain overhead)
    (count : Nat) : (levelTable.readCellCosted count).cost <= 1 := by
  rw [levelTable.readCellCosted_cost count]
  omega

theorem readCellCosted_erase {domain overhead count : Nat}
    (levelTable : PayloadLiveBPSparseLevelTable domain overhead)
    (hcount : count < domain) :
    (levelTable.readCellCosted count).erase =
      some (bpSparseLevelCell domain count) := by
  unfold readCellCosted
  rw [FixedWidthNatTable.readCosted_erase]
  exact bpSparseLevelEntries_getElem? hcount

/-! ### The charged values agree with the accepted silent computation -/

/-- THE LEVEL EQUIVALENCE: the charged read's level is `Nat.log2 count`. -/
theorem readCellCosted_erase_div {domain overhead count : Nat}
    (levelTable : PayloadLiveBPSparseLevelTable domain overhead)
    (hdomain : 2 <= domain) (hcount : count < domain) :
    ((levelTable.readCellCosted count).erase).map (fun cell => cell / domain) =
      some (Nat.log2 count) := by
  rw [levelTable.readCellCosted_erase hcount]
  simp [bpSparseLevelCell_div hdomain hcount]

/-- THE SPAN EQUIVALENCE: the same charged read carries `bpSparseLogSpan`. -/
theorem readCellCosted_erase_mod {domain overhead count : Nat}
    (levelTable : PayloadLiveBPSparseLevelTable domain overhead)
    (hdomain : 2 <= domain) (hcount : count < domain) :
    ((levelTable.readCellCosted count).erase).map (fun cell => cell % domain) =
      some (bpSparseLogSpan count) := by
  rw [levelTable.readCellCosted_erase hcount]
  simp [bpSparseLevelCell_mod hdomain hcount]

end PayloadLiveBPSparseLevelTable

/-! ## Size accounting -/

/-- Counted size of a charged sparse-level table, in bits. -/
def bpSparseLevelTableOverhead (domain : Nat) : Nat :=
  domain * bpSparseLevelWidth domain

theorem bpSparseLevelTable_payload_length {domain : Nat}
    (table : FixedWidthNatTable (bpSparseLevelEntries domain)
      (bpSparseLevelWidth domain)) :
    table.payload.length = bpSparseLevelTableOverhead domain := by
  rw [table.payload_length, bpSparseLevelEntries_length]
  unfold bpSparseLevelTableOverhead
  rfl

/-- The canonical construction of the table from its reference entries. -/
def bpSparseLevelTable (bound : Nat) :
    PayloadLiveBPSparseLevelTable (bpSparseLevelDomain bound)
      (bpSparseLevelTableOverhead (bpSparseLevelDomain bound)) where
  table :=
    FixedWidthNatTable.ofEntries (bpSparseLevelEntries (bpSparseLevelDomain bound))
      (bpSparseLevelWidth (bpSparseLevelDomain bound))
      (bpSparseLevelEntries_lt_two_pow (two_le_bpSparseLevelDomain bound))
  payload_length_eq := bpSparseLevelTable_payload_length _

end SuccinctClose

end RMQ
