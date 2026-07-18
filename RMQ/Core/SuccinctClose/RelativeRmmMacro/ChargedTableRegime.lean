import RMQ.Core.SuccinctClose.RelativeRmmMacro.ChargedWordChunks
import RMQ.Core.SuccinctClose.RelativeRmmMacro.ChargedFringeTableFacts

/-!
# Chunk-width regime and direct table-space theorems (B4)

B4 provenance-hardening companions to the B2/B3 charged-table route
(matrix rows REQ-B4-04 / REQ-B4-05):

* the 8-chunk coverage cap (`bpWordChunkCount`'s `min _ 8`) is made
  explicit as an ALL-size identity over the route's own scales
  (`machineWordBits m` at chunk width `bpFringeChunkBits m`), two-sided
  (`1 <=` and coverage), with the small-size corners pinned to literal
  numerals - including `m = 0` and `m = 1`, and the array-size corners
  `n = 0` / `n = 1` at the route scale `m = 2 * n`;
* the total new-table bit count (the ACTUAL payload lengths of the stored
  fringe chunk table and select chunk table - the objects the execution
  reads and the public space theorem counts) is bounded by the concrete
  `LittleOLinear` witness chain
  `bpFringeTableOverhead_littleO.add bpChunkSelectTableOverhead_littleO`,
  so the o(n) claim does not rest on the overhead DEFINITIONS alone;
* numeric sanity pins at small sizes (`n = 4 / 16 / 256`): chunk widths,
  table row counts (stored words), entry widths, and total bit counts as
  kernel-checked equations.

`Nat.log2` literals do not reduce under kernel `decide`/`rfl`
(well-founded recursion; B3 M2 ledger).  Every concrete `log2` value below
is pinned by `simp [Nat.log2]` (equation-lemma evaluation), after which the
remaining arithmetic is `decide`-safe.  Only kernel decision procedures are
used, and there is no concrete-record defeq at large shapes.
-/

namespace RMQ

namespace SuccinctClose

open SuccinctSpace

/-! ## Concrete `Nat.log2` pins (kernel-checkable via equation lemmas) -/

theorem bpRegime_log2_one : Nat.log2 1 = 0 := by
  simp [Nat.log2]

theorem bpRegime_log2_two : Nat.log2 2 = 1 := by
  simp [Nat.log2]

theorem bpRegime_log2_eight : Nat.log2 8 = 3 := by
  simp [Nat.log2]

theorem bpRegime_log2_twentyFour : Nat.log2 24 = 4 := by
  simp [Nat.log2]

theorem bpRegime_log2_thirtyTwo : Nat.log2 32 = 5 := by
  simp [Nat.log2]

theorem bpRegime_log2_ninety : Nat.log2 90 = 6 := by
  simp [Nat.log2]

theorem bpRegime_log2_fiveHundredTwelve : Nat.log2 512 = 9 := by
  simp [Nat.log2]

/-! ## Small-size chunk-width and word-width pins -/

theorem bpFringeChunkBits_zero : bpFringeChunkBits 0 = 1 := by
  simp [bpFringeChunkBits]

theorem bpFringeChunkBits_one : bpFringeChunkBits 1 = 1 := by
  simp [bpFringeChunkBits, Nat.log2]

theorem bpFringeChunkBits_two : bpFringeChunkBits 2 = 1 := by
  simp [bpFringeChunkBits, Nat.log2]

theorem bpFringeChunkBits_eight : bpFringeChunkBits 8 = 1 := by
  simp [bpFringeChunkBits, Nat.log2]

theorem bpFringeChunkBits_thirtyTwo : bpFringeChunkBits 32 = 1 := by
  simp [bpFringeChunkBits, Nat.log2]

theorem bpFringeChunkBits_fiveHundredTwelve : bpFringeChunkBits 512 = 2 := by
  simp [bpFringeChunkBits, Nat.log2]

theorem machineWordBits_zero : SuccinctRank.machineWordBits 0 = 1 := by
  simp [SuccinctRank.machineWordBits]

theorem machineWordBits_one : SuccinctRank.machineWordBits 1 = 1 := by
  simp [SuccinctRank.machineWordBits, Nat.log2]

theorem machineWordBits_two : SuccinctRank.machineWordBits 2 = 2 := by
  simp [SuccinctRank.machineWordBits, Nat.log2]

/-! ## The 8-chunk coverage cap as an all-size identity (REQ-B4-04) -/

/--
On the route's own scales the `min _ 8` cap of `bpWordChunkCount` is the
identity at EVERY size: one machine word of `machineWordBits m` bits is
covered by exactly `(machineWordBits m - 1) / bpFringeChunkBits m + 1`
chunks, with no size hypothesis (the `8 * c` geometry bound is proven for
all `m` by `machineWordBits_le_8_mul_bpFringeChunkBits`).
-/
theorem bpWordChunkCount_machineWord_eq (m : Nat) :
    bpWordChunkCount (bpFringeChunkBits m) (SuccinctRank.machineWordBits m) =
      (SuccinctRank.machineWordBits m - 1) / bpFringeChunkBits m + 1 :=
  bpWordChunkCount_eq (bpFringeChunkBits_pos m)
    (machineWordBits_le_8_mul_bpFringeChunkBits m)

/-- Lower side of the two-sided regime bound: at least one chunk is always
visited. -/
theorem one_le_bpWordChunkCount_machineWord (m : Nat) :
    1 <= bpWordChunkCount (bpFringeChunkBits m)
      (SuccinctRank.machineWordBits m) := by
  rw [bpWordChunkCount_machineWord_eq]
  exact Nat.le_add_left 1 _

/-- Upper side of the two-sided regime bound (restated at the route
scales): never more than 8 chunks. -/
theorem bpWordChunkCount_machineWord_le_eight (m : Nat) :
    bpWordChunkCount (bpFringeChunkBits m)
      (SuccinctRank.machineWordBits m) <= 8 :=
  bpWordChunkCount_le_eight _ _

/-- Coverage: the visited chunks cover the whole machine word at every
size. -/
theorem machineWordBits_le_bpWordChunkCount_mul (m : Nat) :
    SuccinctRank.machineWordBits m <=
      bpWordChunkCount (bpFringeChunkBits m)
          (SuccinctRank.machineWordBits m) *
        bpFringeChunkBits m := by
  rw [bpWordChunkCount_machineWord_eq]
  exact bpWordChunkCount_cov (bpFringeChunkBits_pos m)

/-- Corner `m = 0`: the empty BP code still yields exactly one covering
chunk. -/
theorem bpWordChunkCount_machineWord_zero :
    bpWordChunkCount (bpFringeChunkBits 0)
      (SuccinctRank.machineWordBits 0) = 1 := by
  rw [bpWordChunkCount_machineWord_eq, bpFringeChunkBits_zero,
    machineWordBits_zero]

/-- Corner `m = 1`: exactly one covering chunk. -/
theorem bpWordChunkCount_machineWord_one :
    bpWordChunkCount (bpFringeChunkBits 1)
      (SuccinctRank.machineWordBits 1) = 1 := by
  rw [bpWordChunkCount_machineWord_eq, bpFringeChunkBits_one,
    machineWordBits_one]

/-- Array-size corner `n = 0` at the route scale `m = 2 * n = 0`: one
covering chunk. -/
theorem bpWordChunkCount_machineWord_size_zero :
    bpWordChunkCount (bpFringeChunkBits (2 * 0))
      (SuccinctRank.machineWordBits (2 * 0)) = 1 :=
  bpWordChunkCount_machineWord_zero

/-- Array-size corner `n = 1` at the route scale `m = 2 * n = 2`: the
two-bit BP code needs exactly two width-1 chunks. -/
theorem bpWordChunkCount_machineWord_size_one :
    bpWordChunkCount (bpFringeChunkBits (2 * 1))
      (SuccinctRank.machineWordBits (2 * 1)) = 2 := by
  rw [show 2 * 1 = 2 from rfl, bpWordChunkCount_machineWord_eq,
    bpFringeChunkBits_two, machineWordBits_two]

/-! ## Direct o(n) for the ACTUAL stored-table bit counts (REQ-B4-05) -/

/-- The fringe overhead function is EXACTLY the stored fringe chunk table's
payload bit count at the route scale. -/
theorem bpFringeChunkTable_payload_length_overhead (n : Nat) :
    (bpFringeChunkTable (bpFringeChunkBits (2 * n))).payload.length =
      bpFringeTableOverhead n :=
  bpFringeChunkTable_payload_length (bpFringeChunkBits (2 * n))

/-- The select overhead function is EXACTLY the stored select chunk table's
payload bit count at the route scale. -/
theorem bpChunkSelectTable_payload_length_overhead (n : Nat) :
    (bpChunkSelectTable (bpFringeChunkBits (2 * n)) false).payload.length =
      bpChunkSelectTableOverhead n :=
  bpChunkSelectTable_payload_length (bpFringeChunkBits (2 * n)) false

/-- The named `LittleOLinear` witness for the SUM of the two new-table
overhead functions (`LittleOLinear.add` applied to the two concrete
witnesses). -/
theorem bpNewTableOverheadSum_littleO :
    SuccinctSpace.LittleOLinear
      (fun n => bpFringeTableOverhead n + bpChunkSelectTableOverhead n) :=
  bpFringeTableOverhead_littleO.add bpChunkSelectTableOverhead_littleO

/--
Direct o(n) theorem for the total new-table bit count (REQ-B4-05): the sum
of the ACTUAL payload lengths of the stored fringe chunk table and select
chunk table - the same objects the accepted execution reads at segments 21
and 22 and the public space theorem counts - is `LittleOLinear`, via the
concrete witness chain
`bpFringeTableOverhead_littleO.add bpChunkSelectTableOverhead_littleO`
transported along the exact payload-length identities.  The o(n) claim
therefore does not rest on the overhead DEFINITIONS alone.
-/
theorem bpNewTablePayloadBits_littleO :
    SuccinctSpace.LittleOLinear
      (fun n =>
        (bpFringeChunkTable (bpFringeChunkBits (2 * n))).payload.length +
          (bpChunkSelectTable
            (bpFringeChunkBits (2 * n)) false).payload.length) :=
  SuccinctSpace.LittleOLinear.of_le bpNewTableOverheadSum_littleO
    (fun n => by
      rw [bpFringeChunkTable_payload_length_overhead,
        bpChunkSelectTable_payload_length_overhead]
      exact Nat.le_refl _)

/-! ## Numeric sanity pins at small sizes (REQ-B4-05)

Hand-checked values at the route scale `c = bpFringeChunkBits (2 * n)`:

| n   | c | fringe rows | fringe width | fringe bits | select rows | select width | select bits |
|-----|---|-------------|--------------|-------------|-------------|--------------|-------------|
| 4   | 1 | 8           | 5            | 40          | 4           | 2            | 8           |
| 16  | 1 | 8           | 5            | 40          | 4           | 2            | 8           |
| 256 | 2 | 36          | 7            | 252         | 12          | 2            | 24          |

`n = 256` is the first sanity size where the fringe chunk width leaves 1.
-/

theorem bpFringeChunkEntryWidth_at_one : bpFringeChunkEntryWidth 1 = 5 := by
  unfold bpFringeChunkEntryWidth
  rw [show bpFringeChunkEntryBound 1 = 24 by decide, bpRegime_log2_twentyFour]

theorem bpFringeChunkEntryWidth_at_two : bpFringeChunkEntryWidth 2 = 7 := by
  unfold bpFringeChunkEntryWidth
  rw [show bpFringeChunkEntryBound 2 = 90 by decide, bpRegime_log2_ninety]

theorem bpChunkSelectEntryWidth_at_one : bpChunkSelectEntryWidth 1 = 2 := by
  simp [bpChunkSelectEntryWidth, Nat.log2]

theorem bpChunkSelectEntryWidth_at_two : bpChunkSelectEntryWidth 2 = 2 := by
  simp [bpChunkSelectEntryWidth, Nat.log2]

/-- Stored fringe-table words (rows) at `n = 4`. -/
theorem bpFringeChunkRowCount_size_four :
    bpFringeChunkRowCount (bpFringeChunkBits (2 * 4)) = 8 := by
  rw [show 2 * 4 = 8 from rfl, bpFringeChunkBits_eight]
  decide

/-- Stored fringe-table words (rows) at `n = 16`. -/
theorem bpFringeChunkRowCount_size_sixteen :
    bpFringeChunkRowCount (bpFringeChunkBits (2 * 16)) = 8 := by
  rw [show 2 * 16 = 32 from rfl, bpFringeChunkBits_thirtyTwo]
  decide

/-- Stored fringe-table words (rows) at `n = 256`. -/
theorem bpFringeChunkRowCount_size_twoFiftySix :
    bpFringeChunkRowCount (bpFringeChunkBits (2 * 256)) = 36 := by
  rw [show 2 * 256 = 512 from rfl, bpFringeChunkBits_fiveHundredTwelve]
  decide

/-- Stored select-table words (rows) at `n = 4`. -/
theorem bpChunkSelectRowCount_size_four :
    bpChunkSelectRowCount (bpFringeChunkBits (2 * 4)) = 4 := by
  rw [show 2 * 4 = 8 from rfl, bpFringeChunkBits_eight]
  decide

/-- Stored select-table words (rows) at `n = 16`. -/
theorem bpChunkSelectRowCount_size_sixteen :
    bpChunkSelectRowCount (bpFringeChunkBits (2 * 16)) = 4 := by
  rw [show 2 * 16 = 32 from rfl, bpFringeChunkBits_thirtyTwo]
  decide

/-- Stored select-table words (rows) at `n = 256`. -/
theorem bpChunkSelectRowCount_size_twoFiftySix :
    bpChunkSelectRowCount (bpFringeChunkBits (2 * 256)) = 12 := by
  rw [show 2 * 256 = 512 from rfl, bpFringeChunkBits_fiveHundredTwelve]
  decide

/-- Total fringe-table bit count at `n = 4`. -/
theorem bpFringeTableOverhead_size_four : bpFringeTableOverhead 4 = 40 := by
  unfold bpFringeTableOverhead
  rw [show 2 * 4 = 8 from rfl, bpFringeChunkBits_eight,
    bpFringeChunkEntryWidth_at_one]
  decide

/-- Total fringe-table bit count at `n = 16`. -/
theorem bpFringeTableOverhead_size_sixteen :
    bpFringeTableOverhead 16 = 40 := by
  unfold bpFringeTableOverhead
  rw [show 2 * 16 = 32 from rfl, bpFringeChunkBits_thirtyTwo,
    bpFringeChunkEntryWidth_at_one]
  decide

/-- Total fringe-table bit count at `n = 256`. -/
theorem bpFringeTableOverhead_size_twoFiftySix :
    bpFringeTableOverhead 256 = 252 := by
  unfold bpFringeTableOverhead
  rw [show 2 * 256 = 512 from rfl, bpFringeChunkBits_fiveHundredTwelve,
    bpFringeChunkEntryWidth_at_two]
  decide

/-- Total select-table bit count at `n = 4`. -/
theorem bpChunkSelectTableOverhead_size_four :
    bpChunkSelectTableOverhead 4 = 8 := by
  unfold bpChunkSelectTableOverhead
  rw [show 2 * 4 = 8 from rfl, bpFringeChunkBits_eight,
    bpChunkSelectEntryWidth_at_one]
  decide

/-- Total select-table bit count at `n = 16`. -/
theorem bpChunkSelectTableOverhead_size_sixteen :
    bpChunkSelectTableOverhead 16 = 8 := by
  unfold bpChunkSelectTableOverhead
  rw [show 2 * 16 = 32 from rfl, bpFringeChunkBits_thirtyTwo,
    bpChunkSelectEntryWidth_at_one]
  decide

/-- Total select-table bit count at `n = 256`. -/
theorem bpChunkSelectTableOverhead_size_twoFiftySix :
    bpChunkSelectTableOverhead 256 = 24 := by
  unfold bpChunkSelectTableOverhead
  rw [show 2 * 256 = 512 from rfl, bpFringeChunkBits_fiveHundredTwelve,
    bpChunkSelectEntryWidth_at_two]
  decide

/-- The stored-table PAYLOAD bit counts match the same literals (via the
exact payload-length identities), tying the sanity pins to the objects the
execution reads. -/
theorem bpNewTablePayloadBits_size_four :
    (bpFringeChunkTable (bpFringeChunkBits (2 * 4))).payload.length +
        (bpChunkSelectTable
          (bpFringeChunkBits (2 * 4)) false).payload.length = 48 := by
  rw [bpFringeChunkTable_payload_length_overhead,
    bpChunkSelectTable_payload_length_overhead,
    bpFringeTableOverhead_size_four, bpChunkSelectTableOverhead_size_four]

theorem bpNewTablePayloadBits_size_sixteen :
    (bpFringeChunkTable (bpFringeChunkBits (2 * 16))).payload.length +
        (bpChunkSelectTable
          (bpFringeChunkBits (2 * 16)) false).payload.length = 48 := by
  rw [bpFringeChunkTable_payload_length_overhead,
    bpChunkSelectTable_payload_length_overhead,
    bpFringeTableOverhead_size_sixteen, bpChunkSelectTableOverhead_size_sixteen]

theorem bpNewTablePayloadBits_size_twoFiftySix :
    (bpFringeChunkTable (bpFringeChunkBits (2 * 256))).payload.length +
        (bpChunkSelectTable
          (bpFringeChunkBits (2 * 256)) false).payload.length = 276 := by
  rw [bpFringeChunkTable_payload_length_overhead,
    bpChunkSelectTable_payload_length_overhead,
    bpFringeTableOverhead_size_twoFiftySix,
    bpChunkSelectTableOverhead_size_twoFiftySix]

end SuccinctClose

end RMQ
