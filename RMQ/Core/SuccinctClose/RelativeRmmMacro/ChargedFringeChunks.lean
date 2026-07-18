import RMQ.Core.SuccinctClose.RelativeRmmMacro.LocalBPDecoder
import RMQ.Core.SuccinctSpace.Tables
import RMQ.Core.GenericSelect.DenseEntryTable

/-!
# Charged chunked endpoint-fringe tables (Option B, B1/B2 core)

Half-word chunk lookup tables for the endpoint-fringe min-excess/argmin
computation, replacing the event-silent per-position scan of
`LocalBPDecoder.lean` by charged `FixedWidthNatTable` reads plus ordinary
arithmetic (the Fischer–Heun / four-Russians shape).

Layer plan:

1. chunk geometry (`bpFringeChunkBits`, the `/8` sub-log scale that reuses the
   proven `RankSelectCompressedSubLog` o(n) slack);
2. chunk spec: offset-encoded prefix-excess statistics of a `c`-bit pattern,
   with truncation-free characterizations (the offset encoding is proven, not
   assumed);
3. one packed lookup table indexed by `(chunkValue, startOff, endOff)` whose
   entry carries `(deltaOffset, rangeMinOffset, rangeArgMin)`;
4. generic scan algebra connecting the accepted per-position fringe scan with
   a chunkwise fold (later sections);
5. the charged chunked fringe evaluator and its equivalence with the accepted
   seeded fringe candidates (later sections).
-/

namespace RMQ

namespace SuccinctClose

open SuccinctSpace

/-! ## Chunk geometry -/

/--
Fringe chunk width over the BP-code length `m`.

The `/8` scale mirrors `RankSelectSpec.fixedWeightSubLogChunkBlockSize`, whose
dense-table budget is already proven `o(n)` with elementary exponential slack.
-/
def bpFringeChunkBits (m : Nat) : Nat :=
  Nat.log2 m / 8 + 1

theorem bpFringeChunkBits_pos (m : Nat) : 0 < bpFringeChunkBits m := by
  unfold bpFringeChunkBits
  omega

/-- The accepted four-word fringe window fits in 32 chunks at every size. -/
theorem four_machineWordBits_le_32_mul_bpFringeChunkBits (m : Nat) :
    4 * SuccinctRank.machineWordBits m <= 32 * bpFringeChunkBits m := by
  unfold SuccinctRank.machineWordBits bpFringeChunkBits
  omega

/-! ## Chunk spec: offset-encoded prefix-excess statistics -/

/-- Canonical `c`-bit pattern of a chunk value. -/
def bpFringeChunkPattern (c v : Nat) : List Bool :=
  SuccinctSpace.natToBitsLE c v

@[simp] theorem bpFringeChunkPattern_length (c v : Nat) :
    (bpFringeChunkPattern c v).length = c := by
  unfold bpFringeChunkPattern
  exact SuccinctSpace.natToBitsLE_length c v

/--
Offset-encoded prefix excess of the chunk pattern at offset `t`: the value
`c + (opens - closes)` of the first `t` pattern bits, kept in `Nat` by the
`+ c` offset.
-/
def bpFringeChunkExcessOffsetAt (c v t : Nat) : Nat :=
  c + Succinct.rankPrefix true (bpFringeChunkPattern c v) t
    - Succinct.rankPrefix false (bpFringeChunkPattern c v) t

/--
The offset encoding is truncation-free: adding back the close count recovers
`c` plus the open count exactly.  This is the proven (not assumed) content of
the signed-excess offset encoding.
-/
theorem bpFringeChunkExcessOffsetAt_add_false (c v t : Nat) :
    bpFringeChunkExcessOffsetAt c v t +
        Succinct.rankPrefix false (bpFringeChunkPattern c v) t =
      c + Succinct.rankPrefix true (bpFringeChunkPattern c v) t := by
  have hfalse :=
    Succinct.rankPrefix_le_length false (bpFringeChunkPattern c v) t
  rw [bpFringeChunkPattern_length] at hfalse
  unfold bpFringeChunkExcessOffsetAt
  omega

theorem bpFringeChunkExcessOffsetAt_le (c v t : Nat) :
    bpFringeChunkExcessOffsetAt c v t <= 2 * c := by
  have htrue :=
    Succinct.rankPrefix_le_length true (bpFringeChunkPattern c v) t
  rw [bpFringeChunkPattern_length] at htrue
  unfold bpFringeChunkExcessOffsetAt
  omega

/-- At offset `0` the offset-encoded excess is exactly the offset `c`. -/
@[simp] theorem bpFringeChunkExcessOffsetAt_zero (c v : Nat) :
    bpFringeChunkExcessOffsetAt c v 0 = c := by
  unfold bpFringeChunkExcessOffsetAt
  simp [Succinct.rankPrefix_zero]

/--
Offset-encoded excess versus the truncated bits-level excess: whenever the
local prefix excess is nonnegative (closes never exceed opens), the offset
encoding is exactly `c` plus `bpExcessAtBits` of the pattern.
-/
theorem bpFringeChunkExcessOffsetAt_eq_add_bpExcessAtBits
    {c v t : Nat}
    (hnonneg :
      Succinct.rankPrefix false (bpFringeChunkPattern c v) t <=
        Succinct.rankPrefix true (bpFringeChunkPattern c v) t) :
    bpFringeChunkExcessOffsetAt c v t =
      c + bpExcessAtBits (bpFringeChunkPattern c v) t := by
  have hchar := bpFringeChunkExcessOffsetAt_add_false c v t
  unfold bpExcessAtBits
  omega

/-! ## Generic leftmost-argmin scan

The same strict-less/keep-left recursion as the accepted
`localBPSeededPrefixRangeArgMinPrefixPosFrom`, over an abstract score
function.  Both the chunk-table entries and (in later sections) the accepted
window scan are instances, so the chunked-fold equivalence becomes generic
scan algebra.
-/

/-- Keep-left better step: switch only on strictly smaller score. -/
def bpFringeScanBetter (f : Nat -> Nat) (best sample : Nat) : Nat :=
  if f sample < f best then sample else best

def bpFringeScanArgMinFrom (f : Nat -> Nat) : Nat -> Nat -> Nat -> Nat
  | _pos, 0, best => best
  | pos, steps + 1, best =>
      bpFringeScanArgMinFrom f (pos + 1) steps (bpFringeScanBetter f best pos)

/-- Leftmost argmin of `f` over `[start, start + count)`; `start` if empty. -/
def bpFringeScanArgMin (f : Nat -> Nat) (start count : Nat) : Nat :=
  match count with
  | 0 => start
  | steps + 1 => bpFringeScanArgMinFrom f (start + 1) steps start

theorem bpFringeScanArgMinFrom_le
    {f : Nat -> Nat} {pos steps best bound : Nat}
    (hbest : best <= bound) (hcov : pos + steps <= bound + 1) :
    bpFringeScanArgMinFrom f pos steps best <= bound := by
  induction steps generalizing pos best with
  | zero =>
      simpa [bpFringeScanArgMinFrom] using hbest
  | succ steps ih =>
      have hpos : pos <= bound := by omega
      have hbetter : bpFringeScanBetter f best pos <= bound := by
        unfold bpFringeScanBetter
        by_cases hlt : f pos < f best
        · simpa [hlt] using hpos
        · simpa [hlt] using hbest
      simpa [bpFringeScanArgMinFrom] using
        ih (pos := pos + 1)
          (best := bpFringeScanBetter f best pos)
          hbetter (by omega)

theorem bpFringeScanArgMinFrom_ge
    {f : Nat -> Nat} {pos steps best lowb : Nat}
    (hbest : lowb <= best) (hpos : lowb <= pos) :
    lowb <= bpFringeScanArgMinFrom f pos steps best := by
  induction steps generalizing pos best with
  | zero =>
      simpa [bpFringeScanArgMinFrom] using hbest
  | succ steps ih =>
      have hbetter : lowb <= bpFringeScanBetter f best pos := by
        unfold bpFringeScanBetter
        by_cases hlt : f pos < f best
        · simpa [hlt] using hpos
        · simpa [hlt] using hbest
      simpa [bpFringeScanArgMinFrom] using
        ih (pos := pos + 1)
          (best := bpFringeScanBetter f best pos)
          hbetter (by omega)

theorem bpFringeScanArgMin_le
    {f : Nat -> Nat} {start count bound : Nat}
    (hstart : start <= bound) (hcov : start + count <= bound + 1) :
    bpFringeScanArgMin f start count <= bound := by
  cases count with
  | zero =>
      simpa [bpFringeScanArgMin] using hstart
  | succ steps =>
      exact bpFringeScanArgMinFrom_le hstart (by omega)

theorem bpFringeScanArgMin_ge
    {f : Nat -> Nat} {start count : Nat} :
    start <= bpFringeScanArgMin f start count := by
  cases count with
  | zero =>
      simp [bpFringeScanArgMin]
  | succ steps =>
      exact bpFringeScanArgMinFrom_ge (Nat.le_refl start) (by omega)

/-! ## Chunk table fields -/

/--
Leftmost argmin of the offset-encoded chunk prefix excess over offsets in
`[a, b)` (returns `a` for an empty range).
-/
def bpFringeChunkArgMin (c v a b : Nat) : Nat :=
  bpFringeScanArgMin (bpFringeChunkExcessOffsetAt c v) a (b - a)

/-- Offset-encoded minimum prefix excess over offsets in `[a, b)`. -/
def bpFringeChunkMinOffset (c v a b : Nat) : Nat :=
  bpFringeChunkExcessOffsetAt c v (bpFringeChunkArgMin c v a b)

/-- Offset-encoded total excess change across the full chunk. -/
def bpFringeChunkDeltaOffset (c v : Nat) : Nat :=
  bpFringeChunkExcessOffsetAt c v c

theorem bpFringeChunkArgMin_le
    (c v : Nat) {a b : Nat} (ha : a <= c) (hb : b <= c) :
    bpFringeChunkArgMin c v a b <= c := by
  unfold bpFringeChunkArgMin
  exact bpFringeScanArgMin_le ha (by omega)

theorem bpFringeChunkArgMin_ge (c v a b : Nat) :
    a <= bpFringeChunkArgMin c v a b := by
  unfold bpFringeChunkArgMin
  exact bpFringeScanArgMin_ge

theorem bpFringeChunkMinOffset_le (c v a b : Nat) :
    bpFringeChunkMinOffset c v a b <= 2 * c := by
  unfold bpFringeChunkMinOffset
  exact bpFringeChunkExcessOffsetAt_le c v _

theorem bpFringeChunkDeltaOffset_le (c v : Nat) :
    bpFringeChunkDeltaOffset c v <= 2 * c := by
  unfold bpFringeChunkDeltaOffset
  exact bpFringeChunkExcessOffsetAt_le c v c

/-! ## Packed entries -/

/--
Packed table entry: `(delta * (2c+2) + rangeMin) * (c+1) + rangeArg`, i.e.
mixed-radix packing with argmin in the lowest digit and the two
offset-encoded excess fields above it.
-/
def bpFringeChunkPacked (c v a b : Nat) : Nat :=
  (bpFringeChunkDeltaOffset c v * (2 * c + 2) +
      bpFringeChunkMinOffset c v a b) * (c + 1) +
    bpFringeChunkArgMin c v a b

theorem bpFringeChunkPacked_arg
    (c v : Nat) {a b : Nat} (ha : a <= c) (hb : b <= c) :
    bpFringeChunkPacked c v a b % (c + 1) = bpFringeChunkArgMin c v a b := by
  have harg := bpFringeChunkArgMin_le c v ha hb
  unfold bpFringeChunkPacked
  rw [Nat.mul_comm
    (bpFringeChunkDeltaOffset c v * (2 * c + 2) +
      bpFringeChunkMinOffset c v a b) (c + 1)]
  rw [Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt (by omega)

theorem bpFringeChunkPacked_div_base (c v a b : Nat)
    (ha : a <= c) (hb : b <= c) :
    bpFringeChunkPacked c v a b / (c + 1) =
      bpFringeChunkDeltaOffset c v * (2 * c + 2) +
        bpFringeChunkMinOffset c v a b := by
  have harg := bpFringeChunkArgMin_le c v ha hb
  unfold bpFringeChunkPacked
  rw [Nat.mul_comm
    (bpFringeChunkDeltaOffset c v * (2 * c + 2) +
      bpFringeChunkMinOffset c v a b) (c + 1)]
  rw [Nat.mul_add_div (by omega)]
  rw [Nat.div_eq_of_lt (by omega)]
  omega

theorem bpFringeChunkPacked_min
    (c v : Nat) {a b : Nat} (ha : a <= c) (hb : b <= c) :
    bpFringeChunkPacked c v a b / (c + 1) % (2 * c + 2) =
      bpFringeChunkMinOffset c v a b := by
  have hmin := bpFringeChunkMinOffset_le c v a b
  rw [bpFringeChunkPacked_div_base c v a b ha hb]
  rw [Nat.mul_comm (bpFringeChunkDeltaOffset c v) (2 * c + 2)]
  rw [Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt (by omega)

theorem bpFringeChunkPacked_delta
    (c v : Nat) {a b : Nat} (ha : a <= c) (hb : b <= c) :
    bpFringeChunkPacked c v a b / ((c + 1) * (2 * c + 2)) =
      bpFringeChunkDeltaOffset c v := by
  have hmin := bpFringeChunkMinOffset_le c v a b
  rw [<- Nat.div_div_eq_div_mul]
  rw [bpFringeChunkPacked_div_base c v a b ha hb]
  rw [Nat.mul_comm (bpFringeChunkDeltaOffset c v) (2 * c + 2)]
  rw [Nat.mul_add_div (by omega)]
  rw [Nat.div_eq_of_lt (by omega)]
  omega

/-- Strict packed-entry bound. -/
def bpFringeChunkEntryBound (c : Nat) : Nat :=
  (2 * c + 1) * ((2 * c + 2) * (c + 1))

theorem bpFringeChunkPacked_lt_entryBound
    (c v : Nat) {a b : Nat} (ha : a <= c) (hb : b <= c) :
    bpFringeChunkPacked c v a b < bpFringeChunkEntryBound c := by
  have hdelta := bpFringeChunkDeltaOffset_le c v
  have hmin := bpFringeChunkMinOffset_le c v a b
  have harg := bpFringeChunkArgMin_le c v ha hb
  have hhead :
      bpFringeChunkDeltaOffset c v * (2 * c + 2) +
          bpFringeChunkMinOffset c v a b + 1 <=
        (2 * c + 1) * (2 * c + 2) := by
    have hmul :
        bpFringeChunkDeltaOffset c v * (2 * c + 2) <=
          (2 * c) * (2 * c + 2) :=
      Nat.mul_le_mul_right (2 * c + 2) hdelta
    have hsucc : (2 * c + 1) * (2 * c + 2) =
        (2 * c) * (2 * c + 2) + (2 * c + 2) :=
      Nat.succ_mul (2 * c) (2 * c + 2)
    omega
  have hstep :
      bpFringeChunkPacked c v a b <
        (bpFringeChunkDeltaOffset c v * (2 * c + 2) +
            bpFringeChunkMinOffset c v a b + 1) * (c + 1) := by
    have hexpand :
        (bpFringeChunkDeltaOffset c v * (2 * c + 2) +
            bpFringeChunkMinOffset c v a b + 1) * (c + 1) =
          (bpFringeChunkDeltaOffset c v * (2 * c + 2) +
            bpFringeChunkMinOffset c v a b) * (c + 1) + (c + 1) :=
      Nat.succ_mul _ (c + 1)
    unfold bpFringeChunkPacked
    omega
  have hmulLe :
      (bpFringeChunkDeltaOffset c v * (2 * c + 2) +
          bpFringeChunkMinOffset c v a b + 1) * (c + 1) <=
        ((2 * c + 1) * (2 * c + 2)) * (c + 1) :=
    Nat.mul_le_mul_right (c + 1) hhead
  have hassoc :
      ((2 * c + 1) * (2 * c + 2)) * (c + 1) = bpFringeChunkEntryBound c := by
    unfold bpFringeChunkEntryBound
    rw [Nat.mul_assoc]
  omega

/-- Fixed entry width: enough bits for every packed entry. -/
def bpFringeChunkEntryWidth (c : Nat) : Nat :=
  Nat.log2 (bpFringeChunkEntryBound c) + 1

theorem bpFringeChunkEntryBound_lt_two_pow_width (c : Nat) :
    bpFringeChunkEntryBound c < 2 ^ bpFringeChunkEntryWidth c := by
  unfold bpFringeChunkEntryWidth
  exact Nat.lt_log2_self

theorem bpFringeChunkPacked_lt_two_pow_width
    (c v : Nat) {a b : Nat} (ha : a <= c) (hb : b <= c) :
    bpFringeChunkPacked c v a b < 2 ^ bpFringeChunkEntryWidth c := by
  exact Nat.lt_trans (bpFringeChunkPacked_lt_entryBound c v ha hb)
    (bpFringeChunkEntryBound_lt_two_pow_width c)

/-! ## Table rows -/

/-- Row index of `(chunkValue v, startOff a, endOff b)`. -/
def bpFringeChunkSlot (c v a b : Nat) : Nat :=
  (v * (c + 1) + a) * (c + 1) + b

def bpFringeChunkRowCount (c : Nat) : Nat :=
  2 ^ c * ((c + 1) * (c + 1))

theorem bpFringeChunkSlot_lt_rowCount
    {c v a b : Nat} (hv : v < 2 ^ c) (ha : a <= c) (hb : b <= c) :
    bpFringeChunkSlot c v a b < bpFringeChunkRowCount c := by
  have hhead : v * (c + 1) + a + 1 <= 2 ^ c * (c + 1) := by
    have hmul : v * (c + 1) + (c + 1) <= 2 ^ c * (c + 1) := by
      have hstep : (v + 1) * (c + 1) <= 2 ^ c * (c + 1) :=
        Nat.mul_le_mul_right (c + 1) hv
      have hexpand : (v + 1) * (c + 1) = v * (c + 1) + (c + 1) :=
        Nat.succ_mul v (c + 1)
      omega
    omega
  have hstep :
      bpFringeChunkSlot c v a b < (v * (c + 1) + a + 1) * (c + 1) := by
    have hexpand :
        (v * (c + 1) + a + 1) * (c + 1) =
          (v * (c + 1) + a) * (c + 1) + (c + 1) :=
      Nat.succ_mul _ (c + 1)
    unfold bpFringeChunkSlot
    omega
  have hmulLe :
      (v * (c + 1) + a + 1) * (c + 1) <= (2 ^ c * (c + 1)) * (c + 1) :=
    Nat.mul_le_mul_right (c + 1) hhead
  have hassoc :
      (2 ^ c * (c + 1)) * (c + 1) = bpFringeChunkRowCount c := by
    unfold bpFringeChunkRowCount
    rw [Nat.mul_assoc]
  omega

theorem bpFringeChunkSlot_div_sq
    {c v a b : Nat} (ha : a <= c) (hb : b <= c) :
    bpFringeChunkSlot c v a b / ((c + 1) * (c + 1)) = v := by
  rw [<- Nat.div_div_eq_div_mul]
  unfold bpFringeChunkSlot
  rw [Nat.mul_comm (v * (c + 1) + a) (c + 1)]
  rw [Nat.mul_add_div (by omega)]
  rw [Nat.div_eq_of_lt (show b < c + 1 by omega), Nat.add_zero]
  rw [Nat.mul_comm v (c + 1)]
  rw [Nat.mul_add_div (by omega)]
  rw [Nat.div_eq_of_lt (show a < c + 1 by omega), Nat.add_zero]

theorem bpFringeChunkSlot_div_mod
    {c v a b : Nat} (ha : a <= c) (hb : b <= c) :
    bpFringeChunkSlot c v a b / (c + 1) % (c + 1) = a := by
  unfold bpFringeChunkSlot
  rw [Nat.mul_comm (v * (c + 1) + a) (c + 1)]
  rw [Nat.mul_add_div (by omega)]
  rw [Nat.div_eq_of_lt (show b < c + 1 by omega), Nat.add_zero]
  rw [Nat.mul_comm v (c + 1)]
  rw [Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt (by omega)

theorem bpFringeChunkSlot_mod
    {c v a b : Nat} (hb : b <= c) :
    bpFringeChunkSlot c v a b % (c + 1) = b := by
  unfold bpFringeChunkSlot
  rw [Nat.mul_comm (v * (c + 1) + a) (c + 1)]
  rw [Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt (by omega)

/-- Reference entry list: one packed entry per decoded row index. -/
def bpFringeChunkEntries (c : Nat) : List Nat :=
  (List.range (bpFringeChunkRowCount c)).map fun slot =>
    bpFringeChunkPacked c (slot / ((c + 1) * (c + 1)))
      (slot / (c + 1) % (c + 1)) (slot % (c + 1))

@[simp] theorem bpFringeChunkEntries_length (c : Nat) :
    (bpFringeChunkEntries c).length = bpFringeChunkRowCount c := by
  unfold bpFringeChunkEntries
  simp

theorem bpFringeChunkEntries_getElem
    {c v a b : Nat} (hv : v < 2 ^ c) (ha : a <= c) (hb : b <= c) :
    (bpFringeChunkEntries c)[bpFringeChunkSlot c v a b]? =
      some (bpFringeChunkPacked c v a b) := by
  have hlt := bpFringeChunkSlot_lt_rowCount hv ha hb
  unfold bpFringeChunkEntries
  rw [List.getElem?_map]
  rw [List.getElem?_range hlt]
  simp [bpFringeChunkSlot_div_sq ha hb, bpFringeChunkSlot_div_mod ha hb,
    bpFringeChunkSlot_mod hb]

theorem bpFringeChunkEntries_mem_lt_two_pow_width
    {c entry : Nat} (hmem : List.Mem entry (bpFringeChunkEntries c)) :
    entry < 2 ^ bpFringeChunkEntryWidth c := by
  unfold bpFringeChunkEntries at hmem
  rcases List.mem_map.mp hmem with ⟨slot, _hslot, rfl⟩
  apply bpFringeChunkPacked_lt_two_pow_width
  · exact Nat.le_of_lt_succ (Nat.mod_lt _ (by omega))
  · exact Nat.le_of_lt_succ (Nat.mod_lt _ (by omega))

/-! ## The counted table -/

/--
The charged fringe chunk table: a payload-live fixed-width table whose stored
words decode to exactly the packed reference entries.
-/
def bpFringeChunkTable (c : Nat) :
    SuccinctSpace.FixedWidthNatTable (bpFringeChunkEntries c)
      (bpFringeChunkEntryWidth c) :=
  SuccinctSpace.FixedWidthNatTable.ofEntries
    (bpFringeChunkEntries c) (bpFringeChunkEntryWidth c)
    (fun hmem => bpFringeChunkEntries_mem_lt_two_pow_width hmem)

/--
Charged-read exactness at a decoded row: one counted store read returns the
packed entry of `(v, a, b)`.
-/
theorem bpFringeChunkTable_readCosted_erase
    {c v a b : Nat} (hv : v < 2 ^ c) (ha : a <= c) (hb : b <= c) :
    ((bpFringeChunkTable c).readCosted
        (bpFringeChunkSlot c v a b)).erase =
      some (bpFringeChunkPacked c v a b) := by
  rw [SuccinctSpace.FixedWidthNatTable.readCosted_erase]
  exact bpFringeChunkEntries_getElem hv ha hb

theorem bpFringeChunkTable_readCosted_cost
    (c i : Nat) :
    ((bpFringeChunkTable c).readCosted i).cost = 1 := by
  simp

/-! ## Window chunk values -/

/-- Chunk value of window chunk `j`: the `c`-bit slice starting at `j * c`. -/
def bpFringeWindowChunkValue (c : Nat) (window : List Bool) (j : Nat) : Nat :=
  SuccinctSpace.bitsToNatLE ((window.drop (j * c)).take c)

theorem bpFringeWindowChunkValue_lt
    (c : Nat) (window : List Bool) (j : Nat) :
    bpFringeWindowChunkValue c window j < 2 ^ c := by
  have hlt :=
    GenericSelect.bitsToNatLE_lt_two_pow_length
      ((window.drop (j * c)).take c)
  have hlen : ((window.drop (j * c)).take c).length <= c := by
    simp [List.length_take]
    omega
  exact Nat.lt_of_lt_of_le hlt
    (Nat.pow_le_pow_right (by omega) hlen)

/-- `natToBitsLE width 0` is the all-`false` pattern. -/
theorem natToBitsLE_zero (width : Nat) :
    SuccinctSpace.natToBitsLE width 0 = List.replicate width false := by
  induction width with
  | zero => rfl
  | succ w ih =>
      simp [SuccinctSpace.natToBitsLE, ih, List.replicate_succ]

/--
Re-encoding a short bit list pads it with `false` on the right: the canonical
pattern of a window slice is the slice followed by padding, so pattern
statistics at offsets `t <= slice.length` never see the padding.
-/
theorem natToBitsLE_bitsToNatLE_append_replicate
    {bits : List Bool} {width : Nat} (hle : bits.length <= width) :
    SuccinctSpace.natToBitsLE width (SuccinctSpace.bitsToNatLE bits) =
      bits ++ List.replicate (width - bits.length) false := by
  induction bits generalizing width with
  | nil =>
      simpa using natToBitsLE_zero width
  | cons bit rest ih =>
      cases width with
      | zero =>
          simp at hle
      | succ w =>
          have hrest : rest.length <= w := by
            simpa using hle
          have hbit : SuccinctSpace.bitToNat bit <= 1 := by
            cases bit <;> simp [SuccinctSpace.bitToNat]
          have hmod :
              (SuccinctSpace.bitToNat bit +
                  2 * SuccinctSpace.bitsToNatLE rest) % 2 =
                SuccinctSpace.bitToNat bit := by
            omega
          have hdiv :
              (SuccinctSpace.bitToNat bit +
                  2 * SuccinctSpace.bitsToNatLE rest) / 2 =
                SuccinctSpace.bitsToNatLE rest := by
            omega
          have hdecide :
              decide ((SuccinctSpace.bitToNat bit +
                  2 * SuccinctSpace.bitsToNatLE rest) % 2 = 1) = bit := by
            rw [hmod]
            cases bit <;> simp [SuccinctSpace.bitToNat]
          show
            decide ((SuccinctSpace.bitToNat bit +
                2 * SuccinctSpace.bitsToNatLE rest) % 2 = 1) ::
              SuccinctSpace.natToBitsLE w
                ((SuccinctSpace.bitToNat bit +
                  2 * SuccinctSpace.bitsToNatLE rest) / 2) =
            (bit :: rest) ++
              List.replicate (w + 1 - (rest.length + 1)) false
          rw [hdecide, hdiv, ih hrest]
          simp [Nat.succ_sub_succ]

/--
Pattern statistics of a window chunk agree with the raw window slice at every
offset inside the slice: padding never corrupts prefix ranks.
-/
theorem bpFringeChunkPattern_windowChunkValue_rankPrefix
    (target : Bool) (c : Nat) (window : List Bool) {j t : Nat}
    (ht : t <= ((window.drop (j * c)).take c).length) :
    Succinct.rankPrefix target
        (bpFringeChunkPattern c (bpFringeWindowChunkValue c window j)) t =
      Succinct.rankPrefix target ((window.drop (j * c)).take c) t := by
  have hlen : ((window.drop (j * c)).take c).length <= c := by
    simp [List.length_take]
    omega
  unfold bpFringeChunkPattern bpFringeWindowChunkValue
  rw [natToBitsLE_bitsToNatLE_append_replicate hlen]
  exact Succinct.rankPrefix_append_of_le target _ _ ht

/-! ## Generic scan algebra -/

/-- Splitting a scan run at an intermediate position. -/
theorem bpFringeScanArgMinFrom_add
    (f : Nat -> Nat) (pos s t best : Nat) :
    bpFringeScanArgMinFrom f pos (s + t) best =
      bpFringeScanArgMinFrom f (pos + s) t
        (bpFringeScanArgMinFrom f pos s best) := by
  induction s generalizing pos best with
  | zero =>
      simp [bpFringeScanArgMinFrom]
  | succ s ih =>
      have hsteps : s + 1 + t = (s + t) + 1 := by omega
      rw [hsteps]
      show
        bpFringeScanArgMinFrom f (pos + 1) (s + t)
            (bpFringeScanBetter f best pos) =
          bpFringeScanArgMinFrom f (pos + (s + 1)) t
            (bpFringeScanArgMinFrom f (pos + 1) s
              (bpFringeScanBetter f best pos))
      rw [ih (pos := pos + 1) (best := bpFringeScanBetter f best pos)]
      have hpos : pos + 1 + s = pos + (s + 1) := by omega
      rw [hpos]

/-- The keep-left better step is associative. -/
theorem bpFringeScanBetter_assoc (f : Nat -> Nat) (x y z : Nat) :
    bpFringeScanBetter f (bpFringeScanBetter f x y) z =
      bpFringeScanBetter f x (bpFringeScanBetter f y z) := by
  by_cases hyx : f y < f x
  · by_cases hzy : f z < f y
    · have hzx : f z < f x := Nat.lt_trans hzy hyx
      simp [bpFringeScanBetter, hyx, hzy, hzx]
    · simp [bpFringeScanBetter, hyx, hzy]
  · by_cases hzy : f z < f y
    · simp [bpFringeScanBetter, hyx, hzy]
    · have hzx : ¬ f z < f x := by omega
      simp [bpFringeScanBetter, hyx, hzy, hzx]

/-- A scan continuation is the better-merge of the seed with the fresh run. -/
theorem bpFringeScanArgMinFrom_eq_better_scanArgMin
    (f : Nat -> Nat) (pos steps best : Nat) :
    bpFringeScanArgMinFrom f pos (steps + 1) best =
      bpFringeScanBetter f best (bpFringeScanArgMin f pos (steps + 1)) := by
  induction steps generalizing pos best with
  | zero =>
      simp [bpFringeScanArgMinFrom, bpFringeScanArgMin]
  | succ steps ih =>
      show
        bpFringeScanArgMinFrom f (pos + 1) (steps + 1)
            (bpFringeScanBetter f best pos) =
          bpFringeScanBetter f best
            (bpFringeScanArgMin f pos (steps + 1 + 1))
      rw [ih (pos := pos + 1) (best := bpFringeScanBetter f best pos)]
      have hrun :
          bpFringeScanArgMin f pos (steps + 1 + 1) =
            bpFringeScanBetter f pos
              (bpFringeScanArgMin f (pos + 1) (steps + 1)) := by
        show
          bpFringeScanArgMinFrom f (pos + 1) (steps + 1) pos =
            bpFringeScanBetter f pos
              (bpFringeScanArgMin f (pos + 1) (steps + 1))
        rw [ih (pos := pos + 1) (best := pos)]
      rw [hrun, bpFringeScanBetter_assoc]

/-- Concatenating two nonempty scan ranges merges their leftmost argmins. -/
theorem bpFringeScanArgMin_append
    (f : Nat -> Nat) (lo n m : Nat) (hn : 0 < n) (hm : 0 < m) :
    bpFringeScanArgMin f lo (n + m) =
      bpFringeScanBetter f (bpFringeScanArgMin f lo n)
        (bpFringeScanArgMin f (lo + n) m) := by
  cases n with
  | zero => omega
  | succ n' =>
      cases m with
      | zero => omega
      | succ m' =>
          have hsum : n' + 1 + (m' + 1) = (n' + (m' + 1)) + 1 := by omega
          rw [hsum]
          show
            bpFringeScanArgMinFrom f (lo + 1) (n' + (m' + 1)) lo =
              bpFringeScanBetter f
                (bpFringeScanArgMin f lo (n' + 1))
                (bpFringeScanArgMin f (lo + (n' + 1)) (m' + 1))
          rw [bpFringeScanArgMinFrom_add f (lo + 1) n' (m' + 1) lo]
          have hpos : lo + 1 + n' = lo + (n' + 1) := by omega
          rw [hpos]
          rw [bpFringeScanArgMinFrom_eq_better_scanArgMin]
          rfl

/--
Affine reindexing: when a score `g` agrees with `f` shifted by `k` positions
up to a common additive normalization (`f (k + t) + cOff = D + g t` on the
scanned domain), the scans agree up to the `k` shift.
-/
theorem bpFringeScanArgMinFrom_affine
    (f g : Nat -> Nat) (k D cOff : Nat) {lowb upb pos steps best : Nat}
    (hval : forall t, lowb <= t -> t < upb -> f (k + t) + cOff = D + g t)
    (hbest : lowb <= best) (hbestUp : best < upb)
    (hpos : lowb <= pos) (hcov : pos + steps <= upb) :
    bpFringeScanArgMinFrom f (k + pos) steps (k + best) =
      k + bpFringeScanArgMinFrom g pos steps best := by
  induction steps generalizing pos best with
  | zero =>
      simp [bpFringeScanArgMinFrom]
  | succ steps ih =>
      have hposUp : pos < upb := by omega
      have hfb := hval best hbest hbestUp
      have hfp := hval pos hpos hposUp
      show
        bpFringeScanArgMinFrom f (k + pos + 1) steps
            (bpFringeScanBetter f (k + best) (k + pos)) =
          k + bpFringeScanArgMinFrom g (pos + 1) steps
            (bpFringeScanBetter g best pos)
      have hshift : k + pos + 1 = k + (pos + 1) := by omega
      by_cases hcmp : g pos < g best
      · have hf : f (k + pos) < f (k + best) := by omega
        have hbl :
            bpFringeScanBetter f (k + best) (k + pos) = k + pos := by
          simp [bpFringeScanBetter, hf]
        have hbr : bpFringeScanBetter g best pos = pos := by
          simp [bpFringeScanBetter, hcmp]
        rw [hbl, hbr, hshift]
        exact ih (pos := pos + 1) (best := pos)
          hpos hposUp (by omega) (by omega)
      · have hf : ¬ f (k + pos) < f (k + best) := by omega
        have hbl :
            bpFringeScanBetter f (k + best) (k + pos) = k + best := by
          simp [bpFringeScanBetter, hf]
        have hbr : bpFringeScanBetter g best pos = best := by
          simp [bpFringeScanBetter, hcmp]
        rw [hbl, hbr, hshift]
        exact ih (pos := pos + 1) (best := best)
          hbest hbestUp (by omega) (by omega)

theorem bpFringeScanArgMin_affine
    (f g : Nat -> Nat) (k D cOff : Nat) {lo count upb : Nat}
    (hval : forall t, lo <= t -> t < upb -> f (k + t) + cOff = D + g t)
    (hcount : 0 < count) (hcov : lo + count <= upb) :
    bpFringeScanArgMin f (k + lo) count =
      k + bpFringeScanArgMin g lo count := by
  cases count with
  | zero => omega
  | succ steps =>
      show
        bpFringeScanArgMinFrom f (k + lo + 1) steps (k + lo) =
          k + bpFringeScanArgMinFrom g (lo + 1) steps lo
      have hshift : k + lo + 1 = k + (lo + 1) := by omega
      rw [hshift]
      exact bpFringeScanArgMinFrom_affine f g k D cOff
        (lowb := lo) (upb := upb)
        hval (Nat.le_refl lo) (by omega) (by omega) (by omega)

/-! ## The accepted scan as a generic scan -/

/-- Relative seeded prefix score along the window. -/
def bpFringeWindowScore (window : List Bool) (seed t : Nat) : Nat :=
  seed + Succinct.rankPrefix true window t -
    Succinct.rankPrefix false window t

/--
Window/seed validity: the threaded seed dominates every prefix close surplus.
At accepted invocations this is exactly nonnegativity of the absolute BP
prefix excess, so it holds on the whole reachable domain.
-/
def BPFringeWindowValid (window : List Bool) (seed : Nat) : Prop :=
  forall t, t <= window.length ->
    Succinct.rankPrefix false window t <=
      seed + Succinct.rankPrefix true window t

theorem bpFringeWindowScore_add_false
    {window : List Bool} {seed : Nat}
    (hvalid : BPFringeWindowValid window seed)
    {t : Nat} (ht : t <= window.length) :
    bpFringeWindowScore window seed t +
        Succinct.rankPrefix false window t =
      seed + Succinct.rankPrefix true window t := by
  have hv := hvalid t ht
  unfold bpFringeWindowScore
  omega

@[simp] theorem bpFringeWindowScore_zero
    (window : List Bool) (seed : Nat) :
    bpFringeWindowScore window seed 0 = seed := by
  unfold bpFringeWindowScore
  simp [Succinct.rankPrefix_zero]

/-- The accepted seeded excess at `base + t` is the relative window score. -/
theorem localBPSeededExcessAt_base_add
    (window : List Bool) (seed base : Nat) {t : Nat}
    (ht : t <= window.length) :
    localBPSeededExcessAt window seed base (base + t) =
      bpFringeWindowScore window seed t := by
  unfold localBPSeededExcessAt bpFringeWindowScore
  have hmin : Nat.min (base + t) (base + window.length) = base + t :=
    Nat.min_eq_left (by omega)
  rw [hmin]
  simp

/-- Clamp-free view of the accepted per-position scan under coverage. -/
theorem localBPSeededPrefixRangeArgMinPrefixPosFrom_eq_scanFrom
    (window : List Bool) (seed base : Nat) {pos steps best : Nat}
    (hcov : pos + steps <= base + window.length + 1) :
    localBPSeededPrefixRangeArgMinPrefixPosFrom window seed base
        pos steps best =
      bpFringeScanArgMinFrom (localBPSeededExcessAt window seed base)
        pos steps best := by
  induction steps generalizing pos best with
  | zero =>
      rfl
  | succ steps ih =>
      have hsample : Nat.min pos (base + window.length) = pos :=
        Nat.min_eq_left (by omega)
      show
        localBPSeededPrefixRangeArgMinPrefixPosFrom window seed base
            (pos + 1) steps
            (localBPSeededBetterPrefixPos window seed base best
              (Nat.min pos (base + window.length))) =
          bpFringeScanArgMinFrom (localBPSeededExcessAt window seed base)
            (pos + 1) steps
            (bpFringeScanBetter (localBPSeededExcessAt window seed base)
              best pos)
      rw [hsample]
      have hbetter :
          localBPSeededBetterPrefixPos window seed base best pos =
            bpFringeScanBetter (localBPSeededExcessAt window seed base)
              best pos := by
        rfl
      rw [hbetter]
      exact ih (by omega)

theorem localBPSeededPrefixRangeArgMinPrefixPos_eq_scanArgMin
    (window : List Bool) (seed base : Nat) {start count : Nat}
    (hstartCov : start <= base + window.length)
    (hcov : start + count <= base + window.length + 1) :
    localBPSeededPrefixRangeArgMinPrefixPos window seed base start count =
      bpFringeScanArgMin (localBPSeededExcessAt window seed base)
        start count := by
  cases count with
  | zero =>
      show Nat.min start (base + window.length) = start
      exact Nat.min_eq_left hstartCov
  | succ steps =>
      show
        localBPSeededPrefixRangeArgMinPrefixPosFrom window seed base
            (start + 1) steps (Nat.min start (base + window.length)) =
          bpFringeScanArgMinFrom (localBPSeededExcessAt window seed base)
            (start + 1) steps start
      have hmin : Nat.min start (base + window.length) = start :=
        Nat.min_eq_left hstartCov
      rw [hmin]
      exact
        localBPSeededPrefixRangeArgMinPrefixPosFrom_eq_scanFrom
          window seed base (by omega)

/-! ## Window-chunk score correspondence -/

/--
Chunk characterization of the window score: inside chunk `j`, the score at
`j * c + t` is the boundary score plus the offset-encoded chunk excess, under
the common `+ c` normalization.  This is the four-Russians decomposition the
charged fold evaluates.
-/
theorem bpFringeWindowScore_chunk_char
    {window : List Bool} {seed : Nat} (c : Nat) {j t : Nat}
    (ht : t <= c) (hcov : j * c + t <= window.length)
    (hvalid : BPFringeWindowValid window seed) :
    bpFringeWindowScore window seed (j * c + t) + c =
      bpFringeWindowScore window seed (j * c) +
        bpFringeChunkExcessOffsetAt c
          (bpFringeWindowChunkValue c window j) t := by
  have hslice_len :
      ((window.drop (j * c)).take c).length =
        Nat.min c (window.length - j * c) := by
    simp [List.length_take, List.length_drop]
  have ht_slice : t <= ((window.drop (j * c)).take c).length := by
    rw [hslice_len]
    exact Nat.le_min.mpr ⟨ht, by omega⟩
  have hpat :
      forall target : Bool,
        Succinct.rankPrefix target
            (bpFringeChunkPattern c (bpFringeWindowChunkValue c window j))
            t =
          Succinct.rankPrefix target window (j * c + t) -
            Succinct.rankPrefix target window (j * c) := by
    intro target
    rw [bpFringeChunkPattern_windowChunkValue_rankPrefix target c window
      ht_slice]
    rw [Succinct.rankPrefix_take_eq_of_le target _ ht_slice]
    have hdrop :=
      Succinct.rankPrefix_drop_eq_sub_of_le target window
        (start := j * c) (limit := j * c + t) (by omega) hcov
    have hsub : j * c + t - (j * c) = t := by omega
    rw [hsub] at hdrop
    exact hdrop
  have hmonoT :
      Succinct.rankPrefix true window (j * c) <=
        Succinct.rankPrefix true window (j * c + t) :=
    Succinct.rankPrefix_mono_limit true window (by omega)
  have hmonoF :
      Succinct.rankPrefix false window (j * c) <=
        Succinct.rankPrefix false window (j * c + t) :=
    Succinct.rankPrefix_mono_limit false window (by omega)
  have hpatT := hpat true
  have hpatF := hpat false
  have hchar :=
    bpFringeChunkExcessOffsetAt_add_false c
      (bpFringeWindowChunkValue c window j) t
  have hscoreT := bpFringeWindowScore_add_false hvalid hcov
  have hscoreJ :=
    bpFringeWindowScore_add_false hvalid
      (show j * c <= window.length by omega)
  omega

/-! ## The silent chunked fold -/

/-- Keep-left merge of optional `(value, position)` candidates. -/
def bpFringeMergeCand :
    Option (Nat × Nat) -> Option (Nat × Nat) -> Option (Nat × Nat)
  | none, cand? => cand?
  | some best, none => some best
  | some best, some cand =>
      if cand.1 < best.1 then some cand else some best

/-- Start offset of the query range inside chunk `j` (capped into `[0, c]`). -/
def bpFringeChunkStartOff (c relLo j : Nat) : Nat :=
  Nat.min c (Nat.max relLo (j * c) - j * c)

/-- End offset (exclusive) of the query range inside chunk `j`. -/
def bpFringeChunkEndOff (c relHi j : Nat) : Nat :=
  Nat.min (relHi + 1) ((j + 1) * c) - j * c

theorem bpFringeChunkStartOff_le (c relLo j : Nat) :
    bpFringeChunkStartOff c relLo j <= c := by
  unfold bpFringeChunkStartOff
  exact Nat.min_le_left _ _

theorem bpFringeChunkEndOff_le (c relHi j : Nat) :
    bpFringeChunkEndOff c relHi j <= c := by
  unfold bpFringeChunkEndOff
  have hminR : Nat.min (relHi + 1) ((j + 1) * c) <= (j + 1) * c :=
    Nat.min_le_right _ _
  have hmul : (j + 1) * c = j * c + c := Nat.succ_mul j c
  omega

/-- The candidate contributed by chunk `j` at accumulator `acc`. -/
def bpFringeChunkCand (c : Nat) (window : List Bool)
    (relLo relHi j acc : Nat) : Option (Nat × Nat) :=
  if bpFringeChunkStartOff c relLo j < bpFringeChunkEndOff c relHi j then
    some
      (acc +
          bpFringeChunkMinOffset c (bpFringeWindowChunkValue c window j)
            (bpFringeChunkStartOff c relLo j)
            (bpFringeChunkEndOff c relHi j) - c,
        j * c +
          bpFringeChunkArgMin c (bpFringeWindowChunkValue c window j)
            (bpFringeChunkStartOff c relLo j)
            (bpFringeChunkEndOff c relHi j))
  else
    none

/-- One silent fold step over chunk `j` (spec-level fields). -/
def bpFringeChunkFoldStep (c : Nat) (window : List Bool)
    (relLo relHi j : Nat) (st : Nat × Option (Nat × Nat)) :
    Nat × Option (Nat × Nat) :=
  (st.1 +
      bpFringeChunkDeltaOffset c (bpFringeWindowChunkValue c window j) - c,
    bpFringeMergeCand st.2
      (bpFringeChunkCand c window relLo relHi j st.1))

def bpFringeChunkFoldFrom (c : Nat) (window : List Bool)
    (relLo relHi : Nat) :
    Nat -> Nat -> (Nat × Option (Nat × Nat)) -> Nat × Option (Nat × Nat)
  | _j, 0, st => st
  | j, count + 1, st =>
      bpFringeChunkFoldFrom c window relLo relHi (j + 1) count
        (bpFringeChunkFoldStep c window relLo relHi j st)

def bpFringeChunkFold (c : Nat) (window : List Bool)
    (seed relLo relHi count : Nat) : Nat × Option (Nat × Nat) :=
  bpFringeChunkFoldFrom c window relLo relHi 0 count (seed, none)

/-- Expected best candidate over relative positions `[relLo, upper)`. -/
def bpFringeExpectedBest
    (window : List Bool) (seed relLo upper : Nat) :
    Option (Nat × Nat) :=
  if upper <= relLo then none
  else
    some
      (bpFringeWindowScore window seed
        (bpFringeScanArgMin (bpFringeWindowScore window seed) relLo
          (upper - relLo)),
        bpFringeScanArgMin (bpFringeWindowScore window seed) relLo
          (upper - relLo))

/-- Division bound: `n < (n / c + 1) * c` for positive `c`. -/
theorem nat_lt_div_succ_mul {n c : Nat} (hc : 0 < c) :
    n < (n / c + 1) * c := by
  have hdm := Nat.div_add_mod n c
  have hmod : n % c < c := Nat.mod_lt _ hc
  have hmul : (n / c + 1) * c = c * (n / c) + c := by
    rw [Nat.succ_mul, Nat.mul_comm]
  generalize hA : c * (n / c) = A at *
  omega

/-- Division bound: `(n / c) * c <= n`. -/
theorem nat_div_mul_le (n c : Nat) : (n / c) * c <= n := by
  have := Nat.div_mul_le_self n c
  omega

/-- End offset in `j * c + c` normal form (linear-arithmetic friendly). -/
theorem bpFringeChunkEndOff_eq (c relHi j : Nat) :
    bpFringeChunkEndOff c relHi j =
      Nat.min (relHi + 1) (j * c + c) - j * c := by
  unfold bpFringeChunkEndOff
  rw [Nat.succ_mul j c]

/--
Merging the running best with the chunk-`j` candidate advances the covered
upper bound by one chunk.  This is the single-chunk core of the fold
invariant, split into intersecting and non-intersecting cases.
-/
theorem bpFringeChunkBestStep
    {window : List Bool} {seed : Nat} (c : Nat) (hc : 0 < c)
    (hvalid : BPFringeWindowValid window seed)
    {relLo relHi j acc : Nat}
    (hlo : relLo <= relHi) (hhi : relHi <= window.length)
    (hjcLe : j * c <= relHi)
    (hacc : acc = bpFringeWindowScore window seed (j * c)) :
    bpFringeMergeCand
        (bpFringeExpectedBest window seed relLo
          (Nat.min (relHi + 1) (j * c)))
        (bpFringeChunkCand c window relLo relHi j acc) =
      bpFringeExpectedBest window seed relLo
        (Nat.min (relHi + 1) (j * c + c)) := by
  have hminN2L : Nat.min (relHi + 1) (j * c + c) <= relHi + 1 :=
    Nat.min_le_left _ _
  have hminN2R : Nat.min (relHi + 1) (j * c + c) <= j * c + c :=
    Nat.min_le_right _ _
  have hminN2G : j * c + 1 <= Nat.min (relHi + 1) (j * c + c) :=
    Nat.le_min.mpr ⟨by omega, by omega⟩
  have hmaxL : relLo <= Nat.max relLo (j * c) := Nat.le_max_left _ _
  have hmaxR : j * c <= Nat.max relLo (j * c) := Nat.le_max_right _ _
  have hminN1 : Nat.min (relHi + 1) (j * c) = j * c :=
    Nat.min_eq_right (by omega)
  by_cases hint :
      Nat.max relLo (j * c) < Nat.min (relHi + 1) (j * c + c)
  · -- Chunk j intersects the query range.
    have haval :
        bpFringeChunkStartOff c relLo j =
          Nat.max relLo (j * c) - j * c := by
      unfold bpFringeChunkStartOff
      exact Nat.min_eq_right (by omega)
    have hbval := bpFringeChunkEndOff_eq c relHi j
    have hab :
        bpFringeChunkStartOff c relLo j <
          bpFringeChunkEndOff c relHi j := by
      rw [haval, hbval]
      omega
    have haLe : bpFringeChunkStartOff c relLo j <= c :=
      bpFringeChunkStartOff_le c relLo j
    have hbLe : bpFringeChunkEndOff c relHi j <= c :=
      bpFringeChunkEndOff_le c relHi j
    have hstartPos :
        j * c + bpFringeChunkStartOff c relLo j =
          Nat.max relLo (j * c) := by
      rw [haval]
      omega
    have hendPos :
        j * c + bpFringeChunkEndOff c relHi j =
          Nat.min (relHi + 1) (j * c + c) := by
      rw [hbval]
      omega
    have hvalRel :
        forall t,
          bpFringeChunkStartOff c relLo j <= t ->
          t < bpFringeChunkEndOff c relHi j ->
            bpFringeWindowScore window seed (j * c + t) + c =
              bpFringeWindowScore window seed (j * c) +
                bpFringeChunkExcessOffsetAt c
                  (bpFringeWindowChunkValue c window j) t := by
      intro t _hta htb
      have ht : t <= c := by omega
      have hcovt : j * c + t <= window.length := by
        have hlt : j * c + t < j * c + bpFringeChunkEndOff c relHi j := by
          omega
        rw [hendPos] at hlt
        omega
      exact bpFringeWindowScore_chunk_char c ht hcovt hvalid
    have hargEq :
        bpFringeScanArgMin (bpFringeWindowScore window seed)
            (j * c + bpFringeChunkStartOff c relLo j)
            (bpFringeChunkEndOff c relHi j -
              bpFringeChunkStartOff c relLo j) =
          j * c +
            bpFringeChunkArgMin c (bpFringeWindowChunkValue c window j)
              (bpFringeChunkStartOff c relLo j)
              (bpFringeChunkEndOff c relHi j) := by
      unfold bpFringeChunkArgMin
      exact
        bpFringeScanArgMin_affine
          (fun t => bpFringeWindowScore window seed t)
          (bpFringeChunkExcessOffsetAt c
            (bpFringeWindowChunkValue c window j))
          (j * c) (bpFringeWindowScore window seed (j * c)) c
          (lo := bpFringeChunkStartOff c relLo j)
          (upb := bpFringeChunkEndOff c relHi j)
          hvalRel (by omega) (by omega)
    have hargGe :
        bpFringeChunkStartOff c relLo j <=
          bpFringeChunkArgMin c (bpFringeWindowChunkValue c window j)
            (bpFringeChunkStartOff c relLo j)
            (bpFringeChunkEndOff c relHi j) :=
      bpFringeChunkArgMin_ge c _ _ _
    have hargLt :
        bpFringeChunkArgMin c (bpFringeWindowChunkValue c window j)
            (bpFringeChunkStartOff c relLo j)
            (bpFringeChunkEndOff c relHi j) <
          bpFringeChunkEndOff c relHi j := by
      unfold bpFringeChunkArgMin
      have hle :=
        bpFringeScanArgMin_le
          (f := bpFringeChunkExcessOffsetAt c
            (bpFringeWindowChunkValue c window j))
          (start := bpFringeChunkStartOff c relLo j)
          (count := bpFringeChunkEndOff c relHi j -
            bpFringeChunkStartOff c relLo j)
          (bound := bpFringeChunkEndOff c relHi j - 1)
          (by omega) (by omega)
      omega
    have hcandVal :
        acc +
            bpFringeChunkMinOffset c
              (bpFringeWindowChunkValue c window j)
              (bpFringeChunkStartOff c relLo j)
              (bpFringeChunkEndOff c relHi j) - c =
          bpFringeWindowScore window seed
            (j * c +
              bpFringeChunkArgMin c
                (bpFringeWindowChunkValue c window j)
                (bpFringeChunkStartOff c relLo j)
                (bpFringeChunkEndOff c relHi j)) := by
      have hv := hvalRel _ hargGe hargLt
      unfold bpFringeChunkMinOffset
      omega
    have hcand :
        bpFringeChunkCand c window relLo relHi j acc =
          some
            (bpFringeWindowScore window seed
                (j * c +
                  bpFringeChunkArgMin c
                    (bpFringeWindowChunkValue c window j)
                    (bpFringeChunkStartOff c relLo j)
                    (bpFringeChunkEndOff c relHi j)),
              j * c +
                bpFringeChunkArgMin c
                  (bpFringeWindowChunkValue c window j)
                  (bpFringeChunkStartOff c relLo j)
                  (bpFringeChunkEndOff c relHi j)) := by
      unfold bpFringeChunkCand
      rw [if_pos hab, hcandVal]
    by_cases hfirst : Nat.min (relHi + 1) (j * c) <= relLo
    · -- First intersecting chunk: previous best is empty.
      have hjcLo : j * c <= relLo := by omega
      have hmaxLo : Nat.max relLo (j * c) = relLo :=
        Nat.max_eq_left hjcLo
      have hprev :
          bpFringeExpectedBest window seed relLo
              (Nat.min (relHi + 1) (j * c)) = none := by
        unfold bpFringeExpectedBest
        rw [if_pos hfirst]
      have hupper : relLo < Nat.min (relHi + 1) (j * c + c) := by
        omega
      have hstartEq : j * c + bpFringeChunkStartOff c relLo j = relLo := by
        rw [hstartPos, hmaxLo]
      have hcountEq :
          Nat.min (relHi + 1) (j * c + c) - relLo =
            bpFringeChunkEndOff c relHi j -
              bpFringeChunkStartOff c relLo j := by
        omega
      have hscanEq :
          bpFringeScanArgMin (bpFringeWindowScore window seed) relLo
              (Nat.min (relHi + 1) (j * c + c) - relLo) =
            j * c +
              bpFringeChunkArgMin c
                (bpFringeWindowChunkValue c window j)
                (bpFringeChunkStartOff c relLo j)
                (bpFringeChunkEndOff c relHi j) := by
        have h1 := hargEq
        rw [hstartEq] at h1
        rw [hcountEq]
        exact h1
      rw [hprev, hcand]
      unfold bpFringeExpectedBest
      rw [if_neg (by omega)]
      unfold bpFringeMergeCand
      rw [hscanEq]
    · -- Continuing: previous best covers `[relLo, j*c)`.
      have hUeq : Nat.min (relHi + 1) (j * c) = j * c := hminN1
      have hLoLt : relLo < j * c := by omega
      have hmaxJc : Nat.max relLo (j * c) = j * c :=
        Nat.max_eq_right (by omega)
      have haZero : bpFringeChunkStartOff c relLo j = 0 := by
        rw [haval, hmaxJc]
        omega
      have hprev :
          bpFringeExpectedBest window seed relLo
              (Nat.min (relHi + 1) (j * c)) =
            some
              (bpFringeWindowScore window seed
                  (bpFringeScanArgMin (bpFringeWindowScore window seed)
                    relLo (j * c - relLo)),
                bpFringeScanArgMin (bpFringeWindowScore window seed)
                  relLo (j * c - relLo)) := by
        unfold bpFringeExpectedBest
        rw [hUeq, if_neg (by omega)]
      have hchunkScan :
          bpFringeScanArgMin (bpFringeWindowScore window seed) (j * c)
              (Nat.min (relHi + 1) (j * c + c) - j * c) =
            j * c +
              bpFringeChunkArgMin c
                (bpFringeWindowChunkValue c window j)
                (bpFringeChunkStartOff c relLo j)
                (bpFringeChunkEndOff c relHi j) := by
        have hb' :
            Nat.min (relHi + 1) (j * c + c) - j * c =
              bpFringeChunkEndOff c relHi j -
                bpFringeChunkStartOff c relLo j := by
          rw [hbval, haZero]
          omega
        have hstart0 :
            j * c + bpFringeChunkStartOff c relLo j = j * c := by
          rw [haZero]
          omega
        have h1 := hargEq
        rw [hstart0] at h1
        rw [hb']
        exact h1
      have hsplit :
          bpFringeScanArgMin (bpFringeWindowScore window seed) relLo
              (Nat.min (relHi + 1) (j * c + c) - relLo) =
            bpFringeScanBetter (bpFringeWindowScore window seed)
              (bpFringeScanArgMin (bpFringeWindowScore window seed)
                relLo (j * c - relLo))
              (bpFringeScanArgMin (bpFringeWindowScore window seed)
                (j * c) (Nat.min (relHi + 1) (j * c + c) - j * c)) := by
        have hsum :
            Nat.min (relHi + 1) (j * c + c) - relLo =
              (j * c - relLo) +
                (Nat.min (relHi + 1) (j * c + c) - j * c) := by
          omega
        rw [hsum]
        have happend :=
          bpFringeScanArgMin_append (bpFringeWindowScore window seed)
            relLo (j * c - relLo)
            (Nat.min (relHi + 1) (j * c + c) - j * c)
            (by omega) (by omega)
        have hlo' : relLo + (j * c - relLo) = j * c := by omega
        rw [hlo'] at happend
        exact happend
      rw [hprev, hcand]
      unfold bpFringeExpectedBest
      rw [if_neg (by omega)]
      rw [hsplit, hchunkScan]
      unfold bpFringeMergeCand bpFringeScanBetter
      by_cases hlt :
          bpFringeWindowScore window seed
              (j * c +
                bpFringeChunkArgMin c
                  (bpFringeWindowChunkValue c window j)
                  (bpFringeChunkStartOff c relLo j)
                  (bpFringeChunkEndOff c relHi j)) <
            bpFringeWindowScore window seed
              (bpFringeScanArgMin (bpFringeWindowScore window seed)
                relLo (j * c - relLo))
      · simp [hlt]
      · simp [hlt]
  · -- Chunk j lies entirely before the query range.
    have hbefore : j * c + c <= relLo := by
      rcases Nat.le_total relLo (j * c) with hcase | hcase
      · exfalso
        have hmaxEq : Nat.max relLo (j * c) = j * c :=
          Nat.max_eq_right hcase
        omega
      · have hmaxEq : Nat.max relLo (j * c) = relLo :=
          Nat.max_eq_left hcase
        rcases Nat.le_total (relHi + 1) (j * c + c) with hmcase | hmcase
        · have hminEq : Nat.min (relHi + 1) (j * c + c) = relHi + 1 :=
            Nat.min_eq_left hmcase
          omega
        · have hminEq : Nat.min (relHi + 1) (j * c + c) = j * c + c :=
            Nat.min_eq_right hmcase
          omega
    have hcandNone :
        bpFringeChunkCand c window relLo relHi j acc = none := by
      unfold bpFringeChunkCand
      rw [if_neg]
      rw [bpFringeChunkEndOff_eq]
      unfold bpFringeChunkStartOff
      have hmaxGe : j * c + c <= Nat.max relLo (j * c) := by
        omega
      have hminC :
          Nat.min c (Nat.max relLo (j * c) - j * c) = c :=
        Nat.min_eq_left (by omega)
      omega
    have hprevNone :
        bpFringeExpectedBest window seed relLo
            (Nat.min (relHi + 1) (j * c)) = none := by
      unfold bpFringeExpectedBest
      rw [if_pos (by omega)]
    have hnextNone :
        bpFringeExpectedBest window seed relLo
            (Nat.min (relHi + 1) (j * c + c)) = none := by
      unfold bpFringeExpectedBest
      rw [if_pos (by omega)]
    rw [hprevNone, hcandNone, hnextNone]
    rfl

/--
Fold invariant: starting at chunk `j` with the boundary score and the best
candidate over the already-covered prefix, the fold finishes with the best
candidate over the whole query range.
-/
theorem bpFringeChunkFoldFrom_snd_invariant
    {window : List Bool} {seed : Nat} (c : Nat)
    (hc : 0 < c)
    (hvalid : BPFringeWindowValid window seed)
    {relLo relHi : Nat}
    (hlo : relLo <= relHi) (hhi : relHi <= window.length)
    {j count : Nat} {acc : Nat}
    (hend : j + count = relHi / c + 1)
    (hacc : j <= relHi / c ->
      acc = bpFringeWindowScore window seed (j * c)) :
    (bpFringeChunkFoldFrom c window relLo relHi j count
        (acc,
          bpFringeExpectedBest window seed relLo
            (Nat.min (relHi + 1) (j * c)))).2 =
      bpFringeExpectedBest window seed relLo (relHi + 1) := by
  induction count generalizing j acc with
  | zero =>
      have hj : j = relHi / c + 1 := by omega
      have hjc : relHi + 1 <= j * c := by
        subst hj
        exact nat_lt_div_succ_mul hc
      have hmin : Nat.min (relHi + 1) (j * c) = relHi + 1 :=
        Nat.min_eq_left hjc
      simp [bpFringeChunkFoldFrom, hmin]
  | succ count ih =>
      have hj : j <= relHi / c := by omega
      have hjcLe : j * c <= relHi := by
        calc j * c <= (relHi / c) * c := Nat.mul_le_mul_right c hj
          _ <= relHi := nat_div_mul_le relHi c
      have haccj := hacc hj
      show
        (bpFringeChunkFoldFrom c window relLo relHi (j + 1) count
            (bpFringeChunkFoldStep c window relLo relHi j
              (acc,
                bpFringeExpectedBest window seed relLo
                  (Nat.min (relHi + 1) (j * c))))).2 =
          bpFringeExpectedBest window seed relLo (relHi + 1)
      have hstep :
          bpFringeChunkFoldStep c window relLo relHi j
              (acc,
                bpFringeExpectedBest window seed relLo
                  (Nat.min (relHi + 1) (j * c))) =
            (acc +
                bpFringeChunkDeltaOffset c
                  (bpFringeWindowChunkValue c window j) - c,
              bpFringeExpectedBest window seed relLo
                (Nat.min (relHi + 1) ((j + 1) * c))) := by
        unfold bpFringeChunkFoldStep
        refine congrArg (Prod.mk _) ?_
        show
          bpFringeMergeCand
              (bpFringeExpectedBest window seed relLo
                (Nat.min (relHi + 1) (j * c)))
              (bpFringeChunkCand c window relLo relHi j acc) =
            bpFringeExpectedBest window seed relLo
              (Nat.min (relHi + 1) ((j + 1) * c))
        rw [Nat.succ_mul j c]
        exact bpFringeChunkBestStep c hc hvalid hlo hhi hjcLe haccj
      rw [hstep]
      apply ih (j := j + 1)
        (acc := acc +
          bpFringeChunkDeltaOffset c
            (bpFringeWindowChunkValue c window j) - c)
        (by omega)
      intro hnext
      have hfull : (j + 1) * c <= window.length := by
        have hmul : (j + 1) * c <= (relHi / c) * c :=
          Nat.mul_le_mul_right c hnext
        have hdivLe := nat_div_mul_le relHi c
        omega
      have hsucc_mul : (j + 1) * c = j * c + c := Nat.succ_mul j c
      have hchar :=
        bpFringeWindowScore_chunk_char (window := window)
          (seed := seed) c (j := j) (t := c)
          (Nat.le_refl c) (by omega) hvalid
      unfold bpFringeChunkDeltaOffset
      rw [haccj, hsucc_mul]
      omega

/--
The silent chunked fold computes the leftmost minimum of the relative window
score over `[relLo, relHi]`, matching the per-position scan.
-/
theorem bpFringeChunkFold_snd_eq
    {window : List Bool} {seed : Nat} (c : Nat) (hc : 0 < c)
    (hvalid : BPFringeWindowValid window seed)
    {relLo relHi : Nat}
    (hlo : relLo <= relHi) (hhi : relHi <= window.length) :
    (bpFringeChunkFold c window seed relLo relHi (relHi / c + 1)).2 =
      some
        (bpFringeWindowScore window seed
            (bpFringeScanArgMin (bpFringeWindowScore window seed) relLo
              (relHi + 1 - relLo)),
          bpFringeScanArgMin (bpFringeWindowScore window seed) relLo
            (relHi + 1 - relLo)) := by
  have hinv :=
    bpFringeChunkFoldFrom_snd_invariant (window := window) (seed := seed)
      c hc hvalid hlo hhi (j := 0) (count := relHi / c + 1) (acc := seed)
      (by omega)
      (fun _ => by simp)
  have hmin0 : Nat.min (relHi + 1) (0 * c) = 0 := by
    simp
  rw [hmin0] at hinv
  have hnone :
      bpFringeExpectedBest window seed relLo 0 = none := by
    unfold bpFringeExpectedBest
    rw [if_pos (by omega)]
  rw [hnone] at hinv
  unfold bpFringeChunkFold
  rw [hinv]
  unfold bpFringeExpectedBest
  rw [if_neg (by omega)]

/--
Bridge to the accepted seeded fringe scan: for every covered invocation the
silent chunked fold returns exactly the accepted
`(minExcess, argMinPrefixPos)` pair (positions global).
-/
theorem bpFringeChunkFold_eq_localBPSeeded
    {window : List Bool} {seed base start count : Nat} (c : Nat)
    (hc : 0 < c)
    (hvalid : BPFringeWindowValid window seed)
    (hcount : 0 < count) (hstart : base <= start)
    (hcov : start + count <= base + window.length + 1) :
    Option.map (fun p : Nat × Nat => (p.1, base + p.2))
        (bpFringeChunkFold c window seed (start - base)
          (start + count - 1 - base)
          ((start + count - 1 - base) / c + 1)).2 =
      some
        (localBPSeededPrefixRangeMinExcess window seed base start count,
          localBPSeededPrefixRangeArgMinPrefixPos window seed base
            start count) := by
  have hlo : start - base <= start + count - 1 - base := by omega
  have hhi : start + count - 1 - base <= window.length := by omega
  have hfold :=
    bpFringeChunkFold_snd_eq c hc hvalid hlo hhi
  have hcount' :
      start + count - 1 - base + 1 - (start - base) = count := by
    omega
  rw [hcount'] at hfold
  -- Transport the relative scan to the accepted global scan.
  have hvalGlob :
      forall t, start - base <= t -> t < start + count - 1 - base + 1 ->
        localBPSeededExcessAt window seed base (base + t) + 0 =
          0 + bpFringeWindowScore window seed t := by
    intro t _ht htUp
    have htLen : t <= window.length := by omega
    rw [localBPSeededExcessAt_base_add window seed base htLen]
    omega
  have haffine :=
    bpFringeScanArgMin_affine
      (localBPSeededExcessAt window seed base)
      (bpFringeWindowScore window seed) base 0 0
      (lo := start - base) (upb := start + count - 1 - base + 1)
      hvalGlob hcount (by omega)
  have hbaseLo : base + (start - base) = start := by omega
  rw [hbaseLo] at haffine
  have hargAccepted :=
    localBPSeededPrefixRangeArgMinPrefixPos_eq_scanArgMin window seed base
      (start := start) (count := count)
      (by omega) hcov
  -- Relative argmin bounds for the score conversion.
  have hrelArgLe :
      bpFringeScanArgMin (bpFringeWindowScore window seed)
          (start - base) count <=
        start + count - 1 - base :=
    bpFringeScanArgMin_le (by omega) (by omega)
  have hrelArgLen :
      bpFringeScanArgMin (bpFringeWindowScore window seed)
          (start - base) count <= window.length := by
    omega
  have hminEq :
      localBPSeededPrefixRangeMinExcess window seed base start count =
        bpFringeWindowScore window seed
          (bpFringeScanArgMin (bpFringeWindowScore window seed)
            (start - base) count) := by
    unfold localBPSeededPrefixRangeMinExcess
    rw [hargAccepted, haffine]
    exact localBPSeededExcessAt_base_add window seed base hrelArgLen
  have hargEq :
      localBPSeededPrefixRangeArgMinPrefixPos window seed base
          start count =
        base +
          bpFringeScanArgMin (bpFringeWindowScore window seed)
            (start - base) count := by
    rw [hargAccepted, haffine]
  rw [hfold, hminEq, hargEq]
  rfl

end SuccinctClose

end RMQ
