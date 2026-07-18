import RMQ.Core.SuccinctClose.RelativeRmmMacro.ChargedFringeChunks
import RMQ.Core.SuccinctSpace.Asymptotics
import RMQ.Core.GenericSelect.SelectFacts

/-!
# Charged chunked in-word rank/select (B3 core)

The accepted route's remaining `wordRank`/`wordSelect` emissions all reduce
to two in-word primitives: `RMQ.RAM.boolRankPrefix` (rank of `target` bits
below an offset inside one machine word) and `RMQ.RAM.boolSelectInWord`
(position of the k-th `target` bit inside one machine word).  This module
recharges both as chunk-table reads plus silent bounded arithmetic:

* in-word rank reuses B2's `(v, a, b)` fringe chunk table: the entry at slot
  `(v, t, t)` has empty-range min field
  `bpFringeChunkExcessOffsetAt c v t = c + rankTrue(t) - rankFalse(t)`, and
  with `rankTrue(t) + rankFalse(t) = t` both in-chunk prefix ranks decode
  from one existing-table read (no new rank table, no new counted bits);
* in-word select adds ONE new table `bpChunkSelectTable c target` (rows
  `2^c * (c+1)`, slot `v * (c+1) + k`, entry = position of the k-th
  `target` bit of the c-bit pattern of `v`, sentinel `c` when absent); the
  fold locates the containing chunk by decoded slice popcounts and
  finishes with exactly one select-table read.

Both evaluators visit at most 8 chunks because one machine word fits in 8
fringe chunks at every size (`machineWordBits_le_8_mul_bpFringeChunkBits`),
mirroring B2's 32-chunk window cap; the caps are proven identities on the
reachable domain, so the read counts are all-size literals with no guards.
-/

namespace RMQ

namespace SuccinctClose

open SuccinctSpace

/-! ## Word geometry: one machine word is at most 8 fringe chunks -/

theorem machineWordBits_le_8_mul_bpFringeChunkBits (m : Nat) :
    SuccinctRank.machineWordBits m <= 8 * bpFringeChunkBits m := by
  unfold SuccinctRank.machineWordBits bpFringeChunkBits
  omega

/-! ## In-chunk rank decode from the existing `(v, a, b)` table -/

/-- Counting both targets over any prefix fills the prefix exactly. -/
theorem bpRankPrefix_true_add_false (bits : List Bool) (limit : Nat) :
    Succinct.rankPrefix true bits limit +
        Succinct.rankPrefix false bits limit =
      Nat.min limit bits.length := by
  induction bits generalizing limit with
  | nil =>
      rw [Succinct.rankPrefix_nil, Succinct.rankPrefix_nil]
      have hmin : Nat.min limit ([] : List Bool).length = 0 :=
        Nat.min_zero limit
      omega
  | cons bit rest ih =>
      cases limit with
      | zero =>
          rw [Succinct.rankPrefix_zero, Succinct.rankPrefix_zero]
          have hmin : Nat.min 0 (bit :: rest).length = 0 :=
            Nat.min_eq_left (Nat.zero_le _)
          omega
      | succ limit =>
          have hrec := ih limit
          have hT :
              Succinct.rankPrefix true (bit :: rest) (limit + 1) =
                (if bit = true then 1 else 0) +
                  Succinct.rankPrefix true rest limit := rfl
          have hF :
              Succinct.rankPrefix false (bit :: rest) (limit + 1) =
                (if bit = false then 1 else 0) +
                  Succinct.rankPrefix false rest limit := rfl
          have hlen : (bit :: rest).length = rest.length + 1 := rfl
          have hmin :
              Nat.min (limit + 1) (rest.length + 1) =
                Nat.min limit rest.length + 1 :=
            Nat.succ_min_succ limit rest.length
          rw [hT, hF, hlen, hmin]
          cases bit with
          | false =>
              have h1 : (if (false = true) then (1 : Nat) else 0) = 0 := rfl
              have h2 : (if (false = false) then (1 : Nat) else 0) = 1 := rfl
              rw [h1, h2]
              omega
          | true =>
              have h1 : (if (true = true) then (1 : Nat) else 0) = 1 := rfl
              have h2 : (if (true = false) then (1 : Nat) else 0) = 0 := rfl
              rw [h1, h2]
              omega

/--
The min field of an empty `[t, t)` range is the offset-encoded prefix
excess at `t` itself: the empty-range argmin is the range start.
-/
theorem bpFringeChunkMinOffset_self (c v t : Nat) :
    bpFringeChunkMinOffset c v t t = bpFringeChunkExcessOffsetAt c v t := by
  unfold bpFringeChunkMinOffset bpFringeChunkArgMin
  rw [Nat.sub_self]
  rfl

/--
Silent in-chunk rank decode: from a raw packed entry, recover the number of
`target` bits among the first `t` pattern bits via the min field.
-/
def bpChunkRankOfEntry (c : Nat) (target : Bool) (t entry : Nat) : Nat :=
  cond target ((entry / (c + 1) % (2 * c + 2) + t - c) / 2)
    (t - (entry / (c + 1) % (2 * c + 2) + t - c) / 2)

/--
Decode exactness on honest entries: the decoded value is the in-chunk
prefix rank of `target` at offset `t`, for both targets, truncation-free.
-/
theorem bpChunkRankOfEntry_packed
    (c : Nat) (target : Bool) {v t : Nat} (_hv : v < 2 ^ c) (ht : t <= c) :
    bpChunkRankOfEntry c target t (bpFringeChunkPacked c v t t) =
      Succinct.rankPrefix target (bpFringeChunkPattern c v) t := by
  have hmin := bpFringeChunkPacked_min c v (a := t) (b := t) ht ht
  have hself := bpFringeChunkMinOffset_self c v t
  have hchar := bpFringeChunkExcessOffsetAt_add_false c v t
  have hsum := bpRankPrefix_true_add_false (bpFringeChunkPattern c v) t
  rw [bpFringeChunkPattern_length] at hsum
  have hminTC : Nat.min t c = t := Nat.min_eq_left ht
  rw [hminTC] at hsum
  unfold bpChunkRankOfEntry
  rw [hmin, hself]
  cases target with
  | true =>
      show (bpFringeChunkExcessOffsetAt c v t + t - c) / 2 = _
      omega
  | false =>
      show t - (bpFringeChunkExcessOffsetAt c v t + t - c) / 2 = _
      omega

/-! ## Word chunk slices under an effective limit -/

/-- `boolRankPrefix` never counts past the word end. -/
def bpWordRankEffLimit (word : List Bool) (limit : Nat) : Nat :=
  Nat.min limit word.length

/-- Length of the part of chunk `j` below the effective limit `e`. -/
def bpWordChunkSliceLen (c e j : Nat) : Nat :=
  Nat.min c (e - j * c)

theorem bpWordChunkSliceLen_le (c e j : Nat) :
    bpWordChunkSliceLen c e j <= c :=
  Nat.min_le_left _ _

/-- Number of chunks the folds visit: covers `[0, e)`, capped by 8. -/
def bpWordChunkCount (c e : Nat) : Nat :=
  Nat.min ((e - 1) / c + 1) 8

theorem bpWordChunkCount_le_eight (c e : Nat) :
    bpWordChunkCount c e <= 8 :=
  Nat.min_le_right _ _

/-- The cap is the identity whenever `e` fits in 8 chunks. -/
theorem bpWordChunkCount_eq {c e : Nat} (hc : 0 < c) (he : e <= 8 * c) :
    bpWordChunkCount c e = (e - 1) / c + 1 := by
  have hdiv : (e - 1) / c < 8 := by
    rw [Nat.div_lt_iff_lt_mul hc]
    omega
  unfold bpWordChunkCount
  exact Nat.min_eq_left (by omega)

/-- The uncapped chunk count covers the effective limit. -/
theorem bpWordChunkCount_cov {c e : Nat} (hc : 0 < c) :
    e <= ((e - 1) / c + 1) * c := by
  have hlt := nat_lt_div_succ_mul (n := e - 1) hc
  omega

/--
Chunk-step rank identity: the in-chunk prefix rank of the chunk-`j` slice
under effective limit `e` is the difference of clamped word prefix ranks at
consecutive chunk boundaries.  Padding of short slices is never decoded as
data.
-/
theorem bpWordChunkRank_step
    (c : Nat) (target : Bool) (word : List Bool) {e : Nat}
    (he : e <= word.length) (j : Nat) :
    Succinct.rankPrefix target
        (bpFringeChunkPattern c (bpFringeWindowChunkValue c word j))
        (bpWordChunkSliceLen c e j) =
      Succinct.rankPrefix target word (Nat.min ((j + 1) * c) e) -
        Succinct.rankPrefix target word (Nat.min (j * c) e) := by
  have hexp : (j + 1) * c = j * c + c := Nat.succ_mul j c
  by_cases hje : e <= j * c
  · have ht0 : bpWordChunkSliceLen c e j = 0 := by
      unfold bpWordChunkSliceLen
      rw [Nat.sub_eq_zero_of_le hje]
      exact Nat.min_zero c
    have hminJ : Nat.min (j * c) e = e := Nat.min_eq_right hje
    have hminJ1 : Nat.min ((j + 1) * c) e = e :=
      Nat.min_eq_right (by omega)
    rw [ht0, hminJ, hminJ1, Succinct.rankPrefix_zero]
    omega
  · have hlt : j * c < e := Nat.lt_of_not_ge hje
    have hminJ : Nat.min (j * c) e = j * c :=
      Nat.min_eq_left (Nat.le_of_lt hlt)
    have htc : bpWordChunkSliceLen c e j <= c := Nat.min_le_left _ _
    have hte : bpWordChunkSliceLen c e j <= e - j * c :=
      Nat.min_le_right _ _
    have hsliceLen :
        ((word.drop (j * c)).take c).length =
          Nat.min c (word.length - j * c) := by
      simp [List.length_take, List.length_drop]
    have htSlice :
        bpWordChunkSliceLen c e j <=
          ((word.drop (j * c)).take c).length := by
      rw [hsliceLen]
      exact Nat.le_min.mpr ⟨htc, by omega⟩
    have hpattern :=
      bpFringeChunkPattern_windowChunkValue_rankPrefix target c word
        (j := j) (t := bpWordChunkSliceLen c e j) htSlice
    have htake :
        Succinct.rankPrefix target ((word.drop (j * c)).take c)
            (bpWordChunkSliceLen c e j) =
          Succinct.rankPrefix target (word.drop (j * c))
            (bpWordChunkSliceLen c e j) :=
      Succinct.rankPrefix_take_eq_of_le target (word.drop (j * c)) htSlice
    have hjt : j * c + bpWordChunkSliceLen c e j <= word.length := by
      omega
    have hdrop :=
      Succinct.rankPrefix_drop_eq_sub_of_le target word
        (start := j * c) (limit := j * c + bpWordChunkSliceLen c e j)
        (Nat.le_add_right _ _) hjt
    have hsub :
        j * c + bpWordChunkSliceLen c e j - j * c =
          bpWordChunkSliceLen c e j := by
      omega
    rw [hsub] at hdrop
    have hminJ1 :
        Nat.min ((j + 1) * c) e = j * c + bpWordChunkSliceLen c e j := by
      rcases Nat.le_total c (e - j * c) with hcase | hcase
      · have ht : bpWordChunkSliceLen c e j = c := by
          unfold bpWordChunkSliceLen
          exact Nat.min_eq_left hcase
        have hle : (j + 1) * c <= e := by omega
        have hminE : Nat.min ((j + 1) * c) e = (j + 1) * c :=
          Nat.min_eq_left hle
        rw [hminE, hexp, ht]
      · have ht : bpWordChunkSliceLen c e j = e - j * c := by
          unfold bpWordChunkSliceLen
          exact Nat.min_eq_right hcase
        have hle : e <= (j + 1) * c := by omega
        have hminE : Nat.min ((j + 1) * c) e = e :=
          Nat.min_eq_right hle
        rw [hminE, ht]
        omega
    rw [hpattern, htake, hdrop, hminJ, hminJ1]

/-! ## The charged in-word rank fold -/

/-- One rank fold step from a raw table read: decode and accumulate. -/
def bpWordRankStepDecoded (c : Nat) (target : Bool) (t acc : Nat)
    (entry? : Option Nat) : Nat :=
  acc + bpChunkRankOfEntry c target t (entry?.getD 0)

/--
The charged in-word rank fold: one counted read of the `(v_j, t_j, t_j)`
slot per visited chunk, generic over the supplied table so store corruption
is expressible.
-/
def bpChunkedWordRankCostedFrom {entries : List Nat} {width : Nat}
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (c : Nat) (target : Bool) (word : List Bool) (e : Nat) :
    Nat -> Nat -> Nat -> Costed Nat
  | _j, 0, acc => Costed.pure acc
  | j, count + 1, acc =>
      Costed.bind
        (table.readCosted
          (bpFringeChunkSlot c (bpFringeWindowChunkValue c word j)
            (bpWordChunkSliceLen c e j) (bpWordChunkSliceLen c e j)))
        (fun entry? =>
          bpChunkedWordRankCostedFrom table c target word e (j + 1) count
            (bpWordRankStepDecoded c target (bpWordChunkSliceLen c e j)
              acc entry?))

/-- Charged in-word rank of `target` below `limit` in one word. -/
def bpChunkedWordRankCosted {entries : List Nat} {width : Nat}
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (c : Nat) (target : Bool) (word : List Bool) (limit : Nat) :
    Costed Nat :=
  bpChunkedWordRankCostedFrom table c target word
    (bpWordRankEffLimit word limit) 0
    (bpWordChunkCount c (bpWordRankEffLimit word limit)) 0

/-- Exactly one charged read per visited chunk. -/
theorem bpChunkedWordRankCostedFrom_cost
    {entries : List Nat} {width : Nat}
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (c : Nat) (target : Bool) (word : List Bool) (e : Nat) :
    forall (count j acc : Nat),
      (bpChunkedWordRankCostedFrom table c target word e j count
          acc).cost = count := by
  intro count
  induction count with
  | zero =>
      intro j acc
      simp [bpChunkedWordRankCostedFrom, Costed.pure]
  | succ count ih =>
      intro j acc
      simp [bpChunkedWordRankCostedFrom, Costed.bind, ih]
      omega

/-- All-size literal read bound for the charged in-word rank. -/
theorem bpChunkedWordRankCosted_cost_le
    {entries : List Nat} {width : Nat}
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (c : Nat) (target : Bool) (word : List Bool) (limit : Nat) :
    (bpChunkedWordRankCosted table c target word limit).cost <= 8 := by
  unfold bpChunkedWordRankCosted
  rw [bpChunkedWordRankCostedFrom_cost]
  exact bpWordChunkCount_le_eight _ _

/--
Fold invariant against the honest table: the fold accumulates exactly the
clamped word prefix-rank difference across the chunks it visits.
-/
theorem bpChunkedWordRankCostedFrom_value
    (c : Nat) (target : Bool) (word : List Bool) {e : Nat}
    (he : e <= word.length) :
    forall (count j acc : Nat), e <= (j + count) * c ->
      (bpChunkedWordRankCostedFrom (bpFringeChunkTable c) c target word e
          j count acc).value =
        acc +
          (Succinct.rankPrefix target word e -
            Succinct.rankPrefix target word (Nat.min (j * c) e)) := by
  intro count
  induction count with
  | zero =>
      intro j acc hcov
      have hje : e <= j * c := by
        have hzero : (j + 0) * c = j * c := by rw [Nat.add_zero]
        omega
      have hmin : Nat.min (j * c) e = e := Nat.min_eq_right hje
      show acc = acc + _
      rw [hmin]
      omega
  | succ count ih =>
      intro j acc hcov
      have hv := bpFringeWindowChunkValue_lt c word j
      have ht := bpWordChunkSliceLen_le c e j
      have hread :
          ((bpFringeChunkTable c).readCosted
              (bpFringeChunkSlot c (bpFringeWindowChunkValue c word j)
                (bpWordChunkSliceLen c e j)
                (bpWordChunkSliceLen c e j))).value =
            some
              (bpFringeChunkPacked c (bpFringeWindowChunkValue c word j)
                (bpWordChunkSliceLen c e j)
                (bpWordChunkSliceLen c e j)) :=
        bpFringeChunkTable_readCosted_erase hv ht ht
      show
        (bpChunkedWordRankCostedFrom (bpFringeChunkTable c) c target word
            e (j + 1) count
            (bpWordRankStepDecoded c target (bpWordChunkSliceLen c e j)
              acc
              ((bpFringeChunkTable c).readCosted
                (bpFringeChunkSlot c (bpFringeWindowChunkValue c word j)
                  (bpWordChunkSliceLen c e j)
                  (bpWordChunkSliceLen c e j))).value)).value = _
      rw [hread]
      have hstep :
          bpWordRankStepDecoded c target (bpWordChunkSliceLen c e j) acc
              (some
                (bpFringeChunkPacked c
                  (bpFringeWindowChunkValue c word j)
                  (bpWordChunkSliceLen c e j)
                  (bpWordChunkSliceLen c e j))) =
            acc +
              (Succinct.rankPrefix target word
                  (Nat.min ((j + 1) * c) e) -
                Succinct.rankPrefix target word (Nat.min (j * c) e)) := by
        unfold bpWordRankStepDecoded
        rw [Option.getD_some]
        rw [bpChunkRankOfEntry_packed c target hv ht]
        rw [bpWordChunkRank_step c target word he j]
      rw [hstep]
      have hcov' : e <= (j + 1 + count) * c := by
        have hidx : j + 1 + count = j + (count + 1) := by omega
        rw [hidx]
        exact hcov
      rw [ih (j + 1) _ hcov']
      have hexp : (j + 1) * c = j * c + c := Nat.succ_mul j c
      have hjj1 : j * c <= (j + 1) * c := by omega
      have hm1 : Nat.min (j * c) e <= Nat.min ((j + 1) * c) e :=
        Nat.le_min.mpr
          ⟨Nat.le_trans (Nat.min_le_left _ _) hjj1, Nat.min_le_right _ _⟩
      have hm2 : Nat.min ((j + 1) * c) e <= e := Nat.min_le_right _ _
      have hr1 := Succinct.rankPrefix_mono_limit target word hm1
      have hr2 := Succinct.rankPrefix_mono_limit target word hm2
      omega

/--
Universal in-word rank equivalence: against the honest chunk table, the
charged chunked in-word rank computes exactly `RMQ.RAM.boolRankPrefix`, for
every target, word, and limit, whenever the word fits in 8 chunks — the
hypothesis every accepted call site discharges from its own word-size
fields.
-/
theorem bpChunkedWordRankCosted_value
    (c : Nat) (hc : 0 < c) (target : Bool) (word : List Bool)
    (limit : Nat) (hlen : word.length <= 8 * c) :
    (bpChunkedWordRankCosted (bpFringeChunkTable c) c target word
        limit).value =
      RMQ.RAM.boolRankPrefix target word limit := by
  have heLen : bpWordRankEffLimit word limit <= word.length :=
    Nat.min_le_right _ _
  have hcount :
      bpWordChunkCount c (bpWordRankEffLimit word limit) =
        (bpWordRankEffLimit word limit - 1) / c + 1 :=
    bpWordChunkCount_eq hc (by omega)
  have hcov :
      bpWordRankEffLimit word limit <=
        (0 + ((bpWordRankEffLimit word limit - 1) / c + 1)) * c := by
    rw [Nat.zero_add]
    exact bpWordChunkCount_cov hc
  unfold bpChunkedWordRankCosted
  rw [hcount]
  rw [bpChunkedWordRankCostedFrom_value c target word heLen _ 0 0 hcov]
  have hmin0 : Nat.min (0 * c) (bpWordRankEffLimit word limit) = 0 := by
    rw [Nat.zero_mul]
    exact Nat.min_eq_left (Nat.zero_le _)
  rw [hmin0, Succinct.rankPrefix_zero]
  have hlim :
      Succinct.rankPrefix target word (bpWordRankEffLimit word limit) =
        Succinct.rankPrefix target word limit := by
    unfold bpWordRankEffLimit
    exact Succinct.rankPrefix_min_length_eq target word limit
  rw [hlim, Succinct.ram_boolRankPrefix_eq_rankPrefix]
  omega

/-! ## The select chunk table -/

/--
Position of the k-th `target` bit in the c-bit pattern of `v`; sentinel `c`
when the pattern has at most `k` such bits.  On the honest charged route
the sentinel is unreachable: the fold only reads slot `(v, k)` when `k` is
below the pattern's slice popcount.
-/
def bpChunkSelectPos (c : Nat) (target : Bool) (v k : Nat) : Nat :=
  (Succinct.select target (bpFringeChunkPattern c v) k).getD c

theorem bpChunkSelectPos_le (c : Nat) (target : Bool) (v k : Nat) :
    bpChunkSelectPos c target v k <= c := by
  unfold bpChunkSelectPos
  cases hsel : Succinct.select target (bpFringeChunkPattern c v) k with
  | none =>
      simp
  | some pos =>
      have hbound := Succinct.select_bounds hsel
      rw [bpFringeChunkPattern_length] at hbound
      simp
      omega

/-- Row index of `(chunkValue v, occurrence k)`. -/
def bpChunkSelectSlot (c v k : Nat) : Nat :=
  v * (c + 1) + k

def bpChunkSelectRowCount (c : Nat) : Nat :=
  2 ^ c * (c + 1)

theorem bpChunkSelectSlot_lt_rowCount
    {c v k : Nat} (hv : v < 2 ^ c) (hk : k <= c) :
    bpChunkSelectSlot c v k < bpChunkSelectRowCount c := by
  have hmul : (v + 1) * (c + 1) <= 2 ^ c * (c + 1) :=
    Nat.mul_le_mul_right (c + 1) hv
  have hexpand : (v + 1) * (c + 1) = v * (c + 1) + (c + 1) :=
    Nat.succ_mul v (c + 1)
  unfold bpChunkSelectSlot bpChunkSelectRowCount
  omega

theorem bpChunkSelectSlot_div
    {c v k : Nat} (hk : k <= c) :
    bpChunkSelectSlot c v k / (c + 1) = v := by
  unfold bpChunkSelectSlot
  rw [Nat.mul_comm v (c + 1)]
  rw [Nat.mul_add_div (by omega)]
  rw [Nat.div_eq_of_lt (show k < c + 1 by omega), Nat.add_zero]

theorem bpChunkSelectSlot_mod
    {c v k : Nat} (hk : k <= c) :
    bpChunkSelectSlot c v k % (c + 1) = k := by
  unfold bpChunkSelectSlot
  rw [Nat.mul_comm v (c + 1)]
  rw [Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt (by omega)

/-- Reference entry list: one select position per decoded row index. -/
def bpChunkSelectEntries (c : Nat) (target : Bool) : List Nat :=
  (List.range (bpChunkSelectRowCount c)).map fun slot =>
    bpChunkSelectPos c target (slot / (c + 1)) (slot % (c + 1))

@[simp] theorem bpChunkSelectEntries_length (c : Nat) (target : Bool) :
    (bpChunkSelectEntries c target).length = bpChunkSelectRowCount c := by
  unfold bpChunkSelectEntries
  simp

theorem bpChunkSelectEntries_getElem
    {c : Nat} (target : Bool) {v k : Nat}
    (hv : v < 2 ^ c) (hk : k <= c) :
    (bpChunkSelectEntries c target)[bpChunkSelectSlot c v k]? =
      some (bpChunkSelectPos c target v k) := by
  have hlt := bpChunkSelectSlot_lt_rowCount hv hk
  unfold bpChunkSelectEntries
  rw [List.getElem?_map]
  rw [List.getElem?_range hlt]
  simp [bpChunkSelectSlot_div hk, bpChunkSelectSlot_mod hk]

/-- Fixed entry width: enough bits for every position and the sentinel. -/
def bpChunkSelectEntryWidth (c : Nat) : Nat :=
  Nat.log2 (c + 1) + 1

theorem bpChunkSelectEntries_mem_lt_two_pow_width
    {c : Nat} {target : Bool} {entry : Nat}
    (hmem : List.Mem entry (bpChunkSelectEntries c target)) :
    entry < 2 ^ bpChunkSelectEntryWidth c := by
  have hself : c + 1 < 2 ^ (Nat.log2 (c + 1) + 1) := Nat.lt_log2_self
  unfold bpChunkSelectEntries at hmem
  rcases List.mem_map.mp hmem with ⟨slot, _hslot, rfl⟩
  have hle := bpChunkSelectPos_le c target (slot / (c + 1)) (slot % (c + 1))
  unfold bpChunkSelectEntryWidth
  omega

/--
The charged select chunk table: a payload-live fixed-width table whose
stored words decode to exactly the reference select positions.
-/
def bpChunkSelectTable (c : Nat) (target : Bool) :
    SuccinctSpace.FixedWidthNatTable (bpChunkSelectEntries c target)
      (bpChunkSelectEntryWidth c) :=
  SuccinctSpace.FixedWidthNatTable.ofEntries
    (bpChunkSelectEntries c target) (bpChunkSelectEntryWidth c)
    (fun hmem => bpChunkSelectEntries_mem_lt_two_pow_width hmem)

/-- Charged-read exactness at a decoded row. -/
theorem bpChunkSelectTable_readCosted_erase
    {c : Nat} (target : Bool) {v k : Nat}
    (hv : v < 2 ^ c) (hk : k <= c) :
    ((bpChunkSelectTable c target).readCosted
        (bpChunkSelectSlot c v k)).erase =
      some (bpChunkSelectPos c target v k) := by
  rw [SuccinctSpace.FixedWidthNatTable.readCosted_erase]
  exact bpChunkSelectEntries_getElem target hv hk

/-! ## Select chunk table: size/width/erasure/o(n) facts -/

/-- Counted table payload identity: rows times fixed width. -/
theorem bpChunkSelectTable_payload_length (c : Nat) (target : Bool) :
    (bpChunkSelectTable c target).payload.length =
      bpChunkSelectRowCount c * bpChunkSelectEntryWidth c := by
  have h := (bpChunkSelectTable c target).payload_length
  rw [bpChunkSelectEntries_length] at h
  exact h

/-- Component-level exact physical erasure of the table store. -/
theorem bpChunkSelectTable_store_erases (c : Nat) (target : Bool) :
    SuccinctSpace.flattenPayloadWords
        (bpChunkSelectTable c target).store.words.toList =
      (bpChunkSelectTable c target).payload :=
  (bpChunkSelectTable c target).store.payload_eq_words_join

/-- Every stored table word has exactly the entry width. -/
theorem bpChunkSelectTable_word_length
    {c : Nat} {target : Bool} {i : Nat} {word : List Bool}
    (hword : (bpChunkSelectTable c target).store.words[i]? = some word) :
    word.length = bpChunkSelectEntryWidth c :=
  (bpChunkSelectTable c target).word_length_of_get? hword

/-- The select entry width is at most `c + 2` bits. -/
theorem bpChunkSelectEntryWidth_le (c : Nat) :
    bpChunkSelectEntryWidth c <= c + 2 := by
  have hpow : c + 1 <= 2 ^ (c + 1) := SuccinctSpace.nat_le_two_pow (c + 1)
  have hlog : Nat.log2 (c + 1) <= c + 1 := by
    rcases Nat.lt_or_ge (c + 1) (Nat.log2 (c + 1)) with hlt | hge
    · exfalso
      have hge2 : c + 2 <= Nat.log2 (c + 1) := by omega
      have hp : 2 ^ (c + 2) <= 2 ^ Nat.log2 (c + 1) :=
        Nat.pow_le_pow_right (by omega) hge2
      have hself : 2 ^ Nat.log2 (c + 1) <= c + 1 :=
        Nat.log2_self_le (by omega)
      have hsucc : 2 ^ (c + 2) = 2 * 2 ^ (c + 1) := by
        rw [Nat.pow_succ, Nat.mul_comm]
      have hposPow : 0 < 2 ^ (c + 1) := Nat.pow_pos (by omega)
      omega
    · exact hge
  unfold bpChunkSelectEntryWidth
  omega

/-- Row-count bound: `2^c (c+1) <= 2^(2c+1)`. -/
theorem bpChunkSelectRowCount_le_two_pow (c : Nat) :
    bpChunkSelectRowCount c <= 2 ^ (2 * c + 1) := by
  have h1 : c + 1 <= 2 ^ (c + 1) := SuccinctSpace.nat_le_two_pow (c + 1)
  unfold bpChunkSelectRowCount
  calc
    2 ^ c * (c + 1) <= 2 ^ c * 2 ^ (c + 1) :=
      Nat.mul_le_mul_left (2 ^ c) h1
    _ = 2 ^ (2 * c + 1) := by
      rw [<- Nat.pow_add]
      congr 1
      omega

/--
Per-source capacity feed: the select table stores one word per row, and
the row count is bounded by `16 * (n + 1)` at every size.
-/
theorem bpChunkSelectRowCount_le_linear (n : Nat) :
    bpChunkSelectRowCount (bpFringeChunkBits (2 * n)) <= 16 * (n + 1) := by
  have hrows :=
    bpChunkSelectRowCount_le_two_pow (bpFringeChunkBits (2 * n))
  have hc : bpFringeChunkBits (2 * n) = Nat.log2 (2 * n) / 8 + 1 := rfl
  have h28 : 2 * (Nat.log2 (2 * n) / 8) <= Nat.log2 (2 * n) := by omega
  have hsplit :
      2 ^ (2 * bpFringeChunkBits (2 * n) + 1) =
        8 * 2 ^ (2 * (Nat.log2 (2 * n) / 8)) := by
    rw [hc]
    rw [show 2 * (Nat.log2 (2 * n) / 8 + 1) + 1 =
      2 * (Nat.log2 (2 * n) / 8) + 3 by omega]
    rw [Nat.pow_add]
    omega
  have hmono :
      2 ^ (2 * (Nat.log2 (2 * n) / 8)) <= 2 ^ Nat.log2 (2 * n) :=
    Nat.pow_le_pow_right (by omega) h28
  cases n with
  | zero =>
      have hle := hrows
      rw [hsplit] at hle
      have hlog0 : Nat.log2 0 = 0 := by simp
      simp only [Nat.mul_zero] at hle ⊢
      rw [hlog0] at hle
      simp at hle
      omega
  | succ m =>
      have hpow2n : 2 ^ Nat.log2 (2 * (m + 1)) <= 2 * (m + 1) :=
        Nat.log2_self_le (by omega)
      have hle := hrows
      rw [hsplit] at hle
      have hstep :
          8 * 2 ^ (2 * (Nat.log2 (2 * (m + 1)) / 8)) <=
            8 * (2 * (m + 1)) := by
        have := Nat.le_trans hmono hpow2n
        omega
      omega

/-- Select-table bit budget over the public input size. -/
def bpChunkSelectTableOverhead (n : Nat) : Nat :=
  bpChunkSelectRowCount (bpFringeChunkBits (2 * n)) *
    bpChunkSelectEntryWidth (bpFringeChunkBits (2 * n))

/-- The select-table budget is `o(n)`. -/
theorem bpChunkSelectTableOverhead_littleO :
    SuccinctSpace.LittleOLinear bpChunkSelectTableOverhead := by
  intro scale hscale
  refine ⟨2 ^ (16 * scale + 80), ?_⟩
  intro n hn
  have hpos : 0 < 2 ^ (16 * scale + 80) := Nat.pow_pos (by omega)
  have hn1 : 1 <= n := Nat.le_trans hpos hn
  have hlogbig : 16 * scale + 80 <= Nat.log2 n := by
    rcases Nat.lt_or_ge (Nat.log2 n) (16 * scale + 80) with hlt | hge
    · exfalso
      have h2 : 2 ^ (Nat.log2 n + 1) <= 2 ^ (16 * scale + 80) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have h3 : n < 2 ^ (Nat.log2 n + 1) := Nat.lt_log2_self
      exact Nat.lt_irrefl n (Nat.lt_of_lt_of_le h3 (Nat.le_trans h2 hn))
    · exact hge
  have hcle :
      bpFringeChunkBits (2 * n) <= Nat.log2 n / 8 + 2 := by
    have hlt2n : 2 * n < 2 ^ (Nat.log2 n + 2) := by
      have h3 : n < 2 ^ (Nat.log2 n + 1) := Nat.lt_log2_self
      have hdouble : 2 ^ (Nat.log2 n + 2) = 2 * 2 ^ (Nat.log2 n + 1) := by
        rw [Nat.pow_succ, Nat.mul_comm]
      omega
    have hlog2n : Nat.log2 (2 * n) <= Nat.log2 n + 1 := by
      rcases Nat.lt_or_ge (Nat.log2 n + 1) (Nat.log2 (2 * n)) with hlt | hge
      · exfalso
        have hp : 2 ^ (Nat.log2 n + 2) <= 2 ^ Nat.log2 (2 * n) :=
          Nat.pow_le_pow_right (by omega) (by omega)
        have hself : 2 ^ Nat.log2 (2 * n) <= 2 * n :=
          Nat.log2_self_le (by omega)
        omega
      · exact hge
    unfold bpFringeChunkBits
    omega
  have hwidth :=
    bpChunkSelectEntryWidth_le (bpFringeChunkBits (2 * n))
  have hwidthPow :
      bpFringeChunkBits (2 * n) + 2 <=
        2 ^ (bpFringeChunkBits (2 * n) + 2) :=
    SuccinctSpace.nat_le_two_pow _
  have hrows :=
    bpChunkSelectRowCount_le_two_pow (bpFringeChunkBits (2 * n))
  have hT :
      bpChunkSelectTableOverhead n <=
        2 ^ (3 * bpFringeChunkBits (2 * n) + 3) := by
    unfold bpChunkSelectTableOverhead
    calc
      bpChunkSelectRowCount (bpFringeChunkBits (2 * n)) *
          bpChunkSelectEntryWidth (bpFringeChunkBits (2 * n)) <=
        2 ^ (2 * bpFringeChunkBits (2 * n) + 1) *
          2 ^ (bpFringeChunkBits (2 * n) + 2) :=
        Nat.mul_le_mul hrows (by omega)
      _ = 2 ^ (3 * bpFringeChunkBits (2 * n) + 3) := by
        rw [<- Nat.pow_add]
        congr 1
        omega
  have hscalePow : scale <= 2 ^ scale := SuccinctSpace.nat_le_two_pow scale
  have hexp :
      scale + (3 * bpFringeChunkBits (2 * n) + 3) <= Nat.log2 n := by
    have hq : 3 * (Nat.log2 n / 8) <= Nat.log2 n - Nat.log2 n / 4 := by
      omega
    omega
  have hchain :
      scale * bpChunkSelectTableOverhead n <=
        2 ^ (scale + (3 * bpFringeChunkBits (2 * n) + 3)) := by
    calc
      scale * bpChunkSelectTableOverhead n <=
          2 ^ scale * 2 ^ (3 * bpFringeChunkBits (2 * n) + 3) :=
        Nat.mul_le_mul hscalePow hT
      _ = 2 ^ (scale + (3 * bpFringeChunkBits (2 * n) + 3)) := by
        rw [<- Nat.pow_add]
  have hlogPow : 2 ^ Nat.log2 n <= n := Nat.log2_self_le (by omega)
  have hmono :
      2 ^ (scale + (3 * bpFringeChunkBits (2 * n) + 3)) <=
        2 ^ Nat.log2 n :=
    Nat.pow_le_pow_right (by omega) hexp
  omega

/--
The select-table word fits one machine word of the linear reviewer
capacity `400000 * (n + 1)` at every input size.
-/
theorem bpChunkSelectEntryWidth_le_machineWordBits_capacity (n : Nat) :
    bpChunkSelectEntryWidth (bpFringeChunkBits (2 * n)) <=
      SuccinctRank.machineWordBits (400000 * (n + 1)) := by
  have hwidth := bpChunkSelectEntryWidth_le (bpFringeChunkBits (2 * n))
  have hc : bpFringeChunkBits (2 * n) = Nat.log2 (2 * n) / 8 + 1 := rfl
  have h18 : 18 <= Nat.log2 (400000 * (n + 1)) := by
    rcases Nat.lt_or_ge (Nat.log2 (400000 * (n + 1))) 18 with hlt | hge
    · exfalso
      have h3 :
          400000 * (n + 1) < 2 ^ (Nat.log2 (400000 * (n + 1)) + 1) :=
        Nat.lt_log2_self
      have h2 :
          2 ^ (Nat.log2 (400000 * (n + 1)) + 1) <= 2 ^ 18 :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have hval : (2 : Nat) ^ 18 = 262144 := by decide
      have hlin : 400000 <= 400000 * (n + 1) := by
        have := Nat.mul_le_mul_left 400000 (show 1 <= n + 1 by omega)
        omega
      omega
    · exact hge
  have hmono :
      Nat.log2 (2 * n) <= Nat.log2 (400000 * (n + 1)) := by
    have h :=
      SuccinctRank.machineWordBits_mono_le
        (show 2 * n <= 400000 * (n + 1) by omega)
    unfold SuccinctRank.machineWordBits at h
    omega
  unfold SuccinctRank.machineWordBits
  omega

/-! ## The charged in-word select fold -/

/--
The charged in-word select fold: per chunk one popcount read of the
existing table routes the fold; the containing chunk finishes with exactly
one select-table read.  Generic over both supplied tables so store
corruption is expressible.
-/
def bpChunkedWordSelectCostedFrom
    {entriesR : List Nat} {widthR : Nat} {entriesS : List Nat}
    {widthS : Nat}
    (rankTable : SuccinctSpace.FixedWidthNatTable entriesR widthR)
    (selTable : SuccinctSpace.FixedWidthNatTable entriesS widthS)
    (c : Nat) (target : Bool) (word : List Bool) :
    Nat -> Nat -> Nat -> Costed (Option Nat)
  | _j, 0, _k => Costed.pure none
  | j, count + 1, k =>
      Costed.bind
        (rankTable.readCosted
          (bpFringeChunkSlot c (bpFringeWindowChunkValue c word j)
            (bpWordChunkSliceLen c word.length j)
            (bpWordChunkSliceLen c word.length j)))
        (fun entry? =>
          if k <
              bpChunkRankOfEntry c target
                (bpWordChunkSliceLen c word.length j)
                (entry?.getD 0) then
            Costed.map (fun sel? => some (j * c + sel?.getD 0))
              (selTable.readCosted
                (bpChunkSelectSlot c (bpFringeWindowChunkValue c word j)
                  k))
          else
            bpChunkedWordSelectCostedFrom rankTable selTable c target
              word (j + 1) count
              (k -
                bpChunkRankOfEntry c target
                  (bpWordChunkSliceLen c word.length j)
                  (entry?.getD 0)))

/--
One-step value characterization on the found branch: when the decoded
routing count of chunk `j` exceeds `k`, the fold returns the select-table
read shifted to the chunk base (used by the corruption witness without
reducing through the stored tables).
-/
theorem bpChunkedWordSelectCostedFrom_step_found
    {entriesR : List Nat} {widthR : Nat} {entriesS : List Nat}
    {widthS : Nat}
    (rankTable : SuccinctSpace.FixedWidthNatTable entriesR widthR)
    (selTable : SuccinctSpace.FixedWidthNatTable entriesS widthS)
    (c : Nat) (target : Bool) (word : List Bool) (j count k : Nat)
    (hfound :
      k <
        bpChunkRankOfEntry c target
          (bpWordChunkSliceLen c word.length j)
          (((rankTable.readCosted
              (bpFringeChunkSlot c (bpFringeWindowChunkValue c word j)
                (bpWordChunkSliceLen c word.length j)
                (bpWordChunkSliceLen c word.length j))).value).getD 0)) :
    (bpChunkedWordSelectCostedFrom rankTable selTable c target word j
        (count + 1) k).value =
      some
        (j * c +
          (((selTable.readCosted
              (bpChunkSelectSlot c (bpFringeWindowChunkValue c word j)
                k)).value).getD 0)) := by
  show
    (Costed.bind
        (rankTable.readCosted
          (bpFringeChunkSlot c (bpFringeWindowChunkValue c word j)
            (bpWordChunkSliceLen c word.length j)
            (bpWordChunkSliceLen c word.length j)))
        _).value = _
  rw [Costed.value_bind]
  rw [if_pos hfound]
  rw [Costed.map_value]

/-- Charged in-word select of the k-th `target` bit in one word. -/
def bpChunkedWordSelectCosted
    {entriesR : List Nat} {widthR : Nat} {entriesS : List Nat}
    {widthS : Nat}
    (rankTable : SuccinctSpace.FixedWidthNatTable entriesR widthR)
    (selTable : SuccinctSpace.FixedWidthNatTable entriesS widthS)
    (c : Nat) (target : Bool) (word : List Bool) (occurrence : Nat) :
    Costed (Option Nat) :=
  bpChunkedWordSelectCostedFrom rankTable selTable c target word 0
    (bpWordChunkCount c word.length) occurrence

/-- At most one read per visited chunk plus the final select read. -/
theorem bpChunkedWordSelectCostedFrom_cost_le
    {entriesR : List Nat} {widthR : Nat} {entriesS : List Nat}
    {widthS : Nat}
    (rankTable : SuccinctSpace.FixedWidthNatTable entriesR widthR)
    (selTable : SuccinctSpace.FixedWidthNatTable entriesS widthS)
    (c : Nat) (target : Bool) (word : List Bool) :
    forall (count j k : Nat),
      (bpChunkedWordSelectCostedFrom rankTable selTable c target word
          j count k).cost <= count + 1 := by
  intro count
  induction count with
  | zero =>
      intro j k
      simp [bpChunkedWordSelectCostedFrom, Costed.pure]
  | succ count ih =>
      intro j k
      have hrank := rankTable.readCosted_cost_le_one
        (bpFringeChunkSlot c (bpFringeWindowChunkValue c word j)
          (bpWordChunkSliceLen c word.length j)
          (bpWordChunkSliceLen c word.length j))
      have hsel := selTable.readCosted_cost_le_one
        (bpChunkSelectSlot c (bpFringeWindowChunkValue c word j) k)
      have hrec := ih (j + 1)
        (k -
          bpChunkRankOfEntry c target
            (bpWordChunkSliceLen c word.length j)
            (((rankTable.readCosted
                (bpFringeChunkSlot c
                  (bpFringeWindowChunkValue c word j)
                  (bpWordChunkSliceLen c word.length j)
                  (bpWordChunkSliceLen c word.length j))).value).getD 0))
      by_cases hfound :
          k <
            bpChunkRankOfEntry c target
              (bpWordChunkSliceLen c word.length j)
              (((rankTable.readCosted
                  (bpFringeChunkSlot c
                    (bpFringeWindowChunkValue c word j)
                    (bpWordChunkSliceLen c word.length j)
                    (bpWordChunkSliceLen c word.length j))).value).getD 0)
      · simp [bpChunkedWordSelectCostedFrom, Costed.bind, Costed.map,
          hfound]
        all_goals omega
      · simp [bpChunkedWordSelectCostedFrom, Costed.bind, hfound]
        all_goals omega

/-- All-size literal read bound for the charged in-word select. -/
theorem bpChunkedWordSelectCosted_cost_le
    {entriesR : List Nat} {widthR : Nat} {entriesS : List Nat}
    {widthS : Nat}
    (rankTable : SuccinctSpace.FixedWidthNatTable entriesR widthR)
    (selTable : SuccinctSpace.FixedWidthNatTable entriesS widthS)
    (c : Nat) (target : Bool) (word : List Bool) (occurrence : Nat) :
    (bpChunkedWordSelectCosted rankTable selTable c target word
        occurrence).cost <= 9 := by
  have h :=
    bpChunkedWordSelectCostedFrom_cost_le rankTable selTable c target
      word (bpWordChunkCount c word.length) 0 occurrence
  have hcap := bpWordChunkCount_le_eight c word.length
  unfold bpChunkedWordSelectCosted
  omega

/--
Fold invariant against the honest tables: starting at chunk `j` with the
occurrence shifted by the clamped prefix rank at the chunk boundary, the
fold returns exactly the reference in-word select value.
-/
theorem bpChunkedWordSelectCostedFrom_value
    (c : Nat) (target : Bool) (word : List Bool) :
    forall (count j k occurrence : Nat),
      word.length <= (j + count) * c ->
      Succinct.rankPrefix target word (Nat.min (j * c) word.length) <=
        occurrence ->
      k =
        occurrence -
          Succinct.rankPrefix target word
            (Nat.min (j * c) word.length) ->
      (bpChunkedWordSelectCostedFrom (bpFringeChunkTable c)
          (bpChunkSelectTable c target) c target word j count k).value =
        Succinct.select target word occurrence := by
  intro count
  induction count with
  | zero =>
      intro j k occurrence hcov hlow _hk
      have hje : word.length <= j * c := by
        have hzero : (j + 0) * c = j * c := by rw [Nat.add_zero]
        omega
      have hmin : Nat.min (j * c) word.length = word.length :=
        Nat.min_eq_right hje
      rw [hmin] at hlow
      cases hsel : Succinct.select target word occurrence with
      | none =>
          rfl
      | some pos =>
          exfalso
          have hbound := Succinct.select_bounds hsel
          have hlt :=
            GenericSelect.occurrence_lt_rankPrefix_of_select_lt hsel
              hbound
          omega
  | succ count ih =>
      intro j k occurrence hcov hlow hk
      have hv := bpFringeWindowChunkValue_lt c word j
      have ht := bpWordChunkSliceLen_le c word.length j
      have hread :
          ((bpFringeChunkTable c).readCosted
              (bpFringeChunkSlot c (bpFringeWindowChunkValue c word j)
                (bpWordChunkSliceLen c word.length j)
                (bpWordChunkSliceLen c word.length j))).value =
            some
              (bpFringeChunkPacked c (bpFringeWindowChunkValue c word j)
                (bpWordChunkSliceLen c word.length j)
                (bpWordChunkSliceLen c word.length j)) :=
        bpFringeChunkTable_readCosted_erase hv ht ht
      have hstep :=
        bpWordChunkRank_step c target word (Nat.le_refl word.length) j
      have hcnt :
          bpChunkRankOfEntry c target
              (bpWordChunkSliceLen c word.length j)
              (bpFringeChunkPacked c (bpFringeWindowChunkValue c word j)
                (bpWordChunkSliceLen c word.length j)
                (bpWordChunkSliceLen c word.length j)) =
            Succinct.rankPrefix target word
                (Nat.min ((j + 1) * c) word.length) -
              Succinct.rankPrefix target word
                (Nat.min (j * c) word.length) := by
        rw [bpChunkRankOfEntry_packed c target hv ht]
        exact hstep
      have hexp : (j + 1) * c = j * c + c := Nat.succ_mul j c
      have hjj1 : j * c <= (j + 1) * c := by omega
      have hm1 :
          Nat.min (j * c) word.length <=
            Nat.min ((j + 1) * c) word.length :=
        Nat.le_min.mpr
          ⟨Nat.le_trans (Nat.min_le_left _ _) hjj1, Nat.min_le_right _ _⟩
      have hr1 := Succinct.rankPrefix_mono_limit target word hm1
      show
        (Costed.bind
            ((bpFringeChunkTable c).readCosted
              (bpFringeChunkSlot c (bpFringeWindowChunkValue c word j)
                (bpWordChunkSliceLen c word.length j)
                (bpWordChunkSliceLen c word.length j)))
            _).value = _
      rw [Costed.value_bind, hread]
      simp only [Option.getD_some]
      rw [hcnt]
      by_cases hfound :
          k <
            Succinct.rankPrefix target word
                (Nat.min ((j + 1) * c) word.length) -
              Succinct.rankPrefix target word
                (Nat.min (j * c) word.length)
      · rw [if_pos hfound]
        -- the occurrence lands in chunk j
        have hocc :
            occurrence =
              Succinct.rankPrefix target word
                  (Nat.min (j * c) word.length) + k := by
          omega
        have hoccLt :
            occurrence <
              Succinct.rankPrefix target word
                (Nat.min ((j + 1) * c) word.length) := by
          omega
        rcases GenericSelect.select_exists_of_lt_rankPrefix hoccLt with
          ⟨pos, hsel⟩
        have hposLen := Succinct.select_bounds hsel
        have hposLow : j * c <= pos := by
          by_cases hple : j * c <= pos
          · exact hple
          · exfalso
            have hplt : pos < j * c := by omega
            have hpltMin : pos < Nat.min (j * c) word.length :=
              Nat.lt_min.mpr ⟨hplt, hposLen⟩
            have hltRank :=
              GenericSelect.occurrence_lt_rankPrefix_of_select_lt hsel
                hpltMin
            omega
        have hposHi : pos < Nat.min ((j + 1) * c) word.length := by
          by_cases hplt : pos < Nat.min ((j + 1) * c) word.length
          · exact hplt
          · exfalso
            have hge : Nat.min ((j + 1) * c) word.length <= pos := by
              omega
            have hrle :=
              Succinct.rankPrefix_le_occurrence_of_le_select hsel hge
            omega
        have hjcLt : j * c < word.length := by
          omega
        have hminJ : Nat.min (j * c) word.length = j * c :=
          Nat.min_eq_left (Nat.le_of_lt hjcLt)
        have hposC : pos < j * c + c := by
          have hle : Nat.min ((j + 1) * c) word.length <= (j + 1) * c :=
            Nat.min_le_left _ _
          omega
        have hrankLe :
            Succinct.rankPrefix target word (j * c) <= occurrence := by
          rw [hminJ] at hlow
          exact hlow
        have hlocal :=
          Succinct.select_drop_take_eq_sub_of_select
            (target := target) (bits := word) (occurrence := occurrence)
            (idx := pos) (start := j * c) (width := c)
            hsel hposLow hposC (Nat.le_of_lt hjcLt) hrankLe
        have hlocalK :
            Succinct.select target ((word.drop (j * c)).take c) k =
              some (pos - j * c) := by
          rw [<- hlocal]
          congr 1
          rw [hk, hminJ]
        have hkc : k <= c := by
          have hcntLe :
              Succinct.rankPrefix target word
                  (Nat.min ((j + 1) * c) word.length) -
                Succinct.rankPrefix target word
                  (Nat.min (j * c) word.length) <=
                bpWordChunkSliceLen c word.length j := by
            rw [<- hstep]
            have := Succinct.rankPrefix_le_limit target
              (bpFringeChunkPattern c
                (bpFringeWindowChunkValue c word j))
              (bpWordChunkSliceLen c word.length j)
            omega
          omega
        have hselRead :
            ((bpChunkSelectTable c target).readCosted
                (bpChunkSelectSlot c (bpFringeWindowChunkValue c word j)
                  k)).value =
              some
                (bpChunkSelectPos c target
                  (bpFringeWindowChunkValue c word j) k) :=
          bpChunkSelectTable_readCosted_erase target hv hkc
        have hpatternSel :
            bpChunkSelectPos c target (bpFringeWindowChunkValue c word j)
                k = pos - j * c := by
          unfold bpChunkSelectPos
          have hlenSlice : ((word.drop (j * c)).take c).length <= c := by
            simp [List.length_take]
            omega
          have happend :
              Succinct.select target
                  (bpFringeChunkPattern c
                    (bpFringeWindowChunkValue c word j)) k =
                some (pos - j * c) := by
            unfold bpFringeChunkPattern bpFringeWindowChunkValue
            rw [natToBitsLE_bitsToNatLE_append_replicate hlenSlice]
            exact Succinct.select_append_left_of_some hlocalK
          rw [happend]
          rfl
        show
          (Costed.map (fun sel? => some (j * c + sel?.getD 0))
              ((bpChunkSelectTable c target).readCosted
                (bpChunkSelectSlot c (bpFringeWindowChunkValue c word j)
                  k))).value = _
        rw [Costed.map_value, hselRead]
        simp only [Option.getD_some]
        rw [hpatternSel]
        have hposEq : j * c + (pos - j * c) = pos := by omega
        rw [hposEq]
        exact hsel.symm
      · rw [if_neg hfound]
        have hcov' : word.length <= (j + 1 + count) * c := by
          have hidx : j + 1 + count = j + (count + 1) := by omega
          rw [hidx]
          exact hcov
        have hlow' :
            Succinct.rankPrefix target word
                (Nat.min ((j + 1) * c) word.length) <= occurrence := by
          omega
        have hk' :
            k -
                (Succinct.rankPrefix target word
                    (Nat.min ((j + 1) * c) word.length) -
                  Succinct.rankPrefix target word
                    (Nat.min (j * c) word.length)) =
              occurrence -
                Succinct.rankPrefix target word
                  (Nat.min ((j + 1) * c) word.length) := by
          omega
        rw [ih (j + 1) _ occurrence hcov' hlow' hk']

/--
Universal in-word select equivalence: against the honest tables, the
charged chunked in-word select computes exactly
`RMQ.RAM.boolSelectInWord`, for every target, word, and occurrence,
whenever the word fits in 8 chunks.
-/
theorem bpChunkedWordSelectCosted_value
    (c : Nat) (hc : 0 < c) (target : Bool) (word : List Bool)
    (occurrence : Nat) (hlen : word.length <= 8 * c) :
    (bpChunkedWordSelectCosted (bpFringeChunkTable c)
        (bpChunkSelectTable c target) c target word occurrence).value =
      RMQ.RAM.boolSelectInWord target word occurrence := by
  have hcount :
      bpWordChunkCount c word.length = (word.length - 1) / c + 1 :=
    bpWordChunkCount_eq hc hlen
  have hcov :
      word.length <= (0 + ((word.length - 1) / c + 1)) * c := by
    rw [Nat.zero_add]
    exact bpWordChunkCount_cov hc
  have hmin0 : Nat.min (0 * c) word.length = 0 := by
    rw [Nat.zero_mul]
    exact Nat.min_eq_left (Nat.zero_le _)
  unfold bpChunkedWordSelectCosted
  rw [hcount]
  rw [bpChunkedWordSelectCostedFrom_value c target word
    ((word.length - 1) / c + 1) 0 occurrence occurrence hcov
    (by rw [hmin0, Succinct.rankPrefix_zero]; omega)
    (by rw [hmin0, Succinct.rankPrefix_zero]; omega)]
  rw [Succinct.ram_boolSelectInWord_eq_select]

/-! ## Adversarial select-table corruption witness (value dependency)

Corrupting the one select-table entry the charged fold actually reads
changes the returned position on a concrete witness input.  Slot `0` is
exactly the slot the witness invocation reads (`hslot` below), so the
corrupted entry lies in the actual charged read footprint.
-/

def bpChunkSelectCorruptedEntriesWitness : List Nat :=
  (bpChunkSelectEntries 1 false).set 0 1

def bpChunkSelectCorruptedTableWitness :
    SuccinctSpace.FixedWidthNatTable bpChunkSelectCorruptedEntriesWitness
      (bpChunkSelectEntryWidth 1) :=
  SuccinctSpace.FixedWidthNatTable.ofEntries _ _ (by
    intro entry hmem
    rcases List.mem_or_eq_of_mem_set hmem with hmem' | rfl
    · exact bpChunkSelectEntries_mem_lt_two_pow_width hmem'
    · show 1 < 2 ^ bpChunkSelectEntryWidth 1
      have hself : 1 + 1 < 2 ^ (Nat.log2 (1 + 1) + 1) := Nat.lt_log2_self
      have hwidth : bpChunkSelectEntryWidth 1 = Nat.log2 (1 + 1) + 1 := rfl
      rw [hwidth]
      omega)

theorem bpChunkSelectTable_corruption_changes_select_value :
    (bpChunkedWordSelectCosted (bpFringeChunkTable 1)
        (bpChunkSelectTable 1 false) 1 false [false] 0).value ≠
      (bpChunkedWordSelectCosted (bpFringeChunkTable 1)
        bpChunkSelectCorruptedTableWitness 1 false [false] 0).value := by
  have hslot : bpChunkSelectSlot 1 (bpFringeWindowChunkValue 1 [false] 0)
      0 = 0 := by decide
  have hhonest :
      (bpChunkedWordSelectCosted (bpFringeChunkTable 1)
          (bpChunkSelectTable 1 false) 1 false [false] 0).value =
        some 0 := by
    rw [bpChunkedWordSelectCosted_value 1 (by omega) false [false] 0
      (by decide)]
    decide
  have hcorrupt :
      (bpChunkedWordSelectCosted (bpFringeChunkTable 1)
          bpChunkSelectCorruptedTableWitness 1 false [false] 0).value =
        some 1 := by
    have hread :
        ((bpFringeChunkTable 1).readCosted
            (bpFringeChunkSlot 1 (bpFringeWindowChunkValue 1 [false] 0)
              (bpWordChunkSliceLen 1 (List.length [false]) 0)
              (bpWordChunkSliceLen 1 (List.length [false]) 0))).value =
          some
            (bpFringeChunkPacked 1 (bpFringeWindowChunkValue 1 [false] 0)
              (bpWordChunkSliceLen 1 (List.length [false]) 0)
              (bpWordChunkSliceLen 1 (List.length [false]) 0)) :=
      bpFringeChunkTable_readCosted_erase (by decide) (by decide)
        (by decide)
    have hfound :
        0 <
          bpChunkRankOfEntry 1 false
            (bpWordChunkSliceLen 1 (List.length [false]) 0)
            ((((bpFringeChunkTable 1).readCosted
                (bpFringeChunkSlot 1
                  (bpFringeWindowChunkValue 1 [false] 0)
                  (bpWordChunkSliceLen 1 (List.length [false]) 0)
                  (bpWordChunkSliceLen 1
                    (List.length [false]) 0))).value).getD 0) := by
      rw [hread]
      decide
    have hstep :=
      bpChunkedWordSelectCostedFrom_step_found (bpFringeChunkTable 1)
        bpChunkSelectCorruptedTableWitness 1 false [false] 0 0 0 hfound
    have hget : bpChunkSelectCorruptedEntriesWitness[0]? = some 1 := by
      decide
    have hselread :
        (bpChunkSelectCorruptedTableWitness.readCosted 0).value =
          some 1 := by
      have h :=
        SuccinctSpace.FixedWidthNatTable.readCosted_erase
          bpChunkSelectCorruptedTableWitness 0
      rw [hget] at h
      exact h
    have hcount :
        bpWordChunkCount 1 (List.length [false]) = 0 + 1 := by decide
    show
      (bpChunkedWordSelectCostedFrom (bpFringeChunkTable 1)
          bpChunkSelectCorruptedTableWitness 1 false [false] 0
          (bpWordChunkCount 1 (List.length [false])) 0).value = some 1
    rw [hcount, hstep, hslot, hselread]
    decide
  rw [hhonest, hcorrupt]
  simp

end SuccinctClose

end RMQ
