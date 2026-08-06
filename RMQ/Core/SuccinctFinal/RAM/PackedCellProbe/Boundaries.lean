import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ExecutedUniverse

/-!
# Named geometry thresholds, kernel-checked

`FG-14` asks for instances at each relevant threshold minus one, at, and plus one,
with the thresholds *named explicitly from the geometry* rather than asserted.
This module locates and checks the long crossover the commissioning prompt
recorded as `5488/5489`.

`decide` cannot do it. `Nat.log2` is defined by well-founded recursion, so kernel
reduction sticks on it -- `#eval` succeeds through the compiler and proves
nothing. `packedLog2_eq` closes the gap: it pins a logarithm from a pair of
power-of-two bounds, which the kernel evaluates without unfolding the recursion at
all.

The crossover is the point where a superblock's span stops covering the whole BP
code. Below it `min (2n) (superLongSpan (2n))` is `2n`; at and above it the span
is the smaller of the two, so the select layer's relative width stops tracking the
input size. It is not a threshold anybody chose: it is where
`superStride * wordBits * ell` stops growing while `2n` keeps going.
-/

namespace RMQ

namespace SuccinctFinal

namespace PackedCellProbe

open Cartesian

/-! ## Pinning a logarithm without unfolding it -/

/--
`Nat.log2 n = k` from two power-of-two bounds.

`Nat.le_log2` and `Nat.log2_lt` are the two halves; the kernel needs neither the
recursion nor a fuel bound, only `2 ^ k` and `2 ^ (k + 1)` as literals.
-/
theorem packedLog2_eq {n k : Nat} (hn : n ≠ 0)
    (hlow : 2 ^ k <= n) (hhigh : n < 2 ^ (k + 1)) :
    Nat.log2 n = k := by
  have h1 : k <= Nat.log2 n := (Nat.le_log2 hn).mpr hlow
  have h2 : Nat.log2 n < k + 1 := (Nat.log2_lt hn).mpr hhigh
  omega

theorem packedMachineWordBits_eq {n k : Nat} (hn : n ≠ 0)
    (hlow : 2 ^ k <= n) (hhigh : n < 2 ^ (k + 1)) :
    SuccinctRank.machineWordBits n = k + 1 := by
  unfold SuccinctRank.machineWordBits
  rw [packedLog2_eq hn hlow hhigh]

/-! ## The long crossover

At `n = 5488` the BP code is `10976` bits and a superblock's long span is exactly
`10976`. One step later the code is `10978` bits and the span has not moved.
-/

theorem packedWordBits_bpCode_5488 :
    GenericSelect.wordBits (2 * 5488) = 14 := by
  unfold GenericSelect.wordBits
  exact packedMachineWordBits_eq (by omega) (by decide) (by decide)

theorem packedWordBits_bpCode_5489 :
    GenericSelect.wordBits (2 * 5489) = 14 := by
  unfold GenericSelect.wordBits
  exact packedMachineWordBits_eq (by omega) (by decide) (by decide)

theorem packedEll_bpCode_5488 :
    GenericSelect.ell (2 * 5488) = 4 := by
  unfold GenericSelect.ell
  rw [packedWordBits_bpCode_5488]
  rw [packedLog2_eq (n := 14) (k := 3) (by omega) (by decide) (by decide)]

theorem packedEll_bpCode_5489 :
    GenericSelect.ell (2 * 5489) = 4 := by
  unfold GenericSelect.ell
  rw [packedWordBits_bpCode_5489]
  rw [packedLog2_eq (n := 14) (k := 3) (by omega) (by decide) (by decide)]

theorem packedSuperLongSpan_5488 :
    GenericSelect.superLongSpan (2 * 5488) = 10976 := by
  unfold GenericSelect.superLongSpan GenericSelect.superStride
  rw [packedWordBits_bpCode_5488, packedEll_bpCode_5488]

theorem packedSuperLongSpan_5489 :
    GenericSelect.superLongSpan (2 * 5489) = 10976 := by
  unfold GenericSelect.superLongSpan GenericSelect.superStride
  rw [packedWordBits_bpCode_5489, packedEll_bpCode_5489]

/--
**At `5488` the span still covers the code.** The relative width tracks the input
size.
-/
theorem packedLongCrossover_at :
    Nat.min (2 * 5488) (GenericSelect.superLongSpan (2 * 5488)) = 2 * 5488 := by
  rw [packedSuperLongSpan_5488]
  decide

/--
**At `5489` it no longer does.** One step later the span is strictly smaller than
the BP code, so `min` switches sides and the select layer's relative width stops
tracking the input size. This is the crossover the commissioning prompt recorded,
located from the geometry rather than asserted.
-/
theorem packedLongCrossover_after :
    Nat.min (2 * 5489) (GenericSelect.superLongSpan (2 * 5489)) < 2 * 5489 := by
  rw [packedSuperLongSpan_5489]
  decide

/-- One step before the crossover, for the minus-one/at/plus-one triple. -/
theorem packedLongCrossover_before :
    Nat.min (2 * 5487) (GenericSelect.superLongSpan (2 * 5487)) = 2 * 5487 := by
  have hword : GenericSelect.wordBits (2 * 5487) = 14 := by
    unfold GenericSelect.wordBits
    exact packedMachineWordBits_eq (by omega) (by decide) (by decide)
  have hell : GenericSelect.ell (2 * 5487) = 4 := by
    unfold GenericSelect.ell
    rw [hword]
    rw [packedLog2_eq (n := 14) (k := 3) (by omega) (by decide) (by decide)]
  have hspan : GenericSelect.superLongSpan (2 * 5487) = 10976 := by
    unfold GenericSelect.superLongSpan GenericSelect.superStride
    rw [hword, hell]
  rw [hspan]
  decide

/--
The crossover is visible in the packed geometry itself: `packedLocalWidth` is
`machineWordBits` of exactly this `min`.
-/
theorem packedLocalWidth_at_crossover :
    packedLocalWidth 5488 = SuccinctRank.machineWordBits (2 * 5488) /\
      packedLocalWidth 5489 = SuccinctRank.machineWordBits 10976 := by
  constructor
  · unfold packedLocalWidth
    rw [packedLongCrossover_at]
  · unfold packedLocalWidth
    rw [packedSuperLongSpan_5489]
    congr 1

/-! ## The interior-readiness window

`PackedInteriorReady n` is `PackedSummaryActive n` and
`packedInteriorMacroSize n <= packedSummaryBlockCount n`. Across `[1023, 1331]`
the activity predicate does not move; the second conjunct does, and it moves for
a reason visible in one number.

`packedSummaryBase n = Nat.log2 n + 1` jumps from `10` to `11` at `n = 1024`. The
macro size is that base squared, so it jumps `100 -> 121`, while the raw block
count is `n / base`, which *drops* `102 -> 93` because the divisor grew. The
interior is unready until the block count climbs back to the macro size, which
happens exactly at `n = 1331` (`1331 / 11 = 121`).

So the recorded `[1024, 1330]` window is not a tuning constant: it is the interval
on which `base * base` exceeds `n / base`, and its two endpoints are checked below
with their neighbours.
-/

theorem packedSummaryBase_1023 : packedSummaryBase 1023 = 10 := by
  unfold packedSummaryBase
  rw [packedLog2_eq (n := 1023) (k := 9) (by omega) (by decide) (by decide)]

theorem packedSummaryBase_1024 : packedSummaryBase 1024 = 11 := by
  unfold packedSummaryBase
  rw [packedLog2_eq (n := 1024) (k := 10) (by omega) (by decide) (by decide)]

theorem packedSummaryBase_1330 : packedSummaryBase 1330 = 11 := by
  unfold packedSummaryBase
  rw [packedLog2_eq (n := 1330) (k := 10) (by omega) (by decide) (by decide)]

theorem packedSummaryBase_1331 : packedSummaryBase 1331 = 11 := by
  unfold packedSummaryBase
  rw [packedLog2_eq (n := 1331) (k := 10) (by omega) (by decide) (by decide)]

/-- Just below the window the macro size still fits. -/
theorem packedInteriorFits_1023 :
    packedInteriorMacroSize 1023 <= packedSummaryBlockCountRaw 1023 := by
  unfold packedInteriorMacroSize packedSummaryBlockCountRaw
  rw [packedSummaryBase_1023]
  decide

/-- At the window's lower endpoint it does not: the base grew, so the macro size
grew and the block count fell. -/
theorem packedInteriorUnfits_1024 :
    packedSummaryBlockCountRaw 1024 < packedInteriorMacroSize 1024 := by
  unfold packedInteriorMacroSize packedSummaryBlockCountRaw
  rw [packedSummaryBase_1024]
  decide

/-- Still unready at the window's upper endpoint, by exactly one block. -/
theorem packedInteriorUnfits_1330 :
    packedSummaryBlockCountRaw 1330 < packedInteriorMacroSize 1330 := by
  unfold packedInteriorMacroSize packedSummaryBlockCountRaw
  rw [packedSummaryBase_1330]
  decide

/-- One step later the block count has caught up and the window closes. -/
theorem packedInteriorFits_1331 :
    packedInteriorMacroSize 1331 <= packedSummaryBlockCountRaw 1331 := by
  unfold packedInteriorMacroSize packedSummaryBlockCountRaw
  rw [packedSummaryBase_1331]
  decide

/-- The base does not move inside the window: `1025` still sits in
`[2^10, 2^11)`, so the divisor that jumped at `1024` stays put. -/
theorem packedSummaryBase_1025 : packedSummaryBase 1025 = 11 := by
  unfold packedSummaryBase
  rw [packedLog2_eq (n := 1025) (k := 10) (by omega) (by decide) (by decide)]

/-- One step past the lower endpoint nothing has recovered: with the base pinned
at `11` the block count is still `93` against a macro size of `121`, so the
unreadiness at `1024` is not a boundary accident. -/
theorem packedInteriorUnfits_1025 :
    packedSummaryBlockCountRaw 1025 < packedInteriorMacroSize 1025 := by
  unfold packedInteriorMacroSize packedSummaryBlockCountRaw
  rw [packedSummaryBase_1025]
  decide

/-- The base has been `11` the whole way across: `1329` is still short of
`2048`. -/
theorem packedSummaryBase_1329 : packedSummaryBase 1329 = 11 := by
  unfold packedSummaryBase
  rw [packedLog2_eq (n := 1329) (k := 10) (by omega) (by decide) (by decide)]

/-- One step before the upper endpoint the block count has already climbed to
`120` -- the same one-block shortfall as at `1330`, because `n / 11` only moves
every eleventh step. -/
theorem packedInteriorUnfits_1329 :
    packedSummaryBlockCountRaw 1329 < packedInteriorMacroSize 1329 := by
  unfold packedInteriorMacroSize packedSummaryBlockCountRaw
  rw [packedSummaryBase_1329]
  decide

/--
**The window with a step inside each endpoint.** The readiness clause fails one
step into the interval as well as at its endpoints, so the failure belongs to the
interval `[1024, 1330]` itself and not to an accident of its edges.
-/
theorem packedInteriorReadinessWindowNeighbors :
    packedInteriorMacroSize 1023 <= packedSummaryBlockCountRaw 1023 /\
      packedSummaryBlockCountRaw 1024 < packedInteriorMacroSize 1024 /\
        packedSummaryBlockCountRaw 1025 < packedInteriorMacroSize 1025 /\
          packedSummaryBlockCountRaw 1329 < packedInteriorMacroSize 1329 /\
            packedSummaryBlockCountRaw 1330 < packedInteriorMacroSize 1330 /\
              packedInteriorMacroSize 1331 <= packedSummaryBlockCountRaw 1331 :=
  ⟨packedInteriorFits_1023, packedInteriorUnfits_1024, packedInteriorUnfits_1025,
    packedInteriorUnfits_1329, packedInteriorUnfits_1330, packedInteriorFits_1331⟩

/--
**The window, as one statement.** The readiness clause that moves fails at both
endpoints of `[1024, 1330]` and holds at both neighbours.
-/
theorem packedInteriorReadinessWindow :
    packedInteriorMacroSize 1023 <= packedSummaryBlockCountRaw 1023 /\
      packedSummaryBlockCountRaw 1024 < packedInteriorMacroSize 1024 /\
        packedSummaryBlockCountRaw 1330 < packedInteriorMacroSize 1330 /\
          packedInteriorMacroSize 1331 <= packedSummaryBlockCountRaw 1331 :=
  ⟨packedInteriorFits_1023, packedInteriorUnfits_1024,
    packedInteriorUnfits_1330, packedInteriorFits_1331⟩

/-! ## The sparse-exception path is unreachable at unit stride

`DD-20260804-041`. A local slot covers `localStride` occurrences, and
`shortSuperLocalSpan` measures the span *between the slot's own occurrences* --
base occurrence position to last occurrence position, plus one. So at unit stride
a slot's span is at most one, the exception predicate's second conjunct becomes
`wordBits < 1`, and `wordBits_pos` closes it.

This is why the measured sparse exception count is zero everywhere: the path is
unreachable, not merely unvisited.
-/

theorem packedShortSuperLocalSpan_le_one_of_unit_stride
    (bits : List Bool) (target : Bool) (slot : Nat)
    (hstride : GenericSelect.localStride bits.length = 1) :
    GenericSelect.shortSuperLocalSpan bits target slot <= 1 := by
  have hmin :
      Nat.min (GenericSelect.localBaseOccurrence bits.length slot + 1)
          (GenericSelect.superEndOccurrence bits target
            (GenericSelect.localSuperSlot bits.length slot)) <=
        GenericSelect.localBaseOccurrence bits.length slot + 1 :=
    Nat.min_le_left _ _
  have hle :
      Nat.min (GenericSelect.localBaseOccurrence bits.length slot + 1)
          (GenericSelect.superEndOccurrence bits target
            (GenericSelect.localSuperSlot bits.length slot)) - 1 <=
        GenericSelect.localBaseOccurrence bits.length slot := by
    omega
  have hmono := GenericSelect.position_mono bits target hle
  simp only [GenericSelect.shortSuperLocalSpan,
    GenericSelect.shortSuperLocalEndOccurrence, hstride]
  omega

/--
**No sparse exception can occur at unit stride.** Not because the bit pattern is
convenient -- because a one-occurrence span cannot exceed a machine word.
-/
theorem packedLocalIsSparseException_false_of_unit_stride
    (bits : List Bool) (target : Bool) (slot : Nat)
    (hstride : GenericSelect.localStride bits.length = 1) :
    GenericSelect.localIsSparseException bits target slot = false := by
  have hspan :=
    packedShortSuperLocalSpan_le_one_of_unit_stride bits target slot hstride
  have hword : 0 < GenericSelect.wordBits bits.length :=
    GenericSelect.wordBits_pos _
  have hnot :
      ¬ GenericSelect.wordBits bits.length <
          GenericSelect.shortSuperLocalSpan bits target slot := by
    omega
  unfold GenericSelect.localIsSparseException
  simp [hnot]

/-! ### From "no exception" to "no entries" -/

theorem packedRankPrefix_true_eq_zero_of_all_false :
    forall (l : List Bool) (k : Nat),
      (forall b, List.Mem b l -> b = false) ->
        RMQ.Succinct.rankPrefix true l k = 0 := by
  intro l
  induction l with
  | nil =>
      intro k _
      cases k with
      | zero => rfl
      | succ _ => rfl
  | cons bit rest ih =>
      intro k hall
      cases k with
      | zero => rfl
      | succ k =>
          have hbit : bit = false := hall bit List.mem_cons_self
          have hrest : forall b, List.Mem b rest -> b = false := by
            intro b hmem
            exact hall b (List.mem_cons_of_mem bit hmem)
          simp [RMQ.Succinct.rankPrefix, hbit, ih k hrest]

theorem packedSparseFlagBits_allFalse_of_unit_stride
    (bits : List Bool) (target : Bool)
    (hstride : GenericSelect.localStride bits.length = 1) :
    forall b, List.Mem b (GenericSelect.sparseExceptionFlagBits bits target) ->
      b = false := by
  intro b hmem
  unfold GenericSelect.sparseExceptionFlagBits at hmem
  rcases List.mem_map.mp hmem with ⟨slot, _hslot, hb⟩
  rw [← hb]
  exact packedLocalIsSparseException_false_of_unit_stride bits target slot hstride

/--
**The sparse relative table is empty at unit stride.** This is the statement that
dissolves `DD-20260804-022`: the one source whose word count was not a function of
the input size and the header has no entries at all.
-/
theorem packedSparseExceptionEntries_nil_of_unit_stride
    (bits : List Bool) (target : Bool)
    (hstride : GenericSelect.localStride bits.length = 1) :
    GenericSelect.sparseExceptionRelativeEntries bits target = [] := by
  have hlen := GenericSelect.sparseExceptionRelativeEntries_length bits target
  have hzero :
      RMQ.Succinct.rankPrefix true
        (GenericSelect.sparseExceptionFlagBits bits target)
        (GenericSelect.localSlotCount bits target) = 0 :=
    packedRankPrefix_true_eq_zero_of_all_false _ _
      (packedSparseFlagBits_allFalse_of_unit_stride bits target hstride)
  rw [hzero, Nat.zero_mul] at hlen
  exact List.eq_nil_of_length_eq_zero hlen

/--
**The sparse relative source answers nothing at unit stride.** The store's word
array for it is empty, so the capacity over-approximation of `DD-20260804-022` is
never exercised: there is no index at which the packed read and the store can
disagree.
-/
theorem packedSparseRelativeWords_none_of_unit_stride
    (shape : CartesianShape) (index : Nat)
    (hstride : GenericSelect.localStride shape.bpCode.length = 1) :
    (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape
      .selectSparseRelative)[index]? = none := by
  have hnil :=
    packedSparseExceptionEntries_nil_of_unit_stride shape.bpCode false hstride
  show
    (GenericSelect.sparseExceptionRelativeTable shape.bpCode
      false).store.words[index]? = none
  have hzero :
      (GenericSelect.sparseExceptionRelativeEntries shape.bpCode false).length = 0 := by
    rw [hnil]
    rfl
  rw [packedFixedWidthTable_getElem?]
  exact packedWordSlice_of_le (by omega)

end PackedCellProbe

end SuccinctFinal

end RMQ
