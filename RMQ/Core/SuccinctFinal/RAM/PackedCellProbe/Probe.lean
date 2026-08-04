import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.Address

/-!
# The physical probe plan

This module works towards `EG-CP` rows `FG-05-PACKED-MEMORY`,
`FG-08-PHYSICAL-LOWERING` and `FG-09-TOTALITY-AND-CAP`.

A logical read asks for `width` bits starting at bit `bit` of the packed memory.
`packedProbePlan` turns that request into the list of cell addresses that must
actually be fetched. It issues **one** cell when the request stays inside the
cell that contains its first bit, and **two** when it crosses a cell boundary.
A zero-width request issues none.

The earlier draft of this development always issued the pair
`(bit / w, bit / w + 1)`. That is wrong at the end of the memory: the successor
address is not allocated, and the only reason the slice theorem still held was
that the total cell accessor returns the empty list outside the allocation. The
point of a cell-probe claim is that an issued address is a real address, so this
module fetches through `List.getElem?` and proves the fetch returns `some`.
`packedMemory_getElem?_cellCount` records that the address the old plan would
have issued at the end of the memory is genuinely absent, so the repair is not
cosmetic.

Both branches are reachable: `packedProbePlan_of_offset` exhibits the one-cell
plan and `packedProbePlan_of_crossing` the two-cell plan, so the condition is
not secretly constant.

## What this module does not establish

* There is still no controller: these are the probes a read lowers to, not
  probes emitted by an execution. Relating them to an actual run is the
  remaining `FG-07`/`FG-08` obligation.
-/

namespace RMQ
namespace SuccinctFinal
namespace PackedCellProbe

open RMQ.Cartesian

/-! ### Cancelling a common factor -/

private theorem packedLtOfMulLtMul {a b w : Nat} (h : a * w < b * w) : a < b := by
  by_cases hab : a < b
  · exact hab
  · have hba : b <= a := by omega
    have hmul := Nat.mul_le_mul_right w hba
    omega

/-! ### Cells outside the allocation are absent -/

/--
**The successor of the last cell is not allocated.**

This is the fact the unconditional two-cell plan ignored. Fetching that address
through `List.getElem?` fails; only a total accessor makes it look harmless.
-/
theorem packedMemory_getElem?_cellCount (shape : CartesianShape) :
    (packedMemory shape)[packedCellCount shape.size]? = none := by
  rw [List.getElem?_eq_none]
  rw [packedMemory_length]
  omega

/-- Every allocated cell is exactly one width, addressed by index. -/
theorem packedCellAt_length
    (shape : CartesianShape) {i : Nat}
    (hi : i < packedCellCount shape.size) :
    (packedCellAt shape i).length = packedCellWidth shape.size := by
  have hpad := packedPaddedBits_length shape
  have hbound :
      i * packedCellWidth shape.size + packedCellWidth shape.size <=
        packedAllocatedBits shape.size := by
    unfold packedAllocatedBits
    have hstep : i + 1 <= packedCellCount shape.size := hi
    calc
      i * packedCellWidth shape.size + packedCellWidth shape.size
          = (i + 1) * packedCellWidth shape.size := by
            rw [Nat.add_mul, Nat.one_mul]
      _ <= packedCellCount shape.size * packedCellWidth shape.size :=
          Nat.mul_le_mul_right _ hstep
  unfold packedCellAt
  rw [List.length_take, List.length_drop]
  omega

/-! ### The plan -/

/--
The physical cells one logical read must fetch.

* A zero-width request issues no probe.
* A request that stays inside the cell holding its first bit issues that one
  cell.
* A request that crosses the boundary issues that cell and its successor.

The width hypothesis `width <= packedCellWidth n` used by the theorems below
makes the third case the only crossing possibility: a request no wider than a
cell can straddle at most one boundary.
-/
def packedProbePlan (n bit width : Nat) : List Nat :=
  if width = 0 then
    []
  else if bit % packedCellWidth n + width <= packedCellWidth n then
    [bit / packedCellWidth n]
  else
    [bit / packedCellWidth n, bit / packedCellWidth n + 1]

/--
The charged number of physical probes: the length of the plan actually issued,
not a separately declared constant.
-/
def packedProbeCount (n bit width : Nat) : Nat :=
  (packedProbePlan n bit width).length

theorem packedProbeCount_eq_zero (n bit : Nat) :
    packedProbeCount n bit 0 = 0 := by
  simp [packedProbeCount, packedProbePlan]

theorem packedProbeCount_eq_one
    {n bit width : Nat} (hpos : 0 < width)
    (hin : bit % packedCellWidth n + width <= packedCellWidth n) :
    packedProbeCount n bit width = 1 := by
  have hne : Not (width = 0) := by omega
  simp [packedProbeCount, packedProbePlan, hne, hin]

theorem packedProbeCount_eq_two
    {n bit width : Nat}
    (hcross : Not (bit % packedCellWidth n + width <= packedCellWidth n)) :
    packedProbeCount n bit width = 2 := by
  have hmod : bit % packedCellWidth n < packedCellWidth n :=
    Nat.mod_lt _ (packedCellWidth_pos n)
  have hne : Not (width = 0) := by omega
  simp [packedProbeCount, packedProbePlan, hne, hcross]

/-- **The probe cap for one logical read.** Never more than two cells. -/
theorem packedProbeCount_le_two (n bit width : Nat) :
    packedProbeCount n bit width <= 2 := by
  unfold packedProbeCount packedProbePlan
  split
  · simp
  · split <;> simp

/-- A request of positive width issues at least one probe. -/
theorem packedProbeCount_pos
    {n bit width : Nat} (hpos : 0 < width) :
    0 < packedProbeCount n bit width := by
  have hne : Not (width = 0) := by omega
  unfold packedProbeCount packedProbePlan
  rw [if_neg hne]
  split <;> simp

/--
**Coverage.** After skipping the in-cell offset of the first probe, the fetched
window still contains at least `width` bits, so the requested range is inside
the cells actually issued.
-/
theorem packedProbe_covers_range
    (n bit width : Nat) (hwidth : width <= packedCellWidth n) :
    width <=
      packedProbeCount n bit width * packedCellWidth n -
        bit % packedCellWidth n := by
  have hw : 0 < packedCellWidth n := packedCellWidth_pos n
  have hmod : bit % packedCellWidth n < packedCellWidth n :=
    Nat.mod_lt _ hw
  by_cases hzero : width = 0
  · omega
  · by_cases hin : bit % packedCellWidth n + width <= packedCellWidth n
    · rw [packedProbeCount_eq_one (by omega) hin]
      omega
    · rw [packedProbeCount_eq_two hin]
      omega

/-! ### Both branches are reachable -/

/--
A read whose first bit sits at `offset` inside cell `base`, and which fits in
that cell, issues exactly the one probe `base`.
-/
theorem packedProbePlan_of_offset
    (n base offset width : Nat)
    (hpos : 0 < width)
    (hin : offset + width <= packedCellWidth n) :
    packedProbePlan n (offset + base * packedCellWidth n) width = [base] := by
  have hw : 0 < packedCellWidth n := packedCellWidth_pos n
  have hoff : offset < packedCellWidth n := by omega
  have hdiv :
      (offset + base * packedCellWidth n) / packedCellWidth n = base := by
    rw [Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt hoff, Nat.zero_add]
  have hmod :
      (offset + base * packedCellWidth n) % packedCellWidth n = offset := by
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hoff]
  have hzero : Not (width = 0) := by omega
  unfold packedProbePlan
  rw [hdiv, hmod]
  simp [hzero, hin]

/--
A read whose first bit sits at `offset` inside cell `base` and which runs past
the end of that cell issues exactly the two probes `base` and `base + 1`.
-/
theorem packedProbePlan_of_crossing
    (n base offset width : Nat)
    (hoff : offset < packedCellWidth n)
    (hcross : packedCellWidth n < offset + width) :
    packedProbePlan n (offset + base * packedCellWidth n) width =
      [base, base + 1] := by
  have hw : 0 < packedCellWidth n := packedCellWidth_pos n
  have hdiv :
      (offset + base * packedCellWidth n) / packedCellWidth n = base := by
    rw [Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt hoff, Nat.zero_add]
  have hmod :
      (offset + base * packedCellWidth n) % packedCellWidth n = offset := by
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hoff]
  have hzero : Not (width = 0) := by omega
  have hnotin : Not (offset + width <= packedCellWidth n) := by omega
  unfold packedProbePlan
  rw [hdiv, hmod]
  simp [hzero, hnotin]

/-! ### Issuing the plan against a memory -/

/--
One physical probe. `none` means the address is not allocated; this accessor
deliberately fails outside the allocation so that an out-of-range address cannot
be mistaken for an empty slice.
-/
def packedProbeCell (memory : List (List Bool)) (addr : Nat) :
    Option (List Bool) :=
  memory[addr]?

/--
Issue a whole plan. The result is `some` only when **every** issued address is
allocated.
-/
def packedFetch (memory : List (List Bool)) :
    List Nat -> Option (List (List Bool))
  | [] => some []
  | addr :: rest =>
      match packedProbeCell memory addr, packedFetch memory rest with
      | some cell, some cells => some (cell :: cells)
      | _, _ => none

/-- The concatenated reply window of a plan issued against the packed memory. -/
def packedProbeWindow (shape : CartesianShape) (plan : List Nat) : List Bool :=
  (plan.map (packedCellAt shape)).flatten

/--
**Every issued address is allocated.** When the plan stays inside the cell
count, the fetch succeeds and returns exactly the addressed cells.
-/
theorem packedFetch_packedMemory
    (shape : CartesianShape) (plan : List Nat)
    (hplan : forall addr, addr ∈ plan -> addr < packedCellCount shape.size) :
    packedFetch (packedMemory shape) plan =
      some (plan.map (packedCellAt shape)) := by
  induction plan with
  | nil => rfl
  | cons addr rest ih =>
      have haddr : addr < packedCellCount shape.size := hplan addr (by simp)
      have hrest :
          forall a, a ∈ rest -> a < packedCellCount shape.size := by
        intro a ha
        exact hplan a (List.mem_cons_of_mem _ ha)
      have hcell :
          packedProbeCell (packedMemory shape) addr =
            some (packedCellAt shape addr) :=
        packedMemory_getElem? shape haddr
      simp [packedFetch, hcell, ih hrest]

/--
**Plan addresses are allocated.** Every cell the plan issues is a real cell of
`packedMemory`, given only that the requested range fits the allocation.
-/
theorem packedProbePlan_lt_cellCount
    {n bit width addr : Nat}
    (hfit : bit + width <= packedAllocatedBits n)
    (hmem : addr ∈ packedProbePlan n bit width) :
    addr < packedCellCount n := by
  have hw : 0 < packedCellWidth n := packedCellWidth_pos n
  have hmod : bit % packedCellWidth n < packedCellWidth n := Nat.mod_lt _ hw
  have hsplit :
      bit % packedCellWidth n +
          packedCellWidth n * (bit / packedCellWidth n) = bit :=
    Nat.mod_add_div bit (packedCellWidth n)
  have hcomm :
      packedCellWidth n * (bit / packedCellWidth n) =
        bit / packedCellWidth n * packedCellWidth n :=
    Nat.mul_comm _ _
  have halloc :
      packedAllocatedBits n = packedCellCount n * packedCellWidth n := rfl
  by_cases hzero : width = 0
  · simp [packedProbePlan, hzero] at hmem
  · by_cases hin : bit % packedCellWidth n + width <= packedCellWidth n
    · have heq : addr = bit / packedCellWidth n := by
        simpa [packedProbePlan, hzero, hin] using hmem
      have hlt :
          bit / packedCellWidth n * packedCellWidth n <
            packedCellCount n * packedCellWidth n := by omega
      have := packedLtOfMulLtMul hlt
      omega
    · have hstep :
          (bit / packedCellWidth n + 1) * packedCellWidth n =
            bit / packedCellWidth n * packedCellWidth n + packedCellWidth n := by
        rw [Nat.add_mul, Nat.one_mul]
      have hlt :
          (bit / packedCellWidth n + 1) * packedCellWidth n <
            packedCellCount n * packedCellWidth n := by omega
      have hsucc : bit / packedCellWidth n + 1 < packedCellCount n :=
        packedLtOfMulLtMul hlt
      have hcases :
          addr = bit / packedCellWidth n ∨
            addr = bit / packedCellWidth n + 1 := by
        simpa [packedProbePlan, hzero, hin] using hmem
      rcases hcases with heq | heq <;> omega

/-- The fetch of a fitted plan succeeds. -/
theorem packedFetch_plan
    (shape : CartesianShape) {bit width : Nat}
    (hfit : bit + width <= packedAllocatedBits shape.size) :
    packedFetch (packedMemory shape) (packedProbePlan shape.size bit width) =
      some ((packedProbePlan shape.size bit width).map (packedCellAt shape)) :=
  packedFetch_packedMemory shape _ fun _ hmem =>
    packedProbePlan_lt_cellCount hfit hmem

/-- The fetched window is exactly one full cell per issued probe. -/
theorem packedProbeWindow_length
    (shape : CartesianShape) {bit width : Nat}
    (hfit : bit + width <= packedAllocatedBits shape.size) :
    (packedProbeWindow shape (packedProbePlan shape.size bit width)).length =
      packedProbeCount shape.size bit width * packedCellWidth shape.size := by
  by_cases hzero : width = 0
  · simp [packedProbeWindow, packedProbeCount, packedProbePlan, hzero]
  · by_cases hin :
        bit % packedCellWidth shape.size + width <= packedCellWidth shape.size
    · have hplan :
          packedProbePlan shape.size bit width =
            [bit / packedCellWidth shape.size] := by
        simp [packedProbePlan, hzero, hin]
      have hmem0 :
          bit / packedCellWidth shape.size ∈
            packedProbePlan shape.size bit width := by
        rw [hplan]; simp
      have h0 :=
        packedCellAt_length shape (packedProbePlan_lt_cellCount hfit hmem0)
      simp [packedProbeWindow, packedProbeCount, hplan, h0]
    · have hplan :
          packedProbePlan shape.size bit width =
            [bit / packedCellWidth shape.size,
              bit / packedCellWidth shape.size + 1] := by
        simp [packedProbePlan, hzero, hin]
      have hmem0 :
          bit / packedCellWidth shape.size ∈
            packedProbePlan shape.size bit width := by
        rw [hplan]; simp
      have hmem1 :
          bit / packedCellWidth shape.size + 1 ∈
            packedProbePlan shape.size bit width := by
        rw [hplan]; simp
      have h0 :=
        packedCellAt_length shape (packedProbePlan_lt_cellCount hfit hmem0)
      have h1 :=
        packedCellAt_length shape (packedProbePlan_lt_cellCount hfit hmem1)
      simp [packedProbeWindow, packedProbeCount, hplan, h0, h1]
      omega

/-! ### Decoding -/

/--
Decode a reply window: skip the in-cell offset of the first probe, keep the
requested width. The controller applies this to the words it received, not to
the memory.
-/
def packedDecodeSpan (n bit width : Nat) (cells : List (List Bool)) : List Bool :=
  (cells.flatten.drop (bit % packedCellWidth n)).take width

/--
**Decoding is correct.** The fetched cells decode to exactly the requested
window of the packed bit string.

This is the statement that fails for a plan issuing an unallocated address:
there the fetch is `none`, so no decoding claim is available at all.
-/
theorem packedProbePlan_decode
    (shape : CartesianShape) {bit width : Nat}
    (hwidth : width <= packedCellWidth shape.size)
    (hfit : bit + width <= packedAllocatedBits shape.size) :
    (packedFetch (packedMemory shape)
          (packedProbePlan shape.size bit width)).map
        (packedDecodeSpan shape.size bit width) =
      some (((packedPaddedBits shape).drop bit).take width) := by
  have hw : 0 < packedCellWidth shape.size := packedCellWidth_pos shape.size
  have hmod : bit % packedCellWidth shape.size < packedCellWidth shape.size :=
    Nat.mod_lt _ hw
  have hsplit :
      bit % packedCellWidth shape.size +
          packedCellWidth shape.size * (bit / packedCellWidth shape.size) =
        bit :=
    Nat.mod_add_div bit (packedCellWidth shape.size)
  have hcomm :
      packedCellWidth shape.size * (bit / packedCellWidth shape.size) =
        bit / packedCellWidth shape.size * packedCellWidth shape.size :=
    Nat.mul_comm _ _
  rw [packedFetch_plan shape hfit, Option.map_some]
  congr 1
  unfold packedDecodeSpan
  by_cases hzero : width = 0
  · simp [packedProbePlan, hzero]
  · by_cases hin :
        bit % packedCellWidth shape.size + width <= packedCellWidth shape.size
    · have hplan :
          packedProbePlan shape.size bit width =
            [bit / packedCellWidth shape.size] := by
        simp [packedProbePlan, hzero, hin]
      rw [hplan]
      simp only [List.map_cons, List.map_nil, List.flatten_cons,
        List.flatten_nil, List.append_nil]
      unfold packedCellAt
      rw [List.drop_take, List.take_take, List.drop_drop]
      have hidx :
          bit / packedCellWidth shape.size * packedCellWidth shape.size +
              bit % packedCellWidth shape.size = bit := by omega
      have hmin :
          min width
              (packedCellWidth shape.size - bit % packedCellWidth shape.size) =
            width := by omega
      rw [hidx, hmin]
    · have hplan :
          packedProbePlan shape.size bit width =
            [bit / packedCellWidth shape.size,
              bit / packedCellWidth shape.size + 1] := by
        simp [packedProbePlan, hzero, hin]
      rw [hplan]
      simp only [List.map_cons, List.map_nil, List.flatten_cons,
        List.flatten_nil, List.append_nil]
      exact (packedSpan_from_two_cells shape bit width hwidth).symm

/-! ### The boundary case the old plan got wrong -/

/--
**A read contained in the final allocated cell.** It issues exactly one probe,
that probe is the last allocated cell, and the fetch succeeds.

Under the unconditional two-cell plan the second issued address would have been
`packedCellCount shape.size`, which `packedMemory_getElem?_cellCount` shows is
absent, so the fetch would have returned `none`.
-/
theorem packedProbe_final_cell
    (shape : CartesianShape) {offset width : Nat}
    (hpos : 0 < width)
    (hin : offset + width <= packedCellWidth shape.size) :
    packedProbePlan shape.size
        (offset +
          (packedCellCount shape.size - 1) * packedCellWidth shape.size)
        width =
      [packedCellCount shape.size - 1] /\
    packedFetch (packedMemory shape)
        (packedProbePlan shape.size
          (offset +
            (packedCellCount shape.size - 1) * packedCellWidth shape.size)
          width) =
      some [packedCellAt shape (packedCellCount shape.size - 1)] := by
  have hcount : 0 < packedCellCount shape.size := by
    unfold packedCellCount
    omega
  have hplan :=
    packedProbePlan_of_offset shape.size (packedCellCount shape.size - 1)
      offset width hpos hin
  refine ⟨hplan, ?_⟩
  rw [hplan]
  rw [packedFetch_packedMemory shape [packedCellCount shape.size - 1]
    (by
      intro addr hmem
      have heq : addr = packedCellCount shape.size - 1 := by simpa using hmem
      omega)]
  simp

/-! ### Reads of one typed source -/

/-- The physical probe plan of one fixed-width read of one typed source. -/
def packedSourceProbePlan (n longCount : Nat)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
    (index width : Nat) : List Nat :=
  packedProbePlan n (packedBitAddress n longCount source index width) width

/-- The charged probe count of one such read. -/
def packedSourceProbeCount (n longCount : Nat)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
    (index width : Nat) : Nat :=
  packedProbeCount n (packedBitAddress n longCount source index width) width

theorem packedSourceProbeCount_le_two (n longCount : Nat)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
    (index width : Nat) :
    packedSourceProbeCount n longCount source index width <= 2 :=
  packedProbeCount_le_two _ _ _

/--
**Decoding equals the canonical packed slice.** The cells issued for one typed
source read decode to exactly the corresponding slice of the `FG-01` payload
object.

The address is computed by `packedBitAddress`, whose arguments are the input
size, the decoded long count, the typed source, the index and the width. No
shape is consulted.
-/
theorem packedSourceRead_decode
    (shape : CartesianShape)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
    (index width : Nat)
    (hwidth : width <= packedCellWidth shape.size)
    (hfit :
      concreteBPNativeSuccinctRMQFlatPayloadSourceFlatOffset shape source +
          index * width + width <=
        packedPayloadLength shape.size) :
    (packedFetch (packedMemory shape)
          (packedSourceProbePlan shape.size (longCount shape) source index
            width)).map
        (packedDecodeSpan shape.size
          (packedBitAddress shape.size (longCount shape) source index width)
          width) =
      some
        (((packedPayloadBits shape).drop
            (concreteBPNativeSuccinctRMQFlatPayloadSourceFlatOffset shape source +
              index * width)).take width) := by
  have hoff := packedSourceFlatOffset_eq shape source
  have hserial := packedSerialized_le_allocated shape.size
  have haddr :
      packedBitAddress shape.size (longCount shape) source index width =
        packedCellWidth shape.size +
          (concreteBPNativeSuccinctRMQFlatPayloadSourceFlatOffset shape source +
            index * width) := by
    unfold packedBitAddress
    omega
  have hfitalloc :
      packedBitAddress shape.size (longCount shape) source index width + width <=
        packedAllocatedBits shape.size := by
    rw [haddr]
    omega
  have hdecode :=
    packedProbePlan_decode shape
      (bit := packedBitAddress shape.size (longCount shape) source index width)
      (width := width) hwidth hfitalloc
  have hslice :=
    packedPayloadSlice shape
      (concreteBPNativeSuccinctRMQFlatPayloadSourceFlatOffset shape source +
        index * width)
      width (by omega)
  unfold packedSourceProbePlan
  rw [hdecode, haddr, hslice]

end PackedCellProbe
end SuccinctFinal
end RMQ
