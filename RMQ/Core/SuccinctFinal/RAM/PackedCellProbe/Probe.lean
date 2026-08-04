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

/-! ### Logical read addresses are typed without a shape

A logical read of the flat payload store is a pair `(segment, index)`. The
segment-to-source map is already shape-free — its type mentions only `Nat` and
the closed source inductive — so the whole address side of a read can be typed
and lowered by a definition a controller could evaluate.

The width is still an explicit argument here. Deriving it from `(n, longCount,
segment)` is the next leaf and is **not** claimed: see the result report.
-/

/--
The logical-to-typed-source map used by the flat payload read store, named at
the packed layer.
-/
def packedSegmentSource? :
    Nat -> Option ConcreteBPNativeSuccinctRMQFlatPayloadSource :=
  concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?

/-- The physical probe plan of one logical read address of a given width. -/
def packedLogicalProbePlan (n longCount segment index width : Nat) : List Nat :=
  match packedSegmentSource? segment with
  | some source => packedSourceProbePlan n longCount source index width
  | none => []

/-- A logical read never issues more than two physical probes. -/
theorem packedLogicalProbePlan_length_le_two
    (n longCount segment index width : Nat) :
    (packedLogicalProbePlan n longCount segment index width).length <= 2 := by
  unfold packedLogicalProbePlan
  cases packedSegmentSource? segment with
  | none => simp
  | some source => exact packedProbeCount_le_two _ _ _

/--
Decoding a logical read: the cells issued for `(segment, index)` at width
`width` decode to exactly the canonical payload slice of the source that segment
names.
-/
theorem packedLogicalRead_decode
    (shape : CartesianShape) {segment : Nat}
    {source : ConcreteBPNativeSuccinctRMQFlatPayloadSource}
    (index width : Nat)
    (hsource : packedSegmentSource? segment = some source)
    (hwidth : width <= packedCellWidth shape.size)
    (hfit :
      concreteBPNativeSuccinctRMQFlatPayloadSourceFlatOffset shape source +
          index * width + width <=
        packedPayloadLength shape.size) :
    (packedFetch (packedMemory shape)
          (packedLogicalProbePlan shape.size (longCount shape) segment index
            width)).map
        (packedDecodeSpan shape.size
          (packedBitAddress shape.size (longCount shape) source index width)
          width) =
      some
        (((packedPayloadBits shape).drop
            (concreteBPNativeSuccinctRMQFlatPayloadSourceFlatOffset shape source +
              index * width)).take width) := by
  unfold packedLogicalProbePlan
  rw [hsource]
  exact packedSourceRead_decode shape source index width hwidth hfit

/-! ### The BP code: one source lowered completely

`packedBitAddress` multiplies the index by the read width, which silently assumes
that a source's stride and its read width coincide. They do not for a chunked bit
source: the BP code is cut into `machineWordBits (2n)`-bit words, and the last
word is short whenever `2n` is not a multiple of that width. Reading the last
word at full width would pull bits belonging to the next component.

`packedStridedBitAddress` separates the two. The BP code is then lowered
completely: the address, the stride and the exact read width are all functions of
`n` and the index alone, and the decoded bits are the word the flat payload store
would have returned.
-/

/--
The bit address of entry `index` of a source read at a fixed stride, with the
stride and the read width kept separate.
-/
def packedStridedBitAddress (n longCount : Nat)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
    (index stride : Nat) : Nat :=
  packedCellWidth n + packedSourceFlatOffset n longCount source + index * stride

/-- The uniform-width address is the strided address with stride equal to width. -/
theorem packedBitAddress_eq_strided (n longCount : Nat)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
    (index width : Nat) :
    packedBitAddress n longCount source index width =
      packedStridedBitAddress n longCount source index width :=
  rfl

/-- The BP code's machine word width at input size `n`. -/
def packedBpCodeWordWidth (n : Nat) : Nat :=
  SuccinctRank.machineWordBits (2 * n)

/--
The exact number of bits BP-code word `index` carries: a full width, except in
the final word, which is short whenever `2 * n` is not a multiple of the width.
-/
def packedBpCodeReadWidth (n index : Nat) : Nat :=
  min (packedBpCodeWordWidth n) (2 * n - index * packedBpCodeWordWidth n)

theorem packedBpCodeWordWidth_pos (n : Nat) : 0 < packedBpCodeWordWidth n :=
  SuccinctRank.machineWordBits_pos _

/-- A BP-code word fits one packed cell. -/
theorem packedBpCodeWordWidth_le_cellWidth (n : Nat) :
    packedBpCodeWordWidth n <= packedCellWidth n := by
  unfold packedBpCodeWordWidth packedCellWidth
  refine SuccinctRank.machineWordBits_mono_le ?_
  unfold packedPayloadLength
  omega

theorem packedBpCodeReadWidth_le (n index : Nat) :
    packedBpCodeReadWidth n index <= packedBpCodeWordWidth n := by
  unfold packedBpCodeReadWidth
  omega

/-- The BP code starts the canonical payload, so its flat offset is zero. -/
theorem packedBpCode_flatOffset (n longCount : Nat) :
    packedSourceFlatOffset n longCount
      ConcreteBPNativeSuccinctRMQFlatPayloadSource.bpCode = 0 :=
  rfl

private theorem take_eq_take_min_length {α : Type} (s : List α) (a : Nat) :
    s.take a = s.take (min a s.length) := by
  by_cases h : a <= s.length
  · rw [Nat.min_eq_left h]
  · have hlen : s.length <= a := by omega
    rw [Nat.min_eq_right hlen, List.take_length, List.take_of_length_le hlen]

/--
A BP-code word exists only at an index whose strided offset is inside the code.
-/
theorem packedBpCodeWord_index_lt
    (shape : CartesianShape) {index : Nat} {word : List Bool}
    (hget :
      (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape
        ConcreteBPNativeSuccinctRMQFlatPayloadSource.bpCode)[index]? =
        some word) :
    index * packedBpCodeWordWidth shape.size < 2 * shape.size := by
  have hbp := CartesianShape.bpCode_length shape
  by_cases hlt : index * packedBpCodeWordWidth shape.size < 2 * shape.size
  · exact hlt
  · exfalso
    have hle :
        shape.bpCode.length <=
          index * SuccinctRank.machineWordBits shape.bpCode.length := by
      unfold packedBpCodeWordWidth at hlt
      rw [hbp]
      omega
    have hnone :=
      SuccinctSpace.chunkPayloadWords_get?_none_of_length_le_mul
        (wordSize := SuccinctRank.machineWordBits shape.bpCode.length)
        (payload := shape.bpCode) (i := index) hle
    have hlist :
        (SuccinctSpace.chunkPayloadWords
          (SuccinctRank.machineWordBits shape.bpCode.length)
          shape.bpCode)[index]? = some word := by
      simpa [concreteBPNativeSuccinctRMQFlatPayloadSourceWords,
        Array.getElem?_toList] using hget
    rw [hnone] at hlist
    exact Option.noConfusion hlist

/--
Every BP-code word that exists is a slice of the canonical payload at the strided
offset, of exactly the read width.
-/
theorem packedBpCodeWord_eq
    (shape : CartesianShape) {index : Nat} {word : List Bool}
    (hget :
      (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape
        ConcreteBPNativeSuccinctRMQFlatPayloadSource.bpCode)[index]? =
        some word) :
    word =
      ((packedPayloadBits shape).drop
          (index * packedBpCodeWordWidth shape.size)).take
        (packedBpCodeReadWidth shape.size index) := by
  have hbp := CartesianShape.bpCode_length shape
  have hwidth :
      SuccinctRank.machineWordBits shape.bpCode.length =
        packedBpCodeWordWidth shape.size := by
    unfold packedBpCodeWordWidth
    rw [hbp]
  have hlist :
      (SuccinctSpace.chunkPayloadWords (packedBpCodeWordWidth shape.size)
        shape.bpCode)[index]? = some word := by
    have := hget
    simp only [concreteBPNativeSuccinctRMQFlatPayloadSourceWords, hwidth] at this
    simpa [Array.getElem?_toList] using this
  have hslice :=
    SuccinctSpace.chunkPayloadWords_get?_eq_take_drop hlist
  have hdroplen :
      (shape.bpCode.drop (index * packedBpCodeWordWidth shape.size)).length =
        2 * shape.size - index * packedBpCodeWordWidth shape.size := by
    rw [List.length_drop, hbp]
  have hcut :
      (shape.bpCode.drop (index * packedBpCodeWordWidth shape.size)).take
          (packedBpCodeWordWidth shape.size) =
        (shape.bpCode.drop (index * packedBpCodeWordWidth shape.size)).take
          (packedBpCodeReadWidth shape.size index) := by
    rw [take_eq_take_min_length
      (shape.bpCode.drop (index * packedBpCodeWordWidth shape.size))
      (packedBpCodeWordWidth shape.size), hdroplen]
    rfl
  have hindex := packedBpCodeWord_index_lt shape hget
  have hfit :
      index * packedBpCodeWordWidth shape.size +
          packedBpCodeReadWidth shape.size index <=
        shape.bpCode.length := by
    unfold packedBpCodeReadWidth
    rw [hbp]
    omega
  have hpayload :
      ((packedPayloadBits shape).drop
            (index * packedBpCodeWordWidth shape.size)).take
          (packedBpCodeReadWidth shape.size index) =
        (shape.bpCode.drop (index * packedBpCodeWordWidth shape.size)).take
          (packedBpCodeReadWidth shape.size index) := by
    have hsplit := packedPayloadBits_eq_bpCode_append_aux shape
    have hjle :
        index * packedBpCodeWordWidth shape.size <= shape.bpCode.length := by
      omega
    have hwle :
        packedBpCodeReadWidth shape.size index <=
          (shape.bpCode.drop
            (index * packedBpCodeWordWidth shape.size)).length := by
      rw [List.length_drop]
      omega
    rw [hsplit, List.drop_append_of_le_length hjle,
      List.take_append_of_le_length hwle]
  rw [hpayload, ← hcut, hslice]

/--
**The BP code lowers completely.** For every shape and every BP-code word that
exists, the physical probe plan at the strided address and the exact read width
fetches successfully and decodes to exactly that word.

Every quantity the plan uses -- the address, the stride and the read width -- is
a function of the input size and the index alone.
-/
theorem packedBpCodeRead_decode
    (shape : CartesianShape) {index : Nat} {word : List Bool}
    (hget :
      (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape
        ConcreteBPNativeSuccinctRMQFlatPayloadSource.bpCode)[index]? =
        some word) :
    (packedFetch (packedMemory shape)
          (packedProbePlan shape.size
            (packedStridedBitAddress shape.size (longCount shape)
              ConcreteBPNativeSuccinctRMQFlatPayloadSource.bpCode index
              (packedBpCodeWordWidth shape.size))
            (packedBpCodeReadWidth shape.size index))).map
        (packedDecodeSpan shape.size
          (packedStridedBitAddress shape.size (longCount shape)
            ConcreteBPNativeSuccinctRMQFlatPayloadSource.bpCode index
            (packedBpCodeWordWidth shape.size))
          (packedBpCodeReadWidth shape.size index)) =
      some word := by
  have hbp := CartesianShape.bpCode_length shape
  have hserial := packedSerialized_le_allocated shape.size
  have hpaylen : 2 * shape.size <= packedPayloadLength shape.size := by
    unfold packedPayloadLength
    omega
  have hexists := packedBpCodeWord_index_lt shape hget
  have hreadle :
      index * packedBpCodeWordWidth shape.size +
          packedBpCodeReadWidth shape.size index <=
        packedPayloadLength shape.size := by
    unfold packedBpCodeReadWidth
    omega
  have haddr :
      packedStridedBitAddress shape.size (longCount shape)
          ConcreteBPNativeSuccinctRMQFlatPayloadSource.bpCode index
          (packedBpCodeWordWidth shape.size) =
        packedCellWidth shape.size +
          index * packedBpCodeWordWidth shape.size := by
    unfold packedStridedBitAddress
    rw [packedBpCode_flatOffset]
    omega
  have hwidthle :
      packedBpCodeReadWidth shape.size index <= packedCellWidth shape.size := by
    have h1 := packedBpCodeReadWidth_le shape.size index
    have h2 := packedBpCodeWordWidth_le_cellWidth shape.size
    omega
  have hfitalloc :
      packedStridedBitAddress shape.size (longCount shape)
            ConcreteBPNativeSuccinctRMQFlatPayloadSource.bpCode index
            (packedBpCodeWordWidth shape.size) +
          packedBpCodeReadWidth shape.size index <=
        packedAllocatedBits shape.size := by
    rw [haddr]
    omega
  rw [packedProbePlan_decode shape hwidthle hfitalloc, haddr,
    packedPayloadSlice shape (index * packedBpCodeWordWidth shape.size)
      (packedBpCodeReadWidth shape.size index) hreadle,
    ← packedBpCodeWord_eq shape hget]

end PackedCellProbe
end SuccinctFinal
end RMQ
