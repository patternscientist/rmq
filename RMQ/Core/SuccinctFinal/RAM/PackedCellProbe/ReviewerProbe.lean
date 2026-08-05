import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReviewerComponentAccess

/-!
# The conditional physical probe over the consumed payload

`Probe.lean` builds the one-or-two-cell probe plan over `packedMemory`, the memory
laid out over the *flat* payload. This module builds the same plan over
`packedReviewerMemory`, the memory laid out over the payload the accepted RMQ
semantics actually consumes -- the fourth step of the `DD-20260804-038` re-target.

The probe *issuing* machinery is not duplicated: `packedProbeCell` and
`packedFetch` already take the memory as an argument, so they are reused verbatim.
What has to be rebuilt is everything that mentions a cell width or a cell count,
because both differ:

* `packedReviewerCellWidth n` is a different width from `packedCellWidth n`, so the
  plan's `bit / w` and `bit % w` are different addresses.
* `packedReviewerCellCount n longCount sparseCount` takes both recovered counts,
  where `packedCellCount n` does not. Every allocation claim therefore carries
  them explicitly rather than deriving them from the size.

That second difference is the `K1` argument made load-bearing: a controller cannot
know which addresses are allocated until it has probed cell zero and decoded the
header.

## What this module does not establish

* Nothing here issues a probe on behalf of a source. The per-source geometry over
  the consumed payload is separate, and the whole-run lowering separate again.
* The plan, count, allocation of every issued address, window length, and decode
  are all-size statements over the actual sparse count.
-/

namespace RMQ

namespace SuccinctFinal

namespace PackedCellProbe

open RMQ.Cartesian

/-! ### Cancelling a common factor -/

private theorem packedReviewerLtOfMulLtMul {a b w : Nat} (h : a * w < b * w) :
    a < b := by
  by_cases hab : a < b
  · exact hab
  · have hba : b <= a := by omega
    have hmul := Nat.mul_le_mul_right w hba
    omega

/-! ### Cells outside the allocation are absent -/

/--
**The successor of the last cell is not allocated.**

The reviewer counterpart of `packedMemory_getElem?_cellCount`, and the reason the
plan below has to be conditional: an unconditional second probe at the end of the
allocation addresses this cell, and fetching it through `List.getElem?` fails. Only
a total accessor would make that look harmless.
-/
theorem packedReviewerMemory_getElem?_cellCount (shape : CartesianShape) :
    (packedReviewerMemory shape)[packedReviewerCellCount shape.size
        (longCount shape) (packedReviewerSparseCount shape)]? = none := by
  rw [List.getElem?_eq_none]
  rw [packedReviewerMemory_length]
  omega

/-- Every allocated cell is exactly one reviewer width, addressed by index. -/
theorem packedReviewerCellAt_length
    (shape : CartesianShape)
    {i : Nat}
    (hi : i < packedReviewerCellCount shape.size (longCount shape)
      (packedReviewerSparseCount shape)) :
    (packedReviewerCellAt shape i).length = packedReviewerCellWidth shape.size := by
  have hpad := packedReviewerPaddedBits_length shape
  have hsucc : i + 1 <= packedReviewerCellCount shape.size (longCount shape)
      (packedReviewerSparseCount shape) := hi
  have hmul := Nat.mul_le_mul_right (packedReviewerCellWidth shape.size) hsucc
  have hexp :
      (i + 1) * packedReviewerCellWidth shape.size =
        i * packedReviewerCellWidth shape.size +
          packedReviewerCellWidth shape.size := by
    rw [Nat.add_mul, Nat.one_mul]
  have halloc :
      packedReviewerCellCount shape.size (longCount shape)
          (packedReviewerSparseCount shape) *
          packedReviewerCellWidth shape.size =
        packedReviewerAllocatedBits shape.size (longCount shape)
          (packedReviewerSparseCount shape) := rfl
  unfold packedReviewerCellAt
  rw [List.length_take, List.length_drop, hpad]
  omega

/-! ### The plan -/

/--
The physical cells one logical read must fetch from the reviewer memory.

* A zero-width request issues no probe.
* A request that stays inside the cell holding its first bit issues that one cell.
* A request that crosses the boundary issues that cell and its successor.

The width hypothesis `width <= packedReviewerCellWidth n` used below makes the
third case the only crossing possibility: a request no wider than a cell can
straddle at most one boundary.
-/
def packedReviewerProbePlan (n bit width : Nat) : List Nat :=
  if width = 0 then
    []
  else if bit % packedReviewerCellWidth n + width <= packedReviewerCellWidth n then
    [bit / packedReviewerCellWidth n]
  else
    [bit / packedReviewerCellWidth n, bit / packedReviewerCellWidth n + 1]

/--
The charged number of physical probes: the length of the plan actually issued, not
a separately declared constant.
-/
def packedReviewerProbeCount (n bit width : Nat) : Nat :=
  (packedReviewerProbePlan n bit width).length

theorem packedReviewerProbeCount_eq_zero (n bit : Nat) :
    packedReviewerProbeCount n bit 0 = 0 := by
  simp [packedReviewerProbeCount, packedReviewerProbePlan]

theorem packedReviewerProbeCount_eq_one
    {n bit width : Nat} (hpos : 0 < width)
    (hin : bit % packedReviewerCellWidth n + width <=
      packedReviewerCellWidth n) :
    packedReviewerProbeCount n bit width = 1 := by
  have hne : Not (width = 0) := by omega
  simp [packedReviewerProbeCount, packedReviewerProbePlan, hne, hin]

theorem packedReviewerProbeCount_eq_two
    {n bit width : Nat}
    (hcross : Not (bit % packedReviewerCellWidth n + width <=
      packedReviewerCellWidth n)) :
    packedReviewerProbeCount n bit width = 2 := by
  have hmod : bit % packedReviewerCellWidth n < packedReviewerCellWidth n :=
    Nat.mod_lt _ (packedReviewerCellWidth_pos n)
  have hne : Not (width = 0) := by omega
  simp [packedReviewerProbeCount, packedReviewerProbePlan, hne, hcross]

/-- **The probe cap for one logical read.** Never more than two cells. -/
theorem packedReviewerProbeCount_le_two (n bit width : Nat) :
    packedReviewerProbeCount n bit width <= 2 := by
  unfold packedReviewerProbeCount packedReviewerProbePlan
  split
  · simp
  · split <;> simp

/-- A request of positive width issues at least one probe. -/
theorem packedReviewerProbeCount_pos
    {n bit width : Nat} (hpos : 0 < width) :
    0 < packedReviewerProbeCount n bit width := by
  have hne : Not (width = 0) := by omega
  unfold packedReviewerProbeCount packedReviewerProbePlan
  rw [if_neg hne]
  split <;> simp

/--
**Coverage.** After skipping the in-cell offset of the first probe, the fetched
window still contains at least `width` bits, so the requested range is inside the
cells actually issued.
-/
theorem packedReviewerProbe_covers_range
    (n bit width : Nat) (hwidth : width <= packedReviewerCellWidth n) :
    width <=
      packedReviewerProbeCount n bit width * packedReviewerCellWidth n -
        bit % packedReviewerCellWidth n := by
  have hw : 0 < packedReviewerCellWidth n := packedReviewerCellWidth_pos n
  have hmod : bit % packedReviewerCellWidth n < packedReviewerCellWidth n :=
    Nat.mod_lt _ hw
  by_cases hzero : width = 0
  · omega
  · by_cases hin :
        bit % packedReviewerCellWidth n + width <= packedReviewerCellWidth n
    · rw [packedReviewerProbeCount_eq_one (by omega) hin]
      omega
    · rw [packedReviewerProbeCount_eq_two hin]
      omega

/-! ### Both branches are reachable -/

/--
A read whose first bit sits at `offset` inside cell `base`, and which fits in that
cell, issues exactly the one probe `base`.
-/
theorem packedReviewerProbePlan_of_offset
    (n base offset width : Nat)
    (hpos : 0 < width)
    (hin : offset + width <= packedReviewerCellWidth n) :
    packedReviewerProbePlan n (offset + base * packedReviewerCellWidth n) width =
      [base] := by
  have hw : 0 < packedReviewerCellWidth n := packedReviewerCellWidth_pos n
  have hoff : offset < packedReviewerCellWidth n := by omega
  have hdiv :
      (offset + base * packedReviewerCellWidth n) /
          packedReviewerCellWidth n = base := by
    rw [Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt hoff, Nat.zero_add]
  have hmod :
      (offset + base * packedReviewerCellWidth n) %
          packedReviewerCellWidth n = offset := by
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hoff]
  have hzero : Not (width = 0) := by omega
  unfold packedReviewerProbePlan
  rw [hdiv, hmod]
  simp [hzero, hin]

/--
A read whose first bit sits at `offset` inside cell `base` and which runs past the
end of that cell issues exactly the two probes `base` and `base + 1`.
-/
theorem packedReviewerProbePlan_of_crossing
    (n base offset width : Nat)
    (hoff : offset < packedReviewerCellWidth n)
    (hcross : packedReviewerCellWidth n < offset + width) :
    packedReviewerProbePlan n (offset + base * packedReviewerCellWidth n) width =
      [base, base + 1] := by
  have hw : 0 < packedReviewerCellWidth n := packedReviewerCellWidth_pos n
  have hdiv :
      (offset + base * packedReviewerCellWidth n) /
          packedReviewerCellWidth n = base := by
    rw [Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt hoff, Nat.zero_add]
  have hmod :
      (offset + base * packedReviewerCellWidth n) %
          packedReviewerCellWidth n = offset := by
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hoff]
  have hzero : Not (width = 0) := by omega
  have hnotin : Not (offset + width <= packedReviewerCellWidth n) := by omega
  unfold packedReviewerProbePlan
  rw [hdiv, hmod]
  simp [hzero, hnotin]

/-! ### Issuing the plan against the reviewer memory

`packedProbeCell` and `packedFetch` are memory-generic and are reused unchanged.
Only the allocation facts are new.
-/

/-- The concatenated reply window of a plan issued against the reviewer memory. -/
def packedReviewerProbeWindow (shape : CartesianShape) (plan : List Nat) :
    List Bool :=
  (plan.map (packedReviewerCellAt shape)).flatten

/--
**Every issued address is allocated.** When the plan stays inside the cell count,
the fetch succeeds and returns exactly the addressed cells.
-/
theorem packedReviewerFetch_memory
    (shape : CartesianShape) (plan : List Nat)
    (hplan : forall addr, addr ∈ plan ->
      addr < packedReviewerCellCount shape.size (longCount shape)
        (packedReviewerSparseCount shape)) :
    packedFetch (packedReviewerMemory shape) plan =
      some (plan.map (packedReviewerCellAt shape)) := by
  induction plan with
  | nil => rfl
  | cons addr rest ih =>
      have haddr :
          addr < packedReviewerCellCount shape.size (longCount shape)
            (packedReviewerSparseCount shape) :=
        hplan addr (by simp)
      have hrest :
          forall a, a ∈ rest ->
            a < packedReviewerCellCount shape.size (longCount shape)
              (packedReviewerSparseCount shape) := by
        intro a ha
        exact hplan a (List.mem_cons_of_mem _ ha)
      have hcell :
          packedProbeCell (packedReviewerMemory shape) addr =
            some (packedReviewerCellAt shape addr) :=
        packedReviewerMemory_getElem? shape haddr
      simp [packedFetch, hcell, ih hrest]

/--
**Plan addresses are allocated.** Every cell the plan issues is a real cell of
`packedReviewerMemory`, given only that the requested range fits the allocation.

The `longCount` and `sparseCount` arguments are where this differs from its flat
counterpart: the allocation depends on both recovered scalars.
-/
theorem packedReviewerProbePlan_lt_cellCount
    {n longCount sparseCount bit width addr : Nat}
    (hfit : bit + width <= packedReviewerAllocatedBits n longCount sparseCount)
    (hmem : addr ∈ packedReviewerProbePlan n bit width) :
    addr < packedReviewerCellCount n longCount sparseCount := by
  have hw : 0 < packedReviewerCellWidth n := packedReviewerCellWidth_pos n
  have hmod : bit % packedReviewerCellWidth n < packedReviewerCellWidth n :=
    Nat.mod_lt _ hw
  have hsplit :
      bit % packedReviewerCellWidth n +
          packedReviewerCellWidth n * (bit / packedReviewerCellWidth n) = bit :=
    Nat.mod_add_div bit (packedReviewerCellWidth n)
  have hcomm :
      packedReviewerCellWidth n * (bit / packedReviewerCellWidth n) =
        bit / packedReviewerCellWidth n * packedReviewerCellWidth n :=
    Nat.mul_comm _ _
  have halloc :
      packedReviewerAllocatedBits n longCount sparseCount =
        packedReviewerCellCount n longCount sparseCount *
          packedReviewerCellWidth n := rfl
  by_cases hzero : width = 0
  · simp [packedReviewerProbePlan, hzero] at hmem
  · by_cases hin :
        bit % packedReviewerCellWidth n + width <= packedReviewerCellWidth n
    · have heq : addr = bit / packedReviewerCellWidth n := by
        simpa [packedReviewerProbePlan, hzero, hin] using hmem
      have hlt :
          bit / packedReviewerCellWidth n * packedReviewerCellWidth n <
            packedReviewerCellCount n longCount sparseCount *
              packedReviewerCellWidth n := by omega
      have := packedReviewerLtOfMulLtMul hlt
      omega
    · have hstep :
          (bit / packedReviewerCellWidth n + 1) * packedReviewerCellWidth n =
            bit / packedReviewerCellWidth n * packedReviewerCellWidth n +
              packedReviewerCellWidth n := by
        rw [Nat.add_mul, Nat.one_mul]
      have hlt :
          (bit / packedReviewerCellWidth n + 1) * packedReviewerCellWidth n <
            packedReviewerCellCount n longCount sparseCount *
              packedReviewerCellWidth n := by omega
      have hsucc :
          bit / packedReviewerCellWidth n + 1 <
            packedReviewerCellCount n longCount sparseCount :=
        packedReviewerLtOfMulLtMul hlt
      have hcases :
          addr = bit / packedReviewerCellWidth n ∨
            addr = bit / packedReviewerCellWidth n + 1 := by
        simpa [packedReviewerProbePlan, hzero, hin] using hmem
      rcases hcases with heq | heq <;> omega

/-- The fetch of a fitted plan succeeds. -/
theorem packedReviewerFetch_plan
    (shape : CartesianShape) {bit width : Nat}
    (hfit : bit + width <=
      packedReviewerAllocatedBits shape.size (longCount shape)
        (packedReviewerSparseCount shape)) :
    packedFetch (packedReviewerMemory shape)
        (packedReviewerProbePlan shape.size bit width) =
      some ((packedReviewerProbePlan shape.size bit width).map
        (packedReviewerCellAt shape)) :=
  packedReviewerFetch_memory shape _ fun _ hmem =>
    packedReviewerProbePlan_lt_cellCount hfit hmem

/-- The fetched window is exactly one full cell per issued probe. -/
theorem packedReviewerProbeWindow_length
    (shape : CartesianShape)
    {bit width : Nat}
    (hfit : bit + width <=
      packedReviewerAllocatedBits shape.size (longCount shape)
        (packedReviewerSparseCount shape)) :
    (packedReviewerProbeWindow shape
        (packedReviewerProbePlan shape.size bit width)).length =
      packedReviewerProbeCount shape.size bit width *
        packedReviewerCellWidth shape.size := by
  by_cases hzero : width = 0
  · simp [packedReviewerProbeWindow, packedReviewerProbeCount,
      packedReviewerProbePlan, hzero]
  · by_cases hin :
        bit % packedReviewerCellWidth shape.size + width <=
          packedReviewerCellWidth shape.size
    · have hplan :
          packedReviewerProbePlan shape.size bit width =
            [bit / packedReviewerCellWidth shape.size] := by
        simp [packedReviewerProbePlan, hzero, hin]
      have hmem0 :
          bit / packedReviewerCellWidth shape.size ∈
            packedReviewerProbePlan shape.size bit width := by
        rw [hplan]; simp
      have h0 :=
        packedReviewerCellAt_length shape
          (packedReviewerProbePlan_lt_cellCount hfit hmem0)
      simp [packedReviewerProbeWindow, packedReviewerProbeCount, hplan, h0]
    · have hplan :
          packedReviewerProbePlan shape.size bit width =
            [bit / packedReviewerCellWidth shape.size,
              bit / packedReviewerCellWidth shape.size + 1] := by
        simp [packedReviewerProbePlan, hzero, hin]
      have hmem0 :
          bit / packedReviewerCellWidth shape.size ∈
            packedReviewerProbePlan shape.size bit width := by
        rw [hplan]; simp
      have hmem1 :
          bit / packedReviewerCellWidth shape.size + 1 ∈
            packedReviewerProbePlan shape.size bit width := by
        rw [hplan]; simp
      have h0 :=
        packedReviewerCellAt_length shape
          (packedReviewerProbePlan_lt_cellCount hfit hmem0)
      have h1 :=
        packedReviewerCellAt_length shape
          (packedReviewerProbePlan_lt_cellCount hfit hmem1)
      simp [packedReviewerProbeWindow, packedReviewerProbeCount, hplan, h0, h1]
      omega

/-! ### Decoding -/

/--
Decode a reply window: skip the in-cell offset of the first probe, keep the
requested width. The controller applies this to the words it received, not to the
memory.
-/
def packedReviewerDecodeSpan (n bit width : Nat) (cells : List (List Bool)) :
    List Bool :=
  (cells.flatten.drop (bit % packedReviewerCellWidth n)).take width

/--
**Decoding is correct.** The fetched cells decode to exactly the requested window
of the reviewer memory's padded bit string.

This is the statement that fails for a plan issuing an unallocated address: there
the fetch is `none`, so no decoding claim is available at all.
-/
theorem packedReviewerProbePlan_decode
    (shape : CartesianShape) {bit width : Nat}
    (hwidth : width <= packedReviewerCellWidth shape.size)
    (hfit : bit + width <=
      packedReviewerAllocatedBits shape.size (longCount shape)
        (packedReviewerSparseCount shape)) :
    (packedFetch (packedReviewerMemory shape)
          (packedReviewerProbePlan shape.size bit width)).map
        (packedReviewerDecodeSpan shape.size bit width) =
      some (((packedReviewerPaddedBits shape).drop bit).take width) := by
  have hw : 0 < packedReviewerCellWidth shape.size :=
    packedReviewerCellWidth_pos shape.size
  have hmod :
      bit % packedReviewerCellWidth shape.size <
        packedReviewerCellWidth shape.size :=
    Nat.mod_lt _ hw
  have hsplit :
      bit % packedReviewerCellWidth shape.size +
          packedReviewerCellWidth shape.size *
            (bit / packedReviewerCellWidth shape.size) = bit :=
    Nat.mod_add_div bit (packedReviewerCellWidth shape.size)
  have hcomm :
      packedReviewerCellWidth shape.size *
          (bit / packedReviewerCellWidth shape.size) =
        bit / packedReviewerCellWidth shape.size *
          packedReviewerCellWidth shape.size :=
    Nat.mul_comm _ _
  rw [packedReviewerFetch_plan shape hfit, Option.map_some]
  congr 1
  unfold packedReviewerDecodeSpan
  by_cases hzero : width = 0
  · simp [packedReviewerProbePlan, hzero]
  · by_cases hin :
        bit % packedReviewerCellWidth shape.size + width <=
          packedReviewerCellWidth shape.size
    · have hplan :
          packedReviewerProbePlan shape.size bit width =
            [bit / packedReviewerCellWidth shape.size] := by
        simp [packedReviewerProbePlan, hzero, hin]
      rw [hplan]
      simp only [List.map_cons, List.map_nil, List.flatten_cons,
        List.flatten_nil, List.append_nil]
      unfold packedReviewerCellAt
      rw [List.drop_take, List.take_take, List.drop_drop]
      have hidx :
          bit / packedReviewerCellWidth shape.size *
              packedReviewerCellWidth shape.size +
            bit % packedReviewerCellWidth shape.size = bit := by omega
      have hmin :
          min width
              (packedReviewerCellWidth shape.size -
                bit % packedReviewerCellWidth shape.size) = width := by omega
      rw [hidx, hmin]
    · have hplan :
          packedReviewerProbePlan shape.size bit width =
            [bit / packedReviewerCellWidth shape.size,
              bit / packedReviewerCellWidth shape.size + 1] := by
        simp [packedReviewerProbePlan, hzero, hin]
      rw [hplan]
      simp only [List.map_cons, List.map_nil, List.flatten_cons,
        List.flatten_nil, List.append_nil]
      exact (packedReviewerSpan_from_two_cells shape bit width hwidth).symm

/-! ### The boundary case an unconditional plan gets wrong -/

/--
**A read contained in the final allocated cell.** It issues exactly one probe, that
probe is the last allocated cell, and the fetch succeeds.

Under an unconditional two-cell plan the second issued address would have been
`packedReviewerCellCount shape.size (longCount shape)
(packedReviewerSparseCount shape)`, which
`packedReviewerMemory_getElem?_cellCount` shows is absent, so the fetch would have
returned `none`.
-/
theorem packedReviewerProbe_final_cell
    (shape : CartesianShape) {offset width : Nat}
    (hpos : 0 < width)
    (hin : offset + width <= packedReviewerCellWidth shape.size) :
    packedReviewerProbePlan shape.size
        (offset +
          (packedReviewerCellCount shape.size (longCount shape)
              (packedReviewerSparseCount shape) - 1) *
            packedReviewerCellWidth shape.size)
        width =
      [packedReviewerCellCount shape.size (longCount shape)
        (packedReviewerSparseCount shape) - 1] /\
    packedFetch (packedReviewerMemory shape)
        (packedReviewerProbePlan shape.size
          (offset +
            (packedReviewerCellCount shape.size (longCount shape)
                (packedReviewerSparseCount shape) - 1) *
              packedReviewerCellWidth shape.size)
          width) =
      some [packedReviewerCellAt shape
        (packedReviewerCellCount shape.size (longCount shape)
          (packedReviewerSparseCount shape) - 1)] := by
  have hcount : 0 < packedReviewerCellCount shape.size (longCount shape)
      (packedReviewerSparseCount shape) := by
    unfold packedReviewerCellCount
    omega
  have hplan :=
    packedReviewerProbePlan_of_offset shape.size
      (packedReviewerCellCount shape.size (longCount shape)
        (packedReviewerSparseCount shape) - 1) offset width
      hpos hin
  refine ⟨hplan, ?_⟩
  rw [hplan]
  rw [packedReviewerFetch_memory shape
    [packedReviewerCellCount shape.size (longCount shape)
      (packedReviewerSparseCount shape) - 1]
    (by
      intro addr hmem
      have heq :
          addr = packedReviewerCellCount shape.size (longCount shape)
            (packedReviewerSparseCount shape) - 1 := by
        simpa using hmem
      omega)]
  simp

/-! ### The header probe

Every other address over the reviewer memory takes the decoded long count as an
argument. This first probe is still load-bearing, but it is not sufficient by
itself: the controller also obtains `sparseCount` through the charged sparse-rank
prelude before it names the full allocation or the last cell.
-/

/-- The controller's first probe: cell zero, unconditionally. -/
def packedReviewerHeaderProbePlan : List Nat := [0]

/-- The header probe costs exactly one probe. -/
theorem packedReviewerHeaderProbePlan_length :
    packedReviewerHeaderProbePlan.length = 1 := rfl

/-- The header probe is allocated at every size and fetches the header cell. -/
theorem packedReviewerHeaderFetch (shape : CartesianShape) :
    packedFetch (packedReviewerMemory shape) packedReviewerHeaderProbePlan =
      some [packedReviewerHeaderBits shape] := by
  have hzero := packedReviewerMemory_header_cell shape
  simp [packedFetch, packedReviewerHeaderProbePlan, packedProbeCell, hzero]

/--
**The long count comes from a probe.** Fetching cell zero of the reviewer memory
and decoding it with the little-endian codec yields exactly `longCount shape`, at
every size and for every shape, with no size side condition.

Unlike its flat counterpart this is load-bearing rather than decorative: the flat
cell count is size-only, while the reviewer count requires this decoded value and
the separately recovered sparse count.
-/
theorem packedReviewerHeaderProbe_decode (shape : CartesianShape) :
    (packedFetch (packedReviewerMemory shape)
          packedReviewerHeaderProbePlan).map
        (fun cells => SuccinctSpace.bitsToNatLE cells.flatten) =
      some (longCount shape) := by
  rw [packedReviewerHeaderFetch shape]
  simp [packedReviewerHeaderBits_decode shape]

end PackedCellProbe

end SuccinctFinal

end RMQ
