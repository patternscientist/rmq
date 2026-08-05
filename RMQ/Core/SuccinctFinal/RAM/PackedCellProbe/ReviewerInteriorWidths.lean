import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReviewerEntryAddress

/-!
# The interior components' shared prerequisites

`packedMachineStoreWords_payload` needs three things from each of the eight
interior components: the machine word size is positive, the entry width is
positive, and the index is in range. The first two are shared, and this module
supplies them.

All four interior entry widths turn out to be positive for a stated reason rather
than by accident:

```
superWidth        = machineWordBits shape.bpCode.length   -- machineWordBits_pos
offsetWidth       = machineWordBits layout.macroSize      -- machineWordBits_pos
blockAddressWidth = machineWordBits layout.blockCount     -- machineWordBits_pos
relativeWidth                                             -- Valid.relativeWidth_pos
```

Three are `machineWordBits` of something, which is positive at every argument
including zero. The fourth is not, and its positivity is a *hypothesis of the
layout's validity record* rather than a computation -- `relativeWidth` has to be
wide enough to hold a superblock span, and `Valid` carries that. Worth noting
because it is the same width the three over-wide columns of `DD-20260804-051`
carry, so both facts about it come from different places.

`packedInteriorComponentWord` specialises the address theorem to the interior's
machine word size, leaving a component to supply only its width positivity and its
index bound.

## What this module does not establish

* No component is instantiated. Each of the eight still needs its index bound,
  which is the `FG-09` obligation the `some`-shaped statement of
  `DD-20260804-052` deliberately refuses to absorb.
* Nothing here places a component's payload inside the consumed payload; that
  needs `canonicalRelativeRmmInteriorComponentOffsets`.
-/

namespace RMQ
namespace SuccinctFinal
namespace PackedCellProbe

open RMQ.Cartesian
open RMQ.SuccinctSpace

/-! ### The interior's machine word size -/

/-- The machine word size every interior component store is bounded by. -/
def packedInteriorWordSize (shape : CartesianShape) : Nat :=
  SuccinctRank.machineWordBits shape.bpCode.length

theorem packedInteriorWordSize_pos (shape : CartesianShape) :
    0 < packedInteriorWordSize shape :=
  SuccinctRank.machineWordBits_pos _

/-! ### Positivity of the four interior entry widths -/

theorem packedInteriorSuperWidth_pos (shape : CartesianShape) :
    0 < (SuccinctClose.RelativeRmm.canonicalLayout shape).superWidth shape :=
  SuccinctRank.machineWordBits_pos _

theorem packedInteriorRelativeWidth_pos (shape : CartesianShape) :
    0 < (SuccinctClose.RelativeRmm.canonicalLayout shape).relativeWidth :=
  (SuccinctClose.RelativeRmm.canonicalLayout_valid shape).relativeWidth_pos

theorem packedInteriorOffsetWidth_pos (shape : CartesianShape) :
    0 < (SuccinctClose.RelativeRmm.canonicalLayout shape).offsetWidth :=
  SuccinctRank.machineWordBits_pos _

theorem packedInteriorBlockAddressWidth_pos (shape : CartesianShape) :
    0 < (SuccinctClose.RelativeRmm.canonicalLayout shape).blockAddressWidth :=
  SuccinctRank.machineWordBits_pos _

/-! ### The instantiation each interior component uses -/

/--
`packedMachineStoreWords_payload` specialised to the interior's machine word size,
so a component supplies only its entry width's positivity and its index bound.
-/
theorem packedInteriorComponentWord
    {entries : List Nat} {width : Nat}
    (shape : CartesianShape)
    (table : FixedWidthNatTable entries width)
    (hpos : 0 < width) (i : Nat)
    (hi : i / packedChunkCount width (packedInteriorWordSize shape) <
      entries.length) :
    (table.machineStore (packedInteriorWordSize_pos shape)).store.words[i]? =
      some ((table.payload.drop
          (packedEntryChunkBitOffset width (packedInteriorWordSize shape) i)).take
        (packedEntryChunkReadWidth width (packedInteriorWordSize shape) i)) :=
  packedMachineStoreWords_payload table (packedInteriorWordSize_pos shape) hpos i hi

end PackedCellProbe
end SuccinctFinal
end RMQ
