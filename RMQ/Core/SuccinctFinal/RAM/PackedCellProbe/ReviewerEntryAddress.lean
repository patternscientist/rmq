import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReviewerEntryChunks

/-!
# A machine word as a bit range of its table's payload

`ReviewerEntryChunks.lean` indexed an entry-chunked machine store two-level:
machine word `i` is chunk `i % c` of logical entry `i / c`. That statement is
about *words*. The packed physical read needs *bits* -- an offset into a payload
and a width -- so this module composes the two-level index with
`packedFixedWidthTable_getElem?` and collapses the result to one `drop`/`take`:

```
packedEntryChunkBitOffset width wordSize i = (i % c) * wordSize + (i / c) * width
packedEntryChunkReadWidth  width wordSize i = min (width - (i % c) * wordSize) wordSize
```

The offset is the entry's base plus the chunk's offset within it. The width is a
full machine word except in an entry's final chunk, where the entry runs out
first -- which is exactly the case the three over-wide interior columns of
`DD-20260804-051` exercise at every size below roughly `512`.

`packedMachineStoreWords_payload` states the whole thing as a `some`, with the
in-range hypothesis `i / c < entries.length` discharged by the caller rather than
absorbed into an `Option`. That is deliberate: `FG-09` requires attempted probes to
be *shown* in range, so a formulation that silently returned `none` off the end
would move the obligation instead of meeting it.

## What this module does not establish

* No interior component is instantiated. Each still supplies its own `width`,
  positivity, and the index bound.
* This is a bit range of *the table's own payload*. Placing that payload inside the
  consumed payload -- and hence inside a cell -- needs the component offsets, which
  are not yet composed in.
-/

namespace RMQ
namespace SuccinctFinal
namespace PackedCellProbe

open RMQ.Cartesian
open RMQ.SuccinctSpace

/-- Bit offset, in the table's payload, of machine word `i`. -/
def packedEntryChunkBitOffset (width wordSize i : Nat) : Nat :=
  (i % packedChunkCount width wordSize) * wordSize +
    (i / packedChunkCount width wordSize) * width

/-- Bit width of machine word `i`: a full word, or the entry's short final chunk. -/
def packedEntryChunkReadWidth (width wordSize i : Nat) : Nat :=
  min (width - (i % packedChunkCount width wordSize) * wordSize) wordSize

/--
**A machine word as a bit range of the table's own payload.** This is the pair the
packed physical read consumes: one offset, one width, both computed from `i`, the
entry width and the machine word size.
-/
theorem packedMachineStoreWords_payload
    {entries : List Nat} {width wordSize : Nat}
    (table : FixedWidthNatTable entries width)
    (hword : 0 < wordSize) (hpos : 0 < width) (i : Nat)
    (hi : i / packedChunkCount width wordSize < entries.length) :
    (table.machineStore hword).store.words[i]? =
      some ((table.payload.drop (packedEntryChunkBitOffset width wordSize i)).take
        (packedEntryChunkReadWidth width wordSize i)) := by
  have hc : 0 < packedChunkCount width wordSize := packedChunkCount_pos hword hpos
  have hmod : i % packedChunkCount width wordSize < packedChunkCount width wordSize :=
    Nat.mod_lt _ hc
  have hpay := table.payload_length_eq
  have hfit :
      i / packedChunkCount width wordSize * width + width <= table.payload.length := by
    rw [hpay]
    have : i / packedChunkCount width wordSize + 1 <= entries.length := hi
    have hmul := Nat.mul_le_mul_right width this
    have hexp :
        (i / packedChunkCount width wordSize + 1) * width =
          i / packedChunkCount width wordSize * width + width := by
      rw [Nat.add_mul, Nat.one_mul]
    omega
  have hentry :
      ((table.payload.drop (i / packedChunkCount width wordSize * width)).take
        width).length = width := by
    rw [List.length_take, List.length_drop]
    omega
  rw [packedMachineStoreWords_getElem?_general table hword hpos i,
    Array.getElem?_toList,
    packedFixedWidthTable_getElem? table (i / packedChunkCount width wordSize)]
  unfold packedWordSlice
  rw [if_pos hi]
  simp only [Option.bind_some]
  rw [hentry, if_pos hmod]
  congr 1
  unfold packedEntryChunkBitOffset packedEntryChunkReadWidth
  rw [List.drop_take, List.take_take, List.drop_drop, Nat.min_comm,
    Nat.add_comm (i / packedChunkCount width wordSize * width)
      (i % packedChunkCount width wordSize * wordSize)]

end PackedCellProbe
end SuccinctFinal
end RMQ
