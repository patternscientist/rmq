import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.Probe
import RMQ.Core.GenericSelect.RAMStoreParam

/-!
# Logical reads carry no table content

This module works towards `EG-CP` row `FG-07-CLOSED-CONTROLLER`. It answers the
question the controller obligation actually turns on: when the existing
supplied-store query leaves issue a read, does the reply come from the supplied
store, or from the shape-derived table the leaf was handed?

It comes from the store. `SuccinctSpace.PayloadWordStore.readProgram` ignores its
store argument and returns `WordRAM.Program.readWord 0 i`, so a fixed-width
table's read program is an index and nothing else. The theorems below make that
checkable rather than a reading of the source: two tables with **arbitrary and
unrelated** entries and widths issue the same program at the same index, and the
four-field select entry read against a supplied store returns the same trace
result for arbitrary and unrelated tables.

## Why this matters for `FG-07`

The controller obligation forbids the executed definition from receiving a
`CartesianShape` or shape-derived data. The existing leaves do take such data --
`GenericSelect.sparseExceptionSelectData shape.bpCode false` -- so the question is
whether that argument is load-bearing for the *replies*, or only for *geometry*
(strides, field widths, slot counts).

These theorems show it is not load-bearing for the replies at the entry-table
level. What remains is the geometry, and geometry is what the shape-free mirrors
in `SourceFactorization.lean` already factor through `(n, longCount)`. So the
remaining `FG-07` work is a factorization of scalars, not a change of
architecture.

## What this module does not establish

* It covers the entry-table read, not the whole select leaf.
  `bpChunkedSelectTraceResultWithStore` additionally consumes `superStride`,
  `localStride`, `localSlotsPerSuper`, `wordSize` and `queryOccurrence` from the
  same record. Those are scalars, and each needs its own mirror and agreement
  theorem before the leaf itself is shape-free. None of that is claimed here.
* Nothing here builds a controller.
-/

namespace RMQ
namespace SuccinctFinal
namespace PackedCellProbe

/-! ### A fixed-width table read is an index, not a lookup -/

/--
**The read program of a fixed-width table carries no table content.**

The two tables share no parameter: different entry lists, different widths. They
still issue the same program at the same index, so the program cannot be
transporting anything derived from the stored data.
-/
theorem packedTableReadProgram_content_free
    {entriesLeft entriesRight : List Nat} {widthLeft widthRight : Nat}
    (tableLeft : SuccinctSpace.FixedWidthNatTable entriesLeft widthLeft)
    (tableRight : SuccinctSpace.FixedWidthNatTable entriesRight widthRight)
    (index : Nat) :
    tableLeft.readProgram index = tableRight.readProgram index :=
  rfl

/-- The program itself, written out: read word `index` of segment zero. -/
theorem packedTableReadProgram_eq_readWord
    {entries : List Nat} {width : Nat}
    (table : SuccinctSpace.FixedWidthNatTable entries width) (index : Nat) :
    table.readProgram index =
      WordRAM.Program.mapOptWordNat (WordRAM.Program.readWord 0 index) :=
  rfl

/-! ### The select entry-table read is determined by the store -/

/--
**The four-field select entry read carries no table content.**

Given the same segment layout, the same supplied store and the same index, two
select entry tables with unrelated entries and unrelated field widths produce the
same trace result: the same reads, in the same order, with the same replies, and
the same decoded entry.

This is the statement that decides `FG-07`'s shape: the reply a leaf gets is a
function of the supplied store and the index, not of the shape-derived table it
was handed.
-/
theorem packedSelectEntryRead_content_free
    {entriesLeft entriesRight :
      List GenericSelect.SparseDenseSelectDenseLocalEntry}
    {widthLeft widthRight : Nat}
    (tableLeft :
      GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable
        entriesLeft widthLeft)
    (tableRight :
      GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable
        entriesRight widthRight)
    (layout : GenericSelect.SparseDenseEntryTableTraceSegmentBases)
    (store : WordRAM.ReadStore) (index : Nat) :
    tableLeft.readTraceResultRelabeledWithStore layout store index =
      tableRight.readTraceResultRelabeledWithStore layout store index :=
  rfl

end PackedCellProbe
end SuccinctFinal
end RMQ
