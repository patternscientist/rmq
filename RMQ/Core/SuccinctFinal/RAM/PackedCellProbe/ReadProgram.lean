import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.Probe
import RMQ.Core.GenericSelect.RAMStoreParam
import RMQ.Core.SuccinctClose.RelativeRmmMacro.ChargedRankSelectLeafTrace

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

/-! ### The select leaf's geometry scalars are size-only

`bpChunkedSelectTraceResultWithStore` consumes four scalars from the select data
record and one validity guard. All five are functions of the input size alone,
because `sparseExceptionSelectData` sets each of them from `bits.length` and the
BP code has length `2 * n`.

Together with the content-free theorems above, this is the whole select-side
shape-dependence except `queryOccurrence`, which is not mirrored here.
-/

open RMQ.Cartesian

/-- Size-only mirror of the select word size. -/
def packedSelectWordSize (n : Nat) : Nat :=
  GenericSelect.wordBits (2 * n)

/-- Size-only mirror of the select super stride. -/
def packedSelectSuperStride (n : Nat) : Nat :=
  GenericSelect.superStride (2 * n)

/-- Size-only mirror of the select local stride. -/
def packedSelectLocalStride (n : Nat) : Nat :=
  GenericSelect.localStride (2 * n)

/-- Size-only mirror of the local slots per super block. -/
def packedSelectLocalSlotsPerSuper (n : Nat) : Nat :=
  GenericSelect.localSlotsPerSuper (2 * n)

theorem packedSelectWordSize_eq (shape : CartesianShape) :
    (GenericSelect.sparseExceptionSelectData shape.bpCode false).wordSize =
      packedSelectWordSize shape.size := by
  show GenericSelect.wordBits shape.bpCode.length =
    packedSelectWordSize shape.size
  unfold packedSelectWordSize
  rw [CartesianShape.bpCode_length]

theorem packedSelectSuperStride_eq (shape : CartesianShape) :
    (GenericSelect.sparseExceptionSelectData shape.bpCode false).superStride =
      packedSelectSuperStride shape.size := by
  show GenericSelect.superStride shape.bpCode.length =
    packedSelectSuperStride shape.size
  unfold packedSelectSuperStride
  rw [CartesianShape.bpCode_length]

theorem packedSelectLocalStride_eq (shape : CartesianShape) :
    (GenericSelect.sparseExceptionSelectData shape.bpCode false).localStride =
      packedSelectLocalStride shape.size := by
  show GenericSelect.localStride shape.bpCode.length =
    packedSelectLocalStride shape.size
  unfold packedSelectLocalStride
  rw [CartesianShape.bpCode_length]

theorem packedSelectLocalSlotsPerSuper_eq (shape : CartesianShape) :
    (GenericSelect.sparseExceptionSelectData
        shape.bpCode false).localSlotsPerSuper =
      packedSelectLocalSlotsPerSuper shape.size := by
  show GenericSelect.localSlotsPerSuper shape.bpCode.length =
    packedSelectLocalSlotsPerSuper shape.size
  unfold packedSelectLocalSlotsPerSuper
  rw [CartesianShape.bpCode_length]

/--
**The select leaf's validity guard is the input size.**

`bpChunkedSelectTraceResultWithStore` dispatches on
`idx < occurrenceCount bits target`. For the close-select instance that guard is
exactly `idx < n`, so a controller can evaluate it from `n` alone with no header
field and no probe.
-/
theorem packedSelectOccurrenceCount_eq_size (shape : CartesianShape) :
    GenericSelect.occurrenceCount shape.bpCode false = shape.size := by
  unfold GenericSelect.occurrenceCount
  exact SuccinctSpace.bpCode_rankFalse_full shape

/-! ### The leaf's other read sub-calls

`bpChunkedSelectTraceResultWithStore` reaches the store through four helpers. The
entry-table read is content-free above. Two of the remaining three are covered
here; the fourth, the two-level rank read, consumes scalars of its own record and
is not covered.
-/

/--
**The dense two-word select read carries no bit-store content.**

The two bit stores are over unrelated bit strings; only the word size is shared,
and the word size is a type index rather than stored data. The results agree, so
this helper reads the supplied store and consults its own argument only for that
scalar.
-/
theorem packedDenseTwoWordSelectRead_content_free
    {bitsLeft bitsRight : List Bool} {wordSize : Nat}
    (bitWordsLeft : SuccinctSpace.BoundedPayloadWordStore bitsLeft wordSize)
    (bitWordsRight : SuccinctSpace.BoundedPayloadWordStore bitsRight wordSize)
    (bitWordSegment rankTableSegment selectTableSegment chunkBits : Nat)
    (target : Bool) (store : WordRAM.ReadStore)
    (basePosition baseOccurrence occurrence : Nat) :
    GenericSelect.bpChunkedDenseTwoWordSelectTraceResultWithStore
        bitWordSegment rankTableSegment selectTableSegment chunkBits target
        bitWordsLeft store basePosition baseOccurrence occurrence =
      GenericSelect.bpChunkedDenseTwoWordSelectTraceResultWithStore
        bitWordSegment rankTableSegment selectTableSegment chunkBits target
        bitWordsRight store basePosition baseOccurrence occurrence :=
  rfl

/--
**The two-level rank read is determined by three scalars.**

Its body mentions its record only through `superIndex`, `wordIndex` and
`wordOffset`, and those three unfold to `queryPos pos`, `wordSize` and
`blocksPerSuper`. Two rank records over unrelated bit strings, with unrelated
overheads and unrelated query costs, therefore agree whenever those three agree.

This is the fourth and last helper `bpChunkedSelectTraceResultWithStore` uses to
reach the store. With the three content-free results above, the select leaf's
whole dependence on its shape-derived arguments is a fixed list of scalars.
-/
theorem packedRankRead_scalar_determined
    {bitsLeft bitsRight : List Bool}
    {superLeft blockLeft queryLeft : Nat}
    {superRight blockRight queryRight : Nat}
    (dataLeft :
      SuccinctRank.TwoLevelPayloadLiveStoredWordRankData
        bitsLeft superLeft blockLeft queryLeft)
    (dataRight :
      SuccinctRank.TwoLevelPayloadLiveStoredWordRankData
        bitsRight superRight blockRight queryRight)
    (store : WordRAM.ReadStore)
    (superSegment blockSegment wordSegment chunkSegment chunkBits : Nat)
    (target : Bool) (pos : Nat)
    (hquery : dataLeft.queryPos pos = dataRight.queryPos pos)
    (hwordSize : dataLeft.wordSize = dataRight.wordSize)
    (hblocks : dataLeft.blocksPerSuper = dataRight.blocksPerSuper) :
    dataLeft.bpChunkedRankTraceResultWithStore store superSegment blockSegment
        wordSegment chunkSegment chunkBits target pos =
      dataRight.bpChunkedRankTraceResultWithStore store superSegment blockSegment
        wordSegment chunkSegment chunkBits target pos := by
  have hword : dataLeft.wordIndex pos = dataRight.wordIndex pos := by
    unfold SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordIndex
    rw [hquery, hwordSize]
  have hsuper : dataLeft.superIndex pos = dataRight.superIndex pos := by
    unfold SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.superIndex
    rw [hword, hblocks]
  have hoffset : dataLeft.wordOffset pos = dataRight.wordOffset pos := by
    unfold SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordOffset
    rw [hquery, hword, hwordSize]
  unfold
    SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.bpChunkedRankTraceResultWithStore
  rw [hsuper, hword, hoffset]

/--
**The relative-offset read takes no record at all.**

Its declared type is a supplied store and three naturals. Nothing shape-derived
can reach it, so a controller can issue it directly.
-/
def packedRelativeOffsetReadSignature :
    WordRAM.ReadStore -> Nat -> Nat -> Nat ->
      WordRAM.TraceResult (Option Nat) :=
  GenericSelect.bpRelativeOffsetReadTraceResultWithStore

/--
The clamped query position of a two-level rank read, as a function of the bit
length and the requested position.
-/
def packedRankQueryPos (bitLength pos : Nat) : Nat :=
  Nat.min pos bitLength

/--
**The rank read's query position is a function of the bit length alone.**

`queryPos` binds its record as `_data`; its body is `Nat.min pos bits.length`.
So one of the three scalars the rank read consumes is already reduced to a
length, and this development has size-only mirrors for the lengths of both rank
records the select leaf uses.
-/
theorem packedRankQueryPos_eq
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      SuccinctRank.TwoLevelPayloadLiveStoredWordRankData
        bits superOverhead blockOverhead queryCost)
    (pos : Nat) :
    data.queryPos pos = packedRankQueryPos bits.length pos :=
  rfl

/-- Equal bit lengths give equal query positions, over unrelated records. -/
theorem packedRankQueryPos_length_determined
    {bitsLeft bitsRight : List Bool}
    {superLeft blockLeft queryLeft superRight blockRight queryRight : Nat}
    (dataLeft :
      SuccinctRank.TwoLevelPayloadLiveStoredWordRankData
        bitsLeft superLeft blockLeft queryLeft)
    (dataRight :
      SuccinctRank.TwoLevelPayloadLiveStoredWordRankData
        bitsRight superRight blockRight queryRight)
    (hlength : bitsLeft.length = bitsRight.length) (pos : Nat) :
    dataLeft.queryPos pos = dataRight.queryPos pos := by
  rw [packedRankQueryPos_eq dataLeft pos, packedRankQueryPos_eq dataRight pos,
    hlength]

/-! #### The last two scalars: `blocksPerSuper`

The rank read consumes `blocksPerSuper` from its record. The select leaf uses two
rank records, and both values turn out to be reachable from the input size: the
long-flag one is a literal, and the sparse one is `machineWordBits` of a length
this development already mirrors.
-/

/--
**The long-flag rank data groups one block per super block.**

`longFlagRankBlocksPerSuper` binds both arguments as `_bits` and `_target` and
returns `1`, so this scalar is a literal at every size.
-/
theorem packedLongFlagBlocksPerSuper_eq (bits : List Bool) (target : Bool) :
    (GenericSelect.longFlagRankData bits target).blocksPerSuper = 1 :=
  rfl

/--
**The sparse flag rank data also groups one block per super block.**

`sparseExceptionEffectiveFlagRankBlocksPerSuper` likewise binds both arguments as
`_bits` and `_target` and returns `1`.

With this, every scalar `bpChunkedSelectTraceResultWithStore` consumes is either
a literal or a size-only function of the input size, and the select leaf's whole
dependence on the shape is discharged.
-/
theorem packedSparseFlagBlocksPerSuper_eq (bits : List Bool) (target : Bool) :
    (GenericSelect.sparseExceptionEffectiveFlagRankData
        bits target).blocksPerSuper = 1 :=
  rfl

/-! ### A record-free select entry read

The content-free theorems above say the record does not affect the result. This
section goes one step further and removes the record from the *definition*:
`packedSelectEntryRead` takes a segment layout, a supplied store and an index,
and nothing else. `packedSelectEntryRead_eq` proves it is the record-taking read,
by `rfl`.

That is the difference between an analysis and a construction. A controller can
call this definition; it could not call the record-taking one without being
handed a shape-derived table.
-/

/--
The four-field select entry read, with no table argument: four charged reads at
the layout's four segments, then `entryOfFields` on the replies.
-/
def packedSelectEntryRead
    (layout : GenericSelect.SparseDenseEntryTableTraceSegmentBases)
    (store : WordRAM.ReadStore) (index : Nat) :
    WordRAM.TraceResult
      (Option GenericSelect.SparseDenseSelectDenseLocalEntry) :=
  WordRAM.TraceResult.bind
    (WordRAM.TraceResult.ofProgramWithStore
      (WordRAM.singletonSegmentMap layout.baseOccurrence layout.deadSegment)
      store (WordRAM.Program.mapOptWordNat (WordRAM.Program.readWord 0 index)))
    fun baseOccurrence? =>
      WordRAM.TraceResult.bind
        (WordRAM.TraceResult.ofProgramWithStore
          (WordRAM.singletonSegmentMap layout.baseWordIndex layout.deadSegment)
          store
          (WordRAM.Program.mapOptWordNat (WordRAM.Program.readWord 0 index)))
        fun baseWordIndex? =>
          WordRAM.TraceResult.bind
            (WordRAM.TraceResult.ofProgramWithStore
              (WordRAM.singletonSegmentMap layout.rankBefore layout.deadSegment)
              store
              (WordRAM.Program.mapOptWordNat
                (WordRAM.Program.readWord 0 index)))
            fun rankBefore? =>
              WordRAM.TraceResult.map
                (fun firstOffset? =>
                  GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable.entryOfFields
                    baseOccurrence? baseWordIndex? rankBefore? firstOffset?)
                (WordRAM.TraceResult.ofProgramWithStore
                  (WordRAM.singletonSegmentMap layout.firstOffset
                    layout.deadSegment)
                  store
                  (WordRAM.Program.mapOptWordNat
                    (WordRAM.Program.readWord 0 index)))

/--
**The record-free read is the record-taking read.**

For every select entry table, over any entries and any field width, the existing
leaf's entry read *is* `packedSelectEntryRead` applied to the same layout, store
and index. The proof is `rfl`, so this is not an approximation: the two are the
same term.
-/
theorem packedSelectEntryRead_eq
    {entries : List GenericSelect.SparseDenseSelectDenseLocalEntry}
    {fieldWidth : Nat}
    (table :
      GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable
        entries fieldWidth)
    (layout : GenericSelect.SparseDenseEntryTableTraceSegmentBases)
    (store : WordRAM.ReadStore) (index : Nat) :
    table.readTraceResultRelabeledWithStore layout store index =
      packedSelectEntryRead layout store index :=
  rfl

/-! ### A record-free two-level rank read

The rank read genuinely consults its record, so the record-free version takes the
three scalars as arguments -- the bit length, the word size and the blocks per
super block. `DD-20260804-009` predicted exactly this shape. The equation is
still `rfl`, because the record's contribution is those three projections and
nothing else.
-/

/--
The chunked two-level rank read, with no record argument: the super sample, the
block sample, the packed word, and the in-word rank, all against the supplied
store, with the indices computed from the three supplied scalars.
-/
def packedRankRead
    (superSegment blockSegment wordSegment chunkSegment chunkBits : Nat)
    (target : Bool) (store : WordRAM.ReadStore)
    (bitLength wordSize blocksPerSuper pos : Nat) : WordRAM.TraceResult Nat :=
  WordRAM.TraceResult.bind
    (SuccinctClose.bpChunkReadTraceResult store superSegment
      (Nat.min pos bitLength / wordSize / blocksPerSuper))
    fun super? =>
      WordRAM.TraceResult.bind
        (SuccinctClose.bpChunkReadTraceResult store blockSegment
          (Nat.min pos bitLength / wordSize))
        fun delta? =>
          WordRAM.TraceResult.bind
            (SuccinctClose.bpWordReadTraceResult store wordSegment
              (Nat.min pos bitLength / wordSize))
            fun word? =>
              match super?, delta?, word? with
              | some super, some delta, some word =>
                  WordRAM.TraceResult.map
                    (fun localRank => super + delta + localRank)
                    (SuccinctClose.bpChunkedWordRankTraceResultAtSegmentWithStore
                      store chunkSegment chunkBits target word
                      (Nat.min pos bitLength -
                        Nat.min pos bitLength / wordSize * wordSize))
              | _, _, _ => WordRAM.TraceResult.pure 0

/--
**The record-free rank read is the record-taking rank read**, once its three
scalars are supplied. Proved by `rfl`, over records with any bit string, any
overheads and any query cost.
-/
theorem packedRankRead_eq
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      SuccinctRank.TwoLevelPayloadLiveStoredWordRankData
        bits superOverhead blockOverhead queryCost)
    (store : WordRAM.ReadStore)
    (superSegment blockSegment wordSegment chunkSegment chunkBits : Nat)
    (target : Bool) (pos : Nat) :
    data.bpChunkedRankTraceResultWithStore store superSegment blockSegment
        wordSegment chunkSegment chunkBits target pos =
      packedRankRead superSegment blockSegment wordSegment chunkSegment
        chunkBits target store bits.length data.wordSize data.blocksPerSuper
        pos :=
  rfl

/-! ### A record-free sparse-directory read

The third component. It composes the two already built: the record-free rank read
followed by the record-free relative-offset read, with one further scalar, the
local stride.
-/

/-- The sparse-directory read with no record argument. -/
def packedSparseDirectoryRead
    (layout : GenericSelect.SparseExceptionDirectoryTraceSegmentBases)
    (chunkSegment : Nat) (store : WordRAM.ReadStore) (chunkBits : Nat)
    (bitLength wordSize blocksPerSuper localStride : Nat)
    (base localSlot localOccurrence : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  WordRAM.TraceResult.bind
    (packedRankRead layout.rankBase (layout.rankBase + 1) (layout.rankBase + 2)
      chunkSegment chunkBits true store bitLength wordSize blocksPerSuper
      localSlot)
    fun exceptionRank =>
      GenericSelect.bpRelativeOffsetReadTraceResultWithStore store
        layout.relativeBase base
        (GenericSelect.relativeSplitSelectSparseCompactSlot exceptionRank
          localOccurrence localStride)

/--
**The record-free sparse-directory read is the record-taking one**, once its four
scalars are supplied. Proved by `rfl`.
-/
theorem packedSparseDirectoryRead_eq
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      GenericSelect.SparseExceptionDirectory
        bits target rankSuperOverhead rankBlockOverhead)
    (layout : GenericSelect.SparseExceptionDirectoryTraceSegmentBases)
    (chunkSegment : Nat) (store : WordRAM.ReadStore) (chunkBits : Nat)
    (base localSlot localOccurrence : Nat) :
    directory.bpChunkedReadTraceResultWithStore layout chunkSegment store
        chunkBits base localSlot localOccurrence =
      packedSparseDirectoryRead layout chunkSegment store chunkBits
        directory.flagBits.length directory.rankData.wordSize
        directory.rankData.blocksPerSuper directory.localStride base localSlot
        localOccurrence :=
  rfl

/-- Size-only mirror of the shared fringe chunk width. -/
def packedFringeChunkBits (n : Nat) : Nat :=
  SuccinctClose.bpFringeChunkBits (2 * n)

/--
**The fringe chunk width is a function of the input size.**

This is the one scalar supplied *beside* the select data rather than inside it:
the leaf takes it as the argument the layout calls `c`. It is a width of the BP
code, so the mirror is immediate.
-/
theorem packedFringeChunkBits_eq (shape : CartesianShape) :
    SuccinctClose.bpFringeChunkBits shape.bpCode.length =
      packedFringeChunkBits shape.size := by
  unfold packedFringeChunkBits
  rw [CartesianShape.bpCode_length]

/--
**The sparse-directory read is determined by four scalars.**

Its body is the chunked rank seed followed by one relative-offset read. The rank
seed is scalar-determined by the theorem above; the relative-offset read takes no
record; and the only other use of the directory is `localStride`. So four scalars
suffice, over directories with unrelated bit strings, targets and overheads.

This is the fifth and last helper reached by
`bpChunkedSelectTraceResultWithStore`.
-/
theorem packedSparseDirectoryRead_scalar_determined
    {bitsLeft bitsRight : List Bool} {targetLeft targetRight : Bool}
    {superLeft blockLeft superRight blockRight : Nat}
    (directoryLeft :
      GenericSelect.SparseExceptionDirectory
        bitsLeft targetLeft superLeft blockLeft)
    (directoryRight :
      GenericSelect.SparseExceptionDirectory
        bitsRight targetRight superRight blockRight)
    (layout : GenericSelect.SparseExceptionDirectoryTraceSegmentBases)
    (chunkSegment : Nat) (store : WordRAM.ReadStore) (chunkBits : Nat)
    (base localSlot localOccurrence : Nat)
    (hquery :
      directoryLeft.rankData.queryPos localSlot =
        directoryRight.rankData.queryPos localSlot)
    (hwordSize :
      directoryLeft.rankData.wordSize = directoryRight.rankData.wordSize)
    (hblocks :
      directoryLeft.rankData.blocksPerSuper =
        directoryRight.rankData.blocksPerSuper)
    (hlocalStride : directoryLeft.localStride = directoryRight.localStride) :
    directoryLeft.bpChunkedReadTraceResultWithStore layout chunkSegment store
        chunkBits base localSlot localOccurrence =
      directoryRight.bpChunkedReadTraceResultWithStore layout chunkSegment store
        chunkBits base localSlot localOccurrence := by
  unfold
    GenericSelect.SparseExceptionDirectory.bpChunkedReadTraceResultWithStore
  rw [packedRankRead_scalar_determined directoryLeft.rankData
      directoryRight.rankData store layout.rankBase (layout.rankBase + 1)
      (layout.rankBase + 2) chunkSegment chunkBits true localSlot hquery
      hwordSize hblocks, hlocalStride]

/--
**The queried occurrence carries no record content.**

The two records share no parameter: different bit strings, different targets,
different overheads. They still map the same index to the same occurrence, so
this last select-side scalar is a function of the index alone and needs no
mirror.

With the four geometry mirrors and the validity guard above, that completes the
select leaf's scalar list from `DD-20260804-006`.
-/
theorem packedSelectQueryOccurrence_content_free
    {bitsLeft bitsRight : List Bool} {targetLeft targetRight : Bool}
    {superLeft blockLeft superRight blockRight : Nat}
    (dataLeft :
      GenericSelect.SparseExceptionSelectData
        bitsLeft targetLeft superLeft blockLeft)
    (dataRight :
      GenericSelect.SparseExceptionSelectData
        bitsRight targetRight superRight blockRight)
    (index : Nat) :
    dataLeft.queryOccurrence index = dataRight.queryOccurrence index :=
  rfl

end PackedCellProbe
end SuccinctFinal
end RMQ
