import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.Probe
import RMQ.Core.GenericSelect.RAMStoreParam
import RMQ.Core.SuccinctClose.RelativeRmmMacro.ChargedRankSelectLeafTrace
import RMQ.Core.SuccinctFinalStoreParam

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

/-! ### A record-free dense two-word select read

The fourth component. Its body never mentions the bit store: it uses only the
word size, which reaches it as a type index of that store. Taking the word size
as an ordinary argument therefore removes the record without changing the term.
-/

/-- The dense two-word select read with no bit-store argument. -/
def packedDenseTwoWordSelectRead
    (bitWordSegment rankTableSegment selectTableSegment chunkBits : Nat)
    (target : Bool) (store : WordRAM.ReadStore) (wordSize : Nat)
    (basePosition baseOccurrence occurrence : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  WordRAM.TraceResult.bind
    (SuccinctClose.bpWordReadTraceResult store bitWordSegment
      (basePosition / wordSize))
    fun firstWord? =>
      match firstWord? with
      | none => WordRAM.TraceResult.pure none
      | some firstWord =>
          WordRAM.TraceResult.bind
            (SuccinctClose.bpChunkedWordRankTraceResultAtSegmentWithStore
              store rankTableSegment chunkBits target firstWord
              (basePosition - basePosition / wordSize * wordSize))
            fun beforeFirst =>
              WordRAM.TraceResult.bind
                (SuccinctClose.bpChunkedWordRankTraceResultAtSegmentWithStore
                  store rankTableSegment chunkBits target firstWord
                  firstWord.length)
                fun uptoFirst =>
                  if occurrence - baseOccurrence < uptoFirst - beforeFirst then
                    WordRAM.TraceResult.map
                      (fun local? =>
                        local?.map fun offset =>
                          basePosition / wordSize * wordSize + offset)
                      (SuccinctClose.bpChunkedWordSelectTraceResultAtSegmentsWithStore
                        store rankTableSegment selectTableSegment chunkBits
                        target firstWord
                        (beforeFirst + (occurrence - baseOccurrence)))
                  else
                    WordRAM.TraceResult.bind
                      (SuccinctClose.bpWordReadTraceResult store bitWordSegment
                        (basePosition / wordSize + 1))
                      fun secondWord? =>
                        match secondWord? with
                        | none => WordRAM.TraceResult.pure none
                        | some secondWord =>
                            WordRAM.TraceResult.map
                              (fun local? =>
                                local?.map fun offset =>
                                  (basePosition / wordSize + 1) * wordSize +
                                    offset)
                              (SuccinctClose.bpChunkedWordSelectTraceResultAtSegmentsWithStore
                                store rankTableSegment selectTableSegment
                                chunkBits target secondWord
                                (occurrence - baseOccurrence -
                                  (uptoFirst - beforeFirst)))

/--
**The record-free dense two-word select read is the record-taking one**, once the
word size is supplied. Proved by `rfl`, over bit stores on any bit string.
-/
theorem packedDenseTwoWordSelectRead_eq
    {bits : List Bool} {wordSize : Nat}
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (bitWordSegment rankTableSegment selectTableSegment chunkBits : Nat)
    (target : Bool) (store : WordRAM.ReadStore)
    (basePosition baseOccurrence occurrence : Nat) :
    GenericSelect.bpChunkedDenseTwoWordSelectTraceResultWithStore
        bitWordSegment rankTableSegment selectTableSegment chunkBits target
        bitWords store basePosition baseOccurrence occurrence =
      packedDenseTwoWordSelectRead bitWordSegment rankTableSegment
        selectTableSegment chunkBits target store wordSize basePosition
        baseOccurrence occurrence :=
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

/-! ### The whole select leaf, record-free

All four helpers are now record-free definitions, so the leaf itself can be
written the same way: segments, a supplied store, the geometry scalars, and the
query index. No `SparseExceptionSelectData`, no `CartesianShape`, no list, no
proof argument.

`queryOccurrence` binds its record as `_data` and returns `idx`, so it is
inlined as `idx`.
-/

/--
The chunked close-select leaf with no data record: every input is a segment
number, the supplied store, a geometry scalar, the target bit, or the query
index.
-/
def packedSelectCloseRead
    (layout : GenericSelect.SparseExceptionSelectTraceSegmentLayout)
    (chunkSegment selectTableSegment : Nat) (store : WordRAM.ReadStore)
    (chunkBits : Nat) (target : Bool)
    (occurrenceCount superStride wordSize localSlotsPerSuper
      localStride : Nat)
    (longFlagBitLength longFlagWordSize longFlagBlocksPerSuper : Nat)
    (sparseBitLength sparseWordSize sparseBlocksPerSuper
      sparseLocalStride : Nat)
    (idx : Nat) : WordRAM.TraceResult (Option Nat) :=
  if idx < occurrenceCount then
    WordRAM.TraceResult.bind
      (packedSelectEntryRead layout.superTable store
        (GenericSelect.selectSuperSlot idx superStride))
      fun super? =>
        match super? with
        | none => WordRAM.TraceResult.pure none
        | some super =>
            if GenericSelect.relativeSplitSelectEntryIsMarked super then
              WordRAM.TraceResult.bind
                (packedRankRead layout.longFlagRankBase
                  (layout.longFlagRankBase + 1) (layout.longFlagRankBase + 2)
                  chunkSegment chunkBits true store longFlagBitLength
                  longFlagWordSize longFlagBlocksPerSuper
                  (GenericSelect.selectSuperSlot idx superStride))
                fun exceptionRank =>
                  GenericSelect.bpRelativeOffsetReadTraceResultWithStore store
                    layout.longRelativeBase
                    (GenericSelect.relativeSplitSelectEntryBasePosition wordSize
                      super)
                    (GenericSelect.relativeSplitSelectLongCompactSlot
                      exceptionRank (idx - super.baseOccurrence) superStride)
            else
              WordRAM.TraceResult.bind
                (packedSelectEntryRead layout.localTable store
                  (GenericSelect.relativeSplitSelectLocalSlot idx superStride
                    localSlotsPerSuper localStride super))
                fun loc? =>
                  match loc? with
                  | none => WordRAM.TraceResult.pure none
                  | some loc =>
                      if GenericSelect.relativeSplitSelectEntryIsMarked loc then
                        packedSparseDirectoryRead layout.sparseDirectory
                          chunkSegment store chunkBits sparseBitLength
                          sparseWordSize sparseBlocksPerSuper sparseLocalStride
                          (GenericSelect.relativeSplitSelectLocalBasePosition
                            wordSize super loc)
                          (GenericSelect.relativeSplitSelectLocalSlot idx
                            superStride localSlotsPerSuper localStride super)
                          (idx -
                            GenericSelect.relativeSplitSelectLocalBaseOccurrence
                              super loc)
                      else
                        packedDenseTwoWordSelectRead layout.bitWordBase
                          chunkSegment selectTableSegment chunkBits target store
                          wordSize
                          (GenericSelect.relativeSplitSelectLocalBasePosition
                            wordSize super loc)
                          (GenericSelect.relativeSplitSelectLocalBaseOccurrence
                            super loc)
                          idx
  else
    WordRAM.TraceResult.pure none

/--
**The record-free leaf is the leaf.**

For every `SparseExceptionSelectData`, the existing chunked close-select leaf
*is* `packedSelectCloseRead` applied to the same segments and store together with
that record's geometry scalars. The proof is `rfl`: the two are the same term.

Every scalar on the right has been discharged for the close-select instance:
`occurrenceCount` is `n`; `superStride`, `wordSize`, `localSlotsPerSuper` and
`localStride` have size-only mirrors at `2 * n`; both `blocksPerSuper` are the
literal `1`; both bit lengths are mirrored size-only; the sparse local stride is
the same `localStride` expression. So a controller holding only `n` can supply
every argument.
-/
theorem packedSelectCloseRead_eq
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      GenericSelect.SparseExceptionSelectData
        bits target rankSuperOverhead rankBlockOverhead)
    (layout : GenericSelect.SparseExceptionSelectTraceSegmentLayout)
    (chunkSegment selectTableSegment : Nat) (store : WordRAM.ReadStore)
    (chunkBits idx : Nat) :
    data.bpChunkedSelectTraceResultWithStore layout chunkSegment
        selectTableSegment store chunkBits idx =
      packedSelectCloseRead layout chunkSegment selectTableSegment store
        chunkBits target (GenericSelect.occurrenceCount bits target)
        data.superStride data.wordSize data.localSlotsPerSuper data.localStride
        data.longFlagBits.length data.longFlagRankData.wordSize
        data.longFlagRankData.blocksPerSuper
        data.sparseDirectory.flagBits.length
        data.sparseDirectory.rankData.wordSize
        data.sparseDirectory.rankData.blocksPerSuper
        data.sparseDirectory.localStride idx :=
  rfl

/-! ### The close-side rank leaf

The whole-query program's `rankCloseIfSome` instruction reaches the store through
`concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore`, which is the same
two-level rank read at a different segment base. So the record-free version is
`packedRankRead` again, and no new construction is needed.
-/

/-- The close-side rank leaf with no shape argument. -/
def packedRankCloseRead (store : WordRAM.ReadStore)
    (rankSegmentBase chunkBits bitLength wordSize blocksPerSuper pos : Nat) :
    WordRAM.TraceResult Nat :=
  packedRankRead rankSegmentBase (rankSegmentBase + 1) (rankSegmentBase + 2)
    (rankSegmentBase + 4) chunkBits false store bitLength wordSize
    blocksPerSuper pos

/--
**The close-side rank leaf is the record-free rank read.** Proved by `rfl`.

The chunk width is written here at `shape.bpCode.length`, which
`packedFringeChunkBits_eq` mirrors size-only; the bit length is the BP code
length, which `CartesianShape.bpCode_length` gives as `2 * n`.
-/
theorem packedRankCloseRead_eq
    (shape : CartesianShape) (store : WordRAM.ReadStore)
    (rankSegmentBase pos : Nat) :
    concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore shape store
        rankSegmentBase pos =
      packedRankCloseRead store rankSegmentBase
        (SuccinctClose.bpFringeChunkBits shape.bpCode.length)
        shape.bpCode.length
        (builtRelativeSplitBPCloseRankData shape).wordSize
        (builtRelativeSplitBPCloseRankData shape).blocksPerSuper pos :=
  rfl

/-! ### The close/LCA leaf is where the shape genuinely enters

The other three whole-query instructions reach the store through definitions that
take a *derived record* -- a select data record, a rank data record -- and the
inlining technique removes those records because the helpers consult them only
for scalars.

`lcaClose` is different, and the difference is visible in the type.
`concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore` takes
`CartesianShape` as its first explicit argument, and passes it straight through
to
`SuccinctClose.ConcreteCompactBPCloseLCADirectory.lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore`.
So the shape is not reachable by removing a record; it is an argument of the
navigator itself.

This section records that boundary precisely rather than leaving it as a guess:
the signature that carries the shape, and the fact that everything *else* the
leaf hands the navigator is already record-free.
-/

/--
The close/LCA leaf's signature, pinned. Its first argument is a
`CartesianShape`, so a controller cannot call it as it stands. This is the one
remaining whole-query instruction leaf with that property.
-/
def packedLcaCloseLeafSignature :
    CartesianShape -> WordRAM.ReadStore -> Nat -> Nat ->
      WordRAM.TraceResult (Option Nat) :=
  concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore

/--
**The rank seed the close/LCA leaf supplies is already record-free.**

The navigator receives a rank-seed function, three fixed segment constants, the
store and the two close endpoints, plus the shape. This theorem discharges the
rank seed: it is `packedRankCloseRead` at the close rank segment base. What
remains irreducible is the shape argument itself.
-/
theorem packedLcaCloseRankSeed_eq
    (shape : CartesianShape) (store : WordRAM.ReadStore) (pos : Nat) :
    concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore shape store
        concreteBPNativeRankCloseTraceSegmentBase pos =
      packedRankCloseRead store concreteBPNativeRankCloseTraceSegmentBase
        (SuccinctClose.bpFringeChunkBits shape.bpCode.length)
        shape.bpCode.length
        (builtRelativeSplitBPCloseRankData shape).wordSize
        (builtRelativeSplitBPCloseRankData shape).blocksPerSuper pos :=
  rfl

/-! #### The navigator's dispatch is size-only

The close/LCA navigator's own body uses `shape` in two places: the block size that
decides same-block versus cross-block, and the recursive hand-off to the two
sub-navigators. The first is settled here.
-/

/-- Size-only mirror of the summary block size that drives the close dispatch. -/
def packedSummaryBlockSizeRaw (n : Nat) : Nat :=
  2 * packedSummaryBase n

/--
**The close/LCA dispatch scalar is a function of the input size.**

`lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore` branches on
`blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape) leftClose =
blockOfClose … rightClose`. That block size is `2 * (n.log2 + 1)`, so the branch
is decided by `n` and the two close endpoints alone -- exactly the inputs `FG-07`
permits.
-/
theorem packedSummaryBlockSizeRaw_eq (shape : CartesianShape) :
    SuccinctClose.canonicalBPRelativeSummaryBlockSizeRaw shape =
      packedSummaryBlockSizeRaw shape.size :=
  rfl

/-! #### The same-block sub-navigator's seed is shape-free

`bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegmentWithStore` binds a
local-BP seed and then hands it to the seeded reader. The seed comes from
`localBPSeedFromRankCloseTraceResult`, whose only use of the shape is
`localBPWindowBase shape blockSize close` -- and that in turn uses the shape only
through `machineWordBits shape.bpCode.length`, which is the BP-code word width
already mirrored above.
-/

/-- Size-only mirror of the local-BP window base. -/
def packedLocalBPWindowBase (n blockSize close : Nat) : Nat :=
  SuccinctClose.blockStartOf blockSize
      (SuccinctClose.blockOfClose blockSize close) /
    packedBpCodeWordWidth n * packedBpCodeWordWidth n

theorem packedLocalBPWindowBase_eq
    (shape : CartesianShape) (blockSize close : Nat) :
    SuccinctClose.localBPWindowBase shape blockSize close =
      packedLocalBPWindowBase shape.size blockSize close := by
  unfold SuccinctClose.localBPWindowBase packedLocalBPWindowBase
    packedBpCodeWordWidth
  rw [CartesianShape.bpCode_length]

/--
The local-BP seed with no shape argument: the rank-close reader is supplied by
the caller, and the window base comes from the input size.
-/
def packedLocalBPSeed (n : Nat)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (blockSize close : Nat) : WordRAM.TraceResult Nat :=
  WordRAM.TraceResult.map
    (fun rankFalse =>
      SuccinctClose.localBPSeedFromRankFalse
        (packedLocalBPWindowBase n blockSize close) rankFalse)
    (rankCloseTrace (packedLocalBPWindowBase n blockSize close))

/--
**The same-block seed is shape-free.** Its only shape use was the window base,
and that is a function of the input size.
-/
theorem packedLocalBPSeed_eq
    (shape : CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (blockSize close : Nat) :
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPSeedFromRankCloseTraceResult shape rankCloseTrace
        blockSize close =
      packedLocalBPSeed shape.size rankCloseTrace blockSize close := by
  unfold SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPSeedFromRankCloseTraceResult packedLocalBPSeed
  rw [packedLocalBPWindowBase_eq]

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

/-! #### The same-block seeded reader

Its shape uses are the fringe chunk width, the local-BP window base, and the
window reader itself. The first two are already mirrored size-only, so the
record-free version takes the window trace as a supplied argument -- the same
pattern the rank seed used.
-/

/-- The same-block seeded close reader with no shape argument. -/
def packedSameBlockCloseSeededRead
    (store : WordRAM.ReadStore) (fringeSegment : Nat)
    (windowBits : WordRAM.TraceResult (List Bool))
    (n blockSize leftClose rightClose seed : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  WordRAM.TraceResult.bind windowBits
    (fun window =>
      WordRAM.TraceResult.map
        (fun st =>
          SuccinctClose.bpCandidateClose?
            (SuccinctClose.bpFringeCandGlobal
              (packedLocalBPWindowBase n blockSize leftClose) seed
              (leftClose + 1) st.2))
        (SuccinctClose.bpFringeChunkFoldTraceResultAtSegmentWithStore store
          fringeSegment (packedFringeChunkBits n) window seed
          (leftClose + 1 - packedLocalBPWindowBase n blockSize leftClose)
          (leftClose + 1 + (rightClose - leftClose + 1) - 1 -
            packedLocalBPWindowBase n blockSize leftClose)
          (Nat.min
            ((leftClose + 1 + (rightClose - leftClose + 1) - 1 -
                packedLocalBPWindowBase n blockSize leftClose) /
              packedFringeChunkBits n + 1) 33)))

/--
**The same-block seeded reader is shape-free given its window trace.** Its only
remaining shape use was the window reader, which is now an argument.
-/
theorem packedSameBlockCloseSeededRead_eq
    (shape : CartesianShape) (store : WordRAM.ReadStore)
    (fringeSegment blockSize leftClose rightClose seed : Nat) :
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedSameBlockCloseSeededTraceResultAtSegmentWithStore
        shape store fringeSegment blockSize leftClose rightClose seed =
      packedSameBlockCloseSeededRead store fringeSegment
        (SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPWindowBitsTraceResultWithStore shape store
          blockSize leftClose)
        shape.size blockSize leftClose rightClose seed := by
  unfold SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedSameBlockCloseSeededTraceResultAtSegmentWithStore
    packedSameBlockCloseSeededRead
  rw [packedFringeChunkBits_eq, packedLocalBPWindowBase_eq]


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
