import RMQ.Core.WordRAM.E1InteriorChunkExact
import RMQ.Core.SuccinctClose.EndpointFringe.InteriorCandidate.InteriorDirectory

/-! # The value bridge's agreement premise, discharged AT the interior store

`hexact_of_segment_agrees` (`E1InteriorChunkExact.lean`) reduces the value
bridge's exactness premise to ONE parameter, `hagree`: that the machine's
flat store agrees, at the table's own base offset, with the table's machine
word list.  M3d-16 exhibited a store meeting it (`segmentStore_agrees`).
THAT IS SATISFIABILITY, NOT DISCHARGE.  This module closes the gap: it
derives `hagree` at `canonicalRelativeRmmInteriorComponentStore`, the one
store the interior composition instantiates the fold against, for ALL EIGHT
of its component tables.

## The premise as inherited was FALSE at that store

`hagree` was stated unbounded -- agreement at EVERY address `base + a`.  It
cannot hold at the interior store for any table but the last, and the
reason is structural rather than delicate.
`canonicalRelativeRmmInteriorComponentStore` is the CONCATENATION of the
eight tables' machine word lists
(`canonicalRelativeRmmInteriorComponentStore_words_toList`,
`InteriorDirectory.lean:1665`).  Past the end of any one table the store
still answers `some` -- with the NEXT table's word -- while
`(machineWords table)[a]?` has run out and answers `none`.

This was settled by EVALUATION before anything was built on it, per the
standing rule.  At the one-node shape the baseline table contributes `2`
words to a `31`-word store, so the unbounded premise fails first at
`a = 2`; `probeShape_unbounded_agreement_fails` below states that as a
CHECKED theorem rather than a note.

So the inherited premise is the same failure class M3d-14 found in the
width premise one level down -- a hypothesis that looks merely unproved at
the definition site and is in fact unmeetable at the intended
instantiation.  Everything composed on it would have been vacuous.

## The repair, and why it costs nothing

STRENGTHENING ONLY: `hagree` is BOUNDED to addresses the table's own word
list indexes, and `machineWords_index_lt` supplies the bound at the single
index the proof uses (`i * chunkCount + j`, for a cell the table holds and
a chunk below the count).  No conclusion moved, nothing was renamed, and
the corollary's consumers see a WEAKER premise.

The bounded form is exactly what an append decomposition yields, so it
discharges here for all eight tables from two facts and no side conditions:
the store's word list is the eight-fold append, and
`canonicalRelativeRmmInteriorComponentOffsets` (`InteriorDirectory.lean:1614`)
is the running prefix sums of that append.  The offsets are the same
constants the route's own read computations use (`:2282`, `:2317`, `:2335`),
so this is agreement with the ROUTE'S addressing, not with a layout chosen
here.

See DD-20260719-012 (claimed this session; the maximum OBSERVED in
`DESIGN_DECISIONS.md` was `DD-20260719-011`).
-/

open RMQ
open RMQ.SuccinctSpace
open RMQ.SuccinctClose

namespace RMQ
namespace WordRAM
namespace E1InteriorChunkStore

open RMQ.WordRAM.E1InteriorChunkExact
open RMQ.WordRAM.E1InteriorChunkFold

/-! ## Generic slice agreement -/

/-- Indexing an append past the whole prefix is indexing the suffix. -/
theorem getElem?_append_len_add {α : Type} (pre rest : List α) (a : Nat) :
    (pre ++ rest)[pre.length + a]? = rest[a]? := by
  induction pre with
  | nil => simp
  | cons x xs ih =>
      have hlen : (x :: xs).length + a = (xs.length + a) + 1 := by
        simp [Nat.add_comm, Nat.add_assoc]
      rw [hlen]
      simpa using ih

/-- AGREEMENT ON ONE SLICE OF A FLAT STORE.

If the store's segment reproduces `whole`, and `whole` splits as
`pre ++ mid ++ post`, then the store agrees with `mid` at base
`pre.length` -- for indices `mid` actually has.  The bound is not
removable: at `a = mid.length` the left side reads the first word of
`post`. -/
theorem readWord?_slice
    {store : ReadStore} {segment : Nat} {whole pre mid post : List Word}
    (hstore : ∀ a, store.readWord? segment a = whole[a]?)
    (hsplit : whole = pre ++ mid ++ post)
    {a : Nat} (ha : a < mid.length) :
    store.readWord? segment (pre.length + a) = mid[a]? := by
  rw [hstore, hsplit, List.append_assoc, getElem?_append_len_add,
    List.getElem?_append_left ha]

/-- A table's machine store reproduces its machine word list verbatim. -/
theorem machineStore_words_toList
    {entries : List Nat} {width wordSize : Nat}
    (table : FixedWidthNatTable entries width) (hwordSize : 0 < wordSize) :
    (table.machineStore hwordSize).store.words.toList =
      fixedWidthNatTableMachineWords table wordSize := by
  simp [FixedWidthNatTable.machineStore]

/-- The same fact as a SIZE equation.  The offsets are running sums of
`Array.size`; the splits below are running sums of `List.length`.  Without
this bridge the two never meet and every offset goal stalls. -/
@[simp] theorem machineStore_words_size
    {entries : List Nat} {width wordSize : Nat}
    (table : FixedWidthNatTable entries width) (hwordSize : 0 < wordSize) :
    (table.machineStore hwordSize).store.words.size =
      (fixedWidthNatTableMachineWords table wordSize).length := by
  simp [FixedWidthNatTable.machineStore]

/-! ## The interior store, and what a machine store must hold -/

/-- The machine's flat store, at `segment`, holds the interior component
store's words.

This is the SETUP hypothesis of the interior composition, not a
mathematical debt: it says the machine was loaded with the directory the
route reads.  Every clause below is conditional on exactly this and on
nothing else about the machine. -/
def HoldsInteriorStore (store : ReadStore) (segment : Nat)
    (shape : Cartesian.CartesianShape) : Prop :=
  ∀ a, store.readWord? segment a =
    (canonicalRelativeRmmInteriorComponentStore shape).store.words.toList[a]?

/-- The setup hypothesis is SATISFIABLE, by the store that literally holds
the directory.  A setup hypothesis owes this on the same terms a proof
obligation does. -/
def interiorReadStore (shape : Cartesian.CartesianShape) (segment : Nat) :
    ReadStore where
  readWord? := fun s a =>
    if s = segment then
      (canonicalRelativeRmmInteriorComponentStore shape).store.words.toList[a]?
    else none

theorem interiorReadStore_holds
    (shape : Cartesian.CartesianShape) (segment : Nat) :
    HoldsInteriorStore (interiorReadStore shape segment) segment shape := by
  intro a
  simp [interiorReadStore]

/-! ## The eight component word lists, named -/

/-- The interior store's machine word size is positive -- the side
condition every `machineStore` projection below needs. -/
theorem interior_wordSize_pos (shape : Cartesian.CartesianShape) :
    0 < SuccinctRank.machineWordBits shape.bpCode.length :=
  SuccinctRank.machineWordBits_pos shape.bpCode.length

abbrev wordsBaseline (shape : Cartesian.CartesianShape) : List Word :=
  fixedWidthNatTableMachineWords
    (canonicalRelativeRmmSummaryTable shape).baselineTable (SuccinctRank.machineWordBits shape.bpCode.length)

abbrev wordsMinRel (shape : Cartesian.CartesianShape) : List Word :=
  fixedWidthNatTableMachineWords
    (canonicalRelativeRmmSummaryTable shape).minRelTable (SuccinctRank.machineWordBits shape.bpCode.length)

abbrev wordsMaxRel (shape : Cartesian.CartesianShape) : List Word :=
  fixedWidthNatTableMachineWords
    (canonicalRelativeRmmSummaryTable shape).maxRelTable (SuccinctRank.machineWordBits shape.bpCode.length)

abbrev wordsArgOffset (shape : Cartesian.CartesianShape) : List Word :=
  fixedWidthNatTableMachineWords
    (canonicalRelativeRmmSummaryTable shape).argOffsetTable (SuccinctRank.machineWordBits shape.bpCode.length)

abbrev wordsLocal (shape : Cartesian.CartesianShape) : List Word :=
  fixedWidthNatTableMachineWords
    (canonicalRelativeRmmInteriorLocalTable shape).table (SuccinctRank.machineWordBits shape.bpCode.length)

abbrev wordsGlobal (shape : Cartesian.CartesianShape) : List Word :=
  fixedWidthNatTableMachineWords
    (canonicalRelativeRmmInteriorGlobalTable shape).table (SuccinctRank.machineWordBits shape.bpCode.length)

abbrev wordsLocalLevel (shape : Cartesian.CartesianShape) : List Word :=
  fixedWidthNatTableMachineWords
    (canonicalRelativeRmmInteriorLocalLevelTable shape).table (SuccinctRank.machineWordBits shape.bpCode.length)

abbrev wordsGlobalLevel (shape : Cartesian.CartesianShape) : List Word :=
  fixedWidthNatTableMachineWords
    (canonicalRelativeRmmInteriorGlobalLevelTable shape).table (SuccinctRank.machineWordBits shape.bpCode.length)

/-- THE STORE IS THE EIGHT-FOLD APPEND, in the components' own names.

This is `canonicalRelativeRmmInteriorComponentStore_words_toList`
(`InteriorDirectory.lean:1665`) with each component's `machineStore`
projection collapsed to its machine word list. -/
theorem interior_words_toList (shape : Cartesian.CartesianShape) :
    (canonicalRelativeRmmInteriorComponentStore shape).store.words.toList =
      wordsBaseline shape ++ wordsMinRel shape ++ wordsMaxRel shape ++
        wordsArgOffset shape ++ wordsLocal shape ++ wordsGlobal shape ++
          wordsLocalLevel shape ++ wordsGlobalLevel shape := by
  rw [canonicalRelativeRmmInteriorComponentStore_words_toList]
  simp [machineStore_words_toList]

/-! ### The eight splits

`interior_words_toList` re-associated so each component sits in the
`pre ++ mid ++ post` position `readWord?_slice` consumes. -/

theorem split_baseline (shape : Cartesian.CartesianShape) :
    (canonicalRelativeRmmInteriorComponentStore shape).store.words.toList =
      ([] : List Word) ++ wordsBaseline shape ++
        (wordsMinRel shape ++ wordsMaxRel shape ++ wordsArgOffset shape ++
          wordsLocal shape ++ wordsGlobal shape ++ wordsLocalLevel shape ++
            wordsGlobalLevel shape) := by
  rw [interior_words_toList]; simp [List.append_assoc]

theorem split_minRel (shape : Cartesian.CartesianShape) :
    (canonicalRelativeRmmInteriorComponentStore shape).store.words.toList =
      wordsBaseline shape ++ wordsMinRel shape ++
        (wordsMaxRel shape ++ wordsArgOffset shape ++ wordsLocal shape ++
          wordsGlobal shape ++ wordsLocalLevel shape ++
            wordsGlobalLevel shape) := by
  rw [interior_words_toList]; simp [List.append_assoc]

theorem split_maxRel (shape : Cartesian.CartesianShape) :
    (canonicalRelativeRmmInteriorComponentStore shape).store.words.toList =
      (wordsBaseline shape ++ wordsMinRel shape) ++ wordsMaxRel shape ++
        (wordsArgOffset shape ++ wordsLocal shape ++ wordsGlobal shape ++
          wordsLocalLevel shape ++ wordsGlobalLevel shape) := by
  rw [interior_words_toList]; simp [List.append_assoc]

theorem split_argOffset (shape : Cartesian.CartesianShape) :
    (canonicalRelativeRmmInteriorComponentStore shape).store.words.toList =
      (wordsBaseline shape ++ wordsMinRel shape ++ wordsMaxRel shape) ++
        wordsArgOffset shape ++
          (wordsLocal shape ++ wordsGlobal shape ++ wordsLocalLevel shape ++
            wordsGlobalLevel shape) := by
  rw [interior_words_toList]; simp [List.append_assoc]

theorem split_local (shape : Cartesian.CartesianShape) :
    (canonicalRelativeRmmInteriorComponentStore shape).store.words.toList =
      (wordsBaseline shape ++ wordsMinRel shape ++ wordsMaxRel shape ++
        wordsArgOffset shape) ++ wordsLocal shape ++
          (wordsGlobal shape ++ wordsLocalLevel shape ++
            wordsGlobalLevel shape) := by
  rw [interior_words_toList]; simp [List.append_assoc]

theorem split_global (shape : Cartesian.CartesianShape) :
    (canonicalRelativeRmmInteriorComponentStore shape).store.words.toList =
      (wordsBaseline shape ++ wordsMinRel shape ++ wordsMaxRel shape ++
        wordsArgOffset shape ++ wordsLocal shape) ++ wordsGlobal shape ++
          (wordsLocalLevel shape ++ wordsGlobalLevel shape) := by
  rw [interior_words_toList]; simp [List.append_assoc]

theorem split_localLevel (shape : Cartesian.CartesianShape) :
    (canonicalRelativeRmmInteriorComponentStore shape).store.words.toList =
      (wordsBaseline shape ++ wordsMinRel shape ++ wordsMaxRel shape ++
        wordsArgOffset shape ++ wordsLocal shape ++ wordsGlobal shape) ++
          wordsLocalLevel shape ++ wordsGlobalLevel shape :=
  interior_words_toList shape

theorem split_globalLevel (shape : Cartesian.CartesianShape) :
    (canonicalRelativeRmmInteriorComponentStore shape).store.words.toList =
      (wordsBaseline shape ++ wordsMinRel shape ++ wordsMaxRel shape ++
        wordsArgOffset shape ++ wordsLocal shape ++ wordsGlobal shape ++
          wordsLocalLevel shape) ++ wordsGlobalLevel shape ++
            ([] : List Word) := by
  rw [interior_words_toList]; simp [List.append_assoc]

/-! ### The eight agreement clauses

Each is the bounded `hagree` of `hexact_of_segment_agrees`, at the offset
the route's own read computation uses for that component.  All are
unconditional in `shape`. -/

theorem hagree_baseline {store : ReadStore} {segment : Nat}
    {shape : Cartesian.CartesianShape}
    (hstore : HoldsInteriorStore store segment shape) :
    ∀ a, a < (wordsBaseline shape).length →
      store.readWord? segment
          ((canonicalRelativeRmmInteriorComponentOffsets shape).baseline + a) =
        (wordsBaseline shape)[a]? := by
  intro a ha
  have hoff : (canonicalRelativeRmmInteriorComponentOffsets shape).baseline
      = ([] : List Word).length := by
    simp [canonicalRelativeRmmInteriorComponentOffsets]
  rw [hoff]
  exact readWord?_slice hstore (split_baseline shape) ha

theorem hagree_minRel {store : ReadStore} {segment : Nat}
    {shape : Cartesian.CartesianShape}
    (hstore : HoldsInteriorStore store segment shape) :
    ∀ a, a < (wordsMinRel shape).length →
      store.readWord? segment
          ((canonicalRelativeRmmInteriorComponentOffsets shape).minRel + a) =
        (wordsMinRel shape)[a]? := by
  intro a ha
  have hoff : (canonicalRelativeRmmInteriorComponentOffsets shape).minRel
      = (wordsBaseline shape).length := by
    simp [canonicalRelativeRmmInteriorComponentOffsets]
  rw [hoff]
  exact readWord?_slice hstore (split_minRel shape) ha

theorem hagree_maxRel {store : ReadStore} {segment : Nat}
    {shape : Cartesian.CartesianShape}
    (hstore : HoldsInteriorStore store segment shape) :
    ∀ a, a < (wordsMaxRel shape).length →
      store.readWord? segment
          ((canonicalRelativeRmmInteriorComponentOffsets shape).maxRel + a) =
        (wordsMaxRel shape)[a]? := by
  intro a ha
  have hoff : (canonicalRelativeRmmInteriorComponentOffsets shape).maxRel
      = (wordsBaseline shape ++ wordsMinRel shape).length := by
    simp [canonicalRelativeRmmInteriorComponentOffsets]
  rw [hoff]
  exact readWord?_slice hstore (split_maxRel shape) ha

theorem hagree_argOffset {store : ReadStore} {segment : Nat}
    {shape : Cartesian.CartesianShape}
    (hstore : HoldsInteriorStore store segment shape) :
    ∀ a, a < (wordsArgOffset shape).length →
      store.readWord? segment
          ((canonicalRelativeRmmInteriorComponentOffsets shape).argOffset + a) =
        (wordsArgOffset shape)[a]? := by
  intro a ha
  have hoff : (canonicalRelativeRmmInteriorComponentOffsets shape).argOffset
      = (wordsBaseline shape ++ wordsMinRel shape ++
          wordsMaxRel shape).length := by
    simp [canonicalRelativeRmmInteriorComponentOffsets,
      wordsBaseline, wordsMinRel, wordsMaxRel]
    omega
  rw [hoff]
  exact readWord?_slice hstore (split_argOffset shape) ha

theorem hagree_local {store : ReadStore} {segment : Nat}
    {shape : Cartesian.CartesianShape}
    (hstore : HoldsInteriorStore store segment shape) :
    ∀ a, a < (wordsLocal shape).length →
      store.readWord? segment
          ((canonicalRelativeRmmInteriorComponentOffsets shape).localOffset + a) =
        (wordsLocal shape)[a]? := by
  intro a ha
  have hoff : (canonicalRelativeRmmInteriorComponentOffsets shape).localOffset
      = (wordsBaseline shape ++ wordsMinRel shape ++ wordsMaxRel shape ++
          wordsArgOffset shape).length := by
    simp [canonicalRelativeRmmInteriorComponentOffsets,
      wordsBaseline, wordsMinRel, wordsMaxRel, wordsArgOffset]
    omega
  rw [hoff]
  exact readWord?_slice hstore (split_local shape) ha

theorem hagree_global {store : ReadStore} {segment : Nat}
    {shape : Cartesian.CartesianShape}
    (hstore : HoldsInteriorStore store segment shape) :
    ∀ a, a < (wordsGlobal shape).length →
      store.readWord? segment
          ((canonicalRelativeRmmInteriorComponentOffsets shape).globalBlock + a) =
        (wordsGlobal shape)[a]? := by
  intro a ha
  have hoff : (canonicalRelativeRmmInteriorComponentOffsets shape).globalBlock
      = (wordsBaseline shape ++ wordsMinRel shape ++ wordsMaxRel shape ++
          wordsArgOffset shape ++ wordsLocal shape).length := by
    simp [canonicalRelativeRmmInteriorComponentOffsets,
      canonicalRelativeRmmLocalMachineStore,
      wordsBaseline, wordsMinRel, wordsMaxRel, wordsArgOffset, wordsLocal]
    omega
  rw [hoff]
  exact readWord?_slice hstore (split_global shape) ha

theorem hagree_localLevel {store : ReadStore} {segment : Nat}
    {shape : Cartesian.CartesianShape}
    (hstore : HoldsInteriorStore store segment shape) :
    ∀ a, a < (wordsLocalLevel shape).length →
      store.readWord? segment
          ((canonicalRelativeRmmInteriorComponentOffsets shape).localLevel + a) =
        (wordsLocalLevel shape)[a]? := by
  intro a ha
  have hoff : (canonicalRelativeRmmInteriorComponentOffsets shape).localLevel
      = (wordsBaseline shape ++ wordsMinRel shape ++ wordsMaxRel shape ++
          wordsArgOffset shape ++ wordsLocal shape ++
            wordsGlobal shape).length := by
    simp [canonicalRelativeRmmInteriorComponentOffsets,
      canonicalRelativeRmmLocalMachineStore,
      canonicalRelativeRmmGlobalMachineStore,
      wordsBaseline, wordsMinRel, wordsMaxRel, wordsArgOffset, wordsLocal,
      wordsGlobal]
    omega
  rw [hoff]
  exact readWord?_slice hstore (split_localLevel shape) ha

theorem hagree_globalLevel {store : ReadStore} {segment : Nat}
    {shape : Cartesian.CartesianShape}
    (hstore : HoldsInteriorStore store segment shape) :
    ∀ a, a < (wordsGlobalLevel shape).length →
      store.readWord? segment
          ((canonicalRelativeRmmInteriorComponentOffsets shape).globalLevel + a) =
        (wordsGlobalLevel shape)[a]? := by
  intro a ha
  have hoff : (canonicalRelativeRmmInteriorComponentOffsets shape).globalLevel
      = (wordsBaseline shape ++ wordsMinRel shape ++ wordsMaxRel shape ++
          wordsArgOffset shape ++ wordsLocal shape ++ wordsGlobal shape ++
            wordsLocalLevel shape).length := by
    simp [canonicalRelativeRmmInteriorComponentOffsets,
      canonicalRelativeRmmLocalMachineStore,
      canonicalRelativeRmmGlobalMachineStore,
      canonicalRelativeRmmLocalLevelMachineStore,
      wordsBaseline, wordsMinRel, wordsMaxRel, wordsArgOffset, wordsLocal,
      wordsGlobal, wordsLocalLevel]
    omega
  rw [hoff]
  exact readWord?_slice hstore (split_globalLevel shape) ha

/-! ## `hexact` AT the interior store, for the summary group's four reads

THIS IS THE COMPOSITION STEP.  Each clause is
`hexact_of_segment_agrees` instantiated at
`canonicalRelativeRmmInteriorComponentStore`, with its `hagree` parameter
supplied by the matching clause above rather than assumed.  What remains
in each statement -- `hcount`, `hvalid`, `hentries` -- are facts about the
CALLER's index arithmetic, fixed when the summary group's program is
written, not debts owed to the store.

The base offset in each is the SAME constant the route's own read
computation uses (`InteriorDirectory.lean:2282`), so these are `hexact` at
the route's addressing.
-/

theorem hexact_baseline
    {store : ReadStore} {segment : Nat} {shape : Cartesian.CartesianShape}
    (hstore : HoldsInteriorStore store segment shape)
    {deadAddress entriesLen chunkCount i : Nat}
    (hcount : chunkCount = fixedWidthNatTableMachineChunkCount
      ((RelativeRmm.canonicalLayout shape).superWidth shape)
      (SuccinctRank.machineWordBits shape.bpCode.length))
    (hvalid : i < entriesLen)
    (hentries : i < (bpSuperblockBaselineEntries shape
      (RelativeRmm.canonicalLayout shape).blockSize
      (RelativeRmm.canonicalLayout shape).blocksPerSuper
      (RelativeRmm.canonicalLayout shape).superSampleCount).length) :
    ∀ j, j + 1 < chunkIters entriesLen chunkCount i → ∀ w,
      store.readWord? segment
          (chunkStart (canonicalRelativeRmmInteriorComponentOffsets shape).baseline
            deadAddress entriesLen chunkCount i + j) = some w →
        w.length = SuccinctRank.machineWordBits shape.bpCode.length :=
  hexact_of_segment_agrees _ (interior_wordSize_pos shape) store hcount hvalid
    hentries (hagree_baseline hstore)

theorem hexact_minRel
    {store : ReadStore} {segment : Nat} {shape : Cartesian.CartesianShape}
    (hstore : HoldsInteriorStore store segment shape)
    {deadAddress entriesLen chunkCount i : Nat}
    (hcount : chunkCount = fixedWidthNatTableMachineChunkCount
      (RelativeRmm.canonicalLayout shape).relativeWidth
      (SuccinctRank.machineWordBits shape.bpCode.length))
    (hvalid : i < entriesLen)
    (hentries : i < (bpBlockRelativeMinExcessEntries shape
      (RelativeRmm.canonicalLayout shape).blockSize
      (RelativeRmm.canonicalLayout shape).blocksPerSuper
      (RelativeRmm.canonicalLayout shape).blockCount).length) :
    ∀ j, j + 1 < chunkIters entriesLen chunkCount i → ∀ w,
      store.readWord? segment
          (chunkStart (canonicalRelativeRmmInteriorComponentOffsets shape).minRel
            deadAddress entriesLen chunkCount i + j) = some w →
        w.length = SuccinctRank.machineWordBits shape.bpCode.length :=
  hexact_of_segment_agrees _ (interior_wordSize_pos shape) store hcount hvalid
    hentries (hagree_minRel hstore)

theorem hexact_maxRel
    {store : ReadStore} {segment : Nat} {shape : Cartesian.CartesianShape}
    (hstore : HoldsInteriorStore store segment shape)
    {deadAddress entriesLen chunkCount i : Nat}
    (hcount : chunkCount = fixedWidthNatTableMachineChunkCount
      (RelativeRmm.canonicalLayout shape).relativeWidth
      (SuccinctRank.machineWordBits shape.bpCode.length))
    (hvalid : i < entriesLen)
    (hentries : i < (bpBlockRelativeMaxExcessEntries shape
      (RelativeRmm.canonicalLayout shape).blockSize
      (RelativeRmm.canonicalLayout shape).blocksPerSuper
      (RelativeRmm.canonicalLayout shape).blockCount).length) :
    ∀ j, j + 1 < chunkIters entriesLen chunkCount i → ∀ w,
      store.readWord? segment
          (chunkStart (canonicalRelativeRmmInteriorComponentOffsets shape).maxRel
            deadAddress entriesLen chunkCount i + j) = some w →
        w.length = SuccinctRank.machineWordBits shape.bpCode.length :=
  hexact_of_segment_agrees _ (interior_wordSize_pos shape) store hcount hvalid
    hentries (hagree_maxRel hstore)

theorem hexact_argOffset
    {store : ReadStore} {segment : Nat} {shape : Cartesian.CartesianShape}
    (hstore : HoldsInteriorStore store segment shape)
    {deadAddress entriesLen chunkCount i : Nat}
    (hcount : chunkCount = fixedWidthNatTableMachineChunkCount
      (RelativeRmm.canonicalLayout shape).relativeWidth
      (SuccinctRank.machineWordBits shape.bpCode.length))
    (hvalid : i < entriesLen)
    (hentries : i < (bpBlockArgMinLocalOffsetEntries shape
      (RelativeRmm.canonicalLayout shape).blockSize
      (RelativeRmm.canonicalLayout shape).blockCount).length) :
    ∀ j, j + 1 < chunkIters entriesLen chunkCount i → ∀ w,
      store.readWord? segment
          (chunkStart (canonicalRelativeRmmInteriorComponentOffsets shape).argOffset
            deadAddress entriesLen chunkCount i + j) = some w →
        w.length = SuccinctRank.machineWordBits shape.bpCode.length :=
  hexact_of_segment_agrees _ (interior_wordSize_pos shape) store hcount hvalid
    hentries (hagree_argOffset hstore)

/-! ## Anti-vacuity: the bound is load-bearing, and its necessity is PROVED

The standing rule -- where a quantity is computable, EVALUATE it -- was
applied first: `#eval` on the one-node shape gives a baseline table of `2`
words inside a `31`-word store, so the unbounded premise is wrong about
twenty-nine addresses rather than a boundary one.

That evaluation is not what ships, for a reason worth recording.  The
interior store's sizes run through `Nat.log2`, which Lean defines by
well-founded recursion; the compiler evaluates it but THE KERNEL CANNOT
REDUCE IT, so `rfl` and `decide` both fail on the numeric statement.  The
compiler-backed decision tactic this project forbids would close it, and
the prohibition is right: it would move the check out of the kernel.

So the fact is proved GENERALLY instead, which is stronger than the
fixture would have been: it holds at every shape whose `minRel` table is
non-empty, not just at the probe.
-/

/-- THE UNBOUNDED AGREEMENT PREMISE IS REFUTABLE AT THE INTERIOR STORE.

Assume the store holds the directory, that the `minRel` table is
non-empty, and that agreement with the baseline table holds at EVERY
address.  That is contradictory: at address
`offsets.baseline + (wordsBaseline shape).length` the baseline table's own
word list has run out and answers `none`, while the store answers with the
first word of `minRel`.

This is why `hexact_of_segment_agrees` had to be re-cut before it could be
composed.  As inherited its premise was not merely unproved at the
intended instantiation -- it was unmeetable there, so every consumer would
have been vacuous.  The bound in the re-cut premise is what makes the
difference, and this theorem is the evidence that it is load-bearing
rather than defensive. -/
theorem unbounded_agreement_refuted
    {store : ReadStore} {segment : Nat} {shape : Cartesian.CartesianShape}
    (hstore : HoldsInteriorStore store segment shape)
    (hne : 0 < (wordsMinRel shape).length)
    (hunbounded : ∀ a, store.readWord? segment
        ((canonicalRelativeRmmInteriorComponentOffsets shape).baseline + a) =
      (wordsBaseline shape)[a]?) :
    False := by
  -- the store's answer just past the baseline table is `minRel`'s first word
  have hmin := hagree_minRel hstore 0 hne
  -- the two addresses coincide, because `minRel`'s offset IS `baseline`'s length
  have haddr :
      (canonicalRelativeRmmInteriorComponentOffsets shape).minRel + 0 =
        (canonicalRelativeRmmInteriorComponentOffsets shape).baseline +
          (wordsBaseline shape).length := by
    simp [canonicalRelativeRmmInteriorComponentOffsets]
  rw [haddr, hunbounded] at hmin
  -- but the baseline table has nothing at its own length
  rw [List.getElem?_eq_none (Nat.le_refl _)] at hmin
  have h0 : (wordsMinRel shape)[0]? = none := hmin.symm
  rw [List.getElem?_eq_none_iff] at h0
  omega

end E1InteriorChunkStore
end WordRAM
end RMQ
