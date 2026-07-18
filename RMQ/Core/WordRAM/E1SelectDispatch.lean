import RMQ.Core.WordRAM.E1DenseSelectBlock
import RMQ.Core.WordRAM.E1SelectLegBlocks

/-!
# E1 amended machine: top-level select-close dispatch (M3c-6c)

The accepted select-close routing evaluator
`SparseExceptionSelectData.bpChunkedSelectTraceResultWithStore`
(`ChargedRankSelectLeafTrace.lean:1157`) is a five-way dispatch:

* an occurrence-range guard `idx < occurrenceCount bits target`;
* a super entry-table 4-read at `selectSuperSlot q superStride`, whose
  absence answers `none`;
* if the super entry is marked, the LONG leg (already simulated by
  `E1SelectLegBlocks.longLegBlock_runsTo`);
* otherwise a local entry-table 4-read at
  `relativeSplitSelectLocalSlot q ...`, whose absence answers `none`;
* if the local entry is marked, the SPARSE leg
  (`E1SelectLegBlocks.sparseLegBlock_runsTo`), else the DENSE two-word
  leg (`E1DenseSelectBlock.denseSelectLegBlock_runsTo`).

This module composes those three simulated legs, the two entry reads
(`E1SelectBridge.entryReadBlock_runsTo`) and the routing arithmetic into
one 405-instruction block whose receipts are POSITIONALLY EQUAL to the
whole dispatch's trace, across all six control branches (out-of-range,
super-miss, long, local-miss, sparse, dense).

`queryOccurrence data idx = idx` definitionally (`Source.lean:1851`), so
the machine's `xQ` is a register copy of `xIdx`; the copy is kept because
the leg blocks read the query from `xQ`.

GOTCHA recorded for the worklog: the SPARSE compact slot uses
`data.sparseDirectory.localStride`, which is NOT `data.localStride` (the
latter drives `relativeSplitSelectLocalSlotInSuper`).  The block takes
both as separate parameters `LS` and `DLS`.
-/

namespace RMQ
namespace WordRAM
namespace E1SelectDispatch

open E1Machine
open E1RankBlock
open E1SelectBridge
open E1SelectLegBlocks
open E1DenseSelectBlock
open RMQ.SuccinctClose
open RMQ.GenericSelect

/-! ## Straight-line segments -/

/--
Dispatch prologue: pin the three loop constants (`rOne`, `rC`, `rEight`)
that the dense leg requires, load the per-shape occurrence count into
`rA`, copy the query index into `xQ` (`queryOccurrence` is the identity),
and compare.  `rB` ends holding the in-range indicator.
-/
def selectPrologue (c OC : Nat) : List Instr :=
  [ .const rOne 1
  , .const rC c
  , .const rEight 8
  , .const rA OC
  , .move xQ xIdx
  , .natLt rB xIdx rA ]

@[simp] theorem selectPrologue_length (c OC : Nat) :
    (selectPrologue c OC).length = 6 := rfl

/-- Super-slot computation: `selectSuperSlot q superStride = q / SS` into
`rPos` (the rank-block input for the long leg) and `rP` (the entry-read
slot input). -/
def selectSuperSlotSeg (SS : Nat) : List Instr :=
  [ .divConst rPos xQ SS
  , .move rP rPos ]

@[simp] theorem selectSuperSlotSeg_length (SS : Nat) :
    (selectSuperSlotSeg SS).length = 2 := rfl

/--
Local-slot computation:
`relativeSplitSelectLocalSlot q SS LSPS LS super =
  selectSuperSlot q SS * LSPS + (q - super.baseOccurrence) / LS`,
reusing the super slot still resident in `rPos`, and leaving the local
slot in both `rPos` (sparse rank-block input) and `rP` (entry-read
input).
-/
def selectLocalSlotSeg (LSPS LS : Nat) : List Instr :=
  [ .mulConst rA rPos LSPS
  , .sub rB xSF1 rOne
  , .sub rB xQ rB
  , .divConst rB rB LS
  , .add rPos rA rB
  , .move rP rPos ]

@[simp] theorem selectLocalSlotSeg_length (LSPS LS : Nat) :
    (selectLocalSlotSeg LSPS LS).length = 6 := rfl

/--
Dense-leg base computation:
`relativeSplitSelectLocalBasePosition WS super loc =
  (super.baseWordIndex + loc.baseWordIndex) * WS + loc.firstOffset` into
`xBPos`, and
`relativeSplitSelectLocalBaseOccurrence super loc =
  super.baseOccurrence + loc.baseOccurrence` into `xBOcc`, from the
shifted field encodes in the extension bank.
-/
def selectDenseBaseSeg (WS : Nat) : List Instr :=
  [ .sub rA xSF2 rOne
  , .sub rB xLF2 rOne
  , .add rA rA rB
  , .mulConst rA rA WS
  , .sub rB xLF4 rOne
  , .add xBPos rA rB
  , .sub rA xSF1 rOne
  , .sub rB xLF1 rOne
  , .add xBOcc rA rB ]

@[simp] theorem selectDenseBaseSeg_length (WS : Nat) :
    (selectDenseBaseSeg WS).length = 9 := rfl

/-! ## The dispatch block -/

/--
The select-close dispatch at block base `A` (405 instructions).  Layout:

| range | contents |
| --- | --- |
| `A+0..A+5` | `selectPrologue` (pin constants, occurrence count, `xQ`, compare) |
| `A+6..A+7` | range branch (`A+8` in range, else the `none` tail) |
| `A+8..A+9` | super slot into `rPos`/`rP` |
| `A+10..A+21` | super entry 4-read into `xSF1..xSF4` |
| `A+22` | super-miss branch to the `none` tail |
| `A+23..A+24` | marked test on `super.rankBefore`, branch to LONG |
| `A+25..A+30` | local slot into `rPos`/`rP` |
| `A+31..A+42` | local entry 4-read into `xLF1..xLF4` |
| `A+43` | local-miss branch to the `none` tail |
| `A+44..A+45` | marked test on `loc.rankBefore`, branch to SPARSE |
| `A+46..A+54` | dense base position/occurrence into `xBPos`/`xBOcc` |
| `A+55..A+247` | DENSE two-word leg |
| `A+248..A+249` | jump to END |
| `A+250..A+322` | LONG leg |
| `A+323..A+324` | jump to END |
| `A+325..A+401` | SPARSE leg |
| `A+402..A+403` | jump to END |
| `A+404` | `none` tail (`rVal := 0`) |
| `A+405` | END |

Segment parameters: `S1..S4` super entry field segments, `M1..M4` local
entry field segments, `GL`/`RL` the long flag rank seeds and relative
table, `GS`/`RS` the sparse directory's, `G` the dense chunk base (the
chunk table is at `G + 4`), `W` the packed bit words, `ST` the select
chunk table.  Numeric parameters: chunk width `c`, occurrence count `OC`,
super stride `SS`, local slots per super `LSPS`, local stride `LS`,
DIRECTORY local stride `DLS`, word size `WS`, bit length `N2`, and the
two rank blocks' per-shape constants.
-/
def selectCloseBlock
    (A S1 S2 S3 S4 M1 M2 M3 M4 GL RL GS RS G W ST : Nat)
    (c OC SS LSPS LS DLS WS N2 : Nat)
    (LLen LWS LBPS SLen SWS SBPS : Nat) : List Instr :=
  selectPrologue c OC ++
    ([ .brNZ rB (A + 8), .brNZ rOne (A + 404) ] ++
      (selectSuperSlotSeg SS ++
        (entryReadBlock S1 S2 S3 S4 xSF1 xSF2 xSF3 xSF4 ++
          ([ .brNZ rA (A + 404) ] ++
            ([ .sub rB xSF3 rOne, .brNZ rB (A + 250) ] ++
              (selectLocalSlotSeg LSPS LS ++
                (entryReadBlock M1 M2 M3 M4 xLF1 xLF2 xLF3 xLF4 ++
                  ([ .brNZ rA (A + 404) ] ++
                    ([ .sub rB xLF3 rOne, .brNZ rB (A + 325) ] ++
                      (selectDenseBaseSeg WS ++
                        (denseSelectLegBlock (A + 55) W G ST c WS N2 ++
                          ([ .const rB 1, .brNZ rB (A + 405) ] ++
                            (longLegBlock (A + 250) GL (G + 4) RL SS WS c
                                LLen LWS LBPS ++
                              ([ .const rB 1, .brNZ rB (A + 405) ] ++
                                (sparseLegBlock (A + 325) GS (G + 4) RS
                                    DLS WS c SLen SWS SBPS ++
                                  ([ .const rB 1, .brNZ rB (A + 405) ] ++
                                    [ .const rVal 0 ]))))))))))))))))

@[simp] theorem selectCloseBlock_length
    (A S1 S2 S3 S4 M1 M2 M3 M4 GL RL GS RS G W ST : Nat)
    (c OC SS LSPS LS DLS WS N2 : Nat)
    (LLen LWS LBPS SLen SWS SBPS : Nat) :
    (selectCloseBlock A S1 S2 S3 S4 M1 M2 M3 M4 GL RL GS RS G W ST
      c OC SS LSPS LS DLS WS N2 LLen LWS LBPS SLen SWS SBPS).length =
      405 := by
  simp [selectCloseBlock]

/-! ## Straightness certificates -/

theorem selectPrologue_straight (c OC : Nat) :
    ∀ instr ∈ selectPrologue c OC, instr.isStraight = true := by
  intro instr hi
  simp only [selectPrologue, List.mem_cons, List.not_mem_nil,
    or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem selectSuperSlotSeg_straight (SS : Nat) :
    ∀ instr ∈ selectSuperSlotSeg SS, instr.isStraight = true := by
  intro instr hi
  simp only [selectSuperSlotSeg, List.mem_cons, List.not_mem_nil,
    or_false] at hi
  rcases hi with rfl | rfl <;> rfl

theorem selectLocalSlotSeg_straight (LSPS LS : Nat) :
    ∀ instr ∈ selectLocalSlotSeg LSPS LS, instr.isStraight = true := by
  intro instr hi
  simp only [selectLocalSlotSeg, List.mem_cons, List.not_mem_nil,
    or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem selectDenseBaseSeg_straight (WS : Nat) :
    ∀ instr ∈ selectDenseBaseSeg WS, instr.isStraight = true := by
  intro instr hi
  simp only [selectDenseBaseSeg, List.mem_cons, List.not_mem_nil,
    or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rfl

/-! ## Route-side entry abbreviations -/

/-- The accepted super entry-table value at the dispatch's super slot. -/
def superEntry
    {bits : List Bool} {target : Bool} {rso rbo : Nat}
    (data : SparseExceptionSelectData bits target rso rbo)
    (layout : SparseExceptionSelectTraceSegmentLayout)
    (store : ReadStore) (idx : Nat) :
    Option SparseDenseSelectDenseLocalEntry :=
  (data.superTable.readTraceResultRelabeledWithStore layout.superTable
    store (selectSuperSlot idx data.superStride)).value

/-- The accepted local entry-table value at the dispatch's local slot. -/
def localEntry
    {bits : List Bool} {target : Bool} {rso rbo : Nat}
    (data : SparseExceptionSelectData bits target rso rbo)
    (layout : SparseExceptionSelectTraceSegmentLayout)
    (store : ReadStore) (idx : Nat)
    (super : SparseDenseSelectDenseLocalEntry) :
    Option SparseDenseSelectDenseLocalEntry :=
  (data.localTable.readTraceResultRelabeledWithStore layout.localTable
    store
    (relativeSplitSelectLocalSlot idx data.superStride
      data.localSlotsPerSuper data.localStride super)).value

/-! ## Derived category logs -/

/-- Categories charged by the dispatch prologue. -/
def selectPrologueCats : List Category :=
  [ .registerWrite, .registerWrite, .registerWrite, .registerWrite
  , .registerWrite, .comparison ]

@[simp] theorem selectPrologueCats_eq (c OC : Nat) :
    (selectPrologue c OC).map Instr.category = selectPrologueCats := rfl

/-- Categories charged by the super-slot computation. -/
def selectSuperSlotCats : List Category := [ .arithmetic, .registerWrite ]

@[simp] theorem selectSuperSlotCats_eq (SS : Nat) :
    (selectSuperSlotSeg SS).map Instr.category = selectSuperSlotCats := rfl

/-- Categories charged by the local-slot computation. -/
def selectLocalSlotCats : List Category :=
  [ .arithmetic, .arithmetic, .arithmetic, .arithmetic, .arithmetic
  , .registerWrite ]

@[simp] theorem selectLocalSlotCats_eq (LSPS LS : Nat) :
    (selectLocalSlotSeg LSPS LS).map Instr.category =
      selectLocalSlotCats := rfl

/-- Categories charged by the dense base computation. -/
def selectDenseBaseCats : List Category :=
  [ .arithmetic, .arithmetic, .arithmetic, .arithmetic, .arithmetic
  , .arithmetic, .arithmetic, .arithmetic, .arithmetic ]

@[simp] theorem selectDenseBaseCats_eq (WS : Nat) :
    (selectDenseBaseSeg WS).map Instr.category = selectDenseBaseCats := rfl

/--
The dispatch's derived category log: a function of the store and the
route's own decoded entries, matching `bpChunkedSelectTraceResultWithStore`
branch for branch.  Nothing here is asserted — every summand is either a
frozen straight-line segment's `Instr.category` image or one of the three
legs' own derived logs.
-/
def selectCloseCats
    {bits : List Bool} {target : Bool} {rso rbo : Nat}
    (data : SparseExceptionSelectData bits target rso rbo)
    (layout : SparseExceptionSelectTraceSegmentLayout)
    (G ST : Nat) (store : ReadStore) (c idx : Nat) : List Category :=
  if idx < occurrenceCount bits target then
    selectPrologueCats ++
      (Category.branch :: (selectSuperSlotCats ++
        (entryReadCats ++
          (Category.branch ::
            match superEntry data layout store idx with
            | none => [Category.registerWrite]
            | some super =>
                Category.arithmetic :: Category.branch ::
                  if relativeSplitSelectEntryIsMarked super then
                    longLegCats
                      (bpWordChunkCount c
                        (data.longFlagRankData.wordOffset
                          (selectSuperSlot idx data.superStride)))
                      (store.readWord? layout.longRelativeBase
                        (relativeSplitSelectLongCompactSlot
                          (data.longFlagRankData.bpChunkedRankTraceResultWithStore
                            store layout.longFlagRankBase
                            (layout.longFlagRankBase + 1)
                            (layout.longFlagRankBase + 2) (G + 4) c true
                            (selectSuperSlot idx data.superStride)).value
                          (idx - super.baseOccurrence)
                          data.superStride)).isSome ++
                      [Category.registerWrite, Category.branch]
                  else
                    selectLocalSlotCats ++
                      (entryReadCats ++
                        (Category.branch ::
                          match localEntry data layout store idx super with
                          | none => [Category.registerWrite]
                          | some loc =>
                              Category.arithmetic :: Category.branch ::
                                if relativeSplitSelectEntryIsMarked loc then
                                  sparseLegCats
                                    (bpWordChunkCount c
                                      (data.sparseDirectory.rankData.wordOffset
                                        (relativeSplitSelectLocalSlot idx
                                          data.superStride
                                          data.localSlotsPerSuper
                                          data.localStride super)))
                                    (store.readWord?
                                      layout.sparseDirectory.relativeBase
                                      (relativeSplitSelectSparseCompactSlot
                                        (data.sparseDirectory.rankData.bpChunkedRankTraceResultWithStore
                                          store
                                          layout.sparseDirectory.rankBase
                                          (layout.sparseDirectory.rankBase + 1)
                                          (layout.sparseDirectory.rankBase + 2)
                                          (G + 4) c true
                                          (relativeSplitSelectLocalSlot idx
                                            data.superStride
                                            data.localSlotsPerSuper
                                            data.localStride super)).value
                                        (idx -
                                          relativeSplitSelectLocalBaseOccurrence
                                            super loc)
                                        data.sparseDirectory.localStride)).isSome ++
                                    [Category.registerWrite, Category.branch]
                                else
                                  selectDenseBaseCats ++
                                    (denseLegCats store layout.bitWordBase G
                                      ST c data.wordSize
                                      (relativeSplitSelectLocalBasePosition
                                        data.wordSize super loc)
                                      (relativeSplitSelectLocalBaseOccurrence
                                        super loc) idx ++
                                      [Category.registerWrite,
                                        Category.branch])))))))
  else
    selectPrologueCats ++
      [Category.branch, Category.branch, Category.registerWrite]

/-! ## Hosting bundle -/

/-- Rebase a hosting fact along a proved base equality.  Used to keep the
`append_right` peel PROPOSITIONAL: the raw peel produces bases of the form
`A + 6 + 2 + 12 + ...`, and converting those to `A + 248` by defeq would
force a 248-deep `Nat.succ` tower through the kernel.  Every rebase below
is discharged by `simp only [<length lemmas>]; omega` instead. -/
theorem hostRebase {program : E1Machine.Program} {b b' : Nat}
    {code : List Instr} (h : HostedAt program b code) (e : b = b') :
    HostedAt program b' code := by
  subst e; exact h

/-- Length-normalizing arithmetic for the hosting peel. -/
local macro "host_len" : tactic =>
  `(tactic| first
      | omega
      | (simp only [selectPrologue_length, selectSuperSlotSeg_length,
          selectLocalSlotSeg_length, selectDenseBaseSeg_length,
          entryReadBlock_length, denseSelectLegBlock_length,
          longLegBlock_length, sparseLegBlock_length,
          List.length_cons, List.length_nil] <;> omega))

/-- Peel the dispatch block's hosting into its seventeen pieces. -/
theorem selectCloseBlock_hosting {program : E1Machine.Program}
    {A S1 S2 S3 S4 M1 M2 M3 M4 GL RL GS RS G W ST : Nat}
    {c OC SS LSPS LS DLS WS N2 : Nat}
    {LLen LWS LBPS SLen SWS SBPS : Nat}
    (hhost : HostedAt program A
      (selectCloseBlock A S1 S2 S3 S4 M1 M2 M3 M4 GL RL GS RS G W ST
        c OC SS LSPS LS DLS WS N2 LLen LWS LBPS SLen SWS SBPS)) :
    HostedAt program A (selectPrologue c OC) ∧
    program[A + 6]? = some (.brNZ rB (A + 8)) ∧
    program[A + 7]? = some (.brNZ rOne (A + 404)) ∧
    HostedAt program (A + 8) (selectSuperSlotSeg SS) ∧
    HostedAt program (A + 10)
      (entryReadBlock S1 S2 S3 S4 xSF1 xSF2 xSF3 xSF4) ∧
    program[A + 22]? = some (.brNZ rA (A + 404)) ∧
    program[A + 23]? = some (.sub rB xSF3 rOne) ∧
    program[A + 24]? = some (.brNZ rB (A + 250)) ∧
    HostedAt program (A + 25) (selectLocalSlotSeg LSPS LS) ∧
    HostedAt program (A + 31)
      (entryReadBlock M1 M2 M3 M4 xLF1 xLF2 xLF3 xLF4) ∧
    program[A + 43]? = some (.brNZ rA (A + 404)) ∧
    program[A + 44]? = some (.sub rB xLF3 rOne) ∧
    program[A + 45]? = some (.brNZ rB (A + 325)) ∧
    HostedAt program (A + 46) (selectDenseBaseSeg WS) ∧
    HostedAt program (A + 55)
      (denseSelectLegBlock (A + 55) W G ST c WS N2) ∧
    program[A + 248]? = some (.const rB 1) ∧
    program[A + 249]? = some (.brNZ rB (A + 405)) ∧
    HostedAt program (A + 250)
      (longLegBlock (A + 250) GL (G + 4) RL SS WS c LLen LWS LBPS) ∧
    program[A + 323]? = some (.const rB 1) ∧
    program[A + 324]? = some (.brNZ rB (A + 405)) ∧
    HostedAt program (A + 325)
      (sparseLegBlock (A + 325) GS (G + 4) RS DLS WS c SLen SWS SBPS) ∧
    program[A + 402]? = some (.const rB 1) ∧
    program[A + 403]? = some (.brNZ rB (A + 405)) ∧
    program[A + 404]? = some (.const rVal 0) := by
  have h1 := hostRebase (HostedAt.append_right hhost)
    (show A + (selectPrologue c OC).length = A + 6 by host_len)
  have h2 := hostRebase (HostedAt.append_right h1)
    (show A + 6 + 2 = A + 8 by host_len)
  have h3 := hostRebase (HostedAt.append_right h2)
    (show A + 8 + (selectSuperSlotSeg SS).length = A + 10 by host_len)
  have h4 := hostRebase (HostedAt.append_right h3)
    (show A + 10 +
      (entryReadBlock S1 S2 S3 S4 xSF1 xSF2 xSF3 xSF4).length = A + 22 by
        host_len)
  have h5 := hostRebase (HostedAt.append_right h4)
    (show A + 22 + 1 = A + 23 by host_len)
  have h6 := hostRebase (HostedAt.append_right h5)
    (show A + 23 + 2 = A + 25 by host_len)
  have h7 := hostRebase (HostedAt.append_right h6)
    (show A + 25 + (selectLocalSlotSeg LSPS LS).length = A + 31 by
      host_len)
  have h8 := hostRebase (HostedAt.append_right h7)
    (show A + 31 +
      (entryReadBlock M1 M2 M3 M4 xLF1 xLF2 xLF3 xLF4).length = A + 43 by
        host_len)
  have h9 := hostRebase (HostedAt.append_right h8)
    (show A + 43 + 1 = A + 44 by host_len)
  have h10 := hostRebase (HostedAt.append_right h9)
    (show A + 44 + 2 = A + 46 by host_len)
  have h11 := hostRebase (HostedAt.append_right h10)
    (show A + 46 + (selectDenseBaseSeg WS).length = A + 55 by host_len)
  have h12 := hostRebase (HostedAt.append_right h11)
    (show A + 55 + (denseSelectLegBlock (A + 55) W G ST c WS N2).length =
      A + 248 by host_len)
  have h13 := hostRebase (HostedAt.append_right h12)
    (show A + 248 + 2 = A + 250 by host_len)
  have h14 := hostRebase (HostedAt.append_right h13)
    (show A + 250 +
      (longLegBlock (A + 250) GL (G + 4) RL SS WS c LLen LWS LBPS).length =
      A + 323 by host_len)
  have h15 := hostRebase (HostedAt.append_right h14)
    (show A + 323 + 2 = A + 325 by host_len)
  have h16 := hostRebase (HostedAt.append_right h15)
    (show A + 325 +
      (sparseLegBlock (A + 325) GS (G + 4) RS DLS WS c SLen SWS
        SBPS).length = A + 402 by host_len)
  have h17 := hostRebase (HostedAt.append_right h16)
    (show A + 402 + 2 = A + 404 by host_len)
  refine ⟨HostedAt.append_left hhost, ?_, ?_,
    HostedAt.append_left h2, HostedAt.append_left h3, ?_, ?_, ?_,
    HostedAt.append_left h6, HostedAt.append_left h7, ?_, ?_, ?_,
    HostedAt.append_left h10, HostedAt.append_left h11, ?_, ?_,
    HostedAt.append_left h13, ?_, ?_,
    HostedAt.append_left h15, ?_, ?_, ?_⟩
  · exact (HostedAt.append_left h1).head
  · exact ((HostedAt.append_left h1).tail).head
  · exact (HostedAt.append_left h4).head
  · exact (HostedAt.append_left h5).head
  · exact ((HostedAt.append_left h5).tail).head
  · exact (HostedAt.append_left h8).head
  · exact (HostedAt.append_left h9).head
  · exact ((HostedAt.append_left h9).tail).head
  · exact (HostedAt.append_left h12).head
  · exact ((HostedAt.append_left h12).tail).head
  · exact (HostedAt.append_left h14).head
  · exact ((HostedAt.append_left h14).tail).head
  · exact (HostedAt.append_left h16).head
  · exact ((HostedAt.append_left h16).tail).head
  · exact h17.head

end E1SelectDispatch
end WordRAM
end RMQ
