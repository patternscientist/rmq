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

/-! ## Symbolic-evaluation macros -/

local macro "disp_eval" : tactic =>
  `(tactic| straight_eval [selectPrologue, selectSuperSlotSeg,
      selectLocalSlotSeg, selectDenseBaseSeg,
      rPos, rVal, rP, rWI, rSI, rE, rSup, rBlk, rWrd,
      rR, rK, rT, rV, rSlot, rA, rB, rOne, rC, rEight, rJC,
      xIdx, xQ, xSF1, xSF2, xSF3, xSF4, xLF1, xLF2, xLF3, xLF4,
      xBPos, xBOcc])

local macro "disp_writes" : tactic =>
  `(tactic| straight_writes [rPos, rVal, rP, rWI, rSI, rE, rSup,
      rBlk, rWrd, rR, rK, rT, rV, rSlot, rA, rB, rOne, rC, rEight, rJC,
      xIdx, xQ, xSF1, xSF2, xSF3, xSF4, xLF1, xLF2, xLF3, xLF4,
      xBPos, xBOcc])

/-! ## Straight-line segment simulations -/

/-- The dispatch prologue: pins the three dense-leg constants, loads the
occurrence count, copies the query index into `xQ`, and leaves the
in-range indicator in `rB`. -/
theorem dispatchPrologue_runsTo
    (store : ReadStore) {program : E1Machine.Program} {A c OC : Nat}
    (hhost : HostedAt program A (selectPrologue c OC))
    (regs0 : RegFile) :
    ∃ regsP : RegFile,
      RunsTo store program ⟨regs0, A, false⟩ ⟨regsP, A + 6, false⟩ []
        selectPrologueCats ∧
      regsP rOne = 1 ∧ regsP rC = c ∧ regsP rEight = 8 ∧
      regsP xQ = regs0 xIdx ∧
      regsP rB = (if regs0 xIdx < OC then 1 else 0) ∧
      (∀ r, r ≠ 22 → r ≠ 23 → r ≠ 24 → r ≠ 25 → r ≠ 26 → r ≠ 29 →
        regsP r = regs0 r) := by
  have hrun := RunsTo.straight store (selectPrologue c OC)
    (selectPrologue_straight c OC) A hhost regs0
  obtain ⟨regsP, hregsP⟩ :
      ∃ x, straightRegs store (selectPrologue c OC) regs0 = x := ⟨_, rfl⟩
  rw [hregsP] at hrun
  have hreads : straightReads store (selectPrologue c OC) regs0 = [] := by
    disp_eval
  rw [hreads, selectPrologueCats_eq, selectPrologue_length] at hrun
  refine ⟨regsP, hrun, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hregsP]; disp_eval
  · rw [← hregsP]; disp_eval
  · rw [← hregsP]; disp_eval
  · rw [← hregsP]; disp_eval
  · rw [← hregsP]; disp_eval
  · intro r h1 h2 h3 h4 h5 h6
    rw [← hregsP]
    apply straightRegs_preserves
    intro instr hi
    simp only [selectPrologue, List.mem_cons, List.not_mem_nil,
      or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      disp_writes <;> omega

/-- The super-slot segment: `selectSuperSlot q SS` into `rPos` and `rP`. -/
theorem dispatchSuperSlot_runsTo
    (store : ReadStore) {program : E1Machine.Program} {A SS : Nat}
    (hhost : HostedAt program A (selectSuperSlotSeg SS))
    (regs0 : RegFile) :
    ∃ regsS : RegFile,
      RunsTo store program ⟨regs0, A, false⟩ ⟨regsS, A + 2, false⟩ []
        selectSuperSlotCats ∧
      regsS rPos = regs0 xQ / SS ∧ regsS rP = regs0 xQ / SS ∧
      (∀ r, r ≠ 8 → r ≠ 10 → regsS r = regs0 r) := by
  have hrun := RunsTo.straight store (selectSuperSlotSeg SS)
    (selectSuperSlotSeg_straight SS) A hhost regs0
  obtain ⟨regsS, hregsS⟩ :
      ∃ x, straightRegs store (selectSuperSlotSeg SS) regs0 = x := ⟨_, rfl⟩
  rw [hregsS] at hrun
  have hreads :
      straightReads store (selectSuperSlotSeg SS) regs0 = [] := by
    disp_eval
  rw [hreads, selectSuperSlotCats_eq, selectSuperSlotSeg_length] at hrun
  refine ⟨regsS, hrun, ?_, ?_, ?_⟩
  · rw [← hregsS]; disp_eval
  · rw [← hregsS]; disp_eval
  · intro r h1 h2
    rw [← hregsS]
    apply straightRegs_preserves
    intro instr hi
    simp only [selectSuperSlotSeg, List.mem_cons, List.not_mem_nil,
      or_false] at hi
    rcases hi with rfl | rfl <;> disp_writes <;> omega

/-- The local-slot segment: reusing the super slot in `rPos`, compute
`relativeSplitSelectLocalSlot q SS LSPS LS super` into `rPos` and `rP`. -/
theorem dispatchLocalSlot_runsTo
    (store : ReadStore) {program : E1Machine.Program} {A LSPS LS : Nat}
    (hhost : HostedAt program A (selectLocalSlotSeg LSPS LS))
    (regs0 : RegFile) (hOne : regs0 rOne = 1) :
    ∃ regsL : RegFile,
      RunsTo store program ⟨regs0, A, false⟩ ⟨regsL, A + 6, false⟩ []
        selectLocalSlotCats ∧
      regsL rPos =
        regs0 rPos * LSPS + (regs0 xQ - (regs0 xSF1 - 1)) / LS ∧
      regsL rP =
        regs0 rPos * LSPS + (regs0 xQ - (regs0 xSF1 - 1)) / LS ∧
      (∀ r, r ≠ 8 → r ≠ 10 → r ≠ 22 → r ≠ 23 → regsL r = regs0 r) := by
  have hrun := RunsTo.straight store (selectLocalSlotSeg LSPS LS)
    (selectLocalSlotSeg_straight LSPS LS) A hhost regs0
  obtain ⟨regsL, hregsL⟩ :
      ∃ x, straightRegs store (selectLocalSlotSeg LSPS LS) regs0 = x :=
    ⟨_, rfl⟩
  rw [hregsL] at hrun
  have hreads :
      straightReads store (selectLocalSlotSeg LSPS LS) regs0 = [] := by
    disp_eval
  rw [hreads, selectLocalSlotCats_eq, selectLocalSlotSeg_length] at hrun
  refine ⟨regsL, hrun, ?_, ?_, ?_⟩
  · rw [← hregsL]; disp_eval <;> rw [hOne]
  · rw [← hregsL]; disp_eval <;> rw [hOne]
  · intro r h1 h2 h3 h4
    rw [← hregsL]
    apply straightRegs_preserves
    intro instr hi
    simp only [selectLocalSlotSeg, List.mem_cons, List.not_mem_nil,
      or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      disp_writes <;> omega

/-- The dense base segment: base position into `xBPos`, base occurrence
into `xBOcc`, from the shifted field encodes. -/
theorem dispatchDenseBase_runsTo
    (store : ReadStore) {program : E1Machine.Program} {A WS : Nat}
    (hhost : HostedAt program A (selectDenseBaseSeg WS))
    (regs0 : RegFile) (hOne : regs0 rOne = 1) :
    ∃ regsD : RegFile,
      RunsTo store program ⟨regs0, A, false⟩ ⟨regsD, A + 9, false⟩ []
        selectDenseBaseCats ∧
      regsD xBPos =
        ((regs0 xSF2 - 1) + (regs0 xLF2 - 1)) * WS + (regs0 xLF4 - 1) ∧
      regsD xBOcc = (regs0 xSF1 - 1) + (regs0 xLF1 - 1) ∧
      (∀ r, r ≠ 22 → r ≠ 23 → r ≠ 38 → r ≠ 39 → regsD r = regs0 r) := by
  have hrun := RunsTo.straight store (selectDenseBaseSeg WS)
    (selectDenseBaseSeg_straight WS) A hhost regs0
  obtain ⟨regsD, hregsD⟩ :
      ∃ x, straightRegs store (selectDenseBaseSeg WS) regs0 = x := ⟨_, rfl⟩
  rw [hregsD] at hrun
  have hreads :
      straightReads store (selectDenseBaseSeg WS) regs0 = [] := by
    disp_eval
  rw [hreads, selectDenseBaseCats_eq, selectDenseBaseSeg_length] at hrun
  refine ⟨regsD, hrun, ?_, ?_, ?_⟩
  · rw [← hregsD]; disp_eval <;> rw [hOne]
  · rw [← hregsD]; disp_eval <;> rw [hOne]
  · intro r h1 h2 h3 h4
    rw [← hregsD]
    apply straightRegs_preserves
    intro instr hi
    simp only [selectDenseBaseSeg, List.mem_cons, List.not_mem_nil,
      or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      disp_writes <;> omega

/-! ## The dispatch block at the accepted layout -/

/-- The dispatch block with every segment and constant instantiated from
the accepted select data and its trace segment layout.  All simulation
theorems below are stated against this instantiation. -/
def selectCloseBlockAt
    {bits : List Bool} {rso rbo : Nat}
    (data : SparseExceptionSelectData bits false rso rbo)
    (layout : SparseExceptionSelectTraceSegmentLayout)
    (A G ST c : Nat) : List Instr :=
  selectCloseBlock A
    layout.superTable.baseOccurrence layout.superTable.baseWordIndex
    layout.superTable.rankBefore layout.superTable.firstOffset
    layout.localTable.baseOccurrence layout.localTable.baseWordIndex
    layout.localTable.rankBefore layout.localTable.firstOffset
    layout.longFlagRankBase layout.longRelativeBase
    layout.sparseDirectory.rankBase layout.sparseDirectory.relativeBase
    G layout.bitWordBase ST
    c (occurrenceCount bits false) data.superStride
    data.localSlotsPerSuper data.localStride
    data.sparseDirectory.localStride data.wordSize bits.length
    data.longFlagBits.length data.longFlagRankData.wordSize
    data.longFlagRankData.blocksPerSuper
    data.sparseDirectory.flagBits.length
    data.sparseDirectory.rankData.wordSize
    data.sparseDirectory.rankData.blocksPerSuper

/-! ## Tail helpers -/

/-- The `none` tail at `A + 404`: one register write reaches END with the
`none` packet. -/
theorem dispatchNoneTail_runsTo
    (store : ReadStore) {program : E1Machine.Program} {A : Nat}
    (hNone : program[A + 404]? = some (.const rVal 0)) (regs : RegFile) :
    RunsTo store program ⟨regs, A + 404, false⟩
      ⟨regs.write rVal 0, A + 405, false⟩ [] [Category.registerWrite] :=
  RunsTo.const (s := ⟨regs, A + 404, false⟩) rfl hNone

/-- A leg's unconditional jump to END.  `rOne` cannot serve as the
condition here: the long and sparse legs preserve only `r ≤ 8 ∨ 28 ≤ r`,
so `rOne = 24` may have been clobbered; the two-instruction
`const rB 1; brNZ rB END` idiom is condition-independent. -/
theorem dispatchJump_runsTo
    (store : ReadStore) {program : E1Machine.Program} {A K : Nat}
    (hc : program[K]? = some (.const rB 1))
    (hbr : program[K + 1]? = some (.brNZ rB (A + 405)))
    (regs : RegFile) :
    RunsTo store program ⟨regs, K, false⟩
      ⟨regs.write rB 1, A + 405, false⟩ []
      [Category.registerWrite, Category.branch] := by
  have h1 : RunsTo store program ⟨regs, K, false⟩
      ⟨regs.write rB 1, K + 1, false⟩ [] [Category.registerWrite] :=
    RunsTo.const (s := ⟨regs, K, false⟩) rfl hc
  have h2 : RunsTo store program ⟨regs.write rB 1, K + 1, false⟩
      ⟨regs.write rB 1, A + 405, false⟩ [] [Category.branch] :=
    RunsTo.brNZ_taken (s := ⟨regs.write rB 1, K + 1, false⟩) rfl hbr
      (by simp [RegFile.write_same])
  simpa using h1.trans h2

/-! ## Shared prefix: prologue, range branch, super slot, super read -/

/--
The dispatch prefix on the in-range path: from block entry with the query
index in `xIdx`, the machine reaches the super-miss branch at `A + 22`
having emitted EXACTLY the accepted super entry-table read events, with
the four shifted field decodes in the super bank, the miss indicator in
`rA`, the super slot in `rPos`, and the pinned constants live.
-/
theorem selectCloseBlock_prefix_runsTo
    (store : ReadStore) {program : E1Machine.Program}
    {bits : List Bool} {rso rbo : Nat}
    (data : SparseExceptionSelectData bits false rso rbo)
    (layout : SparseExceptionSelectTraceSegmentLayout)
    {A G ST c : Nat}
    (hhost : HostedAt program A (selectCloseBlockAt data layout A G ST c))
    (regs0 : RegFile) (idx : Nat) (hIdx : regs0 xIdx = idx)
    (hrange : idx < occurrenceCount bits false) :
    ∃ regsE : RegFile,
      RunsTo store program ⟨regs0, A, false⟩ ⟨regsE, A + 22, false⟩
        (entryFieldEvents store layout.superTable.baseOccurrence
          layout.superTable.baseWordIndex layout.superTable.rankBefore
          layout.superTable.firstOffset
          (selectSuperSlot idx data.superStride))
        (selectPrologueCats ++
          (Category.branch :: (selectSuperSlotCats ++ entryReadCats))) ∧
      regsE rPos = selectSuperSlot idx data.superStride ∧
      regsE xQ = idx ∧ regsE rOne = 1 ∧ regsE rC = c ∧ regsE rEight = 8 ∧
      regsE xSF1 = decodeRead (store.readWord?
        layout.superTable.baseOccurrence
        (selectSuperSlot idx data.superStride)) ∧
      regsE xSF2 = decodeRead (store.readWord?
        layout.superTable.baseWordIndex
        (selectSuperSlot idx data.superStride)) ∧
      regsE xSF3 = decodeRead (store.readWord?
        layout.superTable.rankBefore
        (selectSuperSlot idx data.superStride)) ∧
      regsE xSF4 = decodeRead (store.readWord?
        layout.superTable.firstOffset
        (selectSuperSlot idx data.superStride)) ∧
      regsE rA =
        ((if decodeRead (store.readWord? layout.superTable.baseOccurrence
            (selectSuperSlot idx data.superStride)) = 0 then 1 else 0) +
          (if decodeRead (store.readWord? layout.superTable.baseWordIndex
            (selectSuperSlot idx data.superStride)) = 0 then 1 else 0) +
          (if decodeRead (store.readWord? layout.superTable.rankBefore
            (selectSuperSlot idx data.superStride)) = 0 then 1 else 0) +
          (if decodeRead (store.readWord? layout.superTable.firstOffset
            (selectSuperSlot idx data.superStride)) = 0 then 1 else 0)) ∧
      (∀ r, r ≤ 7 ∨ r = 28 → regsE r = regs0 r) := by
  obtain ⟨hPro, hbr6, -, hSlotH, hSuperH, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -⟩ := selectCloseBlock_hosting hhost
  obtain ⟨regsP, hrunP, hPOne, hPC, hPEight, hPQ, hPB, hPpres⟩ :=
    dispatchPrologue_runsTo store hPro regs0
  rw [hIdx] at hPQ hPB
  have hPBne : regsP rB ≠ 0 := by rw [hPB, if_pos hrange]; omega
  have hbrun : RunsTo store program ⟨regsP, A + 6, false⟩
      ⟨regsP, A + 8, false⟩ [] [Category.branch] :=
    RunsTo.brNZ_taken (s := ⟨regsP, A + 6, false⟩) rfl hbr6 hPBne
  obtain ⟨regsS, hrunS, hSPos, hSP, hSpres⟩ :=
    dispatchSuperSlot_runsTo store hSlotH regsP
  rw [hPQ] at hSPos hSP
  rw [show A + 8 + 2 = A + 10 from by omega] at hrunS
  have hSP' : regsS rP = selectSuperSlot idx data.superStride := hSP
  obtain ⟨regsE, hrunE, hE1, hE2, hE3, hE4, hEA, hEpres⟩ :=
    entryReadBlock_runsTo store hSuperH (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) regsS
      (selectSuperSlot idx data.superStride) hSP'
  rw [show A + 10 + 12 = A + 22 from by omega] at hrunE
  have hall := hrunP.trans (hbrun.trans (hrunS.trans hrunE))
  -- `omega` cannot see through the register abbrevs (worklog gotcha), so
  -- the open preservation side conditions get their numerals explicitly.
  have nSF1 : xSF1 = 30 := rfl
  have nSF2 : xSF2 = 31 := rfl
  have nSF3 : xSF3 = 32 := rfl
  have nSF4 : xSF4 = 33 := rfl
  have hEpres' : ∀ r, r ≤ 7 ∨ r = 28 → regsE r = regs0 r := by
    intro r hr
    rw [hEpres r (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega),
      hSpres r (by omega) (by omega),
      hPpres r (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega)]
  refine ⟨regsE, by simpa using hall, ?_, ?_, ?_, ?_, ?_, hE1, hE2, hE3,
    hE4, hEA, hEpres'⟩
  · rw [hEpres rPos (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact hSPos
  · rw [hEpres xQ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), hSpres xQ (by decide)
      (by decide)]
    exact hPQ
  · rw [hEpres rOne (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), hSpres rOne (by decide)
      (by decide)]
    exact hPOne
  · rw [hEpres rC (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), hSpres rC (by decide)
      (by decide)]
    exact hPC
  · rw [hEpres rEight (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide),
      hSpres rEight (by decide) (by decide)]
    exact hPEight

/-! ## Entry-decode inversion -/

/--
Inversion of the accepted 4-read entry decode: when the entry table
answers `some entry`, each of the four shifted field decodes is exactly
that field plus one — which is precisely the shifted-encode hypothesis
shape the leg blocks consume, and (being a successor) also witnesses a
zero miss indicator.
-/
theorem entryFields_of_some
    {entries : List SparseDenseSelectDenseLocalEntry} {fieldWidth : Nat}
    (table :
      FixedWidthSparseDenseSelectDenseLocalEntryTable entries fieldWidth)
    (lay : SparseDenseEntryTableTraceSegmentBases)
    (store : ReadStore) (i : Nat)
    {entry : SparseDenseSelectDenseLocalEntry}
    (h : (table.readTraceResultRelabeledWithStore lay store i).value =
      some entry) :
    decodeRead (store.readWord? lay.baseOccurrence i) =
      entry.baseOccurrence + 1 ∧
    decodeRead (store.readWord? lay.baseWordIndex i) =
      entry.baseWordIndex + 1 ∧
    decodeRead (store.readWord? lay.rankBefore i) =
      entry.rankBefore + 1 ∧
    decodeRead (store.readWord? lay.firstOffset i) =
      entry.firstOffset + 1 := by
  rw [entryRead_value_eq] at h
  cases h1 : store.readWord? lay.baseOccurrence i <;>
    cases h2 : store.readWord? lay.baseWordIndex i <;>
      cases h3 : store.readWord? lay.rankBefore i <;>
        cases h4 : store.readWord? lay.firstOffset i <;>
          rw [h1, h2, h3, h4] at h <;>
          simp [FixedWidthSparseDenseSelectDenseLocalEntryTable.entryOfFields]
            at h <;>
          simp [decodeRead, ← h]

/-! ## Branch simulations: the two `none`-answering guards -/

/-- Out-of-range dispatch: the occurrence-range guard is computed by the
machine's own `natLt` on the query operand (REQ-E1-05 shape), the read
projection is empty, and the answer is the `none` packet. -/
theorem selectCloseBlock_runsTo_outOfRange
    (store : ReadStore) {program : E1Machine.Program}
    {bits : List Bool} {rso rbo : Nat}
    (data : SparseExceptionSelectData bits false rso rbo)
    (layout : SparseExceptionSelectTraceSegmentLayout)
    {A G ST c : Nat}
    (hhost : HostedAt program A (selectCloseBlockAt data layout A G ST c))
    (regs0 : RegFile) (idx : Nat) (hIdx : regs0 xIdx = idx)
    (hrange : ¬ idx < occurrenceCount bits false) :
    ∃ regsF : RegFile,
      RunsTo store program ⟨regs0, A, false⟩ ⟨regsF, A + 405, false⟩
        (data.bpChunkedSelectTraceResultWithStore layout (G + 4) ST
          store c idx).trace
        (selectCloseCats data layout G ST store c idx) ∧
      E1Query.decodePacket (regsF rVal) =
        (data.bpChunkedSelectTraceResultWithStore layout (G + 4) ST
          store c idx).value ∧
      (∀ r, r ≤ 7 ∨ r = 28 → regsF r = regs0 r) := by
  obtain ⟨hPro, hbr6, hbr7, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, hNoneH⟩ := selectCloseBlock_hosting hhost
  obtain ⟨regsP, hrunP, hPOne, -, -, hPQ, hPB, hPpres⟩ :=
    dispatchPrologue_runsTo store hPro regs0
  rw [hIdx] at hPQ hPB
  have hPBz : regsP rB = 0 := by rw [hPB, if_neg hrange]
  have hb6 : RunsTo store program ⟨regsP, A + 6, false⟩
      ⟨regsP, A + 7, false⟩ [] [Category.branch] :=
    RunsTo.brNZ_not_taken (s := ⟨regsP, A + 6, false⟩) rfl hbr6 hPBz
  have hOneNe : regsP rOne ≠ 0 := by rw [hPOne]; omega
  have hb7 : RunsTo store program ⟨regsP, A + 7, false⟩
      ⟨regsP, A + 404, false⟩ [] [Category.branch] :=
    RunsTo.brNZ_taken (s := ⟨regsP, A + 7, false⟩) rfl hbr7 hOneNe
  have hnone := dispatchNoneTail_runsTo store hNoneH regsP
  have hall := hrunP.trans (hb6.trans (hb7.trans hnone))
  have nVal : rVal = 9 := rfl
  refine ⟨regsP.write rVal 0, ?_, ?_, ?_⟩
  · have hroute :
        (data.bpChunkedSelectTraceResultWithStore layout (G + 4) ST
          store c idx).trace = [] := by
      simp [SparseExceptionSelectData.bpChunkedSelectTraceResultWithStore,
        hrange]
    have hcats : selectCloseCats data layout G ST store c idx =
        selectPrologueCats ++
          [Category.branch, Category.branch, Category.registerWrite] := by
      simp [selectCloseCats, hrange]
    rw [hroute, hcats]
    simpa using hall
  · rw [RegFile.write_same]
    simp [SparseExceptionSelectData.bpChunkedSelectTraceResultWithStore,
      hrange]
  · intro r hr
    rw [RegFile.write_other _ _ (show r ≠ rVal by omega),
      hPpres r (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega)]

/-- In-range dispatch whose super entry-table read misses: the four field
reads are still charged and still appear in the receipt, and the answer is
the `none` packet. -/
theorem selectCloseBlock_runsTo_superMiss
    (store : ReadStore) {program : E1Machine.Program}
    {bits : List Bool} {rso rbo : Nat}
    (data : SparseExceptionSelectData bits false rso rbo)
    (layout : SparseExceptionSelectTraceSegmentLayout)
    {A G ST c : Nat}
    (hhost : HostedAt program A (selectCloseBlockAt data layout A G ST c))
    (regs0 : RegFile) (idx : Nat) (hIdx : regs0 xIdx = idx)
    (hrange : idx < occurrenceCount bits false)
    (hmiss : superEntry data layout store idx = none) :
    ∃ regsF : RegFile,
      RunsTo store program ⟨regs0, A, false⟩ ⟨regsF, A + 405, false⟩
        (data.bpChunkedSelectTraceResultWithStore layout (G + 4) ST
          store c idx).trace
        (selectCloseCats data layout G ST store c idx) ∧
      E1Query.decodePacket (regsF rVal) =
        (data.bpChunkedSelectTraceResultWithStore layout (G + 4) ST
          store c idx).value ∧
      (∀ r, r ≤ 7 ∨ r = 28 → regsF r = regs0 r) := by
  obtain ⟨-, -, -, -, -, hbr22, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, hNoneH⟩ := selectCloseBlock_hosting hhost
  obtain ⟨regsE, hrunE, -, -, -, -, -, hE1, hE2, hE3, hE4, hEA,
    hEpres⟩ :=
    selectCloseBlock_prefix_runsTo store data layout hhost regs0 idx hIdx
      hrange
  have hmissRaw :
      (data.superTable.readTraceResultRelabeledWithStore layout.superTable
        store (selectSuperSlot idx data.superStride)).value = none := hmiss
  have hmiss' := hmissRaw
  rw [entryRead_value_eq] at hmiss'
  have hAne : regsE rA ≠ 0 := by
    intro h0
    rw [hEA] at h0
    obtain ⟨h1, h2, h3, h4⟩ := (missSum_eq_zero_iff _ _ _ _).mp h0
    rw [entryOfFields_decode_some h1 h2 h3 h4] at hmiss'
    exact absurd hmiss' (by simp)
  have hb22 : RunsTo store program ⟨regsE, A + 22, false⟩
      ⟨regsE, A + 404, false⟩ [] [Category.branch] :=
    RunsTo.brNZ_taken (s := ⟨regsE, A + 22, false⟩) rfl hbr22 hAne
  have hnone := dispatchNoneTail_runsTo store hNoneH regsE
  have hall := hrunE.trans (hb22.trans hnone)
  have nVal : rVal = 9 := rfl
  refine ⟨regsE.write rVal 0, ?_, ?_, ?_⟩
  · have hroute :
        (data.bpChunkedSelectTraceResultWithStore layout (G + 4) ST
            store c idx).trace =
          entryFieldEvents store layout.superTable.baseOccurrence
            layout.superTable.baseWordIndex layout.superTable.rankBefore
            layout.superTable.firstOffset
            (selectSuperSlot idx data.superStride) := by
      simp only [SparseExceptionSelectData.bpChunkedSelectTraceResultWithStore,
        SparseExceptionSelectData.queryOccurrence, if_pos hrange,
        TraceResult.bind_trace]
      rw [entryRead_trace_eq, hmissRaw]
      simp
    have hcats : selectCloseCats data layout G ST store c idx =
        selectPrologueCats ++
          (Category.branch :: (selectSuperSlotCats ++
            (entryReadCats ++
              [Category.branch, Category.registerWrite]))) := by
      simp only [selectCloseCats, if_pos hrange, hmiss]
    rw [hroute, hcats]
    simpa using hall
  · rw [RegFile.write_same]
    simp only [SparseExceptionSelectData.bpChunkedSelectTraceResultWithStore,
      SparseExceptionSelectData.queryOccurrence, if_pos hrange,
      TraceResult.bind_value]
    rw [hmissRaw]
    simp
  · intro r hr
    rw [RegFile.write_other _ _ (show r ≠ rVal by omega), hEpres r hr]

/-! ## Branch simulation: the long exception leg -/

/-- In-range dispatch whose super entry is present and MARKED: control
takes the long leg (exception rank on the long flag bits, then one
relative-offset read).  Seed presence and the offset bound are route-side
hypotheses, discharged at canonical instantiation. -/
theorem selectCloseBlock_runsTo_long
    (store : ReadStore) {program : E1Machine.Program}
    {bits : List Bool} {rso rbo : Nat}
    (data : SparseExceptionSelectData bits false rso rbo)
    (layout : SparseExceptionSelectTraceSegmentLayout)
    {A G ST c : Nat}
    (hhost : HostedAt program A (selectCloseBlockAt data layout A G ST c))
    (regs0 : RegFile) (idx : Nat) (hIdx : regs0 xIdx = idx)
    (hrange : idx < occurrenceCount bits false)
    {super : SparseDenseSelectDenseLocalEntry}
    (hsome : superEntry data layout store idx = some super)
    (hmarked : relativeSplitSelectEntryIsMarked super = true)
    {superWord deltaWord w : List Bool}
    (hseedS : store.readWord? layout.longFlagRankBase
      (data.longFlagRankData.superIndex
        (selectSuperSlot idx data.superStride)) = some superWord)
    (hseedB : store.readWord? (layout.longFlagRankBase + 1)
      (data.longFlagRankData.wordIndex
        (selectSuperSlot idx data.superStride)) = some deltaWord)
    (hseedW : store.readWord? (layout.longFlagRankBase + 2)
      (data.longFlagRankData.wordIndex
        (selectSuperSlot idx data.superStride)) = some w)
    (hoff : data.longFlagRankData.wordOffset
      (selectSuperSlot idx data.superStride) ≤ w.length) :
    ∃ regsF : RegFile,
      RunsTo store program ⟨regs0, A, false⟩ ⟨regsF, A + 405, false⟩
        (data.bpChunkedSelectTraceResultWithStore layout (G + 4) ST
          store c idx).trace
        (selectCloseCats data layout G ST store c idx) ∧
      E1Query.decodePacket (regsF rVal) =
        (data.bpChunkedSelectTraceResultWithStore layout (G + 4) ST
          store c idx).value ∧
      (∀ r, r ≤ 7 ∨ r = 28 → regsF r = regs0 r) := by
  obtain ⟨-, -, -, -, -, hbr22, hsub23, hbr24, -, -, -, -, -, -, -,
    -, -, hLongH, hc323, hbr324, -, -, -, -⟩ :=
    selectCloseBlock_hosting hhost
  obtain ⟨regsE, hrunE, hEPos, hEQ, hEOne, -, -, hE1, hE2, hE3, hE4,
    hEA, hEpres⟩ :=
    selectCloseBlock_prefix_runsTo store data layout hhost regs0 idx
      hIdx hrange
  obtain ⟨hf1, hf2, hf3, hf4⟩ :=
    entryFields_of_some data.superTable layout.superTable store
      (selectSuperSlot idx data.superStride) hsome
  have hA0 : regsE rA = 0 := by rw [hEA, hf1, hf2, hf3, hf4]; simp
  have hb22 : RunsTo store program ⟨regsE, A + 22, false⟩
      ⟨regsE, A + 23, false⟩ [] [Category.branch] :=
    RunsTo.brNZ_not_taken (s := ⟨regsE, A + 22, false⟩) rfl hbr22 hA0
  have hsub : RunsTo store program ⟨regsE, A + 23, false⟩
      ⟨regsE.write rB (regsE xSF3 - regsE rOne), A + 24, false⟩ []
      [Category.arithmetic] :=
    RunsTo.sub (s := ⟨regsE, A + 23, false⟩) rfl hsub23
  obtain ⟨regsM, hregsM⟩ :
      ∃ x, regsE.write rB (regsE xSF3 - regsE rOne) = x := ⟨_, rfl⟩
  rw [hregsM] at hsub
  have hMpres : ∀ r, r ≠ 23 → regsM r = regsE r := by
    intro r hr
    rw [← hregsM]
    exact RegFile.write_other _ _ hr
  have hMB : regsM rB = super.rankBefore := by
    rw [← hregsM, RegFile.write_same, hE3, hf3, hEOne]
    omega
  have hMBne : regsM rB ≠ 0 := by
    rw [hMB]
    exact (relativeSplitSelectEntryIsMarked_iff super).mp hmarked
  have hb24 : RunsTo store program ⟨regsM, A + 24, false⟩
      ⟨regsM, A + 250, false⟩ [] [Category.branch] :=
    RunsTo.brNZ_taken (s := ⟨regsM, A + 24, false⟩) rfl hbr24 hMBne
  have hMPos : regsM rPos = selectSuperSlot idx data.superStride := by
    rw [hMpres rPos (by decide)]; exact hEPos
  have hMQ : regsM xQ = idx := by rw [hMpres xQ (by decide)]; exact hEQ
  have hMF1 : regsM xSF1 = super.baseOccurrence + 1 := by
    rw [hMpres xSF1 (by decide), hE1]; exact hf1
  have hMF2 : regsM xSF2 = super.baseWordIndex + 1 := by
    rw [hMpres xSF2 (by decide), hE2]; exact hf2
  have hMF4 : regsM xSF4 = super.firstOffset + 1 := by
    rw [hMpres xSF4 (by decide), hE4]; exact hf4
  have hsS : store.readWord? layout.longFlagRankBase
      (data.longFlagRankData.superIndex (regsM rPos)) = some superWord := by
    rw [hMPos]; exact hseedS
  have hsB : store.readWord? (layout.longFlagRankBase + 1)
      (data.longFlagRankData.wordIndex (regsM rPos)) = some deltaWord := by
    rw [hMPos]; exact hseedB
  have hsW : store.readWord? (layout.longFlagRankBase + 2)
      (data.longFlagRankData.wordIndex (regsM rPos)) = some w := by
    rw [hMPos]; exact hseedW
  have hsO : data.longFlagRankData.wordOffset (regsM rPos) ≤ w.length := by
    rw [hMPos]; exact hoff
  obtain ⟨regsL, hrunL, hdecL, hpresL⟩ :=
    longLegBlock_runsTo store data.longFlagRankData hLongH regsM super
      idx hMQ hMF1 hMF2 hMF4 hsS hsB hsW hsO
  rw [show A + 250 + 73 = A + 323 from by omega] at hrunL
  rw [hMPos] at hrunL hdecL
  have hjump := dispatchJump_runsTo store hc323 hbr324 regsL
  have hall :=
    hrunE.trans (hb22.trans (hsub.trans (hb24.trans (hrunL.trans hjump))))
  have hsomeRaw :
      (data.superTable.readTraceResultRelabeledWithStore layout.superTable
        store (selectSuperSlot idx data.superStride)).value =
      some super := hsome
  have nVal : rVal = 9 := rfl
  have nB : rB = 23 := rfl
  refine ⟨regsL.write rB 1, ?_, ?_, ?_⟩
  · have hroute :
        (data.bpChunkedSelectTraceResultWithStore layout (G + 4) ST
            store c idx).trace =
          entryFieldEvents store layout.superTable.baseOccurrence
            layout.superTable.baseWordIndex layout.superTable.rankBefore
            layout.superTable.firstOffset
            (selectSuperSlot idx data.superStride) ++
          (TraceResult.bind
            (data.longFlagRankData.bpChunkedRankTraceResultWithStore store
              layout.longFlagRankBase (layout.longFlagRankBase + 1)
              (layout.longFlagRankBase + 2) (G + 4) c true
              (selectSuperSlot idx data.superStride))
            (fun exceptionRank =>
              bpRelativeOffsetReadTraceResultWithStore store
                layout.longRelativeBase
                (relativeSplitSelectEntryBasePosition data.wordSize super)
                (relativeSplitSelectLongCompactSlot exceptionRank
                  (idx - super.baseOccurrence) data.superStride))).trace := by
      simp only [SparseExceptionSelectData.bpChunkedSelectTraceResultWithStore,
        SparseExceptionSelectData.queryOccurrence, if_pos hrange,
        TraceResult.bind_trace]
      rw [entryRead_trace_eq, hsomeRaw]
      simp [hmarked]
    have hcats : selectCloseCats data layout G ST store c idx =
        selectPrologueCats ++
          (Category.branch :: (selectSuperSlotCats ++
            (entryReadCats ++
              (Category.branch :: Category.arithmetic :: Category.branch ::
                (longLegCats
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
                  [Category.registerWrite, Category.branch]))))) := by
      simp only [selectCloseCats, if_pos hrange, hsome, hmarked, if_true]
    rw [hroute, hcats]
    simpa using hall
  · rw [RegFile.write_other _ _ (show rVal ≠ rB by decide)]
    simp only [SparseExceptionSelectData.bpChunkedSelectTraceResultWithStore,
      SparseExceptionSelectData.queryOccurrence, if_pos hrange,
      TraceResult.bind_value]
    rw [hsomeRaw]
    simp only [hmarked, if_true]
    exact hdecL
  · intro r hr
    rw [RegFile.write_other _ _ (show r ≠ rB by omega),
      hpresL r (by omega) (by omega), hMpres r (by omega), hEpres r hr]

/-! ## Shared local prefix: unmarked super, local slot, local read -/

/--
The dispatch prefix continued past an UNMARKED super entry: the local
slot is computed from the super slot still resident in `rPos` and the
super entry's base occurrence, the local entry table is read, and control
reaches the local-miss branch at `A + 43`.  Receipts are the accepted
super read events followed by the accepted local read events.
-/
theorem selectCloseBlock_localPrefix_runsTo
    (store : ReadStore) {program : E1Machine.Program}
    {bits : List Bool} {rso rbo : Nat}
    (data : SparseExceptionSelectData bits false rso rbo)
    (layout : SparseExceptionSelectTraceSegmentLayout)
    {A G ST c : Nat}
    (hhost : HostedAt program A (selectCloseBlockAt data layout A G ST c))
    (regs0 : RegFile) (idx : Nat) (hIdx : regs0 xIdx = idx)
    (hrange : idx < occurrenceCount bits false)
    {super : SparseDenseSelectDenseLocalEntry}
    (hsome : superEntry data layout store idx = some super)
    (hunmarked : relativeSplitSelectEntryIsMarked super = false) :
    ∃ regsE : RegFile,
      RunsTo store program ⟨regs0, A, false⟩ ⟨regsE, A + 43, false⟩
        (entryFieldEvents store layout.superTable.baseOccurrence
          layout.superTable.baseWordIndex layout.superTable.rankBefore
          layout.superTable.firstOffset
          (selectSuperSlot idx data.superStride) ++
        entryFieldEvents store layout.localTable.baseOccurrence
          layout.localTable.baseWordIndex layout.localTable.rankBefore
          layout.localTable.firstOffset
          (relativeSplitSelectLocalSlot idx data.superStride
            data.localSlotsPerSuper data.localStride super))
        (selectPrologueCats ++
          (Category.branch :: (selectSuperSlotCats ++
            (entryReadCats ++
              (Category.branch :: Category.arithmetic :: Category.branch ::
                (selectLocalSlotCats ++ entryReadCats)))))) ∧
      regsE rPos =
        relativeSplitSelectLocalSlot idx data.superStride
          data.localSlotsPerSuper data.localStride super ∧
      regsE xQ = idx ∧ regsE rOne = 1 ∧ regsE rC = c ∧ regsE rEight = 8 ∧
      regsE xSF1 = super.baseOccurrence + 1 ∧
      regsE xSF2 = super.baseWordIndex + 1 ∧
      regsE xSF4 = super.firstOffset + 1 ∧
      regsE xLF1 = decodeRead (store.readWord?
        layout.localTable.baseOccurrence
        (relativeSplitSelectLocalSlot idx data.superStride
          data.localSlotsPerSuper data.localStride super)) ∧
      regsE xLF2 = decodeRead (store.readWord?
        layout.localTable.baseWordIndex
        (relativeSplitSelectLocalSlot idx data.superStride
          data.localSlotsPerSuper data.localStride super)) ∧
      regsE xLF3 = decodeRead (store.readWord?
        layout.localTable.rankBefore
        (relativeSplitSelectLocalSlot idx data.superStride
          data.localSlotsPerSuper data.localStride super)) ∧
      regsE xLF4 = decodeRead (store.readWord?
        layout.localTable.firstOffset
        (relativeSplitSelectLocalSlot idx data.superStride
          data.localSlotsPerSuper data.localStride super)) ∧
      regsE rA =
        ((if decodeRead (store.readWord? layout.localTable.baseOccurrence
            (relativeSplitSelectLocalSlot idx data.superStride
              data.localSlotsPerSuper data.localStride super)) = 0
          then 1 else 0) +
          (if decodeRead (store.readWord? layout.localTable.baseWordIndex
            (relativeSplitSelectLocalSlot idx data.superStride
              data.localSlotsPerSuper data.localStride super)) = 0
          then 1 else 0) +
          (if decodeRead (store.readWord? layout.localTable.rankBefore
            (relativeSplitSelectLocalSlot idx data.superStride
              data.localSlotsPerSuper data.localStride super)) = 0
          then 1 else 0) +
          (if decodeRead (store.readWord? layout.localTable.firstOffset
            (relativeSplitSelectLocalSlot idx data.superStride
              data.localSlotsPerSuper data.localStride super)) = 0
          then 1 else 0)) ∧
      (∀ r, r ≤ 7 ∨ r = 28 → regsE r = regs0 r) := by
  obtain ⟨-, -, -, -, -, hbr22, hsub23, hbr24, hLocalSlotH, hLocalH, -,
    -, -, -, -, -, -, -, -, -, -, -, -, -⟩ :=
    selectCloseBlock_hosting hhost
  obtain ⟨regsP, hrunP, hPPos, hPQ, hPOne, hPC, hPEight, hP1, hP2, hP3,
    hP4, hPA, hPpres⟩ :=
    selectCloseBlock_prefix_runsTo store data layout hhost regs0 idx
      hIdx hrange
  obtain ⟨hf1, hf2, hf3, hf4⟩ :=
    entryFields_of_some data.superTable layout.superTable store
      (selectSuperSlot idx data.superStride) hsome
  have hA0 : regsP rA = 0 := by rw [hPA, hf1, hf2, hf3, hf4]; simp
  have hb22 : RunsTo store program ⟨regsP, A + 22, false⟩
      ⟨regsP, A + 23, false⟩ [] [Category.branch] :=
    RunsTo.brNZ_not_taken (s := ⟨regsP, A + 22, false⟩) rfl hbr22 hA0
  have hsub : RunsTo store program ⟨regsP, A + 23, false⟩
      ⟨regsP.write rB (regsP xSF3 - regsP rOne), A + 24, false⟩ []
      [Category.arithmetic] :=
    RunsTo.sub (s := ⟨regsP, A + 23, false⟩) rfl hsub23
  obtain ⟨regsM, hregsM⟩ :
      ∃ x, regsP.write rB (regsP xSF3 - regsP rOne) = x := ⟨_, rfl⟩
  rw [hregsM] at hsub
  have hMpres : ∀ r, r ≠ 23 → regsM r = regsP r := by
    intro r hr
    rw [← hregsM]
    exact RegFile.write_other _ _ hr
  have hrankZero : super.rankBefore = 0 := by
    simpa [relativeSplitSelectEntryIsMarked] using hunmarked
  have hMB : regsM rB = 0 := by
    rw [← hregsM, RegFile.write_same, hP3, hf3, hPOne, hrankZero]
  have hb24 : RunsTo store program ⟨regsM, A + 24, false⟩
      ⟨regsM, A + 25, false⟩ [] [Category.branch] :=
    RunsTo.brNZ_not_taken (s := ⟨regsM, A + 24, false⟩) rfl hbr24 hMB
  have hMOne : regsM rOne = 1 := by
    rw [hMpres rOne (by decide)]; exact hPOne
  obtain ⟨regsS, hrunS, hSPos, hSP, hSpres⟩ :=
    dispatchLocalSlot_runsTo store hLocalSlotH regsM hMOne
  rw [show A + 25 + 6 = A + 31 from by omega] at hrunS
  have hslot :
      regsM rPos * data.localSlotsPerSuper +
          (regsM xQ - (regsM xSF1 - 1)) / data.localStride =
        relativeSplitSelectLocalSlot idx data.superStride
          data.localSlotsPerSuper data.localStride super := by
    rw [hMpres rPos (by decide), hMpres xQ (by decide),
      hMpres xSF1 (by decide), hPPos, hPQ, hP1, hf1]
    simp [relativeSplitSelectLocalSlot, relativeSplitSelectLocalSlotInSuper]
  rw [hslot] at hSPos hSP
  obtain ⟨regsE, hrunE, hE1, hE2, hE3, hE4, hEA, hEpres⟩ :=
    entryReadBlock_runsTo store hLocalH (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) regsS
      (relativeSplitSelectLocalSlot idx data.superStride
        data.localSlotsPerSuper data.localStride super) hSP
  rw [show A + 31 + 12 = A + 43 from by omega] at hrunE
  have hall :=
    hrunP.trans (hb22.trans (hsub.trans (hb24.trans (hrunS.trans hrunE))))
  have nLF1 : xLF1 = 34 := rfl
  have nLF2 : xLF2 = 35 := rfl
  have nLF3 : xLF3 = 36 := rfl
  have nLF4 : xLF4 = 37 := rfl
  have hchain : ∀ r, r ≠ 34 → r ≠ 35 → r ≠ 36 → r ≠ 37 → r ≠ 19 →
      r ≠ 22 → r ≠ 23 → r ≠ 8 → r ≠ 10 → regsE r = regsP r := by
    intro r h1 h2 h3 h4 h5 h6 h7 h8 h9
    rw [hEpres r (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega),
      hSpres r (by omega) (by omega) (by omega) (by omega),
      hMpres r (by omega)]
  refine ⟨regsE, by simpa using hall, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hE1, hE2, hE3, hE4, hEA, ?_⟩
  · rw [hEpres rPos (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact hSPos
  · rw [hchain xQ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hPQ
  · rw [hchain rOne (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hPOne
  · rw [hchain rC (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hPC
  · rw [hchain rEight (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hPEight
  · rw [hchain xSF1 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), hP1]
    exact hf1
  · rw [hchain xSF2 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), hP2]
    exact hf2
  · rw [hchain xSF4 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), hP4]
    exact hf4
  · intro r hr
    rw [hchain r (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega),
      hPpres r hr]

/-! ## Branch simulations: local miss, sparse leg, dense leg -/

/-- In-range dispatch with an unmarked super entry whose local
entry-table read misses: both 4-reads are charged and appear in the
receipt, and the answer is the `none` packet. -/
theorem selectCloseBlock_runsTo_localMiss
    (store : ReadStore) {program : E1Machine.Program}
    {bits : List Bool} {rso rbo : Nat}
    (data : SparseExceptionSelectData bits false rso rbo)
    (layout : SparseExceptionSelectTraceSegmentLayout)
    {A G ST c : Nat}
    (hhost : HostedAt program A (selectCloseBlockAt data layout A G ST c))
    (regs0 : RegFile) (idx : Nat) (hIdx : regs0 xIdx = idx)
    (hrange : idx < occurrenceCount bits false)
    {super : SparseDenseSelectDenseLocalEntry}
    (hsome : superEntry data layout store idx = some super)
    (hunmarked : relativeSplitSelectEntryIsMarked super = false)
    (hmiss : localEntry data layout store idx super = none) :
    ∃ regsF : RegFile,
      RunsTo store program ⟨regs0, A, false⟩ ⟨regsF, A + 405, false⟩
        (data.bpChunkedSelectTraceResultWithStore layout (G + 4) ST
          store c idx).trace
        (selectCloseCats data layout G ST store c idx) ∧
      E1Query.decodePacket (regsF rVal) =
        (data.bpChunkedSelectTraceResultWithStore layout (G + 4) ST
          store c idx).value ∧
      (∀ r, r ≤ 7 ∨ r = 28 → regsF r = regs0 r) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hbr43, -, -, -, -,
    -, -, -, -, -, -, -, -, hNoneH⟩ := selectCloseBlock_hosting hhost
  obtain ⟨regsE, hrunE, -, -, -, -, -, -, -, -, -, -, -, -, hEA,
    hEpres⟩ :=
    selectCloseBlock_localPrefix_runsTo store data layout hhost regs0 idx
      hIdx hrange hsome hunmarked
  have hmissRaw :
      (data.localTable.readTraceResultRelabeledWithStore layout.localTable
        store (relativeSplitSelectLocalSlot idx data.superStride
          data.localSlotsPerSuper data.localStride super)).value =
      none := hmiss
  have hmiss' := hmissRaw
  rw [entryRead_value_eq] at hmiss'
  have hAne : regsE rA ≠ 0 := by
    intro h0
    rw [hEA] at h0
    obtain ⟨h1, h2, h3, h4⟩ := (missSum_eq_zero_iff _ _ _ _).mp h0
    rw [entryOfFields_decode_some h1 h2 h3 h4] at hmiss'
    exact absurd hmiss' (by simp)
  have hb43 : RunsTo store program ⟨regsE, A + 43, false⟩
      ⟨regsE, A + 404, false⟩ [] [Category.branch] :=
    RunsTo.brNZ_taken (s := ⟨regsE, A + 43, false⟩) rfl hbr43 hAne
  have hnone := dispatchNoneTail_runsTo store hNoneH regsE
  have hall := hrunE.trans (hb43.trans hnone)
  have hsomeRaw :
      (data.superTable.readTraceResultRelabeledWithStore layout.superTable
        store (selectSuperSlot idx data.superStride)).value =
      some super := hsome
  have nVal : rVal = 9 := rfl
  refine ⟨regsE.write rVal 0, ?_, ?_, ?_⟩
  · have hroute :
        (data.bpChunkedSelectTraceResultWithStore layout (G + 4) ST
            store c idx).trace =
          entryFieldEvents store layout.superTable.baseOccurrence
            layout.superTable.baseWordIndex layout.superTable.rankBefore
            layout.superTable.firstOffset
            (selectSuperSlot idx data.superStride) ++
          entryFieldEvents store layout.localTable.baseOccurrence
            layout.localTable.baseWordIndex layout.localTable.rankBefore
            layout.localTable.firstOffset
            (relativeSplitSelectLocalSlot idx data.superStride
              data.localSlotsPerSuper data.localStride super) := by
      simp [SparseExceptionSelectData.bpChunkedSelectTraceResultWithStore,
        SparseExceptionSelectData.queryOccurrence, hrange, hsomeRaw,
        hunmarked, hmissRaw, entryRead_trace_eq]
    have hcats : selectCloseCats data layout G ST store c idx =
        selectPrologueCats ++
          (Category.branch :: (selectSuperSlotCats ++
            (entryReadCats ++
              (Category.branch :: Category.arithmetic :: Category.branch ::
                (selectLocalSlotCats ++
                  (entryReadCats ++
                    [Category.branch, Category.registerWrite])))))) := by
      simp [selectCloseCats, hrange, hsome, hunmarked, hmiss]
    rw [hroute, hcats]
    simpa using hall
  · rw [RegFile.write_same]
    simp [SparseExceptionSelectData.bpChunkedSelectTraceResultWithStore,
      SparseExceptionSelectData.queryOccurrence, hrange, hsomeRaw,
      hunmarked, hmissRaw]
  · intro r hr
    rw [RegFile.write_other _ _ (show r ≠ rVal by omega), hEpres r hr]

/-- In-range dispatch with an unmarked super entry and a MARKED local
entry: control takes the sparse-directory leg. -/
theorem selectCloseBlock_runsTo_sparse
    (store : ReadStore) {program : E1Machine.Program}
    {bits : List Bool} {rso rbo : Nat}
    (data : SparseExceptionSelectData bits false rso rbo)
    (layout : SparseExceptionSelectTraceSegmentLayout)
    {A G ST c : Nat}
    (hhost : HostedAt program A (selectCloseBlockAt data layout A G ST c))
    (regs0 : RegFile) (idx : Nat) (hIdx : regs0 xIdx = idx)
    (hrange : idx < occurrenceCount bits false)
    {super loc : SparseDenseSelectDenseLocalEntry}
    (hsome : superEntry data layout store idx = some super)
    (hunmarked : relativeSplitSelectEntryIsMarked super = false)
    (hlocSome : localEntry data layout store idx super = some loc)
    (hlocMarked : relativeSplitSelectEntryIsMarked loc = true)
    {superWord deltaWord w : List Bool}
    (hseedS : store.readWord? layout.sparseDirectory.rankBase
      (data.sparseDirectory.rankData.superIndex
        (relativeSplitSelectLocalSlot idx data.superStride
          data.localSlotsPerSuper data.localStride super)) =
      some superWord)
    (hseedB : store.readWord? (layout.sparseDirectory.rankBase + 1)
      (data.sparseDirectory.rankData.wordIndex
        (relativeSplitSelectLocalSlot idx data.superStride
          data.localSlotsPerSuper data.localStride super)) =
      some deltaWord)
    (hseedW : store.readWord? (layout.sparseDirectory.rankBase + 2)
      (data.sparseDirectory.rankData.wordIndex
        (relativeSplitSelectLocalSlot idx data.superStride
          data.localSlotsPerSuper data.localStride super)) = some w)
    (hoff : data.sparseDirectory.rankData.wordOffset
      (relativeSplitSelectLocalSlot idx data.superStride
        data.localSlotsPerSuper data.localStride super) ≤ w.length) :
    ∃ regsF : RegFile,
      RunsTo store program ⟨regs0, A, false⟩ ⟨regsF, A + 405, false⟩
        (data.bpChunkedSelectTraceResultWithStore layout (G + 4) ST
          store c idx).trace
        (selectCloseCats data layout G ST store c idx) ∧
      E1Query.decodePacket (regsF rVal) =
        (data.bpChunkedSelectTraceResultWithStore layout (G + 4) ST
          store c idx).value ∧
      (∀ r, r ≤ 7 ∨ r = 28 → regsF r = regs0 r) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hbr43, hsub44, hbr45, -, -,
    -, -, -, -, -, hSparseH, hc402, hbr403, -⟩ :=
    selectCloseBlock_hosting hhost
  obtain ⟨regsE, hrunE, hEPos, hEQ, hEOne, -, -, hES1, hES2, hES4,
    hEL1, hEL2, hEL3, hEL4, hEA, hEpres⟩ :=
    selectCloseBlock_localPrefix_runsTo store data layout hhost regs0 idx
      hIdx hrange hsome hunmarked
  obtain ⟨hg1, hg2, hg3, hg4⟩ :=
    entryFields_of_some data.localTable layout.localTable store
      (relativeSplitSelectLocalSlot idx data.superStride
        data.localSlotsPerSuper data.localStride super) hlocSome
  have hA0 : regsE rA = 0 := by rw [hEA, hg1, hg2, hg3, hg4]; simp
  have hb43 : RunsTo store program ⟨regsE, A + 43, false⟩
      ⟨regsE, A + 44, false⟩ [] [Category.branch] :=
    RunsTo.brNZ_not_taken (s := ⟨regsE, A + 43, false⟩) rfl hbr43 hA0
  have hsub : RunsTo store program ⟨regsE, A + 44, false⟩
      ⟨regsE.write rB (regsE xLF3 - regsE rOne), A + 45, false⟩ []
      [Category.arithmetic] :=
    RunsTo.sub (s := ⟨regsE, A + 44, false⟩) rfl hsub44
  obtain ⟨regsM, hregsM⟩ :
      ∃ x, regsE.write rB (regsE xLF3 - regsE rOne) = x := ⟨_, rfl⟩
  rw [hregsM] at hsub
  have hMpres : ∀ r, r ≠ 23 → regsM r = regsE r := by
    intro r hr
    rw [← hregsM]
    exact RegFile.write_other _ _ hr
  have hMB : regsM rB = loc.rankBefore := by
    rw [← hregsM, RegFile.write_same, hEL3, hg3, hEOne]
    omega
  have hMBne : regsM rB ≠ 0 := by
    rw [hMB]
    exact (relativeSplitSelectEntryIsMarked_iff loc).mp hlocMarked
  have hb45 : RunsTo store program ⟨regsM, A + 45, false⟩
      ⟨regsM, A + 325, false⟩ [] [Category.branch] :=
    RunsTo.brNZ_taken (s := ⟨regsM, A + 45, false⟩) rfl hbr45 hMBne
  have hMPos : regsM rPos =
      relativeSplitSelectLocalSlot idx data.superStride
        data.localSlotsPerSuper data.localStride super := by
    rw [hMpres rPos (by decide)]; exact hEPos
  have hMQ : regsM xQ = idx := by rw [hMpres xQ (by decide)]; exact hEQ
  have hMS1 : regsM xSF1 = super.baseOccurrence + 1 := by
    rw [hMpres xSF1 (by decide)]; exact hES1
  have hMS2 : regsM xSF2 = super.baseWordIndex + 1 := by
    rw [hMpres xSF2 (by decide)]; exact hES2
  have hML1 : regsM xLF1 = loc.baseOccurrence + 1 := by
    rw [hMpres xLF1 (by decide), hEL1]; exact hg1
  have hML2 : regsM xLF2 = loc.baseWordIndex + 1 := by
    rw [hMpres xLF2 (by decide), hEL2]; exact hg2
  have hML4 : regsM xLF4 = loc.firstOffset + 1 := by
    rw [hMpres xLF4 (by decide), hEL4]; exact hg4
  have hsS : store.readWord? layout.sparseDirectory.rankBase
      (data.sparseDirectory.rankData.superIndex (regsM rPos)) =
      some superWord := by rw [hMPos]; exact hseedS
  have hsB : store.readWord? (layout.sparseDirectory.rankBase + 1)
      (data.sparseDirectory.rankData.wordIndex (regsM rPos)) =
      some deltaWord := by rw [hMPos]; exact hseedB
  have hsW : store.readWord? (layout.sparseDirectory.rankBase + 2)
      (data.sparseDirectory.rankData.wordIndex (regsM rPos)) =
      some w := by rw [hMPos]; exact hseedW
  have hsO : data.sparseDirectory.rankData.wordOffset (regsM rPos) ≤
      w.length := by rw [hMPos]; exact hoff
  obtain ⟨regsL, hrunL, hdecL, hpresL⟩ :=
    sparseLegBlock_runsTo store data.sparseDirectory.rankData hSparseH
      regsM super loc idx hMQ hMS1 hMS2 hML1 hML2 hML4 hsS hsB hsW hsO
  rw [show A + 325 + 77 = A + 402 from by omega] at hrunL
  rw [hMPos] at hrunL hdecL
  have hjump := dispatchJump_runsTo store hc402 hbr403 regsL
  have hall :=
    hrunE.trans (hb43.trans (hsub.trans (hb45.trans (hrunL.trans hjump))))
  have hsomeRaw :
      (data.superTable.readTraceResultRelabeledWithStore layout.superTable
        store (selectSuperSlot idx data.superStride)).value =
      some super := hsome
  have hlocRaw :
      (data.localTable.readTraceResultRelabeledWithStore layout.localTable
        store (relativeSplitSelectLocalSlot idx data.superStride
          data.localSlotsPerSuper data.localStride super)).value =
      some loc := hlocSome
  have nVal : rVal = 9 := rfl
  have nB : rB = 23 := rfl
  refine ⟨regsL.write rB 1, ?_, ?_, ?_⟩
  · have hroute :
        (data.bpChunkedSelectTraceResultWithStore layout (G + 4) ST
            store c idx).trace =
          entryFieldEvents store layout.superTable.baseOccurrence
            layout.superTable.baseWordIndex layout.superTable.rankBefore
            layout.superTable.firstOffset
            (selectSuperSlot idx data.superStride) ++
          (entryFieldEvents store layout.localTable.baseOccurrence
            layout.localTable.baseWordIndex layout.localTable.rankBefore
            layout.localTable.firstOffset
            (relativeSplitSelectLocalSlot idx data.superStride
              data.localSlotsPerSuper data.localStride super) ++
          (TraceResult.bind
            (data.sparseDirectory.rankData.bpChunkedRankTraceResultWithStore
              store layout.sparseDirectory.rankBase
              (layout.sparseDirectory.rankBase + 1)
              (layout.sparseDirectory.rankBase + 2) (G + 4) c true
              (relativeSplitSelectLocalSlot idx data.superStride
                data.localSlotsPerSuper data.localStride super))
            (fun exceptionRank =>
              bpRelativeOffsetReadTraceResultWithStore store
                layout.sparseDirectory.relativeBase
                (relativeSplitSelectLocalBasePosition data.wordSize super
                  loc)
                (relativeSplitSelectSparseCompactSlot exceptionRank
                  (idx -
                    relativeSplitSelectLocalBaseOccurrence super loc)
                  data.sparseDirectory.localStride))).trace) := by
      simp [SparseExceptionSelectData.bpChunkedSelectTraceResultWithStore,
        SparseExceptionSelectData.queryOccurrence, hrange, hsomeRaw,
        hunmarked, hlocRaw, hlocMarked, entryRead_trace_eq,
        SparseExceptionDirectory.bpChunkedReadTraceResultWithStore]
    have hcats : selectCloseCats data layout G ST store c idx =
        selectPrologueCats ++
          (Category.branch :: (selectSuperSlotCats ++
            (entryReadCats ++
              (Category.branch :: Category.arithmetic :: Category.branch ::
                (selectLocalSlotCats ++
                  (entryReadCats ++
                    (Category.branch :: Category.arithmetic ::
                      Category.branch ::
                      (sparseLegCats
                        (bpWordChunkCount c
                          (data.sparseDirectory.rankData.wordOffset
                            (relativeSplitSelectLocalSlot idx
                              data.superStride data.localSlotsPerSuper
                              data.localStride super)))
                        (store.readWord?
                          layout.sparseDirectory.relativeBase
                          (relativeSplitSelectSparseCompactSlot
                            (data.sparseDirectory.rankData.bpChunkedRankTraceResultWithStore
                              store layout.sparseDirectory.rankBase
                              (layout.sparseDirectory.rankBase + 1)
                              (layout.sparseDirectory.rankBase + 2)
                              (G + 4) c true
                              (relativeSplitSelectLocalSlot idx
                                data.superStride data.localSlotsPerSuper
                                data.localStride super)).value
                            (idx -
                              relativeSplitSelectLocalBaseOccurrence
                                super loc)
                            data.sparseDirectory.localStride)).isSome ++
                        [Category.registerWrite,
                          Category.branch])))))))) := by
      simp [selectCloseCats, hrange, hsome, hunmarked, hlocSome,
        hlocMarked]
    rw [hroute, hcats]
    simpa using hall
  · rw [RegFile.write_other _ _ (show rVal ≠ rB by decide)]
    have hval :
        (data.bpChunkedSelectTraceResultWithStore layout (G + 4) ST
            store c idx).value =
          (TraceResult.bind
            (data.sparseDirectory.rankData.bpChunkedRankTraceResultWithStore
              store layout.sparseDirectory.rankBase
              (layout.sparseDirectory.rankBase + 1)
              (layout.sparseDirectory.rankBase + 2) (G + 4) c true
              (relativeSplitSelectLocalSlot idx data.superStride
                data.localSlotsPerSuper data.localStride super))
            (fun exceptionRank =>
              bpRelativeOffsetReadTraceResultWithStore store
                layout.sparseDirectory.relativeBase
                (relativeSplitSelectLocalBasePosition data.wordSize super
                  loc)
                (relativeSplitSelectSparseCompactSlot exceptionRank
                  (idx -
                    relativeSplitSelectLocalBaseOccurrence super loc)
                  data.sparseDirectory.localStride))).value := by
      simp [SparseExceptionSelectData.bpChunkedSelectTraceResultWithStore,
        SparseExceptionSelectData.queryOccurrence, hrange, hsomeRaw,
        hunmarked, hlocRaw, hlocMarked,
        SparseExceptionDirectory.bpChunkedReadTraceResultWithStore]
    rw [hval]
    exact hdecL
  · intro r hr
    rw [RegFile.write_other _ _ (show r ≠ rB by omega),
      hpresL r (by omega) (by omega), hMpres r (by omega), hEpres r hr]

/-- In-range dispatch with an unmarked super entry and an unmarked local
entry: control takes the dense two-word leg.  The word-length min chains
are route-side hypotheses, discharged at canonical instantiation. -/
theorem selectCloseBlock_runsTo_dense
    (store : ReadStore) {program : E1Machine.Program}
    {bits : List Bool} {rso rbo : Nat}
    (data : SparseExceptionSelectData bits false rso rbo)
    (layout : SparseExceptionSelectTraceSegmentLayout)
    {A G ST c : Nat}
    (hhost : HostedAt program A (selectCloseBlockAt data layout A G ST c))
    (regs0 : RegFile) (idx : Nat) (hIdx : regs0 xIdx = idx)
    (hrange : idx < occurrenceCount bits false)
    {super loc : SparseDenseSelectDenseLocalEntry}
    (hsome : superEntry data layout store idx = some super)
    (hunmarked : relativeSplitSelectEntryIsMarked super = false)
    (hlocSome : localEntry data layout store idx super = some loc)
    (hlocUnmarked : relativeSplitSelectEntryIsMarked loc = false)
    (hlen1 : ∀ w1, store.readWord? layout.bitWordBase
        (relativeSplitSelectLocalBasePosition data.wordSize super loc /
          data.wordSize) = some w1 →
      w1.length = Nat.min data.wordSize
        (bits.length -
          relativeSplitSelectLocalBasePosition data.wordSize super loc /
            data.wordSize * data.wordSize))
    (hlen2 : ∀ w2, store.readWord? layout.bitWordBase
        (relativeSplitSelectLocalBasePosition data.wordSize super loc /
          data.wordSize + 1) = some w2 →
      w2.length = Nat.min data.wordSize
        (bits.length -
          (relativeSplitSelectLocalBasePosition data.wordSize super loc /
            data.wordSize + 1) * data.wordSize)) :
    ∃ regsF : RegFile,
      RunsTo store program ⟨regs0, A, false⟩ ⟨regsF, A + 405, false⟩
        (data.bpChunkedSelectTraceResultWithStore layout (G + 4) ST
          store c idx).trace
        (selectCloseCats data layout G ST store c idx) ∧
      E1Query.decodePacket (regsF rVal) =
        (data.bpChunkedSelectTraceResultWithStore layout (G + 4) ST
          store c idx).value ∧
      (∀ r, r ≤ 7 ∨ r = 28 → regsF r = regs0 r) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hbr43, hsub44, hbr45,
    hDenseBaseH, hDenseH, hc248, hbr249, -, -, -, -, -, -, -⟩ :=
    selectCloseBlock_hosting hhost
  obtain ⟨regsE, hrunE, -, hEQ, hEOne, hEC, hEEight, hES1, hES2, -,
    hEL1, hEL2, hEL3, hEL4, hEA, hEpres⟩ :=
    selectCloseBlock_localPrefix_runsTo store data layout hhost regs0 idx
      hIdx hrange hsome hunmarked
  obtain ⟨hg1, hg2, hg3, hg4⟩ :=
    entryFields_of_some data.localTable layout.localTable store
      (relativeSplitSelectLocalSlot idx data.superStride
        data.localSlotsPerSuper data.localStride super) hlocSome
  have hA0 : regsE rA = 0 := by rw [hEA, hg1, hg2, hg3, hg4]; simp
  have hb43 : RunsTo store program ⟨regsE, A + 43, false⟩
      ⟨regsE, A + 44, false⟩ [] [Category.branch] :=
    RunsTo.brNZ_not_taken (s := ⟨regsE, A + 43, false⟩) rfl hbr43 hA0
  have hsub : RunsTo store program ⟨regsE, A + 44, false⟩
      ⟨regsE.write rB (regsE xLF3 - regsE rOne), A + 45, false⟩ []
      [Category.arithmetic] :=
    RunsTo.sub (s := ⟨regsE, A + 44, false⟩) rfl hsub44
  obtain ⟨regsM, hregsM⟩ :
      ∃ x, regsE.write rB (regsE xLF3 - regsE rOne) = x := ⟨_, rfl⟩
  rw [hregsM] at hsub
  have hMpres : ∀ r, r ≠ 23 → regsM r = regsE r := by
    intro r hr
    rw [← hregsM]
    exact RegFile.write_other _ _ hr
  have hlocZero : loc.rankBefore = 0 := by
    simpa [relativeSplitSelectEntryIsMarked] using hlocUnmarked
  have hMB : regsM rB = 0 := by
    rw [← hregsM, RegFile.write_same, hEL3, hg3, hEOne, hlocZero]
  have hb45 : RunsTo store program ⟨regsM, A + 45, false⟩
      ⟨regsM, A + 46, false⟩ [] [Category.branch] :=
    RunsTo.brNZ_not_taken (s := ⟨regsM, A + 45, false⟩) rfl hbr45 hMB
  have hMOne : regsM rOne = 1 := by
    rw [hMpres rOne (by decide)]; exact hEOne
  obtain ⟨regsD, hrunD, hDPos, hDOcc, hDpres⟩ :=
    dispatchDenseBase_runsTo store hDenseBaseH regsM hMOne
  rw [show A + 46 + 9 = A + 55 from by omega] at hrunD
  have hDPos' : regsD xBPos =
      relativeSplitSelectLocalBasePosition data.wordSize super loc := by
    rw [hDPos, hMpres xSF2 (by decide), hMpres xLF2 (by decide),
      hMpres xLF4 (by decide), hES2, hEL2, hEL4, hg2, hg4]
    simp [relativeSplitSelectLocalBasePosition]
  have hDOcc' : regsD xBOcc =
      relativeSplitSelectLocalBaseOccurrence super loc := by
    rw [hDOcc, hMpres xSF1 (by decide), hMpres xLF1 (by decide),
      hES1, hEL1, hg1]
    simp [relativeSplitSelectLocalBaseOccurrence]
  have hDQ : regsD xQ = idx := by
    rw [hDpres xQ (by decide) (by decide) (by decide) (by decide),
      hMpres xQ (by decide)]
    exact hEQ
  have hDOne : regsD rOne = 1 := by
    rw [hDpres rOne (by decide) (by decide) (by decide) (by decide)]
    exact hMOne
  have hDC : regsD rC = c := by
    rw [hDpres rC (by decide) (by decide) (by decide) (by decide),
      hMpres rC (by decide)]
    exact hEC
  have hDEight : regsD rEight = 8 := by
    rw [hDpres rEight (by decide) (by decide) (by decide) (by decide),
      hMpres rEight (by decide)]
    exact hEEight
  have hlen1' : ∀ w1, store.readWord? layout.bitWordBase
      (regsD xBPos / data.wordSize) = some w1 →
      w1.length = Nat.min data.wordSize
        (bits.length - regsD xBPos / data.wordSize * data.wordSize) := by
    rw [hDPos']; exact hlen1
  have hlen2' : ∀ w2, store.readWord? layout.bitWordBase
      (regsD xBPos / data.wordSize + 1) = some w2 →
      w2.length = Nat.min data.wordSize
        (bits.length -
          (regsD xBPos / data.wordSize + 1) * data.wordSize) := by
    rw [hDPos']; exact hlen2
  obtain ⟨regsL, hrunL, hdecL, hpresL⟩ :=
    denseSelectLegBlock_runsTo store data.bitWords hDenseH regsD hlen1'
      hlen2' hDOne hDC hDEight
  rw [show A + 55 + 193 = A + 248 from by omega] at hrunL
  rw [hDPos', hDOcc', hDQ] at hrunL hdecL
  have hjump := dispatchJump_runsTo store hc248 hbr249 regsL
  have hall :=
    hrunE.trans (hb43.trans (hsub.trans (hb45.trans (hrunD.trans
      (hrunL.trans hjump)))))
  have hsomeRaw :
      (data.superTable.readTraceResultRelabeledWithStore layout.superTable
        store (selectSuperSlot idx data.superStride)).value =
      some super := hsome
  have hlocRaw :
      (data.localTable.readTraceResultRelabeledWithStore layout.localTable
        store (relativeSplitSelectLocalSlot idx data.superStride
          data.localSlotsPerSuper data.localStride super)).value =
      some loc := hlocSome
  have nVal : rVal = 9 := rfl
  have nB : rB = 23 := rfl
  refine ⟨regsL.write rB 1, ?_, ?_, ?_⟩
  · have hroute :
        (data.bpChunkedSelectTraceResultWithStore layout (G + 4) ST
            store c idx).trace =
          entryFieldEvents store layout.superTable.baseOccurrence
            layout.superTable.baseWordIndex layout.superTable.rankBefore
            layout.superTable.firstOffset
            (selectSuperSlot idx data.superStride) ++
          (entryFieldEvents store layout.localTable.baseOccurrence
            layout.localTable.baseWordIndex layout.localTable.rankBefore
            layout.localTable.firstOffset
            (relativeSplitSelectLocalSlot idx data.superStride
              data.localSlotsPerSuper data.localStride super) ++
          (bpChunkedDenseTwoWordSelectTraceResultWithStore
            layout.bitWordBase (G + 4) ST c false data.bitWords store
            (relativeSplitSelectLocalBasePosition data.wordSize super loc)
            (relativeSplitSelectLocalBaseOccurrence super loc)
            idx).trace) := by
      simp [SparseExceptionSelectData.bpChunkedSelectTraceResultWithStore,
        SparseExceptionSelectData.queryOccurrence, hrange, hsomeRaw,
        hunmarked, hlocRaw, hlocUnmarked, entryRead_trace_eq]
    have hcats : selectCloseCats data layout G ST store c idx =
        selectPrologueCats ++
          (Category.branch :: (selectSuperSlotCats ++
            (entryReadCats ++
              (Category.branch :: Category.arithmetic :: Category.branch ::
                (selectLocalSlotCats ++
                  (entryReadCats ++
                    (Category.branch :: Category.arithmetic ::
                      Category.branch ::
                      (selectDenseBaseCats ++
                        (denseLegCats store layout.bitWordBase G ST c
                          data.wordSize
                          (relativeSplitSelectLocalBasePosition
                            data.wordSize super loc)
                          (relativeSplitSelectLocalBaseOccurrence super
                            loc) idx ++
                          [Category.registerWrite,
                            Category.branch]))))))))) := by
      simp [selectCloseCats, hrange, hsome, hunmarked, hlocSome,
        hlocUnmarked]
    rw [hroute, hcats]
    simpa using hall
  · rw [RegFile.write_other _ _ (show rVal ≠ rB by decide)]
    have hval :
        (data.bpChunkedSelectTraceResultWithStore layout (G + 4) ST
            store c idx).value =
          (bpChunkedDenseTwoWordSelectTraceResultWithStore
            layout.bitWordBase (G + 4) ST c false data.bitWords store
            (relativeSplitSelectLocalBasePosition data.wordSize super loc)
            (relativeSplitSelectLocalBaseOccurrence super loc)
            idx).value := by
      simp [SparseExceptionSelectData.bpChunkedSelectTraceResultWithStore,
        SparseExceptionSelectData.queryOccurrence, hrange, hsomeRaw,
        hunmarked, hlocRaw, hlocUnmarked]
    rw [hval]
    exact hdecL
  · intro r hr
    rw [RegFile.write_other _ _ (show r ≠ rB by omega),
      hpresL r (by omega), hDpres r (by omega) (by omega) (by omega)
        (by omega), hMpres r (by omega), hEpres r hr]

/-! ## The whole select-close dispatch -/

/--
The whole accepted select-close dispatch, all six control branches in one
statement: from block entry with the query index in `xIdx`, the hosted
405-instruction block runs — with exact fuel — to `A + 405` with

* receipts POSITIONALLY EQUAL to
  `(data.bpChunkedSelectTraceResultWithStore layout (G + 4) ST store c
  idx).trace`,
* that evaluator's optional answer under `decodePacket` in `rVal`,
* the derived category log `selectCloseCats`, and
* the query-level registers `r ≤ 7` and the query index `xIdx`
  preserved.

The three route-side hypotheses supply, per branch, the rank seeds the
exception legs read and the dense leg's word-length min chains; each is
conditioned on exactly the branch that consumes it, and all three are
discharged at canonical instantiation from the accepted store's layout
facts.
-/
theorem selectCloseBlock_runsTo
    (store : ReadStore) {program : E1Machine.Program}
    {bits : List Bool} {rso rbo : Nat}
    (data : SparseExceptionSelectData bits false rso rbo)
    (layout : SparseExceptionSelectTraceSegmentLayout)
    {A G ST c : Nat}
    (hhost : HostedAt program A (selectCloseBlockAt data layout A G ST c))
    (regs0 : RegFile) (idx : Nat) (hIdx : regs0 xIdx = idx)
    (hLongSeed : ∀ super, superEntry data layout store idx = some super →
      relativeSplitSelectEntryIsMarked super = true →
      ∃ sw dw w,
        store.readWord? layout.longFlagRankBase
            (data.longFlagRankData.superIndex
              (selectSuperSlot idx data.superStride)) = some sw ∧
        store.readWord? (layout.longFlagRankBase + 1)
            (data.longFlagRankData.wordIndex
              (selectSuperSlot idx data.superStride)) = some dw ∧
        store.readWord? (layout.longFlagRankBase + 2)
            (data.longFlagRankData.wordIndex
              (selectSuperSlot idx data.superStride)) = some w ∧
        data.longFlagRankData.wordOffset
          (selectSuperSlot idx data.superStride) ≤ w.length)
    (hSparseSeed : ∀ super loc,
      superEntry data layout store idx = some super →
      relativeSplitSelectEntryIsMarked super = false →
      localEntry data layout store idx super = some loc →
      relativeSplitSelectEntryIsMarked loc = true →
      ∃ sw dw w,
        store.readWord? layout.sparseDirectory.rankBase
            (data.sparseDirectory.rankData.superIndex
              (relativeSplitSelectLocalSlot idx data.superStride
                data.localSlotsPerSuper data.localStride super)) =
          some sw ∧
        store.readWord? (layout.sparseDirectory.rankBase + 1)
            (data.sparseDirectory.rankData.wordIndex
              (relativeSplitSelectLocalSlot idx data.superStride
                data.localSlotsPerSuper data.localStride super)) =
          some dw ∧
        store.readWord? (layout.sparseDirectory.rankBase + 2)
            (data.sparseDirectory.rankData.wordIndex
              (relativeSplitSelectLocalSlot idx data.superStride
                data.localSlotsPerSuper data.localStride super)) =
          some w ∧
        data.sparseDirectory.rankData.wordOffset
          (relativeSplitSelectLocalSlot idx data.superStride
            data.localSlotsPerSuper data.localStride super) ≤ w.length)
    (hDenseLen : ∀ super loc,
      superEntry data layout store idx = some super →
      relativeSplitSelectEntryIsMarked super = false →
      localEntry data layout store idx super = some loc →
      relativeSplitSelectEntryIsMarked loc = false →
      (∀ w1, store.readWord? layout.bitWordBase
          (relativeSplitSelectLocalBasePosition data.wordSize super loc /
            data.wordSize) = some w1 →
        w1.length = Nat.min data.wordSize
          (bits.length -
            relativeSplitSelectLocalBasePosition data.wordSize super loc /
              data.wordSize * data.wordSize)) ∧
      (∀ w2, store.readWord? layout.bitWordBase
          (relativeSplitSelectLocalBasePosition data.wordSize super loc /
            data.wordSize + 1) = some w2 →
        w2.length = Nat.min data.wordSize
          (bits.length -
            (relativeSplitSelectLocalBasePosition data.wordSize super loc /
              data.wordSize + 1) * data.wordSize))) :
    ∃ regsF : RegFile,
      RunsTo store program ⟨regs0, A, false⟩ ⟨regsF, A + 405, false⟩
        (data.bpChunkedSelectTraceResultWithStore layout (G + 4) ST
          store c idx).trace
        (selectCloseCats data layout G ST store c idx) ∧
      E1Query.decodePacket (regsF rVal) =
        (data.bpChunkedSelectTraceResultWithStore layout (G + 4) ST
          store c idx).value ∧
      (∀ r, r ≤ 7 ∨ r = 28 → regsF r = regs0 r) := by
  by_cases hrange : idx < occurrenceCount bits false
  · cases hsuper : superEntry data layout store idx with
    | none =>
        exact selectCloseBlock_runsTo_superMiss store data layout hhost
          regs0 idx hIdx hrange hsuper
    | some super =>
        by_cases hmk : relativeSplitSelectEntryIsMarked super = true
        · obtain ⟨sw, dw, w, h1, h2, h3, h4⟩ := hLongSeed super hsuper hmk
          exact selectCloseBlock_runsTo_long store data layout hhost
            regs0 idx hIdx hrange hsuper hmk h1 h2 h3 h4
        · have hunm : relativeSplitSelectEntryIsMarked super = false := by
            simpa using hmk
          cases hloc : localEntry data layout store idx super with
          | none =>
              exact selectCloseBlock_runsTo_localMiss store data layout
                hhost regs0 idx hIdx hrange hsuper hunm hloc
          | some loc =>
              by_cases hlmk : relativeSplitSelectEntryIsMarked loc = true
              · obtain ⟨sw, dw, w, h1, h2, h3, h4⟩ :=
                  hSparseSeed super loc hsuper hunm hloc hlmk
                exact selectCloseBlock_runsTo_sparse store data layout
                  hhost regs0 idx hIdx hrange hsuper hunm hloc hlmk
                  h1 h2 h3 h4
              · have hlunm :
                    relativeSplitSelectEntryIsMarked loc = false := by
                  simpa using hlmk
                obtain ⟨hl1, hl2⟩ :=
                  hDenseLen super loc hsuper hunm hloc hlunm
                exact selectCloseBlock_runsTo_dense store data layout
                  hhost regs0 idx hIdx hrange hsuper hunm hloc hlunm
                  hl1 hl2
  · exact selectCloseBlock_runsTo_outOfRange store data layout hhost
      regs0 idx hIdx hrange

end E1SelectDispatch
end WordRAM
end RMQ
