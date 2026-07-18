import RMQ.Core.WordRAM.E1RankTrueBlock
import RMQ.Core.WordRAM.E1SelectBridge

/-!
# E1 amended machine: select-close long and sparse legs (M3c-6a)

The two exception legs of the accepted select-close dispatch
(`bpChunkedSelectTraceResultWithStore`, `ChargedRankSelectLeafTrace.lean`),
each the same shape: a seeded TRUE-target chunked rank block (the
exception rank), slot/base arithmetic from the decoded entry fields in
the extension bank, and one relative-offset read returning the answer
packet.

* `longLegBlock LB GL CH RL SS WS c L WSc BPS` (73 instructions): the
  hosted `rankTrueCloseBlock` at seeds `GL..GL+2`/chunk `CH` on the super
  slot in `rPos`, then `longLegSetup` (re-pin `rOne`, compact slot
  `exceptionRank * SS + (q - super.baseOccurrence)` into `rSlot`, base
  position `super.baseWordIndex * WS + super.firstOffset` into `xBPos`),
  then `relativeReadBlock` at segment `RL`, then the packet move into
  `rVal`.
* `sparseLegBlock LB GS CH RS LS WS c L WSc BPS` (77 instructions): the
  same with the sparse directory's seeds `GS..GS+2`, the local-slot rank
  position, the two-entry base-occurrence/base-position sums, stride
  `LS`, and relative segment `RS`.

The simulation theorems deliver receipts POSITIONALLY EQUAL to the
route-side `TraceResult.bind` of the accepted seeded rank component and
the accepted relative-offset read (exactly the dispatch's long-leg
expression and the body of
`SparseExceptionDirectory.bpChunkedReadTraceResultWithStore`), the
packet under `decodePacket` in `rVal`, and derived category logs.
-/

namespace RMQ
namespace WordRAM
namespace E1SelectLegBlocks

open E1Machine
open E1RankBlock
open E1RankTrueBlock
open E1SelectBridge
open RMQ.SuccinctClose
open RMQ.GenericSelect

/-! ## Setup segments -/

/-- Long-leg setup: re-pin `rOne`, local occurrence
`q - super.baseOccurrence`, compact slot
`exceptionRank * SS + localOccurrence` into `rSlot`, base position
`super.baseWordIndex * WS + super.firstOffset` into `xBPos`. -/
def longLegSetup (SS WS : Nat) : List Instr :=
  [ .const rOne 1
  , .sub rB xSF1 rOne
  , .sub rT xQ rB
  , .mulConst rA rVal SS
  , .add rSlot rA rT
  , .sub rB xSF2 rOne
  , .mulConst rB rB WS
  , .sub rA xSF4 rOne
  , .add xBPos rB rA ]

@[simp] theorem longLegSetup_length (SS WS : Nat) :
    (longLegSetup SS WS).length = 9 := rfl

/-- Sparse-leg setup: re-pin `rOne`, local occurrence
`q - (super.baseOccurrence + loc.baseOccurrence)`, compact slot
`exceptionRank * LS + localOccurrence` into `rSlot`, base position
`(super.baseWordIndex + loc.baseWordIndex) * WS + loc.firstOffset` into
`xBPos`. -/
def sparseLegSetup (LS WS : Nat) : List Instr :=
  [ .const rOne 1
  , .sub rB xSF1 rOne
  , .sub rA xLF1 rOne
  , .add rB rB rA
  , .sub rT xQ rB
  , .mulConst rA rVal LS
  , .add rSlot rA rT
  , .sub rB xSF2 rOne
  , .sub rA xLF2 rOne
  , .add rB rB rA
  , .mulConst rB rB WS
  , .sub rA xLF4 rOne
  , .add xBPos rB rA ]

@[simp] theorem sparseLegSetup_length (LS WS : Nat) :
    (sparseLegSetup LS WS).length = 13 := rfl

/-! ## Leg blocks -/

/--
The long select leg at base `LB`: hosted TRUE-target rank block (seeds
`GL..GL+2`, chunk table `CH`, per-shape constants `L`/`WSc`/`BPS`),
setup, relative read at `RL`, packet move.  Layout: rank `LB..LB+58`,
setup `LB+59..LB+67`, relative read `LB+68..LB+71`, move `LB+72`, end
`LB+73`.
-/
def longLegBlock (LB GL CH RL SS WS c L WSc BPS : Nat) : List Instr :=
  rankTrueCloseBlock LB GL CH c L WSc BPS ++
    (longLegSetup SS WS ++
      (relativeReadBlock (LB + 68) RL ++ [Instr.move rVal rT]))

@[simp] theorem longLegBlock_length (LB GL CH RL SS WS c L WSc BPS : Nat) :
    (longLegBlock LB GL CH RL SS WS c L WSc BPS).length = 73 := rfl

/--
The sparse select leg at base `LB`: hosted TRUE-target rank block (seeds
`GS..GS+2`, chunk table `CH`), setup, relative read at `RS`, packet
move.  Layout: rank `LB..LB+58`, setup `LB+59..LB+71`, relative read
`LB+72..LB+75`, move `LB+76`, end `LB+77`.
-/
def sparseLegBlock (LB GS CH RS LS WS c L WSc BPS : Nat) : List Instr :=
  rankTrueCloseBlock LB GS CH c L WSc BPS ++
    (sparseLegSetup LS WS ++
      (relativeReadBlock (LB + 72) RS ++ [Instr.move rVal rT]))

@[simp] theorem sparseLegBlock_length
    (LB GS CH RS LS WS c L WSc BPS : Nat) :
    (sparseLegBlock LB GS CH RS LS WS c L WSc BPS).length = 77 := rfl

/-! ## Frozen category logs -/

/-- Categories charged by the long-leg setup. -/
def longLegSetupCats : List Category :=
  [ .registerWrite, .arithmetic, .arithmetic, .arithmetic, .arithmetic
  , .arithmetic, .arithmetic, .arithmetic, .arithmetic ]

@[simp] theorem longLegSetupCats_eq (SS WS : Nat) :
    (longLegSetup SS WS).map Instr.category = longLegSetupCats := rfl

/-- Categories charged by the sparse-leg setup. -/
def sparseLegSetupCats : List Category :=
  [ .registerWrite, .arithmetic, .arithmetic, .arithmetic, .arithmetic
  , .arithmetic, .arithmetic, .arithmetic, .arithmetic, .arithmetic
  , .arithmetic, .arithmetic, .arithmetic ]

@[simp] theorem sparseLegSetupCats_eq (LS WS : Nat) :
    (sparseLegSetup LS WS).map Instr.category = sparseLegSetupCats := rfl

/-- Derived long-leg category log: the hit-path rank categories at the
fold chunk count, the setup, the relative read (present/absent), the
packet move. -/
def longLegCats (count : Nat) (present : Bool) : List Category :=
  rankTrueCloseHitCats count ++
    (longLegSetupCats ++
      (relativeReadCats present ++ [Category.registerWrite]))

/-- Derived sparse-leg category log. -/
def sparseLegCats (count : Nat) (present : Bool) : List Category :=
  rankTrueCloseHitCats count ++
    (sparseLegSetupCats ++
      (relativeReadCats present ++ [Category.registerWrite]))

/-! ## Straightness certificates -/

theorem longLegSetup_straight (SS WS : Nat) :
    ∀ instr ∈ longLegSetup SS WS, instr.isStraight = true := by
  intro instr hi
  simp only [longLegSetup, List.mem_cons, List.not_mem_nil,
    or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl <;> rfl

theorem sparseLegSetup_straight (LS WS : Nat) :
    ∀ instr ∈ sparseLegSetup LS WS, instr.isStraight = true := by
  intro instr hi
  simp only [sparseLegSetup, List.mem_cons, List.not_mem_nil,
    or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;> rfl

/-! ## Hosting bundles -/

theorem longLegBlock_hosting {program : E1Machine.Program}
    {LB GL CH RL SS WS c L WSc BPS : Nat}
    (hhost : HostedAt program LB
      (longLegBlock LB GL CH RL SS WS c L WSc BPS)) :
    HostedAt program LB (rankTrueCloseBlock LB GL CH c L WSc BPS) ∧
    HostedAt program (LB + 59) (longLegSetup SS WS) ∧
    HostedAt program (LB + 68) (relativeReadBlock (LB + 68) RL) ∧
    program[LB + 72]? = some (.move rVal rT) := by
  have h1 := HostedAt.append_right hhost
  have h2 := HostedAt.append_right h1
  have h3 := HostedAt.append_right h2
  exact
    ⟨ HostedAt.append_left hhost
    , HostedAt.append_left h1
    , HostedAt.append_left h2
    , h3.head ⟩

theorem sparseLegBlock_hosting {program : E1Machine.Program}
    {LB GS CH RS LS WS c L WSc BPS : Nat}
    (hhost : HostedAt program LB
      (sparseLegBlock LB GS CH RS LS WS c L WSc BPS)) :
    HostedAt program LB (rankTrueCloseBlock LB GS CH c L WSc BPS) ∧
    HostedAt program (LB + 59) (sparseLegSetup LS WS) ∧
    HostedAt program (LB + 72) (relativeReadBlock (LB + 72) RS) ∧
    program[LB + 76]? = some (.move rVal rT) := by
  have h1 := HostedAt.append_right hhost
  have h2 := HostedAt.append_right h1
  have h3 := HostedAt.append_right h2
  exact
    ⟨ HostedAt.append_left hhost
    , HostedAt.append_left h1
    , HostedAt.append_left h2
    , h3.head ⟩

/-! ## Symbolic-evaluation macros -/

local macro "leg_eval" : tactic =>
  `(tactic| straight_eval [longLegSetup, sparseLegSetup,
      rPos, rVal, rP, rWI, rSI, rE, rSup, rBlk, rWrd,
      rR, rK, rT, rV, rSlot, rA, rB, rOne, rC, rEight, rJC,
      xIdx, xQ, xSF1, xSF2, xSF3, xSF4, xLF1, xLF2, xLF3, xLF4,
      xBPos, xBOcc])

local macro "leg_writes" : tactic =>
  `(tactic| straight_writes [rPos, rVal, rP, rWI, rSI, rE, rSup,
      rBlk, rWrd, rR, rK, rT, rV, rSlot, rA, rB, rOne, rC, rEight, rJC,
      xBPos])

/-! ## Long-leg simulation -/

/--
The long select leg: from block entry with the super slot in `rPos`,
the query occurrence in `xQ`, and the decoded super entry fields in the
extension bank (shifted encode), the hosted leg runs — with exact
fuel — to `LB + 73` with

* receipts POSITIONALLY EQUAL to the dispatch's long-leg expression
  (the seeded TRUE rank component bound into the accepted
  relative-offset read),
* that expression's packet under `decodePacket` in `rVal`,
* the derived `longLegCats`, and
* every register `r ≤ 8 ∨ 28 ≤ r` except `xBPos` preserved.

Seed presence and the offset bound are route-side hypotheses discharged
at canonical instantiation.
-/
theorem longLegBlock_runsTo
    (store : ReadStore) {program : E1Machine.Program}
    {LB GL CH RL SS WS c : Nat}
    {bits : List Bool} {so bo qc : Nat}
    (d : SuccinctRank.TwoLevelPayloadLiveStoredWordRankData bits so bo qc)
    (hhost : HostedAt program LB
      (longLegBlock LB GL CH RL SS WS c bits.length d.wordSize
        d.blocksPerSuper))
    (regs0 : RegFile) (super : SparseDenseSelectDenseLocalEntry)
    (q : Nat)
    (hQ : regs0 xQ = q)
    (hF1 : regs0 xSF1 = super.baseOccurrence + 1)
    (hF2 : regs0 xSF2 = super.baseWordIndex + 1)
    (hF4 : regs0 xSF4 = super.firstOffset + 1)
    {superWord deltaWord w : List Bool}
    (hsuper :
      store.readWord? GL (d.superIndex (regs0 rPos)) = some superWord)
    (hblock :
      store.readWord? (GL + 1) (d.wordIndex (regs0 rPos)) =
        some deltaWord)
    (hword :
      store.readWord? (GL + 2) (d.wordIndex (regs0 rPos)) = some w)
    (hoff : d.wordOffset (regs0 rPos) ≤ w.length) :
    ∃ regsF : RegFile,
      RunsTo store program ⟨regs0, LB, false⟩ ⟨regsF, LB + 73, false⟩
        (TraceResult.bind
          (d.bpChunkedRankTraceResultWithStore store GL (GL + 1)
            (GL + 2) CH c true (regs0 rPos))
          (fun exceptionRank =>
            bpRelativeOffsetReadTraceResultWithStore store RL
              (relativeSplitSelectEntryBasePosition WS super)
              (relativeSplitSelectLongCompactSlot exceptionRank
                (q - super.baseOccurrence) SS))).trace
        (longLegCats (bpWordChunkCount c (d.wordOffset (regs0 rPos)))
          (store.readWord? RL
            (relativeSplitSelectLongCompactSlot
              (d.bpChunkedRankTraceResultWithStore store GL (GL + 1)
                (GL + 2) CH c true (regs0 rPos)).value
              (q - super.baseOccurrence) SS)).isSome) ∧
      E1Query.decodePacket (regsF rVal) =
        (TraceResult.bind
          (d.bpChunkedRankTraceResultWithStore store GL (GL + 1)
            (GL + 2) CH c true (regs0 rPos))
          (fun exceptionRank =>
            bpRelativeOffsetReadTraceResultWithStore store RL
              (relativeSplitSelectEntryBasePosition WS super)
              (relativeSplitSelectLongCompactSlot exceptionRank
                (q - super.baseOccurrence) SS))).value ∧
      (∀ r, r ≤ 8 ∨ 28 ≤ r → r ≠ 38 → regsF r = regs0 r) := by
  obtain ⟨hRank, hSetup, hRel, hMove⟩ := longLegBlock_hosting hhost
  obtain ⟨regsR, hrunR, hRVal, hRpres⟩ :=
    rankTrueCloseBlock_runsTo_hit store d hRank regs0 hsuper hblock
      hword hoff
  -- setup
  have hrunS := RunsTo.straight store (longLegSetup SS WS)
    (longLegSetup_straight SS WS) (LB + 59) hSetup regsR
  obtain ⟨regsS, hregsS⟩ :
      ∃ x, straightRegs store (longLegSetup SS WS) regsR = x := ⟨_, rfl⟩
  rw [hregsS] at hrunS
  have hreadsS : straightReads store (longLegSetup SS WS) regsR = [] := by
    leg_eval
  rw [hreadsS] at hrunS
  have hSpres : ∀ r, r ≠ 24 → r ≠ 23 → r ≠ 19 → r ≠ 22 → r ≠ 21 →
      r ≠ 38 → regsS r = regsR r := by
    intro r h1 h2 h3 h4 h5 h6
    rw [← hregsS]
    apply straightRegs_preserves
    intro instr hi
    simp only [longLegSetup, List.mem_cons, List.not_mem_nil,
      or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl <;> leg_writes <;> omega
  have hRQ : regsR xQ = q := by
    rw [hRpres xQ (by decide)]
    exact hQ
  have hRF1 : regsR xSF1 = super.baseOccurrence + 1 := by
    rw [hRpres xSF1 (by decide)]
    exact hF1
  have hRF2 : regsR xSF2 = super.baseWordIndex + 1 := by
    rw [hRpres xSF2 (by decide)]
    exact hF2
  have hRF4 : regsR xSF4 = super.firstOffset + 1 := by
    rw [hRpres xSF4 (by decide)]
    exact hF4
  have hSOne : regsS rOne = 1 := by
    rw [← hregsS]
    leg_eval
  have hSSlot : regsS rSlot =
      relativeSplitSelectLongCompactSlot
        (d.bpChunkedRankTraceResultWithStore store GL (GL + 1) (GL + 2)
          CH c true (regs0 rPos)).value
        (q - super.baseOccurrence) SS := by
    rw [← hregsS]
    leg_eval <;>
      simp [hRVal, hRQ, hRF1, relativeSplitSelectLongCompactSlot]
  have hSBPos : regsS xBPos =
      relativeSplitSelectEntryBasePosition WS super := by
    rw [← hregsS]
    leg_eval <;>
      simp [hRF2, hRF4, relativeSplitSelectEntryBasePosition]
  -- relative read
  obtain ⟨regsRel, hrunRel, hdecRel, hpresRel⟩ :=
    relativeReadBlock_runsTo store hRel regsS
      (relativeSplitSelectEntryBasePosition WS super) hSBPos hSOne
  rw [hSSlot] at hrunRel hdecRel
  -- packet move
  have hmove := RunsTo.move (store := store)
    (s := ⟨regsRel, LB + 72, false⟩) rfl hMove
  have hall := hrunR.trans (hrunS.trans (hrunRel.trans hmove))
  -- route-side composition shape
  have htrace :
      (TraceResult.bind
        (d.bpChunkedRankTraceResultWithStore store GL (GL + 1) (GL + 2)
          CH c true (regs0 rPos))
        (fun exceptionRank =>
          bpRelativeOffsetReadTraceResultWithStore store RL
            (relativeSplitSelectEntryBasePosition WS super)
            (relativeSplitSelectLongCompactSlot exceptionRank
              (q - super.baseOccurrence) SS))).trace =
      (d.bpChunkedRankTraceResultWithStore store GL (GL + 1) (GL + 2)
        CH c true (regs0 rPos)).trace ++
        [TraceEvent.readWord RL
          (relativeSplitSelectLongCompactSlot
            (d.bpChunkedRankTraceResultWithStore store GL (GL + 1)
              (GL + 2) CH c true (regs0 rPos)).value
            (q - super.baseOccurrence) SS)
          (store.readWord? RL
            (relativeSplitSelectLongCompactSlot
              (d.bpChunkedRankTraceResultWithStore store GL (GL + 1)
                (GL + 2) CH c true (regs0 rPos)).value
              (q - super.baseOccurrence) SS))] := by
    simp [TraceResult.bind, bpRelativeOffsetReadTraceResultWithStore,
      TraceResult.map, TraceResult.pure, bpChunkReadTraceResult]
  have hvalue :
      (TraceResult.bind
        (d.bpChunkedRankTraceResultWithStore store GL (GL + 1) (GL + 2)
          CH c true (regs0 rPos))
        (fun exceptionRank =>
          bpRelativeOffsetReadTraceResultWithStore store RL
            (relativeSplitSelectEntryBasePosition WS super)
            (relativeSplitSelectLongCompactSlot exceptionRank
              (q - super.baseOccurrence) SS))).value =
      ((store.readWord? RL
          (relativeSplitSelectLongCompactSlot
            (d.bpChunkedRankTraceResultWithStore store GL (GL + 1)
              (GL + 2) CH c true (regs0 rPos)).value
            (q - super.baseOccurrence) SS)).map
        SuccinctSpace.bitsToNatLE).map
        (fun offset =>
          relativeSplitSelectEntryBasePosition WS super + offset) := by
    simp [TraceResult.bind, bpRelativeOffsetReadTraceResultWithStore,
      TraceResult.map, TraceResult.pure, bpChunkReadTraceResult]
  refine ⟨regsRel.write rVal (regsRel rT), ?_, ?_, ?_⟩
  · rw [htrace]
    simpa [longLegCats] using hall
  · rw [hvalue]
    show E1Query.decodePacket
        (regsRel.write rVal (regsRel rT) rVal) = _
    rw [RegFile.write_same]
    have hfn : bitsToNatLE = SuccinctSpace.bitsToNatLE :=
      funext SuccinctSpace.WordRAMBridge.bitsToNatLE_eq
    rw [← hfn]
    exact hdecRel
  · intro r hr hr38
    have hr9 : r ≠ 9 := by omega
    rw [RegFile.write_other _ _ (show r ≠ rVal from hr9),
      hpresRel r (by omega),
      hSpres r (by omega) (by omega) (by omega) (by omega) (by omega)
        hr38,
      hRpres r hr]

/-! ## Sparse-leg simulation -/

/--
The sparse select leg: from block entry with the local slot in `rPos`,
the query occurrence in `xQ`, and the decoded super and local entry
fields in the extension bank, the hosted leg runs — with exact fuel —
to `LB + 77` with receipts POSITIONALLY EQUAL to the body of the
accepted
`SparseExceptionDirectory.bpChunkedReadTraceResultWithStore` (the
seeded TRUE rank component bound into the accepted relative-offset
read at the sparse compact slot), the packet under `decodePacket` in
`rVal`, the derived `sparseLegCats`, and every register
`r ≤ 8 ∨ 28 ≤ r` except `xBPos` preserved.
-/
theorem sparseLegBlock_runsTo
    (store : ReadStore) {program : E1Machine.Program}
    {LB GS CH RS LS WS c : Nat}
    {bits : List Bool} {so bo qc : Nat}
    (d : SuccinctRank.TwoLevelPayloadLiveStoredWordRankData bits so bo qc)
    (hhost : HostedAt program LB
      (sparseLegBlock LB GS CH RS LS WS c bits.length d.wordSize
        d.blocksPerSuper))
    (regs0 : RegFile) (super loc : SparseDenseSelectDenseLocalEntry)
    (q : Nat)
    (hQ : regs0 xQ = q)
    (hF1 : regs0 xSF1 = super.baseOccurrence + 1)
    (hF2 : regs0 xSF2 = super.baseWordIndex + 1)
    (hL1 : regs0 xLF1 = loc.baseOccurrence + 1)
    (hL2 : regs0 xLF2 = loc.baseWordIndex + 1)
    (hL4 : regs0 xLF4 = loc.firstOffset + 1)
    {superWord deltaWord w : List Bool}
    (hsuper :
      store.readWord? GS (d.superIndex (regs0 rPos)) = some superWord)
    (hblock :
      store.readWord? (GS + 1) (d.wordIndex (regs0 rPos)) =
        some deltaWord)
    (hword :
      store.readWord? (GS + 2) (d.wordIndex (regs0 rPos)) = some w)
    (hoff : d.wordOffset (regs0 rPos) ≤ w.length) :
    ∃ regsF : RegFile,
      RunsTo store program ⟨regs0, LB, false⟩ ⟨regsF, LB + 77, false⟩
        (TraceResult.bind
          (d.bpChunkedRankTraceResultWithStore store GS (GS + 1)
            (GS + 2) CH c true (regs0 rPos))
          (fun exceptionRank =>
            bpRelativeOffsetReadTraceResultWithStore store RS
              (relativeSplitSelectLocalBasePosition WS super loc)
              (relativeSplitSelectSparseCompactSlot exceptionRank
                (q - relativeSplitSelectLocalBaseOccurrence super loc)
                LS))).trace
        (sparseLegCats (bpWordChunkCount c (d.wordOffset (regs0 rPos)))
          (store.readWord? RS
            (relativeSplitSelectSparseCompactSlot
              (d.bpChunkedRankTraceResultWithStore store GS (GS + 1)
                (GS + 2) CH c true (regs0 rPos)).value
              (q - relativeSplitSelectLocalBaseOccurrence super loc)
              LS)).isSome) ∧
      E1Query.decodePacket (regsF rVal) =
        (TraceResult.bind
          (d.bpChunkedRankTraceResultWithStore store GS (GS + 1)
            (GS + 2) CH c true (regs0 rPos))
          (fun exceptionRank =>
            bpRelativeOffsetReadTraceResultWithStore store RS
              (relativeSplitSelectLocalBasePosition WS super loc)
              (relativeSplitSelectSparseCompactSlot exceptionRank
                (q - relativeSplitSelectLocalBaseOccurrence super loc)
                LS))).value ∧
      (∀ r, r ≤ 8 ∨ 28 ≤ r → r ≠ 38 → regsF r = regs0 r) := by
  obtain ⟨hRank, hSetup, hRel, hMove⟩ := sparseLegBlock_hosting hhost
  obtain ⟨regsR, hrunR, hRVal, hRpres⟩ :=
    rankTrueCloseBlock_runsTo_hit store d hRank regs0 hsuper hblock
      hword hoff
  -- setup
  have hrunS := RunsTo.straight store (sparseLegSetup LS WS)
    (sparseLegSetup_straight LS WS) (LB + 59) hSetup regsR
  obtain ⟨regsS, hregsS⟩ :
      ∃ x, straightRegs store (sparseLegSetup LS WS) regsR = x :=
    ⟨_, rfl⟩
  rw [hregsS] at hrunS
  have hreadsS :
      straightReads store (sparseLegSetup LS WS) regsR = [] := by
    leg_eval
  rw [hreadsS] at hrunS
  have hSpres : ∀ r, r ≠ 24 → r ≠ 23 → r ≠ 19 → r ≠ 22 → r ≠ 21 →
      r ≠ 38 → regsS r = regsR r := by
    intro r h1 h2 h3 h4 h5 h6
    rw [← hregsS]
    apply straightRegs_preserves
    intro instr hi
    simp only [sparseLegSetup, List.mem_cons, List.not_mem_nil,
      or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl <;> leg_writes <;> omega
  have hRQ : regsR xQ = q := by
    rw [hRpres xQ (by decide)]
    exact hQ
  have hRF1 : regsR xSF1 = super.baseOccurrence + 1 := by
    rw [hRpres xSF1 (by decide)]
    exact hF1
  have hRF2 : regsR xSF2 = super.baseWordIndex + 1 := by
    rw [hRpres xSF2 (by decide)]
    exact hF2
  have hRL1 : regsR xLF1 = loc.baseOccurrence + 1 := by
    rw [hRpres xLF1 (by decide)]
    exact hL1
  have hRL2 : regsR xLF2 = loc.baseWordIndex + 1 := by
    rw [hRpres xLF2 (by decide)]
    exact hL2
  have hRL4 : regsR xLF4 = loc.firstOffset + 1 := by
    rw [hRpres xLF4 (by decide)]
    exact hL4
  have hSOne : regsS rOne = 1 := by
    rw [← hregsS]
    leg_eval
  have hSSlot : regsS rSlot =
      relativeSplitSelectSparseCompactSlot
        (d.bpChunkedRankTraceResultWithStore store GS (GS + 1) (GS + 2)
          CH c true (regs0 rPos)).value
        (q - relativeSplitSelectLocalBaseOccurrence super loc) LS := by
    rw [← hregsS]
    leg_eval <;>
      simp [hRVal, hRQ, hRF1, hRL1,
        relativeSplitSelectSparseCompactSlot,
        relativeSplitSelectLocalBaseOccurrence]
  have hSBPos : regsS xBPos =
      relativeSplitSelectLocalBasePosition WS super loc := by
    rw [← hregsS]
    leg_eval <;>
      simp [hRF2, hRL2, hRL4, relativeSplitSelectLocalBasePosition]
  -- relative read
  obtain ⟨regsRel, hrunRel, hdecRel, hpresRel⟩ :=
    relativeReadBlock_runsTo store hRel regsS
      (relativeSplitSelectLocalBasePosition WS super loc) hSBPos hSOne
  rw [hSSlot] at hrunRel hdecRel
  -- packet move
  have hmove := RunsTo.move (store := store)
    (s := ⟨regsRel, LB + 76, false⟩) rfl hMove
  have hall := hrunR.trans (hrunS.trans (hrunRel.trans hmove))
  have htrace :
      (TraceResult.bind
        (d.bpChunkedRankTraceResultWithStore store GS (GS + 1) (GS + 2)
          CH c true (regs0 rPos))
        (fun exceptionRank =>
          bpRelativeOffsetReadTraceResultWithStore store RS
            (relativeSplitSelectLocalBasePosition WS super loc)
            (relativeSplitSelectSparseCompactSlot exceptionRank
              (q - relativeSplitSelectLocalBaseOccurrence super loc)
              LS))).trace =
      (d.bpChunkedRankTraceResultWithStore store GS (GS + 1) (GS + 2)
        CH c true (regs0 rPos)).trace ++
        [TraceEvent.readWord RS
          (relativeSplitSelectSparseCompactSlot
            (d.bpChunkedRankTraceResultWithStore store GS (GS + 1)
              (GS + 2) CH c true (regs0 rPos)).value
            (q - relativeSplitSelectLocalBaseOccurrence super loc) LS)
          (store.readWord? RS
            (relativeSplitSelectSparseCompactSlot
              (d.bpChunkedRankTraceResultWithStore store GS (GS + 1)
                (GS + 2) CH c true (regs0 rPos)).value
              (q - relativeSplitSelectLocalBaseOccurrence super loc)
              LS))] := by
    simp [TraceResult.bind, bpRelativeOffsetReadTraceResultWithStore,
      TraceResult.map, TraceResult.pure, bpChunkReadTraceResult]
  have hvalue :
      (TraceResult.bind
        (d.bpChunkedRankTraceResultWithStore store GS (GS + 1) (GS + 2)
          CH c true (regs0 rPos))
        (fun exceptionRank =>
          bpRelativeOffsetReadTraceResultWithStore store RS
            (relativeSplitSelectLocalBasePosition WS super loc)
            (relativeSplitSelectSparseCompactSlot exceptionRank
              (q - relativeSplitSelectLocalBaseOccurrence super loc)
              LS))).value =
      ((store.readWord? RS
          (relativeSplitSelectSparseCompactSlot
            (d.bpChunkedRankTraceResultWithStore store GS (GS + 1)
              (GS + 2) CH c true (regs0 rPos)).value
            (q - relativeSplitSelectLocalBaseOccurrence super loc)
            LS)).map SuccinctSpace.bitsToNatLE).map
        (fun offset =>
          relativeSplitSelectLocalBasePosition WS super loc +
            offset) := by
    simp [TraceResult.bind, bpRelativeOffsetReadTraceResultWithStore,
      TraceResult.map, TraceResult.pure, bpChunkReadTraceResult]
  refine ⟨regsRel.write rVal (regsRel rT), ?_, ?_, ?_⟩
  · rw [htrace]
    simpa [sparseLegCats] using hall
  · rw [hvalue]
    show E1Query.decodePacket
        (regsRel.write rVal (regsRel rT) rVal) = _
    rw [RegFile.write_same]
    have hfn : bitsToNatLE = SuccinctSpace.bitsToNatLE :=
      funext SuccinctSpace.WordRAMBridge.bitsToNatLE_eq
    rw [← hfn]
    exact hdecRel
  · intro r hr hr38
    have hr9 : r ≠ 9 := by omega
    rw [RegFile.write_other _ _ (show r ≠ rVal from hr9),
      hpresRel r (by omega),
      hSpres r (by omega) (by omega) (by omega) (by omega) (by omega)
        hr38,
      hRpres r hr]

/-! ## Width certificates (REQ-E1-02 consumption for the legs) -/

theorem longLegBlock_fits {w LB GL CH RL SS WS c L WSc BPS : Nat}
    (hreg : 40 ≤ 2 ^ w) (hGL : GL + 4 < 2 ^ w) (hCH : CH < 2 ^ w)
    (hRL : RL < 2 ^ w) (hL : L < 2 ^ w) (hcpos : 0 < c)
    (hWScpos : 0 < WSc) (hWSc : WSc < 2 ^ w)
    (hBPSpos : 0 < BPS) (hBPS : BPS < 2 ^ w)
    (hpow : 2 ^ c < 2 ^ w) (hlin : 2 * c + 2 < 2 ^ w)
    (hSS : SS < 2 ^ w) (hWS : WS < 2 ^ w) (hLB : LB + 73 < 2 ^ w) :
    ∀ instr ∈ longLegBlock LB GL CH RL SS WS c L WSc BPS,
      instr.FieldsFit w := by
  intro instr hmem
  simp only [longLegBlock, longLegSetup, relativeReadBlock,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    or_assoc] at hmem
  rcases hmem with hmem | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    first
      | exact rankTrueCloseBlock_fits (by omega) hGL hCH hL hcpos
          hWScpos hWSc hBPSpos hBPS hpow hlin (by omega) instr hmem
      | (simp only [Instr.FieldsFit, rVal, rSlot, rA, rB, rOne, rT,
          xQ, xSF1, xSF2, xSF4, xBPos]
         omega)

theorem sparseLegBlock_fits {w LB GS CH RS LS WS c L WSc BPS : Nat}
    (hreg : 40 ≤ 2 ^ w) (hGS : GS + 4 < 2 ^ w) (hCH : CH < 2 ^ w)
    (hRS : RS < 2 ^ w) (hL : L < 2 ^ w) (hcpos : 0 < c)
    (hWScpos : 0 < WSc) (hWSc : WSc < 2 ^ w)
    (hBPSpos : 0 < BPS) (hBPS : BPS < 2 ^ w)
    (hpow : 2 ^ c < 2 ^ w) (hlin : 2 * c + 2 < 2 ^ w)
    (hLS : LS < 2 ^ w) (hWS : WS < 2 ^ w) (hLB : LB + 77 < 2 ^ w) :
    ∀ instr ∈ sparseLegBlock LB GS CH RS LS WS c L WSc BPS,
      instr.FieldsFit w := by
  intro instr hmem
  simp only [sparseLegBlock, sparseLegSetup, relativeReadBlock,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    or_assoc] at hmem
  rcases hmem with hmem | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    first
      | exact rankTrueCloseBlock_fits (by omega) hGS hCH hL hcpos
          hWScpos hWSc hBPSpos hBPS hpow hlin (by omega) instr hmem
      | (simp only [Instr.FieldsFit, rVal, rSlot, rA, rB, rOne, rT,
          xQ, xSF1, xSF2, xLF1, xLF2, xLF4, xBPos]
         omega)

end E1SelectLegBlocks
end WordRAM
end RMQ
