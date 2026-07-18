import RMQ.Core.WordRAM.E1RankBlock

/-!
# E1 amended machine: TRUE-target rank component block (M3c-4a)

Mechanical clone of `E1RankBlock.lean` for the TRUE-target seeded rank
component
`(data).bpChunkedRankTraceResultWithStore store G (G+1) (G+2) (G+4) c TRUE
pos` — consumed twice by the select-close leg (long-flag seeds at
`layout.longFlagRankBase..+2`; sparse leg via
`sparseDirectory.bpChunkedReadTraceResultWithStore`, both at chunk segment
21).  Deltas vs the false block (worklog RESUME step 1):

* the loop body drops the final `.sub rA rT rA` flip — the true-target
  in-chunk decode ends at the `/2` division per `bpChunkRankOfEntry_true_eq`
  (`E1RankBridge.lean`); 23 loop instructions instead of 24;
* block length 59: prologue/guards/init at the same offsets (`B..B+29`),
  loop `B+30..B+52`, back edge `B+53`, epilogue `B+54..B+56`, exit jump
  `B+57` (target `B+59`), miss exit `B+58`, block exit `B+59`;
* per-pass category log `rankTrueLoopPassCats` is 24 long (one arithmetic
  tick fewer), hit-path total `34 + 24 * count`.

The prologue, guard, init, epilogue, and miss segments are shared with the
false block verbatim (`rankSeg1/2/3`, `rankSegInit`, `rankSegFin`,
`rankMissSeg` — re-used, not cloned).  The loop simulation
`rankTrueLoopFold_runsTo` is stated at a generic loop base `LB` so the
select-close legs can host the fold at any offset.
-/

namespace RMQ
namespace WordRAM
namespace E1RankTrueBlock

open E1Machine
open E1RankBlock
open RMQ.SuccinctClose

/-! ## True-target loop body -/

/-- Loop body (one chunk visit) for the TRUE target, without the back-edge
branch: the false body with the final `t -` flip dropped
(`bpChunkRankOfEntry_true_eq`). -/
def rankTrueLoopBody (G c : Nat) : List Instr :=
  [ .sub rA rE rJC
  , .sub rB rC rA
  , .sub rT rC rB
  , .divConst rA rR (2 ^ c)
  , .mulConst rB rA (2 ^ c)
  , .sub rV rR rB
  , .move rR rA
  , .mulConst rA rV (c + 1)
  , .add rA rA rT
  , .mulConst rA rA (c + 1)
  , .add rSlot rA rT
  , .readMem rA (G + 4) rSlot
  , .sub rA rA rOne
  , .divConst rA rA (c + 1)
  , .divConst rB rA (2 * c + 2)
  , .mulConst rB rB (2 * c + 2)
  , .sub rA rA rB
  , .add rA rA rT
  , .sub rA rA rC
  , .divConst rA rA 2
  , .add rVal rVal rA
  , .add rJC rJC rC
  , .sub rK rK rOne ]

@[simp] theorem rankTrueLoopBody_length (G c : Nat) :
    (rankTrueLoopBody G c).length = 23 := rfl

/--
The TRUE-target rank component block at block base `B`, seed segment base
`G`, chunk width `c`, input length `L`, word size `WS`, blocks-per-super
`BPS`.  Layout: prologue `B..B+14`, guards at `B+15/17/19` (miss target
`B+58`), init `B+20..29`, loop `B+30..52` with back edge at `B+53`,
epilogue `B+54..56`, exit jump at `B+57` (target `B+59`), miss exit
`B+58`.
-/
def rankTrueCloseBlock (B G c L WS BPS : Nat) : List Instr :=
  rankSeg1 G c L WS BPS ++
    ([Instr.brNZ rA (B + 58)] ++
      (rankSeg2 ++
        ([Instr.brNZ rA (B + 58)] ++
          (rankSeg3 ++
            ([Instr.brNZ rA (B + 58)] ++
              (rankSegInit c ++
                (rankTrueLoopBody G c ++
                  ([Instr.brNZ rK (B + 30)] ++
                    (rankSegFin ++
                      ([Instr.brNZ rA (B + 59)] ++ rankMissSeg))))))))))

@[simp] theorem rankTrueCloseBlock_length (B G c L WS BPS : Nat) :
    (rankTrueCloseBlock B G c L WS BPS).length = 59 := rfl

/-! ## Frozen category logs -/

/-- Categories charged by one TRUE-target loop pass (body plus back edge):
the false pass log with one arithmetic tick fewer. -/
def rankTrueLoopPassCats : List Category :=
  [ .arithmetic, .arithmetic, .arithmetic, .arithmetic, .arithmetic
  , .arithmetic, .registerWrite, .arithmetic, .arithmetic, .arithmetic
  , .arithmetic, .memoryRead, .arithmetic, .arithmetic, .arithmetic
  , .arithmetic, .arithmetic, .arithmetic, .arithmetic, .arithmetic
  , .arithmetic, .arithmetic, .arithmetic, .branch ]

@[simp] theorem rankTrueLoopPassCats_length :
    rankTrueLoopPassCats.length = 24 := rfl

/-- The full frozen hit-path category log at chunk count `count` (head and
tail shared with the false block). -/
def rankTrueCloseHitCats (count : Nat) : List Category :=
  rankHitHeadCats ++
    (iterLog (fun _ => rankTrueLoopPassCats) count ++ rankHitTailCats)

/-- Derived hit-path step total: `34 + 24 * count`. -/
theorem rankTrueCloseHitCats_length (count : Nat) :
    (rankTrueCloseHitCats count).length = 34 + 24 * count := by
  unfold rankTrueCloseHitCats
  rw [List.length_append, List.length_append, iterLog_const_length]
  simp
  omega

/-! ## Hosting bundle -/

/-- Peel the block's hosting fact into per-segment hosting facts and
per-branch fetch facts (all bases literal offsets from `B`). -/
theorem rankTrueCloseBlock_hosting {program : E1Machine.Program}
    {B G c L WS BPS : Nat}
    (hhost : HostedAt program B (rankTrueCloseBlock B G c L WS BPS)) :
    HostedAt program B (rankSeg1 G c L WS BPS) ∧
    program[B + 15]? = some (.brNZ rA (B + 58)) ∧
    HostedAt program (B + 16) rankSeg2 ∧
    program[B + 17]? = some (.brNZ rA (B + 58)) ∧
    HostedAt program (B + 18) rankSeg3 ∧
    program[B + 19]? = some (.brNZ rA (B + 58)) ∧
    HostedAt program (B + 20) (rankSegInit c) ∧
    HostedAt program (B + 30) (rankTrueLoopBody G c) ∧
    program[B + 53]? = some (.brNZ rK (B + 30)) ∧
    HostedAt program (B + 54) rankSegFin ∧
    program[B + 57]? = some (.brNZ rA (B + 59)) ∧
    HostedAt program (B + 58) rankMissSeg := by
  have hR1 := HostedAt.append_right hhost
  have hR2 := HostedAt.append_right hR1
  have hR3 := HostedAt.append_right hR2
  have hR4 := HostedAt.append_right hR3
  have hR5 := HostedAt.append_right hR4
  have hR6 := HostedAt.append_right hR5
  have hR7 := HostedAt.append_right hR6
  have hR8 := HostedAt.append_right hR7
  have hR9 := HostedAt.append_right hR8
  have hR10 := HostedAt.append_right hR9
  have hR11 := HostedAt.append_right hR10
  exact
    ⟨ HostedAt.append_left hhost
    , (HostedAt.append_left hR1).head
    , HostedAt.append_left hR2
    , (HostedAt.append_left hR3).head
    , HostedAt.append_left hR4
    , (HostedAt.append_left hR5).head
    , HostedAt.append_left hR6
    , HostedAt.append_left hR7
    , (HostedAt.append_left hR8).head
    , HostedAt.append_left hR9
    , (HostedAt.append_left hR10).head
    , hR11 ⟩

/-! ## Straightness certificate -/

theorem rankTrueLoopBody_straight (G c : Nat) :
    forall instr, instr ∈ rankTrueLoopBody G c ->
      instr.isStraight = true := by
  intro instr hi
  simp only [rankTrueLoopBody, List.mem_cons, List.not_mem_nil,
    or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl <;> rfl

/-! ## Shared symbolic-evaluation macros (module-local instances) -/

/-- Symbolic machine-state evaluation with this module's segments and the
shared register-bank numerals. -/
local macro "regs_eval" : tactic =>
  `(tactic| straight_eval [rankSeg1, rankSeg2, rankSeg3, rankSegInit,
      rankTrueLoopBody, rankSegFin, rankMissSeg,
      rPos, rVal, rP, rWI, rSI, rE, rSup, rBlk, rWrd,
      rR, rK, rT, rV, rSlot, rA, rB, rOne, rC, rEight, rJC])

/-- Destination-register evaluation for preservation side conditions. -/
local macro "writes_eval" : tactic =>
  `(tactic| straight_writes [rPos, rVal, rP, rWI, rSI, rE, rSup,
      rBlk, rWrd, rR, rK, rT, rV, rSlot, rA, rB, rOne, rC, rEight, rJC])

/-! ## Prologue simulation (block entry to loop entry, hit path) -/

/--
Hit-path prologue for the TRUE block: identical to the false block's
prologue (the shared segments), with the guard misses jumping to `B + 58`.
-/
theorem rankTrueCloseBlock_prologue_runsTo
    (store : ReadStore) {program : E1Machine.Program} {B G c : Nat}
    {bits : List Bool} {so bo qc : Nat}
    (d : SuccinctRank.TwoLevelPayloadLiveStoredWordRankData bits so bo qc)
    (hhost : HostedAt program B
      (rankTrueCloseBlock B G c bits.length d.wordSize d.blocksPerSuper))
    (regs0 : RegFile) {superWord deltaWord w : List Bool}
    (hsuper : store.readWord? G (d.superIndex (regs0 rPos)) = some superWord)
    (hblock :
      store.readWord? (G + 1) (d.wordIndex (regs0 rPos)) = some deltaWord)
    (hword : store.readWord? (G + 2) (d.wordIndex (regs0 rPos)) = some w) :
    ∃ regs5 : RegFile,
      RunsTo store program ⟨regs0, B, false⟩ ⟨regs5, B + 30, false⟩
        [ TraceEvent.readWord G (d.superIndex (regs0 rPos))
            (some superWord)
        , TraceEvent.readWord (G + 1) (d.wordIndex (regs0 rPos))
            (some deltaWord)
        , TraceEvent.readWord (G + 2) (d.wordIndex (regs0 rPos))
            (some w) ]
        rankHitHeadCats ∧
      regs5 rOne = 1 ∧ regs5 rC = c ∧
      regs5 rE = d.wordOffset (regs0 rPos) ∧
      regs5 rSup = SuccinctSpace.bitsToNatLE superWord ∧
      regs5 rBlk = SuccinctSpace.bitsToNatLE deltaWord ∧
      regs5 rR = SuccinctSpace.bitsToNatLE w ∧
      regs5 rJC = 0 ∧ regs5 rVal = 0 ∧
      regs5 rK = bpWordChunkCount c (d.wordOffset (regs0 rPos)) ∧
      (forall r, r <= 8 ∨ 28 <= r -> regs5 r = regs0 r) := by
  obtain ⟨hS1, hbr1, hS2, hbr2, hS3, hbr3, hInit, _hLoop, _hbrL, _hFin,
    _hbr4, _hMiss⟩ := rankTrueCloseBlock_hosting hhost
  -- route-form address bridges (machine truncated-subtraction forms)
  have hqp : regs0 rPos - (regs0 rPos - bits.length) =
      d.queryPos (regs0 rPos) := by
    show _ = Nat.min (regs0 rPos) bits.length
    exact (nat_min_eq_sub_sub _ _).symm
  have hwi : (regs0 rPos - (regs0 rPos - bits.length)) / d.wordSize =
      d.wordIndex (regs0 rPos) := by
    show _ = d.queryPos (regs0 rPos) / d.wordSize
    rw [hqp]
  have hsi2 : d.wordIndex (regs0 rPos) / d.blocksPerSuper =
      d.superIndex (regs0 rPos) := rfl
  have hoffe : regs0 rPos - (regs0 rPos - bits.length) -
      d.wordIndex (regs0 rPos) * d.wordSize = d.wordOffset (regs0 rPos) := by
    show _ = d.queryPos (regs0 rPos) - d.wordIndex (regs0 rPos) * d.wordSize
    rw [hqp]
  -- segment 1
  have hrun1 := RunsTo.straight store
    (rankSeg1 G c bits.length d.wordSize d.blocksPerSuper)
    (rankSeg1_straight G c bits.length d.wordSize d.blocksPerSuper)
    B hS1 regs0
  obtain ⟨regs1, hregs1⟩ :
      ∃ x, straightRegs store
        (rankSeg1 G c bits.length d.wordSize d.blocksPerSuper) regs0 = x :=
    ⟨_, rfl⟩
  rw [hregs1] at hrun1
  have h1Sup : regs1 rSup = SuccinctSpace.bitsToNatLE superWord + 1 := by
    rw [<- hregs1]
    regs_eval <;> simp [hwi, hsi2, hsuper,
      SuccinctSpace.WordRAMBridge.bitsToNatLE_eq]
  have h1Blk : regs1 rBlk = SuccinctSpace.bitsToNatLE deltaWord + 1 := by
    rw [<- hregs1]
    regs_eval <;> simp [hwi, hblock,
      SuccinctSpace.WordRAMBridge.bitsToNatLE_eq]
  have h1Wrd : regs1 rWrd = SuccinctSpace.bitsToNatLE w + 1 := by
    rw [<- hregs1]
    regs_eval <;> simp [hwi, hword,
      SuccinctSpace.WordRAMBridge.bitsToNatLE_eq]
  have h1B : regs1 rB = 0 := by
    rw [<- hregs1]
    regs_eval
  have h1A : regs1 rA = 0 := by
    rw [<- hregs1]
    regs_eval <;> simp [hwi, hsi2, hsuper]
  have h1E : regs1 rE = d.wordOffset (regs0 rPos) := by
    rw [<- hregs1]
    regs_eval <;> simp [hwi, hoffe]
  have h1One : regs1 rOne = 1 := by
    rw [<- hregs1]
    regs_eval
  have h1C : regs1 rC = c := by
    rw [<- hregs1]
    regs_eval
  have h1Eight : regs1 rEight = 8 := by
    rw [<- hregs1]
    regs_eval
  have h1pres : forall r, r <= 8 ∨ 28 <= r -> regs1 r = regs0 r := by
    intro r hr
    rw [<- hregs1]
    apply straightRegs_preserves
    intro i hi
    simp only [rankSeg1, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl <;>
      writes_eval <;> omega
  have hreads1 : straightReads store
      (rankSeg1 G c bits.length d.wordSize d.blocksPerSuper) regs0 =
      [ TraceEvent.readWord G (d.superIndex (regs0 rPos)) (some superWord)
      , TraceEvent.readWord (G + 1) (d.wordIndex (regs0 rPos))
          (some deltaWord)
      , TraceEvent.readWord (G + 2) (d.wordIndex (regs0 rPos))
          (some w) ] := by
    regs_eval <;> simp [hwi, hsi2, hsuper, hblock, hword]
  -- guard branch 1 (not taken)
  have hbr1run := RunsTo.brNZ_not_taken (store := store)
    (s := ⟨regs1, B + 15, false⟩) rfl hbr1 h1A
  -- segment 2
  have hrun2 := RunsTo.straight store rankSeg2 rankSeg2_straight
    (B + 16) hS2 regs1
  obtain ⟨regs2, hregs2⟩ :
      ∃ x, straightRegs store rankSeg2 regs1 = x := ⟨_, rfl⟩
  rw [hregs2] at hrun2
  have h2pass : forall r, r ≠ rA -> regs2 r = regs1 r := by
    intro r hrne
    rw [<- hregs2]
    simp only [rankSeg2, straightRegs_cons, straightRegs_nil,
      straightStepRegs]
    exact RegFile.write_other _ _ hrne
  have h2A : regs2 rA = 0 := by
    rw [<- hregs2]
    regs_eval <;> simp [h1Blk, h1B]
  have hreads2 : straightReads store rankSeg2 regs1 = [] := by
    regs_eval
  have hbr2run := RunsTo.brNZ_not_taken (store := store)
    (s := ⟨regs2, B + 17, false⟩) rfl hbr2 h2A
  -- segment 3
  have hrun3 := RunsTo.straight store rankSeg3 rankSeg3_straight
    (B + 18) hS3 regs2
  obtain ⟨regs3, hregs3⟩ :
      ∃ x, straightRegs store rankSeg3 regs2 = x := ⟨_, rfl⟩
  rw [hregs3] at hrun3
  have h3pass : forall r, r ≠ rA -> regs3 r = regs2 r := by
    intro r hrne
    rw [<- hregs3]
    simp only [rankSeg3, straightRegs_cons, straightRegs_nil,
      straightStepRegs]
    exact RegFile.write_other _ _ hrne
  have h3A : regs3 rA = 0 := by
    rw [<- hregs3]
    have hWrd2 : regs2 rWrd = SuccinctSpace.bitsToNatLE w + 1 := by
      rw [h2pass rWrd (by decide)]
      exact h1Wrd
    have hB2 : regs2 rB = 0 := by
      rw [h2pass rB (by decide)]
      exact h1B
    regs_eval <;> simp [hWrd2, hB2]
  have hreads3 : straightReads store rankSeg3 regs2 = [] := by
    regs_eval
  have hbr3run := RunsTo.brNZ_not_taken (store := store)
    (s := ⟨regs3, B + 19, false⟩) rfl hbr3 h3A
  -- named regs3 facts for the init segment
  have h3E : regs3 rE = d.wordOffset (regs0 rPos) := by
    rw [h3pass rE (by decide), h2pass rE (by decide)]
    exact h1E
  have h3One : regs3 rOne = 1 := by
    rw [h3pass rOne (by decide), h2pass rOne (by decide)]
    exact h1One
  have h3C : regs3 rC = c := by
    rw [h3pass rC (by decide), h2pass rC (by decide)]
    exact h1C
  have h3Eight : regs3 rEight = 8 := by
    rw [h3pass rEight (by decide), h2pass rEight (by decide)]
    exact h1Eight
  have h3Sup : regs3 rSup = SuccinctSpace.bitsToNatLE superWord + 1 := by
    rw [h3pass rSup (by decide), h2pass rSup (by decide)]
    exact h1Sup
  have h3Blk : regs3 rBlk = SuccinctSpace.bitsToNatLE deltaWord + 1 := by
    rw [h3pass rBlk (by decide), h2pass rBlk (by decide)]
    exact h1Blk
  have h3Wrd : regs3 rWrd = SuccinctSpace.bitsToNatLE w + 1 := by
    rw [h3pass rWrd (by decide), h2pass rWrd (by decide)]
    exact h1Wrd
  -- init segment
  have hrunInit := RunsTo.straight store (rankSegInit c)
    (rankSegInit_straight c) (B + 20) hInit regs3
  obtain ⟨regs5, hregs5⟩ :
      ∃ x, straightRegs store (rankSegInit c) regs3 = x := ⟨_, rfl⟩
  rw [hregs5] at hrunInit
  have hreadsInit : straightReads store (rankSegInit c) regs3 = [] := by
    simp [rankSegInit, straightReads_cons, straightStepEvent]
  have h5One : regs5 rOne = 1 := by
    rw [<- hregs5]
    rw [straightRegs_preserves store _ _ _ (by
      intro i hi
      simp only [rankSegInit, List.mem_cons, List.not_mem_nil,
        or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        | rfl <;> writes_eval)]
    exact h3One
  have h5C : regs5 rC = c := by
    rw [<- hregs5]
    rw [straightRegs_preserves store _ _ _ (by
      intro i hi
      simp only [rankSegInit, List.mem_cons, List.not_mem_nil,
        or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        | rfl <;> writes_eval)]
    exact h3C
  have h5E : regs5 rE = d.wordOffset (regs0 rPos) := by
    rw [<- hregs5]
    rw [straightRegs_preserves store _ _ _ (by
      intro i hi
      simp only [rankSegInit, List.mem_cons, List.not_mem_nil,
        or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        | rfl <;> writes_eval)]
    exact h3E
  have h5Sup : regs5 rSup = SuccinctSpace.bitsToNatLE superWord := by
    rw [<- hregs5]
    regs_eval <;> simp [h3Sup, h3One]
  have h5Blk : regs5 rBlk = SuccinctSpace.bitsToNatLE deltaWord := by
    rw [<- hregs5]
    regs_eval <;> simp [h3Blk, h3One]
  have h5R : regs5 rR = SuccinctSpace.bitsToNatLE w := by
    rw [<- hregs5]
    regs_eval <;> simp [h3Wrd, h3One]
  have h5JC : regs5 rJC = 0 := by
    rw [<- hregs5]
    regs_eval
  have h5Val : regs5 rVal = 0 := by
    rw [<- hregs5]
    regs_eval
  have h5K : regs5 rK =
      bpWordChunkCount c (d.wordOffset (regs0 rPos)) := by
    rw [<- hregs5, bpWordChunkCount_eq_sub]
    regs_eval <;> simp [h3E, h3One, h3Eight]
  have h5pres : forall r, r <= 8 ∨ 28 <= r -> regs5 r = regs0 r := by
    intro r hr
    rw [<- hregs5]
    rw [straightRegs_preserves store _ _ _ (by
      intro i hi
      simp only [rankSegInit, List.mem_cons, List.not_mem_nil,
        or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        | rfl <;> writes_eval <;> omega)]
    rw [h3pass r (by show r ≠ 22; omega), h2pass r (by show r ≠ 22; omega)]
    exact h1pres r hr
  -- assemble
  have hall := (((((hrun1.trans hbr1run).trans hrun2).trans
    hbr2run).trans hrun3).trans hbr3run).trans hrunInit
  rw [hreads1, hreads2, hreads3, hreadsInit] at hall
  refine ⟨regs5, ?_, h5One, h5C, h5E, h5Sup, h5Blk, h5R, h5JC, h5Val,
    h5K, h5pres⟩
  exact hall

/-! ## Loop simulation (TRUE-target chunk fold at a generic loop base) -/

/--
TRUE-target chunk-fold loop at a generic loop base `LB`: from the loop
entry with the fold registers initialized (remaining word, zeroed cursor
and accumulator, 8-capped count), the hosted loop body plus back edge run —
with exact fuel — to `LB + 24`, emitting exactly the fold's ascending
chunk-table reads as receipts, charging `count` copies of the frozen
per-pass category log, and leaving the TRUE-target literal iterated
accumulator in `rVal`.  Registers outside the loop's write set (notably
the decoded samples in `rSup`/`rBlk`) are preserved.
-/
theorem rankTrueLoopFold_runsTo
    (store : ReadStore) {program : E1Machine.Program} {LB G c : Nat}
    (hLoop : HostedAt program LB (rankTrueLoopBody G c))
    (hbrL : program[LB + 23]? = some (.brNZ rK LB))
    (w : List Bool) (e : Nat) (regsL : RegFile)
    (hOne : regsL rOne = 1) (hC : regsL rC = c) (hE : regsL rE = e)
    (hR : regsL rR = SuccinctSpace.bitsToNatLE w)
    (hJC : regsL rJC = 0) (hVal : regsL rVal = 0)
    (hK : regsL rK = bpWordChunkCount c e) :
    ∃ regs6 : RegFile,
      RunsTo store program ⟨regsL, LB, false⟩ ⟨regs6, LB + 24, false⟩
        ((List.range (bpWordChunkCount c e)).map
          (fun j => bpWordRankChunkEventAt store (G + 4) c w e j))
        (iterLog (fun _ => rankTrueLoopPassCats) (bpWordChunkCount c e)) ∧
      regs6 rVal =
        bpWordRankAccAt store (G + 4) c true w e (bpWordChunkCount c e) ∧
      (forall r, r <= 8 ∨ r = 14 ∨ r = 15 ∨ 28 <= r ->
        regs6 r = regsL r) := by
  have hcpos : 1 <= bpWordChunkCount c e := by
    rw [bpWordChunkCount_eq_sub]
    generalize (e - 1) / c = q
    omega
  -- loop invariant, indexed by the remaining iteration count
  let count := bpWordChunkCount c e
  let P : Nat -> State -> Prop := fun k s =>
    k <= count ∧ s.halted = false ∧
    s.pc = (if k = 0 then LB + 24 else LB) ∧
    s.regs rOne = 1 ∧ s.regs rC = c ∧ s.regs rE = e ∧
    s.regs rR = SuccinctSpace.bitsToNatLE w / 2 ^ ((count - k) * c) ∧
    s.regs rJC = (count - k) * c ∧
    s.regs rVal =
      bpWordRankAccAt store (G + 4) c true w e (count - k) ∧
    s.regs rK = k ∧
    (forall r, r <= 8 ∨ r = 14 ∨ r = 15 ∨ 28 <= r ->
      s.regs r = regsL r)
  have hstep : forall k s, P (k + 1) s ->
      ∃ s', RunsTo store program s s'
          [bpWordRankChunkEventAt store (G + 4) c w e (count - (k + 1))]
          rankTrueLoopPassCats ∧ P k s' := by
    intro k s hP
    obtain ⟨regs, pc, halted⟩ := s
    obtain ⟨hkle, hhalt, hpc, hone, hc, he, hr, hjc, hval, hk, hpres⟩ := hP
    simp only at hhalt hpc hone hc he hr hjc hval hk hpres
    subst hhalt
    have hpcEq : (if k + 1 = 0 then LB + 24 else LB) = LB :=
      if_neg (Nat.succ_ne_zero k)
    rw [hpcEq] at hpc
    subst pc
    have hik : count - k = (count - (k + 1)) + 1 := by omega
    -- body straight run
    have hbody := RunsTo.straight store (rankTrueLoopBody G c)
      (rankTrueLoopBody_straight G c) LB hLoop regs
    obtain ⟨regsB, hregsB⟩ :
        ∃ x, straightRegs store (rankTrueLoopBody G c) regs = x := ⟨_, rfl⟩
    rw [hregsB] at hbody
    -- receipts of one pass
    have hreadsB : straightReads store (rankTrueLoopBody G c) regs =
        [bpWordRankChunkEventAt store (G + 4) c w e (count - (k + 1))] := by
      regs_eval <;>
        simp [hc, he, hjc, hr, bpWordRankChunkEventAt,
          bpWordRankChunkSlotAt, bpFringeChunkSlot,
          bpWordChunkSliceLen_eq_sub, bpFringeWindowChunkValue_eq_div_mod,
          nat_mod_eq_sub_div_mul]
    rw [hreadsB] at hbody
    -- invariant registers after the body
    have hBOne : regsB rOne = 1 := by
      rw [<- hregsB]
      rw [straightRegs_preserves store _ _ _ (by
        intro i hi
        simp only [rankTrueLoopBody, List.mem_cons, List.not_mem_nil,
          or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          | rfl | rfl | rfl | rfl <;> writes_eval)]
      exact hone
    have hBC : regsB rC = c := by
      rw [<- hregsB]
      rw [straightRegs_preserves store _ _ _ (by
        intro i hi
        simp only [rankTrueLoopBody, List.mem_cons, List.not_mem_nil,
          or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          | rfl | rfl | rfl | rfl <;> writes_eval)]
      exact hc
    have hBE : regsB rE = e := by
      rw [<- hregsB]
      rw [straightRegs_preserves store _ _ _ (by
        intro i hi
        simp only [rankTrueLoopBody, List.mem_cons, List.not_mem_nil,
          or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          | rfl | rfl | rfl | rfl <;> writes_eval)]
      exact he
    have hBR : regsB rR =
        SuccinctSpace.bitsToNatLE w / 2 ^ ((count - k) * c) := by
      rw [<- hregsB, hik]
      regs_eval <;> simp [hr]
      exact div_pow_chunk_succ _ _ _
    have hBJC : regsB rJC = (count - k) * c := by
      rw [<- hregsB, hik]
      regs_eval <;> simp [hjc, hc]
      rw [Nat.succ_mul]
    have hBVal : regsB rVal =
        bpWordRankAccAt store (G + 4) c true w e (count - k) := by
      rw [<- hregsB, hik]
      regs_eval <;>
        simp [hval, hone, hc, he, hjc, hr, bpWordRankAccAt,
          bpWordRankStepDecoded, bpChunkRankOfEntry_true_eq,
          decodeRead_pred_eq_map_getD, bpWordRankChunkSlotAt,
          bpFringeChunkSlot, bpWordChunkSliceLen_eq_sub,
          bpFringeWindowChunkValue_eq_div_mod, nat_mod_eq_sub_div_mul]
    have hBK : regsB rK = k := by
      rw [<- hregsB]
      regs_eval <;> simp [hk, hone]
    have hBpres : forall r, r <= 8 ∨ r = 14 ∨ r = 15 ∨ 28 <= r ->
        regsB r = regsL r := by
      intro r hrcond
      rw [<- hregsB]
      rw [straightRegs_preserves store _ _ _ (by
        intro i hi
        simp only [rankTrueLoopBody, List.mem_cons, List.not_mem_nil,
          or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          | rfl | rfl | rfl | rfl <;> writes_eval <;> omega)]
      exact hpres r hrcond
    -- back edge
    by_cases hk0 : k = 0
    · subst hk0
      have hbr := RunsTo.brNZ_not_taken (store := store)
        (s := ⟨regsB, LB + 23, false⟩) rfl hbrL (by simpa using hBK)
      refine ⟨⟨regsB, LB + 24, false⟩, hbody.trans hbr, ?_⟩
      refine ⟨Nat.zero_le _, rfl, by simp, hBOne, hBC, hBE, ?_, ?_, ?_,
        ?_, hBpres⟩
      · simpa using hBR
      · simpa using hBJC
      · simpa using hBVal
      · simpa using hBK
    · have hbr := RunsTo.brNZ_taken (store := store)
        (s := ⟨regsB, LB + 23, false⟩) rfl hbrL (by
          rw [show (⟨regsB, LB + 23, false⟩ : State).regs = regsB from rfl,
            hBK]
          exact hk0)
      refine ⟨⟨regsB, LB, false⟩, hbody.trans hbr, ?_⟩
      refine ⟨by omega, rfl, by simp [hk0], hBOne, hBC, hBE, hBR, hBJC,
        hBVal, hBK, hBpres⟩
  -- start state satisfies the invariant at the full count
  have hstart : P count ⟨regsL, LB, false⟩ := by
    refine ⟨Nat.le_refl _, rfl, ?_, hOne, hC, hE, ?_, ?_, ?_, hK,
      fun r _ => rfl⟩
    · have : count ≠ 0 := by omega
      simp [this]
    · simp [Nat.sub_self, hR]
    · simp [Nat.sub_self, hJC]
    · simp [Nat.sub_self, hVal, bpWordRankAccAt]
  obtain ⟨sEnd, hloopRun, hPEnd⟩ :=
    RunsTo.iterate P
      (fun k => [bpWordRankChunkEventAt store (G + 4) c w e
        (count - (k + 1))])
      (fun _ => rankTrueLoopPassCats) hstep count ⟨regsL, LB, false⟩ hstart
  obtain ⟨regsE, pcE, haltE⟩ := sEnd
  obtain ⟨_, hEhalt, hEpc, _, _, _, _, _, hEVal, _, hEpres⟩ := hPEnd
  simp only at hEhalt hEpc hEVal hEpres
  subst hEhalt
  simp at hEpc
  subst hEpc
  -- receipts in ascending chunk order
  have hreadsIter :
      iterLog (fun k => [bpWordRankChunkEventAt store (G + 4) c w e
        (count - (k + 1))]) count =
      (List.range count).map
        (fun j => bpWordRankChunkEventAt store (G + 4) c w e j) := by
    have h1 : iterLog (fun k => [bpWordRankChunkEventAt store (G + 4) c
        w e (count - (k + 1))]) count =
        iterLog (fun k => [bpWordRankChunkEventAt store (G + 4) c w e
          (0 + (count - (k + 1)))]) count := by
      apply iterLog_congr
      intro kk _
      rw [Nat.zero_add]
    rw [h1, iterLog_singleton_desc]
    apply List.map_congr_left
    intro dd _
    rw [Nat.zero_add]
  rw [hreadsIter] at hloopRun
  exact ⟨regsE, hloopRun, by simpa using hEVal, hEpres⟩

/-! ## Whole-block hit-path simulation against the accepted component -/

/--
Hit-path simulation of the accepted TRUE-target chunked rank component:
from block entry with the position in `rPos`, when the store presents the
three seed reads and the offset lies inside the stored word, the hosted
block runs — with exact fuel — to the block exit at `B + 59` with

* receipts POSITIONALLY EQUAL to the component's trace,
* the component's value in `rVal`,
* the frozen category log `rankTrueCloseHitCats count` (derived length
  `34 + 24 * count`, `count <= 8`), and
* every register outside the component bank (`r <= 8` or `28 <= r`)
  preserved.
-/
theorem rankTrueCloseBlock_runsTo_hit
    (store : ReadStore) {program : E1Machine.Program} {B G c : Nat}
    {bits : List Bool} {so bo qc : Nat}
    (d : SuccinctRank.TwoLevelPayloadLiveStoredWordRankData bits so bo qc)
    (hhost : HostedAt program B
      (rankTrueCloseBlock B G c bits.length d.wordSize d.blocksPerSuper))
    (regs0 : RegFile) {superWord deltaWord w : List Bool}
    (hsuper : store.readWord? G (d.superIndex (regs0 rPos)) = some superWord)
    (hblock :
      store.readWord? (G + 1) (d.wordIndex (regs0 rPos)) = some deltaWord)
    (hword : store.readWord? (G + 2) (d.wordIndex (regs0 rPos)) = some w)
    (hoff : d.wordOffset (regs0 rPos) <= w.length) :
    ∃ regsF : RegFile,
      RunsTo store program ⟨regs0, B, false⟩ ⟨regsF, B + 59, false⟩
        (d.bpChunkedRankTraceResultWithStore store G (G + 1) (G + 2)
          (G + 4) c true (regs0 rPos)).trace
        (rankTrueCloseHitCats
          (bpWordChunkCount c (d.wordOffset (regs0 rPos)))) ∧
      regsF rVal =
        (d.bpChunkedRankTraceResultWithStore store G (G + 1) (G + 2)
          (G + 4) c true (regs0 rPos)).value ∧
      (forall r, r <= 8 ∨ 28 <= r -> regsF r = regs0 r) := by
  obtain ⟨_, _, _, _, _, _, _, hLoop, hbrL, hFin, hbr4, _⟩ :=
    rankTrueCloseBlock_hosting hhost
  obtain ⟨regs5, hpro, h5One, h5C, h5E, h5Sup, h5Blk, h5R, h5JC, h5Val,
    h5K, h5pres⟩ :=
    rankTrueCloseBlock_prologue_runsTo store d hhost regs0 hsuper hblock
      hword
  have hbrL' : program[B + 30 + 23]? = some (.brNZ rK (B + 30)) := by
    rw [show B + 30 + 23 = B + 53 from by omega]
    exact hbrL
  obtain ⟨regs6, hloop, h6Val, h6pres⟩ :=
    rankTrueLoopFold_runsTo store hLoop hbrL' w
      (d.wordOffset (regs0 rPos)) regs5 h5One h5C h5E h5R h5JC h5Val h5K
  rw [show B + 30 + 24 = B + 54 from by omega] at hloop
  -- epilogue
  have h6Sup : regs6 rSup = SuccinctSpace.bitsToNatLE superWord := by
    rw [h6pres rSup (by decide)]
    exact h5Sup
  have h6Blk : regs6 rBlk = SuccinctSpace.bitsToNatLE deltaWord := by
    rw [h6pres rBlk (by decide)]
    exact h5Blk
  have hrunFin := RunsTo.straight store rankSegFin rankSegFin_straight
    (B + 54) hFin regs6
  obtain ⟨regs7, hregs7⟩ :
      ∃ x, straightRegs store rankSegFin regs6 = x := ⟨_, rfl⟩
  rw [hregs7] at hrunFin
  have hreadsFin : straightReads store rankSegFin regs6 = [] := by
    regs_eval
  rw [hreadsFin] at hrunFin
  have h7Val : regs7 rVal =
      bpWordRankAccAt store (G + 4) c true w
          (d.wordOffset (regs0 rPos))
          (bpWordChunkCount c (d.wordOffset (regs0 rPos))) +
        SuccinctSpace.bitsToNatLE superWord +
        SuccinctSpace.bitsToNatLE deltaWord := by
    rw [<- hregs7]
    regs_eval <;> simp [h6Val, h6Sup, h6Blk]
  have h7A : regs7 rA = 1 := by
    rw [<- hregs7]
    regs_eval
  have h7pres : forall r, r <= 8 ∨ 28 <= r -> regs7 r = regs0 r := by
    intro r hr
    rw [<- hregs7]
    rw [straightRegs_preserves store _ _ _ (by
      intro i hi
      simp only [rankSegFin, List.mem_cons, List.not_mem_nil,
        or_false] at hi
      rcases hi with rfl | rfl | rfl <;> writes_eval <;> omega)]
    rw [h6pres r (by omega)]
    exact h5pres r hr
  have hbr4run := RunsTo.brNZ_taken (store := store)
    (s := ⟨regs7, B + 57, false⟩) rfl hbr4 (by
      show regs7 rA ≠ 0
      rw [h7A]
      omega)
  have hall := ((hpro.trans hloop).trans hrunFin).trans hbr4run
  -- component trace and value, unfolded on the hit path
  have hfoldVal :
      (bpChunkedWordRankTraceFromWithStore store (G + 4) c true w
          (d.wordOffset (regs0 rPos)) 0
          (bpWordChunkCount c (d.wordOffset (regs0 rPos))) 0).value =
        bpWordRankAccAt store (G + 4) c true w
          (d.wordOffset (regs0 rPos))
          (bpWordChunkCount c (d.wordOffset (regs0 rPos))) := by
    have h := bpChunkedWordRankTraceFromWithStore_value_accAt store
      (G + 4) c true w (d.wordOffset (regs0 rPos))
      (bpWordChunkCount c (d.wordOffset (regs0 rPos))) 0
    simpa [bpWordRankAccAt] using h
  have hcompTrace :
      (d.bpChunkedRankTraceResultWithStore store G (G + 1) (G + 2)
          (G + 4) c true (regs0 rPos)).trace =
        [ TraceEvent.readWord G (d.superIndex (regs0 rPos))
            (some superWord)
        , TraceEvent.readWord (G + 1) (d.wordIndex (regs0 rPos))
            (some deltaWord)
        , TraceEvent.readWord (G + 2) (d.wordIndex (regs0 rPos))
            (some w) ] ++
        (List.range (bpWordChunkCount c (d.wordOffset (regs0 rPos)))).map
          (fun j => bpWordRankChunkEventAt store (G + 4) c w
            (d.wordOffset (regs0 rPos)) j) := by
    simp [SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.bpChunkedRankTraceResultWithStore,
      TraceResult.bind, TraceResult.map, TraceResult.pure,
      bpChunkReadTraceResult, bpWordReadTraceResult,
      bpChunkedWordRankTraceResultAtSegmentWithStore,
      bpWordRankEffLimit_eq_of_le hoff,
      bpChunkedWordRankTraceFromWithStore_trace_map,
      hsuper, hblock, hword]
  have hcompVal :
      (d.bpChunkedRankTraceResultWithStore store G (G + 1) (G + 2)
          (G + 4) c true (regs0 rPos)).value =
        SuccinctSpace.bitsToNatLE superWord +
          SuccinctSpace.bitsToNatLE deltaWord +
          bpWordRankAccAt store (G + 4) c true w
            (d.wordOffset (regs0 rPos))
            (bpWordChunkCount c (d.wordOffset (regs0 rPos))) := by
    simp [SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.bpChunkedRankTraceResultWithStore,
      TraceResult.bind, TraceResult.map, TraceResult.pure,
      bpChunkReadTraceResult, bpWordReadTraceResult,
      bpChunkedWordRankTraceResultAtSegmentWithStore,
      bpWordRankEffLimit_eq_of_le hoff, hfoldVal,
      hsuper, hblock, hword]
  refine ⟨regs7, ?_, ?_, h7pres⟩
  · rw [hcompTrace]
    show RunsTo store program ⟨regs0, B, false⟩ ⟨regs7, B + 59, false⟩ _
      (rankTrueCloseHitCats
        (bpWordChunkCount c (d.wordOffset (regs0 rPos))))
    have hcats : rankTrueCloseHitCats
        (bpWordChunkCount c (d.wordOffset (regs0 rPos))) =
        (rankHitHeadCats ++
          iterLog (fun _ => rankTrueLoopPassCats)
            (bpWordChunkCount c (d.wordOffset (regs0 rPos))) ++
          List.map Instr.category rankSegFin) ++ [Category.branch] := by
      simp [rankTrueCloseHitCats, rankHitTailCats, rankSegFin,
        List.append_assoc, Instr.category]
    rw [hcats]
    have hreads :
        ([ TraceEvent.readWord G (d.superIndex (regs0 rPos))
             (some superWord)
         , TraceEvent.readWord (G + 1) (d.wordIndex (regs0 rPos))
             (some deltaWord)
         , TraceEvent.readWord (G + 2) (d.wordIndex (regs0 rPos))
             (some w) ] ++
          (List.range (bpWordChunkCount c
            (d.wordOffset (regs0 rPos)))).map
            (fun j => bpWordRankChunkEventAt store (G + 4) c w
              (d.wordOffset (regs0 rPos)) j)) =
        (([ TraceEvent.readWord G (d.superIndex (regs0 rPos))
              (some superWord)
          , TraceEvent.readWord (G + 1) (d.wordIndex (regs0 rPos))
              (some deltaWord)
          , TraceEvent.readWord (G + 2) (d.wordIndex (regs0 rPos))
              (some w) ] ++
          (List.range (bpWordChunkCount c
            (d.wordOffset (regs0 rPos)))).map
            (fun j => bpWordRankChunkEventAt store (G + 4) c w
              (d.wordOffset (regs0 rPos)) j)) ++ []) ++ [] := by
      simp
    rw [hreads]
    exact hall
  · rw [hcompVal, h7Val]
    omega

/-! ## Width certificate (REQ-E1-02 consumption for this block) -/

/--
Constructor-exhaustive width certificate for the TRUE-target rank block:
every encoded field — register identifiers (bank `8..27`), seed segments
`G..G+4`, the immediates `0`/`1`/`8`/`L`, the multiplier/divisor
constants `WS`/`BPS`/`2^c`/`c+1`/`2*c+2`/`2`, and the branch targets
`B+30`/`B+58`/`B+59` — fits the modeled width `w`, with the variable
divisors `c`/`WS`/`BPS` positive (`2^c`, `c+1`, `2*c+2`, `2` are
positive outright; the route discharges `0 < c` by
`bpFringeChunkBits_pos`).
-/
theorem rankTrueCloseBlock_fits {w B G c L WS BPS : Nat}
    (hreg : 28 ≤ 2 ^ w) (hG : G + 4 < 2 ^ w) (hL : L < 2 ^ w)
    (hcpos : 0 < c)
    (hWSpos : 0 < WS) (hWS : WS < 2 ^ w)
    (hBPSpos : 0 < BPS) (hBPS : BPS < 2 ^ w)
    (hpow : 2 ^ c < 2 ^ w) (hlin : 2 * c + 2 < 2 ^ w)
    (hB : B + 59 < 2 ^ w) :
    ∀ instr ∈ rankTrueCloseBlock B G c L WS BPS, instr.FieldsFit w := by
  have hppos : 0 < 2 ^ c := Nat.pow_pos (by omega)
  intro instr hmem
  simp only [rankTrueCloseBlock, rankSeg1, rankSeg2, rankSeg3, rankSegInit,
    rankTrueLoopBody, rankSegFin, rankMissSeg, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Instr.FieldsFit, rPos, rVal, rP, rWI, rSI, rE, rSup, rBlk,
      rWrd, rR, rK, rT, rV, rSlot, rA, rB, rOne, rC, rEight, rJC] <;>
    omega

end E1RankTrueBlock
end WordRAM
end RMQ
