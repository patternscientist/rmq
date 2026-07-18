import RMQ.Core.WordRAM.E1StraightLine
import RMQ.Core.WordRAM.E1RankBridge

/-!
# E1 amended machine: rank-close component block (M3c-1b)

The concrete machine program fragment simulating the accepted rank-close
component
`(builtRelativeSplitBPCloseRankData shape).bpChunkedRankTraceResultWithStore
store G (G+1) (G+2) (G+4) c false pos` (the body of
`concreteBPNativeRankCloseWordTraceResultAtSegment`, frozen matrix
REQ-E1-03/04), and its exact-fuel `RunsTo` simulation theorem.

Shape of the block (60 instructions at block base `B`, all straight-line
except four `brNZ` and no `halt` — the block is a component, not a whole
program):

* prologue (`rankSeg1`): pin the constants `1`, `c`, `8`; clamp
  `p = min pos L` by truncated subtraction; derive the word index
  `p / WS`, super index `p / WS / BPS`, and offset `e = p - (p/WS)*WS` by
  constant division/multiplication; perform the three accepted seed reads
  (super sample at `G`, block sample at `G+1`, packed word at `G+2`); zero
  test the three decoded registers (option-shift: `0` decodes `none`);
* the three `brNZ` guards jump to the miss exit (`rankMissSeg`), which
  pins the component's `pure 0` value — mirroring the component's `match`
  on the three optional reads by machine comparisons;
* init (`rankSegInit`): shift the three decodes down by one (option
  shift), zero the chunk cursor and accumulator, and derive the 8-capped
  chunk count `min ((e-1)/c + 1) 8` by the subtraction chain;
* loop (`rankLoopBody` + back-edge `brNZ`): per visited chunk, derive the
  slice length `t = min c (e - j*c)` and window chunk value
  `v = (W / 2^(j*c)) % 2^c` by constant div/mod forms, read the chunk
  table at slot `(v*(c+1)+t)*(c+1)+t` (segment `G+4`), decode the entry's
  routing rank by the `bpChunkRankOfEntry` constant chain, and accumulate;
* epilogue (`rankSegFin`): add the super and block samples into the
  accumulator (the component's `super + delta + localRank`) and jump over
  the miss exit.

The hit-path simulation theorem `rankCloseBlock_runsTo_hit` delivers, for
any hosting program and any store presenting the three seed reads: exact
receipts positionally equal to the component's trace, the component's value
in `rVal`, and the frozen category log `rankCloseHitCats count` whose
length is derived (`30 + 25 * count + 4`, `count <= 8`).
-/

namespace RMQ
namespace WordRAM
namespace E1RankBlock

open E1Machine
open RMQ.SuccinctClose

/-! ## Frozen register bank (component registers, from `firstComponentReg`) -/

/-- Input: query position `pos` (the rank-close argument). -/
abbrev rPos : Nat := 8
/-- Output: the component value. -/
abbrev rVal : Nat := 9
/-- Clamped position `min pos L`. -/
abbrev rP : Nat := 10
/-- Word index `p / WS`. -/
abbrev rWI : Nat := 11
/-- Super index `p / WS / BPS`. -/
abbrev rSI : Nat := 12
/-- Word offset (= effective fold limit) `e`. -/
abbrev rE : Nat := 13
/-- Decoded super sample read (then the super sample itself). -/
abbrev rSup : Nat := 14
/-- Decoded block sample read (then the block delta itself). -/
abbrev rBlk : Nat := 15
/-- Decoded packed-word read. -/
abbrev rWrd : Nat := 16
/-- Remaining-word register `W / 2^(j*c)`. -/
abbrev rR : Nat := 17
/-- Loop counter (remaining chunk visits). -/
abbrev rK : Nat := 18
/-- Slice length `t`. -/
abbrev rT : Nat := 19
/-- Window chunk value `v`. -/
abbrev rV : Nat := 20
/-- Chunk-table slot. -/
abbrev rSlot : Nat := 21
/-- Scratch. -/
abbrev rA : Nat := 22
/-- Scratch. -/
abbrev rB : Nat := 23
/-- Pinned constant `1`. -/
abbrev rOne : Nat := 24
/-- Pinned constant `c`. -/
abbrev rC : Nat := 25
/-- Pinned constant `8`. -/
abbrev rEight : Nat := 26
/-- Chunk cursor `j * c`. -/
abbrev rJC : Nat := 27

/-! ## Block segments -/

/-- Prologue: constants, clamp, address arithmetic, the three seed reads,
and the first zero test. -/
def rankSeg1 (G c L WS BPS : Nat) : List Instr :=
  [ .const rOne 1
  , .const rC c
  , .const rEight 8
  , .const rA L
  , .sub rB rPos rA
  , .sub rP rPos rB
  , .divConst rWI rP WS
  , .divConst rSI rWI BPS
  , .mulConst rA rWI WS
  , .sub rE rP rA
  , .readMem rSup G rSI
  , .readMem rBlk (G + 1) rWI
  , .readMem rWrd (G + 2) rWI
  , .const rB 0
  , .natEq rA rSup rB ]

@[simp] theorem rankSeg1_length (G c L WS BPS : Nat) :
    (rankSeg1 G c L WS BPS).length = 15 := rfl

/-- Second zero test (block sample). -/
def rankSeg2 : List Instr := [ .natEq rA rBlk rB ]

@[simp] theorem rankSeg2_length : rankSeg2.length = 1 := rfl

/-- Third zero test (packed word). -/
def rankSeg3 : List Instr := [ .natEq rA rWrd rB ]

@[simp] theorem rankSeg3_length : rankSeg3.length = 1 := rfl

/-- Fold initialization: option-shift the three decodes, zero the cursor
and accumulator, derive the 8-capped chunk count. -/
def rankSegInit (c : Nat) : List Instr :=
  [ .sub rR rWrd rOne
  , .sub rSup rSup rOne
  , .sub rBlk rBlk rOne
  , .const rJC 0
  , .const rVal 0
  , .sub rA rE rOne
  , .divConst rA rA c
  , .add rK rA rOne
  , .sub rB rK rEight
  , .sub rK rK rB ]

@[simp] theorem rankSegInit_length (c : Nat) :
    (rankSegInit c).length = 10 := rfl

/-- Loop body (one chunk visit), without the back-edge branch. -/
def rankLoopBody (G c : Nat) : List Instr :=
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
  , .sub rA rT rA
  , .add rVal rVal rA
  , .add rJC rJC rC
  , .sub rK rK rOne ]

@[simp] theorem rankLoopBody_length (G c : Nat) :
    (rankLoopBody G c).length = 24 := rfl

/-- Epilogue: fold in the super and block samples, jump over the miss
exit. -/
def rankSegFin : List Instr :=
  [ .add rVal rVal rSup
  , .add rVal rVal rBlk
  , .const rA 1 ]

@[simp] theorem rankSegFin_length : rankSegFin.length = 3 := rfl

/-- Miss exit: the component's `pure 0`. -/
def rankMissSeg : List Instr := [ .const rVal 0 ]

@[simp] theorem rankMissSeg_length : rankMissSeg.length = 1 := rfl

/--
The rank-close component block at block base `B`, seed segment base `G`,
chunk width `c`, input length `L`, word size `WS`, blocks-per-super `BPS`.
Layout: prologue `B..B+14`, guards at `B+15/17/19` (miss target `B+59`),
init `B+20..29`, loop `B+30..53` with back edge at `B+54`, epilogue
`B+55..57`, exit jump at `B+58` (target `B+60`), miss exit `B+59`.
-/
def rankCloseBlock (B G c L WS BPS : Nat) : List Instr :=
  rankSeg1 G c L WS BPS ++
    ([Instr.brNZ rA (B + 59)] ++
      (rankSeg2 ++
        ([Instr.brNZ rA (B + 59)] ++
          (rankSeg3 ++
            ([Instr.brNZ rA (B + 59)] ++
              (rankSegInit c ++
                (rankLoopBody G c ++
                  ([Instr.brNZ rK (B + 30)] ++
                    (rankSegFin ++
                      ([Instr.brNZ rA (B + 60)] ++ rankMissSeg))))))))))

@[simp] theorem rankCloseBlock_length (B G c L WS BPS : Nat) :
    (rankCloseBlock B G c L WS BPS).length = 60 := rfl

/-! ## Frozen category logs -/

/-- Categories charged by the hit path up to the loop entry. -/
def rankHitHeadCats : List Category :=
  [ .registerWrite, .registerWrite, .registerWrite, .registerWrite
  , .arithmetic, .arithmetic, .arithmetic, .arithmetic, .arithmetic
  , .arithmetic
  , .memoryRead, .memoryRead, .memoryRead
  , .registerWrite, .comparison
  , .branch, .comparison, .branch, .comparison, .branch
  , .arithmetic, .arithmetic, .arithmetic, .registerWrite, .registerWrite
  , .arithmetic, .arithmetic, .arithmetic, .arithmetic, .arithmetic ]

@[simp] theorem rankHitHeadCats_length : rankHitHeadCats.length = 30 := rfl

/-- Categories charged by one loop pass (body plus back edge). -/
def rankLoopPassCats : List Category :=
  [ .arithmetic, .arithmetic, .arithmetic, .arithmetic, .arithmetic
  , .arithmetic, .registerWrite, .arithmetic, .arithmetic, .arithmetic
  , .arithmetic, .memoryRead, .arithmetic, .arithmetic, .arithmetic
  , .arithmetic, .arithmetic, .arithmetic, .arithmetic, .arithmetic
  , .arithmetic, .arithmetic, .arithmetic, .arithmetic, .branch ]

@[simp] theorem rankLoopPassCats_length : rankLoopPassCats.length = 25 := rfl

/-- Categories charged by the hit-path epilogue. -/
def rankHitTailCats : List Category :=
  [ .arithmetic, .arithmetic, .registerWrite, .branch ]

@[simp] theorem rankHitTailCats_length : rankHitTailCats.length = 4 := rfl

/-- The full frozen hit-path category log at chunk count `count`. -/
def rankCloseHitCats (count : Nat) : List Category :=
  rankHitHeadCats ++
    (iterLog (fun _ => rankLoopPassCats) count ++ rankHitTailCats)

/-- Derived hit-path step total: `34 + 25 * count`. -/
theorem rankCloseHitCats_length (count : Nat) :
    (rankCloseHitCats count).length = 34 + 25 * count := by
  unfold rankCloseHitCats
  rw [List.length_append, List.length_append, iterLog_const_length]
  simp
  omega

/-! ## Hosting bundle -/

/-- Peel the block's hosting fact into per-segment hosting facts and
per-branch fetch facts (all bases literal offsets from `B`). -/
theorem rankCloseBlock_hosting {program : E1Machine.Program}
    {B G c L WS BPS : Nat}
    (hhost : HostedAt program B (rankCloseBlock B G c L WS BPS)) :
    HostedAt program B (rankSeg1 G c L WS BPS) ∧
    program[B + 15]? = some (.brNZ rA (B + 59)) ∧
    HostedAt program (B + 16) rankSeg2 ∧
    program[B + 17]? = some (.brNZ rA (B + 59)) ∧
    HostedAt program (B + 18) rankSeg3 ∧
    program[B + 19]? = some (.brNZ rA (B + 59)) ∧
    HostedAt program (B + 20) (rankSegInit c) ∧
    HostedAt program (B + 30) (rankLoopBody G c) ∧
    program[B + 54]? = some (.brNZ rK (B + 30)) ∧
    HostedAt program (B + 55) rankSegFin ∧
    program[B + 58]? = some (.brNZ rA (B + 60)) ∧
    HostedAt program (B + 59) rankMissSeg := by
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

/-! ## Straightness certificates -/

theorem rankSeg1_straight (G c L WS BPS : Nat) :
    forall instr, instr ∈ rankSeg1 G c L WS BPS ->
      instr.isStraight = true := by
  intro instr hi
  simp only [rankSeg1, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem rankSeg2_straight :
    forall instr, instr ∈ rankSeg2 -> instr.isStraight = true := by
  intro instr hi
  simp only [rankSeg2, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl
  rfl

theorem rankSeg3_straight :
    forall instr, instr ∈ rankSeg3 -> instr.isStraight = true := by
  intro instr hi
  simp only [rankSeg3, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl
  rfl

theorem rankSegInit_straight (c : Nat) :
    forall instr, instr ∈ rankSegInit c -> instr.isStraight = true := by
  intro instr hi
  simp only [rankSegInit, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl <;> rfl

theorem rankLoopBody_straight (G c : Nat) :
    forall instr, instr ∈ rankLoopBody G c -> instr.isStraight = true := by
  intro instr hi
  simp only [rankLoopBody, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl <;> rfl

theorem rankSegFin_straight :
    forall instr, instr ∈ rankSegFin -> instr.isStraight = true := by
  intro instr hi
  simp only [rankSegFin, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl <;> rfl

/-! ## Prologue simulation (block entry to loop entry, hit path) -/

/-- Symbolic machine-state evaluation: the shared `straight_eval` core
(`E1StraightLine.lean`) instantiated with this block's segments and
register-bank numerals.  Bridge equations are applied by a follow-up
`simp` at each call site. -/
local macro "regs_eval" : tactic =>
  `(tactic| straight_eval [rankSeg1, rankSeg2, rankSeg3, rankSegInit,
      rankLoopBody, rankSegFin, rankMissSeg,
      rPos, rVal, rP, rWI, rSI, rE, rSup, rBlk, rWrd,
      rR, rK, rT, rV, rSlot, rA, rB, rOne, rC, rEight, rJC])

/-- Destination-register evaluation for preservation side conditions. -/
local macro "writes_eval" : tactic =>
  `(tactic| straight_writes [rPos, rVal, rP, rWI, rSI, rE, rSup,
      rBlk, rWrd, rR, rK, rT, rV, rSlot, rA, rB, rOne, rC, rEight, rJC])

/--
Hit-path prologue: from block entry with the query position in `rPos`, any
program hosting the block runs — with exact fuel — to the loop entry at
`B + 30`, emitting exactly the component's three seed reads (super sample,
block sample, packed word) as receipts, charging exactly
`rankHitHeadCats`, and reaching a register file holding the decoded
samples, the decoded word, the word offset, the zeroed cursor/accumulator,
and the 8-capped chunk count.
-/
theorem rankCloseBlock_prologue_runsTo
    (store : ReadStore) {program : E1Machine.Program} {B G c : Nat}
    {bits : List Bool} {so bo qc : Nat}
    (d : SuccinctRank.TwoLevelPayloadLiveStoredWordRankData bits so bo qc)
    (hhost : HostedAt program B
      (rankCloseBlock B G c bits.length d.wordSize d.blocksPerSuper))
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
    _hbr4, _hMiss⟩ := rankCloseBlock_hosting hhost
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
  have hbr1run := RunsTo.brNZ_not_taken (store := store) (s := ⟨regs1, B + 15, false⟩)
    rfl hbr1 h1A
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
  have hbr2run := RunsTo.brNZ_not_taken (store := store) (s := ⟨regs2, B + 17, false⟩)
    rfl hbr2 h2A
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
  have hbr3run := RunsTo.brNZ_not_taken (store := store) (s := ⟨regs3, B + 19, false⟩)
    rfl hbr3 h3A
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

/-! ## Loop simulation (chunk fold, `RunsTo.iterate`) -/

/--
Chunk-fold loop: from the loop entry with the fold registers initialized
(remaining word, zeroed cursor and accumulator, 8-capped count), the hosted
loop body plus back edge run — with exact fuel — to the epilogue at
`B + 55`, emitting exactly the fold's ascending chunk-table reads as
receipts, charging `count` copies of the frozen per-pass category log, and
leaving the fold's literal iterated accumulator in `rVal`.  Registers
outside the loop's write set (notably the decoded samples in `rSup`/`rBlk`)
are preserved.
-/
theorem rankCloseBlock_loop_runsTo
    (store : ReadStore) {program : E1Machine.Program} {B G c : Nat}
    (hLoop : HostedAt program (B + 30) (rankLoopBody G c))
    (hbrL : program[B + 54]? = some (.brNZ rK (B + 30)))
    (w : List Bool) (e : Nat) (regsL : RegFile)
    (hOne : regsL rOne = 1) (hC : regsL rC = c) (hE : regsL rE = e)
    (hR : regsL rR = SuccinctSpace.bitsToNatLE w)
    (hJC : regsL rJC = 0) (hVal : regsL rVal = 0)
    (hK : regsL rK = bpWordChunkCount c e) :
    ∃ regs6 : RegFile,
      RunsTo store program ⟨regsL, B + 30, false⟩ ⟨regs6, B + 55, false⟩
        ((List.range (bpWordChunkCount c e)).map
          (fun j => bpWordRankChunkEventAt store (G + 4) c w e j))
        (iterLog (fun _ => rankLoopPassCats) (bpWordChunkCount c e)) ∧
      regs6 rVal =
        bpWordRankAccAt store (G + 4) c false w e (bpWordChunkCount c e) ∧
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
    s.pc = (if k = 0 then B + 55 else B + 30) ∧
    s.regs rOne = 1 ∧ s.regs rC = c ∧ s.regs rE = e ∧
    s.regs rR = SuccinctSpace.bitsToNatLE w / 2 ^ ((count - k) * c) ∧
    s.regs rJC = (count - k) * c ∧
    s.regs rVal =
      bpWordRankAccAt store (G + 4) c false w e (count - k) ∧
    s.regs rK = k ∧
    (forall r, r <= 8 ∨ r = 14 ∨ r = 15 ∨ 28 <= r ->
      s.regs r = regsL r)
  have hstep : forall k s, P (k + 1) s ->
      ∃ s', RunsTo store program s s'
          [bpWordRankChunkEventAt store (G + 4) c w e (count - (k + 1))]
          rankLoopPassCats ∧ P k s' := by
    intro k s hP
    obtain ⟨regs, pc, halted⟩ := s
    obtain ⟨hkle, hhalt, hpc, hone, hc, he, hr, hjc, hval, hk, hpres⟩ := hP
    simp only at hhalt hpc hone hc he hr hjc hval hk hpres
    subst hhalt
    have hpcEq : (if k + 1 = 0 then B + 55 else B + 30) = B + 30 :=
      if_neg (Nat.succ_ne_zero k)
    rw [hpcEq] at hpc
    subst hpc
    have hik : count - k = (count - (k + 1)) + 1 := by omega
    -- body straight run
    have hbody := RunsTo.straight store (rankLoopBody G c)
      (rankLoopBody_straight G c) (B + 30) hLoop regs
    obtain ⟨regsB, hregsB⟩ :
        ∃ x, straightRegs store (rankLoopBody G c) regs = x := ⟨_, rfl⟩
    rw [hregsB] at hbody
    -- receipts of one pass
    have hreadsB : straightReads store (rankLoopBody G c) regs =
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
        simp only [rankLoopBody, List.mem_cons, List.not_mem_nil,
          or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          | rfl | rfl | rfl | rfl | rfl <;> writes_eval)]
      exact hone
    have hBC : regsB rC = c := by
      rw [<- hregsB]
      rw [straightRegs_preserves store _ _ _ (by
        intro i hi
        simp only [rankLoopBody, List.mem_cons, List.not_mem_nil,
          or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          | rfl | rfl | rfl | rfl | rfl <;> writes_eval)]
      exact hc
    have hBE : regsB rE = e := by
      rw [<- hregsB]
      rw [straightRegs_preserves store _ _ _ (by
        intro i hi
        simp only [rankLoopBody, List.mem_cons, List.not_mem_nil,
          or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          | rfl | rfl | rfl | rfl | rfl <;> writes_eval)]
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
        bpWordRankAccAt store (G + 4) c false w e (count - k) := by
      rw [<- hregsB, hik]
      regs_eval <;>
        simp [hval, hone, hc, he, hjc, hr, bpWordRankAccAt,
          bpWordRankStepDecoded, bpChunkRankOfEntry_false_eq,
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
        simp only [rankLoopBody, List.mem_cons, List.not_mem_nil,
          or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          | rfl | rfl | rfl | rfl | rfl <;> writes_eval <;> omega)]
      exact hpres r hrcond
    -- back edge
    by_cases hk0 : k = 0
    · subst hk0
      have hbr := RunsTo.brNZ_not_taken (store := store)
        (s := ⟨regsB, B + 54, false⟩) rfl hbrL (by simpa using hBK)
      refine ⟨⟨regsB, B + 55, false⟩, hbody.trans hbr, ?_⟩
      refine ⟨Nat.zero_le _, rfl, by simp, hBOne, hBC, hBE, ?_, ?_, ?_,
        ?_, hBpres⟩
      · simpa using hBR
      · simpa using hBJC
      · simpa using hBVal
      · simpa using hBK
    · have hbr := RunsTo.brNZ_taken (store := store)
        (s := ⟨regsB, B + 54, false⟩) rfl hbrL (by
          rw [show (⟨regsB, B + 54, false⟩ : State).regs = regsB from rfl,
            hBK]
          exact hk0)
      refine ⟨⟨regsB, B + 30, false⟩, hbody.trans hbr, ?_⟩
      refine ⟨by omega, rfl, by simp [hk0], hBOne, hBC, hBE, hBR, hBJC,
        hBVal, hBK, hBpres⟩
  -- start state satisfies the invariant at the full count
  have hstart : P count ⟨regsL, B + 30, false⟩ := by
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
      (fun _ => rankLoopPassCats) hstep count ⟨regsL, B + 30, false⟩ hstart
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
Hit-path simulation of the accepted chunked rank-close component: from
block entry with the position in `rPos`, when the store presents the three
seed reads (super sample, block sample, packed word) and the offset lies
inside the stored word, the hosted block runs — with exact fuel — to the
block exit at `B + 60` with

* receipts POSITIONALLY EQUAL to the component's trace,
* the component's value in `rVal`,
* the frozen category log `rankCloseHitCats count` (derived length
  `34 + 25 * count`, `count <= 8`), and
* every register outside the component bank (`r <= 8` or `28 <= r`)
  preserved.
-/
theorem rankCloseBlock_runsTo_hit
    (store : ReadStore) {program : E1Machine.Program} {B G c : Nat}
    {bits : List Bool} {so bo qc : Nat}
    (d : SuccinctRank.TwoLevelPayloadLiveStoredWordRankData bits so bo qc)
    (hhost : HostedAt program B
      (rankCloseBlock B G c bits.length d.wordSize d.blocksPerSuper))
    (regs0 : RegFile) {superWord deltaWord w : List Bool}
    (hsuper : store.readWord? G (d.superIndex (regs0 rPos)) = some superWord)
    (hblock :
      store.readWord? (G + 1) (d.wordIndex (regs0 rPos)) = some deltaWord)
    (hword : store.readWord? (G + 2) (d.wordIndex (regs0 rPos)) = some w)
    (hoff : d.wordOffset (regs0 rPos) <= w.length) :
    ∃ regsF : RegFile,
      RunsTo store program ⟨regs0, B, false⟩ ⟨regsF, B + 60, false⟩
        (d.bpChunkedRankTraceResultWithStore store G (G + 1) (G + 2)
          (G + 4) c false (regs0 rPos)).trace
        (rankCloseHitCats
          (bpWordChunkCount c (d.wordOffset (regs0 rPos)))) ∧
      regsF rVal =
        (d.bpChunkedRankTraceResultWithStore store G (G + 1) (G + 2)
          (G + 4) c false (regs0 rPos)).value ∧
      (forall r, r <= 8 ∨ 28 <= r -> regsF r = regs0 r) := by
  obtain ⟨_, _, _, _, _, _, _, hLoop, hbrL, hFin, hbr4, _⟩ :=
    rankCloseBlock_hosting hhost
  obtain ⟨regs5, hpro, h5One, h5C, h5E, h5Sup, h5Blk, h5R, h5JC, h5Val,
    h5K, h5pres⟩ :=
    rankCloseBlock_prologue_runsTo store d hhost regs0 hsuper hblock hword
  obtain ⟨regs6, hloop, h6Val, h6pres⟩ :=
    rankCloseBlock_loop_runsTo store hLoop hbrL w
      (d.wordOffset (regs0 rPos)) regs5 h5One h5C h5E h5R h5JC h5Val h5K
  -- epilogue
  have h6Sup : regs6 rSup = SuccinctSpace.bitsToNatLE superWord := by
    rw [h6pres rSup (by decide)]
    exact h5Sup
  have h6Blk : regs6 rBlk = SuccinctSpace.bitsToNatLE deltaWord := by
    rw [h6pres rBlk (by decide)]
    exact h5Blk
  have hrunFin := RunsTo.straight store rankSegFin rankSegFin_straight
    (B + 55) hFin regs6
  obtain ⟨regs7, hregs7⟩ :
      ∃ x, straightRegs store rankSegFin regs6 = x := ⟨_, rfl⟩
  rw [hregs7] at hrunFin
  have hreadsFin : straightReads store rankSegFin regs6 = [] := by
    regs_eval
  rw [hreadsFin] at hrunFin
  have h7Val : regs7 rVal =
      bpWordRankAccAt store (G + 4) c false w
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
    (s := ⟨regs7, B + 58, false⟩) rfl hbr4 (by
      show regs7 rA ≠ 0
      rw [h7A]
      omega)
  have hall := ((hpro.trans hloop).trans hrunFin).trans hbr4run
  -- component trace and value, unfolded on the hit path
  have hfoldVal :
      (bpChunkedWordRankTraceFromWithStore store (G + 4) c false w
          (d.wordOffset (regs0 rPos)) 0
          (bpWordChunkCount c (d.wordOffset (regs0 rPos))) 0).value =
        bpWordRankAccAt store (G + 4) c false w
          (d.wordOffset (regs0 rPos))
          (bpWordChunkCount c (d.wordOffset (regs0 rPos))) := by
    have h := bpChunkedWordRankTraceFromWithStore_value_accAt store
      (G + 4) c false w (d.wordOffset (regs0 rPos))
      (bpWordChunkCount c (d.wordOffset (regs0 rPos))) 0
    simpa [bpWordRankAccAt] using h
  have hcompTrace :
      (d.bpChunkedRankTraceResultWithStore store G (G + 1) (G + 2)
          (G + 4) c false (regs0 rPos)).trace =
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
          (G + 4) c false (regs0 rPos)).value =
        SuccinctSpace.bitsToNatLE superWord +
          SuccinctSpace.bitsToNatLE deltaWord +
          bpWordRankAccAt store (G + 4) c false w
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
    show RunsTo store program ⟨regs0, B, false⟩ ⟨regs7, B + 60, false⟩ _
      (rankCloseHitCats
        (bpWordChunkCount c (d.wordOffset (regs0 rPos))))
    have hcats : rankCloseHitCats
        (bpWordChunkCount c (d.wordOffset (regs0 rPos))) =
        (rankHitHeadCats ++
          iterLog (fun _ => rankLoopPassCats)
            (bpWordChunkCount c (d.wordOffset (regs0 rPos))) ++
          List.map Instr.category rankSegFin) ++ [Category.branch] := by
      simp [rankCloseHitCats, rankHitTailCats, rankSegFin,
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
Constructor-exhaustive width certificate for the rank-close block: every
encoded field — register identifiers (bank `8..27`), seed segments
`G..G+4`, the immediates `0`/`1`/`8`/`L`, the multiplier/divisor
constants `WS`/`BPS`/`2^c`/`c+1`/`2*c+2`/`2`, and the branch targets
`B+30`/`B+59`/`B+60` — fits the modeled width `w`, with the variable
divisors `c`/`WS`/`BPS` positive (`2^c`, `c+1`, `2*c+2`, `2` are
positive outright; the route discharges `0 < c` by
`bpFringeChunkBits_pos`).
-/
theorem rankCloseBlock_fits {w B G c L WS BPS : Nat}
    (hreg : 28 ≤ 2 ^ w) (hG : G + 4 < 2 ^ w) (hL : L < 2 ^ w)
    (hcpos : 0 < c)
    (hWSpos : 0 < WS) (hWS : WS < 2 ^ w)
    (hBPSpos : 0 < BPS) (hBPS : BPS < 2 ^ w)
    (hpow : 2 ^ c < 2 ^ w) (hlin : 2 * c + 2 < 2 ^ w)
    (hB : B + 60 < 2 ^ w) :
    ∀ instr ∈ rankCloseBlock B G c L WS BPS, instr.FieldsFit w := by
  have hppos : 0 < 2 ^ c := Nat.pow_pos (by omega)
  intro instr hmem
  simp only [rankCloseBlock, rankSeg1, rankSeg2, rankSeg3, rankSegInit,
    rankLoopBody, rankSegFin, rankMissSeg, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, or_assoc] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Instr.FieldsFit, rPos, rVal, rP, rWI, rSI, rE, rSup, rBlk,
      rWrd, rR, rK, rT, rV, rSlot, rA, rB, rOne, rC, rEight, rJC] <;>
    omega

end E1RankBlock
end WordRAM
end RMQ
