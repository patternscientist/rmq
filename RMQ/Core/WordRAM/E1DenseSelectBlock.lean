import RMQ.Core.WordRAM.E1RankAtBlock
import RMQ.Core.WordRAM.E1SelectBridge

/-!
# E1 amended machine: dense two-word select leg, head block (M3c-5b)

Stage 1 of worklog RESUME step 4.  The accepted dense leg
(`bpChunkedDenseTwoWordSelectTraceResultWithStore`,
`ChargedRankSelectLeafTrace.lean`) is: first packed word read, none
propagation, TWO atomic FALSE-target chunk rank folds on the first word
(limits `firstOffset` and `firstWord.length`), the first-count compare,
then a select fold on the first word or a second word read plus select
fold.  This module machine-simulates the leg HEAD — everything up to and
including the compare — as `denseHeadBlock B M W G c WS N2` (84
instructions):

* prologue (`denseSegA`, 4): `firstWordIndex := xBPos / WS` (`rP`),
  `firstWordStart := firstWordIndex * WS` (`rWI`),
  `localOccurrence := xQ - xBOcc` (`rSI`), packed word read at segment
  `W` into `rWrd` (shifted `decodeRead` encode);
* presence branch pair (`B+4`/`B+5`): a missing word exits to the leg's
  miss tail at absolute target `M` (the leg supplies the `none` packet);
* word-length computation (`denseSegB`, 9): the machine derives the
  first word's length `min WS (N2 - firstWordStart)` (`rBlk`) from the
  per-shape constants `WS` (word size) and `N2` (total payload bit
  length) by the truncated-subtraction min chain — the route-side
  hypothesis `hlen` identifies it with `firstWord.length`; then the
  first fold's effective limit `min firstOffset length` (`rE`) and the
  decoded word value (`rR`);
* fold 1 (`rankAtSegmentBlock (B+15) G c`, 32) — the accepted atomic
  rank fold at limit `firstOffset`, value `beforeFirst` saved to `rSup`
  by `denseSegC`;
* fold 2 (`rankAtSegmentBlock (B+50) G c`, 32) at limit
  `firstWord.length`, then `denseSegD`: `firstCount := upto - before`
  (`rVal`) and the compare `localOccurrence < firstCount` (`rA`).

`denseHeadBlock_runsTo_present` delivers exact fuel to `B + 84` with
receipts POSITIONALLY EQUAL to the leg's word-read event followed by the
two accepted fold traces, all branch inputs decoded in registers, and the
pinned/extension banks preserved; `denseHeadBlock_runsTo_miss` delivers
the absent-word exit to `M` with exactly the read receipt.  Stage 2 (the
select tails and the whole-leg theorem) composes on top.
-/

namespace RMQ
namespace WordRAM
namespace E1DenseSelectBlock

open E1Machine
open E1RankBlock
open E1RankAtBlock
open E1SelectBridge
open RMQ.SuccinctClose

/-! ## Head segments -/

/-- Prologue: word index/start, local occurrence, packed word read. -/
def denseSegA (W WS : Nat) : List Instr :=
  [ .divConst rP xBPos WS
  , .mulConst rWI rP WS
  , .sub rSI xQ xBOcc
  , .readMem rWrd W rP ]

@[simp] theorem denseSegA_length (W WS : Nat) :
    (denseSegA W WS).length = 4 := rfl

/-- Word-length min chain, first effective limit, word decode. -/
def denseSegB (WS N2 : Nat) : List Instr :=
  [ .const rA WS
  , .const rB N2
  , .sub rB rB rWI
  , .sub rT rA rB
  , .sub rBlk rA rT
  , .sub rE xBPos rWI
  , .sub rT rE rBlk
  , .sub rE rE rT
  , .sub rR rWrd rOne ]

@[simp] theorem denseSegB_length (WS N2 : Nat) :
    (denseSegB WS N2).length = 9 := rfl

/-- Between the folds: save `beforeFirst`, load the second limit, reload
the word decode. -/
def denseSegC : List Instr :=
  [ .move rSup rVal
  , .move rE rBlk
  , .sub rR rWrd rOne ]

@[simp] theorem denseSegC_length : denseSegC.length = 3 := rfl

/-- After the folds: first count and the branch compare. -/
def denseSegD : List Instr :=
  [ .sub rVal rVal rSup
  , .natLt rA rSI rVal ]

@[simp] theorem denseSegD_length : denseSegD.length = 2 := rfl

/--
The dense-leg head block at base `B`: prologue, presence branch pair
(miss exit to the absolute target `M`), word-length computation, the two
hosted atomic FALSE-target rank folds, first count, compare.  `W` is the
packed-word segment, `G + 4` the chunk-table segment, `c` the chunk
width, `WS`/`N2` the per-shape word-size and payload-bit-length
constants.
-/
def denseHeadBlock (B M W G c WS N2 : Nat) : List Instr :=
  denseSegA W WS ++
    ([Instr.brNZ rWrd (B + 6), Instr.brNZ rOne M] ++
      (denseSegB WS N2 ++
        (rankAtSegmentBlock (B + 15) G c ++
          (denseSegC ++
            (rankAtSegmentBlock (B + 50) G c ++ denseSegD)))))

@[simp] theorem denseHeadBlock_length (B M W G c WS N2 : Nat) :
    (denseHeadBlock B M W G c WS N2).length = 84 := rfl

/-! ## Frozen category logs -/

/-- Category log of the present path of the head block, as a function of
the two fold chunk counts. -/
def denseHeadPresentCats (n1 n2 : Nat) : List Category :=
  [.arithmetic, .arithmetic, .arithmetic, .memoryRead] ++
    ([.branch] ++
      ([.registerWrite, .registerWrite, .arithmetic, .arithmetic,
        .arithmetic, .arithmetic, .arithmetic, .arithmetic,
        .arithmetic] ++
        (rankAtSegmentCats n1 ++
          ([.registerWrite, .registerWrite, .arithmetic] ++
            (rankAtSegmentCats n2 ++ [.arithmetic, .comparison])))))

/-- Derived present-path step total: `33 + 25 * (n1 + n2)`. -/
theorem denseHeadPresentCats_length (n1 n2 : Nat) :
    (denseHeadPresentCats n1 n2).length = 33 + 25 * (n1 + n2) := by
  simp [denseHeadPresentCats, rankAtSegmentCats_length]
  omega

/-- Category log of the miss path of the head block. -/
def denseHeadMissCats : List Category :=
  [.arithmetic, .arithmetic, .arithmetic, .memoryRead] ++
    ([.branch] ++ [.branch])

@[simp] theorem denseHeadMissCats_length : denseHeadMissCats.length = 6 :=
  rfl

/-! ## Straightness certificates -/

theorem denseSegA_straight (W WS : Nat) :
    ∀ instr ∈ denseSegA W WS, instr.isStraight = true := by
  intro instr hi
  simp only [denseSegA, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl <;> rfl

theorem denseSegB_straight (WS N2 : Nat) :
    ∀ instr ∈ denseSegB WS N2, instr.isStraight = true := by
  intro instr hi
  simp only [denseSegB, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rfl

theorem denseSegC_straight :
    ∀ instr ∈ denseSegC, instr.isStraight = true := by
  intro instr hi
  simp only [denseSegC, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl <;> rfl

theorem denseSegD_straight :
    ∀ instr ∈ denseSegD, instr.isStraight = true := by
  intro instr hi
  simp only [denseSegD, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl <;> rfl

/-! ## Hosting bundle -/

/-- Peel the head block's hosting fact into its segment hosting facts and
the branch-pair fetch facts. -/
theorem denseHeadBlock_hosting {program : E1Machine.Program}
    {B M W G c WS N2 : Nat}
    (hhost : HostedAt program B (denseHeadBlock B M W G c WS N2)) :
    HostedAt program B (denseSegA W WS) ∧
    program[B + 4]? = some (.brNZ rWrd (B + 6)) ∧
    program[B + 5]? = some (.brNZ rOne M) ∧
    HostedAt program (B + 6) (denseSegB WS N2) ∧
    HostedAt program (B + 15) (rankAtSegmentBlock (B + 15) G c) ∧
    HostedAt program (B + 47) denseSegC ∧
    HostedAt program (B + 50) (rankAtSegmentBlock (B + 50) G c) ∧
    HostedAt program (B + 82) denseSegD := by
  have h1 := HostedAt.append_right hhost
  have h2 := HostedAt.append_right h1
  have h3 := HostedAt.append_right h2
  have h4 := HostedAt.append_right h3
  have h5 := HostedAt.append_right h4
  have h6 := HostedAt.append_right h5
  exact
    ⟨ HostedAt.append_left hhost
    , (HostedAt.append_left h1).head
    , (HostedAt.append_left h1).tail.head
    , HostedAt.append_left h2
    , HostedAt.append_left h3
    , HostedAt.append_left h4
    , HostedAt.append_left h5
    , h6 ⟩

/-! ## Shared symbolic-evaluation macros (module-local instances) -/

/-- Symbolic machine-state evaluation with this module's segments and the
shared register-bank numerals. -/
local macro "regs_eval" : tactic =>
  `(tactic| straight_eval [denseSegA, denseSegB, denseSegC, denseSegD,
      rPos, rVal, rP, rWI, rSI, rE, rSup, rBlk, rWrd,
      rR, rK, rT, rV, rSlot, rA, rB, rOne, rC, rEight, rJC,
      xIdx, xQ, xSF1, xSF2, xSF3, xSF4, xLF1, xLF2, xLF3, xLF4,
      xBPos, xBOcc])

/-- Destination-register evaluation for preservation side conditions. -/
local macro "writes_eval" : tactic =>
  `(tactic| straight_writes [rPos, rVal, rP, rWI, rSI, rE, rSup,
      rBlk, rWrd, rR, rK, rT, rV, rSlot, rA, rB, rOne, rC, rEight, rJC])

/-! ## Miss-path simulation -/

/--
Absent first word: from block entry the head runs the prologue, fails the
presence test, and exits to the leg's miss tail at `M` with exactly the
word-read receipt, the frozen `denseHeadMissCats`, the zero decode in
`rWrd`, and everything outside the prologue's write set preserved.
-/
theorem denseHeadBlock_runsTo_miss
    (store : ReadStore) {program : E1Machine.Program}
    {B M W G c WS N2 : Nat}
    (hhost : HostedAt program B (denseHeadBlock B M W G c WS N2))
    (regs0 : RegFile)
    (hword : store.readWord? W (regs0 xBPos / WS) = none)
    (hOne : regs0 rOne = 1) :
    ∃ regsH : RegFile,
      RunsTo store program ⟨regs0, B, false⟩ ⟨regsH, M, false⟩
        [TraceEvent.readWord W (regs0 xBPos / WS) none]
        denseHeadMissCats ∧
      regsH rWrd = 0 ∧
      (∀ r, r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 16 → regsH r = regs0 r) := by
  obtain ⟨hA, hbr1, hbr2, _, _, _, _, _⟩ := denseHeadBlock_hosting hhost
  have hrunA := RunsTo.straight store (denseSegA W WS)
    (denseSegA_straight W WS) B hA regs0
  obtain ⟨regs1, hregs1⟩ :
      ∃ x, straightRegs store (denseSegA W WS) regs0 = x := ⟨_, rfl⟩
  rw [hregs1] at hrunA
  have hreadsA : straightReads store (denseSegA W WS) regs0 =
      [TraceEvent.readWord W (regs0 xBPos / WS) none] := by
    regs_eval <;> simp [hword]
  rw [hreadsA] at hrunA
  have h1pres : ∀ r, r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 16 →
      regs1 r = regs0 r := by
    intro r hr1 hr2 hr3 hr4
    rw [← hregs1]
    apply straightRegs_preserves
    intro instr hi
    simp only [denseSegA, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> writes_eval <;> omega
  have h1Wrd : regs1 rWrd = 0 := by
    rw [← hregs1]
    regs_eval <;> simp [hword]
  have hbrA := RunsTo.brNZ_not_taken (store := store)
    (s := ⟨regs1, B + 4, false⟩) rfl hbr1 (by simpa using h1Wrd)
  have hbrB := RunsTo.brNZ_taken (store := store)
    (s := ⟨regs1, B + 5, false⟩) rfl hbr2 (by
      show regs1 rOne ≠ 0
      rw [h1pres rOne (by decide) (by decide) (by decide) (by decide),
        hOne]
      decide)
  have hall := hrunA.trans (hbrA.trans hbrB)
  exact ⟨regs1, by simpa [denseHeadMissCats] using hall, h1Wrd, h1pres⟩

/-! ## Present-path simulation -/

/--
Present first word: from block entry with the query state in the
extension bank (`xBPos`/`xQ`/`xBOcc`) and the pinned constants, the head
runs — with exact fuel — to the compare point `B + 84` with

* receipts POSITIONALLY EQUAL to the leg's word-read event followed by
  the two accepted atomic fold traces (limits `firstOffset` and
  `firstWord.length`),
* the frozen category log `denseHeadPresentCats` at the two fold chunk
  counts,
* the branch inputs decoded in registers: word index/start
  (`rP`/`rWI`), local occurrence (`rSI`), word length (`rBlk`), shifted
  word decode (`rWrd`), `beforeFirst` (`rSup`), `firstCount` (`rVal`),
  and the compare flag (`rA`), and
* the pinned constants (`24..26`) and the extension bank (`28 ≤ r`)
  preserved.

The route-side hypothesis `hlen` identifies the machine's min-chain word
length with `firstWord.length`; the canonical instantiation discharges it
from the dense store's word-length characterization.
-/
theorem denseHeadBlock_runsTo_present
    (store : ReadStore) {program : E1Machine.Program}
    {B M W G c WS N2 : Nat}
    (hhost : HostedAt program B (denseHeadBlock B M W G c WS N2))
    (regs0 : RegFile) (w1 : List Bool)
    (hword : store.readWord? W (regs0 xBPos / WS) = some w1)
    (hlen : w1.length = Nat.min WS (N2 - regs0 xBPos / WS * WS))
    (hOne : regs0 rOne = 1) (hC : regs0 rC = c)
    (hEight : regs0 rEight = 8) :
    ∃ regsH : RegFile,
      RunsTo store program ⟨regs0, B, false⟩ ⟨regsH, B + 84, false⟩
        (TraceEvent.readWord W (regs0 xBPos / WS) (some w1) ::
          ((bpChunkedWordRankTraceResultAtSegmentWithStore store (G + 4)
              c false w1
              (regs0 xBPos - regs0 xBPos / WS * WS)).trace ++
            (bpChunkedWordRankTraceResultAtSegmentWithStore store (G + 4)
              c false w1 w1.length).trace))
        (denseHeadPresentCats
          (bpWordChunkCount c
            (bpWordRankEffLimit w1
              (regs0 xBPos - regs0 xBPos / WS * WS)))
          (bpWordChunkCount c (bpWordRankEffLimit w1 w1.length))) ∧
      regsH rP = regs0 xBPos / WS ∧
      regsH rWI = regs0 xBPos / WS * WS ∧
      regsH rSI = regs0 xQ - regs0 xBOcc ∧
      regsH rBlk = w1.length ∧
      regsH rWrd = decodeRead (some w1) ∧
      regsH rSup =
        (bpChunkedWordRankTraceResultAtSegmentWithStore store (G + 4) c
          false w1 (regs0 xBPos - regs0 xBPos / WS * WS)).value ∧
      regsH rVal =
        (bpChunkedWordRankTraceResultAtSegmentWithStore store (G + 4) c
            false w1 w1.length).value -
          (bpChunkedWordRankTraceResultAtSegmentWithStore store (G + 4)
            c false w1
            (regs0 xBPos - regs0 xBPos / WS * WS)).value ∧
      regsH rA =
        (if regs0 xQ - regs0 xBOcc <
            (bpChunkedWordRankTraceResultAtSegmentWithStore store (G + 4)
                c false w1 w1.length).value -
              (bpChunkedWordRankTraceResultAtSegmentWithStore store
                (G + 4) c false w1
                (regs0 xBPos - regs0 xBPos / WS * WS)).value
          then 1 else 0) ∧
      (∀ r, (24 ≤ r ∧ r ≤ 26) ∨ 28 ≤ r → regsH r = regs0 r) := by
  obtain ⟨hA, hbr1, hbr2, hB, hF1, hCseg, hF2, hD⟩ :=
    denseHeadBlock_hosting hhost
  -- prologue
  have hrunA := RunsTo.straight store (denseSegA W WS)
    (denseSegA_straight W WS) B hA regs0
  obtain ⟨regs1, hregs1⟩ :
      ∃ x, straightRegs store (denseSegA W WS) regs0 = x := ⟨_, rfl⟩
  rw [hregs1] at hrunA
  have hreadsA : straightReads store (denseSegA W WS) regs0 =
      [TraceEvent.readWord W (regs0 xBPos / WS) (some w1)] := by
    regs_eval <;> simp [hword]
  rw [hreadsA] at hrunA
  have h1pres : ∀ r, r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 16 →
      regs1 r = regs0 r := by
    intro r hr1 hr2 hr3 hr4
    rw [← hregs1]
    apply straightRegs_preserves
    intro instr hi
    simp only [denseSegA, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> writes_eval <;> omega
  have h1P : regs1 rP = regs0 xBPos / WS := by
    rw [← hregs1]
    regs_eval
  have h1WI : regs1 rWI = regs0 xBPos / WS * WS := by
    rw [← hregs1]
    regs_eval
  have h1SI : regs1 rSI = regs0 xQ - regs0 xBOcc := by
    rw [← hregs1]
    regs_eval
  have h1Wrd : regs1 rWrd = decodeRead (some w1) := by
    rw [← hregs1]
    regs_eval <;> simp [hword]
  have h1BPos : regs1 xBPos = regs0 xBPos :=
    h1pres xBPos (by decide) (by decide) (by decide) (by decide)
  -- presence branch (taken)
  have hbrA := RunsTo.brNZ_taken (store := store)
    (s := ⟨regs1, B + 4, false⟩) rfl hbr1 (by
      show regs1 rWrd ≠ 0
      rw [h1Wrd]
      simp [decodeRead])
  -- word-length computation
  have hrunB := RunsTo.straight store (denseSegB WS N2)
    (denseSegB_straight WS N2) (B + 6) hB regs1
  obtain ⟨regs2, hregs2⟩ :
      ∃ x, straightRegs store (denseSegB WS N2) regs1 = x := ⟨_, rfl⟩
  rw [hregs2] at hrunB
  have hreadsB : straightReads store (denseSegB WS N2) regs1 = [] := by
    regs_eval
  rw [hreadsB] at hrunB
  have h2pres : ∀ r, r ≠ 13 → r ≠ 15 → r ≠ 17 → r ≠ 19 → r ≠ 22 →
      r ≠ 23 → regs2 r = regs1 r := by
    intro r hr1 hr2 hr3 hr4 hr5 hr6
    rw [← hregs2]
    apply straightRegs_preserves
    intro instr hi
    simp only [denseSegB, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      writes_eval <;> omega
  have h2Blk : regs2 rBlk = w1.length := by
    rw [← hregs2]
    regs_eval <;> simp [h1WI]
    rw [hlen, nat_min_eq_sub_sub]
  have hlenChain : w1.length =
      WS - (WS - (N2 - regs0 xBPos / WS * WS)) := by
    rw [hlen, nat_min_eq_sub_sub]
  have h2E : regs2 rE =
      bpWordRankEffLimit w1 (regs0 xBPos - regs0 xBPos / WS * WS) := by
    rw [← hregs2]
    regs_eval <;> simp [h1WI, h1BPos]
    simp only [bpWordRankEffLimit, nat_min_eq_sub_sub]
    rw [hlenChain]
  have h2R : regs2 rR = SuccinctSpace.bitsToNatLE w1 := by
    rw [← hregs2]
    regs_eval <;>
      simp [h1Wrd, h1pres rOne (by decide) (by decide) (by decide)
        (by decide), hOne, decodeRead,
        SuccinctSpace.WordRAMBridge.bitsToNatLE_eq]
  have h2One : regs2 rOne = 1 := by
    rw [h2pres rOne (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide),
      h1pres rOne (by decide) (by decide) (by decide) (by decide), hOne]
  have h2C : regs2 rC = c := by
    rw [h2pres rC (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide),
      h1pres rC (by decide) (by decide) (by decide) (by decide), hC]
  have h2Eight : regs2 rEight = 8 := by
    rw [h2pres rEight (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide),
      h1pres rEight (by decide) (by decide) (by decide) (by decide),
      hEight]
  -- fold 1 (limit firstOffset)
  obtain ⟨regs3, hfold1, h3Val, h3pres⟩ :=
    rankAtSegmentBlock_runsTo store hF1 regs2 w1
      (regs0 xBPos - regs0 xBPos / WS * WS) h2One h2C h2Eight h2E h2R
  -- inter-fold glue
  have hrunC := RunsTo.straight store denseSegC denseSegC_straight
    (B + 47) hCseg regs3
  obtain ⟨regs4, hregs4⟩ :
      ∃ x, straightRegs store denseSegC regs3 = x := ⟨_, rfl⟩
  rw [hregs4] at hrunC
  have hreadsC : straightReads store denseSegC regs3 = [] := by
    regs_eval
  rw [hreadsC] at hrunC
  have h4pres : ∀ r, r ≠ 13 → r ≠ 14 → r ≠ 17 →
      regs4 r = regs3 r := by
    intro r hr1 hr2 hr3
    rw [← hregs4]
    apply straightRegs_preserves
    intro instr hi
    simp only [denseSegC, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> writes_eval <;> omega
  have h3Blk : regs3 rBlk = w1.length := by
    rw [h3pres rBlk (by decide), h2Blk]
  have h3Wrd : regs3 rWrd = decodeRead (some w1) := by
    rw [h3pres rWrd (by decide),
      h2pres rWrd (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), h1Wrd]
  have h3One : regs3 rOne = 1 := by
    rw [h3pres rOne (by decide), h2One]
  have h4Sup : regs4 rSup =
      (bpChunkedWordRankTraceResultAtSegmentWithStore store (G + 4) c
        false w1 (regs0 xBPos - regs0 xBPos / WS * WS)).value := by
    rw [← hregs4]
    regs_eval <;> simp [h3Val]
  have h4E : regs4 rE = bpWordRankEffLimit w1 w1.length := by
    rw [← hregs4]
    regs_eval <;> simp [h3Blk]
    simp [bpWordRankEffLimit]
  have h4R : regs4 rR = SuccinctSpace.bitsToNatLE w1 := by
    rw [← hregs4]
    regs_eval <;>
      simp [h3Wrd, h3One, decodeRead,
        SuccinctSpace.WordRAMBridge.bitsToNatLE_eq]
  have h4One : regs4 rOne = 1 := by
    rw [h4pres rOne (by decide) (by decide) (by decide), h3One]
  have h4C : regs4 rC = c := by
    rw [h4pres rC (by decide) (by decide) (by decide),
      h3pres rC (by decide), h2C]
  have h4Eight : regs4 rEight = 8 := by
    rw [h4pres rEight (by decide) (by decide) (by decide),
      h3pres rEight (by decide), h2Eight]
  -- fold 2 (limit firstWord.length)
  obtain ⟨regs5, hfold2, h5Val, h5pres⟩ :=
    rankAtSegmentBlock_runsTo store hF2 regs4 w1 w1.length h4One h4C
      h4Eight h4E h4R
  -- first count and compare
  have hrunD := RunsTo.straight store denseSegD denseSegD_straight
    (B + 82) hD regs5
  obtain ⟨regs6, hregs6⟩ :
      ∃ x, straightRegs store denseSegD regs5 = x := ⟨_, rfl⟩
  rw [hregs6] at hrunD
  have hreadsD : straightReads store denseSegD regs5 = [] := by
    regs_eval
  rw [hreadsD] at hrunD
  have h6pres : ∀ r, r ≠ 9 → r ≠ 22 → regs6 r = regs5 r := by
    intro r hr1 hr2
    rw [← hregs6]
    apply straightRegs_preserves
    intro instr hi
    simp only [denseSegD, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> writes_eval <;> omega
  have h5Sup : regs5 rSup =
      (bpChunkedWordRankTraceResultAtSegmentWithStore store (G + 4) c
        false w1 (regs0 xBPos - regs0 xBPos / WS * WS)).value := by
    rw [h5pres rSup (by decide), h4Sup]
  have h5SI : regs5 rSI = regs0 xQ - regs0 xBOcc := by
    rw [h5pres rSI (by decide), h4pres rSI (by decide) (by decide)
      (by decide), h3pres rSI (by decide),
      h2pres rSI (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), h1SI]
  have h6Val : regs6 rVal =
      (bpChunkedWordRankTraceResultAtSegmentWithStore store (G + 4) c
          false w1 w1.length).value -
        (bpChunkedWordRankTraceResultAtSegmentWithStore store (G + 4) c
          false w1 (regs0 xBPos - regs0 xBPos / WS * WS)).value := by
    rw [← hregs6]
    regs_eval <;> simp [h5Val, h5Sup]
  have h6A : regs6 rA =
      (if regs0 xQ - regs0 xBOcc <
          (bpChunkedWordRankTraceResultAtSegmentWithStore store (G + 4)
              c false w1 w1.length).value -
            (bpChunkedWordRankTraceResultAtSegmentWithStore store (G + 4)
              c false w1
              (regs0 xBPos - regs0 xBPos / WS * WS)).value
        then 1 else 0) := by
    rw [← hregs6]
    regs_eval <;> simp [h5Val, h5Sup, h5SI]
  -- remaining branch-input registers at the end state
  have h6P : regs6 rP = regs0 xBPos / WS := by
    rw [h6pres rP (by decide) (by decide), h5pres rP (by decide),
      h4pres rP (by decide) (by decide) (by decide),
      h3pres rP (by decide),
      h2pres rP (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), h1P]
  have h6WI : regs6 rWI = regs0 xBPos / WS * WS := by
    rw [h6pres rWI (by decide) (by decide), h5pres rWI (by decide),
      h4pres rWI (by decide) (by decide) (by decide),
      h3pres rWI (by decide),
      h2pres rWI (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), h1WI]
  have h6SI : regs6 rSI = regs0 xQ - regs0 xBOcc := by
    rw [h6pres rSI (by decide) (by decide), h5SI]
  have h6Blk : regs6 rBlk = w1.length := by
    rw [h6pres rBlk (by decide) (by decide), h5pres rBlk (by decide),
      h4pres rBlk (by decide) (by decide) (by decide), h3Blk]
  have h6Wrd : regs6 rWrd = decodeRead (some w1) := by
    rw [h6pres rWrd (by decide) (by decide), h5pres rWrd (by decide),
      h4pres rWrd (by decide) (by decide) (by decide), h3Wrd]
  have h6Sup : regs6 rSup =
      (bpChunkedWordRankTraceResultAtSegmentWithStore store (G + 4) c
        false w1 (regs0 xBPos - regs0 xBPos / WS * WS)).value := by
    rw [h6pres rSup (by decide) (by decide), h5Sup]
  have h6bank : ∀ r, (24 ≤ r ∧ r ≤ 26) ∨ 28 ≤ r →
      regs6 r = regs0 r := by
    intro r hrcond
    rw [h6pres r (by omega) (by omega), h5pres r (by omega),
      h4pres r (by omega) (by omega) (by omega), h3pres r (by omega),
      h2pres r (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega),
      h1pres r (by omega) (by omega) (by omega) (by omega)]
  -- compose
  have hall := hrunA.trans (hbrA.trans (hrunB.trans (hfold1.trans
    (hrunC.trans (hfold2.trans hrunD)))))
  refine ⟨regs6, ?_, h6P, h6WI, h6SI, h6Blk, h6Wrd, h6Sup, h6Val, h6A,
    h6bank⟩
  simpa [denseHeadPresentCats, denseSegA, denseSegB, denseSegC,
    denseSegD, Instr.category] using hall

/-! ## Width certificate (REQ-E1-02 consumption for this block) -/

/--
Constructor-exhaustive width certificate for the head block: register
numerals (component bank plus `xBPos/xQ/xBOcc`), the packed-word segment
`W`, the chunk-table segment `G + 4`, the per-shape constants `WS`
(positive divisor) and `N2`, and the branch targets `B + 6`, `M`, and the
fold back-edges all fit the modeled width.
-/
theorem denseHeadBlock_fits {w B M W G c WS N2 : Nat}
    (hreg : 40 ≤ 2 ^ w) (hW : W < 2 ^ w) (hG : G + 4 < 2 ^ w)
    (hcpos : 0 < c) (hpow : 2 ^ c < 2 ^ w) (hlin : 2 * c + 2 < 2 ^ w)
    (hWSpos : 0 < WS) (hWS : WS < 2 ^ w) (hN2 : N2 < 2 ^ w)
    (hB : B + 84 < 2 ^ w) (hM : M < 2 ^ w) :
    ∀ instr ∈ denseHeadBlock B M W G c WS N2, instr.FieldsFit w := by
  intro instr hmem
  simp only [denseHeadBlock, denseSegA, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, or_assoc] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | hmem | hmem |
      hmem | hmem | hmem
  · simp only [Instr.FieldsFit, rP, xBPos]
    omega
  · simp only [Instr.FieldsFit, rWI, rP]
    omega
  · simp only [Instr.FieldsFit, rSI, xQ, xBOcc]
    omega
  · simp only [Instr.FieldsFit, rWrd, rP]
    omega
  · simp only [Instr.FieldsFit, rWrd]
    omega
  · simp only [Instr.FieldsFit, rOne]
    omega
  · -- denseSegB
    simp only [denseSegB, List.mem_cons, List.not_mem_nil,
      or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl <;>
      simp only [Instr.FieldsFit, rE, rBlk, rWrd, rR, rT,
        rA, rB, rOne, rWI, xBPos] <;>
      omega
  · -- fold 1
    exact rankAtSegmentBlock_fits (by omega) hG hcpos hpow hlin
      (by omega) instr hmem
  · -- denseSegC
    simp only [denseSegC, List.mem_cons, List.not_mem_nil,
      or_false] at hmem
    rcases hmem with rfl | rfl | rfl <;>
      simp only [Instr.FieldsFit, rVal, rE, rSup, rBlk, rWrd, rR,
        rOne] <;>
      omega
  · -- fold 2
    exact rankAtSegmentBlock_fits (by omega) hG hcpos hpow hlin
      (by omega) instr hmem
  · -- denseSegD
    simp only [denseSegD, List.mem_cons, List.not_mem_nil,
      or_false] at hmem
    rcases hmem with rfl | rfl <;>
      simp only [Instr.FieldsFit, rVal, rSup, rSI, rA] <;>
      omega

end E1DenseSelectBlock
end WordRAM
end RMQ
