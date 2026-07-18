import RMQ.Core.WordRAM.E1RankAtBlock
import RMQ.Core.WordRAM.E1SelectBridge
import RMQ.Core.WordRAM.E1SelectBlock

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
open RMQ.GenericSelect

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

/-! ## Stage 2 (M3c-5c): dense-leg tails and the whole two-word leg

The instruction-exact stage-2 layout from the worklog: the head block
(miss target `L + 192`), the compare branch, the second-word tail
(probe read, min-chain length from the per-shape constants, remaining
occurrence, hosted select fold, packet shift), the first-word tail
(length from `rBlk`, occurrence `beforeFirst + localOccurrence`, hosted
select fold, packet shift), and the shared miss tail. -/

/-! ### Tail segments -/

/-- Second-word probe: advance the word index, read the packed word. -/
def denseTail2Pre (W : Nat) : List Instr :=
  [ .add rP rP rOne
  , .readMem rWrd W rP ]

@[simp] theorem denseTail2Pre_length (W : Nat) :
    (denseTail2Pre W).length = 2 := rfl

/-- Second-word tail setup: second word start, word length by the
min chain from the per-shape constants, remaining occurrence
`localOccurrence - firstCount`, word decode, cursor zero, 8-capped
chunk count. -/
def denseTail2Setup (WS N2 c : Nat) : List Instr :=
  [ .mulConst rWI rP WS
  , .const rA WS
  , .const rB N2
  , .sub rB rB rWI
  , .sub rT rA rB
  , .sub rE rA rT
  , .sub rSI rSI rVal
  , .sub rR rWrd rOne
  , .const rJC 0
  , .sub rA rE rOne
  , .divConst rA rA c
  , .add rK rA rOne
  , .sub rB rK rEight
  , .sub rK rK rB ]

@[simp] theorem denseTail2Setup_length (WS N2 c : Nat) :
    (denseTail2Setup WS N2 c).length = 14 := rfl

/-- First-word tail setup: word length from `rBlk`, occurrence
`beforeFirst + localOccurrence`, word decode, cursor zero, 8-capped
chunk count. -/
def denseTail1Setup (c : Nat) : List Instr :=
  [ .move rE rBlk
  , .add rSI rSup rSI
  , .sub rR rWrd rOne
  , .const rJC 0
  , .sub rA rE rOne
  , .divConst rA rA c
  , .add rK rA rOne
  , .sub rB rK rEight
  , .sub rK rK rB ]

@[simp] theorem denseTail1Setup_length (c : Nat) :
    (denseTail1Setup c).length = 9 := rfl

/--
The whole dense two-word select leg at base `L` (193 instructions).
Layout: head `L..L+83` (miss exit `L+192`), compare branch at `L+84`
(taken -> first tail at `L+143`), second tail `L+85..L+142` (probe
read with presence pair, setup `L+89..L+102`, hosted select fold
`L+103..L+138`, packet shift `L+139..L+142`), first tail
`L+143..L+191` (setup `L+143..L+151`, hosted select fold
`L+152..L+187`, packet shift `L+188..L+191`), miss tail `L+192`,
block end `L+193`.
-/
def denseSelectLegBlock (L W G S c WS N2 : Nat) : List Instr :=
  denseHeadBlock L (L + 192) W G c WS N2 ++
    ([Instr.brNZ rA (L + 143)] ++
      (denseTail2Pre W ++
        ([Instr.brNZ rWrd (L + 89), Instr.brNZ rOne (L + 192)] ++
          (denseTail2Setup WS N2 c ++
            (E1SelectBlock.selectFoldBlock (L + 103) (G + 4) S c ++
              ([Instr.brNZ rVal (L + 141), Instr.brNZ rOne (L + 142),
                Instr.add rVal rWI rVal, Instr.brNZ rOne (L + 193)] ++
                (denseTail1Setup c ++
                  (E1SelectBlock.selectFoldBlock (L + 152) (G + 4) S c ++
                    ([Instr.brNZ rVal (L + 190),
                      Instr.brNZ rOne (L + 191),
                      Instr.add rVal rWI rVal,
                      Instr.brNZ rOne (L + 193)] ++
                      [Instr.const rVal 0])))))))))

@[simp] theorem denseSelectLegBlock_length (L W G S c WS N2 : Nat) :
    (denseSelectLegBlock L W G S c WS N2).length = 193 := rfl

/-! ### Frozen category logs (stage 2) -/

/-- Categories charged by the first-word tail setup. -/
def denseTail1SetupCats : List Category :=
  [ .registerWrite, .arithmetic, .arithmetic, .registerWrite,
    .arithmetic, .arithmetic, .arithmetic, .arithmetic, .arithmetic ]

@[simp] theorem denseTail1SetupCats_eq (c : Nat) :
    (denseTail1Setup c).map Instr.category = denseTail1SetupCats := rfl

/-- Categories charged by the second-word tail setup. -/
def denseTail2SetupCats : List Category :=
  [ .arithmetic, .registerWrite, .registerWrite, .arithmetic,
    .arithmetic, .arithmetic, .arithmetic, .arithmetic, .registerWrite,
    .arithmetic, .arithmetic, .arithmetic, .arithmetic, .arithmetic ]

@[simp] theorem denseTail2SetupCats_eq (WS N2 c : Nat) :
    (denseTail2Setup WS N2 c).map Instr.category =
      denseTail2SetupCats := rfl

@[simp] theorem denseTail2PreCats_eq (W : Nat) :
    (denseTail2Pre W).map Instr.category =
      [Category.arithmetic, Category.memoryRead] := rfl

/-- Categories of the three executed packet-shift steps (packet test;
the word-start add or the skip branch; the exit branch), decided by the
fold's packet. -/
def packetShiftCats : Option Nat -> List Category
  | none => [.branch, .branch, .branch]
  | some _ => [.branch, .arithmetic, .branch]

/--
Derived category log of the whole dense leg: a FUNCTION of the store
and the query state mirroring the accepted evaluator's four control
branches (missing first word / first-word select / missing second word
/ second-word select) — never asserted; the simulation theorem charges
exactly this log.
-/
def denseLegCats (store : ReadStore) (W G S c WS : Nat)
    (bPos bOcc q : Nat) : List Category :=
  match store.readWord? W (bPos / WS) with
  | none => denseHeadMissCats ++ [Category.registerWrite]
  | some w1 =>
      denseHeadPresentCats
          (bpWordChunkCount c
            (bpWordRankEffLimit w1 (bPos - bPos / WS * WS)))
          (bpWordChunkCount c (bpWordRankEffLimit w1 w1.length)) ++
        ([Category.branch] ++
          (if q - bOcc <
              (bpChunkedWordRankTraceResultAtSegmentWithStore store
                  (G + 4) c false w1 w1.length).value -
                (bpChunkedWordRankTraceResultAtSegmentWithStore store
                  (G + 4) c false w1 (bPos - bPos / WS * WS)).value then
            denseTail1SetupCats ++
              (E1SelectBlock.selectFoldCats store (G + 4) c w1 0
                  (bpWordChunkCount c w1.length)
                  ((bpChunkedWordRankTraceResultAtSegmentWithStore store
                      (G + 4) c false w1
                      (bPos - bPos / WS * WS)).value +
                    (q - bOcc)) ++
                packetShiftCats
                  (bpChunkedWordSelectTraceResultAtSegmentsWithStore
                    store (G + 4) S c false w1
                    ((bpChunkedWordRankTraceResultAtSegmentWithStore
                        store (G + 4) c false w1
                        (bPos - bPos / WS * WS)).value +
                      (q - bOcc))).value)
          else
            [Category.arithmetic, Category.memoryRead] ++
              (match store.readWord? W (bPos / WS + 1) with
               | none =>
                   [Category.branch, Category.branch,
                     Category.registerWrite]
               | some w2 =>
                   [Category.branch] ++
                     (denseTail2SetupCats ++
                       (E1SelectBlock.selectFoldCats store (G + 4) c w2
                           0 (bpWordChunkCount c w2.length)
                           ((q - bOcc) -
                             ((bpChunkedWordRankTraceResultAtSegmentWithStore
                                 store (G + 4) c false w1
                                 w1.length).value -
                               (bpChunkedWordRankTraceResultAtSegmentWithStore
                                 store (G + 4) c false w1
                                 (bPos - bPos / WS * WS)).value)) ++
                         packetShiftCats
                           (bpChunkedWordSelectTraceResultAtSegmentsWithStore
                             store (G + 4) S c false w2
                             ((q - bOcc) -
                               ((bpChunkedWordRankTraceResultAtSegmentWithStore
                                   store (G + 4) c false w1
                                   w1.length).value -
                                 (bpChunkedWordRankTraceResultAtSegmentWithStore
                                   store (G + 4) c false w1
                                   (bPos -
                                     bPos / WS * WS)).value))).value)))))

/-! ### Straightness certificates (stage 2) -/

theorem denseTail2Pre_straight (W : Nat) :
    ∀ instr ∈ denseTail2Pre W, instr.isStraight = true := by
  intro instr hi
  simp only [denseTail2Pre, List.mem_cons, List.not_mem_nil,
    or_false] at hi
  rcases hi with rfl | rfl <;> rfl

theorem denseTail2Setup_straight (WS N2 c : Nat) :
    ∀ instr ∈ denseTail2Setup WS N2 c, instr.isStraight = true := by
  intro instr hi
  simp only [denseTail2Setup, List.mem_cons, List.not_mem_nil,
    or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl <;> rfl

theorem denseTail1Setup_straight (c : Nat) :
    ∀ instr ∈ denseTail1Setup c, instr.isStraight = true := by
  intro instr hi
  simp only [denseTail1Setup, List.mem_cons, List.not_mem_nil,
    or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl <;> rfl

/-! ### Hosting bundle (stage 2) -/

set_option maxRecDepth 8192 in
/-- Peel the leg's hosting fact into the component hosting facts and
per-branch fetch facts (all bases literal offsets from `L`). -/
theorem denseSelectLegBlock_hosting {program : E1Machine.Program}
    {L W G S c WS N2 : Nat}
    (hhost : HostedAt program L (denseSelectLegBlock L W G S c WS N2)) :
    HostedAt program L (denseHeadBlock L (L + 192) W G c WS N2) ∧
    program[L + 84]? = some (.brNZ rA (L + 143)) ∧
    HostedAt program (L + 85) (denseTail2Pre W) ∧
    program[L + 87]? = some (.brNZ rWrd (L + 89)) ∧
    program[L + 88]? = some (.brNZ rOne (L + 192)) ∧
    HostedAt program (L + 89) (denseTail2Setup WS N2 c) ∧
    HostedAt program (L + 103)
      (E1SelectBlock.selectFoldBlock (L + 103) (G + 4) S c) ∧
    program[L + 139]? = some (.brNZ rVal (L + 141)) ∧
    program[L + 140]? = some (.brNZ rOne (L + 142)) ∧
    program[L + 141]? = some (.add rVal rWI rVal) ∧
    program[L + 142]? = some (.brNZ rOne (L + 193)) ∧
    HostedAt program (L + 143) (denseTail1Setup c) ∧
    HostedAt program (L + 152)
      (E1SelectBlock.selectFoldBlock (L + 152) (G + 4) S c) ∧
    program[L + 188]? = some (.brNZ rVal (L + 190)) ∧
    program[L + 189]? = some (.brNZ rOne (L + 191)) ∧
    program[L + 190]? = some (.add rVal rWI rVal) ∧
    program[L + 191]? = some (.brNZ rOne (L + 193)) ∧
    program[L + 192]? = some (.const rVal 0) := by
  have h1 := HostedAt.append_right hhost
  have h2 := HostedAt.append_right h1
  have h3 := HostedAt.append_right h2
  have h4 := HostedAt.append_right h3
  have h5 := HostedAt.append_right h4
  have h6 := HostedAt.append_right h5
  have h7 := HostedAt.append_right h6
  have h8 := HostedAt.append_right h7
  have h9 := HostedAt.append_right h8
  have h10 := HostedAt.append_right h9
  exact
    ⟨ HostedAt.append_left hhost
    , (HostedAt.append_left h1).head
    , HostedAt.append_left h2
    , (HostedAt.append_left h3).head
    , (HostedAt.append_left h3).tail.head
    , HostedAt.append_left h4
    , HostedAt.append_left h5
    , (HostedAt.append_left h6).head
    , (HostedAt.append_left h6).tail.head
    , (HostedAt.append_left h6).tail.tail.head
    , (HostedAt.append_left h6).tail.tail.tail.head
    , HostedAt.append_left h7
    , HostedAt.append_left h8
    , (HostedAt.append_left h9).head
    , (HostedAt.append_left h9).tail.head
    , (HostedAt.append_left h9).tail.tail.head
    , (HostedAt.append_left h9).tail.tail.tail.head
    , h10.head ⟩

/-! ### Stage-2 symbolic-evaluation macros -/

/-- Symbolic machine-state evaluation for the stage-2 tail segments. -/
local macro "tail_eval" : tactic =>
  `(tactic| straight_eval [denseTail2Pre, denseTail2Setup,
      denseTail1Setup,
      rPos, rVal, rP, rWI, rSI, rE, rSup, rBlk, rWrd,
      rR, rK, rT, rV, rSlot, rA, rB, rOne, rC, rEight, rJC,
      xIdx, xQ, xSF1, xSF2, xSF3, xSF4, xLF1, xLF2, xLF3, xLF4,
      xBPos, xBOcc])

/-- Destination-register evaluation for the stage-2 preservation side
conditions. -/
local macro "tail_writes" : tactic =>
  `(tactic| straight_writes [rPos, rVal, rP, rWI, rSI, rE, rSup,
      rBlk, rWrd, rR, rK, rT, rV, rSlot, rA, rB, rOne, rC, rEight, rJC])

/-! ### Shared fold-plus-packet-shift simulation -/

/--
Hosted select fold followed by the three-step packet shift, shared by
both dense tails (the shift sits at the fold-relative offsets
`FB+36..FB+39` in both instantiations): from the fold entry with the
fold state in the bank, the run ends at the absolute exit `E` with the
accepted in-word select trace as receipts, the word-start-shifted
packet in `rVal` (`decodePacket` convention), the fold categories plus
`packetShiftCats`, and the fold's preservation set intact.
-/
theorem denseFoldShift_runsTo
    (store : ReadStore) {program : E1Machine.Program} {FB R S c E : Nat}
    (hfold : HostedAt program FB
      (E1SelectBlock.selectFoldBlock FB R S c))
    (hbr1 : program[FB + 36]? = some (.brNZ rVal (FB + 38)))
    (hbr2 : program[FB + 37]? = some (.brNZ rOne (FB + 39)))
    (hadd : program[FB + 38]? = some (.add rVal rWI rVal))
    (hbr3 : program[FB + 39]? = some (.brNZ rOne E))
    (word : List Bool) (k : Nat) (regs1 : RegFile)
    (hOne : regs1 rOne = 1) (hC : regs1 rC = c)
    (hLen : regs1 rE = word.length)
    (hR : regs1 rR = SuccinctSpace.bitsToNatLE word)
    (hJC : regs1 rJC = 0) (hOcc : regs1 rSI = k)
    (hK : regs1 rK = bpWordChunkCount c word.length) :
    ∃ regsF : RegFile,
      RunsTo store program ⟨regs1, FB, false⟩ ⟨regsF, E, false⟩
        (bpChunkedWordSelectTraceResultAtSegmentsWithStore store R S c
          false word k).trace
        (E1SelectBlock.selectFoldCats store R c word 0
            (bpWordChunkCount c word.length) k ++
          packetShiftCats
            (bpChunkedWordSelectTraceResultAtSegmentsWithStore store R
              S c false word k).value) ∧
      E1Query.decodePacket (regsF rVal) =
        ((bpChunkedWordSelectTraceResultAtSegmentsWithStore store R S c
            false word k).value).map (fun off => regs1 rWI + off) ∧
      (∀ r, r ≤ 8 ∨ r = 10 ∨ r = 11 ∨ r = 13 ∨ r = 14 ∨ r = 15 ∨
          r = 16 ∨ r = 24 ∨ r = 25 ∨ r = 26 ∨ 28 ≤ r →
        regsF r = regs1 r) := by
  have hcpos : 0 < bpWordChunkCount c word.length := by
    rw [bpWordChunkCount_eq_sub]
    generalize (word.length - 1) / c = qq
    omega
  have hR' : regs1 E1SelectBlock.sR =
      SuccinctSpace.bitsToNatLE word / 2 ^ (0 * c) := by
    show regs1 rR = _
    rw [hR]
    simp
  have hJC' : regs1 E1SelectBlock.sJC = 0 * c := by
    show regs1 rJC = _
    simp [hJC]
  obtain ⟨regsM, hrunF, hdec, hpresF⟩ :=
    E1SelectBlock.selectFoldBlock_runsTo store hfold word
      (bpWordChunkCount c word.length) hcpos 0 k regs1 hOne hC hLen hR'
      hJC' hOcc hK
  have hrunF' :
      RunsTo store program ⟨regs1, FB, false⟩ ⟨regsM, FB + 36, false⟩
        (bpChunkedWordSelectTraceResultAtSegmentsWithStore store R S c
          false word k).trace
        (E1SelectBlock.selectFoldCats store R c word 0
          (bpWordChunkCount c word.length) k) := hrunF
  have hdec' : E1Query.decodePacket (regsM E1SelectBlock.sVal) =
      (bpChunkedWordSelectTraceResultAtSegmentsWithStore store R S c
        false word k).value := hdec
  have hMOne : regsM rOne = 1 := by
    rw [hpresF rOne (by decide)]
    exact hOne
  cases hv : (bpChunkedWordSelectTraceResultAtSegmentsWithStore store R
      S c false word k).value with
  | none =>
      rw [hv] at hdec'
      have hsval : regsM E1SelectBlock.sVal = 0 := by
        cases hval : regsM E1SelectBlock.sVal with
        | zero => rfl
        | succ u =>
            rw [hval] at hdec'
            simp at hdec'
      have hb1 := RunsTo.brNZ_not_taken (store := store)
        (s := ⟨regsM, FB + 36, false⟩) rfl hbr1 (by
          show regsM E1SelectBlock.sVal = 0
          exact hsval)
      have hb2 := RunsTo.brNZ_taken (store := store)
        (s := ⟨regsM, FB + 37, false⟩) rfl hbr2 (by
          show regsM rOne ≠ 0
          rw [hMOne]
          omega)
      have hb3 := RunsTo.brNZ_taken (store := store)
        (s := ⟨regsM, FB + 39, false⟩) rfl hbr3 (by
          show regsM rOne ≠ 0
          rw [hMOne]
          omega)
      have hall := hrunF'.trans (hb1.trans (hb2.trans hb3))
      refine ⟨regsM, ?_, ?_, ?_⟩
      · simpa [packetShiftCats] using hall
      · show E1Query.decodePacket (regsM E1SelectBlock.sVal) = _
        rw [hsval]
        rfl
      · intro r hr
        exact hpresF r hr
  | some off =>
      rw [hv] at hdec'
      have hsval : regsM E1SelectBlock.sVal = off + 1 := by
        cases hval : regsM E1SelectBlock.sVal with
        | zero =>
            rw [hval] at hdec'
            simp at hdec'
        | succ u =>
            rw [hval] at hdec'
            simp at hdec'
            omega
      have hb1 := RunsTo.brNZ_taken (store := store)
        (s := ⟨regsM, FB + 36, false⟩) rfl hbr1 (by
          show regsM E1SelectBlock.sVal ≠ 0
          rw [hsval]
          omega)
      have hb2 := RunsTo.add (store := store)
        (s := ⟨regsM, FB + 38, false⟩) rfl hadd
      have hb3 := RunsTo.brNZ_taken (store := store)
        (s := ⟨regsM.write rVal (regsM rWI + regsM rVal), FB + 39,
          false⟩) rfl hbr3 (by
          show regsM.write rVal (regsM rWI + regsM rVal) rOne ≠ 0
          rw [RegFile.write_other _ _ (by decide), hMOne]
          omega)
      have hall := hrunF'.trans (hb1.trans (hb2.trans hb3))
      refine ⟨regsM.write rVal (regsM rWI + regsM rVal), ?_, ?_, ?_⟩
      · simpa [packetShiftCats] using hall
      · have hMWI : regsM rWI = regs1 rWI := hpresF rWI (by decide)
        have hsval' : regsM rVal = off + 1 := hsval
        have hout : regsM.write rVal (regsM rWI + regsM rVal) rVal =
            regs1 rWI + off + 1 := by
          rw [RegFile.write_same, hMWI, hsval']
          omega
        rw [hout]
        simp
      · intro r hr
        have hr9 : r ≠ 9 := by omega
        rw [RegFile.write_other _ _ (show r ≠ rVal from hr9),
          hpresF r hr]

/-! ### Whole-leg simulation -/

/--
The whole dense two-word select leg: from block entry with the query
state in the extension bank and the pinned constants, the hosted leg
runs — with exact fuel — to `L + 193` with

* receipts POSITIONALLY EQUAL to
  `(bpChunkedDenseTwoWordSelectTraceResultWithStore W (G+4) S c false
  bitWords store bPos bOcc q).trace` (the accepted dense leaf's trace
  twin, across all four control branches),
* the leaf's optional value under `decodePacket` in `rVal`,
* the derived category log `denseLegCats`, and
* the pinned constants (`24..26`) and the extension bank (`28 ≤ r`)
  preserved.

The route-side hypotheses `hlen1`/`hlen2` identify the machine's
min-chain word lengths with the stored words' lengths; the canonical
instantiation discharges them from the dense store's word-length
characterization.
-/
theorem denseSelectLegBlock_runsTo
    (store : ReadStore) {program : E1Machine.Program}
    {L W G S c WS N2 : Nat} {bits : List Bool}
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits WS)
    (hhost : HostedAt program L (denseSelectLegBlock L W G S c WS N2))
    (regs0 : RegFile)
    (hlen1 : ∀ w1, store.readWord? W (regs0 xBPos / WS) = some w1 →
      w1.length = Nat.min WS (N2 - regs0 xBPos / WS * WS))
    (hlen2 : ∀ w2,
      store.readWord? W (regs0 xBPos / WS + 1) = some w2 →
      w2.length = Nat.min WS (N2 - (regs0 xBPos / WS + 1) * WS))
    (hOne : regs0 rOne = 1) (hC : regs0 rC = c)
    (hEight : regs0 rEight = 8) :
    ∃ regsF : RegFile,
      RunsTo store program ⟨regs0, L, false⟩ ⟨regsF, L + 193, false⟩
        (bpChunkedDenseTwoWordSelectTraceResultWithStore W (G + 4) S c
          false bitWords store (regs0 xBPos) (regs0 xBOcc)
          (regs0 xQ)).trace
        (denseLegCats store W G S c WS (regs0 xBPos) (regs0 xBOcc)
          (regs0 xQ)) ∧
      E1Query.decodePacket (regsF rVal) =
        (bpChunkedDenseTwoWordSelectTraceResultWithStore W (G + 4) S c
          false bitWords store (regs0 xBPos) (regs0 xBOcc)
          (regs0 xQ)).value ∧
      (∀ r, (24 ≤ r ∧ r ≤ 26) ∨ 28 ≤ r → regsF r = regs0 r) := by
  obtain ⟨hHead, hbrCmp, hPre, hbrW2p, hbrW2m, hSetup2, hFold2, hbrP2a,
    hbrP2b, hAdd2, hbrP2c, hSetup1, hFold1, hbrP1a, hbrP1b, hAdd1,
    hbrP1c, hMissC⟩ := denseSelectLegBlock_hosting hhost
  cases hword1 : store.readWord? W (regs0 xBPos / WS) with
  | none =>
      obtain ⟨regsH, hrunH, hHWrd, hHpres⟩ :=
        denseHeadBlock_runsTo_miss store hHead regs0 hword1 hOne
      have hconst := RunsTo.const (store := store)
        (s := ⟨regsH, L + 192, false⟩) rfl hMissC
      have hall := hrunH.trans hconst
      have hTrace :
          (bpChunkedDenseTwoWordSelectTraceResultWithStore W (G + 4) S
            c false bitWords store (regs0 xBPos) (regs0 xBOcc)
            (regs0 xQ)).trace =
          [TraceEvent.readWord W (regs0 xBPos / WS) none] := by
        simp [bpChunkedDenseTwoWordSelectTraceResultWithStore,
          TraceResult.bind, TraceResult.pure, bpWordReadTraceResult,
          hword1]
      have hCats :
          denseLegCats store W G S c WS (regs0 xBPos) (regs0 xBOcc)
            (regs0 xQ) =
          denseHeadMissCats ++ [Category.registerWrite] := by
        simp [denseLegCats, hword1]
      have hValue :
          (bpChunkedDenseTwoWordSelectTraceResultWithStore W (G + 4) S
            c false bitWords store (regs0 xBPos) (regs0 xBOcc)
            (regs0 xQ)).value = none := by
        simp [bpChunkedDenseTwoWordSelectTraceResultWithStore,
          TraceResult.bind, TraceResult.pure, bpWordReadTraceResult,
          hword1]
      refine ⟨regsH.write rVal 0, ?_, ?_, ?_⟩
      · rw [hTrace, hCats]
        simpa using hall
      · rw [hValue]
        simp
      · intro r hr
        have hr9 : r ≠ 9 := by omega
        rw [RegFile.write_other _ _ (show r ≠ rVal from hr9),
          hHpres r (by omega) (by omega) (by omega) (by omega)]
  | some w1 =>
      obtain ⟨regsH, hrunH, hHP, hHWI, hHSI, hHBlk, hHWrd, hHSup, hHVal,
        hHA, hHbank⟩ :=
        denseHeadBlock_runsTo_present store hHead regs0 w1 hword1
          (hlen1 w1 hword1) hOne hC hEight
      have hHOne : regsH rOne = 1 := by
        rw [hHbank rOne (by decide)]
        exact hOne
      have hHC : regsH rC = c := by
        rw [hHbank rC (by decide)]
        exact hC
      have hHEight : regsH rEight = 8 := by
        rw [hHbank rEight (by decide)]
        exact hEight
      by_cases hcmp : regs0 xQ - regs0 xBOcc <
          (bpChunkedWordRankTraceResultAtSegmentWithStore store (G + 4)
              c false w1 w1.length).value -
            (bpChunkedWordRankTraceResultAtSegmentWithStore store
              (G + 4) c false w1
              (regs0 xBPos - regs0 xBPos / WS * WS)).value
      · -- FIRST-WORD TAIL
        have hbr := RunsTo.brNZ_taken (store := store)
          (s := ⟨regsH, L + 84, false⟩) rfl hbrCmp (by
            show regsH rA ≠ 0
            rw [hHA, if_pos hcmp]
            omega)
        have hrunT := RunsTo.straight store (denseTail1Setup c)
          (denseTail1Setup_straight c) (L + 143) hSetup1 regsH
        obtain ⟨regsT, hregsT⟩ :
            ∃ x, straightRegs store (denseTail1Setup c) regsH = x :=
          ⟨_, rfl⟩
        rw [hregsT] at hrunT
        have hreadsT :
            straightReads store (denseTail1Setup c) regsH = [] := by
          tail_eval
        rw [hreadsT] at hrunT
        have hTpres : ∀ r, r ≠ 13 → r ≠ 12 → r ≠ 17 → r ≠ 27 →
            r ≠ 22 → r ≠ 18 → r ≠ 23 → regsT r = regsH r := by
          intro r h1 h2 h3 h4 h5 h6 h7
          rw [← hregsT]
          apply straightRegs_preserves
          intro instr hi
          simp only [denseTail1Setup, List.mem_cons, List.not_mem_nil,
            or_false] at hi
          rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
              rfl <;> tail_writes <;> omega
        have hTLen : regsT rE = w1.length := by
          rw [← hregsT]
          tail_eval <;> simp [hHBlk]
        have hTOcc : regsT rSI =
            (bpChunkedWordRankTraceResultAtSegmentWithStore store
                (G + 4) c false w1
                (regs0 xBPos - regs0 xBPos / WS * WS)).value +
              (regs0 xQ - regs0 xBOcc) := by
          rw [← hregsT]
          tail_eval <;> simp [hHSup, hHSI]
        have hTR : regsT rR = SuccinctSpace.bitsToNatLE w1 := by
          rw [← hregsT]
          tail_eval <;>
            simp [hHWrd, hHOne, decodeRead,
              SuccinctSpace.WordRAMBridge.bitsToNatLE_eq]
        have hTJC : regsT rJC = 0 := by
          rw [← hregsT]
          tail_eval
        have hTK : regsT rK = bpWordChunkCount c w1.length := by
          rw [← hregsT, bpWordChunkCount_eq_sub]
          tail_eval <;> simp [hHBlk, hHOne, hHEight]
        have hTOne : regsT rOne = 1 := by
          rw [hTpres rOne (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide), hHOne]
        have hTC : regsT rC = c := by
          rw [hTpres rC (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide), hHC]
        have hTWI : regsT rWI = regs0 xBPos / WS * WS := by
          rw [hTpres rWI (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide), hHWI]
        obtain ⟨regsF, hrunFS, hdecFS, hpresFS⟩ :=
          denseFoldShift_runsTo store hFold1 hbrP1a hbrP1b hAdd1 hbrP1c
            w1
            ((bpChunkedWordRankTraceResultAtSegmentWithStore store
                (G + 4) c false w1
                (regs0 xBPos - regs0 xBPos / WS * WS)).value +
              (regs0 xQ - regs0 xBOcc))
            regsT hTOne hTC hTLen hTR hTJC hTOcc hTK
        have hall := hrunH.trans (hbr.trans (hrunT.trans hrunFS))
        have hTrace :
            (bpChunkedDenseTwoWordSelectTraceResultWithStore W (G + 4)
              S c false bitWords store (regs0 xBPos) (regs0 xBOcc)
              (regs0 xQ)).trace =
            TraceEvent.readWord W (regs0 xBPos / WS) (some w1) ::
              (((bpChunkedWordRankTraceResultAtSegmentWithStore store
                    (G + 4) c false w1
                    (regs0 xBPos - regs0 xBPos / WS * WS)).trace ++
                  (bpChunkedWordRankTraceResultAtSegmentWithStore store
                    (G + 4) c false w1 w1.length).trace) ++
                (bpChunkedWordSelectTraceResultAtSegmentsWithStore
                  store (G + 4) S c false w1
                  ((bpChunkedWordRankTraceResultAtSegmentWithStore
                      store (G + 4) c false w1
                      (regs0 xBPos - regs0 xBPos / WS * WS)).value +
                    (regs0 xQ - regs0 xBOcc))).trace) := by
          simp [bpChunkedDenseTwoWordSelectTraceResultWithStore,
            TraceResult.bind, TraceResult.map, TraceResult.pure,
            bpWordReadTraceResult, hword1, hcmp]
        have hCats :
            denseLegCats store W G S c WS (regs0 xBPos) (regs0 xBOcc)
              (regs0 xQ) =
            denseHeadPresentCats
                (bpWordChunkCount c
                  (bpWordRankEffLimit w1
                    (regs0 xBPos - regs0 xBPos / WS * WS)))
                (bpWordChunkCount c (bpWordRankEffLimit w1
                  w1.length)) ++
              ([Category.branch] ++
                (denseTail1SetupCats ++
                  (E1SelectBlock.selectFoldCats store (G + 4) c w1 0
                      (bpWordChunkCount c w1.length)
                      ((bpChunkedWordRankTraceResultAtSegmentWithStore
                          store (G + 4) c false w1
                          (regs0 xBPos - regs0 xBPos / WS * WS)).value +
                        (regs0 xQ - regs0 xBOcc)) ++
                    packetShiftCats
                      (bpChunkedWordSelectTraceResultAtSegmentsWithStore
                        store (G + 4) S c false w1
                        ((bpChunkedWordRankTraceResultAtSegmentWithStore
                            store (G + 4) c false w1
                            (regs0 xBPos -
                              regs0 xBPos / WS * WS)).value +
                          (regs0 xQ - regs0 xBOcc))).value))) := by
          simp [denseLegCats, hword1, hcmp]
        have hValue :
            (bpChunkedDenseTwoWordSelectTraceResultWithStore W (G + 4)
              S c false bitWords store (regs0 xBPos) (regs0 xBOcc)
              (regs0 xQ)).value =
            ((bpChunkedWordSelectTraceResultAtSegmentsWithStore store
                (G + 4) S c false w1
                ((bpChunkedWordRankTraceResultAtSegmentWithStore store
                    (G + 4) c false w1
                    (regs0 xBPos - regs0 xBPos / WS * WS)).value +
                  (regs0 xQ - regs0 xBOcc))).value).map
              (fun off => regs0 xBPos / WS * WS + off) := by
          simp [bpChunkedDenseTwoWordSelectTraceResultWithStore,
            TraceResult.bind, TraceResult.map, TraceResult.pure,
            bpWordReadTraceResult, hword1, hcmp]
        refine ⟨regsF, ?_, ?_, ?_⟩
        · rw [hTrace, hCats]
          simpa using hall
        · rw [hValue]
          rw [hTWI] at hdecFS
          exact hdecFS
        · intro r hr
          rw [hpresFS r (by omega),
            hTpres r (by omega) (by omega) (by omega) (by omega)
              (by omega) (by omega) (by omega),
            hHbank r hr]
      · -- SECOND-WORD PATHS
        have hbr := RunsTo.brNZ_not_taken (store := store)
          (s := ⟨regsH, L + 84, false⟩) rfl hbrCmp (by
            show regsH rA = 0
            rw [hHA, if_neg hcmp])
        have hrunP := RunsTo.straight store (denseTail2Pre W)
          (denseTail2Pre_straight W) (L + 85) hPre regsH
        obtain ⟨regsP, hregsP⟩ :
            ∃ x, straightRegs store (denseTail2Pre W) regsH = x :=
          ⟨_, rfl⟩
        rw [hregsP] at hrunP
        have hreadsP : straightReads store (denseTail2Pre W) regsH =
            [TraceEvent.readWord W (regs0 xBPos / WS + 1)
              (store.readWord? W (regs0 xBPos / WS + 1))] := by
          tail_eval <;> simp [hHP, hHOne]
        rw [hreadsP] at hrunP
        have hPpres : ∀ r, r ≠ 10 → r ≠ 16 → regsP r = regsH r := by
          intro r h1 h2
          rw [← hregsP]
          apply straightRegs_preserves
          intro instr hi
          simp only [denseTail2Pre, List.mem_cons, List.not_mem_nil,
            or_false] at hi
          rcases hi with rfl | rfl <;> tail_writes <;> omega
        have hPP : regsP rP = regs0 xBPos / WS + 1 := by
          rw [← hregsP]
          tail_eval <;> simp [hHP, hHOne]
        have hPWrd : regsP rWrd =
            decodeRead (store.readWord? W (regs0 xBPos / WS + 1)) := by
          rw [← hregsP]
          tail_eval <;> simp [hHP, hHOne]
        have hPOne : regsP rOne = 1 := by
          rw [hPpres rOne (by decide) (by decide), hHOne]
        have hPC : regsP rC = c := by
          rw [hPpres rC (by decide) (by decide), hHC]
        have hPEight : regsP rEight = 8 := by
          rw [hPpres rEight (by decide) (by decide), hHEight]
        have hPSI : regsP rSI = regs0 xQ - regs0 xBOcc := by
          rw [hPpres rSI (by decide) (by decide), hHSI]
        have hPVal : regsP rVal =
            (bpChunkedWordRankTraceResultAtSegmentWithStore store
                (G + 4) c false w1 w1.length).value -
              (bpChunkedWordRankTraceResultAtSegmentWithStore store
                (G + 4) c false w1
                (regs0 xBPos - regs0 xBPos / WS * WS)).value := by
          rw [hPpres rVal (by decide) (by decide), hHVal]
        cases hword2 : store.readWord? W (regs0 xBPos / WS + 1) with
        | none =>
            have hPWrd0 : regsP rWrd = 0 := by
              rw [hPWrd, hword2]
              rfl
            have hbrA := RunsTo.brNZ_not_taken (store := store)
              (s := ⟨regsP, L + 87, false⟩) rfl hbrW2p (by
                show regsP rWrd = 0
                exact hPWrd0)
            have hbrB := RunsTo.brNZ_taken (store := store)
              (s := ⟨regsP, L + 88, false⟩) rfl hbrW2m (by
                show regsP rOne ≠ 0
                rw [hPOne]
                omega)
            have hconst := RunsTo.const (store := store)
              (s := ⟨regsP, L + 192, false⟩) rfl hMissC
            have hall := hrunH.trans (hbr.trans (hrunP.trans
              (hbrA.trans (hbrB.trans hconst))))
            have hTrace :
                (bpChunkedDenseTwoWordSelectTraceResultWithStore W
                  (G + 4) S c false bitWords store (regs0 xBPos)
                  (regs0 xBOcc) (regs0 xQ)).trace =
                TraceEvent.readWord W (regs0 xBPos / WS) (some w1) ::
                  (((bpChunkedWordRankTraceResultAtSegmentWithStore
                        store (G + 4) c false w1
                        (regs0 xBPos - regs0 xBPos / WS * WS)).trace ++
                      (bpChunkedWordRankTraceResultAtSegmentWithStore
                        store (G + 4) c false w1 w1.length).trace) ++
                    [TraceEvent.readWord W (regs0 xBPos / WS + 1)
                      none]) := by
              simp [bpChunkedDenseTwoWordSelectTraceResultWithStore,
                TraceResult.bind, TraceResult.pure,
                bpWordReadTraceResult, hword1, hcmp, hword2]
            have hCats :
                denseLegCats store W G S c WS (regs0 xBPos)
                  (regs0 xBOcc) (regs0 xQ) =
                denseHeadPresentCats
                    (bpWordChunkCount c
                      (bpWordRankEffLimit w1
                        (regs0 xBPos - regs0 xBPos / WS * WS)))
                    (bpWordChunkCount c
                      (bpWordRankEffLimit w1 w1.length)) ++
                  ([Category.branch] ++
                    ([Category.arithmetic, Category.memoryRead] ++
                      [Category.branch, Category.branch,
                        Category.registerWrite])) := by
              simp [denseLegCats, hword1, hcmp, hword2]
            have hValue :
                (bpChunkedDenseTwoWordSelectTraceResultWithStore W
                  (G + 4) S c false bitWords store (regs0 xBPos)
                  (regs0 xBOcc) (regs0 xQ)).value = none := by
              simp [bpChunkedDenseTwoWordSelectTraceResultWithStore,
                TraceResult.bind, TraceResult.pure,
                bpWordReadTraceResult, hword1, hcmp, hword2]
            refine ⟨regsP.write rVal 0, ?_, ?_, ?_⟩
            · rw [hTrace, hCats]
              simpa [hword2] using hall
            · rw [hValue]
              simp
            · intro r hr
              have hr9 : r ≠ 9 := by omega
              rw [RegFile.write_other _ _ (show r ≠ rVal from hr9),
                hPpres r (by omega) (by omega), hHbank r hr]
        | some w2 =>
            have hPWrdS : regsP rWrd = decodeRead (some w2) := by
              rw [hPWrd, hword2]
            have hbrA := RunsTo.brNZ_taken (store := store)
              (s := ⟨regsP, L + 87, false⟩) rfl hbrW2p (by
                show regsP rWrd ≠ 0
                rw [hPWrdS]
                simp [decodeRead])
            have hrunS := RunsTo.straight store
              (denseTail2Setup WS N2 c)
              (denseTail2Setup_straight WS N2 c) (L + 89) hSetup2 regsP
            obtain ⟨regsT2, hregsT2⟩ :
                ∃ x, straightRegs store (denseTail2Setup WS N2 c)
                  regsP = x := ⟨_, rfl⟩
            rw [hregsT2] at hrunS
            have hreadsS : straightReads store
                (denseTail2Setup WS N2 c) regsP = [] := by
              tail_eval
            rw [hreadsS] at hrunS
            have hT2pres : ∀ r, r ≠ 11 → r ≠ 22 → r ≠ 23 → r ≠ 19 →
                r ≠ 13 → r ≠ 12 → r ≠ 17 → r ≠ 27 → r ≠ 18 →
                regsT2 r = regsP r := by
              intro r h1 h2 h3 h4 h5 h6 h7 h8 h9
              rw [← hregsT2]
              apply straightRegs_preserves
              intro instr hi
              simp only [denseTail2Setup, List.mem_cons,
                List.not_mem_nil, or_false] at hi
              rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                  rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
                tail_writes <;> omega
            have hlen2' := hlen2 w2 hword2
            have hT2WI : regsT2 rWI =
                (regs0 xBPos / WS + 1) * WS := by
              rw [← hregsT2]
              tail_eval <;> simp [hPP]
            have hT2Len : regsT2 rE = w2.length := by
              rw [← hregsT2]
              tail_eval <;> simp [hPP]
              rw [hlen2', nat_min_eq_sub_sub]
            have hT2Occ : regsT2 rSI =
                (regs0 xQ - regs0 xBOcc) -
                  ((bpChunkedWordRankTraceResultAtSegmentWithStore
                      store (G + 4) c false w1 w1.length).value -
                    (bpChunkedWordRankTraceResultAtSegmentWithStore
                      store (G + 4) c false w1
                      (regs0 xBPos - regs0 xBPos / WS * WS)).value) := by
              rw [← hregsT2]
              tail_eval <;> simp [hPSI, hPVal]
            have hT2R : regsT2 rR = SuccinctSpace.bitsToNatLE w2 := by
              rw [← hregsT2]
              tail_eval <;>
                simp [hPWrdS, hPOne, decodeRead,
                  SuccinctSpace.WordRAMBridge.bitsToNatLE_eq]
            have hT2JC : regsT2 rJC = 0 := by
              rw [← hregsT2]
              tail_eval
            have hT2K : regsT2 rK = bpWordChunkCount c w2.length := by
              rw [← hregsT2, bpWordChunkCount_eq_sub, hlen2',
                nat_min_eq_sub_sub]
              tail_eval <;> simp [hPP, hPOne, hPEight]
            have hT2One : regsT2 rOne = 1 := by
              rw [hT2pres rOne (by decide) (by decide) (by decide)
                (by decide) (by decide) (by decide) (by decide)
                (by decide) (by decide), hPOne]
            have hT2C : regsT2 rC = c := by
              rw [hT2pres rC (by decide) (by decide) (by decide)
                (by decide) (by decide) (by decide) (by decide)
                (by decide) (by decide), hPC]
            obtain ⟨regsF, hrunFS, hdecFS, hpresFS⟩ :=
              denseFoldShift_runsTo store hFold2 hbrP2a hbrP2b hAdd2
                hbrP2c w2
                ((regs0 xQ - regs0 xBOcc) -
                  ((bpChunkedWordRankTraceResultAtSegmentWithStore
                      store (G + 4) c false w1 w1.length).value -
                    (bpChunkedWordRankTraceResultAtSegmentWithStore
                      store (G + 4) c false w1
                      (regs0 xBPos - regs0 xBPos / WS * WS)).value))
                regsT2 hT2One hT2C hT2Len hT2R hT2JC hT2Occ hT2K
            have hall := hrunH.trans (hbr.trans (hrunP.trans
              (hbrA.trans (hrunS.trans hrunFS))))
            have hTrace :
                (bpChunkedDenseTwoWordSelectTraceResultWithStore W
                  (G + 4) S c false bitWords store (regs0 xBPos)
                  (regs0 xBOcc) (regs0 xQ)).trace =
                TraceEvent.readWord W (regs0 xBPos / WS) (some w1) ::
                  (((bpChunkedWordRankTraceResultAtSegmentWithStore
                        store (G + 4) c false w1
                        (regs0 xBPos - regs0 xBPos / WS * WS)).trace ++
                      (bpChunkedWordRankTraceResultAtSegmentWithStore
                        store (G + 4) c false w1 w1.length).trace) ++
                    (TraceEvent.readWord W (regs0 xBPos / WS + 1)
                        (some w2) ::
                      (bpChunkedWordSelectTraceResultAtSegmentsWithStore
                        store (G + 4) S c false w2
                        ((regs0 xQ - regs0 xBOcc) -
                          ((bpChunkedWordRankTraceResultAtSegmentWithStore
                              store (G + 4) c false w1
                              w1.length).value -
                            (bpChunkedWordRankTraceResultAtSegmentWithStore
                              store (G + 4) c false w1
                              (regs0 xBPos -
                                regs0 xBPos / WS * WS)).value))).trace)) := by
              simp [bpChunkedDenseTwoWordSelectTraceResultWithStore,
                TraceResult.bind, TraceResult.map, TraceResult.pure,
                bpWordReadTraceResult, hword1, hcmp, hword2]
            have hCats :
                denseLegCats store W G S c WS (regs0 xBPos)
                  (regs0 xBOcc) (regs0 xQ) =
                denseHeadPresentCats
                    (bpWordChunkCount c
                      (bpWordRankEffLimit w1
                        (regs0 xBPos - regs0 xBPos / WS * WS)))
                    (bpWordChunkCount c
                      (bpWordRankEffLimit w1 w1.length)) ++
                  ([Category.branch] ++
                    ([Category.arithmetic, Category.memoryRead] ++
                      ([Category.branch] ++
                        (denseTail2SetupCats ++
                          (E1SelectBlock.selectFoldCats store (G + 4) c
                              w2 0 (bpWordChunkCount c w2.length)
                              ((regs0 xQ - regs0 xBOcc) -
                                ((bpChunkedWordRankTraceResultAtSegmentWithStore
                                    store (G + 4) c false w1
                                    w1.length).value -
                                  (bpChunkedWordRankTraceResultAtSegmentWithStore
                                    store (G + 4) c false w1
                                    (regs0 xBPos -
                                      regs0 xBPos / WS * WS)).value)) ++
                            packetShiftCats
                              (bpChunkedWordSelectTraceResultAtSegmentsWithStore
                                store (G + 4) S c false w2
                                ((regs0 xQ - regs0 xBOcc) -
                                  ((bpChunkedWordRankTraceResultAtSegmentWithStore
                                      store (G + 4) c false w1
                                      w1.length).value -
                                    (bpChunkedWordRankTraceResultAtSegmentWithStore
                                      store (G + 4) c false w1
                                      (regs0 xBPos -
                                        regs0 xBPos / WS *
                                          WS)).value))).value))))) := by
              simp [denseLegCats, hword1, hcmp, hword2]
            have hValue :
                (bpChunkedDenseTwoWordSelectTraceResultWithStore W
                  (G + 4) S c false bitWords store (regs0 xBPos)
                  (regs0 xBOcc) (regs0 xQ)).value =
                ((bpChunkedWordSelectTraceResultAtSegmentsWithStore
                    store (G + 4) S c false w2
                    ((regs0 xQ - regs0 xBOcc) -
                      ((bpChunkedWordRankTraceResultAtSegmentWithStore
                          store (G + 4) c false w1 w1.length).value -
                        (bpChunkedWordRankTraceResultAtSegmentWithStore
                          store (G + 4) c false w1
                          (regs0 xBPos -
                            regs0 xBPos / WS * WS)).value))).value).map
                  (fun off => (regs0 xBPos / WS + 1) * WS + off) := by
              simp [bpChunkedDenseTwoWordSelectTraceResultWithStore,
                TraceResult.bind, TraceResult.map, TraceResult.pure,
                bpWordReadTraceResult, hword1, hcmp, hword2]
            refine ⟨regsF, ?_, ?_, ?_⟩
            · rw [hTrace, hCats]
              simpa [hword2] using hall
            · rw [hValue]
              rw [hT2WI] at hdecFS
              exact hdecFS
            · intro r hr
              rw [hpresFS r (by omega),
                hT2pres r (by omega) (by omega) (by omega) (by omega)
                  (by omega) (by omega) (by omega) (by omega)
                  (by omega),
                hPpres r (by omega) (by omega), hHbank r hr]

/-! ### Width certificate (REQ-E1-02 consumption for the whole leg) -/

/--
Constructor-exhaustive width certificate for the whole dense leg:
delegates the head and the two hosted select folds to their
certificates and checks every tail instruction's fields — register
numerals, the packed-word segment `W`, the chunk-table segments
`G + 4`/`S`, the per-shape constants `WS` (positive divisor
requirement on `divConst` handled by `c`) and `N2`, and the branch
targets, all within the modeled width.
-/
theorem denseSelectLegBlock_fits {w L W G S c WS N2 : Nat}
    (hreg : 40 ≤ 2 ^ w) (hW : W < 2 ^ w) (hG : G + 4 < 2 ^ w)
    (hS : S < 2 ^ w) (hcpos : 0 < c) (hpow : 2 ^ c < 2 ^ w)
    (hlin : 2 * c + 2 < 2 ^ w) (hWSpos : 0 < WS) (hWS : WS < 2 ^ w)
    (hN2 : N2 < 2 ^ w) (hL : L + 193 < 2 ^ w) :
    ∀ instr ∈ denseSelectLegBlock L W G S c WS N2,
      instr.FieldsFit w := by
  intro instr hmem
  simp only [denseSelectLegBlock, denseTail2Pre, denseTail2Setup,
    denseTail1Setup, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, or_assoc] at hmem
  rcases hmem with hmem | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | hmem | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | hmem | rfl | rfl | rfl | rfl | rfl
  all_goals
    first
      | exact denseHeadBlock_fits hreg hW hG hcpos hpow hlin hWSpos
          hWS hN2 (by omega) (by omega) instr hmem
      | exact E1SelectBlock.selectFoldBlock_fits (by omega) hG hS hpow
          hlin (by omega) instr hmem
      | (simp only [Instr.FieldsFit, rVal, rP, rWI, rSI, rE, rSup,
          rBlk, rWrd, rR, rK, rT, rA, rB, rOne, rEight, rJC]
         omega)

end E1DenseSelectBlock
end WordRAM
end RMQ
