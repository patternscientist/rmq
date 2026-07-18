import RMQ.Core.WordRAM.E1StraightLine
import RMQ.Core.WordRAM.E1RankBridge
import RMQ.Core.WordRAM.E1QueryProgram

/-!
# E1 amended machine: in-word select fold block (M3c-3a)

The machine program fragment simulating the accepted early-exit in-word
select fold
`bpChunkedWordSelectTraceFromWithStore store R S c false word j count k`
(`ChargedRankSelectTrace.lean`), the core of the dense leg of the accepted
select-close component (frozen matrix REQ-E1-03/04).

Shape of the block (36 instructions at block base `LB`; the block is a
loop component, not a whole program):

* loop head (`selSeg1`, 22 instructions): derive the slice length
  `t = min c (len - j*c)` and window chunk value `v = R % 2^c` by constant
  div/mod forms, advance the remaining-word register, read the fringe
  chunk table at slot `(v*(c+1)+t)*(c+1)+t` (segment `R`), decode the
  entry's false-rank `r` by the `bpChunkRankOfEntry` constant chain, and
  compare the remaining occurrence `k < r`;
* the exit `brNZ` (at `LB+22`) jumps to the exit tail when the occurrence
  falls inside the current chunk — the fold's DATA-DEPENDENT EARLY EXIT;
* continue tail (`selSegCont` + back edge, 4 instructions): subtract the
  chunk's rank from the occurrence, advance the cursor, decrement the
  counter, loop while nonzero;
* exhaustion tail (`selSegExhaust` + jump, 3 instructions): the fold's
  `pure none` — packet `0`;
* exit tail (`selSegExit`, 6 instructions): read the select chunk table at
  slot `v*(c+1)+k` (segment `S`) and assemble the found position packet
  `j*c + sel + 1` (option shift, `decodePacket`).

The simulation theorem `selectFoldBlock_runsTo` delivers, for any hosting
program and any store: exact receipts POSITIONALLY EQUAL to the fold's
trace, the fold's optional value under `decodePacket` in `sVal`, and the
derived category log `selectFoldCats` (a function of store and inputs,
mirroring the fold's exit structure, with derived length bound
`<= 27 * count + 3`).
-/

namespace RMQ
namespace WordRAM
namespace E1SelectBlock

open E1Machine
open RMQ.SuccinctClose

/-! ## Frozen register bank (select fold registers)

Numerals are aligned with the rank-close bank where the roles coincide
(`sT/sV/sSlot/sA/sB/sOne/sC/sJC` at `19..25/27`); the fold-specific state
(`sVal/sOcc/sLen/sR/sK`) reuses freed rank registers.  The block never
writes `sLen/sOne/sC` (loop-constant inputs). -/

/-- Output: the found-position packet (`decodePacket` convention). -/
abbrev sVal : Nat := 9
/-- Remaining occurrence `k`. -/
abbrev sOcc : Nat := 12
/-- Word length (loop constant). -/
abbrev sLen : Nat := 13
/-- Remaining word `W / 2^(j*c)`. -/
abbrev sR : Nat := 17
/-- Loop counter (remaining chunk visits). -/
abbrev sK : Nat := 18
/-- Slice length `t`. -/
abbrev sT : Nat := 19
/-- Window chunk value `v`. -/
abbrev sV : Nat := 20
/-- Chunk-table slot. -/
abbrev sSlot : Nat := 21
/-- Scratch. -/
abbrev sA : Nat := 22
/-- Scratch (holds the decoded chunk rank at the exit test). -/
abbrev sB : Nat := 23
/-- Pinned constant `1` (input). -/
abbrev sOne : Nat := 24
/-- Pinned constant `c` (input). -/
abbrev sC : Nat := 25
/-- Chunk cursor `j * c`. -/
abbrev sJC : Nat := 27

/-! ## Block segments -/

/-- Loop head: slice length, window chunk value, remaining-word advance,
fringe chunk-table read, false-rank decode, exit test. -/
def selSeg1 (R c : Nat) : List Instr :=
  [ .sub sA sLen sJC
  , .sub sB sC sA
  , .sub sT sC sB
  , .divConst sA sR (2 ^ c)
  , .mulConst sB sA (2 ^ c)
  , .sub sV sR sB
  , .move sR sA
  , .mulConst sA sV (c + 1)
  , .add sA sA sT
  , .mulConst sA sA (c + 1)
  , .add sSlot sA sT
  , .readMem sA R sSlot
  , .sub sA sA sOne
  , .divConst sA sA (c + 1)
  , .divConst sB sA (2 * c + 2)
  , .mulConst sB sB (2 * c + 2)
  , .sub sA sA sB
  , .add sA sA sT
  , .sub sA sA sC
  , .divConst sA sA 2
  , .sub sB sT sA
  , .natLt sA sOcc sB ]

@[simp] theorem selSeg1_length (R c : Nat) : (selSeg1 R c).length = 22 := rfl

/-- Continue tail: consume the chunk's rank, advance, decrement. -/
def selSegCont : List Instr :=
  [ .sub sOcc sOcc sB
  , .add sJC sJC sC
  , .sub sK sK sOne ]

@[simp] theorem selSegCont_length : selSegCont.length = 3 := rfl

/-- Exhaustion tail: the fold's `pure none` (packet `0`). -/
def selSegExhaust : List Instr :=
  [ .const sVal 0
  , .const sA 1 ]

@[simp] theorem selSegExhaust_length : selSegExhaust.length = 2 := rfl

/-- Exit tail: select chunk-table read and found-position packet. -/
def selSegExit (S c : Nat) : List Instr :=
  [ .mulConst sA sV (c + 1)
  , .add sA sA sOcc
  , .readMem sA S sA
  , .sub sA sA sOne
  , .add sA sA sJC
  , .add sVal sA sOne ]

@[simp] theorem selSegExit_length (S c : Nat) :
    (selSegExit S c).length = 6 := rfl

/--
The in-word select fold block at block base `LB`, fringe chunk-table
segment `R`, select chunk-table segment `S`, chunk width `c`.  Layout:
loop head `LB..LB+21`, exit branch at `LB+22` (target `LB+30`), continue
tail `LB+23..25`, back edge at `LB+26` (target `LB`), exhaustion tail
`LB+27..28`, exhaustion jump at `LB+29` (target `LB+36`), exit tail
`LB+30..35`, block exit `LB+36`.
-/
def selectFoldBlock (LB R S c : Nat) : List Instr :=
  selSeg1 R c ++
    ([Instr.brNZ sA (LB + 30)] ++
      (selSegCont ++
        ([Instr.brNZ sK LB] ++
          (selSegExhaust ++
            ([Instr.brNZ sA (LB + 36)] ++ selSegExit S c)))))

@[simp] theorem selectFoldBlock_length (LB R S c : Nat) :
    (selectFoldBlock LB R S c).length = 36 := rfl

/-! ## Frozen category logs -/

/-- Categories charged by the loop head. -/
def selSeg1Cats : List Category :=
  [ .arithmetic, .arithmetic, .arithmetic, .arithmetic, .arithmetic
  , .arithmetic, .registerWrite, .arithmetic, .arithmetic, .arithmetic
  , .arithmetic, .memoryRead, .arithmetic, .arithmetic, .arithmetic
  , .arithmetic, .arithmetic, .arithmetic, .arithmetic, .arithmetic
  , .arithmetic, .comparison ]

@[simp] theorem selSeg1Cats_length : selSeg1Cats.length = 22 := rfl

/-- Categories charged by one continuing loop pass (head, exit branch not
taken, continue tail, back edge). -/
def selContPassCats : List Category :=
  selSeg1Cats ++
    [ .branch, .arithmetic, .arithmetic, .arithmetic, .branch ]

@[simp] theorem selContPassCats_length : selContPassCats.length = 27 := by
  simp [selContPassCats]

/-- Categories charged by the exiting pass (head, exit branch taken, exit
tail). -/
def selExitPassCats : List Category :=
  selSeg1Cats ++
    [ .branch
    , .arithmetic, .arithmetic, .memoryRead, .arithmetic, .arithmetic
    , .arithmetic ]

@[simp] theorem selExitPassCats_length : selExitPassCats.length = 29 := by
  simp [selExitPassCats]

/-- Categories charged by the exhaustion tail. -/
def selExhaustCats : List Category :=
  [ .registerWrite, .registerWrite, .branch ]

@[simp] theorem selExhaustCats_length : selExhaustCats.length = 3 := rfl

/-- The chunk rank the fold consumes at cursor `j` (the decoded fringe
chunk-table entry at the fold's routing read). -/
def selChunkRankAt (store : ReadStore) (R c : Nat) (word : List Bool)
    (j : Nat) : Nat :=
  bpChunkRankOfEntry c false (bpWordChunkSliceLen c word.length j)
    (((store.readWord? R
        (bpFringeChunkSlot c (bpFringeWindowChunkValue c word j)
          (bpWordChunkSliceLen c word.length j)
          (bpWordChunkSliceLen c word.length j))).map
      SuccinctSpace.bitsToNatLE).getD 0)

/--
Derived category log of the whole fold block run: mirrors the fold's
early-exit recursion (continue passes, then either the exiting pass or the
exhaustion tail).  A FUNCTION of the store and the loop inputs — never
asserted; the simulation theorem charges exactly this log.
-/
def selectFoldCats (store : ReadStore) (R c : Nat) (word : List Bool) :
    Nat -> Nat -> Nat -> List Category
  | _j, 0, _k => selExhaustCats
  | j, count + 1, k =>
      if k < selChunkRankAt store R c word j then selExitPassCats
      else
        selContPassCats ++
          selectFoldCats store R c word (j + 1) count
            (k - selChunkRankAt store R c word j)

/-- Derived step bound for the fold block: at most `27` steps per
available pass plus the `3`-step exhaustion tail (the exiting pass's `29`
steps are covered by the first pass's `27 + 3` budget). -/
theorem selectFoldCats_length_le (store : ReadStore) (R c : Nat)
    (word : List Bool) :
    forall count j k,
      (selectFoldCats store R c word j count k).length <=
        27 * count + 3 := by
  intro count
  induction count with
  | zero =>
      intro j k
      simp [selectFoldCats]
  | succ count ih =>
      intro j k
      show (if k < selChunkRankAt store R c word j then selExitPassCats
        else selContPassCats ++
          selectFoldCats store R c word (j + 1) count
            (k - selChunkRankAt store R c word j)).length <= _
      by_cases hcase : k < selChunkRankAt store R c word j
      · rw [if_pos hcase]
        simp
        omega
      · rw [if_neg hcase]
        rw [List.length_append]
        have := ih (j + 1) (k - selChunkRankAt store R c word j)
        simp at this ⊢
        omega

/-! ## Hosting bundle -/

/-- Peel the block's hosting fact into per-segment hosting facts and
per-branch fetch facts (all bases literal offsets from `LB`). -/
theorem selectFoldBlock_hosting {program : E1Machine.Program}
    {LB R S c : Nat}
    (hhost : HostedAt program LB (selectFoldBlock LB R S c)) :
    HostedAt program LB (selSeg1 R c) ∧
    program[LB + 22]? = some (.brNZ sA (LB + 30)) ∧
    HostedAt program (LB + 23) selSegCont ∧
    program[LB + 26]? = some (.brNZ sK LB) ∧
    HostedAt program (LB + 27) selSegExhaust ∧
    program[LB + 29]? = some (.brNZ sA (LB + 36)) ∧
    HostedAt program (LB + 30) (selSegExit S c) := by
  have hR1 := HostedAt.append_right hhost
  have hR2 := HostedAt.append_right hR1
  have hR3 := HostedAt.append_right hR2
  have hR4 := HostedAt.append_right hR3
  have hR5 := HostedAt.append_right hR4
  have hR6 := HostedAt.append_right hR5
  exact
    ⟨ HostedAt.append_left hhost
    , (HostedAt.append_left hR1).head
    , HostedAt.append_left hR2
    , (HostedAt.append_left hR3).head
    , HostedAt.append_left hR4
    , (HostedAt.append_left hR5).head
    , hR6 ⟩

/-! ## Straightness certificates -/

theorem selSeg1_straight (R c : Nat) :
    forall instr, instr ∈ selSeg1 R c -> instr.isStraight = true := by
  intro instr hi
  simp only [selSeg1, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl <;> rfl

theorem selSegCont_straight :
    forall instr, instr ∈ selSegCont -> instr.isStraight = true := by
  intro instr hi
  simp only [selSegCont, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl <;> rfl

theorem selSegExhaust_straight :
    forall instr, instr ∈ selSegExhaust -> instr.isStraight = true := by
  intro instr hi
  simp only [selSegExhaust, List.mem_cons, List.not_mem_nil,
    or_false] at hi
  rcases hi with rfl | rfl <;> rfl

theorem selSegExit_straight (S c : Nat) :
    forall instr, instr ∈ selSegExit S c -> instr.isStraight = true := by
  intro instr hi
  simp only [selSegExit, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-! ## Width certificate (REQ-E1-02 consumption for this block) -/

/--
Constructor-exhaustive width certificate for the select fold block: every
encoded field — register identifiers (bank `9..27`), table segments
`R`/`S`, the immediates `0`/`1`, the multiplier/divisor constants
`2^c`/`c+1`/`2*c+2`/`2` (all positive outright), and the branch targets
`LB`/`LB+30`/`LB+36` — fits the modeled width `w`.
-/
theorem selectFoldBlock_fits {w LB R S c : Nat}
    (hreg : 28 <= 2 ^ w) (hR : R < 2 ^ w) (hS : S < 2 ^ w)
    (hpow : 2 ^ c < 2 ^ w) (hlin : 2 * c + 2 < 2 ^ w)
    (hLB : LB + 36 < 2 ^ w) :
    forall instr, instr ∈ selectFoldBlock LB R S c ->
      instr.FieldsFit w := by
  have hppos : 0 < 2 ^ c := Nat.pow_pos (by omega)
  intro instr hmem
  simp only [selectFoldBlock, selSeg1, selSegCont, selSegExhaust,
    selSegExit, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, or_assoc] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Instr.FieldsFit, sVal, sOcc, sLen, sR, sK, sT, sV, sSlot,
      sA, sB, sOne, sC, sJC] <;>
    omega

/-! ## Simulation -/

/-- Symbolic machine-state evaluation: the shared `straight_eval` core
instantiated with this block's segments and register-bank numerals. -/
local macro "regs_eval" : tactic =>
  `(tactic| straight_eval [selSeg1, selSegCont, selSegExhaust, selSegExit,
      sVal, sOcc, sLen, sR, sK, sT, sV, sSlot, sA, sB, sOne, sC, sJC])

/-- Destination-register evaluation for preservation side conditions. -/
local macro "writes_eval" : tactic =>
  `(tactic| straight_writes [sVal, sOcc, sLen, sR, sK, sT, sV, sSlot,
      sA, sB, sOne, sC, sJC])

/--
In-word select fold simulation: from the loop entry with the fold state in
the frozen bank (remaining word, cursor, occurrence, counter `>= 1`, word
length, pinned `1`/`c`), any program hosting the block runs — with exact
fuel — to the block exit at `LB + 36` with

* receipts POSITIONALLY EQUAL to the fold's trace,
* the fold's optional value under `decodePacket` in `sVal`,
* the derived category log `selectFoldCats` (length `<= 27*count + 3`),
* every register outside the fold bank (`r <= 8`, `10`, `11`, `13..16`,
  `24..26`, `28 <=`) preserved.

The early exit is decided by the machine's own `natLt`/`brNZ` on the
decoded chunk rank — no meta-level guard.
-/
theorem selectFoldBlock_runsTo
    (store : ReadStore) {program : E1Machine.Program} {LB R S c : Nat}
    (hhost : HostedAt program LB (selectFoldBlock LB R S c))
    (word : List Bool) :
    forall (count : Nat), 0 < count ->
    forall (j k : Nat) (regs0 : RegFile),
      regs0 sOne = 1 -> regs0 sC = c -> regs0 sLen = word.length ->
      regs0 sR = SuccinctSpace.bitsToNatLE word / 2 ^ (j * c) ->
      regs0 sJC = j * c -> regs0 sOcc = k -> regs0 sK = count ->
      ∃ regsF : RegFile,
        RunsTo store program ⟨regs0, LB, false⟩ ⟨regsF, LB + 36, false⟩
          (bpChunkedWordSelectTraceFromWithStore store R S c false word
            j count k).trace
          (selectFoldCats store R c word j count k) ∧
        E1Query.decodePacket (regsF sVal) =
          (bpChunkedWordSelectTraceFromWithStore store R S c false word
            j count k).value ∧
        (forall r,
          r <= 8 ∨ r = 10 ∨ r = 11 ∨ r = 13 ∨ r = 14 ∨ r = 15 ∨
            r = 16 ∨ r = 24 ∨ r = 25 ∨ r = 26 ∨ 28 <= r ->
          regsF r = regs0 r) := by
  obtain ⟨hS1, hbrExit, hCont, hbrBack, hExhaust, hbrDone, hExit⟩ :=
    selectFoldBlock_hosting hhost
  intro count
  induction count with
  | zero =>
      intro hpos
      omega
  | succ n ih =>
      intro _hpos j k regs0 hOne hC hLen hR hJC hOcc hK
      -- loop head
      have hrun1 := RunsTo.straight store (selSeg1 R c)
        (selSeg1_straight R c) LB hS1 regs0
      obtain ⟨regs1, hregs1⟩ :
          ∃ x, straightRegs store (selSeg1 R c) regs0 = x := ⟨_, rfl⟩
      rw [hregs1] at hrun1
      have h1T : regs1 sT = bpWordChunkSliceLen c word.length j := by
        rw [<- hregs1]
        regs_eval <;> simp [hLen, hJC, hC, bpWordChunkSliceLen_eq_sub]
      have h1V : regs1 sV = bpFringeWindowChunkValue c word j := by
        rw [<- hregs1]
        regs_eval <;>
          simp [hR, bpFringeWindowChunkValue_eq_div_mod,
            nat_mod_eq_sub_div_mul]
      have h1R : regs1 sR =
          SuccinctSpace.bitsToNatLE word / 2 ^ ((j + 1) * c) := by
        rw [<- hregs1]
        regs_eval <;> simp [hR]
        exact div_pow_chunk_succ _ _ _
      have h1B : regs1 sB = selChunkRankAt store R c word j := by
        rw [<- hregs1]
        regs_eval <;>
          simp [hLen, hJC, hC, hR, hOne, selChunkRankAt,
            bpChunkRankOfEntry_false_eq, decodeRead_pred_eq_map_getD,
            bpFringeChunkSlot, bpWordChunkSliceLen_eq_sub,
            bpFringeWindowChunkValue_eq_div_mod, nat_mod_eq_sub_div_mul]
      have h1A : regs1 sA =
          if k < selChunkRankAt store R c word j then 1 else 0 := by
        rw [<- hregs1]
        regs_eval <;>
          simp [hLen, hJC, hC, hR, hOne, hOcc, selChunkRankAt,
            bpChunkRankOfEntry_false_eq, decodeRead_pred_eq_map_getD,
            bpFringeChunkSlot, bpWordChunkSliceLen_eq_sub,
            bpFringeWindowChunkValue_eq_div_mod, nat_mod_eq_sub_div_mul]
      have h1pass : forall r,
          r ≠ 22 -> r ≠ 23 -> r ≠ 19 -> r ≠ 20 -> r ≠ 21 -> r ≠ 17 ->
          regs1 r = regs0 r := by
        intro r hA hB hT hV hSlot hRr
        rw [<- hregs1]
        apply straightRegs_preserves
        intro i hi
        simp only [selSeg1, List.mem_cons, List.not_mem_nil,
          or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          | rfl | rfl | rfl | rfl <;> writes_eval <;> omega
      have hreads1 : straightReads store (selSeg1 R c) regs0 =
          [ TraceEvent.readWord R
              (bpFringeChunkSlot c (bpFringeWindowChunkValue c word j)
                (bpWordChunkSliceLen c word.length j)
                (bpWordChunkSliceLen c word.length j))
              (store.readWord? R
                (bpFringeChunkSlot c
                  (bpFringeWindowChunkValue c word j)
                  (bpWordChunkSliceLen c word.length j)
                  (bpWordChunkSliceLen c word.length j))) ] := by
        regs_eval <;>
          simp [hLen, hJC, hC, hR, bpFringeChunkSlot,
            bpWordChunkSliceLen_eq_sub,
            bpFringeWindowChunkValue_eq_div_mod, nat_mod_eq_sub_div_mul]
      -- named pre-branch register facts
      have h1One : regs1 sOne = 1 := by
        rw [h1pass sOne (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide)]
        exact hOne
      have h1C : regs1 sC = c := by
        rw [h1pass sC (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide)]
        exact hC
      have h1Len : regs1 sLen = word.length := by
        rw [h1pass sLen (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide)]
        exact hLen
      have h1JC : regs1 sJC = j * c := by
        rw [h1pass sJC (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide)]
        exact hJC
      have h1Occ : regs1 sOcc = k := by
        rw [h1pass sOcc (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide)]
        exact hOcc
      have h1K : regs1 sK = n + 1 := by
        rw [h1pass sK (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide)]
        exact hK
      by_cases hcase : k < selChunkRankAt store R c word j
      · -- EXIT PASS: branch taken, select-table read, packet assembly
        have h1A1 : regs1 sA = 1 := by rw [h1A, if_pos hcase]
        have hbr := RunsTo.brNZ_taken (store := store)
          (s := ⟨regs1, LB + 22, false⟩) rfl hbrExit (by
            show regs1 sA ≠ 0
            rw [h1A1]
            omega)
        have hrun2 := RunsTo.straight store (selSegExit S c)
          (selSegExit_straight S c) (LB + 30) hExit regs1
        obtain ⟨regs2, hregs2⟩ :
            ∃ x, straightRegs store (selSegExit S c) regs1 = x := ⟨_, rfl⟩
        rw [hregs2] at hrun2
        have hreads2 : straightReads store (selSegExit S c) regs1 =
            [ TraceEvent.readWord S
                (bpChunkSelectSlot c (bpFringeWindowChunkValue c word j)
                  k)
                (store.readWord? S
                  (bpChunkSelectSlot c
                    (bpFringeWindowChunkValue c word j) k)) ] := by
          regs_eval <;> simp [h1V, h1Occ, bpChunkSelectSlot]
        have h2Val : regs2 sVal =
            ((store.readWord? S
                (bpChunkSelectSlot c (bpFringeWindowChunkValue c word j)
                  k)).map SuccinctSpace.bitsToNatLE).getD 0 +
              j * c + 1 := by
          rw [<- hregs2]
          regs_eval <;>
            simp [h1V, h1Occ, h1JC, h1One, decodeRead_pred_eq_map_getD,
              bpChunkSelectSlot]
        have h2pres : forall r, r ≠ 22 -> r ≠ 9 ->
            regs2 r = regs1 r := by
          intro r hA hVal
          rw [<- hregs2]
          apply straightRegs_preserves
          intro i hi
          simp only [selSegExit, List.mem_cons, List.not_mem_nil,
            or_false] at hi
          rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
            writes_eval <;> omega
        have hall := (hrun1.trans hbr).trans hrun2
        rw [hreads1, hreads2] at hall
        refine ⟨regs2, ?_, ?_, ?_⟩
        · have htrace :
              (bpChunkedWordSelectTraceFromWithStore store R S c false
                word j (n + 1) k).trace =
              [ TraceEvent.readWord R
                  (bpFringeChunkSlot c
                    (bpFringeWindowChunkValue c word j)
                    (bpWordChunkSliceLen c word.length j)
                    (bpWordChunkSliceLen c word.length j))
                  (store.readWord? R
                    (bpFringeChunkSlot c
                      (bpFringeWindowChunkValue c word j)
                      (bpWordChunkSliceLen c word.length j)
                      (bpWordChunkSliceLen c word.length j))) ] ++
              ([] ++
                [ TraceEvent.readWord S
                    (bpChunkSelectSlot c
                      (bpFringeWindowChunkValue c word j) k)
                    (store.readWord? S
                      (bpChunkSelectSlot c
                        (bpFringeWindowChunkValue c word j) k)) ]) := by
            have hcase' := hcase
            unfold selChunkRankAt at hcase'
            simp [bpChunkedWordSelectTraceFromWithStore,
              TraceResult.bind, TraceResult.map, TraceResult.pure,
              bpChunkReadTraceResult, hcase']
          have hcats : selectFoldCats store R c word j (n + 1) k =
              (selSeg1 R c).map Instr.category ++
                ([Category.branch] ++
                  (selSegExit S c).map Instr.category) := by
            show (if k < selChunkRankAt store R c word j then
                selExitPassCats
              else _) = _
            rw [if_pos hcase]
            simp [selExitPassCats, selSeg1Cats, selSeg1, selSegExit,
              Instr.category]
          rw [htrace, hcats]
          exact hall
        · have hvalue :
              (bpChunkedWordSelectTraceFromWithStore store R S c false
                word j (n + 1) k).value =
              some (j * c +
                ((store.readWord? S
                    (bpChunkSelectSlot c
                      (bpFringeWindowChunkValue c word j) k)).map
                  SuccinctSpace.bitsToNatLE).getD 0) := by
            have hcase' := hcase
            unfold selChunkRankAt at hcase'
            simp [bpChunkedWordSelectTraceFromWithStore,
              TraceResult.bind, TraceResult.map, TraceResult.pure,
              bpChunkReadTraceResult, hcase']
          rw [hvalue, h2Val]
          generalize ((store.readWord? S
              (bpChunkSelectSlot c (bpFringeWindowChunkValue c word j)
                k)).map SuccinctSpace.bitsToNatLE).getD 0 = X
          rw [show X + j * c + 1 = j * c + X + 1 from by omega]
          simp
        · intro r hr
          rw [h2pres r (by omega) (by omega)]
          rw [h1pass r (by omega) (by omega) (by omega) (by omega)
            (by omega) (by omega)]
      · -- CONTINUE PASS: branch not taken, consume, advance, decrement
        have h1A0 : regs1 sA = 0 := by rw [h1A, if_neg hcase]
        have hbr := RunsTo.brNZ_not_taken (store := store)
          (s := ⟨regs1, LB + 22, false⟩) rfl hbrExit h1A0
        have hrun2 := RunsTo.straight store selSegCont
          selSegCont_straight (LB + 23) hCont regs1
        obtain ⟨regs2, hregs2⟩ :
            ∃ x, straightRegs store selSegCont regs1 = x := ⟨_, rfl⟩
        rw [hregs2] at hrun2
        have hreads2 : straightReads store selSegCont regs1 = [] := by
          regs_eval
        rw [hreads2] at hrun2
        have h2Occ : regs2 sOcc =
            k - selChunkRankAt store R c word j := by
          rw [<- hregs2]
          regs_eval <;> simp [h1Occ, h1B]
        have h2JC : regs2 sJC = (j + 1) * c := by
          rw [<- hregs2]
          regs_eval <;> simp [h1JC, h1C]
          rw [Nat.succ_mul]
        have h2K : regs2 sK = n := by
          rw [<- hregs2]
          regs_eval <;> simp [h1K, h1One]
        have h2pass : forall r,
            r ≠ 12 -> r ≠ 27 -> r ≠ 18 -> regs2 r = regs1 r := by
          intro r hO hJ hKr
          rw [<- hregs2]
          apply straightRegs_preserves
          intro i hi
          simp only [selSegCont, List.mem_cons, List.not_mem_nil,
            or_false] at hi
          rcases hi with rfl | rfl | rfl <;> writes_eval <;> omega
        have h2One : regs2 sOne = 1 := by
          rw [h2pass sOne (by decide) (by decide) (by decide)]
          exact h1One
        have h2C : regs2 sC = c := by
          rw [h2pass sC (by decide) (by decide) (by decide)]
          exact h1C
        have h2Len : regs2 sLen = word.length := by
          rw [h2pass sLen (by decide) (by decide) (by decide)]
          exact h1Len
        have h2R : regs2 sR =
            SuccinctSpace.bitsToNatLE word / 2 ^ ((j + 1) * c) := by
          rw [h2pass sR (by decide) (by decide) (by decide)]
          exact h1R
        -- fold branch facts (continue)
        have hfoldTrace :
            (bpChunkedWordSelectTraceFromWithStore store R S c false
              word j (n + 1) k).trace =
            [ TraceEvent.readWord R
                (bpFringeChunkSlot c (bpFringeWindowChunkValue c word j)
                  (bpWordChunkSliceLen c word.length j)
                  (bpWordChunkSliceLen c word.length j))
                (store.readWord? R
                  (bpFringeChunkSlot c
                    (bpFringeWindowChunkValue c word j)
                    (bpWordChunkSliceLen c word.length j)
                    (bpWordChunkSliceLen c word.length j))) ] ++
            (bpChunkedWordSelectTraceFromWithStore store R S c false
              word (j + 1) n
              (k - selChunkRankAt store R c word j)).trace := by
          have hcase' := hcase
          unfold selChunkRankAt at hcase'
          simp [bpChunkedWordSelectTraceFromWithStore,
            TraceResult.bind, bpChunkReadTraceResult, hcase',
            selChunkRankAt]
        have hfoldValue :
            (bpChunkedWordSelectTraceFromWithStore store R S c false
              word j (n + 1) k).value =
            (bpChunkedWordSelectTraceFromWithStore store R S c false
              word (j + 1) n
              (k - selChunkRankAt store R c word j)).value := by
          have hcase' := hcase
          unfold selChunkRankAt at hcase'
          simp [bpChunkedWordSelectTraceFromWithStore,
            TraceResult.bind, bpChunkReadTraceResult, hcase',
            selChunkRankAt]
        have hfoldCats : selectFoldCats store R c word j (n + 1) k =
            selContPassCats ++
              selectFoldCats store R c word (j + 1) n
                (k - selChunkRankAt store R c word j) := by
          show (if k < selChunkRankAt store R c word j then _ else _) = _
          rw [if_neg hcase]
        by_cases hn : n = 0
        · -- EXHAUSTION: back edge not taken, `pure none` tail
          subst hn
          have hbr2 := RunsTo.brNZ_not_taken (store := store)
            (s := ⟨regs2, LB + 26, false⟩) rfl hbrBack (by simpa using h2K)
          have hrun3 := RunsTo.straight store selSegExhaust
            selSegExhaust_straight (LB + 27) hExhaust regs2
          obtain ⟨regs3, hregs3⟩ :
              ∃ x, straightRegs store selSegExhaust regs2 = x := ⟨_, rfl⟩
          rw [hregs3] at hrun3
          have hreads3 : straightReads store selSegExhaust regs2 = [] := by
            regs_eval
          rw [hreads3] at hrun3
          have h3Val : regs3 sVal = 0 := by
            rw [<- hregs3]
            regs_eval
          have h3A : regs3 sA = 1 := by
            rw [<- hregs3]
            regs_eval
          have h3pres : forall r, r ≠ 9 -> r ≠ 22 ->
              regs3 r = regs2 r := by
            intro r hV hA
            rw [<- hregs3]
            apply straightRegs_preserves
            intro i hi
            simp only [selSegExhaust, List.mem_cons, List.not_mem_nil,
              or_false] at hi
            rcases hi with rfl | rfl <;> writes_eval <;> omega
          have hbr3 := RunsTo.brNZ_taken (store := store)
            (s := ⟨regs3, LB + 29, false⟩) rfl hbrDone (by
              show regs3 sA ≠ 0
              rw [h3A]
              omega)
          have hall := ((((hrun1.trans hbr).trans hrun2).trans
            hbr2).trans hrun3).trans hbr3
          rw [hreads1] at hall
          refine ⟨regs3, ?_, ?_, ?_⟩
          · rw [hfoldTrace, hfoldCats]
            show RunsTo store program _ _
              (_ ++ (bpChunkedWordSelectTraceFromWithStore store R S c
                false word (j + 1) 0 _).trace) _
            have hznil :
                (bpChunkedWordSelectTraceFromWithStore store R S c
                  false word (j + 1) 0
                  (k - selChunkRankAt store R c word j)).trace = [] := rfl
            rw [hznil]
            have hcats :
                selContPassCats ++
                  selectFoldCats store R c word (j + 1) 0
                    (k - selChunkRankAt store R c word j) =
                (selSeg1 R c).map Instr.category ++
                  ([Category.branch] ++
                    (selSegCont.map Instr.category ++
                      ([Category.branch] ++
                        (selSegExhaust.map Instr.category ++
                          [Category.branch])))) := by
              show selContPassCats ++ selExhaustCats = _
              simp [selContPassCats, selExhaustCats, selSeg1Cats,
                selSeg1, selSegCont, selSegExhaust, Instr.category]
            rw [hcats]
            simpa using hall
          · rw [hfoldValue]
            have hzval :
                (bpChunkedWordSelectTraceFromWithStore store R S c
                  false word (j + 1) 0
                  (k - selChunkRankAt store R c word j)).value =
                none := rfl
            rw [hzval, h3Val]
            rfl
          · intro r hr
            rw [h3pres r (by omega) (by omega),
              h2pass r (by omega) (by omega) (by omega),
              h1pass r (by omega) (by omega) (by omega) (by omega)
                (by omega) (by omega)]
        · -- LOOP: back edge taken, inductive hypothesis at `n`
          have hbr2 := RunsTo.brNZ_taken (store := store)
            (s := ⟨regs2, LB + 26, false⟩) rfl hbrBack (by
              show regs2 sK ≠ 0
              rw [h2K]
              exact hn)
          obtain ⟨regsF, hrest, hvalF, hpresF⟩ :=
            ih (by omega) (j + 1) (k - selChunkRankAt store R c word j)
              regs2 h2One h2C h2Len h2R h2JC h2Occ h2K
          have hall := (((hrun1.trans hbr).trans hrun2).trans
            hbr2).trans hrest
          rw [hreads1] at hall
          refine ⟨regsF, ?_, ?_, ?_⟩
          · rw [hfoldTrace, hfoldCats]
            have hcats :
                selContPassCats ++
                  selectFoldCats store R c word (j + 1) n
                    (k - selChunkRankAt store R c word j) =
                (selSeg1 R c).map Instr.category ++
                  ([Category.branch] ++
                    (selSegCont.map Instr.category ++
                      ([Category.branch] ++
                        selectFoldCats store R c word (j + 1) n
                          (k - selChunkRankAt store R c word j)))) := by
              simp [selContPassCats, selSeg1Cats, selSeg1, selSegCont,
                Instr.category]
            rw [hcats]
            simpa using hall
          · rw [hfoldValue]
            exact hvalF
          · intro r hr
            rw [hpresF r hr,
              h2pass r (by omega) (by omega) (by omega),
              h1pass r (by omega) (by omega) (by omega) (by omega)
                (by omega) (by omega)]

end E1SelectBlock
end WordRAM
end RMQ
