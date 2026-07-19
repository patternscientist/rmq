import RMQ.Core.WordRAM.E1FringeBridge
import RMQ.Core.WordRAM.E1RankAtBlock

/-!
# E1 amended machine: the charged fringe chunk-fold block (M3d-1b)

The machine realization of `bpFringeChunkFoldComputationFrom`
(`ChargedFringeTrace.lean:32`), the charged chunked fringe fold that BOTH
arms of the close/LCA dispatcher run after B6.

Two things make this block different from every earlier fold block:

* the fold's window is the FOUR payload words of `localBPWindowBits`, so
  the machine carries it in four registers under the fixed-stride Horner
  representation `windowRegsValue` (`E1FringeBridge.lean`), advancing it
  each pass by the constant-only four-register shift
  `windowRegsValue_shift`;
* the loop body is NOT branch-free.  `bpFringeMergeCand`
  (`ChargedFringeChunks.lean:892`) is a three-way match gated by
  `startOff < endOff`, and a branch-free encoding would need `take * X`
  with a RUNTIME `0/1` multiplier, which the ISA deliberately excludes
  (`mulConst` takes an encoded constant only).  So the merge segment
  branches, and the per-pass simulation is a FOUR-WAY case analysis.

Because the merge branches, the per-pass category log is NOT a constant
list: it is a function of the route-side branch conditions
(`fringeMergeCatsAt`), following the `selectFoldCats` / `denseLegCats`
precedent.  No per-pass numeral is ever asserted.

Layout at loop base `LB` (66-instruction body, back edge at `LB + 66`):

| range | segment | contents |
| --- | --- | --- |
| `LB+0 .. LB+31` | `fringePrefix` | chunk value, start/end offsets, slot, read+decode, candidate, accumulator advance |
| `LB+32 .. LB+44` | `fringeMerge` | the four-arm keep-left merge |
| `LB+45 .. LB+63` | `fringeShift` | the four-register constant-stride window advance |
| `LB+64 .. LB+65` | `fringeAdvance` | chunk cursor and loop counter |
| `LB+66` | back edge | `brNZ fCnt LB` |

The best candidate is carried option-shifted across two registers
(`fBV = value + 1`, `0 = none`; `fBP = position`), the same convention
`decodeRead` uses for reads, so the option test is one register
comparison against zero.
-/

namespace RMQ
namespace WordRAM
namespace E1FringeFoldBlock

open E1Machine
open RMQ.SuccinctClose

/-! ## Register bank (fringe leg, `40 .. 62`)

Fresh bank above the skeleton (`0..7`), component (`8..27`) and select
extension (`28..39`) banks.  The LCA leg runs third, so `28..39` is dead
by then; a fresh bank is still preferred so the glue never reasons about
liveness across legs.  Recorded as a design decision.
-/

/-- Pinned constant `1`. -/
abbrev fOne : Nat := 40
/-- Pinned constant `c` (the chunk width). -/
abbrev fC : Nat := 41
/-- Window register 0 (least significant). -/
abbrev fW0 : Nat := 42
/-- Window register 1. -/
abbrev fW1 : Nat := 43
/-- Window register 2. -/
abbrev fW2 : Nat := 44
/-- Window register 3 (most significant). -/
abbrev fW3 : Nat := 45
/-- Fold accumulator (`st.1`). -/
abbrev fAcc : Nat := 46
/-- Best candidate value, option-shifted (`0 = none`). -/
abbrev fBV : Nat := 47
/-- Best candidate position. -/
abbrev fBP : Nat := 48
/-- Chunk cursor `j * c`. -/
abbrev fJC : Nat := 49
/-- Relative range low endpoint. -/
abbrev fLo : Nat := 50
/-- Relative range high endpoint (inclusive). -/
abbrev fHi : Nat := 51
/-- Remaining chunk visits. -/
abbrev fCnt : Nat := 52
/-- Window chunk value at the current chunk. -/
abbrev fV : Nat := 53
/-- Chunk start offset. -/
abbrev fA : Nat := 54
/-- Chunk end offset (exclusive). -/
abbrev fB : Nat := 55
/-- Chunk-table slot. -/
abbrev fSlot : Nat := 56
/-- Decoded chunk-table entry (`decodeRead - 1`). -/
abbrev fE : Nat := 57
/-- Candidate value. -/
abbrev fCV : Nat := 58
/-- Candidate position. -/
abbrev fCP : Nat := 59
/-- Scratch. -/
abbrev fT : Nat := 60
/-- Scratch. -/
abbrev fU : Nat := 61
/-- Scratch. -/
abbrev fX : Nat := 62

/-! ## Option-shifted best candidate -/

/--
The two-register representation of the fold's `Option (Nat × Nat)` best
candidate: `bv = 0` is `none`, `bv = v + 1` is `some (v, bp)`.
-/
def bestOfRegs (bv bp : Nat) : Option (Nat × Nat) :=
  if bv = 0 then none else some (bv - 1, bp)

@[simp] theorem bestOfRegs_zero (bp : Nat) : bestOfRegs 0 bp = none := rfl

@[simp] theorem bestOfRegs_succ (v bp : Nat) :
    bestOfRegs (v + 1) bp = some (v, bp) := by
  simp [bestOfRegs]

/-- The machine's shifted comparison `cv + 1 < bv` is the fold's
`cand.1 < best.1` whenever the best register is occupied. -/
theorem bestOfRegs_merge_some {bv : Nat} (hbv : bv ≠ 0) (bp cv cp : Nat) :
    bpFringeMergeCand (bestOfRegs bv bp) (some (cv, cp)) =
      if cv + 1 < bv then bestOfRegs (cv + 1) cp else bestOfRegs bv bp := by
  unfold bestOfRegs
  rw [if_neg hbv]
  show
    (if cv < bv - 1 then some (cv, cp) else some (bv - 1, bp)) =
      if cv + 1 < bv then _ else _
  by_cases hlt : cv + 1 < bv
  · rw [if_pos hlt, if_pos (by omega), if_neg (by omega)]
    simp
  · rw [if_neg hlt, if_neg (by omega)]

/-! ## Block segments -/

/--
Straight prefix of one fold pass (`LB+0 .. LB+31`): chunk value, chunk
start/end offsets in truncated-subtraction form, chunk-table slot, the
one charged read with its bounded decode, the candidate value/position
(which read the OLD accumulator), then the accumulator advance.
-/
def fringePrefix (S c : Nat) : List Instr :=
  [ -- chunk value `W0 % 2 ^ c`
    .divConst fT fW0 (2 ^ c)
  , .mulConst fT fT (2 ^ c)
  , .sub fV fW0 fT
    -- start offset `c - (c - (relLo - j * c))`
  , .sub fT fLo fJC
  , .const fA c
  , .sub fU fA fT
  , .sub fA fA fU
    -- end offset `((relHi+1) - ((relHi+1) - (j*c + c))) - j*c`
  , .add fT fHi fOne
  , .const fU c
  , .add fU fJC fU
  , .sub fX fT fU
  , .sub fB fT fX
  , .sub fB fB fJC
    -- slot `(v * (c+1) + a) * (c+1) + b`
  , .mulConst fSlot fV (c + 1)
  , .add fSlot fSlot fA
  , .mulConst fSlot fSlot (c + 1)
  , .add fSlot fSlot fB
    -- the one charged read, decoded
  , .readMem fE S fSlot
  , .sub fE fE fOne
    -- candidate value `acc + (e / (c+1)) % (2c+2) - c`
  , .divConst fT fE (c + 1)
  , .divConst fU fT (2 * c + 2)
  , .mulConst fU fU (2 * c + 2)
  , .sub fT fT fU
  , .add fCV fAcc fT
  , .sub fCV fCV fC
    -- candidate position `j*c + e % (c+1)`
  , .divConst fT fE (c + 1)
  , .mulConst fT fT (c + 1)
  , .sub fT fE fT
  , .add fCP fJC fT
    -- accumulator advance `acc + e / ((c+1)*(2c+2)) - c`
  , .divConst fT fE ((c + 1) * (2 * c + 2))
  , .add fAcc fAcc fT
  , .sub fAcc fAcc fC ]

@[simp] theorem fringePrefix_length (S c : Nat) :
    (fringePrefix S c).length = 32 := rfl

/--
The branching keep-left merge (`LB+32 .. LB+44`), four arms:

* `¬ (a < b)`: no candidate, best unchanged (3 instructions);
* `a < b`, best `none`: best := candidate (6);
* `a < b`, best `some`, candidate strictly better: best := candidate (8);
* `a < b`, best `some`, candidate not better: unchanged (7).
-/
def fringeMerge (LB : Nat) : List Instr :=
  [ .natLt fT fA fB            -- LB+32
  , .brNZ fT (LB + 35)         -- LB+33
  , .brNZ fOne (LB + 45)       -- LB+34
  , .brNZ fBV (LB + 39)        -- LB+35
  , .add fBV fCV fOne          -- LB+36
  , .move fBP fCP              -- LB+37
  , .brNZ fOne (LB + 45)       -- LB+38
  , .add fT fCV fOne           -- LB+39
  , .natLt fU fT fBV           -- LB+40
  , .brNZ fU (LB + 43)         -- LB+41
  , .brNZ fOne (LB + 45)       -- LB+42
  , .add fBV fCV fOne          -- LB+43
  , .move fBP fCP ]            -- LB+44

@[simp] theorem fringeMerge_length (LB : Nat) :
    (fringeMerge LB).length = 13 := rfl

/--
The four-register constant-stride window advance (`LB+45 .. LB+63`),
justified by `windowRegsValue_shift`.  Performed in order `i = 0,1,2`,
which needs no temporaries: `Wi'` depends only on `Wi` and `W(i+1)`, and
`Wi` is dead once written.
-/
def fringeShift (c L : Nat) : List Instr :=
  [ .divConst fT fW0 (2 ^ c)
  , .divConst fU fW1 (2 ^ c)
  , .mulConst fX fU (2 ^ c)
  , .sub fX fW1 fX
  , .mulConst fX fX (2 ^ (L - c))
  , .add fW0 fT fX
  , .divConst fT fW1 (2 ^ c)
  , .divConst fU fW2 (2 ^ c)
  , .mulConst fX fU (2 ^ c)
  , .sub fX fW2 fX
  , .mulConst fX fX (2 ^ (L - c))
  , .add fW1 fT fX
  , .divConst fT fW2 (2 ^ c)
  , .divConst fU fW3 (2 ^ c)
  , .mulConst fX fU (2 ^ c)
  , .sub fX fW3 fX
  , .mulConst fX fX (2 ^ (L - c))
  , .add fW2 fT fX
  , .divConst fW3 fW3 (2 ^ c) ]

@[simp] theorem fringeShift_length (c L : Nat) :
    (fringeShift c L).length = 19 := rfl

/-- Chunk cursor and loop counter (`LB+64 .. LB+65`). -/
def fringeAdvance : List Instr :=
  [ .add fJC fJC fC
  , .sub fCnt fCnt fOne ]

@[simp] theorem fringeAdvance_length : fringeAdvance.length = 2 := rfl

/-- The full 66-instruction fold body at loop base `LB`. -/
def fringeLoopBody (S c L LB : Nat) : List Instr :=
  fringePrefix S c ++ (fringeMerge LB ++ (fringeShift c L ++ fringeAdvance))

@[simp] theorem fringeLoopBody_length (S c L LB : Nat) :
    (fringeLoopBody S c L LB).length = 66 := rfl

/-! ## Frozen category logs

The merge arm is a function of the route-side branch conditions, never a
numeral: `fringeMergeCatsAt` dispatches on exactly the conditions the
accepted fold dispatches on.
-/

/-- Categories charged by the straight prefix. -/
def fringePrefixCats : List Category :=
  (fringePrefix 0 0).map Instr.category

/-- Categories charged by the window shift and the cursor advance. -/
def fringeTailCats : List Category :=
  (fringeShift 0 0).map Instr.category ++ fringeAdvance.map Instr.category

/-- Categories charged by the merge segment on the arm selected by the
fold state at chunk `j`. -/
def fringeMergeCatsAt (c : Nat) (relLo relHi j : Nat)
    (best : Option (Nat × Nat)) (candValue : Nat) : List Category :=
  if bpFringeChunkStartOff c relLo j < bpFringeChunkEndOff c relHi j then
    match best with
    | none =>
        [ .comparison, .branch, .branch, .arithmetic, .registerWrite
        , .branch ]
    | some b =>
        if candValue < b.1 then
          [ .comparison, .branch, .branch, .arithmetic, .comparison
          , .branch, .arithmetic, .registerWrite ]
        else
          [ .comparison, .branch, .branch, .arithmetic, .comparison
          , .branch, .branch ]
  else
    [ .comparison, .branch, .branch ]

/-- Category log of one full fold pass at chunk `j` from fold state
`st`, including the back edge. -/
def fringePassCats (c : Nat) (relLo relHi j : Nat)
    (st : Nat × Option (Nat × Nat)) (entry : Nat) : List Category :=
  fringePrefixCats ++
    (fringeMergeCatsAt c relLo relHi j st.2
        (st.1 + entry / (c + 1) % (2 * c + 2) - c) ++
      (fringeTailCats ++ [Category.branch]))

/-! ## Hosting bundle -/

/-- Peel the body's hosting fact into its four segments. -/
theorem fringeLoopBody_hosting {program : E1Machine.Program}
    {S c L LB : Nat}
    (hhost : HostedAt program LB (fringeLoopBody S c L LB)) :
    HostedAt program LB (fringePrefix S c) ∧
    HostedAt program (LB + 32) (fringeMerge LB) ∧
    HostedAt program (LB + 45) (fringeShift c L) ∧
    HostedAt program (LB + 64) fringeAdvance := by
  have hR1 := HostedAt.append_right hhost
  have hR2 := HostedAt.append_right hR1
  have hR3 := HostedAt.append_right hR2
  refine ⟨HostedAt.append_left hhost, ?_, ?_, ?_⟩
  · exact HostedAt.append_left hR1
  · exact HostedAt.append_left hR2
  · exact hR3

/-! ## Straightness certificates -/

theorem fringePrefix_straight (S c : Nat) :
    forall instr, instr ∈ fringePrefix S c -> instr.isStraight = true := by
  intro instr hi
  simp only [fringePrefix, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem fringeShift_straight (c L : Nat) :
    forall instr, instr ∈ fringeShift c L -> instr.isStraight = true := by
  intro instr hi
  simp only [fringeShift, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem fringeAdvance_straight :
    forall instr, instr ∈ fringeAdvance -> instr.isStraight = true := by
  intro instr hi
  simp only [fringeAdvance, List.mem_cons, List.not_mem_nil,
    or_false] at hi
  rcases hi with rfl | rfl <;> rfl

/-- The shift and the cursor advance run as one straight segment. -/
theorem fringeTail_straight (c L : Nat) :
    forall instr, instr ∈ fringeShift c L ++ fringeAdvance ->
      instr.isStraight = true := by
  intro instr hi
  rcases List.mem_append.mp hi with h | h
  · exact fringeShift_straight c L instr h
  · exact fringeAdvance_straight instr h

/-! ## Width certificate (REQ-E1-02 consumption for this block) -/

/--
Constructor-exhaustive width certificate for the fold body: every encoded
field — register identifiers (bank `40..62`), the fringe segment `S`, the
immediate `c`, the multiplier/divisor constants `2^c`, `2^(L-c)`, `c+1`,
`2*c+2`, `(c+1)*(2*c+2)`, and the four branch targets — fits the modeled
width `w`.
-/
theorem fringeLoopBody_fits {w S c L LB : Nat}
    (hreg : 63 ≤ 2 ^ w) (hS : S < 2 ^ w) (hcpos : 0 < c)
    (hc : c ≤ L)
    (hpow : 2 ^ L < 2 ^ w) (hmix : (c + 1) * (2 * c + 2) < 2 ^ w)
    (hLB : LB + 67 < 2 ^ w) :
    ∀ instr ∈ fringeLoopBody S c L LB, instr.FieldsFit w := by
  have hppos : 0 < 2 ^ c := Nat.pow_pos (by omega)
  have hqpos : 0 < 2 ^ (L - c) := Nat.pow_pos (by omega)
  have hcw : 2 ^ c ≤ 2 ^ L := Nat.pow_le_pow_right (by omega) hc
  have hqw : 2 ^ (L - c) ≤ 2 ^ L := Nat.pow_le_pow_right (by omega) (by omega)
  have hlin : 2 * c + 2 < 2 ^ w := by
    have : 2 * c + 2 ≤ (c + 1) * (2 * c + 2) := by
      have : 1 ≤ c + 1 := by omega
      calc 2 * c + 2 = 1 * (2 * c + 2) := by omega
        _ ≤ (c + 1) * (2 * c + 2) := by
            exact Nat.mul_le_mul_right _ this
    omega
  have hc1 : c + 1 < 2 ^ w := by
    have : c + 1 ≤ (c + 1) * (2 * c + 2) := by
      have h2 : 1 ≤ 2 * c + 2 := by omega
      calc c + 1 = (c + 1) * 1 := by omega
        _ ≤ (c + 1) * (2 * c + 2) := Nat.mul_le_mul_left _ h2
    omega
  obtain ⟨M, hMdef⟩ : ∃ M, M = (c + 1) * (2 * c + 2) := ⟨_, rfl⟩
  rw [<- hMdef] at hmix
  have hMpos : 0 < M := by
    rw [hMdef]
    exact Nat.mul_pos (by omega) (by omega)
  intro instr hmem
  simp only [fringeLoopBody, fringePrefix, fringeMerge, fringeShift,
    fringeAdvance, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, or_assoc] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl <;>
    simp only [Instr.FieldsFit, fOne, fC, fW0, fW1, fW2, fW3, fAcc, fBV,
      fBP, fJC, fLo, fHi, fCnt, fV, fA, fB, fSlot, fE, fCV, fCP, fT, fU,
      fX] <;>
    (try simp only [<- hMdef]) <;>
    omega

end E1FringeFoldBlock
end WordRAM
end RMQ
