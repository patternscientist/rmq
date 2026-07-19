import RMQ.Core.WordRAM.E1SameBlockArm
import RMQ.Core.WordRAM.E1RankCanonical

/-!
# E1 amended machine: the same-block close LEG at the canonical store (M3d-4)

`E1SameBlockArm.sameBlockArm_runsTo` simulates the same-block arm from a
register state in which the window base, the range registers and the rank
SEED are already established.  This module supplies the seed and closes
the composition, reaching the accepted DECODED object

    bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegmentWithStore
    (`ChargedSameBlockTrace.lean:340`)

instantiated at `rankCloseTrace :=`
`concreteBPNativeChunkedRankCloseGlobalWordTraceResult shape`.

## Why this is the canonical-STORE form

`E1RankCanonical.rankCloseBlock_runsTo_canonical` runs against
`concreteBPNativeSuccinctRMQGlobalReadStore shape` -- the one store the
whole accepted query reads -- while `sameBlockArm_runsTo` is
store-parametric.  Composing them forces the arm's `store` to be that same
canonical store, which is exactly what the whole-query composition needs.
The two legs are therefore not merely both true; they are true of a SINGLE
machine run against a SINGLE store, and the receipt below is that run's
own log.

## The seed is three instructions

`localBPSeedFromRankCloseTraceResult` (`ConcreteDirectoryRAM.lean:1530`)
is `TraceResult.map (localBPSeedFromRankFalse base) (rankCloseTrace base)`
with `base := localBPWindowBase shape blockSize close`, and
`localBPSeedFromRankFalse base r = base - 2 * r`
(`LocalBPDecoder.lean:484`).  The `map` emits no event of its own, so the
whole seed leg's receipt is the rank-close component's receipt, and the
arithmetic after it is three register instructions -- a doubling by the
CONSTANT `2`, a truncated subtraction, and a copy.  No divisor, no scan,
no table decode.
-/

namespace RMQ
namespace WordRAM
namespace E1SameBlockLeg

open E1Machine
open E1FringeFoldBlock
open E1FringeArmBlock
open E1SameBlockArm
open E1RankBlock
open RMQ.SuccinctClose
open RMQ.SuccinctFinal
open RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory

/-! ## The canonical store's window widths

The composed legs below used to carry, undischarged, the demand that the
first three window words be FULL WIDTH.  That demand is FALSE at the
canonical store, and not marginally: evaluated at the left spine of 16
nodes the three words measure `2, 0, 0` against a required `L = 6`, and 12
of that shape's 32 close positions fail.  The BP code's last bit is a
CLOSE, so the failing positions are reachable endpoints, and
`ofChunksWithSentinel` would not rescue it — its sentinel words are
`List.replicate ... []`, of length `0`.

What the store DOES guarantee is density (`WindowDense`,
`E1FringeArmBlock.lean`): a word is full width whenever the NEXT word is
nonempty.  That is enough for the Horner decode, because a short word's
weight only ever multiplies an empty tail.  This is the repair M3d-14 made
one layer down at the interior chunk store, applied to the same defect.

PADDING THE BP CODE IS NOT THE FIX and was not considered: it would reshape
the accepted artifact to spare a proof, and would ripple into space
accounting and the frozen constants.
-/

/-- The canonical BP store's word at index `j` is exactly the code's `j`-th
`wordSize`-slice.  Unconditional: past the end both sides are empty. -/
theorem canonicalReadBits_eq (shape : Cartesian.CartesianShape) (j : Nat) :
    readBits (concreteBPNativeSuccinctRMQGlobalReadStore shape) j =
      (shape.bpCode.drop
          (j * SuccinctRank.machineWordBits shape.bpCode.length)).take
        (SuccinctRank.machineWordBits shape.bpCode.length) := by
  unfold readBits
  rw [concreteBPNativeSuccinctRMQGlobalReadStore_bpCode shape j,
    List.getElem?_toArray]
  rcases Nat.lt_or_ge
      (j * SuccinctRank.machineWordBits shape.bpCode.length)
      shape.bpCode.length with hlt | hge
  · obtain ⟨word, hword⟩ :=
      SuccinctSpace.chunkPayloadWords_get?_some_of_mul_lt
        (SuccinctRank.machineWordBits_pos shape.bpCode.length) hlt
    rw [hword]
    exact SuccinctSpace.chunkPayloadWords_get?_eq_take_drop hword
  · rw [SuccinctSpace.chunkPayloadWords_get?_none_of_length_le_mul hge]
    rw [List.drop_eq_nil_of_le hge]
    rfl

/-- Hence the word's length is the truncated slice width. -/
theorem canonicalReadBits_length (shape : Cartesian.CartesianShape)
    (j : Nat) :
    (readBits (concreteBPNativeSuccinctRMQGlobalReadStore shape) j).length =
      Nat.min (SuccinctRank.machineWordBits shape.bpCode.length)
        (shape.bpCode.length -
          j * SuccinctRank.machineWordBits shape.bpCode.length) := by
  rw [canonicalReadBits_eq shape j, List.length_take, List.length_drop]

/--
THE DISCHARGE.  The canonical store's window is DENSE at every base, so
none of the nine full-width premises the composed legs used to carry is
needed.  A nonempty successor word forces its predecessor to be full,
because `chunkPayloadWords` truncates only the FINAL word.
-/
theorem canonicalWindowDense (shape : Cartesian.CartesianShape)
    (base : Nat) :
    WindowDense (concreteBPNativeSuccinctRMQGlobalReadStore shape) base
      (SuccinctRank.machineWordBits shape.bpCode.length) := by
  have step : ∀ j : Nat,
      readBits (concreteBPNativeSuccinctRMQGlobalReadStore shape) (j + 1) ≠
          [] ->
        (readBits (concreteBPNativeSuccinctRMQGlobalReadStore shape)
            j).length =
          SuccinctRank.machineWordBits shape.bpCode.length := by
    intro j hne
    have hlen1 :
        (readBits (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          (j + 1)).length ≠ 0 := by
      intro h
      exact hne (List.eq_nil_of_length_eq_zero h)
    rw [canonicalReadBits_length shape (j + 1)] at hlen1
    -- `omega` sees `Nat.min` as an atom, so bound it explicitly first.
    have hle1 :
        Nat.min (SuccinctRank.machineWordBits shape.bpCode.length)
            (shape.bpCode.length -
              (j + 1) * SuccinctRank.machineWordBits shape.bpCode.length) ≤
          shape.bpCode.length -
            (j + 1) * SuccinctRank.machineWordBits shape.bpCode.length :=
      Nat.min_le_right _ _
    have hsucc :
        (j + 1) * SuccinctRank.machineWordBits shape.bpCode.length =
          j * SuccinctRank.machineWordBits shape.bpCode.length +
            SuccinctRank.machineWordBits shape.bpCode.length :=
      Nat.succ_mul j _
    have hfull :
        SuccinctRank.machineWordBits shape.bpCode.length ≤
          shape.bpCode.length -
            j * SuccinctRank.machineWordBits shape.bpCode.length := by
      omega
    rw [canonicalReadBits_length shape j]
    exact Nat.min_eq_left hfull
  exact ⟨step base, step (base + 1), step (base + 2)⟩

/-! ## Feeding the rank-close component its position -/

/-- One instruction: the rank-close component reads its query position from
`rPos`, and the position the route uses is the window bit base `fBB` that
the address preamble computed. -/
def rankSeedPos : List Instr := [ .move rPos fBB ]

@[simp] theorem rankSeedPos_length : rankSeedPos.length = 1 := rfl

/-- Category log of the position feed. -/
def rankSeedPosCats : List Category := [.registerWrite]

/-- Constructor-exhaustive width certificate for the position feed. -/
theorem rankSeedPos_fits (w : Nat) (hw : 64 < 2 ^ w) :
    ∀ instr ∈ rankSeedPos, Instr.FieldsFit w instr := by
  intro instr hinstr
  have h8 : (8 : Nat) < 2 ^ w := by omega
  simp only [rankSeedPos, List.mem_cons, List.not_mem_nil, or_false] at hinstr
  subst hinstr
  exact ⟨h8, hw⟩

/-- Exact simulation of the position feed: no receipt, one tick. -/
theorem rankSeedPos_runsTo
    (store : ReadStore) {program : E1Machine.Program} {P : Nat}
    (hHost : HostedAt program P rankSeedPos) (regs : RegFile) :
    ∃ regs' : RegFile,
      RunsTo store program ⟨regs, P, false⟩ ⟨regs', P + 1, false⟩ []
        rankSeedPosCats ∧
      regs' rPos = regs fBB ∧
      (∀ r, r ≠ 8 → regs' r = regs r) := by
  have hf0 : program[P]? = some (.move rPos fBB) := by
    have := hHost 0 (by decide)
    simpa using this
  refine ⟨regs.write rPos (regs fBB), ?_, ?_, ?_⟩
  · have s0 : RunsTo store program ⟨regs, P, false⟩
        ⟨regs.write rPos (regs fBB), P + 1, false⟩ [] [.registerWrite] :=
      RunsTo.move (s := ⟨regs, P, false⟩) rfl hf0
    simpa [rankSeedPosCats] using s0
  · simp [RegFile.write, rPos]
  · intro r hr
    simp [RegFile.write, rPos, hr]

/-! ## The seed arithmetic -/

/-- Three instructions: `seed := base - 2 * rankFalse`, delivered into BOTH
registers the fringe arm consumes (`fAcc` as the fold accumulator seed,
`fSeed` as the pinned rebase constant). -/
def rankSeedFinish : List Instr :=
  [ .mulConst fU rVal 2     -- S+0  rankFalse * 2
  , .sub fAcc fBB fU        -- S+1  base - that
  , .move fSeed fAcc ]      -- S+2  the arm pins the same value twice

@[simp] theorem rankSeedFinish_length : rankSeedFinish.length = 3 := rfl

/-- Category log of the seed arithmetic. -/
def rankSeedFinishCats : List Category :=
  [.arithmetic, .arithmetic, .registerWrite]

/-- Constructor-exhaustive width certificate for the seed arithmetic. -/
theorem rankSeedFinish_fits (w : Nat) (hw : 65 < 2 ^ w) :
    ∀ instr ∈ rankSeedFinish, Instr.FieldsFit w instr := by
  intro instr hinstr
  have h2 : (2 : Nat) < 2 ^ w := by omega
  have h9 : (9 : Nat) < 2 ^ w := by omega
  have h46 : (46 : Nat) < 2 ^ w := by omega
  have h61 : (61 : Nat) < 2 ^ w := by omega
  have h64 : (64 : Nat) < 2 ^ w := by omega
  have h65 : (65 : Nat) < 2 ^ w := hw
  simp only [rankSeedFinish, List.mem_cons, List.not_mem_nil, or_false]
    at hinstr
  rcases hinstr with h | h | h <;> subst h
  · exact ⟨h61, h9, h2⟩
  · exact ⟨h46, h64, h61⟩
  · exact ⟨h65, h46⟩

/-- Every seed-arithmetic instruction is straight-line. -/
theorem rankSeedFinish_straight :
    ∀ instr ∈ rankSeedFinish, instr.isStraight = true := by
  intro instr hinstr
  simp only [rankSeedFinish, List.mem_cons, List.not_mem_nil, or_false]
    at hinstr
  rcases hinstr with rfl | rfl | rfl <;> rfl

local macro "seed_eval" : tactic =>
  `(tactic| straight_eval [rankSeedFinish, fU, fAcc, fSeed, fBB, rVal])

/-- The seed arithmetic writes only `fU`, `fAcc` and `fSeed`.  Numerals,
not abbrevs, so `omega` can use it. -/
abbrev RankSeedUntouched (r : Nat) : Prop :=
  r ≠ 46 ∧ r ≠ 61 ∧ r ≠ 65

/-- Exact simulation of the seed arithmetic: no receipt, three ticks, and
both seed registers holding the accepted `localBPSeedFromRankFalse` of the
rank-close component's own returned value. -/
theorem rankSeedFinish_runsTo
    (store : ReadStore) {program : E1Machine.Program} {S : Nat}
    (hHost : HostedAt program S rankSeedFinish)
    (regs : RegFile) (base rankFalse : Nat)
    (hBB : regs fBB = base) (hVal : regs rVal = rankFalse) :
    ∃ regs' : RegFile,
      RunsTo store program ⟨regs, S, false⟩ ⟨regs', S + 3, false⟩ []
        rankSeedFinishCats ∧
      regs' fAcc = localBPSeedFromRankFalse base rankFalse ∧
      regs' fSeed = localBPSeedFromRankFalse base rankFalse ∧
      (∀ r, RankSeedUntouched r → regs' r = regs r) := by
  have hrun := RunsTo.straight store rankSeedFinish rankSeedFinish_straight
    S hHost regs
  obtain ⟨regsW, hregsW⟩ :
      ∃ x, straightRegs store rankSeedFinish regs = x := ⟨_, rfl⟩
  rw [hregsW] at hrun
  have hreads : straightReads store rankSeedFinish regs = [] := by seed_eval
  have hcats : rankSeedFinish.map Instr.category = rankSeedFinishCats := rfl
  rw [hreads, hcats] at hrun
  refine ⟨regsW, by simpa using hrun, ?_, ?_, ?_⟩
  · rw [<- hregsW]
    seed_eval <;> simp [hBB, hVal, localBPSeedFromRankFalse, Nat.mul_comm]
  · rw [<- hregsW]
    seed_eval <;> simp [hBB, hVal, localBPSeedFromRankFalse, Nat.mul_comm]
  · intro r hr
    obtain ⟨h46, h61, h65⟩ := hr
    rw [<- hregsW]
    apply straightRegs_preserves
    intro i hi
    simp only [rankSeedFinish, List.mem_cons, List.not_mem_nil, or_false]
      at hi
    rcases hi with rfl | rfl | rfl <;>
      straight_writes [fU, fAcc, fSeed] <;> omega

/-! ## The seed leg: position feed, rank-close component, seed arithmetic -/

/-- Category log of the whole seed leg, indexed by the ROUTE-side chunk
count the rank-close component's own hit path derives -- never a numeral. -/
def rankSeedLegCats (shape : Cartesian.CartesianShape) (base : Nat) :
    List Category :=
  rankSeedPosCats ++
    (rankCloseHitCats
      (bpWordChunkCount (bpFringeChunkBits shape.bpCode.length)
        ((builtRelativeSplitBPCloseRankData shape).wordOffset base)) ++
      rankSeedFinishCats)

/--
THE SEED LEG'S WRITE-SET COMPLEMENT.

The leg writes `rPos` (8), the rank-close component's bank (9 .. 27) and
the seed arithmetic's `fAcc` (46), `fU` (61) and `fSeed` (65).  Numerals,
not abbrevs, so `omega` can use it.

Added M3d-9 for the cross-block composition: the four specific clauses
already in `rankSeedLeg_runsTo_canonical` cover only the registers the
SAME-BLOCK leg happened to need, and the cross-block composition must
carry the left stash's merge slots `mLV` (75) and `mLP` (76) plus the
interior's `mMV` (77) / `mMP` (78) across the RIGHT seed leg.  Those four
satisfy this predicate by `decide`.
-/
abbrev RankSeedLegUntouched (r : Nat) : Prop :=
  (r ≤ 7 ∨ 28 ≤ r) ∧ r ≠ 46 ∧ r ≠ 61 ∧ r ≠ 65

/--
EXACT SIMULATION OF THE SEED LEG (`P -> P + 64`) at the canonical store.

The receipt is POSITIONALLY equal to the accepted seed object's `.trace`
(`localBPSeedFromRankCloseTraceResult` at the canonical rank-close trace),
and both seed registers carry its `.value`.  The seed is computed from the
machine's OWN charged reads: `rVal` is whatever the rank-close component's
reads returned, not a copy of the spec value.
-/
theorem rankSeedLeg_runsTo_canonical
    (shape : Cartesian.CartesianShape) {program : E1Machine.Program}
    {P blockSize leftClose : Nat}
    (hPos : HostedAt program P rankSeedPos)
    (hRank : HostedAt program (P + 1)
      (rankCloseBlock (P + 1) concreteBPNativeRankCloseTraceSegmentBase
        (bpFringeChunkBits shape.bpCode.length)
        shape.bpCode.length
        (builtRelativeSplitBPCloseRankData shape).wordSize
        (builtRelativeSplitBPCloseRankData shape).blocksPerSuper))
    (hFin : HostedAt program (P + 61) rankSeedFinish)
    (regs : RegFile)
    (hBB : regs fBB = sbBB shape blockSize leftClose) :
    ∃ regs' : RegFile,
      RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape) program
          ⟨regs, P, false⟩ ⟨regs', P + 64, false⟩
        (localBPSeedFromRankCloseTraceResult shape
          (concreteBPNativeChunkedRankCloseGlobalWordTraceResult shape)
          blockSize leftClose).trace
        (rankSeedLegCats shape (sbBB shape blockSize leftClose)) ∧
      regs' fAcc =
        (localBPSeedFromRankCloseTraceResult shape
          (concreteBPNativeChunkedRankCloseGlobalWordTraceResult shape)
          blockSize leftClose).value ∧
      regs' fSeed =
        (localBPSeedFromRankCloseTraceResult shape
          (concreteBPNativeChunkedRankCloseGlobalWordTraceResult shape)
          blockSize leftClose).value ∧
      regs' fBase = regs fBase ∧
      regs' fBB = regs fBB ∧
      regs' fClose = regs fClose ∧
      regs' fRight = regs fRight ∧
      (∀ r, RankSeedLegUntouched r → regs' r = regs r) := by
  obtain ⟨regs1, hrun1, hpos1, hpres1⟩ :=
    rankSeedPos_runsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      hPos regs
  obtain ⟨regs2, hrun2, hval2, hpres2⟩ :=
    rankCloseBlock_runsTo_canonical shape hRank regs1
  obtain ⟨regs3, hrun3, hacc3, hseed3, hpres3⟩ :=
    rankSeedFinish_runsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      hFin regs2 (sbBB shape blockSize leftClose)
      (concreteBPNativeChunkedRankCloseGlobalWordTraceResult shape
        (regs1 rPos)).value
      (by rw [hpres2 fBB (by decide), hpres1 fBB (by decide)]; exact hBB)
      hval2
  -- the position the rank component saw IS the route's window bit base
  have hp : regs1 rPos = sbBB shape blockSize leftClose := by
    rw [hpos1]; exact hBB
  refine ⟨regs3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have htrans := (hrun1.trans hrun2).trans hrun3
    have hpc : P + 1 + 60 + 3 = P + 64 := by omega
    rw [hpc] at htrans
    rw [hp] at htrans
    simpa [rankSeedLegCats, localBPSeedFromRankCloseTraceResult,
      WordRAM.TraceResult.map, WordRAM.TraceResult.bind,
      WordRAM.TraceResult.pure, sbBB] using htrans
  · rw [hacc3, hp]
    simp [localBPSeedFromRankCloseTraceResult, WordRAM.TraceResult.map,
      WordRAM.TraceResult.bind, WordRAM.TraceResult.pure, sbBB]
  · rw [hseed3, hp]
    simp [localBPSeedFromRankCloseTraceResult, WordRAM.TraceResult.map,
      WordRAM.TraceResult.bind, WordRAM.TraceResult.pure, sbBB]
  · rw [hpres3 fBase (by decide), hpres2 fBase (by decide),
      hpres1 fBase (by decide)]
  · rw [hpres3 fBB (by decide), hpres2 fBB (by decide),
      hpres1 fBB (by decide)]
  · rw [hpres3 fClose (by decide), hpres2 fClose (by decide),
      hpres1 fClose (by decide)]
  · rw [hpres3 fRight (by decide), hpres2 fRight (by decide),
      hpres1 fRight (by decide)]
  · intro r hr
    obtain ⟨hbank, h46, h61, h65⟩ := hr
    rw [hpres3 r ⟨h46, h61, h65⟩, hpres2 r (by omega),
      hpres1 r (by omega)]

/-! ## The whole same-block close leg at the canonical store

Layout at base `A` (173 instructions):

| range | segment | instructions |
| --- | --- | --- |
| `A .. A+3` | address preamble `windowAddr` | 4 |
| `A+4` | position feed `rankSeedPos` | 1 |
| `A+5 .. A+64` | `rankCloseBlock` | 60 |
| `A+65 .. A+67` | seed arithmetic `rankSeedFinish` | 3 |
| `A+68 .. A+75` | range preamble `windowRange` | 8 |
| `A+76 .. A+172` | `sameBlockArm` | 97 |

Only the rank-close component emits receipts before the arm, so the whole
leg's log is the accepted decoded object's log, in order.
-/

/-- The route's own seed value at the canonical rank-close trace. -/
abbrev canonicalSeed (shape : Cartesian.CartesianShape)
    (blockSize leftClose : Nat) : Nat :=
  (localBPSeedFromRankCloseTraceResult shape
    (concreteBPNativeChunkedRankCloseGlobalWordTraceResult shape)
    blockSize leftClose).value

/-- Category log of the whole same-block close leg: the four preamble
ticks, the seed leg's route-indexed log, the eight range ticks, and the
arm's own route-indexed log.  Every component is a FUNCTION of route-side
data; no numeral is asserted anywhere in this log. -/
def sameBlockLegCats (shape : Cartesian.CartesianShape)
    (fringeSegment blockSize leftClose rightClose : Nat) : List Category :=
  windowAddrCats ++
    (rankSeedLegCats shape (sbBB shape blockSize leftClose) ++
      (windowRangeCats ++
        sameBlockArmCats shape
          (concreteBPNativeSuccinctRMQGlobalReadStore shape) fringeSegment
          blockSize leftClose rightClose
          (canonicalSeed shape blockSize leftClose)))

/--
EXACT SIMULATION OF THE WHOLE SAME-BLOCK CLOSE LEG (173 instructions,
`A -> A + 173`) AT THE CANONICAL STORE.

Receipts are POSITIONALLY equal -- a `List` equality, not a multiset or
membership claim -- to
`bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegmentWithStore`
(`ChargedSameBlockTrace.lean:340`) instantiated at the canonical
rank-close trace and the canonical global store, and `fRes` carries its
`.value`.

Everything the machine consumes it computed itself: the window base from
the query operand by constant-divisor arithmetic, the seed from the
rank-close component's OWN charged reads, the range registers by add/sub,
and the candidate from the four window words its own `readMem`
instructions returned.  Nothing is copied from the spec.

This is the same-block leg only.  The cross-block/interior composition is
NOT part of this statement -- see `E1_WORKLOG.md` M3d-4 for exactly what
it still needs.
-/
theorem sameBlockLeg_runsTo_canonical
    (shape : Cartesian.CartesianShape) {program : E1Machine.Program}
    {A fringeSegment blockSize leftClose rightClose : Nat}
    (hAddr : HostedAt program A
      (windowAddr blockSize
        (SuccinctRank.machineWordBits shape.bpCode.length)))
    (hPos : HostedAt program (A + 4) rankSeedPos)
    (hRank : HostedAt program (A + 5)
      (rankCloseBlock (A + 5) concreteBPNativeRankCloseTraceSegmentBase
        (bpFringeChunkBits shape.bpCode.length)
        shape.bpCode.length
        (builtRelativeSplitBPCloseRankData shape).wordSize
        (builtRelativeSplitBPCloseRankData shape).blocksPerSuper))
    (hFin : HostedAt program (A + 65) rankSeedFinish)
    (hRange : HostedAt program (A + 68) windowRange)
    (hPro : HostedAt program (A + 76) (fringeArmPrologue (sbChunkBits shape)))
    (hPre : HostedAt program (A + 97)
      (fringePrefix fringeSegment (sbChunkBits shape)))
    (hMrg : HostedAt program (A + 129) (fringeMerge (A + 97)))
    (hTail : HostedAt program (A + 142)
      (fringeShift (sbChunkBits shape)
        (SuccinctRank.machineWordBits shape.bpCode.length) ++ fringeAdvance))
    (hbr : program[A + 163]? = some (.brNZ fCnt (A + 97)))
    (hEpi : HostedAt program (A + 164) (fringeCandGlobal (A + 164)))
    (hCls : HostedAt program (A + 171) sameBlockClose)
    (regs : RegFile)
    (hClose : regs fClose = leftClose) (hRight : regs fRight = rightClose) :
    ∃ regsF : RegFile,
      RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape) program
          ⟨regs, A, false⟩ ⟨regsF, A + 173, false⟩
        (bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegmentWithStore
          shape (concreteBPNativeChunkedRankCloseGlobalWordTraceResult shape)
          fringeSegment (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          blockSize leftClose rightClose).trace
        (sameBlockLegCats shape fringeSegment blockSize leftClose
          rightClose) ∧
      some (regsF fRes) =
        (bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegmentWithStore
          shape (concreteBPNativeChunkedRankCloseGlobalWordTraceResult shape)
          fringeSegment (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          blockSize leftClose rightClose).value ∧
      (∀ r, CloseLegUntouched r -> regsF r = regs r) := by
  -- 1. address preamble
  obtain ⟨regs1, hrun1, hbase1, hbb1, hpres1⟩ :=
    windowAddr_runsTo_route shape
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) hAddr regs leftClose
      hClose
  -- 2. seed leg (position feed, rank-close component, seed arithmetic)
  obtain ⟨regs2, hrun2, hacc2, hseed2, hb2, hbb2, hcl2, hri2, hpres2⟩ :=
    rankSeedLeg_runsTo_canonical shape (blockSize := blockSize)
      (leftClose := leftClose) hPos hRank hFin regs1 hbb1
  -- 3. range preamble
  obtain ⟨regs3, hrun3, hstart3, hlo3, hhi3, hpres3⟩ :=
    windowRange_runsTo_route shape
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) hRange regs2
      leftClose rightClose
      (by rw [hcl2, hpres1 fClose (by decide)]; exact hClose)
      (by rw [hri2, hpres1 fRight (by decide)]; exact hRight)
      (by rw [hbb2]; exact hbb1)
  -- 4. the same-block arm at the route's own seed
  obtain ⟨regsF, hrunA, hvalA, hpresA⟩ :=
    sameBlockArm_runsTo shape (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (bpFringeChunkBits_le_machineWordBits shape.bpCode.length)
      hPro hPre hMrg hTail hbr hEpi hCls blockSize leftClose rightClose
      (canonicalSeed shape blockSize leftClose)
      (SuccinctRank.machineWordBits_pos shape.bpCode.length)
      (canonicalWindowDense shape (sbBase shape blockSize leftClose)) regs3
      (by rw [hpres3 fBase (by decide), hb2]; exact hbase1)
      hlo3 hhi3
      (by rw [hpres3 fAcc (by decide)]; exact hacc2)
      (by rw [hpres3 fBB (by decide), hbb2]; exact hbb1)
      (by rw [hpres3 fSeed (by decide)]; exact hseed2)
      hstart3
  refine ⟨regsF, ?_, ?_, ?_⟩
  · have htrans := ((hrun1.trans hrun2).trans hrun3).trans hrunA
    have hpc : A + 4 + 64 + 8 + 97 = A + 173 := by omega
    rw [hpc] at htrans
    simpa [sameBlockLegCats,
      bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegmentWithStore,
      WordRAM.TraceResult.bind, canonicalSeed] using htrans
  · rw [hvalA]
    simp [bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegmentWithStore,
      WordRAM.TraceResult.bind, canonicalSeed]
  · -- COMPOSED PRESERVATION.  Every stage admits `r <= 7 ∨ r = 28`: the two
    -- preambles and the arm sit at `>= 40`, and the rank-seed leg's own
    -- clause already carves out exactly this band.
    intro r hr
    have hr' : r ≤ 7 ∨ r = 28 := hr
    rw [hpresA r hr,
      hpres3 r (by refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega),
      hpres2 r (by refine ⟨?_, ?_, ?_, ?_⟩ <;> omega),
      hpres1 r (by refine ⟨?_, ?_⟩ <;> omega)]

/-! ## ANTI-VACUITY: the hosting hypotheses are simultaneously satisfiable

`sameBlockLeg_runsTo_canonical` takes THIRTEEN `HostedAt` hypotheses plus a
back-edge fetch, all constraining ONE program at overlapping-looking
offsets.  A theorem whose hypotheses cannot all hold at once is worthless,
so this section exhibits a concrete program and discharges every one of
them, leaving only genuine route-side facts as hypotheses.

This is the vacuity challenge the matrix demands for a composed
simulation: had any offset in the layout table been wrong by one, the
peeling below would fail to typecheck.
-/

/-- Peel one hosted segment off an append chain at a computed base. -/
private theorem hostedAt_step {program : E1Machine.Program} {base : Nat}
    {code₁ code₂ : List Instr} {n : Nat}
    (h : HostedAt program base (code₁ ++ code₂))
    (hn : base + code₁.length = n) :
    HostedAt program n code₂ := hn ▸ h.append_right

/-- The concrete 173-instruction same-block close leg program, laid out
exactly as the table above.  The internal branch targets (`97` for the
fold back edge, `164` for the global-rebase epilogue) are the absolute
addresses that layout produces. -/
def sameBlockLegProgram (shape : Cartesian.CartesianShape)
    (fringeSegment blockSize : Nat) : List Instr :=
  windowAddr blockSize (SuccinctRank.machineWordBits shape.bpCode.length) ++
    (rankSeedPos ++
      (rankCloseBlock 5 concreteBPNativeRankCloseTraceSegmentBase
          (bpFringeChunkBits shape.bpCode.length) shape.bpCode.length
          (builtRelativeSplitBPCloseRankData shape).wordSize
          (builtRelativeSplitBPCloseRankData shape).blocksPerSuper ++
        (rankSeedFinish ++
          (windowRange ++
            (fringeArmPrologue (sbChunkBits shape) ++
              (fringePrefix fringeSegment (sbChunkBits shape) ++
                (fringeMerge 97 ++
                  ((fringeShift (sbChunkBits shape)
                        (SuccinctRank.machineWordBits shape.bpCode.length) ++
                      fringeAdvance) ++
                    ([Instr.brNZ fCnt 97] ++
                      (fringeCandGlobal 164 ++ sameBlockClose))))))))))

@[simp] theorem sameBlockLegProgram_length
    (shape : Cartesian.CartesianShape) (fringeSegment blockSize : Nat) :
    (sameBlockLegProgram shape fringeSegment blockSize).length = 173 := by
  simp [sameBlockLegProgram]

/--
EVERY hosting hypothesis of `sameBlockLeg_runsTo_canonical` holds
simultaneously of `sameBlockLegProgram` at base `0`, so the composed
simulation is NOT vacuous.  Each offset below is forced by the preceding
segments' lengths; the layout table is checked, not asserted.
-/
theorem sameBlockLegProgram_hosts
    (shape : Cartesian.CartesianShape) (fringeSegment blockSize : Nat) :
    HostedAt (sameBlockLegProgram shape fringeSegment blockSize) 0
        (windowAddr blockSize
          (SuccinctRank.machineWordBits shape.bpCode.length)) ∧
      HostedAt (sameBlockLegProgram shape fringeSegment blockSize) 4
        rankSeedPos ∧
      HostedAt (sameBlockLegProgram shape fringeSegment blockSize) 5
        (rankCloseBlock 5 concreteBPNativeRankCloseTraceSegmentBase
          (bpFringeChunkBits shape.bpCode.length) shape.bpCode.length
          (builtRelativeSplitBPCloseRankData shape).wordSize
          (builtRelativeSplitBPCloseRankData shape).blocksPerSuper) ∧
      HostedAt (sameBlockLegProgram shape fringeSegment blockSize) 65
        rankSeedFinish ∧
      HostedAt (sameBlockLegProgram shape fringeSegment blockSize) 68
        windowRange ∧
      HostedAt (sameBlockLegProgram shape fringeSegment blockSize) 76
        (fringeArmPrologue (sbChunkBits shape)) ∧
      HostedAt (sameBlockLegProgram shape fringeSegment blockSize) 97
        (fringePrefix fringeSegment (sbChunkBits shape)) ∧
      HostedAt (sameBlockLegProgram shape fringeSegment blockSize) 129
        (fringeMerge 97) ∧
      HostedAt (sameBlockLegProgram shape fringeSegment blockSize) 142
        (fringeShift (sbChunkBits shape)
          (SuccinctRank.machineWordBits shape.bpCode.length) ++
          fringeAdvance) ∧
      (sameBlockLegProgram shape fringeSegment blockSize)[163]? =
        some (.brNZ fCnt 97) ∧
      HostedAt (sameBlockLegProgram shape fringeSegment blockSize) 164
        (fringeCandGlobal 164) ∧
      HostedAt (sameBlockLegProgram shape fringeSegment blockSize) 171
        sameBlockClose := by
  have h0 : HostedAt (sameBlockLegProgram shape fringeSegment blockSize) 0
      (sameBlockLegProgram shape fringeSegment blockSize) :=
    hostedAt_self _
  rw [sameBlockLegProgram] at h0
  have h1 := hostedAt_step (n := 4) h0 (by simp)
  have h2 := hostedAt_step (n := 5) h1 (by simp)
  have h3 := hostedAt_step (n := 65) h2 (by simp)
  have h4 := hostedAt_step (n := 68) h3 (by simp)
  have h5 := hostedAt_step (n := 76) h4 (by simp)
  have h6 := hostedAt_step (n := 97) h5 (by simp)
  have h7 := hostedAt_step (n := 129) h6 (by simp)
  have h8 := hostedAt_step (n := 142) h7 (by simp)
  have h9 := hostedAt_step (n := 163) h8 (by simp)
  have h10 := hostedAt_step (n := 164) h9 (by simp)
  have h11 := hostedAt_step (n := 171) h10 (by simp)
  refine ⟨h0.append_left, h1.append_left, h2.append_left, h3.append_left,
    h4.append_left, h5.append_left, h6.append_left, h7.append_left,
    h8.append_left, ?_, h10.append_left, h11⟩
  exact h9.append_left 0 (by decide)

/--
THE SAME-BLOCK CLOSE LEG, HOSTING-UNCONDITIONAL.

`sameBlockLeg_runsTo_canonical` with every `HostedAt` hypothesis
discharged by the concrete `sameBlockLegProgram`.  NOTHING route-side
remains: the chunk-width fact is unconditional
(`bpFringeChunkBits_le_machineWordBits`) and the window-width demand has
been replaced by density, which the canonical store satisfies outright
(`canonicalWindowDense`).
-/
theorem sameBlockLegProgram_runsTo_canonical
    (shape : Cartesian.CartesianShape)
    {fringeSegment blockSize leftClose rightClose : Nat}
    (regs : RegFile)
    (hClose : regs fClose = leftClose) (hRight : regs fRight = rightClose) :
    ∃ regsF : RegFile,
      RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          (sameBlockLegProgram shape fringeSegment blockSize)
          ⟨regs, 0, false⟩ ⟨regsF, 173, false⟩
        (bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegmentWithStore
          shape (concreteBPNativeChunkedRankCloseGlobalWordTraceResult shape)
          fringeSegment (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          blockSize leftClose rightClose).trace
        (sameBlockLegCats shape fringeSegment blockSize leftClose
          rightClose) ∧
      some (regsF fRes) =
        (bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegmentWithStore
          shape (concreteBPNativeChunkedRankCloseGlobalWordTraceResult shape)
          fringeSegment (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          blockSize leftClose rightClose).value ∧
      (∀ r, CloseLegUntouched r -> regsF r = regs r) := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11⟩ :=
    sameBlockLegProgram_hosts shape fringeSegment blockSize
  have h :=
    sameBlockLeg_runsTo_canonical (A := 0) shape p0 p1 p2 p3 p4 p5 p6 p7
      p8 p9 p10 p11 regs hClose hRight
  simpa using h

/-! ## BASE-PARAMETRIC HOSTING (M3d-6)

`sameBlockLegProgram` above is a witness only at base `0`: three of its
internal branch targets are ABSOLUTE addresses (`fringeMerge 97`, the
`brNZ fCnt 97` fold back edge, and `fringeCandGlobal 164`), plus the
rank-close block's own segment base `5`.  Hosting the leg BEHIND a
dispatch prefix moves the whole block off `0`, so those four internal
addresses must move with it.

`sameBlockLegProgramAt B` is the same 173-instruction layout with every
internal address rebased to `B`.  Note that `sameBlockLeg_runsTo_canonical`
was ALREADY stated base-parametrically -- its hosting hypotheses sit at
`A + k` and its targets are written `A + 97` / `A + 164` -- so the
simulation theorem needs no change.  What was missing, and what this
section supplies, is a witness program able to satisfy those hypotheses at
a NONZERO base.
-/

/-- The 173-instruction same-block close leg laid out for host base `B`:
identical to `sameBlockLegProgram` except that the four internal addresses
are `B`-relative. -/
def sameBlockLegProgramAt (shape : Cartesian.CartesianShape)
    (fringeSegment blockSize B : Nat) : List Instr :=
  windowAddr blockSize (SuccinctRank.machineWordBits shape.bpCode.length) ++
    (rankSeedPos ++
      (rankCloseBlock (B + 5) concreteBPNativeRankCloseTraceSegmentBase
          (bpFringeChunkBits shape.bpCode.length) shape.bpCode.length
          (builtRelativeSplitBPCloseRankData shape).wordSize
          (builtRelativeSplitBPCloseRankData shape).blocksPerSuper ++
        (rankSeedFinish ++
          (windowRange ++
            (fringeArmPrologue (sbChunkBits shape) ++
              (fringePrefix fringeSegment (sbChunkBits shape) ++
                (fringeMerge (B + 97) ++
                  ((fringeShift (sbChunkBits shape)
                        (SuccinctRank.machineWordBits shape.bpCode.length) ++
                      fringeAdvance) ++
                    ([Instr.brNZ fCnt (B + 97)] ++
                      (fringeCandGlobal (B + 164) ++ sameBlockClose))))))))))

@[simp] theorem sameBlockLegProgramAt_length
    (shape : Cartesian.CartesianShape) (fringeSegment blockSize B : Nat) :
    (sameBlockLegProgramAt shape fringeSegment blockSize B).length = 173 := by
  simp [sameBlockLegProgramAt]

/-- The base-parametric layout SPECIALISES to the landed base-`0` one, so
nothing already proved about `sameBlockLegProgram` regresses. -/
theorem sameBlockLegProgramAt_zero
    (shape : Cartesian.CartesianShape) (fringeSegment blockSize : Nat) :
    sameBlockLegProgramAt shape fringeSegment blockSize 0 =
      sameBlockLegProgram shape fringeSegment blockSize := by
  simp [sameBlockLegProgramAt, sameBlockLegProgram]

/--
EVERY hosting hypothesis of `sameBlockLeg_runsTo_canonical` at base `B`
follows from the single assumption that `sameBlockLegProgramAt ... B` is
hosted at `B`.  Each offset is forced by the preceding segments' lengths
through `append_right`, so the layout table is CHECKED, not asserted -- an
off-by-one anywhere makes this fail to typecheck.
-/
theorem sameBlockLegProgramAt_hosts
    (shape : Cartesian.CartesianShape) {program : E1Machine.Program}
    (fringeSegment blockSize B : Nat)
    (hHost : HostedAt program B
      (sameBlockLegProgramAt shape fringeSegment blockSize B)) :
    HostedAt program B
        (windowAddr blockSize
          (SuccinctRank.machineWordBits shape.bpCode.length)) ∧
      HostedAt program (B + 4) rankSeedPos ∧
      HostedAt program (B + 5)
        (rankCloseBlock (B + 5) concreteBPNativeRankCloseTraceSegmentBase
          (bpFringeChunkBits shape.bpCode.length) shape.bpCode.length
          (builtRelativeSplitBPCloseRankData shape).wordSize
          (builtRelativeSplitBPCloseRankData shape).blocksPerSuper) ∧
      HostedAt program (B + 65) rankSeedFinish ∧
      HostedAt program (B + 68) windowRange ∧
      HostedAt program (B + 76) (fringeArmPrologue (sbChunkBits shape)) ∧
      HostedAt program (B + 97)
        (fringePrefix fringeSegment (sbChunkBits shape)) ∧
      HostedAt program (B + 129) (fringeMerge (B + 97)) ∧
      HostedAt program (B + 142)
        (fringeShift (sbChunkBits shape)
          (SuccinctRank.machineWordBits shape.bpCode.length) ++
          fringeAdvance) ∧
      program[B + 163]? = some (.brNZ fCnt (B + 97)) ∧
      HostedAt program (B + 164) (fringeCandGlobal (B + 164)) ∧
      HostedAt program (B + 171) sameBlockClose := by
  rw [sameBlockLegProgramAt] at hHost
  have h1 := hostedAt_step (n := B + 4) hHost (by simp)
  have h2 := hostedAt_step (n := B + 5) h1 (by simp)
  have h3 := hostedAt_step (n := B + 65) h2 (by simp)
  have h4 := hostedAt_step (n := B + 68) h3 (by simp)
  have h5 := hostedAt_step (n := B + 76) h4 (by simp)
  have h6 := hostedAt_step (n := B + 97) h5 (by simp)
  have h7 := hostedAt_step (n := B + 129) h6 (by simp)
  have h8 := hostedAt_step (n := B + 142) h7 (by simp)
  have h9 := hostedAt_step (n := B + 163) h8 (by simp)
  have h10 := hostedAt_step (n := B + 164) h9 (by simp)
  have h11 := hostedAt_step (n := B + 171) h10 (by simp)
  refine ⟨hHost.append_left, h1.append_left, h2.append_left, h3.append_left,
    h4.append_left, h5.append_left, h6.append_left, h7.append_left,
    h8.append_left, ?_, h10.append_left, h11⟩
  -- NOTE: `by decide` closes this at base `0` but NOT here: with `B` free
  -- the goal `0 < [Instr.brNZ fCnt (B + 97)].length` contains a free
  -- variable and `decide` refuses it.  `simp` computes the length instead.
  exact h9.append_left 0 (by simp)

/--
THE SAME-BLOCK CLOSE LEG AT AN ARBITRARY HOST BASE.

`sameBlockLegProgram_runsTo_canonical` generalised off base `0`: given only
that the rebased layout is hosted at `B`, the leg runs from `B` to
`B + 173` reproducing the route's own trace and value.  This is the form a
dispatch prefix needs.
-/
theorem sameBlockLegProgramAt_runsTo_canonical
    (shape : Cartesian.CartesianShape) {program : E1Machine.Program}
    {fringeSegment blockSize leftClose rightClose B : Nat}
    (hHost : HostedAt program B
      (sameBlockLegProgramAt shape fringeSegment blockSize B))
    (regs : RegFile)
    (hClose : regs fClose = leftClose) (hRight : regs fRight = rightClose) :
    ∃ regsF : RegFile,
      RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          program ⟨regs, B, false⟩ ⟨regsF, B + 173, false⟩
        (bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegmentWithStore
          shape (concreteBPNativeChunkedRankCloseGlobalWordTraceResult shape)
          fringeSegment (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          blockSize leftClose rightClose).trace
        (sameBlockLegCats shape fringeSegment blockSize leftClose
          rightClose) ∧
      some (regsF fRes) =
        (bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegmentWithStore
          shape (concreteBPNativeChunkedRankCloseGlobalWordTraceResult shape)
          fringeSegment (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          blockSize leftClose rightClose).value ∧
      (∀ r, CloseLegUntouched r -> regsF r = regs r) := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11⟩ :=
    sameBlockLegProgramAt_hosts shape fringeSegment blockSize B hHost
  exact sameBlockLeg_runsTo_canonical (A := B) shape p0 p1 p2 p3 p4 p5 p6
    p7 p8 p9 p10 p11 regs hClose hRight

end E1SameBlockLeg
end WordRAM
end RMQ
