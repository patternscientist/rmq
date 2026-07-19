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
      regs' fRight = regs fRight := by
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
  refine ⟨regs3, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    (hc : sbChunkBits shape ≤ SuccinctRank.machineWordBits shape.bpCode.length)
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
    (h0 : (readBits (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (sbBase shape blockSize leftClose)).length =
        SuccinctRank.machineWordBits shape.bpCode.length)
    (h1 : (readBits (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (sbBase shape blockSize leftClose + 1)).length =
        SuccinctRank.machineWordBits shape.bpCode.length)
    (h2 : (readBits (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (sbBase shape blockSize leftClose + 2)).length =
        SuccinctRank.machineWordBits shape.bpCode.length)
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
          blockSize leftClose rightClose).value := by
  -- 1. address preamble
  obtain ⟨regs1, hrun1, hbase1, hbb1, hpres1⟩ :=
    windowAddr_runsTo_route shape
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) hAddr regs leftClose
      hClose
  -- 2. seed leg (position feed, rank-close component, seed arithmetic)
  obtain ⟨regs2, hrun2, hacc2, hseed2, hb2, hbb2, hcl2, hri2⟩ :=
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
  obtain ⟨regsF, hrunA, hvalA⟩ :=
    sameBlockArm_runsTo shape (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      hc hPro hPre hMrg hTail hbr hEpi hCls blockSize leftClose rightClose
      (canonicalSeed shape blockSize leftClose) h0 h1 h2 regs3
      (by rw [hpres3 fBase (by decide), hb2]; exact hbase1)
      hlo3 hhi3
      (by rw [hpres3 fAcc (by decide)]; exact hacc2)
      (by rw [hpres3 fBB (by decide), hbb2]; exact hbb1)
      (by rw [hpres3 fSeed (by decide)]; exact hseed2)
      hstart3
  refine ⟨regsF, ?_, ?_⟩
  · have htrans := ((hrun1.trans hrun2).trans hrun3).trans hrunA
    have hpc : A + 4 + 64 + 8 + 97 = A + 173 := by omega
    rw [hpc] at htrans
    simpa [sameBlockLegCats,
      bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegmentWithStore,
      WordRAM.TraceResult.bind, canonicalSeed] using htrans
  · rw [hvalA]
    simp [bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegmentWithStore,
      WordRAM.TraceResult.bind, canonicalSeed]

end E1SameBlockLeg
end WordRAM
end RMQ
