import RMQ.Core.WordRAM.E1FringeArmBlock
import RMQ.Core.SuccinctClose.RelativeRmmMacro.ChargedSameBlockTrace

/-!
# E1 amended machine: the SAME-BLOCK close arm (M3d-3, step 2)

The B6 same-block object
`bpChunkedSameBlockCloseSeededTraceResultAtSegmentWithStore`
(`ChargedSameBlockTrace.lean:55`) is, structurally, exactly the fringe arm
this rung already simulates (`E1FringeArmBlock.fringeArm_runsTo`)
instantiated at the same-block range (`start := leftClose + 1`,
`count := rightClose - leftClose + 1`) and post-composed with the accepted
PURE projection `bpCandidateClose?`.

Two facts make the composition cheap and make it honest:

* `bpFringeCandGlobal` is total into `some` (`ChargedFringeChunks.lean:1617`
  — both arms produce `some`), so `bpCandidateClose?` on it is the single
  arithmetic expression `position - 1`.  The epilogue is therefore TWO
  instructions, not an option dispatch, and it emits NO read event —
  matching the route, whose `TraceResult.map` contributes no trace.
* the same-block object's 33-cap init is literally
  `Nat.min (relHi / c + 1) 33` (`ChargedSameBlockTrace.lean:52`), the SAME
  shape `E1FringeArmBlock.cap_chain_eq_min` already derives, so no new cap
  reasoning is needed and no numeral is asserted.

The receipt obligation is discharged POSITIONALLY: the arm's log is the
four window reads followed by the accepted fold object's own trace, and
`sameBlockSeeded_trace_eq` identifies that, as a `List` equality, with the
accepted same-block object's `.trace`.
-/

namespace RMQ
namespace WordRAM
namespace E1SameBlockArm

open E1Machine
open E1FringeFoldBlock
open E1FringeArmBlock
open RMQ.SuccinctClose
open RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory

/-! ## Register bank extension (same-block arm, `69`) -/

/-- The same-block close result (the `bpCandidateClose?` payload). -/
abbrev fRes : Nat := 69

/-! ## Route-side instantiation of the same-block range

These are the route object's own `let`-bindings, named so the composed
theorem statement stays readable.  They are `abbrev`s, hence reducible, so
the route object unfolds onto them definitionally.
-/

/-- Chunk width. -/
abbrev sbChunkBits (shape : Cartesian.CartesianShape) : Nat :=
  bpFringeChunkBits shape.bpCode.length

/-- Window bit base (the route's `base`, and the arm's rebase constant). -/
abbrev sbBB (shape : Cartesian.CartesianShape)
    (blockSize leftClose : Nat) : Nat :=
  localBPWindowBase shape blockSize leftClose

/-- Window word index (the machine's `fBase`). -/
abbrev sbBase (shape : Cartesian.CartesianShape)
    (blockSize leftClose : Nat) : Nat :=
  bpWindowFirstWord shape blockSize leftClose

/-- Fallback candidate position. -/
abbrev sbStart (leftClose : Nat) : Nat := leftClose + 1

/-- Low relative offset. -/
abbrev sbRelLo (shape : Cartesian.CartesianShape)
    (blockSize leftClose : Nat) : Nat :=
  leftClose + 1 - localBPWindowBase shape blockSize leftClose

/-- High relative offset, at the same-block count. -/
abbrev sbRelHi (shape : Cartesian.CartesianShape)
    (blockSize leftClose rightClose : Nat) : Nat :=
  leftClose + 1 + (rightClose - leftClose + 1) - 1 -
    localBPWindowBase shape blockSize leftClose

/-- The DERIVED 33-capped chunk count, never an asserted numeral. -/
abbrev sbCount (shape : Cartesian.CartesianShape)
    (blockSize leftClose rightClose : Nat) : Nat :=
  Nat.min
    (sbRelHi shape blockSize leftClose rightClose / sbChunkBits shape + 1) 33

/-- The accepted fold object at the same-block instantiation. -/
abbrev sbFold (shape : Cartesian.CartesianShape) (store : ReadStore)
    (fringeSegment blockSize leftClose rightClose seed : Nat) :
    WordRAM.TraceResult (Nat × Option (Nat × Nat)) :=
  bpFringeChunkFoldTraceResultAtSegmentWithStore store fringeSegment
    (sbChunkBits shape)
    (windowBitsOfStore store (sbBase shape blockSize leftClose))
    seed
    (sbRelLo shape blockSize leftClose)
    (sbRelHi shape blockSize leftClose rightClose)
    (sbCount shape blockSize leftClose rightClose)

/-! ## The ADDRESS PREAMBLE (risk gate: constant divisors only)

`fringeArm_runsTo` takes the window base registers as hypotheses.  This
block computes them from the query operand, and it is the reason the
divisor question had to be settled first: the ISA has `divConst`/
`mulConst` only, so every divisor here must be a PER-SHAPE constant.

It is.  `blockOfClose blockSize close = close / blockSize` and
`blockStartOf blockSize block = block * blockSize`
(`BlockLocal.lean:863`/`:866`), and on the accepted route `blockSize` is
always `canonicalBPRelativeSummaryBlockSizeRaw shape`
(`RelativeSummary.lean:1240`), a function of `shape` alone -- never of
`close`, `left`, `right`, or any value read from memory.  Likewise
`L = SuccinctRank.machineWordBits shape.bpCode.length`
(`SuccinctRank.lean:38`).  Both are positive, which `divConst`'s width
arm additionally requires.

So the whole preamble is FOUR arithmetic instructions with encoded
constants, and no variable-divisor instruction is needed.
-/

/-- The close position the preamble consumes. -/
abbrev fClose : Nat := 70

/-- The address preamble at base `P` (four instructions, exit `P + 4`):
window word index into `fBase`, window bit base into `fBB`. -/
def windowAddr (blockSize L : Nat) : List Instr :=
  [ .divConst fBase fClose blockSize   -- P+0  block index
  , .mulConst fBase fBase blockSize    -- P+1  block start
  , .divConst fBase fBase L            -- P+2  first window word
  , .mulConst fBB fBase L ]            -- P+3  window bit base

@[simp] theorem windowAddr_length (blockSize L : Nat) :
    (windowAddr blockSize L).length = 4 := rfl

/-- Category log of the preamble: four unconditional arithmetic ticks. -/
def windowAddrCats : List Category :=
  [.arithmetic, .arithmetic, .arithmetic, .arithmetic]

/-- Constructor-exhaustive width certificate for the address preamble.
The `0 < blockSize` and `0 < L` side conditions are exactly `divConst`'s
positivity arm, and both hold on the accepted route. -/
theorem windowAddr_fits (w blockSize L : Nat) (hw : 70 < 2 ^ w)
    (hbs : 0 < blockSize) (hbsw : blockSize < 2 ^ w)
    (hL : 0 < L) (hLw : L < 2 ^ w) :
    ∀ instr ∈ windowAddr blockSize L, Instr.FieldsFit w instr := by
  intro instr hinstr
  have h63 : (63 : Nat) < 2 ^ w := by omega
  have h64 : (64 : Nat) < 2 ^ w := by omega
  have h70 : (70 : Nat) < 2 ^ w := hw
  simp only [windowAddr, List.mem_cons, List.not_mem_nil, or_false] at hinstr
  rcases hinstr with h | h | h | h <;> subst h
  · exact ⟨h63, h70, hbs, hbsw⟩
  · exact ⟨h63, h63, hbsw⟩
  · exact ⟨h63, h63, hL, hLw⟩
  · exact ⟨h64, h63, hLw⟩

/-- Every preamble instruction is straight-line (no branch, no halt). -/
theorem windowAddr_straight (blockSize L : Nat) :
    ∀ instr ∈ windowAddr blockSize L, instr.isStraight = true := by
  intro instr hinstr
  simp only [windowAddr, List.mem_cons, List.not_mem_nil, or_false] at hinstr
  rcases hinstr with rfl | rfl | rfl | rfl <;> rfl

local macro "addr_eval" : tactic =>
  `(tactic| straight_eval [windowAddr, fBase, fBB, fClose])

/-- The preamble writes only the two window base registers. -/
abbrev WindowAddrUntouched (r : Nat) : Prop := r ≠ 63 ∧ r ≠ 64

/-- Exact simulation of the address preamble: no receipt, four arithmetic
ticks, and the two window base registers computed from the query operand
by constant-divisor arithmetic alone. -/
theorem windowAddr_runsTo
    (store : ReadStore) {program : E1Machine.Program} {P blockSize L : Nat}
    (hHost : HostedAt program P (windowAddr blockSize L))
    (regs : RegFile) (close : Nat) (hClose : regs fClose = close) :
    ∃ regs' : RegFile,
      RunsTo store program ⟨regs, P, false⟩ ⟨regs', P + 4, false⟩ []
        windowAddrCats ∧
      regs' fBase = blockStartOf blockSize (blockOfClose blockSize close) / L ∧
      regs' fBB =
        blockStartOf blockSize (blockOfClose blockSize close) / L * L ∧
      (∀ r, WindowAddrUntouched r → regs' r = regs r) := by
  have hrun := RunsTo.straight store (windowAddr blockSize L)
    (windowAddr_straight blockSize L) P hHost regs
  obtain ⟨regsW, hregsW⟩ :
      ∃ x, straightRegs store (windowAddr blockSize L) regs = x := ⟨_, rfl⟩
  rw [hregsW] at hrun
  have hreads : straightReads store (windowAddr blockSize L) regs = [] := by
    addr_eval
  have hcats :
      (windowAddr blockSize L).map Instr.category = windowAddrCats := rfl
  rw [hreads, hcats] at hrun
  refine ⟨regsW, by simpa using hrun, ?_, ?_, ?_⟩
  · rw [<- hregsW]
    addr_eval <;> simp [hClose, blockStartOf, blockOfClose]
  · rw [<- hregsW]
    addr_eval <;> simp [hClose, blockStartOf, blockOfClose]
  · intro r hr
    obtain ⟨hB, hBB⟩ := hr
    rw [<- hregsW]
    apply straightRegs_preserves
    intro i hi
    simp only [windowAddr, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;>
      straight_writes [fBase, fBB, fClose] <;> omega

/-- The preamble's outputs ARE the route's window word index and window
bit base, at the accepted route's own `blockSize` and word width. -/
theorem windowAddr_runsTo_route
    (shape : Cartesian.CartesianShape) (store : ReadStore)
    {program : E1Machine.Program} {P blockSize : Nat}
    (hHost : HostedAt program P
      (windowAddr blockSize
        (SuccinctRank.machineWordBits shape.bpCode.length)))
    (regs : RegFile) (close : Nat) (hClose : regs fClose = close) :
    ∃ regs' : RegFile,
      RunsTo store program ⟨regs, P, false⟩ ⟨regs', P + 4, false⟩ []
        windowAddrCats ∧
      regs' fBase = bpWindowFirstWord shape blockSize close ∧
      regs' fBB = localBPWindowBase shape blockSize close ∧
      (∀ r, WindowAddrUntouched r → regs' r = regs r) := by
  obtain ⟨regs', hrun, hbase, hbb, hpres⟩ :=
    windowAddr_runsTo store hHost regs close hClose
  refine ⟨regs', hrun, hbase, ?_, hpres⟩
  rw [hbb, localBPWindowBase_eq]
  rfl

/-! ## The `bpCandidateClose?` epilogue

`bpCandidateClose?` maps an occupied candidate to `position - 1`
(`Candidate.lean:28`).  Because the arm's output is `bpFringeCandGlobal`,
which is always occupied, the epilogue needs no option test.
-/

/-- The close epilogue at base `E` (two instructions, exit `E + 2`). -/
def sameBlockClose : List Instr :=
  [ .const fT 1          -- E+0
  , .sub fRes fRP fT ]   -- E+1

@[simp] theorem sameBlockClose_length : sameBlockClose.length = 2 := rfl

/-- Category log of the close epilogue.  Unconditional: the epilogue has
no route-side branch, because `bpFringeCandGlobal` is total into `some`. -/
def sameBlockCloseCats : List Category := [.registerWrite, .arithmetic]

/-- Constructor-exhaustive width certificate for the close epilogue. -/
theorem sameBlockClose_fits (w : Nat) (hw : 69 < 2 ^ w) :
    ∀ instr ∈ sameBlockClose, Instr.FieldsFit w instr := by
  intro instr hinstr
  have h1 : (1 : Nat) < 2 ^ w := by omega
  have h60 : (60 : Nat) < 2 ^ w := by omega
  have h68 : (68 : Nat) < 2 ^ w := by omega
  have h69 : (69 : Nat) < 2 ^ w := hw
  simp only [sameBlockClose, List.mem_cons, List.not_mem_nil, or_false]
    at hinstr
  rcases hinstr with h | h <;> subst h
  · exact ⟨h60, h1⟩
  · exact ⟨h69, h68, h60⟩

/-- Exact simulation of the close epilogue: no receipt, a fixed two-tick
category log, and `fRes` holding the accepted `bpCandidateClose?` payload
of the arm's occupied result pair. -/
theorem sameBlockClose_runsTo
    (store : ReadStore) {program : E1Machine.Program} {E : Nat}
    (hHost : HostedAt program E sameBlockClose)
    (regs : RegFile) :
    ∃ regs' : RegFile,
      RunsTo store program ⟨regs, E, false⟩ ⟨regs', E + 2, false⟩ []
        sameBlockCloseCats ∧
      regs' fRes = regs fRP - 1 ∧
      (∀ r, r ≠ fT ∧ r ≠ fRes → regs' r = regs r) := by
  have hf0 : program[E]? = some (.const fT 1) := by
    have := hHost 0 (by decide)
    simpa using this
  have hf1 : program[E + 1]? = some (.sub fRes fRP fT) := by
    have := hHost 1 (by decide)
    simpa using this
  have s0 : RunsTo store program ⟨regs, E, false⟩
      ⟨regs.write fT 1, E + 1, false⟩ [] [.registerWrite] :=
    RunsTo.const (s := ⟨regs, E, false⟩) rfl hf0
  have s1 : RunsTo store program ⟨regs.write fT 1, E + 1, false⟩
      ⟨(regs.write fT 1).write fRes
          ((regs.write fT 1) fRP - (regs.write fT 1) fT),
        E + 1 + 1, false⟩ [] [.arithmetic] :=
    RunsTo.sub (s := ⟨regs.write fT 1, E + 1, false⟩) rfl hf1
  refine ⟨(regs.write fT 1).write fRes
      ((regs.write fT 1) fRP - (regs.write fT 1) fT), ?_, ?_, ?_⟩
  · have h := s0.trans s1
    have hpc : E + 1 + 1 = E + 2 := by omega
    rw [hpc] at h
    simpa [sameBlockCloseCats] using h
  · simp [RegFile.write, fRes, fRP, fT]
  · intro r hr
    obtain ⟨hT, hRes⟩ := hr
    simp [RegFile.write, hT, hRes]

/-! ## Receipt and value bridges to the accepted same-block object -/

/--
RECEIPT BRIDGE.  The accepted same-block object's trace is POSITIONALLY —
a `List` equality, not a multiset or membership claim — the four window
reads followed by the accepted fold object's own trace.  The
`bpCandidateClose?` projection is a `TraceResult.map` and contributes no
event, exactly as the machine's epilogue emits none.
-/
theorem sameBlockSeeded_trace_eq
    (shape : Cartesian.CartesianShape) (store : ReadStore)
    (fringeSegment blockSize leftClose rightClose seed : Nat) :
    (bpChunkedSameBlockCloseSeededTraceResultAtSegmentWithStore
        shape store fringeSegment blockSize leftClose rightClose seed).trace =
      windowReadEvents store (sbBase shape blockSize leftClose) ++
        (sbFold shape store fringeSegment blockSize leftClose rightClose
          seed).trace := by
  simp only [bpChunkedSameBlockCloseSeededTraceResultAtSegmentWithStore,
    WordRAM.TraceResult.bind, WordRAM.TraceResult.map,
    WordRAM.TraceResult.pure]
  rw [<- windowReadEvents_eq_route_windowBits shape store blockSize leftClose,
    route_windowBits_eq_windowBitsOfStore shape store blockSize leftClose]
  simp only [List.append_nil]

/--
VALUE BRIDGE.  The accepted same-block object's value is the accepted
`bpCandidateClose?` of the accepted `bpFringeCandGlobal` of the accepted
fold object's own best candidate — the composite the arm plus the
two-instruction epilogue produce.
-/
theorem sameBlockSeeded_value_eq
    (shape : Cartesian.CartesianShape) (store : ReadStore)
    (fringeSegment blockSize leftClose rightClose seed : Nat) :
    (bpChunkedSameBlockCloseSeededTraceResultAtSegmentWithStore
        shape store fringeSegment blockSize leftClose rightClose seed).value =
      bpCandidateClose?
        (bpFringeCandGlobal (sbBB shape blockSize leftClose) seed
          (sbStart leftClose)
          (sbFold shape store fringeSegment blockSize leftClose rightClose
            seed).value.2) := by
  simp only [bpChunkedSameBlockCloseSeededTraceResultAtSegmentWithStore,
    WordRAM.TraceResult.bind, WordRAM.TraceResult.map,
    WordRAM.TraceResult.pure]
  rw [route_windowBits_eq_windowBitsOfStore shape store blockSize leftClose]

/-! ## The whole same-block close arm -/

/-- Category log of the whole same-block arm: the fringe arm's own
route-indexed log followed by the epilogue's two unconditional ticks. -/
def sameBlockArmCats (shape : Cartesian.CartesianShape) (store : ReadStore)
    (fringeSegment blockSize leftClose rightClose seed : Nat) :
    List Category :=
  fringeArmCats store fringeSegment (sbChunkBits shape)
    (windowBitsOfStore store (sbBase shape blockSize leftClose))
    (sbRelLo shape blockSize leftClose)
    (sbRelHi shape blockSize leftClose rightClose)
    seed (sbCount shape blockSize leftClose rightClose) ++
    sameBlockCloseCats

/--
EXACT SIMULATION OF THE WHOLE SAME-BLOCK CLOSE ARM (97 instructions,
`A -> A + 97`).

The receipt is POSITIONALLY equal to the accepted same-block object's
`.trace`, and the result register `fRes` carries its `.value` — both
against the NAMED accepted object
`bpChunkedSameBlockCloseSeededTraceResultAtSegmentWithStore`
(`ChargedSameBlockTrace.lean:55`), at the route's own instantiation of the
window base, `relLo`, `relHi` and the derived 33-cap.

The value is computed from the machine's OWN charged reads: the window
bits entering the fold are `windowBitsOfStore`, the four words the
machine's four `readMem` instructions returned, not a copy of the spec.
-/
theorem sameBlockArm_runsTo
    (shape : Cartesian.CartesianShape) (store : ReadStore)
    {program : E1Machine.Program} {A L fringeSegment : Nat}
    (hc : sbChunkBits shape ≤ L)
    (hPro : HostedAt program A (fringeArmPrologue (sbChunkBits shape)))
    (hPre : HostedAt program (A + 21)
      (fringePrefix fringeSegment (sbChunkBits shape)))
    (hMrg : HostedAt program (A + 21 + 32) (fringeMerge (A + 21)))
    (hTail : HostedAt program (A + 21 + 45)
      (fringeShift (sbChunkBits shape) L ++ fringeAdvance))
    (hbr : program[A + 21 + 66]? = some (.brNZ fCnt (A + 21)))
    (hEpi : HostedAt program (A + 88) (fringeCandGlobal (A + 88)))
    (hCls : HostedAt program (A + 95) sameBlockClose)
    (blockSize leftClose rightClose seed : Nat)
    (h0 : (readBits store (sbBase shape blockSize leftClose)).length = L)
    (h1 : (readBits store (sbBase shape blockSize leftClose + 1)).length = L)
    (h2 : (readBits store (sbBase shape blockSize leftClose + 2)).length = L)
    (regs : RegFile)
    (hBase : regs fBase = sbBase shape blockSize leftClose)
    (hLo : regs fLo = sbRelLo shape blockSize leftClose)
    (hHi : regs fHi = sbRelHi shape blockSize leftClose rightClose)
    (hAcc : regs fAcc = seed)
    (hBB : regs fBB = sbBB shape blockSize leftClose)
    (hSeed : regs fSeed = seed)
    (hStart : regs fStart = sbStart leftClose) :
    ∃ regsF : RegFile,
      RunsTo store program ⟨regs, A, false⟩ ⟨regsF, A + 97, false⟩
        (bpChunkedSameBlockCloseSeededTraceResultAtSegmentWithStore
          shape store fringeSegment blockSize leftClose rightClose seed).trace
        (sameBlockArmCats shape store fringeSegment blockSize leftClose
          rightClose seed) ∧
      some (regsF fRes) =
        (bpChunkedSameBlockCloseSeededTraceResultAtSegmentWithStore
          shape store fringeSegment blockSize leftClose rightClose
          seed).value := by
  -- `fringeArm_runsTo` also delivers a preservation clause (M3d-9); this
  -- theorem's own conclusion does not restate it, so it is discarded here.
  obtain ⟨regsA, hrunA, hvalA, _hpresA⟩ :=
    fringeArm_runsTo store hc hPro hPre hMrg hTail hbr hEpi
      (sbBase shape blockSize leftClose) (sbBB shape blockSize leftClose)
      (sbRelLo shape blockSize leftClose)
      (sbRelHi shape blockSize leftClose rightClose) seed
      (sbStart leftClose) h0 h1 h2 regs hBase hLo hHi hAcc hBB hSeed hStart
  obtain ⟨regsF, hrunC, hresC, _hpresC⟩ :=
    sameBlockClose_runsTo store hCls regsA
  have htrans := RunsTo.trans hrunA hrunC
  have hpc : A + 95 + 2 = A + 97 := by omega
  rw [hpc] at htrans
  rw [sameBlockSeeded_trace_eq shape store fringeSegment blockSize leftClose
    rightClose seed]
  refine ⟨regsF, ?_, ?_⟩
  · simpa [sameBlockArmCats] using htrans
  · rw [sameBlockSeeded_value_eq shape store fringeSegment blockSize
      leftClose rightClose seed, <- hvalA, hresC]
    rfl

/-! ## The RANGE PREAMBLE (add/sub only)

`sameBlockArm_runsTo` also needs `fStart`, `fLo` and `fHi`.  Unlike the
address preamble, none of these needs a divisor: the route's own
`sbStart`/`sbRelLo`/`sbRelHi` are built from `+` and truncated `-` alone.

The instruction order below mirrors the route expressions LEFT TO RIGHT,
which matters because `Nat` subtraction is truncated: `sbRelHi` is
`leftClose + 1 + (rightClose - leftClose + 1) - 1 - base`, so the machine
must subtract `1` and then `base`, in that order, from the sum -- not
combine them.  Reassociating would change the value at the clamping
boundary, so the block is written to match the route syntactically.
-/

/-- The right close position the range preamble consumes. -/
abbrev fRight : Nat := 71

/-- The range preamble at base `Q` (eight instructions, exit `Q + 8`):
`fStart`, `fLo` and `fHi` from the two query operands and the window bit
base `fBB` that the address preamble has already computed. -/
def windowRange : List Instr :=
  [ .const fT 1             -- Q+0  the only immediate the block needs
  , .add fStart fClose fT   -- Q+1  start   = leftClose + 1
  , .sub fLo fStart fBB     -- Q+2  relLo   = start - base
  , .sub fU fRight fClose   -- Q+3            rightClose - leftClose
  , .add fU fU fT           -- Q+4  count   = that + 1
  , .add fHi fStart fU      -- Q+5            start + count
  , .sub fHi fHi fT         -- Q+6            ... - 1
  , .sub fHi fHi fBB ]      -- Q+7  relHi   = ... - base

@[simp] theorem windowRange_length : windowRange.length = 8 := rfl

/-- Category log of the range preamble: one register write and seven
unconditional arithmetic ticks.  No read, no branch. -/
def windowRangeCats : List Category :=
  [.registerWrite, .arithmetic, .arithmetic, .arithmetic, .arithmetic,
    .arithmetic, .arithmetic, .arithmetic]

/-- Constructor-exhaustive width certificate for the range preamble.  No
wildcard arm: every one of the eight instructions is discharged by its own
constructor's field conjunction. -/
theorem windowRange_fits (w : Nat) (hw : 71 < 2 ^ w) :
    ∀ instr ∈ windowRange, Instr.FieldsFit w instr := by
  intro instr hinstr
  have h1 : (1 : Nat) < 2 ^ w := by omega
  have h50 : (50 : Nat) < 2 ^ w := by omega
  have h51 : (51 : Nat) < 2 ^ w := by omega
  have h60 : (60 : Nat) < 2 ^ w := by omega
  have h61 : (61 : Nat) < 2 ^ w := by omega
  have h64 : (64 : Nat) < 2 ^ w := by omega
  have h66 : (66 : Nat) < 2 ^ w := by omega
  have h70 : (70 : Nat) < 2 ^ w := by omega
  have h71 : (71 : Nat) < 2 ^ w := hw
  simp only [windowRange, List.mem_cons, List.not_mem_nil, or_false]
    at hinstr
  rcases hinstr with h | h | h | h | h | h | h | h <;> subst h
  · exact ⟨h60, h1⟩
  · exact ⟨h66, h70, h60⟩
  · exact ⟨h50, h66, h64⟩
  · exact ⟨h61, h71, h70⟩
  · exact ⟨h61, h61, h60⟩
  · exact ⟨h51, h66, h61⟩
  · exact ⟨h51, h51, h60⟩
  · exact ⟨h51, h51, h64⟩

/-- Every range-preamble instruction is straight-line. -/
theorem windowRange_straight :
    ∀ instr ∈ windowRange, instr.isStraight = true := by
  intro instr hinstr
  simp only [windowRange, List.mem_cons, List.not_mem_nil, or_false]
    at hinstr
  rcases hinstr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

local macro "range_eval" : tactic =>
  `(tactic| straight_eval [windowRange, fT, fU, fLo, fHi, fStart, fClose,
      fRight, fBB])

/-- The range preamble writes only `fLo`, `fHi`, `fT`, `fU` and `fStart`.
Stated in NUMERALS, not the register abbrevs, so `omega` can use it. -/
abbrev WindowRangeUntouched (r : Nat) : Prop :=
  r ≠ 50 ∧ r ≠ 51 ∧ r ≠ 60 ∧ r ≠ 61 ∧ r ≠ 66

/-- Exact simulation of the range preamble: no receipt, eight ticks, and
the three range registers `sameBlockArm_runsTo` demands, computed from the
query operands by addition and truncated subtraction alone. -/
theorem windowRange_runsTo
    (store : ReadStore) {program : E1Machine.Program} {Q : Nat}
    (hHost : HostedAt program Q windowRange)
    (regs : RegFile) (leftClose rightClose base : Nat)
    (hClose : regs fClose = leftClose) (hRight : regs fRight = rightClose)
    (hBB : regs fBB = base) :
    ∃ regs' : RegFile,
      RunsTo store program ⟨regs, Q, false⟩ ⟨regs', Q + 8, false⟩ []
        windowRangeCats ∧
      regs' fStart = leftClose + 1 ∧
      regs' fLo = leftClose + 1 - base ∧
      regs' fHi =
        leftClose + 1 + (rightClose - leftClose + 1) - 1 - base ∧
      (∀ r, WindowRangeUntouched r → regs' r = regs r) := by
  have hrun := RunsTo.straight store windowRange windowRange_straight Q
    hHost regs
  obtain ⟨regsW, hregsW⟩ :
      ∃ x, straightRegs store windowRange regs = x := ⟨_, rfl⟩
  rw [hregsW] at hrun
  have hreads : straightReads store windowRange regs = [] := by range_eval
  have hcats : windowRange.map Instr.category = windowRangeCats := rfl
  rw [hreads, hcats] at hrun
  refine ⟨regsW, by simpa using hrun, ?_, ?_, ?_, ?_⟩
  · rw [<- hregsW]
    range_eval <;> simp [hClose]
  · rw [<- hregsW]
    range_eval <;> simp [hClose, hBB]
  · rw [<- hregsW]
    range_eval <;> simp [hClose, hRight, hBB]
  · intro r hr
    obtain ⟨h50, h51, h60, h61, h66⟩ := hr
    rw [<- hregsW]
    apply straightRegs_preserves
    intro i hi
    simp only [windowRange, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      straight_writes [fT, fU, fLo, fHi, fStart] <;> omega

/-- The range preamble's outputs ARE the route's own `sbStart`, `sbRelLo`
and `sbRelHi` at the accepted window bit base -- the exact three
hypotheses `sameBlockArm_runsTo` takes. -/
theorem windowRange_runsTo_route
    (shape : Cartesian.CartesianShape) (store : ReadStore)
    {program : E1Machine.Program} {Q blockSize : Nat}
    (hHost : HostedAt program Q windowRange)
    (regs : RegFile) (leftClose rightClose : Nat)
    (hClose : regs fClose = leftClose) (hRight : regs fRight = rightClose)
    (hBB : regs fBB = sbBB shape blockSize leftClose) :
    ∃ regs' : RegFile,
      RunsTo store program ⟨regs, Q, false⟩ ⟨regs', Q + 8, false⟩ []
        windowRangeCats ∧
      regs' fStart = sbStart leftClose ∧
      regs' fLo = sbRelLo shape blockSize leftClose ∧
      regs' fHi = sbRelHi shape blockSize leftClose rightClose ∧
      (∀ r, WindowRangeUntouched r → regs' r = regs r) :=
  windowRange_runsTo store hHost regs leftClose rightClose
    (sbBB shape blockSize leftClose) hClose hRight hBB

end E1SameBlockArm
end WordRAM
end RMQ
