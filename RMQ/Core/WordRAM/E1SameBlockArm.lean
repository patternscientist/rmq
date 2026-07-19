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
  obtain ⟨regsA, hrunA, hvalA⟩ :=
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

end E1SameBlockArm
end WordRAM
end RMQ
