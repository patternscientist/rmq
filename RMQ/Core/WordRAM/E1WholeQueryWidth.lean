import RMQ.Core.WordRAM.E1ReviewerWidth
import RMQ.Core.WordRAM.E1WholeQueryProgram

/-!
# The EXECUTED program's width story (E1-LaneM)

REQ-E1-02 asks for two things about the program the agreement actually runs:
a certificate that every instruction fits the modeled width, and an
anti-vacuity witness that the width DISCRIMINATES.  `E1ReviewerWidth.lean`
supplies both — but for `assembledValidPath`, which is NOT the executed
program.

## Which program is executed, and why the existing pair is about another one

`wholeQueryMachineAgrees_of_bounds` (`E1WholeQueryAgreement.lean:68`) runs
`programSkeleton n (wholeQueryValidPath shape wholeQueryNoneExit)`, which is
`wholeQueryProgram shape n` by definition (`E1WholeQueryProgram.lean:878`).
`assembledValidPath` (`E1ReviewerWidth.lean:249`) has twelve line-hits, ALL
inside `E1ReviewerWidth.lean`, and passes `interior = []`; the two are
siblings under one `programSkeleton`, of lengths `547` and `5636`, related by
no lemma.

## What this module supplies, and what it does not

The REJECTION half is here and is about the executed program.  The POSITIVE
half is NOT here: it needs `canonicalInteriorDispatchBlock_fits`,
`selectCloseBlockAt_fits` and the close/LCA composition, none of which exist
yet.  See `E1_LIVE_STATE.md` §17.  Nothing in this module is stated
conditionally on those, because a premise with no witness is exactly what
this campaign has been paying down.

**The executed program does fit** — that is settled by evaluation, not
assumed: at `shape.size = 0/1/5/40/64/300` the largest field any of the
`5646` instructions encodes is `5644` at EVERY size, against reviewer
envelopes `2 ^ 19 = 524288` through `2 ^ 27`, with zero `divConst` zero
divisors.  The binding field is `wholeQueryNoneExit` itself, a branch target
fixed by the program's own length.  DD-20260719-264.
-/

namespace RMQ
namespace WordRAM
namespace E1WholeQueryWidth

open E1Machine
open E1Query
open RMQ.SuccinctClose
open E1ReviewerWidth

/-- The guard's invalid-exit branch of the EXECUTED program carries the target
`5644`, and that instruction really is in the program.  `5644` is
`8 + (wholeQueryValidPath shape wholeQueryNoneExit).length`, the skeleton's
own invalid-exit base, which is also `wholeQueryNoneExit`
(`E1WholeQueryProgram.lean:532`).  Named because the refutation turns on it. -/
theorem wholeQueryInvalidBranch_mem (shape : Cartesian.CartesianShape)
    (n : Nat) :
    Instr.brNZ regG 5644 ∈ wholeQueryProgram shape n := by
  simp [wholeQueryProgram, programSkeleton, guardBlock]

/--
**THE SIZE-INDEXED WIDTH IS REFUTED FOR THE PROGRAM THAT ACTUALLY EXECUTES.**

At `SuccinctRank.machineWordBits shape.size` the executed program does NOT
fit, for every shape of size at most `2821`.  The witness is the guard's own
invalid-exit branch `brNZ regG 5644`: its target field is `5644`, while the
modeled bound `2 ^ machineWordBits shape.size` is at most `2 * shape.size + 2`
(`two_pow_machineWordBits_le`), hence at most `5644` on that window.

This is the anti-vacuity witness REQ-E1-02's column demands FOR THE EXECUTED
PROGRAM. `programSkeleton_not_fits_machineWordBits` (`E1ReviewerWidth.lean:399`)
is the same statement about `assembledValidPath`, whose corresponding constant
is `555` and whose window is `<= 255`; neither implies the other, since the two
programs are related by no lemma.

The bound `2821` is an artifact of how cheaply the refutation can be stated,
not of where the failure stops: past it the binding field becomes
`2 ^ machineWordBits shape.bpCode.length` with
`shape.bpCode.length = 2 * shape.size`, which outruns
`2 ^ machineWordBits shape.size` at every size.  Only the `<= 2821` window is
machine-checked here.

Note this is quantified over EVERY `n`, not just `n = shape.size`: the guard's
branch target does not depend on the size constant the guard loads.
-/
theorem wholeQueryProgram_not_fits_machineWordBits
    (shape : Cartesian.CartesianShape) (n : Nat)
    (hsmall : shape.size <= 2821) :
    ¬ ProgramFits (SuccinctRank.machineWordBits shape.size)
        (wholeQueryProgram shape n) := by
  intro hfits
  have hmem := wholeQueryInvalidBranch_mem shape n
  have hfield := hfits _ hmem
  have hbound : 5644 < 2 ^ SuccinctRank.machineWordBits shape.size := by
    simpa [Instr.FieldsFit] using hfield.2
  have hle := two_pow_machineWordBits_le shape.size
  omega

end E1WholeQueryWidth
end WordRAM
end RMQ
