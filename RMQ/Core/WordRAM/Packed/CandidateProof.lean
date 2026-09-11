import RMQ.Core.WordRAM.Packed.InteriorSource
import RMQ.Core.WordRAM.Packed.Frame
import RMQ.Core.SuccinctClose.EndpointFringe.InteriorCandidate.Candidate

/-! # Register-level candidate semantics and leftmost ties -/

namespace RMQ.SuccinctFinal.PackedWordRAM

open Structured

def candidateOfRegs (base : Nat) (regs : Registers) : Option (Nat × Nat) :=
  if regs base = 0 then none else some (regs (base + 1), regs (base + 2))

theorem candidateNoneBlock_source (memory : Memory) (regs : Registers) :
    let actual := candidateNoneBlock.eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.reads = [] ∧
    candidateOfRegs 7000 actual.final.regs = none := by
  simp [candidateNoneBlock, Block.sequence, Block.eval, Action.eval,
    Action.instruction, execute, State.writeNext, Data.ofState,
    Registers.write, candidateOfRegs]

theorem candidateSaveBlock_source (base : Nat) (hb : base + 3 ≤ 7000)
    (memory : Memory) (regs : Registers) :
    let actual := (candidateSaveBlock base).eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.reads = [] ∧
    candidateOfRegs base actual.final.regs = candidateOfRegs 7000 regs ∧
    candidateOfRegs 7000 actual.final.regs = candidateOfRegs 7000 regs := by
  have h0 : 7000 ≠ base := by omega
  have h1 : 7001 ≠ base ∧ 7001 ≠ base + 1 := by omega
  have h2 : 7002 ≠ base ∧ 7002 ≠ base + 1 ∧ 7002 ≠ base + 2 := by omega
  simp [candidateSaveBlock, Block.sequence, Block.eval, Action.eval,
    Action.instruction, execute, State.writeNext, Data.ofState,
    Registers.write, candidateOfRegs, h0, h1.1, h1.2, h2.1, h2.2.1, h2.2.2,
    show 7000 ≠ base + 1 by omega, show 7000 ≠ base + 2 by omega,
    show 7001 ≠ base + 2 by omega]

theorem candidateRestoreBlock_source (base : Nat) (hb : base + 3 ≤ 7000)
    (memory : Memory) (regs : Registers) :
    let actual := (candidateRestoreBlock base).eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.reads = [] ∧
    candidateOfRegs 7000 actual.final.regs = candidateOfRegs base regs := by
  simp [candidateRestoreBlock, Block.sequence, Block.eval, Action.eval,
    Action.instruction, execute, State.writeNext, Data.ofState, Registers.write,
    candidateOfRegs, show base + 1 ≠ 7000 by omega,
    show base + 2 ≠ 7000 by omega, show base + 2 ≠ 7001 by omega]

theorem candidateMergeLeftBlock_source (base : Nat) (hb : base + 3 ≤ 7000)
    (memory : Memory) (regs : Registers) :
    let actual := (candidateMergeLeftBlock base).eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.reads = [] ∧
    candidateOfRegs 7000 actual.final.regs =
      SuccinctClose.bpCandidateMerge? (candidateOfRegs base regs) (candidateOfRegs 7000 regs) := by
  by_cases hl : regs base = 0
  · simp [candidateMergeLeftBlock, Block.eval, hl, candidateOfRegs,
      SuccinctClose.bpCandidateMerge?]
  · by_cases hr : regs 7000 = 0
    · simpa only [candidateMergeLeftBlock, Block.eval, hl, if_false, hr, if_true,
        candidateOfRegs, SuccinctClose.bpCandidateMerge?] using
        candidateRestoreBlock_source base hb memory regs
    · by_cases hbetter : regs 7001 < regs (base + 1)
      all_goals simp [candidateMergeLeftBlock, candidateRestoreBlock, Block.sequence,
        Block.eval, Action.eval, Action.instruction, execute, State.writeNext,
        Data.ofState, Registers.write, Comparison.eval, candidateOfRegs,
        SuccinctClose.bpCandidateMerge?, SuccinctClose.bpCandidateBetter, hl, hr, hbetter,
        show base ≠ 7003 by omega, show base + 1 ≠ 7003 by omega,
        show base + 2 ≠ 7003 by omega, show base + 1 ≠ 7000 by omega,
        show base + 2 ≠ 7000 by omega, show base + 2 ≠ 7001 by omega]

theorem candidateMergeLeftBlock_writesOnly (base : Nat) :
    (candidateMergeLeftBlock base).WritesOnly (fun r => 7000 ≤ r ∧ r < 7004) := by
  simp [candidateMergeLeftBlock, candidateRestoreBlock, Block.sequence,
    Block.WritesOnly, Action.destination]

theorem candidateMergeLeftBlock_frame (base : Nat) (memory : Memory) (s : Data)
    (r : Nat) (hr : r < 7000 ∨ 7004 ≤ r) :
    ((candidateMergeLeftBlock base).eval memory s).final.regs r = s.regs r :=
  Block.eval_frame memory _ _ (candidateMergeLeftBlock_writesOnly base) r (by omega) s

/-- Equal scores retain the earlier candidate, independently of positions. -/
theorem candidateMergeLeftBlock_tie (base score leftPosition rightPosition : Nat)
    (hb : base + 3 ≤ 7000) (memory : Memory) (regs : Registers)
    (hl : candidateOfRegs base regs = some (score, leftPosition))
    (hr : candidateOfRegs 7000 regs = some (score, rightPosition)) :
    candidateOfRegs 7000
      ((candidateMergeLeftBlock base).eval memory ⟨regs, .running⟩).final.regs =
      some (score, leftPosition) := by
  rw [(candidateMergeLeftBlock_source base hb memory regs).2.2, hl, hr]
  simp [SuccinctClose.bpCandidateMerge?, SuccinctClose.bpCandidateBetter]

end RMQ.SuccinctFinal.PackedWordRAM
