import RMQ.Core.WordRAM.Packed.Primitive

/-! # Array-indexed evaluation of the primitive machine

`run` fetches each instruction from a `List`, which costs time linear in the
program counter when the evaluator is executed. `runArray` fetches from an
`Array` and is otherwise the same definition. The equality theorem below makes
it an exact stand-in for `run` in executable validation; it is not used by any
proof of the query contract.
-/

namespace RMQ.SuccinctFinal.PackedWordRAM

def stepArray (memory : Memory) (program : Array Instruction) (s : State) : Option Transition :=
  match s.status with
  | .running =>
      match program[s.pc]? with
      | none => none
      | some i =>
          let result := execute memory i s
          some ⟨s, i, result.1, result.2⟩
  | _ => none

def runArray (memory : Memory) (program : Array Instruction) : Nat → State → Run
  | 0, s => ⟨s, []⟩
  | fuel + 1, s =>
      match stepArray memory program s with
      | none => ⟨s, []⟩
      | some t =>
          let rest := runArray memory program fuel t.after
          ⟨rest.final, t :: rest.transitions⟩

theorem stepArray_toArray (memory : Memory) (program : Program) (s : State) :
    stepArray memory program.toArray s = step memory program s := by
  unfold stepArray step
  cases s.status with
  | running =>
      rw [List.getElem?_toArray]
      cases program[s.pc]? <;> rfl
  | halted _ => rfl
  | fault => rfl

/-- The array evaluator returns the same run, with every transition, receipt,
final state and step, as `run` on the same list program. -/
theorem runArray_toArray (memory : Memory) (program : Program) (fuel : Nat) (s : State) :
    runArray memory program.toArray fuel s = run memory program fuel s := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
      simp only [runArray, run, stepArray_toArray]
      cases step memory program s with
      | none => rfl
      | some t => simp only [ih]

end RMQ.SuccinctFinal.PackedWordRAM
