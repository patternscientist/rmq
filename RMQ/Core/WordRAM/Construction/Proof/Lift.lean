import RMQ.Core.WordRAM.Construction.Conservative
import RMQ.Core.WordRAM.Construction.Calculus
import RMQ.Core.WordRAM.Packed.QueryStatic

/-! # PRE-1 join: lifted Conservative simulation of the accepted query (stage S8)

Coordinator ruling Q3 (c). `translatedQueryProgram` is the accepted
`PackedWordRAM.queryProgram` translated instruction by instruction through
`Conservative.instruction` (every operand fits 32 bits: the largest encoded
field is 8270 and the program length 837572). `translated_run` proves that from
the embedded state of any old state and any memory, the new interpreter runs the
translated program exactly as the old interpreter runs the query: the final
state is the embedded old final state and the step counts agree. This is a
simulation of the query on the detached emitted list, not an offset-relocated
execution inside the builder's memory (ruling Q3, recorded limit).
-/

namespace RMQ.SuccinctFinal.PackedConstruction

namespace Conservative

open RMQ.SuccinctFinal.PackedWordRAM (queryProgram querySource queryBudget)

theorem querySource_size_lt32 : querySource.size < 2 ^ 32 := by
  have h := PackedWordRAM.queryBudget_eq
  simp only [PackedWordRAM.querySource, PackedWordRAM.guardedBlock_size, PackedWordRAM.queryBudget] at h ⊢
  omega

/-- Every instruction of the accepted query fits 32-bit fields. -/
theorem queryProgram_fits32 : ∀ i ∈ queryProgram, i.Fits 32 := by
  intro instruction h
  change instruction ∈ querySource.compileAt 0 ++ [.halt 3] at h
  rcases List.mem_append.mp h with h | h
  · refine querySource.compile_fits 32 0 ?_ (by simpa using querySource_size_lt32) instruction h
    apply PackedWordRAM.Structured.Block.fieldsFit_of_maxEncodedField
    rw [PackedWordRAM.querySource_maxEncodedField]
    decide
  · simp only [List.mem_singleton] at h
    subst instruction
    intro operand hop
    simp [PackedWordRAM.Instruction.encoding, PackedWordRAM.Instruction.operands] at hop
    omega

instance (i : OldInstruction) : Decidable (OperandsFit32 i) := by
  unfold OperandsFit32; infer_instance

/-- Total translation; the fallback never occurs on the accepted query. -/
def translate (i : OldInstruction) : BInstr :=
  if h : OperandsFit32 i then ⟨instruction i h⟩ else ⟨.halt 0⟩

/-- The accepted query program in the construction instruction set. -/
def translatedQueryProgram : List BInstr := queryProgram.map translate

theorem translate_of_fits (i : OldInstruction) (h : OperandsFit32 i) : translate i = ⟨instruction i h⟩ := by
  simp [translate, h]

/-- **Lifted simulation.** -/
theorem translated_run (memory : PackedWordRAM.Memory) :
    ∀ (fuel : Nat) (s : OldState),
      (run translatedQueryProgram fuel (state memory s)).final =
        state memory (PackedWordRAM.run memory queryProgram fuel s).final ∧
      (run translatedQueryProgram fuel (state memory s)).steps =
        (PackedWordRAM.run memory queryProgram fuel s).steps := by
  intro fuel
  induction fuel with
  | zero => intro s; exact ⟨rfl, rfl⟩
  | succ fuel ih =>
      intro s
      cases hs : s.status with
      | halted v =>
          have hnew : stepProgram translatedQueryProgram (state memory s) = none := by
            apply stepProgram_none_of_stopped
            simp [state, hs, status]
          have hold : PackedWordRAM.step memory queryProgram s = none := by
            simp [PackedWordRAM.step, hs]
          simp only [run, hnew, PackedWordRAM.run, hold]
          exact ⟨trivial, rfl⟩
      | fault =>
          have hnew : stepProgram translatedQueryProgram (state memory s) = none := by
            apply stepProgram_none_of_stopped
            simp [state, hs, status]
          have hold : PackedWordRAM.step memory queryProgram s = none := by
            simp [PackedWordRAM.step, hs]
          simp only [run, hnew, PackedWordRAM.run, hold]
          exact ⟨trivial, rfl⟩
      | running =>
          cases hf : queryProgram[s.pc]? with
          | none =>
              have hnew : stepProgram translatedQueryProgram (state memory s) = none := by
                simp [stepProgram, fetch, translatedQueryProgram, state, hf]
              have hold : PackedWordRAM.step memory queryProgram s = none := by
                simp [PackedWordRAM.step, hs, hf]
              simp only [run, hnew, PackedWordRAM.run, hold]
              exact ⟨trivial, rfl⟩
          | some i =>
              have hfit : OperandsFit32 i :=
                operandsFit32_of_fits i (queryProgram_fits32 i (List.mem_of_getElem? hf))
              have hexec := execute_eq memory i hfit s hs
              have hnew : stepProgram translatedQueryProgram (state memory s) =
                  some ⟨state memory s, ⟨instruction i hfit⟩, state memory (PackedWordRAM.execute memory i s).1⟩ := by
                have hfetch : fetch translatedQueryProgram (state memory s) = some ⟨instruction i hfit⟩ := by
                  simp [fetch, translatedQueryProgram, state, hf, translate_of_fits i hfit]
                have hrun : (state memory s).status = .running := by simp [state, hs, status]
                simp only [stepProgram, hfetch, checkedStep, hrun, bstep, hexec]
              have hold : PackedWordRAM.step memory queryProgram s =
                  some ⟨s, i, (PackedWordRAM.execute memory i s).1, (PackedWordRAM.execute memory i s).2⟩ := by
                simp [PackedWordRAM.step, hs, hf]
              obtain ⟨h1, h2⟩ := ih (PackedWordRAM.execute memory i s).1
              simp only [run, hnew, PackedWordRAM.run, hold]
              exact ⟨h1, by simp only [Run.steps, PackedWordRAM.Run.steps, List.length_cons] at h2 ⊢; omega⟩

end Conservative

end RMQ.SuccinctFinal.PackedConstruction
