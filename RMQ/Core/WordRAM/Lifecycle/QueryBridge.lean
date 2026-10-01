import RMQ.Core.WordRAM.Optimization.Query
import RMQ.Core.WordRAM.Construction.Proof.Lift

/-! # Exact compact-query translation

The existing conservative instruction translation preserves complete states,
ordered transitions and every attempted read. The embedding has canonical
numeric extent and empty key channels; lifecycle producers must establish
those facts before invoking this adapter.
-/

namespace RMQ.SuccinctFinal.PackedLifecycle.QueryBridge

open RMQ.SuccinctFinal
open PackedWordRAM PackedWordRAM.Structured PackedWordRAM.Optimization

theorem compact_fields32 : ∀ i ∈ compactQueryProgram, i.Fits 32 := by
  apply compactAt_fits compactQuerySource 32 compactQueryFresh 0 0
  · refine ⟨?_, ?_⟩
    · apply Block.fieldsFit_of_maxEncodedField
      rw [querySource_maxEncodedField]
      decide
    · change (Instruction.halt 3).Fits 32
      simp [Instruction.Fits, Instruction.encoding, Instruction.operands]
  · rw [compactQuery_maxCount]
    decide
  · decide
  · simp only [compactQueryFresh, queryRegisterCount_eq, compactQuery_depth]
    decide
  · rw [Nat.zero_add, compactQuerySize_eq]
    decide

theorem oversized_literal_rejected : ¬ (Instruction.constant 0 (2^32)).Fits 32 := by
  intro h
  have hbad := h (2^32) (by simp [Instruction.encoding, Instruction.operands])
  omega


open PackedConstruction PackedConstruction.Conservative

def liftTransition (memory : PackedWordRAM.Memory)
    (t : PackedWordRAM.Transition) : PackedConstruction.Transition :=
  ⟨state memory t.before, translate t.instruction, state memory t.after⟩

def readReply (t : PackedConstruction.Transition) : Option PackedWordRAM.Receipt :=
  match t.instruction.primitive with
  | .load _ address =>
      let a := t.before.regs address
      some ⟨a, if a < t.before.extent then t.before.memory a else none⟩
  | _ => none

theorem readReply_execute (memory : PackedWordRAM.Memory)
    (i : OldInstruction) (hi : OperandsFit32 i) (s : OldState) :
    readReply ⟨state memory s, translate i,
      state memory (PackedWordRAM.execute memory i s).1⟩ =
      (PackedWordRAM.execute memory i s).2 := by
  rw [translate_of_fits i hi]
  cases i with
  | load dst address =>
      simp only [readReply, instruction, state, PackedWordRAM.execute]
      by_cases ha : s.regs address < memory.length
      · simp [ha]
      · have hm : memory[s.regs address]? = none :=
          List.getElem?_eq_none_iff.mpr (by omega)
        simp [ha]
  | constant dst value => rfl
  | move dst src => rfl
  | arithmetic op dst lhs rhs => rfl
  | comparison op dst lhs rhs => rfl
  | jump target => rfl
  | jumpRegister src => rfl
  | branchZero condition target => rfl
  | halt src => rfl

theorem translated_run_all (memory : PackedWordRAM.Memory)
    (program : PackedWordRAM.Program)
    (fit : ∀ i ∈ program, OperandsFit32 i) :
    ∀ (fuel : Nat) (s : OldState),
      (PackedConstruction.run (program.map translate) fuel (state memory s)).final =
        state memory (PackedWordRAM.run memory program fuel s).final ∧
      (PackedConstruction.run (program.map translate) fuel (state memory s)).transitions =
        (PackedWordRAM.run memory program fuel s).transitions.map (liftTransition memory) ∧
      (PackedConstruction.run (program.map translate) fuel (state memory s)).transitions.filterMap readReply =
        (PackedWordRAM.run memory program fuel s).reads := by
  intro fuel
  induction fuel with
  | zero => intro s; exact ⟨rfl, rfl, rfl⟩
  | succ fuel ih =>
      intro s
      cases hs : s.status with
      | halted v =>
          have hnew : stepProgram (program.map translate) (state memory s) = none := by
            apply stepProgram_none_of_stopped
            simp [state, hs, status]
          have hold : PackedWordRAM.step memory program s = none := by
            simp [PackedWordRAM.step, hs]
          simp only [PackedConstruction.run, hnew, PackedWordRAM.run, hold]
          exact ⟨trivial, rfl, rfl⟩
      | fault =>
          have hnew : stepProgram (program.map translate) (state memory s) = none := by
            apply stepProgram_none_of_stopped
            simp [state, hs, status]
          have hold : PackedWordRAM.step memory program s = none := by
            simp [PackedWordRAM.step, hs]
          simp only [PackedConstruction.run, hnew, PackedWordRAM.run, hold]
          exact ⟨trivial, rfl, rfl⟩
      | running =>
          cases hf : program[s.pc]? with
          | none =>
              have hnew : stepProgram (program.map translate) (state memory s) = none := by
                simp [stepProgram, fetch, state, hf]
              have hold : PackedWordRAM.step memory program s = none := by
                simp [PackedWordRAM.step, hs, hf]
              simp only [PackedConstruction.run, hnew, PackedWordRAM.run, hold]
              exact ⟨trivial, rfl, rfl⟩
          | some i =>
              have hfit := fit i (List.mem_of_getElem? hf)
              have hexec := execute_eq memory i hfit s hs
              have hnew : stepProgram (program.map translate) (state memory s) =
                  some ⟨state memory s, ⟨instruction i hfit⟩,
                    state memory (PackedWordRAM.execute memory i s).1⟩ := by
                have hfetch : fetch (program.map translate) (state memory s) =
                    some ⟨instruction i hfit⟩ := by
                  simp [fetch, state, hf, translate_of_fits i hfit]
                have hrun : (state memory s).status = .running := by
                  simp [state, hs, status]
                simp only [stepProgram, hfetch, checkedStep, hrun, bstep, hexec]
              have hold : PackedWordRAM.step memory program s =
                  some ⟨s, i, (PackedWordRAM.execute memory i s).1,
                    (PackedWordRAM.execute memory i s).2⟩ := by
                simp [PackedWordRAM.step, hs, hf]
              obtain ⟨hfinal, htrace, hreads⟩ := ih (PackedWordRAM.execute memory i s).1
              simp only [PackedConstruction.run, hnew, PackedWordRAM.run, hold]
              refine ⟨hfinal, ?_, ?_⟩
              · simp only [List.map_cons, liftTransition, translate_of_fits i hfit]
                exact congrArg (fun tail => _ :: tail) htrace
              · simp only [PackedWordRAM.Run.reads] at hreads ⊢
                simp only [List.filterMap_cons]
                rw [hreads]
                have hr := readReply_execute memory i hfit s
                rw [translate_of_fits i hfit] at hr
                rw [hr]

theorem compact_translated_run (memory : PackedWordRAM.Memory) (fuel : Nat) (s : OldState) :
    (PackedConstruction.run (compactQueryProgram.map translate) fuel (state memory s)).final =
      state memory (PackedWordRAM.run memory compactQueryProgram fuel s).final ∧
    (PackedConstruction.run (compactQueryProgram.map translate) fuel (state memory s)).transitions =
      (PackedWordRAM.run memory compactQueryProgram fuel s).transitions.map (liftTransition memory) ∧
    (PackedConstruction.run (compactQueryProgram.map translate) fuel (state memory s)).transitions.filterMap readReply =
      (PackedWordRAM.run memory compactQueryProgram fuel s).reads :=
  translated_run_all memory compactQueryProgram
    (fun i hi => operandsFit32_of_fits i (compact_fields32 i hi)) fuel s

theorem translated_steps (memory : PackedWordRAM.Memory) (program : PackedWordRAM.Program)
    (fit : ∀ i ∈ program, OperandsFit32 i) (fuel : Nat) (s : OldState) :
    (PackedConstruction.run (program.map translate) fuel (state memory s)).steps =
      (PackedWordRAM.run memory program fuel s).steps := by
  have h := congrArg List.length (translated_run_all memory program fit fuel s).2.1
  simpa only [PackedConstruction.Run.steps, PackedWordRAM.Run.steps, List.length_map] using h


end RMQ.SuccinctFinal.PackedLifecycle.QueryBridge
