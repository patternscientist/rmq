import RMQ.Core.WordRAM.Packed.QueryCorrect

/-! # Direct observations of the fixed query run

These facts are stated on the actual primitive run rather than through the
total wrapper `queryNat` or the RC6 reference: a valid range returns the packet
of the independent `scanWindow` answer, no receipt of such a run lacks a reply,
and the endpoint guard rejects every invalid range in four or six steps.
-/

namespace RMQ.SuccinctFinal.PackedWordRAM

open Structured

/-- A raw load with no reply faults at once, and a stopped state takes no
further step. Hence a run that does not end in a fault logged no failed load. -/
theorem run_reads_reply_of_not_fault (memory : Memory) (program : Program) (fuel : Nat)
    (s : State) (h : (run memory program fuel s).final.status ≠ .fault) :
    ∀ receipt ∈ (run memory program fuel s).reads, ∃ value, receipt.reply = some value := by
  induction fuel generalizing s with
  | zero => simp [run, Run.reads]
  | succ fuel ih =>
      cases hs : step memory program s with
      | none => simp [run, hs, Run.reads]
      | some t =>
          have hrun : run memory program (fuel + 1) s =
              ⟨(run memory program fuel t.after).final,
                t :: (run memory program fuel t.after).transitions⟩ := by
            simp [run, hs]
          rw [hrun] at h ⊢
          intro receipt hmem
          have hrest : ∀ receipt ∈ (run memory program fuel t.after).reads,
              ∃ value, receipt.reply = some value := ih t.after h
          cases hr : t.receipt with
          | none =>
              simp only [Run.reads, List.filterMap_cons, hr] at hmem
              exact hrest receipt hmem
          | some first =>
              simp only [Run.reads, List.filterMap_cons, hr, List.mem_cons] at hmem
              rcases hmem with hmem | hmem
              · subst receipt
                cases hreply : first.reply with
                | some value => exact ⟨value, rfl⟩
                | none =>
                    exfalso
                    have he := (step_spec hs).2.2.2
                    obtain ⟨dst, addrReg, hi, haddr, hmissing⟩ :=
                      execute_receipt (memory := memory) (i := t.instruction) (s := s)
                        (by rw [he]; exact hr)
                    have hnone : memory[s.regs addrReg]? = none := by
                      rw [← haddr, ← hmissing, hreply]
                    rw [hi] at he
                    have hafter : t.after.status = .fault := by
                      have hfirst := congrArg Prod.fst he
                      simp only [execute, hnone] at hfirst
                      rw [← hfirst]
                    have hstop : run memory program fuel t.after = ⟨t.after, []⟩ :=
                      run_of_step_none memory program t.after fuel (by simp [step, hafter])
                    rw [hstop] at h
                    exact h hafter
              · exact hrest receipt hmem

private theorem getElem?_append_append (pre mid post : List Instruction) (k i : Nat)
    (hi : i = pre.length + mid.length + k) : (pre ++ (mid ++ post))[i]? = post[k]? := by
  subst hi
  rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
  congr 1
  omega

/-- The first instructions of every guarded program, and the two halts that
end its rejection branches. -/
private theorem guardedProgram_fetch (body : Block) :
    (guardedProgram body)[0]? = some (.constant 3 0) ∧
    (guardedProgram body)[1]? = some (.comparison .lt 4 0 1) ∧
    (guardedProgram body)[2]? = some (.branchZero 4 (body.size + 8)) ∧
    (guardedProgram body)[3]? = some (.comparison .le 5 1 2) ∧
    (guardedProgram body)[4]? = some (.branchZero 5 (body.size + 6)) ∧
    (guardedProgram body)[body.size + 6]? = some (.halt 3) ∧
    (guardedProgram body)[body.size + 8]? = some (.halt 3) := by
  have hshape : guardedProgram body =
      [.constant 3 0, .comparison .lt 4 0 1, .branchZero 4 (body.size + 8),
        .comparison .le 5 1 2, .branchZero 5 (body.size + 6)] ++
      (body.compileAt 5 ++ [.jump (body.size + 7), .halt 3, .jump (body.size + 9), .halt 3,
        .halt 3]) := by
    simp [guardedProgram, guardedBlock, Block.compileAt, Block.size, Action.instruction]
    omega
  rw [hshape]
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · refine (getElem?_append_append _ _ _ 1 _ ?_).trans rfl
    simp only [List.length_cons, List.length_nil, Block.compile_length]
    omega
  · refine (getElem?_append_append _ _ _ 3 _ ?_).trans rfl
    simp only [List.length_cons, List.length_nil, Block.compile_length]
    omega

private theorem run_steps_of_fetch {memory : Memory} {program : Program} {s : State}
    {i : Instruction} (fuel : Nat) (hs : s.status = .running) (hf : program[s.pc]? = some i) :
    (run memory program (fuel + 1) s).steps =
      (run memory program fuel (execute memory i s).1).steps + 1 := by
  simp [run, step, hs, hf, Run.steps]

private theorem run_steps_of_halted {memory : Memory} {program : Program} {s : State}
    (fuel value : Nat) (h : s.status = .halted value) :
    (run memory program fuel s).steps = 0 := by
  rw [run_of_halted memory program fuel s value h]
  rfl

/-- Exact rejection cost of the endpoint guard for every body and memory: four
steps when `left ≥ right`, six when `left < right` but `right > n`. -/
theorem guardedProgram_invalid_steps (body : Block) (memory : Memory) (n left right : Nat)
    (hinvalid : ¬ (left < right ∧ right ≤ n)) :
    (run memory (guardedProgram body) (body.size + 10) (initialState n left right)).steps =
      if left < right then 6 else 4 := by
  obtain ⟨h0, h1, h2, h3, h4, h6, h8⟩ := guardedProgram_fetch body
  let s0 := initialState n left right
  let s1 := (execute memory (.constant 3 0) s0).1
  let s2 := (execute memory (.comparison .lt 4 0 1) s1).1
  let s3 := (execute memory (.branchZero 4 (body.size + 8)) s2).1
  have hs2 : s2.regs 4 = if left < right then 1 else 0 := by
    simp [s2, s1, s0, execute, State.writeNext, Registers.write, Comparison.eval,
      initialState, inputRegisters]
  have r0 := run_steps_of_fetch (memory := memory) (s := s0) (body.size + 9) rfl h0
  have r1 := run_steps_of_fetch (memory := memory) (s := s1) (body.size + 8) rfl h1
  have r2 := run_steps_of_fetch (memory := memory) (s := s2) (body.size + 7) rfl h2
  rw [show body.size + 10 = body.size + 9 + 1 by omega, r0, r1, r2]
  by_cases hlt : left < right
  · have hle : ¬ right ≤ n := fun hle => hinvalid ⟨hlt, hle⟩
    have hpc3 : s3.pc = 3 := by
      simp only [s3, execute, hs2, if_pos hlt]
      rfl
    let s4 := (execute memory (.comparison .le 5 1 2) s3).1
    let s5 := (execute memory (.branchZero 5 (body.size + 6)) s4).1
    have hs4 : s4.regs 5 = 0 := by
      have hr1 : s3.regs 1 = right := by
        simp [s3, s2, s1, s0, execute, State.writeNext, Registers.write, initialState,
          inputRegisters]
      have hr2 : s3.regs 2 = n := by
        simp [s3, s2, s1, s0, execute, State.writeNext, Registers.write, initialState,
          inputRegisters]
      simp [s4, execute, State.writeNext, Registers.write, Comparison.eval, hr1, hr2, hle]
    have hpc4 : s4.pc = 4 := by
      simp [s4, execute, State.writeNext, hpc3]
    have hpc5 : s5.pc = body.size + 6 := by
      simp [s5, execute, hs4]
    have r3 := run_steps_of_fetch (memory := memory) (s := s3) (body.size + 6) rfl
      (by rw [hpc3]; exact h3)
    have r4 := run_steps_of_fetch (memory := memory) (s := s4) (body.size + 5) rfl
      (by rw [hpc4]; exact h4)
    have r5 := run_steps_of_fetch (memory := memory) (s := s5) (body.size + 4) rfl
      (by rw [hpc5]; exact h6)
    rw [show body.size + 7 = body.size + 6 + 1 by omega, r3,
      show body.size + 6 = body.size + 5 + 1 by omega, r4,
      show body.size + 5 = body.size + 4 + 1 by omega, r5,
      run_steps_of_halted (body.size + 4) (s5.regs 3) rfl, if_pos hlt]
  · have hpc3 : s3.pc = body.size + 8 := by
      simp [s3, execute, hs2, hlt]
    have r3 := run_steps_of_fetch (memory := memory) (s := s3) (body.size + 6) rfl
      (by rw [hpc3]; exact h8)
    rw [show body.size + 7 = body.size + 6 + 1 by omega, r3,
      run_steps_of_halted (body.size + 6) (s3.regs 3) rfl, if_neg hlt]

theorem queryRun_invalid_steps (memory : Memory) (n left right : Nat)
    (hinvalid : ¬ (left < right ∧ right ≤ n)) :
    (queryRun memory n left right).steps = if left < right then 6 else 4 :=
  guardedProgram_invalid_steps queryBody memory n left right hinvalid

/-- A valid range returns the packet of the independent leftmost-scan answer.
This is read off the run itself, not through the RC6 reference value. -/
theorem queryRun_scanWindow (xs : List Int) (left right : Nat) (hv : ValidRange xs left right) :
    (queryRun (buildMemory xs) xs.length left right).result =
      some (scanWindow xs left (right - left) + 1) := by
  have hnat := queryNat_exact xs left right
  rw [if_pos hv] at hnat
  simp only [queryNat, valid_inputs_encode xs.length left right hv.1 hv.2] at hnat
  have hres := queryRun_result xs left right
  unfold queryRun at hres ⊢
  rw [hres] at hnat ⊢
  generalize optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value = packet
    at hnat ⊢
  change (if packet = 0 then none else some (packet - 1)) = _ at hnat
  by_cases hp : packet = 0
  · rw [if_pos hp] at hnat
    cases hnat
  · rw [if_neg hp] at hnat
    have hv := Option.some.inj hnat
    rw [← hv, Nat.sub_add_cancel (Nat.pos_of_ne_zero hp)]

/-- No logged raw load of the fixed query lacks a reply, for every list and
endpoint pair, because the canonical run always halts. -/
theorem queryRun_reads_reply (xs : List Int) (left right : Nat) :
    ∀ receipt ∈ (queryRun (buildMemory xs) xs.length left right).reads,
      ∃ value, receipt.reply = some value := by
  have h := queryRun_halts xs left right
  unfold queryRun at h ⊢
  apply run_reads_reply_of_not_fault
  rw [h]
  simp

end RMQ.SuccinctFinal.PackedWordRAM
