import RMQ.Core.WordRAM.Construction.Calculus

/-! # The run-level header-use certificate (contract amendment AMEND-1)

`reserve` exposes `extent = n + 1` in the word model, so a program could
recover the input length without ever reading cell 0. The accepted builder
therefore carries `HeaderUse`, a checked certificate on the ACTUAL accepted
runs: the program starts with the header load, no other instruction writes
register 1, the header-removed run faults after exactly one transition with no
writes, no reservations and unchanged extent (both models, every input
including `[]`, every fuel at least 1), the first transition of the intact run
is the header load moving `xs.length` into register 1 (both models), and the
comparison model's numeric extent is one, so no reservation can reveal `n`
there. The five run-level fields carry default proofs derived from the two
syntactic fields through the generic header lemmas of the calculus, so the
certificate of a closed program constant is discharged by two decidable facts.
This module is a consumer of the execution calculus, outside the operational
closure.
-/

namespace RMQ.SuccinctFinal.PackedConstruction

/-- The intact word-model run starts with the header load. -/
theorem wordHeaderReceipt_of_head (program : List BInstr)
    (hhead : program[0]? = some headerInstruction) (width : Nat) (xs : List Int) (fuel : Nat)
    (hf : 1 ≤ fuel) :
    ∃ t : Transition, (run program fuel (wordInputState width xs)).transitions[0]? = some t ∧
      t.instruction = headerInstruction ∧ t.before.regs 1 = 0 ∧
      t.after.regs 1 = xs.length ∧ t.after.status = .running := by
  obtain ⟨t, h0, hi, hb, hr, hst, _, _⟩ := run_header_first program hhead (wordInputState width xs)
    rfl rfl rfl xs.length (by simp [wordInputState]) (by simp [wordInputState, inputCellCount])
    fuel hf
  exact ⟨t, h0, hi, by rw [hb]; rfl, hr, hst⟩

/-- The intact comparison-model run starts with the header load. -/
theorem comparisonHeaderReceipt_of_head (program : List BInstr)
    (hhead : program[0]? = some headerInstruction) (xs : List Int) (fuel : Nat) (hf : 1 ≤ fuel) :
    ∃ t : Transition, (run program fuel (comparisonInputState xs)).transitions[0]? = some t ∧
      t.instruction = headerInstruction ∧ t.before.regs 1 = 0 ∧
      t.after.regs 1 = xs.length ∧ t.after.status = .running := by
  obtain ⟨t, h0, hi, hb, hr, hst, _, _⟩ := run_header_first program hhead (comparisonInputState xs)
    rfl rfl rfl xs.length (by simp [comparisonInputState]) (by simp [comparisonInputState])
    fuel hf
  exact ⟨t, h0, hi, by rw [hb]; rfl, hr, hst⟩

structure HeaderUse (program : List BInstr) : Prop where
  headerFirst : program[0]? = some headerInstruction
  tailNeverWritesR1 : ∀ i ∈ program.tail, WritesOnly (fun r => r ≠ 1) i
  wordMissingHeaderFault : ∀ (width : Nat) (xs : List Int) (fuel : Nat), 1 ≤ fuel →
    (run program fuel
      { wordInputState width xs with memory := put (encodeInput width xs) 0 none }).final.status =
        .fault ∧
    (run program fuel
      { wordInputState width xs with memory := put (encodeInput width xs) 0 none }).steps = 1 ∧
    (run program fuel
      { wordInputState width xs with memory := put (encodeInput width xs) 0 none }).writes = [] ∧
    (run program fuel
      { wordInputState width xs with memory := put (encodeInput width xs) 0 none }).reserves = [] ∧
    (run program fuel
      { wordInputState width xs with memory := put (encodeInput width xs) 0 none }).final.extent =
        (wordInputState width xs).extent :=
    fun width xs fuel hf => run_missing_header program headerFirst
      { wordInputState width xs with memory := put (encodeInput width xs) 0 none }
      rfl rfl rfl (by simp [put]) fuel hf
  comparisonMissingHeaderFault : ∀ (xs : List Int) (fuel : Nat), 1 ≤ fuel →
    (run program fuel
      { comparisonInputState xs with
        memory := put (comparisonInputState xs).memory 0 none }).final.status = .fault ∧
    (run program fuel
      { comparisonInputState xs with
        memory := put (comparisonInputState xs).memory 0 none }).steps = 1 ∧
    (run program fuel
      { comparisonInputState xs with
        memory := put (comparisonInputState xs).memory 0 none }).writes = [] ∧
    (run program fuel
      { comparisonInputState xs with
        memory := put (comparisonInputState xs).memory 0 none }).reserves = [] ∧
    (run program fuel
      { comparisonInputState xs with
        memory := put (comparisonInputState xs).memory 0 none }).final.extent =
        (comparisonInputState xs).extent :=
    fun xs fuel hf => run_missing_header program headerFirst
      { comparisonInputState xs with memory := put (comparisonInputState xs).memory 0 none }
      rfl rfl rfl (by simp [put]) fuel hf
  wordHeaderReceipt : ∀ (width : Nat) (xs : List Int) (fuel : Nat), 1 ≤ fuel →
    ∃ t : Transition, (run program fuel (wordInputState width xs)).transitions[0]? = some t ∧
      t.instruction = headerInstruction ∧ t.before.regs 1 = 0 ∧
      t.after.regs 1 = xs.length ∧ t.after.status = .running :=
    wordHeaderReceipt_of_head program headerFirst
  comparisonHeaderReceipt : ∀ (xs : List Int) (fuel : Nat), 1 ≤ fuel →
    ∃ t : Transition, (run program fuel (comparisonInputState xs)).transitions[0]? = some t ∧
      t.instruction = headerInstruction ∧ t.before.regs 1 = 0 ∧
      t.after.regs 1 = xs.length ∧ t.after.status = .running :=
    comparisonHeaderReceipt_of_head program headerFirst
  oracleExtentOne : ∀ xs : List Int, (comparisonInputState xs).extent = 1 := fun _ => rfl

/-- The certificate of a program follows from the two syntactic facts: the
header load is first and no later instruction writes register 1. Both are
decidable on a closed program constant. The `trivial` fallbacks below never
fire on the real field types; they exist so that the registry's field-weakening
mutations reach the exact-type consumer instead of stopping at this
initializer (the load-bearing pins live in `scripts/preprocessing_builder_check.lean`). -/
theorem headerUse_of_program (program : List BInstr)
    (hhead : program[0]? = some headerInstruction)
    (htail : ∀ i ∈ program.tail, WritesOnly (fun r => r ≠ 1) i) : HeaderUse program :=
  { headerFirst := by first | exact hhead | trivial
    tailNeverWritesR1 := by first | exact htail | trivial }

/-- Register 1 is written only by the header load: along any run of a program
whose tail never writes register 1, as long as the program counter never
returns to 0, the value in register 1 persists. The stage proofs establish the
"never returns to 0" part through the compiler theorem (compiled code hosted
from base 1 has no target 0); here only the tail frame is packaged. -/
theorem tail_frame_of_never_writes {program : List BInstr}
    (htail : ∀ i ∈ program.tail, WritesOnly (fun r => r ≠ 1) i) (fuel : Nat)
    (s : State) (hpc : ∀ k, k ≤ fuel → (run program k s).final.pc ≠ 0) :
    (run program fuel s).final.regs 1 = s.regs 1 := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
      cases hs : stepProgram program s with
      | none => simp [run, hs]
      | some t =>
          obtain ⟨hb, _, hf, he⟩ := step_spec hs
          subst hb
          have hpc0 : t.before.pc ≠ 0 := by simpa using hpc 0 (Nat.zero_le _)
          have hmem : t.instruction ∈ program.tail := by
            obtain ⟨m, hm⟩ : ∃ m, t.before.pc = m + 1 :=
              ⟨t.before.pc - 1, by omega⟩
            rw [hm] at hf
            have : program.tail[m]? = some t.instruction := by
              rw [List.getElem?_tail]; exact hf
            exact List.mem_of_getElem? this
          have hframe : t.after.regs 1 = t.before.regs 1 := by
            rw [he]
            exact execPrim_frame _ _ (fun r => r ≠ 1) (htail t.instruction hmem) 1 (by simp)
          have hrest := ih t.after (fun k hk => by
            have := hpc (k + 1) (by omega)
            simpa [run, hs] using this)
          simpa [run, hs] using hrest.trans hframe

end RMQ.SuccinctFinal.PackedConstruction
