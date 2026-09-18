import RMQ.Core.WordRAM.Construction.Proof.RunFacts

/-! # Static facts of the two builder constants

For every instruction of `builderProgram` and `builderProgramWord`, executed or
dormant: operands fit every `wordWidth n`, register operands are below 400,
branch and jump targets are below the program length, and no `jumpRegister`
occurs. The per-transition `Run.Safe` facts of the executed runs are in
`Proof/RunFacts.lean`. -/

namespace RMQ.SuccinctFinal.PackedConstruction.Structured

/-- Every control target of a compiled block, executed or dormant, stays within
its hosted range, and no `jumpRegister` is emitted. -/
theorem Block.compile_targets (block : Block) : ∀ base, base + block.size < 2 ^ 32 →
    ∀ i ∈ block.compileAt base,
      (∀ c t, i.primitive = .branchZero c t → t.val ≤ base + block.size) ∧
      (∀ t, i.primitive = .jump t → t.val ≤ base + block.size) ∧
      (∀ src, i.primitive ≠ .jumpRegister src) := by
  induction block with
  | skip => intro base _ i hi; simp [Block.compileAt] at hi
  | action op =>
      intro base _ i hi
      simp only [Block.compileAt, List.mem_singleton] at hi
      subst hi
      obtain ⟨hj, hjr, hb, _⟩ := Action.prim_not_control op
      exact ⟨fun c t h => absurd h (hb c t), fun t h => absurd h (hj t), hjr⟩
  | exit src =>
      intro base _ i hi
      simp only [Block.compileAt, List.mem_singleton] at hi
      subst hi
      exact ⟨fun c t h => (by cases h), fun t h => (by cases h), fun s h => (by cases h)⟩
  | seq a b iha ihb =>
      intro base hbound i hi
      simp only [Block.size] at hbound
      rcases List.mem_append.mp (by simpa [Block.compileAt] using hi) with hi | hi
      · obtain ⟨h1, h2, h3⟩ := iha base (by omega) i hi
        refine ⟨fun c t h => ?_, fun t h => ?_, h3⟩
        · have := h1 c t h; simp only [Block.size]; omega
        · have := h2 t h; simp only [Block.size]; omega
      · obtain ⟨h1, h2, h3⟩ := ihb (base + a.size) (by omega) i hi
        refine ⟨fun c t h => ?_, fun t h => ?_, h3⟩
        · have := h1 c t h; simp only [Block.size]; omega
        · have := h2 t h; simp only [Block.size]; omega
  | ifZero cond zero nonzero ihz ihn =>
      intro base hbound i hi
      simp only [Block.size] at hbound
      simp only [Block.compileAt, List.mem_append, List.mem_singleton] at hi
      rcases hi with ((rfl | hi) | rfl) | hi
      · refine ⟨fun c t h => ?_, fun t h => (by cases h), fun s h => (by cases h)⟩
        simp only [Prim.branchZero.injEq] at h
        obtain ⟨_, rfl⟩ := h
        rw [fin_val_of_lt (by omega)]; simp only [Block.size]; omega
      · obtain ⟨h1, h2, h3⟩ := ihn (base + 1) (by omega) i hi
        refine ⟨fun c t h => ?_, fun t h => ?_, h3⟩
        · have := h1 c t h; simp only [Block.size]; omega
        · have := h2 t h; simp only [Block.size]; omega
      · refine ⟨fun c t h => (by cases h), fun t h => ?_, fun s h => (by cases h)⟩
        simp only [Prim.jump.injEq] at h
        subst h
        rw [fin_val_of_lt (by omega)]; simp only [Block.size]; omega
      · obtain ⟨h1, h2, h3⟩ := ihz (base + 1 + nonzero.size + 1) (by omega) i hi
        refine ⟨fun c t h => ?_, fun t h => ?_, h3⟩
        · have := h1 c t h; simp only [Block.size]; omega
        · have := h2 t h; simp only [Block.size]; omega
  | loop cond body ih =>
      intro base hbound i hi
      simp only [Block.size] at hbound
      simp only [Block.compileAt, List.mem_append, List.mem_singleton] at hi
      rcases hi with (rfl | hi) | rfl
      · refine ⟨fun c t h => ?_, fun t h => (by cases h), fun s h => (by cases h)⟩
        simp only [Prim.branchZero.injEq] at h
        obtain ⟨_, rfl⟩ := h
        rw [fin_val_of_lt (by omega)]; simp only [Block.size]; omega
      · obtain ⟨h1, h2, h3⟩ := ih (base + 1) (by omega) i hi
        refine ⟨fun c t h => ?_, fun t h => ?_, h3⟩
        · have := h1 c t h; simp only [Block.size]; omega
        · have := h2 t h; simp only [Block.size]; omega
      · refine ⟨fun c t h => (by cases h), fun t h => ?_, fun s h => (by cases h)⟩
        simp only [Prim.jump.injEq] at h
        subst h
        rw [fin_val_of_lt (by omega)]; simp only [Block.size]; omega

end RMQ.SuccinctFinal.PackedConstruction.Structured

namespace RMQ.SuccinctFinal.PackedConstruction.Proof

open Structured

/-- Static facts of a compiled builder source followed by `halt 3`, at every
word width at least 32: every operand fits, every register operand is below
400, every branch or jump target is inside the program, and there is no
`jumpRegister`. -/
theorem program_static (leaf : Block) (hsz : (builderSource leaf).size = 2106)
    (hrb : ∀ i ∈ (builderSource leaf).compileAt 0 ++ [(⟨.halt 3⟩ : BInstr)], i.primitive.RegistersBelow 400)
    (W : Nat) (hW : 32 ≤ W) :
    ∀ i ∈ (builderSource leaf).compileAt 0 ++ [(⟨.halt 3⟩ : BInstr)],
      i.primitive.OperandsFit W ∧ i.primitive.RegistersBelow 400 ∧
      (∀ c t, i.primitive = .branchZero c t → t.val < 2107) ∧
      (∀ t, i.primitive = .jump t → t.val < 2107) ∧
      (∀ src, i.primitive ≠ .jumpRegister src) := by
  intro i hi
  refine ⟨Prim.operandsFit_of_width _ hW, hrb i hi, ?_⟩
  rcases List.mem_append.mp hi with hi | hi
  · obtain ⟨h1, h2, h3⟩ := Block.compile_targets (builderSource leaf) 0 (by rw [hsz]; decide) i hi
    exact ⟨fun c t h => by have := h1 c t h; rw [hsz] at this; omega,
      fun t h => by have := h2 t h; rw [hsz] at this; omega, h3⟩
  · simp only [List.mem_singleton] at hi
    subst hi
    exact ⟨fun c t h => (by cases h), fun t h => (by cases h), fun s h => (by cases h)⟩

theorem builderProgram_static (n : Nat) :
    ∀ i ∈ builderProgram, i.primitive.OperandsFit (PackedWordRAM.wordWidth n) ∧
      i.primitive.RegistersBelow 400 ∧
      (∀ c t, i.primitive = .branchZero c t → t.val < builderProgram.length) ∧
      (∀ t, i.primitive = .jump t → t.val < builderProgram.length) ∧
      (∀ src, i.primitive ≠ .jumpRegister src) := by
  rw [builderProgram_length_eq]
  exact program_static keyLeaf builderSource_size_keyLeaf_eq builderProgram_registersBelow _ (wordWidth_ge_32 n)

theorem builderProgramWord_static (n : Nat) :
    ∀ i ∈ builderProgramWord, i.primitive.OperandsFit (PackedWordRAM.wordWidth n) ∧
      i.primitive.RegistersBelow 400 ∧
      (∀ c t, i.primitive = .branchZero c t → t.val < builderProgramWord.length) ∧
      (∀ t, i.primitive = .jump t → t.val < builderProgramWord.length) ∧
      (∀ src, i.primitive ≠ .jumpRegister src) := by
  rw [builderProgramWord_length_eq]
  exact program_static wordLeaf builderSource_size_wordLeaf_eq builderProgramWord_registersBelow _ (wordWidth_ge_32 n)

end RMQ.SuccinctFinal.PackedConstruction.Proof
