import RMQ.Core.WordRAM.Optimization.Compact
import RMQ.Core.WordRAM.Packed.Scratch

/-!
# Literal compact code fields and finite register storage

The count inventory is separate from the baseline source-field inventory,
which erases repeat counts. Static fit covers every emitted instruction,
including dormant branches, and the register frame covers every actual fuel
prefix. These facts do not assert runtime arithmetic or query correctness.
-/

namespace RMQ.SuccinctFinal.PackedWordRAM.Optimization

open Structured

/-- Conservative maximum over every source repeat literal, including dormant
syntax. No source immediate, register, or PC is substituted for a loop count. -/
def compactMaxCount : Block → Nat
  | .skip | .action _ | .exit _ => 0
  | .seq a b | .ifZero _ a b => max (compactMaxCount a) (compactMaxCount b)
  | .repeat count body => max count (compactMaxCount body)

/-- Exact literal serialized-word count; loop wrappers have lengths
3, 3, 3, 5 and 2 in their actual emitted order. -/
def compactEncodingWords : Block → Nat
  | .skip => 0
  | .action op => op.instruction.encoding.length
  | .exit _ => 2
  | .seq a b => compactEncodingWords a + compactEncodingWords b
  | .ifZero _ zero nonzero => 5 + compactEncodingWords nonzero + compactEncodingWords zero
  | .repeat 0 _ => 0
  | .repeat (_ + 1) body => 16 + compactEncodingWords body

theorem instruction_writesOnly_mono (instruction : Instruction) {small large : Nat → Prop}
    (writes : instruction.WritesOnly small) (subset : ∀ r, small r → large r) :
    instruction.WritesOnly large := by
  cases instruction <;> first | exact subset _ writes | trivial

/-- Every actual emitted write lies in the original source bank or one of the
two explicitly charged registers per active syntactic loop depth. -/
theorem compactAt_writesOnly (block : Block) (fresh depth base : Nat)
    (bounded : BlockRegistersBelow fresh block) :
    ∀ instruction ∈ compactAt block fresh depth base,
      instruction.WritesOnly (fun r => r < fresh + 2 * (depth + compactDepth block)) := by
  induction block generalizing depth base with
  | skip => simp [compactAt]
  | action op =>
      intro instruction hi
      have hd := ActionRegistersBelow.destination bounded
      simp only [compactAt, List.mem_singleton] at hi
      subst instruction
      cases op <;> simp only [Action.instruction, Instruction.WritesOnly, compactDepth,
        Action.destination] at hd ⊢ <;> omega
  | exit src => simp [compactAt, Instruction.WritesOnly]
  | seq a b iha ihb =>
      intro instruction hi
      rcases List.mem_append.mp hi with hi | hi
      · apply instruction_writesOnly_mono instruction (iha depth base bounded.1 instruction hi)
        intro r hr
        have h := Nat.le_max_left (compactDepth a) (compactDepth b)
        simp only [compactDepth]
        omega
      · apply instruction_writesOnly_mono instruction
          (ihb depth (base + compactSize a) bounded.2 instruction hi)
        intro r hr
        have h := Nat.le_max_right (compactDepth a) (compactDepth b)
        simp only [compactDepth]
        omega
  | ifZero condition zero nonzero ihz ihn =>
      intro instruction hi
      simp only [compactAt, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with ((rfl | hi) | rfl) | hi
      · trivial
      · apply instruction_writesOnly_mono instruction (ihn depth _ bounded.2.2 instruction hi)
        intro r hr
        have h := Nat.le_max_right (compactDepth zero) (compactDepth nonzero)
        simp only [compactDepth]
        omega
      · trivial
      · apply instruction_writesOnly_mono instruction (ihz depth _ bounded.2.1 instruction hi)
        intro r hr
        have h := Nat.le_max_left (compactDepth zero) (compactDepth nonzero)
        simp only [compactDepth]
        omega
  | «repeat» count body ih =>
      cases count with
      | zero => simp [compactAt]
      | succ count =>
          intro instruction hi
          simp only [compactAt, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with ((rfl | rfl | rfl) | hi) | (rfl | rfl)
          · simp only [Instruction.WritesOnly, compactDepth, compactCounter]; omega
          · simp only [Instruction.WritesOnly, compactDepth, compactCounter]; omega
          · trivial
          · apply instruction_writesOnly_mono instruction (ih (depth + 1) _ bounded instruction hi)
            intro r hr
            simp only [compactDepth]
            omega
          · simp only [Instruction.WritesOnly, compactDepth, compactCounter]; omega
          · trivial

/-- Every fuel prefix is framed, with no assumption on starting PC, status,
memory replies or query validity. Only destinations of actual code are used. -/
theorem compact_run_frame (memory : Memory) (block : Block) (fresh depth base fuel : Nat)
    (bounded : BlockRegistersBelow fresh block) (state : State) (r : Nat)
    (outside : fresh + 2 * (depth + compactDepth block) ≤ r) :
    (run memory (compactAt block fresh depth base) fuel state).final.regs r = state.regs r :=
  run_frame memory (compactAt block fresh depth base) fuel state _
    (compactAt_writesOnly block fresh depth base bounded) r (by omega)

/-- The scratch writes also have a lower bound: enclosing loop counters lie
between the original source bank and this compilation depth's first pair. -/
theorem compactAt_writesOnly_interval (block : Block) (fresh depth base : Nat)
    (bounded : BlockRegistersBelow fresh block) :
    ∀ instruction ∈ compactAt block fresh depth base,
      instruction.WritesOnly (fun r => r < fresh ∨
        fresh + 2 * depth ≤ r ∧ r < fresh + 2 * (depth + compactDepth block)) := by
  induction block generalizing depth base with
  | skip => simp [compactAt]
  | action op =>
      intro instruction hi
      have hd := ActionRegistersBelow.destination bounded
      simp only [compactAt, List.mem_singleton] at hi
      subst instruction
      cases op <;> simp only [Action.instruction, Instruction.WritesOnly,
        Action.destination] at hd ⊢ <;> exact Or.inl hd
  | exit src => simp [compactAt, Instruction.WritesOnly]
  | seq a b iha ihb =>
      intro instruction hi
      rcases List.mem_append.mp hi with hi | hi
      · apply instruction_writesOnly_mono instruction (iha depth base bounded.1 instruction hi)
        intro r hr
        have h := Nat.le_max_left (compactDepth a) (compactDepth b)
        simp only [compactDepth]
        omega
      · apply instruction_writesOnly_mono instruction
          (ihb depth (base + compactSize a) bounded.2 instruction hi)
        intro r hr
        have h := Nat.le_max_right (compactDepth a) (compactDepth b)
        simp only [compactDepth]
        omega
  | ifZero condition zero nonzero ihz ihn =>
      intro instruction hi
      simp only [compactAt, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with ((rfl | hi) | rfl) | hi
      · trivial
      · apply instruction_writesOnly_mono instruction (ihn depth _ bounded.2.2 instruction hi)
        intro r hr
        have h := Nat.le_max_right (compactDepth zero) (compactDepth nonzero)
        simp only [compactDepth]
        omega
      · trivial
      · apply instruction_writesOnly_mono instruction (ihz depth _ bounded.2.1 instruction hi)
        intro r hr
        have h := Nat.le_max_left (compactDepth zero) (compactDepth nonzero)
        simp only [compactDepth]
        omega
  | «repeat» count body ih =>
      cases count with
      | zero => simp [compactAt]
      | succ count =>
          intro instruction hi
          simp only [compactAt, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with ((rfl | rfl | rfl) | hi) | (rfl | rfl)
          · simp only [Instruction.WritesOnly, compactDepth, compactCounter]; omega
          · simp only [Instruction.WritesOnly, compactDepth, compactCounter]; omega
          · trivial
          · apply instruction_writesOnly_mono instruction (ih (depth + 1) _ bounded instruction hi)
            intro r hr
            simp only [compactDepth]
            omega
          · simp only [Instruction.WritesOnly, compactDepth, compactCounter]; omega
          · trivial

theorem compact_run_ancestor_frame (memory : Memory) (block : Block)
    (fresh depth base fuel : Nat) (bounded : BlockRegistersBelow fresh block)
    (state : State) (r : Nat) (ancestor : fresh ≤ r ∧ r < fresh + 2 * depth) :
    (run memory (compactAt block fresh depth base) fuel state).final.regs r = state.regs r :=
  run_frame memory (compactAt block fresh depth base) fuel state _
    (compactAt_writesOnly_interval block fresh depth base bounded) r (by omega)

private theorem compact_branch_fits {width condition target : Nat}
    (fields : (Instruction.branchZero condition 0).Fits width)
    (address : target < 2 ^ width) : (Instruction.branchZero condition target).Fits width := by
  simp [Instruction.Fits, Instruction.encoding, Instruction.operands] at fields ⊢
  exact ⟨fields.1, fields.2.1, address⟩

private theorem compact_jump_fits {width target : Nat}
    (fields : (Instruction.jump 0).Fits width) (address : target < 2 ^ width) :
    (Instruction.jump target).Fits width := by
  simp [Instruction.Fits, Instruction.encoding, Instruction.operands] at fields ⊢
  exact ⟨fields.1, address⟩

/-- Constructor-complete fit for the literal emitted encodings. Baseline
source fields cover original constants, registers and tags; the independent
count, wrapper-tag, bank and end-PC guards cover all added control fields. -/
theorem compactAt_fits (block : Block) (width fresh depth base : Nat)
    (fields : block.FieldsFit width) (counts : compactMaxCount block < 2 ^ width)
    (tags : 7 < 2 ^ width)
    (registers : fresh + 2 * (depth + compactDepth block) ≤ 2 ^ width)
    (endPC : base + compactSize block < 2 ^ width) :
    ∀ instruction ∈ compactAt block fresh depth base, instruction.Fits width := by
  have positiveWidth : 0 < width := by
    by_cases zero : width = 0
    · simp [zero] at tags
    · omega
  induction block generalizing depth base with
  | skip => simp [compactAt]
  | action op => simpa [compactAt] using fields
  | exit src => simpa [compactAt] using fields
  | seq a b iha ihb =>
      simp only [compactMaxCount, Nat.max_lt] at counts
      have ha := Nat.le_max_left (compactDepth a) (compactDepth b)
      have hb := Nat.le_max_right (compactDepth a) (compactDepth b)
      simp only [compactDepth] at registers
      simp only [compactSize] at endPC
      intro instruction hi
      rcases List.mem_append.mp hi with hi | hi
      · exact iha depth base fields.1 counts.1 (by omega) (by omega) instruction hi
      · exact ihb depth (base + compactSize a) fields.2 counts.2
          (by omega) (by omega) instruction hi
  | ifZero condition zero nonzero ihz ihn =>
      simp only [Block.FieldsFit] at fields
      simp only [compactMaxCount, Nat.max_lt] at counts
      have hz := Nat.le_max_left (compactDepth zero) (compactDepth nonzero)
      have hn := Nat.le_max_right (compactDepth zero) (compactDepth nonzero)
      simp only [compactDepth] at registers
      simp only [compactSize] at endPC
      intro instruction hi
      simp only [compactAt, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with ((rfl | hi) | rfl) | hi
      · exact compact_branch_fits fields.1 (by omega)
      · exact ihn depth (base + 1) fields.2.2.2 counts.2 (by omega) (by omega) instruction hi
      · exact compact_jump_fits fields.2.1 (by omega)
      · exact ihz depth _ fields.2.2.1 counts.1 (by omega) (by omega) instruction hi
  | «repeat» count body ih =>
      cases count with
      | zero => simp [compactAt]
      | succ count =>
          simp only [compactMaxCount, Nat.max_lt] at counts
          simp only [compactDepth] at registers
          simp only [compactSize] at endPC
          intro instruction hi
          simp only [compactAt, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with ((rfl | rfl | rfl) | hi) | (rfl | rfl)
          · simp [Instruction.Fits, Instruction.encoding, Instruction.operands, compactCounter]
            omega
          · simp [Instruction.Fits, Instruction.encoding, Instruction.operands, compactCounter]
            omega
          · simp [Instruction.Fits, Instruction.encoding, Instruction.operands, compactCounter]
            omega
          · exact ih (depth + 1) (base + 3) fields counts.2
              (by omega) (by omega) instruction hi
          · simp [Instruction.Fits, Instruction.encoding, Instruction.operands,
              Arithmetic.code, compactCounter]
            omega
          · simp [Instruction.Fits, Instruction.encoding, Instruction.operands]
            omega

theorem compactAt_encoding_length (block : Block) (fresh depth base : Nat) :
    ((compactAt block fresh depth base).map Instruction.encoding).flatten.length =
      compactEncodingWords block := by
  induction block generalizing depth base with
  | skip => rfl
  | action op => simp [compactAt, compactEncodingWords]
  | exit src => rfl
  | seq a b iha ihb =>
      simp [compactAt, compactEncodingWords, List.map_append, List.flatten_append, iha, ihb]
  | ifZero c z n ihz ihn =>
      simp [compactAt, compactEncodingWords, List.map_append, List.flatten_append,
        Instruction.encoding, Instruction.operands, ihz, ihn] <;> omega
  | «repeat» count body ih =>
      cases count with
      | zero => rfl
      | succ count =>
          simp [compactAt, compactEncodingWords, List.map_append, List.flatten_append,
            Instruction.encoding, Instruction.operands, Arithmetic.code, ih] <;> omega

namespace CompactStaticConsumers

theorem frame_expectedType (memory : Memory) (block : Block) (fresh depth base fuel : Nat)
    (bounded : BlockRegistersBelow fresh block) (state : State) :
    ∀ r, fresh + 2 * (depth + compactDepth block) ≤ r →
      (run memory (compactAt block fresh depth base) fuel state).final.regs r = state.regs r :=
  fun r hr => compact_run_frame memory block fresh depth base fuel bounded state r hr

theorem fields_expectedType (block : Block) (width fresh depth base : Nat)
    (fields : block.FieldsFit width) (counts : compactMaxCount block < 2 ^ width)
    (tags : 7 < 2 ^ width)
    (registers : fresh + 2 * (depth + compactDepth block) ≤ 2 ^ width)
    (endPC : base + compactSize block < 2 ^ width) :
    ∀ instruction ∈ compactAt block fresh depth base,
      ∀ operand ∈ instruction.encoding, operand < 2 ^ width :=
  compactAt_fits block width fresh depth base fields counts tags registers endPC

theorem encoding_expectedType (block : Block) (fresh depth base : Nat) :
    ((compactAt block fresh depth base).map Instruction.encoding).flatten.length =
      compactEncodingWords block := compactAt_encoding_length block fresh depth base

theorem count_missing_from_baseline_inventory : (Block.repeat 16 .skip).FieldsFit 4 := by
  trivial

theorem oversized_count_rejected :
    ¬ (∀ instruction ∈ compactAt (.repeat 16 .skip) 0 0 0, instruction.Fits 4) := by
  intro all
  have bad := all (.constant 0 16) (by simp [compactAt, compactCounter])
  have h := bad 16 (by simp [Instruction.encoding, Instruction.operands])
  omega

theorem oversized_counter_rejected :
    ¬ (∀ instruction ∈ compactAt (.repeat 1 .skip) 16 0 0, instruction.Fits 4) := by
  intro all
  have bad := all (.constant 16 1) (by simp [compactAt, compactCounter])
  have h := bad 16 (by simp [Instruction.encoding, Instruction.operands])
  omega

theorem oversized_target_rejected :
    ¬ (∀ instruction ∈ compactAt (.repeat 1 .skip) 0 0 11, instruction.Fits 4) := by
  intro all
  have bad := all (.branchZero 0 16) (by simp [compactAt, compactCounter, compactSize])
  have h := bad 16 (by simp [Instruction.encoding, Instruction.operands])
  omega

theorem oversized_control_tag_rejected :
    ¬ (∀ instruction ∈ compactAt (.repeat 1 .skip) 0 0 0, instruction.Fits 2) := by
  intro all
  have bad := all (.branchZero 0 5) (by simp [compactAt, compactCounter, compactSize])
  have h := bad 7 (by simp [Instruction.encoding, Instruction.operands])
  omega

theorem legal_maximum_count :
    ∀ instruction ∈ compactAt (.repeat 15 .skip) 0 0 0, instruction.Fits 4 := by
  apply compactAt_fits <;> simp [Block.FieldsFit, compactMaxCount, compactDepth, compactSize]

theorem nested_loop_encoding (fresh depth base : Nat) :
    ((compactAt (.repeat 2 (.repeat 3 .skip)) fresh depth base).map
      Instruction.encoding).flatten.length = 32 := by
  rw [compactAt_encoding_length]
  rfl

theorem zero_loop_encoding (body : Block) (fresh depth base : Nat) :
    ((compactAt (.repeat 0 body) fresh depth base).map Instruction.encoding).flatten.length = 0 :=
  rfl

end CompactStaticConsumers

end RMQ.SuccinctFinal.PackedWordRAM.Optimization
