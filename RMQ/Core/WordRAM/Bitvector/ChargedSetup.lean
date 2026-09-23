import RMQ.Core.WordRAM.Bitvector.Source
import RMQ.Core.WordRAM.Bitvector.ControllerInterface
import RMQ.Core.WordRAM.Packed.LoadSafety

/-! # Charged loading of the shared bitvector metadata

The metadata functions below describe the values loaded by the existing source.
They are not used by the executable setup or its compiled program.
-/

namespace RMQ.PackedBitvector.ChargedSetup

open SuccinctFinal.PackedWordRAM SuccinctFinal.PackedWordRAM.Structured

def setupMetadata (bits : List Bool) (regs : Registers) : Registers :=
  fun r => if r = 6 then 18
    else if 16 ≤ r ∧ r < 35 then
      ((Allocation.scalarHeader bits)[r - 16]?).getD 0
    else regs r

def targetMetadata (bits : List Bool) (regs : Registers) : Registers :=
  fun r => if regs 3 = 0 then regs r
    else if r = 6 then 22
    else if r = 16 then regs 17
    else if 28 ≤ r ∧ r < 32 then
      ((Allocation.scalarHeader bits)[r - 9]?).getD 0
    else regs r

def setupReceipts (bits : List Bool) : List Receipt :=
  (List.range 19).map fun i =>
    ⟨i, some (((Allocation.scalarHeader bits)[i]?).getD 0)⟩

def targetReceipts (bits : List Bool) (regs : Registers) : List Receipt :=
  if regs 3 = 0 then [] else
    (List.range 4).map fun i =>
      ⟨19 + i, some (((Allocation.scalarHeader bits)[19 + i]?).getD 0)⟩

theorem memory_scalar (bits : List Bool) (index : Nat) (hi : index < 23) :
    (Allocation.memory bits)[index]? =
      some (((Allocation.scalarHeader bits)[index]?).getD 0) := by
  have hscalar : index < (Allocation.scalarHeader bits).length := by simpa using hi
  unfold Allocation.memory Allocation.header
  rw [List.getElem?_append_left (by simp only [List.length_append]; omega),
    List.getElem?_append_left (by simp only [List.length_append]; omega),
    List.getElem?_append_left hscalar, List.getElem?_eq_getElem hscalar]
  rfl

private theorem eval_skip (memory : Memory) (s : Data) :
    Block.skip.eval memory s = ⟨s, []⟩ := by
  cases s with
  | mk regs status => cases status <;> rfl

private theorem sequence_cons (first : Block) (rest : List Block) :
    Block.sequence (first :: rest) = .seq first (Block.sequence rest) := rfl

private theorem sequence_append_eval (memory : Memory) (first second : List Block)
    (s : Data) :
    (Block.sequence (first ++ second)).eval memory s =
      let a := (Block.sequence first).eval memory s
      let b := (Block.sequence second).eval memory a.final
      ⟨b.final, a.reads ++ b.reads⟩ := by
  induction first generalizing s with
  | nil => simp [Block.sequence, eval_skip]
  | cons head rest ih =>
      simp only [List.cons_append, sequence_cons, Block.eval_seq, Evaluation.bind]
      rw [ih]
      simp only [List.append_assoc]

private theorem load_pair_source (memory : Memory) (regs : Registers)
    (address dst value : Nat) (found : memory[address]? = some value) :
    (Block.seq (.action (.constant 6 address)) (.action (.load dst 6))).eval
      memory ⟨regs, .running⟩ =
      ⟨⟨(regs.write 6 address).write dst value, .running⟩,
        [⟨address, some value⟩]⟩ := by
  simp [Block.eval, Action.eval, Action.instruction, SuccinctFinal.PackedWordRAM.execute,
    State.writeNext, Data.ofState, Registers.write, found]

private theorem sequence_single_eval (memory : Memory) (block : Block) (s : Data) :
    (Block.sequence [block]).eval memory s = block.eval memory s := by
  simp [Block.sequence, Block.eval_seq, Evaluation.bind, eval_skip]

private def prefixMetadata (bits : List Bool) (count : Nat) (regs : Registers) : Registers :=
  fun r => if r = 6 then if count = 0 then regs 6 else count - 1
    else if 16 ≤ r ∧ r < 16 + count then
      ((Allocation.scalarHeader bits)[r - 16]?).getD 0
    else regs r

private theorem prefixMetadata_zero (bits : List Bool) (regs : Registers) :
    prefixMetadata bits 0 regs = regs := by
  funext r
  by_cases h : r = 6
  · subst r; simp [prefixMetadata]
  · have hout : ¬ (16 ≤ r ∧ r < 16 + 0) := by omega
    simp [prefixMetadata, h, hout]

private theorem prefixMetadata_step (bits : List Bool) (count : Nat) (regs : Registers) :
    ((prefixMetadata bits count regs).write 6 count).write (16 + count)
        (((Allocation.scalarHeader bits)[count]?).getD 0) =
      prefixMetadata bits (count + 1) regs := by
  funext r
  by_cases hi : r = 16 + count
  · subst r
    have h6 : 16 + count ≠ 6 := by omega
    have hsub : 16 + count - 16 = count := by omega
    simp [Registers.write, prefixMetadata, h6, hsub]
  · by_cases h6 : r = 6
    · subst r
      simp [Registers.write, prefixMetadata, hi]
    · have hinterval : (16 ≤ r ∧ r < 16 + (count + 1)) ↔
          (16 ≤ r ∧ r < 16 + count) := by omega
      simp [Registers.write, prefixMetadata, hi, h6, hinterval]

private theorem prefix_source (bits : List Bool) (count : Nat) (regs : Registers)
    (hc : count ≤ 19) :
    (Block.sequence ((List.range count).map fun index =>
      .seq (.action (.constant 6 index)) (.action (.load (16 + index) 6)))).eval
      (Allocation.memory bits) ⟨regs, .running⟩ =
      ⟨⟨prefixMetadata bits count regs, .running⟩,
        (List.range count).map fun i =>
          ⟨i, some (((Allocation.scalarHeader bits)[i]?).getD 0)⟩⟩ := by
  induction count with
  | zero => simp [Block.sequence, eval_skip, prefixMetadata_zero]
  | succ count ih =>
      rw [List.range_succ, List.map_append, sequence_append_eval, ih (by omega)]
      simp only [List.map_cons, List.map_nil, sequence_single_eval]
      rw [load_pair_source _ _ _ _ _ (memory_scalar bits count (by omega))]
      simp only [prefixMetadata_step]
      simp only [List.map_append, List.map_cons, List.map_nil]

theorem setup_source (bits : List Bool) (regs : Registers) :
    Experiment.setup.eval (Allocation.memory bits) ⟨regs, .running⟩ =
      ⟨⟨setupMetadata bits regs, .running⟩, setupReceipts bits⟩ := by
  simpa only [Experiment.setup, prefixMetadata, setupMetadata, setupReceipts,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceEqDiff, if_false] using
    prefix_source bits 19 regs (by decide)

private def targetLoaded (bits : List Bool) (regs : Registers) : Registers :=
  let r := ((regs.write 16 (regs 17)).write 6 19).write 28
    (((Allocation.scalarHeader bits)[19]?).getD 0)
  let r := (r.write 6 20).write 29 (((Allocation.scalarHeader bits)[20]?).getD 0)
  let r := (r.write 6 21).write 30 (((Allocation.scalarHeader bits)[21]?).getD 0)
  (r.write 6 22).write 31 (((Allocation.scalarHeader bits)[22]?).getD 0)

private theorem targetLoaded_eq (bits : List Bool) (regs : Registers) (hn : regs 3 ≠ 0) :
    targetLoaded bits regs = targetMetadata bits regs := by
  funext r
  by_cases h6 : r = 6
  · subst r; simp [targetLoaded, targetMetadata, Registers.write, hn]
  by_cases h16 : r = 16
  · subst r; simp [targetLoaded, targetMetadata, Registers.write, hn]
  by_cases h28 : r = 28
  · subst r; simp [targetLoaded, targetMetadata, Registers.write, hn]
  by_cases h29 : r = 29
  · subst r; simp [targetLoaded, targetMetadata, Registers.write, hn]
  by_cases h30 : r = 30
  · subst r; simp [targetLoaded, targetMetadata, Registers.write, hn]
  by_cases h31 : r = 31
  · subst r; simp [targetLoaded, targetMetadata, hn]
  have hout : ¬ (28 ≤ r ∧ r < 32) := by omega
  simp [targetLoaded, targetMetadata, Registers.write, hn, h6, h16,
    h28, h29, h30, h31, hout]

theorem targetSetup_source (bits : List Bool) (regs : Registers) :
    Experiment.targetSetup.eval (Allocation.memory bits) ⟨regs, .running⟩ =
      ⟨⟨targetMetadata bits regs, .running⟩, targetReceipts bits regs⟩ := by
  by_cases hz : regs 3 = 0
  · simp only [Experiment.targetSetup, Block.eval, hz,
      targetReceipts, ↓reduceIte, Evaluation.mk.injEq, Data.mk.injEq, and_true]
    funext r
    simp [targetMetadata, hz]
  · have h19 := memory_scalar bits 19 (by decide)
    have h20 := memory_scalar bits 20 (by decide)
    have h21 := memory_scalar bits 21 (by decide)
    have h22 := memory_scalar bits 22 (by decide)
    have heq := targetLoaded_eq bits regs hz
    simpa [Experiment.targetSetup, Block.sequence, Block.eval,
      Action.eval, Action.instruction, SuccinctFinal.PackedWordRAM.execute, State.writeNext, Data.ofState,
      Registers.write, hz, h19, h20, h21, h22, targetReceipts, List.range_succ,
      targetLoaded] using congrArg (fun out : Registers =>
        (⟨⟨out, .running⟩, targetReceipts bits regs⟩ : Evaluation)) heq

private theorem sequence_safe (memory : Memory) (width : Nat) (blocks : List Block)
    (each : ∀ block ∈ blocks, ∀ s, s.Fits width → block.Safe memory width s)
    (s : Data) (fit : s.Fits width) : (Block.sequence blocks).Safe memory width s := by
  induction blocks generalizing s with
  | nil => exact Block.safe_skip memory width s fit
  | cons head rest ih =>
      have hs := each head (by simp) s fit
      exact Block.safe_seq hs (ih (fun b hb => each b (by simp [hb])) _
        (Block.eval_fits memory width head s hs))

private theorem load_pair_safe (memory : Memory) (width address dst : Nat)
    (memoryFit : MemoryWordsFit memory width) (ha : address < 2 ^ width)
    (s : Data) (fit : s.Fits width) :
    (Block.seq (.action (.constant 6 address)) (.action (.load dst 6))).Safe memory width s := by
  have hc := Block.safe_action memory width (.constant 6 address) s fit ha
  apply Block.safe_seq hc
  apply Block.safe_action _ _ _ _ (Block.eval_fits memory width _ _ hc)
  exact fun value found => memoryFit.reply found

theorem setup_safe (bits : List Bool) (width : Nat) (regs : Registers)
    (hw : 32 ≤ width) (memoryFit : MemoryWordsFit (Allocation.memory bits) width)
    (fit : (⟨regs, .running⟩ : Data).Fits width) :
    Experiment.setup.Safe (Allocation.memory bits) width ⟨regs, .running⟩ := by
  have cap : 4294967296 ≤ 2 ^ width := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hw
  apply sequence_safe _ _ _ ?_ _ fit
  intro block hb s fs
  obtain ⟨index, hi, rfl⟩ := List.mem_map.mp hb
  have hn : index < 19 := List.mem_range.mp hi
  exact load_pair_safe _ _ _ _ memoryFit (by omega) s fs

theorem targetSetup_safe (bits : List Bool) (width : Nat) (regs : Registers)
    (hw : 32 ≤ width) (memoryFit : MemoryWordsFit (Allocation.memory bits) width)
    (fit : (⟨regs, .running⟩ : Data).Fits width) :
    Experiment.targetSetup.Safe (Allocation.memory bits) width ⟨regs, .running⟩ := by
  have cap : 4294967296 ≤ 2 ^ width := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hw
  apply Block.safe_ifZero fit
  split
  · exact Block.safe_skip _ _ _ fit
  · apply sequence_safe _ _ _ ?_ _ fit
    intro block hb s fs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals apply Block.safe_action _ _ _ _ fs
    · exact fs.1 17
    · exact (by omega : 19 < 2 ^ width)
    · exact fun value found => memoryFit.reply found
    · exact (by omega : 20 < 2 ^ width)
    · exact fun value found => memoryFit.reply found
    · exact (by omega : 21 < 2 ^ width)
    · exact fun value found => memoryFit.reply found
    · exact (by omega : 22 < 2 ^ width)
    · exact fun value found => memoryFit.reply found

theorem setup_frame (bits : List Bool) (regs : Registers) (r : Nat)
    (h6 : r ≠ 6) (outside : r < 16 ∨ 35 ≤ r) :
    (Experiment.setup.eval (Allocation.memory bits) ⟨regs, .running⟩).final.regs r = regs r := by
  rw [setup_source]
  simp only [setupMetadata, if_neg h6]
  split <;> omega

theorem targetSetup_frame (bits : List Bool) (regs : Registers) (r : Nat)
    (h6 : r ≠ 6) (outside : r < 16 ∨ 35 ≤ r) :
    (Experiment.targetSetup.eval (Allocation.memory bits) ⟨regs, .running⟩).final.regs r = regs r := by
  rw [targetSetup_source]
  have h16 : r ≠ 16 := by omega
  have hflags : ¬ (28 ≤ r ∧ r < 32) := by omega
  simp [targetMetadata, h6, h16, hflags]

/-- Exact expected-type consumer for the same charged setup sequence. -/
theorem setup_then_target_source (bits : List Bool) (regs : Registers) :
    (Block.seq Experiment.setup Experiment.targetSetup).eval
      (Allocation.memory bits) ⟨regs, .running⟩ =
      ⟨⟨targetMetadata bits (setupMetadata bits regs), .running⟩,
        setupReceipts bits ++ targetReceipts bits (setupMetadata bits regs)⟩ := by
  rw [Block.eval_seq, setup_source]
  simp only [Evaluation.bind]
  rw [targetSetup_source]

/-- Exact safety consumer follows the actual intermediate setup evaluation. -/
theorem setup_then_target_safe (bits : List Bool) (width : Nat) (regs : Registers)
    (hw : 32 ≤ width) (memoryFit : MemoryWordsFit (Allocation.memory bits) width)
    (fit : (⟨regs, .running⟩ : Data).Fits width) :
    (Block.seq Experiment.setup Experiment.targetSetup).Safe
      (Allocation.memory bits) width ⟨regs, .running⟩ := by
  have first := setup_safe bits width regs hw memoryFit fit
  have next := Block.eval_fits (Allocation.memory bits) width _ _ first
  apply Block.safe_seq first
  rw [setup_source] at next ⊢
  exact targetSetup_safe bits width _ hw memoryFit next

#print axioms setup_source
#print axioms targetSetup_source
#print axioms setup_safe
#print axioms targetSetup_safe
#print axioms setup_then_target_source
#print axioms setup_then_target_safe

end RMQ.PackedBitvector.ChargedSetup
