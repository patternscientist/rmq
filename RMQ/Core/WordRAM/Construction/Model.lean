import RMQ.Core.WordRAM.Construction.Primitive
import RMQ.Core.WordRAM.Construction.Input

/-! # C1-C4 model prerequisites

Only initial-state and primitive facts are established here. A construction
program, its run and its RMQ allocation are deliberately absent before audit.
-/

namespace RMQ.SuccinctFinal.PackedConstruction

def CleanTail (s : State) : Prop := ∀ a, s.extent ≤ a → s.memory a = none

theorem reserve_fresh (s : State) (h : CleanTail s) (dst : Operand) :
    (execPrim (.reserve dst) s).memory s.extent = none := h s.extent (by omega)

theorem reserve_cleanTail (s : State) (h : CleanTail s) (dst : Operand) :
    CleanTail (execPrim (.reserve dst) s) := by
  intro a ha
  exact h a (by change s.extent + 1 ≤ a at ha; omega)

theorem store_cleanTail (s : State) (h : CleanTail s) (address value : Operand) :
    CleanTail (execPrim (.store address value) s) := by
  intro a ha
  by_cases hb : s.regs address < s.extent
  · simp only [execPrim, if_pos hb, State.next] at ha ⊢
    simp [put, show a ≠ s.regs address by omega, h a ha]
  · simp only [execPrim, if_neg hb] at ha ⊢
    exact h a ha

theorem constants_fit_width (i : BInstr) (p : Prim) (hp : p ∈ i.semantics)
    (c : Operand) (hc : c ∈ p.constants) (width : Nat) (hw : 32 ≤ width) :
    c.val < 2 ^ width :=
  Nat.lt_of_lt_of_le (prim_const_cap i p hp c hc)
    (Nat.pow_le_pow_right (by decide) hw)

/-- Numeric input is pre-supplied pointwise; all numeric registers start zero.
The key oracle is absent in this signed-word initial state. -/
def wordInputState (width : Nat) (xs : List Int) : State where
  regs := fun _ => 0
  memory := encodeInput width xs
  extent := inputCellCount xs
  keys := fun _ => none
  keyRegs := fun _ => 0
  pc := 0
  status := .running

/-- In the arbitrary-Int model keys occupy separately counted input cells.
The only numeric input cell is the same unsigned header. -/
def comparisonInputState (xs : List Int) : State where
  regs := fun _ => 0
  memory := fun a => if a = 0 then some xs.length else none
  extent := 1
  keys := fun i => xs[i]?
  keyRegs := fun _ => 0
  pc := 0
  status := .running

theorem wordInputState_cleanTail (width : Nat) (xs : List Int) :
    CleanTail (wordInputState width xs) := by
  intro a ha
  apply (encodeInput_eq_none_iff width xs a).2
  change xs.length + 1 ≤ a at ha
  omega

theorem comparisonInputState_cleanTail (xs : List Int) :
    CleanTail (comparisonInputState xs) := by
  intro a ha
  change 1 ≤ a at ha
  simp [comparisonInputState, show a ≠ 0 by omega]

def headerInstruction : BInstr := ⟨.load 1 0⟩

theorem header_read (width : Nat) (xs : List Int) :
    (bstep headerInstruction (wordInputState width xs)).regs 1 = xs.length ∧
    (bstep headerInstruction (wordInputState width xs)).status = .running := by
  simp [bstep, headerInstruction, execPrim, wordInputState, inputCellCount,
    State.writeNext, State.next, put]

theorem comparison_header_read (xs : List Int) :
    (bstep headerInstruction (comparisonInputState xs)).regs 1 = xs.length ∧
    (bstep headerInstruction (comparisonInputState xs)).status = .running := by
  simp [bstep, headerInstruction, execPrim, comparisonInputState,
    State.writeNext, State.next, put]

theorem missing_header_fault (width : Nat) (xs : List Int) :
    (bstep headerInstruction
      { wordInputState width xs with memory := put (encodeInput width xs) 0 none }).status =
      .fault := by
  simp [bstep, headerInstruction, execPrim, wordInputState, inputCellCount, put]

theorem comparison_missing_header_fault (xs : List Int) :
    (bstep headerInstruction
      { comparisonInputState xs with memory := put (comparisonInputState xs).memory 0 none }).status =
      .fault := by
  simp [bstep, headerInstruction, execPrim, comparisonInputState, put]

/-- Terminal states do not execute another instruction. Program fetch and
loops must use this boundary, rather than calling the scalar evaluator again. -/
def checkedStep (i : BInstr) (s : State) : Option State :=
  match s.status with
  | .running => some (bstep i s)
  | .halted _ => none
  | .fault => none

theorem checkedStep_running (i : BInstr) (s : State) (hs : s.status = .running) :
    checkedStep i s = some (interpretPrims i.semantics s) := by
  simp [checkedStep, hs, bstep_reflects]

theorem checkedStep_fault (i : BInstr) (s : State) (hs : s.status = .fault) :
    checkedStep i s = none := by simp [checkedStep, hs]

theorem checkedStep_halted (i : BInstr) (s : State) (v : Nat)
    (hs : s.status = .halted v) : checkedStep i s = none := by simp [checkedStep, hs]

end RMQ.SuccinctFinal.PackedConstruction
