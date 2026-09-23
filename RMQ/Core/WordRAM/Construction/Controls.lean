import RMQ.Core.WordRAM.Construction.Model
import RMQ.Core.Shape

/-! # C4 negative controls

This module is outside the interpreter firewall. It deliberately names an
existing semantic shape builder to define a forbidden one-step oracle. No
production instruction, initial state, or program imports this module.
-/

namespace RMQ.SuccinctFinal.PackedConstruction

theorem execPrim_numeric_independent (p : Prim) (s : State)
    (otherKeys : Nat → Option Int) :
    (execPrim p { s with keys := otherKeys }).regs = (execPrim p s).regs := by
  cases p <;> simp only [execPrim, State.writeNext, State.next]
  all_goals repeat first | rfl | split

theorem capped_numeric_independent (ps : List Prim) (hcap : ps.length ≤ primCap)
    (s : State) (otherKeys : Nat → Option Int) :
    (interpretPrims ps { s with keys := otherKeys }).regs = (interpretPrims ps s).regs := by
  cases ps with
  | nil => rfl
  | cons p ps =>
      cases ps with
      | nil => exact execPrim_numeric_independent p s otherKeys
      | cons q qs => simp [primCap] at hcap

/-- Actual existing Cartesian serialization, packed little-endian, used ONLY
as the hypothetical oracle's answer. This is not an efficient builder. -/
def oracleBPWord (s : State) : Nat :=
  (Cartesian.stackCartesianShape [(s.keys 0).getD 0, (s.keys 1).getD 0]).bpCode.foldr
    (fun b acc => (if b then 1 else 0) + 2 * acc) 0

def oracleSemantics (s : State) : State := s.writeNext 0 (oracleBPWord s)

theorem oracle_increasing : oracleBPWord (comparisonInputState [0, 1]) = 5 := by
  simp [oracleBPWord, comparisonInputState, Cartesian.stackCartesianShape,
    Cartesian.StackCartesianTree.buildTree, Cartesian.StackCartesianTree.buildTreeAux,
    Cartesian.StackCartesianTree.insertRightStack_eq_insertRight,
    Cartesian.StackCartesianTree.insertRight, Cartesian.StackCartesianTree.shape,
    Cartesian.CartesianShape.bpCode]
theorem oracle_decreasing : oracleBPWord (comparisonInputState [1, 0]) = 3 := by
  simp [oracleBPWord, comparisonInputState, Cartesian.stackCartesianShape,
    Cartesian.StackCartesianTree.buildTree, Cartesian.StackCartesianTree.buildTreeAux,
    Cartesian.StackCartesianTree.insertRightStack_eq_insertRight,
    Cartesian.StackCartesianTree.insertRight, Cartesian.StackCartesianTree.shape,
    Cartesian.CartesianShape.bpCode]
theorem oracle_equal : oracleBPWord (comparisonInputState [1, 1]) = 5 := by
  simp [oracleBPWord, comparisonInputState, Cartesian.stackCartesianShape,
    Cartesian.StackCartesianTree.buildTree, Cartesian.StackCartesianTree.buildTreeAux,
    Cartesian.StackCartesianTree.insertRightStack_eq_insertRight,
    Cartesian.StackCartesianTree.insertRight, Cartesian.StackCartesianTree.shape,
    Cartesian.CartesianShape.bpCode]

/-- The C4 fake changes the numeric result using input keys which no one
reflected primitive can yet transfer into that result. The quantified domain
is exactly the all-state reflection domain, and the proof uses two legitimate
same-length pointwise comparison inputs. -/
theorem oracle_not_reflected : ¬ ∃ ps : List Prim,
    ps.length ≤ primCap ∧ ∀ s, interpretPrims ps s = oracleSemantics s := by
  rintro ⟨ps, hcap, heq⟩
  have hi := capped_numeric_independent ps hcap (comparisonInputState [0, 1])
    (comparisonInputState [1, 0]).keys
  have hs : { comparisonInputState [0, 1] with keys := (comparisonInputState [1, 0]).keys } =
      comparisonInputState [1, 0] := rfl
  rw [hs, heq, heq] at hi
  have hv := congrFun hi 0
  simp [oracleSemantics, State.writeNext, put, oracle_increasing, oracle_decreasing] at hv

abbrev Program := List BInstr

/-- Same code for every input, including length zero. -/
def Uniform (program : Program) (family : List Int → Program) : Prop :=
  ∀ xs, family xs = program

theorem closed_uniform (program : Program) : Uniform program (fun _ => program) := by
  intro _
  rfl

def bakedProgram (xs : List Int) : Program :=
  [⟨.constant 0 (if (xs[0]?).getD 0 ≤ (xs[1]?).getD 0 then 5 else 3)⟩,
    ⟨.store 1 0⟩]

theorem baked_length (xs : List Int) : (bakedProgram xs).length = 2 := rfl

/-- The negative uses the same Uniform predicate as every accepted program.
A length/shape-indexed baked table cannot be disguised as fixed code. -/
theorem baked_not_uniform : ¬ ∃ program, Uniform program bakedProgram := by
  rintro ⟨program, h⟩
  have hdiff : bakedProgram [0, 1] ≠ bakedProgram [1, 0] := by decide
  exact hdiff ((h [0, 1]).trans (h [1, 0]).symm)

def programWords (program : Program) : Nat :=
  ((program.map (fun i => i.primitive.constants)).flatten).length

def CodeAccounting (program : Program) (width bits : Nat) : Prop :=
  bits = programWords program * width

theorem code_accounting_exact (program : Program) (width : Nat) :
    CodeAccounting program width (programWords program * width) := rfl

/-- A plain-data replay predicate can express and reject a fabricated result;
it is intentionally not advertised as sufficient anti-oracle evidence. -/
def Replays (initial : Memory) (writes : List (Nat × Nat)) (final : Memory) : Prop :=
  final = writes.foldl (fun memory event => put memory event.1 (some event.2)) initial

theorem fabricated_replay_rejected :
    ¬ Replays (fun _ => none) [(0, 0)] (put (fun _ => none) 1 (some 7)) := by
  intro h
  have hv := congrFun h 1
  simp [put] at hv

end RMQ.SuccinctFinal.PackedConstruction
