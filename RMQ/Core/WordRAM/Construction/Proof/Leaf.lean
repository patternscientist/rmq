import RMQ.Core.WordRAM.Construction.Proof.GeometryBank
import RMQ.Core.WordRAM.Construction.Builder.Cartesian

/-! # PRE-1 builder proofs: the two comparison leaves

Outside the builder firewall. `KeySpec W xs Inp leaf` is the only key
hypothesis of the stage proofs: from every running state satisfying the input
predicate `Inp`, with indices `i < n` in register 4 and `j < n` in register 5
and the constant 1 in register 2, the leaf safely decides `xs[i] < xs[j]` into
register 6 in exactly five transitions, changes no register other than 6, 7
and 8, and leaves memory, extent and keys unchanged (key registers may change).

`keyLeaf_spec` (comparison-oracle leaf, oracle input predicate
`keys = fun i => xs[i]?`, unconditionally) and `wordLeaf_spec` (word-model leaf,
pre-supplied memory input under `InputFits W xs`) prove it; since the leaves are
declared in `Builder/Program.lean`, both proofs live in `Proof/Leaves.lean`, after
the proof tower (coordinator ruling R-S7-7), so this module and the tower do not
import the program host module.
-/

namespace RMQ.SuccinctFinal.PackedConstruction.Proof

open Structured Builder

/-- The leaf contract. -/
def KeySpec (W : Nat) (xs : List Int) (Inp : State → Prop) (leaf : Block) : Prop :=
  ∀ u : State, u.status = .running → Inp u → u.regs 2 = 1 →
    u.regs 4 < xs.length → u.regs 5 < xs.length →
    ∃ u', SafeEval W leaf u u' 5 ∧ u'.status = .running ∧
      u'.regs 6 = (if xs.getD (u.regs 4) 0 < xs.getD (u.regs 5) 0 then 1 else 0) ∧
      (∀ r : Nat, r ≠ 6 → r ≠ 7 → r ≠ 8 → u'.regs r = u.regs r) ∧
      u'.memory = u.memory ∧ u'.extent = u.extent ∧ u'.keys = u.keys

/-- Input predicate of the comparison-oracle model. -/
def OracleInput (xs : List Int) (u : State) : Prop := u.keys = fun i => xs[i]?

/-- Input predicate of the word model: the keys are pre-supplied encoded words. -/
def WordInput (W : Nat) (xs : List Int) (u : State) : Prop :=
  InputFits W xs ∧ xs.length + 1 ≤ u.extent ∧
    ∀ k, k < xs.length → u.memory (k + 1) = some (encodeInt W (xs.getD k 0))

theorem exec_loadKey (s : State) (d a : Operand) {k : Int} (h : s.keys (s.regs a) = some k) :
    execPrim (.loadKey d a) s = { s.next with keyRegs := put s.keyRegs d k } := by
  simp [execPrim, h]

theorem exec_compareKey (s : State) (d a b : Operand) :
    execPrim (.compareKey d a b) s =
      s.writeNext d (if s.keyRegs a < s.keyRegs b then 1 else 0) := rfl

theorem getD_eq_of_getElem? {xs : List Int} {i : Nat} (hi : i < xs.length) :
    xs[i]? = some (xs.getD i 0) := by
  simp [List.getD, List.getElem?_eq_getElem hi]

end RMQ.SuccinctFinal.PackedConstruction.Proof
