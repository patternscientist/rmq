import RMQ.Core.WordRAM.Construction.Proof.BPEmit
import RMQ.Core.WordRAM.Construction.Builder.Program

/-! # PRE-1 builder proofs: the two leaves and their S3 instances

Outside the builder firewall. The leaves `keyLeaf` and `wordLeaf` are declared
in `Builder/Program.lean` (contract clause V3-1). Their contract proofs and the
two S3 instances of the Cartesian BP theorem at the leaves were moved here from
`Proof/Leaf.lean` and `Proof/BPEmit.lean` without change of name, namespace,
type or proof (coordinator ruling R-S7-7), so that the proof tower does not
import the program host module. `keyLeaf_spec` proves `KeySpec` for the
comparison-oracle leaf on the oracle input predicate unconditionally;
`wordLeaf_spec` proves it for the word-model leaf on the pre-supplied memory
input under `InputFits W xs`; `cartesianBP_key` and `cartesianBP_word`
instantiate `cartesianBP_spec` at them.
-/

namespace RMQ.SuccinctFinal.PackedConstruction.Proof

open Structured Builder

/-- **Comparison-oracle leaf.** -/
theorem keyLeaf_spec {W : Nat} (hW : 32 ≤ W) (xs : List Int) :
    KeySpec W xs (OracleInput xs) keyLeaf := by
  intro u hrun hinp _ hi hj
  have hki : u.keys (u.regs 4) = some (xs.getD (u.regs 4) 0) := by
    rw [hinp]; exact getD_eq_of_getElem? hi
  have hkj : u.keys (u.regs 5) = some (xs.getD (u.regs 5) 0) := by
    rw [hinp]; exact getD_eq_of_getElem? hj
  let u1 := execPrim (Prim.loadKey 0 4) u
  have e1 := exec_loadKey u 0 4 hki
  let u2 := execPrim (Prim.loadKey 1 5) u1
  have hkj1 : u1.keys (u1.regs 5) = some (xs.getD (u.regs 5) 0) := by
    simp only [u1, e1, State.next]; exact hkj
  have e2 := exec_loadKey u1 1 5 hkj1
  let u3 := execPrim (Prim.compareKey 6 0 1) u2
  have e3 := exec_compareKey u2 6 0 1
  let u4 := execPrim (Prim.move 6 6) u3
  have e4 := exec_move u3 6 6
  let u5 := execPrim (Prim.move 6 6) u4
  have e5 := exec_move u4 6 6
  have u2kr : u2.keyRegs = put (put u.keyRegs 0 (xs.getD (u.regs 4) 0)) 1
      (xs.getD (u.regs 5) 0) := by
    simp [u2, e2, u1, e1, State.next]
  have u2r : u2.regs = u.regs := by simp [u2, e2, u1, e1, State.next]
  have u3r : u3.regs = put u.regs 6
      (if xs.getD (u.regs 4) 0 < xs.getD (u.regs 5) 0 then 1 else 0) := by
    simp only [u3, e3, State.writeNext, State.next, u2kr, u2r]
    simp [put]
  have u5r : u5.regs = u3.regs := by
    simp only [u5, e5, u4, e4]
    funext r
    simp only [put]
    split <;> simp_all
  have hsafe : ActsOK (Action.Safe W) [.loadKey 0 4, .loadKey 1 5, .compareKey 6 0 1,
      .move 6 6, .move 6 6] u := by
    refine ⟨⟨Prim.operandsFit_of_width _ hW, ⟨_, hki⟩⟩, ?_, ?_⟩
    · simp [Action.prim, e1, State.next, hrun]
    refine ⟨⟨Prim.operandsFit_of_width _ hW, ⟨_, hkj1⟩⟩, ?_, ?_⟩
    · show u2.status = .running
      simp [u2, e2, u1, e1, State.next, hrun]
    refine ⟨⟨Prim.operandsFit_of_width _ hW, trivial⟩, ?_, ?_⟩
    · show u3.status = .running
      simp [u3, e3, State.writeNext, u2, e2, u1, e1, State.next, hrun]
    refine ⟨safe_move hW _ _ _, ?_, safe_move hW _ _ _, ?_, trivial⟩
    · show u4.status = .running
      simp [u4, e4, u3, e3, State.writeNext, u2, e2, u1, e1, State.next, hrun]
    · show u5.status = .running
      simp [u5, e5, u4, e4, u3, e3, State.writeNext, u2, e2, u1, e1, State.next, hrun]
  have heval := acts_evalG (P := Action.Safe W) _ u hrun hsafe
  refine ⟨u5, heval, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [u5, e5, u4, e4, u3, e3, State.writeNext, u2, e2, u1, e1, State.next, hrun]
  · rw [u5r, u3r, put_same]
  · intro r h6 _ _
    rw [u5r, u3r, put_ne _ _ h6]
  · simp [u5, e5, u4, e4, u3, e3, State.writeNext, u2, e2, u1, e1, State.next]
  · simp [u5, e5, u4, e4, u3, e3, State.writeNext, u2, e2, u1, e1, State.next]
  · simp [u5, e5, u4, e4, u3, e3, State.writeNext, u2, e2, u1, e1, State.next]

/-- **Word-model leaf.** -/
theorem wordLeaf_spec {W : Nat} (hW : 32 ≤ W) (xs : List Int) :
    KeySpec W xs (WordInput W xs) wordLeaf := by
  intro u hrun ⟨hfits, hext, hmem⟩ hone hi hj
  obtain ⟨_, hnW, hsigned⟩ := hfits
  have hsi : SignedFits W (xs.getD (u.regs 4) 0) := by
    apply hsigned; simp [List.getD, List.getElem?_eq_getElem hi]
  have hsj : SignedFits W (xs.getD (u.regs 5) 0) := by
    apply hsigned; simp [List.getD, List.getElem?_eq_getElem hj]
  have hei := encodeInt_lt_capacity hsi
  have hej := encodeInt_lt_capacity hsj
  generalize hI : u.regs 4 = i at hi hsi hei ⊢
  generalize hJ : u.regs 5 = j at hj hsj hej ⊢
  -- add 7 4 2
  let u1 := execPrim (Prim.arithmetic .add 7 4 2) u
  have e1 := exec_arithmetic u .add 7 4 2
  have u1r : u1.regs = put u.regs 7 (i + 1) := by
    simp only [u1, e1, Arithmetic.eval]
    rw [show ((4 : Operand) : Nat) = 4 from rfl, show ((2 : Operand) : Nat) = 2 from rfl, hI, hone]
    rfl
  have u1m : u1.memory = u.memory := by simp [u1, e1]
  have u1e : u1.extent = u.extent := by simp [u1, e1]
  have u1s : u1.status = .running := by simp [u1, e1, hrun]
  -- load 7 7
  have hload1 : u1.regs 7 < u1.extent := by rw [u1r, put_same, u1e]; omega
  have hmem1 : u1.memory (u1.regs 7) = some (encodeInt W (xs.getD i 0)) := by
    rw [u1r, put_same, u1m]; exact hmem i hi
  let u2 := execPrim (Prim.load 7 7) u1
  have e2 := exec_load u1 7 7 hload1 hmem1
  have u2r : u2.regs = put (put u.regs 7 (i + 1)) 7 (encodeInt W (xs.getD i 0)) := by
    simp only [u2, e2, u1r]
    rfl
  have u2s : u2.status = .running := by simp [u2, e2, u1s]
  have u2m : u2.memory = u.memory := by simp [u2, e2, u1m]
  have u2e : u2.extent = u.extent := by simp [u2, e2, u1e]
  -- add 8 5 2
  let u3 := execPrim (Prim.arithmetic .add 8 5 2) u2
  have e3 := exec_arithmetic u2 .add 8 5 2
  have u2_5 : u2.regs 5 = j := by rw [u2r]; simp [put, hJ]
  have u2_2 : u2.regs 2 = 1 := by rw [u2r]; simp [put, hone]
  have u3r : u3.regs = put u2.regs 8 (j + 1) := by
    simp only [u3, e3, Arithmetic.eval]
    rw [show ((5 : Operand) : Nat) = 5 from rfl, show ((2 : Operand) : Nat) = 2 from rfl, u2_5,
      u2_2]
    rfl
  have u3s : u3.status = .running := by simp [u3, e3, u2s]
  have u3m : u3.memory = u.memory := by simp [u3, e3, u2m]
  have u3e : u3.extent = u.extent := by simp [u3, e3, u2e]
  -- load 8 8
  have hload3 : u3.regs 8 < u3.extent := by rw [u3r, put_same, u3e]; omega
  have hmem3 : u3.memory (u3.regs 8) = some (encodeInt W (xs.getD j 0)) := by
    rw [u3r, put_same, u3m]; exact hmem j hj
  let u4 := execPrim (Prim.load 8 8) u3
  have e4 := exec_load u3 8 8 hload3 hmem3
  have u4r : u4.regs = put u3.regs 8 (encodeInt W (xs.getD j 0)) := by simp only [u4, e4]; rfl
  have u4s : u4.status = .running := by simp [u4, e4, u3s]
  have u4_7 : u4.regs 7 = encodeInt W (xs.getD i 0) := by
    rw [u4r, put_ne _ _ (by decide), u3r, put_ne _ _ (by decide), u2r, put_same]
  have u4_8 : u4.regs 8 = encodeInt W (xs.getD j 0) := by rw [u4r, put_same]
  -- comparison lt 6 7 8
  let u5 := execPrim (Prim.comparison .lt 6 7 8) u4
  have e5 := exec_comparison u4 .lt 6 7 8
  have u5r : u5.regs = put u4.regs 6
      (if xs.getD i 0 < xs.getD j 0 then 1 else 0) := by
    simp only [u5, e5, Comparison.eval]
    rw [show ((7 : Operand) : Nat) = 7 from rfl, show ((8 : Operand) : Nat) = 8 from rfl, u4_7,
      u4_8]
    simp only [encodeInt_lt_iff hsi hsj]
    rfl
  have hW2 : 2 ^ 32 ≤ 2 ^ W := Nat.pow_le_pow_right (by decide) hW
  have hsafe : ActsOK (Action.Safe W) [.arithmetic .add 7 4 2, .load 7 7,
      .arithmetic .add 8 5 2, .load 8 8, .comparison .lt 6 7 8] u := by
    refine ⟨safe_add hW u _ _ _ ?_, u1s, ?_⟩
    · show u.regs 4 + u.regs 2 < 2 ^ W
      rw [hI, hone]; omega
    refine ⟨⟨Prim.operandsFit_of_width _ hW, hload1, _, hmem1, hei⟩, u2s, ?_⟩
    refine ⟨safe_add hW u2 _ _ _ ?_, u3s, ?_⟩
    · show u2.regs 5 + u2.regs 2 < 2 ^ W
      rw [u2_5, u2_2]; omega
    refine ⟨⟨Prim.operandsFit_of_width _ hW, hload3, _, hmem3, hej⟩, u4s, ?_⟩
    exact ⟨safe_comparison hW u4 _ _ _ _, by
      show (execPrim (Prim.comparison .lt 6 7 8) u4).status = .running
      rw [e5]; exact u4s, trivial⟩
  have heval := acts_evalG (P := Action.Safe W) _ u hrun hsafe
  refine ⟨u5, heval, by simp [u5, e5, u4s], by rw [u5r, put_same], ?_, ?_, ?_, ?_⟩
  · intro r h6 h7 h8
    rw [u5r, put_ne _ _ h6, u4r, put_ne _ _ h8, u3r, put_ne _ _ h8, u2r, put_ne _ _ h7,
      put_ne _ _ h7]
  · simp [u5, e5, u4, e4, u3m]
  · simp [u5, e5, u4, e4, u3e]
  · simp [u5, e5, u4, e4, u3, e3, u2, e2, u1, e1]

section S3Instances

open Spec Spec.StackCartesianTreeSpec RMQ.Cartesian

/-- **S3, comparison-oracle model.** -/
theorem cartesianBP_key {W : Nat} (hW : 32 ≤ W) (xs : List Int) (s : State)
    (hrun : s.status = .running) (hzero : s.regs 0 = 0) (hone : s.regs 2 = 1)
    (hn : s.regs 1 = xs.length) (hkeys : s.keys = fun i => xs[i]?)
    (hcap : s.extent + 3 * (xs.length + 1) + 2 * xs.length + 2 < 2 ^ W) :
    ∃ s' k, SafeEval W (.seq stackArraysBlock (.seq (stackPassBlock keyLeaf) bpEmitBlock)) s s' k ∧
      k ≤ 79 * xs.length + 19 ∧ s'.status = .running ∧
      s'.extent = s.extent + 3 * (xs.length + 1) + 2 * xs.length ∧
      (∀ a, a < s.extent → s'.memory a = s.memory a) ∧
      Region s' (s.extent + 3 * (xs.length + 1)) (2 * xs.length)
        (fun k => ((shape xs).bpCode.map SuccinctSpace.bitToNat).getD k 0) ∧
      (∀ r : Nat, ¬ (4 ≤ r ∧ r ≤ 8) → r ≠ 10 → r ≠ 12 → ¬ (100 ≤ r ∧ r ≤ 114) →
        s'.regs r = s.regs r) ∧
      s'.keys = s.keys :=
  cartesianBP_spec hW xs (OracleInput xs) keyLeaf (keyLeaf_spec hW xs) s hrun hzero hone hn hkeys
    (oracleInput_below xs s.extent) hcap

/-- **S3, word model** (under `InputFits W xs`, with the keys pre-supplied below
the current extent). -/
theorem cartesianBP_word {W : Nat} (hW : 32 ≤ W) (xs : List Int) (s : State)
    (hrun : s.status = .running) (hzero : s.regs 0 = 0) (hone : s.regs 2 = 1)
    (hn : s.regs 1 = xs.length) (hinp : WordInput W xs s)
    (hcap : s.extent + 3 * (xs.length + 1) + 2 * xs.length + 2 < 2 ^ W) :
    ∃ s' k, SafeEval W (.seq stackArraysBlock (.seq (stackPassBlock wordLeaf) bpEmitBlock)) s s' k ∧
      k ≤ 79 * xs.length + 19 ∧ s'.status = .running ∧
      s'.extent = s.extent + 3 * (xs.length + 1) + 2 * xs.length ∧
      (∀ a, a < s.extent → s'.memory a = s.memory a) ∧
      Region s' (s.extent + 3 * (xs.length + 1)) (2 * xs.length)
        (fun k => ((shape xs).bpCode.map SuccinctSpace.bitToNat).getD k 0) ∧
      (∀ r : Nat, ¬ (4 ≤ r ∧ r ≤ 8) → r ≠ 10 → r ≠ 12 → ¬ (100 ≤ r ∧ r ≤ 114) →
        s'.regs r = s.regs r) ∧
      s'.keys = s.keys :=
  cartesianBP_spec hW xs (WordInput W xs) wordLeaf (wordLeaf_spec hW xs) s hrun hzero hone hn hinp
    (wordInput_below W xs s.extent hinp.2.1) hcap

end S3Instances

end RMQ.SuccinctFinal.PackedConstruction.Proof
