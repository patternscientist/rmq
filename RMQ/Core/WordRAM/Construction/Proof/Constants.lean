import RMQ.Core.WordRAM.Construction.Builder.Program
import RMQ.Core.WordRAM.Construction.Contract

/-! # PRE-1 builder proofs: literal pins of the program constants (stage S7)

Outside the builder firewall, and independent of the stage proof tower, so a
change to a closure module rebuilds only these pins. `builderBudget_eq_mul_add`
gives the affine reading `C * n + D` of the amended fuel body (V3-6a)
propositionally. The source sizes and program lengths are pinned by `rfl` on the
compiled lists. The V3-4 leaf-difference theorem is proved at its contract type
through one simultaneous traversal of both compiled lists
(`filter_range_ne_eq_diffPositions`, then `rfl` on the traversal), and both V3-5
contract instances carry the literal length and encoded-word counts, each
checked by `rfl` on the compiled list.
-/

namespace RMQ.SuccinctFinal.PackedConstruction.Proof

open Structured

/-! ## Fuel body (V3-6a) -/

/-- The affine reading of the amended fuel body (V3-6a), proved propositionally. -/
theorem builderBudget_eq_mul_add : ∀ n, builderBudget n = 1000000000 * n + 1000000000 := by
  intro n
  unfold builderBudget
  omega

/-! ## Sizes -/

set_option maxRecDepth 100000 in
theorem builderSource_size_keyLeaf_eq : (builderSource keyLeaf).size = 2106 := by rfl

set_option maxRecDepth 100000 in
theorem builderSource_size_wordLeaf_eq : (builderSource wordLeaf).size = 2106 := by rfl

theorem builderSource_size_keyLeaf : (builderSource keyLeaf).size < 2 ^ 32 := by
  rw [builderSource_size_keyLeaf_eq]; decide

theorem builderSource_size_wordLeaf : (builderSource wordLeaf).size < 2 ^ 32 := by
  rw [builderSource_size_wordLeaf_eq]; decide

/-! ## Leaf difference (V3-4) -/

/-- Positions from `k` on at which two lists differ, by one simultaneous traversal. -/
def diffPositionsFrom {α : Type} [DecidableEq α] : List α → List α → Nat → List Nat
  | a :: as, b :: bs, k => if a = b then diffPositionsFrom as bs (k + 1) else k :: diffPositionsFrom as bs (k + 1)
  | _, _, _ => []

theorem filter_range'_eq_diffPositionsFrom {α : Type} [DecidableEq α] (L1 L2 : List α) :
    ∀ (as bs : List α) (k : Nat), L1.drop k = as → L2.drop k = bs → as.length = bs.length →
      (List.range' k as.length).filter (fun i => decide (L1[i]? ≠ L2[i]?)) =
        diffPositionsFrom as bs k
  | [], [], _, _, _, _ => by simp [diffPositionsFrom]
  | [], _ :: _, _, _, _, h => by simp at h
  | _ :: _, [], _, _, _, h => by simp at h
  | a :: as, b :: bs, k, h1, h2, hlen => by
      have e1 : L1[k]? = some a := by
        have : (L1.drop k)[0]? = some a := by rw [h1]; rfl
        simpa using this
      have e2 : L2[k]? = some b := by
        have : (L2.drop k)[0]? = some b := by rw [h2]; rfl
        simpa using this
      have d1 : L1.drop (k + 1) = as := by
        rw [← List.drop_drop, h1]; rfl
      have d2 : L2.drop (k + 1) = bs := by
        rw [← List.drop_drop, h2]; rfl
      have ih := filter_range'_eq_diffPositionsFrom L1 L2 as bs (k + 1) d1 d2
        (by simpa using hlen)
      rw [List.length_cons, List.range'_succ, List.filter_cons, e1, e2, ih]
      by_cases hab : a = b
      · subst hab; simp [diffPositionsFrom]
      · simp [diffPositionsFrom, hab]

/-- The positions at which two equal-length lists differ. -/
theorem filter_range_ne_eq_diffPositions {α : Type} [DecidableEq α] (L1 L2 : List α)
    (hlen : L1.length = L2.length) :
    (List.range L1.length).filter (fun i => decide (L1[i]? ≠ L2[i]?)) =
      diffPositionsFrom L1 L2 0 := by
  rw [List.range_eq_range']
  exact filter_range'_eq_diffPositionsFrom L1 L2 L1 L2 0 rfl rfl hlen

set_option maxRecDepth 100000 in
theorem builderProgram_length_eq : builderProgram.length = 2107 := by rfl

set_option maxRecDepth 100000 in
theorem builderProgramWord_length_eq : builderProgramWord.length = 2107 := by rfl

set_option maxRecDepth 100000 in
theorem builder_diffPositions_eq :
    diffPositionsFrom builderProgram builderProgramWord 0 =
      [411, 412, 413, 414, 415, 429, 430, 431, 432, 433] := by rfl

set_option maxRecDepth 100000 in
theorem builder_leaf_difference :
    builderProgram.length = builderProgramWord.length ∧
    (List.range builderProgram.length).filter
        (fun i => builderProgram[i]? ≠ builderProgramWord[i]?) =
      [411, 412, 413, 414, 415, 429, 430, 431, 432, 433] ∧
    ([411, 412, 413, 414, 415, 429, 430, 431, 432, 433] : List Nat).map (fun i => builderProgram[i]?) =
      [some ⟨.loadKey 0 4⟩, some ⟨.loadKey 1 5⟩, some ⟨.compareKey 6 0 1⟩, some ⟨.move 6 6⟩,
        some ⟨.move 6 6⟩, some ⟨.loadKey 0 4⟩, some ⟨.loadKey 1 5⟩, some ⟨.compareKey 6 0 1⟩,
        some ⟨.move 6 6⟩, some ⟨.move 6 6⟩] ∧
    ([411, 412, 413, 414, 415, 429, 430, 431, 432, 433] : List Nat).map (fun i => builderProgramWord[i]?) =
      [some ⟨.arithmetic .add 7 4 2⟩, some ⟨.load 7 7⟩, some ⟨.arithmetic .add 8 5 2⟩,
        some ⟨.load 8 8⟩, some ⟨.comparison .lt 6 7 8⟩, some ⟨.arithmetic .add 7 4 2⟩,
        some ⟨.load 7 7⟩, some ⟨.arithmetic .add 8 5 2⟩, some ⟨.load 8 8⟩,
        some ⟨.comparison .lt 6 7 8⟩] := by
  have hlen : builderProgram.length = builderProgramWord.length := by
    rw [builderProgram_length_eq, builderProgramWord_length_eq]
  refine ⟨hlen, ?_, by rfl, by rfl⟩
  rw [filter_range_ne_eq_diffPositions _ _ hlen, builder_diffPositions_eq]

/-! ## Contract instances (V3-5) -/

set_option maxRecDepth 100000 in
theorem builderProgram_programWords : programWords builderProgram = 8079 := by rfl

set_option maxRecDepth 100000 in
theorem builderProgramWord_programWords : programWords builderProgramWord = 8089 := by rfl

theorem builderProgram_contract :
    ProgramContract builderProgram (fun _ => builderProgram) 2107 8079 where
  uniform := closed_uniform builderProgram
  lengthPinned := builderProgram_length_eq
  encodedPinned := builderProgram_programWords
  codeBits := fun width => by
    unfold CodeAccounting
    rw [builderProgram_programWords]

theorem builderProgramWord_contract :
    ProgramContract builderProgramWord (fun _ => builderProgramWord) 2107 8089 where
  uniform := closed_uniform builderProgramWord
  lengthPinned := builderProgramWord_length_eq
  encodedPinned := builderProgramWord_programWords
  codeBits := fun width => by
    unfold CodeAccounting
    rw [builderProgramWord_programWords]

end RMQ.SuccinctFinal.PackedConstruction.Proof
