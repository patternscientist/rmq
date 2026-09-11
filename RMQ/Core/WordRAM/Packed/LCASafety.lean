import RMQ.Core.WordRAM.Packed.QueryCorrect
import RMQ.Core.WordRAM.Packed.ReaderSafety

/-! # Scalar bounds and composition for the complete LCA controller -/

namespace RMQ.SuccinctFinal.PackedWordRAM

open Cartesian Structured SuccinctSpace PackedCellProbe SuccinctClose

theorem lca_size_envelope (n : Nat) : 2 * n + 2 ≤ metadataEnvelope n := by
  have hn := packedReviewerInputSize_lt_two_pow_cellWidth n
  have hq := Nat.two_pow_pos (packedReviewerCellWidth n)
  have hsq := Nat.le_mul_of_pos_right (2 ^ packedReviewerCellWidth n) hq
  unfold metadataEnvelope
  rw [Nat.pow_two]
  omega

theorem lca_two_envelopes_fit (n : Nat) :
    2 * metadataEnvelope n + 2 < 2 ^ wordWidth n := by
  have he := metadataEnvelope_pos n
  have hp := reader_polynomial_fit n
  omega

theorem MetadataMatches.lca_block_pos (shape : CartesianShape) (regs : Registers)
    (hm : MetadataMatches shape regs) : 0 < regs 33 := by
  have hb := hm 17 (by decide)
  change regs 33 = (metadata shape)[17]?.getD 0 at hb
  have hgeom : (metadata shape)[17]?.getD 0 = 2 * (shape.size.log2 + 1) := rfl
  rw [hb, hgeom]
  omega

theorem lcaInitBlock_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) :
    lcaInitBlock.Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  have hp := hm.lca_block_pos shape regs
  have hl := fit.1 1200
  have hr := fit.1 1201
  dsimp only at hl hr
  have hld := Nat.div_le_self (regs 1200) (regs 33)
  have hrd := Nat.div_le_self (regs 1201) (regs 33)
  have hone := lca_two_envelopes_fit shape.size
  have hwne : wordWidth shape.size ≠ 0 := by unfold wordWidth; omega
  apply ScalarChecks_safe _ _ _ _ fit
  by_cases heq : regs 1200 / regs 33 = regs 1201 / regs 33
  all_goals simp [ScalarChecks, lcaInitBlock, Block.sequence, Block.eval, Action.eval,
    Action.instruction, Action.LocalSafe, execute, State.writeNext, Data.ofState,
    Registers.write, Arithmetic.eval, Comparison.eval, hwne, heq] <;> omega

theorem lcaSamePrepareBlock_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hone : regs 1214 = 1) (hl : regs 1200 ≤ 2 * shape.size)
    (hr : regs 1201 ≤ 2 * shape.size) :
    lcaSamePrepareBlock.Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  have he := lca_size_envelope shape.size
  have hp := lca_two_envelopes_fit shape.size
  have hwne : wordWidth shape.size ≠ 0 := by unfold wordWidth; omega
  apply ScalarChecks_safe _ _ _ _ fit
  by_cases hsub : regs 1200 ≤ regs 1201
  all_goals simp [ScalarChecks, lcaSamePrepareBlock, Block.sequence, Block.eval, Action.eval,
    Action.instruction, Action.LocalSafe, execute, State.writeNext, Data.ofState,
    Registers.write, Arithmetic.eval, Comparison.eval, natSubBlock, hone, hsub, hwne] <;> omega

theorem lcaCrossLeftPrepareBlock_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (hone : regs 1214 = 1)
    (hl : regs 1200 ≤ 2 * shape.size) (hlb : regs 1203 = regs 1200 / regs 33) :
    lcaCrossLeftPrepareBlock.Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  have he := lca_size_envelope shape.size
  have hp := lca_two_envelopes_fit shape.size
  have hb := hm.envelope shape regs 33 (by decide)
  have hmul : regs 1203 * regs 33 ≤ regs 1200 := by rw [hlb]; exact Nat.div_mul_le_self _ _
  have hwne : wordWidth shape.size ≠ 0 := by unfold wordWidth; omega
  apply ScalarChecks_safe _ _ _ _ fit
  by_cases hsub : regs 1200 ≤ regs 1203 * regs 33 + regs 33
  all_goals simp [ScalarChecks, lcaCrossLeftPrepareBlock, Block.sequence, Block.eval, Action.eval,
    Action.instruction, Action.LocalSafe, execute, State.writeNext, Data.ofState,
    Registers.write, Arithmetic.eval, Comparison.eval, natSubBlock, hone, hsub, hwne] <;> omega

theorem lcaCrossRightPrepareBlock_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hr : regs 1201 ≤ 2 * shape.size) (hrb : regs 1204 = regs 1201 / regs 33) :
    lcaCrossRightPrepareBlock.Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  have he := lca_size_envelope shape.size
  have hp := lca_two_envelopes_fit shape.size
  have hmul : regs 1204 * regs 33 ≤ regs 1201 := by rw [hrb]; exact Nat.div_mul_le_self _ _
  have hwne : wordWidth shape.size ≠ 0 := by unfold wordWidth; omega
  apply ScalarChecks_safe _ _ _ _ fit
  simp [ScalarChecks, lcaCrossRightPrepareBlock, Block.sequence, Block.eval, Action.eval,
    Action.instruction, Action.LocalSafe, execute, State.writeNext, Data.ofState,
    Registers.write, Arithmetic.eval, Comparison.eval, natSubBlock, hmul, hwne]
  omega

theorem lcaFinishBlock_safe (memory : Memory) (width : Nat) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits width) (one : 1 < 2 ^ width)
    (hone : regs 1214 = 1) : lcaFinishBlock.Safe memory width ⟨regs, .running⟩ := by
  have hp := fit.1 7002
  dsimp only at hp
  have hwne : width ≠ 0 := by intro h; simp [h] at one
  apply ScalarChecks_safe _ _ _ _ fit
  by_cases hz : regs 7000 = 0
  · simp [ScalarChecks, lcaFinishBlock, hz]
  · by_cases hsub : 1 ≤ regs 7002
    all_goals simp [ScalarChecks, lcaFinishBlock, Block.sequence, Block.eval, Action.eval,
      Action.instruction, Action.LocalSafe, execute, State.writeNext, Data.ofState,
      Registers.write, Arithmetic.eval, Comparison.eval, natSubBlock, hone, hsub, hwne, hz] <;> omega

def CanonicalFringeSafety (shape : CartesianShape) : Prop :=
  ∀ regs : Registers, (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size) →
    MetadataMatches shape regs → regs 1104 ≤ metadataEnvelope shape.size →
    regs 1105 ≤ metadataEnvelope shape.size → regs 1106 ≤ metadataEnvelope shape.size →
    (fringeBlock logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩

def CanonicalInteriorSafety (shape : CartesianShape) : Prop :=
  ∀ regs : Registers, (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size) →
    MetadataMatches shape regs → regs 896 ≤ metadataEnvelope shape.size →
    regs 897 ≤ metadataEnvelope shape.size →
    (interiorRangeBlock logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩

theorem candidateSaveBlock_safe (memory : Memory) (width base : Nat) (s : Data)
    (fit : s.Fits width) : (candidateSaveBlock base).Safe memory width s := by
  apply SimpleScalar.safe memory width _ _ s fit
  simp [SimpleScalar, candidateSaveBlock, Block.sequence]

theorem candidateMergeLeftBlock_safe (memory : Memory) (width base : Nat) (s : Data)
    (fit : s.Fits width) (one : 1 < 2 ^ width) :
    (candidateMergeLeftBlock base).Safe memory width s := by
  apply SimpleScalar.safe memory width _ _ s fit
  simp [SimpleScalar, candidateMergeLeftBlock, candidateRestoreBlock, Block.sequence, one]

theorem candidateNoneBlock_safe (memory : Memory) (width : Nat) (s : Data)
    (fit : s.Fits width) : candidateNoneBlock.Safe memory width s := by
  apply SimpleScalar.safe memory width _ _ s fit
  simp [SimpleScalar, candidateNoneBlock, Block.sequence, Nat.two_pow_pos]

theorem lcaSameBlock_safe_with_fringe (shape : CartesianShape)
    (hfringe : CanonicalFringeSafety shape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (hone : regs 1214 = 1)
    (hl : regs 1200 ≤ 2 * shape.size) (hr : regs 1201 ≤ 2 * shape.size) :
    (lcaSameBlock logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  have hs := lcaSamePrepareBlock_safe shape regs fit hone hl hr
  apply Block.safe_seq hs
  have fp := lcaSamePrepareBlock.eval_fits _ _ _ hs
  have hp := lcaSamePrepareBlock_source (shapeMemory shape) regs hone
  have hframe (r : Nat) (hout : ¬ LCAPrepareWrites r) :=
    Block.eval_frame (shapeMemory shape) _ _ lcaSamePrepareBlock_writes r hout ⟨regs, .running⟩
  generalize he : lcaSamePrepareBlock.eval (shapeMemory shape) ⟨regs, .running⟩ = actual at fp hp hframe ⊢
  rcases actual with ⟨⟨ar, ast⟩, reads⟩
  dsimp only at fp hp hframe ⊢
  obtain ⟨hst, _, hc, hstart, hspan⟩ := hp
  subst ast
  have hmeta : MetadataMatches shape ar := by
    intro i hi; rw [hframe _ (by unfold LCAPrepareWrites; omega)]; exact hm i hi
  have he := lca_size_envelope shape.size
  exact hfringe ar fp hmeta (by rw [hc]; omega) (by rw [hstart]; omega) (by rw [hspan]; omega)

theorem lcaCrossLeftBlock_safe_with_fringe (shape : CartesianShape)
    (hfringe : CanonicalFringeSafety shape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (hone : regs 1214 = 1)
    (hl : regs 1200 ≤ 2 * shape.size) (hlb : regs 1203 = regs 1200 / regs 33) :
    (lcaCrossLeftBlock logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  have hs := lcaCrossLeftPrepareBlock_safe shape regs fit hm hone hl hlb
  apply Block.safe_seq hs
  have fp := lcaCrossLeftPrepareBlock.eval_fits _ _ _ hs
  have hp := lcaCrossLeftPrepareBlock_source (shapeMemory shape) regs hone
  have hframe (r : Nat) (hout : ¬ LCAPrepareWrites r) :=
    Block.eval_frame (shapeMemory shape) _ _ lcaCrossLeftPrepareBlock_writes r hout ⟨regs, .running⟩
  generalize he : lcaCrossLeftPrepareBlock.eval (shapeMemory shape) ⟨regs, .running⟩ = actual at fp hp hframe ⊢
  rcases actual with ⟨⟨ar, ast⟩, reads⟩
  dsimp only at fp hp hframe ⊢
  obtain ⟨hst, _, hc, hstart, hspan⟩ := hp
  subst ast
  have hmeta : MetadataMatches shape ar := by
    intro i hi; rw [hframe _ (by unfold LCAPrepareWrites; omega)]; exact hm i hi
  have he := lca_size_envelope shape.size
  have hb := hm.envelope shape regs 33 (by decide)
  have hmul : regs 1203 * regs 33 ≤ regs 1200 := by rw [hlb]; exact Nat.div_mul_le_self _ _
  have hf := hfringe ar fp hmeta (by rw [hc]; omega) (by rw [hstart]; omega) (by rw [hspan]; omega)
  exact Block.safe_seq hf (candidateSaveBlock_safe _ _ 1205 _ (Block.eval_fits _ _ _ _ hf))

theorem lcaCrossRightBlock_safe_with_fringe (shape : CartesianShape)
    (hfringe : CanonicalFringeSafety shape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (hr : regs 1201 ≤ 2 * shape.size)
    (hrb : regs 1204 = regs 1201 / regs 33) :
    (lcaCrossRightBlock logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  have hs := lcaCrossRightPrepareBlock_safe shape regs fit hr hrb
  apply Block.safe_seq hs
  have fp := lcaCrossRightPrepareBlock.eval_fits _ _ _ hs
  have hp := lcaCrossRightPrepareBlock_source (shapeMemory shape) regs
  have hframe (r : Nat) (hout : ¬ LCAPrepareWrites r) :=
    Block.eval_frame (shapeMemory shape) _ _ lcaCrossRightPrepareBlock_writes r hout ⟨regs, .running⟩
  generalize he : lcaCrossRightPrepareBlock.eval (shapeMemory shape) ⟨regs, .running⟩ = actual at fp hp hframe ⊢
  rcases actual with ⟨⟨ar, ast⟩, reads⟩
  dsimp only at fp hp hframe ⊢
  obtain ⟨hst, _, hc, hstart, hspan⟩ := hp
  subst ast
  have hmeta : MetadataMatches shape ar := by
    intro i hi; rw [hframe _ (by unfold LCAPrepareWrites; omega)]; exact hm i hi
  have he := lca_size_envelope shape.size
  have hp := lca_two_envelopes_fit shape.size
  have hmul : regs 1204 * regs 33 ≤ regs 1201 := by rw [hrb]; exact Nat.div_mul_le_self _ _
  have hf := hfringe ar fp hmeta (by rw [hc]; omega) (by rw [hstart]; omega) (by rw [hspan]; omega)
  exact Block.safe_seq hf (candidateMergeLeftBlock_safe _ _ 1208 _ (Block.eval_fits _ _ _ _ hf) (by omega))

theorem lcaCrossMiddleInitBlock_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hone : regs 1214 = 1) (hlb : regs 1203 ≤ 2 * shape.size) :
    lcaCrossMiddleInitBlock.Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  have he := lca_size_envelope shape.size
  have hp := lca_two_envelopes_fit shape.size
  have hwne : wordWidth shape.size ≠ 0 := by unfold wordWidth; omega
  apply ScalarChecks_safe _ _ _ _ fit
  by_cases hlt : regs 1203 + 1 < regs 1204
  all_goals simp [ScalarChecks, lcaCrossMiddleInitBlock, Block.sequence, Block.eval, Action.eval,
    Action.instruction, Action.LocalSafe, execute, State.writeNext, Data.ofState,
    Registers.write, Arithmetic.eval, Comparison.eval, hone, hwne, hlt] <;> omega

theorem lcaCrossMiddleCountBlock_safe (memory : Memory) (width : Nat) (s : Data)
    (fit : s.Fits width) (one : 1 < 2 ^ width) :
    lcaCrossMiddleCountBlock.Safe memory width s := by
  have first := natSubBlock_safe memory width 897 1204 1203 1215 s fit one (by decide) (by decide)
  exact Block.safe_seq first (natSubBlock_safe memory width 897 897 1214 1215 _
    (Block.eval_fits _ _ _ _ first) one (by decide) (by decide))

theorem lcaMiddleWithCount_safe (shape : CartesianShape)
    (hinterior : CanonicalInteriorSafety shape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (hone : regs 1214 = 1)
    (hstart : regs 896 ≤ metadataEnvelope shape.size) (hrb : regs 1204 ≤ 2 * shape.size) :
    (Block.seq lcaCrossMiddleCountBlock (interiorRangeBlock logicalReadBlock)).Safe
      (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  have hp := lca_two_envelopes_fit shape.size
  have hs := lcaCrossMiddleCountBlock_safe (shapeMemory shape) (wordWidth shape.size)
    ⟨regs, .running⟩ fit (by omega)
  apply Block.safe_seq hs
  have fp := lcaCrossMiddleCountBlock.eval_fits _ _ _ hs
  have hc := lcaCrossMiddleCountBlock_source (shapeMemory shape) regs hone
  have hf (r : Nat) (hout : r ≠ 897 ∧ r ≠ 1215) :=
    Block.eval_frame (shapeMemory shape) _ _ lcaCrossMiddleCountBlock_writes r (by omega) ⟨regs, .running⟩
  generalize he : lcaCrossMiddleCountBlock.eval (shapeMemory shape) ⟨regs, .running⟩ = actual at fp hc hf ⊢
  rcases actual with ⟨⟨ar, ast⟩, reads⟩
  dsimp only at fp hc hf ⊢
  obtain ⟨hst, _, hcount⟩ := hc
  subst ast
  have hmeta : MetadataMatches shape ar := by
    intro i hi; rw [hf _ (by omega)]; exact hm i hi
  have he := lca_size_envelope shape.size
  exact hinterior ar fp hmeta (by rw [hf 896 (by decide)]; exact hstart) (by rw [hcount]; omega)

theorem lcaCrossMiddleBlock_safe_with_interior (shape : CartesianShape)
    (hinterior : CanonicalInteriorSafety shape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (hone : regs 1214 = 1)
    (hlb : regs 1203 ≤ 2 * shape.size) (hrb : regs 1204 ≤ 2 * shape.size) :
    (lcaCrossMiddleBlock logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  have hs := lcaCrossMiddleInitBlock_safe shape regs fit hone hlb
  apply Block.safe_seq hs
  have fp := lcaCrossMiddleInitBlock.eval_fits _ _ _ hs
  have hp := lcaCrossMiddleInitBlock_source (shapeMemory shape) regs hone
  have hf (r : Nat) (hout : r ≠ 896 ∧ r ≠ 1215) :=
    Block.eval_frame (shapeMemory shape) _ _ lcaCrossMiddleInitBlock_writes r (by omega) ⟨regs, .running⟩
  generalize he : lcaCrossMiddleInitBlock.eval (shapeMemory shape) ⟨regs, .running⟩ = actual at fp hp hf ⊢
  rcases actual with ⟨⟨ar, ast⟩, reads⟩
  dsimp only at fp hp hf ⊢
  obtain ⟨hst, _, hstart, _⟩ := hp
  subst ast
  have hmeta : MetadataMatches shape ar := by
    intro i hi; rw [hf _ (by omega)]; exact hm i hi
  have he := lca_size_envelope shape.size
  apply Block.safe_ifZero fp
  split
  · exact candidateNoneBlock_safe _ _ _ fp
  · exact lcaMiddleWithCount_safe shape hinterior ar fp hmeta
      (by rw [hf 1214 (by decide)]; exact hone) (by rw [hstart]; omega)
      (by rw [hf 1204 (by decide)]; exact hrb)

structure LCACaller (shape : CartesianShape) (regs : Registers) : Prop where
  metadata : MetadataMatches shape regs
  left : regs 1200 ≤ 2 * shape.size
  right : regs 1201 ≤ 2 * shape.size
  one : regs 1214 = 1
  leftBlock : regs 1203 = regs 1200 / regs 33
  rightBlock : regs 1204 = regs 1201 / regs 33

def LCAProtected (r : Nat) : Prop := r < 190 ∨ r = 1200 ∨ r = 1201 ∨ r = 1203 ∨ r = 1204 ∨ r = 1214

theorem LCACaller.frame (shape : CartesianShape) (before after : Registers)
    (h : LCACaller shape before) (hf : ∀ r, LCAProtected r → after r = before r) :
    LCACaller shape after := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi; rw [hf _ (by unfold LCAProtected; omega)]; exact h.metadata i hi
  · rw [hf 1200 (by simp [LCAProtected])]; exact h.left
  · rw [hf 1201 (by simp [LCAProtected])]; exact h.right
  · rw [hf 1214 (by simp [LCAProtected])]; exact h.one
  · rw [hf 1203 (by simp [LCAProtected]), hf 1200 (by simp [LCAProtected]), hf 33 (by simp [LCAProtected])]; exact h.leftBlock
  · rw [hf 1204 (by simp [LCAProtected]), hf 1201 (by simp [LCAProtected]), hf 33 (by simp [LCAProtected])]; exact h.rightBlock

def LCASafeBlock (shape : CartesianShape) (block : Block) : Prop :=
  ∀ regs : Registers, (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size) → LCACaller shape regs →
    block.Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ ∧
    (block.eval (shapeMemory shape) ⟨regs, .running⟩).final.status = .running ∧
    LCACaller shape (block.eval (shapeMemory shape) ⟨regs, .running⟩).final.regs

theorem lcaSafeBlock_of (shape : CartesianShape) (block : Block) (allowed : Nat → Prop)
    (hw : block.WritesOnly allowed) (hout : ∀ r, LCAProtected r → ¬ allowed r)
    (safe : ∀ regs, (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size) → LCACaller shape regs →
      block.Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩)
    (running : ∀ regs, LCACaller shape regs →
      (block.eval (shapeMemory shape) ⟨regs, .running⟩).final.status = .running) :
    LCASafeBlock shape block := by
  intro regs fit caller
  exact ⟨safe regs fit caller, running regs caller,
    caller.frame shape regs _ (fun r hr => Block.eval_frame _ _ _ hw r (hout r hr) _)⟩

theorem LCASafeBlock.seq (shape : CartesianShape) (first second : Block)
    (hfirst : LCASafeBlock shape first) (hsecond : LCASafeBlock shape second) :
    LCASafeBlock shape (.seq first second) := by
  intro regs fit caller
  have ha := hfirst regs fit caller
  have fa := first.eval_fits _ _ _ ha.1
  generalize he : first.eval (shapeMemory shape) ⟨regs, .running⟩ = actual at ha fa
  rcases actual with ⟨⟨ar, ast⟩, reads⟩
  dsimp only at ha fa
  obtain ⟨hsafe, hstatus, hcaller⟩ := ha
  subst ast
  have hb := hsecond ar fa hcaller
  refine ⟨Block.safe_seq hsafe (by rw [he]; exact hb.1), ?_, ?_⟩
  · simpa only [Block.eval_seq, he, Evaluation.bind] using hb.2.1
  · simpa only [Block.eval_seq, he, Evaluation.bind] using hb.2.2

theorem lcaProtected_not_cross (r : Nat) (hr : LCAProtected r) : ¬ LCACrossWrites r := by
  unfold LCAProtected at hr
  unfold LCACrossWrites LCALeftWrites LCAMiddleWrites LCAMergeSaveWrites LCARightWrites
    LCASameWrites LCAPrepareWrites LCAInteriorWrites FringeWrites FringeSeedWrites
    FringeWindowWrites FringeFoldWrites WindowWrites RankWrapperWrites
  omega

theorem lcaCrossLeftBlock_lcaSafe (shape : CartesianShape) (hf : CanonicalFringeSafety shape) :
    LCASafeBlock shape (lcaCrossLeftBlock logicalReadBlock) := by
  apply lcaSafeBlock_of shape _ LCALeftWrites
    (lcaCrossLeftBlock_writes logicalReadBlock logicalReadBlock_writesOnly)
    (fun r hr h => lcaProtected_not_cross r hr (Or.inl h))
  · intro regs fit caller
    exact lcaCrossLeftBlock_safe_with_fringe shape hf regs fit caller.metadata caller.one caller.left caller.leftBlock
  · intro regs caller
    exact (lcaCrossLeftBlock_source shape (shapeMemory shape) logicalReadBlock
      (logicalReadBlock_correct shape) logicalReadBlock_writesOnly regs caller.metadata caller.one).1

theorem lcaCrossRightBlock_lcaSafe (shape : CartesianShape) (hf : CanonicalFringeSafety shape) :
    LCASafeBlock shape (lcaCrossRightBlock logicalReadBlock) := by
  apply lcaSafeBlock_of shape _ LCARightWrites
    (lcaCrossRightBlock_writes logicalReadBlock logicalReadBlock_writesOnly)
    (fun r hr h => lcaProtected_not_cross r hr (Or.inr (Or.inr (Or.inr h))))
  · intro regs fit caller
    exact lcaCrossRightBlock_safe_with_fringe shape hf regs fit caller.metadata caller.right caller.rightBlock
  · intro regs caller
    exact (lcaCrossRightBlock_source shape (shapeMemory shape) logicalReadBlock
      (logicalReadBlock_correct shape) logicalReadBlock_writesOnly regs caller.metadata).1

theorem lcaCrossMiddleBlock_lcaSafe (shape : CartesianShape) (hi : CanonicalInteriorSafety shape) :
    LCASafeBlock shape (lcaCrossMiddleBlock logicalReadBlock) := by
  apply lcaSafeBlock_of shape _ LCAMiddleWrites
    (lcaCrossMiddleProgram_writes _ (interiorRangeBlock_lcaWrites logicalReadBlock logicalReadBlock_writesOnly))
    (fun r hr h => lcaProtected_not_cross r hr (Or.inr (Or.inl h)))
  · intro regs fit caller
    apply lcaCrossMiddleBlock_safe_with_interior shape hi regs fit caller.metadata caller.one
    · rw [caller.leftBlock]; exact Nat.le_trans (Nat.div_le_self _ _) caller.left
    · rw [caller.rightBlock]; exact Nat.le_trans (Nat.div_le_self _ _) caller.right
  · intro regs caller
    exact (lcaCrossMiddleProgram_source shape (shapeMemory shape) _ (interiorRangeBlock_correct shape)
      regs caller.metadata caller.one).1

theorem lcaCrossMergeSaveBlock_lcaSafe (shape : CartesianShape) :
    LCASafeBlock shape lcaCrossMergeSaveBlock := by
  apply lcaSafeBlock_of shape _ LCAMergeSaveWrites lcaCrossMergeSaveBlock_writes
    (fun r hr h => lcaProtected_not_cross r hr (Or.inr (Or.inr (Or.inl h))))
  · intro regs fit _
    have hp := lca_two_envelopes_fit shape.size
    have hs := candidateMergeLeftBlock_safe (shapeMemory shape) (wordWidth shape.size) 1205 _ fit (by omega)
    exact Block.safe_seq hs (candidateSaveBlock_safe _ _ 1208 _ (Block.eval_fits _ _ _ _ hs))
  · intro regs _
    exact (lcaCrossMergeSaveBlock_source (shapeMemory shape) regs).1

theorem lcaCrossBlock_lcaSafe (shape : CartesianShape)
    (hf : CanonicalFringeSafety shape) (hi : CanonicalInteriorSafety shape) :
    LCASafeBlock shape (lcaCrossBlock logicalReadBlock) :=
  LCASafeBlock.seq shape _ _ (lcaCrossLeftBlock_lcaSafe shape hf)
    (LCASafeBlock.seq shape _ _ (lcaCrossMiddleBlock_lcaSafe shape hi)
      (LCASafeBlock.seq shape _ _ (lcaCrossMergeSaveBlock_lcaSafe shape) (lcaCrossRightBlock_lcaSafe shape hf)))

theorem lcaSameBlock_lcaSafe (shape : CartesianShape) (hf : CanonicalFringeSafety shape) :
    LCASafeBlock shape (lcaSameBlock logicalReadBlock) := by
  apply lcaSafeBlock_of shape _ LCASameWrites
    (lcaSameBlock_writes logicalReadBlock logicalReadBlock_writesOnly)
    (fun r hr h => lcaProtected_not_cross r hr (Or.inl (Or.inl h)))
  · intro regs fit caller
    exact lcaSameBlock_safe_with_fringe shape hf regs fit caller.metadata caller.one caller.left caller.right
  · intro regs caller
    exact (lcaSameBlock_source shape (shapeMemory shape) logicalReadBlock
      (logicalReadBlock_correct shape) logicalReadBlock_writesOnly regs caller.metadata caller.one).1

theorem LCASafeBlock.ifZero (shape : CartesianShape) (condition : Nat) (zero nonzero : Block)
    (hz : LCASafeBlock shape zero) (hn : LCASafeBlock shape nonzero) :
    LCASafeBlock shape (.ifZero condition zero nonzero) := by
  intro regs fit caller
  by_cases hc : regs condition = 0
  · have h := hz regs fit caller
    refine ⟨Block.safe_ifZero fit (by simpa only [if_pos hc] using h.1), ?_, ?_⟩
    · simpa only [Block.eval, if_pos rfl, if_pos hc] using h.2.1
    · simpa only [Block.eval, if_pos rfl, if_pos hc] using h.2.2
  · have h := hn regs fit caller
    refine ⟨Block.safe_ifZero fit (by simpa only [if_neg hc] using h.1), ?_, ?_⟩
    · simpa only [Block.eval, if_pos rfl, if_neg hc] using h.2.1
    · simpa only [Block.eval, if_pos rfl, if_neg hc] using h.2.2

theorem lcaChooseProgram_lcaSafe (shape : CartesianShape)
    (hf : CanonicalFringeSafety shape) (hi : CanonicalInteriorSafety shape) :
    LCASafeBlock shape (lcaChooseProgram logicalReadBlock (interiorRangeBlock logicalReadBlock)) :=
  LCASafeBlock.ifZero shape _ _ _ (lcaCrossBlock_lcaSafe shape hf hi) (lcaSameBlock_lcaSafe shape hf)

theorem lcaCloseBlock_running_safe_with_leaves (shape : CartesianShape)
    (hfringe : CanonicalFringeSafety shape) (hinterior : CanonicalInteriorSafety shape)
    (regs : Registers) (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (hl : regs 1200 ≤ 2 * shape.size)
    (hr : regs 1201 ≤ 2 * shape.size) :
    (lcaCloseBlock logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  have hs := lcaInitBlock_safe shape regs fit hm
  apply Block.safe_seq hs
  have fi := lcaInitBlock.eval_fits _ _ _ hs
  have source := lcaInitBlock_source (shapeMemory shape) regs
  have frame (r : Nat) (hout : r < 1202 ∨ (1205 ≤ r ∧ r ≠ 1214 ∧ r ≠ 1215)) :=
    Block.eval_frame (shapeMemory shape) _ _ lcaInitBlock_writes r (by omega) ⟨regs, .running⟩
  generalize he : lcaInitBlock.eval (shapeMemory shape) ⟨regs, .running⟩ = initialized at fi source frame ⊢
  rcases initialized with ⟨⟨ir, ist⟩, reads⟩
  dsimp only at fi source frame ⊢
  obtain ⟨hst, _, _, hone, hleft, hright, _⟩ := source
  subst ist
  have caller : LCACaller shape ir := by
    refine ⟨?_, ?_, ?_, hone, ?_, ?_⟩
    · intro i hi; rw [frame _ (Or.inl (by omega))]; exact hm i hi
    · rw [frame 1200 (by decide)]; exact hl
    · rw [frame 1201 (by decide)]; exact hr
    · rw [frame 1200 (by decide), frame 33 (by decide)]; exact hleft
    · rw [frame 1201 (by decide), frame 33 (by decide)]; exact hright
  have hc := lcaChooseProgram_lcaSafe shape hfringe hinterior ir fi caller
  apply Block.safe_seq hc.1
  have fc := Block.eval_fits _ _ _ _ hc.1
  generalize hec : (lcaChooseProgram logicalReadBlock (interiorRangeBlock logicalReadBlock)).eval
    (shapeMemory shape) ⟨ir, .running⟩ = chosen at hc fc ⊢
  rcases chosen with ⟨⟨cr, cst⟩, creads⟩
  dsimp only at hc fc ⊢
  obtain ⟨_, hst, hcaller⟩ := hc
  subst cst
  have hp := lca_two_envelopes_fit shape.size
  exact lcaFinishBlock_safe _ _ cr fc (by omega) hcaller.one

theorem lcaCloseBlock_safe_with_leaves (shape : CartesianShape)
    (hfringe : CanonicalFringeSafety shape) (hinterior : CanonicalInteriorSafety shape)
    (s : Data) (fit : s.Fits (wordWidth shape.size)) (hm : MetadataMatches shape s.regs)
    (hl : s.regs 1200 ≤ 2 * shape.size) (hr : s.regs 1201 ≤ 2 * shape.size) :
    (lcaCloseBlock logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) s := by
  by_cases hs : s.status = .running
  · cases s with
    | mk regs status =>
      dsimp only at hs
      subst status
      exact lcaCloseBlock_running_safe_with_leaves shape hfringe hinterior regs fit hm hl hr
  · exact Block.safe_stopped _ _ _ s fit hs

end RMQ.SuccinctFinal.PackedWordRAM
