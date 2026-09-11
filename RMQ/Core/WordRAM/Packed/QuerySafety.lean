import RMQ.Core.WordRAM.Packed.SelectSafety
import RMQ.Core.WordRAM.Packed.LCASafety
import RMQ.Core.WordRAM.Packed.QueryObservations
import RMQ.Core.WordRAM.Packed.FringeSafety
import RMQ.Core.WordRAM.Packed.InteriorSafety

/-! # Word safety of the fixed complete guarded query

Every varying field is loaded by the charged setup. Proof-side stage predicates
compose the unchanged source before its fixed compiled execution is considered.
-/

namespace RMQ.SuccinctFinal.PackedWordRAM
open Cartesian Structured SuccinctSpace PackedCellProbe SuccinctClose

private structure QueryContext (shape : CartesianShape) (regs : Registers) : Prop where
  metadata : MetadataMatches shape regs
  one : regs 2048 = 1

private def QueryStage (shape : CartesianShape) (block : Block)
    (before after : Registers → Prop) : Prop :=
  ∀ regs, (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size) → before regs →
    block.Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ ∧
    (block.eval (shapeMemory shape) ⟨regs, .running⟩).final.status = .running ∧
    after (block.eval (shapeMemory shape) ⟨regs, .running⟩).final.regs

private theorem query_safe_follow {memory : Memory} {width : Nat}
    {first second : Block} {s : Data}
    (head : first.Safe memory width s)
    (tail : (first.eval memory s).final.Fits width → second.Safe memory width (first.eval memory s).final) :
    (Block.seq first second).Safe memory width s :=
  Block.safe_seq head (tail (Block.eval_fits _ _ _ _ head))

private theorem QueryStage.seq (shape : CartesianShape) (first second program : Block)
    (programEq : program = .seq first second) (before middle after : Registers → Prop)
    (a : QueryStage shape first before middle) (b : QueryStage shape second middle after) :
    QueryStage shape program before after := by
  subst program
  intro regs fit pre
  have ha := a regs fit pre
  have fm := Block.eval_fits _ _ _ _ ha.1
  generalize he : first.eval (shapeMemory shape) ⟨regs, .running⟩ = mid at ha fm ⊢
  rcases mid with ⟨⟨mr, mst⟩, reads⟩
  dsimp only at ha fm
  have hs := ha.2.1
  subst mst
  have hb := b mr fm ha.2.2
  refine ⟨Block.safe_seq ha.1 ?_, ?_, ?_⟩
  · rw [he]; exact hb.1
  · simpa only [Block.eval_seq, Evaluation.bind, he] using hb.2.1
  · simpa only [Block.eval_seq, Evaluation.bind, he] using hb.2.2

private theorem QueryStage.adapt (shape : CartesianShape) (block : Block)
    (before after before' after' : Registers → Prop)
    (stage : QueryStage shape block before after)
    (pre : ∀ regs, before' regs → before regs) (post : ∀ regs, after regs → after' regs) :
    QueryStage shape block before' after' := by
  intro regs fit h
  have result := stage regs fit (pre regs h)
  exact ⟨result.1, result.2.1, post _ result.2.2⟩

private theorem QueryStage.ifZero (shape : CartesianShape) (condition : Nat)
    (zero nonzero program : Block) (programEq : program = .ifZero condition zero nonzero)
    (before after : Registers → Prop)
    (hz : QueryStage shape zero before after) (hn : QueryStage shape nonzero before after) :
    QueryStage shape program before after := by
  subst program
  intro regs fit pre
  by_cases hc : regs condition = 0
  · have h := hz regs fit pre
    refine ⟨Block.safe_ifZero fit (by simpa only [if_pos hc] using h.1), ?_, ?_⟩
    · simpa only [Block.eval, if_pos rfl, if_pos hc] using h.2.1
    · simpa only [Block.eval, if_pos rfl, if_pos hc] using h.2.2
  · have h := hn regs fit pre
    refine ⟨Block.safe_ifZero fit (by simpa only [if_neg hc] using h.1), ?_, ?_⟩
    · simpa only [Block.eval, if_pos rfl, if_neg hc] using h.2.1
    · simpa only [Block.eval, if_pos rfl, if_neg hc] using h.2.2

private theorem query_skip_stage (shape : CartesianShape) (before after : Registers → Prop)
    (imp : ∀ regs, before regs → after regs) : QueryStage shape .skip before after := by
  intro regs fit hp
  exact ⟨Block.safe_skip _ _ _ fit, rfl, imp regs hp⟩

private theorem QueryContext.frame (shape : CartesianShape) (before after : Registers)
    (context : QueryContext shape before)
    (frame : ∀ r, (16 ≤ r ∧ r < 190) ∨ r = 2048 → after r = before r) :
    QueryContext shape after := by
  refine ⟨?_, (frame 2048 (Or.inr rfl)).trans context.one⟩
  intro i hi
  rw [frame (16 + i) (Or.inl (by omega))]
  exact context.metadata i hi

private theorem query_context_stage (shape : CartesianShape) (block : Block) (allowed : Nat → Prop)
    (writes : block.WritesOnly allowed)
    (outside : ∀ r, ((16 ≤ r ∧ r < 190) ∨ r = 2048) → ¬ allowed r)
    (safe : ∀ regs, (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size) →
      QueryContext shape regs → block.Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩)
    (running : ∀ regs, QueryContext shape regs →
      (block.eval (shapeMemory shape) ⟨regs, .running⟩).final.status = .running) :
    QueryStage shape block (QueryContext shape) (QueryContext shape) := by
  intro regs fit context
  exact ⟨safe regs fit context, running regs context, QueryContext.frame shape regs _ context
    (fun r hr => Block.eval_frame (shapeMemory shape) block allowed writes r (outside r hr) ⟨regs, .running⟩)⟩

private theorem query_stage_output (shape : CartesianShape) (block : Block) (before after : Registers → Prop)
    (stage : QueryStage shape block before after) (output bound : Nat)
    (valueBound : ∀ regs, before regs →
      (block.eval (shapeMemory shape) ⟨regs, .running⟩).final.regs output ≤ bound) :
    QueryStage shape block before (fun regs => after regs ∧ regs output ≤ bound) := by
  intro regs fit pre
  have h := stage regs fit pre
  exact ⟨h.1, h.2.1, h.2.2, valueBound regs pre⟩

private theorem query_stage_keep (shape : CartesianShape) (block : Block) (before after : Registers → Prop)
    (stage : QueryStage shape block before after) (output bound : Nat)
    (frame : ∀ regs, (block.eval (shapeMemory shape) ⟨regs, .running⟩).final.regs output = regs output) :
    QueryStage shape block (fun regs => before regs ∧ regs output ≤ bound)
      (fun regs => after regs ∧ regs output ≤ bound) := by
  intro regs fit pre
  have h := stage regs fit pre.1
  exact ⟨h.1, h.2.1, h.2.2, by rw [frame regs]; exact pre.2⟩

theorem queryAnswerPrepareBlock_safe (memory : Memory) (width : Nat)
    (one : 1 < 2 ^ width) (s : Data) (fit : s.Fits width) :
    queryAnswerPrepareBlock.Safe memory width s := by
  exact Block.safe_seq (natSubBlock_safe memory width 1200 2049 2048 2051 s fit one (by decide) (by decide))
    (natSubBlock_safe memory width 1201 2050 2048 2051 _
      (Block.eval_fits _ _ _ _ (natSubBlock_safe memory width 1200 2049 2048 2051 s fit one (by decide) (by decide))) one (by decide) (by decide))

theorem queryRankFinishBlock_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size)) (hone : regs 2048 = 1) :
    queryRankFinishBlock.Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ := by
  have one := select_constant_fit shape.size 1 (by decide)
  have sub := natSubBlock_safe (shapeMemory shape) (wordWidth shape.size) 3 360 2048 2051 ⟨regs, .running⟩ fit one (by decide) (by decide)
  refine query_safe_follow sub (fun fp => ?_)
  have source := natSubBlock_source 3 360 2048 2051 (shapeMemory shape) regs (by decide) (by decide)
  rw [source] at fp ⊢
  apply Block.safe_action _ _ _ _ fp
  have rankFit : regs 360 < 2 ^ wordWidth shape.size := fit.1 360
  simp [Action.LocalSafe, Arithmetic.eval, Registers.write, hone]
  omega


private theorem query_move_stage (shape : CartesianShape) (dst src : Nat)
    (outside : (dst < 16 ∨ 190 ≤ dst) ∧ dst ≠ 2048) :
    QueryStage shape (.action (.move dst src)) (QueryContext shape) (QueryContext shape) := by
  apply query_context_stage shape (.action (.move dst src)) (fun r => r = dst) rfl
  · intro r hr hd; omega
  · intro regs fit _; exact Block.safe_action _ _ _ _ fit (fit.1 src)
  · intro regs _; rfl

private theorem query_rank_stage (shape : CartesianShape) :
    QueryStage shape (rankCloseBlock logicalReadBlock) (QueryContext shape) (QueryContext shape) := by
  apply query_context_stage shape _ RankWrapperWrites
    (rankCloseBlock_writes logicalReadBlock logicalReadBlock_writesOnly)
  · intro r hr; unfold RankWrapperWrites; omega
  · intro regs fit context; exact rankCloseBlock_safe shape _ fit context.metadata
  · intro regs context
    exact (rankCloseBlock_source shape (shapeMemory shape) logicalReadBlock
      (logicalReadBlock_correct shape) logicalReadBlock_writesOnly regs context.metadata).1

private theorem query_finish_stage (shape : CartesianShape) :
    QueryStage shape queryRankFinishBlock (QueryContext shape) (QueryContext shape) := by
  apply query_context_stage shape _ (fun r => r = 3 ∨ r = 2051) queryRankFinishBlock_writes
  · intro r hr hw; omega
  · intro regs fit context; exact queryRankFinishBlock_safe shape regs fit context.one
  · intro regs context; exact (queryRankFinishBlock_source (shapeMemory shape) regs context.one).1

private theorem query_final_rank_stage (shape : CartesianShape) :
    QueryStage shape (queryFinalRankBlock logicalReadBlock) (QueryContext shape) (QueryContext shape) :=
  QueryStage.seq shape (.action (.move 352 1202))
    (.seq (rankCloseBlock logicalReadBlock) queryRankFinishBlock) (queryFinalRankBlock logicalReadBlock) rfl
    _ _ _ (query_move_stage shape 352 1202 (by decide))
    (QueryStage.seq shape _ _ _ rfl _ _ _ (query_rank_stage shape) (query_finish_stage shape))

theorem queryFinalRankBlock_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (hone : regs 2048 = 1) :
    (queryFinalRankBlock logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ :=
  (query_final_rank_stage shape regs fit ⟨hm, hone⟩).1

private theorem query_after_lca_stage (shape : CartesianShape) :
    QueryStage shape (queryAfterLCABlock logicalReadBlock) (QueryContext shape) (QueryContext shape) :=
  QueryStage.ifZero shape 1202 .skip (queryFinalRankBlock logicalReadBlock) _ rfl _ _
    (query_skip_stage shape _ _ (fun _ h => h)) (query_final_rank_stage shape)

private def QuerySelected (shape : CartesianShape) (regs : Registers) : Prop :=
  QueryContext shape regs ∧ regs 2049 ≤ 2 * shape.size ∧ regs 2050 ≤ 2 * shape.size

private def QueryCloses (shape : CartesianShape) (regs : Registers) : Prop :=
  QueryContext shape regs ∧ regs 1200 ≤ 2 * shape.size ∧ regs 1201 ≤ 2 * shape.size

private theorem query_prepare_stage (shape : CartesianShape) :
    QueryStage shape queryAnswerPrepareBlock (QuerySelected shape) (QueryCloses shape) := by
  intro regs fit pre
  have safe := queryAnswerPrepareBlock_safe (shapeMemory shape) (wordWidth shape.size)
    (select_constant_fit shape.size 1 (by decide)) ⟨regs, .running⟩ fit
  have source := queryAnswerPrepareBlock_source (shapeMemory shape) regs pre.1.one
  have frame (r : Nat) (ho : r ≠ 1200 ∧ r ≠ 1201 ∧ r ≠ 2051) :=
    Block.eval_frame (shapeMemory shape) _ _ queryAnswerPrepareBlock_writes r (by omega) ⟨regs, .running⟩
  refine ⟨safe, source.1, QueryContext.frame shape regs _ pre.1 (fun r hr => frame r (by omega)), ?_, ?_⟩
  · rw [source.2.2.1]; exact Nat.le_trans (Nat.sub_le _ _) pre.2.1
  · rw [source.2.2.2]; exact Nat.le_trans (Nat.sub_le _ _) pre.2.2

private theorem query_lca_protected (r : Nat)
    (hr : (16 ≤ r ∧ r < 190) ∨ r = 2048) : ¬ LCACloseWrites r := by
  unfold LCACloseWrites LCAChooseWrites LCACrossWrites LCALeftWrites LCAMiddleWrites
    LCAMergeSaveWrites LCARightWrites LCASameWrites LCAPrepareWrites LCAInteriorWrites
    FringeWrites FringeSeedWrites RankWrapperWrites FringeWindowWrites WindowWrites FringeFoldWrites
  omega

private theorem query_lca_stage (shape : CartesianShape)
    (hf : CanonicalFringeSafety shape) (hi : CanonicalInteriorSafety shape) :
    QueryStage shape (lcaCloseBlock logicalReadBlock) (QueryCloses shape) (QueryContext shape) := by
  intro regs fit pre
  have safe := lcaCloseBlock_safe_with_leaves shape hf hi ⟨regs, .running⟩ fit pre.1.metadata pre.2.1 pre.2.2
  have source := lcaCloseBlock_correct shape regs pre.1.metadata
  have frame := Block.eval_frame (shapeMemory shape) _ _
    (lcaCloseBlock_writes logicalReadBlock logicalReadBlock_writesOnly)
  exact ⟨safe, source.1, QueryContext.frame shape regs _ pre.1
    (fun r hr => frame r (query_lca_protected r hr) ⟨regs, .running⟩)⟩

private theorem query_answer_stage (shape : CartesianShape)
    (hf : CanonicalFringeSafety shape) (hi : CanonicalInteriorSafety shape) :
    QueryStage shape queryAnswerBlock (QuerySelected shape) (QueryContext shape) :=
  QueryStage.seq shape queryAnswerPrepareBlock
    (.seq (lcaCloseBlock logicalReadBlock) (queryAfterLCABlock logicalReadBlock)) queryAnswerBlock rfl
    _ _ _ (query_prepare_stage shape)
    (QueryStage.seq shape _ _ _ rfl _ _ _ (query_lca_stage shape hf hi) (query_after_lca_stage shape))

private theorem query_after_selects_stage (shape : CartesianShape)
    (hf : CanonicalFringeSafety shape) (hi : CanonicalInteriorSafety shape) :
    QueryStage shape (queryAfterSelectsProgram logicalReadBlock (lcaCloseBlock logicalReadBlock))
      (QuerySelected shape) (QueryContext shape) :=
  QueryStage.ifZero shape 2049 .skip (.ifZero 2050 .skip queryAnswerBlock) _ rfl _ _
    (query_skip_stage shape _ _ (fun _ h => h.1))
    (QueryStage.ifZero shape 2050 .skip queryAnswerBlock _ rfl _ _
      (query_skip_stage shape _ _ (fun _ h => h.1)) (query_answer_stage shape hf hi))


private theorem query_prepared_call_safe (shape : CartesianShape)
    (prepare call program : Block) (output : Nat)
    (programEq : program = .seq prepare (.seq call (.action (.move output 513))))
    (allowed : Nat → Prop) (writes : prepare.WritesOnly allowed)
    (outside : ∀ r, 16 ≤ r → r < 190 → ¬ allowed r)
    (prepareSafe : ∀ s, s.Fits (wordWidth shape.size) →
      prepare.Safe (shapeMemory shape) (wordWidth shape.size) s)
    (callSafe : ∀ s, s.Fits (wordWidth shape.size) → MetadataMatches shape s.regs →
      call.Safe (shapeMemory shape) (wordWidth shape.size) s)
    (s : Data) (fit : s.Fits (wordWidth shape.size)) (hm : MetadataMatches shape s.regs) :
    program.Safe (shapeMemory shape) (wordWidth shape.size) s := by
  subst program
  have hp := prepareSafe s fit
  refine query_safe_follow hp (fun fp => ?_)
  have mp : MetadataMatches shape (prepare.eval (shapeMemory shape) s).final.regs := by
    intro i hi
    rw [Block.eval_frame (shapeMemory shape) prepare allowed writes (16 + i) (outside _ (by omega) (by omega)) s]
    exact hm i hi
  have hc := callSafe _ fp mp
  exact Block.safe_seq hc (Block.safe_action _ _ _ _ (Block.eval_fits _ _ _ _ hc)
    ((Block.eval_fits _ _ _ _ hc).1 513))

theorem queryLeftSelectBlock_safe (shape : CartesianShape) (s : Data)
    (fit : s.Fits (wordWidth shape.size)) (hm : MetadataMatches shape s.regs) :
    (queryLeftSelectBlock logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) s :=
  query_prepared_call_safe shape (.action (.move 512 0)) (selectCloseBlock logicalReadBlock)
    (queryLeftSelectBlock logicalReadBlock) 2049 rfl (fun r => r = 512) rfl
    (by intro r h1 h2 he; omega)
    (fun s fs => Block.safe_action _ _ _ _ fs (fs.1 0))
    (selectCloseBlock_safe shape) s fit hm

theorem queryRightSelectBlock_safe (shape : CartesianShape) (s : Data)
    (fit : s.Fits (wordWidth shape.size)) (hm : MetadataMatches shape s.regs) :
    (queryRightSelectBlock logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) s :=
  query_prepared_call_safe shape (natSubBlock 512 1 2048 2051) (selectCloseBlock logicalReadBlock)
    (queryRightSelectBlock logicalReadBlock) 2050 rfl (fun r => r = 512 ∨ r = 2051)
    (by simp [natSubBlock, Block.WritesOnly, Action.destination])
    (by intro r h1 h2 he; omega)
    (fun s fs => natSubBlock_safe (shapeMemory shape) (wordWidth shape.size) 512 1 2048 2051 s fs
      (select_constant_fit shape.size 1 (by decide)) (by decide) (by decide))
    (selectCloseBlock_safe shape) s fit hm

private theorem query_packet_le_size (shape : CartesianShape) (regs : Registers)
    (hm : MetadataMatches shape regs) (index : Nat) :
    optionNatPacket (packedSelectCloseLeaf (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      shape.size index).value ≤ 2 * shape.size := by
  let prepared := regs.write 512 index
  have mp := MetadataMatches.write shape regs hm 512 index (Or.inr (by decide))
  have source := selectCloseBlock_canonical shape prepared mp
  have bound := selectCloseBlock_output_position_bound shape prepared mp
  rw [source.2.1] at bound
  simpa [prepared, Registers.write] using bound

private theorem query_left_stage (shape : CartesianShape) :
    QueryStage shape (queryLeftSelectBlock logicalReadBlock) (QueryContext shape)
      (fun regs => QueryContext shape regs ∧ regs 2049 ≤ 2 * shape.size) := by
  refine query_stage_output shape _ (QueryContext shape) (QueryContext shape) ?_ 2049 (2 * shape.size) ?_
  · apply query_context_stage shape _ QueryLeftSelectWrites
      (queryLeftSelectBlock_writes logicalReadBlock logicalReadBlock_writesOnly)
    · intro r hr; unfold QueryLeftSelectWrites SelectWrites; omega
    · intro regs fit pre; exact queryLeftSelectBlock_safe shape _ fit pre.metadata
    · intro regs pre
      exact (queryLeftSelectBlock_source shape (shapeMemory shape) logicalReadBlock
        (logicalReadBlock_correct shape) logicalReadBlock_writesOnly regs pre.metadata).1
  · intro regs pre
    rw [(queryLeftSelectBlock_source shape (shapeMemory shape) logicalReadBlock
      (logicalReadBlock_correct shape) logicalReadBlock_writesOnly regs pre.metadata).2.1]
    exact query_packet_le_size shape regs pre.metadata _

private theorem query_right_stage (shape : CartesianShape) :
    QueryStage shape (queryRightSelectBlock logicalReadBlock) (QueryContext shape)
      (fun regs => QueryContext shape regs ∧ regs 2050 ≤ 2 * shape.size) := by
  refine query_stage_output shape _ (QueryContext shape) (QueryContext shape) ?_ 2050 (2 * shape.size) ?_
  · apply query_context_stage shape _ QueryRightSelectWrites
      (queryRightSelectBlock_writes logicalReadBlock logicalReadBlock_writesOnly)
    · intro r hr; unfold QueryRightSelectWrites SelectWrites; omega
    · intro regs fit pre; exact queryRightSelectBlock_safe shape _ fit pre.metadata
    · intro regs pre
      exact (queryRightSelectBlock_source shape (shapeMemory shape) logicalReadBlock
        (logicalReadBlock_correct shape) logicalReadBlock_writesOnly regs pre.metadata pre.one).1
  · intro regs pre
    rw [(queryRightSelectBlock_source shape (shapeMemory shape) logicalReadBlock
      (logicalReadBlock_correct shape) logicalReadBlock_writesOnly regs pre.metadata pre.one).2.1]
    exact query_packet_le_size shape regs pre.metadata _

private theorem query_right_kept_stage (shape : CartesianShape) :
    QueryStage shape (queryRightSelectBlock logicalReadBlock)
      (fun regs => QueryContext shape regs ∧ regs 2049 ≤ 2 * shape.size) (QuerySelected shape) := by
  have kept := query_stage_keep shape _ _ _ (query_right_stage shape) 2049 (2 * shape.size)
    (fun regs => Block.eval_frame (shapeMemory shape) _ _
      (queryRightSelectBlock_writes logicalReadBlock logicalReadBlock_writesOnly) 2049
      (by simp [QueryRightSelectWrites, SelectWrites]) ⟨regs, .running⟩)
  exact QueryStage.adapt shape _ _ _ _ _ kept (fun _ h => h) (fun _ h => ⟨h.1.1, h.2, h.1.2⟩)

private theorem query_selected_stage (shape : CartesianShape)
    (hf : CanonicalFringeSafety shape) (hi : CanonicalInteriorSafety shape) :
    QueryStage shape (querySelectedProgram logicalReadBlock (lcaCloseBlock logicalReadBlock))
      (QueryContext shape) (QueryContext shape) :=
  QueryStage.seq shape (queryLeftSelectBlock logicalReadBlock)
    (.seq (queryRightSelectBlock logicalReadBlock) (queryAfterSelectsProgram logicalReadBlock (lcaCloseBlock logicalReadBlock)))
    _ rfl _ _ _ (query_left_stage shape)
    (QueryStage.seq shape _ _ _ rfl _ _ _ (query_right_kept_stage shape) (query_after_selects_stage shape hf hi))

private theorem query_one_stage (shape : CartesianShape) :
    QueryStage shape (.action (.constant 2048 1)) (MetadataMatches shape) (QueryContext shape) := by
  intro regs fit hm
  have safe := Block.safe_action (shapeMemory shape) (wordWidth shape.size) (.constant 2048 1)
    ⟨regs, .running⟩ fit (select_constant_fit shape.size 1 (by decide))
  exact ⟨safe, rfl, MetadataMatches.write shape regs hm 2048 1 (Or.inr (by decide)), rfl⟩

private theorem query_ready_stage (shape : CartesianShape)
    (hf : CanonicalFringeSafety shape) (hi : CanonicalInteriorSafety shape) :
    QueryStage shape (queryReadyProgram logicalReadBlock (lcaCloseBlock logicalReadBlock))
      (MetadataMatches shape) (QueryContext shape) :=
  QueryStage.seq shape (.action (.constant 2048 1))
    (querySelectedProgram logicalReadBlock (lcaCloseBlock logicalReadBlock)) _ rfl _ _ _
    (query_one_stage shape) (query_selected_stage shape hf hi)

private theorem query_setup_stage (shape : CartesianShape) :
    QueryStage shape metadataSetupBlock (fun _ => True) (MetadataMatches shape) := by
  intro regs fit _
  have safe := metadataSetupBlock_safe (shapeMemory shape) (wordWidth shape.size)
    (by unfold wordWidth; omega) (shapeMemory_words_fit shape) ⟨regs, .running⟩ fit
  have source := shapeMemory_setup shape ⟨regs, .running⟩ rfl
  exact ⟨safe, source.1, source.2.1⟩

private theorem query_body_stage (shape : CartesianShape)
    (hf : CanonicalFringeSafety shape) (hi : CanonicalInteriorSafety shape) :
    QueryStage shape queryBody (fun _ => True) (QueryContext shape) :=
  QueryStage.seq shape metadataSetupBlock
    (queryReadyProgram logicalReadBlock (lcaCloseBlock logicalReadBlock)) queryBody rfl _ _ _
    (query_setup_stage shape) (query_ready_stage shape hf hi)

theorem queryBody_safe_with_leaves (shape : CartesianShape)
    (hf : CanonicalFringeSafety shape) (hi : CanonicalInteriorSafety shape)
    (s : Data) (fit : s.Fits (wordWidth shape.size)) :
    queryBody.Safe (shapeMemory shape) (wordWidth shape.size) s := by
  by_cases hs : s.status = .running
  · cases s with
    | mk regs status =>
      dsimp only at hs
      subst status
      exact (query_body_stage shape hf hi regs fit True.intro).1
  · exact Block.safe_stopped _ _ _ s fit hs


theorem guardedBlock_safe_of_body (memory : Memory) (width : Nat)
    (one : 1 < 2 ^ width) (body : Block)
    (bodySafe : ∀ s, s.Fits width → body.Safe memory width s)
    (s : Data) (fit : s.Fits width) : (guardedBlock body).Safe memory width s := by
  have compare (op : Comparison) (dst lhs rhs : Nat) (state : Data) (fs : state.Fits width) :
      (Block.action (.comparison op dst lhs rhs)).Safe memory width state :=
    SimpleScalar.safe memory width (.action (.comparison op dst lhs rhs)) one state fs
  have zero := Block.safe_action memory width (.constant 3 0) s fit (Nat.two_pow_pos _)
  refine query_safe_follow zero (fun f0 => ?_)
  have first := compare .lt 4 0 1 _ f0
  refine query_safe_follow first (fun f1 => ?_)
  apply Block.safe_ifZero f1
  split
  · exact Block.safe_exit _ _ _ _ f1
  · have second := compare .le 5 1 2 _ f1
    refine query_safe_follow second (fun f2 => ?_)
    apply Block.safe_ifZero f2
    split
    · exact Block.safe_exit _ _ _ _ f2
    · exact bodySafe _ f2

theorem querySource_safe_with_leaves (shape : CartesianShape)
    (hf : CanonicalFringeSafety shape) (hi : CanonicalInteriorSafety shape)
    (s : Data) (fit : s.Fits (wordWidth shape.size)) :
    querySource.Safe (shapeMemory shape) (wordWidth shape.size) s :=
  guardedBlock_safe_of_body (shapeMemory shape) (wordWidth shape.size)
    (select_constant_fit shape.size 1 (by decide)) queryBody (queryBody_safe_with_leaves shape hf hi) s fit

private theorem querySource_budget : querySource.size + 1 = queryBudget := by
  simp only [querySource, guardedBlock_size, queryBudget]

theorem queryRun_execution_safe_with_leaves (shape : CartesianShape)
    (hf : CanonicalFringeSafety shape) (hi : CanonicalInteriorSafety shape) (left right : Nat)
    (hl : left < 2 ^ wordWidth shape.size) (hr : right < 2 ^ wordWidth shape.size) :
    RankExecutionSafety (shapeMemory shape) (wordWidth shape.size) queryProgram queryBudget
      (initialState shape.size left right) := by
  exact rank_compiled_safety (shapeMemory shape) (wordWidth shape.size) querySource 3 queryBudget
    (inputRegisters shape.size left right) querySource_budget (queryBudget_fits shape.size)
    (querySource_fieldsFit shape.size)
    (by have hc := query_small_fields_fit shape.size
        simp [Instruction.Fits, Instruction.encoding, Instruction.operands]; omega)
    (initialState_fits shape.size left right hl hr).2
    (querySource_safe_with_leaves shape hf hi _ (initialState_fits shape.size left right hl hr).2)


/-- Canonical fringe and interior producers discharge the only leaf interfaces.
The statement also covers fitting stopped states and arbitrary fitting registers. -/
theorem querySource_safe (shape : CartesianShape) (s : Data)
    (fit : s.Fits (wordWidth shape.size)) :
    querySource.Safe (shapeMemory shape) (wordWidth shape.size) s :=
  querySource_safe_with_leaves shape (fringeBlock_canonical_safe shape)
    (interiorRangeBlock_canonical_safe shape) s fit

theorem querySource_initial_safe (xs : List Int) (left right : Nat)
    (hl : left < 2 ^ wordWidth xs.length) (hr : right < 2 ^ wordWidth xs.length) :
    querySource.Safe (buildMemory xs) (wordWidth xs.length)
      (Data.ofState (initialState xs.length left right)) := by
  have safe := querySource_safe (SuccinctClassic.cartesianShape xs)
    (Data.ofState (initialState xs.length left right)) (by
      simpa only [packedReviewerCartesianShape_size] using
        (initialState_fits xs.length left right hl hr).2)
  simpa only [buildMemory, packedReviewerCartesianShape_size] using safe

/-- The exact producer consumed by the root capstone: no canonical safety,
metadata, readiness, successful read, or route premise remains. -/
theorem queryRun_execution_safe (xs : List Int) (left right : Nat)
    (hl : left < 2 ^ wordWidth xs.length) (hr : right < 2 ^ wordWidth xs.length) :
    RankExecutionSafety (buildMemory xs) (wordWidth xs.length) queryProgram queryBudget
      (initialState xs.length left right) := by
  have safe := queryRun_execution_safe_with_leaves (SuccinctClassic.cartesianShape xs)
    (fringeBlock_canonical_safe (SuccinctClassic.cartesianShape xs))
    (interiorRangeBlock_canonical_safe (SuccinctClassic.cartesianShape xs)) left right
    (by simpa only [packedReviewerCartesianShape_size] using hl)
    (by simpa only [packedReviewerCartesianShape_size] using hr)
  simpa only [buildMemory, packedReviewerCartesianShape_size] using safe

/-- Semantic observations and safety use one actual primitive execution. -/
theorem queryRun_safe (xs : List Int) (left right : Nat)
    (hl : left < 2 ^ wordWidth xs.length) (hr : right < 2 ^ wordWidth xs.length) :
    let actual := run (buildMemory xs) queryProgram queryBudget (initialState xs.length left right)
    let packet := optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value
    RankExecutionSafety (buildMemory xs) (wordWidth xs.length) queryProgram queryBudget
      (initialState xs.length left right) ∧
    actual.result = some packet ∧ actual.final.status = .halted packet ∧
    actual.reads = (if ValidRange xs left right then
      (List.range 174).map (fun i => ⟨i, (metadata (SuccinctClassic.cartesianShape xs))[i]?⟩) ++
        logicalTraceReads (SuccinctClassic.cartesianShape xs) (buildMemory xs)
          (SuccinctClassic.queryTraceResult xs left right).trace else []) ∧
    packet < 2 ^ wordWidth xs.length ∧ actual.steps ≤ 837572 := by
  have safe := queryRun_execution_safe xs left right hl hr
  have halted := queryRun_halts xs left right
  have result := queryRun_result xs left right
  have reads := queryRun_reference_reads xs left right
  have finalFit := safe.2.1
  have bounded := queryRun_steps_le (buildMemory xs) xs.length left right
  rw [queryBudget_eq] at bounded
  simp only [queryRun] at result halted reads bounded
  generalize execution : run (buildMemory xs) queryProgram queryBudget
    (initialState xs.length left right) = actual at result halted reads bounded finalFit ⊢
  exact ⟨safe, result, halted, reads, finalFit.2.2 _ halted, bounded⟩

/-- Independently expanded expected type fixes the memory, program, fuel,
initial state, every indexed transition, every prefix and every read occurrence. -/
theorem queryRun_requiredSafety (xs : List Int) (left right : Nat)
    (hl : left < 2 ^ wordWidth xs.length) (hr : right < 2 ^ wordWidth xs.length) :
    (∀ instruction ∈ queryProgram, instruction.Fits (wordWidth xs.length)) ∧
    (run (buildMemory xs) queryProgram queryBudget
      (initialState xs.length left right)).final.Fits (wordWidth xs.length) ∧
    (∀ (index : Nat) (t : Transition),
      (run (buildMemory xs) queryProgram queryBudget
        (initialState xs.length left right)).transitions[index]? = some t →
      Instruction.Safe (wordWidth xs.length) t.before t.instruction ∧
        t.after.Fits (wordWidth xs.length)) ∧
    (∀ fuel, fuel ≤ queryBudget →
      (run (buildMemory xs) queryProgram fuel
        (initialState xs.length left right)).final.Fits (wordWidth xs.length)) ∧
    (∀ (index : Nat) (t : Transition) (receipt : Receipt),
      (run (buildMemory xs) queryProgram queryBudget
        (initialState xs.length left right)).transitions[index]? = some t →
      t.receipt = some receipt →
      receipt.address < 2 ^ wordWidth xs.length ∧
      receipt.reply = (buildMemory xs)[receipt.address]? ∧
      (∀ value, receipt.reply = some value → value < 2 ^ wordWidth xs.length)) :=
  queryRun_execution_safe xs left right hl hr

/-- The same positional read has both a fitting address/value and an actual
load instruction at the prefix state. Repeated equal receipts keep their indices. -/
theorem queryRun_safe_read_at (xs : List Int) (left right : Nat)
    (hl : left < 2 ^ wordWidth xs.length) (hr : right < 2 ^ wordWidth xs.length)
    (index : Nat) (t : Transition) (receipt : Receipt)
    (ht : (run (buildMemory xs) queryProgram queryBudget
      (initialState xs.length left right)).transitions[index]? = some t)
    (hrc : t.receipt = some receipt) :
    receipt.address < 2 ^ wordWidth xs.length ∧
    receipt.reply = (buildMemory xs)[receipt.address]? ∧
    (∀ value, receipt.reply = some value → value < 2 ^ wordWidth xs.length) ∧
    t.before = (run (buildMemory xs) queryProgram index (initialState xs.length left right)).final ∧
    t.before.status = .running ∧ queryProgram[t.before.pc]? = some t.instruction ∧
    execute (buildMemory xs) t.instruction t.before = (t.after, t.receipt) ∧
    ∃ dst addrReg, t.instruction = .load dst addrReg ∧
      receipt.address = t.before.regs addrReg ∧ receipt.reply = (buildMemory xs)[receipt.address]? := by
  have width := (queryRun_execution_safe xs left right hl hr).2.2.2.2 index t receipt ht hrc
  exact ⟨width.1, width.2.1, width.2.2, queryRun_read_at xs left right index t receipt ht hrc⟩

theorem queryRun_sameAllocation_safe (xs : List Int) (left right : Nat)
    (hl : left < 2 ^ wordWidth xs.length) (hr : right < 2 ^ wordWidth xs.length) :
    (∀ word ∈ buildMemory xs, word < 2 ^ wordWidth xs.length) ∧
    (∀ address ≤ (buildMemory xs).length, address < 2 ^ wordWidth xs.length) ∧
    (((buildMemory xs).length + queryProgramWords + queryScratchWords) * wordWidth xs.length ≤
      2 * xs.length + queryCompleteRho xs.length) ∧
    (Nat.log2 (xs.length + 2) + 1 ≤ wordWidth xs.length ∧
      wordWidth xs.length ≤ 192 * (Nat.log2 (xs.length + 2) + 1)) ∧
    RankExecutionSafety (buildMemory xs) (wordWidth xs.length) queryProgram queryBudget
      (initialState xs.length left right) :=
  ⟨buildMemory_words_fit xs, buildMemory_address_fit xs, query_complete_capacity xs,
    ⟨wordWidth_log_lower xs.length, wordWidth_le_log xs.length⟩,
    queryRun_execution_safe xs left right hl hr⟩

theorem queryRun_valid_safe (xs : List Int) (left right : Nat) (hv : ValidRange xs left right) :
    encodeInputs xs.length left right = some (initialState xs.length left right) ∧
    RankExecutionSafety (buildMemory xs) (wordWidth xs.length) queryProgram queryBudget
      (initialState xs.length left right) :=
  ⟨valid_inputs_encode xs.length left right hv.1 hv.2,
    queryRun_execution_safe xs left right (validEndpoints_fit xs left right hv).1
      (validEndpoints_fit xs left right hv).2⟩

theorem queryRun_invalid_safe (xs : List Int) (left right : Nat)
    (hl : left < 2 ^ wordWidth xs.length) (hr : right < 2 ^ wordWidth xs.length)
    (hi : ¬ ValidRange xs left right) :
    RankExecutionSafety (buildMemory xs) (wordWidth xs.length) queryProgram queryBudget
      (initialState xs.length left right) ∧
    (run (buildMemory xs) queryProgram queryBudget (initialState xs.length left right)).result = some 0 ∧
    (run (buildMemory xs) queryProgram queryBudget (initialState xs.length left right)).reads = [] :=
  ⟨queryRun_execution_safe xs left right hl hr,
    (queryRun_invalid (buildMemory xs) xs.length left right hi).1,
    (queryRun_invalid (buildMemory xs) xs.length left right hi).2.1⟩

theorem queryRun_empty_safe (left right : Nat)
    (hl : left < 2 ^ wordWidth 0) (hr : right < 2 ^ wordWidth 0) :
    RankExecutionSafety (buildMemory []) (wordWidth 0) queryProgram queryBudget (initialState 0 left right) ∧
    (run (buildMemory []) queryProgram queryBudget (initialState 0 left right)).result = some 0 ∧
    (run (buildMemory []) queryProgram queryBudget (initialState 0 left right)).reads = [] :=
  queryRun_invalid_safe [] left right hl hr (by simp [ValidRange]; omega)

theorem queryRun_last_representable_safe (xs : List Int) :
    let last := 2 ^ wordWidth xs.length - 1
    RankExecutionSafety (buildMemory xs) (wordWidth xs.length) queryProgram queryBudget
      (initialState xs.length last last) ∧
    (run (buildMemory xs) queryProgram queryBudget (initialState xs.length last last)).result = some 0 ∧
    (run (buildMemory xs) queryProgram queryBudget (initialState xs.length last last)).reads = [] := by
  have fit : 2 ^ wordWidth xs.length - 1 < 2 ^ wordWidth xs.length := by
    have := Nat.two_pow_pos (wordWidth xs.length)
    omega
  exact queryRun_invalid_safe xs _ _ fit fit (by simp [ValidRange])

example (value : Int) :
    RankExecutionSafety (buildMemory [value]) (wordWidth 1) queryProgram queryBudget
      (initialState 1 0 1) :=
  (queryRun_valid_safe [value] 0 1 (by simp [ValidRange])).2

example (first second : Int) :
    RankExecutionSafety (buildMemory [first, second]) (wordWidth 2) queryProgram queryBudget
      (initialState 2 0 2) :=
  (queryRun_valid_safe [first, second] 0 2 (by simp [ValidRange])).2

example (first second : Int) :
    RankExecutionSafety (buildMemory [first, second]) (wordWidth 2) queryProgram queryBudget
      (initialState 2 2 1) :=
  (queryRun_invalid_safe [first, second] 2 1 (select_constant_fit 2 2 (by decide))
    (select_constant_fit 2 1 (by decide)) (by simp [ValidRange])).1

example (value : Int) :
    RankExecutionSafety (buildMemory [value]) (wordWidth 1) queryProgram queryBudget
      (initialState 1 0 2) :=
  (queryRun_invalid_safe [value] 0 2 (Nat.two_pow_pos _)
    (select_constant_fit 1 2 (by decide)) (by simp [ValidRange])).1

end RMQ.SuccinctFinal.PackedWordRAM
