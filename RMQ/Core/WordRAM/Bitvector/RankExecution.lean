import RMQ.Core.WordRAM.Bitvector.SelectExecution

/-! # Actual rank wrapper, charged setup and shared primitive execution -/

namespace RMQ.PackedBitvector

open SuccinctRank SuccinctFinal SuccinctFinal.PackedCellProbe
open SuccinctFinal.PackedWordRAM SuccinctFinal.PackedWordRAM.Structured

def rankReadTrace (bits : List Bool) (target : Bool) (argument : Nat) :=
  let d := jacobsonRankData bits
  packedRankRead 17 18 19 21 (SuccinctClose.bpFringeChunkBits (2*bits.length)) target
    (Allocation.readStore bits target) bits.length d.wordSize d.blocksPerSuper argument

def rankBodyReceipts (bits : List Bool) (target : Bool) (argument : Nat) : List Receipt :=
  if argument ≤ bits.length then
    Controller.traceReads (Allocation.readerReceipts bits target) (rankReadTrace bits target argument).trace
  else []

def rankExecutionReceipts (bits : List Bool) (target : Bool) (argument : Nat) : List Receipt :=
  ChargedSetup.setupReceipts bits ++ rankBodyReceipts bits target argument

def rankPacket (bits : List Bool) (target : Bool) (argument : Nat) : Nat :=
  if argument ≤ bits.length then Succinct.rankPrefix target bits argument + 1 else 0

private theorem eval_skip (memory : Memory) (regs : Registers) :
    Block.skip.eval memory ⟨regs, .running⟩ = ⟨⟨regs, .running⟩, []⟩ := rfl

private theorem eval_constant (memory : Memory) (regs : Registers) (dst value : Nat) :
    (Block.action (.constant dst value)).eval memory ⟨regs, .running⟩ =
      ⟨⟨regs.write dst value, .running⟩, []⟩ := rfl

private theorem eval_move (memory : Memory) (regs : Registers) (dst src : Nat) :
    (Block.action (.move dst src)).eval memory ⟨regs, .running⟩ =
      ⟨⟨regs.write dst (regs src), .running⟩, []⟩ := rfl

private theorem eval_comparison (memory : Memory) (regs : Registers)
    (op : Comparison) (dst lhs rhs : Nat) :
    (Block.action (.comparison op dst lhs rhs)).eval memory ⟨regs, .running⟩ =
      ⟨⟨regs.write dst (op.eval (regs lhs) (regs rhs)), .running⟩, []⟩ := rfl

private theorem eval_arithmetic (memory : Memory) (regs : Registers)
    (op : Arithmetic) (dst lhs rhs : Nat) :
    (Block.action (.arithmetic op dst lhs rhs)).eval memory ⟨regs, .running⟩ =
      ⟨⟨regs.write dst (op.eval (regs lhs) (regs rhs)), .running⟩, []⟩ := rfl

private theorem eval_ifZero (memory : Memory) (regs : Registers) (r : Nat) (a b : Block) :
    (Block.ifZero r a b).eval memory ⟨regs, .running⟩ =
      if regs r = 0 then a.eval memory ⟨regs, .running⟩ else b.eval memory ⟨regs, .running⟩ := rfl

theorem rankQuery_source (bits : List Bool) (target : Bool) (argument : Nat) :
    let actual := rankQuery.eval (Allocation.memory bits)
      ⟨loadedMetadata bits .rank target argument, .running⟩
    actual.final.status = .running ∧ actual.final.regs 360 = rankPacket bits target argument ∧
      actual.reads = rankBodyReceipts bits target argument := by
  let regs := loadedMetadata bits .rank target argument
  change (rankQuery.eval (Allocation.memory bits) ⟨regs, .running⟩).final.status = .running ∧
    (rankQuery.eval (Allocation.memory bits) ⟨regs, .running⟩).final.regs 360 =
      rankPacket bits target argument ∧
    (rankQuery.eval (Allocation.memory bits) ⟨regs, .running⟩).reads =
      rankBodyReceipts bits target argument
  have hn : regs 18 = bits.length := loadedMetadata_size bits .rank target argument
  have hi : regs 352 = argument := loadedMetadata_argument bits .rank target argument
  by_cases hvalid : argument ≤ bits.length
  · let pr := ((((((((regs.write 360 0).write 371 0).write 353 (regs 18)).write
      354 (regs 19)).write 355 (regs 20)).write 356 17).write 357 18).write 358 19).write 359 (regs 3)
    have hm : Controller.MetadataMatches (loadedModel bits .rank target argument) pr := by
      intro r hr
      change pr r = regs r
      simp only [pr, Registers.write, if_neg (show r ≠ 359 by omega),
        if_neg (show r ≠ 358 by omega), if_neg (show r ≠ 357 by omega),
        if_neg (show r ≠ 356 by omega), if_neg (show r ≠ 355 by omega),
        if_neg (show r ≠ 354 by omega), if_neg (show r ≠ 353 by omega),
        if_neg (show r ≠ 371 by omega), if_neg (show r ≠ 360 by omega)]
    have htarget : pr 359 = if target then 1 else 0 := by
      simp only [pr, Registers.write, if_true]
      cases target <;> exact loadedMetadata_target bits .rank _ argument
    have h := Controller.rankBlock_source (loadedModel bits .rank target argument)
      (Allocation.memory bits) Experiment.physicalReader (loadedModel_reader bits .rank target argument)
      physicalReader_writes target pr hm htarget
    generalize he : (rankBlock Experiment.physicalReader).eval
      (Allocation.memory bits) ⟨pr, .running⟩ = ranked at h
    have hg := loadedMetadata_rank_geometry bits target argument
    simp only [loadedModel, Allocation.controllerModel, pr, Registers.write,
      reduceIte, hn, hi, regs, loadedMetadata_chunk, hg.1, hg.2] at h
    change _ ∧ _ = (rankReadTrace bits target argument).value ∧
      _ = Controller.traceReads (Allocation.readerReceipts bits target)
        (rankReadTrace bits target argument).trace ∧ _ at h
    have hv := Allocation.readStore_rank_value bits target argument
    change (rankReadTrace bits target argument).value = _ at hv
    rw [hv] at h
    rcases ranked with ⟨⟨final, status⟩, receipts⟩
    dsimp only at h
    obtain ⟨hstatus, hvalue, hreads, _⟩ := h
    subst status
    dsimp only [pr] at he
    rw [hn] at he
    have hlt : ¬bits.length < argument := by omega
    unfold rankQuery
    generalize hcore : rankBlock Experiment.physicalReader = core at he ⊢
    simp [rankPrepare, Block.sequence, List.foldr_cons, List.foldr_nil,
      Block.eval_seq, Evaluation.bind,
      eval_constant, eval_comparison, eval_move, Comparison.eval, Registers.write,
      reduceIte, hn, hi, if_neg hlt, eval_ifZero, he, eval_arithmetic, Arithmetic.eval,
      eval_skip, List.nil_append, List.append_nil, hvalue, hreads,
      rankPacket, rankBodyReceipts, if_pos hvalid]
  · have hlt : bits.length < argument := by omega
    simp [rankQuery, Block.sequence, Block.eval_seq, Evaluation.bind, eval_constant,
      eval_comparison, Comparison.eval, Registers.write, hn, hi, hlt, eval_ifZero,
      eval_skip, rankPacket, rankBodyReceipts, hvalid]

theorem rank_source (bits : List Bool) (target : Bool) (argument : Nat) :
    let actual := (source .rank).eval (Allocation.memory bits)
      ⟨(initial .rank target argument).regs, .running⟩
    actual.final.status = .running ∧ actual.final.regs 360 = rankPacket bits target argument ∧
      actual.reads = rankExecutionReceipts bits target argument := by
  have hs := ChargedSetup.setup_source bits (initial .rank target argument).regs
  have hr := rankQuery_source bits target argument
  simp only [source, operationBody, Block.eval_seq, hs, Evaluation.bind]
  exact ⟨hr.1, hr.2.1, congrArg (ChargedSetup.setupReceipts bits ++ ·) hr.2.2⟩

theorem execute_rank (bits : List Bool) (target : Bool) (argument : Nat) :
    let actual := execute bits .rank target argument
    let packet := rankPacket bits target argument
    actual.result = some packet ∧ actual.final.status = .halted packet ∧
    actual.final.regs 360 = packet ∧ actual.reads = rankExecutionReceipts bits target argument ∧
    actual.steps ≤ (source .rank).size + 1 := by
  have hs := rank_source bits target argument
  exact execute_source_result bits .rank 360 rfl target argument _ _ hs.1 hs.2.1 hs.2.2

end RMQ.PackedBitvector
