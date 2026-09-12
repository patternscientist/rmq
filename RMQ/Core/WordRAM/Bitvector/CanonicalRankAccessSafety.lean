import RMQ.Core.WordRAM.Bitvector.AccessProof
import RMQ.Core.WordRAM.Bitvector.CanonicalSelectSafety
import RMQ.Core.WordRAM.Bitvector.Observations

/-! # Canonical safety of the actual access and rank programs

Charged setup and canonical allocation bounds discharge every internal safety
interface. Only representability of the external argument is assumed.
-/

namespace RMQ.PackedBitvector

open SuccinctSpace SuccinctRank
open SuccinctFinal.PackedWordRAM SuccinctFinal.PackedWordRAM.Structured

theorem canonical_access_source_safe (bits : List Bool) (argument : Nat)
    (ha : argument < 2 ^ Experiment.width bits.length) :
    (source .access).Safe (Allocation.memory bits) (Experiment.width bits.length)
      ⟨(initial .access false argument).regs, .running⟩ := by
  have fit := initial_data_fits bits .access false argument ha
  have setup := ChargedSetup.setup_safe bits _ _ (width_floor bits.length)
    (canonical_memoryWordsFit bits) fit
  have setupFit := Block.eval_fits _ _ _ _ setup
  change (Block.seq Experiment.setup accessQuery).Safe _ _ _
  apply Block.safe_seq setup
  rw [ChargedSetup.setup_source] at setupFit ⊢
  have metadata : AccessProof.AccessMetadata bits
      (ChargedSetup.setupMetadata bits (initial .access false argument).regs) := by
    refine ⟨rfl, rfl, ?_, rfl⟩
    change (jacobsonRankData bits).wordSize = machineWordBits bits.length
    exact jacobson_wordSize_eq bits
  exact AccessProof.accessQuery_safe bits _ metadata setupFit
    (loadedModel_readerSafe bits .access false argument)

private theorem rank_envelope_increment_fit (limits : Controller.SafetyLimits) :
    limits.envelope + 1 < 2 ^ limits.width := by
  have hp := limits.envelope_pos
  have hsq : limits.envelope ≤ limits.envelope * limits.envelope := by
    simpa using Nat.mul_le_mul_left limits.envelope (show 1 ≤ limits.envelope by omega)
  have hc := limits.square
  omega

private theorem rank_increment_safe (memory : Memory) (width envelope : Nat)
    (s : Data) (fit : s.Fits width) (bound : s.regs 360 ≤ envelope)
    (cap : envelope + 1 < 2 ^ width) :
    (Block.sequence [.action (.constant 370 1),
      .action (.arithmetic .add 360 360 370)]).Safe memory width s := by
  have hwne : width ≠ 0 := by
    intro h
    subst width
    simp at cap
  by_cases running : s.status = .running
  · cases s with
    | mk regs status =>
      dsimp only at running fit bound ⊢
      subst status
      apply ScalarChecks_safe memory width _ _ fit
      simp [ScalarChecks, Block.sequence, Block.eval, Action.eval, Action.instruction,
        Action.LocalSafe, SuccinctFinal.PackedWordRAM.execute, State.writeNext,
        Data.ofState, Registers.write, Arithmetic.eval, hwne] <;> omega
  · exact Block.safe_stopped memory width _ s fit running

private def rankPrepared (regs : Registers) : Registers :=
  let r := ((regs.write 353 (regs 18)).write 354 (regs 19)).write 355 (regs 20)
  (((r.write 356 17).write 357 18).write 358 19).write 359 (regs 3)

private theorem rankPrepare_source (memory : Memory) (regs : Registers) :
    rankPrepare.eval memory ⟨regs, .running⟩ = ⟨⟨rankPrepared regs, .running⟩, []⟩ := by
  simp [rankPrepare, rankPrepared, Block.sequence, Block.eval, Action.eval,
    Action.instruction, SuccinctFinal.PackedWordRAM.execute, State.writeNext,
    Data.ofState, Registers.write]

private theorem rankPrepared_metadata (model : Controller.ControllerModel) (regs : Registers)
    (hm : Controller.MetadataMatches model regs) :
    Controller.MetadataMatches model (rankPrepared regs) := by
  intro r hr
  have h353 : r ≠ 353 := by omega
  have h354 : r ≠ 354 := by omega
  have h355 : r ≠ 355 := by omega
  have h356 : r ≠ 356 := by omega
  have h357 : r ≠ 357 := by omega
  have h358 : r ≠ 358 := by omega
  have h359 : r ≠ 359 := by omega
  simpa [rankPrepared, Registers.write, h353, h354, h355, h356, h357, h358, h359] using hm r hr

private theorem rank_body_safe (bits : List Bool) (target : Bool) (argument : Nat)
    (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (Experiment.width bits.length))
    (hm : Controller.MetadataMatches (loadedModel bits .rank target argument) regs) :
    (Block.sequence [rankPrepare, rankBlock Experiment.physicalReader,
      .action (.constant 370 1), .action (.arithmetic .add 360 360 370)]).Safe
        (Allocation.memory bits) (Experiment.width bits.length) ⟨regs, .running⟩ := by
  let limits := canonicalLimits bits.length
  let model := loadedModel bits .rank target argument
  have bounds := loadedModel_safetyBounds bits .rank target argument
  have cap := limits.constant_fit 19 (by decide)
  change 19 < 2 ^ Experiment.width bits.length at cap
  have prep : rankPrepare.Safe (Allocation.memory bits) limits.width ⟨regs, .running⟩ := by
    apply SimpleScalar.safe _ _ _ ?_ _ fit
    simp [rankPrepare, Block.sequence, SimpleScalar]
    omega
  have prepFit := Block.eval_fits _ _ _ _ prep
  change (Block.seq rankPrepare (Block.sequence [rankBlock Experiment.physicalReader,
    .action (.constant 370 1), .action (.arithmetic .add 360 360 370)])).Safe _ _ _
  apply Block.safe_seq prep
  rw [rankPrepare_source] at prepFit ⊢
  have pm := rankPrepared_metadata model regs hm
  have hg := loadedMetadata_rank_geometry bits target argument
  have hw : regs 19 = machineWordBits bits.length :=
    (hm 19 (by decide)).trans (hg.1.trans (jacobson_wordSize_eq bits))
  have hb : regs 20 = machineWordBits bits.length :=
    (hm 20 (by decide)).trans (hg.2.trans (jacobson_blocksPerSuper_eq bits))
  have hlen : regs 18 ≤ limits.envelope :=
    Controller.metadata_envelope model limits bounds regs hm 18 (by decide)
  have core := Controller.rankBlock_safe_bound model limits bounds (Allocation.memory bits)
    Experiment.physicalReader (loadedModel_readerSafe bits .rank target argument)
    (loadedModel_reader bits .rank target argument) physicalReader_writes
    (rankPrepared regs) prepFit pm
    (by simpa [rankPrepared, Registers.write, hw] using machineWordBits_pos bits.length)
    (by simpa [rankPrepared, Registers.write, hb] using machineWordBits_pos bits.length)
    (by simpa [rankPrepared, Registers.write] using hlen)
    (by intro index; simpa [rankPrepared, Registers.write, model, loadedModel,
        Allocation.controllerModel, limits, canonicalLimits] using canonical_rank_raw_length bits target index)
  apply Block.safe_seq core.1
  exact rank_increment_safe (Allocation.memory bits) limits.width limits.envelope _
    (Block.eval_fits _ _ _ _ core.1) core.2 (rank_envelope_increment_fit limits)

private theorem safe_step {memory : Memory} {width : Nat}
    {op : Action} {rest : Block} {regs : Registers}
    (fit : (⟨regs, .running⟩ : Data).Fits width)
    (localSafe : op.LocalSafe memory width ⟨regs, .running⟩)
    (tail : (op.eval memory ⟨regs, .running⟩).final.Fits width →
      rest.Safe memory width (op.eval memory ⟨regs, .running⟩).final) :
    (Block.seq (.action op) rest).Safe memory width ⟨regs, .running⟩ := by
  have first := Block.safe_action memory width op _ fit localSafe
  exact Block.safe_seq first (tail (Block.eval_fits memory width _ _ first))

private theorem canonical_rankQuery_safe (bits : List Bool) (target : Bool) (argument : Nat)
    (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (Experiment.width bits.length))
    (hm : Controller.MetadataMatches (loadedModel bits .rank target argument) regs) :
    rankQuery.Safe (Allocation.memory bits) (Experiment.width bits.length) ⟨regs, .running⟩ := by
  have cap := fixed_floor_capacity bits.length 1 (by decide)
  unfold rankQuery Block.sequence
  refine safe_step fit (by simpa [Action.LocalSafe] using Nat.two_pow_pos (Experiment.width bits.length))
    (fun f1 => ?_)
  have hm1 := Controller.MetadataMatches.write _ _ hm 360 0 (Or.inr (by decide))
  refine safe_step f1 ?_ (fun f2 => ?_)
  · simp only [Action.LocalSafe, Comparison.eval]
    split <;> omega
  · have hm2 := Controller.MetadataMatches.write _ _ hm1 371
      (Comparison.lt.eval (regs 18) (regs 352)) (Or.inr (by decide))
    have branch : (Block.ifZero 371 (Block.sequence [rankPrepare, rankBlock Experiment.physicalReader,
      .action (.constant 370 1), .action (.arithmetic .add 360 360 370)]) .skip).Safe
        (Allocation.memory bits) (Experiment.width bits.length)
        ⟨(regs.write 360 0).write 371 (Comparison.lt.eval (regs 18) (regs 352)), .running⟩ := by
      apply Block.safe_ifZero f2
      split
      · exact rank_body_safe bits target argument _ f2 hm2
      · exact Block.safe_skip _ _ _ f2
    exact Block.safe_seq branch (Block.safe_skip _ _ _ (Block.eval_fits _ _ _ _ branch))

theorem canonical_rank_source_safe (bits : List Bool) (target : Bool) (argument : Nat)
    (ha : argument < 2 ^ Experiment.width bits.length) :
    (source .rank).Safe (Allocation.memory bits) (Experiment.width bits.length)
      ⟨(initial .rank target argument).regs, .running⟩ := by
  have fit := initial_data_fits bits .rank target argument ha
  have setup := ChargedSetup.setup_safe bits _ _ (width_floor bits.length)
    (canonical_memoryWordsFit bits) fit
  have setupFit := Block.eval_fits _ _ _ _ setup
  change (Block.seq Experiment.setup rankQuery).Safe _ _ _
  apply Block.safe_seq setup
  rw [ChargedSetup.setup_source] at setupFit ⊢
  exact canonical_rankQuery_safe bits target argument _ setupFit (fun _ _ => rfl)

theorem canonical_access_source_fieldsFit (bits : List Bool) :
    (source .access).FieldsFit (Experiment.width bits.length) := by
  have cap := fixed_floor_capacity bits.length 8280 (by decide)
  have readerFields := Controller.physicalReader_fieldsFit (canonicalLimits bits.length)
  change Experiment.physicalReader.FieldsFit (Experiment.width bits.length) at readerFields
  have hwne : Experiment.width bits.length ≠ 0 := by have := width_floor bits.length; omega
  simp [source, operationBody, accessQuery, Experiment.setup, List.range_succ, Block.sequence, Block.FieldsFit,
    Action.instruction, Instruction.Fits, Instruction.encoding, Instruction.operands,
    Arithmetic.code, Comparison.code, readerFields, hwne]
  omega

theorem canonical_rank_source_fieldsFit (bits : List Bool) :
    (source .rank).FieldsFit (Experiment.width bits.length) := by
  have cap := fixed_floor_capacity bits.length 8280 (by decide)
  have readerFields := Controller.physicalReader_fieldsFit (canonicalLimits bits.length)
  have coreFields := rankBlock_fieldsFit _ _ readerFields cap
  change (rankBlock Experiment.physicalReader).FieldsFit (Experiment.width bits.length) at coreFields
  have hwne : Experiment.width bits.length ≠ 0 := by have := width_floor bits.length; omega
  simp [source, operationBody, rankQuery, rankPrepare, Experiment.setup, List.range_succ, Block.sequence, Block.FieldsFit,
    Action.instruction, Instruction.Fits, Instruction.encoding, Instruction.operands,
    Arithmetic.code, Comparison.code, coreFields, hwne]
  omega

theorem canonical_access_execution_safe (bits : List Bool) (argument : Nat)
    (ha : argument < 2 ^ Experiment.width bits.length) :
    RankExecutionSafety (Allocation.memory bits) (Experiment.width bits.length)
      (program .access) ((source .access).size + 1) (initial .access false argument) := by
  have cap := fixed_floor_capacity bits.length 132 (by decide)
  exact rank_compiled_safety (Allocation.memory bits) (Experiment.width bits.length)
    (source .access) 705 _ (initial .access false argument).regs rfl
    (by rw [source_budget]; exact cap)
    (canonical_access_source_fieldsFit bits)
    (by have := fixed_floor_capacity bits.length 705 (by decide)
        simp [Instruction.Fits, Instruction.encoding, Instruction.operands]
        omega)
    (initial_data_fits bits .access false argument ha)
    (canonical_access_source_safe bits argument ha)

theorem canonical_rank_execution_safe (bits : List Bool) (target : Bool) (argument : Nat)
    (ha : argument < 2 ^ Experiment.width bits.length) :
    RankExecutionSafety (Allocation.memory bits) (Experiment.width bits.length)
      (program .rank) ((source .rank).size + 1) (initial .rank target argument) := by
  have cap := fixed_floor_capacity bits.length 1450 (by decide)
  exact rank_compiled_safety (Allocation.memory bits) (Experiment.width bits.length)
    (source .rank) 360 _ (initial .rank target argument).regs rfl
    (by rw [source_budget]; exact cap)
    (canonical_rank_source_fieldsFit bits)
    (by simp [Instruction.Fits, Instruction.encoding, Instruction.operands]; omega)
    (initial_data_fits bits .rank target argument ha)
    (canonical_rank_source_safe bits target argument ha)

#print axioms canonical_access_source_safe
#print axioms canonical_rank_source_safe
#print axioms canonical_access_execution_safe
#print axioms canonical_rank_execution_safe

end RMQ.PackedBitvector
