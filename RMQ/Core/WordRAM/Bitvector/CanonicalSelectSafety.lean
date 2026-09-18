import RMQ.Core.WordRAM.Bitvector.GenericSelectSafety
import RMQ.Core.WordRAM.Bitvector.Metadata
import RMQ.Core.WordRAM.Bitvector.CanonicalStoreBounds
import RMQ.Core.WordRAM.Bitvector.CanonicalMemoryBounds

/-! # Safety of the complete canonical select program

The numerical interfaces are derived from the same allocation that the setup,
reader and compiled select program execute. Only machine-input representability
is assumed by the final source and execution theorems.
-/

namespace RMQ.PackedBitvector

open SuccinctSpace SuccinctRank GenericSelect
open SuccinctFinal.PackedWordRAM SuccinctFinal.PackedWordRAM.Structured

private theorem scalarHeader_entry_bound (bits : List Bool) (index : Nat) :
    ((Allocation.scalarHeader bits)[index]?).getD 0 ≤ canonicalEnvelope bits.length := by
  cases he : (Allocation.scalarHeader bits)[index]? with
  | none => simp
  | some value =>
      simpa only [he, Option.getD_some] using
        canonical_scalarHeader_bound bits value (List.mem_of_getElem? he)

private theorem setupMetadata_envelope (bits : List Bool) (regs : Registers)
    (bound : ∀ r, 16 ≤ r → r < 190 → regs r ≤ canonicalEnvelope bits.length) :
    ∀ r, 16 ≤ r → r < 190 →
      ChargedSetup.setupMetadata bits regs r ≤ canonicalEnvelope bits.length := by
  intro r hlo hhi
  simp only [ChargedSetup.setupMetadata, if_neg (show r ≠ 6 by omega)]
  split
  · exact scalarHeader_entry_bound bits _
  · exact bound r hlo hhi

private theorem targetMetadata_envelope (bits : List Bool) (regs : Registers)
    (bound : ∀ r, 16 ≤ r → r < 190 → regs r ≤ canonicalEnvelope bits.length) :
    ∀ r, 16 ≤ r → r < 190 →
      ChargedSetup.targetMetadata bits regs r ≤ canonicalEnvelope bits.length := by
  intro r hlo hhi
  simp only [ChargedSetup.targetMetadata]
  split
  · exact bound r hlo hhi
  · simp only [if_neg (show r ≠ 6 by omega)]
    split
    · exact bound 17 (by decide) (by decide)
    · split
      · exact scalarHeader_entry_bound bits _
      · exact bound r hlo hhi

/-- Every low controller metadata value is one of the charged header replies or
an unchanged bounded input register. This applies to all three operations. -/
theorem loadedMetadata_envelope (bits : List Bool) (operation : Operation)
    (target : Bool) (argument r : Nat) (hlo : 16 ≤ r) (hhi : r < 190) :
    loadedMetadata bits operation target argument r ≤ canonicalEnvelope bits.length := by
  have initialBound : ∀ i, 16 ≤ i → i < 190 →
      (initial operation target argument).regs i ≤ canonicalEnvelope bits.length := by
    intro i hi hj
    have h3 : i ≠ 3 := by omega
    have ha : i ≠ argumentRegister operation := by
      cases operation <;> simp only [argumentRegister] <;> omega
    simp [initial, h3, ha]
  have hs := setupMetadata_envelope bits (initial operation target argument).regs initialBound
  cases operation with
  | access => exact hs r hlo hhi
  | rank => exact hs r hlo hhi
  | select => exact targetMetadata_envelope bits _ hs r hlo hhi

/-- The target used by the loaded flag geometry; access and rank retain the
false-target flags that the initial setup actually loads. -/
def controllerGeometryTarget (operation : Operation) (target : Bool) : Bool :=
  match operation with
  | .select => target
  | _ => false

theorem loadedMetadata_controller_geometry (bits : List Bool) (operation : Operation)
    (target : Bool) (argument : Nat) :
    let regs := loadedMetadata bits operation target argument
    let d := sparseExceptionSelectData bits (controllerGeometryTarget operation target)
    regs 25 = d.superStride ∧ regs 26 = d.localStride ∧ regs 27 = d.localSlotsPerSuper ∧
    regs 28 = d.longFlagBits.length ∧ regs 29 = d.sparseDirectory.flagBits.length ∧
    regs 30 = d.longFlagRankData.wordSize ∧ regs 31 = d.sparseDirectory.rankData.wordSize ∧
    regs 32 = d.wordSize := by
  cases operation <;> cases target <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The actual loaded model satisfies every shared numerical field, without an
extra geometry or metadata premise. -/
theorem loadedModel_safetyBounds (bits : List Bool) (operation : Operation)
    (target : Bool) (argument : Nat) :
    Controller.ControllerSafetyBounds (loadedModel bits operation target argument)
      (canonicalLimits bits.length) := by
  let d := sparseExceptionSelectData bits (controllerGeometryTarget operation target)
  have hg := loadedMetadata_controller_geometry bits operation target argument
  dsimp only at hg
  constructor
  · exact loadedMetadata_envelope bits operation target argument
  · change 0 < loadedMetadata bits operation target argument 25
    rw [hg.1]
    exact d.superStride_pos
  · change 0 < loadedMetadata bits operation target argument 26
    rw [hg.2.1]
    exact d.localStride_pos
  · change 0 < loadedMetadata bits operation target argument 30
    rw [hg.2.2.2.2.2.1]
    exact d.longFlagRankData.wordSize_pos
  · change 0 < loadedMetadata bits operation target argument 31
    rw [hg.2.2.2.2.2.2.1]
    exact d.sparseDirectory.rankData.wordSize_pos
  · change 0 < loadedMetadata bits operation target argument 32
    rw [hg.2.2.2.2.2.2.2]
    exact d.wordSize_pos
  · change 0 < loadedMetadata bits operation target argument 34
    rw [loadedMetadata_chunk]
    exact SuccinctClose.bpFringeChunkBits_pos _
  · change loadedMetadata bits operation target argument 32 ≤ machineWordBits bits.length
    rw [hg.2.2.2.2.2.2.2]
    exact d.wordSize_le_machine
  · change loadedMetadata bits operation target argument 34 ≤ machineWordBits bits.length
    rw [loadedMetadata_chunk]
    exact chunkBits_le_machine _
  · exact canonical_directory_packet bits target
  · exact canonical_table_packet bits target
  · exact canonical_raw_length bits target

/-- Canonical physical-reader safety follows from the actual numerical memory
and descriptor geometry, for every state matching the loaded model. -/
theorem loadedModel_readerSafe (bits : List Bool) (operation : Operation)
    (target : Bool) (argument : Nat) :
    Controller.ReaderSafe (loadedModel bits operation target argument)
      (Experiment.width bits.length) (Allocation.memory bits) Experiment.physicalReader := by
  intro s fit hm
  by_cases running : s.status = .running
  · have he : s = ⟨s.regs, .running⟩ := by cases s; simp_all
    rw [he] at fit ⊢
    have ht : s.regs 3 = target.toNat :=
      (hm 3 (by decide)).trans (loadedMetadata_target bits operation target argument)
    have hw : s.regs 22 = Experiment.width bits.length :=
      (hm 22 (by decide)).trans (loadedMetadata_width bits operation target argument)
    exact physicalReader_safe _ _ s.regs (by have := width_floor bits.length; omega)
      (canonical_memoryWordsFit bits) fit hw
      (canonical_numericReaderGeometry bits target s.regs ⟨ht, hw⟩)
  · exact Block.safe_stopped _ _ _ s fit running

theorem initial_data_fits (bits : List Bool) (operation : Operation)
    (target : Bool) (argument : Nat) (ha : argument < 2 ^ Experiment.width bits.length) :
    (⟨(initial operation target argument).regs, .running⟩ : Data).Fits
      (Experiment.width bits.length) := by
  refine ⟨?_, ?_⟩
  · intro r
    have hp := (canonicalLimits bits.length).constant_fit 1 (by decide)
    change 1 < 2 ^ Experiment.width bits.length at hp
    simp only [initial]
    split
    · cases target
      · exact Nat.two_pow_pos _
      · exact hp
    · split
      · exact ha
      · exact Nat.two_pow_pos _
  · intro value h
    exact Status.noConfusion h

/-- The charged setup stages and the shared controller are safe on the exact
canonical source entry state. -/
theorem canonical_select_source_safe (bits : List Bool) (target : Bool) (argument : Nat)
    (ha : argument < 2 ^ Experiment.width bits.length) :
    (source .select).Safe (Allocation.memory bits) (Experiment.width bits.length)
      ⟨(initial .select target argument).regs, .running⟩ := by
  have fit := initial_data_fits bits .select target argument ha
  have mem := canonical_memoryWordsFit bits
  have setup := ChargedSetup.setup_safe bits _ _ (width_floor bits.length) mem fit
  have setupFit := Block.eval_fits _ _ _ _ setup
  change (Block.seq Experiment.setup
    (.seq Experiment.targetSetup (selectCloseBlock Experiment.physicalReader))).Safe _ _ _
  apply Block.safe_seq setup
  rw [ChargedSetup.setup_source] at setupFit ⊢
  have targetSetup := ChargedSetup.targetSetup_safe bits _ _ (width_floor bits.length) mem setupFit
  have targetFit := Block.eval_fits _ _ _ _ targetSetup
  apply Block.safe_seq targetSetup
  rw [ChargedSetup.targetSetup_source] at targetFit ⊢
  exact Controller.physicalSelect_safe (loadedModel bits .select target argument)
    (canonicalLimits bits.length) (loadedModel_safetyBounds bits .select target argument)
    (Allocation.memory bits) (loadedModel_readerSafe bits .select target argument)
    (loadedModel_reader bits .select target argument) _ targetFit (fun _ _ => rfl)

theorem canonical_select_source_fieldsFit (bits : List Bool) :
    (source .select).FieldsFit (Experiment.width bits.length) := by
  have cap := (canonicalLimits bits.length).constant_fit 8280 (by decide)
  change 8280 < 2 ^ Experiment.width bits.length at cap
  have selectFields := selectCloseBlock_fieldsFit _ _
    (Controller.physicalReader_fieldsFit (canonicalLimits bits.length)) cap
  change (selectCloseBlock Experiment.physicalReader).FieldsFit
    (Experiment.width bits.length) at selectFields
  have hwne : Experiment.width bits.length ≠ 0 := by have := width_floor bits.length; omega
  simp [source, operationBody, Experiment.setup, Experiment.targetSetup, List.range_succ,
    Block.sequence, Block.FieldsFit, Action.instruction, Instruction.Fits, Instruction.encoding,
    Instruction.operands, selectFields, hwne]
  omega

theorem canonical_select_source_budget : (source .select).size + 1 = 10030 := by
  simp [source, operationBody, Experiment.setup, Experiment.targetSetup, List.range_succ,
    selectCloseBlock_size, physicalReader_size, Block.sequence, Block.size]

/-- Safety observations of the complete, fixed compiled select program, from
its actual initial state on its actual canonical allocation. -/
theorem canonical_select_execution_safe (bits : List Bool) (target : Bool) (argument : Nat)
    (ha : argument < 2 ^ Experiment.width bits.length) :
    Controller.SelectExecutionSafety (Allocation.memory bits) (Experiment.width bits.length)
      (program .select) ((source .select).size + 1) (initial .select target argument) := by
  have cap := (canonicalLimits bits.length).constant_fit 10030 (by decide)
  change 10030 < 2 ^ Experiment.width bits.length at cap
  exact rank_compiled_safety (Allocation.memory bits) (Experiment.width bits.length)
    (source .select) 513 _ (initial .select target argument).regs rfl
    (by rw [canonical_select_source_budget]; exact cap)
    (canonical_select_source_fieldsFit bits)
    (by simp [Instruction.Fits, Instruction.encoding, Instruction.operands]; omega)
    (initial_data_fits bits .select target argument ha)
    (canonical_select_source_safe bits target argument ha)

theorem canonical_select_execution_safe_expectedType
    (bits : List Bool) (target : Bool) (argument : Nat)
    (ha : argument < 2 ^ Experiment.width bits.length) :
    let actual := execute bits .select target argument
    (∀ instruction ∈ program .select, instruction.Fits (Experiment.width bits.length)) ∧
    actual.final.Fits (Experiment.width bits.length) ∧
    (∀ (index : Nat) (t : Transition), actual.transitions[index]? = some t →
      Instruction.Safe (Experiment.width bits.length) t.before t.instruction ∧
        t.after.Fits (Experiment.width bits.length)) ∧
    (∀ index, index ≤ (source .select).size + 1 →
      (run (Allocation.memory bits) (program .select) index (initial .select target argument)).final.Fits
        (Experiment.width bits.length)) ∧
    (∀ (index : Nat) (t : Transition) (receipt : Receipt),
      actual.transitions[index]? = some t → t.receipt = some receipt →
      receipt.address < 2 ^ Experiment.width bits.length ∧
      receipt.reply = (Allocation.memory bits)[receipt.address]? ∧
        (∀ value, receipt.reply = some value → value < 2 ^ Experiment.width bits.length)) :=
  canonical_select_execution_safe bits target argument ha

end RMQ.PackedBitvector
