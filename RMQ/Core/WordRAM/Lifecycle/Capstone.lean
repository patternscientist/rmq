import RMQ.Core.WordRAM.Lifecycle.Profile
import RMQ.Core.WordRAM.Lifecycle.Ownership
import RMQ.Core.WordRAM.Lifecycle.Agreement
import RMQ.Core.WordRAM.Lifecycle.CodeFetch

/-! # Continuous succinct construction and reusable charged queries

This candidate interface concerns the numeric primitive model and its finite
container refinement. Input materialization precedes execution. Comparison
keys are separately counted arbitrary integers. Logical owned sizes are not
native allocator capacity or external alias claims.
-/

namespace RMQ.SuccinctFinal.PackedLifecycle

open PackedWordRAM (wordWidth buildMemory)
open PackedWordRAM.Optimization (compactQueryRun)
open Continuous (continuousRun constructionBudget)
set_option maxRecDepth 30000

/-- The construction witness retains the actual hosted body and its producing
trace. Neither the retained allocation nor the query answer is a premise. -/
def ConstructionChain (model : InputModel) (xs : List Int) (left right : Nat) : Prop :=
  ∃ abstract producer body,
    Construction.BuildStage model xs left right abstract producer body ∧
    (Finalization.fullTrace model xs left right producer body).length ≤ constructionBudget xs.length ∧
    Retained.Canonical xs (Finalization.finalState model xs left right producer) ∧
    ServiceSafety.Entered left right (Finalization.finalState model xs left right producer) ∧
    continuousRun model xs left right =
      ⟨(Reusable.serviceRun model (Finalization.finalState model xs left right producer)).final,
        Finalization.fullTrace model xs left right producer body ++
          (Reusable.serviceRun model (Finalization.finalState model xs left right producer)).transitions⟩ ∧
    ∃ entryTransitions : List Transition,
      entryTransitions.length = 4 + QueryEntry.setupCost ∧
      (continuousRun model xs left right).transitions =
        Finalization.fullTrace model xs left right producer body ++ entryTransitions ++
          (compactQueryRun (buildMemory xs) xs.length left right).transitions.map
            (QuerySafetyBridge.liftTransition (buildMemory xs)) ∧
      (continuousRun model xs left right).steps =
        (Finalization.fullTrace model xs left right producer body).length + 4 + QueryEntry.setupCost +
          (compactQueryRun (buildMemory xs) xs.length left right).steps

def ExecutedOwner (model : InputModel) (xs : List Int) (left right : Nat) : Prop :=
  let es := Ownership.owner model xs left right
  es.toState = (continuousRun model xs left right).final ∧
    (Ownership.observations model xs left right).toRun = continuousRun model xs left right ∧
    Ownership.Ready xs es ∧ es.keys = #[] ∧ es.keyRegs = #[] ∧
    Ownership.capacity model es * wordWidth xs.length ≤ 2 * xs.length + retainedRho xs.length

/-- Re-entry operates on any previously halted retained owner, so the same
statement applies repeatedly without carrying request history. -/
def ReusableOwner (model : InputModel) (xs : List Int) : Prop :=
  ∀ (es : Owner) (left right answer : Nat), Ownership.Ready xs es → es.status = .halted answer →
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    Ownership.Ready xs (Executable.queryOwner model left right es) ∧
    (Executable.queryOwner model left right es).status = .halted
      (PackedWordRAM.optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value) ∧
    (Executable.queryOwner model left right es).memory = es.memory ∧
    (Executable.queryArray model left right es).toRun = Reusable.queryRun model left right es.toState ∧
    (Reusable.queryRun model left right es.toState).steps ≤ Reusable.queryBudget ∧
    (Reusable.queryRun model left right es.toState).reads = (0, some xs.length) ::
      (compactQueryRun (buildMemory xs) xs.length left right).reads.map (fun r => (r.address, r.reply)) ∧
    (∀ t ∈ (Reusable.queryRun model left right es.toState).transitions,
      t.ActionSafe (wordWidth xs.length) (Layout.program model).length numericBank Layout.serviceEntry.val ∧
      Retained.Canonical xs t.before ∧ Retained.Canonical xs t.after) ∧
    Ownership.capacity model (Executable.queryOwner model left right es) * wordWidth xs.length ≤
      2 * xs.length + retainedRho xs.length

def PhysicalRun (model : InputModel) (xs : List Int) (left right : Nat) : Prop :=
  (Physical.physicalReads model (continuousRun model xs left right).transitions).map Physical.Read.logicalReceipt =
    (continuousRun model xs left right).reads ∧
  (∀ fuel, fuel ≤ (continuousRun model xs left right).steps →
    let s := (run (Layout.program model) fuel (initialState model xs left right Layout.builderBase)).final
    Physical.extent model s < 2 ^ wordWidth xs.length ∧
      ∀ p value, Physical.lookup model s p = some value → value < 2 ^ wordWidth xs.length) ∧
  (∀ index t address reply, (continuousRun model xs left right).transitions[index]? = some t →
    t.read? = some (address, reply) →
    t.before = (run (Layout.program model) index (initialState model xs left right Layout.builderBase)).final ∧
    (Physical.imageTrace model (continuousRun model xs left right).transitions)[index]? =
      some ⟨Physical.view model t.before, t.action, Physical.view model t.after⟩ ∧
    ∃ physical value, Physical.checkedAddress model t.before address = some physical ∧
      reply = some value ∧ Physical.lookup model t.before physical = some value ∧
      physical < 2 ^ wordWidth xs.length ∧ address < 2 ^ wordWidth xs.length ∧ value < 2 ^ wordWidth xs.length) ∧
  ∀ (index : Nat) (t : Transition), (continuousRun model xs left right).transitions[index]? = some t →
    ∃ instruction : Instruction, t.action = .instruction instruction ∧
      (Layout.program model)[t.before.core.pc]? = some instruction ∧
      ∀ field word, instruction.encoding[field]? = some word →
        Physical.codeOffset (Layout.program model) t.before.core.pc + field < Physical.codeLength model ∧
        Physical.lookup model t.before
          (Physical.codeAddress model (Physical.codeOffset (Layout.program model) t.before.core.pc + field)) = some word

/-- Seven connected interfaces expose the same run, retained owner, fixed code
and width. Proof witnesses carry no executable routing information. -/
structure ContinuousConstructionQuery (model : InputModel) (xs : List Int) (left right : Nat) : Prop where
  construction : ConstructionChain model xs left right
  retained : Retained.Canonical xs (continuousRun model xs left right).final ∧
    (continuousRun model xs left right).final.core.status = .halted
      (PackedWordRAM.optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value) ∧
    (continuousRun model xs left right).steps ≤ constructionBudget xs.length + 160253
  safety : (∀ fuel, fuel ≤ (continuousRun model xs left right).steps →
    Continuous.PrefixProfile model xs
      (run (Layout.program model) fuel (initialState model xs left right Layout.builderBase)).final) ∧
    ∀ t ∈ (continuousRun model xs left right).transitions,
      t.Safe (wordWidth xs.length) (Layout.program model).length
  physical : PhysicalRun model xs left right
  executable : ExecutedOwner model xs left right
  reusable : ReusableOwner model xs
  uniform : SuccinctSpace.LittleOLinear retainedRho ∧
    (Nat.log2 (xs.length + 2) + 1 ≤ wordWidth xs.length ∧
      wordWidth xs.length ≤ 192 * (Nat.log2 (xs.length + 2) + 1)) ∧
    ∀ word ∈ encodedProgram model, word < 2 ^ wordWidth xs.length

theorem reusableOwner_holds (model : InputModel) (xs : List Int) : ReusableOwner model xs := by
  intro es left right answer ready halted hl hr
  have outcome := ready.query model left right answer halted hl hr
  refine ⟨outcome.1, outcome.2.1, outcome.2.2.1, outcome.2.2.2.1, outcome.2.2.2.2,
    Reusable.query_reads model xs left right answer es.toState ready.2 halted hl hr, ?_,
    outcome.1.capacity_bound model⟩
  intro t ht
  exact ⟨Reusable.query_action_safe model xs left right answer es.toState ready.2 halted hl hr t ht,
    Reusable.query_transition_canonical model xs left right answer es.toState ready.2 halted hl hr t ht⟩

theorem continuousConstructionQuery_holds (model : InputModel) (xs : List Int) (left right : Nat)
    (domain : InputDomain model xs) (hl : left < 2 ^ wordWidth xs.length)
    (hr : right < 2 ^ wordWidth xs.length) : ContinuousConstructionQuery model xs left right := by
  obtain ⟨abstract, producer, body, built⟩ := Construction.build_stage model xs left right domain hl hr
  have produced := Finalization.completed built
  obtain ⟨entry, entryLength, suffix⟩ := Continuous.query_suffix built
  have ready := Ownership.ready model xs left right domain hl hr
  have refines := Ownership.refinement model xs left right domain hl hr
  refine {
    construction := ⟨abstract, producer, body, built, Finalization.linear_cost built,
      produced.2.1, Continuous.entered_of_inputs produced.2.2.1, Continuous.exact_run built,
      entry, entryLength, suffix, (Continuous.cost built).1⟩
    retained := ⟨Continuous.canonical built, Continuous.halts built, (Continuous.cost built).2⟩
    safety := ⟨fun fuel within => Continuous.prefix_profile built domain hl hr within, Continuous.safe built⟩
    physical := ⟨Physical.physicalReads_exact model _,
      fun fuel within => Continuous.physical_prefix built domain hl hr within,
      Continuous.physical_read built domain hl hr,
      Physical.run_fetched_words model (Continuous.lifecycleBudget xs.length)
        (initialState model xs left right Layout.builderBase)⟩
    executable := ⟨refines.1, refines.2.2, ready, ready.empty_keys.1, ready.empty_keys.2,
      ready.capacity_bound model⟩
    reusable := reusableOwner_holds model xs
    uniform := ⟨retainedRho_littleO,
      ⟨PackedWordRAM.wordWidth_log_lower xs.length, PackedWordRAM.wordWidth_le_log xs.length⟩,
      all_encoded_fields_fit model xs.length⟩
  }

/-- Word-input form: input values are represented at the same query-independent
width as construction, addresses, code, retained data and queries. -/
theorem wordInputContinuousConstructionQuery (xs : List Int) (left right : Nat)
    (domain : PackedConstruction.InputFits (wordWidth xs.length) xs)
    (hl : left < 2 ^ wordWidth xs.length) (hr : right < 2 ^ wordWidth xs.length) :
    ContinuousConstructionQuery .word xs left right :=
  continuousConstructionQuery_holds .word xs left right domain hl hr

/-- Arbitrary signed input keys use the separately counted comparison channel;
their Int magnitudes are not asserted to occupy bounded numeric words. -/
theorem comparisonInputContinuousConstructionQuery (xs : List Int) (left right : Nat)
    (hl : left < 2 ^ wordWidth xs.length) (hr : right < 2 ^ wordWidth xs.length) :
    ContinuousConstructionQuery .comparison xs left right :=
  continuousConstructionQuery_holds .comparison xs left right True.intro hl hr

theorem ContinuousConstructionQuery.valid {model : InputModel} {xs : List Int} {left right : Nat}
    (contract : ContinuousConstructionQuery model xs left right) (valid : ValidRange xs left right) :
    (continuousRun model xs left right).final.core.status = .halted (scanWindow xs left (right - left) + 1) ∧
      LeftmostArgMin xs left right (scanWindow xs left (right - left)) := by
  have packet := Option.some.inj ((PackedWordRAM.Optimization.compactQueryRun_result xs left right).symm.trans
    (PackedWordRAM.Optimization.compactQueryRun_scanWindow xs left right valid))
  exact ⟨by rw [contract.retained.2.1, packet],
    PackedWordRAM.Optimization.compactQueryNat_leftmost xs left right _
      (by rw [PackedWordRAM.Optimization.compactQueryNat_exact, if_pos valid])⟩

theorem ContinuousConstructionQuery.invalid {model : InputModel} {xs : List Int} {left right : Nat}
    (contract : ContinuousConstructionQuery model xs left right) (invalid : ¬ ValidRange xs left right) :
    (continuousRun model xs left right).final.core.status = .halted 0 := by
  have invalidPacket := PackedWordRAM.Optimization.compactQueryRun_invalid
    (buildMemory xs) xs.length left right invalid
  have packet := Option.some.inj ((PackedWordRAM.Optimization.compactQueryRun_result xs left right).symm.trans
    invalidPacket.1)
  rw [contract.retained.2.1, packet]

/-- Supplied-store agreement is stated on the actual fixed program, with all
guarded replies at matched execution steps. Its conclusion constrains results,
registers, ordered observations and each cost category. -/
theorem lifecycle_store_determinism (model : InputModel) (fuel : Nat) (s t : State)
    (initial : s.Agree t) (reads : DynamicReadsAgree (Layout.program model) fuel s t) :
    (run (Layout.program model) fuel s).Agree (run (Layout.program model) fuel t) ∧
    (run (Layout.program model) fuel s).final.core.status = (run (Layout.program model) fuel t).final.core.status ∧
    (run (Layout.program model) fuel s).reads = (run (Layout.program model) fuel t).reads ∧
    ∀ category, (run (Layout.program model) fuel s).categoryCount category =
      (run (Layout.program model) fuel t).categoryCount category := by
  have agreement := run_agree_of_dynamic_reads (Layout.program model) fuel s t initial reads
  exact ⟨agreement, agreement.final_status, agreement.reads, agreement.categoryCount⟩

end RMQ.SuccinctFinal.PackedLifecycle
