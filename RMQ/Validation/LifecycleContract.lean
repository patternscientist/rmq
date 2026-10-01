import RMQ.Core.WordRAM.Lifecycle.Capstone

/-! # Frozen LIFE-1 client propositions

The expected propositions below are independent source text. In particular they
do not abbreviate the producer's seven property aliases, `Retained.Canonical`,
`Ownership.Ready`, or `Continuous.PrefixProfile`. Each consumer projects the
actual public theorem. Shadow-source replay weakens that theorem's fields while
leaving this file unchanged. Lower machine predicates retain their usual meaning.
-/

namespace RMQ.SuccinctFinal.PackedLifecycle.ContractChecks

open PackedWordRAM (wordWidth buildMemory)
open PackedWordRAM.Optimization (compactQueryRun)
open Continuous (continuousRun constructionBudget)
set_option maxRecDepth 30000

def ExpectedCanonical (xs : List Int) (s : State) : Prop :=
  (s.core.memory = (fun a => (buildMemory xs)[a]?) ∧
    s.core.extent = (buildMemory xs).length ∧
    s.core.keys = (fun _ => none) ∧ s.core.keyRegs = (fun _ => 0) ∧
    s.keyExtent = 0 ∧ s.keyRegExtent = 0) ∧
  (∀ r, 8273 ≤ r → s.core.regs r = 0) ∧ s.Fits (wordWidth xs.length)

def ExpectedReady (xs : List Int) (es : Owner) : Prop :=
  es.regs.size = 8273 ∧ ExpectedCanonical xs es.toState

def ExpectedPrefix (model : InputModel) (xs : List Int) (s : State) : Prop :=
  s.Fits (wordWidth xs.length) ∧ PackedConstruction.CleanTail s.core ∧
    (∀ r, 8273 ≤ r → s.core.regs r = 0) ∧ s.core.extent ≤ 5000000 * (xs.length + 1) ∧
    s.keyExtent ≤ (if model = .comparison then xs.length else 0) ∧
    s.keyRegExtent ≤ (if model = .comparison then 2 else 0)

variable (model : InputModel) (xs : List Int) (left right : Nat)
  (domain : InputDomain model xs) (hl : left < 2 ^ wordWidth xs.length)
  (hr : right < 2 ^ wordWidth xs.length)

include domain hl hr

theorem publicContract : ContinuousConstructionQuery model xs left right :=
  continuousConstructionQuery_holds model xs left right domain hl hr

theorem checkC01_construction :
    ∃ abstract producer body,
      Construction.BuildStage model xs left right abstract producer body ∧
      (Finalization.fullTrace model xs left right producer body).length ≤ constructionBudget xs.length ∧
      ExpectedCanonical xs (Finalization.finalState model xs left right producer) ∧
      ((Finalization.finalState model xs left right producer).core.status = .running ∧
      (Finalization.finalState model xs left right producer).core.pc = Service.entry ∧
      (Finalization.finalState model xs left right producer).core.regs 300 = left ∧
      (Finalization.finalState model xs left right producer).core.regs 301 = right) ∧
      continuousRun model xs left right =
        ⟨(Reusable.serviceRun model (Finalization.finalState model xs left right producer)).final,
          Finalization.fullTrace model xs left right producer body ++
            (Reusable.serviceRun model (Finalization.finalState model xs left right producer)).transitions⟩ ∧
      ∃ entryTransitions : List Transition,
        entryTransitions.length = 4 + 8271 ∧
        (continuousRun model xs left right).transitions =
          Finalization.fullTrace model xs left right producer body ++ entryTransitions ++
            (compactQueryRun (buildMemory xs) xs.length left right).transitions.map
              (QuerySafetyBridge.liftTransition (buildMemory xs)) ∧
        (continuousRun model xs left right).steps =
          (Finalization.fullTrace model xs left right producer body).length + 4 + 8271 +
            (compactQueryRun (buildMemory xs) xs.length left right).steps :=
  (publicContract model xs left right domain hl hr).construction

theorem checkC02_retained :
    ExpectedCanonical xs (continuousRun model xs left right).final ∧
      (continuousRun model xs left right).final.core.status = .halted
        (PackedWordRAM.optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value) ∧
      (continuousRun model xs left right).steps ≤ constructionBudget xs.length + 160253 :=
  (publicContract model xs left right domain hl hr).retained

theorem checkC03_safety :
    (∀ fuel, fuel ≤ (continuousRun model xs left right).steps →
      ExpectedPrefix model xs
        (run (Layout.program model) fuel (initialState model xs left right Layout.builderBase)).final) ∧
    ∀ t ∈ (continuousRun model xs left right).transitions,
      t.Safe (wordWidth xs.length) (Layout.program model).length :=
  (publicContract model xs left right domain hl hr).safety

theorem checkC04_physical :
    (Physical.physicalReads model (continuousRun model xs left right).transitions).map
        Physical.Read.logicalReceipt = (continuousRun model xs left right).reads ∧
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
        physical < 2 ^ wordWidth xs.length ∧ address < 2 ^ wordWidth xs.length ∧
        value < 2 ^ wordWidth xs.length) ∧
    ∀ (index : Nat) (t : Transition), (continuousRun model xs left right).transitions[index]? = some t →
      ∃ instruction : Instruction, t.action = .instruction instruction ∧
        (Layout.program model)[t.before.core.pc]? = some instruction ∧
        ∀ field word, instruction.encoding[field]? = some word →
          Physical.codeOffset (Layout.program model) t.before.core.pc + field < Physical.codeLength model ∧
          Physical.lookup model t.before
            (Physical.codeAddress model
              (Physical.codeOffset (Layout.program model) t.before.core.pc + field)) = some word :=
  (publicContract model xs left right domain hl hr).physical

theorem checkC05_executable :
    let es := Ownership.owner model xs left right
    es.toState = (continuousRun model xs left right).final ∧
      (Ownership.observations model xs left right).toRun = continuousRun model xs left right ∧
      ExpectedReady xs es ∧ es.keys = #[] ∧ es.keyRegs = #[] ∧
      (es.memory.size + (encodedProgram model).length + es.regs.size + 8) * wordWidth xs.length ≤
        2 * xs.length + retainedRho xs.length :=
  (publicContract model xs left right domain hl hr).executable

theorem checkC06_reusable :
    ∀ (es : Owner) (newLeft newRight answer : Nat), ExpectedReady xs es → es.status = .halted answer →
      newLeft < 2 ^ wordWidth xs.length → newRight < 2 ^ wordWidth xs.length →
      ExpectedReady xs (Executable.queryOwner model newLeft newRight es) ∧
      (Executable.queryOwner model newLeft newRight es).status = .halted
        (PackedWordRAM.optionNatPacket (SuccinctClassic.queryTraceResult xs newLeft newRight).value) ∧
      (Executable.queryOwner model newLeft newRight es).memory = es.memory ∧
      (Executable.queryArray model newLeft newRight es).toRun = Reusable.queryRun model newLeft newRight es.toState ∧
      (Reusable.queryRun model newLeft newRight es.toState).steps ≤ 160257 ∧
      (Reusable.queryRun model newLeft newRight es.toState).reads = (0, some xs.length) ::
        (compactQueryRun (buildMemory xs) xs.length newLeft newRight).reads.map (fun r => (r.address, r.reply)) ∧
      (∀ t ∈ (Reusable.queryRun model newLeft newRight es.toState).transitions,
        t.ActionSafe (wordWidth xs.length) (Layout.program model).length 8273 Layout.serviceEntry.val ∧
        ExpectedCanonical xs t.before ∧ ExpectedCanonical xs t.after) ∧
      ((Executable.queryOwner model newLeft newRight es).memory.size + (encodedProgram model).length +
        (Executable.queryOwner model newLeft newRight es).regs.size + 8) * wordWidth xs.length ≤
        2 * xs.length + retainedRho xs.length :=
  (publicContract model xs left right domain hl hr).reusable

theorem checkC07_uniform :
    SuccinctSpace.LittleOLinear retainedRho ∧
      (Nat.log2 (xs.length + 2) + 1 ≤ wordWidth xs.length ∧
        wordWidth xs.length ≤ 192 * (Nat.log2 (xs.length + 2) + 1)) ∧
      ∀ word ∈ encodedProgram model, word < 2 ^ wordWidth xs.length :=
  (publicContract model xs left right domain hl hr).uniform

omit domain in
/-- Both public input forms must return the actual seven-field interface. -/
theorem checkC08_word (input : PackedConstruction.InputFits (wordWidth xs.length) xs) :
    ContinuousConstructionQuery .word xs left right :=
  wordInputContinuousConstructionQuery xs left right input hl hr

omit domain in
theorem checkC09_comparison : ContinuousConstructionQuery .comparison xs left right :=
  comparisonInputContinuousConstructionQuery xs left right hl hr

omit domain hl hr in
/-- Compile-time pins on the shared constants used by the frozen client. -/
theorem checkC10_constants : numericBank = 8273 ∧ controlWords = 8 ∧ codeWordBudget = 1116895 ∧
    QueryEntry.setupCost = 8271 ∧ Reusable.queryBudget = 160257 ∧ Service.budget = 160253 ∧
    (∀ n, constructionBudget n = 1100000000 * (n + 1)) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩

omit domain hl hr in
theorem checkC11_valid (contract : ContinuousConstructionQuery model xs left right)
    (valid : ValidRange xs left right) :
    (continuousRun model xs left right).final.core.status = .halted (scanWindow xs left (right - left) + 1) ∧
      LeftmostArgMin xs left right (scanWindow xs left (right - left)) :=
  contract.valid valid

omit domain hl hr in
theorem checkC12_invalid (contract : ContinuousConstructionQuery model xs left right)
    (invalid : ¬ ValidRange xs left right) :
    (continuousRun model xs left right).final.core.status = .halted 0 :=
  contract.invalid invalid

omit domain hl hr in
theorem checkC13_store (fuel : Nat) (s t : State)
    (initial :
      (s.core.regs = t.core.regs ∧ s.core.extent = t.core.extent ∧
        s.core.keyRegs = t.core.keyRegs ∧ s.core.pc = t.core.pc ∧ s.core.status = t.core.status) ∧
      s.keyExtent = t.keyExtent ∧ s.keyRegExtent = t.keyRegExtent)
    (reads : DynamicReadsAgree (Layout.program model) fuel s t) :
    (run (Layout.program model) fuel s).Agree (run (Layout.program model) fuel t) ∧
    (run (Layout.program model) fuel s).final.core.status = (run (Layout.program model) fuel t).final.core.status ∧
    (run (Layout.program model) fuel s).reads = (run (Layout.program model) fuel t).reads ∧
    ∀ category, (run (Layout.program model) fuel s).categoryCount category =
      (run (Layout.program model) fuel t).categoryCount category :=
  lifecycle_store_determinism model fuel s t initial reads

omit domain hl hr in
/-- The supplied-store premise includes both actual fetches and the numeric
extent guard. Its key channel is separately the existing Int lookup. -/
theorem checkC14_store_guard (program : List Instruction) (fuel : Nat) (s t : State) :
    DynamicReadsAgree program (fuel + 1) s t =
      (match step program s, step program t with
       | some a, some b =>
           (∀ i, a.action = .instruction i →
             (∀ dst address, i = .old (.load dst address) →
               s.core.regs address < s.core.extent →
               t.core.memory (s.core.regs address) = s.core.memory (s.core.regs address)) ∧
             (∀ dst address, i = .old (.loadKey dst address) →
               t.core.keys (s.core.regs address) = s.core.keys (s.core.regs address))) ∧
             DynamicReadsAgree program fuel a.after b.after
       | _, _ => True) := rfl

end RMQ.SuccinctFinal.PackedLifecycle.ContractChecks
