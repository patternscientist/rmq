import RMQ.Core.WordRAM.Native.Lifecycle.Repack

/-! # One export contract for the produced lifecycle owner

Every construction projection below concerns `buildFirst`, without assuming a
final-memory or answer equality. The domain is the original all-size lifecycle
domain and represented endpoints, including represented invalid RMQ ranges.
Host admission and foreign ownership/capacity are deliberately not hypotheses
or conclusions of this kernel contract.
-/

namespace RMQ.SuccinctFinal.PackedNative.Lifecycle

open PackedLifecycle
open PackedWordRAM (buildMemory wordWidth)
open PackedWordRAM.Optimization (compactQueryRun)

set_option maxRecDepth 30000

theorem ready_metadata {xs : List Int} {owner : Owner} (ready : Ownership.Ready xs owner) :
    owner.memory.getD 0 none = some xs.length ∧
      owner.memory.getD 7 none = some owner.memory.size := by
  have contents : (fun a => owner.memory.getD a none) = fun a => (buildMemory xs)[a]? :=
    ready.2.1.1
  refine ⟨(congrFun contents 0).trans (Builder.metadata_zero xs), ?_⟩
  rw [congrFun contents 7, Builder.metadata_seven, ready.memory_size]

structure QueryContract (model : InputModel) (xs : List Int) (left right : Nat)
    (owner : Owner) : Prop where
  source : query model left right owner = Executable.queryOwner model left right owner
  projection : (query model left right owner).toState =
    (Reusable.queryRun model left right owner.toState).final
  ready : Ownership.Ready xs (query model left right owner)
  halted : (query model left right owner).status = .halted
    (PackedWordRAM.optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value)
  memory : (query model left right owner).memory = owner.memory
  observations : (Executable.queryArray model left right owner).toRun =
    Reusable.queryRun model left right owner.toState
  boundary : (requestProtocol Layout.serviceEntry left right owner.toState).steps = 4 ∧
    (requestProtocol Layout.serviceEntry left right owner.toState).categories =
      [.requestAdmission, .requestAdmission, .controlEntry, .controlEntry]
  steps : (Reusable.queryRun model left right owner.toState).steps = 4 + 4 + QueryEntry.setupCost +
    (compactQueryRun (buildMemory xs) xs.length left right).steps
  budget : (Reusable.queryRun model left right owner.toState).steps ≤ 160257
  capacity : Ownership.capacity model (query model left right owner) * wordWidth xs.length ≤
    2 * xs.length + retainedRho xs.length

theorem query_contract (model : InputModel) (xs : List Int) (left right answer : Nat)
    (owner : Owner) (ready : Ownership.Ready xs owner) (halted : owner.status = .halted answer)
    (hl : left < 2 ^ wordWidth xs.length) (hr : right < 2 ^ wordWidth xs.length) :
    QueryContract model xs left right owner := by
  have reuse := ready.query model left right answer halted hl hr
  have refinement := Executable.query_owner_refinement model xs left right answer owner
    ready.1 ready.2 halted hl hr
  have correct := Reusable.query_correct model xs left right answer owner.toState ready.2 halted hl hr
  exact {
    source := query_eq model left right owner
    projection := by rw [query_eq]; exact refinement.1
    ready := by rw [query_eq]; exact reuse.1
    halted := by rw [query_eq]; exact reuse.2.1
    memory := by rw [query_eq]; exact reuse.2.2.1
    observations := reuse.2.2.2.1
    boundary := (requestProtocol_exact Layout.serviceEntry left right answer owner.toState halted).2
    steps := correct.2.2.2.2.1
    budget := reuse.2.2.2.2
    capacity := by rw [query_eq]; exact reuse.1.capacity_bound model }

structure ExportContract (model : InputModel) (xs : List Int) (left right : Nat) : Prop where
  program : cachedProgram model = (Layout.program model).toArray
  owner : buildFirst model xs left right = Ownership.owner model xs left right
  projection : (buildFirst model xs left right).toState =
    (Continuous.continuousRun model xs left right).final
  ready : Ownership.Ready xs (buildFirst model xs left right)
  halted : (buildFirst model xs left right).status = .halted
    (PackedWordRAM.optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value)
  memory : (∀ a, (buildFirst model xs left right).memory.getD a none = (buildMemory xs)[a]?) ∧
    (buildFirst model xs left right).memory.size = (buildMemory xs).length
  emptyKeys : (buildFirst model xs left right).keys = #[] ∧
    (buildFirst model xs left right).keyRegs = #[]
  bank : (buildFirst model xs left right).regs.size = 8273
  capacity : Ownership.capacity model (buildFirst model xs left right) * wordWidth xs.length ≤
    2 * xs.length + retainedRho xs.length
  metadata : (buildFirst model xs left right).memory.getD 0 none = some xs.length ∧
    (buildFirst model xs left right).memory.getD 7 none =
      some (buildFirst model xs left right).memory.size
  observations : (Ownership.observations model xs left right).toRun =
    Continuous.continuousRun model xs left right
  continuation : ∀ (es : Owner) (newLeft newRight answer : Nat), Ownership.Ready xs es →
    es.status = .halted answer → newLeft < 2 ^ wordWidth xs.length →
    newRight < 2 ^ wordWidth xs.length → QueryContract model xs newLeft newRight es
  repacking : ∀ (source target : Owner) (newLeft newRight : Nat), Repacked source target →
    target = source ∧ target.toState = source.toState ∧ target.status = source.status ∧
      (Ownership.Ready xs target ↔ Ownership.Ready xs source) ∧
      Ownership.capacity model target = Ownership.capacity model source ∧
      query model newLeft newRight target = query model newLeft newRight source

theorem export_contract (model : InputModel) (xs : List Int) (left right : Nat)
    (domain : InputDomain model xs) (hl : left < 2 ^ wordWidth xs.length)
    (hr : right < 2 ^ wordWidth xs.length) : ExportContract model xs left right := by
  have ready : Ownership.Ready xs (buildFirst model xs left right) := by
    rw [buildFirst_eq]
    exact Ownership.ready model xs left right domain hl hr
  have refinement := Ownership.refinement model xs left right domain hl hr
  exact {
    program := cachedProgram_eq model
    owner := buildFirst_eq model xs left right
    projection := by rw [buildFirst_eq]; exact refinement.1
    ready := ready
    halted := by rw [buildFirst_eq]; exact Ownership.halted model xs left right domain hl hr
    memory := ⟨fun a => congrFun ready.2.1.1 a, ready.memory_size⟩
    emptyKeys := ready.empty_keys
    bank := ready.1
    capacity := ready.capacity_bound model
    metadata := ready_metadata ready
    observations := refinement.2.2
    continuation := fun es newLeft newRight answer hrdy hhalt hleft hright =>
      query_contract model xs newLeft newRight answer es hrdy hhalt hleft hright
    repacking := fun source target newLeft newRight copy =>
      repack_transport xs model newLeft newRight source target copy }

theorem word_export_contract (xs : List Int) (left right : Nat)
    (domain : PackedConstruction.InputFits (wordWidth xs.length) xs)
    (hl : left < 2 ^ wordWidth xs.length) (hr : right < 2 ^ wordWidth xs.length) :
    ExportContract .word xs left right :=
  export_contract .word xs left right domain hl hr

theorem comparison_export_contract (xs : List Int) (left right : Nat)
    (hl : left < 2 ^ wordWidth xs.length) (hr : right < 2 ^ wordWidth xs.length) :
    ExportContract .comparison xs left right :=
  export_contract .comparison xs left right trivial hl hr

end RMQ.SuccinctFinal.PackedNative.Lifecycle
