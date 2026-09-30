import RMQ.Core.WordRAM.Native.Lifecycle.Contract
import RMQ.Core.WordRAM.Native.Lifecycle.BoundaryProofs

/-! # Independent expected propositions for the native lifecycle exports

Each check projects a mandatory public field at fixed objects. Ready and
capacity are expanded in independently written expected types, so the checks
do not merely accept a mutable producer record type. Producer-compiling
weakening/deletion/sibling controls must retain this consumer unchanged.
-/

namespace RMQ.SuccinctFinal.PackedNative.Lifecycle.ContractChecks

open PackedLifecycle
open PackedWordRAM (buildMemory wordWidth)
open PackedWordRAM.Optimization (compactQueryRun)

set_option maxRecDepth 30000

def ExpectedCanonical (xs : List Int) (s : State) : Prop :=
  (s.core.memory = (fun a => (buildMemory xs)[a]?) ∧
    s.core.extent = (buildMemory xs).length ∧
    s.core.keys = (fun _ => none) ∧ s.core.keyRegs = (fun _ => 0) ∧
    s.keyExtent = 0 ∧ s.keyRegExtent = 0) ∧
  (∀ r, 8273 ≤ r → s.core.regs r = 0) ∧ s.Fits (wordWidth xs.length)

def ExpectedReady (xs : List Int) (es : Owner) : Prop :=
  es.regs.size = 8273 ∧ ExpectedCanonical xs es.toState

variable (model : InputModel) (xs : List Int) (left right : Nat)
  (domain : InputDomain model xs) (hl : left < 2 ^ wordWidth xs.length)
  (hr : right < 2 ^ wordWidth xs.length)

include domain hl hr

theorem checkE01_program : cachedProgram model = (Layout.program model).toArray :=
  by with_reducible exact (export_contract model xs left right domain hl hr).program

theorem checkE02_owner : buildFirst model xs left right = Ownership.owner model xs left right :=
  by with_reducible exact (export_contract model xs left right domain hl hr).owner

theorem checkE03_projection : (buildFirst model xs left right).toState =
    (Continuous.continuousRun model xs left right).final :=
  (export_contract model xs left right domain hl hr).projection

theorem checkE04_ready : ExpectedReady xs (buildFirst model xs left right) :=
  (export_contract model xs left right domain hl hr).ready

theorem checkE05_halted : (buildFirst model xs left right).status = .halted
    (PackedWordRAM.optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value) :=
  (export_contract model xs left right domain hl hr).halted

theorem checkE06_memory :
    (∀ a, (buildFirst model xs left right).memory.getD a none = (buildMemory xs)[a]?) ∧
    (buildFirst model xs left right).memory.size = (buildMemory xs).length :=
  (export_contract model xs left right domain hl hr).memory

theorem checkE07_emptyKeys : (buildFirst model xs left right).keys = #[] ∧
    (buildFirst model xs left right).keyRegs = #[] :=
  (export_contract model xs left right domain hl hr).emptyKeys

theorem checkE08_bank : (buildFirst model xs left right).regs.size = 8273 :=
  (export_contract model xs left right domain hl hr).bank

theorem checkE09_capacity :
    ((buildFirst model xs left right).memory.size + (encodedProgram model).length +
      (buildFirst model xs left right).regs.size + 8) * wordWidth xs.length ≤
    2 * xs.length + retainedRho xs.length :=
  (export_contract model xs left right domain hl hr).capacity

theorem checkE10_metadata : (buildFirst model xs left right).memory.getD 0 none = some xs.length ∧
    (buildFirst model xs left right).memory.getD 7 none =
      some (buildFirst model xs left right).memory.size :=
  (export_contract model xs left right domain hl hr).metadata

theorem checkE11_observations : (Ownership.observations model xs left right).toRun =
    Continuous.continuousRun model xs left right :=
  (export_contract model xs left right domain hl hr).observations

theorem checkE12_repacking (source target : Owner) (newLeft newRight : Nat)
    (copy : Repacked source target) :
    target = source ∧ target.toState = source.toState ∧ target.status = source.status ∧
      (ExpectedReady xs target ↔ ExpectedReady xs source) ∧
      (target.memory.size + (encodedProgram model).length + target.regs.size + 8) =
        (source.memory.size + (encodedProgram model).length + source.regs.size + 8) ∧
      query model newLeft newRight target = query model newLeft newRight source :=
  (export_contract model xs left right domain hl hr).repacking source target newLeft newRight copy

variable (es : Owner) (newLeft newRight answer : Nat) (ready : ExpectedReady xs es)
  (halted : es.status = .halted answer) (hnewLeft : newLeft < 2 ^ wordWidth xs.length)
  (hnewRight : newRight < 2 ^ wordWidth xs.length)

include ready halted hnewLeft hnewRight

theorem checkQ01_source : query model newLeft newRight es = Executable.queryOwner model newLeft newRight es :=
  ((export_contract model xs left right domain hl hr).continuation es newLeft newRight answer
    ready halted hnewLeft hnewRight).source

theorem checkQ02_projection : (query model newLeft newRight es).toState =
    (Reusable.queryRun model newLeft newRight es.toState).final :=
  ((export_contract model xs left right domain hl hr).continuation es newLeft newRight answer
    ready halted hnewLeft hnewRight).projection

theorem checkQ03_ready : ExpectedReady xs (query model newLeft newRight es) :=
  ((export_contract model xs left right domain hl hr).continuation es newLeft newRight answer
    ready halted hnewLeft hnewRight).ready

theorem checkQ04_halted : (query model newLeft newRight es).status = .halted
    (PackedWordRAM.optionNatPacket (SuccinctClassic.queryTraceResult xs newLeft newRight).value) :=
  ((export_contract model xs left right domain hl hr).continuation es newLeft newRight answer
    ready halted hnewLeft hnewRight).halted

theorem checkQ05_memory : (query model newLeft newRight es).memory = es.memory :=
  ((export_contract model xs left right domain hl hr).continuation es newLeft newRight answer
    ready halted hnewLeft hnewRight).memory

theorem checkQ06_observations : (Executable.queryArray model newLeft newRight es).toRun =
    Reusable.queryRun model newLeft newRight es.toState :=
  ((export_contract model xs left right domain hl hr).continuation es newLeft newRight answer
    ready halted hnewLeft hnewRight).observations

theorem checkQ07_boundary : (requestProtocol Layout.serviceEntry newLeft newRight es.toState).steps = 4 ∧
    (requestProtocol Layout.serviceEntry newLeft newRight es.toState).categories =
      [.requestAdmission, .requestAdmission, .controlEntry, .controlEntry] :=
  ((export_contract model xs left right domain hl hr).continuation es newLeft newRight answer
    ready halted hnewLeft hnewRight).boundary

theorem checkQ08_steps : (Reusable.queryRun model newLeft newRight es.toState).steps =
    4 + 4 + 8271 + (compactQueryRun (buildMemory xs) xs.length newLeft newRight).steps :=
  ((export_contract model xs left right domain hl hr).continuation es newLeft newRight answer
    ready halted hnewLeft hnewRight).steps

theorem checkQ09_budget : (Reusable.queryRun model newLeft newRight es.toState).steps ≤ 160257 :=
  ((export_contract model xs left right domain hl hr).continuation es newLeft newRight answer
    ready halted hnewLeft hnewRight).budget

theorem checkQ10_capacity :
    ((query model newLeft newRight es).memory.size + (encodedProgram model).length +
      (query model newLeft newRight es).regs.size + 8) * wordWidth xs.length ≤
    2 * xs.length + retainedRho xs.length := by
  have projection :=
    ((export_contract model xs left right domain hl hr).continuation es newLeft newRight answer
    ready halted hnewLeft hnewRight).capacity
  change Ownership.capacity model (query model newLeft newRight es) * wordWidth xs.length ≤
    2 * xs.length + retainedRho xs.length
  with_reducible exact projection

omit ready halted hnewLeft hnewRight in
theorem checkE13_invalid (invalid : ¬ ValidRange xs left right) :
    (buildFirst model xs left right).status = .halted 0 ∧
      ExpectedReady xs (buildFirst model xs left right) := by
  refine ⟨?_, (export_contract model xs left right domain hl hr).ready⟩
  rw [(export_contract model xs left right domain hl hr).halted,
    SuccinctClassic.queryTraceResult_invalid xs left right invalid]
  rfl

theorem checkQ11_invalid (invalid : ¬ ValidRange xs newLeft newRight) :
    (query model newLeft newRight es).status = .halted 0 ∧
      ExpectedReady xs (query model newLeft newRight es) := by
  have contract := (export_contract model xs left right domain hl hr).continuation es
    newLeft newRight answer ready halted hnewLeft hnewRight
  refine ⟨?_, contract.ready⟩
  rw [contract.halted, SuccinctClassic.queryTraceResult_invalid xs newLeft newRight invalid]
  rfl

omit domain hl hr ready halted hnewLeft hnewRight in
theorem checkU01_cached_run (fuel : Nat) (owner : Owner) :
    runOwner (cachedProgram model) fuel owner =
      runOwner (Layout.program model).toArray fuel owner :=
  cached_run model fuel owner

omit domain hl hr ready halted hnewLeft hnewRight in
theorem checkU02_word (input : PackedConstruction.InputFits (wordWidth xs.length) xs)
    (hleft : left < 2 ^ wordWidth xs.length) (hright : right < 2 ^ wordWidth xs.length) :
    (buildFirst .word xs left right).status = .halted
      (PackedWordRAM.optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value) :=
  (word_export_contract xs left right input hleft hright).halted

omit domain hl hr ready halted hnewLeft hnewRight in
theorem checkU03_comparison
    (hleft : left < 2 ^ wordWidth xs.length) (hright : right < 2 ^ wordWidth xs.length) :
    (buildFirst .comparison xs left right).status = .halted
      (PackedWordRAM.optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value) :=
  (comparison_export_contract xs left right hleft hright).halted

end RMQ.SuccinctFinal.PackedNative.Lifecycle.ContractChecks

namespace RMQ.SuccinctFinal.PackedNative.Lifecycle.ContractChecks

open PackedLifecycle
open PackedWordRAM (wordWidth optionNatPacket)

theorem checkT01_arbitraryRun (program : Array Instruction) (fuel : Nat) (owner : Owner) :
    runThin program fuel owner = runOwner program fuel owner :=
  runThin_eq_runOwner program fuel owner

theorem checkT02_arbitraryBoundary (boundaries : List Boundary) (owner : Owner) :
    runBoundaryThin boundaries owner = runBoundaryOwner boundaries owner :=
  runBoundaryThin_eq_runBoundaryOwner boundaries owner

theorem checkT03_arbitraryRequest (entry : PackedConstruction.Operand)
    (left right : Nat) (owner : Owner) :
    requestProtocolThin entry left right owner = requestProtocolOwner entry left right owner :=
  requestProtocolThin_eq_requestProtocolOwner entry left right owner

theorem checkT04_arbitraryObservedRun (program : Array Instruction) (fuel : Nat)
    (owner : Owner) (stats : Observations.Stats) :
    Observations.runAccThin program fuel owner stats =
      Observations.runAcc program fuel owner stats :=
  Observations.runAccThin_eq_runAcc program fuel owner stats

theorem checkT05_arbitraryObservedBoundary (boundaries : List Boundary) (owner : Owner)
    (stats : Observations.Stats) :
    Observations.boundaryAccThin boundaries owner stats =
      Observations.boundaryAcc boundaries owner stats :=
  Observations.boundaryAccThin_eq_boundaryAcc boundaries owner stats

theorem checkT06_arbitraryNativeFuel (comparison : Bool) (fuel : Nat) (owner : Owner) :
    nativeRunFuel comparison fuel owner =
      runOwner (Layout.program (modelOfComparison comparison)).toArray fuel owner :=
  nativeRunFuel_source comparison fuel owner

theorem checkT07_arbitraryObservation (stats : Observations.Stats) (transition : ArrayTransition) :
    stats.record transition = stats.recordBefore transition.action transition.before :=
  Observations.Stats.record_eq_recordBefore stats transition

theorem expectedByteCanonical (width : Nat) (bytes : ByteArray) :
    LimbWord.Canonical width bytes.data ↔
      bytes.size = LimbWord.limbCount width ∧ decodeMagnitude bytes < 2 ^ width := Iff.rfl

theorem checkB01_metadata (xs : List Int) (owner : Owner) (ready : ExpectedReady xs owner) :
    nativeMetadata owner 0 = some xs.length ∧ nativeMetadata owner 7 = some owner.memory.size :=
  nativeMetadata_ready ready

theorem checkB02_count (model : InputModel) (xs : List Int) (left right : Nat)
    (domain : InputDomain model xs) (hl : left < 2 ^ wordWidth xs.length)
    (hr : right < 2 ^ wordWidth xs.length) :
    producedCount (buildFirst model xs left right) = xs.length ∧
      nativeMetadata (buildFirst model xs left right) 0 = some xs.length ∧
      nativeMetadata (buildFirst model xs left right) 7 =
        some (buildFirst model xs left right).memory.size :=
  buildFirst_metadata model xs left right domain hl hr

theorem checkB03_queryAdmission (xs : List Int) (owner : Owner) (left right : ByteArray)
    (ready : ExpectedReady xs owner) :
    nativeQueryAdmit owner left right = true ↔
      (left.size = LimbWord.limbCount (wordWidth xs.length) ∧
        decodeMagnitude left < 2 ^ wordWidth xs.length) ∧
      (right.size = LimbWord.limbCount (wordWidth xs.length) ∧
        decodeMagnitude right < 2 ^ wordWidth xs.length) :=
  nativeQueryAdmit_iff xs owner left right ready

theorem checkB04_first (comparison : Bool) (xs : List Int) (count : Nat)
    (left right : ByteArray) (accepted : nativeAdmit comparison xs count left right = true) :
    nativeBuildFirst comparison xs left right = Ownership.owner (modelOfComparison comparison) xs
      (decodeMagnitude left) (decodeMagnitude right) ∧
    ExpectedReady xs (nativeBuildFirst comparison xs left right) ∧
    (nativeBuildFirst comparison xs left right).status = .halted
      (optionNatPacket (SuccinctClassic.queryTraceResult xs
        (decodeMagnitude left) (decodeMagnitude right)).value) :=
  nativeBuildFirst_correct comparison xs count left right accepted

theorem checkB05_firstPacket (comparison : Bool) (xs : List Int) (count : Nat)
    (left right : ByteArray) (accepted : nativeAdmit comparison xs count left right = true) :
    nativePacket (nativeBuildFirst comparison xs left right) = encodeEndpoint (wordWidth xs.length)
      (optionNatPacket (SuccinctClassic.queryTraceResult xs
        (decodeMagnitude left) (decodeMagnitude right)).value) ∧
    ((nativePacket (nativeBuildFirst comparison xs left right)).size =
      LimbWord.limbCount (wordWidth xs.length) ∧
      decodeMagnitude (nativePacket (nativeBuildFirst comparison xs left right)) < 2 ^ wordWidth xs.length) ∧
    decodeMagnitude (nativePacket (nativeBuildFirst comparison xs left right)) =
      optionNatPacket (SuccinctClassic.queryTraceResult xs
        (decodeMagnitude left) (decodeMagnitude right)).value :=
  let h := nativeBuildFirst_packet comparison xs count left right accepted
  ⟨h.1, (expectedByteCanonical _ _).1 h.2.1, h.2.2⟩

theorem checkB06_query (comparison : Bool) (xs : List Int) (owner : Owner)
    (left right : ByteArray) (answer : Nat) (ready : ExpectedReady xs owner)
    (halted : owner.status = .halted answer) (accepted : nativeQueryAdmit owner left right = true) :
    ExpectedReady xs (nativeQuery comparison left right owner) ∧
    (nativeQuery comparison left right owner).status = .halted
      (optionNatPacket (SuccinctClassic.queryTraceResult xs
        (decodeMagnitude left) (decodeMagnitude right)).value) ∧
    (nativeQuery comparison left right owner).memory = owner.memory :=
  nativeQuery_correct comparison xs owner left right answer ready halted accepted

theorem checkB07_queryPacket (comparison : Bool) (xs : List Int) (owner : Owner)
    (left right : ByteArray) (answer : Nat) (ready : ExpectedReady xs owner)
    (halted : owner.status = .halted answer) (accepted : nativeQueryAdmit owner left right = true) :
    nativePacket (nativeQuery comparison left right owner) = encodeEndpoint (wordWidth xs.length)
      (optionNatPacket (SuccinctClassic.queryTraceResult xs
        (decodeMagnitude left) (decodeMagnitude right)).value) ∧
    ((nativePacket (nativeQuery comparison left right owner)).size =
      LimbWord.limbCount (wordWidth xs.length) ∧
      decodeMagnitude (nativePacket (nativeQuery comparison left right owner)) < 2 ^ wordWidth xs.length) ∧
    decodeMagnitude (nativePacket (nativeQuery comparison left right owner)) =
      optionNatPacket (SuccinctClassic.queryTraceResult xs
        (decodeMagnitude left) (decodeMagnitude right)).value :=
  let h := nativeQuery_packet comparison xs owner left right answer ready halted accepted
  ⟨h.1, (expectedByteCanonical _ _).1 h.2.1, h.2.2⟩

theorem checkB08_packetFits (xs : List Int) (left right : Nat) :
    optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value < 2 ^ wordWidth xs.length :=
  answer_packet_fits xs left right

theorem checkB09_allSizeFirstPacket (model : InputModel) (xs : List Int) (left right : Nat)
    (domain : InputDomain model xs) (hl : left < 2 ^ wordWidth xs.length)
    (hr : right < 2 ^ wordWidth xs.length) :
    nativePacket (buildFirst model xs left right) = encodeEndpoint (wordWidth xs.length)
      (optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value) ∧
    ((nativePacket (buildFirst model xs left right)).size = LimbWord.limbCount (wordWidth xs.length) ∧
      decodeMagnitude (nativePacket (buildFirst model xs left right)) < 2 ^ wordWidth xs.length) ∧
    decodeMagnitude (nativePacket (buildFirst model xs left right)) =
      optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value :=
  let h := buildFirst_packet model xs left right domain hl hr
  ⟨h.1, (expectedByteCanonical _ _).1 h.2.1, h.2.2⟩

theorem checkB10_allSizeQueryPacket (model : InputModel) (xs : List Int) (owner : Owner)
    (left right answer : Nat) (ready : ExpectedReady xs owner) (halted : owner.status = .halted answer)
    (hl : left < 2 ^ wordWidth xs.length) (hr : right < 2 ^ wordWidth xs.length) :
    nativePacket (query model left right owner) = encodeEndpoint (wordWidth xs.length)
      (optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value) ∧
    ((nativePacket (query model left right owner)).size = LimbWord.limbCount (wordWidth xs.length) ∧
      decodeMagnitude (nativePacket (query model left right owner)) < 2 ^ wordWidth xs.length) ∧
    decodeMagnitude (nativePacket (query model left right owner)) =
      optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value :=
  let h := query_packet model xs owner left right answer ready halted hl hr
  ⟨h.1, (expectedByteCanonical _ _).1 h.2.1, h.2.2⟩

theorem checkB11_initial (comparison : Bool) (xs : List Int) (left right : ByteArray) :
    nativeInitial comparison xs left right = Executable.initialOwner (modelOfComparison comparison) xs
      (decodeMagnitude left) (decodeMagnitude right) := rfl

theorem checkB12_firstComposition (comparison : Bool) (xs : List Int) (left right : ByteArray) :
    nativeRunFirst comparison xs.length (nativeInitial comparison xs left right) =
      nativeBuildFirst comparison xs left right :=
  nativeInitial_runFirst comparison xs left right

theorem checkB13_observedComposition (comparison : Bool) (xs : List Int) (left right : ByteArray) :
    nativeRunFirstObserved comparison xs.length (nativeInitial comparison xs left right) =
      nativeBuildFirstObserved comparison xs left right :=
  nativeInitial_runFirstObserved comparison xs left right

theorem checkB14_observedFirstOwner (comparison : Bool) (xs : List Int) (left right : ByteArray) :
    (nativeRunFirstObserved comparison xs.length (nativeInitial comparison xs left right)).1 =
      nativeBuildFirst comparison xs left right := by
  rw [nativeInitial_runFirstObserved]
  exact nativeBuildFirstObserved_owner comparison xs left right

theorem checkB15_observedQueryOwner (comparison : Bool) (left right : ByteArray) (owner : Owner) :
    (nativeQueryObserved comparison left right owner).1 = nativeQuery comparison left right owner :=
  nativeQueryObserved_owner comparison left right owner

theorem checkB16_observedArbitraryOwner (comparison : Bool) (count : Nat) (owner : Owner) :
    (nativeRunFirstObserved comparison count owner).1 = nativeRunFirst comparison count owner := by
  unfold nativeRunFirstObserved nativeRunFirst
  rw [runThin_eq_runOwner]
  exact Observations.run_owner _ _ _

theorem checkB17_admittedComposition (comparison : Bool) (xs : List Int) (count : Nat)
    (left right : ByteArray) (accepted : nativeAdmit comparison xs count left right = true) :
    nativeRunFirst comparison count (nativeInitial comparison xs left right) =
      nativeBuildFirst comparison xs left right :=
  nativeInitial_runFirst_admitted comparison xs count left right accepted

theorem checkB18_admittedObservedComposition (comparison : Bool) (xs : List Int) (count : Nat)
    (left right : ByteArray) (accepted : nativeAdmit comparison xs count left right = true) :
    nativeRunFirstObserved comparison count (nativeInitial comparison xs left right) =
      nativeBuildFirstObserved comparison xs left right :=
  nativeInitial_runFirstObserved_admitted comparison xs count left right accepted

end RMQ.SuccinctFinal.PackedNative.Lifecycle.ContractChecks

namespace RMQ.SuccinctFinal.PackedNative.Lifecycle.ContractChecks

open PackedLifecycle
open PackedWordRAM (wordWidth)

set_option maxRecDepth 30000

/-! These checks pin the exported scalar IDs as well as the underlying counts.
First-run observations contain construction and the first request; query
observations contain only the four re-entry events and the service suffix. -/

section FirstObservations

theorem expectedStepCounter (stats : Observations.Stats) :
    nativeObservationCounter stats 15 = stats.steps := rfl

variable (comparison : Bool) (xs : List Int) (left right : ByteArray)
  (domain : InputDomain (modelOfComparison comparison) xs)
  (hl : decodeMagnitude left < 2 ^ wordWidth xs.length)
  (hr : decodeMagnitude right < 2 ^ wordWidth xs.length)

include domain hl hr

theorem checkO01_firstSteps :
    nativeObservationCounter (nativeBuildFirstObserved comparison xs left right).2 15 = (Continuous.continuousRun (modelOfComparison comparison) xs (decodeMagnitude left) (decodeMagnitude right)).steps := by
  rw [expectedStepCounter]
  exact (Observations.buildFirst_model_observations (modelOfComparison comparison) xs (decodeMagnitude left) (decodeMagnitude right) domain hl hr).1

theorem checkO02_firstCategories :
    nativeObservationCounter (nativeBuildFirstObserved comparison xs left right).2 0 =
      (Continuous.continuousRun (modelOfComparison comparison) xs (decodeMagnitude left) (decodeMagnitude right)).categoryCount (.old .read) ∧
    nativeObservationCounter (nativeBuildFirstObserved comparison xs left right).2 1 =
      (Continuous.continuousRun (modelOfComparison comparison) xs (decodeMagnitude left) (decodeMagnitude right)).categoryCount (.old .register) ∧
    nativeObservationCounter (nativeBuildFirstObserved comparison xs left right).2 2 =
      (Continuous.continuousRun (modelOfComparison comparison) xs (decodeMagnitude left) (decodeMagnitude right)).categoryCount (.old .arithmetic) ∧
    nativeObservationCounter (nativeBuildFirstObserved comparison xs left right).2 3 =
      (Continuous.continuousRun (modelOfComparison comparison) xs (decodeMagnitude left) (decodeMagnitude right)).categoryCount (.old .comparison) ∧
    nativeObservationCounter (nativeBuildFirstObserved comparison xs left right).2 4 =
      (Continuous.continuousRun (modelOfComparison comparison) xs (decodeMagnitude left) (decodeMagnitude right)).categoryCount (.old .branch) ∧
    nativeObservationCounter (nativeBuildFirstObserved comparison xs left right).2 5 =
      (Continuous.continuousRun (modelOfComparison comparison) xs (decodeMagnitude left) (decodeMagnitude right)).categoryCount (.old .control) ∧
    nativeObservationCounter (nativeBuildFirstObserved comparison xs left right).2 6 =
      (Continuous.continuousRun (modelOfComparison comparison) xs (decodeMagnitude left) (decodeMagnitude right)).categoryCount (.old .write) ∧
    nativeObservationCounter (nativeBuildFirstObserved comparison xs left right).2 7 =
      (Continuous.continuousRun (modelOfComparison comparison) xs (decodeMagnitude left) (decodeMagnitude right)).categoryCount (.old .allocation) ∧
    nativeObservationCounter (nativeBuildFirstObserved comparison xs left right).2 8 =
      (Continuous.continuousRun (modelOfComparison comparison) xs (decodeMagnitude left) (decodeMagnitude right)).categoryCount (.old .keyRead) ∧
    nativeObservationCounter (nativeBuildFirstObserved comparison xs left right).2 9 =
      (Continuous.continuousRun (modelOfComparison comparison) xs (decodeMagnitude left) (decodeMagnitude right)).categoryCount (.old .oracleComparison) ∧
    nativeObservationCounter (nativeBuildFirstObserved comparison xs left right).2 10 =
      (Continuous.continuousRun (modelOfComparison comparison) xs (decodeMagnitude left) (decodeMagnitude right)).categoryCount (.numericRelease) ∧
    nativeObservationCounter (nativeBuildFirstObserved comparison xs left right).2 11 =
      (Continuous.continuousRun (modelOfComparison comparison) xs (decodeMagnitude left) (decodeMagnitude right)).categoryCount (.keyRelease) ∧
    nativeObservationCounter (nativeBuildFirstObserved comparison xs left right).2 12 =
      (Continuous.continuousRun (modelOfComparison comparison) xs (decodeMagnitude left) (decodeMagnitude right)).categoryCount (.keyRegisterRelease) ∧
    nativeObservationCounter (nativeBuildFirstObserved comparison xs left right).2 13 =
      (Continuous.continuousRun (modelOfComparison comparison) xs (decodeMagnitude left) (decodeMagnitude right)).categoryCount (.requestAdmission) ∧
    nativeObservationCounter (nativeBuildFirstObserved comparison xs left right).2 14 =
      (Continuous.continuousRun (modelOfComparison comparison) xs (decodeMagnitude left) (decodeMagnitude right)).categoryCount (.controlEntry) := by
  have h := (Observations.buildFirst_model_observations (modelOfComparison comparison) xs (decodeMagnitude left) (decodeMagnitude right) domain hl hr).2.1
  exact ⟨h (.old .read),
    h (.old .register),
    h (.old .arithmetic),
    h (.old .comparison),
    h (.old .branch),
    h (.old .control),
    h (.old .write),
    h (.old .allocation),
    h (.old .keyRead),
    h (.old .oracleComparison),
    h (.numericRelease),
    h (.keyRelease),
    h (.keyRegisterRelease),
    h (.requestAdmission),
    h (.controlEntry)⟩

theorem checkO03_firstOrderedReads :
    nativeObservationReads (nativeBuildFirstObserved comparison xs left right).2 = (Continuous.continuousRun (modelOfComparison comparison) xs (decodeMagnitude left) (decodeMagnitude right)).reads.toArray :=
  congrArg List.toArray
    (Observations.buildFirst_model_observations (modelOfComparison comparison) xs (decodeMagnitude left) (decodeMagnitude right) domain hl hr).2.2

omit domain hl hr in
theorem checkO04_firstRoutes :
    nativeObservationRoute (nativeBuildFirstObserved comparison xs left right).2 0 =
      (Ownership.observations (modelOfComparison comparison) xs (decodeMagnitude left) (decodeMagnitude right)).transitions.countP
        (Observations.routeMarked .compactQuery) ∧
    nativeObservationRoute (nativeBuildFirstObserved comparison xs left right).2 1 =
      (Ownership.observations (modelOfComparison comparison) xs (decodeMagnitude left) (decodeMagnitude right)).transitions.countP
        (Observations.routeMarked .servicePrepare) ∧
    nativeObservationRoute (nativeBuildFirstObserved comparison xs left right).2 2 =
      (Ownership.observations (modelOfComparison comparison) xs (decodeMagnitude left) (decodeMagnitude right)).transitions.countP
        (Observations.routeMarked .serviceSetup) ∧
    nativeObservationRoute (nativeBuildFirstObserved comparison xs left right).2 3 =
      (Ownership.observations (modelOfComparison comparison) xs (decodeMagnitude left) (decodeMagnitude right)).transitions.countP
        (Observations.routeMarked .builder) ∧
    nativeObservationRoute (nativeBuildFirstObserved comparison xs left right).2 4 =
      (Ownership.observations (modelOfComparison comparison) xs (decodeMagnitude left) (decodeMagnitude right)).transitions.countP
        (Observations.routeMarked .descriptor) ∧
    nativeObservationRoute (nativeBuildFirstObserved comparison xs left right).2 5 =
      (Ownership.observations (modelOfComparison comparison) xs (decodeMagnitude left) (decodeMagnitude right)).transitions.countP
        (Observations.routeMarked .finalizer) ∧
    nativeObservationRoute (nativeBuildFirstObserved comparison xs left right).2 6 =
      (Ownership.observations (modelOfComparison comparison) xs (decodeMagnitude left) (decodeMagnitude right)).transitions.countP
        (Observations.routeMarked .retirement) ∧
    nativeObservationRoute (nativeBuildFirstObserved comparison xs left right).2 7 =
      (Ownership.observations (modelOfComparison comparison) xs (decodeMagnitude left) (decodeMagnitude right)).transitions.countP
        (Observations.routeMarked .sameBlockDecision) ∧
    nativeObservationRoute (nativeBuildFirstObserved comparison xs left right).2 8 =
      (Ownership.observations (modelOfComparison comparison) xs (decodeMagnitude left) (decodeMagnitude right)).transitions.countP
        (Observations.routeMarked .crossBlockDecision) ∧
    nativeObservationRoute (nativeBuildFirstObserved comparison xs left right).2 9 =
      (Ownership.observations (modelOfComparison comparison) xs (decodeMagnitude left) (decodeMagnitude right)).transitions.countP
        (Observations.routeMarked .interiorNonemptyDecision) ∧
    nativeObservationRoute (nativeBuildFirstObserved comparison xs left right).2 10 =
      (Ownership.observations (modelOfComparison comparison) xs (decodeMagnitude left) (decodeMagnitude right)).transitions.countP
        (Observations.routeMarked .interiorEmptyDecision) ∧
    nativeObservationRoute (nativeBuildFirstObserved comparison xs left right).2 11 =
      (Ownership.observations (modelOfComparison comparison) xs (decodeMagnitude left) (decodeMagnitude right)).transitions.countP
        (Observations.routeMarked .interiorReadMarker) ∧
    nativeObservationRoute (nativeBuildFirstObserved comparison xs left right).2 12 =
      (Ownership.observations (modelOfComparison comparison) xs (decodeMagnitude left) (decodeMagnitude right)).transitions.countP
        (Observations.routeMarked .crossingSecondLoad) :=
  ⟨Observations.buildFirst_route (modelOfComparison comparison) xs (decodeMagnitude left) (decodeMagnitude right) .compactQuery,
    Observations.buildFirst_route (modelOfComparison comparison) xs (decodeMagnitude left) (decodeMagnitude right) .servicePrepare,
    Observations.buildFirst_route (modelOfComparison comparison) xs (decodeMagnitude left) (decodeMagnitude right) .serviceSetup,
    Observations.buildFirst_route (modelOfComparison comparison) xs (decodeMagnitude left) (decodeMagnitude right) .builder,
    Observations.buildFirst_route (modelOfComparison comparison) xs (decodeMagnitude left) (decodeMagnitude right) .descriptor,
    Observations.buildFirst_route (modelOfComparison comparison) xs (decodeMagnitude left) (decodeMagnitude right) .finalizer,
    Observations.buildFirst_route (modelOfComparison comparison) xs (decodeMagnitude left) (decodeMagnitude right) .retirement,
    Observations.buildFirst_route (modelOfComparison comparison) xs (decodeMagnitude left) (decodeMagnitude right) .sameBlockDecision,
    Observations.buildFirst_route (modelOfComparison comparison) xs (decodeMagnitude left) (decodeMagnitude right) .crossBlockDecision,
    Observations.buildFirst_route (modelOfComparison comparison) xs (decodeMagnitude left) (decodeMagnitude right) .interiorNonemptyDecision,
    Observations.buildFirst_route (modelOfComparison comparison) xs (decodeMagnitude left) (decodeMagnitude right) .interiorEmptyDecision,
    Observations.buildFirst_route (modelOfComparison comparison) xs (decodeMagnitude left) (decodeMagnitude right) .interiorReadMarker,
    Observations.buildFirst_route (modelOfComparison comparison) xs (decodeMagnitude left) (decodeMagnitude right) .crossingSecondLoad⟩

end FirstObservations

section QueryObservations

variable (comparison : Bool) (xs : List Int) (left right : ByteArray)
  (owner : Owner) (answer : Nat) (ready : ExpectedReady xs owner)
  (halted : owner.status = .halted answer)
  (hl : decodeMagnitude left < 2 ^ wordWidth xs.length)
  (hr : decodeMagnitude right < 2 ^ wordWidth xs.length)

include ready halted hl hr

theorem checkO05_querySteps :
    nativeObservationCounter (nativeQueryObserved comparison left right owner).2 15 = (Reusable.queryRun (modelOfComparison comparison) (decodeMagnitude left) (decodeMagnitude right) owner.toState).steps :=
  (Observations.query_model_observations (modelOfComparison comparison) xs (decodeMagnitude left) (decodeMagnitude right)
    answer owner ready halted hl hr).1

theorem checkO06_queryCategories :
    nativeObservationCounter (nativeQueryObserved comparison left right owner).2 0 =
      (Reusable.queryRun (modelOfComparison comparison) (decodeMagnitude left) (decodeMagnitude right) owner.toState).categoryCount (.old .read) ∧
    nativeObservationCounter (nativeQueryObserved comparison left right owner).2 1 =
      (Reusable.queryRun (modelOfComparison comparison) (decodeMagnitude left) (decodeMagnitude right) owner.toState).categoryCount (.old .register) ∧
    nativeObservationCounter (nativeQueryObserved comparison left right owner).2 2 =
      (Reusable.queryRun (modelOfComparison comparison) (decodeMagnitude left) (decodeMagnitude right) owner.toState).categoryCount (.old .arithmetic) ∧
    nativeObservationCounter (nativeQueryObserved comparison left right owner).2 3 =
      (Reusable.queryRun (modelOfComparison comparison) (decodeMagnitude left) (decodeMagnitude right) owner.toState).categoryCount (.old .comparison) ∧
    nativeObservationCounter (nativeQueryObserved comparison left right owner).2 4 =
      (Reusable.queryRun (modelOfComparison comparison) (decodeMagnitude left) (decodeMagnitude right) owner.toState).categoryCount (.old .branch) ∧
    nativeObservationCounter (nativeQueryObserved comparison left right owner).2 5 =
      (Reusable.queryRun (modelOfComparison comparison) (decodeMagnitude left) (decodeMagnitude right) owner.toState).categoryCount (.old .control) ∧
    nativeObservationCounter (nativeQueryObserved comparison left right owner).2 6 =
      (Reusable.queryRun (modelOfComparison comparison) (decodeMagnitude left) (decodeMagnitude right) owner.toState).categoryCount (.old .write) ∧
    nativeObservationCounter (nativeQueryObserved comparison left right owner).2 7 =
      (Reusable.queryRun (modelOfComparison comparison) (decodeMagnitude left) (decodeMagnitude right) owner.toState).categoryCount (.old .allocation) ∧
    nativeObservationCounter (nativeQueryObserved comparison left right owner).2 8 =
      (Reusable.queryRun (modelOfComparison comparison) (decodeMagnitude left) (decodeMagnitude right) owner.toState).categoryCount (.old .keyRead) ∧
    nativeObservationCounter (nativeQueryObserved comparison left right owner).2 9 =
      (Reusable.queryRun (modelOfComparison comparison) (decodeMagnitude left) (decodeMagnitude right) owner.toState).categoryCount (.old .oracleComparison) ∧
    nativeObservationCounter (nativeQueryObserved comparison left right owner).2 10 =
      (Reusable.queryRun (modelOfComparison comparison) (decodeMagnitude left) (decodeMagnitude right) owner.toState).categoryCount (.numericRelease) ∧
    nativeObservationCounter (nativeQueryObserved comparison left right owner).2 11 =
      (Reusable.queryRun (modelOfComparison comparison) (decodeMagnitude left) (decodeMagnitude right) owner.toState).categoryCount (.keyRelease) ∧
    nativeObservationCounter (nativeQueryObserved comparison left right owner).2 12 =
      (Reusable.queryRun (modelOfComparison comparison) (decodeMagnitude left) (decodeMagnitude right) owner.toState).categoryCount (.keyRegisterRelease) ∧
    nativeObservationCounter (nativeQueryObserved comparison left right owner).2 13 =
      (Reusable.queryRun (modelOfComparison comparison) (decodeMagnitude left) (decodeMagnitude right) owner.toState).categoryCount (.requestAdmission) ∧
    nativeObservationCounter (nativeQueryObserved comparison left right owner).2 14 =
      (Reusable.queryRun (modelOfComparison comparison) (decodeMagnitude left) (decodeMagnitude right) owner.toState).categoryCount (.controlEntry) := by
  have h := (Observations.query_model_observations (modelOfComparison comparison) xs (decodeMagnitude left) (decodeMagnitude right)
    answer owner ready halted hl hr).2.1
  exact ⟨h (.old .read),
    h (.old .register),
    h (.old .arithmetic),
    h (.old .comparison),
    h (.old .branch),
    h (.old .control),
    h (.old .write),
    h (.old .allocation),
    h (.old .keyRead),
    h (.old .oracleComparison),
    h (.numericRelease),
    h (.keyRelease),
    h (.keyRegisterRelease),
    h (.requestAdmission),
    h (.controlEntry)⟩

theorem checkO07_queryOrderedReads :
    nativeObservationReads (nativeQueryObserved comparison left right owner).2 = (Reusable.queryRun (modelOfComparison comparison) (decodeMagnitude left) (decodeMagnitude right) owner.toState).reads.toArray :=
  congrArg List.toArray
    (Observations.query_model_observations (modelOfComparison comparison) xs (decodeMagnitude left) (decodeMagnitude right)
      answer owner ready halted hl hr).2.2

omit ready halted hl hr in
theorem checkO08_queryRoutes :
    nativeObservationRoute (nativeQueryObserved comparison left right owner).2 0 =
      (Executable.queryArray (modelOfComparison comparison) (decodeMagnitude left) (decodeMagnitude right) owner).transitions.countP
        (Observations.routeMarked .compactQuery) ∧
    nativeObservationRoute (nativeQueryObserved comparison left right owner).2 1 =
      (Executable.queryArray (modelOfComparison comparison) (decodeMagnitude left) (decodeMagnitude right) owner).transitions.countP
        (Observations.routeMarked .servicePrepare) ∧
    nativeObservationRoute (nativeQueryObserved comparison left right owner).2 2 =
      (Executable.queryArray (modelOfComparison comparison) (decodeMagnitude left) (decodeMagnitude right) owner).transitions.countP
        (Observations.routeMarked .serviceSetup) ∧
    nativeObservationRoute (nativeQueryObserved comparison left right owner).2 3 =
      (Executable.queryArray (modelOfComparison comparison) (decodeMagnitude left) (decodeMagnitude right) owner).transitions.countP
        (Observations.routeMarked .builder) ∧
    nativeObservationRoute (nativeQueryObserved comparison left right owner).2 4 =
      (Executable.queryArray (modelOfComparison comparison) (decodeMagnitude left) (decodeMagnitude right) owner).transitions.countP
        (Observations.routeMarked .descriptor) ∧
    nativeObservationRoute (nativeQueryObserved comparison left right owner).2 5 =
      (Executable.queryArray (modelOfComparison comparison) (decodeMagnitude left) (decodeMagnitude right) owner).transitions.countP
        (Observations.routeMarked .finalizer) ∧
    nativeObservationRoute (nativeQueryObserved comparison left right owner).2 6 =
      (Executable.queryArray (modelOfComparison comparison) (decodeMagnitude left) (decodeMagnitude right) owner).transitions.countP
        (Observations.routeMarked .retirement) ∧
    nativeObservationRoute (nativeQueryObserved comparison left right owner).2 7 =
      (Executable.queryArray (modelOfComparison comparison) (decodeMagnitude left) (decodeMagnitude right) owner).transitions.countP
        (Observations.routeMarked .sameBlockDecision) ∧
    nativeObservationRoute (nativeQueryObserved comparison left right owner).2 8 =
      (Executable.queryArray (modelOfComparison comparison) (decodeMagnitude left) (decodeMagnitude right) owner).transitions.countP
        (Observations.routeMarked .crossBlockDecision) ∧
    nativeObservationRoute (nativeQueryObserved comparison left right owner).2 9 =
      (Executable.queryArray (modelOfComparison comparison) (decodeMagnitude left) (decodeMagnitude right) owner).transitions.countP
        (Observations.routeMarked .interiorNonemptyDecision) ∧
    nativeObservationRoute (nativeQueryObserved comparison left right owner).2 10 =
      (Executable.queryArray (modelOfComparison comparison) (decodeMagnitude left) (decodeMagnitude right) owner).transitions.countP
        (Observations.routeMarked .interiorEmptyDecision) ∧
    nativeObservationRoute (nativeQueryObserved comparison left right owner).2 11 =
      (Executable.queryArray (modelOfComparison comparison) (decodeMagnitude left) (decodeMagnitude right) owner).transitions.countP
        (Observations.routeMarked .interiorReadMarker) ∧
    nativeObservationRoute (nativeQueryObserved comparison left right owner).2 12 =
      (Executable.queryArray (modelOfComparison comparison) (decodeMagnitude left) (decodeMagnitude right) owner).transitions.countP
        (Observations.routeMarked .crossingSecondLoad) :=
  ⟨Observations.query_route (modelOfComparison comparison) (decodeMagnitude left) (decodeMagnitude right) owner .compactQuery,
    Observations.query_route (modelOfComparison comparison) (decodeMagnitude left) (decodeMagnitude right) owner .servicePrepare,
    Observations.query_route (modelOfComparison comparison) (decodeMagnitude left) (decodeMagnitude right) owner .serviceSetup,
    Observations.query_route (modelOfComparison comparison) (decodeMagnitude left) (decodeMagnitude right) owner .builder,
    Observations.query_route (modelOfComparison comparison) (decodeMagnitude left) (decodeMagnitude right) owner .descriptor,
    Observations.query_route (modelOfComparison comparison) (decodeMagnitude left) (decodeMagnitude right) owner .finalizer,
    Observations.query_route (modelOfComparison comparison) (decodeMagnitude left) (decodeMagnitude right) owner .retirement,
    Observations.query_route (modelOfComparison comparison) (decodeMagnitude left) (decodeMagnitude right) owner .sameBlockDecision,
    Observations.query_route (modelOfComparison comparison) (decodeMagnitude left) (decodeMagnitude right) owner .crossBlockDecision,
    Observations.query_route (modelOfComparison comparison) (decodeMagnitude left) (decodeMagnitude right) owner .interiorNonemptyDecision,
    Observations.query_route (modelOfComparison comparison) (decodeMagnitude left) (decodeMagnitude right) owner .interiorEmptyDecision,
    Observations.query_route (modelOfComparison comparison) (decodeMagnitude left) (decodeMagnitude right) owner .interiorReadMarker,
    Observations.query_route (modelOfComparison comparison) (decodeMagnitude left) (decodeMagnitude right) owner .crossingSecondLoad⟩

end QueryObservations

/-- Each equal-valued read remains tied to its own transition position and
producing prestate in the actual array execution. -/
theorem checkO09_readPosition {program : Array Instruction} {fuel : Nat} {owner : Owner}
    {index : Nat} {t : ArrayTransition} {reply : Nat × Option Nat}
    (occurs : (runArray program fuel owner).transitions[index]? = some t)
    (read : t.read? = some reply) :
    (Observations.run program fuel owner).2.reads =
      ((runArray program fuel owner).transitions.take index).filterMap ArrayTransition.read? ++
        reply :: ((runArray program fuel owner).transitions.drop (index + 1)).filterMap
          ArrayTransition.read? ∧
    t.before = runOwner program index owner ∧ stepArray program t.before = some t :=
  Observations.read_occurrence_output occurs read

/-- This position includes the four boundary events. Its producing prestate is
the actual service prestate, not a restarted run or a deduplicated read value. -/
theorem checkO10_queryReadPosition (model : InputModel) (xs : List Int)
    (left right answer : Nat) (owner : Owner) (ready : ExpectedReady xs owner)
    (halted : owner.status = .halted answer)
    (hl : left < 2 ^ wordWidth xs.length) (hr : right < 2 ^ wordWidth xs.length)
    (index : Nat) (t : ArrayTransition) (address : Nat) (reply : Option Nat)
    (occurs : (Executable.queryArray model left right owner).transitions[index]? = some t)
    (read : t.read? = some (address, reply)) :
    4 ≤ index ∧
      (Reusable.serviceRun model
        (requestProtocol Layout.serviceEntry left right owner.toState).final).transitions[index - 4]? =
          some t.toTransition ∧
      t.before.toState = (run (Layout.program model) (index - 4)
        (requestProtocol Layout.serviceEntry left right owner.toState).final).final ∧
      step (Layout.program model) t.before.toState = some t.toTransition ∧
      address < 2 ^ wordWidth xs.length ∧ reply = (PackedWordRAM.buildMemory xs)[address]? ∧
      ∃ value, reply = some value ∧ value < 2 ^ wordWidth xs.length := by
  have refinement := (Executable.query_array_refinement model xs left right answer owner
    ready.1 ready.2 halted hl hr).1
  have mapped : (Reusable.queryRun model left right owner.toState).transitions[index]? =
      some t.toTransition := by
    rw [← refinement]
    change ((Executable.queryArray model left right owner).transitions.map
      ArrayTransition.toTransition)[index]? = some t.toTransition
    simp only [List.getElem?_map, occurs, Option.map_some]
  have abstractRead : t.toTransition.read? = some (address, reply) := by
    rw [ArrayTransition.read_toTransition]
    exact read
  exact Reusable.query_read_occurrence model xs left right answer owner.toState ready.2
    halted hl hr index t.toTransition address reply mapped abstractRead

/-- Accumulation is explicitly concatenated first history plus query suffix. -/
theorem checkO11_session (model : InputModel) (xs : List Int)
    (left right nextLeft nextRight : Nat) :
    let first := Observations.buildFirst model xs left right
    Observations.queryAcc model nextLeft nextRight first.1 first.2 =
      (query model nextLeft nextRight (buildFirst model xs left right),
        ({} : Observations.Stats).fold
          ((Ownership.observations model xs left right).transitions ++
            (Executable.queryArray model nextLeft nextRight
              (buildFirst model xs left right)).transitions)) :=
  Observations.first_then_query model xs left right nextLeft nextRight

end RMQ.SuccinctFinal.PackedNative.Lifecycle.ContractChecks
