import RMQ.Core.WordRAM.Lifecycle.Service
import RMQ.Core.WordRAM.Lifecycle.Descriptor
import RMQ.Core.WordRAM.Lifecycle.Finalizer
import RMQ.Core.WordRAM.Lifecycle.Retirement

/-! # The two fixed continuous lifecycle programs

The compact service is an old-instruction prefix. The builder starts at a
nonzero fixed offset, continues through charged descriptor transfer, and then
executes scalar finalization and retirement before jumping to the service.
Neither program depends on an input, its size, or a request.
-/

namespace RMQ.SuccinctFinal.PackedLifecycle.Layout

open PackedConstruction (BInstr Operand)
open PackedConstruction.Structured (Block HostedAt)
open PackedConstruction.Proof

set_option maxRecDepth 30000

def builderBase : Nat := 221239
def descriptorBase : Nat := 223345
def finalizerBase : Nat := 223356
def retirementBase : Nat := 223370

def builderCode (model : InputModel) : List BInstr :=
  (PackedConstruction.builderSource model.source).compileAt builderBase

def oldPrefix (model : InputModel) : List BInstr :=
  Service.program.map PackedConstruction.Conservative.translate ++
    (builderCode model ++ Descriptor.coreCode model)

def retirementCode : InputModel → List Instruction
  | .word => []
  | .comparison => Retirement.code retirementBase (by decide)

def jumpBase : InputModel → Nat
  | .word => 223370
  | .comparison => 223378

def serviceEntry : Operand := ⟨212964, by decide⟩

def tail (model : InputModel) : List Instruction :=
  Finalizer.code finalizerBase (by decide) ++
    (retirementCode model ++ [.old (.jump serviceEntry)])

def program (model : InputModel) : List Instruction :=
  (oldPrefix model).map oldInstruction ++ tail model

theorem source_size (model : InputModel) :
    (PackedConstruction.builderSource model.source).size = 2106 := by
  cases model
  · exact builderSource_size_wordLeaf_eq
  · exact builderSource_size_keyLeaf_eq

theorem builderCode_length (model : InputModel) : (builderCode model).length = 2106 := by
  rw [builderCode, Block.compile_length, source_size]

theorem oldPrefix_length (model : InputModel) : (oldPrefix model).length = finalizerBase := by
  rw [oldPrefix, List.length_append, List.length_map, Service.program_length,
    List.length_append, builderCode_length, Descriptor.coreCode_length]
  rfl

theorem retirementCode_length (model : InputModel) :
    (retirementCode model).length = jumpBase model - retirementBase := by
  cases model <;> rfl

theorem tail_length (model : InputModel) : (tail model).length =
    14 + (jumpBase model - retirementBase) + 1 := by
  have h14 : (Finalizer.code finalizerBase (by decide)).length = 14 := rfl
  rw [tail, List.length_append, List.length_append, retirementCode_length]
  rw [h14]
  simp only [List.length_cons, List.length_nil]
  omega

theorem program_length (model : InputModel) : (program model).length = jumpBase model + 1 := by
  rw [program, List.length_append, List.length_map, oldPrefix_length, tail_length]
  cases model <;> rfl

theorem program_length_lt32 (model : InputModel) : (program model).length < 2^32 := by
  rw [program_length]
  cases model <;> decide

theorem service_split (model : InputModel) : program model =
    (Service.program.map PackedConstruction.Conservative.translate).map oldInstruction ++
      ((builderCode model ++ Descriptor.coreCode model).map oldInstruction ++ tail model) := by
  rw [program, oldPrefix, List.map_append, List.append_assoc]

theorem old_builder_host (model : InputModel) : HostedAt (oldPrefix model) builderBase
    ((PackedConstruction.builderSource model.source).compileAt builderBase) := by
  have hlen : (Service.program.map PackedConstruction.Conservative.translate).length =
      builderBase := by rw [List.length_map, Service.program_length]; rfl
  intro i hi
  change (Service.program.map PackedConstruction.Conservative.translate ++
    (builderCode model ++ Descriptor.coreCode model))[builderBase+i]? = _
  change i < (builderCode model).length at hi
  rw [List.getElem?_append_right (by rw [hlen]; omega), hlen, Nat.add_sub_cancel_left,
    List.getElem?_append_left hi]
  rw [builderCode]

theorem map_host {α β : Type} (f : α → β) (p : List α) (base : Nat) (fragment : List α)
    (host : ∀ i, i < fragment.length → p[base+i]? = fragment[i]?) :
    ∀ i, i < (fragment.map f).length → (p.map f)[base+i]? = (fragment.map f)[i]? := by
  intro i hi
  rw [List.getElem?_map, List.getElem?_map, host i (by simpa only [List.length_map] using hi)]

theorem append_host {α : Type} (p fragment suffix : List α) (base : Nat)
    (host : ∀ i, i < fragment.length → p[base+i]? = fragment[i]?)
    (bound : base+fragment.length ≤ p.length) :
    ∀ i, i < fragment.length → (p++suffix)[base+i]? = fragment[i]? := by
  intro i hi
  rw [List.getElem?_append_left (by omega), host i hi]

theorem descriptor_host (model : InputModel) :
    Descriptor.Hosted (program model) descriptorBase model := by
  have oldHost : HostedAt (oldPrefix model) descriptorBase (Descriptor.coreCode model) := by
    have hlen : (Service.program.map PackedConstruction.Conservative.translate).length +
        (builderCode model).length = descriptorBase := by
      rw [List.length_map, Service.program_length, builderCode_length]; rfl
    intro i hi
    change (Service.program.map PackedConstruction.Conservative.translate ++
      (builderCode model ++ Descriptor.coreCode model))[descriptorBase+i]? = _
    rw [← hlen, Nat.add_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
      List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
  have h := map_host oldInstruction _ descriptorBase _ oldHost
  rw [← Descriptor.code_eq] at h
  have hb : descriptorBase + (Descriptor.code model).length ≤
      ((oldPrefix model).map oldInstruction).length := by
    rw [List.length_map, oldPrefix_length, Descriptor.code_eq, List.length_map,
      Descriptor.coreCode_length]
    decide
  exact append_host _ _ _ _ h hb

theorem finalizer_host (model : InputModel) :
    Finalizer.Hosted (program model) finalizerBase (by decide) := by
  intro i hi
  change ((oldPrefix model).map oldInstruction ++
    (Finalizer.code finalizerBase _ ++ _))[finalizerBase+i]? = _
  have hlen : ((oldPrefix model).map oldInstruction).length = finalizerBase := by
    rw [List.length_map, oldPrefix_length]
  rw [List.getElem?_append_right (by rw [hlen]; omega), hlen, Nat.add_sub_cancel_left,
    List.getElem?_append_left (by exact hi)]

theorem retirement_host : Retirement.Hosted (program .comparison) retirementBase (by decide) := by
  intro i hi
  change ((oldPrefix .comparison).map oldInstruction ++
    (Finalizer.code finalizerBase (by decide) ++
      (Retirement.code retirementBase (by decide) ++ [.old (.jump serviceEntry)])))[retirementBase+i]? = _
  have hlen : ((oldPrefix .comparison).map oldInstruction).length = finalizerBase := by
    rw [List.length_map, oldPrefix_length]
  have h14 : (Finalizer.code finalizerBase (by decide)).length = 14 := rfl
  have hpc : retirementBase+i = finalizerBase+(14+i) := by
    change 223370+i = 223356+(14+i)
    omega
  rw [hpc, List.getElem?_append_right (by rw [hlen]; omega), hlen,
    Nat.add_sub_cancel_left, List.getElem?_append_right (by rw [h14]; omega), h14,
    Nat.add_sub_cancel_left, List.getElem?_append_left (by exact hi)]

theorem jump_fetch (model : InputModel) :
    (program model)[jumpBase model]? = some (.old (.jump serviceEntry)) := by
  have hlen : ((oldPrefix model).map oldInstruction).length = finalizerBase := by
    rw [List.length_map, oldPrefix_length]
  have h14 : (Finalizer.code finalizerBase (by decide)).length = 14 := rfl
  have hret := retirementCode_length model
  have hp : jumpBase model = finalizerBase + (14 + (retirementCode model).length) := by
    rw [hret]; cases model <;> rfl
  change ((oldPrefix model).map oldInstruction ++
    (Finalizer.code finalizerBase _ ++ (retirementCode model ++ _)))[jumpBase model]? = _
  rw [hp, List.getElem?_append_right (by rw [hlen]; omega), hlen, Nat.add_sub_cancel_left,
    List.getElem?_append_right (by rw [h14]; omega), h14, Nat.add_sub_cancel_left,
    List.getElem?_append_right (by omega), Nat.sub_self]
  rfl

end RMQ.SuccinctFinal.PackedLifecycle.Layout
