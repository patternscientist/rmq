import RMQ.Core.WordRAM.Lifecycle.Capstone

/-! # Producing occurrences in the continuous lifecycle trace

Component receipts retain their exact indices after lifting into the defined
continuous run. The output reservation and transfer share the actual producer;
metadata, request, copy and release receipts use that same construction witness.
-/

namespace RMQ.SuccinctFinal.PackedLifecycle.Provenance

open PackedWordRAM (buildMemory)
open Continuous (continuousRun)
set_option maxRecDepth 30000

def Occurrence (model : InputModel) (xs : List Int) (left right index : Nat)
    (t : Transition) : Prop :=
  (continuousRun model xs left right).transitions[index]? = some t ∧
    t.before = (run (Layout.program model) index
      (initialState model xs left right Layout.builderBase)).final ∧
    step (Layout.program model) t.before = some t

theorem occurrence_of_index {model : InputModel} {xs : List Int} {left right index : Nat}
    {t : Transition} (atIndex : (continuousRun model xs left right).transitions[index]? = some t) :
    Occurrence model xs left right index t := ⟨atIndex, run_transition_at atIndex⟩

theorem append_occurrence {α : Type} (before middle after : List α) {index : Nat} {item : α}
    (atIndex : middle[index]? = some item) :
    (before ++ middle ++ after)[before.length + index]? = some item := by
  rw [List.append_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_append_left (List.getElem?_eq_some_iff.mp atIndex).1]
  exact atIndex

theorem body_occurrence {model : InputModel} {xs : List Int} {left right : Nat}
    {abstract producer : PackedConstruction.State} {body : List PackedConstruction.Transition}
    (built : Construction.BuildStage model xs left right abstract producer body)
    {index : Nat} {t : PackedConstruction.Transition} (atIndex : body[index]? = some t) :
    Occurrence model xs left right index
      (oldTransition (initialState model xs left right Layout.builderBase).keyExtent
        (initialState model xs left right Layout.builderBase).keyRegExtent t) := by
  apply occurrence_of_index
  rw [Continuous.exact_run built]
  change (Construction.producedTrace model xs left right body ++
    Finalization.finalTrace model xs left right producer ++ _)[index]? = _
  rw [List.append_assoc, List.getElem?_append_left]
  · simp [Construction.producedTrace, List.getElem?_map, atIndex]
  · simpa [Construction.producedTrace] using (List.getElem?_eq_some_iff.mp atIndex).1

theorem descriptor_occurrence {model : InputModel} {xs : List Int} {left right : Nat}
    {abstract producer : PackedConstruction.State} {body : List PackedConstruction.Transition}
    (built : Construction.BuildStage model xs left right abstract producer body)
    {index : Nat} {t : Transition}
    (atIndex : (Finalization.descriptorRun model xs left right producer).transitions[index]? = some t) :
    Occurrence model xs left right (body.length + index) t := by
  apply occurrence_of_index
  rw [Continuous.exact_run built]
  simp only [Finalization.fullTrace, Finalization.finalTrace, List.append_assoc]
  have lifted := append_occurrence (Construction.producedTrace model xs left right body)
    (Finalization.descriptorRun model xs left right producer).transitions
    ((Finalization.copyRun model xs left right producer).transitions ++
      (Finalization.retirementRun model xs left right producer).transitions ++
      [⟨(Finalization.retirementRun model xs left right producer).final,
        .instruction (.old (.jump Layout.serviceEntry)), Finalization.finalState model xs left right producer⟩] ++
      (Reusable.serviceRun model (Finalization.finalState model xs left right producer)).transitions) atIndex
  simpa only [Construction.producedTrace, List.length_map, List.append_assoc] using lifted

theorem copy_occurrence {model : InputModel} {xs : List Int} {left right : Nat}
    {abstract producer : PackedConstruction.State} {body : List PackedConstruction.Transition}
    (built : Construction.BuildStage model xs left right abstract producer body)
    {index : Nat} {t : Transition}
    (atIndex : (Finalization.copyRun model xs left right producer).transitions[index]? = some t) :
    Occurrence model xs left right (body.length + 11 + index) t := by
  apply occurrence_of_index
  rw [Continuous.exact_run built]
  simp only [Finalization.fullTrace, Finalization.finalTrace, List.append_assoc]
  have length := (Descriptor.transfer (Layout.descriptor_host model) built.descriptor).2
  change (Finalization.descriptorRun model xs left right producer).transitions.length = 11 at length
  have lifted := append_occurrence
    (Construction.producedTrace model xs left right body ++
      (Finalization.descriptorRun model xs left right producer).transitions)
    (Finalization.copyRun model xs left right producer).transitions
    ((Finalization.retirementRun model xs left right producer).transitions ++
      [⟨(Finalization.retirementRun model xs left right producer).final,
        .instruction (.old (.jump Layout.serviceEntry)), Finalization.finalState model xs left right producer⟩] ++
      (Reusable.serviceRun model (Finalization.finalState model xs left right producer)).transitions) atIndex
  simpa only [List.length_append, Construction.producedTrace, List.length_map, length, List.append_assoc] using lifted

/-- The producer register keeps its actual reserved extent until the transfer. -/
theorem reserve_output {model : InputModel} {xs : List Int} {left right : Nat}
    {abstract producer : PackedConstruction.State} {body : List PackedConstruction.Transition}
    (built : Construction.BuildStage model xs left right abstract producer body) :
    ∃ (index : Nat) (pre : PackedConstruction.State), index < body.length ∧
      Occurrence model xs left right index
        (oldTransition (initialState model xs left right Layout.builderBase).keyExtent
          (initialState model xs left right Layout.builderBase).keyRegExtent
          ⟨pre, ⟨.reserve 3⟩, PackedConstruction.execPrim (.reserve 3) pre⟩) ∧
      producer.regs 3 = pre.extent ∧
      ∀ fuel, index + 1 ≤ fuel → fuel ≤ body.length →
        (run (Layout.program model) fuel
          (initialState model xs left right Layout.builderBase)).final.core.regs 3 = pre.extent := by
  obtain ⟨pre, before, after, first, running, fetch, rest, trace, frame, value⟩ := built.body.reservation
  have prefixRun := first.trans (PackedConstruction.RunsTo.instruction running fetch)
  have prefixExact : PackedConstruction.run (Layout.oldPrefix model) (before.length+1)
      (initialState model xs left right Layout.builderBase).core =
      ⟨PackedConstruction.execPrim (.reserve 3) pre,
        before ++ [⟨pre, ⟨.reserve 3⟩, PackedConstruction.execPrim (.reserve 3) pre⟩]⟩ := by
    simpa only [PackedConstruction.RunsTo, List.length_append, List.length_singleton] using prefixRun
  have length : body.length = before.length + 1 + after.length := by
    rw [trace, List.length_append, List.length_append, List.length_singleton]
  have atIndex : body[before.length]? =
      some ⟨pre, ⟨.reserve 3⟩, PackedConstruction.execPrim (.reserve 3) pre⟩ := by
    rw [trace, List.append_assoc, List.getElem?_append_right (Nat.le_refl _)]
    simp
  refine ⟨before.length, pre, by omega, body_occurrence built atIndex, value, ?_⟩
  intro fuel lower upper
  have remaining : fuel - (before.length+1) ≤ after.length := by omega
  have allowed : ∀ t ∈ (PackedConstruction.run (Layout.oldPrefix model) after.length
      (PackedConstruction.execPrim (.reserve 3) pre)).transitions,
      PackedConstruction.WritesOnly (fun r => r ≠ 3) t.instruction := by
    rw [show PackedConstruction.run (Layout.oldPrefix model) after.length _ = _ from rest]
    exact frame
  have stable := Builder.run_prefix_frame remaining (fun r => r ≠ 3) allowed 3 (by simp)
  rw [Construction.body_prefix_lift built.body upper]
  change (PackedConstruction.run (Layout.oldPrefix model) fuel
    (initialState model xs left right Layout.builderBase).core).final.regs 3 = pre.extent
  rw [show fuel = (before.length+1) + (fuel-(before.length+1)) by omega,
    PackedConstruction.run_add, prefixExact]
  simpa [PackedConstruction.execPrim, PackedConstruction.State.writeNext,
    PackedConstruction.State.next, PackedConstruction.put] using stable

structure ProductionReceipts (model : InputModel) (xs : List Int) (left right : Nat)
    (producer : PackedConstruction.State) (body : List PackedConstruction.Transition) : Prop where
  output : ∃ (index : Nat) (pre : PackedConstruction.State) (transfer : Transition),
    index < body.length ∧
    Occurrence model xs left right index
      (oldTransition (initialState model xs left right Layout.builderBase).keyExtent
        (initialState model xs left right Layout.builderBase).keyRegExtent
        ⟨pre, ⟨.reserve 3⟩, PackedConstruction.execPrim (.reserve 3) pre⟩) ∧
    producer.regs 3 = pre.extent ∧
    (∀ fuel, index+1 ≤ fuel → fuel ≤ body.length →
      (run (Layout.program model) fuel
        (initialState model xs left right Layout.builderBase)).final.core.regs 3 = pre.extent) ∧
    Occurrence model xs left right body.length transfer ∧
    transfer.before = Construction.producedState model xs left right producer ∧
    Descriptor.OutputReceipt transfer ∧ transfer.after.core.regs 0 = pre.extent
  metadata :
    (∃ t, Occurrence model xs left right (body.length+1) t ∧
      Descriptor.ReadReceipt 302 0 (producer.regs 3) xs.length t) ∧
    (∃ t, Occurrence model xs left right (body.length+4) t ∧
      Descriptor.ReadReceipt 2 4 (producer.regs 3+7) (buildMemory xs).length t) ∧
    (∃ t, Occurrence model xs left right (body.length+8) t ∧
      Descriptor.ReadReceipt 300 4 (Descriptor.requestBase model xs.length) left t) ∧
    (∃ t, Occurrence model xs left right (body.length+10) t ∧
      Descriptor.ReadReceipt 301 4 (Descriptor.requestBase model xs.length+1) right t)
  copy : ∀ i, i < (buildMemory xs).length → ∃ load store,
    Occurrence model xs left right (body.length+11+(4+7*i)) load ∧
    Occurrence model xs left right (body.length+11+(5+7*i)) store ∧
    Finalizer.CopyReceipt producer.memory (producer.regs 3) i load store ∧
    load.after.core.regs 5 = (buildMemory xs).getD i 0 ∧
    store.after.core.memory i = (buildMemory xs)[i]?
  releases : ∀ k, k < producer.regs 3 → ∃ t,
    Occurrence model xs left right
      (body.length+11+(5+7*(buildMemory xs).length+4*k)) t ∧
    Finalizer.ReleaseReceipt ((buildMemory xs).length+(producer.regs 3-k)-1) t

theorem production_receipts {model : InputModel} {xs : List Int} {left right : Nat}
    {abstract producer : PackedConstruction.State} {body : List PackedConstruction.Transition}
    (built : Construction.BuildStage model xs left right abstract producer body) :
    ProductionReceipts model xs left right producer body := by
  have entry := Finalization.descriptor_to_finalizer built
  have memory := (Descriptor.transfer (Layout.descriptor_host model) built.descriptor).1.2.2.2.2.2.2.2.1
  change (Finalization.descriptorRun model xs left right producer).final.core.memory = producer.memory at memory
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨index, pre, inside, reserve, value, stable⟩ := reserve_output built
    obtain ⟨transfer, position, before, receipt, output⟩ :=
      Descriptor.output_transfer_at (Layout.descriptor_host model) built.descriptor
    refine ⟨index, pre, transfer, inside, reserve, value, stable, ?_, before, receipt, output.trans value⟩
    simpa only [Nat.add_zero] using descriptor_occurrence built position
  · obtain ⟨⟨a, ha, ra⟩, ⟨b, hb, rb⟩, ⟨c, hc, rc⟩, ⟨d, hd, rd⟩⟩ :=
      Descriptor.read_occurrences (Layout.descriptor_host model) built.descriptor
    exact ⟨⟨a, descriptor_occurrence built ha, ra⟩, ⟨b, descriptor_occurrence built hb, rb⟩,
      ⟨c, descriptor_occurrence built hc, rc⟩, ⟨d, descriptor_occurrence built hd, rd⟩⟩
  · intro i hi
    obtain ⟨load, store, atLoad, atStore, receipt, _⟩ :=
      Finalizer.ordered_copy (Layout.finalizer_host model) entry i hi
    rw [memory] at receipt
    have cell := built.body.cells i hi
    have loaded : load.after.core.regs 5 = (buildMemory xs).getD i 0 :=
      Option.some.inj (receipt.2.2.2.2.2.1.trans cell)
    have stored := receipt.2.2.2.2.2.2.2.1.trans cell
    refine ⟨load, store, copy_occurrence built atLoad, copy_occurrence built atStore,
      receipt, loaded, ?_⟩
    rw [List.getElem?_eq_getElem hi]
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] using stored
  · intro k hk
    obtain ⟨t, position, receipt, _⟩ :=
      Finalizer.ordered_release (Layout.finalizer_host model) entry k hk
    exact ⟨t, copy_occurrence built position, receipt⟩

/-- The public contract supplies one actual producer shared by every receipt. -/
theorem continuous_production {model : InputModel} {xs : List Int} {left right : Nat}
    (contract : ContinuousConstructionQuery model xs left right) :
    ∃ abstract producer body,
      Construction.BuildStage model xs left right abstract producer body ∧
      ProductionReceipts model xs left right producer body := by
  obtain ⟨abstract, producer, body, built, _⟩ := contract.construction
  exact ⟨abstract, producer, body, built, production_receipts built⟩

end RMQ.SuccinctFinal.PackedLifecycle.Provenance
