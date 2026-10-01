import RMQ.Core.WordRAM.Lifecycle.Construction
import RMQ.Core.WordRAM.Lifecycle.Retained

/-! # Actual construction continuation into retained service state

The descriptor, scalar copy/release loop, key retirement, and service jump are
composed as ordered executions of the same lifecycle program and state.
-/

namespace RMQ.SuccinctFinal.PackedLifecycle.Finalization

open PackedWordRAM (wordWidth buildMemory)
open PackedConstruction.Proof

def descriptorRun (model : InputModel) (xs : List Int) (left right : Nat)
    (producer : PackedConstruction.State) : Run :=
  run (Layout.program model) 11 (Construction.producedState model xs left right producer)

def copyRun (model : InputModel) (xs : List Int) (left right : Nat)
    (producer : PackedConstruction.State) : Run :=
  run (Layout.program model) (Finalizer.cost (producer.regs 3) (buildMemory xs).length)
    (descriptorRun model xs left right producer).final

def retirementCost : InputModel → Nat → Nat
  | .word, _ => 0
  | .comparison, n => Retirement.cost n

def retirementRun (model : InputModel) (xs : List Int) (left right : Nat)
    (producer : PackedConstruction.State) : Run :=
  run (Layout.program model) (retirementCost model xs.length)
    (copyRun model xs left right producer).final

def finalState (model : InputModel) (xs : List Int) (left right : Nat)
    (producer : PackedConstruction.State) : State :=
  execute (.old (.jump Layout.serviceEntry)) (retirementRun model xs left right producer).final

def finalTrace (model : InputModel) (xs : List Int) (left right : Nat)
    (producer : PackedConstruction.State) : List Transition :=
  (descriptorRun model xs left right producer).transitions ++
    (copyRun model xs left right producer).transitions ++
    (retirementRun model xs left right producer).transitions ++
    [⟨(retirementRun model xs left right producer).final, .instruction (.old (.jump Layout.serviceEntry)),
      finalState model xs left right producer⟩]

def continuationCost (model : InputModel) (n B M : Nat) : Nat :=
  11 + Finalizer.cost B M + retirementCost model n + 1

theorem program_fits (model : InputModel) (xs : List Int) :
    (Layout.program model).length < 2^wordWidth xs.length :=
  Nat.lt_of_lt_of_le (Layout.program_length_lt32 model)
    (Nat.pow_le_pow_right (by decide) (wordWidth_ge_32 xs.length))

theorem finalizer_continuation (model : InputModel) :
    Layout.finalizerBase+14 < (Layout.program model).length := by
  rw [Layout.program_length]
  cases model <;> decide

theorem retirement_continuation : Layout.retirementBase+8 < (Layout.program .comparison).length := by
  rw [Layout.program_length]
  decide

structure Copied (model : InputModel) (xs : List Int) (left right : Nat) (s : State) : Prop where
  memory : s.core.memory = (fun a => (buildMemory xs)[a]?)
  extent : s.core.extent = (buildMemory xs).length
  running : s.core.status = .running
  pc : s.core.pc = Layout.retirementBase
  left : s.core.regs 300 = left
  right : s.core.regs 301 = right
  size : s.core.regs 302 = xs.length
  keyExtent : s.keyExtent = if model = .comparison then xs.length else 0
  keyRegExtent : s.keyRegExtent = if model = .comparison then 2 else 0
  closed : s.Closed
  fits : s.Fits (wordWidth xs.length)
  finite : ∀ r, 400 ≤ r → s.core.regs r = 0

theorem descriptor_to_finalizer {model : InputModel} {xs : List Int} {left right : Nat}
    {abstract producer : PackedConstruction.State} {ts : List PackedConstruction.Transition}
    (built : Construction.BuildStage model xs left right abstract producer ts) :
    Finalizer.Entry Layout.finalizerBase (producer.regs 3) (buildMemory xs).length
      (descriptorRun model xs left right producer).final := by
  have delivered := (Descriptor.transfer (Layout.descriptor_host model) built.descriptor).1
  obtain ⟨hr, hpc, hB, hM, _, _, _, hm, he, _, _, _, _, _⟩ := delivered
  change (descriptorRun model xs left right producer).final.core.memory = producer.memory at hm
  have closed := (Descriptor.transfer_prefix_frame (Layout.descriptor_host model)
    built.descriptor (Nat.le_refl 11)).closed built.closed
  refine ⟨hr, ?_, he.trans built.body.extent, hB, hM, ?_, closed.1⟩
  · exact hpc
  · intro i hi
    refine ⟨(buildMemory xs).getD i 0, ?_⟩
    rw [hm]
    exact built.body.cells i hi

theorem copy_stage {model : InputModel} {xs : List Int} {left right : Nat}
    {abstract producer : PackedConstruction.State} {ts : List PackedConstruction.Transition}
    (built : Construction.BuildStage model xs left right abstract producer ts) :
    Copied model xs left right (copyRun model xs left right producer).final ∧
      (descriptorRun model xs left right producer).steps = 11 ∧
      (copyRun model xs left right producer).steps =
        Finalizer.cost (producer.regs 3) (buildMemory xs).length ∧
      Descriptor.Good (wordWidth xs.length) (Layout.program model)
        (descriptorRun model xs left right producer) ∧
      Finalizer.Good (wordWidth xs.length) (Layout.program model)
        (copyRun model xs left right producer) := by
  have entry := descriptor_to_finalizer built
  have desc := Descriptor.transfer (Layout.descriptor_host model) built.descriptor
  obtain ⟨_, _, _, _, hn, hl, hr, hm, _, _, _, hk, hkr, htail⟩ := desc.1
  change (descriptorRun model xs left right producer).final.core.memory = producer.memory at hm
  have descClosed := (Descriptor.transfer_prefix_frame (Layout.descriptor_host model)
    built.descriptor (Nat.le_refl 11)).closed built.closed
  change (descriptorRun model xs left right producer).final.Closed at descClosed
  have descSafe := Descriptor.transfer_safe (Layout.descriptor_host model) built.descriptor
    (wordWidth_ge_32 xs.length) built.fits (program_fits model xs)
  have safe := Finalizer.finalizer_safe (Layout.finalizer_host model) (wordWidth_ge_32 xs.length)
    (finalizer_continuation model) (program_fits model xs) descSafe.2.1 entry
  have output := Finalizer.finalizer (Layout.finalizer_host model) entry
  have frame := (Finalizer.finalizer_frame (Layout.finalizer_host model) entry).1
  change Finalizer.Frame (descriptorRun model xs left right producer).final
    (copyRun model xs left right producer).final at frame
  have exactMemory := Finalizer.finalizer_memory (Layout.finalizer_host model) (buildMemory xs)
    entry (by
      intro i hi
      rw [hm]
      simpa [List.getD, List.getElem?_eq_getElem hi] using built.body.cells i hi)
  have closed : (copyRun model xs left right producer).final.Closed := by
    refine ⟨output.1.2.2, ?_, ?_⟩
    · intro a ha
      rw [frame.2.2.1]
      apply descClosed.2.1 a
      rw [← frame.1]
      exact ha
    · intro r hr
      rw [frame.2.2.2.1]
      apply descClosed.2.2 r
      rw [← frame.2.1]
      exact hr
  refine ⟨⟨exactMemory.1, exactMemory.2.1, exactMemory.2.2.1, exactMemory.2.2.2,
    (frame.2.2.2.2.2 300 (by decide)).trans hl,
    (frame.2.2.2.2.2 301 (by decide)).trans hr,
    (frame.2.2.2.2.2 302 (by decide)).trans hn,
    frame.1.trans hk, frame.2.1.trans hkr, closed, safe.2.1, ?_⟩,
    desc.2, output.2.2.2, descSafe.1, safe.1⟩
  intro r h400
  exact ((frame.2.2.2.2.2 r (by omega)).trans (htail r h400)).trans (built.numericFinite r h400)

structure Retired (model : InputModel) (xs : List Int) (left right : Nat) (s : State) : Prop where
  data : Retained.Data (buildMemory xs) s
  running : s.core.status = .running
  pc : s.core.pc = Layout.jumpBase model
  left : s.core.regs 300 = left
  right : s.core.regs 301 = right
  fits : s.Fits (wordWidth xs.length)
  finite : ∀ r, 400 ≤ r → s.core.regs r = 0

theorem retire_copied {model : InputModel} {xs : List Int} {left right : Nat} {s : State}
    (copied : Copied model xs left right s) :
    Retired model xs left right (run (Layout.program model) (retirementCost model xs.length) s).final ∧
      (run (Layout.program model) (retirementCost model xs.length) s).steps = retirementCost model xs.length ∧
      Retirement.Good (wordWidth xs.length) (Layout.program model)
        (run (Layout.program model) (retirementCost model xs.length) s) := by
  cases model with
  | word =>
      have empty := empty_keys_of_closed s copied.closed copied.keyExtent copied.keyRegExtent
      exact ⟨⟨⟨copied.memory, copied.extent, empty.1, empty.2, copied.keyExtent, copied.keyRegExtent⟩,
        copied.running, copied.pc, copied.left, copied.right, copied.fits, copied.finite⟩,
        rfl, by simp [Retirement.Good, retirementCost, run]⟩
  | comparison =>
      have entry : Retirement.Entry Layout.retirementBase xs.length s :=
        ⟨copied.running, copied.pc, copied.keyExtent, copied.keyRegExtent, copied.size, copied.closed⟩
      have retired := Retirement.comparison_retired Layout.retirement_host entry
      obtain ⟨_, running, pc, hk, hkr, keys, keyRegs, _, frame, steps, _⟩ := retired
      have safe := Retirement.comparison_safe Layout.retirement_host (wordWidth_ge_32 xs.length)
        retirement_continuation (program_fits .comparison xs) copied.fits entry
      refine ⟨⟨⟨frame.1.trans copied.memory, frame.2.1.trans copied.extent, keys, keyRegs, hk, hkr⟩,
        running, pc, (frame.2.2 300 (by decide) (by decide)).trans copied.left,
        (frame.2.2 301 (by decide) (by decide)).trans copied.right, safe.2.1, ?_⟩, steps, safe.1⟩
      intro r h400
      exact (frame.2.2 r (by omega) (by omega)).trans (copied.finite r h400)

theorem actual_runsTo (program : List Instruction) (fuel : Nat) (s : State) :
    RunsTo program s (run program fuel s).final (run program fuel s).transitions :=
  run_exact_steps program fuel s

theorem retired_jump {model : InputModel} {xs : List Int} {left right : Nat} {s : State}
    (retired : Retired model xs left right s) :
    let after := execute (.old (.jump Layout.serviceEntry)) s
    RunsTo (Layout.program model) s after [⟨s, .instruction (.old (.jump Layout.serviceEntry)), after⟩] ∧
      Retained.Canonical xs after ∧ Service.Inputs left right (Retained.projectQueryState after) ∧
      Transition.Safe (wordWidth xs.length) (Layout.program model).length
        ⟨s, .instruction (.old (.jump Layout.serviceEntry)), after⟩ := by
  have fetch : (Layout.program model)[s.core.pc]? = some (.old (.jump Layout.serviceEntry)) := by
    rw [retired.pc]
    exact Layout.jump_fetch model
  have safe : Instruction.Safe (wordWidth xs.length) (Layout.program model).length s
      (.old (.jump Layout.serviceEntry)) := by
    refine ⟨PackedConstruction.Prim.operandsFit_of_width _ (wordWidth_ge_32 xs.length), ?_⟩
    change Layout.serviceEntry.val < (Layout.program model).length
    rw [Layout.program_length]
    cases model <;> decide
  have fit := execute_safe_fits retired.fits safe (List.getElem?_eq_some_iff.mp fetch).1 (program_fits model xs)
  have data : Retained.Data (buildMemory xs) (execute (.old (.jump Layout.serviceEntry)) s) := by
    simpa only [Retained.Data, execute, PackedConstruction.execPrim] using retired.data
  refine ⟨RunsTo.instruction retired.running fetch, ⟨data, ?_, fit⟩, ?_,
    ⟨.old (.jump Layout.serviceEntry), rfl, safe⟩⟩
  · intro r hr
    exact retired.finite r (by omega)
  · refine ⟨?_, ?_, retired.left, retired.right, ?_⟩
    · change Retained.projectStatus s.core.status = .running
      rw [retired.running]
      rfl
    · change (212964 : Nat) = Service.entry
      exact Service.entry_eq.symm
    · intro r hr
      exact retired.finite r (by omega)

theorem completed {model : InputModel} {xs : List Int} {left right : Nat}
    {abstract producer : PackedConstruction.State} {ts : List PackedConstruction.Transition}
    (built : Construction.BuildStage model xs left right abstract producer ts) :
    RunsTo (Layout.program model) (Construction.producedState model xs left right producer)
      (finalState model xs left right producer) (finalTrace model xs left right producer) ∧
      Retained.Canonical xs (finalState model xs left right producer) ∧
      Service.Inputs left right (Retained.projectQueryState (finalState model xs left right producer)) ∧
      (finalTrace model xs left right producer).length =
        continuationCost model xs.length (producer.regs 3) (buildMemory xs).length ∧
      ∀ t ∈ finalTrace model xs left right producer,
        t.Safe (wordWidth xs.length) (Layout.program model).length := by
  obtain ⟨copied, dlen, clen, dsafe, csafe⟩ := copy_stage built
  obtain ⟨retired, rlen, rsafe⟩ := retire_copied copied
  change (retirementRun model xs left right producer).steps = retirementCost model xs.length at rlen
  obtain ⟨jump, canonical, inputs, jsafe⟩ := retired_jump retired
  have d := actual_runsTo (Layout.program model) 11
    (Construction.producedState model xs left right producer)
  have c := actual_runsTo (Layout.program model)
    (Finalizer.cost (producer.regs 3) (buildMemory xs).length)
    (descriptorRun model xs left right producer).final
  have r := actual_runsTo (Layout.program model) (retirementCost model xs.length)
    (copyRun model xs left right producer).final
  refine ⟨?_, canonical, inputs, ?_, ?_⟩
  · simpa only [finalTrace, List.append_assoc] using ((d.trans c).trans r).trans jump
  · simp only [finalTrace, List.length_append, List.length_cons, List.length_nil]
    change (descriptorRun model xs left right producer).steps +
      (copyRun model xs left right producer).steps+
      (retirementRun model xs left right producer).steps+1 = _
    rw [dlen, clen, rlen]
    simp [continuationCost, Nat.add_assoc]
  · intro t ht
    simp only [finalTrace, List.mem_append, List.mem_singleton, or_assoc] at ht
    rcases ht with ht | ht | ht | ht
    · exact dsafe t ht
    · exact csafe t ht
    · exact rsafe t ht
    · subst t
      exact jsafe

def fullTrace (model : InputModel) (xs : List Int) (left right : Nat)
    (producer : PackedConstruction.State) (ts : List PackedConstruction.Transition) : List Transition :=
  Construction.producedTrace model xs left right ts ++ finalTrace model xs left right producer

theorem full_execution {model : InputModel} {xs : List Int} {left right : Nat}
    {abstract producer : PackedConstruction.State} {ts : List PackedConstruction.Transition}
    (built : Construction.BuildStage model xs left right abstract producer ts) :
    RunsTo (Layout.program model) (initialState model xs left right Layout.builderBase)
      (finalState model xs left right producer) (fullTrace model xs left right producer ts) :=
  built.execution.trans (completed built).1

theorem full_safe {model : InputModel} {xs : List Int} {left right : Nat}
    {abstract producer : PackedConstruction.State} {ts : List PackedConstruction.Transition}
    (built : Construction.BuildStage model xs left right abstract producer ts) :
    ∀ t ∈ fullTrace model xs left right producer ts,
      t.Safe (wordWidth xs.length) (Layout.program model).length := by
  intro t ht
  rcases List.mem_append.mp ht with hbody | hcontinuation
  · exact Construction.body_trace_safe built.body t hbody
  · exact (completed built).2.2.2.2 t hcontinuation

theorem full_prefix_fits {model : InputModel} {xs : List Int} {left right fuel : Nat}
    {abstract producer : PackedConstruction.State} {ts : List PackedConstruction.Transition}
    (built : Construction.BuildStage model xs left right abstract producer ts)
    (domain : InputDomain model xs) (hl : left < 2^wordWidth xs.length)
    (hr : right < 2^wordWidth xs.length)
    (hf : fuel ≤ (fullTrace model xs left right producer ts).length) :
    (run (Layout.program model) fuel (initialState model xs left right Layout.builderBase)).final.Fits
      (wordWidth xs.length) := by
  have initial := initial_fits model xs left right Layout.builderBase domain hl hr
    (Construction.initial_pc_fits xs)
  apply (run_fits initial (program_fits model xs) ?_).1
  intro t ht
  have member : t ∈ (run (Layout.program model) (fullTrace model xs left right producer ts).length
      (initialState model xs left right Layout.builderBase)).transitions := by
    rw [← Nat.add_sub_of_le hf, run_add]
    exact List.mem_append_left _ ht
  have whole : run (Layout.program model) (fullTrace model xs left right producer ts).length
      (initialState model xs left right Layout.builderBase) =
      ⟨finalState model xs left right producer, fullTrace model xs left right producer ts⟩ :=
    full_execution built
  rw [whole] at member
  exact full_safe built t member

def ArenaFrame (s t : State) : Prop :=
  t.core.extent ≤ s.core.extent ∧ ∀ r, 400 ≤ r → t.core.regs r = s.core.regs r

theorem ArenaFrame.refl (s : State) : ArenaFrame s s := ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem ArenaFrame.trans {s t u : State} (a : ArenaFrame s t) (b : ArenaFrame t u) : ArenaFrame s u :=
  ⟨Nat.le_trans b.1 a.1, fun r hr => (b.2 r hr).trans (a.2 r hr)⟩

def PrefixFrame (program : List Instruction) (s : State) (ts : List Transition) : Prop :=
  ∀ fuel, fuel ≤ ts.length → ArenaFrame s (run program fuel s).final

theorem prefixFrame_append {program : List Instruction} {s middle : State}
    {first second : List Transition} (execution : RunsTo program s middle first)
    (hfirst : PrefixFrame program s first) (hsecond : PrefixFrame program middle second) :
    PrefixFrame program s (first++second) := by
  intro fuel hf
  by_cases hp : fuel ≤ first.length
  · exact hfirst fuel hp
  · have hm : ArenaFrame s middle := by
      have h := hfirst first.length (Nat.le_refl _)
      rw [show run program first.length s = ⟨middle, first⟩ from execution] at h
      exact h
    have remain : fuel-first.length ≤ second.length := by rw [List.length_append] at hf; omega
    rw [show fuel=first.length+(fuel-first.length) by omega, run_add,
      show run program first.length s = ⟨middle, first⟩ from execution]
    exact hm.trans (hsecond _ remain)

theorem retirement_prefix_frame {model : InputModel} {xs : List Int} {left right fuel : Nat} {s : State}
    (copied : Copied model xs left right s) (hf : fuel ≤ retirementCost model xs.length) :
    ArenaFrame s (run (Layout.program model) fuel s).final := by
  cases model with
  | word =>
      have hz : fuel=0 := by change fuel ≤ 0 at hf; omega
      subst fuel
      exact ArenaFrame.refl s
  | comparison =>
      have entry : Retirement.Entry Layout.retirementBase xs.length s :=
        ⟨copied.running, copied.pc, copied.keyExtent, copied.keyRegExtent, copied.size, copied.closed⟩
      have whole := (Retirement.comparison_run Layout.retirement_host entry).2.2.2.2.2.2
      have used : Retirement.UsesCode Layout.retirementBase (by decide)
          (run (Layout.program .comparison) fuel s) := by
        intro t ht
        apply whole t
        rw [show Retirement.cost xs.length=fuel+(Retirement.cost xs.length-fuel) by
          change fuel ≤ Retirement.cost xs.length at hf; omega, run_add]
        exact List.mem_append_left _ ht
      have frame := (Retirement.run_frame_closed copied.closed used).1
      exact ⟨Nat.le_of_eq frame.2.1, fun r hr => frame.2.2 r (by omega) (by omega)⟩

theorem jump_prefix_frame {model : InputModel} {xs : List Int} {left right fuel : Nat} {s : State}
    (retired : Retired model xs left right s) (hf : fuel ≤ 1) :
    ArenaFrame s (run (Layout.program model) fuel s).final := by
  by_cases hz : fuel=0
  · subst fuel
    exact ArenaFrame.refl s
  · have one : fuel=1 := by omega
    subst fuel
    have hj : run (Layout.program model) 1 s =
        ⟨execute (.old (.jump Layout.serviceEntry)) s,
          [⟨s, .instruction (.old (.jump Layout.serviceEntry)), execute (.old (.jump Layout.serviceEntry)) s⟩]⟩ :=
      (retired_jump retired).1
    rw [hj]
    exact ArenaFrame.refl s

theorem continuation_prefix_frame {model : InputModel} {xs : List Int} {left right : Nat}
    {abstract producer : PackedConstruction.State} {ts : List PackedConstruction.Transition}
    (built : Construction.BuildStage model xs left right abstract producer ts) :
    PrefixFrame (Layout.program model) (Construction.producedState model xs left right producer)
      (finalTrace model xs left right producer) := by
  obtain ⟨copied, dlen, clen, _, _⟩ := copy_stage built
  obtain ⟨retired, rlen, _⟩ := retire_copied copied
  change (retirementRun model xs left right producer).steps = retirementCost model xs.length at rlen
  have d := actual_runsTo (Layout.program model) 11
    (Construction.producedState model xs left right producer)
  have c := actual_runsTo (Layout.program model)
    (Finalizer.cost (producer.regs 3) (buildMemory xs).length)
    (descriptorRun model xs left right producer).final
  have r := actual_runsTo (Layout.program model) (retirementCost model xs.length)
    (copyRun model xs left right producer).final
  have fd : PrefixFrame (Layout.program model) (Construction.producedState model xs left right producer)
      (descriptorRun model xs left right producer).transitions := by
    intro fuel hf
    change fuel ≤ (descriptorRun model xs left right producer).steps at hf
    rw [dlen] at hf
    have frame := Descriptor.transfer_prefix_frame (Layout.descriptor_host model) built.descriptor hf
    exact ⟨Nat.le_of_eq frame.2.1, frame.2.2.2.2.2.2⟩
  have fc : PrefixFrame (Layout.program model) (descriptorRun model xs left right producer).final
      (copyRun model xs left right producer).transitions := by
    intro fuel hf
    change fuel ≤ (copyRun model xs left right producer).steps at hf
    rw [clen] at hf
    have frame := (Finalizer.finalizer_frame (Layout.finalizer_host model)
      (descriptor_to_finalizer built)).2 fuel hf
    exact ⟨frame.2.2.2.2.1, fun r hr => frame.2.2.2.2.2 r (by omega)⟩
  have fr : PrefixFrame (Layout.program model) (copyRun model xs left right producer).final
      (retirementRun model xs left right producer).transitions := by
    intro fuel hf
    change fuel ≤ (retirementRun model xs left right producer).steps at hf
    rw [rlen] at hf
    exact retirement_prefix_frame copied hf
  have fj : PrefixFrame (Layout.program model) (retirementRun model xs left right producer).final
      [⟨(retirementRun model xs left right producer).final, .instruction (.old (.jump Layout.serviceEntry)),
        finalState model xs left right producer⟩] := by
    intro fuel hf
    exact jump_prefix_frame retired hf
  exact prefixFrame_append ((d.trans c).trans r)
    (prefixFrame_append (d.trans c) (prefixFrame_append d fd fc) fr) fj

theorem full_prefix_resources {model : InputModel} {xs : List Int} {left right fuel : Nat}
    {abstract producer : PackedConstruction.State} {ts : List PackedConstruction.Transition}
    (built : Construction.BuildStage model xs left right abstract producer ts)
    (hf : fuel ≤ (fullTrace model xs left right producer ts).length) :
    (run (Layout.program model) fuel (initialState model xs left right Layout.builderBase)).final.core.extent
      ≤ producer.extent ∧
    ∀ r, 400 ≤ r →
      (run (Layout.program model) fuel (initialState model xs left right Layout.builderBase)).final.core.regs r = 0 := by
  have bodyLength : (Construction.producedTrace model xs left right ts).length = ts.length := by
    simp [Construction.producedTrace]
  by_cases short : fuel ≤ ts.length
  · exact ⟨(Construction.body_peak built.body short).1,
      Construction.body_prefix_numeric_finite built.body short⟩
  · have remain : fuel-ts.length ≤ (finalTrace model xs left right producer).length := by
      rw [fullTrace, List.length_append, bodyLength] at hf
      omega
    have whole : run (Layout.program model) ts.length (initialState model xs left right Layout.builderBase) =
        ⟨Construction.producedState model xs left right producer, Construction.producedTrace model xs left right ts⟩ := by
      have h := built.execution
      unfold RunsTo at h
      rw [bodyLength] at h
      exact h
    rw [show fuel=ts.length+(fuel-ts.length) by omega, run_add, whole]
    have frame := continuation_prefix_frame built (fuel-ts.length) remain
    exact ⟨frame.1, fun r hr => (frame.2 r hr).trans (built.numericFinite r hr)⟩

theorem full_prefix_peak {model : InputModel} {xs : List Int} {left right fuel : Nat}
    {abstract producer : PackedConstruction.State} {ts : List PackedConstruction.Transition}
    (built : Construction.BuildStage model xs left right abstract producer ts)
    (hf : fuel ≤ (fullTrace model xs left right producer ts).length) :
    (run (Layout.program model) fuel (initialState model xs left right Layout.builderBase)).final.core.extent
      ≤ 5000000*(xs.length+1) := by
  have peak := (full_prefix_resources built hf).1
  have base := built.body.baseUpper
  have extent := built.body.extent
  have memory := PackedConstruction.Spec.buildMemory_length_le xs
  have inputBound : (initialState model xs left right Layout.builderBase).core.extent ≤ xs.length+3 := by
    cases model <;> simp [initialState, inputCore, PackedConstruction.wordInputState,
      PackedConstruction.comparisonInputState, PackedConstruction.inputCellCount] <;> omega
  omega

theorem full_prefix_finite {model : InputModel} {xs : List Int} {left right fuel : Nat}
    {abstract producer : PackedConstruction.State} {ts : List PackedConstruction.Transition}
    (built : Construction.BuildStage model xs left right abstract producer ts)
    (hf : fuel ≤ (fullTrace model xs left right producer ts).length) (r : Nat) (hr : 8273 ≤ r) :
    (run (Layout.program model) fuel (initialState model xs left right Layout.builderBase)).final.core.regs r = 0 :=
  (full_prefix_resources built hf).2 r (by omega)

theorem full_transition_resources {model : InputModel} {xs : List Int} {left right : Nat}
    {abstract producer : PackedConstruction.State} {ts : List PackedConstruction.Transition}
    (built : Construction.BuildStage model xs left right abstract producer ts)
    {t : Transition} (ht : t ∈ fullTrace model xs left right producer ts) :
    t.before.core.extent ≤ 5000000*(xs.length+1) ∧ ∀ r, 8273 ≤ r → t.before.core.regs r = 0 := by
  obtain ⟨index, occurrence⟩ := List.mem_iff_getElem?.mp ht
  have within : index ≤ (fullTrace model xs left right producer ts).length :=
    Nat.le_of_lt (List.getElem?_eq_some_iff.mp occurrence).1
  have whole : run (Layout.program model) (fullTrace model xs left right producer ts).length
      (initialState model xs left right Layout.builderBase) =
      ⟨finalState model xs left right producer, fullTrace model xs left right producer ts⟩ := full_execution built
  have actual : (run (Layout.program model) (fullTrace model xs left right producer ts).length
      (initialState model xs left right Layout.builderBase)).transitions[index]? = some t := by
    rw [whole]
    exact occurrence
  rw [(run_transition_at actual).1]
  exact ⟨full_prefix_peak built within, full_prefix_finite built within⟩

theorem exact_cost {model : InputModel} {xs : List Int} {left right : Nat}
    {abstract producer : PackedConstruction.State} {ts : List PackedConstruction.Transition}
    (built : Construction.BuildStage model xs left right abstract producer ts) :
    (fullTrace model xs left right producer ts).length = ts.length + 11 +
      Finalizer.cost (producer.regs 3) (buildMemory xs).length + retirementCost model xs.length + 1 := by
  rw [fullTrace, List.length_append, (completed built).2.2.2.1]
  simp [Construction.producedTrace, continuationCost, Nat.add_assoc]

theorem linear_cost {model : InputModel} {xs : List Int} {left right : Nat}
    {abstract producer : PackedConstruction.State} {ts : List PackedConstruction.Transition}
    (built : Construction.BuildStage model xs left right abstract producer ts) :
    (fullTrace model xs left right producer ts).length ≤ 1100000000*(xs.length+1) := by
  have work := Builder.hosted_linear_work built.body
  have base := built.body.baseUpper
  have memory := PackedConstruction.Spec.buildMemory_length_le xs
  have inputBound : (initialState model xs left right Layout.builderBase).core.extent ≤ xs.length+3 := by
    cases model <;> simp [initialState, inputCore, PackedConstruction.wordInputState,
      PackedConstruction.comparisonInputState, PackedConstruction.inputCellCount] <;> omega
  have retireBound : retirementCost model xs.length ≤ 4*xs.length+5 := by
    cases model <;> simp [retirementCost, Retirement.cost]
  rw [exact_cost built, Finalizer.cost]
  omega

/-- The endpoint is generated by the complete actual trace and satisfies the
retained-data and service-entry predicates without a supplied answer premise. -/
theorem construction_complete (model : InputModel) (xs : List Int) (left right : Nat)
    (domain : InputDomain model xs) (hl : left < 2^wordWidth xs.length)
    (hr : right < 2^wordWidth xs.length) :
    ∃ final ts, RunsTo (Layout.program model)
      (initialState model xs left right Layout.builderBase) final ts ∧
      Retained.Canonical xs final ∧ Service.Inputs left right (Retained.projectQueryState final) ∧
      ts.length ≤ 1100000000*(xs.length+1) := by
  obtain ⟨abstract, producer, ts, built⟩ := Construction.build_stage model xs left right domain hl hr
  exact ⟨finalState model xs left right producer, fullTrace model xs left right producer ts,
    full_execution built, (completed built).2.1, (completed built).2.2.1, linear_cost built⟩

end RMQ.SuccinctFinal.PackedLifecycle.Finalization
