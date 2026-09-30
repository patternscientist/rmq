import RMQ.Core.WordRAM.Lifecycle.Program

/-! # Supplied arena to live canonical builder output

The original builder executes inside the fixed lifecycle program. Its input
assumptions are discharged from the supplied arena, including its two request
cells. Its actual output state provides the charged descriptor's entry facts.
-/

namespace RMQ.SuccinctFinal.PackedLifecycle.Construction

open PackedConstruction.Proof
open PackedWordRAM (wordWidth buildMemory)

def suppliedInput (model : InputModel) (xs : List Int) : PackedConstruction.State → Prop :=
  match model with
  | .word => WordInput (wordWidth xs.length) xs
  | .comparison => OracleInput xs

theorem supplied_spec (model : InputModel) (xs : List Int) :
    KeySpec (wordWidth xs.length) xs (suppliedInput model xs) model.source := by
  cases model
  · exact wordLeaf_spec (wordWidth_ge_32 xs.length) xs
  · exact keyLeaf_spec (wordWidth_ge_32 xs.length) xs

theorem source_bank (model : InputModel) :
    (PackedConstruction.builderBody model.source).RegsBelow 400 := by
  cases model
  · exact rb_builderBody_word
  · exact rb_builderBody_key

theorem initial_supplied (model : InputModel) (xs : List Int) (left right : Nat)
    (domain : InputDomain model xs) :
    suppliedInput model xs (initialState model xs left right Layout.builderBase).core := by
  cases model <;> exact initial_input _ xs left right Layout.builderBase domain

theorem supplied_below (model : InputModel) (xs : List Int) (left right : Nat) :
    InpBelow (suppliedInput model xs)
      (initialState model xs left right Layout.builderBase).core.extent := by
  cases model
  · apply wordInput_below
    change xs.length+1 ≤ (xs.length+1)+2
    omega
  · exact oracleInput_below xs _

theorem initial_regs_zero (model : InputModel) (xs : List Int) (left right entry r : Nat) :
    (initialState model xs left right entry).core.regs r = 0 := by cases model <;> rfl

theorem source_bound (model : InputModel) :
    Layout.builderBase+(PackedConstruction.builderSource model.source).size < 2^32 := by
  rw [Layout.source_size]
  decide

theorem source_inside (model : InputModel) :
    Layout.builderBase+(PackedConstruction.builderSource model.source).size <
      (Layout.oldPrefix model).length := by
  rw [Layout.source_size, Layout.oldPrefix_length]
  decide

theorem initial_pc_fits (xs : List Int) : Layout.builderBase < 2^wordWidth xs.length := by
  have hp : 2^32 ≤ 2^wordWidth xs.length :=
    Nat.pow_le_pow_right (by decide) (wordWidth_ge_32 xs.length)
  have small : Layout.builderBase < 2^32 := by decide
  omega

theorem old_program_fits (model : InputModel) (xs : List Int) :
    (Layout.oldPrefix model).length < 2^wordWidth xs.length := by
  have hp : 2^32 ≤ 2^wordWidth xs.length :=
    Nat.pow_le_pow_right (by decide) (wordWidth_ge_32 xs.length)
  rw [Layout.oldPrefix_length]
  have small : Layout.finalizerBase < 2^32 := by decide
  omega

abbrev Body (model : InputModel) (xs : List Int) (left right : Nat)
    (abstract final : PackedConstruction.State) (ts : List PackedConstruction.Transition) :=
  Builder.HostedBody (wordWidth xs.length) (Layout.oldPrefix model) Layout.builderBase
    model.source xs (initialState model xs left right Layout.builderBase).core abstract final ts

theorem body_exists (model : InputModel) (xs : List Int) (left right : Nat)
    (domain : InputDomain model xs) (hl : left < 2^wordWidth xs.length)
    (hr : right < 2^wordWidth xs.length) :
    ∃ abstract final ts, Body model xs left right abstract final ts := by
  let s := initialState model xs left right Layout.builderBase
  have fit := initial_fits model xs left right Layout.builderBase domain hl hr (initial_pc_fits xs)
  exact Builder.hosted_body (wordWidth_ge_32 xs.length) xs (suppliedInput model xs)
    model.source (supplied_spec model xs) (source_bank model)
    (Layout.oldPrefix model) Layout.builderBase s.core rfl
    (by cases model <;> rfl)
    (initial_regs_zero model xs left right Layout.builderBase)
    (by change 0 < (inputCore model xs).extent+2; omega)
    (initial_header model xs left right Layout.builderBase)
    (initial_supplied model xs left right domain) (supplied_below model xs left right)
    (bankcap_wordWidth xs.length) (initial_capacity model xs left right Layout.builderBase)
    (Nat.le_refl _) (Layout.old_builder_host model) (source_bound model) (source_inside model)
    (old_program_fits model xs) fit.1 (initial_clean model xs left right Layout.builderBase).1

def producedState (model : InputModel) (xs : List Int) (left right : Nat)
    (final : PackedConstruction.State) : State :=
  let initial := initialState model xs left right Layout.builderBase
  ofCore final initial.keyExtent initial.keyRegExtent

def producedTrace (model : InputModel) (xs : List Int) (left right : Nat)
    (ts : List PackedConstruction.Transition) : List Transition :=
  let initial := initialState model xs left right Layout.builderBase
  ts.map (oldTransition initial.keyExtent initial.keyRegExtent)

theorem body_execution {model : InputModel} {xs : List Int} {left right : Nat}
    {abstract final : PackedConstruction.State} {ts : List PackedConstruction.Transition}
    (body : Body model xs left right abstract final ts) :
    RunsTo (Layout.program model) (initialState model xs left right Layout.builderBase)
      (producedState model xs left right final) (producedTrace model xs left right ts) :=
  lift_old_prefix body.execution (Layout.tail model) _ _

theorem primitive_safe_mono {W small large : Nat} {s : PackedConstruction.State}
    {p : PackedConstruction.Prim} (safe : p.Safe W small s) (hle : small ≤ large) :
    p.Safe W large s := by
  refine ⟨safe.1, ?_⟩
  have h := safe.2
  cases p <;> simp only [PackedConstruction.Prim.SafeAt] at h ⊢ <;> try exact h
  all_goals exact Nat.lt_of_lt_of_le h hle

theorem body_trace_safe {model : InputModel} {xs : List Int} {left right : Nat}
    {abstract final : PackedConstruction.State} {ts : List PackedConstruction.Transition}
    (body : Body model xs left right abstract final ts) :
    ∀ t ∈ producedTrace model xs left right ts,
      t.Safe (wordWidth xs.length) (Layout.program model).length := by
  have hlen : (Layout.oldPrefix model).length ≤ (Layout.program model).length := by
    rw [Layout.oldPrefix_length, Layout.program_length]
    cases model <;> decide
  intro u hu
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hu
  refine ⟨oldInstruction t.instruction, rfl, ?_⟩
  exact primitive_safe_mono (body.safe t ht).1 hlen

theorem body_closed {model : InputModel} {xs : List Int} {left right : Nat}
    {abstract final : PackedConstruction.State} {ts : List PackedConstruction.Transition}
    (body : Body model xs left right abstract final ts) :
    (producedState model xs left right final).Closed := by
  have initial := initial_clean model xs left right Layout.builderBase
  refine ⟨body.cleanTail, ?_, ?_⟩
  · intro a ha
    change final.keys a = none
    rw [body.keys]
    exact initial.2.1 a ha
  · intro r hr
    change final.keyRegs r = 0
    cases model with
    | word =>
        rw [Builder.hosted_word_key_frame body]
        exact initial.2.2 r hr
    | comparison =>
        rw [Builder.hosted_comparison_key_frame body r (by exact hr)]
        exact initial.2.2 r hr

theorem body_fits {model : InputModel} {xs : List Int} {left right : Nat}
    {abstract final : PackedConstruction.State} {ts : List PackedConstruction.Transition}
    (body : Body model xs left right abstract final ts)
    (domain : InputDomain model xs) (hl : left < 2^wordWidth xs.length)
    (hr : right < 2^wordWidth xs.length) :
    (producedState model xs left right final).Fits (wordWidth xs.length) := by
  have fit := initial_fits model xs left right Layout.builderBase domain hl hr (initial_pc_fits xs)
  exact ⟨body.fits, fit.2⟩

theorem body_numeric_finite {model : InputModel} {xs : List Int} {left right : Nat}
    {abstract final : PackedConstruction.State} {ts : List PackedConstruction.Transition}
    (body : Body model xs left right abstract final ts) (r : Nat) (hr : 400 ≤ r) :
    final.regs r = 0 :=
  (body.numericFrame r hr).trans (initial_regs_zero model xs left right Layout.builderBase r)

theorem body_prefix_length {model : InputModel} {xs : List Int} {left right fuel : Nat}
    {abstract final : PackedConstruction.State} {ts : List PackedConstruction.Transition}
    (body : Body model xs left right abstract final ts) (hf : fuel ≤ ts.length) :
    (PackedConstruction.run (Layout.oldPrefix model) fuel
      (initialState model xs left right Layout.builderBase).core).transitions.length = fuel := by
  let initial := (initialState model xs left right Layout.builderBase).core
  have completed : PackedConstruction.run (Layout.oldPrefix model) ts.length initial =
      ⟨final, ts⟩ := body.execution
  have split := PackedConstruction.run_add (Layout.oldPrefix model) fuel (ts.length-fuel) initial
  rw [Nat.add_sub_of_le hf, completed] at split
  have len := congrArg (fun r : PackedConstruction.Run => r.transitions.length) split
  dsimp only at len
  rw [List.length_append] at len
  have first := PackedConstruction.run_steps_le_fuel (Layout.oldPrefix model) fuel initial
  have rest := PackedConstruction.run_steps_le_fuel (Layout.oldPrefix model) (ts.length-fuel)
    (PackedConstruction.run (Layout.oldPrefix model) fuel initial).final
  simp only [PackedConstruction.Run.steps] at first rest
  change (PackedConstruction.run (Layout.oldPrefix model) fuel initial).transitions.length = fuel
  omega

/-- Every bounded actual prefix retains the original builder's complete
states and ordered trace, not only its endpoint value. -/
theorem body_prefix_lift {model : InputModel} {xs : List Int} {left right fuel : Nat}
    {abstract final : PackedConstruction.State} {ts : List PackedConstruction.Transition}
    (body : Body model xs left right abstract final ts) (hf : fuel ≤ ts.length) :
    run (Layout.program model) fuel (initialState model xs left right Layout.builderBase) =
      oldRun (initialState model xs left right Layout.builderBase).keyExtent
        (initialState model xs left right Layout.builderBase).keyRegExtent
        (PackedConstruction.run (Layout.oldPrefix model) fuel
          (initialState model xs left right Layout.builderBase).core) :=
  old_run_full (Layout.oldPrefix model) (Layout.tail model) fuel _ _ _ (body_prefix_length body hf)

theorem body_peak {model : InputModel} {xs : List Int} {left right fuel : Nat}
    {abstract final : PackedConstruction.State} {ts : List PackedConstruction.Transition}
    (body : Body model xs left right abstract final ts) (hf : fuel ≤ ts.length) :
    (run (Layout.program model) fuel (initialState model xs left right Layout.builderBase)).final.core.extent
      ≤ final.extent ∧
    (run (Layout.program model) fuel (initialState model xs left right Layout.builderBase)).final.core.extent
      ≤ (initialState model xs left right Layout.builderBase).core.extent +
        3200000*(xs.length+1)+(buildMemory xs).length := by
  rw [body_prefix_lift body hf]
  exact Builder.hosted_peak body fuel hf

theorem body_prefix_numeric_finite {model : InputModel} {xs : List Int} {left right fuel : Nat}
    {abstract final : PackedConstruction.State} {ts : List PackedConstruction.Transition}
    (body : Body model xs left right abstract final ts) (hf : fuel ≤ ts.length)
    (r : Nat) (hr : 400 ≤ r) :
    (run (Layout.program model) fuel (initialState model xs left right Layout.builderBase)).final.core.regs r = 0 := by
  rw [body_prefix_lift body hf]
  exact (Builder.hosted_numeric_prefix_frame body rfl (Layout.old_builder_host model)
    (source_bound model) (source_bank model) fuel hf r hr).trans
      (initial_regs_zero model xs left right Layout.builderBase r)

theorem requestBase_eq (model : InputModel) (xs : List Int) :
    Descriptor.requestBase model xs.length = (inputCore model xs).extent := by cases model <;> rfl

theorem body_descriptor {model : InputModel} {xs : List Int} {left right : Nat}
    {abstract final : PackedConstruction.State} {ts : List PackedConstruction.Transition}
    (body : Body model xs left right abstract final ts) :
    Descriptor.Entry model Layout.descriptorBase (final.regs 3) xs.length
      (buildMemory xs).length left right (producedState model xs left right final) := by
  have metadata := Builder.produced_metadata body
  have hpc : final.pc = Layout.descriptorBase := by
    rw [body.pc, Layout.source_size]
    rfl
  have req := initial_requests model xs left right Layout.builderBase
  have hb := body.baseLower
  have he := body.extent
  have before : Descriptor.requestBase model xs.length+1 <
      (initialState model xs left right Layout.builderBase).core.extent := by
    rw [requestBase_eq]
    change (inputCore model xs).extent+1 < (inputCore model xs).extent+2
    omega
  refine ⟨body.running, hpc, rfl, metadata.2.2, metadata.1, metadata.2.1, ?_, ?_, ?_⟩
  · change Descriptor.requestBase model xs.length+1 < final.extent
    omega
  · change final.memory (Descriptor.requestBase model xs.length) = some left
    rw [body.inputFrame _ (by omega), requestBase_eq]
    exact req.1
  · change final.memory (Descriptor.requestBase model xs.length+1) = some right
    rw [body.inputFrame _ before, requestBase_eq]
    exact req.2

/-- The produced state is the actual complete old run embedded in the single
lifecycle execution, and provides the next fragment's live input. -/
structure BuildStage (model : InputModel) (xs : List Int) (left right : Nat)
    (abstract final : PackedConstruction.State) (ts : List PackedConstruction.Transition) : Prop where
  body : Body model xs left right abstract final ts
  execution : RunsTo (Layout.program model) (initialState model xs left right Layout.builderBase)
    (producedState model xs left right final) (producedTrace model xs left right ts)
  closed : (producedState model xs left right final).Closed
  fits : (producedState model xs left right final).Fits (wordWidth xs.length)
  numericFinite : ∀ r, 400 ≤ r → final.regs r = 0
  descriptor : Descriptor.Entry model Layout.descriptorBase (final.regs 3) xs.length
    (buildMemory xs).length left right (producedState model xs left right final)
  work : (producedTrace model xs left right ts).length ≤ 1000000000*xs.length+1000000000

theorem build_stage (model : InputModel) (xs : List Int) (left right : Nat)
    (domain : InputDomain model xs) (hl : left < 2^wordWidth xs.length)
    (hr : right < 2^wordWidth xs.length) :
    ∃ abstract final ts, BuildStage model xs left right abstract final ts := by
  obtain ⟨abstract, final, ts, body⟩ := body_exists model xs left right domain hl hr
  exact ⟨abstract, final, ts, body, body_execution body, body_closed body,
    body_fits body domain hl hr, body_numeric_finite body, body_descriptor body,
    by simpa [producedTrace] using Builder.hosted_linear_work body⟩

end RMQ.SuccinctFinal.PackedLifecycle.Construction
