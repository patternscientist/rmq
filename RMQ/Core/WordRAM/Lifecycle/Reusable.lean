import RMQ.Core.WordRAM.Lifecycle.Program
import RMQ.Core.WordRAM.Lifecycle.ServiceSafety
import RMQ.Core.WordRAM.Lifecycle.Resources

/-! # Reusable charged queries on the same retained owner

One request is admitted after a halted query. The four boundary events and
the following scalar service execution are both retained in the actual trace.
-/

namespace RMQ.SuccinctFinal.PackedLifecycle.Reusable

open PackedWordRAM.Optimization
open PackedWordRAM (buildMemory wordWidth)
set_option maxRecDepth 30000

def continuation (model : InputModel) : List Instruction :=
  (Layout.builderCode model ++ Descriptor.coreCode model).map oldInstruction ++ Layout.tail model

theorem program_host (model : InputModel) : Layout.program model =
    QuerySafetyBridge.host Service.program (continuation model) := Layout.service_split model

def serviceRun (model : InputModel) (s : State) : Run :=
  run (Layout.program model) Service.budget s

def queryRun (model : InputModel) (left right : Nat) (s : State) : Run :=
  let admission := requestProtocol Layout.serviceEntry left right s
  let service := serviceRun model admission.final
  ⟨service.final, admission.transitions ++ service.transitions⟩

def queryBudget : Nat := 160257

theorem serviceEntry_eq : Layout.serviceEntry.val = Service.entry := by
  rw [Service.entry_eq]
  rfl

theorem program_fits (model : InputModel) (n : Nat) :
    (Layout.program model).length < 2 ^ wordWidth n :=
  Nat.lt_of_lt_of_le (Layout.program_length_lt32 model)
    (Nat.pow_le_pow_right (by decide) (PackedConstruction.Proof.wordWidth_ge_32 n))

theorem entry_inside (model : InputModel) : Layout.serviceEntry.val < (Layout.program model).length := by
  rw [Layout.program_length]
  cases model <;> decide

theorem entered_after_admission (left right answer : Nat) (s : State)
    (halted : s.core.status = .halted answer) :
    ServiceSafety.Entered left right (requestProtocol Layout.serviceEntry left right s).final := by
  rw [(requestProtocol_exact Layout.serviceEntry left right answer s halted).1]
  exact ⟨rfl, serviceEntry_eq, by simp [PackedConstruction.put, requestLeftRegister, requestRightRegister],
    by simp [PackedConstruction.put, requestRightRegister]⟩

theorem service_exact (model : InputModel) (xs : List Int) (left right : Nat) (s : State)
    (canonical : Retained.Canonical xs s) (entered : ServiceSafety.Entered left right s) :
    serviceRun model s =
      ⟨QuerySafetyBridge.embedded (buildMemory xs)
          (compactQueryRun (buildMemory xs) xs.length left right).final,
        (PackedWordRAM.run (buildMemory xs) Service.program Service.budget
          (Retained.projectQueryState s)).transitions.map
            (QuerySafetyBridge.liftTransition (buildMemory xs))⟩ := by
  have actual := ServiceSafety.actual_prefix xs (continuation model) left right Service.budget s
    canonical entered (Nat.le_refl _)
  have obs := Service.observations (buildMemory xs) xs.length left right (Retained.projectQueryState s)
    (ServiceSafety.canonical_header xs) (ServiceSafety.entered_inputs xs left right s canonical entered)
  rw [← program_host model] at actual
  rw [obs.1] at actual
  exact actual

theorem service_canonical (model : InputModel) (xs : List Int) (left right : Nat) (s : State)
    (canonical : Retained.Canonical xs s) (entered : ServiceSafety.Entered left right s) :
    Retained.Canonical xs (serviceRun model s).final := by
  have h := ServiceSafety.actual_prefix_canonical xs (continuation model) left right Service.budget s
    canonical entered (Nat.le_refl _)
  rwa [← program_host model] at h

theorem service_steps (model : InputModel) (xs : List Int) (left right : Nat) (s : State)
    (canonical : Retained.Canonical xs s) (entered : ServiceSafety.Entered left right s) :
    (serviceRun model s).steps = 4 + QueryEntry.setupCost +
      (compactQueryRun (buildMemory xs) xs.length left right).steps ∧
      (serviceRun model s).steps ≤ 160253 := by
  have obs := Service.observations (buildMemory xs) xs.length left right (Retained.projectQueryState s)
    (ServiceSafety.canonical_header xs) (ServiceSafety.entered_inputs xs left right s canonical entered)
  rw [service_exact model xs left right s canonical entered]
  simpa only [Run.steps, List.length_map, PackedWordRAM.Run.steps] using
    (show (PackedWordRAM.run (buildMemory xs) Service.program Service.budget
      (Retained.projectQueryState s)).steps = 4 + QueryEntry.setupCost +
      (compactQueryRun (buildMemory xs) xs.length left right).steps ∧
      (PackedWordRAM.run (buildMemory xs) Service.program Service.budget
        (Retained.projectQueryState s)).steps ≤ 160253 from ⟨obs.2.2.2.1, obs.2.2.2.2.1⟩)

theorem service_halts (model : InputModel) (xs : List Int) (left right : Nat) (s : State)
    (canonical : Retained.Canonical xs s) (entered : ServiceSafety.Entered left right s) :
    (serviceRun model s).final.core.status = .halted
      (PackedWordRAM.optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value) := by
  rw [service_exact model xs left right s canonical entered]
  change PackedConstruction.Conservative.status
    (compactQueryRun (buildMemory xs) xs.length left right).final.status = _
  rw [compactQueryRun_halts]
  rfl

theorem service_reads (model : InputModel) (xs : List Int) (left right : Nat) (s : State)
    (canonical : Retained.Canonical xs s) (entered : ServiceSafety.Entered left right s) :
    (serviceRun model s).reads = (0, some xs.length) ::
      (compactQueryRun (buildMemory xs) xs.length left right).reads.map (fun r => (r.address, r.reply)) := by
  have h := ServiceSafety.actual_prefix_reads xs (continuation model) left right Service.budget s
    canonical entered (Nat.le_refl _)
  rw [← program_host model] at h
  rw [serviceRun, h]
  have obs := Service.observations (buildMemory xs) xs.length left right (Retained.projectQueryState s)
    (ServiceSafety.canonical_header xs) (ServiceSafety.entered_inputs xs left right s canonical entered)
  rw [obs.2.2.1]
  rfl

theorem query_correct (model : InputModel) (xs : List Int) (left right answer : Nat) (s : State)
    (canonical : Retained.Canonical xs s) (halted : s.core.status = .halted answer)
    (hl : left < 2 ^ wordWidth xs.length) (hr : right < 2 ^ wordWidth xs.length) :
    Retained.Canonical xs (queryRun model left right s).final ∧
      (queryRun model left right s).final.core.status = .halted
        (PackedWordRAM.optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value) ∧
      (queryRun model left right s).final.core.memory = s.core.memory ∧
      (queryRun model left right s).final.core.extent = s.core.extent ∧
      (queryRun model left right s).steps = 4 + 4 + QueryEntry.setupCost +
        (compactQueryRun (buildMemory xs) xs.length left right).steps ∧
      (queryRun model left right s).steps ≤ queryBudget := by
  let admitted := (requestProtocol Layout.serviceEntry left right s).final
  have width : Layout.serviceEntry.val < 2 ^ wordWidth xs.length :=
    Nat.lt_trans (entry_inside model) (program_fits model xs.length)
  have hc : Retained.Canonical xs admitted := canonical.requestProtocol Layout.serviceEntry
    left right (Layout.program model).length hl hr (entry_inside model) width
  have he : ServiceSafety.Entered left right admitted := entered_after_admission left right answer s halted
  have out := service_canonical model xs left right admitted hc he
  have stop := service_halts model xs left right admitted hc he
  have cost := service_steps model xs left right admitted hc he
  have admissionCost := (requestProtocol_exact Layout.serviceEntry left right answer s halted).2.1
  refine ⟨out, stop, out.1.1.trans canonical.1.1.symm, out.1.2.1.trans canonical.1.2.1.symm, ?_, ?_⟩
  · change ((requestProtocol Layout.serviceEntry left right s).transitions ++
      (serviceRun model admitted).transitions).length = _
    rw [List.length_append]
    change (requestProtocol Layout.serviceEntry left right s).steps +
      (serviceRun model admitted).steps = _
    rw [admissionCost, cost.1]
    omega
  · change ((requestProtocol Layout.serviceEntry left right s).transitions ++
      (serviceRun model admitted).transitions).length ≤ _
    rw [List.length_append]
    change (requestProtocol Layout.serviceEntry left right s).steps +
      (serviceRun model admitted).steps ≤ 160257
    rw [admissionCost]
    omega

theorem service_transition_canonical (model : InputModel) (xs : List Int)
    (left right : Nat) (s : State) (canonical : Retained.Canonical xs s)
    (entered : ServiceSafety.Entered left right s) :
    ∀ t ∈ (serviceRun model s).transitions,
      Retained.Canonical xs t.before ∧ Retained.Canonical xs t.after := by
  intro t member
  obtain ⟨index, occurs⟩ := List.mem_iff_getElem?.mp member
  have within : index < Service.budget := Nat.lt_of_lt_of_le
    (List.getElem?_eq_some_iff.mp occurs).1
    (Resources.run_steps_le_fuel (Layout.program model) Service.budget s)
  have before := (run_transition_at occurs).1
  have after := Resources.run_transition_after occurs
  have prefixCanonical (fuel : Nat) (bound : fuel ≤ Service.budget) :
      Retained.Canonical xs (run (Layout.program model) fuel s).final := by
    rw [program_host]
    exact ServiceSafety.actual_prefix_canonical xs (continuation model) left right fuel s
      canonical entered bound
  exact ⟨before ▸ prefixCanonical index (by omega), after ▸ prefixCanonical (index + 1) (by omega)⟩

theorem admission_transition_canonical (model : InputModel) (xs : List Int)
    (left right : Nat) (s : State) (canonical : Retained.Canonical xs s)
    (hl : left < 2 ^ wordWidth xs.length) (hr : right < 2 ^ wordWidth xs.length) :
    ∀ t ∈ (requestProtocol Layout.serviceEntry left right s).transitions,
      Retained.Canonical xs t.before ∧ Retained.Canonical xs t.after := by
  apply (Resources.runBoundary_preserves (Retained.Canonical xs)
    [.left left, .right right, .entry Layout.serviceEntry, .activate] s canonical ?_).2
  intro b member t ht
  apply ht.boundary (len := (Layout.program model).length) (entry := Layout.serviceEntry.val)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact ⟨by decide, hl⟩
  · exact ⟨by decide, hr⟩
  · exact ⟨rfl, entry_inside model, Nat.lt_trans (entry_inside model) (program_fits model xs.length)⟩
  · trivial

/-- Every event belongs to the actual charged admission or actual service run. -/
theorem query_action_safe (model : InputModel) (xs : List Int)
    (left right answer : Nat) (s : State) (canonical : Retained.Canonical xs s)
    (halted : s.core.status = .halted answer)
    (hl : left < 2 ^ wordWidth xs.length) (hr : right < 2 ^ wordWidth xs.length) :
    ∀ t ∈ (queryRun model left right s).transitions,
      t.ActionSafe (wordWidth xs.length) (Layout.program model).length 8273
        Layout.serviceEntry.val := by
  have width := Nat.lt_trans (entry_inside model) (program_fits model xs.length)
  have admission := requestProtocol_safe Layout.serviceEntry left right s hl hr
    (entry_inside model) width (by decide : 301 < 8273) canonical.2.2 canonical.closed canonical.2.1
  have hc := canonical.requestProtocol Layout.serviceEntry left right (Layout.program model).length
    hl hr (entry_inside model) width
  have he := entered_after_admission left right answer s halted
  have service := ServiceSafety.actual_prefix_safe xs (continuation model) left right Service.budget
    (requestProtocol Layout.serviceEntry left right s).final hc he (Nat.le_refl _)
  rw [← program_host model] at service
  intro t member
  change t ∈ (requestProtocol Layout.serviceEntry left right s).transitions ++
    (serviceRun model (requestProtocol Layout.serviceEntry left right s).final).transitions at member
  rcases List.mem_append.mp member with member | member
  · exact (admission.2.2.2 t member).1
  · exact instruction_action_safe (service t member)

/-- Full state invariants cover both sides of every recorded query event. -/
theorem query_transition_canonical (model : InputModel) (xs : List Int)
    (left right answer : Nat) (s : State) (canonical : Retained.Canonical xs s)
    (halted : s.core.status = .halted answer)
    (hl : left < 2 ^ wordWidth xs.length) (hr : right < 2 ^ wordWidth xs.length) :
    ∀ t ∈ (queryRun model left right s).transitions,
      Retained.Canonical xs t.before ∧ Retained.Canonical xs t.after := by
  have width := Nat.lt_trans (entry_inside model) (program_fits model xs.length)
  have hc := canonical.requestProtocol Layout.serviceEntry left right (Layout.program model).length
    hl hr (entry_inside model) width
  have he := entered_after_admission left right answer s halted
  intro t member
  change t ∈ (requestProtocol Layout.serviceEntry left right s).transitions ++
    (serviceRun model (requestProtocol Layout.serviceEntry left right s).final).transitions at member
  rcases List.mem_append.mp member with member | member
  · exact admission_transition_canonical model xs left right s canonical hl hr t member
  · exact service_transition_canonical model xs left right _ hc he t member

theorem query_transition_fits (model : InputModel) (xs : List Int)
    (left right answer : Nat) (s : State) (canonical : Retained.Canonical xs s)
    (halted : s.core.status = .halted answer)
    (hl : left < 2 ^ wordWidth xs.length) (hr : right < 2 ^ wordWidth xs.length) :
    ∀ t ∈ (queryRun model left right s).transitions,
      t.before.Fits (wordWidth xs.length) ∧ t.after.Fits (wordWidth xs.length) := by
  intro t member
  have states := query_transition_canonical model xs left right answer s canonical halted hl hr t member
  exact ⟨states.1.2.2, states.2.2.2⟩

def ResourceFrame (s t : State) : Prop :=
  t.core.memory = s.core.memory ∧ t.core.extent = s.core.extent ∧
    t.core.keys = s.core.keys ∧ t.core.keyRegs = s.core.keyRegs ∧
    t.keyExtent = s.keyExtent ∧ t.keyRegExtent = s.keyRegExtent ∧
    ∀ r, 8273 ≤ r → t.core.regs r = s.core.regs r

theorem canonical_frame {xs : List Int} {s t : State}
    (hs : Retained.Canonical xs s) (ht : Retained.Canonical xs t) : ResourceFrame s t := by
  rcases hs.1 with ⟨sm, se, sk, skr, ske, skre⟩
  rcases ht.1 with ⟨tm, te, tk, tkr, tke, tkre⟩
  exact ⟨tm.trans sm.symm, te.trans se.symm, tk.trans sk.symm, tkr.trans skr.symm,
    tke.trans ske.symm, tkre.trans skre.symm, fun r hr => (ht.2.1 r hr).trans (hs.2.1 r hr).symm⟩

theorem query_resources (model : InputModel) (xs : List Int)
    (left right answer : Nat) (s : State) (canonical : Retained.Canonical xs s)
    (halted : s.core.status = .halted answer)
    (hl : left < 2 ^ wordWidth xs.length) (hr : right < 2 ^ wordWidth xs.length) :
    ResourceFrame s (queryRun model left right s).final ∧
      ∀ t ∈ (queryRun model left right s).transitions,
        ResourceFrame s t.before ∧ ResourceFrame s t.after := by
  refine ⟨canonical_frame canonical (query_correct model xs left right answer s canonical halted hl hr).1, ?_⟩
  intro t member
  have states := query_transition_canonical model xs left right answer s canonical halted hl hr t member
  exact ⟨canonical_frame canonical states.1, canonical_frame canonical states.2⟩

/-- The header read precedes every compact-query read, including on rejection. -/
theorem query_reads (model : InputModel) (xs : List Int)
    (left right answer : Nat) (s : State) (canonical : Retained.Canonical xs s)
    (halted : s.core.status = .halted answer)
    (hl : left < 2 ^ wordWidth xs.length) (hr : right < 2 ^ wordWidth xs.length) :
    (queryRun model left right s).reads = (0, some xs.length) ::
      (compactQueryRun (buildMemory xs) xs.length left right).reads.map (fun r => (r.address, r.reply)) := by
  have width := Nat.lt_trans (entry_inside model) (program_fits model xs.length)
  have hc := canonical.requestProtocol Layout.serviceEntry left right (Layout.program model).length
    hl hr (entry_inside model) width
  have he := entered_after_admission left right answer s halted
  change ((requestProtocol Layout.serviceEntry left right s).transitions ++
    (serviceRun model (requestProtocol Layout.serviceEntry left right s).final).transitions).filterMap _ = _
  rw [List.filterMap_append]
  change (runBoundary _ s).reads ++ (serviceRun model _).reads = _
  rw [Resources.runBoundary_reads, List.nil_append, service_reads model xs left right _ hc he]

theorem query_ordered_reads (model : InputModel) (xs : List Int)
    (left right answer : Nat) (s : State) (canonical : Retained.Canonical xs s)
    (halted : s.core.status = .halted answer)
    (hl : left < 2 ^ wordWidth xs.length) (hr : right < 2 ^ wordWidth xs.length) :
    (queryRun model left right s).reads = (0, some xs.length) ::
      (if ValidRange xs left right then
        (List.range 174).map (fun i => (i, (PackedWordRAM.metadata (SuccinctClassic.cartesianShape xs))[i]?)) ++
          (PackedWordRAM.logicalTraceReads (SuccinctClassic.cartesianShape xs) (buildMemory xs)
            (SuccinctClassic.queryTraceResult xs left right).trace).map (fun r => (r.address, r.reply))
       else []) := by
  rw [query_reads model xs left right answer s canonical halted hl hr,
    (compactQueryRun_original_observations (buildMemory xs) xs.length left right).2,
    PackedWordRAM.queryRun_reference_reads]
  split <;> simp [List.map_append, List.map_map]

theorem query_reads_successful (model : InputModel) (xs : List Int)
    (left right answer : Nat) (s : State) (canonical : Retained.Canonical xs s)
    (halted : s.core.status = .halted answer)
    (hl : left < 2 ^ wordWidth xs.length) (hr : right < 2 ^ wordWidth xs.length)
    (address : Nat) (reply : Option Nat)
    (member : (address, reply) ∈ (queryRun model left right s).reads) :
    ∃ value, reply = some value := by
  rw [query_reads model xs left right answer s canonical halted hl hr] at member
  rcases List.mem_cons.mp member with first | rest
  · have eq := congrArg Prod.snd first
    exact ⟨xs.length, eq⟩
  · obtain ⟨receipt, member, eq⟩ := List.mem_map.mp rest
    rw [(compactQueryRun_original_observations (buildMemory xs) xs.length left right).2] at member
    obtain ⟨value, valueEq⟩ := PackedWordRAM.queryRun_reads_reply xs left right receipt member
    exact ⟨value, (congrArg Prod.snd eq).symm.trans valueEq⟩

/-- An observed read has its actual service position after four boundary events. -/
theorem query_read_occurrence (model : InputModel) (xs : List Int)
    (left right answer : Nat) (s : State) (canonical : Retained.Canonical xs s)
    (halted : s.core.status = .halted answer)
    (hl : left < 2 ^ wordWidth xs.length) (hr : right < 2 ^ wordWidth xs.length)
    (index : Nat) (t : Transition) (address : Nat) (reply : Option Nat)
    (occurs : (queryRun model left right s).transitions[index]? = some t)
    (read : t.read? = some (address, reply)) :
    4 ≤ index ∧
      (serviceRun model (requestProtocol Layout.serviceEntry left right s).final).transitions[index - 4]? = some t ∧
      t.before = (run (Layout.program model) (index - 4)
        (requestProtocol Layout.serviceEntry left right s).final).final ∧
      step (Layout.program model) t.before = some t ∧
      address < 2 ^ wordWidth xs.length ∧ reply = (buildMemory xs)[address]? ∧
      ∃ value, reply = some value ∧ value < 2 ^ wordWidth xs.length := by
  have admissionLength := (requestProtocol_exact Layout.serviceEntry left right answer s halted).2.1
  change (requestProtocol Layout.serviceEntry left right s).transitions.length = 4 at admissionLength
  have original := occurs
  change ((requestProtocol Layout.serviceEntry left right s).transitions ++
    (serviceRun model (requestProtocol Layout.serviceEntry left right s).final).transitions)[index]? = some t at occurs
  have afterAdmission : (requestProtocol Layout.serviceEntry left right s).transitions.length ≤ index := by
    by_cases small : (requestProtocol Layout.serviceEntry left right s).transitions.length ≤ index
    · exact small
    exfalso
    have early : index < (requestProtocol Layout.serviceEntry left right s).transitions.length := by omega
    rw [List.getElem?_append_left early] at occurs
    have impossible : (address, reply) ∈ (requestProtocol Layout.serviceEntry left right s).reads :=
      List.mem_filterMap.mpr ⟨t, List.mem_iff_getElem?.mpr ⟨index, occurs⟩, read⟩
    rw [requestProtocol, Resources.runBoundary_reads] at impossible
    cases impossible
  rw [List.getElem?_append_right afterAdmission, admissionLength] at occurs
  have actual := run_transition_at occurs
  have width := Nat.lt_trans (entry_inside model) (program_fits model xs.length)
  have hc := canonical.requestProtocol Layout.serviceEntry left right (Layout.program model).length
    hl hr (entry_inside model) width
  have he := entered_after_admission left right answer s halted
  have hostedOccurs : (run (QuerySafetyBridge.host Service.program (continuation model))
      Service.budget (requestProtocol Layout.serviceEntry left right s).final).transitions[index - 4]? = some t := by
    rwa [← program_host model]
  have backing := ServiceSafety.actual_read_width xs (continuation model) left right _ hc he
    (index - 4) t address reply hostedOccurs read
  obtain ⟨value, valueEq⟩ := query_reads_successful model xs left right answer s canonical halted hl hr
    address reply (List.mem_filterMap.mpr ⟨t, List.mem_iff_getElem?.mpr ⟨index, original⟩, read⟩)
  exact ⟨by omega, occurs, actual.1, actual.2, backing.1, backing.2.1,
    value, valueEq, backing.2.2 value valueEq⟩

theorem query_valid (model : InputModel) (xs : List Int)
    (left right answer : Nat) (s : State) (canonical : Retained.Canonical xs s)
    (halted : s.core.status = .halted answer)
    (hl : left < 2 ^ wordWidth xs.length) (hr : right < 2 ^ wordWidth xs.length)
    (valid : ValidRange xs left right) :
    (queryRun model left right s).final.core.status = .halted (scanWindow xs left (right - left) + 1) ∧
      LeftmostArgMin xs left right (scanWindow xs left (right - left)) := by
  have result := (query_correct model xs left right answer s canonical halted hl hr).2.1
  have packet := Option.some.inj ((compactQueryRun_result xs left right).symm.trans
    (compactQueryRun_scanWindow xs left right valid))
  rw [packet] at result
  exact ⟨result, compactQueryNat_leftmost xs left right _
    (by rw [compactQueryNat_exact, if_pos valid])⟩

theorem query_invalid (model : InputModel) (xs : List Int)
    (left right answer : Nat) (s : State) (canonical : Retained.Canonical xs s)
    (halted : s.core.status = .halted answer)
    (hl : left < 2 ^ wordWidth xs.length) (hr : right < 2 ^ wordWidth xs.length)
    (invalid : ¬ ValidRange xs left right) :
    (queryRun model left right s).final.core.status = .halted 0 ∧
      (queryRun model left right s).reads = [(0, some xs.length)] := by
  have result := (query_correct model xs left right answer s canonical halted hl hr).2.1
  have guard := compactQueryRun_invalid (buildMemory xs) xs.length left right invalid
  have packet := Option.some.inj ((compactQueryRun_result xs left right).symm.trans guard.1)
  rw [packet] at result
  refine ⟨result, ?_⟩
  rw [query_reads model xs left right answer s canonical halted hl hr, guard.2]
  rfl

theorem query_leftmost (model : InputModel) (xs : List Int)
    (left right answer index : Nat) (s : State) (canonical : Retained.Canonical xs s)
    (halted : s.core.status = .halted answer)
    (hl : left < 2 ^ wordWidth xs.length) (hr : right < 2 ^ wordWidth xs.length)
    (observed : (queryRun model left right s).final.core.status = .halted (index + 1)) :
    LeftmostArgMin xs left right index := by
  by_cases valid : ValidRange xs left right
  · have result := query_valid model xs left right answer s canonical halted hl hr valid
    have eq := PackedConstruction.Status.halted.inj (observed.symm.trans result.1)
    have index_eq : index = scanWindow xs left (right - left) := by omega
    exact index_eq ▸ result.2
  · have result := (query_invalid model xs left right answer s canonical halted hl hr valid).1
    have impossible := PackedConstruction.Status.halted.inj (observed.symm.trans result)
    omega

/-- This bounds every construction prefix, hence also the completed full trace.
It remains true after the first service because no instruction grows either bank. -/
theorem construction_key_peak (model : InputModel) (xs : List Int)
    (left right fuel : Nat) :
    (run (Layout.program model) fuel (initialState model xs left right Layout.builderBase)).final.keyExtent ≤
        (if model = .comparison then xs.length else 0) ∧
      (run (Layout.program model) fuel (initialState model xs left right Layout.builderBase)).final.keyRegExtent ≤
        (if model = .comparison then 2 else 0) :=
  (Resources.run_key_extents (Layout.program model) fuel
    (initialState model xs left right Layout.builderBase)).1

theorem construction_transition_key_peak (model : InputModel) (xs : List Int)
    (left right fuel : Nat) :
    ∀ t ∈ (run (Layout.program model) fuel (initialState model xs left right Layout.builderBase)).transitions,
      (t.before.keyExtent ≤ (if model = .comparison then xs.length else 0) ∧
        t.before.keyRegExtent ≤ (if model = .comparison then 2 else 0)) ∧
      (t.after.keyExtent ≤ (if model = .comparison then xs.length else 0) ∧
        t.after.keyRegExtent ≤ (if model = .comparison then 2 else 0)) :=
  (Resources.run_key_extents (Layout.program model) fuel
    (initialState model xs left right Layout.builderBase)).2

theorem construction_numeric_closed (model : InputModel) (xs : List Int)
    (left right fuel : Nat) :
    PackedConstruction.CleanTail
      (run (Layout.program model) fuel (initialState model xs left right Layout.builderBase)).final.core ∧
      ∀ t ∈ (run (Layout.program model) fuel (initialState model xs left right Layout.builderBase)).transitions,
        PackedConstruction.CleanTail t.before.core ∧ PackedConstruction.CleanTail t.after.core :=
  Resources.run_numeric_closed (Layout.program model) fuel
    (initialState model xs left right Layout.builderBase)
    (initial_clean model xs left right Layout.builderBase).1

end RMQ.SuccinctFinal.PackedLifecycle.Reusable
