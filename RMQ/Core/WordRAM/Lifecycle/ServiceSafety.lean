import RMQ.Core.WordRAM.Lifecycle.Retained
import RMQ.Core.WordRAM.Lifecycle.Service

/-! # Safety of the actual charged query service

Preparation, finite-bank clearing, and the compact query run all on one program
and one represented state. Their safety is then transported to the lifecycle
prefix followed by an arbitrary continuation.
-/

namespace RMQ.SuccinctFinal.PackedLifecycle.ServiceSafety

open PackedWordRAM PackedWordRAM.Structured PackedWordRAM.Optimization
open PackedConstruction.Conservative

abbrev QueryAction := PackedWordRAM.Structured.Action
set_option maxRecDepth 30000

attribute [local irreducible] compactQueryProgram QueryEntry.setupCode
attribute [local irreducible] Service.program Service.entry Service.budget

theorem canonical_header (xs : List Int) : (buildMemory xs)[0]? = some xs.length := by
  unfold buildMemory shapeMemory repackWords
  rw [List.getElem?_append_left (by rw [metadata_length]; decide)]
  unfold metadata
  rw [List.getElem?_append_left (by rw [List.length_append, scalarMetadata_length]; omega)]
  rw [List.getElem?_append_left (by rw [scalarMetadata_length]; decide)]
  change some (SuccinctClassic.cartesianShape xs).size = some xs.length
  rw [PackedCellProbe.packedReviewerCartesianShape_size]

private theorem action_next (memory : PackedWordRAM.Memory) (op : QueryAction) (s : PackedWordRAM.State)
    (running : (PackedWordRAM.execute memory op.instruction s).1.status = .running) :
    (PackedWordRAM.execute memory op.instruction s).1.pc = s.pc + 1 := by
  cases op <;> simp [PackedWordRAM.Structured.Action.instruction, PackedWordRAM.execute, PackedWordRAM.State.writeNext] at *
  split <;> simp_all

private theorem actions_safe (memory : PackedWordRAM.Memory) (program : PackedWordRAM.Program)
    (W : Nat) (ops : List QueryAction) (s : PackedWordRAM.State)
    (running : s.status = .running) (fit : s.Fits W)
    (host : HostedAt program s.pc (ops.map PackedWordRAM.Structured.Action.instruction))
    (fields : ∀ op ∈ ops, op.instruction.Fits W)
    (localSafe : ∀ op ∈ ops, ∀ t : PackedWordRAM.State, t.Fits W →
      op.LocalSafe memory W (PackedWordRAM.Structured.Data.ofState t))
    (bound : s.pc + ops.length < 2 ^ W) :
    TraceSafe W (PackedWordRAM.run memory program ops.length s).transitions := by
  induction ops generalizing s with
  | nil => intro t member; cases member
  | cons op ops ih =>
    let after := (PackedWordRAM.execute memory op.instruction s).1
    let first : PackedWordRAM.Transition :=
      ⟨s, op.instruction, after, (PackedWordRAM.execute memory op.instruction s).2⟩
    have fetched := host.head
    have stepEq : PackedWordRAM.step memory program s = some first := by
      simp [PackedWordRAM.step, running, fetched, first, after]
    have hs := PackedWordRAM.Structured.Action.execute_safe memory W op s fit (fields op (by simp))
      (localSafe op (by simp) s fit) (by simp only [List.length_cons] at bound; omega)
    have tail : TraceSafe W (PackedWordRAM.run memory program ops.length after).transitions := by
      by_cases hr : after.status = .running
      · have hp : after.pc = s.pc + 1 := action_next memory op s hr
        apply ih after hr hs.2
        · rw [hp]; exact QueryEntry.hosted_cons_tail host
        · exact fun a ha => fields a (List.mem_cons_of_mem _ ha)
        · exact fun a ha => localSafe a (List.mem_cons_of_mem _ ha)
        · rw [hp]; simp only [List.length_cons] at bound; omega
      · have noStep : PackedWordRAM.step memory program after = none := by
          simp [PackedWordRAM.step]
        rw [PackedWordRAM.run_of_step_none memory program after ops.length noStep]
        intro t member; cases member
    intro t member
    simp only [List.length_cons, PackedWordRAM.run, stepEq, List.mem_cons] at member
    rcases member with rfl | member
    · exact hs
    · exact tail t member

theorem prepare_fields (W : Nat) (cap : 301 < 2 ^ W) :
    ∀ i ∈ Service.prepare, i.Fits W := by
  intro i member
  simp only [Service.prepare, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;>
    simp only [PackedWordRAM.Instruction.Fits, PackedWordRAM.Instruction.encoding,
      PackedWordRAM.Instruction.operands, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] <;> intro value h <;>
    rcases h with rfl | rfl | rfl <;> omega

theorem program_fields (n : Nat) : ∀ i ∈ Service.program, i.Fits (wordWidth n) := by
  intro i member
  rw [Service.program] at member
  rcases List.mem_append.mp member with compact | rest
  · exact compactQueryProgram_fits n i compact
  · rcases List.mem_append.mp rest with preparation | setup
    · exact prepare_fields _ (by have := query_small_fields_fit n; omega) i preparation
    · exact QueryEntry.setupCode_fields n i setup

theorem program_fields32 : ∀ i ∈ Service.program, OperandsFit32 i := by
  intro i member
  apply operandsFit32_of_fits
  rw [Service.program] at member
  rcases List.mem_append.mp member with compact | rest
  · exact QueryBridge.compact_fields32 i compact
  · rcases List.mem_append.mp rest with preparation | setup
    · exact prepare_fields 32 (by decide) i preparation
    · rw [QueryEntry.setupCode] at setup
      rcases List.mem_append.mp setup with clearing | jumping
      · exact QueryEntry.clearCode_fields 32 3 QueryEntry.clearCount (by decide)
          (by rw [QueryEntry.clearCount_eq]; decide) i clearing
      · have hi := List.mem_singleton.mp jumping
        subst i
        simp [PackedWordRAM.Instruction.Fits, PackedWordRAM.Instruction.encoding,
          PackedWordRAM.Instruction.operands]

theorem prepare_safe (xs : List Int) (left right : Nat) (s : PackedWordRAM.State)
    (inputs : Service.Inputs left right s) (fit : s.Fits (wordWidth xs.length)) :
    TraceSafe (wordWidth xs.length)
      (PackedWordRAM.run (buildMemory xs) Service.program 4 s).transitions := by
  let ops : List QueryAction := [.constant 2 0, .load 2 2, .move 0 300, .move 1 301]
  have code : ops.map PackedWordRAM.Structured.Action.instruction = Service.prepare := rfl
  have len : ops.length = 4 := rfl
  rw [← len]
  apply actions_safe (buildMemory xs) Service.program _ ops s inputs.1 fit
  · rw [code, inputs.2.1]
    intro i hi
    exact Service.prepare_fetch i (by simpa only [Service.prepare_length] using hi)
  · intro op member
    apply prepare_fields _ (by have := query_small_fields_fit xs.length; omega)
    rw [← code]
    exact List.mem_map.mpr ⟨op, member, rfl⟩
  · intro op member t hfit
    simp only [ops, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact Nat.two_pow_pos _
    · intro value reply
      exact buildMemory_words_fit xs value (List.mem_of_getElem? reply)
    · exact hfit.2.1 300
    · exact hfit.2.1 301
  · rw [len, inputs.2.1, Service.entry_eq]
    have := query_small_fields_fit xs.length
    omega

private theorem compose_safety (memory : PackedWordRAM.Memory) (program : PackedWordRAM.Program)
    (W a b : Nat) (s middle : PackedWordRAM.State) (fit : s.Fits W)
    (first : TraceSafe W (PackedWordRAM.run memory program a s).transitions)
    (finish : (PackedWordRAM.run memory program a s).final = middle)
    (second : RankExecutionSafety memory W program b middle) :
    RankExecutionSafety memory W program (a + b) s := by
  have splitRun := PackedWordRAM.run_add memory program a b s
  dsimp only at splitRun
  rw [finish] at splitRun
  have all : TraceSafe W (PackedWordRAM.run memory program (a + b) s).transitions := by
    rw [splitRun]
    apply compact_traceSafe_append first
    intro t member
    obtain ⟨index, occurrence⟩ := List.mem_iff_getElem?.mp member
    exact second.2.2.1 index t occurrence
  refine ⟨second.1, ?_, ?_, ?_, ?_⟩
  · rw [splitRun]; exact second.2.1
  · intro index t occurrence; exact all t (List.mem_of_getElem? occurrence)
  · exact run_prefix_fits _ _ _ _ s fit all
  · intro index t receipt occurrence read
    have hs := all t (List.mem_of_getElem? occurrence)
    exact run_read_fits occurrence read hs.1 hs.2

theorem execution_safe (xs : List Int) (left right : Nat) (s : PackedWordRAM.State)
    (inputs : Service.Inputs left right s) (fit : s.Fits (wordWidth xs.length))
    (hl : left < 2 ^ wordWidth xs.length) (hr : right < 2 ^ wordWidth xs.length) :
    RankExecutionSafety (buildMemory xs) (wordWidth xs.length) Service.program Service.budget s := by
  have prep := prepare_safe xs left right s inputs fit
  have hp := Service.prepare_exec (buildMemory xs) xs.length left right s (canonical_header xs) inputs
  have preparedFit : (Service.prepared xs.length s).Fits (wordWidth xs.length) := by
    rw [← hp.1]
    exact run_prefix_fits _ _ _ 4 s fit prep 4 (Nat.le_refl _)
  have setupRaw := QueryEntry.chargedEntry_execution_safe xs
    (Service.prepare ++ QueryEntry.setupCode) left right (Service.prepared xs.length s)
    (Service.prepared_inputs _ _ _ _ inputs)
    (by simpa only [Service.prepared, Service.preparedAt, Service.program] using Service.setup_host)
    preparedFit (by
      change Service.entry + 4 + QueryEntry.clearCount < 2 ^ wordWidth xs.length
      rw [Service.entry_eq, QueryEntry.clearCount_eq]
      have := query_small_fields_fit xs.length
      omega) (by simpa only [Service.program] using program_fields xs.length) hl hr
  have setup : RankExecutionSafety (buildMemory xs) (wordWidth xs.length) Service.program
      (QueryEntry.setupCost + compactQueryBudget) (Service.prepared xs.length s) := by
    simpa only [Service.program] using setupRaw
  simpa only [Service.budget, Nat.add_assoc] using
    compose_safety (buildMemory xs) Service.program (wordWidth xs.length) 4
      (QueryEntry.setupCost + compactQueryBudget) s (Service.prepared xs.length s)
      fit prep hp.1 setup

private theorem clear_writes (first count bank : Nat) (bound : first + count ≤ bank) :
    ∀ i ∈ QueryEntry.clearCode first count, i.WritesOnly (fun r => r < bank) := by
  induction count generalizing first with
  | zero => simp [QueryEntry.clearCode]
  | succ count ih =>
    intro i member
    simp only [QueryEntry.clearCode, List.mem_cons] at member
    rcases member with rfl | member
    · change first < bank; omega
    · exact ih (first + 1) (by omega) i member

theorem program_writes :
    ∀ i ∈ Service.program, i.WritesOnly (fun r => r < 8273) := by
  intro i member
  rw [Service.program] at member
  rcases List.mem_append.mp member with compact | rest
  · have h := compactAt_writesOnly compactQuerySource compactQueryFresh 0 0
      compactQuerySource_registersBelow
    have hb : compactQueryFresh + 2 * (0 + compactDepth compactQuerySource) = 8273 := by
      simpa only [Nat.zero_add, compactQueryRegisterCount] using compactQueryRegisterCount_eq
    rw [hb] at h
    apply h i
    simpa only [compactQueryProgram] using compact
  · rcases List.mem_append.mp rest with preparation | setup
    · simp only [Service.prepare, List.mem_cons, List.not_mem_nil, or_false] at preparation
      rcases preparation with rfl | rfl | rfl | rfl <;> simp [PackedWordRAM.Instruction.WritesOnly]
    · rw [QueryEntry.setupCode] at setup
      rcases List.mem_append.mp setup with clearing | jumping
      · exact clear_writes 3 QueryEntry.clearCount 8273
          (by rw [QueryEntry.clearCount_eq]; decide) i clearing
      · have hi := List.mem_singleton.mp jumping; subst i; trivial

theorem program_control (tail : List PackedLifecycle.Instruction) :
    ∀ i ∈ Service.program, QuerySafetyBridge.ControlBound
      (QuerySafetyBridge.host Service.program tail).length i := by
  intro i member
  rw [Service.program] at member
  rcases List.mem_append.mp member with compact | rest
  · apply QuerySafetyBridge.compact_controlBound _ _ i compact
    simp only [QuerySafetyBridge.host, List.length_append, List.length_map,
      Service.program_length, compactQueryProgram_length_eq]
    omega
  · rcases List.mem_append.mp rest with preparation | setup
    · simp only [Service.prepare, List.mem_cons, List.not_mem_nil, or_false] at preparation
      rcases preparation with rfl | rfl | rfl | rfl <;> trivial
    · apply QuerySafetyBridge.setupCode_controlBound _ _ i setup
      simp only [QuerySafetyBridge.host, List.length_append, List.length_map,
        Service.program_length]
      omega

theorem successful_reads (xs : List Int) (left right : Nat) (s : PackedWordRAM.State)
    (inputs : Service.Inputs left right s) :
    ∀ receipt ∈ (PackedWordRAM.run (buildMemory xs) Service.program Service.budget s).reads,
      ∃ value, receipt.reply = some value := by
  have obs := Service.observations (buildMemory xs) xs.length left right s
    (canonical_header xs) inputs
  rw [obs.2.2.1, (compactQueryRun_original_observations (buildMemory xs) xs.length left right).2]
  intro receipt member
  rcases List.mem_cons.mp member with rfl | old
  · exact ⟨xs.length, rfl⟩
  · exact queryRun_reads_reply xs left right receipt old

def Entered (left right : Nat) (s : PackedLifecycle.State) : Prop :=
  s.core.status = .running ∧ s.core.pc = Service.entry ∧
    s.core.regs 300 = left ∧ s.core.regs 301 = right

theorem entered_inputs (xs : List Int) (left right : Nat) (s : PackedLifecycle.State)
    (canonical : Retained.Canonical xs s) (entered : Entered left right s) :
    Service.Inputs left right (Retained.projectQueryState s) := by
  refine ⟨?_, entered.2.1, entered.2.2.1, entered.2.2.2, canonical.2.1⟩
  simp only [Retained.projectQueryState, entered.1, Retained.projectStatus]

theorem entered_execution_safe (xs : List Int) (left right : Nat) (s : PackedLifecycle.State)
    (canonical : Retained.Canonical xs s) (entered : Entered left right s) :
    RankExecutionSafety (buildMemory xs) (wordWidth xs.length) Service.program Service.budget
      (Retained.projectQueryState s) := by
  apply execution_safe xs left right _ (entered_inputs xs left right s canonical entered)
    (Retained.project_fits canonical.2.2)
  · rw [← entered.2.2.1]; exact canonical.2.2.1.1 300
  · rw [← entered.2.2.2]; exact canonical.2.2.1.1 301

theorem stopped (xs : List Int) (left right : Nat) (s : PackedWordRAM.State)
    (inputs : Service.Inputs left right s) :
    (PackedWordRAM.run (buildMemory xs) Service.program Service.budget s).final.status ≠ .running :=
  (Service.observations (buildMemory xs) xs.length left right s (canonical_header xs) inputs).2.2.2.2.2

/-- The actual retained state, without replacing its registers or status, is
the input to the mixed lifecycle program. -/
theorem actual_prefix (xs : List Int) (tail : List PackedLifecycle.Instruction)
    (left right fuel : Nat) (s : PackedLifecycle.State)
    (canonical : Retained.Canonical xs s) (entered : Entered left right s)
    (within : fuel ≤ Service.budget) :
    PackedLifecycle.run (QuerySafetyBridge.host Service.program tail) fuel s =
      ⟨QuerySafetyBridge.embedded (buildMemory xs)
          (PackedWordRAM.run (buildMemory xs) Service.program fuel (Retained.projectQueryState s)).final,
        (PackedWordRAM.run (buildMemory xs) Service.program fuel (Retained.projectQueryState s)).transitions.map
          (QuerySafetyBridge.liftTransition (buildMemory xs))⟩ := by
  calc
    _ = PackedLifecycle.run (QuerySafetyBridge.host Service.program tail) fuel
        (QuerySafetyBridge.embedded (buildMemory xs) (Retained.projectQueryState s)) :=
      congrArg _ canonical.1.roundtrip
    _ = _ := QuerySafetyBridge.prefix_run _ _ tail program_fields32 fuel Service.budget _ within
      (stopped xs left right _ (entered_inputs xs left right s canonical entered))

theorem actual_prefix_canonical (xs : List Int) (tail : List PackedLifecycle.Instruction)
    (left right fuel : Nat) (s : PackedLifecycle.State)
    (canonical : Retained.Canonical xs s) (entered : Entered left right s)
    (within : fuel ≤ Service.budget) :
    Retained.Canonical xs
      (PackedLifecycle.run (QuerySafetyBridge.host Service.program tail) fuel s).final := by
  rw [actual_prefix xs tail left right fuel s canonical entered within]
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_, ?_⟩
  · intro r hr
    change (PackedWordRAM.run (buildMemory xs) Service.program fuel
      (Retained.projectQueryState s)).final.regs r = 0
    rw [PackedWordRAM.run_frame _ _ _ _ _ program_writes r (by omega)]
    exact canonical.2.1 r hr
  · exact QuerySafetyBridge.embedded_fits _ _ _
      ((entered_execution_safe xs left right s canonical entered).2.2.2.1 fuel within)
      (buildMemory_length_fit xs) (buildMemory_words_fit xs)

theorem actual_prefix_safe (xs : List Int) (tail : List PackedLifecycle.Instruction)
    (left right fuel : Nat) (s : PackedLifecycle.State)
    (canonical : Retained.Canonical xs s) (entered : Entered left right s)
    (within : fuel ≤ Service.budget) :
    ∀ t ∈ (PackedLifecycle.run (QuerySafetyBridge.host Service.program tail) fuel s).transitions,
      t.Safe (wordWidth xs.length) (QuerySafetyBridge.host Service.program tail).length := by
  have source := entered_inputs xs left right s canonical entered
  have safe := QuerySafetyBridge.prefix_safe (buildMemory xs) Service.program tail program_fields32
    fuel Service.budget (wordWidth xs.length) (Retained.projectQueryState s) within
    (stopped xs left right _ source) (entered_execution_safe xs left right s canonical entered)
    (program_control tail) (successful_reads xs left right _ source) (buildMemory_words_fit xs)
  rwa [← canonical.1.roundtrip] at safe

theorem actual_prefix_reads (xs : List Int) (tail : List PackedLifecycle.Instruction)
    (left right fuel : Nat) (s : PackedLifecycle.State)
    (canonical : Retained.Canonical xs s) (entered : Entered left right s)
    (within : fuel ≤ Service.budget) :
    (PackedLifecycle.run (QuerySafetyBridge.host Service.program tail) fuel s).reads =
      (PackedWordRAM.run (buildMemory xs) Service.program fuel (Retained.projectQueryState s)).reads.map
        (fun r => (r.address, r.reply)) := by
  have h := QuerySafetyBridge.prefix_reads (buildMemory xs) Service.program tail program_fields32
    fuel Service.budget (Retained.projectQueryState s) within
    (stopped xs left right _ (entered_inputs xs left right s canonical entered))
  rwa [← canonical.1.roundtrip] at h

theorem actual_read_width (xs : List Int) (tail : List PackedLifecycle.Instruction)
    (left right : Nat) (s : PackedLifecycle.State)
    (canonical : Retained.Canonical xs s) (entered : Entered left right s)
    (index : Nat) (t : PackedLifecycle.Transition) (address : Nat) (reply : Option Nat)
    (occurs : (PackedLifecycle.run (QuerySafetyBridge.host Service.program tail)
      Service.budget s).transitions[index]? = some t)
    (read : t.read? = some (address, reply)) :
    address < 2 ^ wordWidth xs.length ∧ reply = (buildMemory xs)[address]? ∧
      (∀ value, reply = some value → value < 2 ^ wordWidth xs.length) := by
  apply QuerySafetyBridge.run_read_width (buildMemory xs) Service.program tail program_fields32
    Service.budget (wordWidth xs.length) (Retained.projectQueryState s)
    (stopped xs left right _ (entered_inputs xs left right s canonical entered))
    (entered_execution_safe xs left right s canonical entered) index t address reply _ read
  rwa [← canonical.1.roundtrip]

theorem actual_transition_fits (xs : List Int) (tail : List PackedLifecycle.Instruction)
    (left right : Nat) (s : PackedLifecycle.State)
    (canonical : Retained.Canonical xs s) (entered : Entered left right s) :
    ∀ t ∈ (PackedLifecycle.run (QuerySafetyBridge.host Service.program tail)
      Service.budget s).transitions,
      t.before.Fits (wordWidth xs.length) ∧ t.after.Fits (wordWidth xs.length) := by
  have h := QuerySafetyBridge.run_transition_fits (buildMemory xs) Service.program tail program_fields32
    Service.budget (wordWidth xs.length) (Retained.projectQueryState s)
    (stopped xs left right _ (entered_inputs xs left right s canonical entered))
    (entered_execution_safe xs left right s canonical entered)
    (buildMemory_length_fit xs) (buildMemory_words_fit xs)
  rwa [← canonical.1.roundtrip] at h

end RMQ.SuccinctFinal.PackedLifecycle.ServiceSafety
