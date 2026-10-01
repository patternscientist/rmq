import RMQ.Core.WordRAM.Lifecycle.QueryBridge
import RMQ.Core.WordRAM.Lifecycle.QueryEntry
import RMQ.Core.WordRAM.Lifecycle.Finalizer
import RMQ.Core.WordRAM.Lifecycle.Safety

/-! # Packed-query safety on the retained lifecycle state

Packed width safety permits failed reads; construction primitive safety also
requires successful backing and in-program direct targets. These additional
obligations are explicit. Full transition simulation remains valid without
them, including failed reads and stopped initial states.
-/

namespace RMQ.SuccinctFinal.PackedLifecycle.QuerySafetyBridge

open PackedConstruction.Conservative
open PackedWordRAM.Structured PackedWordRAM.Optimization

abbrev QueryState := PackedWordRAM.State
abbrev QueryInstruction := PackedWordRAM.Instruction
abbrev QueryProgram := PackedWordRAM.Program
abbrev QueryMemory := PackedWordRAM.Memory

def ControlBound (len : Nat) : QueryInstruction → Prop
  | .jump target | .branchZero _ target => target < len
  | .jumpRegister _ => False
  | _ => True

def LoadPresent (memory : QueryMemory) (s : QueryState) : QueryInstruction → Prop
  | .load _ address => ∃ value, memory[s.regs address]? = some value
  | _ => True

theorem instruction_encoding (i : QueryInstruction) (fields : OperandsFit32 i) :
    (instruction i fields).constants.map Fin.val = i.encoding := by
  cases i <;> try rfl
  case arithmetic op dst lhs rhs => cases op <;> rfl
  case comparison op dst lhs rhs => cases op <;> rfl

theorem instruction_operands (i : QueryInstruction) (fields : OperandsFit32 i)
    (W : Nat) (fit : i.Fits W) : (instruction i fields).OperandsFit W := by
  intro operand member
  apply fit operand.val
  rw [← instruction_encoding i fields]
  exact List.mem_map.mpr ⟨operand, member, rfl⟩

/-- No answer or routing premise appears: each extra premise describes this
primitive's actual backing or encoded control field. -/
theorem instruction_safe (memory : QueryMemory) (s : QueryState) (i : QueryInstruction)
    (fields : OperandsFit32 i) (W len : Nat)
    (safe : i.Safe W s) (control : ControlBound len i) (present : LoadPresent memory s i)
    (words : ∀ word ∈ memory, word < 2 ^ W) :
    (instruction i fields).Safe W len (state memory s) := by
  refine ⟨instruction_operands i fields W safe.1, ?_⟩
  cases i with
  | load dst address =>
    obtain ⟨value, reply⟩ := present
    have inside := (List.getElem?_eq_some_iff.mp reply).1
    exact ⟨inside, value, reply, words value (List.mem_of_getElem? reply)⟩
  | constant dst value => trivial
  | move dst src => trivial
  | arithmetic op dst lhs rhs =>
    have arithmeticSafe := safe.2.2
    cases op <;>
      simpa [instruction, PackedConstruction.Prim.SafeAt, state, arithmetic,
        PackedWordRAM.Instruction.Safe, PackedWordRAM.Arithmetic.eval,
        PackedConstruction.Arithmetic.eval] using arithmeticSafe
  | comparison op dst lhs rhs => trivial
  | jump target => exact control
  | jumpRegister src => exact control.elim
  | branchZero condition target => exact control
  | halt src => trivial

theorem translate_safe (memory : QueryMemory) (s : QueryState) (i : QueryInstruction)
    (fields : OperandsFit32 i) (W len : Nat)
    (safe : i.Safe W s) (control : ControlBound len i) (present : LoadPresent memory s i)
    (words : ∀ word ∈ memory, word < 2 ^ W) :
    (translate i).primitive.Safe W len (state memory s) := by
  rw [translate_of_fits i fields]
  exact instruction_safe memory s i fields W len safe control present words

/-- The structured compact emitter has only direct, statically bounded jumps.
The bound covers the target even when its branch is not taken. -/
theorem compactAt_controlBound (block : Block) (fresh depth base len : Nat)
    (last : base + compactSize block < len) :
    ∀ i ∈ compactAt block fresh depth base, ControlBound len i := by
  induction block generalizing depth base with
  | skip => simp [compactAt]
  | action op =>
    intro i member
    have equal : i = op.instruction := by simpa [compactAt] using member
    subst i
    cases op <;> trivial
  | exit src => simp [compactAt, ControlBound]
  | seq a b iha ihb =>
    intro i member
    rcases List.mem_append.mp member with member | member
    · exact iha depth base (by simp only [compactSize] at last; omega) i member
    · exact ihb depth (base + compactSize a) (by simp only [compactSize] at last; omega) i member
  | ifZero condition zero nonzero ihz ihn =>
    intro i member
    simp only [compactAt, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
    simp only [compactSize] at last
    rcases member with ((rfl | member) | rfl) | member
    · simp only [ControlBound]; omega
    · exact ihn depth (base + 1) (by omega) i member
    · simp only [ControlBound]; omega
    · exact ihz depth (base + 1 + compactSize nonzero + 1) (by omega) i member
  | «repeat» count body ih =>
    cases count with
    | zero => simp [compactAt]
    | succ count =>
      intro i member
      simp only [compactAt, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
      simp only [compactSize] at last
      rcases member with ((rfl | rfl | rfl) | member) | (rfl | rfl)
      · trivial
      · trivial
      · simp only [ControlBound]; omega
      · exact ih (depth + 1) (base + 3) (by omega) i member
      · trivial
      · simp only [ControlBound]; omega

theorem compact_controlBound (len : Nat) (last : compactQueryProgram.length < len) :
    ∀ i ∈ compactQueryProgram, ControlBound len i := by
  apply compactAt_controlBound compactQuerySource compactQueryFresh 0 0 len
  simpa only [Nat.zero_add, compactQueryProgram_length] using last

theorem clearCode_controlBound (first count len : Nat) :
    ∀ i ∈ QueryEntry.clearCode first count, ControlBound len i := by
  induction count generalizing first with
  | zero => simp [QueryEntry.clearCode]
  | succ count ih =>
    intro i member
    simp only [QueryEntry.clearCode, List.mem_cons] at member
    rcases member with rfl | member
    · trivial
    · exact ih (first + 1) i member

theorem setupCode_controlBound (len : Nat) (positive : 0 < len) :
    ∀ i ∈ QueryEntry.setupCode, ControlBound len i := by
  intro i member
  rcases List.mem_append.mp member with member | member
  · exact clearCode_controlBound 3 QueryEntry.clearCount len i member
  · have equal : i = .jump 0 := List.mem_singleton.mp member
    subst i
    exact positive

def embedded (memory : QueryMemory) (s : QueryState) : State := ofCore (state memory s) 0 0

theorem core_fits (memory : QueryMemory) (s : QueryState) (W : Nat)
    (fit : s.Fits W) (extent : memory.length < 2 ^ W)
    (words : ∀ word ∈ memory, word < 2 ^ W) : (state memory s).Fits W := by
  refine ⟨fit.2.1, fit.1, extent, ?_, ?_⟩
  · intro address value reply
    exact words value (List.mem_of_getElem? reply)
  · intro value halted
    have oldHalted : s.status = .halted value := by
      cases hs : s.status <;> simp_all [state, status]
    exact fit.2.2 value oldHalted

theorem embedded_fits (memory : QueryMemory) (s : QueryState) (W : Nat)
    (fit : s.Fits W) (extent : memory.length < 2 ^ W)
    (words : ∀ word ∈ memory, word < 2 ^ W) : (embedded memory s).Fits W :=
  ⟨core_fits memory s W fit extent words, Nat.two_pow_pos _, Nat.two_pow_pos _⟩

/-- Finite list backing and zero resource extents make retirement explicit. -/
theorem embedded_closed (memory : QueryMemory) (s : QueryState) :
    (embedded memory s).Closed ∧ (embedded memory s).keyExtent = 0 ∧
      (embedded memory s).keyRegExtent = 0 := by
  refine ⟨⟨?_, ?_, ?_⟩, rfl, rfl⟩
  · intro address outside
    exact List.getElem?_eq_none_iff.mpr outside
  · intro address _; rfl
  · intro r _; rfl

theorem embedded_finite_bank (memory : QueryMemory) (s : QueryState) (bank : Nat)
    (finite : ∀ r, bank ≤ r → s.regs r = 0) :
    ∀ r, bank ≤ r → (embedded memory s).core.regs r = 0 := finite

/-- Successful receipt backing is recovered from the same executed occurrence. -/
theorem loadPresent_of_reads {memory : QueryMemory} {program : QueryProgram}
    {fuel : Nat} {s : QueryState} {index : Nat} {t : PackedWordRAM.Transition}
    (occurs : (PackedWordRAM.run memory program fuel s).transitions[index]? = some t)
    (reads : ∀ receipt ∈ (PackedWordRAM.run memory program fuel s).reads,
      ∃ value, receipt.reply = some value) : LoadPresent memory t.before t.instruction := by
  have exec := (PackedWordRAM.run_transition_spec occurs).2.2.2
  cases hi : t.instruction <;> try trivial
  case load dst address =>
    have receipt : t.receipt = some ⟨t.before.regs address, memory[t.before.regs address]?⟩ := by
      have h := congrArg Prod.snd exec
      simpa [hi, PackedWordRAM.execute] using h.symm
    have member : (⟨t.before.regs address, memory[t.before.regs address]?⟩ :
        PackedWordRAM.Receipt) ∈ (PackedWordRAM.run memory program fuel s).reads :=
      List.mem_filterMap.mpr ⟨t, List.mem_of_getElem? occurs, receipt⟩
    exact reads _ member

def host (program : QueryProgram) (tail : List Instruction) : List Instruction :=
  (program.map translate).map oldInstruction ++ tail

def liftTransition (memory : QueryMemory) (t : PackedWordRAM.Transition) : Transition :=
  oldTransition 0 0 (QueryBridge.liftTransition memory t)

private theorem old_prefix_of_stopped (program : List PackedConstruction.BInstr)
    (tail : List Instruction) (fuel budget : Nat) (s : PackedConstruction.State)
    (within : fuel ≤ budget)
    (stopped : (PackedConstruction.run program budget s).final.status ≠ .running) :
    run (program.map oldInstruction ++ tail) fuel (ofCore s 0 0) =
      oldRun 0 0 (PackedConstruction.run program fuel s) := by
  induction fuel generalizing budget s with
  | zero => rfl
  | succ fuel ih =>
    cases budget with
    | zero => omega
    | succ budget =>
      cases hs : PackedConstruction.stepProgram program s with
      | none =>
        have hstop : s.status ≠ .running := by
          simpa [PackedConstruction.run, hs] using stopped
        have hn := step_none_of_stopped (program.map oldInstruction ++ tail)
          (ofCore s 0 0) hstop
        simp [run, hn, PackedConstruction.run, hs, oldRun]
      | some t =>
        have hrest : (PackedConstruction.run program budget t.after).final.status ≠ .running := by
          simpa [PackedConstruction.run, hs] using stopped
        have hn := old_step hs tail 0 0
        simp only [run, hn, PackedConstruction.run, hs]
        rw [show (oldTransition 0 0 t).after = ofCore t.after 0 0 from rfl,
          ih budget t.after (by omega) hrest]
        rfl

/-- Appending a lifecycle continuation preserves every prefix of a stopped
packed run, including faults and early halts. Full states and order are exact. -/
theorem prefix_run (memory : QueryMemory) (program : QueryProgram)
    (tail : List Instruction) (fields : ∀ i ∈ program, OperandsFit32 i)
    (fuel budget : Nat) (s : QueryState) (within : fuel ≤ budget)
    (stopped : (PackedWordRAM.run memory program budget s).final.status ≠ .running) :
    run (host program tail) fuel (embedded memory s) =
      ⟨embedded memory (PackedWordRAM.run memory program fuel s).final,
        (PackedWordRAM.run memory program fuel s).transitions.map (liftTransition memory)⟩ := by
  have all := QueryBridge.translated_run_all memory program fields budget s
  have coreStopped : (PackedConstruction.run (program.map translate) budget
      (state memory s)).final.status ≠ .running := by
    rw [all.1]
    cases hs : (PackedWordRAM.run memory program budget s).final.status <;>
      simp_all [state, status]
  rw [show host program tail = (program.map translate).map oldInstruction ++ tail from rfl,
    show embedded memory s = ofCore (state memory s) 0 0 from rfl,
    old_prefix_of_stopped _ tail fuel budget _ within coreStopped]
  have sim := QueryBridge.translated_run_all memory program fields fuel s
  simp only [oldRun, sim.1, sim.2.1, List.map_map]
  rfl

theorem prefix_fits (memory : QueryMemory) (program : QueryProgram)
    (tail : List Instruction) (fields : ∀ i ∈ program, OperandsFit32 i)
    (fuel budget W : Nat) (s : QueryState) (within : fuel ≤ budget)
    (stopped : (PackedWordRAM.run memory program budget s).final.status ≠ .running)
    (safe : PackedWordRAM.RankExecutionSafety memory W program budget s)
    (extent : memory.length < 2 ^ W) (words : ∀ word ∈ memory, word < 2 ^ W) :
    (run (host program tail) fuel (embedded memory s)).final.Fits W := by
  rw [prefix_run memory program tail fields fuel budget s within stopped]
  exact embedded_fits memory _ W (safe.2.2.2.1 fuel within) extent words

theorem prefix_closed (memory : QueryMemory) (program : QueryProgram)
    (tail : List Instruction) (fields : ∀ i ∈ program, OperandsFit32 i)
    (fuel budget : Nat) (s : QueryState) (within : fuel ≤ budget)
    (stopped : (PackedWordRAM.run memory program budget s).final.status ≠ .running) :
    (run (host program tail) fuel (embedded memory s)).final.Closed ∧
      (run (host program tail) fuel (embedded memory s)).final.keyExtent = 0 ∧
      (run (host program tail) fuel (embedded memory s)).final.keyRegExtent = 0 := by
  rw [prefix_run memory program tail fields fuel budget s within stopped]
  exact embedded_closed memory _

theorem prefix_finite_bank (memory : QueryMemory) (program : QueryProgram)
    (tail : List Instruction) (fields : ∀ i ∈ program, OperandsFit32 i)
    (fuel budget bank : Nat) (s : QueryState) (within : fuel ≤ budget)
    (stopped : (PackedWordRAM.run memory program budget s).final.status ≠ .running)
    (writes : ∀ i ∈ program, i.WritesOnly (fun r => r < bank))
    (finite : ∀ r, bank ≤ r → s.regs r = 0) :
    ∀ r, bank ≤ r → (run (host program tail) fuel (embedded memory s)).final.core.regs r = 0 := by
  rw [prefix_run memory program tail fields fuel budget s within stopped]
  intro r outside
  change (PackedWordRAM.run memory program fuel s).final.regs r = 0
  rw [PackedWordRAM.run_frame memory program fuel s _ writes r (by omega)]
  exact finite r outside

/-- Strong safety is obtained only after successful backing is established for
the actual load occurrences; dormant jump targets are checked independently. -/
theorem run_safe (memory : QueryMemory) (program : QueryProgram)
    (tail : List Instruction) (fields : ∀ i ∈ program, OperandsFit32 i)
    (budget W : Nat) (s : QueryState)
    (stopped : (PackedWordRAM.run memory program budget s).final.status ≠ .running)
    (safe : PackedWordRAM.RankExecutionSafety memory W program budget s)
    (control : ∀ i ∈ program, ControlBound (host program tail).length i)
    (reads : ∀ receipt ∈ (PackedWordRAM.run memory program budget s).reads,
      ∃ value, receipt.reply = some value)
    (words : ∀ word ∈ memory, word < 2 ^ W) :
    ∀ t ∈ (run (host program tail) budget (embedded memory s)).transitions,
      t.Safe W (host program tail).length := by
  rw [prefix_run memory program tail fields budget budget s (Nat.le_refl _) stopped]
  intro t member
  change t ∈ (PackedWordRAM.run memory program budget s).transitions.map (liftTransition memory) at member
  obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨index, occurrence⟩ := List.mem_iff_getElem?.mp oldMember
  have fetched := (PackedWordRAM.run_transition_spec occurrence).2.2.1
  have im := List.mem_of_getElem? fetched
  refine ⟨oldInstruction (translate old.instruction), rfl, ?_⟩
  exact translate_safe memory old.before old.instruction (fields _ im) W _
    (safe.2.2.1 index old occurrence).1 (control _ im)
    (loadPresent_of_reads occurrence reads) words

theorem prefix_occurrence (memory : QueryMemory) (program : QueryProgram)
    (tail : List Instruction) (fields : ∀ i ∈ program, OperandsFit32 i)
    (fuel budget : Nat) (s : QueryState) (within : fuel ≤ budget)
    (stopped : (PackedWordRAM.run memory program budget s).final.status ≠ .running)
    (index : Nat) (t : Transition)
    (occurs : (run (host program tail) fuel (embedded memory s)).transitions[index]? = some t) :
    ∃ old, (PackedWordRAM.run memory program fuel s).transitions[index]? = some old ∧
      t = liftTransition memory old := by
  rw [prefix_run memory program tail fields fuel budget s within stopped] at occurs
  simp only [List.getElem?_map] at occurs
  cases ho : (PackedWordRAM.run memory program fuel s).transitions[index]? with
  | none => simp [ho] at occurs
  | some old =>
    refine ⟨old, rfl, ?_⟩
    simpa [ho] using occurs.symm

theorem lift_read (memory : QueryMemory) (t : PackedWordRAM.Transition)
    (fields : OperandsFit32 t.instruction)
    (exec : PackedWordRAM.execute memory t.instruction t.before = (t.after, t.receipt)) :
    (liftTransition memory t).read? = t.receipt.map (fun r => (r.address, r.reply)) := by
  have hr := QueryBridge.readReply_execute memory t.instruction fields t.before
  have he := congrArg Prod.snd exec
  have read : QueryBridge.readReply (QueryBridge.liftTransition memory t) = t.receipt :=
    hr.trans he
  have same : (liftTransition memory t).read? =
      (QueryBridge.readReply (QueryBridge.liftTransition memory t)).map
        (fun r => (r.address, r.reply)) := by
    unfold liftTransition oldTransition oldInstruction QueryBridge.liftTransition
    unfold Transition.read? QueryBridge.readReply
    cases (translate t.instruction).primitive <;> rfl
  rw [same, read]

/-- The numeric read theorem includes absent replies. Its address and successful
value bounds come from the producing packed occurrence at the same width. -/
theorem run_read_width (memory : QueryMemory) (program : QueryProgram)
    (tail : List Instruction) (fields : ∀ i ∈ program, OperandsFit32 i)
    (budget W : Nat) (s : QueryState)
    (stopped : (PackedWordRAM.run memory program budget s).final.status ≠ .running)
    (safe : PackedWordRAM.RankExecutionSafety memory W program budget s)
    (index : Nat) (t : Transition) (address : Nat) (reply : Option Nat)
    (occurs : (run (host program tail) budget (embedded memory s)).transitions[index]? = some t)
    (read : t.read? = some (address, reply)) :
    address < 2 ^ W ∧ reply = memory[address]? ∧
      (∀ value, reply = some value → value < 2 ^ W) := by
  obtain ⟨old, ho, rfl⟩ := prefix_occurrence memory program tail fields budget budget s
    (Nat.le_refl _) stopped index t occurs
  have spec := PackedWordRAM.run_transition_spec ho
  rw [lift_read memory old (fields _ (List.mem_of_getElem? spec.2.2.1)) spec.2.2.2] at read
  cases hr : old.receipt with
  | none => simp [hr] at read
  | some receipt =>
    have equal : (receipt.address, receipt.reply) = (address, reply) := by simpa [hr] using read
    have h := safe.2.2.2.2 index old receipt ho hr
    cases equal
    exact h

/-- Full before/after width transport does not need successful loads. -/
theorem run_transition_fits (memory : QueryMemory) (program : QueryProgram)
    (tail : List Instruction) (fields : ∀ i ∈ program, OperandsFit32 i)
    (budget W : Nat) (s : QueryState)
    (stopped : (PackedWordRAM.run memory program budget s).final.status ≠ .running)
    (safe : PackedWordRAM.RankExecutionSafety memory W program budget s)
    (extent : memory.length < 2 ^ W) (words : ∀ word ∈ memory, word < 2 ^ W) :
    ∀ t ∈ (run (host program tail) budget (embedded memory s)).transitions,
      t.before.Fits W ∧ t.after.Fits W := by
  intro t member
  obtain ⟨index, occurrence⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨old, ho, rfl⟩ := prefix_occurrence memory program tail fields budget budget s
    (Nat.le_refl _) stopped index t occurrence
  have oldSafe := safe.2.2.1 index old ho
  exact ⟨embedded_fits memory _ W oldSafe.1.2.1 extent words,
    embedded_fits memory _ W oldSafe.2 extent words⟩

theorem host_fields (program : QueryProgram) (tail : List Instruction)
    (fields : ∀ i ∈ program, OperandsFit32 i) (W : Nat)
    (source : ∀ i ∈ program, i.Fits W) (suffix : ∀ i ∈ tail, i.Fits W) :
    ∀ i ∈ host program tail, i.Fits W := by
  intro i member
  rcases List.mem_append.mp member with prefixMember | tailMember
  · obtain ⟨translated, translatedMember, rfl⟩ := List.mem_map.mp prefixMember
    obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp translatedMember
    rw [translate_of_fits old (fields _ oldMember)]
    change ∀ word ∈ (instruction old (fields _ oldMember)).constants.map Fin.val, word < 2 ^ W
    rw [instruction_encoding]
    exact source old oldMember
  · exact suffix i tailMember

private theorem lift_reads_list (memory : QueryMemory) (ts : List PackedWordRAM.Transition)
    (equal : ∀ t ∈ ts, (liftTransition memory t).read? =
      t.receipt.map (fun r => (r.address, r.reply))) :
    (ts.map (liftTransition memory)).filterMap Transition.read? =
      (ts.filterMap (·.receipt)).map (fun r => (r.address, r.reply)) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    have head := equal t (List.mem_cons_self ..)
    have tail := ih (fun u hu => equal u (List.mem_cons_of_mem _ hu))
    simp only [List.map_cons, List.filterMap_cons]
    rw [head, tail]
    cases t.receipt <;> rfl

/-- Every attempted read, in order and with multiplicity, is preserved through
the two existing execution adapters. -/
theorem prefix_reads (memory : QueryMemory) (program : QueryProgram)
    (tail : List Instruction) (fields : ∀ i ∈ program, OperandsFit32 i)
    (fuel budget : Nat) (s : QueryState) (within : fuel ≤ budget)
    (stopped : (PackedWordRAM.run memory program budget s).final.status ≠ .running) :
    (run (host program tail) fuel (embedded memory s)).reads =
      (PackedWordRAM.run memory program fuel s).reads.map (fun r => (r.address, r.reply)) := by
  rw [prefix_run memory program tail fields fuel budget s within stopped]
  apply lift_reads_list
  intro t member
  obtain ⟨index, occurrence⟩ := List.mem_iff_getElem?.mp member
  have spec := PackedWordRAM.run_transition_spec occurrence
  exact lift_read memory t (fields _ (List.mem_of_getElem? spec.2.2.1)) spec.2.2.2

theorem prefix_safe (memory : QueryMemory) (program : QueryProgram)
    (tail : List Instruction) (fields : ∀ i ∈ program, OperandsFit32 i)
    (fuel budget W : Nat) (s : QueryState) (within : fuel ≤ budget)
    (stopped : (PackedWordRAM.run memory program budget s).final.status ≠ .running)
    (safe : PackedWordRAM.RankExecutionSafety memory W program budget s)
    (control : ∀ i ∈ program, ControlBound (host program tail).length i)
    (reads : ∀ receipt ∈ (PackedWordRAM.run memory program budget s).reads,
      ∃ value, receipt.reply = some value)
    (words : ∀ word ∈ memory, word < 2 ^ W) :
    ∀ t ∈ (run (host program tail) fuel (embedded memory s)).transitions,
      t.Safe W (host program tail).length := by
  intro t member
  apply run_safe memory program tail fields budget W s stopped safe control reads words t
  rw [show budget = fuel + (budget - fuel) by omega, run_add]
  exact List.mem_append.mpr (Or.inl member)

/-- Numeric backing and all retired resource channels are invariant throughout
query service. This states actual function equality, not footprint agreement. -/
theorem prefix_storage (memory : QueryMemory) (program : QueryProgram)
    (tail : List Instruction) (fields : ∀ i ∈ program, OperandsFit32 i)
    (fuel budget : Nat) (s : QueryState) (within : fuel ≤ budget)
    (stopped : (PackedWordRAM.run memory program budget s).final.status ≠ .running) :
    let final := (run (host program tail) fuel (embedded memory s)).final
    final.core.memory = (fun a => memory[a]?) ∧ final.core.extent = memory.length ∧
      final.core.keys = (fun _ => none) ∧ final.core.keyRegs = (fun _ => 0) ∧
      final.keyExtent = 0 ∧ final.keyRegExtent = 0 := by
  rw [prefix_run memory program tail fields fuel budget s within stopped]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end RMQ.SuccinctFinal.PackedLifecycle.QuerySafetyBridge
