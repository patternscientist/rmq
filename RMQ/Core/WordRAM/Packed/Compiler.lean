import RMQ.Core.WordRAM.Packed.Structured

/-!
# Correctness of fixed structured assembly compilation

The independent source evaluator carries no PC. The refinement below retains
the actual primitive transition segment, its ordered reads and exact length.
Static code-field fit includes serialization tags and dormant branches; it is
separate from bounds on runtime registers and arithmetic results.
-/

namespace RMQ.SuccinctFinal.PackedWordRAM.Structured

def HostedAt (program : Program) (base : Nat) (code : Program) : Prop :=
  ∀ i, i < code.length → program[base + i]? = code[i]?

theorem HostedAt.self (program : Program) : HostedAt program 0 program := by
  intro i hi
  simp

theorem HostedAt.head {program : Program} {base : Nat} {i : Instruction}
    {rest : Program} (h : HostedAt program base (i :: rest)) :
    program[base]? = some i := by
  simpa using h 0 (by simp)

theorem HostedAt.append_left {program : Program} {base : Nat} {a b : Program}
    (h : HostedAt program base (a ++ b)) : HostedAt program base a := by
  intro i hi
  have hx := h i (by simp only [List.length_append]; omega)
  simpa [List.getElem?_append_left hi] using hx

theorem HostedAt.append_right {program : Program} {base : Nat} {a b : Program}
    (h : HostedAt program base (a ++ b)) :
    HostedAt program (base + a.length) b := by
  intro i hi
  have hx := h (a.length + i) (by simp only [List.length_append]; omega)
  simpa [Nat.add_assoc, List.getElem?_append_right (by omega : a.length ≤ a.length + i)]
    using hx

theorem HostedAt.append (a b : Program) (base : Nat) (program : Program)
    (ha : HostedAt program base a) (hb : HostedAt program (base + a.length) b) :
    HostedAt program base (a ++ b) := by
  intro i hi
  by_cases hia : i < a.length
  · rw [List.getElem?_append_left hia]
    exact ha i hia
  · rw [List.getElem?_append_right (by omega)]
    have hrest := hb (i - a.length) (by simp only [List.length_append] at hi; omega)
    simpa only [Nat.add_assoc, Nat.add_sub_of_le (by omega : a.length ≤ i)] using hrest

theorem Block.compile_repeat_succ (count : Nat) (body : Block) (base : Nat) :
    (Block.repeat (count + 1) body).compileAt base =
      body.compileAt base ++ (Block.repeat count body).compileAt (base + body.size) := by
  simp [Block.compileAt, List.range_succ_eq_map, List.map_map, Function.comp_def, Nat.succ_mul,
    Nat.add_assoc, Nat.add_comm]

@[simp] theorem Block.compile_length (block : Block) (base : Nat) :
    (block.compileAt base).length = block.size := by
  induction block generalizing base with
  | skip => rfl
  | action op => rfl
  | exit src => rfl
  | seq a b iha ihb => simp [Block.compileAt, Block.size, iha, ihb]
  | ifZero c a b iha ihb => simp [Block.compileAt, Block.size, iha, ihb]; omega
  | «repeat» count body ih =>
      induction count generalizing base with
      | zero => simp [Block.compileAt, Block.size]
      | succ count ihc =>
          rw [Block.compile_repeat_succ, List.length_append, ih, ihc]
          simp [Block.size, Nat.succ_mul, Nat.add_comm]

/-- Static source operands include every action encoding, exit register/tag,
branch condition/tag and jump tag. Runtime values are a separate obligation. -/
def Block.FieldsFit (width : Nat) : Block → Prop
  | .skip => True
  | .action op => op.instruction.Fits width
  | .exit src => (Instruction.halt src).Fits width
  | .seq a b => a.FieldsFit width ∧ b.FieldsFit width
  | .ifZero c a b => (Instruction.branchZero c 0).Fits width ∧
      (Instruction.jump 0).Fits width ∧ a.FieldsFit width ∧ b.FieldsFit width
  | .repeat _ body => body.FieldsFit width

private theorem branch_fits {width condition target : Nat}
    (h : (Instruction.branchZero condition 0).Fits width) (ht : target < 2 ^ width) :
    (Instruction.branchZero condition target).Fits width := by
  simp [Instruction.Fits, Instruction.encoding, Instruction.operands] at h ⊢
  exact ⟨h.1, h.2.1, ht⟩

private theorem jump_fits {width target : Nat}
    (h : (Instruction.jump 0).Fits width) (ht : target < 2 ^ width) :
    (Instruction.jump target).Fits width := by
  simp [Instruction.Fits, Instruction.encoding, Instruction.operands] at h ⊢
  exact ⟨h.1, ht⟩

theorem Block.compile_fits (block : Block) (width base : Nat)
    (fields : block.FieldsFit width) (bound : base + block.size < 2 ^ width) :
    ∀ instruction ∈ block.compileAt base, instruction.Fits width := by
  induction block generalizing base with
  | skip => simp [Block.compileAt]
  | action op => simpa [Block.compileAt] using fields
  | exit src => simpa [Block.compileAt] using fields
  | seq a b iha ihb =>
      intro i hi
      rcases List.mem_append.mp hi with hi | hi
      · exact iha base fields.1 (by simp only [Block.size] at bound; omega) i hi
      · exact ihb (base + a.size) fields.2 (by simpa [Block.size, Nat.add_assoc] using bound) i hi
  | ifZero c zero nonzero ihz ihn =>
      simp only [Block.FieldsFit] at fields
      simp only [Block.size] at bound
      intro i hi
      simp only [Block.compileAt, List.mem_append, List.mem_singleton] at hi
      rcases hi with ((hi | hi) | hi) | hi
      · subst i
        exact branch_fits fields.1 (by omega)
      · exact ihn (base + 1) fields.2.2.2 (by omega) i hi
      · subst i
        exact jump_fits fields.2.1 (by omega)
      · exact ihz (base + 1 + nonzero.size + 1) fields.2.2.1 (by omega) i hi
  | «repeat» count body ih =>
      intro i hi
      simp only [Block.compileAt, List.mem_flatten, List.mem_map, List.mem_range] at hi
      obtain ⟨code, ⟨index, hindex, rfl⟩, hi⟩ := hi
      have hm := Nat.mul_le_mul_right body.size (Nat.succ_le_of_lt hindex)
      simp only [Nat.succ_mul] at hm
      apply ih (base + index * body.size) fields _ i hi
      simp only [Block.size] at bound
      omega

theorem Block.eval_stopped (memory : Memory) (block : Block) (s : Data)
    (h : s.status ≠ .running) : block.eval memory s = ⟨s, []⟩ := by
  cases block <;> cases hs : s.status <;> simp_all [Block.eval]

private theorem action_data (memory : Memory) (op : Action) (s : State) :
    Data.ofState (execute memory op.instruction s).1 =
      (op.eval memory (Data.ofState s)).final ∧
    (execute memory op.instruction s).2.toList =
      (op.eval memory (Data.ofState s)).reads ∧
    ((execute memory op.instruction s).1.status = .running →
      (execute memory op.instruction s).1.pc = s.pc + 1) := by
  cases op <;> simp [Action.instruction, Action.eval, execute, State.writeNext, Data.ofState]
  split <;> simp_all

/-- Exact primitive segment witnessing an independent source evaluation. -/
def Realizes (memory : Memory) (program : Program) (s : State)
    (expected : Evaluation) (finish budget : Nat) : Prop :=
  ∃ final transitions,
    RunsTo memory program s final transitions ∧
    Data.ofState final = expected.final ∧
    transitions.filterMap (·.receipt) = expected.reads ∧
    transitions.length ≤ budget ∧
    (final.status = .running → final.pc = finish)

private theorem realizes_stopped (memory : Memory) (program : Program) (s : State)
    (h : s.status ≠ .running) (finish budget : Nat) :
    Realizes memory program s ⟨Data.ofState s, []⟩ finish budget := by
  exact ⟨s, [], RunsTo.refl memory program s, rfl, rfl, Nat.zero_le _,
    fun hr => (h hr).elim⟩

private theorem realizes_mono {memory : Memory} {program : Program} {s : State}
    {expected : Evaluation} {finish a b : Nat}
    (h : Realizes memory program s expected finish a) (hab : a ≤ b) :
    Realizes memory program s expected finish b := by
  obtain ⟨final, ts, hx, hd, hr, hb, hp⟩ := h
  exact ⟨final, ts, hx, hd, hr, Nat.le_trans hb hab, hp⟩

def Evaluation.bind (first : Evaluation) (next : Data → Evaluation) : Evaluation :=
  let second := next first.final
  ⟨second.final, first.reads ++ second.reads⟩

private theorem Realizes.follow {memory : Memory} {program : Program} {s : State}
    {first : Evaluation} {next : Data → Evaluation} {middle finish a b : Nat}
    (hfirst : Realizes memory program s first middle a)
    (stopped : ∀ d, d.status ≠ .running → next d = ⟨d, []⟩)
    (hnext : ∀ t, t.pc = middle → Data.ofState t = first.final →
      t.status = .running → Realizes memory program t (next (Data.ofState t)) finish b) :
    Realizes memory program s (first.bind next) finish (a + b) := by
  obtain ⟨t, ts, hx, hd, hr, hb, hp⟩ := hfirst
  by_cases hs : t.status = .running
  · obtain ⟨u, us, hy, he, ht, hc, hq⟩ := hnext t (hp hs) hd hs
    refine ⟨u, ts ++ us, hx.trans hy, ?_, ?_, ?_, hq⟩
    · simpa [Evaluation.bind, ← hd] using he
    · simp only [List.filterMap_append, hr, ht, Evaluation.bind, ← hd]
    · simp only [List.length_append]
      omega
  · have hstop : next first.final = ⟨first.final, []⟩ := by
      rw [← hd]
      exact stopped _ hs
    refine ⟨t, ts, hx, ?_, ?_, by omega, fun h => (hs h).elim⟩
    · simpa [Evaluation.bind, hstop] using hd
    · simpa [Evaluation.bind, hstop] using hr

theorem Block.eval_seq (memory : Memory) (a b : Block) (s : Data) :
    (Block.seq a b).eval memory s = (a.eval memory s).bind (b.eval memory) := by
  by_cases hs : s.status = .running
  · simp only [Block.eval, hs, Evaluation.bind]
  · rw [Block.eval_stopped memory _ s hs, Block.eval_stopped memory a s hs]
    simp [Evaluation.bind, Block.eval_stopped memory b s hs]

private theorem iterate_stopped (memory : Memory) (body : Block) (count : Nat)
    (s : Data) (hs : s.status ≠ .running) :
    iterate (body.eval memory) count s = ⟨s, []⟩ := by
  induction count with
  | zero => rfl
  | succ count ih => simp [iterate, Block.eval_stopped memory body s hs, ih]

theorem Block.eval_repeat (memory : Memory) (body : Block) (count : Nat) (s : Data) :
    (Block.repeat count body).eval memory s = iterate (body.eval memory) count s := by
  by_cases hs : s.status = .running
  · simp [Block.eval, hs]
  · rw [Block.eval_stopped memory _ s hs, iterate_stopped memory body count s hs]

theorem Block.eval_repeat_succ (memory : Memory) (body : Block) (count : Nat)
    (s : Data) :
    (Block.repeat (count + 1) body).eval memory s =
      (body.eval memory s).bind ((Block.repeat count body).eval memory) := by
  simp [Block.eval_repeat, iterate, Evaluation.bind]

private theorem realizes_jump (memory : Memory) (program : Program) (s : State)
    (target : Nat) (hs : s.status = .running)
    (hf : program[s.pc]? = some (.jump target)) :
    Realizes memory program s ⟨Data.ofState s, []⟩ target 1 := by
  refine ⟨{ s with pc := target }, [⟨s, .jump target, { s with pc := target }, none⟩],
    RunsTo.instruction hs hf, rfl, rfl, Nat.le_refl _, fun _ => rfl⟩

private theorem realizes_branch (memory : Memory) (program : Program) (s : State)
    (condition target : Nat) (hs : s.status = .running)
    (hf : program[s.pc]? = some (.branchZero condition target)) :
    Realizes memory program s ⟨Data.ofState s, []⟩
      (if s.regs condition = 0 then target else s.pc + 1) 1 := by
  let t := { s with pc := if s.regs condition = 0 then target else s.pc + 1 }
  exact ⟨t, [⟨s, .branchZero condition target, t, none⟩],
    RunsTo.instruction hs hf, rfl, rfl, Nat.le_refl _, fun _ => rfl⟩

/-- Every structured block has an adequate exact primitive segment bounded by
its static compiled size, including initially or dynamically stopped states. -/
theorem Block.compile_realizes (memory : Memory) (program : Program) (block : Block)
    (base : Nat) (s : State) (hpc : s.pc = base)
    (host : HostedAt program base (block.compileAt base)) :
    Realizes memory program s (block.eval memory (Data.ofState s))
      (base + block.size) block.size := by
  induction block generalizing base s with
  | skip =>
      by_cases hs : s.status = .running
      · refine ⟨s, [], RunsTo.refl memory program s, ?_, ?_, Nat.le_refl _, ?_⟩
        · simp [Block.eval, Data.ofState, hs]
        · simp [Block.eval, Data.ofState, hs]
        · intro _; simpa [Block.size] using hpc
      · rw [Block.eval_stopped memory _ _ hs]
        exact realizes_stopped memory program s hs _ _
  | action op =>
      by_cases hs : s.status = .running
      · have hf : program[s.pc]? = some op.instruction := by
          rw [hpc]
          exact host.head
        obtain ⟨hd, hr, hp⟩ := action_data memory op s
        refine ⟨(execute memory op.instruction s).1,
          [⟨s, op.instruction, (execute memory op.instruction s).1,
            (execute memory op.instruction s).2⟩], RunsTo.instruction hs hf,
          ?_, ?_, Nat.le_refl _, ?_⟩
        · simpa only [Block.eval, Data.ofState, hs] using hd
        · simpa only [Block.eval, Data.ofState, hs, List.filterMap_cons,
            List.filterMap_nil] using hr
        · intro h
          simpa [Block.size, hpc] using hp h
      · rw [Block.eval_stopped memory _ _ hs]
        exact realizes_stopped memory program s hs _ _
  | exit src =>
      by_cases hs : s.status = .running
      · have hf : program[s.pc]? = some (.halt src) := by rw [hpc]; exact host.head
        refine ⟨{ s with status := .halted (s.regs src) },
          [⟨s, .halt src, { s with status := .halted (s.regs src) }, none⟩],
          RunsTo.instruction hs hf, ?_, ?_, Nat.le_refl _, ?_⟩
        · simp [Block.eval, Data.ofState, hs]
        · simp [Block.eval, Data.ofState, hs]
        · simp
      · rw [Block.eval_stopped memory _ _ hs]
        exact realizes_stopped memory program s hs _ _
  | seq first second ihf ihs =>
      have hf := ihf base s hpc host.append_left
      rw [Block.eval_seq]
      apply Realizes.follow hf (Block.eval_stopped memory second)
      intro t ht _ _
      have hh := ihs (base + first.size) t ht (by simpa using host.append_right)
      simpa [Block.size, Nat.add_assoc] using hh
  | ifZero condition zero nonzero ihz ihn =>
      by_cases hs : s.status = .running
      · have hbranch : program[s.pc]? =
            some (.branchZero condition (base + 1 + nonzero.size + 1)) := by
          rw [hpc]
          exact host.append_left.append_left.append_left.head
        have hn : HostedAt program (base + 1) (nonzero.compileAt (base + 1)) := by
          simpa using host.append_left.append_left.append_right
        have hj : HostedAt program (base + 1 + nonzero.size)
            [.jump (base + 1 + nonzero.size + 1 + zero.size)] := by
          simpa [Block.compileAt, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using host.append_left.append_right
        have hz : HostedAt program (base + 1 + nonzero.size + 1)
            (zero.compileAt (base + 1 + nonzero.size + 1)) := by
          simpa [Block.compileAt, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using host.append_right
        have hb := realizes_branch memory program s condition
          (base + 1 + nonzero.size + 1) hs hbranch
        by_cases hc : s.regs condition = 0
        · simp only [hc, if_true] at hb
          have hzero := Realizes.follow hb (Block.eval_stopped memory zero)
            (fun t ht _ _ => ihz _ t ht hz)
          have hh : (⟨Data.ofState s, []⟩ : Evaluation).bind (zero.eval memory) =
              (Block.ifZero condition zero nonzero).eval memory (Data.ofState s) := by
            simp [Evaluation.bind, Block.eval, Data.ofState, hs, hc]
          rw [hh] at hzero
          have hend : base + 1 + nonzero.size + 1 + zero.size =
              base + (Block.ifZero condition zero nonzero).size := by simp [Block.size]; omega
          rw [hend] at hzero
          exact realizes_mono hzero (by simp [Block.size] <;> omega)
        · simp only [hc, if_false, hpc] at hb
          have hnonzero := Realizes.follow hb (Block.eval_stopped memory nonzero)
            (fun t ht _ _ => ihn _ t ht hn)
          have hall := Realizes.follow hnonzero
            (next := fun d => ⟨d, []⟩) (finish := base + 1 + nonzero.size + 1 + zero.size)
            (b := 1) (fun _ _ => rfl) (by
              intro t ht _ hstatus
              apply realizes_jump memory program t _ hstatus
              rw [ht]
              exact hj.head)
          have hh : ((⟨Data.ofState s, []⟩ : Evaluation).bind (nonzero.eval memory)).bind
              (fun d => ⟨d, []⟩) =
              (Block.ifZero condition zero nonzero).eval memory (Data.ofState s) := by
            simp [Evaluation.bind, Block.eval, Data.ofState, hs, hc]
          rw [hh] at hall
          have hend : base + 1 + nonzero.size + 1 + zero.size =
              base + (Block.ifZero condition zero nonzero).size := by simp [Block.size]; omega
          rw [hend] at hall
          exact realizes_mono hall (by simp [Block.size] <;> omega)
      · rw [Block.eval_stopped memory _ _ hs]
        exact realizes_stopped memory program s hs _ _
  | «repeat» count body ih =>
      induction count generalizing base s with
      | zero =>
          rw [Block.eval_repeat]
          refine ⟨s, [], RunsTo.refl memory program s, rfl, rfl, by simp [Block.size], ?_⟩
          intro _; simpa [Block.size] using hpc
      | succ count ihc =>
          rw [Block.compile_repeat_succ] at host
          have first := ih base s hpc host.append_left
          rw [Block.eval_repeat_succ]
          have all := Realizes.follow first
            (Block.eval_stopped memory (Block.repeat count body)) (by
              intro t ht _ _
              apply ihc (base + body.size) t ht
              simpa using host.append_right)
          simpa [Block.size, Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using all

/-- Public adequacy theorem: fuel is existentially derived, never assumed. -/
theorem Block.compile_correct (memory : Memory) (program : Program) (block : Block)
    (base : Nat) (s : State) (hpc : s.pc = base)
    (host : HostedAt program base (block.compileAt base)) :
    ∃ used, used ≤ block.size ∧
      Data.ofState (run memory program used s).final =
        (block.eval memory (Data.ofState s)).final ∧
      (run memory program used s).reads = (block.eval memory (Data.ofState s)).reads ∧
      (run memory program used s).steps = used ∧
      ((run memory program used s).final.status = .running →
        (run memory program used s).final.pc = base + block.size) := by
  obtain ⟨final, ts, hx, hd, hr, hb, hp⟩ := block.compile_realizes memory program base s hpc host
  refine ⟨ts.length, hb, ?_⟩
  unfold RunsTo at hx
  rw [hx]
  exact ⟨hd, hr, rfl, hp⟩

private theorem run_extend_stopped (memory : Memory) (program : Program)
    (s : State) (used budget : Nat) (hbound : used ≤ budget)
    (hstop : step memory program (run memory program used s).final = none) :
    run memory program budget s = run memory program used s := by
  rw [← Nat.add_sub_of_le hbound, run_add]
  dsimp only
  rw [run_of_step_none memory program _ _ hstop]
  simp

/-- Standalone code is adequate at its full fixed syntax-derived budget.
Normal completion reaches the first address after the code; halted and faulted
executions remain stopped. No adequacy or successful-load premise is needed. -/
theorem Block.compile_run (memory : Memory) (block : Block) (s : State)
    (hpc : s.pc = 0) :
    Data.ofState (run memory (block.compileAt 0) block.size s).final =
      (block.eval memory (Data.ofState s)).final ∧
    (run memory (block.compileAt 0) block.size s).reads =
      (block.eval memory (Data.ofState s)).reads ∧
    (run memory (block.compileAt 0) block.size s).steps ≤ block.size ∧
    ((run memory (block.compileAt 0) block.size s).final.status = .running →
      (run memory (block.compileAt 0) block.size s).final.pc = block.size) := by
  obtain ⟨used, hbound, hd, hr, hc, hp⟩ :=
    block.compile_correct memory (block.compileAt 0) 0 s hpc (HostedAt.self _)
  have hs : step memory (block.compileAt 0)
      (run memory (block.compileAt 0) used s).final = none := by
    cases hstatus : (run memory (block.compileAt 0) used s).final.status with
    | running =>
        have hf : (block.compileAt 0)[(run memory (block.compileAt 0) used s).final.pc]? = none := by
          rw [hp hstatus]
          apply List.getElem?_eq_none
          simp
        simp [step, hstatus, hf]
    | halted value => simp [step, hstatus]
    | fault => simp [step, hstatus]
  rw [run_extend_stopped memory (block.compileAt 0) s used block.size hbound hs]
  exact ⟨hd, hr, by omega, by simpa using hp⟩

def Data.result (s : Data) : Option Nat :=
  match s.status with
  | .halted value => some value
  | _ => none

private theorem exit_reads (memory : Memory) (output : Nat) (s : Data) :
    ((Block.exit output).eval memory s).reads = [] := by
  cases hs : s.status <;> simp [Block.eval, hs]

/-- Appending a halt yields the source output, preserving an earlier halt/fault.
The budget is the literal compiled program length, derived from fixed syntax. -/
theorem Block.compile_with_halt (memory : Memory) (block : Block) (output : Nat)
    (s : State) (hpc : s.pc = 0) :
    let source := block.eval memory (Data.ofState s)
    let program := block.compileAt 0 ++ [Instruction.halt output]
    let actual := run memory program (block.size + 1) s
    Data.ofState actual.final = ((Block.exit output).eval memory source.final).final ∧
    actual.result = (match source.final.status with
      | .running => some (source.final.regs output)
      | .halted value => some value
      | .fault => none) ∧
    actual.reads = source.reads ∧ actual.steps ≤ program.length := by
  dsimp only
  have hh := (Block.seq block (.exit output)).compile_run memory s hpc
  have hd : Data.ofState (run memory (block.compileAt 0 ++ [.halt output])
      (block.size + 1) s).final =
      ((Block.exit output).eval memory (block.eval memory (Data.ofState s)).final).final := by
    simpa [Block.compileAt, Block.size, Block.eval_seq, Evaluation.bind] using hh.1
  refine ⟨hd, ?_, ?_, ?_⟩
  · change (Data.ofState (run memory (block.compileAt 0 ++ [.halt output])
      (block.size + 1) s).final).result = _
    rw [hd]
    cases hs : (block.eval memory (Data.ofState s)).final.status <;>
      simp [Data.result, Block.eval, hs]
  · simpa [Block.compileAt, Block.size, Block.eval_seq, Evaluation.bind, exit_reads]
      using hh.2.1
  · simpa [Block.compileAt, Block.size] using hh.2.2.1

namespace CompilerConsumers

/-- This full expected type does not adapt to the current theorem declaration. -/
theorem compile_correct_expectedType (memory : Memory) (program : Program) (block : Block)
    (base : Nat) (s : State) (hpc : s.pc = base)
    (host : HostedAt program base (block.compileAt base)) :
    ∃ used, used ≤ block.size ∧
      Data.ofState (run memory program used s).final =
        (block.eval memory (Data.ofState s)).final ∧
      (run memory program used s).reads = (block.eval memory (Data.ofState s)).reads ∧
      (run memory program used s).steps = used ∧
      ((run memory program used s).final.status = .running →
        (run memory program used s).final.pc = base + block.size) :=
  block.compile_correct memory program base s hpc host

theorem compile_fits_expectedType (block : Block) (width base : Nat)
    (fields : block.FieldsFit width) (bound : base + block.size < 2 ^ width) :
    ∀ instruction ∈ block.compileAt base, instruction.Fits width :=
  block.compile_fits width base fields bound

theorem compile_with_halt_expectedType (memory : Memory) (block : Block) (output : Nat)
    (s : State) (hpc : s.pc = 0) :
    let source := block.eval memory (Data.ofState s)
    let program := block.compileAt 0 ++ [Instruction.halt output]
    let actual := run memory program (block.size + 1) s
    Data.ofState actual.final = ((Block.exit output).eval memory source.final).final ∧
    actual.result = (match source.final.status with
      | .running => some (source.final.regs output)
      | .halted value => some value
      | .fault => none) ∧
    actual.reads = source.reads ∧ actual.steps ≤ program.length :=
  block.compile_with_halt memory output s hpc

def initial : State := ⟨fun _ => 0, 0, .running⟩
def executeWithHalt (memory : Memory) (block : Block) (output : Nat) (s : State) : Run :=
  run memory (block.compileAt 0 ++ [.halt output]) (block.size + 1) s

def overwrittenOperand : Block :=
  .seq (.action (.constant 1 4)) (.action (.arithmetic .add 1 1 1))

theorem overwrittenOperand_result :
    (executeWithHalt [] overwrittenOperand 1 initial).result = some 8 :=
  (overwrittenOperand.compile_with_halt [] 1 initial rfl).2.1

def branchOverwrite : Block :=
  .ifZero 0 (.action (.constant 0 9)) (.action (.constant 0 8))

theorem zero_branch :
    (executeWithHalt [] branchOverwrite 0 initial).result = some 9 ∧
    (executeWithHalt [] branchOverwrite 0 initial).steps = 3 :=
  ⟨(branchOverwrite.compile_with_halt [] 0 initial rfl).2.1, rfl⟩

def nonzeroInitial : State := { initial with regs := initial.regs.write 0 3 }

theorem nonzero_branch :
    (executeWithHalt [] branchOverwrite 0 nonzeroInitial).result = some 8 ∧
    (executeWithHalt [] branchOverwrite 0 nonzeroInitial).steps = 4 :=
  ⟨(branchOverwrite.compile_with_halt [] 0 nonzeroInitial rfl).2.1, rfl⟩

theorem empty_branches :
    (executeWithHalt [] (.ifZero 0 .skip .skip) 0 initial).steps = 2 ∧
    (executeWithHalt [] (.ifZero 0 .skip .skip) 0 nonzeroInitial).steps = 3 :=
  ⟨rfl, rfl⟩

theorem repeat_zero :
    (executeWithHalt [] (.repeat 0 (.exit 1)) 0 nonzeroInitial).result = some 3 ∧
    (executeWithHalt [] (.repeat 0 (.exit 1)) 0 nonzeroInitial).steps = 1 :=
  ⟨((Block.repeat 0 (.exit 1)).compile_with_halt [] 0 nonzeroInitial rfl).2.1, rfl⟩

theorem repeat_empty :
    Data.ofState (run [] ((Block.repeat 3 .skip).compileAt 0)
      (Block.repeat 3 .skip).size initial).final = Data.ofState initial ∧
    (run [] ((Block.repeat 3 .skip).compileAt 0)
      (Block.repeat 3 .skip).size initial).steps = 0 :=
  ⟨((Block.repeat 3 .skip).compile_run [] initial rfl).1, rfl⟩

def repeatedLoad : Block := .repeat 3 (.action (.load 1 0))

theorem repeated_receipts :
    (executeWithHalt [7] repeatedLoad 1 initial).result = some 7 ∧
    (executeWithHalt [7] repeatedLoad 1 initial).reads =
      [⟨0, some 7⟩, ⟨0, some 7⟩, ⟨0, some 7⟩] ∧
    (executeWithHalt [7] repeatedLoad 1 initial).steps = 4 :=
  ⟨(repeatedLoad.compile_with_halt [7] 1 initial rfl).2.1,
    (repeatedLoad.compile_with_halt [7] 1 initial rfl).2.2.1, rfl⟩

def failingRepeat : Block :=
  .repeat 3 (.seq (.action (.load 1 0)) (.action (.constant 1 999)))

theorem missing_load_termination :
    (executeWithHalt [] failingRepeat 1 initial).result = none ∧
    (executeWithHalt [] failingRepeat 1 initial).final.status = .fault ∧
    (executeWithHalt [] failingRepeat 1 initial).reads = [⟨0, none⟩] ∧
    (executeWithHalt [] failingRepeat 1 initial).steps = 1 :=
  ⟨(failingRepeat.compile_with_halt [] 1 initial rfl).2.1, rfl,
    (failingRepeat.compile_with_halt [] 1 initial rfl).2.2.1, rfl⟩

theorem early_exit :
    (executeWithHalt [] (.seq (.exit 0) (.action (.load 1 0))) 1 nonzeroInitial).result = some 3 ∧
    (executeWithHalt [] (.seq (.exit 0) (.action (.load 1 0))) 1 nonzeroInitial).reads = [] ∧
    (executeWithHalt [] (.seq (.exit 0) (.action (.load 1 0))) 1 nonzeroInitial).steps = 1 :=
  ⟨((Block.seq (.exit 0) (.action (.load 1 0))).compile_with_halt [] 1 nonzeroInitial rfl).2.1,
    ((Block.seq (.exit 0) (.action (.load 1 0))).compile_with_halt [] 1 nonzeroInitial rfl).2.2.1,
    rfl⟩

theorem initially_halted :
    (executeWithHalt [] overwrittenOperand 1 { initial with status := .halted 42 }).result = some 42 ∧
    (executeWithHalt [] overwrittenOperand 1 { initial with status := .halted 42 }).steps = 0 :=
  ⟨(overwrittenOperand.compile_with_halt [] 1 { initial with status := .halted 42 } rfl).2.1,
    rfl⟩

theorem initially_faulted :
    (executeWithHalt [] overwrittenOperand 1 { initial with status := .fault }).result = none ∧
    (executeWithHalt [] overwrittenOperand 1 { initial with status := .fault }).steps = 0 :=
  ⟨(overwrittenOperand.compile_with_halt [] 1 { initial with status := .fault } rfl).2.1, rfl⟩

theorem branch_code_fits :
    ∀ instruction ∈ branchOverwrite.compileAt 0, instruction.Fits 4 := by
  apply compile_fits_expectedType
  · simp [branchOverwrite, Block.FieldsFit, Action.instruction, Instruction.Fits,
      Instruction.encoding, Instruction.operands]
  · decide

/-- The exit serialization tag is not silently exempted at tiny widths. -/
theorem tiny_exit_rejected : ¬ (Block.exit 0).FieldsFit 1 := by
  simp [Block.FieldsFit, Instruction.Fits, Instruction.encoding, Instruction.operands]

/-- A dormant branch's operand is still a code-width obligation. -/
theorem dormant_branch_rejected :
    ¬ (Block.ifZero 0 .skip (.exit 8)).FieldsFit 3 := by
  simp [Block.FieldsFit, Instruction.Fits, Instruction.encoding, Instruction.operands]

/-- Arithmetic subtags, as well as register operands, are encoded fields. -/
theorem arithmetic_tag_rejected :
    ¬ (Block.action (.arithmetic .bxor 0 0 0)).FieldsFit 3 := by
  simp [Block.FieldsFit, Action.instruction, Instruction.Fits, Instruction.encoding,
    Instruction.operands, Arithmetic.code]

end CompilerConsumers

end RMQ.SuccinctFinal.PackedWordRAM.Structured
