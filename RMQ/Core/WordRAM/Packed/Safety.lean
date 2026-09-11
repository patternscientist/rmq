import RMQ.Core.WordRAM.Packed.Compiler

/-!
# Runtime word safety of compiled structured assembly

The source judgment inspects actual scalar operands and source-evaluated
intermediate states. It is independent of compiled execution. The compiler
preservation theorem carries these obligations to the same primitive run as
the value, ordered-read and instruction-budget conclusions.
-/

namespace RMQ.SuccinctFinal.PackedWordRAM.Structured

def Data.Fits (width : Nat) (s : Data) : Prop :=
  (∀ r, s.regs r < 2 ^ width) ∧
  (∀ value, s.status = .halted value → value < 2 ^ width)

theorem state_fits_iff_data (width : Nat) (s : State) :
    s.Fits width ↔ s.pc < 2 ^ width ∧ (Data.ofState s).Fits width := Iff.rfl

/-- Scalar safety uses actual evaluated values, including the actual load reply.
No overflowing result is truncated to satisfy the predicate. -/
def Action.LocalSafe (memory : Memory) (width : Nat) (op : Action) (s : Data) : Prop :=
  match op with
  | .load _ address => ∀ value, memory[s.regs address]? = some value → value < 2 ^ width
  | .constant _ value => value < 2 ^ width
  | .move _ src => s.regs src < 2 ^ width
  | .arithmetic op _ lhs rhs =>
      op.eval (s.regs lhs) (s.regs rhs) < 2 ^ width ∧
      (op = .sub → s.regs rhs ≤ s.regs lhs) ∧
      (op = .div ∨ op = .mod → 0 < s.regs rhs) ∧
      (op = .shl ∨ op = .shr → s.regs rhs < width)
  | .comparison op _ lhs rhs => op.eval (s.regs lhs) (s.regs rhs) < 2 ^ width

/-- Each fixed iteration is checked at the data produced by its predecessors. -/
def IterationsSafe (safe : Data → Prop) (body : Data → Evaluation) : Nat → Data → Prop
  | 0, _ => True
  | count + 1, s => safe s ∧ IterationsSafe safe body count (body s).final

/-- Entry data always fit. Only actually entered operations/selected branches
have local operation obligations; stopped source evaluations are identities. -/
def Block.Safe (memory : Memory) (width : Nat) (block : Block) (s : Data) : Prop :=
  s.Fits width ∧ (s.status = .running →
    match block with
    | .skip => True
    | .action op => op.LocalSafe memory width s
    | .exit src => s.regs src < 2 ^ width
    | .seq first second => first.Safe memory width s ∧
        second.Safe memory width (first.eval memory s).final
    | .ifZero condition zero nonzero =>
        if s.regs condition = 0 then zero.Safe memory width s else nonzero.Safe memory width s
    | .repeat count body => IterationsSafe (body.Safe memory width) (body.eval memory) count s)

theorem Block.safe_data (memory : Memory) (width : Nat) (block : Block) (s : Data)
    (safe : block.Safe memory width s) : s.Fits width := by
  cases block <;> exact safe.1

theorem Block.safe_stopped (memory : Memory) (width : Nat) (block : Block) (s : Data)
    (fit : s.Fits width) (stopped : s.status ≠ .running) : block.Safe memory width s :=
  by cases block <;> exact ⟨fit, fun h => (stopped h).elim⟩

theorem Block.safe_skip (memory : Memory) (width : Nat) (s : Data) (fit : s.Fits width) :
    Block.skip.Safe memory width s := ⟨fit, fun _ => trivial⟩

theorem Block.safe_action (memory : Memory) (width : Nat) (op : Action) (s : Data)
    (fit : s.Fits width) (safe : op.LocalSafe memory width s) :
    (Block.action op).Safe memory width s := ⟨fit, fun _ => safe⟩

theorem Block.safe_exit (memory : Memory) (width output : Nat) (s : Data)
    (fit : s.Fits width) : (Block.exit output).Safe memory width s :=
  ⟨fit, fun _ => fit.1 output⟩

theorem Block.safe_seq {memory : Memory} {width : Nat} {first second : Block} {s : Data}
    (hfirst : first.Safe memory width s)
    (hsecond : second.Safe memory width (first.eval memory s).final) :
    (Block.seq first second).Safe memory width s :=
  ⟨first.safe_data memory width s hfirst, fun _ => ⟨hfirst, hsecond⟩⟩

theorem Block.safe_ifZero {memory : Memory} {width condition : Nat} {zero nonzero : Block}
    {s : Data} (fit : s.Fits width)
    (arms : if s.regs condition = 0 then zero.Safe memory width s else nonzero.Safe memory width s) :
    (Block.ifZero condition zero nonzero).Safe memory width s := ⟨fit, fun _ => arms⟩

theorem Block.safe_repeat {memory : Memory} {width count : Nat} {body : Block} {s : Data}
    (fit : s.Fits width)
    (iterations : IterationsSafe (body.Safe memory width) (body.eval memory) count s) :
    (Block.repeat count body).Safe memory width s := ⟨fit, fun _ => iterations⟩

theorem IterationsSafe.zero (safe : Data → Prop) (body : Data → Evaluation) (s : Data) :
    IterationsSafe safe body 0 s := trivial

theorem IterationsSafe.succ {safe : Data → Prop} {body : Data → Evaluation}
    {count : Nat} {s : Data} (head : safe s)
    (tail : IterationsSafe safe body count (body s).final) :
    IterationsSafe safe body (count + 1) s := ⟨head, tail⟩

theorem IterationsSafe.at {safe : Data → Prop} {body : Data → Evaluation}
    {count : Nat} {s : Data} (h : IterationsSafe safe body count s)
    (index : Nat) (hi : index < count) : safe (iterate body index s).final := by
  induction count generalizing s index with
  | zero => omega
  | succ count ih =>
      cases index with
      | zero => exact h.1
      | succ index =>
          simpa [iterate] using ih h.2 index (by omega)

theorem IterationsSafe.of_invariant (safe invariant : Data → Prop) (body : Data → Evaluation)
    (step : ∀ s, invariant s → safe s ∧ invariant (body s).final)
    (count : Nat) (s : Data) (hs : invariant s) : IterationsSafe safe body count s := by
  induction count generalizing s with
  | zero => trivial
  | succ count ih => exact ⟨(step s hs).1, ih _ (step s hs).2⟩

private theorem data_write_fits (width : Nat) (s : Data) (dst value : Nat)
    (fit : s.Fits width) (hv : value < 2 ^ width) :
    (⟨s.regs.write dst value, .running⟩ : Data).Fits width := by
  constructor
  · intro r
    by_cases h : r = dst
    · simpa [Registers.write, h] using hv
    · simpa [Registers.write, h] using fit.1 r
  · intro value h
    cases h

theorem Action.eval_fits (memory : Memory) (width : Nat) (op : Action) (s : Data)
    (fit : s.Fits width) (safe : op.LocalSafe memory width s) :
    (op.eval memory s).final.Fits width := by
  cases op with
  | load dst address =>
      cases hr : memory[s.regs address]? with
      | none =>
          simp only [Action.eval, Action.instruction, execute, hr, Data.ofState]
          exact ⟨fit.1, fun _ h => Status.noConfusion h⟩
      | some value =>
          simpa [Action.eval, Action.instruction, execute, hr, Data.ofState, State.writeNext]
            using data_write_fits width s dst value fit (safe value hr)
  | constant dst value =>
      exact data_write_fits width s dst value fit safe
  | move dst src =>
      exact data_write_fits width s dst (s.regs src) fit safe
  | arithmetic op dst lhs rhs =>
      exact data_write_fits width s dst _ fit safe.1
  | comparison op dst lhs rhs =>
      exact data_write_fits width s dst _ fit safe

private theorem iterate_fits (width : Nat) (safe : Data → Prop) (body : Data → Evaluation)
    (preserves : ∀ s, safe s → (body s).final.Fits width) (count : Nat) (s : Data)
    (fit : s.Fits width) (h : IterationsSafe safe body count s) :
    (iterate body count s).final.Fits width := by
  induction count generalizing s with
  | zero => exact fit
  | succ count ih =>
      exact ih _ (preserves s h.1) h.2

theorem Block.eval_fits (memory : Memory) (width : Nat) (block : Block) (s : Data)
    (safe : block.Safe memory width s) : (block.eval memory s).final.Fits width := by
  induction block generalizing s with
  | skip =>
      by_cases hs : s.status = .running
      · simpa [Block.eval, hs] using safe.1
      · simpa [Block.eval_stopped memory _ s hs] using safe.1
  | action op =>
      by_cases hs : s.status = .running
      · simpa only [Block.eval, hs] using op.eval_fits memory width s safe.1 (safe.2 hs)
      · simpa [Block.eval_stopped memory _ s hs] using safe.1
  | exit src =>
      by_cases hs : s.status = .running
      · simp only [Block.eval, hs]
        exact ⟨safe.1.1, fun value hv => by cases hv; exact safe.1.1 src⟩
      · simpa [Block.eval_stopped memory _ s hs] using safe.1
  | seq first second ihf ihs =>
      by_cases hs : s.status = .running
      · simpa [Block.eval_seq, Evaluation.bind] using ihs _ (safe.2 hs).2
      · simpa [Block.eval_stopped memory _ s hs] using safe.1
  | ifZero condition zero nonzero ihz ihn =>
      by_cases hs : s.status = .running
      · have ha := safe.2 hs
        by_cases hc : s.regs condition = 0
        · simpa [Block.eval, hs, hc] using ihz s (by simpa [hc] using ha)
        · simpa [Block.eval, hs, hc] using ihn s (by simpa [hc] using ha)
      · simpa [Block.eval_stopped memory _ s hs] using safe.1
  | «repeat» count body ih =>
      rw [Block.eval_repeat]
      by_cases hs : s.status = .running
      · exact iterate_fits width (body.Safe memory width) (body.eval memory) ih count s
          safe.1 (safe.2 hs)
      · have he := (Block.repeat count body).eval_stopped memory s hs
        rw [Block.eval_repeat] at he
        simpa [he] using safe.1

private theorem state_write_fits (width : Nat) (s : State) (dst value : Nat)
    (fit : s.Fits width) (hv : value < 2 ^ width) (hp : s.pc + 1 < 2 ^ width) :
    (s.writeNext dst value).Fits width :=
  ⟨hp, data_write_fits width (Data.ofState s) dst value fit.2 hv⟩

theorem Action.execute_safe (memory : Memory) (width : Nat) (op : Action) (s : State)
    (fit : s.Fits width) (fields : op.instruction.Fits width)
    (safe : op.LocalSafe memory width (Data.ofState s)) (pc : s.pc + 1 < 2 ^ width) :
    Instruction.Safe width s op.instruction ∧ (execute memory op.instruction s).1.Fits width := by
  constructor
  · refine ⟨fields, fit, ?_⟩
    cases op <;> first | exact safe | trivial
  · cases op with
    | load dst address =>
        cases hr : memory[s.regs address]? with
        | none =>
            simp only [Action.instruction, execute, hr]
            exact ⟨fit.1, fit.2.1, fun _ h => Status.noConfusion h⟩
        | some value =>
            simp only [Action.instruction, execute, hr]
            exact state_write_fits width s dst value fit (safe value hr) pc
    | constant dst value => exact state_write_fits width s dst value fit safe pc
    | move dst src => exact state_write_fits width s dst (s.regs src) fit safe pc
    | arithmetic op dst lhs rhs => exact state_write_fits width s dst _ fit safe.1 pc
    | comparison op dst lhs rhs => exact state_write_fits width s dst _ fit safe pc

def TraceSafe (width : Nat) (transitions : List Transition) : Prop :=
  ∀ t ∈ transitions, Instruction.Safe width t.before t.instruction ∧ t.after.Fits width

private theorem traceSafe_append {width : Nat} {a b : List Transition}
    (ha : TraceSafe width a) (hb : TraceSafe width b) : TraceSafe width (a ++ b) := by
  intro t ht
  rcases List.mem_append.mp ht with ht | ht
  · exact ha t ht
  · exact hb t ht

theorem run_prefix_fits (memory : Memory) (program : Program) (width fuel : Nat)
    (s : State) (fit : s.Fits width)
    (safe : TraceSafe width (run memory program fuel s).transitions) :
    ∀ index, index ≤ fuel → (run memory program index s).final.Fits width := by
  induction fuel generalizing s with
  | zero =>
      intro index hi
      have : index = 0 := by omega
      subst index
      exact fit
  | succ fuel ih =>
      intro index hi
      cases hs : step memory program s with
      | none => rw [run_of_step_none memory program s index hs]; exact fit
      | some t =>
          have hhead : Instruction.Safe width t.before t.instruction ∧ t.after.Fits width :=
            safe t (by simp [run, hs])
          have htail : TraceSafe width (run memory program fuel t.after).transitions := by
            intro u hu
            exact safe u (by simp [run, hs, hu])
          cases index with
          | zero => exact fit
          | succ index => simpa [run, hs] using ih t.after hhead.2 htail index (by omega)

/-- A strengthened exact primitive segment; observations remain proof fields. -/
def SafeRealizes (width : Nat) (memory : Memory) (program : Program) (s : State)
    (expected : Evaluation) (finish budget : Nat) : Prop :=
  ∃ final transitions,
    RunsTo memory program s final transitions ∧
    Data.ofState final = expected.final ∧
    transitions.filterMap (·.receipt) = expected.reads ∧
    transitions.length ≤ budget ∧
    (final.status = .running → final.pc = finish) ∧
    final.Fits width ∧ TraceSafe width transitions

private theorem safeRealizes_stopped (width : Nat) (memory : Memory) (program : Program)
    (s : State) (fit : s.Fits width) (h : s.status ≠ .running) (finish budget : Nat) :
    SafeRealizes width memory program s ⟨Data.ofState s, []⟩ finish budget := by
  exact ⟨s, [], RunsTo.refl memory program s, rfl, rfl, Nat.zero_le _,
    fun hr => (h hr).elim, fit, fun _ ht => (List.not_mem_nil ht).elim⟩

private theorem safeRealizes_mono {width : Nat} {memory : Memory} {program : Program}
    {s : State} {expected : Evaluation} {finish a b : Nat}
    (h : SafeRealizes width memory program s expected finish a) (hab : a ≤ b) :
    SafeRealizes width memory program s expected finish b := by
  obtain ⟨final, ts, hx, hd, hr, hb, hp, hf, ht⟩ := h
  exact ⟨final, ts, hx, hd, hr, Nat.le_trans hb hab, hp, hf, ht⟩

private theorem SafeRealizes.follow {width : Nat} {memory : Memory} {program : Program}
    {s : State} {first : Evaluation} {next : Data → Evaluation} {middle finish a b : Nat}
    (hfirst : SafeRealizes width memory program s first middle a)
    (stopped : ∀ d, d.status ≠ .running → next d = ⟨d, []⟩)
    (hnext : ∀ t, t.pc = middle → Data.ofState t = first.final →
      t.status = .running → t.Fits width →
      SafeRealizes width memory program t (next (Data.ofState t)) finish b) :
    SafeRealizes width memory program s (first.bind next) finish (a + b) := by
  obtain ⟨t, ts, hx, hd, hr, hb, hp, hfit, htrace⟩ := hfirst
  by_cases hs : t.status = .running
  · obtain ⟨u, us, hy, he, ht, hc, hq, hufit, hut⟩ := hnext t (hp hs) hd hs hfit
    refine ⟨u, ts ++ us, hx.trans hy, ?_, ?_, ?_, hq, hufit,
      traceSafe_append htrace hut⟩
    · simpa [Evaluation.bind, ← hd] using he
    · simp only [List.filterMap_append, hr, ht, Evaluation.bind, ← hd]
    · simp only [List.length_append]; omega
  · have hstop : next first.final = ⟨first.final, []⟩ := by
      rw [← hd]
      exact stopped _ hs
    refine ⟨t, ts, hx, ?_, ?_, by omega, fun h => (hs h).elim, hfit, htrace⟩
    · simpa [Evaluation.bind, hstop] using hd
    · simpa [Evaluation.bind, hstop] using hr

private theorem action_data (memory : Memory) (op : Action) (s : State) :
    Data.ofState (execute memory op.instruction s).1 =
      (op.eval memory (Data.ofState s)).final ∧
    (execute memory op.instruction s).2.toList =
      (op.eval memory (Data.ofState s)).reads ∧
    ((execute memory op.instruction s).1.status = .running →
      (execute memory op.instruction s).1.pc = s.pc + 1) := by
  cases op <;> simp [Action.instruction, Action.eval, execute, State.writeNext, Data.ofState]
  split <;> simp_all

private theorem safeRealizes_jump (width : Nat) (memory : Memory) (program : Program)
    (s : State) (target : Nat) (fit : s.Fits width) (hs : s.status = .running)
    (fields : (Instruction.jump 0).Fits width) (bound : target < 2 ^ width)
    (hf : program[s.pc]? = some (.jump target)) :
    SafeRealizes width memory program s ⟨Data.ofState s, []⟩ target 1 := by
  have hj : (Instruction.jump target).Fits width := by
    simp [Instruction.Fits, Instruction.encoding, Instruction.operands] at fields ⊢
    exact ⟨fields.1, bound⟩
  have hfit : ({ s with pc := target } : State).Fits width := ⟨bound, fit.2⟩
  refine ⟨{ s with pc := target }, [⟨s, .jump target, { s with pc := target }, none⟩],
    RunsTo.instruction hs hf, rfl, rfl, Nat.le_refl _, fun _ => rfl, hfit, ?_⟩
  intro t ht
  have he := List.mem_singleton.mp ht
  subst t
  exact ⟨⟨hj, fit, trivial⟩, hfit⟩

private theorem safeRealizes_branch (width : Nat) (memory : Memory) (program : Program)
    (s : State) (condition target : Nat) (fit : s.Fits width) (hs : s.status = .running)
    (fields : (Instruction.branchZero condition 0).Fits width)
    (targetBound : target < 2 ^ width) (nextBound : s.pc + 1 < 2 ^ width)
    (hf : program[s.pc]? = some (.branchZero condition target)) :
    SafeRealizes width memory program s ⟨Data.ofState s, []⟩
      (if s.regs condition = 0 then target else s.pc + 1) 1 := by
  have hb : (Instruction.branchZero condition target).Fits width := by
    simp [Instruction.Fits, Instruction.encoding, Instruction.operands] at fields ⊢
    exact ⟨fields.1, fields.2.1, targetBound⟩
  let u := { s with pc := if s.regs condition = 0 then target else s.pc + 1 }
  have hfit : u.Fits width := by
    refine ⟨?_, fit.2⟩
    dsimp [u]
    split <;> assumption
  refine ⟨u, [⟨s, .branchZero condition target, u, none⟩],
    RunsTo.instruction hs hf, rfl, rfl, Nat.le_refl _, fun _ => rfl, hfit, ?_⟩
  intro t ht
  have he := List.mem_singleton.mp ht
  subst t
  exact ⟨⟨hb, fit, trivial⟩, hfit⟩

/-- Local source safety is consumed by the exact primitive compilation proof. -/
theorem Block.compile_safe_realizes (memory : Memory) (program : Program) (width : Nat)
    (block : Block) (base : Nat) (s : State) (hpc : s.pc = base)
    (host : HostedAt program base (block.compileAt base))
    (fields : block.FieldsFit width) (bound : base + block.size < 2 ^ width)
    (fit : s.Fits width) (safe : block.Safe memory width (Data.ofState s)) :
    SafeRealizes width memory program s (block.eval memory (Data.ofState s))
      (base + block.size) block.size := by
  induction block generalizing base s with
  | skip =>
      by_cases hs : s.status = .running
      · refine ⟨s, [], RunsTo.refl memory program s, ?_, ?_, Nat.le_refl _, ?_, fit, ?_⟩
        · simp [Block.eval, Data.ofState, hs]
        · simp [Block.eval, Data.ofState, hs]
        · intro _; simpa [Block.size] using hpc
        · intro _ ht; exact (List.not_mem_nil ht).elim
      · rw [Block.eval_stopped memory _ _ hs]
        exact safeRealizes_stopped width memory program s fit hs _ _
  | action op =>
      by_cases hs : s.status = .running
      · have hf : program[s.pc]? = some op.instruction := by rw [hpc]; exact host.head
        obtain ⟨hd, hr, hp⟩ := action_data memory op s
        obtain ⟨hisafe, afterfit⟩ := op.execute_safe memory width s fit fields (safe.2 hs)
          (by simpa [hpc, Block.size] using bound)
        refine ⟨(execute memory op.instruction s).1,
          [⟨s, op.instruction, (execute memory op.instruction s).1,
            (execute memory op.instruction s).2⟩], RunsTo.instruction hs hf,
          ?_, ?_, Nat.le_refl _, ?_, afterfit, ?_⟩
        · simpa only [Block.eval, Data.ofState, hs] using hd
        · simpa only [Block.eval, Data.ofState, hs, List.filterMap_cons,
            List.filterMap_nil] using hr
        · intro h; simpa [Block.size, hpc] using hp h
        · intro t ht; have he := List.mem_singleton.mp ht; subst t
          exact ⟨hisafe, afterfit⟩
      · rw [Block.eval_stopped memory _ _ hs]
        exact safeRealizes_stopped width memory program s fit hs _ _
  | exit src =>
      by_cases hs : s.status = .running
      · have hf : program[s.pc]? = some (.halt src) := by rw [hpc]; exact host.head
        have haltfit : ({ s with status := .halted (s.regs src) } : State).Fits width :=
          ⟨fit.1, fit.2.1, fun value hv => by cases hv; exact fit.2.1 src⟩
        refine ⟨{ s with status := .halted (s.regs src) },
          [⟨s, .halt src, { s with status := .halted (s.regs src) }, none⟩],
          RunsTo.instruction hs hf, ?_, ?_, Nat.le_refl _, ?_, haltfit, ?_⟩
        · simp [Block.eval, Data.ofState, hs]
        · simp [Block.eval, Data.ofState, hs]
        · simp
        · intro t ht; have he := List.mem_singleton.mp ht; subst t
          exact ⟨⟨fields, fit, trivial⟩, haltfit⟩
      · rw [Block.eval_stopped memory _ _ hs]
        exact safeRealizes_stopped width memory program s fit hs _ _
  | seq first second ihf ihs =>
      by_cases hs : s.status = .running
      · have hf := ihf base s hpc host.append_left fields.1
          (by simp only [Block.size] at bound; omega) fit (safe.2 hs).1
        rw [Block.eval_seq]
        apply SafeRealizes.follow hf (Block.eval_stopped memory second)
        intro t ht hd _ tfit
        have hh := ihs (base + first.size) t ht (by simpa using host.append_right) fields.2
          (by simpa [Block.size, Nat.add_assoc] using bound) tfit (by
            rw [hd]; exact (safe.2 hs).2)
        simpa [Block.size, Nat.add_assoc] using hh
      · rw [Block.eval_stopped memory _ _ hs]
        exact safeRealizes_stopped width memory program s fit hs _ _
  | ifZero condition zero nonzero ihz ihn =>
      by_cases hs : s.status = .running
      · have hbranch : program[s.pc]? =
            some (.branchZero condition (base + 1 + nonzero.size + 1)) := by
          rw [hpc]; exact host.append_left.append_left.append_left.head
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
        have hbound : base + 1 + nonzero.size + 1 + zero.size < 2 ^ width := by
          simpa [Block.size, Nat.add_assoc] using bound
        have hb := safeRealizes_branch width memory program s condition
          (base + 1 + nonzero.size + 1) fit hs fields.1 (by omega) (by omega) hbranch
        by_cases hc : s.regs condition = 0
        · simp only [hc, if_true] at hb
          have hzero := SafeRealizes.follow hb (Block.eval_stopped memory zero) (by
            intro t ht hd _ tfit
            apply ihz _ t ht hz fields.2.2.1 hbound tfit
            rw [hd]
            simpa [Data.ofState, hc] using safe.2 hs)
          have hh : (⟨Data.ofState s, []⟩ : Evaluation).bind (zero.eval memory) =
              (Block.ifZero condition zero nonzero).eval memory (Data.ofState s) := by
            simp [Evaluation.bind, Block.eval, Data.ofState, hs, hc]
          rw [hh] at hzero
          have hend : base + 1 + nonzero.size + 1 + zero.size =
              base + (Block.ifZero condition zero nonzero).size := by simp [Block.size]; omega
          rw [hend] at hzero
          exact safeRealizes_mono hzero (by simp [Block.size] <;> omega)
        · simp only [hc, if_false, hpc] at hb
          have hnonzero := SafeRealizes.follow hb (Block.eval_stopped memory nonzero) (by
            intro t ht hd _ tfit
            apply ihn _ t ht hn fields.2.2.2 (by omega) tfit
            rw [hd]
            simpa [Data.ofState, hc] using safe.2 hs)
          have hall := SafeRealizes.follow hnonzero
            (next := fun d => ⟨d, []⟩) (finish := base + 1 + nonzero.size + 1 + zero.size)
            (b := 1) (fun _ _ => rfl) (by
              intro t ht _ hstatus tfit
              apply safeRealizes_jump width memory program t _ tfit hstatus fields.2.1 hbound
              rw [ht]; exact hj.head)
          have hh : ((⟨Data.ofState s, []⟩ : Evaluation).bind (nonzero.eval memory)).bind
              (fun d => ⟨d, []⟩) =
              (Block.ifZero condition zero nonzero).eval memory (Data.ofState s) := by
            simp [Evaluation.bind, Block.eval, Data.ofState, hs, hc]
          rw [hh] at hall
          have hend : base + 1 + nonzero.size + 1 + zero.size =
              base + (Block.ifZero condition zero nonzero).size := by simp [Block.size]; omega
          rw [hend] at hall
          exact safeRealizes_mono hall (by simp [Block.size] <;> omega)
      · rw [Block.eval_stopped memory _ _ hs]
        exact safeRealizes_stopped width memory program s fit hs _ _
  | «repeat» count body ih =>
      induction count generalizing base s with
      | zero =>
          rw [Block.eval_repeat]
          refine ⟨s, [], RunsTo.refl memory program s, rfl, rfl, by simp [Block.size], ?_, fit, ?_⟩
          · intro _; simpa [Block.size] using hpc
          · intro _ ht; exact (List.not_mem_nil ht).elim
      | succ count ihc =>
          by_cases hs : s.status = .running
          · rw [Block.compile_repeat_succ] at host
            have hiterations := safe.2 hs
            have hbnd : base + body.size + count * body.size < 2 ^ width := by
              simpa [Block.size, Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using bound
            have first := ih base s hpc host.append_left fields (by omega) fit hiterations.1
            rw [Block.eval_repeat_succ]
            have all := SafeRealizes.follow first
              (Block.eval_stopped memory (Block.repeat count body)) (by
                intro t ht hd _ tfit
                apply ihc (base + body.size) t ht (by simpa using host.append_right) fields
                  (by simpa [Block.size] using hbnd) tfit
                rw [hd]
                exact ⟨body.eval_fits memory width _ hiterations.1, fun _ => hiterations.2⟩)
            simpa [Block.size, Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using all
          · rw [Block.eval_stopped memory _ _ hs]
            exact safeRealizes_stopped width memory program s fit hs _ _

/-- One actual hosted run carries value, receipts, exact cost and word safety.
Safety is occurrence-indexed; prefix zero and the final prefix are included. -/
theorem Block.compile_safe_correct (memory : Memory) (program : Program) (width : Nat)
    (block : Block) (base : Nat) (s : State) (hpc : s.pc = base)
    (host : HostedAt program base (block.compileAt base))
    (fields : block.FieldsFit width) (bound : base + block.size < 2 ^ width)
    (fit : s.Fits width) (safe : block.Safe memory width (Data.ofState s)) :
    ∃ used, used ≤ block.size ∧
      Data.ofState (run memory program used s).final =
        (block.eval memory (Data.ofState s)).final ∧
      (run memory program used s).reads = (block.eval memory (Data.ofState s)).reads ∧
      (run memory program used s).steps = used ∧
      ((run memory program used s).final.status = .running →
        (run memory program used s).final.pc = base + block.size) ∧
      (run memory program used s).final.Fits width ∧
      (∀ (index : Nat) (t : Transition), (run memory program used s).transitions[index]? = some t →
        Instruction.Safe width t.before t.instruction ∧ t.after.Fits width) ∧
      (∀ index, index ≤ used → (run memory program index s).final.Fits width) := by
  obtain ⟨final, ts, hx, hd, hr, hb, hp, hf, ht⟩ :=
    block.compile_safe_realizes memory program width base s hpc host fields bound fit safe
  have htrace : TraceSafe width (run memory program ts.length s).transitions := by
    unfold RunsTo at hx
    rw [hx]
    exact ht
  have hprefix := run_prefix_fits memory program width ts.length s fit htrace
  refine ⟨ts.length, hb, ?_⟩
  unfold RunsTo at hx
  rw [hx]
  exact ⟨hd, hr, rfl, hp, hf, fun _ _ h => ht _ (List.mem_of_getElem? h), hprefix⟩

private theorem run_extend_stopped (memory : Memory) (program : Program)
    (s : State) (used budget : Nat) (hbound : used ≤ budget)
    (hstop : step memory program (run memory program used s).final = none) :
    run memory program budget s = run memory program used s := by
  rw [← Nat.add_sub_of_le hbound, run_add]
  dsimp only
  rw [run_of_step_none memory program _ _ hstop]
  simp

/-- Fixed full compiled-size fuel preserves safety, including prefixes beyond
an early stop. The same actual run has the Compiler value/read/budget behavior. -/
theorem Block.compile_run_safe (memory : Memory) (width : Nat) (block : Block)
    (s : State) (hpc : s.pc = 0) (fields : block.FieldsFit width)
    (bound : block.size < 2 ^ width) (fit : s.Fits width)
    (safe : block.Safe memory width (Data.ofState s)) :
    Data.ofState (run memory (block.compileAt 0) block.size s).final =
      (block.eval memory (Data.ofState s)).final ∧
    (run memory (block.compileAt 0) block.size s).reads =
      (block.eval memory (Data.ofState s)).reads ∧
    (run memory (block.compileAt 0) block.size s).steps ≤ block.size ∧
    ((run memory (block.compileAt 0) block.size s).final.status = .running →
      (run memory (block.compileAt 0) block.size s).final.pc = block.size) ∧
    (run memory (block.compileAt 0) block.size s).final.Fits width ∧
    (∀ (index : Nat) (t : Transition), (run memory (block.compileAt 0) block.size s).transitions[index]? = some t →
      Instruction.Safe width t.before t.instruction ∧ t.after.Fits width) ∧
    (∀ index, index ≤ block.size →
      (run memory (block.compileAt 0) index s).final.Fits width) := by
  obtain ⟨used, hb, hd, hr, hc, hp, hf, ht, _⟩ :=
    block.compile_safe_correct memory (block.compileAt 0) width 0 s hpc (HostedAt.self _)
      fields (by simpa using bound) fit safe
  have hs : step memory (block.compileAt 0)
      (run memory (block.compileAt 0) used s).final = none := by
    cases hstatus : (run memory (block.compileAt 0) used s).final.status with
    | running =>
        have hfetch : (block.compileAt 0)[(run memory (block.compileAt 0) used s).final.pc]? = none := by
          rw [hp hstatus]
          apply List.getElem?_eq_none
          simp
        simp [step, hstatus, hfetch]
    | halted value => simp [step, hstatus]
    | fault => simp [step, hstatus]
  have heq := run_extend_stopped memory (block.compileAt 0) s used block.size hb hs
  have htrace : TraceSafe width (run memory (block.compileAt 0) block.size s).transitions := by
    rw [heq]
    intro t hmem
    obtain ⟨index, hi⟩ := List.getElem?_of_mem hmem
    exact ht index t hi
  have hprefix := run_prefix_fits memory (block.compileAt 0) width block.size s fit htrace
  rw [heq]
  exact ⟨hd, hr, by omega, by simpa using hp, hf, ht, hprefix⟩

/-- An output-halt consumer exposes the same source result and actual run as
Compiler, with runtime safety and every fixed-budget prefix included. -/
theorem Block.compile_with_halt_safe (memory : Memory) (width : Nat) (block : Block)
    (output : Nat) (s : State) (hpc : s.pc = 0) (fields : block.FieldsFit width)
    (haltFields : (Instruction.halt output).Fits width)
    (bound : block.size + 1 < 2 ^ width) (fit : s.Fits width)
    (safe : block.Safe memory width (Data.ofState s)) :
    let source := block.eval memory (Data.ofState s)
    let program := block.compileAt 0 ++ [Instruction.halt output]
    let actual := run memory program (block.size + 1) s
    Data.ofState actual.final = ((Block.exit output).eval memory source.final).final ∧
    actual.result = (match source.final.status with
      | .running => some (source.final.regs output)
      | .halted value => some value
      | .fault => none) ∧
    actual.reads = source.reads ∧ actual.steps ≤ program.length ∧
    actual.final.Fits width ∧
    (∀ (index : Nat) (t : Transition), actual.transitions[index]? = some t →
      Instruction.Safe width t.before t.instruction ∧ t.after.Fits width) ∧
    (∀ index, index ≤ block.size + 1 → (run memory program index s).final.Fits width) := by
  have hsource : (Block.seq block (.exit output)).Safe memory width (Data.ofState s) :=
    Block.safe_seq safe (Block.safe_exit memory width output _ (block.eval_fits memory width _ safe))
  have hrun := (Block.seq block (.exit output)).compile_run_safe memory width s hpc
    ⟨fields, haltFields⟩ bound fit hsource
  have hresult := block.compile_with_halt memory output s hpc
  dsimp only
  refine ⟨hresult.1, hresult.2.1, hresult.2.2.1, hresult.2.2.2, ?_⟩
  simpa [Block.compileAt, Block.size] using hrun.2.2.2.2

/-- Read addresses, including failed attempts, and successful reply words fit
the same width at the actual producing transition occurrence. -/
theorem run_read_fits {memory : Memory} {program : Program} {fuel width : Nat}
    {s : State} {index : Nat} {t : Transition} {receipt : Receipt}
    (occurrence : (run memory program fuel s).transitions[index]? = some t)
    (read : t.receipt = some receipt)
    (safe : Instruction.Safe width t.before t.instruction) (afterFit : t.after.Fits width) :
    receipt.address < 2 ^ width ∧ receipt.reply = memory[receipt.address]? ∧
      (∀ value, receipt.reply = some value → value < 2 ^ width) := by
  obtain ⟨_, _, _, he, dst, address, hi, ha, hr⟩ := run_read_at occurrence read
  refine ⟨by rw [ha]; exact safe.2.1.2.1 address, hr, ?_⟩
  intro value hv
  have hlookup : memory[t.before.regs address]? = some value := by
    rw [← ha, ← hr]
    exact hv
  have heafter := congrArg Prod.fst he
  have hafter : t.after = t.before.writeNext dst value := by
    simpa [hi, execute, hlookup] using heafter.symm
  have hvalue := afterFit.2.1 dst
  rw [hafter] at hvalue
  simpa [State.writeNext] using hvalue

namespace SafetyConsumers

theorem hosted_expectedType (memory : Memory) (program : Program) (width : Nat)
    (block : Block) (base : Nat) (s : State) (hpc : s.pc = base)
    (host : HostedAt program base (block.compileAt base))
    (fields : block.FieldsFit width) (bound : base + block.size < 2 ^ width)
    (fit : s.Fits width) (safe : block.Safe memory width (Data.ofState s)) :
    ∃ used, used ≤ block.size ∧
      Data.ofState (run memory program used s).final =
        (block.eval memory (Data.ofState s)).final ∧
      (run memory program used s).reads = (block.eval memory (Data.ofState s)).reads ∧
      (run memory program used s).steps = used ∧
      ((run memory program used s).final.status = .running →
        (run memory program used s).final.pc = base + block.size) ∧
      (run memory program used s).final.Fits width ∧
      (∀ (index : Nat) (t : Transition), (run memory program used s).transitions[index]? = some t →
        Instruction.Safe width t.before t.instruction ∧ t.after.Fits width) ∧
      (∀ index, index ≤ used → (run memory program index s).final.Fits width) :=
  block.compile_safe_correct memory program width base s hpc host fields bound fit safe

theorem standalone_expectedType (memory : Memory) (width : Nat) (block : Block)
    (s : State) (hpc : s.pc = 0) (fields : block.FieldsFit width)
    (bound : block.size < 2 ^ width) (fit : s.Fits width)
    (safe : block.Safe memory width (Data.ofState s)) :
    Data.ofState (run memory (block.compileAt 0) block.size s).final =
      (block.eval memory (Data.ofState s)).final ∧
    (run memory (block.compileAt 0) block.size s).reads =
      (block.eval memory (Data.ofState s)).reads ∧
    (run memory (block.compileAt 0) block.size s).steps ≤ block.size ∧
    ((run memory (block.compileAt 0) block.size s).final.status = .running →
      (run memory (block.compileAt 0) block.size s).final.pc = block.size) ∧
    (run memory (block.compileAt 0) block.size s).final.Fits width ∧
    (∀ (index : Nat) (t : Transition), (run memory (block.compileAt 0) block.size s).transitions[index]? = some t →
      Instruction.Safe width t.before t.instruction ∧ t.after.Fits width) ∧
    (∀ index, index ≤ block.size →
      (run memory (block.compileAt 0) index s).final.Fits width) :=
  block.compile_run_safe memory width s hpc fields bound fit safe

theorem halt_expectedType (memory : Memory) (width : Nat) (block : Block)
    (output : Nat) (s : State) (hpc : s.pc = 0) (fields : block.FieldsFit width)
    (haltFields : (Instruction.halt output).Fits width)
    (bound : block.size + 1 < 2 ^ width) (fit : s.Fits width)
    (safe : block.Safe memory width (Data.ofState s)) :
    let source := block.eval memory (Data.ofState s)
    let program := block.compileAt 0 ++ [Instruction.halt output]
    let actual := run memory program (block.size + 1) s
    Data.ofState actual.final = ((Block.exit output).eval memory source.final).final ∧
    actual.result = (match source.final.status with
      | .running => some (source.final.regs output)
      | .halted value => some value
      | .fault => none) ∧
    actual.reads = source.reads ∧ actual.steps ≤ program.length ∧
    actual.final.Fits width ∧
    (∀ (index : Nat) (t : Transition), actual.transitions[index]? = some t →
      Instruction.Safe width t.before t.instruction ∧ t.after.Fits width) ∧
    (∀ index, index ≤ block.size + 1 → (run memory program index s).final.Fits width) :=
  block.compile_with_halt_safe memory width output s hpc fields haltFields bound fit safe

def operandData (x y : Nat) : Data :=
  ⟨fun r => if r = 0 then x else if r = 1 then y else 0, .running⟩

def operandState (x y : Nat) : State := ⟨(operandData x y).regs, 0, .running⟩

theorem operandData_fits (width x y : Nat) (hx : x < 2 ^ width) (hy : y < 2 ^ width) :
    (operandData x y).Fits width := by
  constructor
  · intro r
    by_cases h0 : r = 0
    · simpa [operandData, h0] using hx
    · by_cases h1 : r = 1
      · simpa [operandData, h0, h1] using hy
      · simp only [operandData, h0, h1, if_false]
        omega
  · intro value hv
    cases hv

theorem operandState_fits (width x y : Nat) (hx : x < 2 ^ width) (hy : y < 2 ^ width) :
    (operandState x y).Fits width :=
  ⟨by dsimp [operandState]; omega, operandData_fits width x y hx hy⟩

/-- A symbolic operation rule exposes all four arithmetic obligations. -/
theorem arithmetic_source_safe (width : Nat) (op : Arithmetic) (x y : Nat)
    (hx : x < 2 ^ width) (hy : y < 2 ^ width)
    (result : op.eval x y < 2 ^ width) (sub : op = .sub → y ≤ x)
    (divisor : op = .div ∨ op = .mod → 0 < y)
    (shift : op = .shl ∨ op = .shr → y < width) :
    (Block.action (.arithmetic op 0 0 1)).Safe [] width (operandData x y) := by
  apply Block.safe_action _ _ _ _ (operandData_fits width x y hx hy)
  simpa [Action.LocalSafe, operandData] using And.intro result ⟨sub, divisor, shift⟩

theorem arithmetic_compiled_safe (width : Nat) (op : Arithmetic) (x y : Nat)
    (hx : x < 2 ^ width) (hy : y < 2 ^ width)
    (result : op.eval x y < 2 ^ width) (sub : op = .sub → y ≤ x)
    (divisor : op = .div ∨ op = .mod → 0 < y)
    (shift : op = .shl ∨ op = .shr → y < width)
    (fields : (Instruction.arithmetic op 0 0 1).Fits width)
    (haltFields : (Instruction.halt 0).Fits width) (bound : 2 < 2 ^ width) :
    let program : Program := [.arithmetic op 0 0 1, .halt 0]
    (run [] program 2 (operandState x y)).result = some (op.eval x y) ∧
    (∀ (index : Nat) (t : Transition), (run [] program 2 (operandState x y)).transitions[index]? = some t →
      Instruction.Safe width t.before t.instruction ∧ t.after.Fits width) ∧
    (∀ index, index ≤ 2 → (run [] program index (operandState x y)).final.Fits width) := by
  have hs := arithmetic_source_safe width op x y hx hy result sub divisor shift
  have hh := (Block.action (.arithmetic op 0 0 1)).compile_with_halt_safe [] width 0
    (operandState x y) rfl fields haltFields bound (operandState_fits width x y hx hy) hs
  exact ⟨hh.2.1, hh.2.2.2.2.2.1, hh.2.2.2.2.2.2⟩

theorem legal_boundary :
    let program : Program := [.arithmetic .add 0 0 1, .halt 0]
    (run [] program 2 (operandState 14 1)).result = some 15 ∧
    (∀ (index : Nat) (t : Transition), (run [] program 2 (operandState 14 1)).transitions[index]? = some t →
      Instruction.Safe 4 t.before t.instruction ∧ t.after.Fits 4) ∧
    (∀ index, index ≤ 2 → (run [] program index (operandState 14 1)).final.Fits 4) := by
  apply arithmetic_compiled_safe 4 .add 14 1 <;>
    simp [Arithmetic.eval, Instruction.Fits, Instruction.encoding, Instruction.operands, Arithmetic.code]

theorem underflow_rejected :
    ¬ (Block.action (.arithmetic .sub 0 0 1)).Safe [] 4 (operandData 0 1) := by
  intro h
  have bad := h.2 rfl
  simp [Action.LocalSafe, operandData, Arithmetic.eval] at bad

theorem zero_divisor_rejected :
    ¬ (Block.action (.arithmetic .div 0 0 1)).Safe [] 4 (operandData 8 0) := by
  intro h
  have bad := h.2 rfl
  simp [Action.LocalSafe, operandData, Arithmetic.eval] at bad

theorem zero_modulus_rejected :
    ¬ (Block.action (.arithmetic .mod 0 0 1)).Safe [] 4 (operandData 8 0) := by
  intro h
  have bad := h.2 rfl
  simp [Action.LocalSafe, operandData, Arithmetic.eval] at bad

theorem excessive_right_shift_rejected :
    ¬ (Block.action (.arithmetic .shr 0 0 1)).Safe [] 4 (operandData 1 4) := by
  intro h
  have bad := h.2 rfl
  simp [Action.LocalSafe, operandData, Arithmetic.eval] at bad

theorem excessive_left_shift_rejected :
    ¬ (Block.action (.arithmetic .shl 0 0 1)).Safe [] 4 (operandData 0 4) := by
  intro h
  have bad := h.2 rfl
  simp [Action.LocalSafe, operandData, Arithmetic.eval] at bad

theorem overflowing_result_rejected :
    ¬ (Block.action (.arithmetic .add 0 0 1)).Safe [] 4 (operandData 15 1) := by
  intro h
  have bad := h.2 rfl
  simp [Action.LocalSafe, operandData, Arithmetic.eval] at bad

theorem failed_address_rejected :
    ¬ (Block.action (.load 1 0)).Safe [] 4 (operandData 16 0) := by
  intro h
  have bad := h.1.1 0
  simp [operandData] at bad

/-- A failed physical load at the largest representable address remains safe. -/
theorem missing_load_safe :
    let program : Program := [.load 1 0, .halt 1]
    (run [] program 2 (operandState 15 0)).result = none ∧
    (run [] program 2 (operandState 15 0)).reads = [⟨15, none⟩] ∧
    (run [] program 2 (operandState 15 0)).steps = 1 ∧
    (∀ index, index ≤ 2 → (run [] program index (operandState 15 0)).final.Fits 4) := by
  have hs : (Block.action (.load 1 0)).Safe [] 4 (operandData 15 0) := by
    apply Block.safe_action _ _ _ _ (operandData_fits 4 15 0 (by decide) (by decide))
    simp [Action.LocalSafe]
  have hh := (Block.action (.load 1 0)).compile_with_halt_safe [] 4 1 (operandState 15 0) rfl
    (by simp [Block.FieldsFit, Action.instruction, Instruction.Fits, Instruction.encoding, Instruction.operands])
    (by simp [Instruction.Fits, Instruction.encoding, Instruction.operands])
    (by decide) (operandState_fits 4 15 0 (by decide) (by decide)) hs
  exact ⟨hh.2.1, hh.2.2.1, rfl, hh.2.2.2.2.2.2⟩

end SafetyConsumers

end RMQ.SuccinctFinal.PackedWordRAM.Structured
