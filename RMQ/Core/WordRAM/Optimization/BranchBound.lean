import RMQ.Core.WordRAM.Packed.Compiler

/-!
# Branch-sensitive execution bounds for the baseline compiler

The recurrence counts the branch actually taken, retaining its branch and jump
instructions. The proof witnesses a segment of the unchanged primitive run;
adequate-fuel equality retains the final state and every ordered transition.
No claim of an attained worst case or Lean runtime bound is made.
-/

namespace RMQ.SuccinctFinal.PackedWordRAM.Optimization

open Structured

/-- Upper bound on executed primitives, allowing either branch direction. -/
def branchBound : Block → Nat
  | .skip => 0
  | .action _ | .exit _ => 1
  | .seq first second => branchBound first + branchBound second
  | .ifZero _ zero nonzero => max (1 + branchBound zero) (2 + branchBound nonzero)
  | .repeat count body => count * branchBound body

/-- Branch-sensitive fuel never exceeds the original compiled-size budget. -/
theorem branchBound_le_size (block : Block) : branchBound block ≤ block.size := by
  induction block with
  | skip => exact Nat.le_refl _
  | action op => exact Nat.le_refl _
  | exit src => exact Nat.le_refl _
  | seq first second ihf ihs => simp only [branchBound, Block.size]; omega
  | ifZero condition zero nonzero ihz ihn =>
      simp only [branchBound, Block.size]
      omega
  | «repeat» count body ih =>
      exact Nat.mul_le_mul_left count ih

private theorem action_data (memory : Memory) (op : Action) (s : State) :
    Data.ofState (execute memory op.instruction s).1 =
      (op.eval memory (Data.ofState s)).final ∧
    (execute memory op.instruction s).2.toList =
      (op.eval memory (Data.ofState s)).reads ∧
    ((execute memory op.instruction s).1.status = .running →
      (execute memory op.instruction s).1.pc = s.pc + 1) := by
  cases op <;> simp [Action.instruction, Action.eval, execute, State.writeNext, Data.ofState]
  split <;> simp_all

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

/-- The hosted baseline code realizes the independent source evaluation with
an actual transition segment bounded by the branch-sensitive recurrence. -/
theorem compile_realizes_branchBound (memory : Memory) (program : Program) (block : Block)
    (base : Nat) (s : State) (hpc : s.pc = base)
    (host : HostedAt program base (block.compileAt base)) :
    Realizes memory program s (block.eval memory (Data.ofState s))
      (base + block.size) (branchBound block) := by
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
      simpa [branchBound, Block.size, Nat.add_assoc] using hh
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
          exact realizes_mono hzero (by simp only [branchBound]; omega)
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
          exact realizes_mono hall (by simp only [branchBound]; omega)
      · rw [Block.eval_stopped memory _ _ hs]
        exact realizes_stopped memory program s hs _ _
  | «repeat» count body ih =>
      induction count generalizing base s with
      | zero =>
          rw [Block.eval_repeat]
          refine ⟨s, [], RunsTo.refl memory program s, rfl, rfl, by simp [branchBound], ?_⟩
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
          simpa [branchBound, Block.size, Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using all

private theorem run_extend_stopped (memory : Memory) (program : Program)
    (s : State) (used budget : Nat) (hbound : used ≤ budget)
    (hstop : step memory program (run memory program used s).final = none) :
    run memory program budget s = run memory program used s := by
  rw [← Nat.add_sub_of_le hbound, run_add]
  dsimp only
  rw [run_of_step_none memory program _ _ hstop]
  simp

/-- Once the structural bound is available, any two adequate fuels give the
same full run. The first conjunct bounds the run at its supplied fuel, rather
than merely applying the generic bound by that fuel. No success premise is
needed: normal code exhaustion, early halt and failed loads are all covered. -/
theorem compiled_run_bound_and_fuel_eq (memory : Memory) (block : Block)
    (s : State) (hpc : s.pc = 0) (a b : Nat)
    (ha : branchBound block ≤ a) (hb : branchBound block ≤ b) :
    (run memory (block.compileAt 0) a s).steps ≤ branchBound block ∧
    run memory (block.compileAt 0) a s = run memory (block.compileAt 0) b s := by
  obtain ⟨final, ts, hx, hd, hr, hbound, hp⟩ :=
    compile_realizes_branchBound memory (block.compileAt 0) block 0 s hpc (HostedAt.self _)
  have hstop : step memory (block.compileAt 0) final = none := by
    cases hs : final.status with
    | running =>
        have hf : (block.compileAt 0)[final.pc]? = none := by
          rw [hp hs]
          apply List.getElem?_eq_none
          simp
        simp [step, hs, hf]
    | halted value => simp [step, hs]
    | fault => simp [step, hs]
  have hstop' : step memory (block.compileAt 0)
      (run memory (block.compileAt 0) ts.length s).final = none := by
    unfold RunsTo at hx
    simpa only [hx] using hstop
  have hrunA := run_extend_stopped memory (block.compileAt 0) s ts.length a
    (Nat.le_trans hbound ha) hstop'
  have hrunB := run_extend_stopped memory (block.compileAt 0) s ts.length b
    (Nat.le_trans hbound hb) hstop'
  refine ⟨?_, hrunA.trans hrunB.symm⟩
  rw [hrunA]
  unfold RunsTo at hx
  simpa only [hx, Run.steps] using hbound

namespace BranchBoundConsumers

/-- Independent expected type pins the actual execution and both fuel arguments. -/
theorem execution_expectedType (memory : Memory) (block : Block)
    (s : State) (hpc : s.pc = 0) (a b : Nat)
    (ha : branchBound block ≤ a) (hb : branchBound block ≤ b) :
    (run memory (block.compileAt 0) a s).steps ≤ branchBound block ∧
    run memory (block.compileAt 0) a s = run memory (block.compileAt 0) b s :=
  compiled_run_bound_and_fuel_eq memory block s hpc a b ha hb

/-- The hosted consumer pins every operational Realizes argument explicitly. -/
theorem realizes_expectedType (memory : Memory) (program : Program) (block : Block)
    (base : Nat) (s : State) (hpc : s.pc = base)
    (host : HostedAt program base (block.compileAt base)) :
    ∃ final transitions,
      RunsTo memory program s final transitions ∧
      Data.ofState final = (block.eval memory (Data.ofState s)).final ∧
      transitions.filterMap (·.receipt) = (block.eval memory (Data.ofState s)).reads ∧
      transitions.length ≤ branchBound block ∧
      (final.status = .running → final.pc = base + block.size) :=
  compile_realizes_branchBound memory program block base s hpc host

private def zeroState : State := ⟨fun _ => 0, 0, .running⟩
private def nonzeroState : State := ⟨fun r => if r = 0 then 1 else 0, 0, .running⟩
private def choice : Block := .seq
  (.ifZero 0 (.action (.constant 1 7)) (.action (.constant 1 8))) (.exit 1)

/-- The branch and its nonzero jump have different charged path lengths. -/
theorem branch_directions :
    branchBound choice = 4 ∧ choice.size = 5 ∧
    (run [] (choice.compileAt 0) 5 zeroState).result = some 7 ∧
    (run [] (choice.compileAt 0) 5 zeroState).steps = 3 ∧
    (run [] (choice.compileAt 0) 5 nonzeroState).result = some 8 ∧
    (run [] (choice.compileAt 0) 5 nonzeroState).steps = 4 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Removing the required fuel guard admits a genuinely truncated execution. -/
theorem one_short_truncates :
    (run [] (choice.compileAt 0) 3 nonzeroState).final.status = .running ∧
    (run [] (choice.compileAt 0) 4 nonzeroState).final.status = .halted 8 :=
  ⟨rfl, rfl⟩

/-- Both boundary targets are legal, even when neither arm emits instructions. -/
theorem empty_branches_at_boundary :
    (run [] ((Block.ifZero 0 .skip .skip).compileAt 0) 9 zeroState).steps = 1 ∧
    (run [] ((Block.ifZero 0 .skip .skip).compileAt 0) 9 nonzeroState).steps = 2 ∧
    (run [] ((Block.ifZero 0 .skip .skip).compileAt 0) 9 nonzeroState).final.pc = 2 :=
  ⟨rfl, rfl, rfl⟩

private def loads (count : Nat) : Block :=
  .seq (.repeat count (.action (.load 1 0))) (.exit 1)

/-- Literal expected replies retain multiplicity and order across repetition. -/
theorem repeated_loads :
    (run [7] ((loads 0).compileAt 0) 20 zeroState).reads = [] ∧
    (run [7] ((loads 1).compileAt 0) 20 zeroState).reads = [⟨0, some 7⟩] ∧
    (run [7] ((loads 3).compileAt 0) 20 zeroState).reads =
      [⟨0, some 7⟩, ⟨0, some 7⟩, ⟨0, some 7⟩] ∧
    (run [7] ((loads 3).compileAt 0) 20 zeroState).result = some 7 ∧
    (run [7] ((loads 3).compileAt 0) 20 zeroState).steps = 4 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Missing physical loads stop the actual run and record the failed attempt. -/
theorem failed_load_stops :
    (run [] ((loads 3).compileAt 0) 20 zeroState).final.status = .fault ∧
    (run [] ((loads 3).compileAt 0) 20 zeroState).reads = [⟨0, none⟩] ∧
    (run [] ((loads 3).compileAt 0) 20 zeroState).steps = 1 :=
  ⟨rfl, rfl, rfl⟩

/-- Nested sequencing does not execute a read after an earlier halt. -/
theorem nested_early_exit :
    let block := Block.seq (.seq (.exit 0) (.action (.load 1 0)))
      (.repeat 3 (.action (.load 1 0)))
    (run [] (block.compileAt 0) 20 nonzeroState).result = some 1 ∧
    (run [] (block.compileAt 0) 20 nonzeroState).reads = [] ∧
    (run [] (block.compileAt 0) 20 nonzeroState).steps = 1 :=
  ⟨rfl, rfl, rfl⟩
end BranchBoundConsumers

end RMQ.SuccinctFinal.PackedWordRAM.Optimization