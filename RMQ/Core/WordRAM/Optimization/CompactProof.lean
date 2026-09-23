import RMQ.Core.WordRAM.Optimization.Compact

/-!
# Exact primitive execution of counted-loop compilation

Scratch registers are excluded from source observations but remain present in
every actual transition. Nested bodies compare against their actual entry data;
source congruence and frames relate that rebased evaluation to the caller.
-/

namespace RMQ.SuccinctFinal.PackedWordRAM.Optimization

open Structured

def CompactRealizes (memory : Memory) (program : Program) (observed : Nat)
    (s : State) (expected : Evaluation) (finish budget : Nat) : Prop :=
  ∃ final transitions,
    RunsTo memory program s final transitions ∧
    DataAgreesBelow observed (Data.ofState final) expected.final ∧
    transitions.filterMap (·.receipt) = expected.reads ∧
    transitions.length ≤ budget ∧
    (final.status = .running → final.pc = finish)

theorem compact_stopped (memory : Memory) (program : Program) (observed : Nat)
    (s : State) (hs : s.status ≠ .running) (finish budget : Nat) :
    CompactRealizes memory program observed s ⟨Data.ofState s, []⟩ finish budget :=
  ⟨s, [], RunsTo.refl memory program s, DataAgreesBelow.refl _ _, rfl,
    Nat.zero_le _, fun h => (hs h).elim⟩

theorem compact_budget_mono {memory : Memory} {program : Program} {observed : Nat}
    {s : State} {expected : Evaluation} {finish a b : Nat}
    (h : CompactRealizes memory program observed s expected finish a) (hab : a ≤ b) :
    CompactRealizes memory program observed s expected finish b := by
  obtain ⟨t, ts, hx, hd, hr, hc, hp⟩ := h
  exact ⟨t, ts, hx, hd, hr, Nat.le_trans hc hab, hp⟩

theorem compact_protected_mono {memory : Memory} {program : Program} {small large : Nat}
    {s : State} {expected : Evaluation} {finish budget : Nat}
    (h : CompactRealizes memory program large s expected finish budget) (hle : small ≤ large) :
    CompactRealizes memory program small s expected finish budget := by
  obtain ⟨t, ts, hx, hd, hr, hc, hp⟩ := h
  exact ⟨t, ts, hx, hd.mono hle, hr, hc, hp⟩

theorem compact_expected_congr {memory : Memory} {program : Program} {observed : Nat}
    {s : State} {left right : Evaluation} {finish budget : Nat}
    (h : CompactRealizes memory program observed s left finish budget)
    (agree : EvaluationAgreesBelow observed left right) :
    CompactRealizes memory program observed s right finish budget := by
  obtain ⟨t, ts, hx, hd, hr, hc, hp⟩ := h
  exact ⟨t, ts, hx, hd.trans agree.1, hr.trans agree.2, hc, hp⟩

theorem compact_follow {memory : Memory} {program : Program} {observed : Nat}
    {s : State} {first : Evaluation} {next : Data → Evaluation}
    {middle finish a b : Nat}
    (hfirst : CompactRealizes memory program observed s first middle a)
    (stopped : ∀ d, d.status ≠ .running → next d = ⟨d, []⟩)
    (congr : ∀ left right, DataAgreesBelow observed left right →
      EvaluationAgreesBelow observed (next left) (next right))
    (hnext : ∀ t, t.pc = middle → DataAgreesBelow observed (Data.ofState t) first.final →
      t.status = .running →
      CompactRealizes memory program observed t (next (Data.ofState t)) finish b) :
    CompactRealizes memory program observed s (first.bind next) finish (a + b) := by
  obtain ⟨t, ts, hx, hd, hr, hc, hp⟩ := hfirst
  by_cases hs : t.status = .running
  · obtain ⟨u, us, hy, he, ht, hb, hq⟩ := hnext t (hp hs) hd hs
    have agree := congr (Data.ofState t) first.final hd
    refine ⟨u, ts ++ us, hx.trans hy, he.trans agree.1, ?_, ?_, hq⟩
    · simpa only [Evaluation.bind, List.filterMap_append, hr, ht] using
        congrArg (first.reads ++ ·) agree.2
    · simp only [List.length_append]; omega
  · have hstop := stopped first.final (by
      intro h; exact hs (hd.1.trans h))
    refine ⟨t, ts, hx, ?_, ?_, by omega, fun h => (hs h).elim⟩
    · simpa only [Evaluation.bind, hstop] using hd
    · simpa only [Evaluation.bind, hstop, List.append_nil] using hr

theorem compact_jump (memory : Memory) (program : Program) (observed : Nat)
    (s : State) (target : Nat) (hs : s.status = .running)
    (hf : program[s.pc]? = some (.jump target)) :
    CompactRealizes memory program observed s ⟨Data.ofState s, []⟩ target 1 := by
  exact ⟨{ s with pc := target }, [⟨s, .jump target, { s with pc := target }, none⟩],
    RunsTo.instruction hs hf, DataAgreesBelow.refl _ _, rfl, Nat.le_refl _, fun _ => rfl⟩

theorem compact_branch (memory : Memory) (program : Program) (observed : Nat)
    (s : State) (condition target : Nat) (hs : s.status = .running)
    (hf : program[s.pc]? = some (.branchZero condition target)) :
    CompactRealizes memory program observed s ⟨Data.ofState s, []⟩
      (if s.regs condition = 0 then target else s.pc + 1) 1 := by
  let t := { s with pc := if s.regs condition = 0 then target else s.pc + 1 }
  exact ⟨t, [⟨s, .branchZero condition target, t, none⟩], RunsTo.instruction hs hf,
    DataAgreesBelow.refl _ _, rfl, Nat.le_refl _, fun _ => rfl⟩

theorem compact_action_data (memory : Memory) (op : Action) (s : State) :
    Data.ofState (execute memory op.instruction s).1 =
      (op.eval memory (Data.ofState s)).final ∧
    (execute memory op.instruction s).2.toList =
      (op.eval memory (Data.ofState s)).reads ∧
    ((execute memory op.instruction s).1.status = .running →
      (execute memory op.instruction s).1.pc = s.pc + 1) := by
  cases op <;> simp [Action.instruction, Action.eval, execute, State.writeNext, Data.ofState]
  split <;> simp_all

theorem compact_iterate_stopped (memory : Memory) (body : Block) (count : Nat)
    (s : Data) (hs : s.status ≠ .running) :
    iterate (body.eval memory) count s = ⟨s, []⟩ := by
  induction count with
  | zero => rfl
  | succ count ih => simp [iterate, Block.eval_stopped memory body s hs, ih]

theorem compact_iterate_congr (memory : Memory) (body : Block) (observed : Nat)
    (bounded : BlockRegistersBelow observed body) (count : Nat) (left right : Data)
    (agree : DataAgreesBelow observed left right) :
    EvaluationAgreesBelow observed (iterate (body.eval memory) count left)
      (iterate (body.eval memory) count right) :=
  iterate_eval_congr observed (body.eval memory)
    (source_eval_congr memory body observed bounded) count left right agree

/-- The loop test and subsequent iterations execute in the one emitted body.
The body is rebased to actual entry data, so its stronger frame protects the
parent counter and unit register even after nested loops use deeper scratch. -/
theorem compact_loop_realizes (memory : Memory) (program : Program) (body : Block)
    (fresh depth base : Nat) (bounded : BlockRegistersBelow fresh body)
    (bodyRun : ∀ t, t.pc = base + 3 →
      CompactRealizes memory program (compactCounter fresh (depth + 1)) t
        (body.eval memory (Data.ofState t)) (base + 3 + compactSize body) (compactBound body))
    (branch : program[base + 2]? =
      some (.branchZero (compactCounter fresh depth) (base + 5 + compactSize body)))
    (decrement : program[base + 3 + compactSize body]? = some
      (.arithmetic .sub (compactCounter fresh depth) (compactCounter fresh depth)
        (compactCounter fresh depth + 1)))
    (jump : program[base + 4 + compactSize body]? = some (.jump (base + 2)))
    (remaining : Nat) (s : State) (hpc : s.pc = base + 2)
    (hc : s.regs (compactCounter fresh depth) = remaining)
    (hu : s.regs (compactCounter fresh depth + 1) = 1) :
    CompactRealizes memory program (compactCounter fresh depth) s
      (iterate (body.eval memory) remaining (Data.ofState s))
      (base + 5 + compactSize body) (1 + remaining * (compactBound body + 3)) := by
  let c := compactCounter fresh depth
  have freshC : fresh ≤ c := by dsimp [c, compactCounter]; omega
  have nextC : compactCounter fresh (depth + 1) = c + 2 := by
    dsimp [c, compactCounter]; omega
  induction remaining generalizing s with
  | zero =>
      by_cases hs : s.status = .running
      · have h := compact_branch memory program c s c (base + 5 + compactSize body) hs
          (by simpa [c, hpc] using branch)
        simpa [hc, c, iterate] using h
      · exact compact_stopped memory program c s hs _ _
  | succ remaining ih =>
      by_cases hs : s.status = .running
      · let entered : State := { s with pc := base + 3 }
        let bt : Transition := ⟨s, .branchZero c (base + 5 + compactSize body), entered, none⟩
        have hbranch : RunsTo memory program s entered [bt] := by
          have h := RunsTo.instruction (memory := memory) hs
            (show program[s.pc]? = some (.branchZero c (base + 5 + compactSize body)) by
              simpa [c, hpc] using branch)
          simpa [execute, hc, c, hpc, entered, bt] using h
        obtain ⟨t, ts, hbody, hd, hr, hb, hp⟩ := bodyRun entered rfl
        have hdLow : DataAgreesBelow c (Data.ofState t)
            (body.eval memory (Data.ofState s)).final := by
          apply hd.mono
          rw [nextC]; omega
        have tc : t.regs c = remaining + 1 := by
          calc
            t.regs c = (body.eval memory (Data.ofState entered)).final.regs c :=
              hd.2 c (by rw [nextC]; omega)
            _ = entered.regs c := source_eval_frame memory body fresh bounded c freshC _
            _ = remaining + 1 := hc
        have tu : t.regs (c + 1) = 1 := by
          calc
            t.regs (c + 1) = (body.eval memory (Data.ofState entered)).final.regs (c + 1) :=
              hd.2 (c + 1) (by rw [nextC]; omega)
            _ = entered.regs (c + 1) := source_eval_frame memory body fresh bounded _ (by omega) _
            _ = 1 := hu
        by_cases ht : t.status = .running
        · let dec : State := t.writeNext c remaining
          let dt : Transition := ⟨t, .arithmetic .sub c c (c + 1), dec, none⟩
          have hdec : RunsTo memory program t dec [dt] := by
            have h := RunsTo.instruction (memory := memory) ht
              (show program[t.pc]? = some (.arithmetic .sub c c (c + 1)) by
                simpa [c, hp ht] using decrement)
            simpa [execute, Arithmetic.eval, tc, tu, dec, dt] using h
          let next : State := { dec with pc := base + 2 }
          let jt : Transition := ⟨dec, .jump (base + 2), next, none⟩
          have hjump : RunsTo memory program dec next [jt] := by
            have h := RunsTo.instruction (memory := memory)
              (show dec.status = .running from rfl)
              (show program[dec.pc]? = some (.jump (base + 2)) by
                have pcDec : dec.pc = base + 4 + compactSize body := by
                  dsimp [dec, State.writeNext]
                  rw [hp ht]
                  omega
                rw [pcDec]
                exact jump)
            exact h
          have nextc : next.regs (compactCounter fresh depth) = remaining := by
            simp [next, dec, State.writeNext, c]
          have nextu : next.regs (compactCounter fresh depth + 1) = 1 := by
            simpa [next, dec, State.writeNext, Registers.write, c] using tu
          obtain ⟨u, us, htail, he, hreads, hcost, hend⟩ := ih next rfl nextc nextu
          have nextAgree : DataAgreesBelow c (Data.ofState next)
              (body.eval memory (Data.ofState s)).final := by
            simpa only [next, dec, State.writeNext, Data.ofState, ht] using
              hdLow.write_left_fresh c remaining (Nat.le_refl _)
          have tailAgree := compact_iterate_congr memory body c (bounded.mono freshC)
            remaining (Data.ofState next) (body.eval memory (Data.ofState s)).final nextAgree
          refine ⟨u, [bt] ++ ts ++ [dt] ++ [jt] ++ us,
            (((hbranch.trans hbody).trans hdec).trans hjump).trans htail,
            he.trans tailAgree.1, ?_, ?_, hend⟩
          · simp only [List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
              bt, dt, jt, List.nil_append, List.append_nil, hr, hreads]
            exact congrArg ((body.eval memory (Data.ofState s)).reads ++ ·) tailAgree.2
          · simp only [List.length_append, List.length_cons, List.length_nil]
            simp only [Nat.succ_mul] at *
            omega
        · have sourceStop : (body.eval memory (Data.ofState s)).final.status ≠ .running := by
            intro h; exact ht (hdLow.1.trans h)
          have stopped := compact_iterate_stopped memory body remaining _ sourceStop
          refine ⟨t, [bt] ++ ts, hbranch.trans hbody, ?_, ?_, ?_, fun h => (ht h).elim⟩
          · simpa only [iterate, stopped] using hdLow
          · simpa only [List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
              bt, List.nil_append, iterate, stopped, List.append_nil] using hr
          · simp only [List.length_append, List.length_cons, List.length_nil, Nat.succ_mul]
            omega
      · rw [compact_iterate_stopped memory body _ _ hs]
        exact compact_stopped memory program c s hs _ _

/-- Every hosted compact block has an actual bounded primitive segment. -/
theorem compact_realizes (memory : Memory) (program : Program) (block : Block)
    (fresh depth base : Nat) (s : State) (hpc : s.pc = base)
    (bounded : BlockRegistersBelow fresh block)
    (host : HostedAt program base (compactAt block fresh depth base)) :
    CompactRealizes memory program (compactCounter fresh depth) s
      (block.eval memory (Data.ofState s)) (base + compactSize block) (compactBound block) := by
  induction block generalizing depth base s with
  | skip =>
      by_cases hs : s.status = .running
      · refine ⟨s, [], RunsTo.refl memory program s, ?_, ?_, Nat.le_refl _, ?_⟩
        · simpa [Block.eval, Data.ofState, hs] using
            DataAgreesBelow.refl (compactCounter fresh depth) (Data.ofState s)
        · simp [Block.eval, Data.ofState, hs]
        · intro _; simpa [compactSize] using hpc
      · rw [Block.eval_stopped memory _ _ hs]
        exact compact_stopped memory program _ s hs _ _
  | action op =>
      by_cases hs : s.status = .running
      · have hf : program[s.pc]? = some op.instruction := by rw [hpc]; exact host.head
        obtain ⟨hd, hr, hp⟩ := compact_action_data memory op s
        refine ⟨(execute memory op.instruction s).1,
          [⟨s, op.instruction, (execute memory op.instruction s).1,
            (execute memory op.instruction s).2⟩], RunsTo.instruction hs hf,
          ?_, ?_, Nat.le_refl _, ?_⟩
        · simp only [Block.eval, Data.ofState, hs] at *
          rw [hd]; exact DataAgreesBelow.refl _ _
        · simpa only [Block.eval, Data.ofState, hs, List.filterMap_cons,
            List.filterMap_nil] using hr
        · intro h; simpa [compactSize, hpc] using hp h
      · rw [Block.eval_stopped memory _ _ hs]
        exact compact_stopped memory program _ s hs _ _
  | exit src =>
      by_cases hs : s.status = .running
      · have hf : program[s.pc]? = some (.halt src) := by rw [hpc]; exact host.head
        refine ⟨{ s with status := .halted (s.regs src) },
          [⟨s, .halt src, { s with status := .halted (s.regs src) }, none⟩],
          RunsTo.instruction hs hf, ?_, ?_, Nat.le_refl _, ?_⟩
        · simpa [Block.eval, Data.ofState, hs] using
            DataAgreesBelow.refl (compactCounter fresh depth) ⟨s.regs, .halted (s.regs src)⟩
        · simp [Block.eval, Data.ofState, hs]
        · simp
      · rw [Block.eval_stopped memory _ _ hs]
        exact compact_stopped memory program _ s hs _ _
  | seq first second ihf ihs =>
      have hf := ihf depth base s hpc bounded.1 host.append_left
      rw [Block.eval_seq]
      apply compact_follow hf (Block.eval_stopped memory second)
        (source_eval_congr memory second _ (bounded.2.mono (by simp [compactCounter])))
      intro t ht _ _
      have hh := ihs depth (base + compactSize first) t ht bounded.2
        (by simpa [compactAt_length] using host.append_right)
      simpa [compactBound, compactSize, Nat.add_assoc] using hh
  | ifZero condition zero nonzero ihz ihn =>
      by_cases hs : s.status = .running
      · have hbranch : program[s.pc]? =
            some (.branchZero condition (base + 1 + compactSize nonzero + 1)) := by
          rw [hpc]
          exact host.append_left.append_left.append_left.head
        have hn : HostedAt program (base + 1) (compactAt nonzero fresh depth (base + 1)) := by
          simpa using host.append_left.append_left.append_right
        have hj : HostedAt program (base + 1 + compactSize nonzero)
            [.jump (base + 1 + compactSize nonzero + 1 + compactSize zero)] := by
          simpa [compactAt, compactAt_length, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using host.append_left.append_right
        have hz : HostedAt program (base + 1 + compactSize nonzero + 1)
            (compactAt zero fresh depth (base + 1 + compactSize nonzero + 1)) := by
          simpa [compactAt, compactAt_length, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using host.append_right
        have hb := compact_branch memory program (compactCounter fresh depth) s condition
          (base + 1 + compactSize nonzero + 1) hs hbranch
        by_cases hc : s.regs condition = 0
        · simp only [hc, if_true] at hb
          have hzero := compact_follow hb (Block.eval_stopped memory zero)
            (source_eval_congr memory zero _ (bounded.2.1.mono (by simp [compactCounter])))
            (fun t ht _ _ => ihz _ _ t ht bounded.2.1 hz)
          have he : (⟨Data.ofState s, []⟩ : Evaluation).bind (zero.eval memory) =
              (Block.ifZero condition zero nonzero).eval memory (Data.ofState s) := by
            simp [Evaluation.bind, Block.eval, Data.ofState, hs, hc]
          rw [he] at hzero
          have hend : base + 1 + compactSize nonzero + 1 + compactSize zero =
              base + compactSize (.ifZero condition zero nonzero) := by simp [compactSize]; omega
          rw [hend] at hzero
          exact compact_budget_mono hzero (by simp only [compactBound]; omega)
        · simp only [hc, if_false, hpc] at hb
          have hnonzero := compact_follow hb (Block.eval_stopped memory nonzero)
            (source_eval_congr memory nonzero _ (bounded.2.2.mono (by simp [compactCounter])))
            (fun t ht _ _ => ihn _ _ t ht bounded.2.2 hn)
          have hall := compact_follow hnonzero
            (next := fun d => ⟨d, []⟩) (finish := base + 1 + compactSize nonzero + 1 + compactSize zero)
            (b := 1) (fun _ _ => rfl) (fun _ _ hd => ⟨hd, rfl⟩) (by
              intro t ht _ hstatus
              apply compact_jump memory program _ t _ hstatus
              rw [ht]; exact hj.head)
          have he : ((⟨Data.ofState s, []⟩ : Evaluation).bind (nonzero.eval memory)).bind
              (fun d => ⟨d, []⟩) =
              (Block.ifZero condition zero nonzero).eval memory (Data.ofState s) := by
            simp [Evaluation.bind, Block.eval, Data.ofState, hs, hc]
          rw [he] at hall
          have hend : base + 1 + compactSize nonzero + 1 + compactSize zero =
              base + compactSize (.ifZero condition zero nonzero) := by simp [compactSize]; omega
          rw [hend] at hall
          exact compact_budget_mono hall (by simp only [compactBound]; omega)
      · rw [Block.eval_stopped memory _ _ hs]
        exact compact_stopped memory program _ s hs _ _
  | «repeat» count body ih =>
      cases count with
      | zero =>
          rw [Block.eval_repeat]
          exact ⟨s, [], RunsTo.refl memory program s, DataAgreesBelow.refl _ _, rfl,
            Nat.le_refl _, fun _ => by simpa [compactSize] using hpc⟩
      | succ count =>
          by_cases hs : s.status = .running
          · let c := compactCounter fresh depth
            have hprefix : HostedAt program base
                [.constant c (count + 1), .constant (c + 1) 1,
                  .branchZero c (base + 5 + compactSize body)] := host.append_left.append_left
            have hbody : HostedAt program (base + 3)
                (compactAt body fresh (depth + 1) (base + 3)) := by
              simpa using host.append_left.append_right
            have htail : HostedAt program (base + 3 + compactSize body)
                [.arithmetic .sub c c (c + 1), .jump (base + 2)] := by
              have he : base +
                  ([Instruction.constant c (count + 1), .constant (c + 1) 1,
                    .branchZero c (base + 5 + compactSize body)] ++
                    compactAt body fresh (depth + 1) (base + 3)).length =
                  base + 3 + compactSize body := by
                simp [compactAt_length]
                omega
              have h := host.append_right
              rw [he] at h
              exact h
            let first := s.writeNext c (count + 1)
            let second := first.writeNext (c + 1) 1
            let ti : Transition := ⟨s, .constant c (count + 1), first, none⟩
            let tj : Transition := ⟨first, .constant (c + 1) 1, second, none⟩
            have hi : RunsTo memory program s first [ti] :=
              RunsTo.instruction hs (by rw [hpc]; exact hprefix.head)
            have hj : RunsTo memory program first second [tj] := by
              apply RunsTo.instruction (show first.status = .running from rfl)
              have h := hprefix 1 (by simp)
              simpa [first, State.writeNext, hpc] using h
            have hloop := compact_loop_realizes memory program body fresh depth base bounded
              (fun t ht => ih (depth + 1) (base + 3) t ht bounded hbody)
              (by simpa [c] using hprefix 2 (by simp)) htail.head
              (by
                have hj := htail 1 (by simp)
                have he : base + 3 + compactSize body + 1 = base + 4 + compactSize body := by omega
                simpa [he] using hj)
              (count + 1) second
              (by simp [second, first, State.writeNext, hpc, Nat.add_assoc])
              (by simp [second, first, State.writeNext, Registers.write, c])
              (by simp [second, State.writeNext, c])
            obtain ⟨final, ts, hx, hd, hr, hb, hp⟩ := hloop
            have sourceBound : BlockRegistersBelow c body := bounded.mono (by simp [c, compactCounter])
            have initialAgree : DataAgreesBelow c (Data.ofState second) (Data.ofState s) := by
              have h := ((DataAgreesBelow.refl c (Data.ofState s)).write_left_fresh
                c (count + 1) (Nat.le_refl _)).write_left_fresh (c + 1) 1 (by omega)
              simpa [second, first, State.writeNext, Data.ofState, hs] using h
            have agree := compact_iterate_congr memory body c sourceBound (count + 1)
              (Data.ofState second) (Data.ofState s) initialAgree
            refine ⟨final, [ti] ++ [tj] ++ ts, (hi.trans hj).trans hx, ?_, ?_, ?_, ?_⟩
            · simpa only [Block.eval_repeat] using hd.trans agree.1
            · simpa only [List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
                ti, tj, List.nil_append, Block.eval_repeat] using hr.trans agree.2
            · simp only [List.length_append, List.length_cons, List.length_nil, compactBound]
              omega
            · simpa [compactSize, Nat.add_assoc] using hp
          · rw [Block.eval_stopped memory _ _ hs]
            exact compact_stopped memory program _ s hs _ _

theorem compact_run_extend_stopped (memory : Memory) (program : Program)
    (s : State) (used budget : Nat) (hbound : used ≤ budget)
    (hstop : step memory program (run memory program used s).final = none) :
    run memory program budget s = run memory program used s := by
  rw [← Nat.add_sub_of_le hbound, run_add]
  dsimp only
  rw [run_of_step_none memory program _ _ hstop]
  simp

/-- Adequacy is derived from an actual segment ending at a terminal fetch. -/
theorem compact_compile_run (memory : Memory) (block : Block) (fresh depth : Nat)
    (s : State) (hpc : s.pc = 0) (bounded : BlockRegistersBelow fresh block)
    (fuel : Nat) (enough : compactBound block ≤ fuel) :
    DataAgreesBelow (compactCounter fresh depth)
      (Data.ofState (run memory (compactAt block fresh depth 0) fuel s).final)
      (block.eval memory (Data.ofState s)).final ∧
    (run memory (compactAt block fresh depth 0) fuel s).reads =
      (block.eval memory (Data.ofState s)).reads ∧
    (run memory (compactAt block fresh depth 0) fuel s).steps ≤ compactBound block ∧
    step memory (compactAt block fresh depth 0)
      (run memory (compactAt block fresh depth 0) fuel s).final = none := by
  obtain ⟨final, ts, hx, hd, hr, hb, hp⟩ :=
    compact_realizes memory (compactAt block fresh depth 0) block fresh depth 0 s hpc
      bounded (HostedAt.self _)
  have hs : step memory (compactAt block fresh depth 0) final = none := by
    cases hstatus : final.status with
    | running =>
        have hf : (compactAt block fresh depth 0)[final.pc]? = none := by
          rw [hp hstatus]
          apply List.getElem?_eq_none
          simp [compactAt_length]
        simp [step, hstatus, hf]
    | halted value => simp [step, hstatus]
    | fault => simp [step, hstatus]
  have he := compact_run_extend_stopped memory (compactAt block fresh depth 0) s ts.length fuel
    (Nat.le_trans hb enough) (by unfold RunsTo at hx; simpa only [hx] using hs)
  rw [he]
  unfold RunsTo at hx
  simpa only [hx, Run.reads, Run.steps] using And.intro hd (And.intro hr (And.intro hb hs))

/-- Appended halt preserves an earlier halt or fault and the exact attempted
read order. Source register agreement is sufficient because the halt executes
on a observed output register; scratch never carries an answer. -/
theorem compact_compile_with_halt (memory : Memory) (block : Block) (fresh output : Nat)
    (s : State) (hpc : s.pc = 0) (bounded : BlockRegistersBelow fresh block)
    (hout : output < fresh) :
    let source := block.eval memory (Data.ofState s)
    let program := compactAt block fresh 0 0 ++ [Instruction.halt output]
    let actual := run memory program (compactBound block + 1) s
    actual.result = (match source.final.status with
      | .running => some (source.final.regs output)
      | .halted value => some value
      | .fault => none) ∧
    actual.reads = source.reads ∧ actual.steps ≤ compactBound block + 1 ∧
    actual.final.status ≠ .running := by
  dsimp only
  have h := compact_compile_run memory (.seq block (.exit output)) fresh 0 s hpc
    ⟨bounded, hout⟩ (compactBound block + 1) (Nat.le_refl _)
  have hd : (run memory (compactAt block fresh 0 0 ++ [.halt output])
      (compactBound block + 1) s).final.status =
      ((Block.exit output).eval memory (block.eval memory (Data.ofState s)).final).final.status := by
    simpa [compactAt, compactBound, Block.eval_seq, Evaluation.bind] using h.1.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Run.result, hd]
    cases hs : (block.eval memory (Data.ofState s)).final.status <;> simp [Block.eval, hs]
  · have exitReads (d : Data) : ((Block.exit output).eval memory d).reads = [] := by
      cases hs : d.status <;> simp [Block.eval, hs]
    simpa [compactAt, compactBound, Block.eval_seq, Evaluation.bind, exitReads] using h.2.1
  · simpa [compactAt, compactBound] using h.2.2.1
  · rw [hd]
    cases hs : (block.eval memory (Data.ofState s)).final.status <;> simp [Block.eval, hs]

namespace CompactConsumers

theorem compact_realizes_expectedType (memory : Memory) (program : Program) (block : Block)
    (fresh depth base : Nat) (s : State) (hpc : s.pc = base)
    (bounded : BlockRegistersBelow fresh block)
    (host : HostedAt program base (compactAt block fresh depth base)) :
    ∃ final transitions,
      RunsTo memory program s final transitions ∧
      final.status = (block.eval memory (Data.ofState s)).final.status ∧
      (∀ r, r < compactCounter fresh depth →
        final.regs r = (block.eval memory (Data.ofState s)).final.regs r) ∧
      transitions.filterMap (·.receipt) = (block.eval memory (Data.ofState s)).reads ∧
      transitions.length ≤ compactBound block ∧
      (final.status = .running → final.pc = base + compactSize block) := by
  obtain ⟨final, ts, hx, hd, hr, hb, hp⟩ :=
    compact_realizes memory program block fresh depth base s hpc bounded host
  exact ⟨final, ts, hx, hd.1, hd.2, hr, hb, hp⟩

theorem compact_halt_expectedType (memory : Memory) (block : Block) (fresh output : Nat)
    (s : State) (hpc : s.pc = 0) (bounded : BlockRegistersBelow fresh block)
    (hout : output < fresh) :
    let source := block.eval memory (Data.ofState s)
    let actual := run memory (compactAt block fresh 0 0 ++ [Instruction.halt output])
      (compactBound block + 1) s
    actual.result = (match source.final.status with
      | .running => some (source.final.regs output)
      | .halted value => some value
      | .fault => none) ∧ actual.reads = source.reads ∧
      actual.steps ≤ compactBound block + 1 ∧ actual.final.status ≠ .running :=
  compact_compile_with_halt memory block fresh output s hpc bounded hout

private def initial : State := ⟨fun _ => 0, 0, .running⟩
private def nestedLoads : Block :=
  .seq (.repeat 2 (.repeat 3 (.action (.load 1 0)))) (.exit 1)

/-- Literal six-read expectation checks nested fresh counters and charged control. -/
theorem nested_loop_execution :
    compactSize nestedLoads = 12 ∧ compactBound nestedLoads = 40 ∧
    (run [7] (compactAt nestedLoads 2 0 0) 40 initial).result = some 7 ∧
    (run [7] (compactAt nestedLoads 2 0 0) 40 initial).reads =
      [⟨0, some 7⟩, ⟨0, some 7⟩, ⟨0, some 7⟩, ⟨0, some 7⟩, ⟨0, some 7⟩, ⟨0, some 7⟩] ∧
    (run [7] (compactAt nestedLoads 2 0 0) 40 initial).steps = 40 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Faulting inside a nested body records the attempt and skips loop control. -/
theorem nested_loop_fault :
    (run [] (compactAt nestedLoads 2 0 0) 40 initial).final.status = .fault ∧
    (run [] (compactAt nestedLoads 2 0 0) 40 initial).reads = [⟨0, none⟩] ∧
    (run [] (compactAt nestedLoads 2 0 0) 40 initial).steps = 7 :=
  ⟨rfl, rfl, rfl⟩

/-- Zero repetitions emit no initialization and preserve initially stopped states. -/
theorem zero_and_stopped_loops :
    compactAt (.repeat 0 (.exit 0)) 1 0 0 = [] ∧
    (run [] (compactAt nestedLoads 2 0 0) 40 { initial with status := .halted 9 }).result = some 9 ∧
    (run [] (compactAt nestedLoads 2 0 0) 40 { initial with status := .fault }).steps = 0 :=
  ⟨rfl, rfl, rfl⟩

theorem counter_collision_rejected :
    ¬ BlockRegistersBelow 2 (.repeat 1 (.action (.constant 2 99))) := by
  simp [BlockRegistersBelow, ActionRegistersBelow]

end CompactConsumers

end RMQ.SuccinctFinal.PackedWordRAM.Optimization
