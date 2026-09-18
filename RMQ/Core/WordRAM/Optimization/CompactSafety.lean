import RMQ.Core.WordRAM.Optimization.CompactProof

/-!
# Word safety for the actual counted-loop execution

Global entry and intermediate state fit is retained independently of agreement
on source registers. Static field hypotheses quantify every emitted instruction.
-/

namespace RMQ.SuccinctFinal.PackedWordRAM.Optimization

open Structured

def CompactSafeRealizes (width : Nat) (memory : Memory) (program : Program) (observed : Nat)
    (s : State) (expected : Evaluation) (finish budget : Nat) : Prop :=
  ∃ final transitions,
    RunsTo memory program s final transitions ∧
    DataAgreesBelow observed (Data.ofState final) expected.final ∧
    transitions.filterMap (·.receipt) = expected.reads ∧
    transitions.length ≤ budget ∧
    (final.status = .running → final.pc = finish) ∧
    final.Fits width ∧ TraceSafe width transitions

theorem compact_traceSafe_append {width : Nat} {a b : List Transition}
    (ha : TraceSafe width a) (hb : TraceSafe width b) : TraceSafe width (a ++ b) := by
  intro t ht
  rcases List.mem_append.mp ht with ht | ht
  · exact ha t ht
  · exact hb t ht

theorem compact_safe_stopped (width : Nat) (memory : Memory) (program : Program)
    (observed : Nat) (s : State) (fit : s.Fits width) (hs : s.status ≠ .running)
    (finish budget : Nat) :
    CompactSafeRealizes width memory program observed s ⟨Data.ofState s, []⟩ finish budget :=
  ⟨s, [], RunsTo.refl memory program s, DataAgreesBelow.refl _ _, rfl,
    Nat.zero_le _, fun h => (hs h).elim, fit, fun _ h => (List.not_mem_nil h).elim⟩

theorem compact_safe_budget_mono {width : Nat} {memory : Memory} {program : Program}
    {observed : Nat} {s : State} {expected : Evaluation} {finish a b : Nat}
    (h : CompactSafeRealizes width memory program observed s expected finish a) (hab : a ≤ b) :
    CompactSafeRealizes width memory program observed s expected finish b := by
  obtain ⟨t, ts, hx, hd, hr, hc, hp, hf, ht⟩ := h
  exact ⟨t, ts, hx, hd, hr, Nat.le_trans hc hab, hp, hf, ht⟩

theorem compact_safe_follow {width : Nat} {memory : Memory} {program : Program} {observed : Nat}
    {s : State} {first : Evaluation} {next : Data → Evaluation} {middle finish a b : Nat}
    (hfirst : CompactSafeRealizes width memory program observed s first middle a)
    (stopped : ∀ d, d.status ≠ .running → next d = ⟨d, []⟩)
    (congr : ∀ left right, DataAgreesBelow observed left right →
      EvaluationAgreesBelow observed (next left) (next right))
    (hnext : ∀ t, t.pc = middle → DataAgreesBelow observed (Data.ofState t) first.final →
      t.status = .running → t.Fits width →
      CompactSafeRealizes width memory program observed t (next (Data.ofState t)) finish b) :
    CompactSafeRealizes width memory program observed s (first.bind next) finish (a + b) := by
  obtain ⟨t, ts, hx, hd, hr, hc, hp, hf, ht⟩ := hfirst
  by_cases hs : t.status = .running
  · obtain ⟨u, us, hy, he, hur, hb, hq, huf, hut⟩ := hnext t (hp hs) hd hs hf
    have agree := congr (Data.ofState t) first.final hd
    refine ⟨u, ts ++ us, hx.trans hy, he.trans agree.1, ?_, ?_, hq, huf,
      compact_traceSafe_append ht hut⟩
    · simpa only [Evaluation.bind, List.filterMap_append, hr, hur] using
        congrArg (first.reads ++ ·) agree.2
    · simp only [List.length_append]; omega
  · have hstop := stopped first.final (by intro h; exact hs (hd.1.trans h))
    refine ⟨t, ts, hx, ?_, ?_, by omega, fun h => (hs h).elim, hf, ht⟩
    · simpa only [Evaluation.bind, hstop] using hd
    · simpa only [Evaluation.bind, hstop, List.append_nil] using hr

theorem compact_safe_jump (width : Nat) (memory : Memory) (program : Program)
    (observed : Nat) (s : State) (target : Nat) (fit : s.Fits width)
    (hs : s.status = .running) (fields : (Instruction.jump target).Fits width)
    (bound : target < 2 ^ width) (hf : program[s.pc]? = some (.jump target)) :
    CompactSafeRealizes width memory program observed s ⟨Data.ofState s, []⟩ target 1 := by
  have afterFit : ({ s with pc := target } : State).Fits width := ⟨bound, fit.2⟩
  refine ⟨{ s with pc := target }, [⟨s, .jump target, { s with pc := target }, none⟩],
    RunsTo.instruction hs hf, DataAgreesBelow.refl _ _, rfl, Nat.le_refl _,
    fun _ => rfl, afterFit, ?_⟩
  intro t ht
  have he := List.mem_singleton.mp ht
  subst t
  exact ⟨⟨fields, fit, trivial⟩, afterFit⟩

theorem compact_safe_branch (width : Nat) (memory : Memory) (program : Program)
    (observed : Nat) (s : State) (condition target : Nat) (fit : s.Fits width)
    (hs : s.status = .running) (fields : (Instruction.branchZero condition target).Fits width)
    (targetBound : target < 2 ^ width) (nextBound : s.pc + 1 < 2 ^ width)
    (hf : program[s.pc]? = some (.branchZero condition target)) :
    CompactSafeRealizes width memory program observed s ⟨Data.ofState s, []⟩
      (if s.regs condition = 0 then target else s.pc + 1) 1 := by
  let t := { s with pc := if s.regs condition = 0 then target else s.pc + 1 }
  have afterFit : t.Fits width := by
    refine ⟨?_, fit.2⟩
    dsimp [t]; split <;> assumption
  refine ⟨t, [⟨s, .branchZero condition target, t, none⟩], RunsTo.instruction hs hf,
    DataAgreesBelow.refl _ _, rfl, Nat.le_refl _, fun _ => rfl, afterFit, ?_⟩
  intro u hu
  have he := List.mem_singleton.mp hu
  subst u
  exact ⟨⟨fields, fit, trivial⟩, afterFit⟩

theorem compact_constant_value_fits {width dst value : Nat}
    (fields : (Instruction.constant dst value).Fits width) : value < 2 ^ width := by
  exact fields value (by simp [Instruction.encoding, Instruction.operands])

/-- Safe loop execution retains the actual global fit at every handoff. -/
theorem compact_safe_loop_realizes (width : Nat) (memory : Memory) (program : Program)
    (body : Block) (fresh depth base : Nat) (bounded : BlockRegistersBelow fresh body)
    (bodyRun : ∀ t, t.pc = base + 3 → t.Fits width →
      body.Safe memory width (Data.ofState t) →
      CompactSafeRealizes width memory program (compactCounter fresh (depth + 1)) t
        (body.eval memory (Data.ofState t)) (base + 3 + compactSize body) (compactBound body))
    (branch : program[base + 2]? =
      some (.branchZero (compactCounter fresh depth) (base + 5 + compactSize body)))
    (decrement : program[base + 3 + compactSize body]? = some
      (.arithmetic .sub (compactCounter fresh depth) (compactCounter fresh depth)
        (compactCounter fresh depth + 1)))
    (jump : program[base + 4 + compactSize body]? = some (.jump (base + 2)))
    (branchFields : (Instruction.branchZero (compactCounter fresh depth)
      (base + 5 + compactSize body)).Fits width)
    (decrementFields : (Instruction.arithmetic .sub (compactCounter fresh depth)
      (compactCounter fresh depth) (compactCounter fresh depth + 1)).Fits width)
    (jumpFields : (Instruction.jump (base + 2)).Fits width)
    (endBound : base + 5 + compactSize body < 2 ^ width)
    (remaining : Nat) (s : State) (hpc : s.pc = base + 2)
    (hc : s.regs (compactCounter fresh depth) = remaining)
    (hu : s.regs (compactCounter fresh depth + 1) = 1) (fit : s.Fits width)
    (iterations : IterationsSafe (body.Safe memory width) (body.eval memory)
      remaining (Data.ofState s)) :
    CompactSafeRealizes width memory program (compactCounter fresh depth) s
      (iterate (body.eval memory) remaining (Data.ofState s))
      (base + 5 + compactSize body) (1 + remaining * (compactBound body + 3)) := by
  let c := compactCounter fresh depth
  have freshC : fresh ≤ c := by dsimp [c, compactCounter]; omega
  have nextC : compactCounter fresh (depth + 1) = c + 2 := by
    dsimp [c, compactCounter]; omega
  induction remaining generalizing s with
  | zero =>
      by_cases hs : s.status = .running
      · have h := compact_safe_branch width memory program c s c
          (base + 5 + compactSize body) fit hs branchFields endBound (by omega)
          (by simpa [c, hpc] using branch)
        simpa [hc, c, iterate] using h
      · exact compact_safe_stopped width memory program c s fit hs _ _
  | succ remaining ih =>
      by_cases hs : s.status = .running
      · let entered : State := { s with pc := base + 3 }
        let bt : Transition := ⟨s, .branchZero c (base + 5 + compactSize body), entered, none⟩
        have enteredFit : entered.Fits width := ⟨by dsimp [entered]; omega, fit.2⟩
        have branchSafe : TraceSafe width [bt] := by
          intro t ht; have he := List.mem_singleton.mp ht; subst t
          exact ⟨⟨branchFields, fit, trivial⟩, enteredFit⟩
        have hbranch : RunsTo memory program s entered [bt] := by
          have h := RunsTo.instruction (memory := memory) hs
            (show program[s.pc]? = some (.branchZero c (base + 5 + compactSize body)) by
              simpa [c, hpc] using branch)
          simpa [execute, hc, c, hpc, entered, bt] using h
        obtain ⟨t, ts, hbody, hd, hr, hb, hp, tFit, bodySafe⟩ :=
          bodyRun entered rfl enteredFit iterations.1
        have hdLow : DataAgreesBelow c (Data.ofState t)
            (body.eval memory (Data.ofState s)).final := by
          apply hd.mono; rw [nextC]; omega
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
          have localSafe : (Action.arithmetic .sub c c (c + 1)).LocalSafe memory width
              (Data.ofState t) := by
            have countFit := tFit.2.1 c
            simp only [tc] at countFit
            simp [Action.LocalSafe, Data.ofState, Arithmetic.eval, tc, tu]
            omega
          have decInfo := (Action.arithmetic .sub c c (c + 1)).execute_safe memory width t
            tFit decrementFields localSafe (by rw [hp ht]; omega)
          have decFit : dec.Fits width := by
            simpa [Action.instruction, execute, Arithmetic.eval, tc, tu, dec] using decInfo.2
          have decrementSafe : TraceSafe width [dt] := by
            intro u hu; have he := List.mem_singleton.mp hu; subst u
            exact ⟨decInfo.1, decFit⟩
          have hdec : RunsTo memory program t dec [dt] := by
            have h := RunsTo.instruction (memory := memory) ht
              (show program[t.pc]? = some (.arithmetic .sub c c (c + 1)) by
                simpa [c, hp ht] using decrement)
            simpa [execute, Arithmetic.eval, tc, tu, dec, dt] using h
          let next : State := { dec with pc := base + 2 }
          let jt : Transition := ⟨dec, .jump (base + 2), next, none⟩
          have nextFit : next.Fits width := ⟨by dsimp [next]; omega, decFit.2⟩
          have jumpSafe : TraceSafe width [jt] := by
            intro u hu; have he := List.mem_singleton.mp hu; subst u
            exact ⟨⟨jumpFields, decFit, trivial⟩, nextFit⟩
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
          have nextAgree : DataAgreesBelow c (Data.ofState next)
              (body.eval memory (Data.ofState s)).final := by
            simpa only [next, dec, State.writeNext, Data.ofState, ht] using
              hdLow.write_left_fresh c remaining (Nat.le_refl _)
          have nextSafe := source_safe_transport memory width c (.repeat remaining body)
            (bounded.mono freshC) (body.eval memory (Data.ofState s)).final (Data.ofState next)
            nextAgree.symm nextFit.2
            (Block.safe_repeat (memory := memory) (width := width) (count := remaining) (body := body)
              (body.eval_fits memory width _ iterations.1) iterations.2)
          obtain ⟨u, us, htail, he, hreads, hcost, hend, finalFit, tailSafe⟩ :=
            ih next rfl nextc nextu nextFit (nextSafe.2 rfl)
          have tailAgree := compact_iterate_congr memory body c (bounded.mono freshC)
            remaining (Data.ofState next) (body.eval memory (Data.ofState s)).final nextAgree
          refine ⟨u, [bt] ++ ts ++ [dt] ++ [jt] ++ us,
            (((hbranch.trans hbody).trans hdec).trans hjump).trans htail,
            he.trans tailAgree.1, ?_, ?_, hend, finalFit,
            compact_traceSafe_append (compact_traceSafe_append
              (compact_traceSafe_append (compact_traceSafe_append branchSafe bodySafe)
                decrementSafe) jumpSafe) tailSafe⟩
          · simp only [List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
              bt, dt, jt, List.nil_append, List.append_nil, hr, hreads]
            exact congrArg ((body.eval memory (Data.ofState s)).reads ++ ·) tailAgree.2
          · simp only [List.length_append, List.length_cons, List.length_nil]
            simp only [Nat.succ_mul] at *
            omega
        · have sourceStop : (body.eval memory (Data.ofState s)).final.status ≠ .running := by
            intro h; exact ht (hdLow.1.trans h)
          have stopped := compact_iterate_stopped memory body remaining _ sourceStop
          refine ⟨t, [bt] ++ ts, hbranch.trans hbody, ?_, ?_, ?_, fun h => (ht h).elim,
            tFit, compact_traceSafe_append branchSafe bodySafe⟩
          · simpa only [iterate, stopped] using hdLow
          · simpa only [List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
              bt, List.nil_append, iterate, stopped, List.append_nil] using hr
          · simp only [List.length_append, List.length_cons, List.length_nil, Nat.succ_mul]
            omega
      · rw [compact_iterate_stopped memory body _ _ hs]
        exact compact_safe_stopped width memory program c s fit hs _ _

/-- Constructor-exhaustive emitted fields, actual entry fit and source safety
produce one semantic segment whose every actual transition is word safe. -/
theorem compact_safe_realizes (width : Nat) (memory : Memory) (program : Program)
    (block : Block) (fresh depth base : Nat) (s : State) (hpc : s.pc = base)
    (bounded : BlockRegistersBelow fresh block)
    (host : HostedAt program base (compactAt block fresh depth base))
    (fields : ∀ instruction ∈ compactAt block fresh depth base, instruction.Fits width)
    (bound : base + compactSize block < 2 ^ width)
    (fit : s.Fits width) (safe : block.Safe memory width (Data.ofState s)) :
    CompactSafeRealizes width memory program (compactCounter fresh depth) s
      (block.eval memory (Data.ofState s)) (base + compactSize block) (compactBound block) := by
  induction block generalizing depth base s with
  | skip =>
      by_cases hs : s.status = .running
      · refine ⟨s, [], RunsTo.refl memory program s, ?_, ?_, Nat.le_refl _, ?_, fit, ?_⟩
        · simpa [Block.eval, Data.ofState, hs] using
            DataAgreesBelow.refl (compactCounter fresh depth) (Data.ofState s)
        · simp [Block.eval, Data.ofState, hs]
        · intro _; simpa [compactSize] using hpc
        · intro _ h; exact (List.not_mem_nil h).elim
      · rw [Block.eval_stopped memory _ _ hs]
        exact compact_safe_stopped width memory program _ s fit hs _ _
  | action op =>
      by_cases hs : s.status = .running
      · have hf : program[s.pc]? = some op.instruction := by rw [hpc]; exact host.head
        obtain ⟨hd, hr, hp⟩ := compact_action_data memory op s
        obtain ⟨instructionSafe, afterFit⟩ := op.execute_safe memory width s fit
          (fields _ (by simp [compactAt])) (safe.2 hs)
          (by simpa [hpc, compactSize] using bound)
        refine ⟨(execute memory op.instruction s).1,
          [⟨s, op.instruction, (execute memory op.instruction s).1,
            (execute memory op.instruction s).2⟩], RunsTo.instruction hs hf,
          ?_, ?_, Nat.le_refl _, ?_, afterFit, ?_⟩
        · simp only [Block.eval, Data.ofState, hs] at *
          rw [hd]; exact DataAgreesBelow.refl _ _
        · simpa only [Block.eval, Data.ofState, hs, List.filterMap_cons,
            List.filterMap_nil] using hr
        · intro h; simpa [compactSize, hpc] using hp h
        · intro t ht; have he := List.mem_singleton.mp ht; subst t
          exact ⟨instructionSafe, afterFit⟩
      · rw [Block.eval_stopped memory _ _ hs]
        exact compact_safe_stopped width memory program _ s fit hs _ _
  | exit src =>
      by_cases hs : s.status = .running
      · have hf : program[s.pc]? = some (.halt src) := by rw [hpc]; exact host.head
        have haltFit : ({ s with status := .halted (s.regs src) } : State).Fits width :=
          ⟨fit.1, fit.2.1, fun value hv => by cases hv; exact fit.2.1 src⟩
        refine ⟨{ s with status := .halted (s.regs src) },
          [⟨s, .halt src, { s with status := .halted (s.regs src) }, none⟩],
          RunsTo.instruction hs hf, ?_, ?_, Nat.le_refl _, ?_, haltFit, ?_⟩
        · simpa [Block.eval, Data.ofState, hs] using
            DataAgreesBelow.refl (compactCounter fresh depth) ⟨s.regs, .halted (s.regs src)⟩
        · simp [Block.eval, Data.ofState, hs]
        · simp
        · intro t ht; have he := List.mem_singleton.mp ht; subst t
          exact ⟨⟨fields _ (by simp [compactAt]), fit, trivial⟩, haltFit⟩
      · rw [Block.eval_stopped memory _ _ hs]
        exact compact_safe_stopped width memory program _ s fit hs _ _
  | seq first second ihf ihs =>
      by_cases hs : s.status = .running
      · have hf := ihf depth base s hpc bounded.1 host.append_left
          (fun i hi => fields i (by simp [compactAt, hi]))
          (by simp only [compactSize] at bound; omega) fit (safe.2 hs).1
        rw [Block.eval_seq]
        apply compact_safe_follow hf (Block.eval_stopped memory second)
          (source_eval_congr memory second _ (bounded.2.mono (by simp [compactCounter])))
        intro t ht hd _ tfit
        have hh := ihs depth (base + compactSize first) t ht bounded.2
          (by simpa [compactAt_length] using host.append_right)
          (fun i hi => fields i (by simp [compactAt, hi]))
          (by simpa [compactSize, Nat.add_assoc] using bound) tfit
          (source_safe_transport memory width _ second (bounded.2.mono (by simp [compactCounter]))
            _ _ hd.symm tfit.2 (safe.2 hs).2)
        simpa [compactBound, compactSize, Nat.add_assoc] using hh
      · rw [Block.eval_stopped memory _ _ hs]
        exact compact_safe_stopped width memory program _ s fit hs _ _
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
        have endBound : base + 1 + compactSize nonzero + 1 + compactSize zero < 2 ^ width := by
          simpa [compactSize, Nat.add_assoc] using bound
        have hb := compact_safe_branch width memory program (compactCounter fresh depth) s condition
          (base + 1 + compactSize nonzero + 1) fit hs
          (fields _ (by simp [compactAt])) (by omega) (by omega) hbranch
        by_cases hc : s.regs condition = 0
        · simp only [hc, if_true] at hb
          have hzero := compact_safe_follow hb (Block.eval_stopped memory zero)
            (source_eval_congr memory zero _ (bounded.2.1.mono (by simp [compactCounter]))) (by
              intro t ht hd _ tfit
              apply ihz depth _ t ht bounded.2.1 hz
                (fun i hi => fields i (by simp [compactAt, hi])) endBound tfit
              apply source_safe_transport memory width _ zero
                (bounded.2.1.mono (by simp [compactCounter])) _ _ hd.symm tfit.2
              simpa [Data.ofState, hc] using safe.2 hs)
          have he : (⟨Data.ofState s, []⟩ : Evaluation).bind (zero.eval memory) =
              (Block.ifZero condition zero nonzero).eval memory (Data.ofState s) := by
            simp [Evaluation.bind, Block.eval, Data.ofState, hs, hc]
          rw [he] at hzero
          have hend : base + 1 + compactSize nonzero + 1 + compactSize zero =
              base + compactSize (.ifZero condition zero nonzero) := by simp [compactSize]; omega
          rw [hend] at hzero
          exact compact_safe_budget_mono hzero (by simp only [compactBound]; omega)
        · simp only [hc, if_false, hpc] at hb
          have hnonzero := compact_safe_follow hb (Block.eval_stopped memory nonzero)
            (source_eval_congr memory nonzero _ (bounded.2.2.mono (by simp [compactCounter]))) (by
              intro t ht hd _ tfit
              apply ihn depth _ t ht bounded.2.2 hn
                (fun i hi => fields i (by simp [compactAt, hi])) (by omega) tfit
              apply source_safe_transport memory width _ nonzero
                (bounded.2.2.mono (by simp [compactCounter])) _ _ hd.symm tfit.2
              simpa [Data.ofState, hc] using safe.2 hs)
          have hall := compact_safe_follow hnonzero
            (next := fun d => ⟨d, []⟩) (finish := base + 1 + compactSize nonzero + 1 + compactSize zero)
            (b := 1) (fun _ _ => rfl) (fun _ _ hd => ⟨hd, rfl⟩) (by
              intro t ht _ hstatus tfit
              apply compact_safe_jump width memory program _ t _ tfit hstatus
                (fields _ (by simp [compactAt])) endBound
              rw [ht]; exact hj.head)
          have he : ((⟨Data.ofState s, []⟩ : Evaluation).bind (nonzero.eval memory)).bind
              (fun d => ⟨d, []⟩) =
              (Block.ifZero condition zero nonzero).eval memory (Data.ofState s) := by
            simp [Evaluation.bind, Block.eval, Data.ofState, hs, hc]
          rw [he] at hall
          have hend : base + 1 + compactSize nonzero + 1 + compactSize zero =
              base + compactSize (.ifZero condition zero nonzero) := by simp [compactSize]; omega
          rw [hend] at hall
          exact compact_safe_budget_mono hall (by simp only [compactBound]; omega)
      · rw [Block.eval_stopped memory _ _ hs]
        exact compact_safe_stopped width memory program _ s fit hs _ _
  | «repeat» count body ih =>
      cases count with
      | zero =>
          rw [Block.eval_repeat]
          exact ⟨s, [], RunsTo.refl memory program s, DataAgreesBelow.refl _ _, rfl,
            Nat.le_refl _, (fun _ => by simpa [compactSize] using hpc), fit,
            fun _ h => (List.not_mem_nil h).elim⟩
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
            have endBound : base + 5 + compactSize body < 2 ^ width := by
              simpa [compactSize, Nat.add_assoc] using bound
            let first := s.writeNext c (count + 1)
            let second := first.writeNext (c + 1) 1
            let ti : Transition := ⟨s, .constant c (count + 1), first, none⟩
            let tj : Transition := ⟨first, .constant (c + 1) 1, second, none⟩
            have fi : (Instruction.constant c (count + 1)).Fits width :=
              fields _ (by simp [compactAt, c])
            have fj : (Instruction.constant (c + 1) 1).Fits width :=
              fields _ (by simp [compactAt, c])
            have infoI := (Action.constant c (count + 1)).execute_safe memory width s fit fi
              (compact_constant_value_fits fi) (by omega)
            have firstFit : first.Fits width := infoI.2
            have infoJ := (Action.constant (c + 1) 1).execute_safe memory width first firstFit fj
              (compact_constant_value_fits fj) (by dsimp [first, State.writeNext]; omega)
            have secondFit : second.Fits width := infoJ.2
            have tiSafe : TraceSafe width [ti] := by
              intro t ht; have he := List.mem_singleton.mp ht; subst t
              exact ⟨infoI.1, firstFit⟩
            have tjSafe : TraceSafe width [tj] := by
              intro t ht; have he := List.mem_singleton.mp ht; subst t
              exact ⟨infoJ.1, secondFit⟩
            have hi : RunsTo memory program s first [ti] :=
              RunsTo.instruction hs (by rw [hpc]; exact hprefix.head)
            have hj : RunsTo memory program first second [tj] := by
              apply RunsTo.instruction (show first.status = .running from rfl)
              have h := hprefix 1 (by simp)
              simpa [first, State.writeNext, hpc] using h
            have sourceBound : BlockRegistersBelow c body := bounded.mono (by simp [c, compactCounter])
            have initialAgree : DataAgreesBelow c (Data.ofState second) (Data.ofState s) := by
              have h := ((DataAgreesBelow.refl c (Data.ofState s)).write_left_fresh
                c (count + 1) (Nat.le_refl _)).write_left_fresh (c + 1) 1 (by omega)
              simpa [second, first, State.writeNext, Data.ofState, hs] using h
            have secondSafe := source_safe_transport memory width c (.repeat (count + 1) body)
              sourceBound (Data.ofState s) (Data.ofState second) initialAgree.symm secondFit.2 safe
            have hloop := compact_safe_loop_realizes width memory program body fresh depth base bounded
              (fun t ht tf ts => ih (depth + 1) (base + 3) t ht bounded hbody
                (fun i hi => fields i (by simp [compactAt, hi])) (by omega) tf ts)
              (by simpa [c] using hprefix 2 (by simp)) htail.head
              (by
                have hj := htail 1 (by simp)
                have he : base + 3 + compactSize body + 1 = base + 4 + compactSize body := by omega
                simpa [he] using hj)
              (fields _ (by simp [compactAt])) (fields _ (by simp [compactAt]))
              (fields _ (by simp [compactAt])) endBound (count + 1) second
              (by simp [second, first, State.writeNext, hpc, Nat.add_assoc])
              (by simp [second, first, State.writeNext, Registers.write, c])
              (by simp [second, State.writeNext, c]) secondFit (secondSafe.2 rfl)
            obtain ⟨final, ts, hx, hd, hr, hb, hp, finalFit, traceSafe⟩ := hloop
            have agree := compact_iterate_congr memory body c sourceBound (count + 1)
              (Data.ofState second) (Data.ofState s) initialAgree
            refine ⟨final, [ti] ++ [tj] ++ ts, (hi.trans hj).trans hx, ?_, ?_, ?_, ?_, finalFit,
              compact_traceSafe_append (compact_traceSafe_append tiSafe tjSafe) traceSafe⟩
            · simpa only [Block.eval_repeat] using hd.trans agree.1
            · simpa only [List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
                ti, tj, List.nil_append, Block.eval_repeat] using hr.trans agree.2
            · simp only [List.length_append, List.length_cons, List.length_nil, compactBound]
              omega
            · simpa [compactSize, Nat.add_assoc] using hp
          · rw [Block.eval_stopped memory _ _ hs]
            exact compact_safe_stopped width memory program _ s fit hs _ _

/-- Every adequate standalone run has the same semantic observations and is
safe at every transition and every fuel prefix, including the initial state. -/
theorem compact_compile_safe_run (width : Nat) (memory : Memory) (block : Block)
    (fresh depth : Nat) (s : State) (hpc : s.pc = 0)
    (bounded : BlockRegistersBelow fresh block)
    (fields : ∀ instruction ∈ compactAt block fresh depth 0, instruction.Fits width)
    (bound : compactSize block < 2 ^ width) (fit : s.Fits width)
    (safe : block.Safe memory width (Data.ofState s))
    (fuel : Nat) (enough : compactBound block ≤ fuel) :
    DataAgreesBelow (compactCounter fresh depth)
      (Data.ofState (run memory (compactAt block fresh depth 0) fuel s).final)
      (block.eval memory (Data.ofState s)).final ∧
    (run memory (compactAt block fresh depth 0) fuel s).reads =
      (block.eval memory (Data.ofState s)).reads ∧
    (run memory (compactAt block fresh depth 0) fuel s).steps ≤ compactBound block ∧
    (run memory (compactAt block fresh depth 0) fuel s).final.Fits width ∧
    TraceSafe width (run memory (compactAt block fresh depth 0) fuel s).transitions ∧
    (∀ index, index ≤ fuel → (run memory (compactAt block fresh depth 0) index s).final.Fits width) := by
  obtain ⟨final, ts, hx, hd, hr, hb, hp, finalFit, traceSafe⟩ :=
    compact_safe_realizes width memory (compactAt block fresh depth 0) block fresh depth 0 s hpc
      bounded (HostedAt.self _) fields (by simpa using bound) fit safe
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
  have actualSafe : TraceSafe width (run memory (compactAt block fresh depth 0) fuel s).transitions := by
    rw [he]; unfold RunsTo at hx; simpa only [hx] using traceSafe
  refine ⟨?_, ?_, ?_, ?_, actualSafe, run_prefix_fits memory _ width fuel s fit actualSafe⟩
  all_goals rw [he]; unfold RunsTo at hx; simp only [hx, Run.reads, Run.steps]; assumption

namespace CompactSafetyConsumers

/-- The consumer spells out actual-state fit and every transition obligation. -/
theorem compact_safe_expectedType (width : Nat) (memory : Memory) (block : Block)
    (fresh depth : Nat) (s : State) (hpc : s.pc = 0)
    (bounded : BlockRegistersBelow fresh block)
    (fields : ∀ instruction ∈ compactAt block fresh depth 0, instruction.Fits width)
    (bound : compactSize block < 2 ^ width) (fit : s.Fits width)
    (safe : block.Safe memory width (Data.ofState s))
    (fuel : Nat) (enough : compactBound block ≤ fuel) :
    let actual := run memory (compactAt block fresh depth 0) fuel s
    actual.final.status = (block.eval memory (Data.ofState s)).final.status ∧
    (∀ r, r < compactCounter fresh depth →
      actual.final.regs r = (block.eval memory (Data.ofState s)).final.regs r) ∧
    actual.reads = (block.eval memory (Data.ofState s)).reads ∧
    actual.steps ≤ compactBound block ∧ actual.final.Fits width ∧
    (∀ t ∈ actual.transitions, Instruction.Safe width t.before t.instruction ∧ t.after.Fits width) ∧
    (∀ index, index ≤ fuel → (run memory (compactAt block fresh depth 0) index s).final.Fits width) := by
  have h := compact_compile_safe_run width memory block fresh depth s hpc bounded fields bound
    fit safe fuel enough
  exact ⟨h.1.1, h.1.2, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- Agreement on source registers alone cannot replace actual global entry fit. -/
theorem finite_agreement_does_not_give_fit :
    let low : Data := ⟨fun _ => 0, .running⟩
    let high : State := ⟨fun r => if r = 2 then 16 else 0, 0, .running⟩
    DataAgreesBelow 2 (Data.ofState high) low ∧ ¬ high.Fits 4 := by
  constructor
  · exact ⟨rfl, fun r hr => by simp [Data.ofState]; omega⟩
  · intro h
    have impossible := h.2.1 2
    exact (by decide : ¬ 16 < 2 ^ 4) impossible

end CompactSafetyConsumers

end RMQ.SuccinctFinal.PackedWordRAM.Optimization
