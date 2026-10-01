import RMQ.Core.WordRAM.Construction.Proof.RunFacts

/-! # Positional output reservation in a hosted builder

The source witness follows the output reservation through sequencing. Only its
suffix needs a register frame; no reduction of the complete compiled builder is
used. The resulting receipt names the actual producing state and trace position.
-/

namespace RMQ.SuccinctFinal.PackedLifecycle.Builder

open PackedConstruction PackedConstruction.Structured PackedConstruction.Proof
open PackedConstruction.Builder

/-- A reserve action followed only by code that preserves its destination. -/
inductive ReservePath (dst : Operand) : Block → Prop where
  | here : ReservePath dst (.action (.reserve dst))
  | left {a b} : ReservePath dst a → b.WritesOnly (fun r => r ≠ dst.val) →
      ReservePath dst (.seq a b)
  | right {a b} : ReservePath dst b → ReservePath dst (.seq a b)

theorem eval_add_writes {P : State → Action → Prop} {b : Block} {s t : State} {k : Nat}
    (e : EvalG P b s t k) (allowed : Nat → Prop) (hw : b.WritesOnly allowed) :
    EvalG (fun s op => P s op ∧ WritesOnly allowed ⟨op.prim⟩) b s t k := by
  induction e with
  | stopped b s h => exact .stopped b s h
  | skip s h => exact .skip s h
  | action op s h hp => exact .action op s h ⟨hp, hw⟩
  | exit src s h => exact .exit src s h
  | seq _ _ iha ihb => exact .seq (iha hw.1) (ihb hw.2)
  | ifZeroTaken h hc _ ih => exact .ifZeroTaken h hc (ih hw.1)
  | ifZeroFallthrough h hc _ hr ih => exact .ifZeroFallthrough h hc (ih hw.2) hr
  | ifZeroFallthroughStopped h hc _ hr ih => exact .ifZeroFallthroughStopped h hc (ih hw.2) hr
  | loopExit h hc => exact .loopExit h hc
  | loopStep h hc _ hr _ ihb ihr => exact .loopStep h hc (ihb hw) hr (ihr hw)
  | loopStopped h hc _ hr ih => exact .loopStopped h hc (ih hw) hr

theorem compile_running {W : Nat} {b : Block} {s t : State} {k : Nat}
    (e : SafeEval W b s t k) (hr : t.status = .running)
    (program : List BInstr) (base : Nat)
    (host : HostedAt program base (b.compileAt base)) (bound : base+b.size < 2^32) :
    ∃ ts, RunsTo program {s with pc := base} {t with pc := base+b.size} ts ∧
      ts.length = k ∧ ∀ u ∈ ts, TransitionShape (Action.Safe W) base b.size u := by
  obtain ⟨mid, ts, hrun, hlen, ha, hp, shapes⟩ := e.compile_realizes
    (fun _ q _ h => h.pc_set q) program base host bound
  have hm : mid.status = .running := ha.status.trans hr
  have he : mid = {t with pc := base+b.size} := by rw [ha.eq_set, hp hm]
  exact ⟨ts, he ▸ hrun, hlen, shapes⟩

theorem compile_running_frame {W : Nat} {b : Block} {s t : State} {k : Nat}
    (e : SafeEval W b s t k) (hr : t.status = .running)
    (program : List BInstr) (base : Nat)
    (host : HostedAt program base (b.compileAt base)) (bound : base+b.size < 2^32)
    (allowed : Nat → Prop) (hw : b.WritesOnly allowed) :
    ∃ ts, RunsTo program {s with pc := base} {t with pc := base+b.size} ts ∧
      ts.length = k ∧ ∀ u ∈ ts, WritesOnly allowed u.instruction := by
  have ew := eval_add_writes e allowed hw
  obtain ⟨mid, ts, hrun, hlen, ha, hp, shapes⟩ := ew.compile_realizes
    (fun _ q _ h => ⟨h.1.pc_set q, h.2⟩) program base host bound
  have hm : mid.status = .running := ha.status.trans hr
  have he : mid = {t with pc := base+b.size} := by rw [ha.eq_set, hp hm]
  refine ⟨ts, he ▸ hrun, hlen, ?_⟩
  intro u hu
  rcases shapes u hu with ⟨op, hi, _, hw⟩ | ⟨c, target, hi, _⟩ |
      ⟨target, hi, _⟩ | ⟨src, hi⟩
  · simpa [hi] using hw
  all_goals simp [hi, WritesOnly, Prim.destination?]

/-- Ordered segment factorization around the source reservation. -/
theorem reserve_factor {dst : Operand} {b : Block} (path : ReservePath dst b) :
    ∀ {W : Nat} {s t : State} {k : Nat}, SafeEval W b s t k → t.status = .running →
    ∀ (program : List BInstr) (base : Nat),
      HostedAt program base (b.compileAt base) → base+b.size < 2^32 →
      ∃ pre before after,
        RunsTo program {s with pc := base} pre before ∧
        pre.status = .running ∧ program[pre.pc]? = some ⟨.reserve dst⟩ ∧
        RunsTo program (execPrim (.reserve dst) pre) {t with pc := base+b.size} after ∧
        before.length+1+after.length = k ∧
        ∀ u ∈ after, WritesOnly (fun r => r ≠ dst.val) u.instruction := by
  induction path with
  | here =>
      intro W s t k e hr program base host bound
      cases e with
      | stopped _ _ hs => exact (hs hr).elim
      | action op s hs hp =>
          refine ⟨{s with pc := base}, [], [], RunsTo.refl _ _, hs, host.head, ?_, rfl, ?_⟩
          · have he : execPrim (.reserve dst) {s with pc := base} =
                {execPrim (.reserve dst) s with pc := base+1} := by
              simp [execPrim, State.writeNext, State.next]
            simpa only [Block.size, he] using
              RunsTo.refl program (execPrim (.reserve dst) {s with pc := base})
          · intro u hu; cases hu
  | @right a b path ih =>
      intro W s t k e hr program base host bound
      cases e with
      | stopped _ _ hs => exact (hs hr).elim
      | @seq _ _ _ mid _ ka kb ea eb =>
          have hm := eb.running_of_result hr
          have ha := host.append_left
          have hb : HostedAt program (base+a.size) (b.compileAt (base+a.size)) := by
            simpa only [Block.compile_length] using host.append_right
          obtain ⟨ta, ra, la, _⟩ := compile_running ea hm program base ha (by
            simp only [Block.size] at bound; omega)
          obtain ⟨pre, before, after, rb, hp, hf, rz, lk, frame⟩ :=
            ih eb hr program (base+a.size) hb (by simpa only [Block.size, Nat.add_assoc] using bound)
          refine ⟨pre, ta++before, after, ra.trans rb, hp, hf, ?_, ?_, frame⟩
          · simpa only [Block.size, Nat.add_assoc] using rz
          · simp only [List.length_append, la]; omega
  | @left a b path frameB ih =>
      intro W s t k e hr program base host bound
      cases e with
      | stopped _ _ hs => exact (hs hr).elim
      | @seq _ _ _ mid _ ka kb ea eb =>
          have hm := eb.running_of_result hr
          have ha := host.append_left
          have hb : HostedAt program (base+a.size) (b.compileAt (base+a.size)) := by
            simpa only [Block.compile_length] using host.append_right
          obtain ⟨pre, before, after, ra, hp, hf, rz, lk, frame⟩ :=
            ih ea hm program base ha (by simp only [Block.size] at bound; omega)
          obtain ⟨tb, rb, lb, frames⟩ := compile_running_frame eb hr program (base+a.size) hb
            (by simpa only [Block.size, Nat.add_assoc] using bound) _ frameB
          refine ⟨pre, before, after++tb, ra, hp, hf, ?_, ?_, ?_⟩
          · simpa only [Block.size, Nat.add_assoc] using rz.trans rb
          · simp only [List.length_append, lb]; omega
          · intro u hu
            rcases List.mem_append.mp hu with hu | hu
            · exact frame u hu
            · exact frames u hu

theorem run_frame_on_trace (program : List BInstr) (fuel : Nat) (s : State)
    (allowed : Nat → Prop)
    (hw : ∀ u ∈ (run program fuel s).transitions, WritesOnly allowed u.instruction)
    (r : Nat) (hout : ¬ allowed r) :
    (run program fuel s).final.regs r = s.regs r := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
      cases hs : stepProgram program s with
      | none => simp [run, hs]
      | some u =>
          have first : WritesOnly allowed u.instruction := hw u (by simp [run, hs])
          have rest : ∀ v ∈ (run program fuel u.after).transitions, WritesOnly allowed v.instruction :=
            fun v hv => hw v (by simp [run, hs, hv])
          have he := (step_spec hs).2.2.2
          have hf : u.after.regs r = s.regs r := by
            rw [he]; exact execPrim_frame _ _ allowed first r hout
          simpa only [run, hs] using (ih u.after rest).trans hf

theorem run_prefix_mem {program : List BInstr} {s : State} {short full : Nat}
    (h : short ≤ full) {u : Transition}
    (hu : u ∈ (run program short s).transitions) :
    u ∈ (run program full s).transitions := by
  rw [← Nat.add_sub_of_le h, run_add]
  exact List.mem_append_left _ hu

theorem run_prefix_frame {program : List BInstr} {s : State} {short full : Nat}
    (h : short ≤ full) (allowed : Nat → Prop)
    (hw : ∀ u ∈ (run program full s).transitions, WritesOnly allowed u.instruction)
    (r : Nat) (hout : ¬ allowed r) :
    (run program short s).final.regs r = s.regs r :=
  run_frame_on_trace program short s allowed
    (fun u hu => hw u (run_prefix_mem h hu)) r hout

theorem emits_preserve_output : ∀ rs, (emitRegs rs).WritesOnly (fun r => r ≠ 3) := by
  intro rs
  induction rs with
  | nil => trivial
  | cons r rs ih =>
      exact ⟨by simp [emitBit, Block.WritesOnly, Action.prim, Prim.destination?], ih⟩

theorem repack_preserves_output : repackBlock.WritesOnly (fun r => r ≠ 3) := by
  simp [acts, emitBit, forSlots, hornerStepBlock, repackBlock, repackWordBlock,
    Block.WritesOnly, Action.prim, Prim.destination?]

/-- Structural route to the existing metadata reservation, for either leaf. -/
theorem builder_reserve_path (leaf : Block) : ReservePath 3 (builderSource leaf) := by
  unfold builderSource builderBody outputBlock metaEmitBlock
  apply ReservePath.right
  apply ReservePath.right
  apply ReservePath.right
  apply ReservePath.right
  apply ReservePath.right
  apply ReservePath.right
  apply ReservePath.left
  · apply ReservePath.left
    · change ReservePath 3 (.seq (.action (.reserve 3)) _)
      exact ReservePath.left .here (by simp [acts, Block.WritesOnly, Action.prim, Prim.destination?])
    · exact emits_preserve_output _
  · exact repack_preserves_output

/-- Positional producing reservation and the complete following register frame. -/
def ReservationReceipt (program : List BInstr) (s t : State) (ts : List Transition)
    (dst : Operand) : Prop :=
  ∃ (pre : State) (before after : List Transition),
    RunsTo program s pre before ∧ pre.status = .running ∧
    program[pre.pc]? = some ⟨.reserve dst⟩ ∧
    RunsTo program (execPrim (.reserve dst) pre) t after ∧
    ts = before ++ [⟨pre, ⟨.reserve dst⟩, execPrim (.reserve dst) pre⟩] ++ after ∧
    (∀ u ∈ after, WritesOnly (fun r => r ≠ dst.val) u.instruction) ∧
    t.regs dst = pre.extent

theorem reservation_receipt {W : Nat} {b : Block} {s t : State} {k base : Nat}
    {program : List BInstr} (e : SafeEval W b s t k) (hr : t.status = .running)
    (entry : s.pc = base) (host : HostedAt program base (b.compileAt base))
    (bound : base+b.size < 2^32) {dst : Operand} (path : ReservePath dst b) :
    ∃ ts, RunsTo program s {t with pc := base+b.size} ts ∧ ts.length = k ∧
      ReservationReceipt program s {t with pc := base+b.size} ts dst := by
  obtain ⟨pre, before, after, rp, hp, hf, rz, lk, frame⟩ :=
    reserve_factor path e hr program base host bound
  have se : ({s with pc := base} : State) = s := by rw [← entry]
  rw [se] at rp
  let tr : Transition := ⟨pre, ⟨.reserve dst⟩, execPrim (.reserve dst) pre⟩
  have whole := (rp.trans (RunsTo.instruction hp hf)).trans rz
  have val : ({t with pc := base+b.size} : State).regs dst = pre.extent := by
    have f := run_frame_on_trace program after.length (execPrim (.reserve dst) pre)
      (fun r => r ≠ dst.val) (by rw [show run program after.length _ = _ from rz]; exact frame)
      dst (by simp)
    rw [show run program after.length _ = _ from rz] at f
    simpa [execPrim, State.writeNext, State.next, put] using f
  refine ⟨before ++ [tr] ++ after, whole, ?_,
    ⟨pre, before, after, rp, hp, hf, rz, rfl, frame, val⟩⟩
  simp only [List.length_append, List.length_singleton]
  omega

/-- A receipt is an indexed actual transition, with a frame through every
remaining prefix of its suffix, not merely membership of a reservation value. -/
theorem ReservationReceipt.occurrence {program : List BInstr} {s t : State}
    {ts : List Transition} {dst : Operand} (h : ReservationReceipt program s t ts dst) :
    ∃ (index : Nat) (pre : State) (after : List Transition),
      ts[index]? = some ⟨pre, ⟨.reserve dst⟩, execPrim (.reserve dst) pre⟩ ∧
      (run program index s).final = pre ∧ pre.status = .running ∧
      program[pre.pc]? = some ⟨.reserve dst⟩ ∧
      (execPrim (.reserve dst) pre).regs dst = pre.extent ∧
      RunsTo program (execPrim (.reserve dst) pre) t after ∧
      (∀ fuel, fuel ≤ after.length →
        (run program fuel (execPrim (.reserve dst) pre)).final.regs dst = pre.extent) ∧
      t.regs dst = pre.extent := by
  obtain ⟨pre, before, after, rp, hr, hf, rs, trace, frame, value⟩ := h
  refine ⟨before.length, pre, after, ?_, congrArg Run.final rp, hr, hf, ?_, rs, ?_, value⟩
  · rw [trace, List.append_assoc, List.getElem?_append_right (Nat.le_refl _)]
    simp
  · simp [execPrim, State.writeNext, State.next, put]
  · intro fuel hle
    have hframe : ∀ u ∈ (run program after.length (execPrim (.reserve dst) pre)).transitions,
        WritesOnly (fun r => r ≠ dst.val) u.instruction := by
      rw [show run program after.length _ = _ from rs]
      exact frame
    have out := run_prefix_frame hle (fun r => r ≠ dst.val) hframe dst (by simp)
    simpa [execPrim, State.writeNext, State.next, put] using out

end RMQ.SuccinctFinal.PackedLifecycle.Builder
