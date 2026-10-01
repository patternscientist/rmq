import RMQ.Core.WordRAM.Lifecycle.BuilderProvenance
import RMQ.Core.WordRAM.Construction.Proof.Static
import RMQ.Core.WordRAM.Packed.Setup
import RMQ.Core.WordRAM.Packed.Width

/-! # Live hosted construction for the continuous lifecycle

This adapter consumes the existing builder source at its actual program offset.
It exports the still-running state, its exact canonical output interval, and the
reservation occurrence that produced register 3. Input materialization and the
later charged descriptor transfer remain separate operations.
-/

namespace RMQ.SuccinctFinal.PackedLifecycle.Builder

open PackedConstruction PackedConstruction.Structured PackedConstruction.Proof
open PackedConstruction.Builder
open PackedWordRAM (buildMemory wordWidth)

theorem metadata_zero (xs : List Int) : (buildMemory xs)[0]? = some xs.length := by
  rw [PackedWordRAM.buildMemory_metadata_prefix xs 0 (by decide)]
  simp [PackedWordRAM.metadata, PackedWordRAM.scalarMetadata,
    PackedCellProbe.packedReviewerCartesianShape_size]

theorem metadata_seven (xs : List Int) :
    (buildMemory xs)[7]? = some (buildMemory xs).length := by
  rw [PackedWordRAM.buildMemory_metadata_prefix xs 7 (by decide)]
  rw [buildMemory, PackedWordRAM.shapeMemory_length_eq]
  simp [PackedWordRAM.metadata, PackedWordRAM.scalarMetadata]

theorem metadata_length (xs : List Int) : 8 ≤ (buildMemory xs).length := by
  have h := PackedWordRAM.shapeMemory_metadata_length_le (SuccinctClassic.cartesianShape xs)
  change 174 ≤ (buildMemory xs).length at h
  omega

theorem regsBelow_writesOnly (b : Block) (R : Nat) (h : b.RegsBelow R) :
    b.WritesOnly (fun r => r < R) := by
  induction b with
  | skip => trivial
  | action op => exact Prim.dest_lt_of_registersBelow h
  | exit src => trivial
  | seq a b iha ihb => exact ⟨iha h.1, ihb h.2⟩
  | ifZero c a b iha ihb => exact ⟨iha h.2.1, ihb h.2.2⟩
  | loop c b ih => exact ih h.2

theorem prim_keyRegs_frame (p : Prim) (s : State) {R : Nat}
    (h : p.RegistersBelow R) (r : Nat) (hr : R ≤ r) :
    (execPrim p s).keyRegs r = s.keyRegs r := by
  cases p <;> simp only [execPrim, State.writeNext, State.next]
  case loadKey dst address =>
    have hne : r ≠ dst.val := by simp only [Prim.RegistersBelow] at h; omega
    split <;> simp [put, hne]
  case load dst address =>
    split
    · split <;> rfl
    · rfl
  case store address value => split <;> rfl
  all_goals rfl

theorem eval_keyRegs_frame {P : State → Action → Prop} {b : Block} {s t : State} {k R : Nat}
    (e : EvalG P b s t k) (h : b.RegsBelow R) (r : Nat) (hr : R ≤ r) :
    t.keyRegs r = s.keyRegs r := by
  induction e with
  | stopped => rfl
  | skip => rfl
  | action op s _ _ => exact prim_keyRegs_frame op.prim s h r hr
  | exit => rfl
  | seq _ _ iha ihb => exact (ihb h.2).trans (iha h.1)
  | ifZeroTaken _ _ _ ih => exact ih h.2.1
  | ifZeroFallthrough _ _ _ _ ih => exact ih h.2.2
  | ifZeroFallthroughStopped _ _ _ _ ih => exact ih h.2.2
  | loopExit => rfl
  | loopStep _ _ _ _ _ ihb ihr => exact (ihr h).trans (ihb h.2)
  | loopStopped _ _ _ _ ih => exact ih h.2

/-- A structural source inventory: one past its largest key-register write.
Control nodes combine inventories; this does not execute the source. -/
def keyRegisterLimit : Block → Nat
  | .action (.loadKey dst _) => dst.val+1
  | .seq a b | .ifZero _ a b => max (keyRegisterLimit a) (keyRegisterLimit b)
  | .loop _ b => keyRegisterLimit b
  | _ => 0

theorem action_keyRegister_frame (op : Action) (s : State) (r : Nat)
    (outside : keyRegisterLimit (.action op) ≤ r) :
    (execPrim op.prim s).keyRegs r = s.keyRegs r := by
  cases op <;> simp only [Action.prim, execPrim, State.writeNext, State.next]
  case loadKey dst address =>
    have hne : r ≠ dst.val := by simp only [keyRegisterLimit] at outside; omega
    split <;> simp [put, hne]
  case load dst address =>
    split
    · split <;> rfl
    · rfl
  case store address value => split <;> rfl
  all_goals rfl

theorem eval_keyRegister_frame {P : State → Action → Prop} {b : Block} {s t : State} {k : Nat}
    (e : EvalG P b s t k) (r : Nat) (outside : keyRegisterLimit b ≤ r) :
    t.keyRegs r = s.keyRegs r := by
  induction e with
  | stopped => rfl
  | skip => rfl
  | action op s _ _ => exact action_keyRegister_frame op s r outside
  | exit => rfl
  | seq _ _ iha ihb =>
      exact (ihb (Nat.le_trans (Nat.le_max_right ..) outside)).trans
        (iha (Nat.le_trans (Nat.le_max_left ..) outside))
  | ifZeroTaken _ _ _ ih => exact ih (Nat.le_trans (Nat.le_max_left ..) outside)
  | ifZeroFallthrough _ _ _ _ ih => exact ih (Nat.le_trans (Nat.le_max_right ..) outside)
  | ifZeroFallthroughStopped _ _ _ _ ih => exact ih (Nat.le_trans (Nat.le_max_right ..) outside)
  | loopExit => rfl
  | loopStep _ _ _ _ _ ihb ihr => exact (ihr outside).trans (ihb outside)
  | loopStopped _ _ _ _ ih => exact ih outside

set_option maxRecDepth 100000 in
theorem word_keyRegister_limit : keyRegisterLimit (builderSource wordLeaf) = 0 := rfl

set_option maxRecDepth 100000 in
theorem comparison_keyRegister_limit : keyRegisterLimit (builderSource keyLeaf) = 2 := rfl

/-- The live producer's state and trace facts, all about one hosted execution. -/
structure HostedBody (W : Nat) (program : List BInstr) (base : Nat) (leaf : Block)
    (xs : List Int) (s abstract final : State) (ts : List Transition) : Prop where
  evaluation : SafeEval W (builderSource leaf) s abstract ts.length
  intermediate : final = {abstract with pc := base+(builderSource leaf).size}
  execution : RunsTo program s final ts
  shapes : ∀ u ∈ ts, TransitionShape (Action.Safe W) base (builderSource leaf).size u
  safe : Run.Safe W program ⟨final, ts⟩
  fits : final.Fits W
  running : final.status = .running
  pc : final.pc = base+(builderSource leaf).size
  work : ts.length ≤ 3+(25*W+40+39*(5*W+20))+2100*(400000*(xs.length+1))
  baseLower : s.extent ≤ final.regs 3
  baseUpper : final.regs 3 ≤ s.extent+3200000*(xs.length+1)
  extent : final.extent = final.regs 3+(buildMemory xs).length
  cells : ∀ i, i < (buildMemory xs).length →
    final.memory (final.regs 3+i) = some ((buildMemory xs).getD i 0)
  inputFrame : ∀ a, a < s.extent → final.memory a = s.memory a
  keys : final.keys = s.keys
  cleanTail : CleanTail final
  numericFrame : ∀ r, 400 ≤ r → final.regs r = s.regs r
  keyFrame : ∀ r, 400 ≤ r → final.keyRegs r = s.keyRegs r
  reservation : ReservationReceipt program s final ts 3

/-- The caller provides the actual live entry PC and supplied input predicate;
the body computes its output rather than receiving an output equality. -/
theorem hosted_body {W : Nat} (hW : 32 ≤ W) (xs : List Int) (Inp : State → Prop)
    (leaf : Block) (hleaf : KeySpec W xs Inp leaf)
    (hbank : (builderBody leaf).RegsBelow 400)
    (program : List BInstr) (base : Nat) (s : State)
    (entry : s.pc = base) (hrun : s.status = .running) (hregs : ∀ r, s.regs r = 0)
    (hext : 0 < s.extent) (hmem : s.memory 0 = some xs.length)
    (hinp : Inp s) (hInp : InpBelow Inp s.extent)
    (hbankcap : 2^32*(2*xs.length+4)^8 < 2^W)
    (hcap : s.extent+64*(400000*(xs.length+1)) < 2^W)
    (hWW : wordWidth xs.length ≤ W)
    (host : HostedAt program base ((builderSource leaf).compileAt base))
    (bound : base+(builderSource leaf).size < 2^32)
    (inside : base+(builderSource leaf).size < program.length)
    (programFits : program.length < 2^W) (initialFits : s.Fits W) (tail : CleanTail s) :
    ∃ abstract final ts, HostedBody W program base leaf xs s abstract final ts := by
  obtain ⟨t, k, e, hk, hr, hlo, hhi, he, hm, hb, hkeys⟩ :=
    builderSource_spec hW xs Inp leaf hleaf s hrun hregs hext hmem hinp hInp hbankcap hcap hWW
  obtain ⟨ts, hrunBody, len, receipt⟩ :=
    reservation_receipt e hr entry host bound (builder_reserve_path leaf)
  obtain ⟨us, urun, ulen, shape⟩ := compile_running e hr program base host bound
  have se : ({s with pc := base} : State) = s := by rw [← entry]
  rw [se] at urun
  have traces : us = ts := by
    have a := urun
    have b := hrunBody
    unfold RunsTo at a b
    rw [ulen] at a
    rw [len] at b
    exact congrArg Run.transitions (a.symm.trans b)
  subst us
  let final : State := {t with pc := base+(builderSource leaf).size}
  have operational : run program ts.length s = ⟨final, ts⟩ := hrunBody
  have safety := Run.Safe.of_transitions program W programFits ts.length s initialFits (by
    rw [operational]
    exact fun u hu => (shape u hu).safe hW inside)
  have fit := safety.final_fits initialFits
  rw [operational] at safety fit
  have rb : (builderSource leaf).RegsBelow 400 := ⟨by
    simp [Block.RegsBelow, Action.prim, Prim.RegistersBelow], hbank⟩
  refine ⟨t, final, ts, ⟨?_, rfl, hrunBody, shape, safety, fit, hr, rfl, ?_, hlo, ?_, he, hm,
    hb, hkeys, ?_, ?_, ?_, receipt⟩⟩
  · simpa only [len] using e
  · omega
  · change t.regs 3 ≤ s.extent+3200000*(xs.length+1)
    omega
  · have h := run_cleanTail program ts.length s tail
    rw [operational] at h
    exact h
  · intro r hr
    exact PackedConstruction.Proof.EvalG.regs_frame e
      (fun x => x < 400) (regsBelow_writesOnly _ _ rb) r (by omega)
  · exact fun r hr => eval_keyRegs_frame e rb r hr

theorem hosted_linear_work {program : List BInstr} {base : Nat} {leaf : Block} {xs : List Int}
    {s abstract final : State} {ts : List Transition}
    (h : HostedBody (wordWidth xs.length) program base leaf xs s abstract final ts) :
    ts.length ≤ 1000000000*xs.length+1000000000 := by
  have hw := h.work
  have hb := budget_ge xs.length
  rw [builderBudget_eq_mul_add] at hb
  omega

/-- The hosted builder's historical numeric extent is bounded before its
continuation starts; no property of code after that point is assumed. -/
theorem hosted_peak {W base : Nat} {program : List BInstr} {leaf : Block} {xs : List Int}
    {s abstract final : State} {ts : List Transition}
    (h : HostedBody W program base leaf xs s abstract final ts)
    (fuel : Nat) (hle : fuel ≤ ts.length) :
    (run program fuel s).final.extent ≤ final.extent ∧
    (run program fuel s).final.extent ≤
      s.extent+3200000*(xs.length+1)+(buildMemory xs).length := by
  have hm := run_extent_mono program (ts.length-fuel) (run program fuel s).final
  have whole := h.execution
  unfold RunsTo at whole
  rw [← Nat.add_sub_of_le hle, run_add] at whole
  have hf := congrArg (fun r : Run => r.final.extent) whole
  dsimp only at hf
  rw [hf] at hm
  exact ⟨hm, by have := h.baseUpper; rw [h.extent] at hm; omega⟩

/-- Numeric finite support throughout the hosted body, including its endpoint. -/
theorem hosted_numeric_prefix_frame {W base : Nat} {program : List BInstr} {leaf : Block}
    {xs : List Int} {s abstract final : State} {ts : List Transition}
    (h : HostedBody W program base leaf xs s abstract final ts)
    (entry : s.pc = base)
    (host : HostedAt program base ((builderSource leaf).compileAt base))
    (bound : base+(builderSource leaf).size < 2^32)
    (bank : (builderBody leaf).RegsBelow 400)
    (fuel : Nat) (hle : fuel ≤ ts.length) (r : Nat) (outside : 400 ≤ r) :
    (run program fuel s).final.regs r = s.regs r := by
  have rb : (builderSource leaf).RegsBelow 400 := ⟨by
    simp [Block.RegsBelow, Action.prim, Prim.RegistersBelow], bank⟩
  have abstractRunning : abstract.status = .running := by
    have hr := h.running
    rw [h.intermediate] at hr
    exact hr
  obtain ⟨us, urun, ulen, frame⟩ := compile_running_frame h.evaluation abstractRunning
    program base host bound (fun r => r < 400) (regsBelow_writesOnly _ _ rb)
  have se : ({s with pc := base} : State) = s := by rw [← entry]
  rw [se, ← h.intermediate] at urun
  have traces : us = ts := by
    have a := urun
    unfold RunsTo at a
    rw [ulen] at a
    exact congrArg Run.transitions (a.symm.trans h.execution)
  subst us
  exact run_prefix_frame hle (fun r => r < 400) (by
    rw [show run program ts.length s = ⟨final, ts⟩ from h.execution]
    exact frame) r (by omega)

theorem hosted_word_key_frame {W base : Nat} {program : List BInstr} {xs : List Int}
    {s abstract final : State} {ts : List Transition}
    (h : HostedBody W program base wordLeaf xs s abstract final ts) :
    final.keyRegs = s.keyRegs := by
  funext r
  rw [h.intermediate]
  exact eval_keyRegister_frame h.evaluation r (by rw [word_keyRegister_limit]; omega)

theorem hosted_comparison_key_frame {W base : Nat} {program : List BInstr} {xs : List Int}
    {s abstract final : State} {ts : List Transition}
    (h : HostedBody W program base keyLeaf xs s abstract final ts) (r : Nat) (outside : 2 ≤ r) :
    final.keyRegs r = s.keyRegs r := by
  rw [h.intermediate]
  exact eval_keyRegister_frame h.evaluation r (by rw [comparison_keyRegister_limit]; exact outside)

/-- Both useful header words are present in the exact produced interval. -/
theorem produced_metadata {W base : Nat} {program : List BInstr} {leaf : Block} {xs : List Int}
    {s abstract final : State} {ts : List Transition}
    (h : HostedBody W program base leaf xs s abstract final ts) :
    final.memory (final.regs 3) = some xs.length ∧
    final.memory (final.regs 3+7) = some (buildMemory xs).length ∧
    final.regs 3+7 < final.extent := by
  have hl := metadata_length xs
  have h0 := h.cells 0 (by omega)
  have h7 := h.cells 7 (by omega)
  simp only [List.getD, metadata_zero, Option.getD_some, Nat.add_zero] at h0
  simp only [List.getD, metadata_seven, Option.getD_some] at h7
  exact ⟨h0, h7, by rw [h.extent]; omega⟩

end RMQ.SuccinctFinal.PackedLifecycle.Builder
