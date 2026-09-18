import RMQ.Core.WordRAM.Bitvector.NumericReader
import RMQ.Core.WordRAM.Packed.ReaderSafety

/-! # Scalar safety of the generic numeric bitvector reader

The bounds concern actual supplied descriptor replies. Missing replies still
fault and stop. Canonical allocation and controller proofs supply these bounds
separately; no Cartesian-shape premise or successful-read oracle is used.
-/

namespace RMQ.PackedBitvector

open SuccinctFinal.PackedWordRAM SuccinctFinal.PackedWordRAM.Structured

def NumericReaderGeometry (memory : Memory) (width : Nat) (regs : Registers) : Prop :=
  (regs 8192 < 23 → numericDescriptorAddress regs + 3 < 2 ^ width) ∧
  (regs 8192 < 23 → ∀ (bitBase bitLength stride count : Nat),
    memory[numericDescriptorAddress regs]? = some bitBase →
    memory[numericDescriptorAddress regs + 1]? = some bitLength →
    memory[numericDescriptorAddress regs + 2]? = some stride →
    memory[numericDescriptorAddress regs + 3]? = some count →
    regs 8193 < count →
    bitBase + regs 8193 * stride < 2 ^ width ∧ stride < width)

private theorem eval_action (memory : Memory) (op : Action) (regs : Registers) :
    (Block.action op).eval memory ⟨regs, .running⟩ = op.eval memory ⟨regs, .running⟩ := rfl

private theorem eval_skip (memory : Memory) (s : Data) :
    Block.skip.eval memory s = ⟨s, []⟩ := by
  cases s with
  | mk regs status => cases status <;> rfl

private theorem eval_ifZero (memory : Memory) (r : Nat) (a b : Block) (regs : Registers) :
    (Block.ifZero r a b).eval memory ⟨regs, .running⟩ =
      if regs r = 0 then a.eval memory ⟨regs, .running⟩
      else b.eval memory ⟨regs, .running⟩ := rfl

private theorem checks_seq (memory : Memory) (width : Nat) (a b : Block) (s : Data) :
    ScalarChecks memory width (.seq a b) s ↔
      (s.status = .running → ScalarChecks memory width a s ∧
        ScalarChecks memory width b (a.eval memory s).final) := Iff.rfl

private theorem checks_action (memory : Memory) (width : Nat) (op : Action) (regs : Registers) :
    ScalarChecks memory width (.action op) ⟨regs, .running⟩ ↔
      op.LocalSafe memory width ⟨regs, .running⟩ := by
  simp [ScalarChecks]

private theorem checks_ifZero (memory : Memory) (width r : Nat) (a b : Block) (regs : Registers) :
    ScalarChecks memory width (.ifZero r a b) ⟨regs, .running⟩ ↔
      (if regs r = 0 then ScalarChecks memory width a ⟨regs, .running⟩
        else ScalarChecks memory width b ⟨regs, .running⟩) := by
  simp [ScalarChecks]

private theorem checks_skip (memory : Memory) (width : Nat) (s : Data) :
    ScalarChecks memory width Block.skip s := fun _ => True.intro

private theorem checks_of_safe (memory : Memory) (width : Nat) (block : Block)
    (s : Data) (safe : block.Safe memory width s) : ScalarChecks memory width block s := by
  induction block generalizing s with
  | skip => exact checks_skip memory width s
  | action op => exact safe.2
  | exit src => exact safe.2
  | seq a b iha ihb =>
      intro hs
      exact ⟨iha s (safe.2 hs).1, ihb _ (safe.2 hs).2⟩
  | ifZero r a b iha ihb =>
      intro hs
      have h := safe.2 hs
      by_cases hz : s.regs r = 0
      · simpa [hz] using iha s (by simpa [hz] using h)
      · simpa [hz] using ihb s (by simpa [hz] using h)
  | «repeat» count body ih =>
      intro hs
      have h := safe.2 hs
      clear safe hs
      induction count generalizing s with
      | zero => trivial
      | succ count iht => exact ⟨ih s h.1, iht _ h.2⟩

private theorem registers_write_fit (width : Nat) (regs : Registers) (dst value : Nat)
    (fit : ∀ r, regs r < 2 ^ width) (valueFit : value < 2 ^ width) :
    ∀ r, regs.write dst value r < 2 ^ width := by
  intro r
  simp only [Registers.write]
  split
  · exact valueFit
  · exact fit r

private def descriptorPrepared (regs : Registers)
    (bitBase bitLength stride count : Nat) : Registers :=
  let r := (regs.write 8208 4).write 8209 (regs 8192 * 4)
  let r := (r.write 8210 92).write 8211 (regs 3 * 92)
  let r := (r.write 8209 (regs 8192 * 4 + regs 3 * 92)).write 8210 23
  let r := (r.write 8209 (numericDescriptorAddress regs)).write 8210 1
  let r := (r.write 8201 bitBase).write 8209 (numericDescriptorAddress regs + 1)
  let r := (r.write 8202 bitLength).write 8209 (numericDescriptorAddress regs + 2)
  let r := (r.write 8203 stride).write 8209 (numericDescriptorAddress regs + 3)
  (r.write 8204 count).write 8200 (regs 8193)

private theorem descriptorPrepared_fit (memory : Memory) (width : Nat) (regs : Registers)
    (bitBase bitLength stride count : Nat) (hw : 8 ≤ width)
    (memoryFit : MemoryWordsFit memory width)
    (fit : (⟨regs, .running⟩ : Data).Fits width)
    (address : numericDescriptorAddress regs + 3 < 2 ^ width)
    (hbase : memory[numericDescriptorAddress regs]? = some bitBase)
    (hlen : memory[numericDescriptorAddress regs + 1]? = some bitLength)
    (hstride : memory[numericDescriptorAddress regs + 2]? = some stride)
    (hcount : memory[numericDescriptorAddress regs + 3]? = some count) :
    (⟨descriptorPrepared regs bitBase bitLength stride count, .running⟩ : Data).Fits width := by
  have hb := memoryFit.reply hbase
  have hl := memoryFit.reply hlen
  have hs := memoryFit.reply hstride
  have hc := memoryFit.reply hcount
  have cap : 256 ≤ 2 ^ width := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hw
  have hi := fit.1 8193
  dsimp only at hi
  have ha := address
  unfold numericDescriptorAddress at ha
  constructor
  · dsimp only [descriptorPrepared]
    repeat' apply registers_write_fit
    all_goals first | exact fit.1 | omega
  · intro value stopped
    cases stopped

/-- Source safety for four descriptor attempts and the shared locator. The
geometric obligation is conditional on all four attempts actually succeeding. -/
theorem descriptorLoads_safe (memory : Memory) (width : Nat) (regs : Registers)
    (hw : 8 ≤ width) (memoryFit : MemoryWordsFit memory width)
    (fit : (⟨regs, .running⟩ : Data).Fits width)
    (address : numericDescriptorAddress regs + 3 < 2 ^ width)
    (position : ∀ (bitBase bitLength stride count : Nat),
      memory[numericDescriptorAddress regs]? = some bitBase →
      memory[numericDescriptorAddress regs + 1]? = some bitLength →
      memory[numericDescriptorAddress regs + 2]? = some stride →
      memory[numericDescriptorAddress regs + 3]? = some count →
      regs 8193 < count → bitBase + regs 8193 * stride < 2 ^ width) :
    Experiment.descriptorLoads.Safe memory width ⟨regs, .running⟩ := by
  apply ScalarChecks_safe memory width _ _ fit
  have cap : 256 ≤ 2 ^ width := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hw
  have hwne : width ≠ 0 := by omega
  have hi := fit.1 8193
  dsimp only at hi
  have hadd2 (a : Nat) : 1 + (1 + a) = 2 + a := by omega
  have hadd3 (a : Nat) : 1 + (2 + a) = 3 + a := by omega
  cases hbase : memory[numericDescriptorAddress regs]? with
  | none =>
      simp only [numericDescriptorAddress, Nat.add_assoc] at hbase address
      simp [Experiment.descriptorLoads, Block.sequence, checks_seq, checks_action,
        eval_action, Action.eval, Action.instruction,
        Action.LocalSafe, execute, State.writeNext, Data.ofState, Registers.write,
        Arithmetic.eval, ScalarChecks_stopped, hbase,
        Nat.add_comm, hwne] <;> omega
  | some bitBase =>
    have hb := memoryFit.reply hbase
    cases hlen : memory[numericDescriptorAddress regs + 1]? with
    | none =>
      simp only [numericDescriptorAddress, Nat.add_assoc, Nat.add_comm] at hbase hlen address
      simp [Experiment.descriptorLoads, Block.sequence, checks_seq, checks_action,
        eval_action, Action.eval, Action.instruction,
        Action.LocalSafe, execute, State.writeNext, Data.ofState, Registers.write,
        Arithmetic.eval, ScalarChecks_stopped, hbase, hlen,
        Nat.add_comm, hwne] <;> omega
    | some bitLength =>
      have hl := memoryFit.reply hlen
      cases hstride : memory[numericDescriptorAddress regs + 2]? with
      | none =>
        simp only [numericDescriptorAddress, Nat.add_assoc, Nat.add_comm] at hbase hlen hstride address
        simp [Experiment.descriptorLoads, Block.sequence, checks_seq, checks_action,
          eval_action, Action.eval, Action.instruction,
          Action.LocalSafe, execute, State.writeNext, Data.ofState, Registers.write,
          Arithmetic.eval, ScalarChecks_stopped, hbase, hlen, hstride,
          Nat.add_comm, hadd2, hwne] <;> omega
      | some stride =>
        have hs := memoryFit.reply hstride
        cases hcount : memory[numericDescriptorAddress regs + 3]? with
        | none =>
          simp only [numericDescriptorAddress, Nat.add_assoc, Nat.add_comm] at hbase hlen hstride hcount address
          simp [Experiment.descriptorLoads, Block.sequence, checks_seq, checks_action,
            eval_action, Action.eval, Action.instruction,
            Action.LocalSafe, execute, State.writeNext, Data.ofState, Registers.write,
            Arithmetic.eval, ScalarChecks_stopped, hbase, hlen, hstride, hcount,
            Nat.add_comm, hadd2, hadd3, hwne] <;> omega
        | some count =>
          have hc := memoryFit.reply hcount
          have hp := position bitBase bitLength stride count hbase hlen hstride hcount
          have fp := descriptorPrepared_fit memory width regs bitBase bitLength stride count
            hw memoryFit fit address hbase hlen hstride hcount
          have locate := regularLocateBlock_safe 8200 width memory
            ⟨descriptorPrepared regs bitBase bitLength stride count, .running⟩ fp (by omega)
            (by simp [descriptorPrepared, Registers.write]; intro h; have := hp h; omega)
            (by simpa [descriptorPrepared, Registers.write] using hp)
          have checks := checks_of_safe memory width _ _ locate
          simp only [descriptorPrepared] at checks
          simp only [numericDescriptorAddress, Nat.add_assoc, Nat.add_comm] at hbase hlen hstride hcount address checks
          simp [Experiment.descriptorLoads, Block.sequence, checks_seq, checks_action, checks_skip,
            eval_action, Action.eval, Action.instruction,
            Action.LocalSafe, execute, State.writeNext, Data.ofState, Registers.write,
            Arithmetic.eval, hbase, hlen, hstride, hcount, checks,
            Nat.add_comm, hadd2, hadd3, hwne] <;> omega

/-- The packet increment executes before the optional complement, so its
bound is proved independently of which target branch is taken. -/
theorem finishPacket_safe (memory : Memory) (width : Nat) (regs : Registers)
    (hw : 8 ≤ width) (fit : (⟨regs, .running⟩ : Data).Fits width)
    (length : regs 8207 < width) (value : regs 8259 < 2 ^ regs 8207) :
    Experiment.finishPacket.Safe memory width ⟨regs, .running⟩ := by
  apply ScalarChecks_safe memory width _ _ fit
  have cap : 256 ≤ 2 ^ width := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hw
  have mask := Nat.pow_lt_pow_right (by decide : 1 < 2) length
  have fl := fit.1 8207
  dsimp only at fl
  have hshift : Nat.shiftLeft 1 (regs 8207) = 2 ^ regs 8207 := by
    simpa using Nat.shiftLeft_eq 1 (regs 8207)
  have hwne : width ≠ 0 := by omega
  by_cases segment : regs 8192 = 0 <;> by_cases target : regs 3 = 0
  all_goals simp [ScalarChecks, Experiment.finishPacket, Block.sequence, Block.eval,
    Action.eval, Action.instruction, Action.LocalSafe, execute, State.writeNext,
    Data.ofState, Registers.write, Arithmetic.eval, segment, target, hshift, hwne] <;> omega

private theorem running_write_fit (width : Nat) (regs : Registers) (dst value : Nat)
    (fit : (⟨regs, .running⟩ : Data).Fits width) (valueFit : value < 2 ^ width) :
    (⟨regs.write dst value, .running⟩ : Data).Fits width :=
  ⟨registers_write_fit width regs dst value fit.1 valueFit, fun _ h => Status.noConfusion h⟩

private theorem safe_move_seq (memory : Memory) (width dst src : Nat)
    (rest : Block) (regs : Registers) (fit : (⟨regs, .running⟩ : Data).Fits width)
    (tail : rest.Safe memory width ⟨regs.write dst (regs src), .running⟩) :
    (Block.seq (.action (.move dst src)) rest).Safe memory width ⟨regs, .running⟩ := by
  refine Block.safe_seq (Block.safe_action memory width _ _ fit (fit.1 src)) ?_
  simpa only [Block.eval, Action.eval, Action.instruction, execute, State.writeNext,
    Data.ofState] using tail

private theorem readerSpan_safe (memory : Memory) (width : Nat) (regs : Registers)
    (hw : 8 ≤ width) (memoryFit : MemoryWordsFit memory width)
    (fit : (⟨regs, .running⟩ : Data).Fits width)
    (hwidth : regs 22 = width) (position : regs 8206 < 2 ^ width)
    (length : regs 8207 < width) :
    (Block.sequence [
      .action (.move 8256 22), .action (.move 8257 8206),
      .action (.move 8258 8207), spanBlock 8256, Experiment.finishPacket]).Safe
        memory width ⟨regs, .running⟩ := by
  let p1 := regs.write 8256 (regs 22)
  let p2 := p1.write 8257 (regs 8206)
  let p3 := p2.write 8258 (regs 8207)
  have f1 := running_write_fit width regs 8256 (regs 22) fit (fit.1 22)
  have f2 := running_write_fit width p1 8257 (regs 8206) f1 (fit.1 8206)
  have f3 := running_write_fit width p2 8258 (regs 8207) f2 (fit.1 8207)
  have w : p3 8256 = width := by simp [p3, p2, p1, Registers.write, hwidth]
  have p : p3 8257 = regs 8206 := by simp [p3, p2, p1, Registers.write]
  have l : p3 8258 = regs 8207 := by simp [p3]
  have spanSafe := spanBlock_safe 8256 width (regs 8206) (regs 8207) memory
    ⟨p3, .running⟩ (by omega) memoryFit f3 w p l position length
  have spanFit := Block.eval_fits memory width _ _ spanSafe
  have source := spanBlock_source 8256 width (regs 8206) (regs 8207) memory p3 w p l
  have frame := spanBlock_frame 8256 memory p3 8207 (by omega)
  have suffix : Experiment.finishPacket.Safe memory width
      ((spanBlock 8256).eval memory ⟨p3, .running⟩).final := by
    generalize he : (spanBlock 8256).eval memory ⟨p3, .running⟩ = loaded at spanFit source frame ⊢
    rcases loaded with ⟨⟨out, status⟩, reads⟩
    dsimp only at spanFit source frame ⊢
    cases decoded : decodeSpanNat width (regs 8206) (regs 8207) memory with
    | none =>
      have stopped := source.1
      simp only [decoded, SpanOutcome] at stopped
      apply Block.safe_stopped memory width _ _ spanFit
      rw [stopped]
      simp
    | some value =>
      have result := source.1
      simp only [decoded, SpanOutcome] at result
      obtain ⟨hstatus, hvalue⟩ := result
      subst status
      have hlength : out 8207 = regs 8207 := by
        simpa [p3, p2, p1, Registers.write] using frame
      apply finishPacket_safe memory width out hw spanFit
      · simpa only [hlength] using length
      · rw [hvalue, hlength]
        exact decodeSpanNat_value_lt width (regs 8206) (regs 8207) memory
          (by omega) length memoryFit value decoded
  simp only [Block.sequence, List.foldr_cons, List.foldr_nil]
  apply safe_move_seq memory width 8256 22 _ regs fit
  apply safe_move_seq memory width 8257 8206 _ p1 f1
  apply safe_move_seq memory width 8258 8207 _ p2 f2
  apply Block.safe_seq spanSafe
  exact Block.safe_seq suffix (Block.safe_skip memory width _
    (Block.eval_fits memory width _ _ suffix))

/-- Reaching the locator implies that all four descriptor attempts succeeded;
the proof follows the supplied replies, with no canonical-memory assumption. -/
private theorem descriptorLoads_successful (memory : Memory) (regs : Registers)
    (running : (Experiment.descriptorLoads.eval memory ⟨regs, .running⟩).final.status = .running) :
    ∃ bitBase bitLength stride count,
      memory[numericDescriptorAddress regs]? = some bitBase ∧
      memory[numericDescriptorAddress regs + 1]? = some bitLength ∧
      memory[numericDescriptorAddress regs + 2]? = some stride ∧
      memory[numericDescriptorAddress regs + 3]? = some count := by
  have hadd2 (a : Nat) : 1 + (1 + a) = 2 + a := by omega
  have hadd3 (a : Nat) : 1 + (2 + a) = 3 + a := by omega
  cases hb : memory[numericDescriptorAddress regs]? with
  | none =>
    simp only [numericDescriptorAddress, Nat.add_assoc] at hb
    simp [Experiment.descriptorLoads, Block.sequence, Block.eval_seq, Evaluation.bind,
      eval_action, Action.eval, Action.instruction, execute, State.writeNext, Data.ofState,
      Registers.write, Arithmetic.eval, Block.eval_stopped, hb, Nat.add_comm] at running
  | some bitBase =>
    cases hl : memory[numericDescriptorAddress regs + 1]? with
    | none =>
      simp only [numericDescriptorAddress, Nat.add_assoc, Nat.add_comm] at hb hl
      simp [Experiment.descriptorLoads, Block.sequence, Block.eval_seq, Evaluation.bind,
        eval_action, Action.eval, Action.instruction, execute, State.writeNext, Data.ofState,
        Registers.write, Arithmetic.eval, Block.eval_stopped, hb, hl,
        Nat.add_comm] at running
    | some bitLength =>
      cases hs : memory[numericDescriptorAddress regs + 2]? with
      | none =>
        simp only [numericDescriptorAddress, Nat.add_assoc, Nat.add_comm] at hb hl hs
        simp [Experiment.descriptorLoads, Block.sequence, Block.eval_seq, Evaluation.bind,
          eval_action, Action.eval, Action.instruction, execute, State.writeNext, Data.ofState,
          Registers.write, Arithmetic.eval, Block.eval_stopped, hb, hl, hs,
          Nat.add_comm, hadd2] at running
      | some stride =>
        cases hc : memory[numericDescriptorAddress regs + 3]? with
        | none =>
          simp only [numericDescriptorAddress, Nat.add_assoc, Nat.add_comm] at hb hl hs hc
          simp [Experiment.descriptorLoads, Block.sequence, Block.eval_seq, Evaluation.bind,
            eval_action, Action.eval, Action.instruction, execute, State.writeNext, Data.ofState,
            Registers.write, Arithmetic.eval, Block.eval_stopped, hb, hl, hs, hc,
            Nat.add_comm, hadd2, hadd3] at running
        | some count => exact ⟨bitBase, bitLength, stride, count, rfl, rfl, rfl, rfl⟩

private def readerPrepared (regs : Registers) : Registers :=
  (((regs.write 8194 0).write 8195 0).write 8208 23).write 8209 1

/-- Every entered scalar operation of the actual reader is safe. Geometry is
required only from successful descriptor replies; payload loads may still
fault, and every later source operation then remains stopped. -/
theorem physicalReader_safe (memory : Memory) (width : Nat) (regs : Registers)
    (hw : 8 ≤ width) (memoryFit : MemoryWordsFit memory width)
    (fit : (⟨regs, .running⟩ : Data).Fits width)
    (hwidth : regs 22 = width)
    (geometry : NumericReaderGeometry memory width regs) :
    Experiment.physicalReader.Safe memory width ⟨regs, .running⟩ := by
  have cap : 256 ≤ 2 ^ width := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hw
  by_cases active : regs 8192 < 23
  · let prepared := readerPrepared regs
    have f1 := running_write_fit width regs 8194 0 fit (by omega)
    have f2 := running_write_fit width (regs.write 8194 0) 8195 0 f1 (by omega)
    have f3 := running_write_fit width ((regs.write 8194 0).write 8195 0) 8208 23 f2 (by omega)
    have f4 : (⟨prepared, .running⟩ : Data).Fits width :=
      running_write_fit width _ 8209 1 f3 (by omega)
    have ga : NumericReaderGeometry memory width prepared := by
      simpa [NumericReaderGeometry, prepared, readerPrepared,
        numericDescriptorAddress, Registers.write] using geometry
    have pa : prepared 8192 < 23 := by
      simpa [prepared, readerPrepared, Registers.write] using active
    have wp : prepared 22 = width := by
      simpa [prepared, readerPrepared, Registers.write] using hwidth
    have dsafe := descriptorLoads_safe memory width prepared hw memoryFit f4 (ga.1 pa)
      (fun bitBase bitLength stride count hb hl hs hc hi =>
        (ga.2 pa bitBase bitLength stride count hb hl hs hc hi).1)
    have dfit := Block.eval_fits memory width _ _ dsafe
    let tail : Block := .ifZero 8205 .skip (Block.sequence [
      .action (.move 8256 22), .action (.move 8257 8206),
      .action (.move 8258 8207), spanBlock 8256, Experiment.finishPacket])
    have tsafe : tail.Safe memory width
        (Experiment.descriptorLoads.eval memory ⟨prepared, .running⟩).final := by
      by_cases running : (Experiment.descriptorLoads.eval memory ⟨prepared, .running⟩).final.status = .running
      · obtain ⟨bitBase, bitLength, stride, count, hb, hl, hs, hc⟩ :=
          descriptorLoads_successful memory prepared running
        have source := descriptorLoads_source memory prepared bitBase bitLength stride count hb hl hs hc
        have widthFrame := Block.eval_frame memory _ _ descriptorLoads_writes 22 (by omega)
          (⟨prepared, .running⟩ : Data)
        generalize hd : Experiment.descriptorLoads.eval memory ⟨prepared, .running⟩ = loaded at dfit source widthFrame running ⊢
        rcases loaded with ⟨⟨out, status⟩, reads⟩
        dsimp only at dfit source widthFrame running ⊢
        subst status
        have wo : out 22 = width := widthFrame.trans wp
        by_cases present : prepared 8193 < count
        · have bounds := ga.2 pa bitBase bitLength stride count hb hl hs hc present
          simp only [LocatedSpan, regularSpan, present, ↓reduceIte] at source
          obtain ⟨⟨_, hpresent, hposition, hlength⟩, _⟩ := source
          apply Block.safe_ifZero dfit
          have body := readerSpan_safe memory width out hw memoryFit dfit wo
            (by simpa only [hposition] using bounds.1)
            (by rw [hlength]; exact Nat.lt_of_le_of_lt (Nat.min_le_left _ _) bounds.2)
          simpa [tail, hpresent] using body
        · simp only [LocatedSpan, regularSpan, present, ↓reduceIte] at source
          obtain ⟨⟨_, hpresent, _, _⟩, _⟩ := source
          apply Block.safe_ifZero dfit
          simpa [tail, hpresent] using Block.safe_skip memory width ⟨out, .running⟩ dfit
      · exact Block.safe_stopped memory width tail _ dfit running
    have dc := checks_of_safe memory width _ _ dsafe
    have tc := checks_of_safe memory width _ _ tsafe
    simp only [prepared, readerPrepared] at dc
    simp only [tail, prepared, readerPrepared, Block.sequence,
      List.foldr_cons, List.foldr_nil] at tc
    apply ScalarChecks_safe memory width _ _ fit
    simp [Experiment.physicalReader, Block.sequence, checks_seq, checks_action,
      checks_ifZero, checks_skip, Block.eval_seq, Evaluation.bind, eval_action,
      eval_skip, eval_ifZero, Action.eval, Action.instruction, Action.LocalSafe,
      execute, State.writeNext, Data.ofState, Registers.write, Comparison.eval,
      active, dc, tc] <;> omega
  · apply ScalarChecks_safe memory width _ _ fit
    simp [Experiment.physicalReader, Block.sequence, checks_seq, checks_action,
      checks_ifZero, checks_skip, eval_action,
      eval_skip, eval_ifZero, Action.eval, Action.instruction, Action.LocalSafe,
      execute, State.writeNext, Data.ofState, Registers.write, Comparison.eval,
      active] <;> omega

/-- An exact expected-type consumer of the full generic safety interface. -/
example (memory : Memory) (width : Nat) (regs : Registers)
    (hw : 8 ≤ width) (memoryFit : MemoryWordsFit memory width)
    (fit : (⟨regs, .running⟩ : Data).Fits width)
    (hwidth : regs 22 = width)
    (geometry : NumericReaderGeometry memory width regs) :
    Experiment.physicalReader.Safe memory width ⟨regs, .running⟩ :=
  physicalReader_safe memory width regs hw memoryFit fit hwidth geometry

#print axioms descriptorLoads_safe
#print axioms finishPacket_safe
#print axioms physicalReader_safe

end RMQ.PackedBitvector
