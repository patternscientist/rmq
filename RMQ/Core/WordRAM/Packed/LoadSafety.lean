import RMQ.Core.WordRAM.Packed.Safety
import RMQ.Core.WordRAM.Packed.SpanAssembly
import RMQ.Core.WordRAM.Packed.Setup
import RMQ.Core.WordRAM.Packed.Width

/-!
# Word safety of the actual scalar loaders

Numeric memory may be short: a failed read remains a real attempt and stops
the routine. The span bounds apply to the masked fragments that the source
actually computes, including the second address before its lookup.
-/

namespace RMQ.SuccinctFinal.PackedWordRAM

open Cartesian PackedCellProbe Structured

/-- A property of numeric cells; no presence assumption is included. -/
def MemoryWordsFit (memory : Memory) (width : Nat) : Prop :=
  ∀ value ∈ memory, value < 2 ^ width

theorem MemoryWordsFit.reply {memory : Memory} {width : Nat}
    (fit : MemoryWordsFit memory width) {address value : Nat}
    (reply : memory[address]? = some value) : value < 2 ^ width :=
  fit value (List.mem_of_getElem? reply)

/-- Local scalar checks without repeating the all-register invariant at every
syntax node. The preservation lemma below restores that invariant. -/
private def localChecks (memory : Memory) (width : Nat) : Block → Data → Prop
  | block, s => s.status = .running →
      match block with
      | .skip => True
      | .action op => op.LocalSafe memory width s
      | .exit src => s.regs src < 2 ^ width
      | .seq first second => localChecks memory width first s ∧
          localChecks memory width second (first.eval memory s).final
      | .ifZero condition zero nonzero =>
          if s.regs condition = 0 then localChecks memory width zero s
          else localChecks memory width nonzero s
      | .repeat count body =>
          IterationsSafe (localChecks memory width body) (body.eval memory) count s

private theorem localChecks_safe (memory : Memory) (width : Nat) (block : Block)
    (s : Data) (fit : s.Fits width) (checks : localChecks memory width block s) :
    block.Safe memory width s := by
  induction block generalizing s with
  | skip => exact Block.safe_skip memory width s fit
  | action op => exact ⟨fit, checks⟩
  | exit src => exact ⟨fit, checks⟩
  | seq first second ihf ihs =>
      refine ⟨fit, fun hs => ?_⟩
      have hf := ihf s fit (checks hs).1
      exact ⟨hf, ihs _ (first.eval_fits memory width s hf) (checks hs).2⟩
  | ifZero condition zero nonzero ihz ihn =>
      refine ⟨fit, fun hs => ?_⟩
      have hc := checks hs
      by_cases hz : s.regs condition = 0
      · simpa [hz] using ihz s fit (by simpa [hz] using hc)
      · simpa [hz] using ihn s fit (by simpa [hz] using hc)
  | «repeat» count body ih =>
      refine ⟨fit, fun hs => ?_⟩
      have hc := checks hs
      clear checks hs
      induction count generalizing s with
      | zero => trivial
      | succ count iht =>
          have hb := ih s fit hc.1
          exact ⟨hb, iht _ (body.eval_fits memory width s hb) hc.2⟩

@[simp] private theorem localChecks_stopped (memory : Memory) (width : Nat)
    (block : Block) (s : Data) (stopped : s.status ≠ .running) :
    localChecks memory width block s := by
  cases block <;> exact fun h => (stopped h).elim

private theorem localChecks_step {memory : Memory} {width : Nat} {op : Action}
    {rest : Block} {s : Data} (operation : op.LocalSafe memory width s)
    (tail : localChecks memory width rest (op.eval memory s).final) :
    localChecks memory width (.seq (.action op) rest) s := by
  intro hs
  exact ⟨fun _ => operation, by simpa [Block.eval, hs] using tail⟩

private theorem localChecks_action {memory : Memory} {width : Nat} {op : Action}
    {s : Data} (operation : op.LocalSafe memory width s) :
    localChecks memory width (.action op) s := fun _ => operation

private theorem localChecks_branch {memory : Memory} {width condition : Nat}
    {zero nonzero : Block} {s : Data}
    (arm : if s.regs condition = 0 then localChecks memory width zero s
      else localChecks memory width nonzero s) :
    localChecks memory width (.ifZero condition zero nonzero) s := fun _ => arm

private theorem localChecks_seq_skip {memory : Memory} {width : Nat}
    {first : Block} {s : Data} (head : localChecks memory width first s) :
    localChecks memory width (.seq first .skip) s :=
  fun _ => ⟨head, fun _ => True.intro⟩

private theorem load_shiftRight (a b : Nat) : Nat.shiftRight a b = a / 2 ^ b :=
  Nat.shiftRight_eq_div_pow a b

private theorem load_shiftLeft (a b : Nat) : Nat.shiftLeft a b = a * 2 ^ b :=
  Nat.shiftLeft_eq a b

local syntax "loader_path" : tactic
local macro_rules
  | `(tactic| loader_path) => `(tactic| (
    first
    | apply localChecks_stopped
      solve | simp
    | apply localChecks_step
    | apply localChecks_branch
    | apply localChecks_action
    | apply localChecks_seq_skip
    | exact fun _ => True.intro
    all_goals
      try simp [*, Action.eval, Action.instruction, Action.LocalSafe, execute,
        State.writeNext, Data.ofState, Registers.write, Arithmetic.eval, Comparison.eval,
        load_shiftRight, load_shiftLeft, -localChecks_stopped]
      all_goals first | omega | loader_path))
theorem span_offset_sum_fit (width offset len : Nat) (hw : 2 ≤ width)
    (ho : offset < width) (hl : len < width) : offset + len < 2 ^ width := by
  have linear : ∀ n, 2 ≤ n → 2 * n - 2 < 2 ^ n := by
    intro n hn
    induction n with
    | zero => omega
    | succ n ih =>
        by_cases h : n = 1
        · subst n; decide
        · have hnn : 2 ≤ n := by omega
          have hp := ih hnn
          rw [Nat.pow_succ]
          omega
  have := linear width hw
  omega

theorem span_next_address_fit (width position : Nat) (hw : 2 ≤ width)
    (hp : position < 2 ^ width) : position / width + 1 < 2 ^ width := by
  by_cases hz : position = 0
  · subst position
    have hcap := Nat.pow_le_pow_right (by decide : 0 < 2) hw
    simp only [Nat.zero_div]
    omega
  · have := Nat.div_lt_self (by omega : 0 < position) (by omega : 1 < width)
    omega

/-- Bounds for both fragments of the crossing arm. The unmasked first word
is shifted right; the second word is reduced before its left shift. -/
theorem span_crossing_bounds (width offset len first second : Nat)
    (ho : offset < width) (hl : len < width) (cross : width < offset + len)
    (hf : first < 2 ^ width) :
    0 < offset ∧ 0 < width - offset ∧ width - offset < width ∧
    width - offset ≤ len ∧ len - (width - offset) < width ∧
    first / 2 ^ offset < 2 ^ (width - offset) ∧
    second % 2 ^ (len - (width - offset)) * 2 ^ (width - offset) < 2 ^ len ∧
    first / 2 ^ offset +
      second % 2 ^ (len - (width - offset)) * 2 ^ (width - offset) < 2 ^ len := by
  have hlow : width - offset + offset = width := by omega
  have htotal : len - (width - offset) + (width - offset) = len := by omega
  have hfirst : first / 2 ^ offset < 2 ^ (width - offset) := by
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos offset)).2
    simpa only [← Nat.pow_add, hlow] using hf
  have hsecond := Nat.mod_lt second (Nat.two_pow_pos (len - (width - offset)))
  have hmul := Nat.mul_lt_mul_of_pos_right hsecond (Nat.two_pow_pos (width - offset))
  have hsum : first / 2 ^ offset +
      second % 2 ^ (len - (width - offset)) * 2 ^ (width - offset) <
      2 ^ (len - (width - offset)) * 2 ^ (width - offset) := by
    have hle : second % 2 ^ (len - (width - offset)) + 1 ≤
        2 ^ (len - (width - offset)) := by omega
    have hh := Nat.mul_le_mul_right (2 ^ (width - offset)) hle
    rw [Nat.add_mul] at hh
    omega
  rw [← Nat.pow_add, htotal] at hmul hsum
  exact ⟨by omega, by omega, by omega, by omega, by omega, hfirst, hmul, hsum⟩

private theorem span_checks_zero (base width position len : Nat) (memory : Memory)
    (regs : Registers) (hw : 2 ≤ width) (_memoryFit : MemoryWordsFit memory width)
    (fit : (⟨regs, .running⟩ : Data).Fits width) (hwreg : regs base = width)
    (_hpreg : regs (base + 1) = position) (hlreg : regs (base + 2) = len)
    (hp : position < 2 ^ width) (hl : len < width)
    (hz : len = 0) :
    localChecks memory width (spanBlock base) ⟨regs, .running⟩ := by
  have hwfit : width < 2 ^ width := by simpa [hwreg] using fit.1 base
  have hpos : 0 < width := by omega
  have hzero := Nat.two_pow_pos width
  have hone : 1 < 2 ^ width := by
    have := Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega : 0 < width)
    simpa using this
  have hquot := Nat.div_lt_of_lt (b := width) hp
  have hoff := Nat.mod_lt position hpos
  have hofffit : position % width < 2 ^ width := by omega
  have hsum := span_offset_sum_fit width (position % width) len hw hoff hl
  have hnext := span_next_address_fit width position hw hp
  have hmask := Nat.pow_lt_pow_right (by decide : 1 < 2) hl
  have hmaskpos := Nat.two_pow_pos len
  have hcmp : (if position % width + len ≤ width then 1 else 0) < 2 ^ width := by
    split <;> omega

  simp only [spanBlock, Block.sequence, List.foldr_cons, List.foldr_nil]
  loader_path
private theorem span_checks_missing_first (base width position len : Nat) (memory : Memory)
    (regs : Registers) (hw : 2 ≤ width) (_memoryFit : MemoryWordsFit memory width)
    (fit : (⟨regs, .running⟩ : Data).Fits width) (hwreg : regs base = width)
    (hpreg : regs (base + 1) = position) (hlreg : regs (base + 2) = len)
    (hp : position < 2 ^ width) (hl : len < width)
    (hz : len ≠ 0) (hf : memory[position / width]? = none) :
    localChecks memory width (spanBlock base) ⟨regs, .running⟩ := by
  have hwfit : width < 2 ^ width := by simpa [hwreg] using fit.1 base
  have hpos : 0 < width := by omega
  have hzero := Nat.two_pow_pos width
  have hone : 1 < 2 ^ width := by
    have := Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega : 0 < width)
    simpa using this
  have hquot := Nat.div_lt_of_lt (b := width) hp
  have hoff := Nat.mod_lt position hpos
  have hofffit : position % width < 2 ^ width := by omega
  have hsum := span_offset_sum_fit width (position % width) len hw hoff hl
  have hnext := span_next_address_fit width position hw hp
  have hmask := Nat.pow_lt_pow_right (by decide : 1 < 2) hl
  have hmaskpos := Nat.two_pow_pos len
  have hcmp : (if position % width + len ≤ width then 1 else 0) < 2 ^ width := by
    split <;> omega

  simp only [spanBlock, Block.sequence, List.foldr_cons, List.foldr_nil]
  loader_path
private theorem span_checks_contained (base width position len : Nat) (memory : Memory)
    (regs : Registers) (hw : 2 ≤ width) (memoryFit : MemoryWordsFit memory width)
    (fit : (⟨regs, .running⟩ : Data).Fits width) (hwreg : regs base = width)
    (hpreg : regs (base + 1) = position) (hlreg : regs (base + 2) = len)
    (hp : position < 2 ^ width) (hl : len < width)
    (hz : len ≠ 0) (first : Nat) (hf : memory[position / width]? = some first)
    (hc : position % width + len ≤ width) :
    localChecks memory width (spanBlock base) ⟨regs, .running⟩ := by
  have hwfit : width < 2 ^ width := by simpa [hwreg] using fit.1 base
  have hpos : 0 < width := by omega
  have hzero := Nat.two_pow_pos width
  have hone : 1 < 2 ^ width := by
    have := Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega : 0 < width)
    simpa using this
  have hquot := Nat.div_lt_of_lt (b := width) hp
  have hoff := Nat.mod_lt position hpos
  have hofffit : position % width < 2 ^ width := by omega
  have hsum := span_offset_sum_fit width (position % width) len hw hoff hl
  have hnext := span_next_address_fit width position hw hp
  have hmask := Nat.pow_lt_pow_right (by decide : 1 < 2) hl
  have hmaskpos := Nat.two_pow_pos len
  have hcmp : (if position % width + len ≤ width then 1 else 0) < 2 ^ width := by
    split <;> omega
  have hfirst := memoryFit.reply hf
  have hshift := Nat.div_lt_of_lt (b := 2 ^ (position % width)) hfirst
  have hmod := Nat.lt_trans (Nat.mod_lt (first / 2 ^ (position % width)) hmaskpos) hmask
  simp only [spanBlock, Block.sequence, List.foldr_cons, List.foldr_nil]
  loader_path
private theorem span_checks_missing_second (base width position len : Nat) (memory : Memory)
    (regs : Registers) (hw : 2 ≤ width) (memoryFit : MemoryWordsFit memory width)
    (fit : (⟨regs, .running⟩ : Data).Fits width) (hwreg : regs base = width)
    (hpreg : regs (base + 1) = position) (hlreg : regs (base + 2) = len)
    (hp : position < 2 ^ width) (hl : len < width)
    (hz : len ≠ 0) (first : Nat) (hf : memory[position / width]? = some first)
    (hc : ¬position % width + len ≤ width) (hs : memory[position / width + 1]? = none) :
    localChecks memory width (spanBlock base) ⟨regs, .running⟩ := by
  have hwfit : width < 2 ^ width := by simpa [hwreg] using fit.1 base
  have hpos : 0 < width := by omega
  have hzero := Nat.two_pow_pos width
  have hone : 1 < 2 ^ width := by
    have := Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega : 0 < width)
    simpa using this
  have hquot := Nat.div_lt_of_lt (b := width) hp
  have hoff := Nat.mod_lt position hpos
  have hofffit : position % width < 2 ^ width := by omega
  have hsum := span_offset_sum_fit width (position % width) len hw hoff hl
  have hnext := span_next_address_fit width position hw hp
  have hmask := Nat.pow_lt_pow_right (by decide : 1 < 2) hl
  have hmaskpos := Nat.two_pow_pos len
  have hcmp : (if position % width + len ≤ width then 1 else 0) < 2 ^ width := by
    split <;> omega
  have hfirst := memoryFit.reply hf
  have hshift := Nat.div_lt_of_lt (b := 2 ^ (position % width)) hfirst
  have hmod := Nat.lt_trans (Nat.mod_lt (first / 2 ^ (position % width)) hmaskpos) hmask
  have bounds := span_crossing_bounds width (position % width) len first 0
    hoff hl (by omega) hfirst
  have hlofit : width - position % width < 2 ^ width := by omega
  have hhifit : len - (width - position % width) < 2 ^ width := by omega
  have hhimask := Nat.pow_lt_pow_right (by decide : 1 < 2) bounds.2.2.2.2.1
  have hhipos := Nat.two_pow_pos (len - (width - position % width))
  simp only [spanBlock, Block.sequence, List.foldr_cons, List.foldr_nil]
  loader_path
private theorem span_checks_crossing (base width position len : Nat) (memory : Memory)
    (regs : Registers) (hw : 2 ≤ width) (memoryFit : MemoryWordsFit memory width)
    (fit : (⟨regs, .running⟩ : Data).Fits width) (hwreg : regs base = width)
    (hpreg : regs (base + 1) = position) (hlreg : regs (base + 2) = len)
    (hp : position < 2 ^ width) (hl : len < width)
    (hz : len ≠ 0) (first : Nat) (hf : memory[position / width]? = some first)
    (hc : ¬position % width + len ≤ width) (second : Nat)
    (hs : memory[position / width + 1]? = some second) :
    localChecks memory width (spanBlock base) ⟨regs, .running⟩ := by
  have hwfit : width < 2 ^ width := by simpa [hwreg] using fit.1 base
  have hpos : 0 < width := by omega
  have hzero := Nat.two_pow_pos width
  have hone : 1 < 2 ^ width := by
    have := Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega : 0 < width)
    simpa using this
  have hquot := Nat.div_lt_of_lt (b := width) hp
  have hoff := Nat.mod_lt position hpos
  have hofffit : position % width < 2 ^ width := by omega
  have hsum := span_offset_sum_fit width (position % width) len hw hoff hl
  have hnext := span_next_address_fit width position hw hp
  have hmask := Nat.pow_lt_pow_right (by decide : 1 < 2) hl
  have hmaskpos := Nat.two_pow_pos len
  have hcmp : (if position % width + len ≤ width then 1 else 0) < 2 ^ width := by
    split <;> omega
  have hfirst := memoryFit.reply hf
  have hshift := Nat.div_lt_of_lt (b := 2 ^ (position % width)) hfirst
  have hmod := Nat.lt_trans (Nat.mod_lt (first / 2 ^ (position % width)) hmaskpos) hmask
  have bounds := span_crossing_bounds width (position % width) len first 0
    hoff hl (by omega) hfirst
  have hlofit : width - position % width < 2 ^ width := by omega
  have hhifit : len - (width - position % width) < 2 ^ width := by omega
  have hhimask := Nat.pow_lt_pow_right (by decide : 1 < 2) bounds.2.2.2.2.1
  have hhipos := Nat.two_pow_pos (len - (width - position % width))
  have hsecond := memoryFit.reply hs
  have hb := span_crossing_bounds width (position % width) len first second
    hoff hl (by omega) hfirst
  have hhmod := Nat.lt_trans (Nat.mod_lt second hhipos) hhimask
  have hhshift := Nat.lt_trans hb.2.2.2.2.2.2.1 hmask
  have hanswer := Nat.lt_trans hb.2.2.2.2.2.2.2 hmask
  simp only [spanBlock, Block.sequence, List.foldr_cons, List.foldr_nil]
  loader_path
/-- Every source operation is safe on fitting memory, including a missing
first or second cell. Register identifiers are handled separately by code fit. -/
theorem spanBlock_safe (base width position len : Nat) (memory : Memory)
    (s : Data) (hw : 2 ≤ width) (memoryFit : MemoryWordsFit memory width)
    (fit : s.Fits width) (hwreg : s.regs base = width)
    (hpreg : s.regs (base + 1) = position) (hlreg : s.regs (base + 2) = len)
    (hp : position < 2 ^ width) (hl : len < width) :
    (spanBlock base).Safe memory width s := by
  apply localChecks_safe memory width _ s fit
  cases s with
  | mk regs status =>
    cases status with
    | halted value => exact localChecks_stopped _ _ _ _ (by simp)
    | fault => exact localChecks_stopped _ _ _ _ (by simp)
    | running =>
      simp only at hwreg hpreg hlreg
      by_cases hz : len = 0
      · exact span_checks_zero base width position len memory regs hw memoryFit fit
          hwreg hpreg hlreg hp hl hz
      · cases hf : memory[position / width]? with
        | none =>
            exact span_checks_missing_first base width position len memory regs hw memoryFit fit
              hwreg hpreg hlreg hp hl hz hf
        | some first =>
          by_cases hc : position % width + len ≤ width
          · exact span_checks_contained base width position len memory regs hw memoryFit fit
              hwreg hpreg hlreg hp hl hz first hf hc
          · cases hs : memory[position / width + 1]? with
            | none =>
                exact span_checks_missing_second base width position len memory regs hw memoryFit fit
                  hwreg hpreg hlreg hp hl hz first hf hc hs
            | some second =>
                exact span_checks_crossing base width position len memory regs hw memoryFit fit
                  hwreg hpreg hlreg hp hl hz first hf hc second hs

/-- Setup safety needs no installed metadata or successful-load hypothesis. -/
theorem metadataSetupFrom_safe (memory : Memory) (width start count : Nat)
    (memoryFit : MemoryWordsFit memory width) (bound : start + count ≤ 2 ^ width)
    (s : Data) (fit : s.Fits width) :
    (metadataSetupFrom start count).Safe memory width s := by
  induction count generalizing start s with
  | zero => exact Block.safe_skip memory width s fit
  | succ count ih =>
    have hconstant : (Block.action (.constant 6 start)).Safe memory width s :=
      Block.safe_action memory width _ s fit (by change start < 2 ^ width; omega)
    have hload : (Block.action (.load (16 + start) 6)).Safe memory width
        ((Block.action (.constant 6 start)).eval memory s).final := by
      apply Block.safe_action
      · exact Block.eval_fits memory width _ s hconstant
      · intro value reply
        exact memoryFit.reply reply
    have hp := Block.safe_seq hconstant hload
    exact Block.safe_seq hp (ih (start + 1) (by omega) _
      (Block.eval_fits memory width (metadataLoadPair start) s hp))

theorem metadataSetupBlock_safe (memory : Memory) (width : Nat)
    (hw : 8 ≤ width) (memoryFit : MemoryWordsFit memory width)
    (s : Data) (fit : s.Fits width) : metadataSetupBlock.Safe memory width s := by
  apply metadataSetupFrom_safe memory width 0 174 memoryFit _ s fit
  have := Nat.pow_le_pow_right (by decide : 0 < 2) hw
  omega

theorem buildMemory_setup_safe (xs : List Int) (s : Data)
    (fit : s.Fits (wordWidth xs.length)) :
    metadataSetupBlock.Safe (buildMemory xs) (wordWidth xs.length) s :=
  metadataSetupBlock_safe _ _ (by unfold wordWidth; omega)
    (buildMemory_words_fit xs) s fit

theorem spanBlock_fieldsFit (base width : Nat) (bound : base + 23 < 2 ^ width) :
    (spanBlock base).FieldsFit width := by
  simp [spanBlock, Block.sequence, Block.FieldsFit, Action.instruction,
    Instruction.Fits, Instruction.encoding, Instruction.operands,
    Arithmetic.code, Comparison.code]
  have hw : width ≠ 0 := by intro h; simp [h] at bound
  repeat' constructor
  all_goals omega

theorem spanRoutine_safe (base width position len : Nat) (memory : Memory)
    (s : Data) (hw : 2 ≤ width) (memoryFit : MemoryWordsFit memory width)
    (fit : s.Fits width) (hwreg : s.regs base = width)
    (hpreg : s.regs (base + 1) = position) (hlreg : s.regs (base + 2) = len)
    (hp : position < 2 ^ width) (hl : len < width) :
    (spanRoutine base).Safe memory width s := by
  have hb := spanBlock_safe base width position len memory s hw memoryFit fit hwreg hpreg hlreg hp hl
  exact Block.safe_seq hb (Block.safe_exit memory width (base + 3) _
    (Block.eval_fits memory width (spanBlock base) s hb))

/-- Same hosted run: scalar value/receipts and all primitive safety clauses. -/
theorem spanBlock_machine_safe (base codeStart width position len : Nat)
    (memory : Memory) (program : Program) (regs : Registers)
    (hw : 2 ≤ width) (memoryFit : MemoryWordsFit memory width)
    (registerFit : ∀ r, regs r < 2 ^ width)
    (hwreg : regs base = width) (hpreg : regs (base + 1) = position)
    (hlreg : regs (base + 2) = len) (hp : position < 2 ^ width) (hl : len < width)
    (host : HostedAt program codeStart ((spanBlock base).compileAt codeStart))
    (fields : (spanBlock base).FieldsFit width) (endFit : codeStart + 22 < 2 ^ width) :
    ∃ used, used ≤ 22 ∧
      let actual := run memory program used ⟨regs, codeStart, .running⟩
      SpanOutcome base (decodeSpanNat width position len memory) (Data.ofState actual.final) ∧
      actual.reads = spanAttemptReceipts width position len memory ∧
      (∀ r, r < base + 3 ∨ base + 14 ≤ r → actual.final.regs r = regs r) ∧
      actual.steps = used ∧
      (actual.final.status = .running → actual.final.pc = codeStart + 22) ∧
      actual.final.Fits width ∧
      (∀ (index : Nat) (t : Transition), actual.transitions[index]? = some t →
        Instruction.Safe width t.before t.instruction ∧ t.after.Fits width) ∧
      (∀ index, index ≤ used →
        (run memory program index ⟨regs, codeStart, .running⟩).final.Fits width) := by
  have fit : (⟨regs, .running⟩ : Data).Fits width :=
    ⟨registerFit, fun _ h => Status.noConfusion h⟩
  obtain ⟨used, hu, hd, hr, hc, hpc, hf, ht, hprefix⟩ :=
    (spanBlock base).compile_safe_correct memory program width codeStart
      ⟨regs, codeStart, .running⟩ rfl host fields (by simpa using endFit)
      ⟨by change codeStart < 2 ^ width; omega, fit⟩
      (spanBlock_safe base width position len memory _ hw memoryFit fit hwreg hpreg hlreg hp hl)
  have he := spanBlock_source base width position len memory regs hwreg hpreg hlreg
  refine ⟨used, by simpa using hu, ?_⟩
  dsimp only
  refine ⟨?_, hr.trans he.2, ?_, hc, by simpa using hpc, hf, ht, hprefix⟩
  · rw [hd]; exact he.1
  · intro r hframe
    exact (congrArg (fun d : Data => d.regs r) hd).trans
      (spanBlock_frame base memory regs r hframe)

/-- Same 23-fuel standalone run as spanRun_correct, now with safety for every
attempt, executed instruction and prefix, even after an early fault. -/
theorem spanRun_safe (base width position len : Nat) (memory : Memory)
    (regs : Registers) (hw : 2 ≤ width) (memoryFit : MemoryWordsFit memory width)
    (registerFit : ∀ r, regs r < 2 ^ width)
    (hwreg : regs base = width) (hpreg : regs (base + 1) = position)
    (hlreg : regs (base + 2) = len) (hp : position < 2 ^ width) (hl : len < width)
    (codeFit : base + 23 < 2 ^ width) :
    let actual := spanRun base memory regs
    actual.result = decodeSpanNat width position len memory ∧
    actual.final.status = (match decodeSpanNat width position len memory with
      | none => .fault | some value => .halted value) ∧
    actual.reads = spanAttemptReceipts width position len memory ∧
    (∀ r, r < base + 3 ∨ base + 14 ≤ r → actual.final.regs r = regs r) ∧
    actual.steps ≤ 23 ∧ actual.final.Fits width ∧
    (∀ (index : Nat) (t : Transition), actual.transitions[index]? = some t →
      Instruction.Safe width t.before t.instruction ∧ t.after.Fits width) ∧
    (∀ index, index ≤ 23 →
      (run memory (spanProgram base) index ⟨regs, 0, .running⟩).final.Fits width) := by
  have fit : (⟨regs, .running⟩ : Data).Fits width :=
    ⟨registerFit, fun _ h => Status.noConfusion h⟩
  have fields : (spanRoutine base).FieldsFit width := by
    refine ⟨spanBlock_fieldsFit base width codeFit, ?_⟩
    simp [Block.FieldsFit, Instruction.Fits, Instruction.encoding, Instruction.operands]
    omega
  have hc := (spanRoutine base).compile_run_safe memory width ⟨regs, 0, .running⟩ rfl
    fields (by simp only [spanRoutine_size]; omega) ⟨by change 0 < 2 ^ width; omega, fit⟩
    (spanRoutine_safe base width position len memory _ hw memoryFit fit hwreg hpreg hlreg hp hl)
  have he := spanRun_correct base width position len memory regs hwreg hpreg hlreg
  refine ⟨he.1, he.2.1, he.2.2.1, he.2.2.2.1, he.2.2.2.2, ?_⟩
  simpa only [spanRun, spanProgram, spanRoutine_size] using hc.2.2.2.2

theorem spanInputRegisters_fit (base width position len : Nat)
    (hp : position < 2 ^ width) (hl : len < width) :
    ∀ r, spanInputRegisters base width position len r < 2 ^ width := by
  have hw : width < 2 ^ width := Nat.lt_pow_self (by decide : 1 < 2)
  intro r
  simp only [spanInputRegisters, Registers.write]
  repeat' split
  all_goals omega

/-- One bounded register-bank theorem covers bases 8192 and 8256. Numeric
geometry is runtime input; the register base only chooses the fixed source. -/
theorem spanRun_canonical_safe (xs : List Int) (base position len : Nat)
    (baseFit : base + 23 < 2 ^ 32) (hp : position < 2 ^ wordWidth xs.length)
    (hl : len < wordWidth xs.length) :
    let width := wordWidth xs.length
    let regs := spanInputRegisters base width position len
    let actual := spanRun base (buildMemory xs) regs
    actual.result = decodeSpanNat width position len (buildMemory xs) ∧
    actual.final.status = (match decodeSpanNat width position len (buildMemory xs) with
      | none => .fault | some value => .halted value) ∧
    actual.reads = spanAttemptReceipts width position len (buildMemory xs) ∧
    (∀ r, r < base + 3 ∨ base + 14 ≤ r → actual.final.regs r = regs r) ∧
    actual.steps ≤ 23 ∧ actual.final.Fits width ∧
    (∀ (index : Nat) (t : Transition), actual.transitions[index]? = some t →
      Instruction.Safe width t.before t.instruction ∧ t.after.Fits width) ∧
    (∀ index, index ≤ 23 →
      (run (buildMemory xs) (spanProgram base) index ⟨regs, 0, .running⟩).final.Fits width) := by
  have hw : 32 ≤ wordWidth xs.length := by unfold wordWidth; omega
  apply spanRun_safe base (wordWidth xs.length) position len (buildMemory xs)
    (spanInputRegisters base (wordWidth xs.length) position len) (by omega)
    (buildMemory_words_fit xs) (spanInputRegisters_fit _ _ _ _ hp hl)
    (by simp [spanInputRegisters, Registers.write])
    (by simp [spanInputRegisters, Registers.write])
    (by simp [spanInputRegisters, Registers.write]) hp hl
  exact Nat.lt_of_lt_of_le baseFit (Nat.pow_le_pow_right (by decide : 0 < 2) hw)

/-- Canonical setup retains its actual installed words and ordered receipt list
while every instruction and every prefix satisfies the declared word width. -/
theorem buildMemory_setup_run_safe (xs : List Int) (s : State)
    (hpc : s.pc = 0) (hs : s.status = .running)
    (registerFit : ∀ r, s.regs r < 2 ^ wordWidth xs.length) :
    let width := wordWidth xs.length
    let actual := run (buildMemory xs) (metadataSetupBlock.compileAt 0) 348 s
    actual.final.status = .running ∧
    (∀ i < 174, actual.final.regs (16 + i) =
      ((metadata (SuccinctClassic.cartesianShape xs))[i]?).getD 0) ∧
    actual.final.regs 6 = 173 ∧
    (∀ r, r ≠ 6 → (r < 16 ∨ 190 ≤ r) → actual.final.regs r = s.regs r) ∧
    actual.reads = (List.range 174).map
      (fun i => ⟨i, (metadata (SuccinctClassic.cartesianShape xs))[i]?⟩) ∧
    actual.steps ≤ 348 ∧ actual.final.pc = 348 ∧ actual.final.Fits width ∧
    (∀ (index : Nat) (t : Transition), actual.transitions[index]? = some t →
      Instruction.Safe width t.before t.instruction ∧ t.after.Fits width) ∧
    (∀ index, index ≤ 348 →
      (run (buildMemory xs) (metadataSetupBlock.compileAt 0) index s).final.Fits width) := by
  have fit : (Data.ofState s).Fits (wordWidth xs.length) :=
    ⟨registerFit, fun _ h => by simp [Data.ofState, hs] at h⟩
  have hw : 32 ≤ wordWidth xs.length := by unfold wordWidth; omega
  have bound : metadataSetupBlock.size < 2 ^ wordWidth xs.length := by
    rw [metadataSetupBlock_size]
    exact Nat.lt_of_lt_of_le (by decide : 348 < 2 ^ 32)
      (Nat.pow_le_pow_right (by decide : 0 < 2) hw)
  have hc := metadataSetupBlock.compile_run_safe (buildMemory xs) (wordWidth xs.length)
    s hpc (metadataSetupBlock_fieldsFit xs.length) bound
    ⟨by rw [hpc]; exact Nat.two_pow_pos _, fit⟩ (buildMemory_setup_safe xs _ fit)
  rw [metadataSetupBlock_size] at hc
  have he := buildMemory_setup_run xs s hpc hs registerFit
  exact ⟨he.1, he.2.1, he.2.2.1, he.2.2.2.1, he.2.2.2.2.1,
    he.2.2.2.2.2.1, he.2.2.2.2.2.2.1, hc.2.2.2.2⟩

/-- Hosted metadata uses the same raw-memory source result and receipts as its
primitive segment. No successful-setup premise is needed for this safety join. -/
theorem metadataSetupBlock_hosted_safe (memory : Memory) (program : Program)
    (width base : Nat) (s : State) (hw : 8 ≤ width)
    (memoryFit : MemoryWordsFit memory width) (fit : s.Fits width)
    (hpc : s.pc = base) (host : HostedAt program base (metadataSetupBlock.compileAt base))
    (fields : metadataSetupBlock.FieldsFit width) (endFit : base + 348 < 2 ^ width) :
    ∃ used, used ≤ 348 ∧
      Data.ofState (run memory program used s).final =
        (metadataSetupBlock.eval memory (Data.ofState s)).final ∧
      (run memory program used s).reads = (metadataSetupBlock.eval memory (Data.ofState s)).reads ∧
      (run memory program used s).steps = used ∧
      ((run memory program used s).final.status = .running →
        (run memory program used s).final.pc = base + 348) ∧
      (run memory program used s).final.Fits width ∧
      (∀ (index : Nat) (t : Transition), (run memory program used s).transitions[index]? = some t →
        Instruction.Safe width t.before t.instruction ∧ t.after.Fits width) ∧
      (∀ index, index ≤ used → (run memory program index s).final.Fits width) := by
  simpa only [metadataSetupBlock_size] using
    metadataSetupBlock.compile_safe_correct memory program width base s hpc host fields
      (by simpa only [metadataSetupBlock_size] using endFit) fit
      (metadataSetupBlock_safe memory width hw memoryFit (Data.ofState s) fit.2)

/-- Actual transition occurrence backing includes representable failed
addresses and successful reply words, at the span run's one declared width. -/
theorem spanRun_safe_read (base width position len : Nat) (memory : Memory)
    (regs : Registers) (hw : 2 ≤ width) (memoryFit : MemoryWordsFit memory width)
    (registerFit : ∀ r, regs r < 2 ^ width)
    (hwreg : regs base = width) (hpreg : regs (base + 1) = position)
    (hlreg : regs (base + 2) = len) (hp : position < 2 ^ width) (hl : len < width)
    (codeFit : base + 23 < 2 ^ width) (index : Nat) (t : Transition) (receipt : Receipt)
    (occurrence : (spanRun base memory regs).transitions[index]? = some t)
    (read : t.receipt = some receipt) :
    receipt.address < 2 ^ width ∧ receipt.reply = memory[receipt.address]? ∧
      (∀ value, receipt.reply = some value → value < 2 ^ width) := by
  have h := spanRun_safe base width position len memory regs hw memoryFit registerFit
    hwreg hpreg hlreg hp hl codeFit
  have ht := h.2.2.2.2.2.2.1 index t occurrence
  exact run_read_fits occurrence read ht.1 ht.2

namespace LoadSafetyConsumers

/-- Exact symbolic source type, independent of the declaration it consumes. -/
theorem span_source_requiredFacts (base width position len : Nat) (memory : Memory)
    (s : Data) (hw : 2 ≤ width) (memoryFit : ∀ value ∈ memory, value < 2 ^ width)
    (fit : s.Fits width) (hwreg : s.regs base = width)
    (hpreg : s.regs (base + 1) = position) (hlreg : s.regs (base + 2) = len)
    (hp : position < 2 ^ width) (hl : len < width) :
    (spanBlock base).Safe memory width s :=
  spanBlock_safe base width position len memory s hw memoryFit fit hwreg hpreg hlreg hp hl

theorem setup_source_requiredFacts (memory : Memory) (width : Nat)
    (hw : 8 ≤ width) (memoryFit : ∀ value ∈ memory, value < 2 ^ width)
    (s : Data) (fit : s.Fits width) : metadataSetupBlock.Safe memory width s :=
  metadataSetupBlock_safe memory width hw memoryFit s fit

/-- The smallest declared width already supports the zero-length path. -/
theorem width_two_zero :
    (spanBlock 0).Safe [] 2 ⟨spanInputRegisters 0 2 3 0, .running⟩ := by
  apply spanBlock_safe 0 2 3 0 [] _ (by decide) (by intro v h; cases h)
    ⟨spanInputRegisters_fit 0 2 3 0 (by decide) (by decide), fun _ h => Status.noConfusion h⟩
    (by simp [spanInputRegisters, Registers.write])
    (by simp [spanInputRegisters, Registers.write])
    (by simp [spanInputRegisters, Registers.write]) (by decide) (by decide)

/-- All-ones crossing uses the actual two replies and produces the maximal
seven-bit result. Its primitive safety proof is the symbolic loader theorem. -/
theorem all_ones_crossing :
    let regs := spanInputRegisters 0 8 7 7
    let actual := spanRun 0 [255, 255] regs
    actual.result = some 127 ∧ actual.reads = [⟨0, some 255⟩, ⟨1, some 255⟩] ∧
    actual.steps ≤ 23 ∧
    (∀ (index : Nat) (t : Transition), actual.transitions[index]? = some t →
      Instruction.Safe 8 t.before t.instruction ∧ t.after.Fits 8) ∧
    (∀ index, index ≤ 23 →
      (run [255, 255] (spanProgram 0) index ⟨regs, 0, .running⟩).final.Fits 8) := by
  have h := spanRun_safe 0 8 7 7 [255, 255] (spanInputRegisters 0 8 7 7) (by decide)
    (by intro v hv; simp at hv; subst v; decide)
    (spanInputRegisters_fit 0 8 7 7 (by decide) (by decide))
    (by simp [spanInputRegisters, Registers.write])
    (by simp [spanInputRegisters, Registers.write])
    (by simp [spanInputRegisters, Registers.write]) (by decide) (by decide) (by decide)
  exact ⟨by simpa [decodeSpanNat] using h.1,
    by simpa [spanAttemptReceipts] using h.2.2.1, h.2.2.2.2.1,
    h.2.2.2.2.2.2⟩

theorem missing_first :
    let regs := spanInputRegisters 0 8 7 7
    let actual := spanRun 0 [] regs
    actual.final.status = .fault ∧ actual.reads = [⟨0, none⟩] ∧
    (∀ (index : Nat) (t : Transition), actual.transitions[index]? = some t →
      Instruction.Safe 8 t.before t.instruction ∧ t.after.Fits 8) ∧
    (∀ index, index ≤ 23 →
      (run [] (spanProgram 0) index ⟨regs, 0, .running⟩).final.Fits 8) := by
  have h := spanRun_safe 0 8 7 7 [] (spanInputRegisters 0 8 7 7) (by decide)
    (by intro v hv; cases hv) (spanInputRegisters_fit 0 8 7 7 (by decide) (by decide))
    (by simp [spanInputRegisters, Registers.write])
    (by simp [spanInputRegisters, Registers.write])
    (by simp [spanInputRegisters, Registers.write]) (by decide) (by decide) (by decide)
  exact ⟨by simpa [decodeSpanNat] using h.2.1,
    by simpa [spanAttemptReceipts] using h.2.2.1, h.2.2.2.2.2.2⟩

theorem missing_second :
    let regs := spanInputRegisters 0 8 7 7
    let actual := spanRun 0 [255] regs
    actual.final.status = .fault ∧ actual.reads = [⟨0, some 255⟩, ⟨1, none⟩] ∧
    (∀ (index : Nat) (t : Transition), actual.transitions[index]? = some t →
      Instruction.Safe 8 t.before t.instruction ∧ t.after.Fits 8) ∧
    (∀ index, index ≤ 23 →
      (run [255] (spanProgram 0) index ⟨regs, 0, .running⟩).final.Fits 8) := by
  have h := spanRun_safe 0 8 7 7 [255] (spanInputRegisters 0 8 7 7) (by decide)
    (by intro v hv; simp at hv; subst v; decide)
    (spanInputRegisters_fit 0 8 7 7 (by decide) (by decide))
    (by simp [spanInputRegisters, Registers.write])
    (by simp [spanInputRegisters, Registers.write])
    (by simp [spanInputRegisters, Registers.write]) (by decide) (by decide) (by decide)
  exact ⟨by simpa [decodeSpanNat] using h.2.1,
    by simpa [spanAttemptReceipts] using h.2.2.1, h.2.2.2.2.2.2⟩

theorem canonical_banks (xs : List Int) (position len : Nat)
    (hp : position < 2 ^ wordWidth xs.length) (hl : len < wordWidth xs.length) :
    (spanRun 8192 (buildMemory xs)
      (spanInputRegisters 8192 (wordWidth xs.length) position len)).final.Fits (wordWidth xs.length) ∧
    (spanRun 8256 (buildMemory xs)
      (spanInputRegisters 8256 (wordWidth xs.length) position len)).final.Fits (wordWidth xs.length) := by
  exact ⟨(spanRun_canonical_safe xs 8192 position len (by decide) hp hl).2.2.2.2.2.1,
    (spanRun_canonical_safe xs 8256 position len (by decide) hp hl).2.2.2.2.2.1⟩

theorem canonical_setup_edges (value : Int) :
    (run (buildMemory []) (metadataSetupBlock.compileAt 0) 348
      ⟨fun _ => 0, 0, .running⟩).final.Fits (wordWidth 0) ∧
    (run (buildMemory [value]) (metadataSetupBlock.compileAt 0) 348
      ⟨fun _ => 0, 0, .running⟩).final.Fits (wordWidth 1) := by
  exact ⟨(buildMemory_setup_run_safe [] ⟨fun _ => 0, 0, .running⟩ rfl rfl
    (by intro r; exact Nat.two_pow_pos _)).2.2.2.2.2.2.2.1,
    (buildMemory_setup_run_safe [value] ⟨fun _ => 0, 0, .running⟩ rfl rfl
    (by intro r; exact Nat.two_pow_pos _)).2.2.2.2.2.2.2.1⟩

/-- The declared capacity belongs to the same canonical memory used by these
runs and retains the already proved logarithmic input-size bound. -/
theorem canonical_width_and_memory (xs : List Int) :
    MemoryWordsFit (buildMemory xs) (wordWidth xs.length) ∧
    (buildMemory xs).length < 2 ^ wordWidth xs.length ∧
    wordWidth xs.length ≤ 192 * (Nat.log2 (xs.length + 2) + 1) :=
  ⟨buildMemory_words_fit xs, buildMemory_length_fit xs, wordWidth_le_log xs.length⟩

theorem canonical_setup_size_installed (xs : List Int) :
    let initial : State := ⟨fun _ => 0, 0, .running⟩
    let actual := run (buildMemory xs) (metadataSetupBlock.compileAt 0) 348 initial
    actual.final.status = .running ∧ actual.final.regs 16 = xs.length ∧
    actual.reads[0]? = some ⟨0, some xs.length⟩ ∧
    (∀ index, index ≤ 348 →
      (run (buildMemory xs) (metadataSetupBlock.compileAt 0) index initial).final.Fits
        (wordWidth xs.length)) := by
  have h := buildMemory_setup_run_safe xs ⟨fun _ => 0, 0, .running⟩ rfl rfl
    (by intro r; exact Nat.two_pow_pos _)
  have hm : (metadata (SuccinctClassic.cartesianShape xs))[0]? = some xs.length := by
    simp [metadata, scalarMetadata, packedReviewerCartesianShape_size]
  refine ⟨h.1, ?_, ?_, h.2.2.2.2.2.2.2.2.2⟩
  · simpa [hm] using h.2.1 0 (by decide)
  · rw [h.2.2.2.2.1]
    simp [hm]

example : (run (buildMemory []) (metadataSetupBlock.compileAt 0) 348
    ⟨fun _ => 0, 0, .running⟩).final.regs 16 = 0 :=
  (canonical_setup_size_installed []).2.1

example (value : Int) : (run (buildMemory [value]) (metadataSetupBlock.compileAt 0) 348
    ⟨fun _ => 0, 0, .running⟩).final.regs 16 = 1 :=
  (canonical_setup_size_installed [value]).2.1

/-- An empty numeric memory faults on the first actual metadata load; safety
still covers the failed address and every later fixed-budget prefix. -/
theorem failed_setup :
    let width := wordWidth 0
    let initial : State := ⟨fun _ => 0, 0, .running⟩
    let actual := run [] (metadataSetupBlock.compileAt 0) 348 initial
    actual.final.status = .fault ∧ actual.reads = [⟨0, none⟩] ∧
    (∀ (index : Nat) (t : Transition), actual.transitions[index]? = some t →
      Instruction.Safe width t.before t.instruction ∧ t.after.Fits width) ∧
    (∀ index, index ≤ 348 →
      (run [] (metadataSetupBlock.compileAt 0) index initial).final.Fits width) := by
  have fit : (⟨fun _ => 0, .running⟩ : Data).Fits (wordWidth 0) :=
    ⟨fun _ => Nat.two_pow_pos _, fun _ h => Status.noConfusion h⟩
  have bound : metadataSetupBlock.size < 2 ^ wordWidth 0 := by
    rw [metadataSetupBlock_size]
    exact Nat.lt_of_lt_of_le (by decide : 348 < 2 ^ 32)
      (Nat.pow_le_pow_right (by decide : 0 < 2) (by unfold wordWidth; omega))
  have hc := metadataSetupBlock.compile_run_safe [] (wordWidth 0)
    ⟨fun _ => 0, 0, .running⟩ rfl (metadataSetupBlock_fieldsFit 0) bound
    ⟨Nat.two_pow_pos _, fit⟩
    (metadataSetupBlock_safe [] (wordWidth 0) (by unfold wordWidth; omega)
      (by intro v h; cases h) _ fit)
  rw [metadataSetupBlock_size] at hc
  have first : (metadataLoadPair 0).eval [] ⟨fun _ => 0, .running⟩ =
      ⟨⟨fun _ => 0, .fault⟩, [⟨0, none⟩]⟩ := by
    simp [metadataLoadPair, Block.eval, Action.eval, Action.instruction,
      execute, State.writeNext, Data.ofState, Registers.write]
    funext r
    simp [Registers.write]
  have source : metadataSetupBlock.eval [] ⟨fun _ => 0, .running⟩ =
      ⟨⟨fun _ => 0, .fault⟩, [⟨0, none⟩]⟩ := by
    change (Block.seq (metadataLoadPair 0) (metadataSetupFrom 1 173)).eval [] _ = _
    rw [Block.eval_seq, first]
    simp only [Evaluation.bind]
    rw [Block.eval_stopped [] _ _ (by decide)]
    rfl
  refine ⟨?_, ?_, hc.2.2.2.2.2⟩
  · have hh := congrArg Data.status hc.1
    simpa [Data.ofState, source] using hh
  · simpa [Data.ofState, source] using hc.2.1

end LoadSafetyConsumers

end RMQ.SuccinctFinal.PackedWordRAM
