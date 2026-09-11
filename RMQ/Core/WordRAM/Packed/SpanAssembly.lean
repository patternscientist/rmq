import RMQ.Core.WordRAM.Packed.Compiler
import RMQ.Core.WordRAM.Packed.Span

/-!
# Fixed scalar assembly for numeric span decoding

Inputs at `base`, `base+1`, `base+2` are width, position and length. The result
is at `base+3`; scratch occupies `base+4` through `base+13`. Source syntax and
its expansion do not depend on runtime geometry or memory. Source arithmetic
uses natural representatives; canonical machine safety additionally uses
`len < wordWidth` so power-of-two masks fit in the machine word.
-/

namespace RMQ.SuccinctFinal.PackedWordRAM

open Structured

/-- At most two actual attempts, stopping if the first lookup fails. -/
def spanAttemptReceipts (width position len : Nat) (memory : Memory) : List Receipt :=
  if len = 0 then []
  else
    let first := memory[position / width]?
    ⟨position / width, first⟩ ::
      match first with
      | none => []
      | some _ => if position % width + len ≤ width then []
          else [⟨position / width + 1, memory[position / width + 1]?⟩]

/-- Fixed scalar source. The crossing arm masks before shifting, so it never
constructs the concatenation of two full-width numeric cells. -/
def spanBlock (base : Nat) : Block :=
  .ifZero (base + 2)
    (.action (.constant (base + 3) 0))
    (Block.sequence [
      .action (.constant (base + 4) 1),
      .action (.arithmetic .div (base + 5) (base + 1) base),
      .action (.arithmetic .mod (base + 6) (base + 1) base),
      .action (.load (base + 3) (base + 5)),
      .action (.arithmetic .shr (base + 3) (base + 3) (base + 6)),
      .action (.arithmetic .add (base + 7) (base + 6) (base + 2)),
      .action (.comparison .le (base + 8) (base + 7) base),
      .ifZero (base + 8)
        (Block.sequence [
          .action (.arithmetic .add (base + 5) (base + 5) (base + 4)),
          .action (.load (base + 10) (base + 5)),
          .action (.arithmetic .sub (base + 11) base (base + 6)),
          .action (.arithmetic .sub (base + 12) (base + 2) (base + 11)),
          .action (.arithmetic .shl (base + 9) (base + 4) (base + 12)),
          .action (.arithmetic .mod (base + 13) (base + 10) (base + 9)),
          .action (.arithmetic .shl (base + 13) (base + 13) (base + 11)),
          .action (.arithmetic .add (base + 3) (base + 3) (base + 13))])
        (Block.sequence [
          .action (.arithmetic .shl (base + 9) (base + 4) (base + 2)),
          .action (.arithmetic .mod (base + 3) (base + 3) (base + 9))])])

@[simp] theorem spanBlock_size (base : Nat) : (spanBlock base).size = 22 := by
  simp [spanBlock, Block.sequence, Block.size]

/-- The source conclusion constrains status and output on the same evaluation.
It is mathematical scalar evaluation, without a word-safety claim. -/
def SpanOutcome (base : Nat) (value : Option Nat) (result : Data) : Prop :=
  match value with
  | none => result.status = .fault
  | some answer => result.status = .running ∧ result.regs (base + 3) = answer

private theorem shiftRight_numeric (a b : Nat) : Nat.shiftRight a b = a / 2 ^ b :=
  Nat.shiftRight_eq_div_pow a b

private theorem shiftLeft_numeric (a b : Nat) : Nat.shiftLeft a b = a * 2 ^ b :=
  Nat.shiftLeft_eq a b

theorem spanBlock_source (base width position len : Nat) (memory : Memory)
    (regs : Registers) (hw : regs base = width) (hp : regs (base + 1) = position)
    (hl : regs (base + 2) = len) :
    SpanOutcome base (decodeSpanNat width position len memory)
      ((spanBlock base).eval memory ⟨regs, .running⟩).final ∧
    ((spanBlock base).eval memory ⟨regs, .running⟩).reads =
      spanAttemptReceipts width position len memory := by
  by_cases hz : len = 0
  · simp [spanBlock, Block.sequence, Block.eval, Action.eval, Action.instruction,
      execute, State.writeNext, Data.ofState, Registers.write, hl, hz,
      decodeSpanNat, SpanOutcome, spanAttemptReceipts]
  · cases hf : memory[position / width]? with
    | none =>
        simp [spanBlock, Block.sequence, Block.eval, Action.eval, Action.instruction,
          execute, State.writeNext, Data.ofState, Registers.write, Arithmetic.eval,
          hw, hp, hl, hz, hf, decodeSpanNat, SpanOutcome, spanAttemptReceipts,
          bind, Option.bind]
    | some first =>
        by_cases hc : position % width + len ≤ width
        · simp [spanBlock, Block.sequence, Block.eval, Action.eval, Action.instruction,
            execute, State.writeNext, Data.ofState, Registers.write, Arithmetic.eval,
            Comparison.eval, hw, hp, hl, hz, hf, hc, decodeSpanNat, SpanOutcome,
            spanAttemptReceipts, bind, Option.bind, shiftRight_numeric,
            shiftLeft_numeric]
        · cases hs : memory[position / width + 1]? <;>
            simp [spanBlock, Block.sequence, Block.eval, Action.eval, Action.instruction,
              execute, State.writeNext, Data.ofState, Registers.write, Arithmetic.eval,
              Comparison.eval, hw, hp, hl, hz, hf, hc, hs, decodeSpanNat, SpanOutcome,
              spanAttemptReceipts, bind, Option.bind, shiftRight_numeric,
              shiftLeft_numeric]

theorem spanBlock_source_some (base width position len : Nat) (memory : Memory)
    (regs : Registers) (hw : regs base = width) (hp : regs (base + 1) = position)
    (hl : regs (base + 2) = len) (value : Nat)
    (hvalue : decodeSpanNat width position len memory = some value) :
    ((spanBlock base).eval memory ⟨regs, .running⟩).final.status = .running ∧
      ((spanBlock base).eval memory ⟨regs, .running⟩).final.regs (base + 3) = value := by
  simpa [SpanOutcome, hvalue] using (spanBlock_source base width position len memory regs hw hp hl).1

theorem spanBlock_source_none (base width position len : Nat) (memory : Memory)
    (regs : Registers) (hw : regs base = width) (hp : regs (base + 1) = position)
    (hl : regs (base + 2) = len)
    (hvalue : decodeSpanNat width position len memory = none) :
    ((spanBlock base).eval memory ⟨regs, .running⟩).final.status = .fault := by
  simpa [SpanOutcome, hvalue] using (spanBlock_source base width position len memory regs hw hp hl).1

theorem spanAttemptReceipts_length_le (width position len : Nat) (memory : Memory) :
    (spanAttemptReceipts width position len memory).length ≤ 2 := by
  by_cases hz : len = 0
  · simp [spanAttemptReceipts, hz]
  · cases hf : memory[position / width]? <;>
      by_cases hc : position % width + len ≤ width <;>
      simp [spanAttemptReceipts, hz, hf, hc]

/-- Every attempted occurrence retains its reply from this numeric memory. -/
theorem spanAttemptReceipts_backing (width position len : Nat) (memory : Memory)
    (occurrence : Nat) (receipt : Receipt)
    (h : (spanAttemptReceipts width position len memory)[occurrence]? = some receipt) :
    receipt.reply = memory[receipt.address]? := by
  have hm : receipt ∈ spanAttemptReceipts width position len memory :=
    List.mem_of_getElem? h
  by_cases hz : len = 0
  · simp [spanAttemptReceipts, hz] at hm
  · cases hf : memory[position / width]? with
    | none =>
      simp [spanAttemptReceipts, hz, hf] at hm
      subst receipt
      exact hf.symm
    | some first =>
      by_cases hc : position % width + len ≤ width
      · simp [spanAttemptReceipts, hz, hf, hc] at hm
        subst receipt
        exact hf.symm
      · simp [spanAttemptReceipts, hz, hf, hc] at hm
        rcases hm with rfl | rfl
        · exact hf.symm
        · rfl

/-- Inputs and every register outside output/scratch are preserved, including
on faults. This is stronger than the requested outside-[base,base+14) frame. -/
theorem spanBlock_frame (base : Nat) (memory : Memory) (regs : Registers)
    (r : Nat) (hr : r < base + 3 ∨ base + 14 ≤ r) :
    ((spanBlock base).eval memory ⟨regs, .running⟩).final.regs r = regs r := by
  have h3 : r ≠ base + 3 := by omega
  have h4 : r ≠ base + 4 := by omega
  have h5 : r ≠ base + 5 := by omega
  have h6 : r ≠ base + 6 := by omega
  have h7 : r ≠ base + 7 := by omega
  have h8 : r ≠ base + 8 := by omega
  have h9 : r ≠ base + 9 := by omega
  have h10 : r ≠ base + 10 := by omega
  have h11 : r ≠ base + 11 := by omega
  have h12 : r ≠ base + 12 := by omega
  have h13 : r ≠ base + 13 := by omega
  by_cases hz : regs (base + 2) = 0
  · simp [spanBlock, Block.sequence, Block.eval, Action.eval, Action.instruction,
      execute, State.writeNext, Data.ofState, Registers.write, hz, h3]
  · cases hf : memory[regs (base + 1) / regs base]? with
    | none =>
        simp [spanBlock, Block.sequence, Block.eval, Action.eval, Action.instruction,
          execute, State.writeNext, Data.ofState, Registers.write, Arithmetic.eval,
          hz, hf, h4, h5, h6]
    | some first =>
        by_cases hc : regs (base + 1) % regs base + regs (base + 2) ≤ regs base
        · simp [spanBlock, Block.sequence, Block.eval, Action.eval, Action.instruction,
            execute, State.writeNext, Data.ofState, Registers.write, Arithmetic.eval,
            Comparison.eval, hz, hf, hc, h3, h4, h5, h6, h7, h8, h9]
        · cases hs : memory[regs (base + 1) / regs base + 1]? <;>
            simp [spanBlock, Block.sequence, Block.eval, Action.eval, Action.instruction,
              execute, State.writeNext, Data.ofState, Registers.write, Arithmetic.eval,
              Comparison.eval, hz, hf, hc, hs, h3, h4, h5, h6, h7, h8, h9,
              h10, h11, h12, h13]

/-- Literal instruction inventory; offsets include both dormant arms and the
end-of-block jump target. Runtime geometry never specializes this program. -/
theorem spanBlock_compilation (base pc : Nat) :
    (spanBlock base).compileAt pc = [
      .branchZero (base + 2) (pc + 21),
      .constant (base + 4) 1,
      .arithmetic .div (base + 5) (base + 1) base,
      .arithmetic .mod (base + 6) (base + 1) base,
      .load (base + 3) (base + 5),
      .arithmetic .shr (base + 3) (base + 3) (base + 6),
      .arithmetic .add (base + 7) (base + 6) (base + 2),
      .comparison .le (base + 8) (base + 7) base,
      .branchZero (base + 8) (pc + 12),
      .arithmetic .shl (base + 9) (base + 4) (base + 2),
      .arithmetic .mod (base + 3) (base + 3) (base + 9),
      .jump (pc + 20),
      .arithmetic .add (base + 5) (base + 5) (base + 4),
      .load (base + 10) (base + 5),
      .arithmetic .sub (base + 11) base (base + 6),
      .arithmetic .sub (base + 12) (base + 2) (base + 11),
      .arithmetic .shl (base + 9) (base + 4) (base + 12),
      .arithmetic .mod (base + 13) (base + 10) (base + 9),
      .arithmetic .shl (base + 13) (base + 13) (base + 11),
      .arithmetic .add (base + 3) (base + 3) (base + 13),
      .jump (pc + 22),
      .constant (base + 3) 0] := by
  simp [spanBlock, Block.sequence, Block.compileAt, Block.size,
    Action.instruction, Nat.add_assoc]

/-- Register identifiers, separately from scalar constants and control PCs. -/
def spanInstructionRegisters : Instruction → List Nat
  | .load dst address => [dst, address]
  | .constant dst _ => [dst]
  | .move dst src => [dst, src]
  | .arithmetic _ dst lhs rhs | .comparison _ dst lhs rhs => [dst, lhs, rhs]
  | .jump _ => []
  | .jumpRegister src | .halt src => [src]
  | .branchZero condition _ => [condition]

/-- Every encoded field and static register ID is bounded, including dormant
branches. The bound on encoded fields also covers scalar and opcode tags. -/
theorem spanBlock_static_fields (base pc : Nat) :
    ∀ instruction ∈ (spanBlock base).compileAt pc,
      (∀ operand ∈ instruction.encoding, operand ≤ base + pc + 22) ∧
      (∀ register ∈ spanInstructionRegisters instruction,
        base ≤ register ∧ register < base + 14) := by
  intro instruction hi
  rw [spanBlock_compilation] at hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals constructor <;> intro field hf
  all_goals simp only [Instruction.encoding, Instruction.operands, Arithmetic.code, Comparison.code,
      spanInstructionRegisters, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hf
  all_goals omega

/-- A terminal wrapper supplies a usual machine result without changing the
numeric decoder. Its fixed expansion adds exactly one halt instruction. -/
def spanRoutine (base : Nat) : Block := .seq (spanBlock base) (.exit (base + 3))

@[simp] theorem spanRoutine_size (base : Nat) : (spanRoutine base).size = 23 := by
  simp [spanRoutine, Block.size]

def spanProgram (base : Nat) : Program := (spanRoutine base).compileAt 0

@[simp] theorem spanProgram_length (base : Nat) : (spanProgram base).length = 23 := by
  simp [spanProgram]

theorem spanProgram_static_fields (base : Nat) :
    ∀ instruction ∈ spanProgram base,
      (∀ operand ∈ instruction.encoding, operand ≤ base + 23) ∧
      (∀ register ∈ spanInstructionRegisters instruction,
        base ≤ register ∧ register < base + 14) := by
  intro instruction hi
  change instruction ∈ (spanBlock base).compileAt 0 ++ [.halt (base + 3)] at hi
  rcases List.mem_append.mp hi with hi | hi
  · have h := spanBlock_static_fields base 0 instruction hi
    refine ⟨?_, h.2⟩
    intro operand ho
    have hb := h.1 operand ho
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    subst instruction
    constructor <;> intro field hf <;>
      simp only [Instruction.encoding, Instruction.operands, spanInstructionRegisters,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hf <;> omega

def spanRun (base : Nat) (memory : Memory) (regs : Registers) : Run :=
  run memory (spanProgram base) 23 ⟨regs, 0, .running⟩

def spanInputRegisters (base width position len : Nat) : Registers :=
  Registers.write (Registers.write (Registers.write (fun _ => 0) base width)
    (base + 1) position) (base + 2) len

private theorem execute_frame_of_registers (memory : Memory) (instruction : Instruction)
    (s : State) (r : Nat)
    (h : ∀ register ∈ spanInstructionRegisters instruction, register ≠ r) :
    (execute memory instruction s).1.regs r = s.regs r := by
  cases instruction <;>
    simp_all [spanInstructionRegisters, execute, State.writeNext, Registers.write, eq_comm]
  split <;> simp_all [Registers.write, eq_comm]

private theorem run_frame_of_registers (memory : Memory) (program : Program)
    (fuel : Nat) (s : State) (r : Nat)
    (h : ∀ instruction ∈ program,
      ∀ register ∈ spanInstructionRegisters instruction, register ≠ r) :
    (run memory program fuel s).final.regs r = s.regs r := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
      cases hs : step memory program s with
      | none => simp [run, hs]
      | some t =>
          have spec := step_spec hs
          have hf := execute_frame_of_registers memory t.instruction s r
            (h t.instruction (List.mem_of_getElem? spec.2.2.1))
          rw [spec.2.2.2] at hf
          simpa only [run, hs] using (ih t.after).trans hf

/-- The outside-register frame holds at every actual primitive prefix, not
only after the final source evaluation. No bound on the prefix fuel is needed. -/
theorem spanRun_prefix_frame (base : Nat) (memory : Memory) (regs : Registers)
    (fuel r : Nat) (hr : r < base ∨ base + 14 ≤ r) :
    (run memory (spanProgram base) fuel ⟨regs, 0, .running⟩).final.regs r = regs r := by
  apply run_frame_of_registers
  intro instruction hi register hregister
  have hb := (spanProgram_static_fields base instruction hi).2 register hregister
  omega

private theorem seq_exit_projections (memory : Memory) (block : Block)
    (regs : Registers) (out : Nat) :
    ((Block.seq block (.exit out)).eval memory ⟨regs, .running⟩).final.regs =
        (block.eval memory ⟨regs, .running⟩).final.regs ∧
    ((Block.seq block (.exit out)).eval memory ⟨regs, .running⟩).reads =
        (block.eval memory ⟨regs, .running⟩).reads ∧
    ((Block.seq block (.exit out)).eval memory ⟨regs, .running⟩).final.status =
      match (block.eval memory ⟨regs, .running⟩).final.status with
      | .running => .halted ((block.eval memory ⟨regs, .running⟩).final.regs out)
      | status => status := by
  cases he : block.eval memory ⟨regs, .running⟩ with
  | mk final reads =>
      cases final with
      | mk finalRegs status =>
          cases status <;> simp [Block.eval, he]

/-- The terminal source wrapper exposes an ordinary result status while
retaining the same output, frame and ordered numeric attempts. -/
theorem spanRoutine_source (base width position len : Nat) (memory : Memory)
    (regs : Registers) (hw : regs base = width) (hp : regs (base + 1) = position)
    (hl : regs (base + 2) = len) :
    ((spanRoutine base).eval memory ⟨regs, .running⟩).final.status =
      (match decodeSpanNat width position len memory with
      | none => .fault
      | some value => .halted value) ∧
    ((spanRoutine base).eval memory ⟨regs, .running⟩).reads =
      spanAttemptReceipts width position len memory ∧
    (∀ r, r < base + 3 ∨ base + 14 ≤ r →
      ((spanRoutine base).eval memory ⟨regs, .running⟩).final.regs r = regs r) := by
  have hsource := spanBlock_source base width position len memory regs hw hp hl
  have hexit := seq_exit_projections memory (spanBlock base) regs (base + 3)
  change _ ∧ _ ∧ _
  refine ⟨?_, ?_, ?_⟩
  · change ((Block.seq (spanBlock base) (.exit (base + 3))).eval memory
      ⟨regs, .running⟩).final.status = _
    rw [hexit.2.2]
    cases hd : decodeSpanNat width position len memory with
    | none =>
        have hf := hsource.1
        simp only [SpanOutcome, hd] at hf
        simp [hf]
    | some value =>
        have hs := hsource.1
        simp only [SpanOutcome, hd] at hs
        simp [hs.1, hs.2]
  · exact hexit.2.1.trans hsource.2
  · intro r hr
    exact (congrArg (fun rs : Registers => rs r) hexit.1).trans
      (spanBlock_frame base memory regs r hr)

/-- A source block embedded at any program position is realized by an exact
primitive segment of at most 22 instructions. The same run supplies output,
status, ordered attempts, the register frame and the continuation PC. -/
theorem spanBlock_machine (base codeStart width position len : Nat)
    (memory : Memory) (program : Program) (regs : Registers)
    (hw : regs base = width) (hp : regs (base + 1) = position)
    (hl : regs (base + 2) = len)
    (host : HostedAt program codeStart ((spanBlock base).compileAt codeStart)) :
    ∃ used, used ≤ 22 ∧
      let actual := run memory program used ⟨regs, codeStart, .running⟩
      SpanOutcome base (decodeSpanNat width position len memory) (Data.ofState actual.final) ∧
      actual.reads = spanAttemptReceipts width position len memory ∧
      (∀ r, r < base + 3 ∨ base + 14 ≤ r → actual.final.regs r = regs r) ∧
      actual.steps = used ∧
      (actual.final.status = .running → actual.final.pc = codeStart + 22) := by
  obtain ⟨used, hbound, hd, hreads, hsteps, hpc⟩ :=
    (spanBlock base).compile_correct memory program codeStart
      ⟨regs, codeStart, .running⟩ rfl host
  have hsource := spanBlock_source base width position len memory regs hw hp hl
  refine ⟨used, by simpa using hbound, ?_⟩
  dsimp only
  refine ⟨?_, hreads.trans hsource.2, ?_, hsteps, ?_⟩
  · rw [hd]
    exact hsource.1
  · intro r hr
    exact (congrArg (fun d : Data => d.regs r) hd).trans (spanBlock_frame base memory regs r hr)
  · simpa using hpc

/-- Fixed-budget adequacy for the ordinary result-producing machine routine.
No successful-read, source-result or fuel-adequacy premise is supplied. -/
theorem spanRun_correct (base width position len : Nat) (memory : Memory)
    (regs : Registers) (hw : regs base = width) (hp : regs (base + 1) = position)
    (hl : regs (base + 2) = len) :
    (spanRun base memory regs).result = decodeSpanNat width position len memory ∧
    (spanRun base memory regs).final.status =
      (match decodeSpanNat width position len memory with
      | none => .fault
      | some value => .halted value) ∧
    (spanRun base memory regs).reads = spanAttemptReceipts width position len memory ∧
    (∀ r, r < base + 3 ∨ base + 14 ≤ r →
      (spanRun base memory regs).final.regs r = regs r) ∧
    (spanRun base memory regs).steps ≤ 23 := by
  have hc := (spanRoutine base).compile_run memory ⟨regs, 0, .running⟩ rfl
  have hd : Data.ofState (spanRun base memory regs).final =
      ((spanRoutine base).eval memory ⟨regs, .running⟩).final := by
    simpa only [spanRun, spanProgram, spanRoutine_size, Data.ofState] using hc.1
  have hsource := spanRoutine_source base width position len memory regs hw hp hl
  have hstatus := (congrArg Data.status hd).trans hsource.1
  refine ⟨?_, hstatus, ?_, ?_, ?_⟩
  · unfold Run.result
    rw [show (spanRun base memory regs).final.status = _ from hstatus]
    cases decodeSpanNat width position len memory <;> rfl
  · have hreads : (spanRun base memory regs).reads =
        ((spanRoutine base).eval memory ⟨regs, .running⟩).reads := by
      simpa only [spanRun, spanProgram, spanRoutine_size, Data.ofState] using hc.2.1
    exact hreads.trans hsource.2.1
  · intro r hr
    exact (congrArg (fun d : Data => d.regs r) hd).trans (hsource.2.2 r hr)
  · simpa only [spanRun, spanProgram, spanRoutine_size] using hc.2.2.1

/-- Canonical numeric register initialization discharges the source input
contract, so the machine result theorem has no semantic premises. -/
theorem spanRun_inputs (base width position len : Nat) (memory : Memory) :
    (spanRun base memory (spanInputRegisters base width position len)).result =
        decodeSpanNat width position len memory ∧
    (spanRun base memory (spanInputRegisters base width position len)).reads =
        spanAttemptReceipts width position len memory ∧
    (spanRun base memory (spanInputRegisters base width position len)).steps ≤ 23 := by
  have h := spanRun_correct base width position len memory
    (spanInputRegisters base width position len)
    (by simp [spanInputRegisters, Registers.write])
    (by simp [spanInputRegisters, Registers.write])
    (by simp [spanInputRegisters, Registers.write])
  exact ⟨h.1, h.2.2.1, h.2.2.2.2⟩

/-- The categories partition every step of the same fixed-budget run. -/
theorem spanRun_steps_partition (base : Nat) (memory : Memory) (regs : Registers) :
    (spanRun base memory regs).steps =
      (spanRun base memory regs).categoryCount .memoryRead +
      (spanRun base memory regs).categoryCount .registerWrite +
      (spanRun base memory regs).categoryCount .arithmetic +
      (spanRun base memory regs).categoryCount .comparison +
      (spanRun base memory regs).categoryCount .branch +
      (spanRun base memory regs).categoryCount .control :=
  Run.steps_partition _

/-- An actual primitive read occurrence retains its pre-state, instruction,
evaluated address and reply in this routine's one numeric memory. -/
theorem spanRun_read_at (base : Nat) (memory : Memory) (regs : Registers)
    (k : Nat) (t : Transition) (receipt : Receipt)
    (ht : (spanRun base memory regs).transitions[k]? = some t)
    (hr : t.receipt = some receipt) :
    t.before = (run memory (spanProgram base) k ⟨regs, 0, .running⟩).final ∧
    t.before.status = .running ∧
    (spanProgram base)[t.before.pc]? = some t.instruction ∧
    execute memory t.instruction t.before = (t.after, t.receipt) ∧
    ∃ dst addrReg, t.instruction = .load dst addrReg ∧
      receipt.address = t.before.regs addrReg ∧ receipt.reply = memory[receipt.address]? :=
  run_read_at ht hr

namespace SpanCompiledExamples

example :
    (spanRun 0 [] (spanInputRegisters 0 4 0 0)).result = some 0 ∧
    (spanRun 0 [] (spanInputRegisters 0 4 0 0)).reads = [] ∧
    (spanRun 0 [] (spanInputRegisters 0 4 0 0)).steps = 3 := by decide

example :
    (spanRun 0 [13] (spanInputRegisters 0 4 1 2)).result = some 2 ∧
    (spanRun 0 [13] (spanInputRegisters 0 4 1 2)).reads = [⟨0, some 13⟩] ∧
    (spanRun 0 [13] (spanInputRegisters 0 4 1 2)).steps = 14 := by decide

example :
    (spanRun 0 [13, 3] (spanInputRegisters 0 4 3 3)).result = some 7 ∧
    (spanRun 0 [13, 3] (spanInputRegisters 0 4 3 3)).reads =
      [⟨0, some 13⟩, ⟨1, some 3⟩] ∧
    (spanRun 0 [13, 3] (spanInputRegisters 0 4 3 3)).steps = 19 := by decide

example :
    (spanRun 0 [] (spanInputRegisters 0 4 3 3)).final.status = .fault ∧
    (spanRun 0 [] (spanInputRegisters 0 4 3 3)).reads = [⟨0, none⟩] ∧
    (spanRun 0 [] (spanInputRegisters 0 4 3 3)).steps = 5 := by decide

example :
    (spanRun 0 [13] (spanInputRegisters 0 4 3 3)).final.status = .fault ∧
    (spanRun 0 [13] (spanInputRegisters 0 4 3 3)).reads =
      [⟨0, some 13⟩, ⟨1, none⟩] ∧
    (spanRun 0 [13] (spanInputRegisters 0 4 3 3)).steps = 11 := by decide

example :
    (spanRun 0 [15] (spanInputRegisters 0 4 0 4)).result = some 15 ∧
    (spanRun 0 [15] (spanInputRegisters 0 4 0 4)).reads = [⟨0, some 15⟩] ∧
    (spanRun 0 [15] (spanInputRegisters 0 4 0 4)).steps = 14 := by decide

theorem returnedValue_dependency :
    (spanRun 0 [13, 3] (spanInputRegisters 0 4 3 3)).result ≠
      (spanRun 0 [5, 3] (spanInputRegisters 0 4 3 3)).result ∧
    (spanRun 0 [13, 3] (spanInputRegisters 0 4 3 3)).result ≠
      (spanRun 0 [13, 2] (spanInputRegisters 0 4 3 3)).result := by decide

end SpanCompiledExamples

end RMQ.SuccinctFinal.PackedWordRAM
