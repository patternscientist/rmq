import RMQ.Core.WordRAM.Construction.Loop
import RMQ.Core.WordRAM.Construction.ArrayRun
import RMQ.Core.WordRAM.Construction.HeaderUse import Lean import RMQ.Core.WordRAM.Construction.Proof.Constants import RMQ.Core.WordRAM.Packed.Allocation

/-! Independent exact-type consumers of the PRE-1 Stage 0 operational
foundations: the fetch-and-step interpreter calculus, the single safety
judgment, the structured compiler theorem, the loop rules, the array-backed
evaluator abstraction and the `HeaderUse` certificate. Every type below is
written out in full and does not adapt to producer edits. Tiny toy programs are
pinned on the mathematical run by `decide`; machine validation of real runs is
the array-backed executable, never kernel evaluation. -/

namespace PRE1BuilderConsumer
open RMQ.SuccinctFinal.PackedConstruction
open RMQ.SuccinctFinal.PackedConstruction.Structured

/-! ## HeaderUse certificate fields (AMEND-1) -/

theorem hu_headerFirst : ∀ (program : List BInstr), HeaderUse program →
    program[0]? = some headerInstruction := fun _ h => h.headerFirst
theorem hu_tailNeverWritesR1 : ∀ (program : List BInstr), HeaderUse program →
    ∀ i ∈ program.tail, WritesOnly (fun r => r ≠ 1) i := fun _ h => h.tailNeverWritesR1
theorem hu_wordMissingHeaderFault : ∀ (program : List BInstr), HeaderUse program →
    ∀ (width : Nat) (xs : List Int) (fuel : Nat), 1 ≤ fuel →
    (run program fuel
      { wordInputState width xs with memory := put (encodeInput width xs) 0 none }).final.status =
        .fault ∧
    (run program fuel
      { wordInputState width xs with memory := put (encodeInput width xs) 0 none }).steps = 1 ∧
    (run program fuel
      { wordInputState width xs with memory := put (encodeInput width xs) 0 none }).writes = [] ∧
    (run program fuel
      { wordInputState width xs with memory := put (encodeInput width xs) 0 none }).reserves = [] ∧
    (run program fuel
      { wordInputState width xs with memory := put (encodeInput width xs) 0 none }).final.extent =
        (wordInputState width xs).extent := fun _ h => h.wordMissingHeaderFault
theorem hu_comparisonMissingHeaderFault : ∀ (program : List BInstr), HeaderUse program →
    ∀ (xs : List Int) (fuel : Nat), 1 ≤ fuel →
    (run program fuel
      { comparisonInputState xs with
        memory := put (comparisonInputState xs).memory 0 none }).final.status = .fault ∧
    (run program fuel
      { comparisonInputState xs with
        memory := put (comparisonInputState xs).memory 0 none }).steps = 1 ∧
    (run program fuel
      { comparisonInputState xs with
        memory := put (comparisonInputState xs).memory 0 none }).writes = [] ∧
    (run program fuel
      { comparisonInputState xs with
        memory := put (comparisonInputState xs).memory 0 none }).reserves = [] ∧
    (run program fuel
      { comparisonInputState xs with
        memory := put (comparisonInputState xs).memory 0 none }).final.extent =
        (comparisonInputState xs).extent := fun _ h => h.comparisonMissingHeaderFault
theorem hu_wordHeaderReceipt : ∀ (program : List BInstr), HeaderUse program →
    ∀ (width : Nat) (xs : List Int) (fuel : Nat), 1 ≤ fuel →
    ∃ t : Transition, (run program fuel (wordInputState width xs)).transitions[0]? = some t ∧
      t.instruction = headerInstruction ∧ t.before.regs 1 = 0 ∧
      t.after.regs 1 = xs.length ∧ t.after.status = .running := fun _ h => h.wordHeaderReceipt
theorem hu_comparisonHeaderReceipt : ∀ (program : List BInstr), HeaderUse program →
    ∀ (xs : List Int) (fuel : Nat), 1 ≤ fuel →
    ∃ t : Transition, (run program fuel (comparisonInputState xs)).transitions[0]? = some t ∧
      t.instruction = headerInstruction ∧ t.before.regs 1 = 0 ∧
      t.after.regs 1 = xs.length ∧ t.after.status = .running := fun _ h => h.comparisonHeaderReceipt
theorem hu_oracleExtentOne : ∀ (program : List BInstr), HeaderUse program →
    ∀ xs : List Int, (comparisonInputState xs).extent = 1 := fun _ h => h.oracleExtentOne
theorem hu_of_program : ∀ (program : List BInstr), program[0]? = some headerInstruction →
    (∀ i ∈ program.tail, WritesOnly (fun r => r ≠ 1) i) → HeaderUse program :=
  headerUse_of_program

/-! ## Toy program: header load, one reservation, one store, halt -/

def toyProgram : List BInstr := [⟨.load 1 0⟩, ⟨.reserve 2⟩, ⟨.store 2 1⟩, ⟨.halt 1⟩]

theorem toy_headerUse : HeaderUse toyProgram := headerUse_of_program _ rfl (by decide)

theorem toy_run :
    (run toyProgram 4 (wordInputState 40 [3])).steps = 4 ∧
    (run toyProgram 4 (wordInputState 40 [3])).categories =
      [.read, .allocation, .write, .control] ∧
    (run toyProgram 4 (wordInputState 40 [3])).final.extent = 3 ∧
    (run toyProgram 4 (wordInputState 40 [3])).writes = [(2, 1)] ∧
    (run toyProgram 4 (wordInputState 40 [3])).reserves = [2] ∧
    (run toyProgram 4 (wordInputState 40 [3])).result = some 1 := by decide

theorem toy_missing_header :
    (run toyProgram 4
      { wordInputState 40 [3] with memory := put (encodeInput 40 [3]) 0 none }).final.status =
        .fault ∧
    (run toyProgram 4
      { wordInputState 40 [3] with memory := put (encodeInput 40 [3]) 0 none }).steps = 1 := by
  decide

/-! ## Execution calculus at full types -/

theorem calc_write_at : ∀ {program : List BInstr} {fuel : Nat} {s : State} {k : Nat}
    {t : Transition} {address value : Operand},
    (run program fuel s).transitions[k]? = some t →
    t.instruction.primitive = .store address value →
    t.before = (run program k s).final ∧ t.before.status = .running ∧
      program[t.before.pc]? = some t.instruction ∧
      (t.before.regs address < t.before.extent →
        t.after.memory (t.before.regs address) = some (t.before.regs value) ∧
        t.after.status = .running ∧ t.after.extent = t.before.extent ∧
        t.write? = some (t.before.regs address, t.before.regs value)) ∧
      (¬ t.before.regs address < t.before.extent →
        t.after.status = .fault ∧ t.after.memory = t.before.memory ∧ t.write? = none) :=
  @run_write_at

theorem calc_load_at : ∀ {program : List BInstr} {fuel : Nat} {s : State} {k : Nat}
    {t : Transition} {dst address : Operand},
    (run program fuel s).transitions[k]? = some t →
    t.instruction.primitive = .load dst address →
    t.before = (run program k s).final ∧ t.before.status = .running ∧
      program[t.before.pc]? = some t.instruction ∧
      t.load? = some (t.before.regs address) ∧
      (∀ v, t.before.regs address < t.before.extent →
        t.before.memory (t.before.regs address) = some v →
        t.after.regs dst = v ∧ t.after.status = .running ∧ t.after.memory = t.before.memory) ∧
      (t.after.status = .running →
        t.before.regs address < t.before.extent ∧
        ∃ v, t.before.memory (t.before.regs address) = some v ∧ t.after.regs dst = v) :=
  @run_load_at

theorem calc_writes_replay : ∀ (program : List BInstr) (fuel : Nat) (s : State),
    (run program fuel s).final.memory =
      (run program fuel s).writes.foldl (fun m e => put m e.1 (some e.2)) s.memory :=
  writes_replay

theorem calc_frame : ∀ (program : List BInstr) (fuel : Nat) (s : State) (allowed : Nat → Prop),
    (∀ i ∈ program, WritesOnly allowed i) → ∀ r, ¬ allowed r →
    (run program fuel s).final.regs r = s.regs r := run_frame

theorem calc_partition : ∀ r : Run,
    r.steps = r.categoryCount .read + r.categoryCount .register + r.categoryCount .arithmetic +
      r.categoryCount .comparison + r.categoryCount .branch + r.categoryCount .control +
      r.categoryCount .write + r.categoryCount .allocation + r.categoryCount .keyRead +
      r.categoryCount .oracleComparison := Run.steps_partition

theorem calc_fuel_extension : ∀ {program : List BInstr} {s s' : State} {ts : List Transition},
    RunsTo program s s' ts → s'.status ≠ .running → ∀ extra : Nat,
    run program (ts.length + extra) s = ⟨s', ts⟩ := @RunsTo.fuel_extension

theorem calc_extent_mono : ∀ (program : List BInstr) (fuel : Nat) (s : State),
    s.extent ≤ (run program fuel s).final.extent := run_extent_mono

theorem calc_cleanTail : ∀ (program : List BInstr) (fuel : Nat) (s : State),
    CleanTail s → CleanTail (run program fuel s).final := run_cleanTail

theorem calc_agree_of_reads : ∀ (program : List BInstr) (fuel : Nat) (s s' : State),
    State.Agree s s' →
    (∀ a ∈ (run program fuel s).loads, s'.memory a = s.memory a) →
    (∀ i ∈ (run program fuel s).keyReads, s'.keys i = s.keys i) →
    Run.Agree (run program fuel s) (run program fuel s') := run_agree_of_reads

theorem calc_agree_of_supplied : ∀ (program : List BInstr) (fuel : Nat) (s s' : State),
    State.Agree s s' → CleanTail s → CleanTail s' →
    (∀ a, a < s.extent → s'.memory a = s.memory a) →
    (∀ i ∈ (run program fuel s).keyReads, s'.keys i = s.keys i) →
    s'.memory = s.memory ∧ Run.Agree (run program fuel s) (run program fuel s') :=
  run_agree_of_supplied

theorem calc_agree_projections : ∀ {r r' : Run}, Run.Agree r r' →
    r.steps = r'.steps ∧ r.categories = r'.categories ∧ r.writes = r'.writes ∧
      r.reserves = r'.reserves ∧ r.result = r'.result :=
  fun h => ⟨h.steps, h.categories, h.writes, h.reserves, h.result⟩

theorem calc_missing_header : ∀ (program : List BInstr),
    program[0]? = some headerInstruction → ∀ (s : State), s.pc = 0 → s.status = .running →
    s.regs 0 = 0 → s.memory 0 = none → ∀ (fuel : Nat), 1 ≤ fuel →
    (run program fuel s).final.status = .fault ∧ (run program fuel s).steps = 1 ∧
      (run program fuel s).writes = [] ∧ (run program fuel s).reserves = [] ∧
      (run program fuel s).final.extent = s.extent := run_missing_header

theorem calc_header_first : ∀ (program : List BInstr),
    program[0]? = some headerInstruction → ∀ (s : State), s.pc = 0 → s.status = .running →
    s.regs 0 = 0 → ∀ (n : Nat), s.memory 0 = some n → 0 < s.extent → ∀ (fuel : Nat), 1 ≤ fuel →
    ∃ t, (run program fuel s).transitions[0]? = some t ∧ t.instruction = headerInstruction ∧
      t.before = s ∧ t.after.regs 1 = n ∧ t.after.status = .running ∧
      t.after.memory = s.memory ∧ t.after.extent = s.extent := run_header_first

/-! ## The single safety judgment (R1) -/

theorem safety_not_fault : ∀ {W len : Nat} {s : State} {p : Prim},
    Prim.Safe W len s p → s.status ≠ .fault → (execPrim p s).status ≠ .fault :=
  @Prim.safe_not_fault

theorem safety_fits : ∀ {W len : Nat} {s : State} {p : Prim},
    s.Fits W → Prim.Safe W len s p → s.pc < len → len < 2 ^ W → (execPrim p s).Fits W :=
  @Prim.safe_fits

theorem safety_run_of_transitions : ∀ (program : List BInstr) (W : Nat),
    program.length < 2 ^ W → ∀ (fuel : Nat) (s : State), s.Fits W →
    (∀ t ∈ (run program fuel s).transitions,
      Prim.Safe W program.length t.before t.instruction.primitive) →
    Run.Safe W program (run program fuel s) := Run.Safe.of_transitions

theorem safety_run_not_fault : ∀ {W : Nat} {program : List BInstr} {fuel : Nat} {s : State},
    Run.Safe W program (run program fuel s) → s.status ≠ .fault →
    (run program fuel s).final.status ≠ .fault := @Run.Safe.not_fault

theorem safety_definition : ∀ (W len : Nat) (s : State) (p : Prim),
    Prim.Safe W len s p ↔ ((∀ c ∈ p.constants, c.val < 2 ^ W) ∧ Prim.SafeAt W len s p) :=
  fun _ _ _ _ => Iff.rfl

theorem safety_jumpRegister_rejected : ∀ (W len : Nat) (s : State) (src : Operand),
    ¬ Prim.Safe W len s (.jumpRegister src) := fun _ _ _ _ h => h.2

/-! ## Structured compilation (exact cost, pc-agreement, safety) -/

theorem compiler_realizes : ∀ {P : State → Action → Prop},
    (∀ (s : State) (q : Nat) (op : Action), P s op → P { s with pc := q } op) →
    ∀ (program : List BInstr) {b : Block} {s s' : State} {k : Nat}, EvalG P b s s' k →
    ∀ (base : Nat), HostedAt program base (b.compileAt base) → base + b.size < 2 ^ 32 →
    ∃ s'' ts, RunsTo program { s with pc := base } s'' ts ∧ ts.length = k ∧
      s'' = { s' with pc := s''.pc } ∧ (s''.status = .running → s''.pc = base + b.size) :=
  fun hP program _ _ _ _ h base host bound =>
    EvalG.compile_realizes' hP program h base host bound

theorem compiler_safe : ∀ {W : Nat}, 32 ≤ W → ∀ (program : List BInstr),
    program.length < 2 ^ W → ∀ {b : Block} {s s' : State} {k : Nat}, SafeEval W b s s' k →
    ∀ (base : Nat), HostedAt program base (b.compileAt base) → base + b.size < 2 ^ 32 →
    base + b.size < program.length → ({ s with pc := base } : State).Fits W →
    ∃ s'' ts, RunsTo program { s with pc := base } s'' ts ∧ ts.length = k ∧
      s'' = { s' with pc := s''.pc } ∧ (s''.status = .running → s''.pc = base + b.size) ∧
      Run.Safe W program (run program ts.length { s with pc := base }) ∧ s''.Fits W :=
  fun hW program hprog _ _ _ _ h base host hbound hin hfit =>
    SafeEval.compile_safe hW program hprog h base host hbound hin hfit

theorem compiler_length : ∀ (block : Block) (base : Nat),
    (block.compileAt base).length = block.size := Block.compile_length

theorem compiler_writesOnly : ∀ (block : Block) (allowed : Nat → Prop),
    block.WritesOnly allowed → ∀ (base : Nat), ∀ i ∈ block.compileAt base, WritesOnly allowed i :=
  Block.compile_writesOnly

theorem structured_evalF_sound : ∀ (fuel : Nat) (b : Block) (s s' : State) (k : Nat),
    evalF fuel b s = some (s', k) → Eval b s s' k := evalF_sound

theorem structured_safe_toEval : ∀ {W : Nat} {b : Block} {s s' : State} {k : Nat},
    SafeEval W b s s' k → Eval b s s' k := @SafeEval.toEval

/-! ## Loop rules -/

theorem loop_iterate : ∀ {P : State → Action → Prop} (Q : Nat → State → Prop)
    (c : Operand) (body : Block) (J : Nat),
    (∀ k s, Q k s → s.status = .running) →
    (∀ k s, Q (k + 1) s → s.regs c ≠ 0) →
    (∀ s, Q 0 s → s.regs c = 0) →
    (∀ k s, Q (k + 1) s → ∃ s' j, EvalG P body s s' j ∧ j ≤ J ∧ Q k s') →
    ∀ k s, Q k s →
      ∃ s' j, EvalG P (.loop c body) s s' j ∧ j ≤ k * (J + 2) + 1 ∧ Q 0 s' :=
  @EvalG.loop_iterate

theorem loop_iterate_potential : ∀ {P : State → Action → Prop} (Q : Nat → State → Prop)
    (Φ : State → Nat) (c : Operand) (body : Block) (J β : Nat),
    (∀ k s, Q k s → s.status = .running) →
    (∀ k s, Q (k + 1) s → s.regs c ≠ 0) →
    (∀ s, Q 0 s → s.regs c = 0) →
    (∀ k s, Q (k + 1) s → ∃ s' j, EvalG P body s s' j ∧ j + β * Φ s' ≤ J + β * Φ s ∧ Q k s') →
    ∀ k s, Q k s →
      ∃ s' j, EvalG P (.loop c body) s s' j ∧ j ≤ k * (J + 2) + 1 + β * Φ s ∧ Q 0 s' :=
  @EvalG.loop_iterate_potential_cost

theorem loop_measure : ∀ {P : State → Action → Prop} (Q : State → Prop) (μ : State → Nat)
    (c : Operand) (body : Block) (J : Nat),
    (∀ s, Q s → s.status = .running) →
    (∀ s, Q s → s.regs c ≠ 0 → ∃ s' j, EvalG P body s s' j ∧ j ≤ J ∧ Q s' ∧ μ s' < μ s) →
    ∀ (s : State), Q s →
      ∃ s' j, EvalG P (.loop c body) s s' j ∧ j ≤ μ s * (J + 2) + 1 ∧ Q s' ∧ s'.regs c = 0 :=
  @EvalG.loop_measure'

/-! ## Countdown loop: exact cost `4k + 1` as a theorem, and the array evaluator -/

/-- `while r0 ≠ 0 do r1 := r1 + r0; r0 := r0 - r2` with `r2` holding one. -/
def countdownBody : Block :=
  .seq (.action (.arithmetic .add 1 1 0)) (.action (.arithmetic .sub 0 0 2))

def countdown : Block := .loop 0 countdownBody

theorem countdown_cost : ∀ (k : Nat) (s : State), s.status = .running → s.regs 0 = k →
    s.regs 2 = 1 → ∃ s', Eval countdown s s' (4 * k + 1) ∧ s'.regs 0 = 0 ∧ s'.status = .running := by
  intro k
  induction k with
  | zero =>
      intro s hs h0 h2
      exact ⟨s, EvalG.loopExit hs (by simpa using h0), by simpa using h0, hs⟩
  | succ k ih =>
      intro s hs h0 h2
      have hs₁ : (execPrim (Prim.arithmetic .add 1 1 0) s).status = .running := by
        simp [execPrim, State.writeNext, State.next, hs]
      have hs₂ : (execPrim (Prim.arithmetic .sub 0 0 2)
          (execPrim (Prim.arithmetic .add 1 1 0) s)).status = .running := by
        simp [execPrim, State.writeNext, State.next, hs]
      have h0' : (execPrim (Prim.arithmetic .sub 0 0 2)
          (execPrim (Prim.arithmetic .add 1 1 0) s)).regs 0 = k := by
        simp [execPrim, State.writeNext, State.next, put, Arithmetic.eval, h0, h2]
      have h2' : (execPrim (Prim.arithmetic .sub 0 0 2)
          (execPrim (Prim.arithmetic .add 1 1 0) s)).regs 2 = 1 := by
        simp [execPrim, State.writeNext, State.next, put, h2]
      obtain ⟨s', hrest, h0'', hs'⟩ := ih _ hs₂ h0' h2'
      have hbody : Eval countdownBody s
          (execPrim (Prim.arithmetic .sub 0 0 2) (execPrim (Prim.arithmetic .add 1 1 0) s)) (1 + 1) :=
        EvalG.seq (EvalG.action (.arithmetic .add 1 1 0) s hs trivial)
          (EvalG.action (.arithmetic .sub 0 0 2) _ hs₁ trivial)
      have hstep := EvalG.loopStep (P := fun _ _ => True) hs
        (by simp [h0]) hbody hs₂ hrest
      have heq : 1 + 1 + (4 * k + 1) + 2 = 4 * (k + 1) + 1 := by omega
      rw [heq] at hstep
      exact ⟨s', hstep, h0'', hs'⟩

def countdownStart (k : Nat) : ExecState :=
  { regs := #[k, 0, 1, 0], memory := #[], keys := #[], keyRegs := #[0, 0, 0, 0],
    pc := 0, status := .running }

#guard (runArray (countdown.compileAt 0).toArray 100 (countdownStart 0)).steps = 1
#guard (runArray (countdown.compileAt 0).toArray 100 (countdownStart 1)).steps = 5
#guard (runArray (countdown.compileAt 0).toArray 100 (countdownStart 7)).steps = 29
#guard (runArray (countdown.compileAt 0).toArray 100 (countdownStart 7)).final.regs = #[0, 28, 1, 0]
#guard (runArray toyProgram.toArray 10 (ExecState.ofWordInput 4 40 [3])).writes = [(2, 1)]

theorem countdown_compiled_length : (countdown.compileAt 0).length = 4 := by decide

/-! ## Array-backed evaluator abstraction -/

theorem arrayRun_abstract : ∀ (program : List BInstr) (R : Nat),
    (∀ i ∈ program, i.primitive.RegistersBelow R) → ∀ (fuel : Nat) (es : ExecState),
    es.regs.size = R → es.keyRegs.size = R →
    (runArray program.toArray fuel es).steps = (run program fuel es.abstract).steps ∧
    (runArray program.toArray fuel es).categories = (run program fuel es.abstract).categories ∧
    (runArray program.toArray fuel es).writes = (run program fuel es.abstract).writes ∧
    (runArray program.toArray fuel es).reserves = (run program fuel es.abstract).reserves ∧
    (runArray program.toArray fuel es).result = (run program fuel es.abstract).result ∧
    (runArray program.toArray fuel es).final.abstract = (run program fuel es.abstract).final :=
  runArray_abstract

theorem arrayRun_word_input : ∀ (R width : Nat) (xs : List Int),
    (ExecState.ofWordInput R width xs).abstract = wordInputState width xs :=
  ExecState.ofWordInput_abstract

theorem arrayRun_comparison_input : ∀ (R : Nat) (xs : List Int),
    (ExecState.ofComparisonInput R xs).abstract = comparisonInputState xs :=
  ExecState.ofComparisonInput_abstract

theorem arrayRun_cleanTail : ∀ es : ExecState, CleanTail es.abstract := ExecState.abstract_cleanTail

/-! ## Program constants (CONTRACT.md V3-1 to V3-6, amendment V3-6a)

Every statement below is written out in full at the contract's type. -/

open Lean in
run_cmd do
  let env ← getEnv
  let host := `RMQ.Core.WordRAM.Construction.Builder.Program
  for name in [`RMQ.SuccinctFinal.PackedConstruction.builderSource,
      `RMQ.SuccinctFinal.PackedConstruction.builderBody,
      `RMQ.SuccinctFinal.PackedConstruction.keyLeaf,
      `RMQ.SuccinctFinal.PackedConstruction.wordLeaf,
      `RMQ.SuccinctFinal.PackedConstruction.builderProgram,
      `RMQ.SuccinctFinal.PackedConstruction.builderProgramWord,
      `RMQ.SuccinctFinal.PackedConstruction.builderBudget,
      `RMQ.SuccinctFinal.PackedConstruction.efficientBuild,
      `RMQ.SuccinctFinal.PackedConstruction.efficientBuildWord] do
    match env.getModuleIdxFor? name with
    | some idx =>
        unless env.header.moduleNames[idx.toNat]! == host do
          throwError "V3-1: {name} is not declared in {host}"
    | none => throwError "V3-1: {name} is not an imported declaration"

example : List BInstr := @builderProgram
example : List BInstr := @builderProgramWord

theorem builderProgram_def :
    builderProgram = (builderSource keyLeaf).compileAt 0 ++ [⟨.halt 3⟩] := rfl
theorem builderProgramWord_def :
    builderProgramWord = (builderSource wordLeaf).compileAt 0 ++ [⟨.halt 3⟩] := rfl
theorem builderSource_def : ∀ leaf : Block,
    builderSource leaf = .seq (.action (.load 1 0)) (builderBody leaf) := fun _ => rfl
theorem keyLeaf_def : keyLeaf =
    .seq (.action (.loadKey 0 4)) (.seq (.action (.loadKey 1 5))
      (.seq (.action (.compareKey 6 0 1)) (.seq (.action (.move 6 6))
        (.action (.move 6 6))))) := rfl
theorem wordLeaf_def : wordLeaf =
    .seq (.action (.arithmetic .add 7 4 2)) (.seq (.action (.load 7 7))
      (.seq (.action (.arithmetic .add 8 5 2)) (.seq (.action (.load 8 8))
        (.action (.comparison .lt 6 7 8))))) := rfl

theorem builder_leaf_difference :
    builderProgram.length = builderProgramWord.length ∧
    (List.range builderProgram.length).filter
        (fun i => builderProgram[i]? ≠ builderProgramWord[i]?) = [411, 412, 413, 414, 415, 429, 430, 431, 432, 433] ∧
    ([411, 412, 413, 414, 415, 429, 430, 431, 432, 433] : List Nat).map (fun i => builderProgram[i]?) =
      [some ⟨.loadKey 0 4⟩, some ⟨.loadKey 1 5⟩, some ⟨.compareKey 6 0 1⟩, some ⟨.move 6 6⟩,
        some ⟨.move 6 6⟩, some ⟨.loadKey 0 4⟩, some ⟨.loadKey 1 5⟩, some ⟨.compareKey 6 0 1⟩,
        some ⟨.move 6 6⟩, some ⟨.move 6 6⟩] ∧
    ([411, 412, 413, 414, 415, 429, 430, 431, 432, 433] : List Nat).map (fun i => builderProgramWord[i]?) =
      [some ⟨.arithmetic .add 7 4 2⟩, some ⟨.load 7 7⟩, some ⟨.arithmetic .add 8 5 2⟩,
        some ⟨.load 8 8⟩, some ⟨.comparison .lt 6 7 8⟩, some ⟨.arithmetic .add 7 4 2⟩,
        some ⟨.load 7 7⟩, some ⟨.arithmetic .add 8 5 2⟩, some ⟨.load 8 8⟩,
        some ⟨.comparison .lt 6 7 8⟩] :=
  Proof.builder_leaf_difference

theorem builderProgram_contract :
    ProgramContract builderProgram (fun _ => builderProgram) 2107 8079 :=
  Proof.builderProgram_contract
theorem builderProgramWord_contract :
    ProgramContract builderProgramWord (fun _ => builderProgramWord) 2107 8089 :=
  Proof.builderProgramWord_contract

theorem builderBudget_def : ∀ n : Nat, builderBudget n = 1000000000 + 1000000000 * n := fun _ => rfl

theorem efficientBuild_def : ∀ xs : List Int, efficientBuild xs =
    match (run builderProgram (builderBudget xs.length) (comparisonInputState xs)).final.status with
    | .halted outBase =>
        emitted (run builderProgram (builderBudget xs.length) (comparisonInputState xs)).final outBase
          ((run builderProgram (builderBudget xs.length) (comparisonInputState xs)).final.extent - outBase)
    | _ => [] := fun _ => rfl
theorem efficientBuildWord_def : ∀ xs : List Int,
    efficientBuildWord (RMQ.SuccinctFinal.PackedWordRAM.wordWidth xs.length) xs =
    match (run builderProgramWord (builderBudget xs.length)
        (wordInputState (RMQ.SuccinctFinal.PackedWordRAM.wordWidth xs.length) xs)).final.status with
    | .halted outBase =>
        emitted (run builderProgramWord (builderBudget xs.length)
            (wordInputState (RMQ.SuccinctFinal.PackedWordRAM.wordWidth xs.length) xs)).final outBase
          ((run builderProgramWord (builderBudget xs.length)
            (wordInputState (RMQ.SuccinctFinal.PackedWordRAM.wordWidth xs.length) xs)).final.extent - outBase)
    | _ => [] := fun _ => rfl

/-! ## Safety definitions pinned arm by arm (condition C3) -/

theorem safety_safeAt_arms : ∀ (W len : Nat) (s : State),
    (∀ dst address : Operand, Prim.SafeAt W len s (.load dst address) ↔
      (s.regs address < s.extent ∧ ∃ v, s.memory (s.regs address) = some v ∧ v < 2 ^ W)) ∧
    (∀ dst value : Operand, Prim.SafeAt W len s (.constant dst value) ↔ True) ∧
    (∀ dst src : Operand, Prim.SafeAt W len s (.move dst src) ↔ True) ∧
    (∀ (op : Arithmetic) (dst lhs rhs : Operand), Prim.SafeAt W len s (.arithmetic op dst lhs rhs) ↔
      (op.eval (s.regs lhs) (s.regs rhs) < 2 ^ W ∧ (op = .sub → s.regs rhs ≤ s.regs lhs) ∧
        (op = .div ∨ op = .mod → 0 < s.regs rhs) ∧ (op = .shl ∨ op = .shr → s.regs rhs < W))) ∧
    (∀ (op : Comparison) (dst lhs rhs : Operand), Prim.SafeAt W len s (.comparison op dst lhs rhs) ↔ True) ∧
    (∀ target : Operand, Prim.SafeAt W len s (.jump target) ↔ target.val < len) ∧
    (∀ src : Operand, Prim.SafeAt W len s (.jumpRegister src) ↔ False) ∧
    (∀ condition target : Operand, Prim.SafeAt W len s (.branchZero condition target) ↔ target.val < len) ∧
    (∀ src : Operand, Prim.SafeAt W len s (.halt src) ↔ True) ∧
    (∀ address value : Operand, Prim.SafeAt W len s (.store address value) ↔
      (s.regs address < s.extent ∧ s.regs value < 2 ^ W)) ∧
    (∀ dst : Operand, Prim.SafeAt W len s (.reserve dst) ↔ s.extent + 1 < 2 ^ W) ∧
    (∀ dst address : Operand, Prim.SafeAt W len s (.loadKey dst address) ↔
      ∃ k, s.keys (s.regs address) = some k) ∧
    (∀ dst lhs rhs : Operand, Prim.SafeAt W len s (.compareKey dst lhs rhs) ↔ True) :=
  fun _ _ _ => ⟨fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ _ _ => Iff.rfl,
    fun _ _ _ _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ => Iff.rfl,
    fun _ _ => Iff.rfl, fun _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ _ => Iff.rfl⟩

theorem safety_run_safe_definition : ∀ (W : Nat) (program : List BInstr) (r : Run),
    Run.Safe W program r ↔ ∀ t ∈ r.transitions,
      Prim.Safe W program.length t.before t.instruction.primitive ∧ t.after.Fits W :=
  fun _ _ _ => Iff.rfl

theorem safety_fits_definition : ∀ (W : Nat) (s : State),
    s.Fits W ↔ ((∀ r, s.regs r < 2 ^ W) ∧ s.pc < 2 ^ W ∧ s.extent < 2 ^ W ∧
      (∀ a v, s.memory a = some v → v < 2 ^ W) ∧ (∀ v, s.status = .halted v → v < 2 ^ W)) :=
  fun _ _ => Iff.rfl

/-! ## Axiom inventory -/

#print axioms headerUse_of_program
#print axioms run_missing_header
#print axioms run_header_first
#print axioms run_write_at
#print axioms run_load_at
#print axioms writes_replay
#print axioms run_frame
#print axioms run_agree_of_reads
#print axioms run_agree_of_supplied
#print axioms Run.steps_partition
#print axioms RunsTo.fuel_extension
#print axioms Prim.safe_not_fault
#print axioms Prim.safe_fits
#print axioms Run.Safe.of_transitions
#print axioms EvalG.compile_realizes
#print axioms SafeEval.compile_safe
#print axioms EvalG.loop_iterate
#print axioms EvalG.loop_iterate_potential
#print axioms EvalG.loop_measure
#print axioms evalF_sound
#print axioms runArray_abstract
#print axioms ExecState.ofWordInput_abstract
#print axioms toy_headerUse
#print axioms toy_run
#print axioms countdown_cost
#print axioms Proof.builder_leaf_difference
#print axioms Proof.filter_range_ne_eq_diffPositions
#print axioms Proof.builderProgram_contract
#print axioms Proof.builderProgramWord_contract
#print axioms builderProgram_def
#print axioms builderProgramWord_def
#print axioms builderSource_def
#print axioms keyLeaf_def
#print axioms wordLeaf_def
#print axioms builderBudget_def
#print axioms efficientBuild_def
#print axioms efficientBuildWord_def
/-! ## Verdict marker (audit PRE-1-A1C P3-1; repair PRE-1-R2 of audit PRE-1-A2 P2-1)

The exit code is the verdict. The marker is printed if and only if (1) the whole
file elaborates with no error-severity message, (2) `consumerWitness`, which
refers to each declaration above, exists and collects no `sorryAx`, and (3)
`consumerGuards`, which repeats the `#guard` checks above, holds; otherwise
nothing is printed and no diagnostic is added, so the failing line set of a
rejected mutation stays exactly the lines above. Lean 4.22 resets the command
state's message log before every command (`Lean.Language.Lean.process.doElab`
sets `messages := .empty`), so this command cannot read an earlier command's
errors from its own state. For the whole-file condition it elaborates the file a
second time in this process from the source text of its own input context, with
only this command blanked (line breaks kept), through `Lean.Parser.parseHeader`,
`Lean.Elab.processHeader` and `Lean.Elab.IO.processCommands`, which collects the
message logs of every command snapshot, and requires `MessageLog.hasErrors` to
be false for the header and for those messages: the predicate by which the
frontend decides the exit code. An error in any command kind (a declaration, an
anonymous example, a `#guard` or `run_cmd` check, a missing declaration after a
maximum-recursion-depth failure, or a command after this one) therefore
suppresses the marker. -/

def consumerWitness : Unit :=
  let _ := @hu_headerFirst
  let _ := @hu_tailNeverWritesR1
  let _ := @hu_wordMissingHeaderFault
  let _ := @hu_comparisonMissingHeaderFault
  let _ := @hu_wordHeaderReceipt
  let _ := @hu_comparisonHeaderReceipt
  let _ := @hu_oracleExtentOne
  let _ := @hu_of_program
  let _ := @toyProgram
  let _ := @toy_headerUse
  let _ := @toy_run
  let _ := @toy_missing_header
  let _ := @calc_write_at
  let _ := @calc_load_at
  let _ := @calc_writes_replay
  let _ := @calc_frame
  let _ := @calc_partition
  let _ := @calc_fuel_extension
  let _ := @calc_extent_mono
  let _ := @calc_cleanTail
  let _ := @calc_agree_of_reads
  let _ := @calc_agree_of_supplied
  let _ := @calc_agree_projections
  let _ := @calc_missing_header
  let _ := @calc_header_first
  let _ := @safety_not_fault
  let _ := @safety_fits
  let _ := @safety_run_of_transitions
  let _ := @safety_run_not_fault
  let _ := @safety_definition
  let _ := @safety_jumpRegister_rejected
  let _ := @compiler_realizes
  let _ := @compiler_safe
  let _ := @compiler_length
  let _ := @compiler_writesOnly
  let _ := @structured_evalF_sound
  let _ := @structured_safe_toEval
  let _ := @loop_iterate
  let _ := @loop_iterate_potential
  let _ := @loop_measure
  let _ := @countdownBody
  let _ := @countdown
  let _ := @countdown_cost
  let _ := @countdownStart
  let _ := @countdown_compiled_length
  let _ := @arrayRun_abstract
  let _ := @arrayRun_word_input
  let _ := @arrayRun_comparison_input
  let _ := @arrayRun_cleanTail
  let _ := @builderProgram_def
  let _ := @builderProgramWord_def
  let _ := @builderSource_def
  let _ := @keyLeaf_def
  let _ := @wordLeaf_def
  let _ := @builder_leaf_difference
  let _ := @builderProgram_contract
  let _ := @builderProgramWord_contract
  let _ := @builderBudget_def
  let _ := @efficientBuild_def
  let _ := @efficientBuildWord_def
  let _ := @safety_safeAt_arms
  let _ := @safety_run_safe_definition
  let _ := @safety_fits_definition
  ()

def consumerGuards : Bool :=
  decide ((runArray (countdown.compileAt 0).toArray 100 (countdownStart 0)).steps = 1) &&
  decide ((runArray (countdown.compileAt 0).toArray 100 (countdownStart 1)).steps = 5) &&
  decide ((runArray (countdown.compileAt 0).toArray 100 (countdownStart 7)).steps = 29) &&
  decide ((runArray (countdown.compileAt 0).toArray 100 (countdownStart 7)).final.regs = #[0, 28, 1, 0]) &&
  decide ((runArray toyProgram.toArray 10 (ExecState.ofWordInput 4 40 [3])).writes = [(2, 1)])

open Lean Elab Command in
#eval show CommandElabM Unit from do
  -- (1) Whole file: elaborate this file again in this process from its own
  -- source text, with only this command blanked (line breaks kept), and read
  -- the message log of the header and of every command.
  let context ← read
  let source := context.fileMap.source
  let scope ← getScope
  let markerStop := (Parser.parseCommand (Parser.mkInputContext source context.fileName)
    { env := ← getEnv, options := scope.opts, currNamespace := scope.currNamespace,
      openDecls := scope.openDecls } { pos := context.cmdPos } {}).2.1.pos
  let blank := (source.extract context.cmdPos markerStop).map
    fun c => if c == '\n' || c == '\r' then c else ' '
  let input := Parser.mkInputContext
    (source.extract 0 context.cmdPos ++ blank ++ source.extract markerStop source.endPos)
    context.fileName
  let (header, parserState, headerMessages) ← Parser.parseHeader input
  let options := Elab.async.setIfNotSet (internal.cmdlineSnapshots.setIfNotSet {} true) true
  let (headerEnv, headerMessages) ← processHeader header options headerMessages input
    (trustLevel := (← getEnv).header.trustLevel) (leakEnv := true)
    (mainModule := (← getEnv).mainModule)
  let whole ← IO.processCommands input parserState (Command.mkState headerEnv {} options)
  let fileClean := !headerMessages.hasErrors && !whole.commandState.messages.hasErrors
  -- (2) The witness exists and collects no `sorryAx`.
  let witness := `PRE1BuilderConsumer.consumerWitness
  let witnessClean ← if (← getEnv).contains witness then
      pure !((← collectAxioms witness).contains ``sorryAx)
    else pure false
  -- (3) The guards hold.
  if fileClean && witnessClean && consumerGuards then IO.println "PRE1-BUILDER-TYPED-CONSUMERS PASS"
end PRE1BuilderConsumer
