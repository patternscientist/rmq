import RMQ.Core.WordRAM.E1Machine

/-!
# E1 amended machine: program-composition calculus

Compositional reasoning layer over `RMQ.WordRAM.E1Machine` for the
concrete whole-query program proofs (frozen matrix REQ-E1-03/04/05/06):

* `HostedAt program base code` - the instruction block `code` sits at
  absolute address `base` inside `program`.  Generators emit blocks at
  explicit bases (branch targets are absolute, resolved by the
  generator), and per-block lemmas are stated against any hosting
  program, so blocks compose by concatenation.
* `RunsTo store program s s' reads cats` - exact-fuel big-step
  execution: running with fuel `cats.length` consumes it exactly,
  reaching `s'` with receipt log `reads` and category log `cats`.
  Reflexivity, transitivity (via `run_add`), one lemma per instruction
  constructor, and fuel-insensitivity after halt make whole-program
  correctness a chain of mechanical steps.

Everything here is machine-generic; nothing mentions the RMQ route.
-/

namespace RMQ
namespace WordRAM
namespace E1Machine

/-! ## Hosted code blocks -/

/-- `code` is hosted at absolute base `base` in `program`: fetching
`base + i` yields instruction `i` of the block. -/
def HostedAt (program : Program) (base : Nat) (code : List Instr) : Prop :=
  ∀ i, i < code.length → program[base + i]? = code[i]?

theorem hostedAt_nil (program : Program) (base : Nat) :
    HostedAt program base [] := by
  intro i hi
  cases hi

/-- A program hosts itself at base `0`. -/
theorem hostedAt_self (program : Program) : HostedAt program 0 program := by
  intro i hi
  simp

theorem HostedAt.head {program : Program} {base : Nat} {instr : Instr}
    {rest : List Instr} (h : HostedAt program base (instr :: rest)) :
    program[base]? = some instr := by
  have := h 0 (Nat.succ_le_succ (Nat.zero_le _))
  simpa using this

theorem HostedAt.tail {program : Program} {base : Nat} {instr : Instr}
    {rest : List Instr} (h : HostedAt program base (instr :: rest)) :
    HostedAt program (base + 1) rest := by
  intro i hi
  have := h (i + 1) (Nat.succ_le_succ hi)
  have harith : base + 1 + i = base + (i + 1) := by omega
  rw [harith]
  simpa using this

theorem HostedAt.append_left {program : Program} {base : Nat}
    {code₁ code₂ : List Instr}
    (h : HostedAt program base (code₁ ++ code₂)) :
    HostedAt program base code₁ := by
  intro i hi
  have hlt : i < (code₁ ++ code₂).length := by
    simp [List.length_append]
    omega
  have := h i hlt
  rwa [List.getElem?_append_left hi] at this

theorem HostedAt.append_right {program : Program} {base : Nat}
    {code₁ code₂ : List Instr}
    (h : HostedAt program base (code₁ ++ code₂)) :
    HostedAt program (base + code₁.length) code₂ := by
  intro i hi
  have hlt : code₁.length + i < (code₁ ++ code₂).length := by
    simp [List.length_append]
    omega
  have harith : base + code₁.length + i = base + (code₁.length + i) := by
    omega
  rw [harith]
  have := h (code₁.length + i) hlt
  rw [this]
  rw [List.getElem?_append_right (by omega)]
  congr 1
  omega

/-! ## Exact-fuel big-step execution -/

/--
Exact-fuel big-step relation: from `s`, running with fuel `cats.length`
consumes every unit (one instruction per category tick), reaching `s'`
with receipt log `reads`.  Because the fuel equals the step count, two
`RunsTo` segments compose exactly.
-/
def RunsTo (store : ReadStore) (program : Program) (s s' : State)
    (reads : List TraceEvent) (cats : List Category) : Prop :=
  run store program cats.length s = ⟨s', reads, cats, cats.length⟩

theorem RunsTo.refl (store : ReadStore) (program : Program) (s : State) :
    RunsTo store program s s [] [] := rfl

theorem RunsTo.trans {store : ReadStore} {program : Program}
    {s₁ s₂ s₃ : State} {r₁ r₂ : List TraceEvent}
    {c₁ c₂ : List Category}
    (h₁ : RunsTo store program s₁ s₂ r₁ c₁)
    (h₂ : RunsTo store program s₂ s₃ r₂ c₂) :
    RunsTo store program s₁ s₃ (r₁ ++ r₂) (c₁ ++ c₂) := by
  unfold RunsTo at h₁ h₂ ⊢
  have hadd := run_add store program c₁.length c₂.length s₁
  rw [h₁] at hadd
  simp only at hadd
  rw [h₂] at hadd
  simp only [List.length_append]
  simpa using hadd

/-- One executed instruction, in relational form. -/
theorem RunsTo.step {store : ReadStore} {program : Program} {s s' : State}
    {instr : Instr} {cat : Category} {event? : Option TraceEvent}
    (hhalt : s.halted = false)
    (hfetch : program[s.pc]? = some instr)
    (hexec : execInstr store instr s = (s', cat, event?)) :
    RunsTo store program s s' event?.toList [cat] := by
  unfold RunsTo
  have hstep : E1Machine.step store program s = some (s', cat, event?) := by
    unfold E1Machine.step
    rw [if_neg (by simp [hhalt]), hfetch]
    simp [hexec]
  show run store program (0 + 1) s = _
  rw [run_succ, hstep]
  simp

/-! ### Per-constructor step rules

Each rule needs only "not halted" and the fetch fact; the successor
state, receipt, and category are computed by the semantics.  These are
the mechanical bricks for the concrete program proofs.
-/

theorem RunsTo.readMem {store : ReadStore} {program : Program} {s : State}
    {dst segment addrReg : Nat} (hhalt : s.halted = false)
    (hfetch : program[s.pc]? = some (.readMem dst segment addrReg)) :
    RunsTo store program s
      ⟨s.regs.write dst
          (decodeRead (store.readWord? segment (s.regs addrReg))),
        s.pc + 1, false⟩
      [.readWord segment (s.regs addrReg)
          (store.readWord? segment (s.regs addrReg))]
      [.memoryRead] :=
  RunsTo.step hhalt hfetch rfl

theorem RunsTo.const {store : ReadStore} {program : Program} {s : State}
    {dst value : Nat} (hhalt : s.halted = false)
    (hfetch : program[s.pc]? = some (.const dst value)) :
    RunsTo store program s
      ⟨s.regs.write dst value, s.pc + 1, false⟩ [] [.registerWrite] :=
  RunsTo.step hhalt hfetch rfl

theorem RunsTo.move {store : ReadStore} {program : Program} {s : State}
    {dst src : Nat} (hhalt : s.halted = false)
    (hfetch : program[s.pc]? = some (.move dst src)) :
    RunsTo store program s
      ⟨s.regs.write dst (s.regs src), s.pc + 1, false⟩ []
      [.registerWrite] :=
  RunsTo.step hhalt hfetch rfl

theorem RunsTo.add {store : ReadStore} {program : Program} {s : State}
    {dst src₁ src₂ : Nat} (hhalt : s.halted = false)
    (hfetch : program[s.pc]? = some (.add dst src₁ src₂)) :
    RunsTo store program s
      ⟨s.regs.write dst (s.regs src₁ + s.regs src₂), s.pc + 1, false⟩ []
      [.arithmetic] :=
  RunsTo.step hhalt hfetch rfl

theorem RunsTo.sub {store : ReadStore} {program : Program} {s : State}
    {dst src₁ src₂ : Nat} (hhalt : s.halted = false)
    (hfetch : program[s.pc]? = some (.sub dst src₁ src₂)) :
    RunsTo store program s
      ⟨s.regs.write dst (s.regs src₁ - s.regs src₂), s.pc + 1, false⟩ []
      [.arithmetic] :=
  RunsTo.step hhalt hfetch rfl

theorem RunsTo.mulConst {store : ReadStore} {program : Program} {s : State}
    {dst src k : Nat} (hhalt : s.halted = false)
    (hfetch : program[s.pc]? = some (.mulConst dst src k)) :
    RunsTo store program s
      ⟨s.regs.write dst (s.regs src * k), s.pc + 1, false⟩ []
      [.arithmetic] :=
  RunsTo.step hhalt hfetch rfl

theorem RunsTo.divConst {store : ReadStore} {program : Program} {s : State}
    {dst src k : Nat} (hhalt : s.halted = false)
    (hfetch : program[s.pc]? = some (.divConst dst src k)) :
    RunsTo store program s
      ⟨s.regs.write dst (s.regs src / k), s.pc + 1, false⟩ []
      [.arithmetic] :=
  RunsTo.step hhalt hfetch rfl

theorem RunsTo.natLt {store : ReadStore} {program : Program} {s : State}
    {dst src₁ src₂ : Nat} (hhalt : s.halted = false)
    (hfetch : program[s.pc]? = some (.natLt dst src₁ src₂)) :
    RunsTo store program s
      ⟨s.regs.write dst (if s.regs src₁ < s.regs src₂ then 1 else 0),
        s.pc + 1, false⟩ [] [.comparison] :=
  RunsTo.step hhalt hfetch rfl

theorem RunsTo.natLe {store : ReadStore} {program : Program} {s : State}
    {dst src₁ src₂ : Nat} (hhalt : s.halted = false)
    (hfetch : program[s.pc]? = some (.natLe dst src₁ src₂)) :
    RunsTo store program s
      ⟨s.regs.write dst (if s.regs src₁ ≤ s.regs src₂ then 1 else 0),
        s.pc + 1, false⟩ [] [.comparison] :=
  RunsTo.step hhalt hfetch rfl

theorem RunsTo.natEq {store : ReadStore} {program : Program} {s : State}
    {dst src₁ src₂ : Nat} (hhalt : s.halted = false)
    (hfetch : program[s.pc]? = some (.natEq dst src₁ src₂)) :
    RunsTo store program s
      ⟨s.regs.write dst (if s.regs src₁ = s.regs src₂ then 1 else 0),
        s.pc + 1, false⟩ [] [.comparison] :=
  RunsTo.step hhalt hfetch rfl

theorem RunsTo.brNZ {store : ReadStore} {program : Program} {s : State}
    {cond target : Nat} (hhalt : s.halted = false)
    (hfetch : program[s.pc]? = some (.brNZ cond target)) :
    RunsTo store program s
      ⟨s.regs, if s.regs cond = 0 then s.pc + 1 else target, false⟩ []
      [.branch] :=
  RunsTo.step hhalt hfetch rfl

theorem RunsTo.halt {store : ReadStore} {program : Program} {s : State}
    (hhalt : s.halted = false)
    (hfetch : program[s.pc]? = some .halt) :
    RunsTo store program s ⟨s.regs, s.pc, true⟩ [] [.control] :=
  RunsTo.step hhalt hfetch rfl

/-! ## Fuel insensitivity after halt -/

/-- Once a `RunsTo` segment ends halted, any surplus fuel changes
nothing: the run packet is determined.  This makes "the machine outcome"
well defined by any fuel budget at least the step count. -/
theorem RunsTo.run_fuel_ge {store : ReadStore} {program : Program}
    {s s' : State} {reads : List TraceEvent} {cats : List Category}
    (h : RunsTo store program s s' reads cats)
    (hhalted : s'.halted = true) (extra : Nat) :
    run store program (cats.length + extra) s = ⟨s', reads, cats,
      cats.length⟩ := by
  have hadd := run_add store program cats.length extra s
  unfold RunsTo at h
  rw [h] at hadd
  simp only at hadd
  have hstuck : E1Machine.step store program s' = none := by
    unfold E1Machine.step
    rw [if_pos hhalted]
  rw [run_stuck store program hstuck extra] at hadd
  simpa using hadd

/-- Restated with an arbitrary sufficient fuel budget. -/
theorem RunsTo.run_of_le_fuel {store : ReadStore} {program : Program}
    {s s' : State} {reads : List TraceEvent} {cats : List Category}
    (h : RunsTo store program s s' reads cats)
    (hhalted : s'.halted = true) {fuel : Nat} (hfuel : cats.length ≤ fuel) :
    run store program fuel s = ⟨s', reads, cats, cats.length⟩ := by
  obtain ⟨extra, rfl⟩ : ∃ extra, fuel = cats.length + extra :=
    ⟨fuel - cats.length, by omega⟩
  exact h.run_fuel_ge hhalted extra

/-! ## Iterated blocks (chunk-loop backbone)

The route's only loops are chunk folds with literal iteration caps
(33 fringe windows, 8 word chunks).  On the machine they compile to a
counted block with a `brNZ` back-edge.  `RunsTo.iterate` is the generic
composition: a loop invariant indexed by the remaining iteration count,
one `RunsTo` segment per iteration with iteration-indexed receipts and
category charges, composed by `RunsTo.trans` down to counter zero.  The
receipts of the whole loop are the concatenation of the per-iteration
receipts in execution order (counter `k` descending to `0`), so exact
positional receipt equality survives loop composition.
-/

/-- Execution-ordered concatenation of iteration-indexed logs: the
iteration executed with remaining counter `k + 1` contributes `f k`, and
iterations run with the counter descending. -/
def iterLog {α : Type} (f : Nat → List α) : Nat → List α
  | 0 => []
  | k + 1 => f k ++ iterLog f k

@[simp] theorem iterLog_zero {α : Type} (f : Nat → List α) :
    iterLog f 0 = [] := rfl

@[simp] theorem iterLog_succ {α : Type} (f : Nat → List α) (k : Nat) :
    iterLog f (k + 1) = f k ++ iterLog f k := rfl

/--
Generic counted-loop composition.  If from every state satisfying the
invariant at counter `k + 1` the body makes one `RunsTo` segment with
receipts `reads k` and charges `cats k`, re-establishing the invariant at
counter `k`, then from any state at counter `k` the whole loop runs to an
invariant-`0` state with the execution-ordered concatenated receipts and
charges.
-/
theorem RunsTo.iterate {store : ReadStore} {program : Program}
    (P : Nat → State → Prop)
    (reads : Nat → List TraceEvent) (cats : Nat → List Category)
    (hstep : ∀ k s, P (k + 1) s →
      ∃ s', RunsTo store program s s' (reads k) (cats k) ∧ P k s') :
    ∀ k s, P k s →
      ∃ s',
        RunsTo store program s s' (iterLog reads k) (iterLog cats k) ∧
          P 0 s' := by
  intro k
  induction k with
  | zero =>
      intro s h
      exact ⟨s, RunsTo.refl store program s, h⟩
  | succ k ih =>
      intro s h
      obtain ⟨s', hbody, hP⟩ := hstep k s h
      obtain ⟨s'', hrest, hP0⟩ := ih s' hP
      exact ⟨s'', hbody.trans hrest, hP0⟩

/-! ## Early-exit iterated blocks (select-fold backbone)

The chunked select fold exits early on the found chunk: the iteration
executed with remaining counter `k + 1` either continues (routing read,
subtract, back edge) or fires the exit tail (select-table read, jump out).
Which alternative runs is determined by the store and the loop inputs, so
it is a FUNCTION of the remaining counter (`exits`), and the whole-loop
receipts/charges stay fixed functions of the initial counter — exact
positional receipt equality survives early-exit loop composition.  The
counter-`0` exhaustion tail (the fold's `none` case) is its own segment.
-/

/-- Execution-ordered log of an early-exit loop: the iteration executed
with remaining counter `k + 1` contributes its exit log `exit k` and stops
if `exits k`, else its continuing log `cont k`; exhaustion (counter `0`)
contributes `exhaust`. -/
def iterUntilLog {α : Type} (exits : Nat → Bool)
    (cont exit : Nat → List α) (exhaust : List α) : Nat → List α
  | 0 => exhaust
  | k + 1 =>
      if exits k then exit k
      else cont k ++ iterUntilLog exits cont exit exhaust k

@[simp] theorem iterUntilLog_zero {α : Type} (exits : Nat → Bool)
    (cont exit : Nat → List α) (exhaust : List α) :
    iterUntilLog exits cont exit exhaust 0 = exhaust := rfl

theorem iterUntilLog_succ {α : Type} (exits : Nat → Bool)
    (cont exit : Nat → List α) (exhaust : List α) (k : Nat) :
    iterUntilLog exits cont exit exhaust (k + 1) =
      if exits k then exit k
      else cont k ++ iterUntilLog exits cont exit exhaust k := rfl

theorem iterUntilLog_succ_of_exits {α : Type} {exits : Nat → Bool}
    (cont exit : Nat → List α) (exhaust : List α) {k : Nat}
    (h : exits k = true) :
    iterUntilLog exits cont exit exhaust (k + 1) = exit k := by
  rw [iterUntilLog_succ, if_pos h]

theorem iterUntilLog_succ_of_continues {α : Type} {exits : Nat → Bool}
    (cont exit : Nat → List α) (exhaust : List α) {k : Nat}
    (h : exits k = false) :
    iterUntilLog exits cont exit exhaust (k + 1) =
      cont k ++ iterUntilLog exits cont exit exhaust k := by
  rw [iterUntilLog_succ, if_neg (by simp [h])]

/--
Generic early-exit loop composition.  If from every state satisfying the
invariant at counter `k + 1` the iteration either exits (when `exits k`)
with receipts `readsExit k` / charges `catsExit k` into the exit predicate
`Q`, or continues (when `¬ exits k`) with receipts `readsCont k` / charges
`catsCont k` re-establishing the invariant at counter `k`, and every
invariant-`0` state runs the exhaustion tail into `Q`, then from any state
at counter `k` the whole loop runs into `Q` with the execution-ordered
`iterUntilLog` receipts and charges.
-/
theorem RunsTo.iterateUntil {store : ReadStore} {program : Program}
    (P : Nat → State → Prop) (Q : State → Prop) (exits : Nat → Bool)
    (readsCont readsExit : Nat → List TraceEvent)
    (catsCont catsExit : Nat → List Category)
    (readsExhaust : List TraceEvent) (catsExhaust : List Category)
    (hstep : ∀ k s, P (k + 1) s →
      if exits k then
        ∃ s', RunsTo store program s s' (readsExit k) (catsExit k) ∧ Q s'
      else
        ∃ s', RunsTo store program s s' (readsCont k) (catsCont k) ∧
          P k s')
    (hexhaust : ∀ s, P 0 s →
      ∃ s', RunsTo store program s s' readsExhaust catsExhaust ∧ Q s') :
    ∀ k s, P k s →
      ∃ s',
        RunsTo store program s s'
            (iterUntilLog exits readsCont readsExit readsExhaust k)
            (iterUntilLog exits catsCont catsExit catsExhaust k) ∧
          Q s' := by
  intro k
  induction k with
  | zero =>
      intro s h
      exact hexhaust s h
  | succ k ih =>
      intro s h
      have hs := hstep k s h
      cases hexit : exits k with
      | true =>
          rw [if_pos (by simp [hexit])] at hs
          obtain ⟨s', hrun, hQ⟩ := hs
          refine ⟨s', ?_, hQ⟩
          rw [iterUntilLog_succ_of_exits _ _ _ hexit,
            iterUntilLog_succ_of_exits _ _ _ hexit]
          exact hrun
      | false =>
          rw [if_neg (by simp [hexit])] at hs
          obtain ⟨s', hbody, hP⟩ := hs
          obtain ⟨s'', hrest, hQ⟩ := ih s' hP
          refine ⟨s'', ?_, hQ⟩
          rw [iterUntilLog_succ_of_continues _ _ _ hexit,
            iterUntilLog_succ_of_continues _ _ _ hexit]
          exact hbody.trans hrest

end E1Machine
end WordRAM
end RMQ
