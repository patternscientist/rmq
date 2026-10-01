import RMQ.Core.WordRAM.Lifecycle.Safety

/-! # Hosted scalar arena finalization

This fragment copies the produced source forward, including overlap, and then
retires exactly its old base offset in single-cell releases. It ends running
at the continuation PC. Functional memory equality is not a native-capacity
or alias-freedom claim.
-/

namespace RMQ.SuccinctFinal.PackedLifecycle.Finalizer

open PackedConstruction (Memory Operand Prim execPrim put Arithmetic)
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

@[simp] theorem operand_zero : (0 : Operand).val = 0 := rfl
@[simp] theorem operand_one : (1 : Operand).val = 1 := rfl
@[simp] theorem operand_two : (2 : Operand).val = 2 := rfl
@[simp] theorem operand_three : (3 : Operand).val = 3 := rfl
@[simp] theorem operand_four : (4 : Operand).val = 4 := rfl
@[simp] theorem operand_five : (5 : Operand).val = 5 := rfl

/-- Fourteen fixed scalar instructions, relocated only by their host offset. -/
def code (base : Nat) (bound : base + 14 < 2 ^ 32) : List Instruction := [
  .old (.move 3 0),
  .old (.constant 1 0),
  .old (.constant 4 1),
  .old (.branchZero 2 ⟨base + 10, by omega⟩),
  .old (.load 5 0),
  .old (.store 1 5),
  .old (.arithmetic .add 0 0 4),
  .old (.arithmetic .add 1 1 4),
  .old (.arithmetic .sub 2 2 4),
  .old (.jump ⟨base + 3, by omega⟩),
  .old (.branchZero 3 ⟨base + 14, bound⟩),
  .releaseCell,
  .old (.arithmetic .sub 3 3 4),
  .old (.jump ⟨base + 10, by omega⟩)]

def Hosted (program : List Instruction) (base : Nat) (bound : base + 14 < 2 ^ 32) : Prop :=
  ∀ i, i < 14 → program[base + i]? = (code base bound)[i]?

theorem fetch_zero {program : List Instruction} {base : Nat} {bound : base + 14 < 2 ^ 32}
    (host : Hosted program base bound) : program[base]? = some (.old (.move 3 0)) := by
  simpa [code] using host 0 (by decide)

def Initialized (original : Memory) (B M : Nat) : Prop :=
  ∀ j, j < M → ∃ v, original (B + j) = some v

abbrev CleanTail (s : State) : Prop := PackedConstruction.CleanTail s.core

def FinalOutput (original : Memory) (B M : Nat) (s : State) : Prop :=
  s.core.extent = M ∧ (∀ j, j < M → s.core.memory j = original (B + j)) ∧ CleanTail s

def CopyInv (base : Nat) (original : Memory) (B M i : Nat) (s : State) : Prop :=
  s.core.status = .running ∧ s.core.pc = base + 3 ∧ s.core.extent = B + M ∧
  s.core.regs 0 = B + i ∧ s.core.regs 1 = i ∧ s.core.regs 2 = M - i ∧
  s.core.regs 3 = B ∧ s.core.regs 4 = 1 ∧
  (∀ j, j < i → s.core.memory j = original (B + j)) ∧
  (∀ a, i ≤ a → s.core.memory a = original a)

def ReleaseInv (base : Nat) (original : Memory) (B M left : Nat) (s : State) : Prop :=
  s.core.status = .running ∧ s.core.pc = base + 10 ∧ s.core.extent = M + left ∧
  s.core.regs 1 = M ∧ s.core.regs 3 = left ∧ s.core.regs 4 = 1 ∧
  (∀ j, j < M → s.core.memory j = original (B + j)) ∧ CleanTail s

def cost (B M : Nat) : Nat := 7 * M + 4 * B + 5

def copyCategories : List Category :=
  [.old .branch, .old .read, .old .write, .old .arithmetic,
    .old .arithmetic, .old .arithmetic, .old .branch]

def releaseCategories : List Category :=
  [.old .branch, .numericRelease, .old .arithmetic, .old .branch]

def expectedCategories (B M : Nat) : List Category :=
  [.old .register, .old .register, .old .register] ++
  (List.replicate M copyCategories).flatten ++ [.old .branch] ++
  (List.replicate B releaseCategories).flatten ++ [.old .branch]

def Entry (base B M : Nat) (s : State) : Prop :=
  s.core.status = .running ∧ s.core.pc = base ∧ s.core.extent = B + M ∧
  s.core.regs 0 = B ∧ s.core.regs 2 = M ∧ Initialized s.core.memory B M ∧ CleanTail s

def Good (W : Nat) (program : List Instruction) (r : Run) : Prop :=
  ∀ t ∈ r.transitions, t.Safe W program.length

def UsesCode (base : Nat) (bound : base + 14 < 2 ^ 32) (r : Run) : Prop :=
  ∀ t ∈ r.transitions, ∃ i ∈ code base bound, t.action = .instruction i

def Frame (before after : State) : Prop :=
  after.keyExtent = before.keyExtent ∧ after.keyRegExtent = before.keyRegExtent ∧
  after.core.keys = before.core.keys ∧ after.core.keyRegs = before.core.keyRegs ∧
  after.core.extent ≤ before.core.extent ∧
  (∀ r, 6 ≤ r → after.core.regs r = before.core.regs r)

def CopyReceipt (original : Memory) (B i : Nat) (load store : Transition) : Prop :=
  load.action = .instruction (.old (.load 5 0)) ∧
  store.action = .instruction (.old (.store 1 5)) ∧
  load.before.core.regs 0 = B + i ∧ store.before.core.regs 1 = i ∧
  load.before.core.memory (B + i) = original (B + i) ∧
  some (load.after.core.regs 5) = original (B + i) ∧ store.before = load.after ∧
  store.after.core.memory i = original (B + i) ∧
  load.read? = some (B + i, original (B + i)) ∧
  store.write? = some (i, load.after.core.regs 5)

def ReleaseReceipt (a : Nat) (t : Transition) : Prop :=
  t.action = .instruction .releaseCell ∧ t.before.core.extent = a + 1 ∧
  t.after.core.extent = a ∧ t.after.core.memory a = none ∧
  (∀ other, other ≠ a → t.after.core.memory other = t.before.core.memory other) ∧
  t.after = execute .releaseCell t.before

theorem run_prefix_at {program : List Instruction} {s : State} {a b c k : Nat} {t : Transition}
    (ha : (run program a s).transitions.length = a)
    (hk : (run program b (run program a s).final).transitions[k]? = some t) :
    (run program (a + (b + c)) s).transitions[a + k]? = some t := by
  simp only [run_add]
  rw [List.getElem?_append_right (by omega), ha, Nat.add_sub_cancel_left]
  have hlt : k < (run program b (run program a s).final).transitions.length :=
    (List.getElem?_eq_some_iff.mp hk).1
  rw [List.getElem?_append_left hlt]
  exact hk

theorem Frame.refl (s : State) : Frame s s := by simp [Frame]

theorem Frame.trans {a b c : State} (hab : Frame a b) (hbc : Frame b c) : Frame a c :=
  ⟨hbc.1.trans hab.1, hbc.2.1.trans hab.2.1,
    hbc.2.2.1.trans hab.2.2.1, hbc.2.2.2.1.trans hab.2.2.2.1,
    Nat.le_trans hbc.2.2.2.2.1 hab.2.2.2.2.1,
    fun r hr => (hbc.2.2.2.2.2 r hr).trans (hab.2.2.2.2.2 r hr)⟩

theorem instruction_frame (s : State) (base : Nat) (bound : base + 14 < 2 ^ 32)
    (i : Instruction) (hi : i ∈ code base bound) : Frame s (execute i s) := by
  simp only [code, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [Frame, execute, execPrim, PackedConstruction.State.next, PackedConstruction.State.writeNext, put]
  all_goals
    repeat' split
    all_goals simp_all [put]
    all_goals omega

theorem run_frame_of_uses {program : List Instruction} {base : Nat} {bound : base + 14 < 2 ^ 32}
    {fuel : Nat} {s : State} (uses : UsesCode base bound (run program fuel s)) :
    Frame s (run program fuel s).final := by
  induction fuel generalizing s with
  | zero => exact Frame.refl s
  | succ fuel ih =>
    cases hs : step program s with
    | none => simpa [run, hs] using Frame.refl s
    | some t =>
      obtain ⟨hb, _, i, _, hi, ha⟩ := step_spec hs
      obtain ⟨j, hj, hjaction⟩ := uses t (by simp [run, hs])
      have hij : i = j := Action.instruction.inj (hi.symm.trans hjaction)
      subst j
      have first : Frame s t.after := by rw [ha]; exact instruction_frame s base bound i hj
      have tail : UsesCode base bound (run program fuel t.after) := by
        intro u hu; exact uses u (by simp [run, hs, hu])
      simpa [run, hs] using first.trans (ih tail)

theorem uses_prefix {program : List Instruction} {base : Nat} {bound : base + 14 < 2 ^ 32}
    {fuel preFuel : Nat} {s : State} (uses : UsesCode base bound (run program fuel s))
    (le : preFuel ≤ fuel) : UsesCode base bound (run program preFuel s) := by
  intro t ht
  have split : fuel = preFuel + (fuel - preFuel) := by omega
  apply uses t
  rw [split, run_add]
  exact List.mem_append_left _ ht

section HostedExecution

variable {program : List Instruction} {base : Nat} {bound : base + 14 < 2 ^ 32}
variable (host : Hosted program base bound)
include host

theorem setup {s : State} {B M : Nat}
    (hr : s.core.status = .running) (hpc : s.core.pc = base) (he : s.core.extent = B + M)
    (hb : s.core.regs 0 = B) (hm : s.core.regs 2 = M) :
    CopyInv base s.core.memory B M 0 (run program 3 s).final ∧
      (run program 3 s).transitions.length = 3 := by
  have get : ∀ i, i < 14 → program[base + i]? = (code base bound)[i]? := host
  simp [run, step, fetch_zero host, get, code, execute, execPrim, hr, hpc, he, hb, hm,
    PackedConstruction.State.writeNext, PackedConstruction.State.next, put, CopyInv, Nat.add_assoc]

theorem copy_step {s : State} {original : Memory} {B M i : Nat}
    (hi : i < M) (hinv : CopyInv base original B M i s)
    (hinit : Initialized original B M) :
    CopyInv base original B M (i + 1) (run program 7 s).final ∧
      (run program 7 s).transitions.length = 7 := by
  obtain ⟨hr, hpc, he, h0, h1, h2, h3, h4, hdone, hfuture⟩ := hinv
  obtain ⟨v, hv⟩ := hinit i hi
  have hm : s.core.memory (B + i) = some v := (hfuture _ (by omega)).trans hv
  have hz : M - i ≠ 0 := by omega
  have hin : B + i < B + M := by omega
  have hdst : i < B + M := by omega
  have hdec : M - i - 1 = M - (i + 1) := by omega
  have get : ∀ j, j < 14 → program[base + j]? = (code base bound)[j]? := host
  simp [run, step, get, code, execute, execPrim, hr, hpc, he, h0, h1, h2,
    h3, h4, hz, hin, hdst, hm, PackedConstruction.State.writeNext, PackedConstruction.State.next,
    put, Arithmetic.eval, CopyInv, hdec, Nat.add_assoc]
  constructor
  · intro j hj
    by_cases hji : j = i
    · subst j; simp [hv]
    · simp [hji, hdone j (by omega)]
  · intro a ha
    simp [show a ≠ i by omega, hfuture a (by omega)]

theorem copy_exit {s : State} {original : Memory} {B M : Nat}
    (hinv : CopyInv base original B M M s)
    (htail : ∀ a, B + M ≤ a → original a = none) :
    ReleaseInv base original B M B (run program 1 s).final ∧
      (run program 1 s).transitions.length = 1 := by
  obtain ⟨hr, hpc, he, h0, h1, h2, h3, h4, hdone, hfuture⟩ := hinv
  have get : ∀ j, j < 14 → program[base + j]? = (code base bound)[j]? := host
  simp [ReleaseInv, run, step, get, code, execute, execPrim, hr, hpc, he, h0, h1, h2,
    h3, h4, hdone, Nat.add_comm, CleanTail, PackedConstruction.CleanTail]
  refine ⟨hdone, ?_⟩
  intro a ha
  exact (hfuture a (by omega)).trans (htail a (by omega))

theorem release_step {s : State} {original : Memory} {B M left : Nat}
    (hl : 0 < left) (hinv : ReleaseInv base original B M left s) :
    ReleaseInv base original B M (left - 1) (run program 4 s).final ∧
      (run program 4 s).transitions.length = 4 := by
  obtain ⟨hr, hpc, he, h1, h3, h4, hdone, htail⟩ := hinv
  have hz : left ≠ 0 := by omega
  have hez : M + left ≠ 0 := by omega
  have get : ∀ j, j < 14 → program[base + j]? = (code base bound)[j]? := host
  simp [ReleaseInv, run, step, get, code, execute, execPrim, hr, hpc, he, h1, h3, h4,
    hz, hez, PackedConstruction.State.next, PackedConstruction.State.writeNext, put,
    Arithmetic.eval, CleanTail, PackedConstruction.CleanTail, Nat.add_assoc]
  refine ⟨by omega, ?_, ?_⟩
  · intro j hj
    simp [show j ≠ M + left - 1 by omega, hdone j hj]
  · intro a ha hne
    exact htail a (by omega)

theorem release_continue {s : State} {original : Memory} {B M : Nat}
    (hinv : ReleaseInv base original B M 0 s) :
    FinalOutput original B M (run program 1 s).final ∧
      (run program 1 s).final.core.status = .running ∧
      (run program 1 s).final.core.pc = base + 14 ∧
      (run program 1 s).transitions.length = 1 := by
  obtain ⟨hr, hpc, he, h1, h3, h4, hdone, htail⟩ := hinv
  have get : ∀ j, j < 14 → program[base + j]? = (code base bound)[j]? := host
  simpa [FinalOutput, run, step, get, code, execute, execPrim, hr, hpc, he, h1, h3,
    CleanTail, PackedConstruction.CleanTail] using And.intro hdone htail

theorem copy_prefix {n i B M : Nat} {s : State} {original : Memory}
    (hcount : i + n ≤ M) (hinv : CopyInv base original B M i s)
    (hinit : Initialized original B M) :
    CopyInv base original B M (i + n) (run program (7 * n) s).final ∧
      (run program (7 * n) s).transitions.length = 7 * n := by
  induction n generalizing i s with
  | zero => exact ⟨by simpa [run] using hinv, rfl⟩
  | succ n ih =>
    have hi : i < M := by omega
    obtain ⟨hnext, hlen⟩ := copy_step host hi hinv hinit
    obtain ⟨hin, hlen'⟩ := ih (by omega) hnext
    rw [show 7 * (n + 1) = 7 + 7 * n by omega, run_add]
    exact ⟨by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hin,
      by simp only [List.length_append, hlen, hlen']⟩

theorem release_prefix {n left B M : Nat} {s : State} {original : Memory}
    (hn : n ≤ left) (hinv : ReleaseInv base original B M left s) :
    ReleaseInv base original B M (left - n) (run program (4 * n) s).final ∧
      (run program (4 * n) s).transitions.length = 4 * n := by
  induction n generalizing left s with
  | zero => exact ⟨by simpa [run] using hinv, rfl⟩
  | succ n ih =>
    obtain ⟨hnext, hlen⟩ := release_step host (by omega : 0 < left) hinv
    obtain ⟨hin, hlen'⟩ := ih (by omega) hnext
    rw [show 4 * (n + 1) = 4 + 4 * n by omega, run_add]
    exact ⟨by simpa [Nat.sub_sub, Nat.add_comm] using hin,
      by simp only [List.length_append, hlen, hlen']⟩

theorem release_entry {s : State} {B M : Nat} (entry : Entry base B M s) :
    ReleaseInv base s.core.memory B M B (run program (4 + 7 * M) s).final ∧
      (run program (4 + 7 * M) s).transitions.length = 4 + 7 * M := by
  obtain ⟨hr, hpc, he, hb, hm, hinit, htail⟩ := entry
  obtain ⟨hinv0, hlen0⟩ := setup host hr hpc he hb hm
  obtain ⟨hinv1, hlen1⟩ := copy_prefix host (by omega : 0 + M ≤ M) hinv0 hinit
  simp only [Nat.zero_add] at hinv1
  obtain ⟨hinv2, hlen2⟩ := copy_exit host hinv1 (by simpa [CleanTail, PackedConstruction.CleanTail, he] using htail)
  rw [show 4 + 7 * M = 3 + (7 * M + 1) by omega]
  simp only [run_add]
  exact ⟨hinv2, by simp [hlen0, hlen1, hlen2]⟩

/-- Completion is reached by execution, before any continuation instruction runs. -/
theorem finalizer {s : State} {B M : Nat} (entry : Entry base B M s) :
    let actual := run program (cost B M) s
    FinalOutput s.core.memory B M actual.final ∧ actual.final.core.status = .running ∧
      actual.final.core.pc = base + 14 ∧ actual.transitions.length = cost B M := by
  obtain ⟨hinv, hlen⟩ := release_entry host entry
  obtain ⟨hinv0, hlen0⟩ := release_prefix host (Nat.le_refl B) hinv
  obtain ⟨hout, hr, hpc, hlen1⟩ := release_continue host (by simpa using hinv0)
  rw [show cost B M = (4 + 7 * M) + (4 * B + 1) by simp [cost]; omega]
  rw [run_add program (4 + 7 * M) (4 * B + 1)]
  dsimp only
  rw [run_add program (4 * B) 1]
  exact ⟨hout, hr, hpc, by simp [hlen, hlen0, hlen1]⟩

theorem setup_good {s : State} {B M W : Nat}
    (hw : 32 ≤ W) (hr : s.core.status = .running) (hpc : s.core.pc = base)
    (hb : s.core.regs 0 = B) (_hm : s.core.regs 2 = M) :
    Good W program (run program 3 s) := by
  have get : ∀ j, j < 14 → program[base + j]? = (code base bound)[j]? := host
  simp [Good, run, step, fetch_zero host, get, code, execute, execPrim, hr, hpc, hb,
    PackedConstruction.State.writeNext, PackedConstruction.State.next, put, Transition.Safe,
    Instruction.Safe, Prim.Safe, Prim.SafeAt, Prim.operandsFit_of_width _ hw, Nat.add_assoc]

theorem copy_good {s : State} {original : Memory} {B M i W : Nat}
    (hw : 32 ≤ W) (cont : base + 14 < program.length)
    (hcap : B + M < 2 ^ W) (hfit : s.Fits W)
    (hi : i < M) (hinv : CopyInv base original B M i s)
    (hinit : Initialized original B M) : Good W program (run program 7 s) := by
  obtain ⟨hr, hpc, he, h0, h1, h2, h3, h4, _, hfuture⟩ := hinv
  obtain ⟨v, hv⟩ := hinit i hi
  have hm : s.core.memory (B + i) = some v := (hfuture _ (by omega)).trans hv
  have hvw := hfit.1.2.2.2.1 _ _ hm
  have hz : M - i ≠ 0 := by omega
  have hin : B + i < B + M := by omega
  have hdst : i < B + M := by omega
  have get : ∀ j, j < 14 → program[base + j]? = (code base bound)[j]? := host
  simp [Good, run, step, get, code, execute, execPrim, hr, hpc, he, h0, h1, h2,
    h3, h4, hz, hin, hdst, hm, PackedConstruction.State.writeNext, PackedConstruction.State.next, put,
    Arithmetic.eval, Transition.Safe, Instruction.Safe, Prim.Safe, Prim.SafeAt,
    Prim.operandsFit_of_width _ hw, Nat.add_assoc]
  omega

theorem copy_exit_good {s : State} {original : Memory} {B M W : Nat}
    (hw : 32 ≤ W) (cont : base + 14 < program.length)
    (hinv : CopyInv base original B M M s) : Good W program (run program 1 s) := by
  obtain ⟨hr, hpc, _, _, _, h2, _, _, _, _⟩ := hinv
  have get : ∀ j, j < 14 → program[base + j]? = (code base bound)[j]? := host
  simp [Good, run, step, get, code, execute, execPrim, hr, hpc, h2,
    Transition.Safe, Instruction.Safe, Prim.Safe, Prim.SafeAt, Prim.operandsFit_of_width _ hw]
  omega

theorem release_good {s : State} {original : Memory} {B M left W : Nat}
    (hw : 32 ≤ W) (cont : base + 14 < program.length) (hfit : s.Fits W)
    (hl : 0 < left) (hinv : ReleaseInv base original B M left s) :
    Good W program (run program 4 s) := by
  obtain ⟨hr, hpc, he, h1, h3, h4, _, _⟩ := hinv
  have hz : left ≠ 0 := by omega
  have hez : M + left ≠ 0 := by omega
  have hw32 : 2 ^ 32 ≤ 2 ^ W := Nat.pow_le_pow_right (by decide) hw
  have hleft := hfit.1.1 3
  rw [h3] at hleft
  have get : ∀ j, j < 14 → program[base + j]? = (code base bound)[j]? := host
  simp [Good, run, step, get, code, execute, execPrim, hr, hpc, he, h1, h3, h4,
    hz, hez, PackedConstruction.State.next, PackedConstruction.State.writeNext, put, Arithmetic.eval,
    Transition.Safe, Instruction.Safe, Prim.Safe, Prim.SafeAt, Prim.operandsFit_of_width _ hw,
    Nat.add_assoc]
  omega

theorem release_continue_good {s : State} {original : Memory} {B M W : Nat}
    (hw : 32 ≤ W) (cont : base + 14 < program.length)
    (hinv : ReleaseInv base original B M 0 s) : Good W program (run program 1 s) := by
  obtain ⟨hr, hpc, _, _, h3, _, _, _⟩ := hinv
  have get : ∀ j, j < 14 → program[base + j]? = (code base bound)[j]? := host
  simp [Good, run, step, get, code, execute, execPrim, hr, hpc, h3,
    Transition.Safe, Instruction.Safe, Prim.Safe, Prim.SafeAt, Prim.operandsFit_of_width _ hw, cont]

theorem copy_prefix_good {n i B M W : Nat} {s : State} {original : Memory}
    (hw : 32 ≤ W) (cont : base + 14 < program.length) (plen : program.length < 2 ^ W)
    (hcap : B + M < 2 ^ W) (hfit : s.Fits W)
    (hcount : i + n ≤ M) (hinv : CopyInv base original B M i s)
    (hinit : Initialized original B M) : Good W program (run program (7 * n) s) := by
  induction n generalizing i s with
  | zero => simp [Good, run]
  | succ n ih =>
    have hi : i < M := by omega
    have hnext := (copy_step host hi hinv hinit).1
    have hg := copy_good host hw cont hcap hfit hi hinv hinit
    have hf := (run_fits hfit plen hg).1
    have hg' := ih hf (by omega) hnext
    rw [show 7 * (n + 1) = 7 + 7 * n by omega, run_add]
    exact fun t ht => (List.mem_append.mp ht).elim (hg t) (hg' t)

theorem release_prefix_good {n left B M W : Nat} {s : State} {original : Memory}
    (hw : 32 ≤ W) (cont : base + 14 < program.length) (plen : program.length < 2 ^ W)
    (hfit : s.Fits W) (hn : n ≤ left) (hinv : ReleaseInv base original B M left s) :
    Good W program (run program (4 * n) s) := by
  induction n generalizing left s with
  | zero => simp [Good, run]
  | succ n ih =>
    have hl : 0 < left := by omega
    have hnext := (release_step host hl hinv).1
    have hg := release_good host hw cont hfit hl hinv
    have hf := (run_fits hfit plen hg).1
    have hg' := ih hf (by omega) hnext
    rw [show 4 * (n + 1) = 4 + 4 * n by omega, run_add]
    exact fun t ht => (List.mem_append.mp ht).elim (hg t) (hg' t)

theorem finalizer_safe {s : State} {B M W : Nat}
    (hw : 32 ≤ W) (cont : base + 14 < program.length) (plen : program.length < 2 ^ W)
    (hfit : s.Fits W) (entry : Entry base B M s) :
    Good W program (run program (cost B M) s) ∧
      (run program (cost B M) s).final.Fits W ∧
      ∀ t ∈ (run program (cost B M) s).transitions, t.before.Fits W ∧ t.after.Fits W := by
  obtain ⟨hr, hpc, he, hb, hm, hinit, htail⟩ := entry
  have hcap : B + M < 2 ^ W := he ▸ hfit.1.2.2.1
  obtain ⟨hi0, _⟩ := setup host hr hpc he hb hm
  have hg0 := setup_good host hw hr hpc hb hm
  have hf0 := (run_fits hfit plen hg0).1
  have hi1 := (copy_prefix host (by omega : 0 + M ≤ M) hi0 hinit).1
  have hg1 := copy_prefix_good host hw cont plen hcap hf0 (by omega : 0 + M ≤ M) hi0 hinit
  have hf1 := (run_fits hf0 plen hg1).1
  simp only [Nat.zero_add] at hi1
  have hi2 := (copy_exit host hi1 (by simpa [CleanTail, PackedConstruction.CleanTail, he] using htail)).1
  have hg2 := copy_exit_good host hw cont hi1
  have hf2 := (run_fits hf1 plen hg2).1
  have hi3 := (release_prefix host (Nat.le_refl B) hi2).1
  have hg3 := release_prefix_good host hw cont plen hf2 (Nat.le_refl B) hi2
  have hf3 := (run_fits hf2 plen hg3).1
  have hg4 := release_continue_good host hw cont (by simpa using hi3)
  have hg : Good W program (run program (cost B M) s) := by
    rw [show cost B M = 3 + (7 * M + (1 + (4 * B + 1))) by simp [cost]; omega]
    simp only [run_add]
    intro t ht
    simp only [List.mem_append] at ht
    rcases ht with ht | ht | ht | ht | ht
    · exact hg0 t ht
    · exact hg1 t ht
    · exact hg2 t ht
    · exact hg3 t ht
    · exact hg4 t ht
  exact ⟨hg, run_fits hfit plen hg⟩

theorem setup_uses {s : State}
    (hr : s.core.status = .running) (hpc : s.core.pc = base) :
    UsesCode base bound (run program 3 s) := by
  have get : ∀ j, j < 14 → program[base + j]? = (code base bound)[j]? := host
  simp [UsesCode, run, step, fetch_zero host, get, code, execute, execPrim, hr, hpc,
    PackedConstruction.State.writeNext, PackedConstruction.State.next, put, Nat.add_assoc]

theorem copy_uses {s : State} {original : Memory} {B M i : Nat}
    (hi : i < M) (hinv : CopyInv base original B M i s) (hinit : Initialized original B M) :
    UsesCode base bound (run program 7 s) := by
  obtain ⟨hr, hpc, he, h0, h1, h2, h3, h4, _, hfuture⟩ := hinv
  obtain ⟨v, hv⟩ := hinit i hi
  have hm : s.core.memory (B + i) = some v := (hfuture _ (by omega)).trans hv
  have hz : M - i ≠ 0 := by omega
  have hin : B + i < B + M := by omega
  have hdst : i < B + M := by omega
  have get : ∀ j, j < 14 → program[base + j]? = (code base bound)[j]? := host
  simp [UsesCode, run, step, get, code, execute, execPrim, hr, hpc, he, h0, h1, h2,
    h3, h4, hz, hin, hdst, hm, PackedConstruction.State.writeNext, PackedConstruction.State.next,
    put, Arithmetic.eval, Nat.add_assoc]

theorem copy_exit_uses {s : State} {original : Memory} {B M : Nat}
    (hinv : CopyInv base original B M M s) : UsesCode base bound (run program 1 s) := by
  obtain ⟨hr, hpc, _, _, _, h2, _, _, _, _⟩ := hinv
  have get : ∀ j, j < 14 → program[base + j]? = (code base bound)[j]? := host
  simp [UsesCode, run, step, get, code, execute, execPrim, hr, hpc, h2]

theorem release_uses {s : State} {original : Memory} {B M left : Nat}
    (hl : 0 < left) (hinv : ReleaseInv base original B M left s) :
    UsesCode base bound (run program 4 s) := by
  obtain ⟨hr, hpc, he, h1, h3, h4, _, _⟩ := hinv
  have hz : left ≠ 0 := by omega
  have hez : M + left ≠ 0 := by omega
  have get : ∀ j, j < 14 → program[base + j]? = (code base bound)[j]? := host
  simp [UsesCode, run, step, get, code, execute, execPrim, hr, hpc, he, h1, h3, h4,
    hz, hez, PackedConstruction.State.next, PackedConstruction.State.writeNext, put,
    Arithmetic.eval, Nat.add_assoc]

theorem release_continue_uses {s : State} {original : Memory} {B M : Nat}
    (hinv : ReleaseInv base original B M 0 s) : UsesCode base bound (run program 1 s) := by
  obtain ⟨hr, hpc, _, _, h3, _, _, _⟩ := hinv
  have get : ∀ j, j < 14 → program[base + j]? = (code base bound)[j]? := host
  simp [UsesCode, run, step, get, code, execute, execPrim, hr, hpc, h3]

theorem copy_prefix_uses {n i B M : Nat} {s : State} {original : Memory}
    (hcount : i + n ≤ M) (hinv : CopyInv base original B M i s)
    (hinit : Initialized original B M) : UsesCode base bound (run program (7 * n) s) := by
  induction n generalizing i s with
  | zero => simp [UsesCode, run]
  | succ n ih =>
    have hi : i < M := by omega
    have hnext := (copy_step host hi hinv hinit).1
    have hg := copy_uses host hi hinv hinit
    have hg' := ih (by omega) hnext
    rw [show 7 * (n + 1) = 7 + 7 * n by omega, run_add]
    exact fun t ht => (List.mem_append.mp ht).elim (hg t) (hg' t)

theorem release_prefix_uses {n left B M : Nat} {s : State} {original : Memory}
    (hn : n ≤ left) (hinv : ReleaseInv base original B M left s) :
    UsesCode base bound (run program (4 * n) s) := by
  induction n generalizing left s with
  | zero => simp [UsesCode, run]
  | succ n ih =>
    have hl : 0 < left := by omega
    have hnext := (release_step host hl hinv).1
    have hg := release_uses host hl hinv
    have hg' := ih (by omega) hnext
    rw [show 4 * (n + 1) = 4 + 4 * n by omega, run_add]
    exact fun t ht => (List.mem_append.mp ht).elim (hg t) (hg' t)

theorem finalizer_uses {s : State} {B M : Nat} (entry : Entry base B M s) :
    UsesCode base bound (run program (cost B M) s) := by
  obtain ⟨hr, hpc, he, hb, hm, hinit, htail⟩ := entry
  have hi0 := (setup host hr hpc he hb hm).1
  have hi1 := (copy_prefix host (by omega : 0 + M ≤ M) hi0 hinit).1
  simp only [Nat.zero_add] at hi1
  have hi2 := (copy_exit host hi1 (by simpa [CleanTail, PackedConstruction.CleanTail, he] using htail)).1
  have hi3 := (release_prefix host (Nat.le_refl B) hi2).1
  have h0 := setup_uses host hr hpc
  have h1 := copy_prefix_uses host (by omega : 0 + M ≤ M) hi0 hinit
  have h2 := copy_exit_uses host hi1
  have h3 := release_prefix_uses host (Nat.le_refl B) hi2
  have h4 := release_continue_uses host (by simpa using hi3)
  rw [show cost B M = 3 + (7 * M + (1 + (4 * B + 1))) by simp [cost]; omega]
  simp only [run_add]
  intro t ht
  simp only [List.mem_append] at ht
  rcases ht with ht | ht | ht | ht | ht
  · exact h0 t ht
  · exact h1 t ht
  · exact h2 t ht
  · exact h3 t ht
  · exact h4 t ht

theorem finalizer_frame {s : State} {B M : Nat} (entry : Entry base B M s) :
    Frame s (run program (cost B M) s).final ∧
      ∀ fuel, fuel ≤ cost B M → Frame s (run program fuel s).final := by
  have uses := finalizer_uses host entry
  exact ⟨run_frame_of_uses uses, fun _ le => run_frame_of_uses (uses_prefix uses le)⟩

/-- The whole memory function is identified, including every absent tail address. -/
theorem finalizer_memory (cells : List Nat) {s : State} {B : Nat}
    (entry : Entry base B cells.length s)
    (producer : ∀ i, i < cells.length → s.core.memory (B + i) = cells[i]?) :
    (run program (cost B cells.length) s).final.core.memory = (fun a => cells[a]?) ∧
      (run program (cost B cells.length) s).final.core.extent = cells.length ∧
      (run program (cost B cells.length) s).final.core.status = .running ∧
      (run program (cost B cells.length) s).final.core.pc = base + 14 := by
  obtain ⟨output, running, pc, _⟩ := finalizer host entry
  refine ⟨?_, output.1, running, pc⟩
  funext a
  by_cases ha : a < cells.length
  · exact (output.2.1 a ha).trans (producer a ha)
  · rw [output.2.2 a (by rw [output.1]; omega)]
    exact (List.getElem?_eq_none_iff.mpr (by omega)).symm

theorem copy_step_receipts {s : State} {original : Memory} {B M i : Nat}
    (hi : i < M) (hinv : CopyInv base original B M i s) (hinit : Initialized original B M) :
    ∃ load store, (run program 7 s).transitions[1]? = some load ∧
      (run program 7 s).transitions[2]? = some store ∧ CopyReceipt original B i load store := by
  obtain ⟨hr, hpc, he, h0, h1, h2, h3, h4, _, hfuture⟩ := hinv
  obtain ⟨v, hv⟩ := hinit i hi
  have hm : s.core.memory (B + i) = some v := (hfuture _ (by omega)).trans hv
  have hz : M - i ≠ 0 := by omega
  have hin : B + i < B + M := by omega
  have hdst : i < B + M := by omega
  have get : ∀ j, j < 14 → program[base + j]? = (code base bound)[j]? := host
  let pre : State := { s with core := { s.core with pc := base + 4 } }
  let loaded := execute (.old (.load 5 0)) pre
  let stored := execute (.old (.store 1 5)) loaded
  refine ⟨⟨pre, .instruction (.old (.load 5 0)), loaded⟩,
    ⟨loaded, .instruction (.old (.store 1 5)), stored⟩, ?_⟩
  simp [run, step, get, code, execute, execPrim, hr, hpc, he, h0, h1, h2,
    h3, h4, hz, hin, hdst, hm, PackedConstruction.State.writeNext, PackedConstruction.State.next, put,
    Arithmetic.eval, CopyReceipt, Transition.read?, Transition.write?, hv, pre, loaded, stored, Nat.add_assoc]

/-- Occurrence indices retain repeated values and the load-to-store dependence. -/
theorem ordered_copy {s : State} {B M : Nat} (entry : Entry base B M s) :
    ∀ i, i < M → ∃ load store,
      (run program (cost B M) s).transitions[4 + 7 * i]? = some load ∧
      (run program (cost B M) s).transitions[5 + 7 * i]? = some store ∧
      CopyReceipt s.core.memory B i load store ∧
      load.before = (run program (4 + 7 * i) s).final ∧ step program load.before = some load ∧
      store.before = (run program (5 + 7 * i) s).final ∧ step program store.before = some store := by
  obtain ⟨hr, hpc, he, hb, hm, hinit, _⟩ := entry
  intro i hi
  obtain ⟨hinv0, hlen0⟩ := setup host hr hpc he hb hm
  obtain ⟨hinvi, hleni⟩ := copy_prefix host (by omega : 0 + i ≤ M) hinv0 hinit
  simp only [Nat.zero_add] at hinvi
  obtain ⟨load, store, hl, hs, hc⟩ := copy_step_receipts host hi hinvi hinit
  have hprefix : (run program (3 + 7 * i) s).transitions.length = 3 + 7 * i := by
    rw [run_add]; simp [hlen0, hleni]
  have hl' : (run program 7 (run program (3 + 7 * i) s).final).transitions[1]? = some load := by
    simpa only [run_add] using hl
  have hs' : (run program 7 (run program (3 + 7 * i) s).final).transitions[2]? = some store := by
    simpa only [run_add] using hs
  have hsplit : cost B M = (3 + 7 * i) + (7 + (cost B M - (3 + 7 * i + 7))) := by simp [cost]; omega
  have hload : (run program (cost B M) s).transitions[4 + 7 * i]? = some load := by
    rw [hsplit]
    have hp := run_prefix_at (c := cost B M - (3 + 7 * i + 7)) hprefix hl'
    rwa [show 3 + 7 * i + 1 = 4 + 7 * i by omega] at hp
  have hstore : (run program (cost B M) s).transitions[5 + 7 * i]? = some store := by
    rw [hsplit]
    have hp := run_prefix_at (c := cost B M - (3 + 7 * i + 7)) hprefix hs'
    rwa [show 3 + 7 * i + 2 = 5 + 7 * i by omega] at hp
  exact ⟨load, store, hload, hstore, hc, (run_transition_at hload).1,
    (run_transition_at hload).2, run_transition_at hstore⟩

theorem release_step_receipt {s : State} {original : Memory} {B M left : Nat}
    (hl : 0 < left) (hinv : ReleaseInv base original B M left s) :
    ∃ t, (run program 4 s).transitions[1]? = some t ∧ ReleaseReceipt (M + left - 1) t := by
  obtain ⟨hr, hpc, he, h1, h3, h4, _, _⟩ := hinv
  have hz : left ≠ 0 := by omega
  have hez : M + left ≠ 0 := by omega
  have get : ∀ j, j < 14 → program[base + j]? = (code base bound)[j]? := host
  let pre : State := { s with core := { s.core with pc := base + 11 } }
  refine ⟨⟨pre, .instruction .releaseCell, execute .releaseCell pre⟩, ?_⟩
  simp [run, step, get, code, execute, execPrim, hr, hpc, he, h1, h3, h4,
    hz, hez, PackedConstruction.State.next, PackedConstruction.State.writeNext, put, Arithmetic.eval,
    ReleaseReceipt, pre, Nat.add_assoc]
  exact ⟨by omega, fun _ hne heq => False.elim (hne heq)⟩

theorem ordered_release {s : State} {B M : Nat} (entry : Entry base B M s) :
    ∀ k, k < B → ∃ t,
      (run program (cost B M) s).transitions[5 + 7 * M + 4 * k]? = some t ∧
      ReleaseReceipt (M + (B - k) - 1) t ∧
      t.before = (run program (5 + 7 * M + 4 * k) s).final ∧ step program t.before = some t := by
  intro k hk
  obtain ⟨hinv, hlen⟩ := release_entry host entry
  obtain ⟨hinvk, hlenk⟩ := release_prefix host (by omega : k ≤ B) hinv
  obtain ⟨t, ht, hc⟩ := release_step_receipt host (by omega : 0 < B - k) hinvk
  have hprefix : (run program ((4 + 7 * M) + 4 * k) s).transitions.length = (4 + 7 * M) + 4 * k := by
    rw [run_add]; simp [hlen, hlenk]
  have ht' : (run program 4 (run program ((4 + 7 * M) + 4 * k) s).final).transitions[1]? = some t := by
    simpa only [run_add] using ht
  have hsplit : cost B M = ((4 + 7 * M) + 4 * k) + (4 + (cost B M - ((4 + 7 * M) + 4 * k + 4))) := by
    simp [cost]; omega
  have occurrence : (run program (cost B M) s).transitions[5 + 7 * M + 4 * k]? = some t := by
    rw [hsplit]
    have hp := run_prefix_at (c := cost B M - ((4 + 7 * M) + 4 * k + 4)) hprefix ht'
    rwa [show 4 + 7 * M + 4 * k + 1 = 5 + 7 * M + 4 * k by omega] at hp
  exact ⟨t, occurrence, hc, run_transition_at occurrence⟩

theorem setup_categories {s : State}
    (hr : s.core.status = .running) (hpc : s.core.pc = base) :
    (run program 3 s).categories = [.old .register, .old .register, .old .register] := by
  have get : ∀ j, j < 14 → program[base + j]? = (code base bound)[j]? := host
  simp [Run.categories, Action.category, Prim.category, run, step, fetch_zero host, get, code,
    execute, execPrim, hr, hpc, PackedConstruction.State.writeNext, PackedConstruction.State.next,
    put, Nat.add_assoc]

theorem copy_categories {s : State} {original : Memory} {B M i : Nat}
    (hi : i < M) (hinv : CopyInv base original B M i s) (hinit : Initialized original B M) :
    (run program 7 s).categories = copyCategories := by
  obtain ⟨hr, hpc, he, h0, h1, h2, h3, h4, _, hfuture⟩ := hinv
  obtain ⟨v, hv⟩ := hinit i hi
  have hm : s.core.memory (B + i) = some v := (hfuture _ (by omega)).trans hv
  have hz : M - i ≠ 0 := by omega
  have hin : B + i < B + M := by omega
  have hdst : i < B + M := by omega
  have get : ∀ j, j < 14 → program[base + j]? = (code base bound)[j]? := host
  simp [Run.categories, Action.category, Prim.category, copyCategories, run, step, get, code,
    execute, execPrim, hr, hpc, he, h0, h1, h2, h3, h4, hz, hin, hdst, hm,
    PackedConstruction.State.writeNext, PackedConstruction.State.next, put, Arithmetic.eval, Nat.add_assoc]

theorem copy_exit_categories {s : State} {original : Memory} {B M : Nat}
    (hinv : CopyInv base original B M M s) : (run program 1 s).categories = [.old .branch] := by
  obtain ⟨hr, hpc, _, _, _, h2, _, _, _, _⟩ := hinv
  have get : ∀ j, j < 14 → program[base + j]? = (code base bound)[j]? := host
  simp [Run.categories, Action.category, Prim.category, run, step, get, code, execute, execPrim,
    hr, hpc, h2]

theorem release_categories {s : State} {original : Memory} {B M left : Nat}
    (hl : 0 < left) (hinv : ReleaseInv base original B M left s) :
    (run program 4 s).categories = releaseCategories := by
  obtain ⟨hr, hpc, he, h1, h3, h4, _, _⟩ := hinv
  have hz : left ≠ 0 := by omega
  have hez : M + left ≠ 0 := by omega
  have get : ∀ j, j < 14 → program[base + j]? = (code base bound)[j]? := host
  simp [Run.categories, Action.category, Prim.category, releaseCategories, run, step, get, code,
    execute, execPrim, hr, hpc, he, h1, h3, h4, hz, hez,
    PackedConstruction.State.next, PackedConstruction.State.writeNext, put, Arithmetic.eval, Nat.add_assoc]

theorem release_continue_categories {s : State} {original : Memory} {B M : Nat}
    (hinv : ReleaseInv base original B M 0 s) : (run program 1 s).categories = [.old .branch] := by
  obtain ⟨hr, hpc, _, _, h3, _, _, _⟩ := hinv
  have get : ∀ j, j < 14 → program[base + j]? = (code base bound)[j]? := host
  simp [Run.categories, Action.category, Prim.category, run, step, get, code, execute, execPrim,
    hr, hpc, h3]

theorem copy_prefix_categories {n i B M : Nat} {s : State} {original : Memory}
    (hcount : i + n ≤ M) (hinv : CopyInv base original B M i s)
    (hinit : Initialized original B M) :
    (run program (7 * n) s).categories = (List.replicate n copyCategories).flatten := by
  induction n generalizing i s with
  | zero => rfl
  | succ n ih =>
    have hi : i < M := by omega
    have hnext := (copy_step host hi hinv hinit).1
    have hg := copy_categories host hi hinv hinit
    have hg' := ih (by omega) hnext
    rw [show 7 * (n + 1) = 7 + 7 * n by omega, run_add]
    simp only [Run.categories, List.map_append] at hg hg' ⊢
    rw [hg, hg', List.replicate_succ, List.flatten_cons]

theorem release_prefix_categories {n left B M : Nat} {s : State} {original : Memory}
    (hn : n ≤ left) (hinv : ReleaseInv base original B M left s) :
    (run program (4 * n) s).categories = (List.replicate n releaseCategories).flatten := by
  induction n generalizing left s with
  | zero => rfl
  | succ n ih =>
    have hl : 0 < left := by omega
    have hnext := (release_step host hl hinv).1
    have hg := release_categories host hl hinv
    have hg' := ih (by omega) hnext
    rw [show 4 * (n + 1) = 4 + 4 * n by omega, run_add]
    simp only [Run.categories, List.map_append] at hg hg' ⊢
    rw [hg, hg', List.replicate_succ, List.flatten_cons]

/-- The category sequence is computed from the same actual transitions. -/
theorem finalizer_categories {s : State} {B M : Nat} (entry : Entry base B M s) :
    (run program (cost B M) s).categories = expectedCategories B M := by
  obtain ⟨hr, hpc, he, hb, hm, hinit, htail⟩ := entry
  have hi0 := (setup host hr hpc he hb hm).1
  have hi1 := (copy_prefix host (by omega : 0 + M ≤ M) hi0 hinit).1
  simp only [Nat.zero_add] at hi1
  have hi2 := (copy_exit host hi1 (by simpa [CleanTail, PackedConstruction.CleanTail, he] using htail)).1
  have hi3 := (release_prefix host (Nat.le_refl B) hi2).1
  have h0 := setup_categories host hr hpc
  have h1 := copy_prefix_categories host (by omega : 0 + M ≤ M) hi0 hinit
  have h2 := copy_exit_categories host hi1
  have h3 := release_prefix_categories host (Nat.le_refl B) hi2
  have h4 := release_continue_categories host (by simpa using hi3)
  rw [show cost B M = 3 + (7 * M + (1 + (4 * B + 1))) by simp [cost]; omega]
  simp only [run_add, Run.categories, List.map_append] at h0 h1 h2 h3 h4 ⊢
  simp only [h0, h1, h2, h3, h4, expectedCategories, List.append_assoc]

omit host in
theorem count_replicated_flatten (pattern : List Category) (n : Nat) (category : Category) :
    ((List.replicate n pattern).flatten).count category = n * pattern.count category := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp [List.replicate_succ, List.flatten_cons, List.count_append, ih, Nat.succ_mul, Nat.add_comm]

theorem finalizer_category_counts {s : State} {B M : Nat} (entry : Entry base B M s) :
    let actual := run program (cost B M) s
    actual.categoryCount .numericRelease = B ∧
      actual.categoryCount (.old .read) = M ∧ actual.categoryCount (.old .write) = M ∧
      actual.categoryCount (.old .register) = 3 ∧
      actual.categoryCount (.old .arithmetic) = 3 * M + B ∧
      actual.categoryCount (.old .branch) = 2 * M + 2 * B + 2 := by
  dsimp only
  simp only [Run.categoryCount, finalizer_categories host entry]
  simp [expectedCategories, List.count_append, count_replicated_flatten,
    copyCategories, releaseCategories, Nat.mul_comm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  omega

theorem zero_base_has_no_releases {s : State} {M : Nat} (entry : Entry base 0 M s) :
    (run program (cost 0 M) s).categoryCount .numericRelease = 0 ∧
      (run program (cost 0 M) s).final.core.extent = M :=
  ⟨(finalizer_category_counts host entry).1, (finalizer host entry).1.1⟩

theorem zero_length_has_no_copy {s : State} {B : Nat} (entry : Entry base B 0 s) :
    (run program (cost B 0) s).categoryCount (.old .read) = 0 ∧
      (run program (cost B 0) s).categoryCount (.old .write) = 0 ∧
      (run program (cost B 0) s).final.core.extent = 0 :=
  ⟨(finalizer_category_counts host entry).2.1, (finalizer_category_counts host entry).2.2.1,
    (finalizer host entry).1.1⟩

theorem finalizer_prefix_fits {s : State} {B M W : Nat}
    (hw : 32 ≤ W) (cont : base + 14 < program.length) (plen : program.length < 2 ^ W)
    (hfit : s.Fits W) (entry : Entry base B M s) :
    ∀ fuel, fuel ≤ cost B M → (run program fuel s).final.Fits W := by
  obtain ⟨_, finalFit, each⟩ := finalizer_safe host hw cont plen hfit entry
  have length := (finalizer host entry).2.2.2
  intro fuel le
  by_cases lt : fuel < cost B M
  · have within : fuel < (run program (cost B M) s).transitions.length := by rw [length]; exact lt
    let t := (run program (cost B M) s).transitions[fuel]
    have occurrence : (run program (cost B M) s).transitions[fuel]? = some t :=
      List.getElem?_eq_getElem within
    rw [← (run_transition_at occurrence).1]
    exact (each t (List.mem_of_getElem? occurrence)).1
  · have equal : fuel = cost B M := by omega
    subst fuel
    exact finalFit

end HostedExecution

theorem code_inventory (base : Nat) (bound : base + 14 < 2 ^ 32) :
    (code base bound).length = 14 ∧
      ((code base bound).map Instruction.encoding).flatten.length = 46 := by
  exact ⟨rfl, rfl⟩

theorem code_fields (base : Nat) (bound : base + 14 < 2 ^ 32) (W : Nat) (hw : 32 ≤ W) :
    ∀ i ∈ code base bound, i.Fits W := by
  have cap : 2 ^ 32 ≤ 2 ^ W := Nat.pow_le_pow_right (by decide) hw
  intro i _
  cases i with
  | old p =>
    intro word member
    simp only [Instruction.encoding, List.mem_map] at member
    obtain ⟨operand, _, rfl⟩ := member
    exact Nat.lt_of_lt_of_le operand.isLt cap
  | releaseCell => simp [Instruction.Fits, Instruction.encoding]; omega
  | releaseKey => simp [Instruction.Fits, Instruction.encoding]; omega
  | releaseKeyRegister => simp [Instruction.Fits, Instruction.encoding]; omega

/-- A zero-extent release faults and preserves every other state component. -/
theorem release_zero_control (s : State) (zero : s.core.extent = 0) :
    execute .releaseCell s = { s with core := { s.core with status := .fault } } ∧
      (execute .releaseCell s).core.extent = 0 ∧
      (execute .releaseCell s).core.memory = s.core.memory ∧
      (execute .releaseCell s).core.pc = s.core.pc := by
  rw [releaseCell_zero s zero]
  exact ⟨rfl, zero, rfl, rfl⟩

theorem exact_domain {original : Memory} {B M : Nat} {s : State}
    (initialized : Initialized original B M) (output : FinalOutput original B M s) :
    ∀ a, s.core.memory a ≠ none ↔ a < M := by
  intro a
  obtain ⟨extent, values, tail⟩ := output
  constructor
  · intro present
    by_cases lt : a < M
    · exact lt
    · exact False.elim (present (tail a (by omega)))
  · intro lt
    obtain ⟨value, source⟩ := initialized a lt
    rw [values a lt, source]
    simp

end RMQ.SuccinctFinal.PackedLifecycle.Finalizer
