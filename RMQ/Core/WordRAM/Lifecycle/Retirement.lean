import RMQ.Core.WordRAM.Lifecycle.Safety

/-! # Charged retirement of comparison resources

This hosted fragment retires the separate input-key bank one cell at a time,
then retires its two key registers. Numeric allocation and request/metadata
registers survive unchanged. The word route already owns no comparison bank.
-/

namespace RMQ.SuccinctFinal.PackedLifecycle.Retirement

open PackedConstruction (Operand Prim execPrim put Arithmetic)
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

@[simp] theorem operand_six : (6 : Operand).val = 6 := rfl
@[simp] theorem operand_seven : (7 : Operand).val = 7 := rfl
@[simp] theorem operand_metadata : (302 : Operand).val = 302 := rfl

def code (base : Nat) (bound : base+8 < 2^32) : List Instruction := [
  .old (.move 6 302),
  .old (.constant 7 1),
  .old (.branchZero 6 ⟨base+6, by omega⟩),
  .releaseKey,
  .old (.arithmetic .sub 6 6 7),
  .old (.jump ⟨base+2, by omega⟩),
  .releaseKeyRegister,
  .releaseKeyRegister]

def Hosted (program : List Instruction) (base : Nat) (bound : base+8 < 2^32) : Prop :=
  ∀ i, i < 8 → program[base+i]? = (code base bound)[i]?

def Entry (base n : Nat) (s : State) : Prop :=
  s.core.status = .running ∧ s.core.pc = base ∧
  s.keyExtent = n ∧ s.keyRegExtent = 2 ∧ s.core.regs 302 = n ∧ s.Closed

def LoopInv (base left : Nat) (s : State) : Prop :=
  s.core.status = .running ∧ s.core.pc = base+2 ∧
  s.keyExtent = left ∧ s.keyRegExtent = 2 ∧ s.core.regs 6 = left ∧ s.core.regs 7 = 1

def cost (n : Nat) : Nat := 4*n+5

def Good (W : Nat) (program : List Instruction) (r : Run) : Prop :=
  ∀ t ∈ r.transitions, t.Safe W program.length

def UsesCode (base : Nat) (bound : base+8 < 2^32) (r : Run) : Prop :=
  ∀ t ∈ r.transitions, ∃ i ∈ code base bound, t.action = .instruction i

def cycleCategories : List Category :=
  [.old .branch, .keyRelease, .old .arithmetic, .old .branch]

def categories (n : Nat) : List Category :=
  [.old .register, .old .register] ++
    (List.replicate n cycleCategories).flatten ++
    [.old .branch, .keyRegisterRelease, .keyRegisterRelease]

section HostedExecution

variable {program : List Instruction} {base : Nat} {bound : base+8 < 2^32}
variable (host : Hosted program base bound)
include host

theorem fetch_zero : program[base]? = some (.old (.move 6 302)) := by
  simpa [code] using host 0 (by decide)

theorem setup {s : State} {n : Nat} (entry : Entry base n s) :
    LoopInv base n (run program 2 s).final ∧
      (run program 2 s).transitions.length = 2 ∧
      (run program 2 s).categories = [.old .register, .old .register] ∧
      UsesCode base bound (run program 2 s) := by
  obtain ⟨hr, hpc, hk, hkr, hn, _⟩ := entry
  have get : ∀ j, j < 8 → program[base+j]? = (code base bound)[j]? := host
  simp [run, step, fetch_zero host, get, code, execute, execPrim, hr, hpc, hk, hkr, hn,
    PackedConstruction.State.writeNext, PackedConstruction.State.next, put, LoopInv,
    Run.categories, Action.category, Prim.category, UsesCode, Nat.add_assoc]

theorem loop_step {s : State} {left : Nat} (hl : 0 < left) (inv : LoopInv base left s) :
    LoopInv base (left-1) (run program 4 s).final ∧
      (run program 4 s).transitions.length = 4 ∧
      (run program 4 s).categories = cycleCategories ∧
      UsesCode base bound (run program 4 s) := by
  obtain ⟨hr, hpc, hk, hkr, h6, h7⟩ := inv
  have hz : left ≠ 0 := by omega
  have get : ∀ j, j < 8 → program[base+j]? = (code base bound)[j]? := host
  simp [run, step, get, code, execute, execPrim, hr, hpc, hk, hkr, h6, h7, hz,
    PackedConstruction.State.writeNext, PackedConstruction.State.next, put, Arithmetic.eval,
    LoopInv, Run.categories, Action.category, Prim.category, cycleCategories, UsesCode,
    Nat.add_assoc]

theorem finish {s : State} (inv : LoopInv base 0 s) :
    (run program 3 s).final.core.status = .running ∧
      (run program 3 s).final.core.pc = base+8 ∧
      (run program 3 s).final.keyExtent = 0 ∧
      (run program 3 s).final.keyRegExtent = 0 ∧
      (run program 3 s).transitions.length = 3 ∧
      (run program 3 s).categories = [.old .branch, .keyRegisterRelease, .keyRegisterRelease] ∧
      UsesCode base bound (run program 3 s) := by
  obtain ⟨hr, hpc, hk, hkr, h6, _⟩ := inv
  have get : ∀ j, j < 8 → program[base+j]? = (code base bound)[j]? := host
  simp [run, step, get, code, execute, execPrim, hr, hpc, hk, hkr, h6,
    PackedConstruction.State.writeNext, PackedConstruction.State.next, put,
    Run.categories, Action.category, Prim.category, UsesCode, Nat.add_assoc]

theorem loop_prefix {s : State} {count left : Nat}
    (hc : count ≤ left) (inv : LoopInv base left s) :
    LoopInv base (left-count) (run program (4*count) s).final ∧
      (run program (4*count) s).transitions.length = 4*count ∧
      (run program (4*count) s).categories = (List.replicate count cycleCategories).flatten ∧
      UsesCode base bound (run program (4*count) s) := by
  induction count generalizing left s with
  | zero => exact ⟨by simpa [run] using inv, rfl, rfl, by simp [UsesCode, run]⟩
  | succ count ih =>
      have hl : 0 < left := by omega
      obtain ⟨next, len, cats, used⟩ := loop_step host hl inv
      obtain ⟨out, len', cats', used'⟩ := ih (by omega) next
      rw [show 4*(count+1)=4+4*count by omega, run_add]
      refine ⟨by simpa [Nat.sub_sub, Nat.add_comm] using out, by simp [len, len'], ?_, ?_⟩
      · simp only [Run.categories, List.map_append] at cats cats' ⊢
        rw [cats, cats']
        simp [List.replicate_succ, List.flatten_cons]
      · exact fun t ht => (List.mem_append.mp ht).elim (used t) (used' t)

theorem comparison_run {s : State} {n : Nat} (entry : Entry base n s) :
    let actual := run program (cost n) s
    actual.final.core.status = .running ∧ actual.final.core.pc = base+8 ∧
      actual.final.keyExtent = 0 ∧ actual.final.keyRegExtent = 0 ∧
      actual.transitions.length = cost n ∧ actual.categories = categories n ∧
      UsesCode base bound actual := by
  obtain ⟨init, len0, cats0, uses0⟩ := setup host entry
  obtain ⟨inv, len1, cats1, uses1⟩ := loop_prefix host (Nat.le_refl n) init
  obtain ⟨hr, hpc, hk, hkr, len2, cats2, uses2⟩ := finish host (by simpa using inv)
  rw [show cost n=2+(4*n+3) by simp [cost]; omega]
  simp only [run_add]
  refine ⟨hr, hpc, hk, hkr, ?_, ?_, ?_⟩
  · simp [List.length_append, len0, len1, len2]
  · simp only [Run.categories, List.map_append] at cats0 cats1 cats2 ⊢
    rw [cats0, cats1, cats2]
    simp [categories, List.append_assoc]
  · intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact uses0 t ht
    · exact (List.mem_append.mp ht).elim (uses1 t) (uses2 t)

theorem setup_good {s : State} {n W : Nat} (hw : 32 ≤ W) (entry : Entry base n s) :
    Good W program (run program 2 s) := by
  obtain ⟨hr, hpc, _, _, hn, _⟩ := entry
  have get : ∀ j, j < 8 → program[base+j]? = (code base bound)[j]? := host
  simp [Good, run, step, fetch_zero host, get, code, execute, execPrim, hr, hpc, hn,
    PackedConstruction.State.writeNext, PackedConstruction.State.next, put, Transition.Safe,
    Instruction.Safe, Prim.Safe, Prim.SafeAt, Prim.operandsFit_of_width _ hw, Nat.add_assoc]

theorem loop_good {s : State} {left W : Nat} (hw : 32 ≤ W)
    (cont : base+8 < program.length) (fit : s.Fits W)
    (hl : 0 < left) (inv : LoopInv base left s) : Good W program (run program 4 s) := by
  obtain ⟨hr, hpc, hk, hkr, h6, h7⟩ := inv
  have hz : left ≠ 0 := by omega
  have cap : left < 2^W := hk ▸ fit.2.1
  have hw32 : 2^32 ≤ 2^W := Nat.pow_le_pow_right (by decide) hw
  have get : ∀ j, j < 8 → program[base+j]? = (code base bound)[j]? := host
  simp [Good, run, step, get, code, execute, execPrim, hr, hpc, hk, hkr, h6, h7, hz,
    PackedConstruction.State.writeNext, PackedConstruction.State.next, put, Arithmetic.eval,
    Transition.Safe, Instruction.Safe, Prim.Safe, Prim.SafeAt,
    Prim.operandsFit_of_width _ hw, Nat.add_assoc]
  omega

theorem finish_good {s : State} {W : Nat} (hw : 32 ≤ W)
    (cont : base+8 < program.length) (inv : LoopInv base 0 s) :
    Good W program (run program 3 s) := by
  obtain ⟨hr, hpc, hk, hkr, h6, _⟩ := inv
  have hw32 : 2^32 ≤ 2^W := Nat.pow_le_pow_right (by decide) hw
  have get : ∀ j, j < 8 → program[base+j]? = (code base bound)[j]? := host
  simp [Good, run, step, get, code, execute, execPrim, hr, hpc, hk, hkr, h6,
    PackedConstruction.State.next, put, Transition.Safe, Instruction.Safe,
    Prim.Safe, Prim.SafeAt, Prim.operandsFit_of_width _ hw, Nat.add_assoc]
  omega

theorem loop_prefix_good {s : State} {count left W : Nat} (hw : 32 ≤ W)
    (cont : base+8 < program.length) (plen : program.length < 2^W)
    (fit : s.Fits W) (hc : count ≤ left) (inv : LoopInv base left s) :
    Good W program (run program (4*count) s) := by
  induction count generalizing left s with
  | zero => simp [Good, run]
  | succ count ih =>
      have hl : 0 < left := by omega
      have next := (loop_step host hl inv).1
      have hg := loop_good host hw cont fit hl inv
      have nextFit := (run_fits fit plen hg).1
      have rest := ih nextFit (by omega) next
      rw [show 4*(count+1)=4+4*count by omega, run_add]
      exact fun t ht => (List.mem_append.mp ht).elim (hg t) (rest t)

theorem comparison_safe {s : State} {n W : Nat} (hw : 32 ≤ W)
    (cont : base+8 < program.length) (plen : program.length < 2^W)
    (fit : s.Fits W) (entry : Entry base n s) :
    Good W program (run program (cost n) s) ∧
      (run program (cost n) s).final.Fits W ∧
      ∀ t ∈ (run program (cost n) s).transitions, t.before.Fits W ∧ t.after.Fits W := by
  have init := (setup host entry).1
  have hg0 := setup_good host hw entry
  have hf0 := (run_fits fit plen hg0).1
  have inv := (loop_prefix host (Nat.le_refl n) init).1
  have hg1 := loop_prefix_good host hw cont plen hf0 (Nat.le_refl n) init
  have hg2 := finish_good host hw cont (by simpa using inv)
  have good : Good W program (run program (cost n) s) := by
    rw [show cost n=2+(4*n+3) by simp [cost]; omega]
    simp only [run_add]
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact hg0 t ht
    · exact (List.mem_append.mp ht).elim (hg1 t) (hg2 t)
  exact ⟨good, run_fits fit plen good⟩

theorem setup_loop_prefix {s : State} {n count : Nat}
    (entry : Entry base n s) (hc : count ≤ n) :
    LoopInv base (n-count) (run program (2+4*count) s).final ∧
      (run program (2+4*count) s).transitions.length = 2+4*count := by
  obtain ⟨init, len0, _, _⟩ := setup host entry
  obtain ⟨inv, len, _, _⟩ := loop_prefix host hc init
  rw [run_add]
  exact ⟨inv, by simp [len0, len]⟩

end HostedExecution

def KeyReleaseReceipt (a : Nat) (t : Transition) : Prop :=
  t.action = .instruction .releaseKey ∧ t.before.keyExtent = a+1 ∧
    t.after.keyExtent = a ∧ t.after.core.keys a = none ∧
    (∀ other, other ≠ a → t.after.core.keys other = t.before.core.keys other) ∧
    t.after = execute .releaseKey t.before

def KeyRegisterReleaseReceipt (r : Nat) (t : Transition) : Prop :=
  t.action = .instruction .releaseKeyRegister ∧ t.before.keyRegExtent = r+1 ∧
    t.after.keyRegExtent = r ∧ t.after.core.keyRegs r = 0 ∧
    (∀ other, other ≠ r → t.after.core.keyRegs other = t.before.core.keyRegs other) ∧
    t.after = execute .releaseKeyRegister t.before

theorem run_prefix_at {program : List Instruction} {s : State} {a b c k : Nat}
    {t : Transition} (ha : (run program a s).transitions.length = a)
    (hk : (run program b (run program a s).final).transitions[k]? = some t) :
    (run program (a+(b+c)) s).transitions[a+k]? = some t := by
  simp only [run_add]
  rw [List.getElem?_append_right (by omega), ha, Nat.add_sub_cancel_left]
  have hlt := (List.getElem?_eq_some_iff.mp hk).1
  rw [List.getElem?_append_left hlt]
  exact hk

section ReleasePositions

variable {program : List Instruction} {base : Nat} {bound : base+8 < 2^32}
variable (host : Hosted program base bound)
include host

theorem loop_release {s : State} {left : Nat} (hl : 0 < left)
    (inv : LoopInv base left s) :
    ∃ t, (run program 4 s).transitions[1]? = some t ∧ KeyReleaseReceipt (left-1) t := by
  obtain ⟨hr, hpc, hk, hkr, h6, h7⟩ := inv
  have hz : left ≠ 0 := by omega
  have hleft : left-1+1 = left := by omega
  have get : ∀ j, j < 8 → program[base+j]? = (code base bound)[j]? := host
  let before := execute (.old (.branchZero 6 ⟨base+6, by omega⟩)) s
  refine ⟨⟨before, .instruction .releaseKey, execute .releaseKey before⟩, ?_, ?_⟩
  · simp [before, run, step, get, code, execute, execPrim, hr, hpc, hk, hkr, h6, h7,
      hz, PackedConstruction.State.next, Nat.add_assoc]
  · simp (config := {contextual := true}) [KeyReleaseReceipt, before, execute, execPrim,
      hk, h6, hz, hleft, PackedConstruction.State.next, put]

theorem finish_release {s : State} {j : Nat} (hj : j < 2) (inv : LoopInv base 0 s) :
    ∃ t, (run program 3 s).transitions[1+j]? = some t ∧ KeyRegisterReleaseReceipt (1-j) t := by
  obtain ⟨hr, hpc, hk, hkr, h6, _⟩ := inv
  have get : ∀ k, k < 8 → program[base+k]? = (code base bound)[k]? := host
  let before := execute (.old (.branchZero 6 ⟨base+6, by omega⟩)) s
  have cases : j=0 ∨ j=1 := by omega
  rcases cases with rfl | rfl
  · refine ⟨⟨before, .instruction .releaseKeyRegister,
      execute .releaseKeyRegister before⟩, ?_, ?_⟩
    · simp [before, run, step, get, code, execute, execPrim, hr, hpc, hk, hkr, h6,
        PackedConstruction.State.next, Nat.add_assoc]
    · simp (config := {contextual := true}) [KeyRegisterReleaseReceipt, before, execute, execPrim, hkr, h6,
        PackedConstruction.State.next, put]
  · let second := execute .releaseKeyRegister before
    refine ⟨⟨second, .instruction .releaseKeyRegister,
      execute .releaseKeyRegister second⟩, ?_, ?_⟩
    · simp [second, before, run, step, get, code, execute, execPrim, hr, hpc, hk, hkr, h6,
        PackedConstruction.State.next, Nat.add_assoc]
    · simp (config := {contextual := true}) [KeyRegisterReleaseReceipt, second, before, execute, execPrim, hkr, h6,
        PackedConstruction.State.next, put]

/-- Reverse extent order and trace position of every key-cell retirement. -/
theorem key_release_at {s : State} {n k : Nat} (entry : Entry base n s) (hk : k < n) :
    ∃ t, (run program (cost n) s).transitions[3+4*k]? = some t ∧
      t.before = (run program (3+4*k) s).final ∧ KeyReleaseReceipt (n-k-1) t := by
  obtain ⟨inv, len⟩ := setup_loop_prefix host entry (by omega : k ≤ n)
  obtain ⟨t, ht, receipt⟩ := loop_release host (by omega : 0 < n-k) inv
  have full := run_prefix_at (c := cost n-((2+4*k)+4)) len ht
  have hcost : (2+4*k)+(4+(cost n-((2+4*k)+4)))=cost n := by simp [cost]; omega
  have hindex : (2+4*k)+1=3+4*k := by omega
  rw [hcost, hindex] at full
  exact ⟨t, full, (run_transition_at full).1, receipt⟩

/-- Exactly the final two positions retire key registers one and zero. -/
theorem key_register_release_at {s : State} {n j : Nat} (entry : Entry base n s)
    (hj : j < 2) :
    ∃ t, (run program (cost n) s).transitions[4*n+3+j]? = some t ∧
      t.before = (run program (4*n+3+j) s).final ∧ KeyRegisterReleaseReceipt (1-j) t := by
  obtain ⟨inv, len⟩ := setup_loop_prefix host entry (Nat.le_refl n)
  obtain ⟨t, ht, receipt⟩ := finish_release host hj (by simpa using inv)
  have full := run_prefix_at (c := 0) len ht
  have hcost : (2+4*n)+(3+0)=cost n := by simp [cost]; omega
  have hindex : (2+4*n)+(1+j)=4*n+3+j := by omega
  rw [hcost, hindex] at full
  exact ⟨t, full, (run_transition_at full).1, receipt⟩

end ReleasePositions

@[simp] theorem code_length (base : Nat) (bound : base+8 < 2^32) :
    (code base bound).length = 8 := rfl

theorem code_fits {base W : Nat} {bound : base+8 < 2^32} (hw : 32 ≤ W)
    {i : Instruction} (_hi : i ∈ code base bound) : i.Fits W := by
  have hw32 : 2^32 ≤ 2^W := Nat.pow_le_pow_right (by decide) hw
  cases i with
  | old p =>
      intro word hword
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hword
      exact Nat.lt_of_lt_of_le v.isLt hw32
  | releaseCell => simp [Instruction.Fits, Instruction.encoding]; omega
  | releaseKey => simp [Instruction.Fits, Instruction.encoding]; omega
  | releaseKeyRegister => simp [Instruction.Fits, Instruction.encoding]; omega

def Frame (before after : State) : Prop :=
  after.core.memory = before.core.memory ∧ after.core.extent = before.core.extent ∧
    (∀ r, r ≠ 6 → r ≠ 7 → after.core.regs r = before.core.regs r)

theorem Frame.refl (s : State) : Frame s s := ⟨rfl, rfl, fun _ _ _ => rfl⟩

theorem Frame.trans {a b c : State} (h : Frame a b) (g : Frame b c) : Frame a c :=
  ⟨g.1.trans h.1, g.2.1.trans h.2.1, fun r h6 h7 => (g.2.2 r h6 h7).trans (h.2.2 r h6 h7)⟩

theorem Frame.descriptor {a b : State} (h : Frame a b) :
    b.core.regs 300 = a.core.regs 300 ∧ b.core.regs 301 = a.core.regs 301 ∧
      b.core.regs 302 = a.core.regs 302 :=
  ⟨h.2.2 300 (by decide) (by decide), h.2.2 301 (by decide) (by decide),
    h.2.2 302 (by decide) (by decide)⟩

theorem Frame.tail {a b : State} (h : Frame a b) {r : Nat} (hr : 400 ≤ r) :
    b.core.regs r = a.core.regs r := h.2.2 r (by omega) (by omega)

theorem instruction_frame {base : Nat} {bound : base+8 < 2^32}
    {i : Instruction} (hi : i ∈ code base bound) (s : State) : Frame s (execute i s) := by
  simp only [code, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [Frame, execute, execPrim, PackedConstruction.State.writeNext,
    PackedConstruction.State.next, put] <;> (try split) <;> (try intros) <;> simp_all

theorem instruction_closed {base : Nat} {bound : base+8 < 2^32}
    {i : Instruction} (hi : i ∈ code base bound) {s : State} (hc : s.Closed) :
    (execute i s).Closed := by
  simp only [code, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [execute, execPrim, State.Closed, PackedConstruction.CleanTail,
      PackedConstruction.State.writeNext, PackedConstruction.State.next] using hc
  · simpa [execute, execPrim, State.Closed, PackedConstruction.CleanTail,
      PackedConstruction.State.writeNext, PackedConstruction.State.next] using hc
  · by_cases h : s.core.regs 6 = 0
    all_goals simpa [execute, execPrim, State.Closed, PackedConstruction.CleanTail,
      h, PackedConstruction.State.next] using hc
  · exact releaseKey_closed s hc
  · simpa [execute, execPrim, State.Closed, PackedConstruction.CleanTail,
      PackedConstruction.State.writeNext, PackedConstruction.State.next] using hc
  · simpa [execute, execPrim, State.Closed, PackedConstruction.CleanTail] using hc
  · exact releaseKeyRegister_closed s hc
  · exact releaseKeyRegister_closed s hc

theorem run_frame_closed {program : List Instruction} {base fuel : Nat}
    {bound : base+8 < 2^32} {s : State} (hc : s.Closed)
    (used : UsesCode base bound (run program fuel s)) :
    Frame s (run program fuel s).final ∧ (run program fuel s).final.Closed := by
  induction fuel generalizing s with
  | zero => exact ⟨Frame.refl s, hc⟩
  | succ fuel ih =>
      cases hs : step program s with
      | none => simpa [run, hs] using (show Frame s s ∧ s.Closed from ⟨Frame.refl s, hc⟩)
      | some t =>
          obtain ⟨hb, _, i, _, hi, ha⟩ := step_spec hs
          obtain ⟨j, hj, hjt⟩ := used t (by simp [run, hs])
          have heq : j = i := Action.instruction.inj (hjt.symm.trans hi)
          subst j
          have hf : Frame s t.after := ha ▸ instruction_frame hj s
          have hclosed : t.after.Closed := ha ▸ instruction_closed hj hc
          have rest := ih hclosed (fun u hu => used u (by simp [run, hs, hu]))
          exact ⟨by simpa [run, hs] using hf.trans rest.1, by simpa [run, hs] using rest.2⟩

/-- The actual completed retirement keeps the numeric arena and its descriptor
registers, and clears both comparison resources in their logical extents. -/
theorem comparison_retired {program : List Instruction} {base n : Nat}
    {bound : base+8 < 2^32} (host : Hosted program base bound)
    {s : State} (entry : Entry base n s) :
    let actual := run program (cost n) s
    RunsTo program s actual.final actual.transitions ∧
      actual.final.core.status = .running ∧ actual.final.core.pc = base+8 ∧
      actual.final.keyExtent = 0 ∧ actual.final.keyRegExtent = 0 ∧
      actual.final.core.keys = (fun _ => none) ∧
      actual.final.core.keyRegs = (fun _ => 0) ∧
      actual.final.Closed ∧ Frame s actual.final ∧
      actual.steps = cost n ∧ actual.categories = categories n := by
  obtain ⟨hr, hpc, hk, hkr, len, cats, used⟩ := comparison_run host entry
  obtain ⟨frame, closed⟩ := run_frame_closed entry.2.2.2.2.2 used
  obtain ⟨keys, keyRegs⟩ := empty_keys_of_closed _ closed hk hkr
  exact ⟨by simpa [RunsTo, Run.steps] using run_exact_steps program (cost n) s,
    hr, hpc, hk, hkr, keys, keyRegs, closed, frame, len, cats⟩

theorem word_retired (program : List Instruction) (s : State) (closed : s.Closed)
    (keys : s.keyExtent = 0) (keyRegs : s.keyRegExtent = 0) :
    run program 0 s = ⟨s, []⟩ ∧ s.core.keys = (fun _ => none) ∧
      s.core.keyRegs = (fun _ => 0) := ⟨rfl, empty_keys_of_closed s closed keys keyRegs⟩

theorem category_counts (n : Nat) :
    (categories n).count .keyRelease = n ∧
      (categories n).count .keyRegisterRelease = 2 ∧
      (categories n).count (.old .register) = 2 ∧
      (categories n).count (.old .arithmetic) = n ∧
      (categories n).count (.old .branch) = 2*n+1 := by
  have cycleCount (m : Nat) :
      ((List.replicate m cycleCategories).flatten).count .keyRelease = m ∧
      ((List.replicate m cycleCategories).flatten).count .keyRegisterRelease = 0 ∧
      ((List.replicate m cycleCategories).flatten).count (.old .register) = 0 ∧
      ((List.replicate m cycleCategories).flatten).count (.old .arithmetic) = m ∧
      ((List.replicate m cycleCategories).flatten).count (.old .branch) = 2*m := by
    induction m with
    | zero => simp
    | succ m ih =>
        obtain ⟨hk, hkr, hr, ha, hb⟩ := ih
        simp only [List.replicate_succ, List.flatten_cons, List.count_append,
          hk, hkr, hr, ha, hb]
        simp [cycleCategories]
        omega
  obtain ⟨hk, hkr, hr, ha, hb⟩ := cycleCount n
  simp [categories, List.count_append, hk, hkr, hr, ha, hb]

theorem comparison_category_counts {program : List Instruction} {base n : Nat}
    {bound : base+8 < 2^32} (host : Hosted program base bound)
    {s : State} (entry : Entry base n s) :
    let actual := run program (cost n) s
    actual.categoryCount .keyRelease = n ∧ actual.categoryCount .keyRegisterRelease = 2 ∧
      actual.categoryCount (.old .register) = 2 ∧
      actual.categoryCount (.old .arithmetic) = n ∧
      actual.categoryCount (.old .branch) = 2*n+1 := by
  have cats := (comparison_run host entry).2.2.2.2.2.1
  simpa only [Run.categoryCount, cats] using category_counts n

end RMQ.SuccinctFinal.PackedLifecycle.Retirement
