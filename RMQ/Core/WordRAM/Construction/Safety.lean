import RMQ.Core.WordRAM.Construction.Program

/-! # The single per-transition safety judgment

`Prim.Safe W len s p` is the only safety vocabulary of the construction lane
(audit recommendation R1). It covers operand fit at the declared width, the
arithmetic result bound, non-underflowing subtraction, positive divisors,
in-range shift amounts, in-extent present-cell loads and in-extent stores with
fitting values, present keys, reservation capacity, in-program branch and jump
targets and the absence of `jumpRegister`. `State.Fits` bounds every register,
the program counter, the extent, every present memory word and any halt value.
A safe transition from a fitting running state never faults and lands in a
fitting state; `Run.Safe` is every transition safe with a fitting post-state.
-/

namespace RMQ.SuccinctFinal.PackedConstruction

/-- Every stored word, register, address and halt value fits the declared width. -/
def State.Fits (W : Nat) (s : State) : Prop :=
  (∀ r, s.regs r < 2 ^ W) ∧ s.pc < 2 ^ W ∧ s.extent < 2 ^ W ∧
    (∀ a v, s.memory a = some v → v < 2 ^ W) ∧
    (∀ v, s.status = .halted v → v < 2 ^ W)

/-- Every encoded operand of the primitive fits the declared width. -/
def Prim.OperandsFit (W : Nat) (p : Prim) : Prop := ∀ c ∈ p.constants, c.val < 2 ^ W

theorem Prim.operandsFit_of_width (p : Prim) {W : Nat} (hw : 32 ≤ W) : p.OperandsFit W := by
  intro c _
  exact Nat.lt_of_lt_of_le c.isLt (Nat.pow_le_pow_right (by decide) hw)

/-- Constructor-exhaustive safety obligations at the actual pre-state. -/
def Prim.SafeAt (W len : Nat) (s : State) : Prim → Prop
  | .load _ address =>
      s.regs address < s.extent ∧ ∃ v, s.memory (s.regs address) = some v ∧ v < 2 ^ W
  | .constant _ _ => True
  | .move _ _ => True
  | .arithmetic op _ lhs rhs =>
      op.eval (s.regs lhs) (s.regs rhs) < 2 ^ W ∧
      (op = .sub → s.regs rhs ≤ s.regs lhs) ∧
      (op = .div ∨ op = .mod → 0 < s.regs rhs) ∧
      (op = .shl ∨ op = .shr → s.regs rhs < W)
  | .comparison _ _ _ _ => True
  | .jump target => target.val < len
  | .jumpRegister _ => False
  | .branchZero _ target => target.val < len
  | .halt _ => True
  | .store address value => s.regs address < s.extent ∧ s.regs value < 2 ^ W
  | .reserve _ => s.extent + 1 < 2 ^ W
  | .loadKey _ address => ∃ k, s.keys (s.regs address) = some k
  | .compareKey _ _ _ => True

/-- The per-transition safety judgment: operands fit and the arm-specific
obligations hold at the pre-state. -/
def Prim.Safe (W len : Nat) (s : State) (p : Prim) : Prop :=
  p.OperandsFit W ∧ p.SafeAt W len s

/-- Every transition of a run is safe and lands in a fitting state. -/
def Run.Safe (W : Nat) (program : List BInstr) (r : Run) : Prop :=
  ∀ t ∈ r.transitions,
    Prim.Safe W program.length t.before t.instruction.primitive ∧ t.after.Fits W

/-! ## Consequences of one safe transition -/

theorem State.Fits.writeNext {W : Nat} {s : State} (hfit : s.Fits W) {dst value : Nat}
    (hv : value < 2 ^ W) (hpc : s.pc + 1 < 2 ^ W) : (s.writeNext dst value).Fits W := by
  obtain ⟨hr, _, he, hm, hh⟩ := hfit
  refine ⟨?_, hpc, he, hm, ?_⟩
  · intro r
    by_cases h : r = dst
    · simpa [State.writeNext, State.next, put, h] using hv
    · simpa [State.writeNext, State.next, put, h] using hr r
  · intro v hv'
    simp only [State.writeNext, State.next] at hv'
    exact hh v hv'

/-- A safe transition never produces a fault. -/
theorem Prim.safe_not_fault {W len : Nat} {s : State} {p : Prim} (hsafe : Prim.Safe W len s p)
    (hs : s.status ≠ .fault) : (execPrim p s).status ≠ .fault := by
  obtain ⟨hops, hat⟩ := hsafe
  cases p <;> dsimp only [Prim.SafeAt] at hat
  case load dst address =>
      obtain ⟨ha, v, hv, _⟩ := hat
      simp [execPrim, ha, hv, State.writeNext, State.next]
      exact hs
  case store address value =>
      simp [execPrim, hat.1, State.next]
      exact hs
  case loadKey dst address =>
      obtain ⟨k, hk⟩ := hat
      simp [execPrim, hk, State.next]
      exact hs
  case halt src => simp [execPrim]
  case jump target => simpa [execPrim] using hs
  case branchZero condition target => simpa [execPrim] using hs
  case constant dst value => simpa [execPrim, State.writeNext, State.next] using hs
  case move dst src => simpa [execPrim, State.writeNext, State.next] using hs
  case arithmetic op dst lhs rhs => simpa [execPrim, State.writeNext, State.next] using hs
  case comparison op dst lhs rhs => simpa [execPrim, State.writeNext, State.next] using hs
  case reserve dst => simpa [execPrim, State.writeNext, State.next] using hs
  case compareKey dst lhs rhs => simpa [execPrim, State.writeNext, State.next] using hs

/-- A safe transition from a fitting state whose program counter is inside a
program that fits lands in a fitting state. -/
theorem Prim.safe_fits {W len : Nat} {s : State} {p : Prim} (hfit : s.Fits W)
    (hsafe : Prim.Safe W len s p) (hpc : s.pc < len) (hlen : len < 2 ^ W) :
    (execPrim p s).Fits W := by
  have hpc1 : s.pc + 1 < 2 ^ W := by omega
  obtain ⟨hops, hat⟩ := hsafe
  have hr := hfit.1
  cases p <;> dsimp only [Prim.SafeAt] at hat
  case load dst address =>
      obtain ⟨ha, v, hv, hvw⟩ := hat
      simp only [execPrim, ha, if_true, hv]
      exact hfit.writeNext hvw hpc1
  case constant dst value =>
      simp only [execPrim]
      exact hfit.writeNext (hops value (by simp [Prim.constants])) hpc1
  case move dst src =>
      simp only [execPrim]
      exact hfit.writeNext (hr src) hpc1
  case arithmetic op dst lhs rhs =>
      simp only [execPrim]
      exact hfit.writeNext hat.1 hpc1
  case comparison op dst lhs rhs =>
      simp only [execPrim]
      have htag : (4 : Operand).val < 2 ^ W := hops 4 (by simp [Prim.constants])
      have hv : Comparison.eval op (s.regs lhs) (s.regs rhs) < 2 ^ W := by
        have h4 : (4 : Operand).val = 4 := rfl
        rw [h4] at htag
        cases op <;> simp only [Comparison.eval] <;> split <;> omega
      exact hfit.writeNext hv hpc1
  case jump target =>
      obtain ⟨_, _, he, hm, hh⟩ := hfit
      refine ⟨hr, ?_, he, hm, hh⟩
      simp only [execPrim]
      omega
  case branchZero condition target =>
      obtain ⟨_, _, he, hm, hh⟩ := hfit
      refine ⟨hr, ?_, he, hm, hh⟩
      simp only [execPrim]
      split <;> omega
  case halt src =>
      obtain ⟨_, hp, he, hm, _⟩ := hfit
      refine ⟨hr, hp, he, hm, ?_⟩
      intro v hv
      simp only [execPrim, Status.halted.injEq] at hv
      rw [← hv]
      exact hr src
  case store address value =>
      obtain ⟨ha, hv⟩ := hat
      obtain ⟨_, _, he, hm, hh⟩ := hfit
      simp only [execPrim, ha, if_true, State.next]
      refine ⟨hr, hpc1, he, ?_, hh⟩
      intro a w hw
      simp only [put] at hw
      split at hw
      · cases hw; exact hv
      · exact hm a w hw
  case reserve dst =>
      have hw := State.Fits.writeNext hfit (dst := dst.val) (value := s.extent) (by omega) hpc1
      obtain ⟨hr', hp', _, hm', hh'⟩ := hw
      exact ⟨hr', hp', hat, hm', hh'⟩
  case loadKey dst address =>
      obtain ⟨k, hk⟩ := hat
      obtain ⟨_, _, he, hm, hh⟩ := hfit
      simp only [execPrim, hk, State.next]
      exact ⟨hr, hpc1, he, hm, hh⟩
  case compareKey dst lhs rhs =>
      simp only [execPrim]
      have htag : (12 : Operand).val < 2 ^ W := hops 12 (by simp [Prim.constants])
      have hv : (if s.keyRegs lhs < s.keyRegs rhs then 1 else 0) < 2 ^ W := by
        have h12 : (12 : Operand).val = 12 := rfl
        rw [h12] at htag
        split <;> omega
      exact hfit.writeNext hv hpc1

/-! The run-level consequences (`run_trace_fits`, `Run.Safe.of_transitions`,
`Run.Safe.not_fault`, `Run.Safe.final_fits`) live in `Compiler.lean`, which
imports both this module and the execution calculus. -/

end RMQ.SuccinctFinal.PackedConstruction
