import RMQ.Core.WordRAM.Packed.Safety
import RMQ.Core.WordRAM.Packed.InteriorLocate

/-! Small scalar-safety rules for the fixed descriptor routines. -/
namespace RMQ.SuccinctFinal.PackedWordRAM
open Structured
/-- Local scalar checks without repeating the all-register invariant at every
syntax node. The preservation lemma below restores that invariant. -/
def ScalarChecks (memory : Memory) (width : Nat) : Block → Data → Prop
  | block, s => s.status = .running →
      match block with
      | .skip => True
      | .action op => op.LocalSafe memory width s
      | .exit src => s.regs src < 2 ^ width
      | .seq first second => ScalarChecks memory width first s ∧
          ScalarChecks memory width second (first.eval memory s).final
      | .ifZero condition zero nonzero =>
          if s.regs condition = 0 then ScalarChecks memory width zero s
          else ScalarChecks memory width nonzero s
      | .repeat count body =>
          IterationsSafe (ScalarChecks memory width body) (body.eval memory) count s

theorem ScalarChecks_safe (memory : Memory) (width : Nat) (block : Block)
    (s : Data) (fit : s.Fits width) (checks : ScalarChecks memory width block s) :
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

@[simp] theorem ScalarChecks_stopped (memory : Memory) (width : Nat)
    (block : Block) (s : Data) (stopped : s.status ≠ .running) :
    ScalarChecks memory width block s := by
  cases block <;> exact fun h => (stopped h).elim

theorem ScalarChecks_step {memory : Memory} {width : Nat} {op : Action}
    {rest : Block} {s : Data} (operation : op.LocalSafe memory width s)
    (tail : ScalarChecks memory width rest (op.eval memory s).final) :
    ScalarChecks memory width (.seq (.action op) rest) s := by
  intro hs
  exact ⟨fun _ => operation, by simpa [Block.eval, hs] using tail⟩

theorem ScalarChecks_action {memory : Memory} {width : Nat} {op : Action}
    {s : Data} (operation : op.LocalSafe memory width s) :
    ScalarChecks memory width (.action op) s := fun _ => operation

theorem ScalarChecks_branch {memory : Memory} {width condition : Nat}
    {zero nonzero : Block} {s : Data}
    (arm : if s.regs condition = 0 then ScalarChecks memory width zero s
      else ScalarChecks memory width nonzero s) :
    ScalarChecks memory width (.ifZero condition zero nonzero) s := fun _ => arm

theorem ScalarChecks_seq_skip {memory : Memory} {width : Nat}
    {first : Block} {s : Data} (head : ScalarChecks memory width first s) :
    ScalarChecks memory width (.seq first .skip) s :=
  fun _ => ⟨head, fun _ => True.intro⟩

/-- Constants, copies and comparisons preserve fitting data without arithmetic
preconditions. This predicate is about fixed source syntax only. -/
def SimpleScalar (width : Nat) : Block → Prop
  | .skip => True
  | .action (.constant _ value) => value < 2 ^ width
  | .action (.move _ _) => True
  | .action (.comparison _ _ _ _) => 1 < 2 ^ width
  | .seq first second => SimpleScalar width first ∧ SimpleScalar width second
  | .ifZero _ zero nonzero => SimpleScalar width zero ∧ SimpleScalar width nonzero
  | _ => False

theorem SimpleScalar.safe (memory : Memory) (width : Nat) (block : Block)
    (simple : SimpleScalar width block) (s : Data) (fit : s.Fits width) :
    block.Safe memory width s := by
  induction block generalizing s with
  | skip => exact Block.safe_skip memory width s fit
  | action op =>
      apply Block.safe_action memory width op s fit
      cases op with
      | constant dst value => exact simple
      | move dst src => exact fit.1 src
      | comparison op dst lhs rhs =>
          cases op <;> simp only [Action.LocalSafe, Comparison.eval] <;>
            split <;> exact Nat.lt_of_le_of_lt (by decide) simple
      | load dst address => exact simple.elim
      | arithmetic op dst lhs rhs => exact simple.elim
  | exit src => exact simple.elim
  | seq first second ihf ihs =>
      have hf := ihf simple.1 s fit
      exact Block.safe_seq hf (ihs simple.2 _ (first.eval_fits memory width s hf))
  | ifZero condition zero nonzero ihz ihn =>
      apply Block.safe_ifZero fit
      split
      · exact ihz simple.1 s fit
      · exact ihn simple.2 s fit
  | «repeat» count body ih => exact simple.elim

theorem minBlock_safe (memory : Memory) (width dst lhs rhs tmp : Nat)
    (s : Data) (fit : s.Fits width) (one : 1 < 2 ^ width) :
    (minBlock dst lhs rhs tmp).Safe memory width s := by
  apply SimpleScalar.safe memory width _ _ s fit
  exact ⟨one, True.intro, True.intro⟩

theorem natSubBlock_safe (memory : Memory) (width dst lhs rhs tmp : Nat)
    (s : Data) (fit : s.Fits width) (one : 1 < 2 ^ width)
    (hl : lhs ≠ tmp) (hr : rhs ≠ tmp) :
    (natSubBlock dst lhs rhs tmp).Safe memory width s := by
  by_cases hs : s.status = .running
  · cases s with
    | mk regs status =>
      try dsimp only at hs fit
      subst status
      apply ScalarChecks_safe memory width _ _ fit
      have hwne : width ≠ 0 := by intro h; simp [h] at one
      have fl := fit.1 lhs
      dsimp only at fl
      by_cases sub : regs rhs ≤ regs lhs
      all_goals simp [ScalarChecks, natSubBlock, Block.eval, Action.eval,
        Action.instruction, Action.LocalSafe, execute, State.writeNext, Data.ofState,
        Registers.write, Arithmetic.eval, Comparison.eval, hl, hr, sub, hwne] <;> omega
  · exact Block.safe_stopped memory width _ s fit hs

theorem regularLocateBlock_safe (base width : Nat) (memory : Memory) (s : Data)
    (fit : s.Fits width) (one : 1 < 2 ^ width)
    (product : s.regs base < s.regs (base + 4) →
      s.regs base * s.regs (base + 3) < 2 ^ width)
    (position : s.regs base < s.regs (base + 4) →
      s.regs (base + 1) + s.regs base * s.regs (base + 3) < 2 ^ width) :
    (regularLocateBlock base).Safe memory width s := by
  have hwne : width ≠ 0 := by intro h; simp [h] at one
  by_cases hs : s.status = .running
  · apply ScalarChecks_safe memory width _ s fit
    cases s with
    | mk regs status =>
      try dsimp only at hs product position
      try dsimp only at hs
      subst status
      try dsimp only at fit
      have f0 := fit.1 base
      have f1 := fit.1 (base + 1)
      have f2 := fit.1 (base + 2)
      have f3 := fit.1 (base + 3)
      dsimp only at f0 f1 f2 f3
      by_cases active : regs base < regs (base + 4)
      · have pm := product active
        have pa := position active
        by_cases sub : regs base * regs (base + 3) ≤ regs (base + 2)
        · by_cases lower : regs (base + 3) ≤ regs (base + 2) - regs base * regs (base + 3)
          all_goals simp [hwne, ScalarChecks, regularLocateBlock, Block.sequence, Block.eval,
            Action.eval, Action.instruction, Action.LocalSafe, execute, State.writeNext,
            Data.ofState, Registers.write, Arithmetic.eval, Comparison.eval,
            natSubBlock, minBlock, active, sub, lower] <;> omega
        · simp [hwne, ScalarChecks, regularLocateBlock, Block.sequence, Block.eval,
            Action.eval, Action.instruction, Action.LocalSafe, execute, State.writeNext,
            Data.ofState, Registers.write, Arithmetic.eval, Comparison.eval,
            natSubBlock, minBlock, active, sub]
          split <;> omega
      · simp [ScalarChecks, regularLocateBlock, Block.sequence, Block.eval,
          Action.eval, Action.instruction, Action.LocalSafe, execute, State.writeNext,
          Data.ofState, Registers.write, Comparison.eval, active]
        omega
  · exact Block.safe_stopped memory width _ s fit hs

theorem interiorLocateBlock_safe (base width : Nat) (memory : Memory) (s : Data)
    (fit : s.Fits width) (one : 1 < 2 ^ width) (chunks : 0 < s.regs (base + 5))
    (products : s.regs (base + 1) ≤ s.regs base →
      s.regs base - s.regs (base + 1) < s.regs (base + 2) →
      ((s.regs base - s.regs (base + 1)) % s.regs (base + 5)) * s.regs (base + 6) < 2 ^ width ∧
      ((s.regs base - s.regs (base + 1)) / s.regs (base + 5)) * s.regs (base + 4) < 2 ^ width ∧
      s.regs (base + 3) +
        ((s.regs base - s.regs (base + 1)) % s.regs (base + 5)) * s.regs (base + 6) +
        ((s.regs base - s.regs (base + 1)) / s.regs (base + 5)) * s.regs (base + 4) < 2 ^ width) :
    (interiorLocateBlock base).Safe memory width s := by
  have hwne : width ≠ 0 := by intro h; simp [h] at one
  by_cases hs : s.status = .running
  · apply ScalarChecks_safe memory width _ s fit
    cases s with
    | mk regs status =>
      try dsimp only at hs
      subst status
      try dsimp only at fit
      have f0 := fit.1 base
      try dsimp only at chunks products
      have f4 := fit.1 (base + 4)
      have f6 := fit.1 (base + 6)
      dsimp only at f0 f4 f6
      have quot := Nat.div_le_self (regs base - regs (base + 1)) (regs (base + 5))
      have rem := Nat.mod_le (regs base - regs (base + 1)) (regs (base + 5))
      by_cases before : regs (base + 1) ≤ regs base
      · by_cases active : regs base - regs (base + 1) < regs (base + 2)
        · obtain ⟨pm, pe, pa⟩ := products before active
          by_cases sub : ((regs base - regs (base + 1)) % regs (base + 5)) * regs (base + 6) ≤ regs (base + 4)
          · by_cases lower : regs (base + 4) - ((regs base - regs (base + 1)) % regs (base + 5)) * regs (base + 6) ≤ regs (base + 6)
            all_goals simp [hwne, ScalarChecks, interiorLocateBlock, Block.sequence, Block.eval,
              Action.eval, Action.instruction, Action.LocalSafe, execute, State.writeNext,
              Data.ofState, Registers.write, Arithmetic.eval, Comparison.eval,
              natSubBlock, minBlock, before, active, sub, lower] <;> omega
          · simp [hwne, ScalarChecks, interiorLocateBlock, Block.sequence, Block.eval,
              Action.eval, Action.instruction, Action.LocalSafe, execute, State.writeNext,
              Data.ofState, Registers.write, Arithmetic.eval, Comparison.eval,
              natSubBlock, minBlock, before, active, sub]
            omega
        · simp [hwne, ScalarChecks, interiorLocateBlock, Block.sequence, Block.eval,
            Action.eval, Action.instruction, Action.LocalSafe, execute, State.writeNext,
            Data.ofState, Registers.write, Arithmetic.eval, Comparison.eval, before, active]
          omega
      · simp [ScalarChecks, interiorLocateBlock, Block.sequence, Block.eval,
          Action.eval, Action.instruction, Action.LocalSafe, execute, State.writeNext,
          Data.ofState, Registers.write, Comparison.eval, before]
        omega
  · exact Block.safe_stopped memory width _ s fit hs

end RMQ.SuccinctFinal.PackedWordRAM
