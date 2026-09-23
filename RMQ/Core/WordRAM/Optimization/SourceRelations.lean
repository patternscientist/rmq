import RMQ.Core.WordRAM.Packed.Frame
import RMQ.Core.WordRAM.Packed.Safety

/-!
# Register agreement for the independent structured source evaluator

The protected register interval includes every source operand, not only write
destinations. Agreement preserves status and the exact ordered receipt list;
registers outside the interval may differ and are framed by source evaluation.
This module makes no claim about an emitted compact program or its cost.
-/

namespace RMQ.SuccinctFinal.PackedWordRAM.Optimization

open Structured

/-- Source-visible status and registers agree; fresh scratch is unrestricted. -/
def DataAgreesBelow (bound : Nat) (left right : Data) : Prop :=
  left.status = right.status ∧ ∀ r, r < bound → left.regs r = right.regs r

/-- Every register identifier of an action lies below the bound. Immediate
constant values are words, not register identifiers, and are not tested here. -/
def ActionRegistersBelow (bound : Nat) : Action → Prop
  | .load dst address => dst < bound ∧ address < bound
  | .constant dst _ => dst < bound
  | .move dst src => dst < bound ∧ src < bound
  | .arithmetic _ dst lhs rhs | .comparison _ dst lhs rhs =>
      dst < bound ∧ lhs < bound ∧ rhs < bound

/-- Includes dormant branch bodies, branch conditions, halt operands, and
every action operand, including source addresses and arithmetic inputs. -/
def BlockRegistersBelow (bound : Nat) : Block → Prop
  | .skip => True
  | .action op => ActionRegistersBelow bound op
  | .exit src => src < bound
  | .seq first second => BlockRegistersBelow bound first ∧ BlockRegistersBelow bound second
  | .ifZero condition zero nonzero => condition < bound ∧
      BlockRegistersBelow bound zero ∧ BlockRegistersBelow bound nonzero
  | .repeat _ body => BlockRegistersBelow bound body

def EvaluationAgreesBelow (bound : Nat) (left right : Evaluation) : Prop :=
  DataAgreesBelow bound left.final right.final ∧ left.reads = right.reads

theorem DataAgreesBelow.refl (bound : Nat) (s : Data) : DataAgreesBelow bound s s :=
  ⟨rfl, fun _ _ => rfl⟩

theorem DataAgreesBelow.symm {bound : Nat} {left right : Data}
    (h : DataAgreesBelow bound left right) : DataAgreesBelow bound right left :=
  ⟨h.1.symm, fun r hr => (h.2 r hr).symm⟩

theorem DataAgreesBelow.trans {bound : Nat} {left middle right : Data}
    (a : DataAgreesBelow bound left middle) (b : DataAgreesBelow bound middle right) :
    DataAgreesBelow bound left right :=
  ⟨a.1.trans b.1, fun r hr => (a.2 r hr).trans (b.2 r hr)⟩

theorem DataAgreesBelow.mono {small large : Nat} {left right : Data}
    (h : DataAgreesBelow large left right) (le : small ≤ large) :
    DataAgreesBelow small left right :=
  ⟨h.1, fun r hr => h.2 r (Nat.lt_of_lt_of_le hr le)⟩

theorem DataAgreesBelow.write_right_fresh {bound : Nat} {left right : Data}
    (h : DataAgreesBelow bound left right) (dst value : Nat) (fresh : bound ≤ dst) :
    DataAgreesBelow bound left ⟨right.regs.write dst value, right.status⟩ := by
  refine ⟨h.1, fun r hr => ?_⟩
  change left.regs r = right.regs.write dst value r
  rw [Registers.write_other right.regs dst value r (by omega)]
  exact h.2 r hr

theorem DataAgreesBelow.write_left_fresh {bound : Nat} {left right : Data}
    (h : DataAgreesBelow bound left right) (dst value : Nat) (fresh : bound ≤ dst) :
    DataAgreesBelow bound ⟨left.regs.write dst value, left.status⟩ right :=
  (h.symm.write_right_fresh dst value fresh).symm

theorem registers_write_agree {bound : Nat} {left right : Registers}
    (h : ∀ r, r < bound → left r = right r) (dst value : Nat) :
    ∀ r, r < bound → left.write dst value r = right.write dst value r := by
  intro r hr
  by_cases he : r = dst
  · simp [Registers.write, he]
  · simp [Registers.write, he, h r hr]

theorem data_write_agree {bound : Nat} {left right : Data}
    (h : DataAgreesBelow bound left right) (dst value : Nat) :
    DataAgreesBelow bound ⟨left.regs.write dst value, .running⟩
      ⟨right.regs.write dst value, .running⟩ :=
  ⟨rfl, registers_write_agree h.2 dst value⟩

theorem ActionRegistersBelow.destination {bound : Nat} {op : Action}
    (h : ActionRegistersBelow bound op) : op.destination < bound := by
  cases op <;> first | exact h | exact h.1

theorem ActionRegistersBelow.mono {small large : Nat} {op : Action}
    (h : ActionRegistersBelow small op) (le : small ≤ large) :
    ActionRegistersBelow large op := by
  cases op <;> simp only [ActionRegistersBelow] at h ⊢ <;> omega

theorem BlockRegistersBelow.mono {small large : Nat} {block : Block}
    (h : BlockRegistersBelow small block) (le : small ≤ large) :
    BlockRegistersBelow large block := by
  induction block with
  | skip => trivial
  | action op => exact ActionRegistersBelow.mono h le
  | exit src => exact Nat.lt_of_lt_of_le h le
  | seq a b iha ihb => exact ⟨iha h.1, ihb h.2⟩
  | ifZero c a b iha ihb => exact ⟨Nat.lt_of_lt_of_le h.1 le, iha h.2.1, ihb h.2.2⟩
  | «repeat» count body ih => exact ih h

theorem BlockRegistersBelow.writesOnly {bound : Nat} {block : Block}
    (h : BlockRegistersBelow bound block) : block.WritesOnly (· < bound) := by
  induction block with
  | skip => trivial
  | action op => exact h.destination
  | exit src => trivial
  | seq a b iha ihb => exact ⟨iha h.1, ihb h.2⟩
  | ifZero c a b iha ihb => exact ⟨iha h.2.1, ihb h.2.2⟩
  | «repeat» count body ih => exact ih h

/-- Even failed loads and stopped evaluations preserve every register outside
the complete source-register interval. -/
theorem source_eval_frame (memory : Memory) (block : Block) (bound : Nat)
    (bounded : BlockRegistersBelow bound block) (r : Nat) (outside : bound ≤ r) (s : Data) :
    (block.eval memory s).final.regs r = s.regs r :=
  block.eval_frame memory (· < bound) bounded.writesOnly r (by omega) s

/-- Scalar execution uses equal actual operands and therefore equal physical
replies. The statement also covers a missing reply, retaining its receipt. -/
theorem action_eval_congr (memory : Memory) (op : Action) (bound : Nat)
    (bounded : ActionRegistersBelow bound op) (left right : Data)
    (agree : DataAgreesBelow bound left right) :
    EvaluationAgreesBelow bound (op.eval memory left) (op.eval memory right) := by
  cases op with
  | load dst address =>
      have ha := agree.2 address bounded.2
      cases reply : memory[right.regs address]? with
      | none =>
          simp only [Action.eval, Action.instruction, execute, ha, reply, Data.ofState]
          exact ⟨⟨rfl, agree.2⟩, rfl⟩
      | some value =>
          simp only [Action.eval, Action.instruction, execute, ha, reply, Data.ofState,
            State.writeNext]
          exact ⟨data_write_agree agree dst value, rfl⟩
  | constant dst value =>
      exact ⟨data_write_agree agree dst value, rfl⟩
  | move dst src =>
      have hs := agree.2 src bounded.2
      simp only [Action.eval, Action.instruction, execute, hs, Data.ofState, State.writeNext]
      exact ⟨data_write_agree agree dst (right.regs src), rfl⟩
  | arithmetic op dst lhs rhs =>
      have hl := agree.2 lhs bounded.2.1
      have hr := agree.2 rhs bounded.2.2
      simp only [Action.eval, Action.instruction, execute, hl, hr, Data.ofState, State.writeNext]
      exact ⟨data_write_agree agree dst _, rfl⟩
  | comparison op dst lhs rhs =>
      have hl := agree.2 lhs bounded.2.1
      have hr := agree.2 rhs bounded.2.2
      simp only [Action.eval, Action.instruction, execute, hl, hr, Data.ofState, State.writeNext]
      exact ⟨data_write_agree agree dst _, rfl⟩

theorem iterate_eval_congr (bound : Nat) (body : Data → Evaluation)
    (congr : ∀ left right, DataAgreesBelow bound left right →
      EvaluationAgreesBelow bound (body left) (body right)) (count : Nat) (left right : Data)
    (agree : DataAgreesBelow bound left right) :
    EvaluationAgreesBelow bound (iterate body count left) (iterate body count right) := by
  induction count generalizing left right with
  | zero => exact ⟨agree, rfl⟩
  | succ count ih =>
      have first := congr left right agree
      have rest := ih (body left).final (body right).final first.1
      refine ⟨rest.1, ?_⟩
      change (body left).reads ++ (iterate body count (body left).final).reads = _
      rw [first.2, rest.2]
      rfl

/-- All source constructors preserve source-visible data and the exact ordered
attempted-read/reply sequence under arbitrary changes to fresh registers. -/
theorem source_eval_congr (memory : Memory) (block : Block) (bound : Nat)
    (bounded : BlockRegistersBelow bound block) (left right : Data)
    (agree : DataAgreesBelow bound left right) :
    EvaluationAgreesBelow bound (block.eval memory left) (block.eval memory right) := by
  induction block generalizing left right with
  | skip =>
      cases hs : left.status <;>
        simp only [Block.eval, ← agree.1, hs] <;> exact ⟨agree, rfl⟩
  | action op =>
      by_cases hs : left.status = .running
      · simp only [Block.eval, ← agree.1, hs]
        exact action_eval_congr memory op bound bounded left right agree
      · have hr : right.status ≠ .running := by rw [← agree.1]; exact hs
        rw [Block.eval_stopped memory _ left hs, Block.eval_stopped memory _ right hr]
        exact ⟨agree, rfl⟩
  | exit src =>
      by_cases hs : left.status = .running
      · simp only [Block.eval, ← agree.1, hs]
        exact ⟨⟨congrArg Status.halted (agree.2 src bounded), agree.2⟩, rfl⟩
      · have hr : right.status ≠ .running := by rw [← agree.1]; exact hs
        rw [Block.eval_stopped memory _ left hs, Block.eval_stopped memory _ right hr]
        exact ⟨agree, rfl⟩
  | seq first second ihf ihs =>
      rw [Block.eval_seq, Block.eval_seq]
      have a := ihf bounded.1 left right agree
      have b := ihs bounded.2 (first.eval memory left).final (first.eval memory right).final a.1
      refine ⟨b.1, ?_⟩
      change (first.eval memory left).reads ++
        (second.eval memory (first.eval memory left).final).reads = _
      rw [a.2, b.2]
      rfl
  | ifZero condition zero nonzero ihz ihn =>
      by_cases hs : left.status = .running
      · simp only [Block.eval, ← agree.1, hs, agree.2 condition bounded.1]
        split
        · exact ihz bounded.2.1 left right agree
        · exact ihn bounded.2.2 left right agree
      · have hr : right.status ≠ .running := by rw [← agree.1]; exact hs
        rw [Block.eval_stopped memory _ left hs, Block.eval_stopped memory _ right hr]
        exact ⟨agree, rfl⟩
  | «repeat» count body ih =>
      rw [Block.eval_repeat, Block.eval_repeat]
      exact iterate_eval_congr bound (body.eval memory) (ih bounded) count left right agree

theorem action_localSafe_congr (memory : Memory) (width bound : Nat) (op : Action)
    (bounded : ActionRegistersBelow bound op) (left right : Data)
    (agree : DataAgreesBelow bound left right) :
    op.LocalSafe memory width left ↔ op.LocalSafe memory width right := by
  cases op with
  | load dst address => simp only [Action.LocalSafe, agree.2 address bounded.2]
  | constant dst value => rfl
  | move dst src => simp only [Action.LocalSafe, agree.2 src bounded.2]
  | arithmetic op dst lhs rhs =>
      simp only [Action.LocalSafe, agree.2 lhs bounded.2.1, agree.2 rhs bounded.2.2]
  | comparison op dst lhs rhs =>
      simp only [Action.LocalSafe, agree.2 lhs bounded.2.1, agree.2 rhs bounded.2.2]

/-- Full source safety transfers when the alternate fresh registers also fit
the same width. Every intermediate body is checked at its own evaluated data. -/
theorem source_safe_transport (memory : Memory) (width bound : Nat) (block : Block)
    (bounded : BlockRegistersBelow bound block) (left right : Data)
    (agree : DataAgreesBelow bound left right) (rightFit : right.Fits width)
    (safe : block.Safe memory width left) : block.Safe memory width right := by
  induction block generalizing left right with
  | skip => exact Block.safe_skip memory width right rightFit
  | action op =>
      refine ⟨rightFit, fun hr => ?_⟩
      have hl : left.status = .running := agree.1.trans hr
      exact (action_localSafe_congr memory width bound op bounded left right agree).mp (safe.2 hl)
  | exit src => exact Block.safe_exit memory width src right rightFit
  | seq first second ihf ihs =>
      refine ⟨rightFit, fun hr => ?_⟩
      have hl : left.status = .running := agree.1.trans hr
      have a := ihf bounded.1 left right agree rightFit (safe.2 hl).1
      exact ⟨a, ihs bounded.2 _ _
        (source_eval_congr memory first bound bounded.1 left right agree).1
        (first.eval_fits memory width right a) (safe.2 hl).2⟩
  | ifZero condition zero nonzero ihz ihn =>
      refine ⟨rightFit, fun hr => ?_⟩
      have hl : left.status = .running := agree.1.trans hr
      have arms := safe.2 hl
      have hc := agree.2 condition bounded.1
      simp only [hc] at arms
      by_cases hz : right.regs condition = 0
      · simp only [hz, if_true] at arms ⊢
        exact ihz bounded.2.1 left right agree rightFit arms
      · simp only [hz, if_false] at arms ⊢
        exact ihn bounded.2.2 left right agree rightFit arms
  | «repeat» count body ih =>
      change BlockRegistersBelow bound body at bounded
      refine ⟨rightFit, fun hr => ?_⟩
      have hl : left.status = .running := agree.1.trans hr
      have iterations := safe.2 hl
      clear safe hr hl
      induction count generalizing left right with
      | zero => trivial
      | succ count ihc =>
          have first := ih bounded left right agree rightFit iterations.1
          exact ⟨first, ihc _ _
            (source_eval_congr memory body bound bounded left right agree).1
            (body.eval_fits memory width right first) iterations.2⟩

namespace SourceRelationsConsumers

/-- Pin every projection independently of the relation's current definition. -/
theorem source_congr_expectedType (memory : Memory) (block : Block) (bound : Nat)
    (bounded : BlockRegistersBelow bound block) (left right : Data)
    (status : left.status = right.status)
    (registers : ∀ r, r < bound → left.regs r = right.regs r) :
    (block.eval memory left).final.status = (block.eval memory right).final.status ∧
    (∀ r, r < bound →
      (block.eval memory left).final.regs r = (block.eval memory right).final.regs r) ∧
    (block.eval memory left).reads = (block.eval memory right).reads := by
  have h := source_eval_congr memory block bound bounded left right ⟨status, registers⟩
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem source_frame_expectedType (memory : Memory) (block : Block) (bound : Nat)
    (bounded : BlockRegistersBelow bound block) (s : Data) :
    ∀ r, bound ≤ r → (block.eval memory s).final.regs r = s.regs r := by
  intro r hr
  exact source_eval_frame memory block bound bounded r hr s

theorem source_safe_expectedType (memory : Memory) (width bound : Nat) (block : Block)
    (bounded : BlockRegistersBelow bound block) (left right : Data)
    (status : left.status = right.status)
    (registers : ∀ r, r < bound → left.regs r = right.regs r)
    (rightFit : right.Fits width) (safe : block.Safe memory width left) :
    block.Safe memory width right :=
  source_safe_transport memory width bound block bounded left right ⟨status, registers⟩
    rightFit safe

theorem fresh_destination_rejected : ¬ BlockRegistersBelow 1 (.action (.constant 1 0)) := by
  simp [BlockRegistersBelow, ActionRegistersBelow]

theorem fresh_address_rejected : ¬ BlockRegistersBelow 1 (.action (.load 0 1)) := by
  simp [BlockRegistersBelow, ActionRegistersBelow]

theorem fresh_move_source_rejected : ¬ BlockRegistersBelow 1 (.action (.move 0 1)) := by
  simp [BlockRegistersBelow, ActionRegistersBelow]

theorem fresh_arithmetic_lhs_rejected :
    ¬ BlockRegistersBelow 1 (.action (.arithmetic .add 0 1 0)) := by
  simp [BlockRegistersBelow, ActionRegistersBelow]

theorem fresh_arithmetic_rhs_rejected :
    ¬ BlockRegistersBelow 1 (.action (.arithmetic .add 0 0 1)) := by
  simp [BlockRegistersBelow, ActionRegistersBelow]

theorem fresh_comparison_lhs_rejected :
    ¬ BlockRegistersBelow 1 (.action (.comparison .eq 0 1 0)) := by
  simp [BlockRegistersBelow, ActionRegistersBelow]

theorem fresh_comparison_rhs_rejected :
    ¬ BlockRegistersBelow 1 (.action (.comparison .eq 0 0 1)) := by
  simp [BlockRegistersBelow, ActionRegistersBelow]

theorem fresh_condition_rejected : ¬ BlockRegistersBelow 1 (.ifZero 1 .skip .skip) := by
  simp [BlockRegistersBelow]

theorem fresh_exit_rejected : ¬ BlockRegistersBelow 1 (.exit 1) := by
  simp [BlockRegistersBelow]

theorem dormant_source_rejected :
    ¬ BlockRegistersBelow 1 (.ifZero 0 .skip (.action (.load 0 1))) := by
  simp [BlockRegistersBelow, ActionRegistersBelow]

theorem zero_repeat_source_rejected :
    ¬ BlockRegistersBelow 1 (.repeat 0 (.action (.load 0 1))) := by
  simp [BlockRegistersBelow, ActionRegistersBelow]

theorem immediate_is_not_register (value : Nat) :
    BlockRegistersBelow 1 (.action (.constant 0 value)) := by
  simp [BlockRegistersBelow, ActionRegistersBelow]

end SourceRelationsConsumers

end RMQ.SuccinctFinal.PackedWordRAM.Optimization
