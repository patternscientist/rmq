import RMQ.Core.WordRAM.Optimization.SourceRelations

/-!
# Counted-loop emission in the existing primitive instruction set

Positive repeats use two fresh registers at each nesting depth and five
ordinary control instructions. The compiler receives fixed source syntax,
fresh-register origin and code position, with no memory or query input.
-/

namespace RMQ.SuccinctFinal.PackedWordRAM.Optimization

open Structured

def compactSize : Block → Nat
  | .skip => 0
  | .action _ | .exit _ => 1
  | .seq a b => compactSize a + compactSize b
  | .ifZero _ zero nonzero => 1 + compactSize nonzero + 1 + compactSize zero
  | .repeat 0 _ => 0
  | .repeat (_ + 1) body => 5 + compactSize body

def compactBound : Block → Nat
  | .skip => 0
  | .action _ | .exit _ => 1
  | .seq a b => compactBound a + compactBound b
  | .ifZero _ zero nonzero => max (1 + compactBound zero) (2 + compactBound nonzero)
  | .repeat 0 _ => 0
  | .repeat (count + 1) body => 3 + (count + 1) * (compactBound body + 3)

def compactDepth : Block → Nat
  | .skip | .action _ | .exit _ => 0
  | .seq a b | .ifZero _ a b => max (compactDepth a) (compactDepth b)
  | .repeat 0 _ => 0
  | .repeat (_ + 1) body => 1 + compactDepth body

def compactCounter (fresh depth : Nat) : Nat := fresh + 2 * depth

/-- Every target is an absolute PC derived from the literal emitted layout.
Body compilation moves to the next scratch pair, preserving parent counters. -/
def compactAt : Block → Nat → Nat → Nat → Program
  | .skip, _, _, _ => []
  | .action op, _, _, _ => [op.instruction]
  | .exit src, _, _, _ => [.halt src]
  | .seq a b, fresh, depth, base =>
      compactAt a fresh depth base ++ compactAt b fresh depth (base + compactSize a)
  | .ifZero condition zero nonzero, fresh, depth, base =>
      [.branchZero condition (base + 1 + compactSize nonzero + 1)] ++
      compactAt nonzero fresh depth (base + 1) ++
      [.jump (base + 1 + compactSize nonzero + 1 + compactSize zero)] ++
      compactAt zero fresh depth (base + 1 + compactSize nonzero + 1)
  | .repeat 0 _, _, _, _ => []
  | .repeat (count + 1) body, fresh, depth, base =>
      let counter := compactCounter fresh depth
      [.constant counter (count + 1), .constant (counter + 1) 1,
        .branchZero counter (base + 5 + compactSize body)] ++
      compactAt body fresh (depth + 1) (base + 3) ++
      [.arithmetic .sub counter counter (counter + 1), .jump (base + 2)]

/-- Exact size of emitted code, including both branch directions and loop
control. This is independent of its execution-cost recurrence. -/
theorem compactAt_length (block : Block) (fresh depth base : Nat) :
    (compactAt block fresh depth base).length = compactSize block := by
  induction block generalizing depth base with
  | skip => rfl
  | action op => rfl
  | exit src => rfl
  | seq a b iha ihb => simp [compactAt, compactSize, iha, ihb]
  | ifZero c z n ihz ihn => simp [compactAt, compactSize, ihz, ihn]; omega
  | «repeat» count body ih =>
      cases count with
      | zero => rfl
      | succ count => simp [compactAt, compactSize, ih]; omega

end RMQ.SuccinctFinal.PackedWordRAM.Optimization
