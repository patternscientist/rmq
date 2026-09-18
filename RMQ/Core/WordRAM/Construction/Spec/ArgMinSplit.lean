import RMQ.Core.SuccinctClose.EndpointFringe.PrefixRange.SparseArgMin

/-!
# PRE-1 S1: splitting the leftmost block-argmin fold

Machine-free specification layer (outside the builder firewall). The sparse
interior tables store `SuccinctClose.bpRangeArgMinBlock shape blockSize start
count`, a left fold of `bpBetterArgMinBlock` over the block indices
`start, start + 1, ..., start + count - 1` seeded with `start`. A linear-time
builder fills these by doubling: the range of length `2^(l+1)` is the `better`
of its two halves of length `2^l`.

The only property used is that `bpBetterArgMinBlock` (strict `<` from the right,
so ties keep the left block) is associative as a function of the block indices.
Its key is `bpExcessAt shape (bpBlockArgMinPrefixPos shape blockSize block)`,
the reference value with all of `bpBlockArgMinPrefixPos`'s clamps to the BP
length; the split law is proved for that exact key and needs no clamp or size
premise. The only side condition is that the right part is nonempty, which is
necessary (a zero-length right part would still be compared).
-/

namespace RMQ.SuccinctFinal.PackedConstruction.Spec

open RMQ.Cartesian RMQ.SuccinctClose

theorem bpBetterArgMinBlock_self (shape : CartesianShape) (blockSize block : Nat) :
    bpBetterArgMinBlock shape blockSize block block = block := by
  unfold bpBetterArgMinBlock
  split <;> rfl

/-- Leftmost-argmin selection is associative. -/
theorem bpBetterArgMinBlock_assoc (shape : CartesianShape) (blockSize a b c : Nat) :
    bpBetterArgMinBlock shape blockSize (bpBetterArgMinBlock shape blockSize a b) c =
      bpBetterArgMinBlock shape blockSize a (bpBetterArgMinBlock shape blockSize b c) := by
  unfold bpBetterArgMinBlock
  by_cases hba : bpExcessAt shape (bpBlockArgMinPrefixPos shape blockSize b) <
      bpExcessAt shape (bpBlockArgMinPrefixPos shape blockSize a)
  · by_cases hcb : bpExcessAt shape (bpBlockArgMinPrefixPos shape blockSize c) <
        bpExcessAt shape (bpBlockArgMinPrefixPos shape blockSize b)
    · have hca : bpExcessAt shape (bpBlockArgMinPrefixPos shape blockSize c) <
          bpExcessAt shape (bpBlockArgMinPrefixPos shape blockSize a) := by omega
      simp [hba, hcb, hca]
    · simp [hba, hcb]
  · by_cases hcb : bpExcessAt shape (bpBlockArgMinPrefixPos shape blockSize c) <
        bpExcessAt shape (bpBlockArgMinPrefixPos shape blockSize b)
    · simp [hba, hcb]
    · have hca : ¬ bpExcessAt shape (bpBlockArgMinPrefixPos shape blockSize c) <
          bpExcessAt shape (bpBlockArgMinPrefixPos shape blockSize a) := by omega
      simp [hba, hcb, hca]

/-- A seed can be factored out of the fold. -/
theorem bpRangeArgMinBlockFrom_better (shape : CartesianShape) (blockSize : Nat) :
    ∀ (block steps x y : Nat),
      bpRangeArgMinBlockFrom shape blockSize block steps
          (bpBetterArgMinBlock shape blockSize x y) =
        bpBetterArgMinBlock shape blockSize x
          (bpRangeArgMinBlockFrom shape blockSize block steps y)
  | block, 0, x, y => rfl
  | block, steps + 1, x, y => by
      simp only [bpRangeArgMinBlockFrom]
      rw [bpBetterArgMinBlock_assoc, bpRangeArgMinBlockFrom_better]

/-- The fold over `s₁ + s₂` steps continues from the fold over `s₁` steps. -/
theorem bpRangeArgMinBlockFrom_add (shape : CartesianShape) (blockSize : Nat) :
    ∀ (block s₁ s₂ best : Nat),
      bpRangeArgMinBlockFrom shape blockSize block (s₁ + s₂) best =
        bpRangeArgMinBlockFrom shape blockSize (block + s₁) s₂
          (bpRangeArgMinBlockFrom shape blockSize block s₁ best)
  | block, 0, s₂, best => by simp [bpRangeArgMinBlockFrom]
  | block, s₁ + 1, s₂, best => by
      rw [show s₁ + 1 + s₂ = (s₁ + s₂) + 1 by omega]
      simp only [bpRangeArgMinBlockFrom]
      rw [bpRangeArgMinBlockFrom_add shape blockSize (block + 1) s₁ s₂,
        show block + 1 + s₁ = block + (s₁ + 1) by omega]

/-- **Split law.** For every shape, block size, start and left length `a`, and
every nonempty right length `b`, the range argmin over `a + b` blocks is the
leftmost-better of the argmins of the two parts. -/
theorem bpRangeArgMinBlock_split (shape : CartesianShape) (blockSize start a b : Nat)
    (hb : 0 < b) :
    bpRangeArgMinBlock shape blockSize start (a + b) =
      bpBetterArgMinBlock shape blockSize
        (bpRangeArgMinBlock shape blockSize start a)
        (bpRangeArgMinBlock shape blockSize (start + a) b) := by
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  cases a with
  | zero =>
      rw [Nat.zero_add, Nat.add_zero]
      simp only [bpRangeArgMinBlock]
      rw [← bpRangeArgMinBlockFrom_better]
      simp only [Nat.add_zero, bpBetterArgMinBlock_self]
  | succ a =>
      rw [show a + 1 + (b' + 1) = (a + (b' + 1)) + 1 by omega]
      simp only [bpRangeArgMinBlock]
      rw [bpRangeArgMinBlockFrom_add, show start + 1 + a = start + (a + 1) by omega]
      simp only [bpRangeArgMinBlockFrom]
      rw [bpRangeArgMinBlockFrom_better]

/-- **Doubling law** used by the sparse memo: for every span `c` (including 0). -/
theorem bpRangeArgMinBlock_double (shape : CartesianShape) (blockSize start c : Nat) :
    bpRangeArgMinBlock shape blockSize start (c + c) =
      bpBetterArgMinBlock shape blockSize
        (bpRangeArgMinBlock shape blockSize start c)
        (bpRangeArgMinBlock shape blockSize (start + c) c) := by
  cases c with
  | zero => simp [bpRangeArgMinBlock, bpBetterArgMinBlock_self]
  | succ c => exact bpRangeArgMinBlock_split shape blockSize start (c + 1) (c + 1) (by omega)

/-- The power-of-two instance consumed by the level-`l + 1` memo row. -/
theorem bpRangeArgMinBlock_pow_succ (shape : CartesianShape) (blockSize start l : Nat) :
    bpRangeArgMinBlock shape blockSize start (2 ^ (l + 1)) =
      bpBetterArgMinBlock shape blockSize
        (bpRangeArgMinBlock shape blockSize start (2 ^ l))
        (bpRangeArgMinBlock shape blockSize (start + 2 ^ l) (2 ^ l)) := by
  rw [Nat.pow_succ, Nat.mul_two]
  exact bpRangeArgMinBlock_double shape blockSize start (2 ^ l)

/-- Macro-granularity doubling: spans `2^(l+1) * m` split into two `2^l * m`
halves, for every macro size `m` (including 0). -/
theorem bpRangeArgMinBlock_pow_succ_mul (shape : CartesianShape)
    (blockSize start l m : Nat) :
    bpRangeArgMinBlock shape blockSize start (2 ^ (l + 1) * m) =
      bpBetterArgMinBlock shape blockSize
        (bpRangeArgMinBlock shape blockSize start (2 ^ l * m))
        (bpRangeArgMinBlock shape blockSize (start + 2 ^ l * m) (2 ^ l * m)) := by
  rw [Nat.pow_succ, Nat.mul_two, Nat.add_mul]
  exact bpRangeArgMinBlock_double shape blockSize start (2 ^ l * m)

/-- The single-block range is the block itself. -/
@[simp] theorem bpRangeArgMinBlock_one (shape : CartesianShape) (blockSize start : Nat) :
    bpRangeArgMinBlock shape blockSize start 1 = start := rfl

end RMQ.SuccinctFinal.PackedConstruction.Spec
