import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
ADVERSARIAL AUDIT of `zkd_f01_k_decision.lean` (lane k-decision).
-/

namespace QvzA

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctSelect

/-! ## A. Non-vacuity: shapes of size 0 and 1 exist -/

def s0 : CartesianShape := .empty
def s1 : CartesianShape := .node .empty .empty
def s2 : CartesianShape := .node (.node .empty .empty) .empty
def chain : Nat -> CartesianShape
  | 0 => .empty
  | n + 1 => .node (chain n) .empty

example : s0.size = 0 := rfl
example : s1.size = 1 := rfl
example : s2.size = 2 := rfl
#eval "A. sizes of chain 0..7:"
#eval (List.range 8).map (fun k => (chain k).size)

/-! ## B. Restate the lane's definitions verbatim -/

def frozenWordWidth (n : Nat) : Nat := SuccinctRank.machineWordBits (2 * n)
def paddedLongBits (n : Nat) : Nat := compactLongSuperRelativeTableOverhead n
def paddedSparseBits (n : Nat) : Nat := sparseExceptionRelativeTableOverhead n
def selectPadRho (n : Nat) : Nat := paddedLongBits n + paddedSparseBits n

def longSpanOfSize (n : Nat) : Nat :=
  SuccinctRank.machineWordBits (2 * n) *
      SuccinctRank.machineWordBits (2 * n) *
      SuccinctRank.machineWordBits (2 * n) *
    (Nat.log2 (SuccinctRank.machineWordBits (2 * n)) + 1)

def localStrideOfSize (n : Nat) : Nat :=
  max 1
    (SuccinctRank.machineWordBits (2 * n) /
      ((Nat.log2 (SuccinctRank.machineWordBits (2 * n)) + 1) *
        (Nat.log2 (SuccinctRank.machineWordBits (2 * n)) + 1)))

def refinedLongBudget (n : Nat) : Nat :=
  if 2 * n < longSpanOfSize n then 0 else paddedLongBits n
def refinedSparseBudget (n : Nat) : Nat :=
  if localStrideOfSize n = 1 then 0 else paddedSparseBits n

/-! ## C. n = 0 and n = 1: instantiate, and CHECK THE NUMBERS -/

example : (0 : Nat) < 2 ^ frozenWordWidth 0 := by decide
example : (1 : Nat) < 2 ^ frozenWordWidth 1 := by decide

#eval "C. (n, frozenWordWidth n, longSpanOfSize n, 2n<span, localStride, refLong, refSparse, padLong, padSparse) for n=0,1,2,3"
#eval (List.range 4).map (fun n =>
  (n, frozenWordWidth n, longSpanOfSize n, decide (2 * n < longSpanOfSize n),
   localStrideOfSize n, refinedLongBudget n, refinedSparseBudget n,
   paddedLongBits n, paddedSparseBits n))

-- The refined regime hypotheses hold at n = 0 and n = 1 (so the "no dead cell"
-- theorem is not vacuous there).
example : 2 * 0 < longSpanOfSize 0 := by decide
example : localStrideOfSize 0 = 1 := by decide
example : 2 * 1 < longSpanOfSize 1 := by decide
example : localStrideOfSize 1 = 1 := by decide

/-! ## D. THE IDENTITY QUESTION.
The frozen reviewer payload segments `.selectLongRelative` / `.selectSparseRelative`
come from `GenericSelect.sparseExceptionSelectData shape.bpCode false`.
The lane's theorems are about `builtRelativeSplitFalseSelect...`.
Are they the same objects? -/

def genericLong (shape : CartesianShape) : Nat :=
  (RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape
    .selectLongRelative).length
def genericSparse (shape : CartesianShape) : Nat :=
  (RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape
    .selectSparseRelative).length
def builtLong (shape : CartesianShape) : Nat :=
  (builtRelativeSplitFalseSelectLongSuperRelativeTable shape).payload.length
def builtSparse (shape : CartesianShape) : Nat :=
  (builtRelativeSplitFalseSelectSparseExceptionRelativeTable shape).payload.length

#eval "D. (size, genericLong, builtLong, genericSparse, builtSparse) -- must agree"
#eval (List.range 9).map (fun k =>
  let sh := chain k
  (sh.size, genericLong sh, builtLong sh, genericSparse sh, builtSparse sh))

/-! ## E. THE COMPOSITION QUESTION.
`selectPadRho_le_charged_overhead` proves only
  paddedLong + paddedSparse <= genericSparseExceptionBPCloseAccessOverhead n.
Space neutrality needs
  (other live-access segments) + paddedLong + paddedSparse <= overhead n.
Measure both. -/

def liveAccessLen (shape : CartesianShape) : Nat :=
  (RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessPayload
    shape).length

def liveAccessPaddedLen (shape : CartesianShape) : Nat :=
  liveAccessLen shape - genericLong shape - genericSparse shape +
    paddedLongBits shape.size + paddedSparseBits shape.size

def liveAccessRefinedLen (shape : CartesianShape) : Nat :=
  liveAccessLen shape - genericLong shape - genericSparse shape +
    refinedLongBudget shape.size + refinedSparseBudget shape.size

def chargedOverhead (n : Nat) : Nat :=
  RMQ.SuccinctFinal.genericSparseExceptionBPCloseAccessOverhead n

#eval "E. (size, liveAccessLen, liveAccessPaddedLen, liveAccessRefinedLen, chargedOverhead, padded<=oh?, refined<=oh?)"
#eval (List.range 9).map (fun k =>
  let sh := chain k
  (sh.size, liveAccessLen sh, liveAccessPaddedLen sh, liveAccessRefinedLen sh,
   chargedOverhead sh.size,
   decide (liveAccessPaddedLen sh <= chargedOverhead sh.size),
   decide (liveAccessRefinedLen sh <= chargedOverhead sh.size)))

/-! ## F. Is `selectPadRho <= chargedOverhead` a tight or vacuous statement?
Compare selectPadRho against the WHOLE overhead. -/

#eval "F. (n, selectPadRho n, chargedOverhead n, 2n)"
#eval [0,1,2,4,8,16,64,256,1024,8192,524288].map (fun n =>
  (n, selectPadRho n, chargedOverhead n, 2 * n))

/-! ## G. Does the frozen width agree with the F03-pinned route word size? -/

#eval "G. (size, builtRelativeSplitBPCloseRankWordSize, frozenWordWidth size)"
#eval (List.range 9).map (fun k =>
  let sh := chain k
  (sh.size, RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankWordSize sh,
   frozenWordWidth sh.size))

end QvzA
