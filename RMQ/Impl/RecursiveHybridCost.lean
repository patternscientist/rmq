import RMQ.Core.CostKernels
import RMQ.Impl.RecursiveHybrid

/-!
# Recursive-hybrid cost recurrence

This module starts the cost model for the self-recursive hybrid backend. It
keeps the recurrence explicit:

* building the block-minimum summary costs one block scan/value-read budget per
  full block, plus the recursive summary build cost;
* querying charges the two boundary scans, the supplied summary-query cost, and
  two combines when the aligned middle schedule is used, otherwise it charges
  one direct range scan.

The definitions are parameterized over the summary query cost so the next layer
can instantiate them with another recursive call.
-/

namespace RMQ.RecursiveHybrid

/-- Cost of computing one full-block summary entry. -/
def blockSummaryEntryCost (b : Nat) : Nat :=
  b

/-- Cost of materializing all full-block minimum summary values. -/
def blockMinSummaryBuildCost (xs : List Int) (b : Nat) : Nat :=
  compressedLength xs.length b * blockSummaryEntryCost b

/-- Costed block-minimum summary build. -/
def blockMinSummaryCosted (xs : List Int) (b : Nat) :
    Costed (List Int) :=
  Costed.tickValue (blockMinSummaryBuildCost xs b) (blockMinSummary xs b)

@[simp] theorem blockMinSummaryCosted_value
    (xs : List Int) (b : Nat) :
    (blockMinSummaryCosted xs b).value = blockMinSummary xs b := by
  rfl

@[simp] theorem blockMinSummaryCosted_erase
    (xs : List Int) (b : Nat) :
    Costed.erase (blockMinSummaryCosted xs b) = blockMinSummary xs b := by
  rfl

theorem blockMinSummaryCosted_cost
    (xs : List Int) (b : Nat) :
    (blockMinSummaryCosted xs b).cost = blockMinSummaryBuildCost xs b := by
  rfl

/-- Build-cost recurrence for the public recursive hybrid shape. -/
def buildCost (xs : List Int) : Nat :=
  recurseOnSummary publicBlockSummaryShape
    (motive := fun _ => Nat)
    (fun _ _ => 0)
    (fun xs _hlarge summaryCost =>
      let b := Nat.log2 xs.length + 1
      blockMinSummaryBuildCost xs b + summaryCost)
    xs

theorem buildCost_of_small
    {xs : List Int} (hsmall : xs.length <= 1) :
    buildCost xs = 0 := by
  unfold buildCost
  rw [recurseOnSummary_of_small publicBlockSummaryShape _ _ hsmall]

theorem buildCost_of_large
    {xs : List Int} (hlarge : 1 < xs.length) :
    buildCost xs =
      let b := Nat.log2 xs.length + 1
      blockMinSummaryBuildCost xs b +
        buildCost (blockMinSummary xs b) := by
  unfold buildCost
  rw [recurseOnSummary_of_large publicBlockSummaryShape _ _ hlarge]
  simp [publicBlockSummaryShape]

/-- Query-step cost with a supplied summary-query cost function. -/
def queryWithSummaryCost
    (xs : List Int) (b : Nat)
    (summaryCost : Nat -> Nat -> Nat)
    (left right : Nat) : Nat :=
  if _h : ValidRange xs left right /\ 0 < b then
    let leftBlock := leftBoundaryBlock left b
    let rightBlock := rightBoundaryBlock right b
    if _hschedule : leftBlock <= rightBlock then
      rangeScanCost xs left (leftBlock * b) +
        summaryCost leftBlock rightBlock +
          rangeScanCost xs (rightBlock * b) right + 2
    else
      rangeScanCost xs left right
  else
    1

/-- Costed recursive-hybrid query step with a supplied costed summary query. -/
def queryWithSummaryCosted
    (xs : List Int) (b : Nat)
    (summaryQuery : Nat -> Nat -> Costed (Option Nat))
    (left right : Nat) : Costed (Option Nat) :=
  if _h : ValidRange xs left right /\ 0 < b then
    let leftBlock := leftBoundaryBlock left b
    let rightBlock := rightBoundaryBlock right b
    if _hschedule : leftBlock <= rightBlock then
      Costed.bind (rangeScanCosted xs left (leftBlock * b)) fun leftCandidate =>
        Costed.bind
          (Costed.map (liftBlockCandidate xs b)
            (summaryQuery leftBlock rightBlock)) fun middleCandidate =>
          Costed.bind
            (rangeScanCosted xs (rightBlock * b) right) fun rightCandidate =>
            Costed.tickValue 2
              (combineIndex xs
                (combineIndex xs leftCandidate middleCandidate)
                rightCandidate)
    else
      rangeScanCosted xs left right
  else
    Costed.tickValue 1 none

@[simp] theorem queryWithSummaryCosted_value
    (xs : List Int) (b : Nat)
    (summaryBackend : RMQBackend (blockMinSummary xs b))
    (summaryQuery : Nat -> Nat -> Costed (Option Nat))
    (hsummary :
      forall left right,
        (summaryQuery left right).value =
          summaryBackend.query summaryBackend.build left right)
    (left right : Nat) :
    (queryWithSummaryCosted xs b summaryQuery left right).value =
      queryWithSummaryBackend xs b summaryBackend left right := by
  unfold queryWithSummaryCosted queryWithSummaryBackend
  by_cases hif : ValidRange xs left right /\ 0 < b
  · rw [dif_pos hif, dif_pos hif]
    by_cases hschedule :
        leftBoundaryBlock left b <= rightBoundaryBlock right b
    · rw [dif_pos hschedule, dif_pos hschedule]
      simp [rangeScanCosted_value, Costed.map_value,
        recursiveMiddleCandidate, hsummary, rangeScan, LinearScan.query]
    · rw [dif_neg hschedule, dif_neg hschedule]
      simp [rangeScanCosted_value, rangeScan, LinearScan.query]
  · rw [dif_neg hif, dif_neg hif]
    simp

@[simp] theorem queryWithSummaryCosted_erase
    (xs : List Int) (b : Nat)
    (summaryBackend : RMQBackend (blockMinSummary xs b))
    (summaryQuery : Nat -> Nat -> Costed (Option Nat))
    (hsummary :
      forall left right,
        (summaryQuery left right).value =
          summaryBackend.query summaryBackend.build left right)
    (left right : Nat) :
    Costed.erase (queryWithSummaryCosted xs b summaryQuery left right) =
      queryWithSummaryBackend xs b summaryBackend left right := by
  exact queryWithSummaryCosted_value xs b summaryBackend summaryQuery hsummary
    left right

theorem queryWithSummaryCosted_cost
    (xs : List Int) (b : Nat)
    (summaryQuery : Nat -> Nat -> Costed (Option Nat))
    (left right : Nat) :
    (queryWithSummaryCosted xs b summaryQuery left right).cost =
      queryWithSummaryCost xs b
        (fun left right => (summaryQuery left right).cost) left right := by
  unfold queryWithSummaryCosted queryWithSummaryCost
  by_cases hif : ValidRange xs left right /\ 0 < b
  · rw [dif_pos hif, dif_pos hif]
    by_cases hschedule :
        leftBoundaryBlock left b <= rightBoundaryBlock right b
    · rw [dif_pos hschedule, dif_pos hschedule]
      simp [rangeScanCosted_cost, Costed.map_cost]
      omega
    · rw [dif_neg hschedule, dif_neg hschedule]
      simp [rangeScanCosted_cost]
  · rw [dif_neg hif, dif_neg hif]
    simp

theorem queryWithSummaryCosted_run
    (xs : List Int) (b : Nat)
    (summaryBackend : RMQBackend (blockMinSummary xs b))
    (summaryQuery : Nat -> Nat -> Costed (Option Nat))
    (hsummary :
      forall left right,
        (summaryQuery left right).value =
          summaryBackend.query summaryBackend.build left right)
    (left right : Nat) :
    Costed.run (queryWithSummaryCosted xs b summaryQuery left right) =
      (queryWithSummaryBackend xs b summaryBackend left right,
        queryWithSummaryCost xs b
          (fun left right => (summaryQuery left right).cost) left right) := by
  simp [Costed.run,
    queryWithSummaryCosted_value xs b summaryBackend summaryQuery hsummary left right,
    queryWithSummaryCosted_cost]

end RMQ.RecursiveHybrid
