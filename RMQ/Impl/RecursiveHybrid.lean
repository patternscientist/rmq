import RMQ.Core.Schedule
import RMQ.Core.Recursion
import RMQ.Impl.LinearScan

/-!
# Self-recursive hybrid RMQ

This module instantiates the recursive-middle combinator with an aligned query
schedule. Boundary fragments are answered by direct scans; the middle full
blocks are answered by a backend recursively built for the block-minimum
summary list.
-/

namespace RMQ.RecursiveHybrid

/-- Option-level argmin combination. `none` represents an absent subrange. -/
abbrev combineIndex := RMQ.combineIndex

/-- Direct scan over a half-open range. -/
abbrev rangeScan := RMQ.LinearScan.query

/--
Query with aligned boundary scans and a recursively supplied summary backend.

If the requested interval contains no complete aligned boundary fragment, this
falls back to a direct scan. Otherwise it scans the left boundary fragment,
queries the summary backend over the full middle blocks, lifts that candidate
back to the original list, and scans the right boundary fragment.
-/
def queryWithSummaryBackend
    (xs : List Int) (b : Nat)
    (summaryBackend : RMQBackend (blockMinSummary xs b))
    (left right : Nat) : Option Nat :=
  if _h : ValidRange xs left right /\ 0 < b then
    let leftBlock := leftBoundaryBlock left b
    let rightBlock := rightBoundaryBlock right b
    if _hschedule : leftBlock <= rightBlock then
      combineIndex xs
        (combineIndex xs (rangeScan xs left (leftBlock * b))
          (recursiveMiddleCandidate xs b summaryBackend leftBlock rightBlock))
        (rangeScan xs (rightBlock * b) right)
    else
      rangeScan xs left right
  else
    none

theorem queryWithSummaryBackend_invalid_none
    {xs : List Int} {b : Nat}
    {summaryBackend : RMQBackend (blockMinSummary xs b)}
    {left right : Nat}
    (hbad : Not (ValidRange xs left right)) :
    queryWithSummaryBackend xs b summaryBackend left right = none := by
  unfold queryWithSummaryBackend
  by_cases hif : ValidRange xs left right /\ 0 < b
  · exact False.elim (hbad hif.1)
  · simp [hif]

theorem queryWithSummaryBackend_valid_exact
    (xs : List Int) (b : Nat)
    (summaryBackend : RMQBackend (blockMinSummary xs b))
    (left right : Nat)
    (hb : 0 < b) (hValid : ValidRange xs left right) :
    exists idx,
      queryWithSummaryBackend xs b summaryBackend left right = some idx /\
        LeftmostArgMin xs left right idx := by
  let leftBlock := leftBoundaryBlock left b
  let rightBlock := rightBoundaryBlock right b
  have hif : ValidRange xs left right /\ 0 < b := ⟨hValid, hb⟩
  by_cases hschedule : leftBlock <= rightBlock
  · have hquery :
        queryWithSummaryBackend xs b summaryBackend left right =
          combineIndex xs
            (combineIndex xs (rangeScan xs left (leftBlock * b))
              (recursiveMiddleCandidate xs b summaryBackend leftBlock rightBlock))
            (rangeScan xs (rightBlock * b) right) := by
      unfold queryWithSummaryBackend
      simp [hif, leftBlock, rightBlock, hschedule]
    have hleft_lt_end : left < leftBlock * b := by
      simpa [leftBlock] using left_lt_leftBoundaryBlock_mul (left := left) hb
    have hrightStart_le_right : rightBlock * b <= right := by
      simpa [rightBlock] using rightBoundaryBlock_mul_le right b
    have hleftEnd_le_rightStart : leftBlock * b <= rightBlock * b :=
      Nat.mul_le_mul_right b hschedule
    have hleftEnd_le_right : leftBlock * b <= right :=
      Nat.le_trans hleftEnd_le_rightStart hrightStart_le_right
    have hleftValid : ValidRange xs left (leftBlock * b) := by
      exact ⟨hleft_lt_end, Nat.le_trans hleftEnd_le_right hValid.2⟩
    rcases RMQ.LinearScan.query_valid_exact xs left (leftBlock * b)
        hleftValid with
      ⟨li, hlres, hlarg⟩
    have hrightCase :
        CandidateExact xs (rightBlock * b) right
          (rangeScan xs (rightBlock * b) right) := by
      by_cases hright_nonempty : rightBlock * b < right
      · have hrightValid : ValidRange xs (rightBlock * b) right :=
          ⟨hright_nonempty, hValid.2⟩
        rcases RMQ.LinearScan.query_valid_exact xs (rightBlock * b) right
            hrightValid with
          ⟨ri, hrres, hrarg⟩
        exact Or.inr ⟨ri, hrres, hrarg⟩
      · have hright_empty : rightBlock * b = right := by omega
        have hright_none : rangeScan xs (rightBlock * b) right = none := by
          exact RMQ.LinearScan.invalid_none (by
            intro hbad
            omega)
        exact Or.inl ⟨hright_none, hright_empty⟩
    have hrightBlock :
        rightBlock <= compressedLength xs.length b := by
      simpa [rightBlock] using
        rightBoundaryBlock_le_compressed (xs := xs) (b := b)
          (right := right) hb hValid.2
    rcases combineRecursiveMiddleLeftmost
        (xs := xs) (b := b) (left := left)
        (leftBlock := leftBlock) (rightBlock := rightBlock)
        (right := right) (li := li)
        (rightCandidate := rangeScan xs (rightBlock * b) right)
        summaryBackend hb hlarg hschedule hrightBlock hrightCase
        hrightStart_le_right with
      ⟨idx, hcombined, harg⟩
    refine ⟨idx, ?_, harg⟩
    rw [hquery]
    simpa [hlres, combineIndex, RMQ.combineIndex] using hcombined
  · have hquery :
        queryWithSummaryBackend xs b summaryBackend left right =
          rangeScan xs left right := by
      unfold queryWithSummaryBackend
      simp [hif, leftBlock, rightBlock, hschedule]
    rcases RMQ.LinearScan.query_valid_exact xs left right hValid with
      ⟨idx, hres, harg⟩
    refine ⟨idx, ?_, harg⟩
    rw [hquery]
    simpa [rangeScan] using hres

theorem queryWithSummaryBackend_sound
    {xs : List Int} {b : Nat}
    {summaryBackend : RMQBackend (blockMinSummary xs b)}
    {left right idx : Nat}
    (hb : 0 < b)
    (hres : queryWithSummaryBackend xs b summaryBackend left right = some idx) :
    LeftmostArgMin xs left right idx := by
  by_cases hValid : ValidRange xs left right
  · rcases queryWithSummaryBackend_valid_exact xs b summaryBackend left right hb
        hValid with
      ⟨idx', hres', harg'⟩
    have hidx : idx = idx' := by
      have hsome : some idx = some idx' := by
        rw [← hres, hres']
      exact Option.some.inj hsome
    simpa [hidx] using harg'
  · have hnone := queryWithSummaryBackend_invalid_none
      (summaryBackend := summaryBackend) hValid
    rw [hnone] at hres
    contradiction

theorem queryWithSummaryBackend_complete
    {xs : List Int} {b : Nat}
    {summaryBackend : RMQBackend (blockMinSummary xs b)}
    {left right idx : Nat}
    (hb : 0 < b)
    (harg : LeftmostArgMin xs left right idx) :
    queryWithSummaryBackend xs b summaryBackend left right = some idx := by
  have hValid : ValidRange xs left right := LeftmostArgMin.valid harg
  rcases queryWithSummaryBackend_valid_exact xs b summaryBackend left right hb
      hValid with
    ⟨idx', hres', harg'⟩
  have hidx : idx' = idx :=
    leftmostArgMin_unique xs left right idx' idx harg' harg
  simpa [hidx] using hres'

/-- A backend assembled from a positive block size and a backend for its summary. -/
def backendWithSummary
    (xs : List Int) (b : Nat)
    (summaryBackend : RMQBackend (blockMinSummary xs b))
    (hb : 0 < b) : RMQBackend xs where
  State := Unit
  build := ()
  query := fun _ => queryWithSummaryBackend xs b summaryBackend
  sound := by
    intro left right idx hres
    exact queryWithSummaryBackend_sound (summaryBackend := summaryBackend) hb hres
  complete := by
    intro left right idx harg
    exact queryWithSummaryBackend_complete
      (summaryBackend := summaryBackend) hb harg
  invalid_none := by
    intro left right hbad
    exact queryWithSummaryBackend_invalid_none
      (summaryBackend := summaryBackend) hbad

/-- Public self-recursive hybrid backend. -/
def backend (xs : List Int) : RMQBackend xs :=
  recurseOnSummary publicBlockSummaryShape
    (motive := fun xs => RMQBackend xs)
    (fun xs _hsmall => RMQ.LinearScan.backend xs)
    (fun xs _hlarge summaryBackend =>
      backendWithSummary xs (Nat.log2 xs.length + 1)
        (by
          simpa [publicBlockSummaryShape] using summaryBackend)
        (by omega))
    xs

/-- Public query over the self-recursive hybrid backend. -/
def query (xs : List Int) (left right : Nat) : Option Nat :=
  let b := backend xs
  b.query b.build left right

theorem query_sound {xs : List Int} {left right idx : Nat}
    (hres : query xs left right = some idx) :
    LeftmostArgMin xs left right idx := by
  unfold query at hres
  let b := backend xs
  exact b.sound hres

theorem query_complete {xs : List Int} {left right idx : Nat}
    (harg : LeftmostArgMin xs left right idx) :
    query xs left right = some idx := by
  unfold query
  let b := backend xs
  exact b.complete harg

theorem invalid_none {xs : List Int} {left right : Nat}
    (hbad : Not (ValidRange xs left right)) :
    query xs left right = none := by
  unfold query
  let b := backend xs
  exact b.invalid_none hbad

example : query [5, 2, 7, 1, 3] 1 4 = some 3 := by native_decide
example : query [4, 1, 1, 2] 0 4 = some 1 := by native_decide
example : query [5, 2, 7] 2 2 = none := by native_decide
example : query [9, 6, 8, 4, 7, 3, 5, 2, 1, 10] 2 9 = some 8 := by
  native_decide

end RMQ.RecursiveHybrid
