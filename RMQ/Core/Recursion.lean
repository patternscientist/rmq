import RMQ.Core.Backend
import RMQ.Core.Window

/-!
# Mathlib-free well-founded recursion helpers

This module isolates the self-referential recursion pattern needed for
recursive hybrid RMQ constructions. Recursive calls are available only on
strictly shorter input lists, measured by `List.length`.
-/

namespace RMQ

/--
Well-founded recursion over lists ordered by length.

The step receives a recursive hypothesis for any strictly shorter list. This is
the ergonomic form we want for recursive RMQ constructions: a summary problem
can call back into the same construction once its length shrink proof is known.
-/
def lengthRec
    {motive : List Int -> Sort u}
    (step : (xs : List Int) ->
      ((ys : List Int) -> ys.length < xs.length -> motive ys) -> motive xs)
    (xs : List Int) : motive xs :=
  step xs (fun ys _h => lengthRec step ys)
termination_by xs.length
decreasing_by
  assumption

/-- Number of full `b`-sized blocks in a list of length `n`. -/
def compressedLength (n b : Nat) : Nat :=
  n / b

theorem compressedLength_lt_self
    {n b : Nat} (hn : 0 < n) (hb : 1 < b) :
    compressedLength n b < n := by
  unfold compressedLength
  exact Nat.div_lt_self hn hb

theorem block_bound_of_lt_compressedLength
    {n b q : Nat} (hb : 0 < b) (hq : q < compressedLength n b) :
    q * b + b <= n := by
  unfold compressedLength at hq
  have hsucc_le : q + 1 <= n / b := by omega
  have hmul_le : (q + 1) * b <= n := by
    exact (Nat.le_div_iff_mul_le hb).1 hsucc_le
  rw [Nat.add_mul] at hmul_le
  simpa [Nat.one_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hmul_le

theorem block_start_lt_of_lt_compressedLength
    {n b q : Nat} (hb : 0 < b) (hq : q < compressedLength n b) :
    q * b < n := by
  have hbound := block_bound_of_lt_compressedLength (n := n) hb hq
  omega

/-- Original-list index selected as the leftmost minimum of full block `q`. -/
def blockMinIndex (xs : List Int) (b q : Nat) : Nat :=
  scanWindow xs (q * b) b

/-- Value stored for full block `q`; invalid blocks fall back to `0`. -/
def blockMinValue (xs : List Int) (b q : Nat) : Int :=
  match xs[blockMinIndex xs b q]? with
  | some v => v
  | none => 0

/-- Full-block summary values for a fixed block size. -/
def blockMinSummary (xs : List Int) (b : Nat) : List Int :=
  List.ofFn (fun q : Fin (compressedLength xs.length b) =>
    blockMinValue xs b q.1)

theorem blockMinSummary_length (xs : List Int) (b : Nat) :
    (blockMinSummary xs b).length = compressedLength xs.length b := by
  simp [blockMinSummary]

theorem blockMinSummary_get?_eq_blockMinValue
    (xs : List Int) (b q : Nat) (hq : q < compressedLength xs.length b) :
    (blockMinSummary xs b)[q]? = some (blockMinValue xs b q) := by
  have hrow : q < (blockMinSummary xs b).length := by
    simpa [blockMinSummary_length] using hq
  rw [List.getElem?_eq_getElem hrow]
  unfold blockMinSummary
  simp

theorem blockMinIndex_leftmost
    (xs : List Int) (b q : Nat)
    (hb : 0 < b) (hq : q < compressedLength xs.length b) :
    LeftmostArgMin xs (q * b) (q * b + b) (blockMinIndex xs b q) := by
  unfold blockMinIndex
  have hbound : q * b + b <= xs.length :=
    block_bound_of_lt_compressedLength (n := xs.length) hb hq
  exact scanWindow_leftmost xs (q * b) b hb hbound

theorem blockMinSummary_entry_exact
    (xs : List Int) (b q : Nat)
    (hb : 0 < b) (hq : q < compressedLength xs.length b) :
    exists idx v,
      (blockMinSummary xs b)[q]? = some v /\
        xs[idx]? = some v /\
        LeftmostArgMin xs (q * b) (q * b + b) idx := by
  have harg := blockMinIndex_leftmost xs b q hb hq
  rcases harg with ⟨_hpos, _hlen, _hleft, _hright, v, hget, hmin, hleftmost⟩
  refine ⟨blockMinIndex xs b q, v, ?_, hget, ?_⟩
  · have hsummary := blockMinSummary_get?_eq_blockMinValue xs b q hq
    unfold blockMinValue at hsummary
    simp [hget] at hsummary
    exact hsummary
  · exact ⟨_hpos, _hlen, _hleft, _hright, v, hget, hmin, hleftmost⟩

theorem blockMinSummary_lift_leftmost
    (xs : List Int) (b left right q : Nat)
    (hb : 0 < b)
    (hsummary : LeftmostArgMin (blockMinSummary xs b) left right q) :
    LeftmostArgMin xs (left * b) (right * b) (blockMinIndex xs b q) := by
  rcases hsummary with ⟨hleft_right, hright_len, hleft_q, hq_right, summaryVal,
    hq_summary_get, hsummary_min, hsummary_leftmost⟩
  have hright_le_compressed : right <= compressedLength xs.length b := by
    simpa [blockMinSummary_length] using hright_len
  have hq_compressed : q < compressedLength xs.length b := by omega
  have hq_block := blockMinIndex_leftmost xs b q hb hq_compressed
  rcases hq_block with ⟨_hq_pos, _hq_len, hq_block_left, hq_block_right,
    blockVal, hq_block_get, hq_block_min, hq_block_leftmost⟩
  have hq_summary_eq :=
    blockMinSummary_get?_eq_blockMinValue xs b q hq_compressed
  unfold blockMinValue at hq_summary_eq
  simp [hq_block_get] at hq_summary_eq
  have hsummary_blockVal : summaryVal = blockVal := by
    exact Option.some.inj (by rw [← hq_summary_get, hq_summary_eq])
  have hright_bound : right * b <= xs.length := by
    exact (Nat.le_div_iff_mul_le hb).1 hright_le_compressed
  have hrange_pos : left * b < right * b := by
    exact Nat.mul_lt_mul_of_pos_right hleft_right hb
  refine ⟨hrange_pos, hright_bound, ?_, ?_, blockVal, hq_block_get, ?_, ?_⟩
  · exact Nat.le_trans (Nat.mul_le_mul_right b hleft_q) hq_block_left
  · have hq_succ_bound : q * b + b <= right * b := by
      have hsucc_le : q + 1 <= right := by omega
      have hmul := Nat.mul_le_mul_right b hsucc_le
      rw [Nat.add_mul] at hmul
      simpa [Nat.one_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hmul
    omega
  · intro t w ht_left ht_right hget
    let j := t / b
    have hj_left : left <= j := by
      exact (Nat.le_div_iff_mul_le hb).2 ht_left
    have hj_right : j < right := by
      exact (Nat.div_lt_iff_lt_mul hb).2 ht_right
    have hj_compressed : j < compressedLength xs.length b := by omega
    rcases blockMinSummary_entry_exact xs b j hb hj_compressed with
      ⟨jIdx, jVal, hj_summary_get, hj_get, hj_arg⟩
    have hsummary_le : summaryVal <= jVal :=
      hsummary_min j jVal hj_left hj_right hj_summary_get
    have hblockVal_le_jVal : blockVal <= jVal := by
      simpa [hsummary_blockVal] using hsummary_le
    rcases hj_arg with ⟨_hj_pos, _hj_len, _hj_left, _hj_right, vj, hj_get_arg,
      hj_min, _hj_leftmost⟩
    have hvj : vj = jVal := by
      exact Option.some.inj (by rw [← hj_get_arg, hj_get])
    have ht_j_left : j * b <= t := by
      unfold j
      exact Nat.div_mul_le_self t b
    have ht_j_right : t < j * b + b := by
      unfold j
      exact Nat.lt_div_mul_add hb
    have hvj_le_w := hj_min t w ht_j_left ht_j_right hget
    omega
  · intro t w ht_left ht_idx hget
    let j := t / b
    have hj_left : left <= j := by
      exact (Nat.le_div_iff_mul_le hb).2 ht_left
    have ht_j_left : j * b <= t := by
      unfold j
      exact Nat.div_mul_le_self t b
    have ht_j_right : t < j * b + b := by
      unfold j
      exact Nat.lt_div_mul_add hb
    have ht_before_q_end : t < q * b + b := by
      exact Nat.lt_trans ht_idx hq_block_right
    have hj_lt_q_succ : j < q + 1 := by
      exact (Nat.div_lt_iff_lt_mul hb).2 (by
        simpa [Nat.add_mul, Nat.one_mul, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc] using ht_before_q_end)
    by_cases hj_before_q : j < q
    · have hj_compressed : j < compressedLength xs.length b := by omega
      rcases blockMinSummary_entry_exact xs b j hb hj_compressed with
        ⟨jIdx, jVal, hj_summary_get, hj_get, hj_arg⟩
      have hsummary_lt : summaryVal < jVal :=
        hsummary_leftmost j jVal hj_left hj_before_q hj_summary_get
      have hblockVal_lt_jVal : blockVal < jVal := by
        simpa [hsummary_blockVal] using hsummary_lt
      rcases hj_arg with ⟨_hj_pos, _hj_len, _hj_left, _hj_right, vj, hj_get_arg,
        hj_min, _hj_leftmost⟩
      have hvj : vj = jVal := by
        exact Option.some.inj (by rw [← hj_get_arg, hj_get])
      have hvj_le_w := hj_min t w ht_j_left ht_j_right hget
      omega
    · have hj_eq_q : j = q := by omega
      have ht_q_left : q * b <= t := by
        simpa [j, hj_eq_q] using ht_j_left
      exact hq_block_leftmost t w ht_q_left ht_idx hget

/-- Map a summary block candidate back to its original-list block-minimum index. -/
def liftBlockCandidate (xs : List Int) (b : Nat) : Option Nat -> Option Nat
  | none => none
  | some q => some (blockMinIndex xs b q)

theorem blockMinSummary_lift_candidate
    (xs : List Int) (b left right : Nat) {candidate : Option Nat}
    (hb : 0 < b)
    (hsummary : CandidateExact (blockMinSummary xs b) left right candidate) :
    CandidateExact xs (left * b) (right * b)
      (liftBlockCandidate xs b candidate) := by
  rcases hsummary with ⟨hnone, hempty⟩ | ⟨q, hsome, harg⟩
  · exact Or.inl ⟨by simp [liftBlockCandidate, hnone], by simp [hempty]⟩
  · refine Or.inr ⟨blockMinIndex xs b q, ?_, ?_⟩
    · simp [liftBlockCandidate, hsome]
    · exact blockMinSummary_lift_leftmost xs b left right q hb harg

/-- Query a summary backend on block indices, then lift its candidate. -/
def recursiveMiddleCandidate
    (xs : List Int) (b : Nat)
    (summaryBackend : RMQBackend (blockMinSummary xs b))
    (leftBlock rightBlock : Nat) : Option Nat :=
  liftBlockCandidate xs b
    (summaryBackend.query summaryBackend.build leftBlock rightBlock)

theorem recursiveMiddleCandidate_exact
    (xs : List Int) (b leftBlock rightBlock : Nat)
    (summaryBackend : RMQBackend (blockMinSummary xs b))
    (hb : 0 < b)
    (hblocks : leftBlock <= rightBlock)
    (hright : rightBlock <= compressedLength xs.length b) :
    CandidateExact xs (leftBlock * b) (rightBlock * b)
      (recursiveMiddleCandidate xs b summaryBackend leftBlock rightBlock) := by
  by_cases hnonempty : leftBlock < rightBlock
  · have hValid :
        ValidRange (blockMinSummary xs b) leftBlock rightBlock := by
      constructor
      · exact hnonempty
      · simpa [blockMinSummary_length] using hright
    let len := rightBlock - leftBlock
    have hlen : 0 < len := by
      unfold len
      omega
    have hbound : leftBlock + len <= (blockMinSummary xs b).length := by
      unfold len
      omega
    have hright_eq : leftBlock + len = rightBlock := by
      unfold len
      omega
    have harg_scan :=
      scanWindow_leftmost (blockMinSummary xs b) leftBlock len hlen hbound
    have harg :
        LeftmostArgMin (blockMinSummary xs b) leftBlock rightBlock
          (scanWindow (blockMinSummary xs b) leftBlock len) := by
      simpa [hright_eq] using harg_scan
    have hquery :
        summaryBackend.query summaryBackend.build leftBlock rightBlock =
          some (scanWindow (blockMinSummary xs b) leftBlock len) :=
      summaryBackend.complete harg
    have hsummary :
        CandidateExact (blockMinSummary xs b) leftBlock rightBlock
          (summaryBackend.query summaryBackend.build leftBlock rightBlock) :=
      Or.inr ⟨scanWindow (blockMinSummary xs b) leftBlock len, hquery, harg⟩
    simpa [recursiveMiddleCandidate] using
      blockMinSummary_lift_candidate xs b leftBlock rightBlock hb hsummary
  · have hempty : leftBlock = rightBlock := by omega
    have hbad :
        Not (ValidRange (blockMinSummary xs b) leftBlock rightBlock) := by
      intro hValid
      omega
    have hquery_none :
        summaryBackend.query summaryBackend.build leftBlock rightBlock = none :=
      summaryBackend.invalid_none hbad
    exact Or.inl ⟨by simp [recursiveMiddleCandidate, hquery_none, liftBlockCandidate],
      by simp [hempty]⟩

/--
Compose a nonempty left boundary, a recursively answered full-block middle, and
an optional right boundary into an exact original-list RMQ witness.
-/
theorem combineRecursiveMiddleLeftmost
    {xs : List Int} {b left leftBlock rightBlock right li : Nat}
    {rightCandidate : Option Nat}
    (summaryBackend : RMQBackend (blockMinSummary xs b))
    (hb : 0 < b)
    (hLeft : LeftmostArgMin xs left (leftBlock * b) li)
    (hblocks : leftBlock <= rightBlock)
    (hrightBlock : rightBlock <= compressedLength xs.length b)
    (hRight : CandidateExact xs (rightBlock * b) right rightCandidate)
    (hMiddleRight : rightBlock * b <= right) :
    exists idx,
      combineIndex xs
        (combineIndex xs (some li)
          (recursiveMiddleCandidate xs b summaryBackend leftBlock rightBlock))
        rightCandidate = some idx /\
      LeftmostArgMin xs left right idx := by
  have hMiddle :
      CandidateExact xs (leftBlock * b) (rightBlock * b)
        (recursiveMiddleCandidate xs b summaryBackend leftBlock rightBlock) :=
    recursiveMiddleCandidate_exact xs b leftBlock rightBlock summaryBackend hb
      hblocks hrightBlock
  have hLeftMiddle : leftBlock * b <= rightBlock * b :=
    Nat.mul_le_mul_right b hblocks
  exact combineHybridLeftmost
    (xs := xs) (left := left) (leftEnd := leftBlock * b)
    (middleEnd := rightBlock * b) (right := right) (li := li)
    (middleCandidate :=
      recursiveMiddleCandidate xs b summaryBackend leftBlock rightBlock)
    (rightCandidate := rightCandidate)
    hLeft hMiddle hRight hLeftMiddle hMiddleRight

/--
For nontrivial inputs, the public hybrid block size is strictly larger than
one. This is the small arithmetic fact that makes recursive compression shrink.
-/
theorem publicBlockSize_gt_one_of_length_gt_one
    {xs : List Int} (hlarge : 1 < xs.length) :
    1 < Nat.log2 xs.length + 1 := by
  have hne : xs.length ≠ 0 := by omega
  have htwo_le : 2 ^ 1 <= xs.length := by
    simp
    omega
  have hlog : 1 <= Nat.log2 xs.length := by
    exact (Nat.le_log2 hne).2 htwo_le
  omega

theorem publicCompressedLength_lt_self
    {xs : List Int} (hlarge : 1 < xs.length) :
    compressedLength xs.length (Nat.log2 xs.length + 1) < xs.length := by
  have hpos : 0 < xs.length := by omega
  have hb := publicBlockSize_gt_one_of_length_gt_one (xs := xs) hlarge
  exact compressedLength_lt_self hpos hb

/--
A summary-shape abstraction for self-recursive constructions.

An implementation supplies a summary list plus a proof that large inputs map to
strictly smaller summary inputs. The values in the summary may be block minima,
cartesian-tree signatures, or any future compressed RMQ representation.
-/
structure SummaryShape where
  summary : List Int -> List Int
  shrink : forall {xs : List Int}, 1 < xs.length -> (summary xs).length < xs.length

/--
Generic self-recursive construction over a shrinking summary shape.

`small` handles inputs of length at most one. `large` handles all larger inputs
and receives the recursively constructed result for the summary problem.
-/
def recurseOnSummary
    (shape : SummaryShape)
    {motive : List Int -> Sort u}
    (small : (xs : List Int) -> xs.length <= 1 -> motive xs)
    (large : (xs : List Int) -> (hlarge : 1 < xs.length) ->
      motive (shape.summary xs) -> motive xs)
    (xs : List Int) : motive xs :=
  lengthRec
    (fun xs rec =>
      if hsmall : xs.length <= 1 then
        small xs hsmall
      else
        let hlarge : 1 < xs.length := by omega
        large xs hlarge (rec (shape.summary xs) (shape.shrink hlarge)))
    xs

theorem recurseOnSummary_of_small
    (shape : SummaryShape)
    {motive : List Int -> Sort u}
    (small : (xs : List Int) -> xs.length <= 1 -> motive xs)
    (large : (xs : List Int) -> (hlarge : 1 < xs.length) ->
      motive (shape.summary xs) -> motive xs)
    {xs : List Int}
    (hsmall : xs.length <= 1) :
    recurseOnSummary shape small large xs = small xs hsmall := by
  conv =>
    lhs
    unfold recurseOnSummary
    rw [lengthRec]
  simp [hsmall]

theorem recurseOnSummary_of_large
    (shape : SummaryShape)
    {motive : List Int -> Sort u}
    (small : (xs : List Int) -> xs.length <= 1 -> motive xs)
    (large : (xs : List Int) -> (hlarge : 1 < xs.length) ->
      motive (shape.summary xs) -> motive xs)
    {xs : List Int}
    (hlarge : 1 < xs.length) :
    recurseOnSummary shape small large xs =
      large xs hlarge (recurseOnSummary shape small large (shape.summary xs)) := by
  conv =>
    lhs
    unfold recurseOnSummary
    rw [lengthRec]
  conv =>
    rhs
    unfold recurseOnSummary
  have hnot_small : Not (xs.length <= 1) := by omega
  simp [hnot_small]

/--
The public hybrid block-size summary shape. Each full block contributes the
value at its original leftmost block minimum, and the summary length is
strictly smaller for nontrivial inputs.
-/
def publicBlockSummaryShape : SummaryShape where
  summary := fun xs => blockMinSummary xs (Nat.log2 xs.length + 1)
  shrink := by
    intro xs hlarge
    simpa [blockMinSummary_length] using
      publicCompressedLength_lt_self (xs := xs) hlarge

/--
A tiny executable witness that the self-recursive shape is accepted by Lean's
well-founded recursion checker. It counts how many recursive summary layers are
formed before the input length reaches at most one.
-/
def publicSummaryDepth (xs : List Int) : Nat :=
  recurseOnSummary publicBlockSummaryShape
    (motive := fun _ => Nat)
    (fun _ _ => 0)
    (fun _ _ depth => depth + 1)
    xs

example : publicSummaryDepth ([] : List Int) = 0 := by native_decide
example : publicSummaryDepth [1] = 0 := by native_decide
example : publicSummaryDepth [1, 2, 3, 4, 5] = 1 := by native_decide

end RMQ
