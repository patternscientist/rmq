import RMQ.Core.EncodingLowerBound
import RMQ.Core.Microtable
import RMQ.Core.TableModel
import RMQ.Impl.FischerHeunCost
import RMQ.Impl.RecursiveHybrid
import RMQ.Impl.SparseTableInstrumented
import RMQ.Impl.SparseTableMemoCost

/-!
# Assembled Fischer-Heun RMQ backend

This module starts the value-level Fischer-Heun assembly.  The state carries
the canonical block size, a certified shape microtable, the block-minimum
summary, and the materialized sparse table for that summary.  The public query
uses the certified local microtable for full boundary blocks and the memoized
sparse-table backend over the block-minimum summary for the middle full blocks.
-/

namespace RMQ

namespace FischerHeun

/-- Microtable type used by a fixed Fischer-Heun block size. -/
abbrev MicrotableFor (blockSize : Nat) :=
  RMQ.Cartesian.Microtable blockSize

/-- Append one dummy block so every real block start has a full local shape. -/
def paddedInput (xs : List Int) (blockSize : Nat) : List Int :=
  xs ++ List.replicate blockSize 0

@[simp] theorem paddedInput_length (xs : List Int) (blockSize : Nat) :
    (paddedInput xs blockSize).length = xs.length + blockSize := by
  simp [paddedInput]

theorem paddedInput_get?_eq
    {xs : List Int} {blockSize i : Nat} (hi : i < xs.length) :
    (paddedInput xs blockSize)[i]? = xs[i]? := by
  simp [paddedInput, List.getElem?_append, hi]

/-- Stored Cartesian signatures for every block index that can arise locally. -/
def storedBlockSignatures
    (xs : List Int) (blockSize : Nat) :
    TableModel.IndexedSeq RMQ.Cartesian.CartesianShape :=
  TableModel.IndexedSeq.ofList
    ((List.range (compressedLength xs.length blockSize + 1)).map fun block =>
      RMQ.Cartesian.blockSignature (paddedInput xs blockSize)
        (block * blockSize) blockSize)

theorem storedBlockSignatures_get?_of_lt
    {xs : List Int} {blockSize block : Nat}
    (hblock : block < compressedLength xs.length blockSize + 1) :
    (storedBlockSignatures xs blockSize).get? block =
      some
        (RMQ.Cartesian.blockSignature (paddedInput xs blockSize)
          (block * blockSize) blockSize) := by
  unfold storedBlockSignatures
  simp [List.getElem?_map, List.getElem?_range hblock]

/-- Index into a materialized shape/query microtable row. -/
structure MicrotableSlotKey where
  shape : RMQ.Cartesian.CartesianShape
  left : Nat
  right : Nat

/-- Stored signatures plus a fixed-size certified local microtable. -/
structure StoredMicrotableView (blockSize : Nat) where
  signatures : TableModel.IndexedSeq RMQ.Cartesian.CartesianShape
  microtable : MicrotableFor blockSize

/-- Shape/query-slot view of a certified microtable. -/
def microtableSlotAccess
    {blockSize : Nat} (table : MicrotableFor blockSize) :
    TableModel.IndexedAccess MicrotableSlotKey Nat where
  get? key := table.queryOffset? key.shape key.left key.right

/-- One modeled indexed read from a shape/query microtable slot. -/
def microtableSlotReadCosted
    {blockSize : Nat} (table : MicrotableFor blockSize)
    (shape : RMQ.Cartesian.CartesianShape) (left right : Nat) :
    Costed (Option Nat) :=
  (microtableSlotAccess table).getCosted
    { shape := shape, left := left, right := right }

@[simp] theorem microtableSlotReadCosted_value
    {blockSize : Nat} (table : MicrotableFor blockSize)
    (shape : RMQ.Cartesian.CartesianShape) (left right : Nat) :
    (microtableSlotReadCosted table shape left right).value =
      table.queryOffset? shape left right := by
  rfl

theorem microtableSlotReadCosted_cost
    {blockSize : Nat} (table : MicrotableFor blockSize)
    (shape : RMQ.Cartesian.CartesianShape) (left right : Nat) :
    (microtableSlotReadCosted table shape left right).cost =
      TableModel.indexedReadCost := by
  rfl

namespace StoredMicrotableView

/-- Read the stored block signature, then read the corresponding local slot. -/
def queryOffsetCosted
    {blockSize : Nat} (store : StoredMicrotableView blockSize)
    (block left right : Nat) : Costed (Option Nat) :=
  Costed.bind (store.signatures.getCosted block) fun
  | some shape => microtableSlotReadCosted store.microtable shape left right
  | none => Costed.tickValue TableModel.indexedReadCost none

@[simp] theorem queryOffsetCosted_value_of_get
    {blockSize : Nat} (store : StoredMicrotableView blockSize)
    {block left right : Nat} {shape : RMQ.Cartesian.CartesianShape}
    (hget : store.signatures.get? block = some shape) :
    (queryOffsetCosted store block left right).value =
      store.microtable.queryOffset? shape left right := by
  unfold queryOffsetCosted
  simp [hget]

theorem queryOffsetCosted_cost
    {blockSize : Nat} (store : StoredMicrotableView blockSize)
    (block left right : Nat) :
    (queryOffsetCosted store block left right).cost =
      storedMicrotableLookupCost := by
  unfold queryOffsetCosted storedMicrotableLookupCost
  cases hget : store.signatures.get? block <;>
    simp [hget, TableModel.IndexedSeq.getCosted_cost,
      microtableSlotReadCosted_cost]

/--
Read a stored local offset and lift it to the global index of the block start
`block * blockSize`.
-/
def queryIndexCosted
    {blockSize : Nat} (store : StoredMicrotableView blockSize)
    (block left right : Nat) : Costed (Option Nat) :=
  Costed.map
    (fun offset? => offset?.map fun offset => block * blockSize + offset)
    (queryOffsetCosted store block left right)

@[simp] theorem queryIndexCosted_value_of_get
    {blockSize : Nat} (store : StoredMicrotableView blockSize)
    {block left right : Nat} {shape : RMQ.Cartesian.CartesianShape}
    (hget : store.signatures.get? block = some shape) :
    (queryIndexCosted store block left right).value =
      (store.microtable.queryOffset? shape left right).map
        fun offset => block * blockSize + offset := by
  unfold queryIndexCosted
  rw [Costed.map_value]
  exact congrArg
    (fun offset? => offset?.map fun offset => block * blockSize + offset)
    (queryOffsetCosted_value_of_get store hget)

theorem queryIndexCosted_cost
    {blockSize : Nat} (store : StoredMicrotableView blockSize)
    (block left right : Nat) :
    (queryIndexCosted store block left right).cost =
      storedMicrotableLookupCost := by
  unfold queryIndexCosted
  rw [Costed.map_cost]
  exact queryOffsetCosted_cost store block left right

end StoredMicrotableView

/-- Stored local-view model for an input and a supplied certified microtable. -/
def storedMicrotableForInputWith
    (xs : List Int) {blockSize : Nat} (microtable : MicrotableFor blockSize) :
    StoredMicrotableView blockSize where
  signatures := storedBlockSignatures xs blockSize
  microtable := microtable

theorem storedMicrotableForInputWith_queryIndexCosted_value_of_lt
    {xs : List Int} {blockSize block left right : Nat}
    {microtable : MicrotableFor blockSize}
    (hblock : block < compressedLength xs.length blockSize + 1) :
    (StoredMicrotableView.queryIndexCosted
        (storedMicrotableForInputWith xs microtable) block left right).value =
      microtable.queryIndex?
        (paddedInput xs blockSize) (block * blockSize) left right := by
  rw [StoredMicrotableView.queryIndexCosted_value_of_get]
  · rfl
  · exact storedBlockSignatures_get?_of_lt hblock

theorem storedMicrotableForInputWith_queryIndexCosted_cost
    (xs : List Int) {blockSize : Nat} (microtable : MicrotableFor blockSize)
    (block left right : Nat) :
    (StoredMicrotableView.queryIndexCosted
        (storedMicrotableForInputWith xs microtable) block left right).cost =
      storedMicrotableLookupCost := by
  exact StoredMicrotableView.queryIndexCosted_cost
    (storedMicrotableForInputWith xs microtable) block left right

/-- Canonical stored local-view model for an input and block size. -/
def storedMicrotableForInput
    (xs : List Int) (blockSize : Nat) : StoredMicrotableView blockSize :=
  storedMicrotableForInputWith xs (RMQ.Cartesian.Microtable.raw blockSize)

theorem storedMicrotableForInput_queryIndexCosted_value_of_lt
    {xs : List Int} {blockSize block left right : Nat}
    (hblock : block < compressedLength xs.length blockSize + 1) :
    (StoredMicrotableView.queryIndexCosted
        (storedMicrotableForInput xs blockSize) block left right).value =
      (RMQ.Cartesian.Microtable.raw blockSize).queryIndex?
        (paddedInput xs blockSize) (block * blockSize) left right := by
  exact storedMicrotableForInputWith_queryIndexCosted_value_of_lt hblock

theorem storedMicrotableForInput_queryIndexCosted_cost
    (xs : List Int) (blockSize block left right : Nat) :
    (StoredMicrotableView.queryIndexCosted
        (storedMicrotableForInput xs blockSize) block left right).cost =
      storedMicrotableLookupCost := by
  exact StoredMicrotableView.queryIndexCosted_cost
    (storedMicrotableForInput xs blockSize) block left right

theorem leftmostArgMin_of_eq_on_range
    {xs ys : List Int} {left right idx : Nat}
    (hright : right <= xs.length)
    (heq :
      forall j, left <= j -> j < right -> ys[j]? = xs[j]?)
    (harg : LeftmostArgMin ys left right idx) :
    LeftmostArgMin xs left right idx := by
  have hleft_right : left < right := harg.1
  have hleft_idx : left <= idx := harg.2.2.1
  have hidx_right : idx < right := harg.2.2.2.1
  cases harg.2.2.2.2 with
  | intro v hv =>
      have hget : ys[idx]? = some v := hv.1
      have hmin :
          forall j w, left <= j -> j < right -> ys[j]? = some w ->
            v <= w := hv.2.1
      have hleftmost :
          forall j w, left <= j -> j < idx -> ys[j]? = some w ->
            v < w := hv.2.2
      have hget_xs : xs[idx]? = some v := by
        have hidx_eq := heq idx hleft_idx hidx_right
        simpa [hidx_eq] using hget
      have hmin_xs :
          forall j w, left <= j -> j < right -> xs[j]? = some w ->
            v <= w := by
        intro j w hleft_j hj_right hget_j
        have hj_eq := heq j hleft_j hj_right
        have hget_y : ys[j]? = some w := by
          simpa [hj_eq] using hget_j
        exact hmin j w hleft_j hj_right hget_y
      have hleftmost_xs :
          forall j w, left <= j -> j < idx -> xs[j]? = some w ->
            v < w := by
        intro j w hleft_j hj_idx hget_j
        have hj_right : j < right := Nat.lt_trans hj_idx hidx_right
        have hj_eq := heq j hleft_j hj_right
        have hget_y : ys[j]? = some w := by
          simpa [hj_eq] using hget_j
        exact hleftmost j w hleft_j hj_idx hget_y
      exact And.intro hleft_right
        (And.intro hright
          (And.intro hleft_idx
            (And.intro hidx_right
              (Exists.intro v
                (And.intro hget_xs
                  (And.intro hmin_xs hleftmost_xs))))))

/--
A certified microtable lookup over one full concrete block is an exact global
RMQ answer for the corresponding subinterval.

This is the local lemma used by the assembled query's boundary candidates.
-/
theorem microQueryIndex_valid_exact
    {blockSize : Nat} (table : MicrotableFor blockSize)
    {xs : List Int} {start left right : Nat}
    (hbound : start + blockSize <= xs.length)
    (hstart_left : start <= left)
    (hright_block : right <= start + blockSize)
    (hValid : ValidRange xs left right) :
    exists idx,
      table.queryIndex? xs start (left - start) (right - start) = some idx /\
        LeftmostArgMin xs left right idx := by
  have hlocal :
      RMQ.Cartesian.LocalValid blockSize (left - start) (right - start) := by
    unfold RMQ.Cartesian.LocalValid
    omega
  exact Exists.elim
    (RMQ.Cartesian.Microtable.queryIndex?_leftmost table hbound hlocal)
    (fun idx hpair => by
      cases hpair with
      | intro hquery harg =>
        refine Exists.intro idx ?_
        refine And.intro hquery ?_
        have hleft : start + (left - start) = left := by omega
        have hright : start + (right - start) = right := by omega
        simpa [hleft, hright] using harg)

/-- Materialized Fischer-Heun state. -/
structure State where
  blockSize : Nat
  microtable : MicrotableFor blockSize
  summary : List Int
  summaryTable : List (List (Option Nat))
  summaryTableStore : Refine.StoredMatrix (Option Nat) summaryTable

/--
A supplied Fischer-Heun state whose summary table is the canonical memoized
sparse table over the block-minimum summary for `xs`.

The store's Array/List erasure certificate is carried directly by
`state.summaryTableStore`; this predicate records the value-level table that
the store is supposed to refine for this input.
-/
structure SummaryTableRefines (xs : List Int) (state : State) : Prop where
  summary_eq :
    state.summary = blockMinSummary xs state.blockSize
  table_eq :
    state.summaryTable =
      RMQ.SparseTable.memoBuildSparseTable
        (blockMinSummary xs state.blockSize)

theorem summaryTableStore_erases (state : State) :
    state.summaryTableStore.repr.toList.map Array.toList =
      state.summaryTable :=
  state.summaryTableStore.erases

theorem summaryTableStore_cell_eq_summaryTable
    (state : State) (row col : Nat) :
    Refine.StoredMatrix.cell? state.summaryTableStore row col =
      Refine.StoredMatrix.absCell? state.summaryTable row col :=
  Refine.StoredMatrix.cell?_eq_absCell? state.summaryTableStore row col

/--
Local candidate inside one block.

The lookup is run against `paddedInput xs state.blockSize`, so the final short
block and same-block intervals have the same unit-cost materialized lookup
shape as interior full blocks.  The queried half-open window itself remains
inside `xs`.
-/
def localBlockCandidate
    (xs : List Int) (state : State) (start left right : Nat) : Option Nat :=
  if _hnonempty : left < right then
    state.microtable.queryIndex? (paddedInput xs state.blockSize) start
      (left - start) (right - start)
  else
    none

theorem localBlockCandidate_exact
    (xs : List Int) (state : State) (start left right : Nat)
    (hstart_left : start <= left)
    (hleft_right : left <= right)
    (hright_len : right <= xs.length)
    (hright_block : right <= start + state.blockSize) :
    CandidateExact xs left right
      (localBlockCandidate xs state start left right) := by
  unfold localBlockCandidate
  by_cases hnonempty : left < right
  case pos =>
    rw [dif_pos hnonempty]
    have hpaddedBound :
        start + state.blockSize <=
          (paddedInput xs state.blockSize).length := by
      rw [paddedInput_length]
      omega
    have hpaddedValid :
        ValidRange (paddedInput xs state.blockSize) left right := by
      exact And.intro hnonempty (by rw [paddedInput_length]; omega)
    exact Exists.elim
      (microQueryIndex_valid_exact state.microtable hpaddedBound
        hstart_left hright_block hpaddedValid)
      (fun idx hpair => by
        cases hpair with
        | intro hquery harg =>
          have harg_xs : LeftmostArgMin xs left right idx :=
            leftmostArgMin_of_eq_on_range hright_len
              (fun j _hleft_j hj_right =>
                paddedInput_get?_eq (xs := xs)
                  (blockSize := state.blockSize) (by omega))
              harg
          exact Or.inr (Exists.intro idx (And.intro hquery harg_xs)))
  case neg =>
    rw [dif_neg hnonempty]
    exact Or.inl (And.intro rfl (by omega))

/-- Right-boundary candidate, implemented as a local padded-block lookup. -/
def rightBoundaryCandidate
    (xs : List Int) (state : State) (start right : Nat) : Option Nat :=
  localBlockCandidate xs state start start right

theorem rightBoundaryCandidate_exact
    (xs : List Int) (state : State) (start right : Nat)
    (hstart_right : start <= right)
    (hright_len : right <= xs.length)
    (hright_block : right <= start + state.blockSize) :
    CandidateExact xs start right
      (rightBoundaryCandidate xs state start right) := by
  exact localBlockCandidate_exact xs state start start right
    (by omega) hstart_right hright_len hright_block

/-- Sparse-table backend used to answer the block-minimum summary RMQ. -/
def summaryBackend (xs : List Int) (blockSize : Nat) :
    RMQBackend (blockMinSummary xs blockSize) :=
  RMQ.SparseTable.memoBackend (blockMinSummary xs blockSize)

/-- Stored summary-table query used by the costed supplied-state path. -/
def summaryStoredQuery
    (xs : List Int) (state : State) (leftBlock rightBlock : Nat) :
    RAM.Exec (Option Nat) :=
  RMQ.SparseTable.Instrumented.queryFromStoredTable
    (blockMinSummary xs state.blockSize) state.summaryTableStore
    leftBlock rightBlock

theorem summaryStoredQuery_value_of_refines
    {xs : List Int} {state : State} {leftBlock rightBlock : Nat}
    (hsummary : SummaryTableRefines xs state) :
    (summaryStoredQuery xs state leftBlock rightBlock).value =
      (summaryBackend xs state.blockSize).query
        (summaryBackend xs state.blockSize).build
        leftBlock rightBlock := by
  unfold summaryStoredQuery summaryBackend RMQ.SparseTable.memoBackend
  rw [RMQ.SparseTable.Instrumented.queryFromStoredTable_value]
  simp [hsummary.table_eq]

theorem summaryStoredQuery_steps_le_seven
    (xs : List Int) (state : State) (leftBlock rightBlock : Nat) :
    (summaryStoredQuery xs state leftBlock rightBlock).steps <= 7 := by
  unfold summaryStoredQuery
  exact
    RMQ.SparseTable.Instrumented.queryFromStoredTable_steps_le_seven
      (blockMinSummary xs state.blockSize) state.summaryTableStore
      leftBlock rightBlock

theorem liftedSummaryStoredQuery_refines_recursiveMiddle_with_steps
    {xs : List Int} {state : State} {leftBlock rightBlock : Nat}
    (hsummary : SummaryTableRefines xs state) :
    liftBlockCandidate xs state.blockSize
        (summaryStoredQuery xs state leftBlock rightBlock).value =
      recursiveMiddleCandidate xs state.blockSize
        (summaryBackend xs state.blockSize) leftBlock rightBlock /\
      (summaryStoredQuery xs state leftBlock rightBlock).steps <= 7 := by
  constructor
  · rw [summaryStoredQuery_value_of_refines hsummary]
    rfl
  · exact summaryStoredQuery_steps_le_seven xs state leftBlock rightBlock

/-- Build a Fischer-Heun state with an explicit block-size choice. -/
def buildWithBlockSize (xs : List Int) (blockSize : Nat) : State :=
  { blockSize := blockSize
    microtable := RMQ.Cartesian.Microtable.raw blockSize
    summary := blockMinSummary xs blockSize
    summaryTable := RMQ.SparseTable.memoBuildSparseTable
      (blockMinSummary xs blockSize)
    summaryTableStore := Refine.StoredMatrix.ofList
      (RMQ.SparseTable.memoBuildSparseTable
        (blockMinSummary xs blockSize)) }

@[simp] theorem buildWithBlockSize_blockSize
    (xs : List Int) (blockSize : Nat) :
    (buildWithBlockSize xs blockSize).blockSize = blockSize := rfl

@[simp] theorem buildWithBlockSize_summary
    (xs : List Int) (blockSize : Nat) :
    (buildWithBlockSize xs blockSize).summary =
      blockMinSummary xs blockSize := rfl

@[simp] theorem buildWithBlockSize_summaryTable
    (xs : List Int) (blockSize : Nat) :
    (buildWithBlockSize xs blockSize).summaryTable =
      RMQ.SparseTable.memoBuildSparseTable (blockMinSummary xs blockSize) := rfl

@[simp] theorem buildWithBlockSize_summaryTableStore_erases
    (xs : List Int) (blockSize : Nat) :
    (buildWithBlockSize xs blockSize).summaryTableStore.repr.toList.map
        Array.toList =
      RMQ.SparseTable.memoBuildSparseTable (blockMinSummary xs blockSize) := by
  simpa using (buildWithBlockSize xs blockSize).summaryTableStore.erases

theorem buildWithBlockSize_summaryTableRefines
    (xs : List Int) (blockSize : Nat) :
    SummaryTableRefines xs (buildWithBlockSize xs blockSize) := by
  constructor <;> rfl

@[simp] theorem buildWithBlockSize_microtable
    (xs : List Int) (blockSize : Nat) :
    (buildWithBlockSize xs blockSize).microtable =
      RMQ.Cartesian.Microtable.raw blockSize := rfl

/-- Exact cost expression for a stored local-block candidate. -/
def storedLocalBlockCandidateCost (left right : Nat) : Nat :=
  if _hnonempty : left < right then
    storedMicrotableLookupCost
  else
    1

/--
Stored-signature/local-slot version of a local block candidate for a freshly
built raw Fischer-Heun local microtable.
-/
def storedLocalBlockCandidateCosted
    (xs : List Int) (blockSize block left right : Nat) :
    Costed (Option Nat) :=
  let start := block * blockSize
  if _hnonempty : left < right then
    StoredMicrotableView.queryIndexCosted
      (storedMicrotableForInput xs blockSize) block
      (left - start) (right - start)
  else
    Costed.tickValue 1 none

@[simp] theorem storedLocalBlockCandidateCosted_value_of_lt
    {xs : List Int} {blockSize block left right : Nat}
    (hblock : block < compressedLength xs.length blockSize + 1) :
    (storedLocalBlockCandidateCosted xs blockSize block left right).value =
      localBlockCandidate xs (buildWithBlockSize xs blockSize)
        (block * blockSize) left right := by
  unfold storedLocalBlockCandidateCosted localBlockCandidate
  by_cases hnonempty : left < right
  · rw [dif_pos hnonempty, dif_pos hnonempty]
    exact storedMicrotableForInput_queryIndexCosted_value_of_lt hblock
  · rw [dif_neg hnonempty, dif_neg hnonempty]
    rfl

theorem storedLocalBlockCandidateCosted_cost
    (xs : List Int) (blockSize block left right : Nat) :
    (storedLocalBlockCandidateCosted xs blockSize block left right).cost =
      storedLocalBlockCandidateCost left right := by
  unfold storedLocalBlockCandidateCosted storedLocalBlockCandidateCost
  by_cases hnonempty : left < right
  · rw [dif_pos hnonempty, dif_pos hnonempty]
    exact storedMicrotableForInput_queryIndexCosted_cost xs blockSize block
      (left - block * blockSize) (right - block * blockSize)
  · rw [dif_neg hnonempty, dif_neg hnonempty]
    rfl

/-- Stored Cartesian signatures for full blocks read directly from `xs`. -/
def storedExactBlockSignatures
    (xs : List Int) (blockSize : Nat) :
    TableModel.IndexedSeq RMQ.Cartesian.CartesianShape :=
  TableModel.IndexedSeq.ofList
    ((List.range (compressedLength xs.length blockSize + 1)).map fun block =>
      RMQ.Cartesian.blockSignature xs (block * blockSize) blockSize)

theorem storedExactBlockSignatures_get?_of_lt
    {xs : List Int} {blockSize block : Nat}
    (hblock : block < compressedLength xs.length blockSize + 1) :
    (storedExactBlockSignatures xs blockSize).get? block =
      some
        (RMQ.Cartesian.blockSignature xs (block * blockSize) blockSize) := by
  unfold storedExactBlockSignatures
  simp [List.getElem?_map, List.getElem?_range hblock]

/-- Stored local-view model for full-block queries over the exact input. -/
def storedMicrotableForExactInputWith
    (xs : List Int) {blockSize : Nat} (microtable : MicrotableFor blockSize) :
    StoredMicrotableView blockSize where
  signatures := storedExactBlockSignatures xs blockSize
  microtable := microtable

theorem storedMicrotableForExactInputWith_queryIndexCosted_value_of_lt
    {xs : List Int} {blockSize block left right : Nat}
    {microtable : MicrotableFor blockSize}
    (hblock : block < compressedLength xs.length blockSize + 1) :
    (StoredMicrotableView.queryIndexCosted
        (storedMicrotableForExactInputWith xs microtable)
          block left right).value =
      microtable.queryIndex? xs (block * blockSize) left right := by
  rw [StoredMicrotableView.queryIndexCosted_value_of_get]
  · rfl
  · exact storedExactBlockSignatures_get?_of_lt hblock

theorem storedMicrotableForExactInputWith_queryIndexCosted_cost
    (xs : List Int) {blockSize : Nat} (microtable : MicrotableFor blockSize)
    (block left right : Nat) :
    (StoredMicrotableView.queryIndexCosted
        (storedMicrotableForExactInputWith xs microtable)
          block left right).cost =
      storedMicrotableLookupCost := by
  exact StoredMicrotableView.queryIndexCosted_cost
    (storedMicrotableForExactInputWith xs microtable) block left right

/-- Stored-read full-block candidate for the supplied state's microtable. -/
def storedFullBlockCandidateCosted
    (xs : List Int) (state : State) (block left right : Nat) :
    Costed (Option Nat) :=
  StoredMicrotableView.queryIndexCosted
    (storedMicrotableForExactInputWith xs state.microtable)
      block left right

@[simp] theorem storedFullBlockCandidateCosted_value_of_lt
    {xs : List Int} {state : State} {block left right : Nat}
    (hblock : block < compressedLength xs.length state.blockSize + 1) :
    (storedFullBlockCandidateCosted xs state block left right).value =
      state.microtable.queryIndex? xs (block * state.blockSize) left right := by
  exact storedMicrotableForExactInputWith_queryIndexCosted_value_of_lt hblock

theorem storedFullBlockCandidateCosted_cost
    (xs : List Int) (state : State) (block left right : Nat) :
    (storedFullBlockCandidateCosted xs state block left right).cost =
      storedMicrotableLookupCost := by
  exact storedMicrotableForExactInputWith_queryIndexCosted_cost xs
    state.microtable block left right

/--
Stored-signature/local-slot version of a padded local block candidate for the
supplied state's microtable.
-/
def storedStateLocalBlockCandidateCosted
    (xs : List Int) (state : State) (block left right : Nat) :
    Costed (Option Nat) :=
  let start := block * state.blockSize
  if _hnonempty : left < right then
    StoredMicrotableView.queryIndexCosted
      (storedMicrotableForInputWith xs state.microtable) block
      (left - start) (right - start)
  else
    Costed.tickValue 1 none

@[simp] theorem storedStateLocalBlockCandidateCosted_value_of_lt
    {xs : List Int} {state : State} {block left right : Nat}
    (hblock : block < compressedLength xs.length state.blockSize + 1) :
    (storedStateLocalBlockCandidateCosted xs state block left right).value =
      localBlockCandidate xs state (block * state.blockSize) left right := by
  unfold storedStateLocalBlockCandidateCosted localBlockCandidate
  by_cases hnonempty : left < right
  · rw [dif_pos hnonempty, dif_pos hnonempty]
    exact storedMicrotableForInputWith_queryIndexCosted_value_of_lt hblock
  · rw [dif_neg hnonempty, dif_neg hnonempty]
    rfl

theorem storedStateLocalBlockCandidateCosted_cost
    (xs : List Int) (state : State) (block left right : Nat) :
    (storedStateLocalBlockCandidateCosted xs state block left right).cost =
      storedLocalBlockCandidateCost left right := by
  unfold storedStateLocalBlockCandidateCosted storedLocalBlockCandidateCost
  by_cases hnonempty : left < right
  · rw [dif_pos hnonempty, dif_pos hnonempty]
    exact storedMicrotableForInputWith_queryIndexCosted_cost xs state.microtable
      block (left - block * state.blockSize) (right - block * state.blockSize)
  · rw [dif_neg hnonempty, dif_neg hnonempty]
    rfl

/-- Charge one tick for each token in a finite construction list. -/
def tickEachCosted {alpha : Type} : List alpha -> Costed Unit
  | [] => Costed.pure ()
  | _ :: rest => Costed.bind (Costed.tick 1) fun _ => tickEachCosted rest

theorem tickEachCosted_cost {alpha : Type} (tokens : List alpha) :
    (tickEachCosted tokens).cost = tokens.length := by
  induction tokens with
  | nil =>
      simp [tickEachCosted]
  | cons _ rest ih =>
      simp [tickEachCosted, ih]
      omega

/-- One token for every local query slot in a materialized shape row. -/
def microtableSlotTokens (blockSize : Nat) : List Unit :=
  List.replicate (localQuerySlotBudget blockSize) ()

theorem microtableSlotTokens_length (blockSize : Nat) :
    (microtableSlotTokens blockSize).length =
      localQuerySlotBudget blockSize := by
  simp [microtableSlotTokens]

/-- Costed construction of one shape row in the raw microtable universe. -/
def microtableShapeRowBuildCosted
    (blockSize : Nat) (_shape : RMQ.Cartesian.CartesianShape) : Costed Unit :=
  tickEachCosted (microtableSlotTokens blockSize)

theorem microtableShapeRowBuildCosted_cost
    (blockSize : Nat) (shape : RMQ.Cartesian.CartesianShape) :
    (microtableShapeRowBuildCosted blockSize shape).cost =
      localQuerySlotBudget blockSize := by
  simp [microtableShapeRowBuildCosted, tickEachCosted_cost,
    microtableSlotTokens_length]

/-- Costed construction of all rows in a supplied shape universe. -/
def microtableRowsBuildCostedFrom
    (blockSize : Nat) : List RMQ.Cartesian.CartesianShape -> Costed Unit
  | [] => Costed.pure ()
  | shape :: rest =>
      Costed.bind (microtableShapeRowBuildCosted blockSize shape) fun _ =>
        microtableRowsBuildCostedFrom blockSize rest

theorem microtableRowsBuildCostedFrom_cost
    (blockSize : Nat) (shapes : List RMQ.Cartesian.CartesianShape) :
    (microtableRowsBuildCostedFrom blockSize shapes).cost =
      shapes.length * localQuerySlotBudget blockSize := by
  induction shapes with
  | nil =>
      simp [microtableRowsBuildCostedFrom]
  | cons shape rest ih =>
      simp [microtableRowsBuildCostedFrom,
        microtableShapeRowBuildCosted_cost, ih, Nat.succ_mul]
      omega

/-- Costed construction of the full raw shape-indexed microtable universe. -/
def microtableRowsBuildCosted (blockSize : Nat) : Costed Unit :=
  microtableRowsBuildCostedFrom blockSize
    (RMQ.Cartesian.shapeUniverse blockSize)

theorem microtableRowsBuildCosted_cost (blockSize : Nat) :
    (microtableRowsBuildCosted blockSize).cost =
      rawMicrotableSlotBudget blockSize := by
  simp [microtableRowsBuildCosted, microtableRowsBuildCostedFrom_cost,
    rawMicrotableSlotBudget, rawShapeTableCount]

/-- Costed materialization of the fixed-size shape microtable family. -/
def microtableBuildCosted (blockSize : Nat) :
    Costed (MicrotableFor blockSize) :=
  Costed.bind (microtableRowsBuildCosted blockSize) fun _ =>
    Costed.pure (RMQ.Cartesian.Microtable.raw blockSize)

@[simp] theorem microtableBuildCosted_value (blockSize : Nat) :
    (microtableBuildCosted blockSize).value =
      RMQ.Cartesian.Microtable.raw blockSize := by
  rfl

theorem microtableBuildCosted_cost (blockSize : Nat) :
    (microtableBuildCosted blockSize).cost =
      rawMicrotableSlotBudget blockSize := by
  simp [microtableBuildCosted, microtableRowsBuildCosted_cost]

/--
Costed Fischer-Heun state build for an explicit block size.

The cost charges the materialized shape-table universe, the block-minimum
summary construction, and the memoized sparse table over that summary.
-/
def buildWithBlockSizeCosted
    (xs : List Int) (blockSize : Nat) : Costed State :=
  Costed.bind (microtableBuildCosted blockSize) fun microtable =>
    Costed.bind
      (RMQ.RecursiveHybrid.blockMinSummaryCosted xs blockSize) fun summary =>
      Costed.bind (RMQ.SparseTable.memoBuildSparseTableCosted summary)
        fun summaryTable =>
        Costed.pure
          { blockSize := blockSize
            microtable := microtable
            summary := summary
            summaryTable := summaryTable
            summaryTableStore := Refine.StoredMatrix.ofList summaryTable }

@[simp] theorem buildWithBlockSizeCosted_value
    (xs : List Int) (blockSize : Nat) :
    (buildWithBlockSizeCosted xs blockSize).value =
      buildWithBlockSize xs blockSize := by
  unfold buildWithBlockSizeCosted buildWithBlockSize
  simp [microtableBuildCosted]

theorem buildWithBlockSizeCosted_cost
    (xs : List Int) (blockSize : Nat) :
    (buildWithBlockSizeCosted xs blockSize).cost =
      buildCost xs blockSize := by
  simp [buildWithBlockSizeCosted, microtableBuildCosted_cost, buildCost,
    summarySparseBuildCost,
    RMQ.RecursiveHybrid.blockMinSummaryCosted_cost,
    RMQ.SparseTable.memoBuildSparseTableCosted_cost]

theorem buildWithBlockSizeCosted_run
    (xs : List Int) (blockSize : Nat) :
    Costed.run (buildWithBlockSizeCosted xs blockSize) =
      (buildWithBlockSize xs blockSize, buildCost xs blockSize) := by
  simp [Costed.run, buildWithBlockSizeCosted_cost]

/-- Build using the canonical quarter-log block size from the cost profile. -/
def build (xs : List Int) : State :=
  buildWithBlockSize xs (canonicalBlockSize xs)

/-- Costed build using the canonical quarter-log block size. -/
def buildCosted (xs : List Int) : Costed State :=
  buildWithBlockSizeCosted xs (canonicalBlockSize xs)

@[simp] theorem buildCosted_value (xs : List Int) :
    (buildCosted xs).value = build xs := by
  exact buildWithBlockSizeCosted_value xs (canonicalBlockSize xs)

theorem buildCosted_cost (xs : List Int) :
    (buildCosted xs).cost = buildCost xs (canonicalBlockSize xs) := by
  exact buildWithBlockSizeCosted_cost xs (canonicalBlockSize xs)

theorem buildCosted_run (xs : List Int) :
    Costed.run (buildCosted xs) =
      (build xs, buildCost xs (canonicalBlockSize xs)) := by
  exact buildWithBlockSizeCosted_run xs (canonicalBlockSize xs)

/--
Query a Fischer-Heun state.

For positive block sizes this composes a certified left-boundary microtable
lookup, a memoized sparse-table query over the block-minimum summary, and a
right-boundary microtable lookup when the right block is full.  The zero-block
case falls back to linear scan, which keeps the API total for small canonical
inputs.
-/
def queryWithState
    (xs : List Int) (state : State) (left right : Nat) : Option Nat :=
  if _hValid : ValidRange xs left right then
    if _hb : 0 < state.blockSize then
      let b := state.blockSize
      let leftBlock := leftBoundaryBlock left b
      let rightBlock := rightBoundaryBlock right b
      if _hschedule : leftBlock <= rightBlock then
        let leftStart := (leftBlock - 1) * b
        let leftCandidate :=
          state.microtable.queryIndex? xs leftStart
            (left - leftStart) (leftBlock * b - leftStart)
        let middleCandidate :=
          recursiveMiddleCandidate xs b (summaryBackend xs b)
            leftBlock rightBlock
        let rightStart := rightBlock * b
        let rightCandidate :=
          rightBoundaryCandidate xs state rightStart right
        combineIndex xs (combineIndex xs leftCandidate middleCandidate)
          rightCandidate
      else
        let blockStart := rightBlock * b
        localBlockCandidate xs state blockStart left right
    else
      RMQ.LinearScan.query xs left right
  else
    none

/-- Exact cost expression for the costed local-block candidate. -/
def localBlockCandidateCost
    (_xs : List Int) (_state : State) (_start left right : Nat) : Nat :=
  storedLocalBlockCandidateCost left right

theorem localBlockCandidateCost_le_two
    (xs : List Int) (state : State) (start left right : Nat) :
    localBlockCandidateCost xs state start left right <= 2 := by
  unfold localBlockCandidateCost storedLocalBlockCandidateCost
  by_cases hnonempty : left < right
  case pos =>
    rw [dif_pos hnonempty]
    simp [storedMicrotableLookupCost, TableModel.indexedReadCost]
  case neg =>
    rw [dif_neg hnonempty]
    omega

/-- Exact cost expression for the costed right-boundary candidate. -/
def rightBoundaryCandidateCost
    (xs : List Int) (state : State) (start right : Nat) : Nat :=
  localBlockCandidateCost xs state start start right

/-- Costed right-boundary candidate matching `rightBoundaryCandidate`. -/
def rightBoundaryCandidateCosted
    (xs : List Int) (state : State) (block right : Nat) :
    Costed (Option Nat) :=
  storedStateLocalBlockCandidateCosted xs state block
    (block * state.blockSize) right

@[simp] theorem rightBoundaryCandidateCosted_value_of_lt
    {xs : List Int} {state : State} {block right : Nat}
    (hblock : block < compressedLength xs.length state.blockSize + 1) :
    (rightBoundaryCandidateCosted xs state block right).value =
      rightBoundaryCandidate xs state (block * state.blockSize) right := by
  exact storedStateLocalBlockCandidateCosted_value_of_lt hblock

theorem rightBoundaryCandidateCosted_cost
    (xs : List Int) (state : State) (block right : Nat) :
    (rightBoundaryCandidateCosted xs state block right).cost =
      rightBoundaryCandidateCost xs state (block * state.blockSize) right := by
  exact storedStateLocalBlockCandidateCosted_cost xs state block
    (block * state.blockSize) right

theorem rightBoundaryCandidateCost_le_two
    (xs : List Int) (state : State) (start right : Nat) :
    rightBoundaryCandidateCost xs state start right <= 2 := by
  exact localBlockCandidateCost_le_two xs state start start right

/-- Exact cost expression for `queryWithStateCosted`. -/
def queryWithStateCost
    (xs : List Int) (state : State) (left right : Nat) : Nat :=
  if _hValid : ValidRange xs left right then
    if _hb : 0 < state.blockSize then
      let b := state.blockSize
      let leftBlock := leftBoundaryBlock left b
      let rightBlock := rightBoundaryBlock right b
      if _hschedule : leftBlock <= rightBlock then
        let rightStart := rightBlock * b
        storedMicrotableLookupCost +
          (summaryStoredQuery xs state leftBlock rightBlock).steps +
            rightBoundaryCandidateCost xs state rightStart right + 2
      else
        let blockStart := rightBlock * b
        localBlockCandidateCost xs state blockStart left right
    else
      rangeScanCost xs left right
  else
    1

/--
Costed supplied-state Fischer-Heun query.

This consumes the state's materialized summary table. For freshly built states
that table is the memoized sparse table used by `queryWithState`, so the
erasure theorem below connects this supplied-table implementation back to the
verified value query.
-/
def queryWithStateCosted
    (xs : List Int) (state : State) (left right : Nat) :
    Costed (Option Nat) :=
  if _hValid : ValidRange xs left right then
    if _hb : 0 < state.blockSize then
      let b := state.blockSize
      let leftBlock := leftBoundaryBlock left b
      let rightBlock := rightBoundaryBlock right b
      if _hschedule : leftBlock <= rightBlock then
        let leftStart := (leftBlock - 1) * b
        Costed.bind
          (storedFullBlockCandidateCosted xs state (leftBlock - 1)
            (left - leftStart) (leftBlock * b - leftStart))
          fun leftCandidate =>
        Costed.bind
          (Costed.map (liftBlockCandidate xs b)
            (RAM.Exec.toCosted
              (summaryStoredQuery xs state leftBlock rightBlock)))
          fun middleCandidate =>
        Costed.bind
          (rightBoundaryCandidateCosted xs state rightBlock right)
          fun rightCandidate =>
        Costed.tickValue 2
          (combineIndex xs (combineIndex xs leftCandidate middleCandidate)
            rightCandidate)
      else
        storedStateLocalBlockCandidateCosted xs state rightBlock left right
    else
      rangeScanCosted xs left right
  else
    Costed.tickValue 1 none

theorem queryWithStateCosted_cost
    (xs : List Int) (state : State) (left right : Nat) :
    (queryWithStateCosted xs state left right).cost =
      queryWithStateCost xs state left right := by
  unfold queryWithStateCosted queryWithStateCost
  by_cases hValid : ValidRange xs left right
  case pos =>
    rw [dif_pos hValid, dif_pos hValid]
    by_cases hb : 0 < state.blockSize
    case pos =>
      rw [dif_pos hb, dif_pos hb]
      by_cases hschedule :
          leftBoundaryBlock left state.blockSize <=
            rightBoundaryBlock right state.blockSize
      case pos =>
        rw [dif_pos hschedule, dif_pos hschedule]
        simp [storedFullBlockCandidateCosted_cost, Costed.map_cost,
          RAM.Exec.toCosted_cost_eq_steps,
          rightBoundaryCandidateCosted_cost]
        omega
      case neg =>
        rw [dif_neg hschedule, dif_neg hschedule]
        simp [storedStateLocalBlockCandidateCosted_cost,
          localBlockCandidateCost]
    case neg =>
      rw [dif_neg hb, dif_neg hb]
      exact rangeScanCosted_cost xs left right
  case neg =>
    rw [dif_neg hValid, dif_neg hValid]
    rfl

theorem queryWithStateCost_le_thirteen_of_blockSize_pos
    (xs : List Int) (state : State) (left right : Nat)
    (hb : 0 < state.blockSize) :
    queryWithStateCost xs state left right <= 13 := by
  unfold queryWithStateCost
  by_cases hValid : ValidRange xs left right
  case pos =>
    rw [dif_pos hValid]
    rw [dif_pos hb]
    by_cases hschedule :
        leftBoundaryBlock left state.blockSize <=
          rightBoundaryBlock right state.blockSize
    case pos =>
      rw [dif_pos hschedule]
      have hsparse :=
        summaryStoredQuery_steps_le_seven xs state
          (leftBoundaryBlock left state.blockSize)
          (rightBoundaryBlock right state.blockSize)
      have hright := rightBoundaryCandidateCost_le_two xs state
        (rightBoundaryBlock right state.blockSize * state.blockSize) right
      simp [storedMicrotableLookupCost, TableModel.indexedReadCost]
      omega
    case neg =>
      rw [dif_neg hschedule]
      have hlocal := localBlockCandidateCost_le_two xs state
        (rightBoundaryBlock right state.blockSize * state.blockSize)
        left right
      exact Nat.le_trans (by simpa using hlocal) (by omega)
  case neg =>
    rw [dif_neg hValid]
    omega

theorem queryWithStateCosted_cost_le_thirteen_of_blockSize_pos
    (xs : List Int) (state : State) (left right : Nat)
    (hb : 0 < state.blockSize) :
    (queryWithStateCosted xs state left right).cost <= 13 := by
  rw [queryWithStateCosted_cost]
  exact queryWithStateCost_le_thirteen_of_blockSize_pos xs state left right hb

theorem queryWithStateCost_le_suppliedQueryCost_of_stored
    {xs : List Int} {state : State} {left right : Nat}
    (hb : 0 < state.blockSize)
    (hschedule :
      leftBoundaryBlock left state.blockSize <=
        rightBoundaryBlock right state.blockSize)
    (_hright :
      rightBoundaryBlock right state.blockSize * state.blockSize = right \/
        rightBoundaryBlock right state.blockSize * state.blockSize +
            state.blockSize <= xs.length) :
    queryWithStateCost xs state left right <=
      suppliedQueryCost xs state.blockSize left right := by
  unfold queryWithStateCost suppliedQueryCost
  by_cases hValid : ValidRange xs left right
  case pos =>
    rw [dif_pos hValid, dif_pos (And.intro hValid hb), dif_pos hb,
      dif_pos hschedule]
    have hsparse :=
      summaryStoredQuery_steps_le_seven xs state
        (leftBoundaryBlock left state.blockSize)
        (rightBoundaryBlock right state.blockSize)
    have hrightCost := rightBoundaryCandidateCost_le_two xs state
      (rightBoundaryBlock right state.blockSize * state.blockSize) right
    simp [storedMicrotableLookupCost, TableModel.indexedReadCost]
    omega
  case neg =>
    rw [dif_neg hValid]
    have hbad : Not (ValidRange xs left right /\ 0 < state.blockSize) := by
      intro h
      exact hValid h.1
    rw [dif_neg hbad]
    exact Nat.le_refl _

theorem queryWithStateCosted_cost_le_suppliedQueryCost_of_stored
    {xs : List Int} {state : State} {left right : Nat}
    (hb : 0 < state.blockSize)
    (hschedule :
      leftBoundaryBlock left state.blockSize <=
        rightBoundaryBlock right state.blockSize)
    (hright :
      rightBoundaryBlock right state.blockSize * state.blockSize = right \/
        rightBoundaryBlock right state.blockSize * state.blockSize +
            state.blockSize <= xs.length) :
    (queryWithStateCosted xs state left right).cost <=
      suppliedQueryCost xs state.blockSize left right := by
  rw [queryWithStateCosted_cost]
  exact queryWithStateCost_le_suppliedQueryCost_of_stored
    hb hschedule hright

theorem queryWithStateCosted_value_of_summaryTableRefines
    {xs : List Int} {state : State} {left right : Nat}
    (hsummary : SummaryTableRefines xs state) :
    (queryWithStateCosted xs state left right).value =
      queryWithState xs state left right := by
  unfold queryWithStateCosted queryWithState
  by_cases hValid : ValidRange xs left right
  case pos =>
    rw [dif_pos hValid, dif_pos hValid]
    by_cases hb : 0 < state.blockSize
    case pos =>
      simp [hb]
      by_cases hschedule :
          leftBoundaryBlock left state.blockSize <=
            rightBoundaryBlock right state.blockSize
      case pos =>
        have hrightBlockLe :
            rightBoundaryBlock right state.blockSize <=
              compressedLength xs.length state.blockSize :=
          rightBoundaryBlock_le_compressed
            (xs := xs) (b := state.blockSize) (right := right)
            hb hValid.2
        have hrightBlockLt :
            rightBoundaryBlock right state.blockSize <
              compressedLength xs.length state.blockSize + 1 := by
          omega
        have hleftBlockLt :
            leftBoundaryBlock left state.blockSize - 1 <
              compressedLength xs.length state.blockSize + 1 := by
          omega
        have hleftValue :
            (storedFullBlockCandidateCosted xs state
                (leftBoundaryBlock left state.blockSize - 1)
                (left - ((leftBoundaryBlock left state.blockSize - 1) *
                    state.blockSize))
                (leftBoundaryBlock left state.blockSize * state.blockSize -
                    (leftBoundaryBlock left state.blockSize - 1) *
                      state.blockSize)).value =
              state.microtable.queryIndex? xs
                ((leftBoundaryBlock left state.blockSize - 1) *
                  state.blockSize)
                (left - ((leftBoundaryBlock left state.blockSize - 1) *
                    state.blockSize))
                (leftBoundaryBlock left state.blockSize * state.blockSize -
                    (leftBoundaryBlock left state.blockSize - 1) *
                      state.blockSize) :=
          storedFullBlockCandidateCosted_value_of_lt hleftBlockLt
        have hrightValue :
            (rightBoundaryCandidateCosted xs state
                (rightBoundaryBlock right state.blockSize) right).value =
              rightBoundaryCandidate xs state
                (rightBoundaryBlock right state.blockSize *
                  state.blockSize) right :=
          rightBoundaryCandidateCosted_value_of_lt hrightBlockLt
        have hmiddle :
            liftBlockCandidate xs state.blockSize
                (summaryStoredQuery xs state
                  (leftBoundaryBlock left state.blockSize)
                  (rightBoundaryBlock right state.blockSize)).value =
              recursiveMiddleCandidate xs state.blockSize
                (summaryBackend xs state.blockSize)
                (leftBoundaryBlock left state.blockSize)
                (rightBoundaryBlock right state.blockSize) :=
          (liftedSummaryStoredQuery_refines_recursiveMiddle_with_steps
            (xs := xs) (state := state)
            (leftBlock := leftBoundaryBlock left state.blockSize)
            (rightBlock := rightBoundaryBlock right state.blockSize)
            hsummary).1
        simp [Costed.map_value, hleftValue, hrightValue, hmiddle,
          hschedule]
      case neg =>
        have hrightBlockLe :
            rightBoundaryBlock right state.blockSize <=
              compressedLength xs.length state.blockSize :=
          rightBoundaryBlock_le_compressed
            (xs := xs) (b := state.blockSize) (right := right)
            hb hValid.2
        have hrightBlockLt :
            rightBoundaryBlock right state.blockSize <
              compressedLength xs.length state.blockSize + 1 := by
          omega
        have hlocalValue :
            (storedStateLocalBlockCandidateCosted xs state
                (rightBoundaryBlock right state.blockSize) left right).value =
              localBlockCandidate xs state
                (rightBoundaryBlock right state.blockSize *
                  state.blockSize) left right :=
          storedStateLocalBlockCandidateCosted_value_of_lt hrightBlockLt
        simp [hlocalValue, hschedule]
    case neg =>
      simp [hb, RMQ.LinearScan.query]
  case neg =>
    rw [dif_neg hValid, dif_neg hValid]
    rfl

@[simp] theorem queryWithStateCosted_value_built
    (xs : List Int) (blockSize left right : Nat) :
    (queryWithStateCosted xs (buildWithBlockSize xs blockSize) left right).value =
      queryWithState xs (buildWithBlockSize xs blockSize) left right := by
  exact queryWithStateCosted_value_of_summaryTableRefines
    (buildWithBlockSize_summaryTableRefines xs blockSize)

theorem queryWithStateCosted_run_built
    (xs : List Int) (blockSize left right : Nat) :
    Costed.run
        (queryWithStateCosted xs (buildWithBlockSize xs blockSize) left right) =
      (queryWithState xs (buildWithBlockSize xs blockSize) left right,
        queryWithStateCost xs (buildWithBlockSize xs blockSize) left right) := by
  simp [Costed.run, queryWithStateCosted_cost]

/-- Query with a freshly built explicit-block-size state. -/
def queryWithBlockSize
    (xs : List Int) (blockSize left right : Nat) : Option Nat :=
  queryWithState xs (buildWithBlockSize xs blockSize) left right

/-- Costed supplied-state query with a freshly built explicit-block-size state. -/
def queryWithBlockSizeCosted
    (xs : List Int) (blockSize left right : Nat) : Costed (Option Nat) :=
  queryWithStateCosted xs (buildWithBlockSize xs blockSize) left right

@[simp] theorem queryWithBlockSizeCosted_value
    (xs : List Int) (blockSize left right : Nat) :
    (queryWithBlockSizeCosted xs blockSize left right).value =
      queryWithBlockSize xs blockSize left right := by
  exact queryWithStateCosted_value_built xs blockSize left right

theorem queryWithBlockSizeCosted_run
    (xs : List Int) (blockSize left right : Nat) :
    Costed.run (queryWithBlockSizeCosted xs blockSize left right) =
      (queryWithBlockSize xs blockSize left right,
        queryWithStateCost xs (buildWithBlockSize xs blockSize) left right) := by
  exact queryWithStateCosted_run_built xs blockSize left right

/-- Public query using the canonical quarter-log block size. -/
def query (xs : List Int) (left right : Nat) : Option Nat :=
  queryWithState xs (build xs) left right

/-- Public costed supplied-state query using the canonical quarter-log block size. -/
def queryCosted (xs : List Int) (left right : Nat) : Costed (Option Nat) :=
  queryWithStateCosted xs (build xs) left right

@[simp] theorem queryCosted_value
    (xs : List Int) (left right : Nat) :
    (queryCosted xs left right).value = query xs left right := by
  unfold queryCosted query build
  exact queryWithStateCosted_value_built xs (canonicalBlockSize xs) left right

theorem queryCosted_run
    (xs : List Int) (left right : Nat) :
    Costed.run (queryCosted xs left right) =
      (query xs left right,
        queryWithStateCost xs (build xs) left right) := by
  unfold queryCosted query build
  exact queryWithStateCosted_run_built xs (canonicalBlockSize xs) left right

/-- Fresh explicit-block-size query that charges both build and supplied query. -/
def queryWithBlockSizeFreshCosted
    (xs : List Int) (blockSize left right : Nat) : Costed (Option Nat) :=
  Costed.bind (buildWithBlockSizeCosted xs blockSize) fun state =>
    queryWithStateCosted xs state left right

@[simp] theorem queryWithBlockSizeFreshCosted_value
    (xs : List Int) (blockSize left right : Nat) :
    (queryWithBlockSizeFreshCosted xs blockSize left right).value =
      queryWithBlockSize xs blockSize left right := by
  simp [queryWithBlockSizeFreshCosted, queryWithBlockSize]

theorem queryWithBlockSizeFreshCosted_cost
    (xs : List Int) (blockSize left right : Nat) :
    (queryWithBlockSizeFreshCosted xs blockSize left right).cost =
      buildCost xs blockSize +
        queryWithStateCost xs (buildWithBlockSize xs blockSize) left right := by
  simp [queryWithBlockSizeFreshCosted, buildWithBlockSizeCosted_cost,
    queryWithStateCosted_cost]

theorem queryWithBlockSizeFreshCosted_run
    (xs : List Int) (blockSize left right : Nat) :
    Costed.run (queryWithBlockSizeFreshCosted xs blockSize left right) =
      (queryWithBlockSize xs blockSize left right,
        buildCost xs blockSize +
          queryWithStateCost xs (buildWithBlockSize xs blockSize)
            left right) := by
  simp [Costed.run, queryWithBlockSizeFreshCosted_cost]

/-- Fresh canonical query that charges both canonical build and supplied query. -/
def freshQueryCosted (xs : List Int) (left right : Nat) :
    Costed (Option Nat) :=
  Costed.bind (buildCosted xs) fun state =>
    queryWithStateCosted xs state left right

@[simp] theorem freshQueryCosted_value
    (xs : List Int) (left right : Nat) :
    (freshQueryCosted xs left right).value = query xs left right := by
  unfold freshQueryCosted query
  simp [buildCosted_value]
  unfold build
  exact queryWithStateCosted_value_built xs (canonicalBlockSize xs) left right

theorem freshQueryCosted_cost
    (xs : List Int) (left right : Nat) :
    (freshQueryCosted xs left right).cost =
      buildCost xs (canonicalBlockSize xs) +
        queryWithStateCost xs (build xs) left right := by
  simp [freshQueryCosted, buildCosted_cost, queryWithStateCosted_cost,
    build]

theorem freshQueryCosted_run
    (xs : List Int) (left right : Nat) :
    Costed.run (freshQueryCosted xs left right) =
      (query xs left right,
        buildCost xs (canonicalBlockSize xs) +
          queryWithStateCost xs (build xs) left right) := by
  simp [Costed.run, freshQueryCosted_cost]

theorem queryWithState_valid_exact
    (xs : List Int) (state : State) (left right : Nat)
    (hValid : ValidRange xs left right) :
    exists idx,
      queryWithState xs state left right = some idx /\
        LeftmostArgMin xs left right idx := by
  by_cases hb : 0 < state.blockSize
  case pos =>
    let b := state.blockSize
    let leftBlock := leftBoundaryBlock left b
    let rightBlock := rightBoundaryBlock right b
    have hif : ValidRange xs left right := hValid
    by_cases hschedule : leftBlock <= rightBlock
    case pos =>
      let leftStart := (leftBlock - 1) * b
      let leftCandidate :=
        state.microtable.queryIndex? xs leftStart
          (left - leftStart) (leftBlock * b - leftStart)
      let middleCandidate :=
        recursiveMiddleCandidate xs b (summaryBackend xs b)
          leftBlock rightBlock
      let rightStart := rightBlock * b
      let rightCandidate := rightBoundaryCandidate xs state rightStart right
      have hquery :
          queryWithState xs state left right =
            combineIndex xs (combineIndex xs leftCandidate middleCandidate)
              rightCandidate := by
        unfold queryWithState
        simp [hif, hb, b, leftBlock, rightBlock, hschedule, leftStart,
          leftCandidate, middleCandidate, rightStart, rightCandidate]
      have hleft_lt_end : left < leftBlock * b := by
        simpa [leftBlock, b] using
          left_lt_leftBoundaryBlock_mul (left := left) hb
      have hrightStart_le_right : rightStart <= right := by
        simpa [rightStart, rightBlock, b] using
          rightBoundaryBlock_mul_le right b
      have hleftEnd_le_rightStart : leftBlock * b <= rightStart := by
        simpa [rightStart] using Nat.mul_le_mul_right b hschedule
      have hleftEnd_le_right : leftBlock * b <= right :=
        Nat.le_trans hleftEnd_le_rightStart hrightStart_le_right
      have hleftEnd_le_len : leftBlock * b <= xs.length :=
        Nat.le_trans hleftEnd_le_right hValid.2
      have hleftBlock_pos : 0 < leftBlock := by
        simp [leftBlock, leftBoundaryBlock]
      have hleftStart_eq : leftStart + b = leftBlock * b := by
        have hsucc : leftBlock - 1 + 1 = leftBlock :=
          Nat.sub_add_cancel (Nat.succ_le_iff.mpr hleftBlock_pos)
        calc
          leftStart + b = (leftBlock - 1) * b + 1 * b := by
            simp [leftStart]
          _ = ((leftBlock - 1) + 1) * b := by
            rw [Nat.add_mul, Nat.one_mul]
          _ = leftBlock * b := by
            rw [hsucc]
      have hleftBound : leftStart + state.blockSize <= xs.length := by
        change leftStart + b <= xs.length
        simpa [hleftStart_eq] using hleftEnd_le_len
      have hleftStart_floor : leftStart = (left / b) * b := by
        simp [leftStart, leftBlock, leftBoundaryBlock]
      have hleftStart_le_left : leftStart <= left := by
        rw [hleftStart_floor]
        exact Nat.div_mul_le_self left b
      have hleftValid : ValidRange xs left (leftBlock * b) :=
        And.intro hleft_lt_end hleftEnd_le_len
      exact Exists.elim
        (microQueryIndex_valid_exact state.microtable hleftBound
          hleftStart_le_left (by omega) hleftValid)
        (fun li hleftPair => by
          cases hleftPair with
          | intro hlres hlarg =>
            have hright_lt_next : right < rightStart + b := by
              have h :=
                Nat.lt_div_mul_add hb (a := right)
              simpa [Nat.add_mul, Nat.one_mul, Nat.add_comm,
                Nat.add_left_comm, Nat.add_assoc, rightStart, rightBlock,
                b] using h
            have hRight :
                CandidateExact xs rightStart right rightCandidate := by
              exact rightBoundaryCandidate_exact xs state rightStart right
                hrightStart_le_right hValid.2 (by omega)
            have hrightBlock :
                rightBlock <= compressedLength xs.length b := by
              simpa [rightBlock, b] using
                rightBoundaryBlock_le_compressed (xs := xs) (b := b)
                  (right := right) hb hValid.2
            exact Exists.elim
              (combineRecursiveMiddleLeftmost
                (xs := xs) (b := b) (left := left)
                (leftBlock := leftBlock) (rightBlock := rightBlock)
                (right := right) (li := li)
                (rightCandidate := rightCandidate)
                (summaryBackend xs b) hb hlarg hschedule hrightBlock
                hRight hrightStart_le_right)
              (fun idx hcombinedPair => by
                cases hcombinedPair with
                | intro hcombined harg =>
                  refine Exists.intro idx ?_
                  refine And.intro ?_ harg
                  rw [hquery]
                  simpa [leftCandidate, middleCandidate, rightCandidate,
                    hlres, RMQ.RecursiveHybrid.combineIndex,
                    RMQ.combineIndex] using hcombined))
    case neg =>
      let blockStart := rightBlock * b
      have hquery :
          queryWithState xs state left right =
            localBlockCandidate xs state blockStart left right := by
        unfold queryWithState
        simp [hValid, hb, b, leftBlock, rightBlock, hschedule, blockStart]
      have hblockStart_le_left : blockStart <= left := by
        have hrightBlock_lt_leftBlock : rightBlock < leftBlock := by omega
        have htmp : rightBlock < left / b + 1 := by
          simpa [leftBlock, leftBoundaryBlock] using hrightBlock_lt_leftBlock
        have hrightBlock_le_left_div : rightBlock <= left / b := by omega
        have hmul := Nat.mul_le_mul_right b hrightBlock_le_left_div
        have hfloor : (left / b) * b <= left := Nat.div_mul_le_self left b
        exact Nat.le_trans (by simpa [blockStart] using hmul) hfloor
      have hright_block : right <= blockStart + state.blockSize := by
        have hlt := Nat.lt_div_mul_add hb (a := right)
        simpa [blockStart, rightBlock, b, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc] using Nat.le_of_lt hlt
      have hlocalExact :
          CandidateExact xs left right
            (localBlockCandidate xs state blockStart left right) :=
        localBlockCandidate_exact xs state blockStart left right
          hblockStart_le_left (Nat.le_of_lt hValid.1) hValid.2
          hright_block
      exact Exists.elim
        (hlocalExact.exists_of_nonempty hValid.1)
        (fun idx hpair => by
          cases hpair with
          | intro hres harg =>
            refine Exists.intro idx ?_
            refine And.intro ?_ harg
            rw [hquery]
            exact hres)
  case neg =>
    have hquery :
        queryWithState xs state left right =
          RMQ.LinearScan.query xs left right := by
      unfold queryWithState
      simp [hValid, hb]
    exact Exists.elim
      (RMQ.LinearScan.query_valid_exact xs left right hValid)
      (fun idx hpair => by
        cases hpair with
        | intro hres harg =>
          refine Exists.intro idx ?_
          refine And.intro ?_ harg
          rw [hquery]
          exact hres)

theorem queryWithState_sound
    {xs : List Int} {state : State} {left right idx : Nat}
    (hres : queryWithState xs state left right = some idx) :
    LeftmostArgMin xs left right idx := by
  by_cases hValid : ValidRange xs left right
  case pos =>
    exact Exists.elim
      (queryWithState_valid_exact xs state left right hValid)
      (fun idx' hpair => by
        cases hpair with
        | intro hres' harg' =>
          have hidx : idx = idx' := by
            have hsome : some idx = some idx' := by
              rw [<- hres, hres']
            exact Option.some.inj hsome
          simpa [hidx] using harg')
  case neg =>
    unfold queryWithState at hres
    simp [hValid] at hres

theorem queryWithState_complete
    {xs : List Int} {state : State} {left right idx : Nat}
    (harg : LeftmostArgMin xs left right idx) :
    queryWithState xs state left right = some idx := by
  have hValid : ValidRange xs left right := LeftmostArgMin.valid harg
  exact Exists.elim
    (queryWithState_valid_exact xs state left right hValid)
    (fun idx' hpair => by
      cases hpair with
      | intro hres' harg' =>
        have hidx : idx' = idx :=
          leftmostArgMin_unique xs left right idx' idx harg' harg
        simpa [hidx] using hres')

theorem queryWithState_invalid_none
    {xs : List Int} {state : State} {left right : Nat}
    (hbad : Not (ValidRange xs left right)) :
    queryWithState xs state left right = none := by
  unfold queryWithState
  simp [hbad]

/-- Backend with an explicit Fischer-Heun block size. -/
def backendWithBlockSize (xs : List Int) (blockSize : Nat) : RMQBackend xs where
  State := State
  build := buildWithBlockSize xs blockSize
  query := queryWithState xs
  sound := by
    intro left right idx hres
    exact queryWithState_sound (state := buildWithBlockSize xs blockSize) hres
  complete := by
    intro left right idx harg
    exact queryWithState_complete
      (state := buildWithBlockSize xs blockSize) harg
  invalid_none := by
    intro left right hbad
    exact queryWithState_invalid_none
      (state := buildWithBlockSize xs blockSize) hbad

/-- Public Fischer-Heun backend using the canonical quarter-log block size. -/
def backend (xs : List Int) : RMQBackend xs :=
  backendWithBlockSize xs (canonicalBlockSize xs)

theorem query_sound {xs : List Int} {left right idx : Nat}
    (hres : query xs left right = some idx) :
    LeftmostArgMin xs left right idx := by
  unfold query at hres
  exact queryWithState_sound hres

theorem query_complete {xs : List Int} {left right idx : Nat}
    (harg : LeftmostArgMin xs left right idx) :
    query xs left right = some idx := by
  unfold query
  exact queryWithState_complete harg

theorem invalid_none {xs : List Int} {left right : Nat}
    (hbad : Not (ValidRange xs left right)) :
    query xs left right = none := by
  unfold query
  exact queryWithState_invalid_none hbad

/--
Large-input side condition for the canonical quarter-log Fischer-Heun profile.

Small inputs can still use the exact value-level Fischer-Heun query, but the
linear-build/constant-supplied-query cost certificate is currently stated for
this finite-table regime.
-/
def canonicalReady (xs : List Int) : Prop :=
  16 <= canonicalBlockSize xs

instance canonicalReadyDecidable (xs : List Int) :
    Decidable (canonicalReady xs) := by
  unfold canonicalReady
  infer_instance

/--
All-input RMQ query policy.

Large inputs use the canonical Fischer-Heun assembly. Inputs outside the
current canonical cost regime fall back to the reference linear scan.
-/
def allInputQuery (xs : List Int) (left right : Nat) : Option Nat :=
  if _hlarge : canonicalReady xs then
    query xs left right
  else
    RMQ.LinearScan.query xs left right

@[simp] theorem allInputQuery_large
    {xs : List Int} {left right : Nat} (hlarge : canonicalReady xs) :
    allInputQuery xs left right = query xs left right := by
  simp [allInputQuery, hlarge]

@[simp] theorem allInputQuery_small
    {xs : List Int} {left right : Nat} (hlarge : Not (canonicalReady xs)) :
    allInputQuery xs left right = RMQ.LinearScan.query xs left right := by
  simp [allInputQuery, hlarge]

/-- Exact cost expression for the all-input fresh query policy. -/
def allInputQueryCost (xs : List Int) (left right : Nat) : Nat :=
  if _hlarge : canonicalReady xs then
    buildCost xs (canonicalBlockSize xs) +
      queryWithStateCost xs (build xs) left right
  else
    rangeScanCost xs left right

/-- Costed all-input fresh query policy. -/
def allInputQueryCosted (xs : List Int) (left right : Nat) :
    Costed (Option Nat) :=
  if _hlarge : canonicalReady xs then
    freshQueryCosted xs left right
  else
    rangeScanCosted xs left right

@[simp] theorem allInputQueryCosted_value
    (xs : List Int) (left right : Nat) :
    (allInputQueryCosted xs left right).value =
      allInputQuery xs left right := by
  unfold allInputQueryCosted allInputQuery
  by_cases hlarge : canonicalReady xs
  case pos =>
    rw [dif_pos hlarge, dif_pos hlarge]
    exact freshQueryCosted_value xs left right
  case neg =>
    rw [dif_neg hlarge, dif_neg hlarge]
    simp [RMQ.LinearScan.query]

theorem allInputQueryCosted_cost
    (xs : List Int) (left right : Nat) :
    (allInputQueryCosted xs left right).cost =
      allInputQueryCost xs left right := by
  unfold allInputQueryCosted allInputQueryCost
  by_cases hlarge : canonicalReady xs
  case pos =>
    rw [dif_pos hlarge, dif_pos hlarge]
    exact freshQueryCosted_cost xs left right
  case neg =>
    rw [dif_neg hlarge, dif_neg hlarge]
    exact rangeScanCosted_cost xs left right

theorem allInputQueryCosted_run
    (xs : List Int) (left right : Nat) :
    Costed.run (allInputQueryCosted xs left right) =
      (allInputQuery xs left right, allInputQueryCost xs left right) := by
  simp [Costed.run, allInputQueryCosted_cost]

theorem allInputQueryCost_large
    {xs : List Int} {left right : Nat} (hlarge : canonicalReady xs) :
    allInputQueryCost xs left right =
      buildCost xs (canonicalBlockSize xs) +
        queryWithStateCost xs (build xs) left right := by
  simp [allInputQueryCost, hlarge]

theorem allInputQueryCost_small
    {xs : List Int} {left right : Nat}
    (hlarge : Not (canonicalReady xs)) :
    allInputQueryCost xs left right = rangeScanCost xs left right := by
  simp [allInputQueryCost, hlarge]

theorem allInputQueryCost_le_build_plus_supplied_of_large_stored
    {xs : List Int} {left right : Nat}
    (hlarge : canonicalReady xs)
    (hschedule :
      leftBoundaryBlock left (canonicalBlockSize xs) <=
        rightBoundaryBlock right (canonicalBlockSize xs))
    (hright :
      rightBoundaryBlock right (canonicalBlockSize xs) *
          canonicalBlockSize xs = right \/
        rightBoundaryBlock right (canonicalBlockSize xs) *
            canonicalBlockSize xs + canonicalBlockSize xs <= xs.length) :
    allInputQueryCost xs left right <=
      buildCost xs (canonicalBlockSize xs) +
        suppliedQueryCost xs (canonicalBlockSize xs) left right := by
  rw [allInputQueryCost_large hlarge]
  have hbCanon : 0 < canonicalBlockSize xs := by
    have h : 16 <= canonicalBlockSize xs := by
      simpa [canonicalReady] using hlarge
    omega
  have hb : 0 < (build xs).blockSize := by
    simpa [build] using hbCanon
  have hscheduleBuild :
      leftBoundaryBlock left (build xs).blockSize <=
        rightBoundaryBlock right (build xs).blockSize := by
    simpa [build] using hschedule
  have hrightBuild :
      rightBoundaryBlock right (build xs).blockSize *
          (build xs).blockSize = right \/
        rightBoundaryBlock right (build xs).blockSize *
            (build xs).blockSize + (build xs).blockSize <= xs.length := by
    simpa [build] using hright
  have hquery :=
    queryWithStateCost_le_suppliedQueryCost_of_stored
      (xs := xs) (state := build xs) (left := left) (right := right)
      hb hscheduleBuild hrightBuild
  exact Nat.add_le_add_left (by simpa [build] using hquery)
    (buildCost xs (canonicalBlockSize xs))

theorem allInputQueryCosted_cost_le_build_plus_supplied_of_large_stored
    {xs : List Int} {left right : Nat}
    (hlarge : canonicalReady xs)
    (hschedule :
      leftBoundaryBlock left (canonicalBlockSize xs) <=
        rightBoundaryBlock right (canonicalBlockSize xs))
    (hright :
      rightBoundaryBlock right (canonicalBlockSize xs) *
          canonicalBlockSize xs = right \/
        rightBoundaryBlock right (canonicalBlockSize xs) *
            canonicalBlockSize xs + canonicalBlockSize xs <= xs.length) :
    (allInputQueryCosted xs left right).cost <=
      buildCost xs (canonicalBlockSize xs) +
        suppliedQueryCost xs (canonicalBlockSize xs) left right := by
  rw [allInputQueryCosted_cost]
  exact allInputQueryCost_le_build_plus_supplied_of_large_stored
    hlarge hschedule hright

theorem queryWithStateCost_built_le_thirteen_of_large
    {xs : List Int} (hlarge : canonicalReady xs) (left right : Nat) :
    queryWithStateCost xs (build xs) left right <= 13 := by
  have hcanon : 16 <= canonicalBlockSize xs := by
    simpa [canonicalReady] using hlarge
  have hbCanon : 0 < canonicalBlockSize xs := by
    omega
  have hb : 0 < (build xs).blockSize := by
    simpa [build] using hbCanon
  exact queryWithStateCost_le_thirteen_of_blockSize_pos
    xs (build xs) left right hb

theorem queryWithStateCosted_built_cost_le_thirteen_of_large
    {xs : List Int} (hlarge : canonicalReady xs) (left right : Nat) :
    (queryWithStateCosted xs (build xs) left right).cost <= 13 := by
  rw [queryWithStateCosted_cost]
  exact queryWithStateCost_built_le_thirteen_of_large hlarge left right

/--
Large-regime supplied-query capstone for the assembled Fischer-Heun backend.

The costed public query erases to the verified value query, and its live
stored-summary/stored-microtable path has constant supplied-query cost in the
RAM/unit-cost indexed-access model.
-/
theorem fischerHeun_refines_with_steps
    {xs : List Int} (hlarge : canonicalReady xs) (left right : Nat) :
    (queryCosted xs left right).value = query xs left right ∧
      (queryCosted xs left right).cost <= 13 := by
  constructor
  · exact queryCosted_value xs left right
  · unfold queryCosted
    exact queryWithStateCosted_built_cost_le_thirteen_of_large
      hlarge left right

/--
Large-regime fresh build+query capstone for the assembled Fischer-Heun backend.

This composes the existing canonical build-cost theorem with the live
stored-summary/stored-microtable supplied-query bound.  It is a component
budget over the current `Costed` builder/query wrappers, not a monolithic
`RAM.Exec` preprocessing program.
-/
theorem fischerHeun_fresh_refines_with_build_query_steps_of_large
    {xs : List Int} (hlarge : canonicalReady xs) (left right : Nat) :
    (freshQueryCosted xs left right).value = query xs left right ∧
      buildCost xs (canonicalBlockSize xs) <= 15 * xs.length ∧
      (queryWithStateCosted xs (build xs) left right).cost <= 13 ∧
      (freshQueryCosted xs left right).cost <= 15 * xs.length + 13 := by
  have hb16 : 16 <= canonicalBlockSize xs := by
    simpa [canonicalReady] using hlarge
  have hpos := canonicalBlockSize_pos_length_of_ge_sixteen (xs := xs) hb16
  have hmicro := rawMicrotableSlotBudget_canonical_le_length xs hpos
  have hsummary := summaryLog_canonical_le_four_mul xs hb16
  have hbuild :
      buildCost xs (canonicalBlockSize xs) <= 15 * xs.length :=
    buildCost_le_fifteen_mul_length xs (canonicalBlockSize xs)
      hmicro hsummary
  have hquery :
      (queryWithStateCosted xs (build xs) left right).cost <= 13 :=
    queryWithStateCosted_built_cost_le_thirteen_of_large
      hlarge left right
  constructor
  · exact freshQueryCosted_value xs left right
  constructor
  · exact hbuild
  constructor
  · exact hquery
  · rw [freshQueryCosted_cost]
    rw [queryWithStateCosted_cost] at hquery
    exact Nat.add_le_add hbuild hquery

theorem allInputQueryCost_large_le_build_plus_thirteen
    {xs : List Int} {left right : Nat} (hlarge : canonicalReady xs) :
    allInputQueryCost xs left right <=
      buildCost xs (canonicalBlockSize xs) + 13 := by
  rw [allInputQueryCost_large hlarge]
  exact Nat.add_le_add_left
    (queryWithStateCost_built_le_thirteen_of_large hlarge left right)
    (buildCost xs (canonicalBlockSize xs))

theorem allInputQueryCosted_cost_large_le_build_plus_thirteen
    {xs : List Int} {left right : Nat} (hlarge : canonicalReady xs) :
    (allInputQueryCosted xs left right).cost <=
      buildCost xs (canonicalBlockSize xs) + 13 := by
  rw [allInputQueryCosted_cost]
  exact allInputQueryCost_large_le_build_plus_thirteen hlarge

/--
Canonical large-input profile for the assembled all-input policy.

The build side is linear in `xs.length`; supplied queries against the built
canonical Fischer-Heun state are bounded by a constant in the RAM/unit-cost
indexed-access model.
-/
theorem linearBuild_constantQuery_profile_allInput_large :
    exists buildC queryC,
      forall xs,
        canonicalReady xs ->
          buildCost xs (canonicalBlockSize xs) <= buildC * xs.length /\
            forall left right,
              queryWithStateCost xs (build xs) left right <= queryC := by
  refine Exists.intro 15 ?_
  refine Exists.intro 13 ?_
  intro xs hlarge
  have hb16 : 16 <= canonicalBlockSize xs := by
    simpa [canonicalReady] using hlarge
  have hpos := canonicalBlockSize_pos_length_of_ge_sixteen (xs := xs) hb16
  have hmicro := rawMicrotableSlotBudget_canonical_le_length xs hpos
  have hsummary := summaryLog_canonical_le_four_mul xs hb16
  exact And.intro
    (buildCost_le_fifteen_mul_length xs (canonicalBlockSize xs)
      hmicro hsummary)
    (fun left right =>
      queryWithStateCost_built_le_thirteen_of_large hlarge left right)

theorem allInputQuery_sound {xs : List Int} {left right idx : Nat}
    (hres : allInputQuery xs left right = some idx) :
    LeftmostArgMin xs left right idx := by
  unfold allInputQuery at hres
  by_cases hlarge : canonicalReady xs
  case pos =>
    rw [dif_pos hlarge] at hres
    exact query_sound hres
  case neg =>
    rw [dif_neg hlarge] at hres
    exact RMQ.LinearScan.query_sound hres

theorem allInputQuery_complete
    {xs : List Int} {left right idx : Nat}
    (harg : LeftmostArgMin xs left right idx) :
    allInputQuery xs left right = some idx := by
  unfold allInputQuery
  by_cases hlarge : canonicalReady xs
  case pos =>
    rw [dif_pos hlarge]
    exact query_complete harg
  case neg =>
    rw [dif_neg hlarge]
    exact RMQ.LinearScan.query_complete harg

theorem allInputQuery_valid_exact
    (xs : List Int) (left right : Nat)
    (hValid : ValidRange xs left right) :
    exists idx,
      allInputQuery xs left right = some idx /\
        LeftmostArgMin xs left right idx := by
  exact Exists.elim
    (RMQ.LinearScan.query_valid_exact xs left right hValid)
    (fun idx hpair => by
      exact Exists.intro idx
        (And.intro (allInputQuery_complete hpair.2) hpair.2))

theorem allInputQuery_invalid_none
    {xs : List Int} {left right : Nat}
    (hbad : Not (ValidRange xs left right)) :
    allInputQuery xs left right = none := by
  unfold allInputQuery
  by_cases hlarge : canonicalReady xs
  case pos =>
    rw [dif_pos hlarge]
    exact invalid_none hbad
  case neg =>
    rw [dif_neg hlarge]
    exact RMQ.LinearScan.invalid_none hbad

/-!
## Lower-bound state encoding

The next definitions instantiate the abstract lower-bound interface with a
Fischer-Heun-shaped state. The `payload` field is the only bitstring charged by
`ExactRMQStateEncoding`; the ordinary built Fischer-Heun state is retained as
proof/certificate data and is deliberately ignored by `encodeState`.
-/

/-- Fischer-Heun-shaped state for the lower-bound adapter. -/
structure EncodedState (n : Nat) where
  payload : List Bool
  built : State

/--
Build the lower-bound state for a representative shape.

The proof-only `built` component is the ordinary one-block Fischer-Heun state
over the canonical representative array; the counted payload is only the
explicit Cartesian shape code tail.
-/
def encodedStateOfShape
    (n : Nat) (shape : Cartesian.CartesianShape) : EncodedState n where
  payload := EncodingLowerBound.canonicalShapePayload shape
  built := buildWithBlockSize shape.representative n

/--
Payload-only query decoder for the Fischer-Heun-shaped lower-bound state.

After decoding the block shape, this performs the same one-block raw
microtable lookup used by the whole-list microtable backend. It does not read
the proof-only built state.
-/
def encodedStateQuery
    (n : Nat) (payload : List Bool) (left right : Nat) : Option Nat :=
  match EncodingLowerBound.decodeShapePayload? n payload with
  | some shape =>
      (RMQ.Cartesian.Microtable.raw n).queryIndex?
        shape.representative 0 left right
  | none => none

/--
Concrete Fischer-Heun-shaped instance of `ExactRMQStateEncoding`.

This is still a baseline explicit-shape payload of length `2*n`, but the state
layout separates the charged payload from the certified Fischer-Heun build
fields. That is the lower-bound interface shape needed before connecting more
compressed concrete layouts.
-/
def stateEncoding (n : Nat) :
    EncodingLowerBound.ExactRMQStateEncoding n (2 * n) where
  State := EncodedState n
  buildState := encodedStateOfShape n
  encodeState state := state.payload
  queryEncoded := encodedStateQuery n
  sample shape := shape.representative
  length_eq := by
    intro shape hmem
    exact Cartesian.CartesianShape.fullCode_tail_length_of_shapeOfSize
      (Cartesian.mem_shapesOfSize_shapeOfSize hmem)
  sample_length_eq := by
    intro shape hmem
    have hshape := Cartesian.mem_shapesOfSize_shapeOfSize hmem
    rw [Cartesian.CartesianShape.representative_length,
      Cartesian.ShapeOfSize.size_eq hshape]
  sample_shape_eq := by
    intro shape _hmem
    exact Cartesian.CartesianShape.shape_representative shape
  query_exact := by
    intro shape hmem left len hlen hbound
    have hshape := Cartesian.mem_shapesOfSize_shapeOfSize hmem
    have hdecode :=
      EncodingLowerBound.decodeShapePayload?_canonicalShapePayload hshape
    have hrepLen : shape.representative.length = n := by
      rw [Cartesian.CartesianShape.representative_length,
        Cartesian.ShapeOfSize.size_eq hshape]
    have htable :=
      RMQ.Cartesian.Microtable.queryIndex?_eq
        (RMQ.Cartesian.Microtable.raw n)
        (xs := shape.representative) (start := 0)
        (left := left) (right := left + len)
        (by omega)
    have hlocal :
        RMQ.Cartesian.LocalValid n left (left + len) := by
      unfold RMQ.Cartesian.LocalValid
      omega
    have hsub : left + len - left = len := by omega
    simp [encodedStateOfShape, encodedStateQuery, hdecode, htable, hlocal,
      hsub]

theorem two_mul_sub_log_slack_le_bits_of_stateEncoding
    (n : Nat) :
    2 * n - (2 * Nat.log2 (2 * n + 1) + 2) <= 2 * n :=
  EncodingLowerBound.two_mul_sub_log_slack_le_bits_of_exactRMQStateEncoding
    (stateEncoding n)

/--
Two-sided fixed-length space sandwich using the Fischer-Heun-shaped state
encoding as the concrete upper witness.

The charged payload remains the explicit `2*n` Cartesian-shape payload; the
ordinary Fischer-Heun build stored in the state is proof-only auxiliary data.
-/
def stateEncodingSpaceBounds (n : Nat) :
    EncodingLowerBound.ExactRMQSpaceBounds
      n (EncodingLowerBound.logSlackLower n) (2 * n) where
  lower_le_any := by
    intro bits encoding
    exact
      EncodingLowerBound.two_mul_sub_log_slack_le_bits_of_exactRMQStateEncoding
        encoding
  upperEncoding := stateEncoding n

theorem exactRMQ_two_sided_log_slack_space_bound_stateEncoding
    (n : Nat) :
    (forall {bits : Nat}, EncodingLowerBound.ExactRMQStateEncoding n bits ->
        EncodingLowerBound.logSlackLower n <= bits) ∧
      (exists _encoding :
        EncodingLowerBound.ExactRMQStateEncoding n (2 * n), True) := by
  exact ⟨(stateEncodingSpaceBounds n).lower_le_any,
    ⟨(stateEncodingSpaceBounds n).upperEncoding, True.intro⟩⟩

/-- All-input backend with linear-scan fallback outside the canonical regime. -/
def allInputBackend (xs : List Int) : RMQBackend xs where
  State := Unit
  build := ()
  query := fun _ => allInputQuery xs
  sound := by
    intro left right idx hres
    exact allInputQuery_sound hres
  complete := by
    intro left right idx harg
    exact allInputQuery_complete harg
  invalid_none := by
    intro left right hbad
    exact allInputQuery_invalid_none hbad

end FischerHeun

end RMQ
