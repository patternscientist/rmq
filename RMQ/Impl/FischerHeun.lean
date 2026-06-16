import RMQ.Core.Microtable
import RMQ.Impl.FischerHeunCost
import RMQ.Impl.RecursiveHybrid
import RMQ.Impl.SparseTableMemoCost

/-!
# Assembled Fischer-Heun RMQ backend

This module starts the value-level Fischer-Heun assembly.  The state carries the
canonical block size, a certified shape microtable, the block-minimum summary,
and the materialized sparse table for that summary.  The first public query
uses the already-certified recursive-hybrid schedule with a memoized sparse
table backend over the summary; the local microtable field is exposed now so
the boundary-scan replacement can be proved against the same state.
-/

namespace RMQ

namespace FischerHeun

/-- Microtable type used by a fixed Fischer-Heun block size. -/
abbrev MicrotableFor (blockSize : Nat) :=
  RMQ.Cartesian.Microtable blockSize

/--
A certified microtable lookup over one full concrete block is an exact global
RMQ answer for the corresponding subinterval.

This is the local lemma needed by the next assembly step, where the current
boundary scans are replaced by shape-table lookups.
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

/--
Materialized Fischer-Heun state.

The query theorem below only depends on `blockSize`; the remaining fields are
the certified/local and supplied-summary artifacts that the fully cost-faithful
backend will consume.
-/
structure State where
  blockSize : Nat
  microtable : MicrotableFor blockSize
  summary : List Int
  summaryTable : List (List (Option Nat))

/-- Sparse-table backend used to answer the block-minimum summary RMQ. -/
def summaryBackend (xs : List Int) (blockSize : Nat) :
    RMQBackend (blockMinSummary xs blockSize) :=
  RMQ.SparseTable.memoBackend (blockMinSummary xs blockSize)

/-- Build a Fischer-Heun state with an explicit block-size choice. -/
def buildWithBlockSize (xs : List Int) (blockSize : Nat) : State :=
  { blockSize := blockSize
    microtable := RMQ.Cartesian.Microtable.raw blockSize
    summary := blockMinSummary xs blockSize
    summaryTable := RMQ.SparseTable.memoBuildSparseTable
      (blockMinSummary xs blockSize) }

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

@[simp] theorem buildWithBlockSize_microtable
    (xs : List Int) (blockSize : Nat) :
    (buildWithBlockSize xs blockSize).microtable =
      RMQ.Cartesian.Microtable.raw blockSize := rfl

/-- Build using the canonical quarter-log block size from the cost profile. -/
def build (xs : List Int) : State :=
  buildWithBlockSize xs (canonicalBlockSize xs)

/--
Query a Fischer-Heun state.

For positive block sizes this composes the aligned recursive-hybrid scheduler
with a memoized sparse-table backend over the block-minimum summary.  The
zero-block case falls back to linear scan, which keeps the API total for small
canonical inputs.
-/
def queryWithState
    (xs : List Int) (state : State) (left right : Nat) : Option Nat :=
  if _hb : 0 < state.blockSize then
    RMQ.RecursiveHybrid.queryWithSummaryBackend xs state.blockSize
      (summaryBackend xs state.blockSize) left right
  else
    RMQ.LinearScan.query xs left right

/-- Query with a freshly built explicit-block-size state. -/
def queryWithBlockSize
    (xs : List Int) (blockSize left right : Nat) : Option Nat :=
  queryWithState xs (buildWithBlockSize xs blockSize) left right

/-- Public query using the canonical quarter-log block size. -/
def query (xs : List Int) (left right : Nat) : Option Nat :=
  queryWithState xs (build xs) left right

theorem queryWithState_valid_exact
    (xs : List Int) (state : State) (left right : Nat)
    (hValid : ValidRange xs left right) :
    exists idx,
      queryWithState xs state left right = some idx /\
        LeftmostArgMin xs left right idx := by
  unfold queryWithState
  by_cases hb : 0 < state.blockSize
  case pos =>
    rw [dif_pos hb]
    exact RMQ.RecursiveHybrid.queryWithSummaryBackend_valid_exact
      xs state.blockSize (summaryBackend xs state.blockSize)
      left right hb hValid
  case neg =>
    rw [dif_neg hb]
    exact RMQ.LinearScan.query_valid_exact xs left right hValid

theorem queryWithState_sound
    {xs : List Int} {state : State} {left right idx : Nat}
    (hres : queryWithState xs state left right = some idx) :
    LeftmostArgMin xs left right idx := by
  unfold queryWithState at hres
  by_cases hb : 0 < state.blockSize
  case pos =>
    rw [dif_pos hb] at hres
    exact RMQ.RecursiveHybrid.queryWithSummaryBackend_sound
      (summaryBackend := summaryBackend xs state.blockSize) hb hres
  case neg =>
    rw [dif_neg hb] at hres
    exact RMQ.LinearScan.query_sound hres

theorem queryWithState_complete
    {xs : List Int} {state : State} {left right idx : Nat}
    (harg : LeftmostArgMin xs left right idx) :
    queryWithState xs state left right = some idx := by
  unfold queryWithState
  by_cases hb : 0 < state.blockSize
  case pos =>
    rw [dif_pos hb]
    exact RMQ.RecursiveHybrid.queryWithSummaryBackend_complete
      (summaryBackend := summaryBackend xs state.blockSize) hb harg
  case neg =>
    rw [dif_neg hb]
    exact RMQ.LinearScan.query_complete harg

theorem queryWithState_invalid_none
    {xs : List Int} {state : State} {left right : Nat}
    (hbad : Not (ValidRange xs left right)) :
    queryWithState xs state left right = none := by
  unfold queryWithState
  by_cases hb : 0 < state.blockSize
  case pos =>
    rw [dif_pos hb]
    exact RMQ.RecursiveHybrid.queryWithSummaryBackend_invalid_none
      (summaryBackend := summaryBackend xs state.blockSize) hbad
  case neg =>
    rw [dif_neg hb]
    exact RMQ.LinearScan.invalid_none hbad

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

example : query [5, 2, 7, 1, 3] 1 4 = some 3 := by native_decide
example : queryWithBlockSize [4, 1, 1, 2] 2 0 4 = some 1 := by native_decide
example : query [5, 2, 7] 2 2 = none := by native_decide

end FischerHeun

end RMQ
