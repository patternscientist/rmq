import RMQ.Core.Microtable
import RMQ.Impl.FischerHeunCost
import RMQ.Impl.RecursiveHybrid
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

/--
Right-boundary candidate.

The final queried boundary can lie in a short trailing block.  Full concrete
blocks use the certified shape microtable; short trailing blocks fall back to
the direct scan until the public wrapper grows a padding or tail policy.
-/
def rightBoundaryCandidate
    (xs : List Int) (state : State) (start right : Nat) : Option Nat :=
  if _hnonempty : start < right then
    if _hbound : start + state.blockSize <= xs.length then
      state.microtable.queryIndex? xs start 0 (right - start)
    else
      RMQ.LinearScan.query xs start right
  else
    none

theorem rightBoundaryCandidate_exact
    (xs : List Int) (state : State) (start right : Nat)
    (hstart_right : start <= right)
    (hright_len : right <= xs.length)
    (hright_block : right <= start + state.blockSize) :
    CandidateExact xs start right
      (rightBoundaryCandidate xs state start right) := by
  unfold rightBoundaryCandidate
  by_cases hnonempty : start < right
  case pos =>
    simp [hnonempty]
    by_cases hbound : start + state.blockSize <= xs.length
    case pos =>
      simp [hbound]
      exact Exists.elim
        (microQueryIndex_valid_exact state.microtable hbound
          (by omega) hright_block (And.intro hnonempty hright_len))
        (fun idx hpair => by
          cases hpair with
          | intro hquery harg =>
            have hzero : start - start = 0 := by omega
            have hquery_zero :
                state.microtable.queryIndex? xs start 0 (right - start) =
                  some idx := by
              simpa [hzero] using hquery
            exact Or.inr (Exists.intro idx (And.intro hquery_zero harg)))
    case neg =>
      simp [hbound]
      exact Exists.elim
        (RMQ.LinearScan.query_valid_exact xs start right
          (And.intro hnonempty hright_len))
        (fun idx hpair => by
          cases hpair with
          | intro hquery harg =>
            exact Or.inr (Exists.intro idx (And.intro hquery harg)))
  case neg =>
    simp [hnonempty]
    exact Or.inl (And.intro rfl (by omega))

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

/-- Costed materialization of the fixed-size shape microtable family. -/
def microtableBuildCosted (blockSize : Nat) :
    Costed (MicrotableFor blockSize) :=
  Costed.tickValue (rawMicrotableSlotBudget blockSize)
    (RMQ.Cartesian.Microtable.raw blockSize)

@[simp] theorem microtableBuildCosted_value (blockSize : Nat) :
    (microtableBuildCosted blockSize).value =
      RMQ.Cartesian.Microtable.raw blockSize := by
  rfl

theorem microtableBuildCosted_cost (blockSize : Nat) :
    (microtableBuildCosted blockSize).cost =
      rawMicrotableSlotBudget blockSize := by
  rfl

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
            summaryTable := summaryTable }

@[simp] theorem buildWithBlockSizeCosted_value
    (xs : List Int) (blockSize : Nat) :
    (buildWithBlockSizeCosted xs blockSize).value =
      buildWithBlockSize xs blockSize := by
  simp [buildWithBlockSizeCosted, buildWithBlockSize, microtableBuildCosted]

theorem buildWithBlockSizeCosted_cost
    (xs : List Int) (blockSize : Nat) :
    (buildWithBlockSizeCosted xs blockSize).cost =
      buildCost xs blockSize := by
  simp [buildWithBlockSizeCosted, microtableBuildCosted, buildCost,
    summarySparseBuildCost, RMQ.RecursiveHybrid.blockMinSummaryCosted_cost,
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
        RMQ.LinearScan.query xs left right
    else
      RMQ.LinearScan.query xs left right
  else
    none

/-- Costed materialized local-table lookup for a supplied Fischer-Heun state. -/
def microQueryIndexCosted
    (xs : List Int) (state : State)
    (start left right : Nat) : Costed (Option Nat) :=
  Costed.tickValue materializedMicrotableLookupCost
    (state.microtable.queryIndex? xs start left right)

@[simp] theorem microQueryIndexCosted_value
    (xs : List Int) (state : State) (start left right : Nat) :
    (microQueryIndexCosted xs state start left right).value =
      state.microtable.queryIndex? xs start left right := by
  rfl

theorem microQueryIndexCosted_cost
    (xs : List Int) (state : State) (start left right : Nat) :
    (microQueryIndexCosted xs state start left right).cost =
      materializedMicrotableLookupCost := by
  rfl

/-- Exact cost expression for the costed right-boundary candidate. -/
def rightBoundaryCandidateCost
    (xs : List Int) (state : State) (start right : Nat) : Nat :=
  if _hnonempty : start < right then
    if _hbound : start + state.blockSize <= xs.length then
      materializedMicrotableLookupCost
    else
      rangeScanCost xs start right
  else
    1

/-- Costed right-boundary candidate matching `rightBoundaryCandidate`. -/
def rightBoundaryCandidateCosted
    (xs : List Int) (state : State) (start right : Nat) :
    Costed (Option Nat) :=
  if _hnonempty : start < right then
    if _hbound : start + state.blockSize <= xs.length then
      microQueryIndexCosted xs state start 0 (right - start)
    else
      rangeScanCosted xs start right
  else
    Costed.tickValue 1 none

@[simp] theorem rightBoundaryCandidateCosted_value
    (xs : List Int) (state : State) (start right : Nat) :
    (rightBoundaryCandidateCosted xs state start right).value =
      rightBoundaryCandidate xs state start right := by
  unfold rightBoundaryCandidateCosted rightBoundaryCandidate
  by_cases hnonempty : start < right
  case pos =>
    rw [dif_pos hnonempty, dif_pos hnonempty]
    by_cases hbound : start + state.blockSize <= xs.length
    case pos =>
      rw [dif_pos hbound, dif_pos hbound]
      simp [microQueryIndexCosted]
    case neg =>
      rw [dif_neg hbound, dif_neg hbound]
      simp [RMQ.LinearScan.query]
  case neg =>
    rw [dif_neg hnonempty, dif_neg hnonempty]
    simp

theorem rightBoundaryCandidateCosted_cost
    (xs : List Int) (state : State) (start right : Nat) :
    (rightBoundaryCandidateCosted xs state start right).cost =
      rightBoundaryCandidateCost xs state start right := by
  unfold rightBoundaryCandidateCosted rightBoundaryCandidateCost
  by_cases hnonempty : start < right
  case pos =>
    rw [dif_pos hnonempty, dif_pos hnonempty]
    by_cases hbound : start + state.blockSize <= xs.length
    case pos =>
      rw [dif_pos hbound, dif_pos hbound]
      simp [microQueryIndexCosted_cost]
    case neg =>
      rw [dif_neg hbound, dif_neg hbound]
      exact rangeScanCosted_cost xs start right
  case neg =>
    rw [dif_neg hnonempty, dif_neg hnonempty]
    rfl

theorem rightBoundaryCandidateCost_eq_materialized
    {xs : List Int} {state : State} {start right : Nat}
    (hmaterialized :
      start = right \/ start + state.blockSize <= xs.length) :
    rightBoundaryCandidateCost xs state start right =
      materializedMicrotableLookupCost := by
  unfold rightBoundaryCandidateCost
  by_cases hnonempty : start < right
  case pos =>
    rw [dif_pos hnonempty]
    rcases hmaterialized with hempty | hbound
    case inl =>
      omega
    case inr =>
      rw [dif_pos hbound]
  case neg =>
    rw [dif_neg hnonempty]
    rfl

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
        materializedMicrotableLookupCost +
          SparseTable.queryFromTableCost (blockMinSummary xs b)
            leftBlock rightBlock +
            rightBoundaryCandidateCost xs state rightStart right + 2
      else
        rangeScanCost xs left right
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
        let rightStart := rightBlock * b
        Costed.bind
          (microQueryIndexCosted xs state leftStart
            (left - leftStart) (leftBlock * b - leftStart))
          fun leftCandidate =>
        Costed.bind
          (Costed.map (liftBlockCandidate xs b)
            (SparseTable.queryFromTableCosted (blockMinSummary xs b)
              state.summaryTable leftBlock rightBlock))
          fun middleCandidate =>
        Costed.bind
          (rightBoundaryCandidateCosted xs state rightStart right)
          fun rightCandidate =>
        Costed.tickValue 2
          (combineIndex xs (combineIndex xs leftCandidate middleCandidate)
            rightCandidate)
      else
        rangeScanCosted xs left right
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
        simp [microQueryIndexCosted_cost, Costed.map_cost,
          SparseTable.queryFromTableCosted_cost,
          rightBoundaryCandidateCosted_cost]
        omega
      case neg =>
        rw [dif_neg hschedule, dif_neg hschedule]
        exact rangeScanCosted_cost xs left right
    case neg =>
      rw [dif_neg hb, dif_neg hb]
      exact rangeScanCosted_cost xs left right
  case neg =>
    rw [dif_neg hValid, dif_neg hValid]
    rfl

theorem queryWithStateCost_eq_suppliedQueryCost_of_materialized
    {xs : List Int} {state : State} {left right : Nat}
    (hb : 0 < state.blockSize)
    (hschedule :
      leftBoundaryBlock left state.blockSize <=
        rightBoundaryBlock right state.blockSize)
    (hright :
      rightBoundaryBlock right state.blockSize * state.blockSize = right \/
        rightBoundaryBlock right state.blockSize * state.blockSize +
            state.blockSize <= xs.length) :
    queryWithStateCost xs state left right =
      suppliedQueryCost xs state.blockSize left right := by
  have hrightCost :
      rightBoundaryCandidateCost xs state
          (rightBoundaryBlock right state.blockSize * state.blockSize) right =
        materializedMicrotableLookupCost := by
    exact rightBoundaryCandidateCost_eq_materialized
      (xs := xs) (state := state)
      (start := rightBoundaryBlock right state.blockSize * state.blockSize)
      (right := right) hright
  simp [queryWithStateCost, suppliedQueryCost, hb, hschedule, hrightCost]

theorem queryWithStateCosted_cost_eq_suppliedQueryCost_of_materialized
    {xs : List Int} {state : State} {left right : Nat}
    (hb : 0 < state.blockSize)
    (hschedule :
      leftBoundaryBlock left state.blockSize <=
        rightBoundaryBlock right state.blockSize)
    (hright :
      rightBoundaryBlock right state.blockSize * state.blockSize = right \/
        rightBoundaryBlock right state.blockSize * state.blockSize +
            state.blockSize <= xs.length) :
    (queryWithStateCosted xs state left right).cost =
      suppliedQueryCost xs state.blockSize left right := by
  rw [queryWithStateCosted_cost]
  exact queryWithStateCost_eq_suppliedQueryCost_of_materialized
    hb hschedule hright

@[simp] theorem queryWithStateCosted_value_built
    (xs : List Int) (blockSize left right : Nat) :
    (queryWithStateCosted xs (buildWithBlockSize xs blockSize) left right).value =
      queryWithState xs (buildWithBlockSize xs blockSize) left right := by
  unfold queryWithStateCosted queryWithState
  by_cases hValid : ValidRange xs left right
  case pos =>
    rw [dif_pos hValid, dif_pos hValid]
    by_cases hb : 0 < blockSize
    case pos =>
      simp [buildWithBlockSize, hb]
      by_cases hschedule :
          leftBoundaryBlock left blockSize <=
            rightBoundaryBlock right blockSize
      case pos =>
        simp [Costed.map_value, recursiveMiddleCandidate, summaryBackend,
          RMQ.SparseTable.memoBackend, rightBoundaryCandidateCosted_value,
          hschedule]
      case neg =>
        simp [RMQ.LinearScan.query, hschedule]
    case neg =>
      simp [buildWithBlockSize, hb, RMQ.LinearScan.query]
  case neg =>
    rw [dif_neg hValid, dif_neg hValid]
    rfl

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
      have hquery :
          queryWithState xs state left right =
            RMQ.LinearScan.query xs left right := by
        unfold queryWithState
        simp [hValid, hb, b, leftBlock, rightBlock, hschedule]
      exact Exists.elim
        (RMQ.LinearScan.query_valid_exact xs left right hValid)
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

example : query [5, 2, 7, 1, 3] 1 4 = some 3 := by native_decide
example : queryWithBlockSize [4, 1, 1, 2] 2 0 4 = some 1 := by native_decide
example : query [5, 2, 7] 2 2 = none := by native_decide

end FischerHeun

end RMQ
