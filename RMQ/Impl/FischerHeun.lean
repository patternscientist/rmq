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

/-- Build using the canonical quarter-log block size from the cost profile. -/
def build (xs : List Int) : State :=
  buildWithBlockSize xs (canonicalBlockSize xs)

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
