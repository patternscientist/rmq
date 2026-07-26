import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
T1 OBLIGATION MAP -- route bridge (theorems) + anti-vacuity (#eval evidence).
-/

namespace T1Route

/-! ## A. The route bridge: `hlen` and `hcount` for BP codes of equal size. -/

theorem bpCode_hlen {a b : RMQ.Cartesian.CartesianShape} (h : a.size = b.size) :
    a.bpCode.length = b.bpCode.length := by
  rw [RMQ.Cartesian.CartesianShape.bpCode_length,
    RMQ.Cartesian.CartesianShape.bpCode_length, h]

theorem bpCode_hcount {a b : RMQ.Cartesian.CartesianShape} (h : a.size = b.size)
    (target : Bool) :
    RMQ.GenericSelect.occurrenceCount a.bpCode target =
      RMQ.GenericSelect.occurrenceCount b.bpCode target := by
  cases target with
  | true =>
      unfold RMQ.GenericSelect.occurrenceCount
      rw [RMQ.SuccinctClose.bpCode_rankTrue_full,
        RMQ.SuccinctClose.bpCode_rankTrue_full, h]
  | false =>
      unfold RMQ.GenericSelect.occurrenceCount
      rw [RMQ.SuccinctSpace.bpCode_rankFalse_full,
        RMQ.SuccinctSpace.bpCode_rankFalse_full, h]

/-! ## B. Anti-vacuity evidence (compiler `#eval`, not kernel). -/

def noiseStore (salt : Nat) : RMQ.WordRAM.ReadStore where
  readWord? segment index :=
    some ((List.range 16).map fun k =>
      (salt + segment * 7919 + index * 104729 + k * 1299709) % 3 == 0)

partial def shapesOfSize : Nat -> List RMQ.Cartesian.CartesianShape
  | 0 => [RMQ.Cartesian.CartesianShape.empty]
  | Nat.succ n =>
      (List.range (n + 1)).flatMap fun k =>
        (shapesOfSize k).flatMap fun l =>
          (shapesOfSize (n - k)).map fun r =>
            RMQ.Cartesian.CartesianShape.node l r

def leafTraceLen (s : RMQ.Cartesian.CartesianShape)
    (store : RMQ.WordRAM.ReadStore) (idx : Nat) : Nat :=
  (RMQ.SuccinctFinal.concreteBPNativeSelectCloseGlobalWordTraceResultWithStore
      s store idx).trace.length

def leafSegs (s : RMQ.Cartesian.CartesianShape)
    (store : RMQ.WordRAM.ReadStore) (idx : Nat) : List Nat :=
  (RMQ.SuccinctFinal.concreteBPNativeSelectCloseGlobalWordTraceResultWithStore
      s store idx).trace.filterMap fun ev =>
    match ev with
    | RMQ.WordRAM.TraceEvent.readWord seg _ _ => some seg
    | _ => none

#eval show IO Unit from do
  IO.println "-- anti-vacuity: leaf L1 emits probes and responds to the store --"
  for salt in [3, 5, 7] do
    let s := (shapesOfSize 4).headD RMQ.Cartesian.CartesianShape.empty
    IO.println s!"  salt={salt} traceLen={leafTraceLen s (noiseStore salt) 1} segs={leafSegs s (noiseStore salt) 1}"

/-- Equal LENGTH but unequal OCCURRENCE COUNT: the two leaves disagree, so
`hcount` cannot be dropped from T1. -/
def hcountWitnessLHS : RMQ.WordRAM.TraceResult (Option Nat) :=
  (RMQ.GenericSelect.sparseExceptionSelectData [true] true).bpChunkedSelectTraceResultWithStore
    RMQ.SuccinctFinal.concreteBPNativeSelectCloseTraceSegmentLayout
    RMQ.SuccinctFinal.concreteBPNativeFringeChunkTraceSegment
    RMQ.SuccinctFinal.concreteBPNativeSelectChunkTraceSegment
    (noiseStore 3) 8 0

def hcountWitnessRHS : RMQ.WordRAM.TraceResult (Option Nat) :=
  (RMQ.GenericSelect.sparseExceptionSelectData [false] true).bpChunkedSelectTraceResultWithStore
    RMQ.SuccinctFinal.concreteBPNativeSelectCloseTraceSegmentLayout
    RMQ.SuccinctFinal.concreteBPNativeFringeChunkTraceSegment
    RMQ.SuccinctFinal.concreteBPNativeSelectChunkTraceSegment
    (noiseStore 3) 8 0

#eval show IO Unit from do
  IO.println "-- hcount necessity: [true] vs [false], equal length, target=true --"
  IO.println s!"  occurrenceCount [true]  true = {RMQ.GenericSelect.occurrenceCount [true] true}"
  IO.println s!"  occurrenceCount [false] true = {RMQ.GenericSelect.occurrenceCount [false] true}"
  IO.println s!"  LHS traceLen={hcountWitnessLHS.trace.length} value={hcountWitnessLHS.value}"
  IO.println s!"  RHS traceLen={hcountWitnessRHS.trace.length} value={hcountWitnessRHS.value}"
  IO.println s!"  traces equal? {hcountWitnessLHS.trace.length == hcountWitnessRHS.trace.length}"

end T1Route

#print axioms T1Route.bpCode_hlen
#print axioms T1Route.bpCode_hcount
