import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-! Adversarial re-check of the lane's canonical-store probe.  `#eval` only. -/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal

namespace AudProbe

def leftSpine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | n + 1 => CartesianShape.node (leftSpine n) CartesianShape.empty

def balanced : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | n + 1 =>
      CartesianShape.node (balanced ((n + 1) / 2)) (balanced (n - (n + 1) / 2))
decreasing_by all_goals omega

def failedOf (s : CartesianShape) (l r : Nat) : List (Nat × Nat) :=
  let st := concreteBPNativeSuccinctRMQGlobalReadStore s
  (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore s st l r).trace.filterMap
    (fun e => match e with
      | WordRAM.TraceEvent.readWord seg idx none => some (seg, idx) | _ => none)

def valOf (s : CartesianShape) (l r : Nat) : Option Nat :=
  let st := concreteBPNativeSuccinctRMQGlobalReadStore s
  (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore s st l r).value

/-- Number of words actually present in segment 0 of the canonical store. -/
def seg0Words (s : CartesianShape) : Nat :=
  (GenericSelect.sparseExceptionSelectData s.bpCode false).bitWords.store.words.size

def report (s : CartesianShape) (tag : String) (l r : Nat) : String :=
  let f := failedOf s l r
  s!"{tag} size={s.size} bpLen={s.bpCode.length} seg0Words={seg0Words s} q=({l},{r}) val={valOf s l r} nFailed={f.length} FAILED={f}"

/-! ### 1. The lane's exact small-`n` claims, with the indices printed. -/
#eval report (leftSpine 1) "spine" 0 1
#eval report (leftSpine 8) "spine" 0 8
#eval report (leftSpine 9) "spine" 0 9

/-! ### 2. Are failed reads an artifact of the endpoint `r = n`?  Try
strictly-interior valid ranges (`ValidRange` is half-open: 0 < r <= n). -/
#eval report (leftSpine 21) "spine" 0 21
#eval report (leftSpine 21) "spine" 0 1
#eval report (leftSpine 21) "spine" 5 6
#eval report (leftSpine 21) "spine" 3 17
#eval report (leftSpine 21) "spine" 20 21

/-! ### 3. Are failed reads an artifact of the left-spine shape? -/
#eval report (balanced 21) "bal" 0 21
#eval report (balanced 21) "bal" 3 17
#eval report (balanced 36) "bal" 0 36
#eval report (balanced 64) "bal" 0 64
#eval report (balanced 100) "bal" 7 93

/-! ### 4. How far up does it persist?  (the lane checked only to n = 36) -/
#eval ([50, 64, 100, 128, 200, 256, 300, 511, 512, 513].map
  (fun n => (n, (failedOf (balanced n) 0 n).length,
    (failedOf (balanced n) 0 n).map Prod.fst)))

/-! ### 5. Are ALL failed reads in segment 0, and is the index always past the
end of segment 0? -/
#eval ([21, 36, 64, 128, 256, 512].map
  (fun n =>
    let s := balanced n
    (n, seg0Words s, (failedOf s 0 n))))

/-! ### 6. Is the returned value still the reference answer?
`RMQ.rmqSpec`-style check via the host list of a left spine is not available
here, so compare the shape-based answer against the size-only monotone
expectation only as a smoke test. -/
#eval ([1,2,3,4,5,8,16,21,36,64].map (fun n => (n, valOf (leftSpine n) 0 n, valOf (balanced n) 0 n)))

/-! ### 7. `n = 0`: there is no valid query at all (0 < r <= 0 is unsatisfiable). -/
#eval report (leftSpine 0) "spine" 0 0
#eval report (leftSpine 0) "spine" 0 1

end AudProbe
