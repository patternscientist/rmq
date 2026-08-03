import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-! Adversarial re-check, small sizes only.  `#eval` only. -/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal

namespace AudProbeS

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

def seg0Words (s : CartesianShape) : Nat :=
  (GenericSelect.sparseExceptionSelectData s.bpCode false).bitWords.store.words.size

def report (s : CartesianShape) (tag : String) (l r : Nat) : String :=
  let f := failedOf s l r
  s!"{tag} size={s.size} bpLen={s.bpCode.length} seg0Words={seg0Words s} q=({l},{r}) val={valOf s l r} nFailed={f.length} FAILED={f}"

#eval report (leftSpine 1) "spine" 0 1
#eval report (leftSpine 8) "spine" 0 8
#eval report (leftSpine 9) "spine" 0 9
#eval report (leftSpine 21) "spine" 0 21
#eval report (leftSpine 21) "spine" 0 1
#eval report (leftSpine 21) "spine" 5 6
#eval report (leftSpine 21) "spine" 3 17
#eval report (leftSpine 21) "spine" 20 21
#eval report (balanced 21) "bal" 0 21
#eval report (balanced 21) "bal" 3 17
#eval report (balanced 36) "bal" 0 36
#eval report (leftSpine 0) "spine" 0 0
#eval report (leftSpine 0) "spine" 0 1

end AudProbeS
