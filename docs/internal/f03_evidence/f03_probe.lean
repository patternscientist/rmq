import RMQ.Core.SuccinctFinalStoreParam
import Lean

open Lean

/-! Smoke test: can we reach the environment and find the target constant? -/

run_cmd do
  let env <- Lean.getEnv
  let target :=
    `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
  match env.find? target with
  | none => Lean.logInfo m!"MISSING {target}"
  | some ci => Lean.logInfo m!"FOUND {target} :: hasValue={ci.value?.isSome}"
