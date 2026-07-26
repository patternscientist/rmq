import RMQ.Core.SuccinctRMQClassic
import Lean

/-! Attack 4: does the public guard `withValidRange` consume `xs` beyond its length? -/

open Lean

namespace AtkG

partial def allConsts : Expr -> Array Name -> Array Name
  | .const c _,       acc => acc.push c
  | .app f a,         acc => allConsts a (allConsts f acc)
  | .lam _ t b _,     acc => allConsts b (allConsts t acc)
  | .forallE _ t b _, acc => allConsts b (allConsts t acc)
  | .letE _ t v b _,  acc => allConsts b (allConsts v (allConsts t acc))
  | .mdata _ e,       acc => allConsts e acc
  | .proj _ _ e,      acc => allConsts e acc
  | _,                acc => acc

run_cmd do
  let env <- Lean.getEnv
  for n in [`RMQ.SuccinctClassic.withValidRange, `RMQ.SuccinctClassic.queryTraceResultWithStore,
            `RMQ.ValidRange, `RMQ.SuccinctClassic.cartesianShape] do
    match env.find? n with
    | some (.defnInfo v) =>
        Lean.logInfo m!"{n}\n  TYPE  {v.type}\n  VALUE {v.value}\n  CONSTS {(allConsts v.value #[]).toList.eraseDups}"
    | _ => Lean.logInfo m!"{n} :: not a def"

end AtkG
