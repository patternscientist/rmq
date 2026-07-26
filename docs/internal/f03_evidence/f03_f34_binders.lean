import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM
import Lean

/-!
Does the overhead index actually reach the executed computation?

For each listed constant we peel every lambda of its VALUE and report, per
binder, whether that binder occurs in the remaining body at all. A binder that
does not occur in the body cannot influence any address, branch, or divisor.
-/

open Lean

namespace F34Binders

/-- peel all lambdas, return (binder names outermost-first, body) -/
partial def peel (e : Expr) (acc : Array Name) : Array Name × Expr :=
  match e with
  | .lam n _ b _ => peel b (acc.push n)
  | .mdata _ e => peel e acc
  | e => (acc, e)

def report (n : Name) : MetaM Unit := do
  let env <- getEnv
  match env.find? n with
  | none => IO.println s!"MISSING {n}"
  | some ci =>
      match ci.value? with
      | none => IO.println s!"NO VALUE {n}"
      | some v =>
          let (names, body) := peel v #[]
          IO.println s!"== {n}  ({names.size} lambda binders)"
          for i in [0:names.size] do
            -- outermost binder i has de Bruijn index (names.size - 1 - i) in body
            let idx := names.size - 1 - i
            let occurs := body.hasLooseBVar idx
            IO.println s!"   binder #{i} {names[i]!} : occursInBody = {occurs}"

def targets : List Name :=
  [ `RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.bpChunkedRankTraceResultWithStore,
    `RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.superIndex,
    `RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordIndex,
    `RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordOffset,
    `RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.queryPos ]

def run : MetaM Unit := do
  for t in targets do
    report t

end F34Binders

open Lean Elab Meta in
run_cmd Command.liftTermElabM F34Binders.run
