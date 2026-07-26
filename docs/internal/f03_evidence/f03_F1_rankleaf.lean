import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM
import Lean

/-!
F03 / F1 classification probe:
  RMQ.SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
-/

open Lean

namespace F03F1

def f1 : Name :=
  `RMQ.SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
def bpCodeN : Name := `RMQ.Cartesian.CartesianShape.bpCode

/-- Walk the value and report, for each `bpCode` occurrence, the chain of
enclosing application heads plus the argument slot it sits in, and whether the
slot is implicit / instImplicit / strictImplicit in the head's own type. -/
partial def locate (env : Environment) (path : List String) :
    Expr -> Array String
  | e@(.app _ _) =>
      let fn := e.getAppFn
      let args := e.getAppArgs
      let headStr :=
        match fn with
        | .const c _ => c.toString
        | _ => "?fn"
      let hereHead : Array String :=
        if fn.isConstOf bpCodeN then
          #[s!"OCCURRENCE(applied) at path: {String.intercalate " > " path.reverse}"]
        else #[]
      let bnders : Array (String) :=
        match fn with
        | .const c _ =>
            match env.find? c with
            | some ci =>
                let rec peel : Expr -> Nat -> Array String -> Array String
                  | .forallE nm _ b bi, k, acc =>
                      peel b (k+1) (acc.push s!"{k}:{nm}:{repr bi}")
                  | _, _, acc => acc
                peel ci.type 0 #[]
            | none => #[]
        | _ => #[]
      let sub := args.mapIdx (fun i a =>
        let slot :=
          match bnders[i]? with
          | some s => s
          | none => s!"{i}:?:?"
        locate env (s!"{headStr}#arg[{slot}]" :: path) a)
      let subFn :=
        match fn with
        | .const _ _ => #[]
        | _ => locate env (s!"?head" :: path) fn
      hereHead ++ subFn ++ sub.foldl (fun a b => a ++ b) #[]
  | .lam n t b _ =>
      locate env (s!"lam({n}).type" :: path) t ++ locate env (s!"lam({n}).body" :: path) b
  | .forallE n t b _ =>
      locate env (s!"pi({n}).type" :: path) t ++ locate env (s!"pi({n}).body" :: path) b
  | .letE n t v b _ =>
      locate env (s!"let({n}).type" :: path) t ++ locate env (s!"let({n}).val" :: path) v
        ++ locate env (s!"let({n}).body" :: path) b
  | .mdata _ e => locate env path e
  | .proj s i e => locate env (s!"proj({s},{i})" :: path) e
  | .const c _ =>
      if c == bpCodeN then
        #[s!"OCCURRENCE(bare) at path: {String.intercalate " > " path.reverse}"]
      else #[]
  | _ => #[]

run_cmd do
  let env <- Lean.getEnv
  match env.find? f1 with
  | none => Lean.logInfo m!"NOT FOUND"
  | some ci =>
    match ci.value? with
    | none => Lean.logInfo m!"NO VALUE"
    | some v =>
      let hits := locate env [] v
      let mut s := s!"F1 = {f1}\nbpCode occurrences in VALUE: {hits.size}\n"
      for h in hits do
        s := s ++ "  " ++ h ++ "\n"
      -- also the type
      let thits := locate env [] ci.type
      s := s ++ s!"bpCode occurrences in TYPE: {thits.size}\n"
      for h in thits do
        s := s ++ "  " ++ h ++ "\n"
      IO.FS.writeFile
        "C:/Users/poin/AppData/Local/Temp/claude/C--Users-poin-Documents-RMQ--claude-worktrees-recursing-cerf-300c92/09e21f10-b494-4393-9fb6-2f4ad4dedb1c/scratchpad/f03_F1_out.txt" s
      Lean.logInfo m!"{s}"

set_option pp.explicit true in
#print RMQ.SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore

end F03F1
