import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM
import Lean

/-!
The TRUE content frontier of the store-parametric controller, and how the
execution-refuted constants are reached from the root.
-/

open Lean

namespace AtkF

def bpCodeN : Name := `RMQ.Cartesian.CartesianShape.bpCode
def sizeN   : Name := `RMQ.Cartesian.CartesianShape.size
def lengthN : Name := `List.length

partial def allConsts : Expr -> Array Name -> Array Name
  | .const c _,       acc => acc.push c
  | .app f a,         acc => allConsts a (allConsts f acc)
  | .lam _ t b _,     acc => allConsts b (allConsts t acc)
  | .forallE _ t b _, acc => allConsts b (allConsts t acc)
  | .letE _ t v b _,  acc => allConsts b (allConsts v (allConsts t acc))
  | .mdata _ e,       acc => allConsts e acc
  | .proj _ _ e,      acc => allConsts e acc
  | _,                acc => acc

def isThm (env : Environment) (n : Name) : Bool :=
  match env.find? n with | some (.thmInfo _) => true | _ => false

def valOf (env : Environment) (n : Name) : Option Expr :=
  match env.find? n with
  | some (.defnInfo v)   => some v.value
  | some (.thmInfo v)    => some v.value
  | some (.opaqueInfo v) => some v.value
  | _ => none

def refsOf (env : Environment) (n : Name) : Array Name :=
  if isThm env n then #[] else (valOf env n).map (allConsts · #[]) |>.getD #[]

partial def countUnderLength : Expr -> Nat × Nat
  | e@(.app _ _) =>
      let fn := e.getAppFn; let args := e.getAppArgs
      match fn with
      | .const c _ =>
          if c == lengthN then
            match args.findSome? (fun a => if a.getAppFn.isConstOf bpCodeN then some a else none) with
            | some inner =>
                let sub := inner.getAppArgs.foldl
                  (fun (acc : Nat × Nat) a => let r := countUnderLength a; (acc.1+r.1, acc.2+r.2)) (0,0)
                let others := args.foldl (fun (acc : Nat × Nat) a =>
                  if a == inner then acc else let r := countUnderLength a; (acc.1+r.1, acc.2+r.2)) (0,0)
                (sub.1 + others.1 + 1, sub.2 + others.2 + 1)
            | none => args.foldl (fun (acc : Nat × Nat) a => let r := countUnderLength a; (acc.1+r.1, acc.2+r.2)) (0,0)
          else
            let here := if c == bpCodeN then 1 else 0
            args.foldl (fun (acc : Nat × Nat) a => let r := countUnderLength a; (acc.1+r.1, acc.2+r.2)) (here, 0)
      | _ =>
          let r0 := countUnderLength fn
          args.foldl (fun (acc : Nat × Nat) a => let r := countUnderLength a; (acc.1+r.1, acc.2+r.2)) r0
  | .lam _ t b _     => let a := countUnderLength t; let c := countUnderLength b; (a.1+c.1, a.2+c.2)
  | .forallE _ t b _ => let a := countUnderLength t; let c := countUnderLength b; (a.1+c.1, a.2+c.2)
  | .letE _ t v b _  => let a := countUnderLength t; let c := countUnderLength v; let d := countUnderLength b
                        (a.1+c.1+d.1, a.2+c.2+d.2)
  | .mdata _ e  => countUnderLength e
  | .proj _ _ e => countUnderLength e
  | .const c _  => (if c == bpCodeN then 1 else 0, 0)
  | _ => (0,0)

partial def closureAux (env : Environment) (seen : Std.HashSet Name)
    (out : Array Name) : List Name -> Std.HashSet Name × Array Name
  | [] => (seen, out)
  | n :: rest =>
      if seen.contains n then closureAux env seen out rest
      else closureAux env (seen.insert n) (out.push n) ((refsOf env n).toList ++ rest)

partial def saturate (env : Environment) (cl : Array Name)
    (tainted : Std.HashSet Name) (fuel : Nat) : Std.HashSet Name :=
  match fuel with
  | 0 => tainted
  | fuel + 1 =>
    let (t', changed) := cl.foldl (fun (acc : Std.HashSet Name × Bool) n =>
      if acc.1.contains n then acc
      else if (refsOf env n).any (fun y => y != bpCodeN && y != sizeN && acc.1.contains y)
        then (acc.1.insert n, true) else acc) (tainted, false)
    if changed then saturate env cl t' fuel else t'

partial def bfs (env : Environment) (frontier : List Name)
    (parent : Std.HashMap Name Name) : Std.HashMap Name Name :=
  match frontier with
  | [] => parent
  | _ =>
    let (nf, p') := frontier.foldl (fun (acc : List Name × Std.HashMap Name Name) n =>
      (refsOf env n).foldl (fun (a2 : List Name × Std.HashMap Name Name) c =>
        if a2.2.contains c then a2 else (c :: a2.1, a2.2.insert c n)) acc) ([], parent)
    bfs env nf p'

partial def pathTo (parent : Std.HashMap Name Name) (root n : Name)
    (fuel : Nat) (acc : List Name) : List Name :=
  match fuel with
  | 0 => n :: acc
  | f + 1 => if n == root then n :: acc
             else match parent[n]? with
               | some p => if p == n then n :: acc else pathTo parent root p f (n :: acc)
               | none => n :: acc

run_cmd do
  let env <- Lean.getEnv
  let root := `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
  let cl := (closureAux env {} #[] [root]).2
  let mut seed : Std.HashSet Name := {}
  for n in cl do
    if isThm env n || n == bpCodeN || n == sizeN then continue
    match valOf env n with
    | none => continue
    | some v => let (t,u) := countUnderLength v
                if t > 0 && t != u then seed := seed.insert n
  let tainted := saturate env cl seed 60
  let parent := bfs env [root] (Std.HashMap.emptyWithCapacity.insert root root)
  let mut lines : Array String := #[]
  lines := lines.push s!"TRUE CONTENT-DEPENDENT SET in the 917-constant executable core: {tainted.size}"
  lines := lines.push "(coordinator reported the frontier as 6)"
  lines := lines.push ""
  for n in cl do
    if tainted.contains n then lines := lines.push s!"  TAINTED {n}"
  lines := lines.push ""
  lines := lines.push "== call paths for the EXECUTION-REFUTED 'size-only' constants =="
  for t in [`RMQ.SuccinctClose.bpBlockArgMinPrefixPos,
            `RMQ.SuccinctClose.bpBlockMinExcess,
            `RMQ.SuccinctClose.bpBlockArgMinLocalOffsetEntries,
            `RMQ.SuccinctClose.canonicalRelativeRmmSummaryTable] do
    lines := lines.push ""
    lines := lines.push s!"--- {t} ---"
    let p := pathTo parent root t 300 []
    for x in p do lines := lines.push s!"    . {x}"
  IO.FS.writeFile
    "C:/Users/poin/AppData/Local/Temp/claude/C--Users-poin-Documents-RMQ--claude-worktrees-recursing-cerf-300c92/09e21f10-b494-4393-9fb6-2f4ad4dedb1c/scratchpad/atk_frontier_out.txt"
    (String.intercalate "\n" lines.toList)
  Lean.logInfo m!"tainted={tainted.size}"

end AtkF
