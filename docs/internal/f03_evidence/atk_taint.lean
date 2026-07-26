import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM
import Lean

/-!
Taint analysis replacing the coordinator's syntactic-occurrence classifier.

The coordinator asked, per constant, "does every syntactic `bpCode` occurrence
in MY value sit under `List.length`?" and called the yes-answers size-only.
That is unsound: content arrives by CALLING a content-dependent constant.

Here: least fixpoint of
    tainted(X)  <=>  bpCode occurs in X not under List.length
                 \/  exists Y in refs(X), tainted(Y), Y not in {bpCode, size}
with `List.length (bpCode s)` and `size s` as taint STOPPERS (both provably
factor through n via `bpCode_length`).
-/

open Lean

namespace AtkT

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

/-- (total bpCode occurrences, occurrences directly under `List.length`). -/
partial def countUnderLength : Expr -> Nat × Nat
  | e@(.app _ _) =>
      let fn := e.getAppFn
      let args := e.getAppArgs
      match fn with
      | .const c _ =>
          if c == lengthN then
            match args.findSome? (fun a => if a.getAppFn.isConstOf bpCodeN then some a else none) with
            | some inner =>
                let sub := inner.getAppArgs.foldl
                  (fun (acc : Nat × Nat) a => let r := countUnderLength a; (acc.1+r.1, acc.2+r.2)) (0,0)
                let others := args.foldl
                  (fun (acc : Nat × Nat) a =>
                    if a == inner then acc else let r := countUnderLength a; (acc.1+r.1, acc.2+r.2)) (0,0)
                (sub.1 + others.1 + 1, sub.2 + others.2 + 1)
            | none =>
                args.foldl (fun (acc : Nat × Nat) a => let r := countUnderLength a; (acc.1+r.1, acc.2+r.2)) (0,0)
          else
            let here := if c == bpCodeN then 1 else 0
            args.foldl (fun (acc : Nat × Nat) a => let r := countUnderLength a; (acc.1+r.1, acc.2+r.2)) (here, 0)
      | _ =>
          let r0 := countUnderLength fn
          args.foldl (fun (acc : Nat × Nat) a => let r := countUnderLength a; (acc.1+r.1, acc.2+r.2)) r0
  | .lam _ t b _     => let a := countUnderLength t; let c := countUnderLength b; (a.1+c.1, a.2+c.2)
  | .forallE _ t b _ => let a := countUnderLength t; let c := countUnderLength b; (a.1+c.1, a.2+c.2)
  | .letE _ t v b _  =>
      let a := countUnderLength t; let c := countUnderLength v; let d := countUnderLength b
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

/-- Iterate the taint rule to a fixpoint over the closure. -/
partial def saturate (env : Environment) (cl : Array Name)
    (tainted : Std.HashSet Name) (fuel : Nat) : Std.HashSet Name :=
  match fuel with
  | 0 => tainted
  | fuel + 1 =>
    let (t', changed) := cl.foldl (fun (acc : Std.HashSet Name × Bool) n =>
      if acc.1.contains n then acc
      else
        let hit := (refsOf env n).any (fun y =>
          y != bpCodeN && y != sizeN && acc.1.contains y)
        if hit then (acc.1.insert n, true) else acc) (tainted, false)
    if changed then saturate env cl t' fuel else t'

run_cmd do
  let env <- Lean.getEnv
  let root := `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
  let cl := (closureAux env {} #[] [root]).2
  -- seed: constants whose OWN value reads bpCode content (not under List.length)
  let mut seed : Std.HashSet Name := {}
  let mut lengthOnly : Array Name := #[]
  for n in cl do
    if isThm env n then continue
    match valOf env n with
    | none => continue
    | some v =>
      if n == bpCodeN || n == sizeN then continue
      let (tot, under) := countUnderLength v
      if tot > 0 then
        if tot == under then lengthOnly := lengthOnly.push n
        else seed := seed.insert n
  let tainted := saturate env cl seed 60
  let mut lines : Array String := #[]
  lines := lines.push s!"CLOSURE {cl.size}"
  lines := lines.push s!"SEED (own value reads bpCode content) {seed.size}"
  lines := lines.push s!"TAINTED_TOTAL (transitively content-dependent) {tainted.size}"
  lines := lines.push s!"COORDINATOR_LENGTHONLY_BUCKET {lengthOnly.size}"
  lines := lines.push ""
  lines := lines.push "== VERDICT on each member of the coordinator's LENGTHONLY bucket =="
  lines := lines.push "   (coordinator: 'these consume only 2n and are derivable from n')"
  let mut mis : Nat := 0
  for n in lengthOnly do
    if tainted.contains n then
      mis := mis + 1
      let wit := (refsOf env n).filter (fun y => y != bpCodeN && y != sizeN && tainted.contains y)
      let wit := wit.toList.eraseDups.take 4
      lines := lines.push s!"  MISCLASSIFIED-CONTENT {n}"
      lines := lines.push s!"      taint witnesses: {wit}"
    else
      lines := lines.push s!"  genuinely-size-only    {n}"
  lines := lines.push ""
  lines := lines.push s!"MISCLASSIFIED_COUNT {mis} of {lengthOnly.size}"
  lines := lines.push ""
  lines := lines.push "== ALSO: is the ROOT itself tainted? =="
  lines := lines.push s!"   root tainted = {tainted.contains root}"
  IO.FS.writeFile
    "C:/Users/poin/AppData/Local/Temp/claude/C--Users-poin-Documents-RMQ--claude-worktrees-recursing-cerf-300c92/09e21f10-b494-4393-9fb6-2f4ad4dedb1c/scratchpad/atk_taint_out.txt"
    (String.intercalate "\n" lines.toList)
  Lean.logInfo m!"seed={seed.size} tainted={tainted.size} lengthOnly={lengthOnly.size} misclassified={mis}"

end AtkT
