import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM
import Lean

/-!
F03 content-dependent constant set, rebuilt.

Three separate jobs, in order:

A. SOUNDNESS PRECONDITION.  Enumerate every core constant that mentions any
   `CartesianShape` eliminator (`rec`, `recOn`, `casesOn`, `brecOn`, `below`,
   `binductionOn`, `noConfusion`, and the raw constructors).  If the only such
   constants are `bpCode`, `size` and their own compiler auxiliaries, then no
   other core constant can inspect a shape except by calling `bpCode` or
   `size`, which is what makes the taint below an over-approximation.

B. TAINT.  Least fixpoint of
       tainted(X) <=> `bpCode` occurs in value(X) not directly under
                      `List.length`
                  \/ exists Y in refs(value(X)), Y notin {bpCode, size},
                     tainted(Y)
   over the value-only closure of the store-parametric root.  Theorems
   contribute no edges.

C. PATHS.  Shortest value-graph path root ~> X for every tainted X, so the
   classification of X can be read off the call site rather than asserted.
-/

open Lean

namespace DPWTaintA

def root : Name :=
  `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore

def bpCodeN : Name := `RMQ.Cartesian.CartesianShape.bpCode
def sizeN   : Name := `RMQ.Cartesian.CartesianShape.size
def lengthN : Name := `List.length
def shapeN  : Name := `RMQ.Cartesian.CartesianShape

/-- Eliminator-ish constants of the shape type: anything that can take a
    `CartesianShape` apart. -/
def elimNames : List Name :=
  [ `RMQ.Cartesian.CartesianShape.rec
  , `RMQ.Cartesian.CartesianShape.recOn
  , `RMQ.Cartesian.CartesianShape.casesOn
  , `RMQ.Cartesian.CartesianShape.brecOn
  , `RMQ.Cartesian.CartesianShape.below
  , `RMQ.Cartesian.CartesianShape.binductionOn
  , `RMQ.Cartesian.CartesianShape.noConfusion
  , `RMQ.Cartesian.CartesianShape.noConfusionType
  , `RMQ.Cartesian.CartesianShape.decEq
  ]

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

/-- Value-graph out-edges.  Theorems have none: a proof term cannot influence
    an executed value. -/
def refsOf (env : Environment) (n : Name) : Array Name :=
  if isThm env n then #[] else (valOf env n).map (allConsts · #[]) |>.getD #[]

partial def closureAux (env : Environment) (seen : Std.HashSet Name)
    (out : Array Name) : List Name -> Std.HashSet Name × Array Name
  | [] => (seen, out)
  | n :: rest =>
      if seen.contains n then closureAux env seen out rest
      else closureAux env (seen.insert n) (out.push n) ((refsOf env n).toList ++ rest)

/-- (total `bpCode` occurrences, occurrences directly under `List.length`). -/
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

/-- Breadth-first parent map over the value graph, restricted to the closure. -/
partial def bfs (env : Environment) (frontier : List Name)
    (parent : Std.HashMap Name Name) : Std.HashMap Name Name :=
  match frontier with
  | [] => parent
  | _ =>
    let (parent, next) := frontier.foldl (fun (acc : Std.HashMap Name Name × List Name) n =>
      (refsOf env n).foldl (fun (acc : Std.HashMap Name Name × List Name) y =>
        if acc.1.contains y || y == root then acc
        else (acc.1.insert y n, y :: acc.2)) acc) (parent, [])
    if next.isEmpty then parent else bfs env next parent

partial def pathTo (parent : Std.HashMap Name Name) (n : Name) (fuel : Nat) : List Name :=
  match fuel with
  | 0 => [n]
  | fuel + 1 =>
    match parent[n]? with
    | none => [n]
    | some p => pathTo parent p fuel ++ [n]

def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx =>
      match env.header.moduleNames[idx.toNat]? with
      | some m => m
      | none => .anonymous
  | none => .anonymous

def typeStr (env : Environment) (n : Name) : String :=
  match env.find? n with
  | none => "?"
  | some ci => toString ci.type

def outPath : String :=
  "C:/Users/poin/AppData/Local/Temp/claude/C--Users-poin-Documents-RMQ--claude-worktrees-recursing-cerf-300c92/09e21f10-b494-4393-9fb6-2f4ad4dedb1c/scratchpad/dpw_taint_a_out.txt"

run_cmd do
  let env <- Lean.getEnv
  let cl := (closureAux env {} #[] [root]).2
  let clSet : Std.HashSet Name := cl.foldl (fun s n => s.insert n) {}
  let mut lines : Array String := #[]
  lines := lines.push s!"ROOT {root}"
  lines := lines.push s!"VALUE_ONLY_CLOSURE {cl.size}"
  lines := lines.push ""
  -- A. eliminator audit
  lines := lines.push "== A. SHAPE-ELIMINATOR AUDIT =="
  lines := lines.push "   core constants whose VALUE mentions a CartesianShape eliminator"
  let elimSet : Std.HashSet Name := elimNames.foldl (fun s n => s.insert n) {}
  let mut elimUsers : Array (Name × List Name) := #[]
  for n in cl do
    if isThm env n then continue
    let rs := (refsOf env n).toList.filter (fun y => elimSet.contains y)
    if !rs.isEmpty then elimUsers := elimUsers.push (n, rs.eraseDups)
  lines := lines.push s!"   ELIM_USER_COUNT {elimUsers.size}"
  for (n, rs) in elimUsers do
    lines := lines.push s!"   ELIMUSER {n} -> {rs}"
  -- also: which core constants mention the raw constructors
  lines := lines.push ""
  lines := lines.push "   core constants whose VALUE mentions CartesianShape constructors"
  let ctorSet : Std.HashSet Name :=
    ({} : Std.HashSet Name).insert `RMQ.Cartesian.CartesianShape.empty
      |>.insert `RMQ.Cartesian.CartesianShape.node
  let mut ctorUsers : Array Name := #[]
  for n in cl do
    if isThm env n then continue
    if (refsOf env n).any (fun y => ctorSet.contains y) then ctorUsers := ctorUsers.push n
  lines := lines.push s!"   CTOR_USER_COUNT {ctorUsers.size}"
  for n in ctorUsers do
    lines := lines.push s!"   CTORUSER {n}"
  -- B. taint
  let mut seed : Std.HashSet Name := {}
  let mut seedList : Array Name := #[]
  let mut lengthOnly : Array Name := #[]
  for n in cl do
    if isThm env n then continue
    if n == bpCodeN || n == sizeN then continue
    match valOf env n with
    | none => continue
    | some v =>
      let (tot, under) := countUnderLength v
      if tot > 0 then
        if tot == under then lengthOnly := lengthOnly.push n
        else
          seed := seed.insert n
          seedList := seedList.push n
  let tainted := saturate env cl seed 200
  lines := lines.push ""
  lines := lines.push "== B. TAINT =="
  lines := lines.push s!"   SEED_COUNT {seed.size}"
  for n in seedList do lines := lines.push s!"   SEED {n}"
  lines := lines.push s!"   BPCODE_LENGTH_ONLY_SYNTACTIC {lengthOnly.size}"
  lines := lines.push s!"   TAINTED_TOTAL {tainted.size}"
  -- C. paths + full listing
  let parent := bfs env [root] {}
  lines := lines.push ""
  lines := lines.push "== C. TAINTED CONSTANTS, full list with type and shortest path from root =="
  let mut idx : Nat := 0
  let mut sorted : Array Name := #[]
  for n in cl do
    if tainted.contains n then sorted := sorted.push n
  for n in sorted do
    idx := idx + 1
    let wit := (refsOf env n).toList.filter (fun y =>
      y != bpCodeN && y != sizeN && tainted.contains y) |>.eraseDups
    let selfSeed := seed.contains n
    let p := pathTo parent n 100
    lines := lines.push s!"[{idx}] {n}"
    lines := lines.push s!"    seed={selfSeed} mod={moduleOf env n}"
    lines := lines.push s!"    type= {typeStr env n}"
    lines := lines.push s!"    taintedRefs= {wit.take 6}"
    lines := lines.push s!"    pathLen={p.length} path= {p}"
  lines := lines.push ""
  lines := lines.push s!"ROOT_IN_CLOSURE {clSet.contains root} ROOT_TAINTED {tainted.contains root}"
  IO.FS.writeFile outPath (String.intercalate "\n" lines.toList)
  Lean.logInfo m!"closure={cl.size} seed={seed.size} tainted={tainted.size} elimUsers={elimUsers.size} ctorUsers={ctorUsers.size}"

end DPWTaintA
