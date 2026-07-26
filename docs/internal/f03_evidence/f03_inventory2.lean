import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM
import Lean

/-!
F03 exhaustive dependency inventory, computational core.

Refinement over the first pass: follow only definitional VALUES and never
descend into theorems. A proof term cannot influence an executed address, so
the resulting closure is the true executable core of the store-parametric
controller. Within that core we ask, for each constant that mentions
`CartesianShape.bpCode`, whether every occurrence sits directly under
`List.length` -- i.e. whether the constant consumes only the SIZE of the tree
(allowed: derivable from `n`) or its CONTENTS (must come from a counted probe).
-/

open Lean

namespace F03Inv2

def root : Name :=
  `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore

def shapeTy : Name := `RMQ.Cartesian.CartesianShape
def bpCodeN : Name := `RMQ.Cartesian.CartesianShape.bpCode
def sizeN : Name := `RMQ.Cartesian.CartesianShape.size
def lengthN : Name := `List.length

def isTheorem (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some (.thmInfo _) => true
  | _ => false

/-- Computational dependencies: value only, skipping proofs. -/
def compDeps (env : Environment) (n : Name) : List Name :=
  if isTheorem env n then []
  else
    match env.find? n with
    | none => []
    | some ci =>
        match ci.value? with
        | some v => v.foldConsts [] (fun c a => c :: a)
        | none => []

partial def closureAux (env : Environment) (seen : Std.HashSet Name)
    (out : Array Name) : List Name -> Std.HashSet Name × Array Name
  | [] => (seen, out)
  | n :: rest =>
      if seen.contains n then closureAux env seen out rest
      else
        let seen := seen.insert n
        let out := out.push n
        closureAux env seen out (compDeps env n ++ rest)

/-- Count occurrences of `target`, and how many are directly under
    `List.length`. Returns (total, underLength). -/
partial def countUnderLength (target : Name) : Expr -> Nat × Nat
  | e@(.app _ _) =>
      let fn := e.getAppFn
      let args := e.getAppArgs
      match fn with
      | .const c _ =>
          if c == lengthN then
            -- List.length {α} (l : List α); check whether l is a `target` app
            let inner := args.findSome? (fun a =>
              if a.getAppFn.isConstOf target then some a else none)
            match inner with
            | some innerArg =>
                -- count target inside innerArg's own arguments too
                let sub := innerArg.getAppArgs.foldl
                  (fun (acc : Nat × Nat) a =>
                    let r := countUnderLength target a
                    (acc.1 + r.1, acc.2 + r.2)) (0, 0)
                let others := args.foldl (fun (acc : Nat × Nat) a =>
                  if a == innerArg then acc
                  else
                    let r := countUnderLength target a
                    (acc.1 + r.1, acc.2 + r.2)) (0, 0)
                (sub.1 + others.1 + 1, sub.2 + others.2 + 1)
            | none =>
                args.foldl (fun (acc : Nat × Nat) a =>
                  let r := countUnderLength target a
                  (acc.1 + r.1, acc.2 + r.2)) (0, 0)
          else
            let here := if c == target then 1 else 0
            args.foldl (fun (acc : Nat × Nat) a =>
              let r := countUnderLength target a
              (acc.1 + r.1, acc.2 + r.2)) (here, 0)
      | _ =>
          let r0 := countUnderLength target fn
          args.foldl (fun (acc : Nat × Nat) a =>
            let r := countUnderLength target a
            (acc.1 + r.1, acc.2 + r.2)) r0
  | .lam _ t b _ =>
      let a := countUnderLength target t
      let b' := countUnderLength target b
      (a.1 + b'.1, a.2 + b'.2)
  | .forallE _ t b _ =>
      let a := countUnderLength target t
      let b' := countUnderLength target b
      (a.1 + b'.1, a.2 + b'.2)
  | .letE _ t v b _ =>
      let a := countUnderLength target t
      let b' := countUnderLength target v
      let c := countUnderLength target b
      (a.1 + b'.1 + c.1, a.2 + b'.2 + c.2)
  | .mdata _ e => countUnderLength target e
  | .proj _ _ e => countUnderLength target e
  | .const c _ => (if c == target then 1 else 0, 0)
  | _ => (0, 0)

def resultHead (env : Environment) (n : Name) : Name :=
  match env.find? n with
  | none => .anonymous
  | some ci =>
      let rec peel : Expr -> Expr
        | .forallE _ _ b _ => peel b
        | e => e
      match (peel ci.type).getAppFn with
      | .const c _ => c
      | _ => .anonymous

def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx =>
      match env.header.moduleNames[idx.toNat]? with
      | some m => m
      | none => .anonymous
  | none => .anonymous

run_cmd do
  let env <- Lean.getEnv
  let cl := (closureAux env {} #[] [root]).2
  let mut lines : Array String := #[]
  lines := lines.push s!"ROOT {root}"
  lines := lines.push s!"COMPUTATIONAL_CLOSURE_TOTAL {cl.size}"
  let mut contentUsers : Array (Name × Nat × Nat) := #[]
  let mut lengthOnly : Array (Name × Nat) := #[]
  let mut sizeUsers : Array Name := #[]
  for n in cl do
    if isTheorem env n then continue
    match env.find? n with
    | none => continue
    | some ci =>
      match ci.value? with
      | none => continue
      | some v =>
        let (tot, under) := countUnderLength bpCodeN v
        if tot > 0 then
          if tot == under then lengthOnly := lengthOnly.push (n, tot)
          else contentUsers := contentUsers.push (n, tot, under)
        let (st, _) := countUnderLength sizeN v
        if st > 0 then sizeUsers := sizeUsers.push n
  lines := lines.push s!"BPCODE_LENGTH_ONLY_COUNT {lengthOnly.size}"
  lines := lines.push s!"BPCODE_CONTENT_COUNT {contentUsers.size}"
  lines := lines.push s!"SIZE_USER_COUNT {sizeUsers.size}"
  lines := lines.push ""
  lines := lines.push "== BPCODE CONTENT USERS (bpCode occurrence NOT under List.length) =="
  lines := lines.push "   these are the F03 candidates: they may read tree CONTENTS"
  for (n, tot, under) in contentUsers do
    lines := lines.push
      s!"  CONTENT {n} :: ret={resultHead env n} occ={tot} underLen={under} mod={moduleOf env n}"
  lines := lines.push ""
  lines := lines.push "== BPCODE LENGTH-ONLY USERS (every occurrence under List.length) =="
  lines := lines.push "   these consume only 2n and are derivable from n"
  for (n, tot) in lengthOnly do
    lines := lines.push s!"  LENGTHONLY {n} :: ret={resultHead env n} occ={tot} mod={moduleOf env n}"
  lines := lines.push ""
  lines := lines.push "== CartesianShape.size USERS =="
  for n in sizeUsers do
    lines := lines.push s!"  SIZE {n} :: ret={resultHead env n} mod={moduleOf env n}"
  IO.FS.writeFile
    "C:/Users/poin/AppData/Local/Temp/claude/C--Users-poin-Documents-RMQ--claude-worktrees-recursing-cerf-300c92/09e21f10-b494-4393-9fb6-2f4ad4dedb1c/scratchpad/f03_inventory2_out.txt"
    (String.intercalate "\n" lines.toList)
  Lean.logInfo
    m!"compClosure={cl.size} contentUsers={contentUsers.size} lengthOnly={lengthOnly.size} sizeUsers={sizeUsers.size}"

end F03Inv2
