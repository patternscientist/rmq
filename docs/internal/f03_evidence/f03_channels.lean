import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM
import Lean

/-!
F03 completeness linchpin.

`CartesianShape` is an inductive type, so the ONLY way executable code can
observe its contents is through its recursor / `casesOn` / a match auxiliary /
a structure projection. If, inside the computational closure of the
store-parametric controller, every such eliminator occurrence lies inside
`CartesianShape.bpCode` or `CartesianShape.size`, then those two functions are
the complete content channel, and the F03 inventory over `bpCode` is exhaustive
rather than representative.

This file enumerates every constant in the computational closure that
references ANY `CartesianShape` eliminator, so the claim can be checked rather
than asserted.
-/

open Lean

namespace F03Chan

def root : Name :=
  `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore

def shapeTy : Name := `RMQ.Cartesian.CartesianShape

def isTheorem (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some (.thmInfo _) => true
  | _ => false

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

/-- Any constant whose name lives in the `CartesianShape` namespace and which
    eliminates the type, plus the constructors. -/
def isShapeEliminator (n : Name) : Bool :=
  let s := n.toString
  (s.startsWith "RMQ.Cartesian.CartesianShape." &&
    (s.endsWith ".rec" || s.endsWith ".recOn" || s.endsWith ".casesOn" ||
     s.endsWith ".brecOn" || s.endsWith ".below" || s.endsWith ".binductionOn" ||
     s.endsWith ".ndrec" || s.endsWith ".ndrecOn")) ||
  n == `RMQ.Cartesian.CartesianShape.node ||
  n == `RMQ.Cartesian.CartesianShape.empty

/-- A match auxiliary generated for a pattern match on shapes. -/
def isShapeMatcher (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | none => false
  | some ci =>
      let s := n.toString
      let hasMatch := (s.splitOn "match_").length > 1
      let hasEqDef := (s.splitOn "eq_def").length > 1
      (hasMatch || hasEqDef) &&
        ci.type.foldConsts false (fun c a => a || c == shapeTy)

run_cmd do
  let env <- Lean.getEnv
  let cl := (closureAux env {} #[] [root]).2
  let mut lines : Array String := #[]
  lines := lines.push s!"COMPUTATIONAL_CLOSURE {cl.size}"
  lines := lines.push ""
  lines := lines.push "== constants in the closure that ARE shape eliminators/constructors =="
  for n in cl do
    if isShapeEliminator n then
      lines := lines.push s!"  ELIM_PRESENT {n}"
    if isShapeMatcher env n then
      lines := lines.push s!"  MATCHER_PRESENT {n}"
  lines := lines.push ""
  lines := lines.push "== constants whose VALUE references a shape eliminator/matcher/constructor =="
  lines := lines.push "   (excluding bpCode and size themselves)"
  let mut users : Nat := 0
  for n in cl do
    if isTheorem env n then continue
    if n == `RMQ.Cartesian.CartesianShape.bpCode then continue
    if n == `RMQ.Cartesian.CartesianShape.size then continue
    match env.find? n with
    | none => continue
    | some ci =>
      match ci.value? with
      | none => continue
      | some v =>
        let hits := v.foldConsts ([] : List Name) (fun c a =>
          if isShapeEliminator c || isShapeMatcher env c then c :: a else a)
        if !hits.isEmpty then
          users := users + 1
          lines := lines.push s!"  USER {n} -> {hits}"
  lines := lines.push ""
  lines := lines.push s!"ELIMINATOR_USERS_OUTSIDE_BPCODE_AND_SIZE {users}"
  IO.FS.writeFile
    "C:/Users/poin/AppData/Local/Temp/claude/C--Users-poin-Documents-RMQ--claude-worktrees-recursing-cerf-300c92/09e21f10-b494-4393-9fb6-2f4ad4dedb1c/scratchpad/f03_channels_out.txt"
    (String.intercalate "\n" lines.toList)
  Lean.logInfo m!"closure={cl.size} eliminatorUsersOutsideBpCodeAndSize={users}"

end F03Chan
