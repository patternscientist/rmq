import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM
import Lean

/-!
BLIND-SPOT AUDIT of the coordinator's `countUnderLength` instrument.

Sound criterion, independent of `bpCode`: a `CartesianShape` is an inductive
type, so the ONLY way any term can observe its CONTENTS is to apply some
constant in the `RMQ.Cartesian.CartesianShape` namespace (rec / recOn /
casesOn / brecOn / below / decEq / a field-like observer) or to be an
auxiliary matcher which itself does so. Matchers compile to `.casesOn`, so
scanning every core constant for references to ANY `CartesianShape.*`
constant is a complete over-approximation of the content frontier.
-/

open Lean

namespace ZZBlind

def root : Name :=
  `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore

def shapeNS : Name := `RMQ.Cartesian.CartesianShape
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

/-- All constants referenced by `v` that live in the CartesianShape namespace. -/
def shapeConstsIn (v : Expr) : Array Name :=
  let all := v.foldConsts ([] : List Name) (fun c a => c :: a)
  (all.filter (fun c => shapeNS.isPrefixOf c)).toArray

/-- Does this expression mention CartesianShape as a type anywhere? -/
def mentionsShapeTy (e : Expr) : Bool :=
  (e.foldConsts false (fun c a => a || c == shapeTy))

/-- Does the constant take a CartesianShape argument (anywhere in its telescope)? -/
def takesShape (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | none => false
  | some ci =>
      let rec go : Expr -> Bool
        | .forallE _ t b _ => (mentionsShapeTy t) || go b
        | _ => false
      go ci.type

def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx =>
      match env.header.moduleNames[idx.toNat]? with
      | some m => m
      | none => .anonymous
  | none => .anonymous

def kindOf (env : Environment) (n : Name) : String :=
  match env.find? n with
  | some (.defnInfo _) => "def"
  | some (.thmInfo _) => "thm"
  | some (.axiomInfo _) => "axiom"
  | some (.opaqueInfo _) => "opaque"
  | some (.ctorInfo _) => "ctor"
  | some (.recInfo _) => "rec"
  | some (.inductInfo _) => "induct"
  | some (.quotInfo _) => "quot"
  | none => "MISSING"

run_cmd do
  let env <- Lean.getEnv
  let cl := (closureAux env {} #[] [root]).2
  let mut lines : Array String := #[]
  lines := lines.push s!"ROOT {root}"
  lines := lines.push s!"COMPUTATIONAL_CLOSURE_TOTAL {cl.size}"

  -- 1. Every constant in the CartesianShape namespace anywhere in the env,
  --    with a mark for whether it is in the computational core.
  let mut nsAll : Array Name := #[]
  for (n, _) in env.constants.toList do
    if shapeNS.isPrefixOf n then nsAll := nsAll.push n
  let clSet : Std.HashSet Name := cl.foldl (fun s n => s.insert n) {}
  lines := lines.push ""
  lines := lines.push s!"== ALL CartesianShape.* CONSTANTS IN ENV ({nsAll.size}) =="
  for n in nsAll.qsort (fun a b => a.toString < b.toString) do
    let mark := if clSet.contains n then "IN_CORE " else "        "
    lines := lines.push s!"  {mark}{kindOf env n} {n}"

  -- 2. Every core constant that references ANY CartesianShape.* constant.
  lines := lines.push ""
  lines := lines.push "== CORE CONSTANTS REFERENCING ANY CartesianShape.* CONSTANT =="
  let mut refCount := 0
  for n in cl do
    if isTheorem env n then continue
    match env.find? n with
    | none => continue
    | some ci =>
      match ci.value? with
      | none => continue
      | some v =>
        let sc := shapeConstsIn v
        if sc.size > 0 then
          refCount := refCount + 1
          -- dedup
          let mut uniq : Array Name := #[]
          for c in sc do
            if !uniq.contains c then uniq := uniq.push c
          let names := String.intercalate "," (uniq.toList.map (fun c => c.toString))
          lines := lines.push s!"  USES {n} :: [{names}] mod={moduleOf env n}"
  lines := lines.push s!"REFERENCING_CORE_CONSTANT_COUNT {refCount}"

  -- 3. Core constants that TAKE a CartesianShape argument but reference NO
  --    CartesianShape.* constant: pass-through only, cannot observe contents.
  let mut passThrough := 0
  let mut observers := 0
  for n in cl do
    if isTheorem env n then continue
    if takesShape env n then
      match (env.find? n).bind (fun ci => ci.value?) with
      | none => pure ()
      | some v =>
        if (shapeConstsIn v).size == 0 then passThrough := passThrough + 1
        else observers := observers + 1
  lines := lines.push ""
  lines := lines.push s!"SHAPE_TAKING_PASSTHROUGH {passThrough}"
  lines := lines.push s!"SHAPE_TAKING_OBSERVERS {observers}"

  -- 4. Specific probes.
  lines := lines.push ""
  lines := lines.push "== TARGETED MEMBERSHIP PROBES =="
  let probes : List Name := [
    `RMQ.SuccinctSpace.bpParensOfShape,
    `RMQ.Cartesian.CartesianShape.rootOffset?,
    `RMQ.Cartesian.CartesianShape.representative,
    `RMQ.Cartesian.CartesianShape.decEq,
    `RMQ.Cartesian.instDecidableEqCartesianShape,
    `RMQ.Cartesian.CartesianShape.rec,
    `RMQ.Cartesian.CartesianShape.casesOn,
    `RMQ.Cartesian.CartesianShape.brecOn,
    `RMQ.Cartesian.CartesianShape.below,
    `RMQ.Cartesian.CartesianShape.node,
    `RMQ.Cartesian.CartesianShape.empty,
    `RMQ.Cartesian.CartesianShape.bpCode,
    `RMQ.Cartesian.CartesianShape.size,
    `RMQ.SuccinctFinal.concreteBPNativeSelectCloseGlobalWordTraceResultWithStore,
    `RMQ.SuccinctFinal.concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore,
    `RMQ.SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
  ]
  for p in probes do
    let inCore := if clSet.contains p then "IN_CORE" else "not-in-core"
    let exists? := if (env.find? p).isSome then kindOf env p else "MISSING"
    lines := lines.push s!"  PROBE {p} :: {inCore} kind={exists?}"

  IO.FS.writeFile
    "C:/Users/poin/AppData/Local/Temp/claude/C--Users-poin-Documents-RMQ--claude-worktrees-recursing-cerf-300c92/09e21f10-b494-4393-9fb6-2f4ad4dedb1c/scratchpad/zz_blind_elim_out.txt"
    (String.intercalate "\n" lines.toList)
  Lean.logInfo m!"core={cl.size} refCount={refCount} nsAll={nsAll.size}"

end ZZBlind
