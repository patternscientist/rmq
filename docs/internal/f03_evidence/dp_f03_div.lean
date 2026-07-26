import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM
import Lean

/-!
DP-F03 (b) part 3: backward slice on the DIVISOR / MODULUS / log2 slots.

For every `HDiv.hDiv` / `Nat.div` / `HMod.hMod` / `Nat.mod` / `Nat.log2` site in
the executed controller core, take the deciding operand (the divisor, resp. the
log2 argument) and trace it BACKWARDS: if it is a literal, done; if it is built
from constants, name them; if it is a formal parameter of the host constant,
walk every call site of that host inside the core and repeat.

The answer per site is a set of ORIGIN TAGS.  Verdict S requires every origin to
be a literal, a size-only constant, or the root's `n`/endpoint parameters.
-/

open Lean Lean.Meta

namespace DPF03Div

def root : Name :=
  `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore

def bpCodeN : Name := `RMQ.Cartesian.CartesianShape.bpCode
def sizeN : Name := `RMQ.Cartesian.CartesianShape.size

def contentSix : List Name :=
  [`RMQ.SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore,
   `RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankData,
   `RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankBlockOverhead,
   `RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankSuperOverhead,
   `RMQ.SuccinctClose.bpExcessAt,
   `RMQ.SuccinctFinal.concreteBPNativeSelectCloseGlobalWordTraceResultWithStore]

def isTheorem (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some (.thmInfo _) => true
  | _ => false

def valueOf (env : Environment) (n : Name) : Option Expr :=
  if isTheorem env n then none
  else match env.find? n with
    | none => none
    | some ci => ci.value?

def compDeps (env : Environment) (n : Name) : List Name :=
  match valueOf env n with
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

def isDivHead (c : Name) : Option String :=
  if c == ``HDiv.hDiv || c == ``Nat.div then some "div"
  else if c == ``HMod.hMod || c == ``Nat.mod then some "mod"
  else if c == `Nat.log2 then some "log2"
  else none

/-- The operand that F03 calls the divisor. -/
def divisorArg (k : String) (args : Array Expr) : Option Expr :=
  if k == "log2" then
    if args.size > 0 then some args[0]! else none
  else if args.size > 5 then some args[5]!
  else if args.size > 1 then some args[1]! else none

/-- Arithmetic scaffolding that carries no information of its own. -/
def neutralNames : List Name :=
  [`HAdd.hAdd, `HSub.hSub, `HMul.hMul, `HDiv.hDiv, `HMod.hMod, `HPow.hPow,
   `Nat.add, `Nat.sub, `Nat.mul, `Nat.div, `Nat.mod, `Nat.pow, `Nat.succ,
   `instHAdd, `instHSub, `instHMul, `instHDiv, `instHMod, `instHPow,
   `instAddNat, `instSubNat, `instMulNat, `Nat.instAdd, `Nat.instSub,
   `Nat.instMul, `Nat.instDiv, `Nat.instMod, `Nat.instPowNat,
   `instPowNat, `Nat.instHPowNatNat, `OfNat.ofNat, `instOfNatNat,
   `Nat.instOfNatNat, `Max.max, `Min.min, `Nat.max, `Nat.min,
   `instMaxNat, `instMinNat, `Nat.instMax, `Nat.instMin, `Nat.log2,
   `instNatAdd, `instNatSub, `instNatMul, `instOfNat, `Nat.instMaxNat,
   `Nat.instMinNat]

def neutralConst (c : Name) : Bool := neutralNames.contains c

structure ArgInfo where
  caller : Name
  consts : Array Name := #[]
  paramIdxs : Array Nat := #[]
  hasLocalFVar : Bool := false
  pure : Bool := false
deriving Inhabited

/-- Classify one argument expression relative to the caller's parameter fvars. -/
def classifyArg (caller : Name) (pmap : Std.HashMap FVarId Nat) (e : Expr) : ArgInfo := Id.run do
  let mut consts : Array Name := #[]
  let mut idxs : Array Nat := #[]
  let mut localF := false
  for c in (e.foldConsts ([] : List Name) (fun c a => c :: a)) do
    if !neutralConst c then
      if !consts.contains c then consts := consts.push c
  let fvs := (Lean.collectFVars {} e).fvarIds
  for f in fvs do
    match pmap[f]? with
    | some i => if !idxs.contains i then idxs := idxs.push i
    | none => localF := true
  pure { caller := caller, consts := consts, paramIdxs := idxs,
         hasLocalFVar := localF,
         pure := consts.isEmpty && fvs.isEmpty }

partial def walk (pmap : Std.HashMap FVarId Nat) (host : Name)
    (divs : Array (String × Expr)) (calls : Array (Name × Array Expr)) :
    Expr -> MetaM (Array (String × Expr) × Array (Name × Array Expr))
  | e@(.app _ _) => do
      let fn := e.getAppFn
      let args := e.getAppArgs
      let mut divs := divs
      let mut calls := calls
      match fn with
      | .const c _ =>
          calls := calls.push (c, args)
          match isDivHead c with
          | some k =>
              match divisorArg k args with
              | some d => divs := divs.push (k, d)
              | none => pure ()
          | none => pure ()
      | _ =>
          let (d1, c1) <- walk pmap host divs calls fn
          divs := d1; calls := c1
      for a in args do
        let (d1, c1) <- walk pmap host divs calls a
        divs := d1; calls := c1
      pure (divs, calls)
  | .lam n t b bi => do
      let (d1, c1) <- walk pmap host divs calls t
      withLocalDecl n bi t fun x => walk pmap host d1 c1 (b.instantiate1 x)
  | .forallE n t b bi => do
      let (d1, c1) <- walk pmap host divs calls t
      withLocalDecl n bi t fun x => walk pmap host d1 c1 (b.instantiate1 x)
  | .letE n t v b _ => do
      let (d1, c1) <- walk pmap host divs calls t
      let (d2, c2) <- walk pmap host d1 c1 v
      withLetDecl n t v fun x => walk pmap host d2 c2 (b.instantiate1 x)
  | .mdata _ e => walk pmap host divs calls e
  | .proj _ _ e => walk pmap host divs calls e
  | _ => pure (divs, calls)

def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx =>
      match env.header.moduleNames[idx.toNat]? with
      | some m => m
      | none => .anonymous
  | none => .anonymous

def trunc (s : String) (n : Nat) : String :=
  if s.length <= n then s else s.take n ++ "..."

run_cmd Lean.Elab.Command.liftTermElabM do
  let env <- Lean.getEnv
  let cl := (closureAux env {} #[] [root]).2
  let clSet : Std.HashSet Name := cl.foldl (fun s n => s.insert n) {}

  -- shape channel sets (value-level, transitive)
  let mut shapeReach : Std.HashSet Name := {}
  shapeReach := shapeReach.insert bpCodeN
  shapeReach := shapeReach.insert sizeN
  let mut contentReach : Std.HashSet Name := {}
  for n in contentSix do contentReach := contentReach.insert n
  let mut changed := true
  while changed do
    changed := false
    for n in cl do
      match valueOf env n with
      | none => pure ()
      | some v =>
        let cs := v.foldConsts ([] : List Name) (fun c a => c :: a)
        if !shapeReach.contains n && cs.any (fun c => shapeReach.contains c) then
          shapeReach := shapeReach.insert n; changed := true
        if !contentReach.contains n && cs.any (fun c => contentReach.contains c) then
          contentReach := contentReach.insert n; changed := true

  -- pass 1: per constant, collect divisor slots and call sites (param-resolved)
  let mut divSites : Array (Name × String × Expr × ArgInfo) := #[]
  let mut callTable : Std.HashMap (Name × Nat) (Array ArgInfo) := {}
  for n in cl do
    match valueOf env n with
    | none => pure ()
    | some v =>
      let (ds, cs) <- lambdaTelescope v fun xs body => do
        let mut pmap : Std.HashMap FVarId Nat := {}
        for h : i in [0:xs.size] do
          match xs[i]! with
          | .fvar fid => pmap := pmap.insert fid i
          | _ => pure ()
        let (divs, calls) <- walk pmap n #[] #[] body
        let mut outD : Array (Name × String × Expr × ArgInfo) := #[]
        for (k, d) in divs do
          outD := outD.push (n, k, d, classifyArg n pmap d)
        let mut outC : Array ((Name × Nat) × ArgInfo) := #[]
        for (g, args) in calls do
          if clSet.contains g then
            for h : j in [0:args.size] do
              outC := outC.push ((g, j), classifyArg n pmap args[j]!)
        pure (outD, outC)
      divSites := divSites ++ ds
      for (key, ai) in cs do
        callTable := callTable.insert key ((callTable.getD key #[]).push ai)

  -- backward resolution of a (constant, paramIdx) slot
  let resolve : Name -> Nat -> Std.HashSet String := fun c0 i0 => Id.run do
    let mut tags : Std.HashSet String := {}
    let mut seen : Std.HashSet (Name × Nat) := {}
    let mut work : Array (Name × Nat) := #[(c0, i0)]
    let mut guard := 0
    while h : work.size > 0 do
      guard := guard + 1
      if guard > 20000 then
        tags := tags.insert "GUARD_EXCEEDED"
        break
      let (c, i) := work[work.size - 1]!
      work := work.pop
      if seen.contains (c, i) then continue
      seen := seen.insert (c, i)
      if c == root then
        tags := tags.insert (if i == 0 then "ROOT_SHAPE"
          else if i == 1 then "ROOT_STORE"
          else if i == 2 then "ROOT_LEFT" else "ROOT_RIGHT")
        continue
      match callTable[(c, i)]? with
      | none => tags := tags.insert s!"NO_CALLSITE({c},{i})"
      | some ais =>
        for ai in ais do
          if ai.pure then tags := tags.insert "LIT"
          for k in ai.consts do
            if contentReach.contains k then tags := tags.insert s!"CONTENT({k})"
            else if shapeReach.contains k then tags := tags.insert s!"SIZEONLY({k})"
            else tags := tags.insert s!"SHAPEFREE({k})"
          if ai.hasLocalFVar then tags := tags.insert s!"LOCAL_IN({ai.caller})"
          for j in ai.paramIdxs do
            work := work.push (ai.caller, j)
    pure tags

  let mut lines : Array String := #[]
  lines := lines.push s!"CORE {cl.size}"
  lines := lines.push s!"DIVISOR_SLOT_SITES {divSites.size}"
  lines := lines.push ""
  let mut nLit := 0
  let mut nSizeOnly := 0
  let mut nContent := 0
  let mut nUnres := 0
  for (host, k, d, ai) in divSites do
    let ds <- try (do pure (toString (<- ppExpr d))) catch _ => pure "<pp-failed>"
    let mut tags : Std.HashSet String := {}
    if ai.pure then tags := tags.insert "LIT"
    for c in ai.consts do
      if contentReach.contains c then tags := tags.insert s!"CONTENT({c})"
      else if shapeReach.contains c then tags := tags.insert s!"SIZEONLY({c})"
      else tags := tags.insert s!"SHAPEFREE({c})"
    if ai.hasLocalFVar then tags := tags.insert s!"LOCAL_IN({host})"
    for j in ai.paramIdxs do
      for t in resolve host j do tags := tags.insert t
    let tl := tags.toList
    let hasContent := tl.any (fun s => s.startsWith "CONTENT(")
    let hasUnres := tl.any (fun s => s.startsWith "LOCAL_IN(" || s.startsWith "NO_CALLSITE(" || s == "GUARD_EXCEEDED")
    let hasSize := tl.any (fun s => s.startsWith "SIZEONLY(") || tl.any (fun s => s == "ROOT_SHAPE")
    let verdict :=
      if hasContent then "X-CANDIDATE"
      else if hasUnres then "UNRESOLVED"
      else if hasSize then "S"
      else "S-or-P"
    if verdict == "X-CANDIDATE" then nContent := nContent + 1
    else if verdict == "UNRESOLVED" then nUnres := nUnres + 1
    else if verdict == "S" then nSizeOnly := nSizeOnly + 1
    else nLit := nLit + 1
    lines := lines.push
      s!"[{verdict}] {host} :: {k} divisor = {trunc ds 110}"
    lines := lines.push s!"        origins = {trunc (toString tl) 900}"
  lines := lines.push ""
  lines := lines.push s!"SUMMARY  S={nSizeOnly}  S-or-P={nLit}  X-CANDIDATE={nContent}  UNRESOLVED={nUnres}"
  IO.FS.writeFile
    "C:/Users/poin/AppData/Local/Temp/claude/C--Users-poin-Documents-RMQ--claude-worktrees-recursing-cerf-300c92/09e21f10-b494-4393-9fb6-2f4ad4dedb1c/scratchpad/dp_f03_div_out.txt"
    (String.intercalate "\n" lines.toList)
  Lean.logInfo m!"divisorSlots={divSites.size} S={nSizeOnly} SorP={nLit} X={nContent} UNRES={nUnres}"

end DPF03Div
