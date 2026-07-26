import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM
import Lean

/-!
DP-F03 (b) part 2: print the DECIDING EXPRESSION of every ite / dite / cond /
decide site and every div / mod / log2 site in the executed controller core,
plus a sound INTERPROCEDURAL taint bound (a callee whose argument carries BP
content is treated as tainted, transitively).
-/

open Lean Lean.Meta

namespace DPF03Branch2

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

def nameHasMatch (n : Name) : Bool :=
  n.components.any fun c =>
    match c with
    | .str _ s => s.startsWith "match_"
    | _ => false

def recSuffixes : List String :=
  ["rec", "recOn", "casesOn", "brecOn", "below", "binductionOn", "brecOnAux",
   "noConfusion", "ndrec", "recAux"]

def isRecName (n : Name) : Bool :=
  match n with
  | .str _ s => recSuffixes.contains s
  | _ => false

def siteKind (c : Name) : Option String :=
  if c == ``ite then some "ite"
  else if c == ``dite then some "dite"
  else if c == ``cond then some "cond"
  else if c == ``Decidable.decide then some "decide"
  else if c == ``HDiv.hDiv || c == ``Nat.div then some "div"
  else if c == ``HMod.hMod || c == ``Nat.mod then some "mod"
  else if c == `Nat.log2 then some "log2"
  else if nameHasMatch c then some "matcher"
  else if isRecName c then some "recursor"
  else none

def decidingArgs (k : String) (args : Array Expr) : Array Expr :=
  if k == "ite" || k == "dite" || k == "cond" then
    if args.size > 1 then #[args[1]!] else args
  else if k == "decide" then
    if args.size > 0 then #[args[0]!] else args
  else if k == "div" || k == "mod" then
    if args.size > 5 then #[args[4]!, args[5]!]
    else if args.size > 1 then #[args[0]!, args[1]!] else args
  else args

partial def mentionsAny (s : Std.HashSet Name) (e : Expr) : Bool :=
  e.foldConsts false (fun c a => a || s.contains c)

/-- Collect (kind, decidingExprs) for the sites we want to print. -/
partial def collect (want : List String) (acc : Array (String × Array Expr)) :
    Expr -> Array (String × Array Expr)
  | e@(.app _ _) =>
      let fn := e.getAppFn
      let args := e.getAppArgs
      let acc :=
        match fn with
        | .const c _ =>
            match siteKind c with
            | some k => if want.contains k then acc.push (k, decidingArgs k args) else acc
            | none => acc
        | _ => acc
      let acc := match fn with
        | .const _ _ => acc
        | _ => collect want acc fn
      args.foldl (fun a x => collect want a x) acc
  | .lam _ t b _ => collect want (collect want acc t) b
  | .forallE _ t b _ => collect want (collect want acc t) b
  | .letE _ t v b _ => collect want (collect want (collect want acc t) v) b
  | .mdata _ e => collect want acc e
  | .proj _ _ e => collect want acc e
  | _ => acc

/-- Constants applied, inside `e`, to an argument that mentions `taint`. -/
partial def calleesWithTaintedArg (taint : Std.HashSet Name)
    (acc : Array Name) : Expr -> Array Name
  | e@(.app _ _) =>
      let fn := e.getAppFn
      let args := e.getAppArgs
      let acc :=
        match fn with
        | .const c _ =>
            if args.any (fun a => mentionsAny taint a) then acc.push c else acc
        | _ => acc
      let acc := match fn with
        | .const _ _ => acc
        | _ => calleesWithTaintedArg taint acc fn
      args.foldl (fun a x => calleesWithTaintedArg taint a x) acc
  | .lam _ t b _ => calleesWithTaintedArg taint (calleesWithTaintedArg taint acc t) b
  | .forallE _ t b _ => calleesWithTaintedArg taint (calleesWithTaintedArg taint acc t) b
  | .letE _ t v b _ =>
      calleesWithTaintedArg taint
        (calleesWithTaintedArg taint (calleesWithTaintedArg taint acc t) v) b
  | .mdata _ e => calleesWithTaintedArg taint acc e
  | .proj _ _ e => calleesWithTaintedArg taint acc e
  | _ => acc

def trunc (s : String) (n : Nat) : String :=
  if s.length <= n then s else s.take n ++ " ..."

def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx =>
      match env.header.moduleNames[idx.toNat]? with
      | some m => m
      | none => .anonymous
  | none => .anonymous

run_cmd Lean.Elab.Command.liftTermElabM do
  let env <- Lean.getEnv
  let cl := (closureAux env {} #[] [root]).2
  let mut lines : Array String := #[]
  lines := lines.push s!"CORE {cl.size}"

  -- interprocedural content taint (sound over-approximation)
  let mut taint : Std.HashSet Name := {}
  for n in contentSix do taint := taint.insert n
  let mut changed := true
  let mut rounds := 0
  while changed do
    changed := false
    rounds := rounds + 1
    for n in cl do
      match valueOf env n with
      | none => pure ()
      | some v =>
        if !taint.contains n && mentionsAny taint v then
          taint := taint.insert n
          changed := true
        if taint.contains n then
          for g in calleesWithTaintedArg taint #[] v do
            if !taint.contains g then
              taint := taint.insert g
              changed := true
  let taintedInCore := cl.filter (fun n => taint.contains n)
  lines := lines.push s!"INTERPROCEDURAL_CONTENT_TAINT_ROUNDS {rounds}"
  lines := lines.push s!"INTERPROCEDURAL_CONTENT_TAINT_IN_CORE {taintedInCore.size} (of {cl.size})"

  -- shape taint (size-only channel included), same fixpoint
  let mut staint : Std.HashSet Name := {}
  staint := staint.insert bpCodeN
  staint := staint.insert sizeN
  changed := true
  while changed do
    changed := false
    for n in cl do
      match valueOf env n with
      | none => pure ()
      | some v =>
        if !staint.contains n && mentionsAny staint v then
          staint := staint.insert n
          changed := true
        if staint.contains n then
          for g in calleesWithTaintedArg staint #[] v do
            if !staint.contains g then
              staint := staint.insert g
              changed := true
  let staintedInCore := cl.filter (fun n => staint.contains n)
  lines := lines.push s!"INTERPROCEDURAL_SHAPE_TAINT_IN_CORE {staintedInCore.size} (of {cl.size})"

  -- count sites hosted inside tainted vs clean constants
  let mut sitesClean := 0
  let mut sitesShapeTainted := 0
  let mut sitesContentTainted := 0
  for n in cl do
    match valueOf env n with
    | none => pure ()
    | some v =>
      let all := collect ["ite","dite","cond","decide","div","mod","log2","matcher","recursor"] #[] v
      if taint.contains n then sitesContentTainted := sitesContentTainted + all.size
      else if staint.contains n then sitesShapeTainted := sitesShapeTainted + all.size
      else sitesClean := sitesClean + all.size
  lines := lines.push s!"SITES_IN_CONTENT_TAINTED_HOSTS {sitesContentTainted}"
  lines := lines.push s!"SITES_IN_SIZE_ONLY_TAINTED_HOSTS {sitesShapeTainted}"
  lines := lines.push s!"SITES_IN_SHAPE_FREE_HOSTS {sitesClean}"
  lines := lines.push ""

  -- print every div / mod / log2 site
  lines := lines.push "== EVERY div / mod / log2 SITE IN THE CORE =="
  let mut divCount := 0
  for n in cl do
    match valueOf env n with
    | none => pure ()
    | some v =>
      let sites <- lambdaTelescope v fun _xs body => do
        let raw := collect ["div","mod","log2"] #[] body
        let mut out : Array String := #[]
        for (k, ds) in raw do
          let mut parts : Array String := #[]
          for d in ds do
            let s <- try (do pure (toString (<- ppExpr d))) catch _ => pure "<pp-failed>"
            parts := parts.push (trunc s 160)
          out := out.push s!"{k}({String.intercalate " , " parts.toList})"
        pure out
      for s in sites do
        divCount := divCount + 1
        let tag :=
          if taint.contains n then "CONTENT-TAINTED-HOST"
          else if staint.contains n then "SIZEONLY-TAINTED-HOST"
          else "SHAPE-FREE-HOST"
        lines := lines.push s!"  [{tag}] {n} :: {s}"
  lines := lines.push s!"DIV_MOD_LOG2_SITE_COUNT {divCount}"
  lines := lines.push ""

  -- print every ite / dite / cond / decide condition
  lines := lines.push "== EVERY ite / dite / cond / decide CONDITION IN THE CORE =="
  let mut condCount := 0
  for n in cl do
    match valueOf env n with
    | none => pure ()
    | some v =>
      let sites <- lambdaTelescope v fun _xs body => do
        let raw := collect ["ite","dite","cond","decide"] #[] body
        let mut out : Array String := #[]
        for (k, ds) in raw do
          let mut parts : Array String := #[]
          for d in ds do
            let s <- try (do pure (toString (<- ppExpr d))) catch _ => pure "<pp-failed>"
            parts := parts.push (trunc s 200)
          out := out.push s!"{k}: {String.intercalate " | " parts.toList}"
        pure out
      for s in sites do
        condCount := condCount + 1
        let tag :=
          if taint.contains n then "CONTENT-TAINTED-HOST"
          else if staint.contains n then "SIZEONLY-TAINTED-HOST"
          else "SHAPE-FREE-HOST"
        lines := lines.push s!"  [{tag}] {n} :: {s}"
  lines := lines.push s!"ITE_DITE_COND_DECIDE_SITE_COUNT {condCount}"
  lines := lines.push ""

  -- matcher / recursor sites: group by head constant
  lines := lines.push "== matcher / recursor HEADS IN THE CORE (grouped) =="
  let mut heads : Std.HashMap String Nat := {}
  let mut headsTainted : Std.HashMap String Nat := {}
  for n in cl do
    match valueOf env n with
    | none => pure ()
    | some v =>
      let rec go (acc : Std.HashMap String Nat × Std.HashMap String Nat) (e : Expr) :
          Std.HashMap String Nat × Std.HashMap String Nat :=
        match e with
        | .app _ _ =>
            let fn := e.getAppFn
            let args := e.getAppArgs
            let acc :=
              match fn with
              | .const c _ =>
                  match siteKind c with
                  | some k =>
                      if k == "matcher" || k == "recursor" then
                        let key := toString c
                        let a1 := acc.1.insert key ((acc.1.getD key 0) + 1)
                        let a2 :=
                          if taint.contains n then
                            acc.2.insert key ((acc.2.getD key 0) + 1)
                          else acc.2
                        (a1, a2)
                      else acc
                  | none => acc
              | _ => acc
            args.foldl (fun a x => go a x) acc
        | .lam _ t b _ => go (go acc t) b
        | .forallE _ t b _ => go (go acc t) b
        | .letE _ t vv b _ => go (go (go acc t) vv) b
        | .mdata _ e => go acc e
        | .proj _ _ e => go acc e
        | _ => acc
      let (h1, h2) := go (heads, headsTainted) v
      heads := h1
      headsTainted := h2
  let mut hs := heads.toList
  hs := hs.mergeSort (fun a b => a.2 >= b.2)
  for (k, c) in hs do
    lines := lines.push s!"  {c} x {k}   (in content-tainted hosts: {headsTainted.getD k 0})"

  IO.FS.writeFile
    "C:/Users/poin/AppData/Local/Temp/claude/C--Users-poin-Documents-RMQ--claude-worktrees-recursing-cerf-300c92/09e21f10-b494-4393-9fb6-2f4ad4dedb1c/scratchpad/dp_f03_branch2_out.txt"
    (String.intercalate "\n" lines.toList)
  Lean.logInfo m!"contentTaint={taintedInCore.size} shapeTaint={staintedInCore.size} divmod={divCount} conds={condCount}"

end DPF03Branch2
