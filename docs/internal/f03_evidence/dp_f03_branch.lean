import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM
import Lean

/-!
DP-F03 (b): exhaustive BRANCH / DIVISOR sweep over the executed controller path.

Same computational core as the coordinator's inventory (values only, theorems
skipped: a proof term cannot influence an executed address).  For every
constant in that core we count every branching site (ite / dite / cond /
matcher / recursor / Decidable.decide) and every division or modulus site, and
we mark whether the DECIDING subterm (condition, discriminants, divisor) can
depend on the `CartesianShape` at all, and if so through which channel.
-/

open Lean

namespace DPF03Branch

def root : Name :=
  `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore

def bpCodeN : Name := `RMQ.Cartesian.CartesianShape.bpCode
def sizeN : Name := `RMQ.Cartesian.CartesianShape.size
def lengthN : Name := `List.length

/-- The six constants that read BP CONTENT (coordinator inventory F1..F6). -/
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

/-! ## site classification -/

inductive Site where
  | ite | dite | cond | matcher | recursor | decide | div | mod | log2
deriving BEq, Hashable, Repr

def siteName : Site -> String
  | .ite => "ite" | .dite => "dite" | .cond => "cond"
  | .matcher => "matcher" | .recursor => "recursor" | .decide => "decide"
  | .div => "div" | .mod => "mod" | .log2 => "log2"

def isBranchSite : Site -> Bool
  | .div | .mod | .log2 => false
  | _ => true

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

/-- Which kind of site (if any) does this head constant open? -/
def siteOf (c : Name) : Option Site :=
  if c == ``ite then some .ite
  else if c == ``dite then some .dite
  else if c == ``cond then some .cond
  else if c == ``Decidable.decide then some .decide
  else if c == ``HDiv.hDiv || c == ``Nat.div then some .div
  else if c == ``HMod.hMod || c == ``Nat.mod then some .mod
  else if c == `Nat.log2 then some .log2
  else if nameHasMatch c then some .matcher
  else if isRecName c then some .recursor
  else none

/-- Subterms that DECIDE the site: condition / divisor / discriminants.
    For matchers and recursors we conservatively take every explicit argument. -/
def decidingArgs (s : Site) (args : Array Expr) : Array Expr :=
  match s with
  | .ite => if h : args.size > 1 then #[args[1]!] else args
  | .dite => if h : args.size > 1 then #[args[1]!] else args
  | .cond => if h : args.size > 1 then #[args[1]!] else args
  | .decide => if h : args.size > 0 then #[args[0]!] else args
  | .div | .mod => if h : args.size > 5 then #[args[4]!, args[5]!]
                   else if h : args.size > 1 then #[args[0]!, args[1]!] else args
  | .log2 => args
  | .matcher | .recursor => args

/-- Does `e` mention any constant from `s`? -/
partial def mentionsAny (s : Std.HashSet Name) (e : Expr) : Bool :=
  (e.foldConsts false (fun c a => a || s.contains c))

/-- Count `bpCode` occurrences and how many sit under `List.length`. -/
partial def countUnderLength (target : Name) : Expr -> Nat × Nat
  | e@(.app _ _) =>
      let fn := e.getAppFn
      let args := e.getAppArgs
      match fn with
      | .const c _ =>
          if c == lengthN then
            let inner := args.findSome? (fun a =>
              if a.getAppFn.isConstOf target then some a else none)
            match inner with
            | some innerArg =>
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

structure Tally where
  perSite : Std.HashMap String Nat := {}
  shapeDeciding : Std.HashMap String Nat := {}
  contentDeciding : Std.HashMap String Nat := {}
  total : Nat := 0
  shapeTotal : Nat := 0
  contentTotal : Nat := 0

def bump (m : Std.HashMap String Nat) (k : String) : Std.HashMap String Nat :=
  m.insert k ((m.getD k 0) + 1)

/-- Walk an expression, tallying every site and classifying its deciding args. -/
partial def sweep (shapeSet contentSet : Std.HashSet Name)
    (t : Tally) : Expr -> Tally
  | e@(.app _ _) =>
      let fn := e.getAppFn
      let args := e.getAppArgs
      let t :=
        match fn with
        | .const c _ =>
            match siteOf c with
            | some s =>
                let dec := decidingArgs s args
                let shapeDep := dec.any (fun a => mentionsAny shapeSet a)
                let contentDep := dec.any (fun a => mentionsAny contentSet a)
                { t with
                  perSite := bump t.perSite (siteName s)
                  total := t.total + 1
                  shapeDeciding :=
                    if shapeDep then bump t.shapeDeciding (siteName s)
                    else t.shapeDeciding
                  shapeTotal := if shapeDep then t.shapeTotal + 1 else t.shapeTotal
                  contentDeciding :=
                    if contentDep then bump t.contentDeciding (siteName s)
                    else t.contentDeciding
                  contentTotal :=
                    if contentDep then t.contentTotal + 1 else t.contentTotal }
            | none => t
        | _ => t
      let t := match fn with
        | .const _ _ => t
        | _ => sweep shapeSet contentSet t fn
      args.foldl (fun acc a => sweep shapeSet contentSet acc a) t
  | .const c _ =>
      match siteOf c with
      | some s =>
          { t with perSite := bump t.perSite (siteName s), total := t.total + 1 }
      | none => t
  | .lam _ ty b _ =>
      sweep shapeSet contentSet (sweep shapeSet contentSet t ty) b
  | .forallE _ ty b _ =>
      sweep shapeSet contentSet (sweep shapeSet contentSet t ty) b
  | .letE _ ty v b _ =>
      sweep shapeSet contentSet
        (sweep shapeSet contentSet (sweep shapeSet contentSet t ty) v) b
  | .mdata _ e => sweep shapeSet contentSet t e
  | .proj _ _ e => sweep shapeSet contentSet t e
  | _ => t

def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx =>
      match env.header.moduleNames[idx.toNat]? with
      | some m => m
      | none => .anonymous
  | none => .anonymous

/-- Names whose closure membership we want to report explicitly. -/
def watchList : List Name :=
  [`RMQ.SuccinctClose.canonicalBPRelativeSummaryBase,
   `RMQ.SuccinctClose.canonicalBPRelativeSummaryBlockCountRaw,
   `RMQ.SuccinctClose.canonicalBPRelativeSummaryBlockSizeRaw,
   `RMQ.SuccinctClose.canonicalBPRelativeSummaryBlocksPerSuperRaw,
   `RMQ.SuccinctClose.canonicalBPRelativeSummarySuperCountRaw,
   `RMQ.SuccinctClose.canonicalBPRelativeSummaryRelativeWidthRaw,
   `RMQ.SuccinctClose.canonicalBPRelativeSummarySuperWidth,
   `RMQ.SuccinctClose.canonicalBPRelativeMinMaxArgSummaryTableActive,
   `RMQ.SuccinctClose.canonicalBPRelativeMinMaxArgSummaryTableActive_decidable,
   `RMQ.SuccinctClose.canonicalBPRelativeSummaryBlockSize,
   `RMQ.SuccinctClose.canonicalBPRelativeSummaryBlocksPerSuper,
   `RMQ.SuccinctClose.canonicalBPRelativeSummaryBlockCount,
   `RMQ.SuccinctClose.canonicalBPRelativeSummarySuperCount,
   `RMQ.SuccinctClose.canonicalBPRelativeSummaryRelativeWidth,
   `RMQ.SuccinctClose.RelativeRmm.canonicalLayout,
   `RMQ.SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable,
   `RMQ.SuccinctClose.bpExcessAt,
   `RMQ.SuccinctClose.bpBlockMinExcess,
   `RMQ.SuccinctClose.bpBlockArgMinPrefixPos,
   `RMQ.SuccinctSpace.sampledDirectoryOverhead,
   `RMQ.SuccinctSpace.logLogSampledDirectoryOverhead,
   `RMQ.SuccinctRank.machineWordBits]

run_cmd do
  let env <- Lean.getEnv
  let cl := (closureAux env {} #[] [root]).2
  let clSet : Std.HashSet Name := cl.foldl (fun s n => s.insert n) {}
  let mut lines : Array String := #[]
  lines := lines.push s!"ROOT {root}"
  lines := lines.push s!"COMPUTATIONAL_CLOSURE_TOTAL {cl.size}"
  lines := lines.push ""
  lines := lines.push "== closure membership of watched geometry constants =="
  for n in watchList do
    let tag := if clSet.contains n then "IN_CORE" else "NOT_IN_CORE"
    lines := lines.push s!"  {tag} {n}"
  -- shape-reachable set: constants whose value transitively mentions bpCode/size
  let mut shapeReach : Std.HashSet Name := {}
  shapeReach := shapeReach.insert bpCodeN
  shapeReach := shapeReach.insert sizeN
  -- fixpoint over the closure
  let mut changed := true
  let mut rounds := 0
  while changed do
    changed := false
    rounds := rounds + 1
    for n in cl do
      if shapeReach.contains n then continue
      match valueOf env n with
      | none => pure ()
      | some v =>
        if mentionsAny shapeReach v then
          shapeReach := shapeReach.insert n
          changed := true
  -- content-reachable set: constants whose value transitively mentions one of the six
  let mut contentReach : Std.HashSet Name := {}
  for n in contentSix do contentReach := contentReach.insert n
  changed := true
  while changed do
    changed := false
    for n in cl do
      if contentReach.contains n then continue
      match valueOf env n with
      | none => pure ()
      | some v =>
        if mentionsAny contentReach v then
          contentReach := contentReach.insert n
          changed := true
  let shapeInCore := cl.filter (fun n => shapeReach.contains n)
  let contentInCore := cl.filter (fun n => contentReach.contains n)
  lines := lines.push ""
  lines := lines.push s!"SHAPE_REACHABLE_IN_CORE {shapeInCore.size} (of {cl.size})"
  lines := lines.push s!"CONTENT_REACHABLE_IN_CORE {contentInCore.size} (of {cl.size})"
  lines := lines.push ""
  lines := lines.push "== content-reachable constants (callers* of the six) =="
  for n in contentInCore do
    lines := lines.push s!"  CONTENTCONE {n} mod={moduleOf env n}"
  -- global site sweep
  let mut t : Tally := {}
  let mut perConst : Array (Name × Nat × Nat × Nat) := #[]
  for n in cl do
    match valueOf env n with
    | none => pure ()
    | some v =>
      let t0 : Tally := {}
      let tn := sweep shapeReach contentReach t0 v
      if tn.total > 0 then
        perConst := perConst.push (n, tn.total, tn.shapeTotal, tn.contentTotal)
      t := { perSite := tn.perSite.fold (fun m k c => m.insert k ((m.getD k 0) + c)) t.perSite
             shapeDeciding := tn.shapeDeciding.fold
               (fun m k c => m.insert k ((m.getD k 0) + c)) t.shapeDeciding
             contentDeciding := tn.contentDeciding.fold
               (fun m k c => m.insert k ((m.getD k 0) + c)) t.contentDeciding
             total := t.total + tn.total
             shapeTotal := t.shapeTotal + tn.shapeTotal
             contentTotal := t.contentTotal + tn.contentTotal }
  lines := lines.push ""
  lines := lines.push "== GLOBAL SITE SWEEP over the computational core =="
  lines := lines.push s!"TOTAL_SITES {t.total}"
  lines := lines.push s!"SITES_WITH_SHAPE_DEPENDENT_DECIDER {t.shapeTotal}"
  lines := lines.push s!"SITES_WITH_CONTENT_DEPENDENT_DECIDER {t.contentTotal}"
  for k in ["ite","dite","cond","matcher","recursor","decide","div","mod","log2"] do
    lines := lines.push
      s!"  {k}: total={t.perSite.getD k 0} shapeDeciding={t.shapeDeciding.getD k 0} contentDeciding={t.contentDeciding.getD k 0}"
  lines := lines.push ""
  lines := lines.push "== constants that host a SHAPE-DEPENDENT deciding site =="
  for (n, tot, sh, co) in perConst do
    if sh > 0 then
      let (bt, bu) := match valueOf env n with
        | some v => countUnderLength bpCodeN v
        | none => (0,0)
      lines := lines.push
        s!"  HOST {n} sites={tot} shapeDeciding={sh} contentDeciding={co} bpCodeOcc={bt} underLen={bu} mod={moduleOf env n}"
  IO.FS.writeFile
    "C:/Users/poin/AppData/Local/Temp/claude/C--Users-poin-Documents-RMQ--claude-worktrees-recursing-cerf-300c92/09e21f10-b494-4393-9fb6-2f4ad4dedb1c/scratchpad/dp_f03_branch_out.txt"
    (String.intercalate "\n" lines.toList)
  Lean.logInfo m!"core={cl.size} sites={t.total} shapeSites={t.shapeTotal} contentSites={t.contentTotal} shapeReach={shapeInCore.size} contentReach={contentInCore.size}"

end DPF03Branch
