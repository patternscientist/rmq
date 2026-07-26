import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM
import RMQ.Core.SuccinctRMQClassic
import Lean

/-!
ATTACK on the F03 completeness linchpin.

Independent re-implementation. Differences from the coordinator's instrument:
 * explicit Expr traversal (does not trust `Expr.foldConsts`),
 * FOLLOWS `opaqueInfo` values instead of silently stopping,
 * REPORTS every constant reached whose value is absent, bucketed by kind,
 * reports `@[implemented_by]` / `@[extern]` on any reached constant,
 * roots the closure at the PUBLIC entry as well as the shape-taking function,
 * name-independent probe for Decidable/Repr/Quot/Classical leakage.
-/

open Lean

namespace Atk

def shapeTy  : Name := `RMQ.Cartesian.CartesianShape
def recN     : Name := `RMQ.Cartesian.CartesianShape.rec
def bpCodeN  : Name := `RMQ.Cartesian.CartesianShape.bpCode
def sizeN    : Name := `RMQ.Cartesian.CartesianShape.size

/-- Explicit total traversal collecting every constant name in an expression. -/
partial def allConsts : Expr -> Array Name -> Array Name
  | .const c _,        acc => acc.push c
  | .app f a,          acc => allConsts a (allConsts f acc)
  | .lam _ t b _,      acc => allConsts b (allConsts t acc)
  | .forallE _ t b _,  acc => allConsts b (allConsts t acc)
  | .letE _ t v b _,   acc => allConsts b (allConsts v (allConsts t acc))
  | .mdata _ e,        acc => allConsts e acc
  | .proj s _ e,       acc => allConsts e (acc.push s)
  | _,                 acc => acc

structure Kind where
  tag      : String
  val      : Option Expr

def kindOf (env : Environment) (n : Name) : Kind :=
  match env.find? n with
  | none                => { tag := "MISSING",  val := none }
  | some (.axiomInfo _) => { tag := "axiom",    val := none }
  | some (.defnInfo v)  => { tag := "def",      val := some v.value }
  | some (.thmInfo v)   => { tag := "theorem",  val := some v.value }
  | some (.opaqueInfo v)=> { tag := "opaque",   val := some v.value }
  | some (.quotInfo _)  => { tag := "quot",     val := none }
  | some (.inductInfo _)=> { tag := "induct",   val := none }
  | some (.ctorInfo _)  => { tag := "ctor",     val := none }
  | some (.recInfo _)   => { tag := "rec",      val := none }

/-- Computational dependencies: skip theorems (proof terms cannot influence an
    executed address), follow EVERYTHING else that has a value, including
    `opaque`. -/
def compDeps (env : Environment) (n : Name) : Array Name :=
  let k := kindOf env n
  if k.tag == "theorem" then #[]
  else match k.val with
    | some v => allConsts v #[]
    | none   => #[]

partial def closureAux (env : Environment) (seen : Std.HashSet Name)
    (out : Array Name) : List Name -> Std.HashSet Name × Array Name
  | [] => (seen, out)
  | n :: rest =>
      if seen.contains n then closureAux env seen out rest
      else
        let seen := seen.insert n
        let out := out.push n
        closureAux env seen out ((compDeps env n).toList ++ rest)

def closure (env : Environment) (roots : List Name) : Array Name :=
  (closureAux env {} #[] roots).2

/-- Direct primitive shape observers: constants whose VALUE mentions the
    recursor or a constructor of `CartesianShape`. Name-independent. -/
def touchesShapePrim (env : Environment) (n : Name) : Array Name :=
  let k := kindOf env n
  if k.tag == "theorem" then #[]
  else match k.val with
    | none => #[]
    | some v =>
        (allConsts v #[]).filter (fun c =>
          c == recN ||
          c == `RMQ.Cartesian.CartesianShape.empty ||
          c == `RMQ.Cartesian.CartesianShape.node)

def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => (env.header.moduleNames[idx.toNat]?).getD .anonymous
  | none => .anonymous

def report (env : Environment) (label : String) (roots : List Name)
    (lines : Array String) : Array String := Id.run do
  let cl := closure env roots
  let mut lines := lines
  lines := lines.push ""
  lines := lines.push s!"################ {label} ################"
  lines := lines.push s!"roots = {roots}"
  lines := lines.push s!"CLOSURE_SIZE {cl.size}"

  -- (A) constants reached whose value is ABSENT, bucketed by kind.
  let mut axioms  : Array Name := #[]
  let mut opaques : Array Name := #[]
  let mut quots   : Array Name := #[]
  let mut missing : Array Name := #[]
  let mut thms    : Nat := 0
  let mut defs    : Nat := 0
  let mut recs    : Nat := 0
  let mut ctors   : Nat := 0
  let mut inducts : Nat := 0
  for n in cl do
    let k := kindOf env n
    if k.tag == "axiom"   then axioms  := axioms.push n
    if k.tag == "opaque"  then opaques := opaques.push n
    if k.tag == "quot"    then quots   := quots.push n
    if k.tag == "MISSING" then missing := missing.push n
    if k.tag == "theorem" then thms    := thms + 1
    if k.tag == "def"     then defs    := defs + 1
    if k.tag == "rec"     then recs    := recs + 1
    if k.tag == "ctor"    then ctors   := ctors + 1
    if k.tag == "induct"  then inducts := inducts + 1
  lines := lines.push s!"KINDS def={defs} theorem={thms} rec={recs} ctor={ctors} induct={inducts} axiom={axioms.size} opaque={opaques.size} quot={quots.size} missing={missing.size}"
  lines := lines.push "-- AXIOMS reached (value absent; closure stops here) --"
  for n in axioms do lines := lines.push s!"   AXIOM {n}"
  lines := lines.push "-- OPAQUE reached (coordinator's `value?` would have returned none here) --"
  for n in opaques do lines := lines.push s!"   OPAQUE {n}"
  lines := lines.push "-- QUOT reached --"
  for n in quots do lines := lines.push s!"   QUOT {n}"
  lines := lines.push "-- MISSING --"
  for n in missing do lines := lines.push s!"   MISSING {n}"

  -- (B) compiler-level overrides on reached constants
  lines := lines.push "-- @[implemented_by] / @[extern] on reached constants --"
  let mut over : Nat := 0
  for n in cl do
    match Lean.Compiler.getImplementedBy? env n with
    | some tgt => over := over + 1; lines := lines.push s!"   IMPLEMENTED_BY {n} -> {tgt}"
    | none => pure ()
    if Lean.isExtern env n then
      over := over + 1; lines := lines.push s!"   EXTERN {n}"
  lines := lines.push s!"   COMPILER_OVERRIDE_COUNT {over}"

  -- (C) primitive shape observers, name-independent
  lines := lines.push "-- constants whose VALUE directly references CartesianShape.rec / ctors --"
  let mut prims : Nat := 0
  for n in cl do
    let hits := touchesShapePrim env n
    if !hits.isEmpty then
      prims := prims + 1
      lines := lines.push s!"   PRIM {n} :: {hits} :: kind={(kindOf env n).tag} mod={moduleOf env n}"
  lines := lines.push s!"   PRIMITIVE_SHAPE_OBSERVER_COUNT {prims}"

  -- (D) named leakage suspects present in the closure
  lines := lines.push "-- leakage suspects present in closure --"
  let suspects : List Name :=
    [ `RMQ.Cartesian.instDecidableEqCartesianShape
    , `RMQ.Cartesian.CartesianShape.decEq
    , `RMQ.Cartesian.reprCartesianShape
    , `RMQ.Cartesian.instReprCartesianShape
    , `Classical.choice, `Classical.propDecidable, `Classical.dec, `Classical.em
    , `sorryAx, `Quot.lift, `Quot.mk, `Quot.ind, `Quot.sound
    , `WellFounded.fix, `WellFounded.fixF, `Decidable.decide, `decide ]
  let clSet : Std.HashSet Name := cl.foldl (fun s n => s.insert n) {}
  for s in suspects do
    let mark := if clSet.contains s then "PRESENT" else "absent "
    lines := lines.push s!"   {mark} {s}"
  return lines

run_cmd do
  let env <- Lean.getEnv
  let mut lines : Array String := #[]

  -- sanity: is CartesianShape a structure (would enable `.proj` leakage)?
  lines := lines.push s!"IS_STRUCTURE_CartesianShape {Lean.isStructure env shapeTy}"
  lines := lines.push s!"HAS_decEq {(env.find? `RMQ.Cartesian.CartesianShape.decEq).isSome}"
  lines := lines.push s!"HAS_instDecidableEq {(env.find? `RMQ.Cartesian.instDecidableEqCartesianShape).isSome}"
  lines := lines.push s!"HAS_repr {(env.find? `RMQ.Cartesian.reprCartesianShape).isSome}"

  lines <- pure (report env "ROOT-A shape-taking store-param whole query (coordinator's root)"
    [`RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore] lines)

  lines <- pure (report env "ROOT-B PUBLIC entry queryTraceResultWithStore"
    [`RMQ.SuccinctClassic.queryTraceResultWithStore] lines)

  IO.FS.writeFile
    "C:/Users/poin/AppData/Local/Temp/claude/C--Users-poin-Documents-RMQ--claude-worktrees-recursing-cerf-300c92/09e21f10-b494-4393-9fb6-2f4ad4dedb1c/scratchpad/atk_linchpin_out.txt"
    (String.intercalate "\n" lines.toList)
  Lean.logInfo m!"wrote atk_linchpin_out.txt ({lines.size} lines)"

end Atk
