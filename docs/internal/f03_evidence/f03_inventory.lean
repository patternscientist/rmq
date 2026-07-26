import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM
import Lean

/-!
F03 exhaustive dependency inventory.

Machine-computed transitive constant closure of the whole-query trace
function's *definitional* unfolding. F03 requires an exhaustive inventory of
every logical-read source and geometry consumer, not representative rows, so
the inventory must be generated rather than curated.

Buckets emitted:
  ALL      - full closure size
  SHAPED   - constants whose TYPE mentions `Cartesian.CartesianShape`
  DESTRUCT - constants that directly reference the shape recursor/casesOn or
             a shape constructor, i.e. that actually take the tree apart
  BPCODE   - constants that directly reference `CartesianShape.bpCode`
  SIZE     - constants that directly reference `CartesianShape.size`
-/

open Lean

namespace F03Inv

def root : Name :=
  `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore

def shapeTy : Name := `RMQ.Cartesian.CartesianShape

/-- Constants appearing in an expression. -/
def constsOf (e : Expr) : List Name :=
  e.foldConsts [] (fun c a => c :: a)

/-- Direct dependencies (type and value) of one constant. -/
def directDeps (env : Environment) (n : Name) : List Name :=
  match env.find? n with
  | none => []
  | some ci =>
      let fromType := constsOf ci.type
      let fromVal := match ci.value? with
        | some v => constsOf v
        | none => []
      fromType ++ fromVal

partial def closureAux (env : Environment) (seen : Std.HashSet Name)
    (out : Array Name) : List Name -> Std.HashSet Name × Array Name
  | [] => (seen, out)
  | n :: rest =>
      if seen.contains n then closureAux env seen out rest
      else
        let seen := seen.insert n
        let out := out.push n
        closureAux env seen out (directDeps env n ++ rest)

def closure (env : Environment) (roots : List Name) : Array Name :=
  (closureAux env {} #[] roots).2

/-- Does this expression mention the given constant? -/
def mentions (e : Expr) (target : Name) : Bool :=
  e.foldConsts false (fun c a => a || c == target)

def typeMentions (env : Environment) (n : Name) (target : Name) : Bool :=
  match env.find? n with
  | none => false
  | some ci => mentions ci.type target

def valueMentions (env : Environment) (n : Name) (targets : List Name) : Bool :=
  match env.find? n with
  | none => false
  | some ci =>
      match ci.value? with
      | none => false
      | some v => targets.any (fun t => mentions v t)

def isProject (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | none => false
  | some ci =>
      match ci with
      | .thmInfo _ => false
      | _ => true

/-- Render the head symbol of a constant's type for compact grouping. -/
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

run_cmd do
  let env <- Lean.getEnv
  let cl := closure env [root]
  let mut shaped : Array Name := #[]
  let mut destruct : Array Name := #[]
  let mut bpcode : Array Name := #[]
  let mut sizeUsers : Array Name := #[]
  let mut thms := 0
  for n in cl do
    if !(isProject env n) then
      thms := thms + 1
      continue
    if typeMentions env n shapeTy then
      shaped := shaped.push n
    if valueMentions env n [shapeTy ++ `rec, shapeTy ++ `casesOn,
        shapeTy ++ `node, shapeTy ++ `empty, shapeTy ++ `recOn,
        shapeTy ++ `brecOn] then
      destruct := destruct.push n
    if valueMentions env n [shapeTy ++ `bpCode] then
      bpcode := bpcode.push n
    if valueMentions env n [shapeTy ++ `size] then
      sizeUsers := sizeUsers.push n
  let lines : Array String :=
    #[s!"ROOT {root}",
      s!"CLOSURE_TOTAL {cl.size}",
      s!"CLOSURE_THEOREMS {thms}",
      s!"SHAPED_TYPE_COUNT {shaped.size}",
      s!"DESTRUCTURES_SHAPE_COUNT {destruct.size}",
      s!"USES_BPCODE_COUNT {bpcode.size}",
      s!"USES_SIZE_COUNT {sizeUsers.size}",
      "",
      "== DESTRUCTURES_SHAPE (directly pattern-matches the Cartesian tree) =="]
  let mut all := lines
  for n in destruct do
    all := all.push s!"  DESTRUCT {n} :: {resultHead env n}"
  all := all.push ""
  all := all.push "== USES_BPCODE (directly references CartesianShape.bpCode) =="
  for n in bpcode do
    all := all.push s!"  BPCODE {n} :: {resultHead env n}"
  all := all.push ""
  all := all.push "== USES_SIZE (directly references CartesianShape.size) =="
  for n in sizeUsers do
    all := all.push s!"  SIZE {n} :: {resultHead env n}"
  all := all.push ""
  all := all.push "== SHAPED_TYPE (type mentions CartesianShape), grouped by result head =="
  for n in shaped do
    all := all.push s!"  SHAPED {n} :: {resultHead env n}"
  let text := String.intercalate "\n" all.toList
  IO.FS.writeFile
    "C:/Users/poin/AppData/Local/Temp/claude/C--Users-poin-Documents-RMQ--claude-worktrees-recursing-cerf-300c92/09e21f10-b494-4393-9fb6-2f4ad4dedb1c/scratchpad/f03_inventory_out.txt"
    text
  Lean.logInfo m!"closure={cl.size} shaped={shaped.size} destruct={destruct.size} bpcode={bpcode.size} size={sizeUsers.size}"

end F03Inv
