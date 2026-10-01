import RMQ.Core.WordRAM.Lifecycle.Executable
import RMQ.Core.WordRAM.Lifecycle.Controls

/-! Finite lifecycle validation. The production owner is run directly. A second,
bounded, history-free fold counts transitions produced by the same scalar step;
its final-owner projection is proved below. Answers come from an independent
strict-comparison scan. No canonical output is materialized as an implementation.
-/
namespace RMQ.Validation.PackedLifecycle
open RMQ.SuccinctFinal RMQ.SuccinctFinal.PackedLifecycle

def categories : Array Category := #[
  .old .read, .old .register, .old .arithmetic, .old .comparison,
  .old .branch, .old .control, .old .write, .old .allocation,
  .old .keyRead, .old .oracleComparison, .numericRelease, .keyRelease,
  .keyRegisterRelease, .requestAdmission, .controlEntry]

def categoryIndex : Category → Nat
  | .old .read => 0 | .old .register => 1 | .old .arithmetic => 2
  | .old .comparison => 3 | .old .branch => 4 | .old .control => 5
  | .old .write => 6 | .old .allocation => 7 | .old .keyRead => 8
  | .old .oracleComparison => 9 | .numericRelease => 10 | .keyRelease => 11
  | .keyRegisterRelease => 12 | .requestAdmission => 13 | .controlEntry => 14

theorem category_index_exact (c : Category) : categories[categoryIndex c]? = some c := by
  cases c with
  | old c => cases c <;> rfl
  | numericRelease | keyRelease | keyRegisterRelease | requestAdmission | controlEntry => rfl

structure Counters where
  steps : Nat := 0
  counts : Array Nat := Array.replicate 15 0
  peak : Nat := 0
  source : Option (Nat × Nat) := none
  scalarSizes : Bool := true

def Counters.add (c : Counters) (t : ArrayTransition) : Counters :=
  let i := categoryIndex t.action.category
  let sizes := match t.action with
    | .instruction .releaseCell => t.before.memory.size == t.after.memory.size + 1
    | .instruction .releaseKey => t.before.keys.size == t.after.keys.size + 1
    | .instruction .releaseKeyRegister => t.before.keyRegs.size == t.after.keyRegs.size + 1
    | .instruction (.old (.reserve _)) => t.after.memory.size == t.before.memory.size + 1
    | _ => true
  { steps := c.steps + 1
    counts := c.counts.setIfInBounds i (c.counts.getD i 0 + 1)
    peak := max c.peak (max t.before.memory.size t.after.memory.size)
    source := if t.before.pc == Layout.finalizerBase then
      some (t.before.regs.getD 0 0, t.before.regs.getD 2 0) else c.source
    scalarSizes := c.scalarSizes && sizes && t.before.regs.size == t.after.regs.size }

/-- Validation-only counters retain no states, input, key bank or trace. -/
def counted (program : Array Instruction) : Nat → Owner → Counters → Owner × Counters
  | 0, owner, c => (owner, c)
  | fuel + 1, owner, c => match stepArray program owner with
    | none => (owner, c)
    | some t => counted program fuel t.after (c.add t)

theorem counted_owner (program : Array Instruction) (fuel : Nat) (owner : Owner) (c : Counters) :
    (counted program fuel owner c).1 = runOwner program fuel owner := by
  induction fuel generalizing owner c with
  | zero => rfl
  | succ fuel ih => cases h : stepArray program owner <;> simp [counted, runOwner, h, ih]

def sameOwner (a b : Owner) : Bool :=
  a.regs == b.regs && a.memory == b.memory && a.keys == b.keys &&
    a.keyRegs == b.keyRegs && a.pc == b.pc && a.status == b.status

/-- Invalid endpoints yield zero. Only strict improvements replace the current
index, so ties keep the first index. This does not call any packed query oracle. -/
def reference (xs : Array Int) (left right : Nat) : Nat :=
  if left < right && right ≤ xs.size then
    let best := (List.range (right-left)).foldl (fun best offset =>
      let i := left + offset
      if xs.getD i 0 < xs.getD best 0 then i else best) left
    best + 1
  else 0

structure Fixture where
  id : String
  model : InputModel
  xs : List Int
  queries : List (Nat × Nat)
  dirty : Bool := false

def geometryInput (n : Nat) : List Int :=
  (List.range n).map (fun i => (Int.ofNat ((i*17 + i/3) % 11)) - 5)

def wideGeometryInput (n : Nat) : List Int :=
  (geometryInput n).map (fun x => x * (2^(PackedWordRAM.wordWidth n + 5) : Int) + 17)

def registry : List Fixture := [
  ⟨"L01-W-EMPTY", .word, [], [(0,0)], false⟩,
  ⟨"L02-C-EMPTY", .comparison, [], [(0,1)], false⟩,
  ⟨"L03-W-SINGLE", .word, [-7], [(0,1)], false⟩,
  ⟨"L04-C-SINGLE", .comparison, [-7], [(0,1)], false⟩,
  ⟨"L05-W-REPEAT", .word, [2,2,2], [(0,3),(1,3)], false⟩,
  ⟨"L06-C-REPEAT", .comparison, [2,2,2], [(0,3),(1,3)], false⟩,
  ⟨"L07-W-TIE", .word, [4,-3,-3,8], [(0,4),(2,4)], false⟩,
  ⟨"L08-C-TIE", .comparison, [4,-3,-3,8], [(0,4),(2,4)], false⟩,
  ⟨"L09-W-INVALID", .word, [3,1], [(2,1),(0,3),(1,1),(0,2)], false⟩,
  ⟨"L10-C-INVALID", .comparison, [3,1], [(2,1),(0,3),(1,1),(0,2)], false⟩,
  ⟨"L11-W-DIRTY", .word, [4,-3,-3,8], [(0,4),(1,3)], true⟩,
  ⟨"L12-C-DIRTY", .comparison, [4,-3,-3,8], [(0,4),(1,3)], true⟩,
  ⟨"L13-W-N24", .word, geometryInput 24, [(0,24),(8,23),(12,24),(1,22)], false⟩,
  ⟨"L14-C-N24", .comparison, wideGeometryInput 24, [(0,24),(8,23),(12,24),(1,22)], false⟩,
  ⟨"L15-W-N83", .word, geometryInput 83, [(0,83),(27,82),(41,83),(1,81)], false⟩,
  ⟨"L16-C-N83", .comparison, wideGeometryInput 83, [(0,83),(27,82),(41,83),(1,81)], false⟩]

def requiredIds := ["L01-W-EMPTY", "L02-C-EMPTY", "L03-W-SINGLE", "L04-C-SINGLE",
  "L05-W-REPEAT", "L06-C-REPEAT", "L07-W-TIE", "L08-C-TIE", "L09-W-INVALID",
  "L10-C-INVALID", "L11-W-DIRTY", "L12-C-DIRTY", "L13-W-N24", "L14-C-N24",
  "L15-W-N83", "L16-C-N83"]

#guard registry.map (·.id) == requiredIds
#guard requiredIds.eraseDups.length == 16
#guard reference #[] 0 0 == 0
#guard reference #[4,-3,-3,8] 0 4 == 2
#guard reference #[4,-3,-3,8] 2 4 == 3
#guard reference #[4,-3,-3,8] 0 5 == 0

def require (ok : Bool) (surface : String) : IO Unit :=
  unless ok do throw (IO.userError surface)

def modelName : InputModel → String | .word => "word" | .comparison => "comparison"

def checkRetained (xs : List Int) (owner : Owner) : IO Unit := do
  require (owner.regs.size == 8273) "numeric-bank"
  require (owner.keys.isEmpty && owner.keyRegs.isEmpty) "literal-key-retirement"
  require (owner.memory.getD 0 none == some xs.length) "retained-header"
  require (owner.memory.getD 7 none == some owner.memory.size) "retained-extent"
  require (owner.memory.all Option.isSome) "retained-initialization"

def checkAnswer (xs : List Int) (left right : Nat) (owner : Owner) : IO Unit :=
  require (owner.status == .halted (reference xs.toArray left right)) "independent-answer"

def checkCounts (c : Counters) : IO Unit := do
  require (c.counts.size == 15 && c.counts.foldl (·+·) 0 == c.steps) "category-sum"
  require c.scalarSizes "scalar-size-step"

def entryMatches (n left right : Nat) (owner : Owner) : Bool :=
  owner.regs.size == 8273 && owner.pc == 0 && owner.status == .running &&
    (List.range 8273).all (fun r => owner.regs.getD r 0 ==
      (PackedWordRAM.initialState n left right).regs r)

/-- Both executions start with the SAME real halted first-query owner. The sole
challenge replaces its witnessed dirty register's clear by a self move. The
rejected surface is the real compact-query entry ABI, not an invented answer. -/
def dirtyControl (f : Fixture) (program : Array Instruction) (first : Owner) : IO Nat := do
  let some r := (List.range (8273-400)).map (·+400) |>.find?
    (fun r => first.regs.getD r 0 != 0)
    | throw (IO.userError "dirty-witness-missing")
  let admitted := requestProtocolOwner Layout.serviceEntry 1 3 first
  let fuel := 4 + QueryEntry.setupCost
  let positive := runOwner program fuel admitted
  require (entryMatches f.xs.length 1 3 positive) "dirty-positive-full-entry"
  require (Controls.entryRegisterClean positive r) "dirty-positive-register"
  let patch := Service.entry + 4 + (r-3)
  let operand : PackedConstruction.Operand := ⟨r % 2^32, Nat.mod_lt _ (by decide)⟩
  require (program[patch]? == some (.old (.constant operand 0))) "dirty-patch-identity"
  let challenged := program.setIfInBounds patch (.old (.move operand operand))
  let negative := runOwner challenged fuel admitted
  require (negative.pc == 0 && negative.status == .running) "dirty-negative-reaches-entry"
  require (negative.memory == positive.memory && negative.regs.size == 8273) "dirty-same-owner-data"
  require (!entryMatches f.xs.length 1 3 negative && !Controls.entryRegisterClean negative r)
    "dirty-negative-entry-must-reject"
  require (negative.regs.getD r 0 == first.regs.getD r 0) "dirty-witness-preserved"
  return r

def runFixture (f : Fixture) : IO Unit := do
  let width := PackedWordRAM.wordWidth f.xs.length
  let half : Int := Int.ofNat (2^(width-1))
  if f.model == .word then
    require (width > 0 && f.xs.length < 2^width &&
      f.xs.all (fun x => -half ≤ x && x < half)) "represented-word-input-domain"
  if f.id == "L14-C-N24" || f.id == "L16-C-N83" then
    require (f.model == .comparison && f.xs.any (fun x => x < -half || half ≤ x))
      "comparison-key-outside-word-domain"
  require (f.queries.all fun q => q.1 < 2^width && q.2 < 2^width)
    "represented-query-endpoints"
  let (left,right) := f.queries.head!
  let program := (Layout.program f.model).toArray
  let fuel := 1100000000 * (f.xs.length+1) + Service.budget
  let initial := Executable.initialOwner f.model f.xs left right
  let owner := runOwner program fuel initial
  let observed := counted program fuel initial {}
  require (sameOwner owner observed.1) "counted-production-owner"
  checkCounts observed.2
  checkRetained f.xs owner
  checkAnswer f.xs left right owner
  let some (base, length) := observed.2.source
    | throw (IO.userError "actual-finalizer-entry-missing")
  require (base > 0 && length > 0 && owner.memory.size == length &&
    observed.2.counts.getD 10 0 == base)
    "actual-copy-and-release"
  require (initial.memory.size + observed.2.counts.getD 7 0 == owner.memory.size + base &&
    observed.2.counts.getD 0 0 > 0 && observed.2.counts.getD 6 0 > 0 &&
    observed.2.counts.getD 7 0 > 0) "actual-load-store-reserve-balance"
  require (observed.2.counts.getD 11 0 == (if f.model == .comparison then f.xs.length else 0))
    "actual-key-release"
  require (observed.2.counts.getD 12 0 == (if f.model == .comparison then 2 else 0))
    "actual-key-register-release"
  require (observed.2.counts.getD 5 0 == 1 && observed.2.counts.getD 13 0 == 0 &&
    observed.2.counts.getD 14 0 == 0) "initial-single-halt-no-boundary"
  require (observed.2.peak ≤ 5000000*(f.xs.length+1)) "construction-peak"
  let dirty ← if f.dirty then dirtyControl f program owner else pure 0
  let mut retained := owner
  let mut querySteps := 0
  for (l,r) in f.queries.drop 1 do
    let admission := requestProtocolArray Layout.serviceEntry l r retained
    require (admission.steps == 4 && admission.categoryCount .requestAdmission == 2 &&
      admission.categoryCount .controlEntry == 2) "charged-boundary-categories"
    let next := Executable.queryOwner f.model l r retained
    let countedQuery := counted program Service.budget admission.final {}
    require (sameOwner next countedQuery.1) "query-production-owner"
    checkCounts countedQuery.2
    require (next.memory == retained.memory) "query-same-allocation"
    require (([6,7,8,9,10,11,12].all fun i => countedQuery.2.counts.getD i 0 == 0))
      "query-no-store-allocation-keys-release"
    require (countedQuery.2.counts.getD 5 0 == 1 && countedQuery.2.steps + 4 ≤ 160257)
      "query-cost-and-single-halt"
    checkRetained f.xs next
    checkAnswer f.xs l r next
    querySteps := querySteps + countedQuery.2.steps + 4
    retained := next
  IO.println s!"LIFE1-CASE|{f.id}|PASS|steps={observed.2.steps}|queries={f.queries.length}|querySteps={querySteps}|extent={owner.memory.size}|peak={observed.2.peak}|release={base}|dirty={dirty}"

def select (args : List String) (env : Option String) : Except String (String × List Fixture) := do
  if args.length > 1 then throw "duplicate-selector"
  if !args.isEmpty && env.isSome then throw "duplicate-selector-channel"
  let selector ← match args, env with
    | [], none => pure none
    | [arg], none => pure (some arg)
    | [], some value =>
      if value.startsWith "id:" then pure (some (value.drop 3))
      else throw "selector-environment-prefix"
    | _, _ => throw "duplicate-selector"
  match selector with
  | none => pure ("full", registry)
  | some id =>
    if id.isEmpty then throw "empty-selector"
    if id.trim != id || id.trim.isEmpty then throw "whitespace-selector"
    match registry.find? (·.id == id) with
    | none => throw "unknown-selector"
    | some f => pure ("single", [f])

private def rejectedAs (args : List String) (env : Option String) (surface : String) : Bool :=
  match select args env with | .error error => error == surface | .ok _ => false

#guard rejectedAs [""] none "empty-selector"
#guard rejectedAs [] (some "id:") "empty-selector"
#guard rejectedAs [" "] none "whitespace-selector"
#guard rejectedAs [" L01-W-EMPTY"] none "whitespace-selector"
#guard rejectedAs ["UNKNOWN"] none "unknown-selector"
#guard rejectedAs ["L01-W-EMPTY", "L01-W-EMPTY"] none "duplicate-selector"
#guard rejectedAs ["L01-W-EMPTY"] (some "id:L01-W-EMPTY") "duplicate-selector-channel"
#guard rejectedAs [] (some "L01-W-EMPTY") "selector-environment-prefix"
#guard match select ["L01-W-EMPTY"] none with
  | .ok (mode, fixtures) => mode == "single" && fixtures.map (·.id) == ["L01-W-EMPTY"]
  | .error _ => false

def mainImpl (args : List String) : IO UInt32 := do
  let env ← IO.getEnv "LIFE1_VALIDATE_SELECTOR"
  if args == ["--registry"] && env.isNone then
    for f in registry do IO.println s!"LIFE1-REGISTRY|{f.id}|{modelName f.model}|{if f.dirty then "dirty-entry" else "lifecycle"}|PASS"
    return 0
  if args == ["--startup"] && env.isNone then
    require (registry.map (·.id) == requiredIds && requiredIds.eraseDups.length == 16) "registry-shape"
    let owner := Executable.initialOwner .comparison [] 0 0
    require (owner.regs.size == 8273 && owner.memory.size == 3 && owner.keyRegs.size == 2)
      "startup-finite-owner"
    IO.println "LIFE1-STARTUP|PASS|cases=16"
    return 0
  let (mode, fixtures) ← match select args env with
    | .error error => throw (IO.userError error)
    | .ok selected => pure selected
  for fixture in fixtures do runFixture fixture
  IO.println s!"LIFE1-PASS|mode={mode}|cases={fixtures.length}"
  return 0

end RMQ.Validation.PackedLifecycle

def main (args : List String) : IO UInt32 := do
  try RMQ.Validation.PackedLifecycle.mainImpl args
  catch error =>
    IO.eprintln s!"LIFE1-FAIL|{error.toString}"
    return (1 : UInt32)
