import RMQ.Core.WordRAM.Construction.ArrayRun
import RMQ.Core.WordRAM.Construction.Builder.Program
import RMQ.Core.WordRAM.Packed.QueryObservations
import RMQ.Core.WordRAM.Packed.ArrayRun

/-! Executable validation of the production PRE-1 builder constants.

Every fixture runs the actual constants `builderProgram` (comparison-oracle
input) and `builderProgramWord` (word input at `wordWidth n`) on the
array-backed interpreter `runArray` at fuel `builderBudget n`, which
`runArray_abstract` proves equal to the mathematical run for programs whose
register operands are below 400 (`builderProgram_registersBelow`). Expected
cells come only from the reference `buildMemory xs`, expected query answers
only from `scanWindow`. Each fixture checks: the run halts; the cells from the
halt value to the extent equal `buildMemory xs`; `steps ≤ 1000000000 * n +
1000000000`; the temporary region below the halt value has at most
`3200000 * n + 3200000` cells; every write addresses at least the initial
extent; the accepted query program, run by the packed array interpreter on the
emitted list, returns the reference answer on three endpoint pairs and 0 on a
reversed pair. The negative controls run only when selected and must fail with
their pinned message: a missing input header, the allocation of a list with a
different Cartesian shape (the negated input) as the expected list, a
mismatched allocation (two cells swapped), and write-unit confusion (the dense
words replaced by their bit cells). -/

namespace RMQ.Validation.Preprocessing

open RMQ.SuccinctFinal

inductive Kind where
  | positive
  | missingHeader
  | wrongExpected
  | swappedCells
  | bitCells
deriving BEq

structure Fixture where
  id : String
  xs : List Int
  kind : Kind := .positive

/-- `crossBlockInput` of `RMQ.Validation.PackedQueryRuntime`, restated literally. -/
def crossBlockInput : List Int := [9, 7, 8, 6, 5, 2, 8, 7, 6, 2, 4, 9]

/-- For this family the serialized length equals the dense length at `n = 83`
(BUILDER_STAGE_LOG.md S6-11): the pad block's probe cell stays after the buffer.
The next such size, `n = 1116`, is not a fixture: the reference `buildMemory`
alone does not finish within ten minutes there. -/
def edgeInput (n : Nat) : List Int := (List.range n).map fun i => ((i * 37 + 11) % 13 : Nat) - 6

def fixtures : List Fixture := [
  ⟨"P01-EMPTY", [], .positive⟩,
  ⟨"P02-SINGLE", [7], .positive⟩,
  ⟨"P03-TWO", [3, 1], .positive⟩,
  ⟨"P04-THREE-TIE", [2, 2, 1], .positive⟩,
  ⟨"P05-LEFTMOST-TIE", [4, -3, -3, 8], .positive⟩,
  ⟨"P06-INCREASING", (List.range 24).map Int.ofNat, .positive⟩,
  ⟨"P07-DECREASING", (List.range 24).reverse.map Int.ofNat, .positive⟩,
  ⟨"P08-EQUAL", List.replicate 24 5, .positive⟩,
  ⟨"P09-CROSS-BLOCK", crossBlockInput, .positive⟩,
  ⟨"P10-DENSE-EDGE-83", edgeInput 83, .positive⟩,
  ⟨"P11-THRESHOLD-129", (List.range 129).map fun i => ((i * 7919 % 211 : Nat) : Int) - 100, .positive⟩]

def requiredIDs : List String := [
  "P01-EMPTY", "P02-SINGLE", "P03-TWO", "P04-THREE-TIE", "P05-LEFTMOST-TIE", "P06-INCREASING",
  "P07-DECREASING", "P08-EQUAL", "P09-CROSS-BLOCK", "P10-DENSE-EDGE-83", "P11-THRESHOLD-129"]

def negativeFixtures : List Fixture := [
  ⟨"N01-MISSING-HEADER", [4, -3, -3, 8], .missingHeader⟩,
  ⟨"N02-WRONG-EXPECTED", [4, -3, -3, 8], .wrongExpected⟩,
  ⟨"N03-MISMATCHED-ALLOCATION", [4, -3, -3, 8], .swappedCells⟩,
  ⟨"N04-WRITE-UNIT-CONFUSION", [4, -3, -3, 8], .bitCells⟩]

def negativeIDs : List String :=
  ["N01-MISSING-HEADER", "N02-WRONG-EXPECTED", "N03-MISMATCHED-ALLOCATION", "N04-WRITE-UNIT-CONFUSION"]

def selectorVariable : String := "PRE1_VALIDATE_SELECTOR"

def registerBank : Nat := 400

def check (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

/-- Signed and header representability at width `W` (`InputFits`, decided). -/
def wordFits (W : Nat) (xs : List Int) : Bool :=
  decide (0 < W) && decide (xs.length < 2 ^ W) &&
    xs.all fun x => decide (-((2 ^ (W - 1) : Nat) : Int) ≤ x) && decide (x < ((2 ^ (W - 1) : Nat) : Int))

/-- The cells from the halt value to the extent of an array run, if it halted. -/
def emittedCells (r : PackedConstruction.ArrayRun) : Option (Nat × List Nat) :=
  match r.final.status with
  | .halted outBase =>
      some (outBase, (List.range (r.final.memory.size - outBase)).map fun k =>
        (r.final.memory.getD (outBase + k) none).getD 0)
  | _ => none

/-- `xs` with the two cells at positions `i` and `j` swapped. -/
def swapCells (cells : List Nat) (i j : Nat) : List Nat :=
  (List.range cells.length).map fun k =>
    if k = i then cells.getD j 0 else if k = j then cells.getD i 0 else cells.getD k 0

/-- The reference allocation with its dense words written as their `W` bit cells. -/
def bitCellAllocation (xs : List Int) : List Nat :=
  let W := PackedWordRAM.wordWidth xs.length
  let cells := PackedWordRAM.buildMemory xs
  cells.take 174 ++ (cells.drop 174).flatMap fun word => (List.range W).map fun b => word / 2 ^ b % 2

def expectedCells (fixture : Fixture) : List Nat :=
  let reference := PackedWordRAM.buildMemory fixture.xs
  match fixture.kind with
  | .wrongExpected => PackedWordRAM.buildMemory (fixture.xs.map (- ·))
  | .swappedCells => swapCells reference 174 175
  | .bitCells => bitCellAllocation fixture.xs
  | _ => reference

def specPacket (xs : List Int) (left right : Nat) : Nat :=
  if left < right ∧ right ≤ xs.length then RMQ.scanWindow xs left (right - left) + 1 else 0

def checkQuery (id : String) (xs : List Int) (cells : List Nat) : IO Unit := do
  let n := xs.length
  let program := PackedWordRAM.queryProgram.toArray
  let pairs : List (Nat × Nat) := [(0, n), (n / 3, 2 * n / 3 + 1), (1, n), (n, 0)]
  for (left, right) in pairs do
    let r := PackedWordRAM.runArray cells program PackedWordRAM.queryBudget
      (PackedWordRAM.initialState n left right)
    check (r.result == some (specPacket xs left right))
      (id ++ ": query result mismatch at (" ++ toString left ++ ", " ++ toString right ++ ")")

/-- One builder run: halting, emitted cells, work, workspace, input ownership. -/
def checkBuild (id model : String) (xs : List Int) (program : Array PackedConstruction.BInstr)
    (start : PackedConstruction.ExecState) (extent0 : Nat) (expected : List Nat) : IO (List Nat) := do
  let n := xs.length
  let r := PackedConstruction.runArray program (PackedConstruction.builderBudget n) start
  match emittedCells r with
  | none => throw (IO.userError (id ++ " " ++ model ++ ": builder did not halt"))
  | some (outBase, cells) =>
      check (cells == expected) (id ++ " " ++ model ++ ": emitted cells differ from the expected allocation")
      check (r.steps ≤ 1000000000 * n + 1000000000) (id ++ " " ++ model ++ ": work bound exceeded")
      check (extent0 ≤ outBase && outBase - extent0 ≤ 3200000 * n + 3200000)
        (id ++ " " ++ model ++ ": workspace bound exceeded")
      check (r.writes.all fun e => extent0 ≤ e.1) (id ++ " " ++ model ++ ": a write addresses an input cell")
      IO.println ("PRE1-VALIDATE " ++ id ++ " " ++ model ++ " steps=" ++ toString r.steps ++
        " cells=" ++ toString cells.length ++ " temporary=" ++ toString (outBase - extent0) ++
        " writes=" ++ toString r.writes.length)
      pure cells

def runFixture (fixture : Fixture) : IO Unit := do
  let xs := fixture.xs
  let n := xs.length
  let expected := expectedCells fixture
  let comparisonStart :=
    if fixture.kind == .missingHeader then
      { PackedConstruction.ExecState.ofComparisonInput registerBank xs with memory := #[] }
    else PackedConstruction.ExecState.ofComparisonInput registerBank xs
  let cells ← checkBuild fixture.id "comparison" xs PackedConstruction.builderProgram.toArray
    comparisonStart 1 expected
  checkQuery fixture.id xs cells
  let W := PackedWordRAM.wordWidth n
  if wordFits W xs then
    let wordCells ← checkBuild fixture.id "word" xs PackedConstruction.builderProgramWord.toArray
      (PackedConstruction.ExecState.ofWordInput registerBank W xs) (n + 1) expected
    check (wordCells == cells) (fixture.id ++ ": the two constants emitted different cells")
  IO.println ("PRE1-VALIDATE CASE " ++ fixture.id ++ " PASS")

def findFixture (id : String) : IO Fixture := do
  if id.trim.isEmpty then throw (IO.userError "PRE1-VALIDATE explicitly empty selector")
  match (fixtures ++ negativeFixtures).find? (fun fixture => fixture.id == id) with
  | none => throw (IO.userError ("PRE1-VALIDATE unknown selector: " ++ id))
  | some fixture => pure fixture

/-- A selector arrives either as the only argument or through
`PRE1_VALIDATE_SELECTOR` spelled `id:<ID>`. -/
def selection (args : List String) : IO (Option Fixture) := do
  let channel ← IO.getEnv selectorVariable
  match args, channel with
  | [], none => pure none
  | [id], none => some <$> findFixture id
  | [], some value =>
      if value.startsWith "id:" then some <$> findFixture (value.drop 3)
      else throw (IO.userError "PRE1-VALIDATE malformed selector channel")
  | _ :: _, some _ => throw (IO.userError "PRE1-VALIDATE selector given twice")
  | _, _ => throw (IO.userError "PRE1-VALIDATE expects zero or one selector")

def mainImpl (args : List String) : IO Unit := do
  check (fixtures.map (·.id) == requiredIDs) "PRE1-VALIDATE registry mismatch, missing or duplicate case"
  check (negativeFixtures.map (·.id) == negativeIDs) "PRE1-VALIDATE negative registry mismatch"
  check (negativeIDs.all fun id => !requiredIDs.contains id) "PRE1-VALIDATE negative control in full registry"
  let chosen ← selection args
  let selected := match chosen with | none => fixtures | some fixture => [fixture]
  for fixture in selected do
    runFixture fixture
  let mode := if chosen.isNone then "full" else "selected"
  IO.println ("PRE1-VALIDATE PASS cases=" ++ toString selected.length ++ " mode=" ++ mode)

end RMQ.Validation.Preprocessing

def main (args : List String) : IO Unit := RMQ.Validation.Preprocessing.mainImpl args

/-! Axiom inventory of the validator declarations. -/

#print axioms RMQ.Validation.Preprocessing.Kind
#print axioms RMQ.Validation.Preprocessing.Fixture
#print axioms RMQ.Validation.Preprocessing.crossBlockInput
#print axioms RMQ.Validation.Preprocessing.edgeInput
#print axioms RMQ.Validation.Preprocessing.fixtures
#print axioms RMQ.Validation.Preprocessing.requiredIDs
#print axioms RMQ.Validation.Preprocessing.negativeFixtures
#print axioms RMQ.Validation.Preprocessing.negativeIDs
#print axioms RMQ.Validation.Preprocessing.selectorVariable
#print axioms RMQ.Validation.Preprocessing.registerBank
#print axioms RMQ.Validation.Preprocessing.check
#print axioms RMQ.Validation.Preprocessing.wordFits
#print axioms RMQ.Validation.Preprocessing.emittedCells
#print axioms RMQ.Validation.Preprocessing.swapCells
#print axioms RMQ.Validation.Preprocessing.bitCellAllocation
#print axioms RMQ.Validation.Preprocessing.expectedCells
#print axioms RMQ.Validation.Preprocessing.specPacket
#print axioms RMQ.Validation.Preprocessing.checkQuery
#print axioms RMQ.Validation.Preprocessing.checkBuild
#print axioms RMQ.Validation.Preprocessing.runFixture
#print axioms RMQ.Validation.Preprocessing.findFixture
#print axioms RMQ.Validation.Preprocessing.selection
#print axioms RMQ.Validation.Preprocessing.mainImpl
#print axioms main
