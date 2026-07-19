import RMQ.Core.WordRAM.E1CloseDispatch
import RMQ.Core.WordRAM.E1SelectCanonical

/-!
# M6: executable validation of the E1 amended machine

This is a NEW executable, separate from `rmq_succinct_classic_validate`
(which validates the list-level public API and is owned elsewhere).  What
this one does that nothing else in the tree does: it actually RUNS the
modeled WordRAM machine.  Before this harness, `E1Machine.run` had no
caller anywhere in the repository -- every machine fact was a `RunsTo`
proposition discharged in the kernel, and no instruction had ever been
executed.  Proofs and execution can only disagree if execution happens.

## The reference is INDEPENDENT

`refRMQ` below is written from the half-open leftmost-RMQ SPECIFICATION:
over `i ∈ [lo, hi)` return the index of the minimum, earliest index on
ties; `none` when the window is empty or out of bounds.  It is a direct
scan over `List Int`.  It does NOT call the route, the machine, the
Cartesian-shape construction, `SuccinctClassic`, or `RMQ.scanWindow`.  Its
only imports are the machine module's, and it uses none of them.  A
harness whose expectations come from the artifact under test proves
nothing, so the expectations here are computed from `refRMQ` alone and
`expectationTable` is materialised BEFORE any machine run happens.

## Modeled steps are NOT wall-clock

`RunResult.steps` is the machine's own modeled step count -- a property of
the abstract machine, meaningful and reproducible.  Wall-clock milliseconds
are a property of this Lean binary on this laptop and are NOT evidence
about the machine.  The report prints them in separate, separately
labelled columns and never adds or compares them.

## Deliberate mutation

`mutatedDispatchProgram` is `witnessProgram` with its `natEq` replaced by
`natLt`.  `mutationRejected` requires the checker to REJECT it.  If a
future edit made the checker vacuous, the mutation would start passing and
this harness exits 1.  A validator that cannot fail is not a validator.
-/

namespace RMQ.Validation.E1MachineValidate

open RMQ.WordRAM
open RMQ.WordRAM.E1Machine
open RMQ.WordRAM.E1CloseDispatch
open RMQ.WordRAM.E1FringeArmBlock
open RMQ.WordRAM.E1SameBlockArm

/-! ## 1. The independent reference implementation

Written from the specification of half-open leftmost RMQ.  Nothing in this
section mentions the machine, the route, or any repository construction. -/

/-- Half-open leftmost range minimum over `xs` on `[lo, hi)`.

Specification, restated: the result is `some i` where `lo ≤ i < hi`,
`xs[i]` is minimal over the window, and no `j < i` in the window attains
that minimum; the result is `none` exactly when the window is empty
(`hi ≤ lo`) or reaches past the end of `xs` (`xs.length < hi`).

The fold replaces the incumbent only on a STRICTLY smaller value, which is
what makes the answer the LEFTMOST minimiser rather than an arbitrary
one. -/
def refRMQ (xs : List Int) (lo hi : Nat) : Option Nat :=
  if hi ≤ lo then none
  else if xs.length < hi then none
  else
    ((List.range (hi - lo)).map (fun k => lo + k)).foldl
      (fun best i =>
        match best with
        | none => some i
        | some b =>
            match xs[i]?, xs[b]? with
            | some v, some bv => if v < bv then some i else some b
            | _, _ => best)
      none

/-! ## 2. Fixtures

Named structural cases first, then deterministic generated ones.  The
generator is pure modular arithmetic so the fixture set is identical on
every machine and in every run. -/

/-- A deterministic generated input; no randomness, no clock. -/
def generatedInput (len seed : Nat) : List Int :=
  (List.range len).map fun i =>
    Int.ofNat ((seed * 7 + len * 5 + i * i + 3 * i) % 11) - 5

/-- The named structural fixtures the delegation calls for. -/
def namedFixtures : List (String × List Int) :=
  [ ("empty",        [])
  , ("singleton",    [42])
  , ("size-two-inc", [1, 2])
  , ("size-two-dec", [2, 1])
  , ("all-equal",    [3, 3, 3, 3])
  , ("ties-left",    [1, 1, 2, 1])
  , ("descending",   [5, 4, 3, 2, 1])
  , ("ascending",    [1, 2, 3, 4, 5])
  , ("negatives",    [-1, -3, 0, -3, 2])
  , ("wide",         [8, 6, 7, 5, 3, 0, 9, 1, 4, 2, 6, 6]) ]

/-- Named fixtures plus a deterministic generated family. -/
def allFixtures : List (String × List Int) :=
  namedFixtures ++
    ((List.range 7).flatMap fun len =>
      (List.range 3).map fun seed =>
        (s!"gen-{len}-{seed}", generatedInput len seed))

/-- Every window over a fixture, including the INVALID ones: empty
(`lo = hi`), reversed (`hi < lo`), and past the end. -/
def windowsFor (xs : List Int) : List (Nat × Nat) :=
  let n := xs.length
  let valid :=
    (List.range (n + 1)).flatMap fun lo =>
      (List.range (n + 1 - lo)).map fun k => (lo, lo + k)
  let invalid := [(0, n + 1), (1, 0), (n + 1, n + 2), (n, n)]
  valid ++ invalid

/-! ## 3. Expectations, computed from the reference ONLY

`expectationTable` is a pure value depending on `refRMQ` and the fixtures.
It is forced and reported before any machine run in `mainImpl`. -/

/-- One expected answer, from the reference implementation. -/
structure Expectation where
  fixture : String
  xs : List Int
  lo : Nat
  hi : Nat
  expected : Option Nat
deriving Repr

/-- Every expectation, computed from `refRMQ` alone. -/
def expectationTable : List Expectation :=
  allFixtures.flatMap fun (name, xs) =>
    (windowsFor xs).map fun (lo, hi) =>
      { fixture := name, xs := xs, lo := lo, hi := hi,
        expected := refRMQ xs lo hi }

/-! ### Self-checks on the reference

The reference is the harness's yardstick, so it gets its own sanity
checks.  These are properties of the SPECIFICATION, checked by execution:
an answer, when present, must lie in the window, must be minimal over it,
and must be the earliest such index.  A reference that failed these would
silently bless a broken machine. -/

/-- The reference's answer lies inside its window and is a leftmost
minimiser, checked by brute force against every other window index. -/
def expectationSelfConsistent (e : Expectation) : Bool :=
  match e.expected with
  | none => decide (e.hi ≤ e.lo) || decide (e.xs.length < e.hi)
  | some i =>
      match e.xs[i]? with
      | none => false
      | some vi =>
          decide (e.lo ≤ i) && decide (i < e.hi) &&
            ((List.range (e.hi - e.lo)).map (fun k => e.lo + k)).all
              (fun j =>
                match e.xs[j]? with
                | none => false
                | some vj => decide (vi ≤ vj) && (decide (vi < vj) || decide (i ≤ j)))

/-- Count of expectations failing the reference self-check. -/
def referenceSelfCheckFailures : Nat :=
  (expectationTable.filter (fun e => !expectationSelfConsistent e)).length

/-! ## 4. Running the actual machine

The dispatch block needs no memory, so it runs against an empty store and
its behaviour is fully determined by the two endpoint registers.  This is
the first executable exercise of `E1Machine.run` in the repository. -/

/-- A store with nothing in it: the dispatch performs no read, so this is
the honest store for it, and any read appearing in the log would be a
defect the harness should surface. -/
def emptyStore : ReadStore := { readWord? := fun _ _ => none }

/-- Which arm the machine actually reached. -/
inductive Outcome where
  | same
  | cross
  | stuck
deriving Repr, DecidableEq, BEq

/-- The initial register file for a dispatch run: the two query endpoints
in their bank slots, everything else zero. -/
def dispatchRegs (leftClose rightClose : Nat) : RegFile := fun r =>
  if r = fClose then leftClose
  else if r = fRight then rightClose
  else 0

/-- What one machine run reports back. -/
structure RunReport where
  outcome : Outcome
  modeledSteps : Nat
  reads : Nat
deriving Repr

/-- RUN THE MACHINE on a dispatch program and classify which arm it
reached, by reading the arm's marker out of the final register file.
`witnessProgram` halts in both arms, so a `stuck` result means the machine
did not halt within fuel or left an unrecognised marker -- both defects. -/
def runDispatch (salt : Nat) (program : List Instr)
    (leftClose rightClose : Nat) : RunReport :=
  let result :=
    E1Machine.run emptyStore program (64 + salt)
      ⟨dispatchRegs leftClose rightClose, 0, false⟩
  let marker := result.final.regs dSame
  let outcome :=
    if !result.final.halted then Outcome.stuck
    else if marker = 9 then Outcome.same
    else if marker = 7 then Outcome.cross
    else Outcome.stuck
  { outcome := outcome, modeledSteps := result.steps,
    reads := result.readLog.length }

/-- The ROUTE's own dispatch condition, evaluated independently of the
machine: `ChargedFringeWiring.lean:496`. -/
def routeOutcome (blockSize leftClose rightClose : Nat) : Outcome :=
  if RMQ.SuccinctClose.blockOfClose blockSize leftClose =
      RMQ.SuccinctClose.blockOfClose blockSize rightClose then
    Outcome.same
  else
    Outcome.cross

/-- Endpoint pairs the dispatch is exercised on, chosen to straddle block
boundaries for the block sizes used below. -/
def dispatchCases : List (Nat × Nat × Nat) :=
  (List.range 5).flatMap fun bsIdx =>
    let blockSize := bsIdx + 1
    (List.range 9).flatMap fun l =>
      (List.range 9).map fun r => (blockSize, l, r)

/-- A dispatch disagreement between the machine and the route. -/
structure DispatchMismatch where
  blockSize : Nat
  leftClose : Nat
  rightClose : Nat
  machine : Outcome
  route : Outcome
deriving Repr

/-- Every case where the RUN MACHINE disagrees with the route condition,
for a given (possibly mutated) program builder. -/
def dispatchMismatches (salt : Nat) (build : Nat → List Instr) :
    List DispatchMismatch :=
  dispatchCases.filterMap fun (blockSize, l, r) =>
    let report := runDispatch salt (build blockSize) l r
    let expected := routeOutcome blockSize l r
    if report.outcome == expected then none
    else
      some { blockSize := blockSize, leftClose := l, rightClose := r,
             machine := report.outcome, route := expected }

/-- Total modeled steps over the whole dispatch sweep.  A MODELED quantity:
reproducible, machine-independent, and not a timing. -/
def dispatchModeledSteps (salt : Nat) (build : Nat → List Instr) : Nat :=
  dispatchCases.foldl
    (fun acc (blockSize, l, r) =>
      acc + (runDispatch salt (build blockSize) l r).modeledSteps)
    0

/-- Reads performed by the dispatch sweep.  Must be zero: the dispatch
block contains no `readMem`. -/
def dispatchReads (salt : Nat) (build : Nat → List Instr) : Nat :=
  dispatchCases.foldl
    (fun acc (blockSize, l, r) =>
      acc + (runDispatch salt (build blockSize) l r).reads)
    0

/-! ## 5. The deliberate mutation

A validator that cannot reject anything is decoration.  This mutation is
surgical and plausible -- exactly the kind of slip a careless edit makes --
and the harness FAILS if it is not caught. -/

/-- The honest program under test. -/
def goodDispatchProgram (blockSize : Nat) : List Instr :=
  witnessProgram blockSize

/-- MUTANT: the same-block test `natEq dSame dLB dRB` becomes
`natLt dSame dLB dRB`.  Every same-block case now falls through to the
cross arm, so the sweep must report mismatches. -/
def mutatedDispatchProgram (blockSize : Nat) : List Instr :=
  (witnessProgram blockSize).map fun instr =>
    match instr with
    | .natEq dst a b => .natLt dst a b
    | other => other

/-- The mutant differs from the honest program: the mutation is real and
actually lands somewhere in the instruction list. -/
def mutationIsReal (blockSize : Nat) : Bool :=
  goodDispatchProgram blockSize != mutatedDispatchProgram blockSize

/-- THE REJECTION CHECK: the mutant must produce at least one
machine/route disagreement.  If it produces none, the checker has gone
vacuous and the harness must fail. -/
def mutationRejected (salt : Nat) : Bool :=
  !(dispatchMismatches salt mutatedDispatchProgram).isEmpty

/-! ## 6. Structural self-checks against the proved theorems

Executable restatements of facts the kernel already proved.  Their value
is that they connect the RUNNING artifact to the PROVED one: if a future
edit changed a program's length or layout, the proof would move with it,
but these checks are computed from the running instruction lists. -/

/-- `closeDispatch_length` says four; check the running list agrees. -/
def dispatchLengthOk : Bool :=
  ((List.range 5).all fun i =>
    (closeDispatch (i + 1) 6).length == 4)

/-- `witnessProgram_length` says eight. -/
def witnessLengthOk : Bool :=
  ((List.range 5).all fun i => (witnessProgram (i + 1)).length == 8)

/-- `sameBlockLegProgram_length` says 173.  Computed here on the actual
instruction list for a real shape. -/
def sameBlockLegLengthOk : Bool :=
  let shape := Cartesian.stackCartesianShape [3, 1, 4, 1, 5]
  (E1SameBlockLeg.sameBlockLegProgram shape 5
    (RMQ.SuccinctClose.canonicalBPRelativeSummaryBlockSizeRaw shape)).length == 173

/-! ## 6b. The SAME-BLOCK LEG: executed, and its receipt compared to the route

This is the strongest check in the harness, and the one that most directly
exercises a proved theorem.

`E1SameBlockLeg.sameBlockLegProgram_runsTo_canonical` proves two things
this section re-establishes by EXECUTION rather than by kernel reduction:
that the leg runs from pc `0` to pc `173`, and that its receipt is
POSITIONALLY EQUAL to the accepted route object's trace.  The proof
asserts it; here the machine is actually run against the canonical store
and the resulting `readLog` is compared, event by event, with the route's
own `.trace` computed independently.

Neither side is derived from the other: the left side is `E1Machine.run`
folding `execInstr` over an instruction list, the right side is the route's
`TraceResult` built by `ChargedSameBlockTrace`.  They can only agree by
being right. -/

/-- The canonical store for a fixture's shape. -/
def legStore (shape : Cartesian.CartesianShape) : ReadStore :=
  SuccinctFinal.concreteBPNativeSuccinctRMQGlobalReadStore shape

/-- The segment index the same-block leg's fringe reads are logged at,
matching the layout the proof uses. -/
def legFringeSegment : Nat := 5

/-- Initial registers for a leg run: the two endpoints, everything else
zero -- exactly the `regs` the theorem quantifies over, constrained only
by `hClose` and `hRight`. -/
def legRegs (leftClose rightClose : Nat) : RegFile := fun r =>
  if r = fClose then leftClose
  else if r = fRight then rightClose
  else 0

/-- What one same-block leg run reports. -/
structure LegReport where
  reachedExit : Bool
  modeledSteps : Nat
  machineReads : Nat
  routeTraceLen : Nat
  receiptMatchesRoute : Bool
deriving Repr

/-- RUN THE SAME-BLOCK LEG and compare its receipt against the route.
`build` lets the caller substitute a mutated program while holding
everything else fixed. -/
def runSameBlockLeg (salt : Nat) (build : List Instr → List Instr)
    (xs : List Int) (leftClose rightClose : Nat) : LegReport :=
  let shape := Cartesian.stackCartesianShape xs
  let blockSize := SuccinctClose.canonicalBPRelativeSummaryBlockSizeRaw shape
  let store := legStore shape
  let program :=
    build (E1SameBlockLeg.sameBlockLegProgram shape legFringeSegment blockSize)
  let result :=
    E1Machine.run store program (40000 + salt)
      ⟨legRegs leftClose rightClose, 0, false⟩
  let routeTrace :=
    (SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegmentWithStore
      shape (SuccinctFinal.concreteBPNativeChunkedRankCloseGlobalWordTraceResult shape)
      legFringeSegment store blockSize leftClose rightClose).trace
  { reachedExit := result.final.pc == 173
    modeledSteps := result.steps
    machineReads := result.readLog.length
    routeTraceLen := routeTrace.length
    receiptMatchesRoute := result.readLog == routeTrace }

/-- Fixtures and windows the leg is exercised on.  Kept modest because
each case runs the machine for hundreds of modeled steps against a store
that rebuilds its directory per read. -/
def legCases : List (List Int × Nat × Nat) :=
  ([2, 3, 5, 8, 12].flatMap fun len =>
    [0, 1].flatMap fun seed =>
      let xs := generatedInput len seed
      ([0, 1, 2].flatMap fun l =>
        [0, 1, 2].map fun d => (xs, l, l + d))).flatMap fun c => [c]

/-- The honest leg program: identity. -/
def goodLeg : List Instr → List Instr := id

/-- MUTANT: the fold's back edge `brNZ fCnt 97` becomes `brNZ fCnt 98`,
skipping the first instruction of the fringe prefix on every iteration.
This is a genuinely nasty mutation -- it does NOT change the program's
length, and it does NOT stop the leg from reaching its exit pc 173, so an
exit-pc-only check would MISS it entirely.  The receipt comparison catches
it.  That is precisely why the harness compares receipts and not just
control flow. -/
def mutatedLeg (program : List Instr) : List Instr :=
  program.map fun instr =>
    match instr with
    | .brNZ cond 97 => .brNZ cond 98
    | other => other

/-- Leg runs whose receipt disagrees with the route, for a given builder. -/
def legReceiptMismatches (salt : Nat) (build : List Instr → List Instr) : Nat :=
  (legCases.filter fun (xs, l, r) =>
    !(runSameBlockLeg salt build xs l r).receiptMatchesRoute).length

/-- Leg runs that fail to reach the proved exit pc 173. -/
def legExitFailures (salt : Nat) (build : List Instr → List Instr) : Nat :=
  (legCases.filter fun (xs, l, r) =>
    !(runSameBlockLeg salt build xs l r).reachedExit).length

/-- Total modeled steps across the leg sweep: a MODELED quantity. -/
def legModeledSteps (salt : Nat) (build : List Instr → List Instr) : Nat :=
  legCases.foldl (fun acc (xs, l, r) =>
    acc + (runSameBlockLeg salt build xs l r).modeledSteps) 0

/-- Total modeled read events across the leg sweep. -/
def legModeledReads (salt : Nat) (build : List Instr → List Instr) : Nat :=
  legCases.foldl (fun acc (xs, l, r) =>
    acc + (runSameBlockLeg salt build xs l r).machineReads) 0

/-- The leg mutation must be REJECTED by the receipt comparison. -/
def legMutationRejected (salt : Nat) : Bool :=
  legReceiptMismatches salt mutatedLeg > 0

/-- The leg mutation genuinely changes the instruction list. -/
def legMutationIsReal : Bool :=
  let shape := Cartesian.stackCartesianShape (generatedInput 5 0)
  let blockSize := SuccinctClose.canonicalBPRelativeSummaryBlockSizeRaw shape
  let program :=
    E1SameBlockLeg.sameBlockLegProgram shape legFringeSegment blockSize
  program != mutatedLeg program

/-! ## 6c. The SELECT-CLOSE LEG: executed, and its receipt compared

`E1SelectCanonical.selectCloseBlock_runsTo_canonical` proves the
405-instruction select dispatch runs `A -> A + 405` against the canonical
store with receipts positionally equal to
`(concreteBPNativeChunkedSelectCloseGlobalWordTraceResult shape idx).trace`.
Hosted at base `0`, that is directly executable, so the same
proof-vs-execution differential applies. -/

/-- The accepted select-close data at a shape.  `E1SelectCanonical`'s own
`selData` is `private`, so the definition is repeated here verbatim from
`E1SelectCanonical.lean:41` rather than reached into. -/
def selectData (shape : Cartesian.CartesianShape) :=
  GenericSelect.sparseExceptionSelectData shape.bpCode false

/-- The select-close leg hosted at base `0`. -/
def selectLegProgram (shape : Cartesian.CartesianShape) : List Instr :=
  E1SelectDispatch.selectCloseBlockAt (selectData shape)
    SuccinctFinal.concreteBPNativeSelectCloseTraceSegmentLayout 0
    SuccinctFinal.concreteBPNativeRankCloseTraceSegmentBase
    SuccinctFinal.concreteBPNativeSelectChunkTraceSegment
    (SuccinctClose.bpFringeChunkBits shape.bpCode.length)

/-- What one select-leg run reports. -/
structure SelectReport where
  reachedExit : Bool
  modeledSteps : Nat
  machineReads : Nat
  routeTraceLen : Nat
  receiptMatchesRoute : Bool
deriving Repr

/-- RUN THE SELECT LEG and compare its receipt against the route. -/
def runSelectLeg (salt : Nat) (build : List Instr → List Instr)
    (xs : List Int) (idx : Nat) : SelectReport :=
  let shape := Cartesian.stackCartesianShape xs
  let store := legStore shape
  let program := build (selectLegProgram shape)
  let regs : RegFile := fun r => if r = E1SelectBridge.xIdx then idx else 0
  let result := E1Machine.run store program (40000 + salt) ⟨regs, 0, false⟩
  let routeTrace :=
    (SuccinctFinal.concreteBPNativeChunkedSelectCloseGlobalWordTraceResult
      shape idx).trace
  { reachedExit := result.final.pc == 405
    modeledSteps := result.steps
    machineReads := result.readLog.length
    routeTraceLen := routeTrace.length
    receiptMatchesRoute := result.readLog == routeTrace }

/-- Fixtures and occurrence indices the select leg is exercised on. -/
def selectCases : List (List Int × Nat) :=
  [2, 3, 5, 8].flatMap fun len =>
    [0, 1].flatMap fun seed =>
      let xs := generatedInput len seed
      [0, 1, 2, 3].map fun idx => (xs, idx)

/-- The honest select program. -/
def goodSelect : List Instr → List Instr := id

/-- Select-leg runs whose receipt disagrees with the route. -/
def selectReceiptMismatches (salt : Nat) (build : List Instr → List Instr) : Nat :=
  (selectCases.filter fun (xs, i) =>
    !(runSelectLeg salt build xs i).receiptMatchesRoute).length

/-- Select-leg runs failing to reach the proved exit pc 405. -/
def selectExitFailures (salt : Nat) (build : List Instr → List Instr) : Nat :=
  (selectCases.filter fun (xs, i) =>
    !(runSelectLeg salt build xs i).reachedExit).length

/-- Total modeled steps across the select sweep. -/
def selectModeledSteps (salt : Nat) (build : List Instr → List Instr) : Nat :=
  selectCases.foldl (fun acc (xs, i) =>
    acc + (runSelectLeg salt build xs i).modeledSteps) 0

/-- Total modeled read events across the select sweep. -/
def selectModeledReads (salt : Nat) (build : List Instr → List Instr) : Nat :=
  selectCases.foldl (fun acc (xs, i) =>
    acc + (runSelectLeg salt build xs i).machineReads) 0

/-! ## 7. THE HOLE: whole-query comparison

DELIBERATELY NOT IMPLEMENTED, and compiling as a hole rather than as a
passing check, so nobody mistakes it for evidence.

The whole-query comparison -- run the machine end to end on a fixture and
compare its answer against `refRMQ` -- cannot be written yet.  It needs
the INTERIOR leg, which is blocked on the `bpSparseLogSpan` /
`Nat.log2` decision recorded in `docs/internal/E1_WORKLOG.md` (M3d-3
section 2): `bpSparseLogSpan blockCount = 2 ^ Nat.log2 blockCount`
(`EndpointFringe/PrefixRange/SparseArgMin.lean:598`) is evaluated on a
RUNTIME-derived `blockCount` and feeds an accepted read address, so no
constant immediate encodes it.

Until that is adjudicated there is no whole-query program to run, and this
harness reports the hole as OPEN rather than reporting a vacuous pass. -/

/-- Status of the whole-query comparison.  `false` means "not yet
attachable", which is the honest state today. -/
def wholeQueryComparisonAvailable : Bool := false

/-- The attachment point.  When the interior leg unblocks, this becomes
the end-to-end differential: build the whole-query program, run it on each
fixture, and compare the answer register against `e.expected`.  It returns
`none` today because the program does not exist -- NOT because the machine
agreed with the reference. -/
def wholeQueryMismatches : Option (List Expectation) :=
  if wholeQueryComparisonAvailable then
    -- Attach here: run the whole-query machine per expectation and keep
    -- the disagreements.  Unreachable until the interior leg lands.
    some []
  else
    none

/-! ## 8. Report -/

/-- Render an outcome for the report. -/
def outcomeName : Outcome → String
  | .same => "same"
  | .cross => "cross"
  | .stuck => "STUCK"

def renderMismatch (m : DispatchMismatch) : String :=
  s!"    blockSize={m.blockSize} left={m.leftClose} right={m.rightClose} " ++
    s!"machine={outcomeName m.machine} route={outcomeName m.route}"

/-! ### Why the sweeps take a `salt`

Getting an honest wall-clock number out of this harness took three tries,
and the failure mode is worth recording because it is silent.

A sweep like `legModeledSteps mutatedLeg` is a CLOSED term: no free
variables, no runtime input.  Lean lifts such terms to top-level constants
that are evaluated once, which means the work can happen before `main`
ever runs -- so bracketing the call with `IO.monoMsNow` measured nothing
and the harness confidently printed `0 ms` for phases that really took
seconds.  Forcing the value inside the bracket did not help, because the
value was already computed.

Threading a runtime-obtained `salt` makes each sweep depend on an input
that cannot be known until execution, so it is evaluated where it is
called.  `salt` is added to the FUEL, which is already generous, so a
salt of `0` -- what `mainImpl` always passes -- changes no result, only
when the work happens.

The modeled step counts were never affected by any of this; only the
wall-clock numbers were, which is exactly the reason the report keeps the
two in separate columns and calls the wall-clock non-evidence. -/

def mainImpl : IO UInt32 := do
  IO.println "== E1 amended-machine validator (M6) =="
  IO.println ""
  -- A runtime-derived zero. See the note above `mainImpl` on why the
  -- sweeps take a salt: without it Lean evaluates them before `main`
  -- starts and every wall-clock reading is a meaningless 0.
  let clock <- IO.monoMsNow
  let salt := clock * 0

  -- STEP 1: the reference and its expectations, BEFORE any machine run.
  IO.println "-- phase 1: independent reference (no machine involved) --"
  let expectations := expectationTable
  let refFailures := referenceSelfCheckFailures
  IO.println s!"fixtures={allFixtures.length}"
  IO.println s!"expectations={expectations.length}"
  IO.println s!"expectationsNone={(expectations.filter (fun e => e.expected.isNone)).length}"
  IO.println s!"expectationsSome={(expectations.filter (fun e => e.expected.isSome)).length}"
  IO.println s!"referenceSelfCheckFailures={refFailures}"
  IO.println ""

  -- STEP 2: structural self-checks against proved lengths.
  IO.println "-- phase 2: structural self-checks --"
  IO.println s!"dispatchLengthOk={dispatchLengthOk}"
  IO.println s!"witnessLengthOk={witnessLengthOk}"
  IO.println s!"sameBlockLegLengthOk={sameBlockLegLengthOk}"
  IO.println ""

  -- STEP 3: run the machine. Modeled steps and wall-clock are reported
  -- separately and never combined.
  IO.println "-- phase 3: machine execution vs route (modeled vs wall-clock) --"
  let t0 <- IO.monoMsNow
  let mismatches := dispatchMismatches salt goodDispatchProgram
  let modeled := dispatchModeledSteps salt goodDispatchProgram
  let reads := dispatchReads salt goodDispatchProgram
  IO.println s!"dispatchCases={dispatchCases.length}"
  IO.println s!"modeledSteps={modeled}   (machine-modeled, reproducible)"
  IO.println s!"modeledReads={reads}   (must be 0: dispatch performs no readMem)"
  IO.println s!"dispatchMismatches={mismatches.length}"
  let t1 <- IO.monoMsNow
  IO.println s!"dispatchWallClockMs={t1 - t0}   (this binary on this host; NOT evidence)"
  for m in mismatches.take 10 do
    IO.println (renderMismatch m)
  IO.println ""

  -- STEP 3b: the same-block leg, executed, receipt compared to the route.
  IO.println "-- phase 3b: same-block LEG execution vs route receipt --"
  let tl0 <- IO.monoMsNow
  let legExitFails := legExitFailures salt goodLeg
  let legReceiptFails := legReceiptMismatches salt goodLeg
  let legSteps := legModeledSteps salt goodLeg
  let legReads := legModeledReads salt goodLeg
  IO.println s!"legCases={legCases.length}"
  IO.println s!"legExitFailures={legExitFails}   (proved exit is pc 173)"
  IO.println s!"legReceiptMismatches={legReceiptFails}   (machine readLog vs route trace)"
  IO.println s!"legModeledSteps={legSteps}   (machine-modeled, reproducible)"
  IO.println s!"legModeledReads={legReads}   (machine-modeled receipt events)"
  let tl1 <- IO.monoMsNow
  IO.println s!"legWallClockMs={tl1 - tl0}   (this binary on this host; NOT evidence)"
  IO.println ""

  -- STEP 3c: the select-close leg, executed, receipt compared to the route.
  IO.println "-- phase 3c: select-close LEG execution vs route receipt --"
  let ts0 <- IO.monoMsNow
  let selExitFails := selectExitFailures salt goodSelect
  let selReceiptFails := selectReceiptMismatches salt goodSelect
  let selSteps := selectModeledSteps salt goodSelect
  let selReads := selectModeledReads salt goodSelect
  IO.println s!"selectCases={selectCases.length}"
  IO.println s!"selectExitFailures={selExitFails}   (proved exit is pc 405)"
  IO.println s!"selectReceiptMismatches={selReceiptFails}   (machine readLog vs route trace)"
  IO.println s!"selectModeledSteps={selSteps}   (machine-modeled, reproducible)"
  IO.println s!"selectModeledReads={selReads}   (machine-modeled receipt events)"
  let ts1 <- IO.monoMsNow
  IO.println s!"selectWallClockMs={ts1 - ts0}   (this binary on this host; NOT evidence)"
  IO.println ""

  -- STEP 4: the mutation must be rejected.
  IO.println "-- phase 4: deliberate mutation --"
  let tm0 <- IO.monoMsNow
  let mutantMismatches := dispatchMismatches salt mutatedDispatchProgram
  let rejected := mutationRejected salt
  IO.println s!"mutationIsReal={mutationIsReal 3}"
  IO.println s!"mutantMismatches={mutantMismatches.length}   (must be > 0)"
  IO.println s!"mutationRejected={rejected}"
  let tm1 <- IO.monoMsNow
  IO.println s!"mutationWallClockMs={tm1 - tm0}"
  for m in mutantMismatches.take 5 do
    IO.println (renderMismatch m)
  IO.println ""

  -- STEP 4b: mutating a REAL machine component (the same-block leg).
  IO.println "-- phase 4b: deliberate mutation of the same-block LEG --"
  let tlm0 <- IO.monoMsNow
  let legMutExitFails := legExitFailures salt mutatedLeg
  let legMutReceiptFails := legReceiptMismatches salt mutatedLeg
  let legMutSteps := legModeledSteps salt mutatedLeg
  IO.println s!"legMutationIsReal={legMutationIsReal}"
  IO.println s!"legMutantExitFailures={legMutExitFails}   (0 expected: exit pc alone MISSES this mutation)"
  IO.println s!"legMutantReceiptMismatches={legMutReceiptFails}   (must be > 0: the receipt catches it)"
  IO.println s!"legMutantModeledSteps={legMutSteps}   (vs honest {legSteps})"
  IO.println s!"legMutationRejected={legMutationRejected salt}"
  let tlm1 <- IO.monoMsNow
  IO.println s!"legMutationWallClockMs={tlm1 - tlm0}"
  IO.println ""

  -- STEP 5: the hole.
  IO.println "-- phase 5: whole-query comparison --"
  IO.println s!"wholeQueryComparisonAvailable={wholeQueryComparisonAvailable}"
  match wholeQueryMismatches with
  | none =>
      IO.println "wholeQueryComparison=OPEN (interior leg blocked; NOT a pass)"
  | some ms =>
      IO.println s!"wholeQueryMismatches={ms.length}"
  IO.println ""

  -- Verdict.
  let ok :=
    refFailures == 0 && dispatchLengthOk && witnessLengthOk &&
      sameBlockLegLengthOk && mismatches.isEmpty && reads == 0 &&
      mutationIsReal 3 && rejected &&
      legExitFails == 0 && legReceiptFails == 0 &&
      legMutationIsReal && legMutationRejected salt &&
      selExitFails == 0 && selReceiptFails == 0
  if ok then
    IO.println "RESULT: PASS (with the whole-query comparison still OPEN)"
    return 0
  else
    IO.println "RESULT: FAIL"
    return 1

end RMQ.Validation.E1MachineValidate

def main : IO UInt32 := RMQ.Validation.E1MachineValidate.mainImpl
