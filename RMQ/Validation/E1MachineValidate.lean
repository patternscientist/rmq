import RMQ.Core.WordRAM.E1CloseCompose
import RMQ.Core.WordRAM.E1SelectCanonical
import RMQ.Core.WordRAM.E1CandMerge3

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

/-! ## 6d. THE COMPOSITE: dispatch ∘ rebased same-block leg, executed

`E1CloseCompose.sameBlockDispatchProgram_runsTo` proves that the four
instruction dispatch followed by the REBASED same-block leg runs
`0 -> 4 + crossArm.length + 173` on the route's own same-block condition,
reproducing the route's trace.  With the dispatch module's two-instruction
witness cross arm that exit is the concrete `179`, and the leg is hosted
at `6` -- so its internal fold back edge targets `103`, not `97`.

This phase executes that composite.  It is a STRICTLY stronger test than
phase 3b, because 3b runs the leg at base `0`, where every absolute
internal target happens to be correct by accident.

Two things are checked, and they are different in kind:

* SAME-BLOCK cases: the branch is taken, the machine must reach `179`, and
  its `readLog` must equal the route's same-block trace event for event.
  Since the dispatch performs no read, the composite's receipt must equal
  the LEG's receipt exactly -- so this also checks the dispatch is
  read-free in situ, not merely by inspection of its opcodes.
* CROSS-BLOCK cases: the branch is not taken and the machine must halt in
  the witness cross arm having read nothing.  This does NOT validate the
  route's cross-block VALUE -- there is no cross-block machine arm yet
  (its interior leg is blocked).  It validates only that the composite
  selects the fall-through and that the leg is genuinely skipped. -/

/-- The honest composite: dispatch at `0`, witness cross arm at `4`, the
REBASED leg at `6`. -/
def goodCompose (shape : Cartesian.CartesianShape) (blockSize : Nat) :
    List Instr :=
  E1CloseCompose.sameBlockDispatchProgram shape legFringeSegment blockSize
    E1CloseDispatch.witnessCrossArm

/-- MUTANT A -- THE REBASING DEFECT ITSELF: host the BASE-0 leg layout at
base `6`, i.e. forget to rebase the leg's four internal addresses.  This
is the exact bug `sameBlockLegProgramAt` exists to prevent, and it is what
a careless composition would produce.  It preserves the program's LENGTH
(both layouts are 173 instructions), so a length check cannot see it. -/
def mutatedComposeUnrebased (shape : Cartesian.CartesianShape)
    (blockSize : Nat) : List Instr :=
  E1CloseDispatch.closeDispatchProgram blockSize
    E1CloseDispatch.witnessCrossArm
    (E1SameBlockLeg.sameBlockLegProgram shape legFringeSegment blockSize)

/-- MUTANT B -- ONE TARGET LEFT BEHIND: rebase everything EXCEPT the fold
back edge, sending it to the base-`0` address `97` instead of `103`.  A
single operand differs from the honest program: same length, same
instruction count, same opcodes.  This is the composite-level analogue of
the phase-4b back-edge mutation and is the sharpest test in the harness. -/
def mutatedComposeBackEdge (shape : Cartesian.CartesianShape)
    (blockSize : Nat) : List Instr :=
  (goodCompose shape blockSize).map fun instr =>
    match instr with
    | .brNZ cond 103 => .brNZ cond 97
    | other => other

/-- What one composite run reports.  `routeSame` is an EXPECTATION: it is
computed from the route's own condition with no machine involved. -/
structure ComposeReport where
  routeSame : Bool
  reachedLegExit : Bool
  haltedInCrossArm : Bool
  modeledSteps : Nat
  machineReads : Nat
  routeTraceLen : Nat
  receiptMatchesRoute : Bool
deriving Repr

/-- Fuel for an HONEST composite run.  Generous: the honest leg completes
in a few hundred modeled steps, and phase 3d prints the observed maximum
so this margin is checkable rather than asserted. -/
def composeFuel : Nat := 40000

/-- Fuel for a MUTANT composite run, and the reason it is smaller.

A mis-rebased leg does not merely compute a wrong answer.  Its fold back
edge jumps to an address that never re-establishes the loop's exit
condition, so the machine runs until fuel is exhausted.  At the honest
budget that made the two mutant sweeps hundreds of times more expensive
than the honest one, and the first version of this phase did not finish in
ten minutes.

Fuel exhaustion is REJECTION, not a pass: a mutant that runs out of fuel
neither reaches the proved exit pc nor reproduces the route's receipt, so
the very same tests the honest run must satisfy count it as a mismatch.
Lowering the mutant budget therefore weakens nothing -- it only bounds the
cost of exhibiting a failure that has already occurred.

The choice is not left to trust: `composeMutantFuelIsSlack` below checks
that this budget strictly exceeds the largest honest run, so a correct
program could never be failed by it. -/
def composeMutantFuel : Nat := 6000

/-- RUN THE COMPOSITE and compare against independently computed
expectations.  The route condition and the route trace are both derived
BEFORE the program is built or run. -/
def runComposeFuel (fuel : Nat) (salt : Nat)
    (build : Cartesian.CartesianShape → Nat → List Instr)
    (xs : List Int) (leftClose rightClose : Nat) : ComposeReport :=
  let shape := Cartesian.stackCartesianShape xs
  let blockSize := SuccinctClose.canonicalBPRelativeSummaryBlockSizeRaw shape
  let store := legStore shape
  -- EXPECTATIONS FIRST, from the route alone.
  let routeSame :=
    SuccinctClose.blockOfClose blockSize leftClose ==
      SuccinctClose.blockOfClose blockSize rightClose
  let routeTrace :=
    (SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegmentWithStore
      shape (SuccinctFinal.concreteBPNativeChunkedRankCloseGlobalWordTraceResult shape)
      legFringeSegment store blockSize leftClose rightClose).trace
  -- ONLY NOW the machine.
  let program := build shape blockSize
  let result :=
    E1Machine.run store program (fuel + salt)
      ⟨legRegs leftClose rightClose, 0, false⟩
  { routeSame := routeSame
    reachedLegExit := result.final.pc == 179
    haltedInCrossArm :=
      result.final.halted && result.final.regs E1CloseDispatch.dSame == 7
    modeledSteps := result.steps
    machineReads := result.readLog.length
    routeTraceLen := routeTrace.length
    receiptMatchesRoute := result.readLog == routeTrace }

/-- Fixtures and windows the composite is exercised on.  Wider endpoint
separations than `legCases` so that BOTH dispatch directions occur, and
FEWER cases, because the composite sweep is run three times (honest plus
two mutants) and each case drives the full leg. -/
def composeCases : List (List Int × Nat × Nat) :=
  [2, 3, 5, 8].flatMap fun len =>
    let xs := generatedInput len 0
    [0, 1].flatMap fun l =>
      [0, 1, 2, 5, 9].map fun d => (xs, l, l + d)

/-- EVERY composite report for one builder, computed ONCE.

Deriving each count from its own sweep would re-run the machine per
statistic -- eight sweeps for the honest builder alone.  That is what the
first version of this phase did, and it did not finish in ten minutes.
The counts below are all folds over this single list. -/
def composeReports (salt : Nat)
    (build : Cartesian.CartesianShape → Nat → List Instr) :
    List ComposeReport :=
  composeCases.map fun (xs, l, r) =>
    runComposeFuel composeFuel salt build xs l r

/-- The subset the MUTANT sweeps run on.  Small for the cost reason given
above `composeMutantFuel`: each mutant case burns its whole fuel budget.
Rejection needs only one surviving disagreement, and this subset contains
same-block cases, which `composeMutantCoversSameBlock` checks. -/
def composeMutantCases : List (List Int × Nat × Nat) :=
  composeCases.take 10

/-- Mutant reports, on the reduced case set and the reduced fuel. -/
def composeMutantReports (salt : Nat)
    (build : Cartesian.CartesianShape → Nat → List Instr) :
    List ComposeReport :=
  composeMutantCases.map fun (xs, l, r) =>
    runComposeFuel composeMutantFuel salt build xs l r

/-- The mutant subset must contain at least one SAME-BLOCK case, or the
mutant sweeps would exercise only the fall-through and reject nothing. -/
def composeMutantCoversSameBlock (salt : Nat) : Bool :=
  ((composeMutantReports salt goodCompose).filter
    fun rep => rep.routeSame).length != 0

/-- The largest modeled step count over the HONEST sweep. -/
def composeMaxModeledSteps (reports : List ComposeReport) : Nat :=
  reports.foldl (fun acc rep => max acc rep.modeledSteps) 0

/-- The mutant fuel budget strictly exceeds every honest run, so it could
never fail a correct program.  Checked, not asserted. -/
def composeMutantFuelIsSlack (reports : List ComposeReport) : Bool :=
  composeMaxModeledSteps reports < composeMutantFuel

/-- Composite same-block cases (the ones whose receipt is comparable). -/
def composeSameCases (reports : List ComposeReport) : Nat :=
  (reports.filter fun rep => rep.routeSame).length

/-- Composite cross-block cases. -/
def composeCrossCases (reports : List ComposeReport) : Nat :=
  (reports.filter fun rep => !rep.routeSame).length

/-- SAME-BLOCK composite runs that fail to reach the proved exit pc 179. -/
def composeLegExitFailures (reports : List ComposeReport) : Nat :=
  (reports.filter fun rep => rep.routeSame && !rep.reachedLegExit).length

/-- SAME-BLOCK composite runs whose receipt disagrees with the route. -/
def composeReceiptMismatches (reports : List ComposeReport) : Nat :=
  (reports.filter fun rep => rep.routeSame && !rep.receiptMatchesRoute).length

/-- CROSS-BLOCK composite runs that fail to halt in the witness cross arm. -/
def composeCrossArmFailures (reports : List ComposeReport) : Nat :=
  (reports.filter fun rep => !rep.routeSame && !rep.haltedInCrossArm).length

/-- CROSS-BLOCK composite runs that performed a read.  Must be zero: the
dispatch reads nothing and the leg must be skipped entirely. -/
def composeCrossReads (reports : List ComposeReport) : Nat :=
  reports.foldl (fun acc rep =>
    if rep.routeSame then acc else acc + rep.machineReads) 0

/-- Total modeled steps across the composite sweep: a MODELED quantity. -/
def composeModeledSteps (reports : List ComposeReport) : Nat :=
  reports.foldl (fun acc rep => acc + rep.modeledSteps) 0

/-- Total modeled read events across the composite sweep. -/
def composeModeledReads (reports : List ComposeReport) : Nat :=
  reports.foldl (fun acc rep => acc + rep.machineReads) 0

/-- Both composite mutations genuinely change the instruction list, and
NEITHER changes its length. -/
def composeMutationsAreReal : Bool :=
  let shape := Cartesian.stackCartesianShape (generatedInput 5 0)
  let blockSize := SuccinctClose.canonicalBPRelativeSummaryBlockSizeRaw shape
  let good := goodCompose shape blockSize
  let mutA := mutatedComposeUnrebased shape blockSize
  let mutB := mutatedComposeBackEdge shape blockSize
  good != mutA && good != mutB &&
    good.length == mutA.length && good.length == mutB.length

/-- `sameBlockDispatchProgram_length` says `4 + 2 + 173 = 179`; check the
running list agrees, and that the rebased layout really does differ from
the base-0 one (if it did not, the rung would be vacuous). -/
def composeLengthOk : Bool :=
  let shape := Cartesian.stackCartesianShape (generatedInput 5 0)
  let blockSize := SuccinctClose.canonicalBPRelativeSummaryBlockSizeRaw shape
  (goodCompose shape blockSize).length == 179 &&
    E1SameBlockLeg.sameBlockLegProgramAt shape legFringeSegment blockSize 6 !=
      E1SameBlockLeg.sameBlockLegProgram shape legFringeSegment blockSize

/-! ## 6e. THE THREE-WAY CANDIDATE MERGE: executed against an INDEPENDENT
reference

`E1CandMerge3.candMerge3` is the machine block for the cross-block close
object's fused epilogue.  This phase RUNS it and compares its answer
against `refMerge3` below, which is written from the specification and
does not call the route.

## Why this phase's discriminator is the VALUE, not the receipt

Every earlier mutation in this harness is ultimately caught by RECEIPT
diffing -- phase 4c's mutant B is the sharpest, changing a single operand
and reaching the correct exit pc while its read log diverges.  That test
is unavailable here, and saying so precisely matters: the merge block is
READ-FREE (`candMerge3_readFree`, and the route's epilogue rides a
`TraceResult.map` that contributes no trace event), so the honest run and
every mutant produce the SAME empty receipt.

So this phase raises the bar rather than reusing it.  `mutantD_position`
below changes ONE source operand, preserves program length, preserves the
entire opcode-category sequence, preserves control flow exactly, and
therefore agrees with the honest run on exit pc, halted flag, modeled step
count AND receipt.  Nothing except comparing the computed value against an
independent reference can reject it -- which is exactly what
INV-VALUE-DEPENDENCY asks for, and a strictly harder target than mutant B.
-/

/-- INDEPENDENT reference for the three-way candidate close.

Written from the SPECIFICATION -- of the present candidates take the one
with the smallest value, earliest on ties, and report its position minus
one -- as a flatten-then-fold.  It does NOT call `bpCandidateMerge3?`,
`bpCandidateMerge?`, `bpCandidateBetter`, `bpCandidateClose?`, or the
machine.

It deliberately does not share the route's structure: the route is a
LEFT-ASSOCIATED pairwise fold of option-lifted merges, while this
flattens the options first and folds once over the survivors.  Agreement
is therefore a real check on the association and on the tie-break, not a
restatement of the same expression. -/
def refMerge3 (left middle right : Option (Nat × Nat)) : Option Nat :=
  match [left, middle, right].filterMap id with
  | [] => none
  | c :: cs =>
      some ((cs.foldl (fun acc x => if x.1 < acc.1 then x else acc) c).2 - 1)

/-- Order-preserving de-duplication, for the path-coverage check. -/
def dedupList {α : Type} [BEq α] (xs : List α) : List α :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

/-- Merge fixtures as `(lv, lp, mv, mp, rv, rp)`, with `mv` in the block's
BIASED form (`0` = middle absent, `k + 1` = middle value `k`).

The value grids overlap deliberately so that TIES occur in both
directions: a tie must keep the LEFT candidate, and a fixture set without
ties could not tell `natLt` from `natLe`. -/
def mergeCases : List (Nat × Nat × Nat × Nat × Nat × Nat) :=
  [0, 3, 5].flatMap fun lv =>
    [0, 1, 4, 6].flatMap fun mv =>
      [0, 3, 5].map fun rv =>
        (lv, 100 + lv, mv, 200 + mv, rv, 300 + rv)

/-- What one merge run reports.  `expected` is computed from the
independent reference BEFORE the program is built or run. -/
structure MergeReport where
  expected : Option Nat
  machine : Nat
  reachedExit : Bool
  modeledSteps : Nat
  machineReads : Nat
  agrees : Bool
  middlePresent : Bool
  middleBetter : Bool
  rightBetter : Bool
deriving Repr

/-- RUN THE MERGE BLOCK and compare against the independent reference. -/
def runMerge (salt : Nat) (build : List Instr -> List Instr)
    (lv lp mv mp rv rp : Nat) : MergeReport :=
  -- EXPECTATION FIRST, from `refMerge3` alone.
  let left : Option (Nat × Nat) := some (lv, lp)
  let middle : Option (Nat × Nat) :=
    if mv == 0 then none else some (mv - 1, mp)
  let right : Option (Nat × Nat) := some (rv, rp)
  let expected := refMerge3 left middle right
  -- Route-side branch conditions, also computed without the machine.
  let midBetter := mv != 0 && mv - 1 < lv
  let acc : Nat × Nat := if midBetter then (mv - 1, mp) else (lv, lp)
  -- ONLY NOW the machine.
  let program := build (E1CandMerge3.candMerge3 0) ++ [Instr.halt]
  let result :=
    E1Machine.run E1CandMerge3.witnessStore program (64 + salt)
      ⟨E1CandMerge3.witnessRegs lv lp mv mp rv rp, 0, false⟩
  let got := result.final.regs E1SameBlockArm.fRes
  { expected := expected
    machine := got
    reachedExit := result.final.pc == 16 && result.final.halted
    modeledSteps := result.steps
    machineReads := result.readLog.length
    agrees := expected == some got
    middlePresent := mv != 0
    middleBetter := midBetter
    rightBetter := rv < acc.1 }

/-- The honest builder. -/
def goodMerge : List Instr -> List Instr := id

/-- MUTANT C: swap the two operands of the RIGHT comparison.  One operand
change; same length; same opcode-category sequence; still reaches the
proved exit pc on every case. -/
def mutatedMergeCompare (program : List Instr) : List Instr :=
  program.map fun instr =>
    match instr with
    | .natLt d s1 s2 =>
        if d == E1CandMerge3.mU then .natLt d s2 s1 else .natLt d s1 s2
    | other => other

/-- MUTANT D: the middle candidate's POSITION move reads the left
candidate's position instead.

This is the harness's sharpest mutation.  It changes ONE source operand,
leaves control flow completely untouched, and therefore agrees with the
honest run on exit pc, halted flag, modeled step count and (the block
being read-free) receipt.  Only the value comparison against `refMerge3`
rejects it, and only on the cases where the middle candidate actually
wins -- so `mergePathCoverage` below is load-bearing for this mutant, not
decorative. -/
def mutatedMergePosition (program : List Instr) : List Instr :=
  program.map fun instr =>
    match instr with
    | .move d s =>
        if d == E1CandMerge3.mAP && s == E1CandMerge3.mMP then
          .move d E1CandMerge3.mLP
        else .move d s
    | other => other

/-- Every merge report for one builder, computed ONCE (the M3d-6 gotcha:
deriving each statistic from its own sweep re-runs the machine per
statistic). -/
def mergeReports (salt : Nat) (build : List Instr -> List Instr) :
    List MergeReport :=
  mergeCases.map fun (lv, lp, mv, mp, rv, rp) =>
    runMerge salt build lv lp mv mp rv rp

/-- Runs whose value disagrees with the independent reference. -/
def mergeMismatches (reports : List MergeReport) : Nat :=
  (reports.filter fun rep => !rep.agrees).length

/-- Runs that fail to reach the proved exit pc 16, halted. -/
def mergeExitFailures (reports : List MergeReport) : Nat :=
  (reports.filter fun rep => !rep.reachedExit).length

/-- Total modeled steps across the merge sweep: a MODELED quantity. -/
def mergeModeledSteps (reports : List MergeReport) : Nat :=
  reports.foldl (fun acc rep => acc + rep.modeledSteps) 0

/-- Total modeled read events.  Must be zero: the block is read-free. -/
def mergeModeledReads (reports : List MergeReport) : Nat :=
  reports.foldl (fun acc rep => acc + rep.machineReads) 0

/-- How many of the block's SIX control paths the fixture set reaches.

The path is identified by the three route-side branch conditions.  If this
is not `6`, some arm of `candMerge3_runsTo` is never exercised and the
mutation tests below may be vacuous on that arm. -/
def mergePathCoverage (reports : List MergeReport) : Nat :=
  (dedupList
    (reports.map fun rep =>
      (rep.middlePresent, rep.middleBetter, rep.rightBetter))).length

/-- Both merge mutations genuinely change the instruction list, and
NEITHER changes its length OR its opcode-category sequence.  This is what
makes them harder than a mutation a length or opcode audit would find. -/
def mergeMutationsAreReal : Bool :=
  let good := E1CandMerge3.candMerge3 0
  let mc := mutatedMergeCompare good
  let mp := mutatedMergePosition good
  good != mc && good != mp &&
    good.length == mc.length && good.length == mp.length &&
    good.map Instr.category == mc.map Instr.category &&
    good.map Instr.category == mp.map Instr.category

/-- MUTANT D IS INVISIBLE TO EVERY NON-VALUE OBSERVABLE.  Checked, not
asserted: exit pc, halted flag, modeled step count and receipt length all
agree with the honest sweep case for case.  This is the statement that
makes the phase's claim -- that only the independent-reference value
comparison can reject it -- evidence rather than commentary. -/
def mergeMutantDIsValueOnly (salt : Nat) : Bool :=
  let honest := mergeReports salt goodMerge
  let mutant := mergeReports salt mutatedMergePosition
  (honest.zip mutant).all fun (h, m) =>
    h.reachedExit == m.reachedExit &&
      h.modeledSteps == m.modeledSteps &&
      h.machineReads == m.machineReads

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

-- The report grew a fourth machine phase and its verdict clauses; the
-- resulting `do` block exceeds the default elaboration recursion depth.
-- This raises only the ELABORATOR's stack budget: it is not a proof
-- option and weakens no check.
set_option maxRecDepth 8000 in
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

  -- STEP 3d: the COMPOSITE (dispatch then rebased leg), executed.
  IO.println "-- phase 3d: COMPOSITE dispatch-then-rebased-leg vs route --"
  let tc0 <- IO.monoMsNow
  let cmpReports := composeReports salt goodCompose
  let cmpSame := composeSameCases cmpReports
  let cmpCross := composeCrossCases cmpReports
  let cmpExitFails := composeLegExitFailures cmpReports
  let cmpReceiptFails := composeReceiptMismatches cmpReports
  let cmpCrossFails := composeCrossArmFailures cmpReports
  let cmpCrossReads := composeCrossReads cmpReports
  let cmpSteps := composeModeledSteps cmpReports
  let cmpReads := composeModeledReads cmpReports
  let cmpMaxSteps := composeMaxModeledSteps cmpReports
  let cmpFuelSlack := composeMutantFuelIsSlack cmpReports
  IO.println s!"composeCases={composeCases.length}"
  IO.println s!"composeLengthOk={composeLengthOk}   (179, and rebased != base-0)"
  IO.println s!"composeSameCases={cmpSame}   (branch taken; leg hosted at 6)"
  IO.println s!"composeCrossCases={cmpCross}   (fall-through to witness cross arm)"
  IO.println s!"composeLegExitFailures={cmpExitFails}   (proved exit is pc 179)"
  IO.println s!"composeReceiptMismatches={cmpReceiptFails}   (machine readLog vs route trace)"
  IO.println s!"composeCrossArmFailures={cmpCrossFails}   (cross cases must halt in the cross arm)"
  IO.println s!"composeCrossReads={cmpCrossReads}   (must be 0: leg skipped entirely)"
  IO.println s!"composeModeledSteps={cmpSteps}   (machine-modeled, reproducible)"
  IO.println s!"composeMaxModeledSteps={cmpMaxSteps}   (largest single honest run)"
  IO.println s!"composeModeledReads={cmpReads}   (machine-modeled receipt events)"
  let tc1 <- IO.monoMsNow
  IO.println s!"composeWallClockMs={tc1 - tc0}   (this binary on this host; NOT evidence)"
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

  -- STEP 4c: mutating the COMPOSITE's rebasing specifically.
  IO.println "-- phase 4c: deliberate REBASING mutations of the composite --"
  let tcm0 <- IO.monoMsNow
  let mutAReports := composeMutantReports salt mutatedComposeUnrebased
  let mutBReports := composeMutantReports salt mutatedComposeBackEdge
  let mutAExit := composeLegExitFailures mutAReports
  let mutAReceipt := composeReceiptMismatches mutAReports
  let mutBExit := composeLegExitFailures mutBReports
  let mutBReceipt := composeReceiptMismatches mutBReports
  IO.println s!"composeMutationsAreReal={composeMutationsAreReal}   (both differ; both same length)"
  IO.println s!"composeMutantCases={composeMutantCases.length}   (subset; each burns its fuel budget)"
  IO.println s!"composeMutantFuel={composeMutantFuel}   (vs honest max modeled {cmpMaxSteps}; slack={cmpFuelSlack})"
  IO.println s!"composeMutantCoversSameBlock={composeMutantCoversSameBlock salt}"
  IO.println s!"mutantA_unrebased_exitFailures={mutAExit}"
  IO.println s!"mutantA_unrebased_receiptMismatches={mutAReceipt}   (must be > 0)"
  IO.println s!"mutantB_backEdge_exitFailures={mutBExit}"
  IO.println s!"mutantB_backEdge_receiptMismatches={mutBReceipt}   (must be > 0)"
  IO.println s!"composeMutationARejected={mutAReceipt != 0}"
  IO.println s!"composeMutationBRejected={mutBReceipt != 0}"
  let tcm1 <- IO.monoMsNow
  IO.println s!"composeMutationWallClockMs={tcm1 - tcm0}"
  IO.println ""

  -- STEP 3e: the THREE-WAY CANDIDATE MERGE, executed vs an independent ref.
  IO.println "-- phase 3e: three-way candidate MERGE vs independent reference --"
  let tg0 <- IO.monoMsNow
  let mrgReports := mergeReports salt goodMerge
  let mrgMismatch := mergeMismatches mrgReports
  let mrgExitFails := mergeExitFailures mrgReports
  let mrgSteps := mergeModeledSteps mrgReports
  let mrgReads := mergeModeledReads mrgReports
  let mrgCoverage := mergePathCoverage mrgReports
  IO.println s!"mergeCases={mergeCases.length}"
  IO.println s!"mergePathCoverage={mrgCoverage}   (must be 6: all six control paths)"
  IO.println s!"mergeExitFailures={mrgExitFails}   (proved exit is pc 16, halted)"
  IO.println s!"mergeMismatches={mrgMismatch}   (machine fRes vs refMerge3; must be 0)"
  IO.println s!"mergeModeledSteps={mrgSteps}   (machine-modeled, reproducible)"
  IO.println s!"mergeModeledReads={mrgReads}   (must be 0: the block is read-free)"
  let tg1 <- IO.monoMsNow
  IO.println s!"mergeWallClockMs={tg1 - tg0}   (this binary on this host; NOT evidence)"
  IO.println ""

  -- STEP 4d: mutating the MERGE, where the receipt cannot help.
  IO.println "-- phase 4d: deliberate mutations of the MERGE block --"
  let tgm0 <- IO.monoMsNow
  let mutCReports := mergeReports salt mutatedMergeCompare
  let mutDReports := mergeReports salt mutatedMergePosition
  let mutCMismatch := mergeMismatches mutCReports
  let mutCExit := mergeExitFailures mutCReports
  let mutDMismatch := mergeMismatches mutDReports
  let mutDExit := mergeExitFailures mutDReports
  let mutDValueOnly := mergeMutantDIsValueOnly salt
  IO.println s!"mergeMutationsAreReal={mergeMutationsAreReal}   (both differ; same length AND same opcode categories)"
  IO.println s!"mutantC_compareSwap_exitFailures={mutCExit}   (0 expected: exit pc alone MISSES this)"
  IO.println s!"mutantC_compareSwap_mismatches={mutCMismatch}   (must be > 0: the value catches it)"
  IO.println s!"mutantD_position_exitFailures={mutDExit}   (0 expected)"
  IO.println s!"mutantD_position_mismatches={mutDMismatch}   (must be > 0: ONLY the value catches it)"
  IO.println s!"mutantD_isValueOnly={mutDValueOnly}   (pc, steps and receipt all agree with honest)"
  IO.println s!"mergeMutationCRejected={mutCMismatch != 0}"
  IO.println s!"mergeMutationDRejected={mutDMismatch != 0}"
  let tgm1 <- IO.monoMsNow
  IO.println s!"mergeMutationWallClockMs={tgm1 - tgm0}"
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

  -- Verdict.  Grouped into named clauses: a single `&&` chain over all of
  -- these exceeds the elaborator's recursion depth on `BEq Nat`.
  let okReference := refFailures == 0
  let okLengths :=
    dispatchLengthOk && witnessLengthOk && sameBlockLegLengthOk &&
      composeLengthOk
  let okDispatch := mismatches.isEmpty && reads == 0
  let okLeg := legExitFails == 0 && legReceiptFails == 0
  let okSelect := selExitFails == 0 && selReceiptFails == 0
  let okCompose :=
    cmpExitFails == 0 && cmpReceiptFails == 0 && cmpCrossFails == 0 &&
      cmpCrossReads == 0
  -- Anti-vacuity: BOTH dispatch directions must actually occur in the
  -- composite sweep, or the composite checks above are empty.
  let okComposeCoverage := cmpSame != 0 && cmpCross != 0
  let okMutations :=
    mutationIsReal 3 && rejected && legMutationIsReal &&
      legMutationRejected salt && composeMutationsAreReal &&
      mutAReceipt != 0 && mutBReceipt != 0
  -- The reduced mutant budget must be provably non-binding for a correct
  -- program, and the reduced case set must reach the same-block arm.
  let okMutantSetup := cmpFuelSlack && composeMutantCoversSameBlock salt
  -- The merge block: value agreement with the independent reference, all
  -- six control paths reached, read-freedom observed in execution.
  let okMerge :=
    mrgMismatch == 0 && mrgExitFails == 0 && mrgReads == 0 &&
      mrgCoverage == 6
  -- Both merge mutants rejected, and mutant D confirmed invisible to every
  -- observable except the value.
  let okMergeMutations :=
    mergeMutationsAreReal && mutCMismatch != 0 && mutDMismatch != 0 &&
      mutDValueOnly
  let okCore := okReference && okLengths && okDispatch && okLeg
  let okComposite := okSelect && okCompose && okComposeCoverage && okMerge
  let okAdversarial := okMutations && okMutantSetup && okMergeMutations
  let ok := okCore && okComposite && okAdversarial
  if ok then
    IO.println "RESULT: PASS (with the whole-query comparison still OPEN)"
    return 0
  else
    IO.println "RESULT: FAIL"
    return 1

end RMQ.Validation.E1MachineValidate

def main : IO UInt32 := RMQ.Validation.E1MachineValidate.mainImpl
