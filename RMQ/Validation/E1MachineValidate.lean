import RMQ.Core.WordRAM.E1CloseCompose
import RMQ.Core.WordRAM.E1SelectCanonical
import RMQ.Core.WordRAM.E1CandMerge3
import RMQ.Core.WordRAM.E1CrossBlockArm
import RMQ.Core.WordRAM.E1FringeArmProgram
import RMQ.Core.WordRAM.E1FringeFoldProgram
import RMQ.Core.WordRAM.E1InteriorChunkFold
import RMQ.Core.WordRAM.E1CostAlgebra
import RMQ.Core.WordRAM.E1WholeQueryCostLiteral

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

-- The `mainImpl` do-block is long enough that elaborating it exceeds the
-- default recursion budget (the existing verdict-grouping comment below
-- records the same pressure on the `&&` chain).
set_option maxRecDepth 8192

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

/-! ## 7. The whole-query comparison

**This section used to be THE HOLE, and it is no longer one.**  Its
machinery now lives further down, beside the fixture classes it needs, at
`## Phase 3n/5: the WHOLE-QUERY comparison`.  It is placed there rather
than here because it depends on `refRMQ`, on the fixture-class classifier
and on `legStore`, and Lean wants those first.

The reason recorded in this docstring across four rounds was a moving
target, and it was wrong in both directions.  It has said, in order: the
`bpSparseLogSpan`/`Nat.log2` obstruction (discharged by B7); that the
INTERIOR LEG was unbuilt (built in M3d-11/M3d-12); and most recently that
"no definition composes the close legs and the interior into a single
runnable query program -- there is no `wholeQueryProgram` in the tree",
which `E1WholeQueryProgram.lean:876` falsifies outright.

**The durable fix is not a fifth sentence.**  Each of those was a
hand-written REASON, and a hand-written reason goes stale silently because
nothing recomputes it.  The status is now DERIVED from a condition the
harness actually evaluates -- see `wholeQueryComparisonAvailable`
(defined at the phase, from the comparison's own case count) and
`wholeQueryStatusLine`, which renders its message from that condition
rather than storing one. -/

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
/-! ## Phase 3f/4e: the FRINGE ARM, where the RECEIPT is the discriminator

The M3d-7 session established that this harness's two discriminators are
COMPLEMENTARY: receipt diffing catches control-flow-preserving mutations
in READ-BEARING blocks, independent-value checking catches value-only
mutations in READ-FREE blocks, and neither subsumes the other.  The merge
block is read-free, so phase 3e/4d had to use the value.

The fringe arm is the other side of that coin.  It is READ-BEARING -- four
charged window reads plus one per capped fold pass -- so here the RECEIPT
is the discriminator with power, and mutant E below is chosen to be
invisible to the value check precisely as mutant D was invisible to the
receipt check.
-/

/-- INDEPENDENT reference for the arm's charged-read accounting.

Computed from the SPECIFICATION -- the window read is four ascending
payload words at the window base in segment `0`, and the 33-capped fold
performs exactly one chunk-table read per pass at the fringe segment --
without calling the machine, `fringeArmProgramAt`, or the route's fold
evaluator.  The cap `33` is the route's literal
(`ChargedFringeTrace.lean:722`). -/
def refArmReads (c relHi : Nat) : Nat := 4 + Nat.min (relHi / c + 1) 33

/-- The four window-read `(segment, address)` pairs the specification
requires, in order. -/
def refArmWindowAddrs (base : Nat) : List (Nat × Nat) :=
  [(0, base), (0, base + 1), (0, base + 2), (0, base + 3)]

/-- Project a trace event onto the `(segment, address)` pair it charges.

Non-`readWord` events map to `none` rather than to a sentinel pair, so
that a receipt carrying a `wordRank`, `wordSelect` or
`syntheticCostOnlyPrimitive` event SHRINKS the projected list and is
caught by the length check in `runArm` -- a sentinel would have silently
passed such an event off as a read. -/
def eventAddr : TraceEvent -> Option (Nat × Nat)
  | .readWord segment address _ => some (segment, address)
  | _ => none

/-- Arm fixtures as `(word, S, c, L, base, relLo, relHi, seed, bb, start)`.
The `relLo`/`relHi` grids straddle the fold's window gate so that BOTH
epilogue arms occur -- an occupied rebase and the seed fallback -- and the
`c`/`relHi` grid makes the pass count vary from one to four. -/
def armCases : List (List Bool × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat) :=
  [[true, false, true, false], [false, false, false, false],
    [true, true, true, true]].flatMap fun w =>
    [(2, 1), (2, 5), (1, 3), (2, 3)].flatMap fun (c, relHi) =>
      [0, 4, 9].map fun relLo =>
        (w, 7, c, 4, 100, relLo, relHi, 0, 500, 900)

/-- What one arm run reports.  Every `expected*` field is computed from
the independent reference BEFORE the program is built or run. -/
structure ArmReport where
  expectedReads : Nat
  machineReads : Nat
  expectedWindowAddrs : List (Nat × Nat)
  machineWindowAddrs : List (Nat × Nat)
  foldSegmentsOk : Bool
  reachedExit : Bool
  modeledSteps : Nat
  value : Nat
  position : Nat
  readsAgree : Bool
  windowAgrees : Bool
deriving Repr

/-- RUN THE ARM at host base `2` and compare its receipt against the
independent reference. -/
def runArm (salt : Nat) (build : List Instr -> List Instr)
    (w : List Bool) (S c L base relLo relHi seed bb start : Nat) :
    ArmReport :=
  -- EXPECTATION FIRST, from `refArmReads`/`refArmWindowAddrs` alone.
  let expectedReads := refArmReads c relHi
  let expectedWindow := refArmWindowAddrs base
  -- ONLY NOW the machine.
  let program := build (E1FringeArmProgram.armWitnessProgram S c L)
  let result :=
    E1Machine.run (E1FringeArmProgram.armWitnessStore w) program
      (4000 + salt)
      ⟨E1FringeArmProgram.armWitnessRegs base relLo relHi seed bb start,
        0, false⟩
  let addrs := result.readLog.filterMap eventAddr
  let window := addrs.take 4
  let folds := addrs.drop 4
  { expectedReads := expectedReads
    machineReads := result.readLog.length
    expectedWindowAddrs := expectedWindow
    machineWindowAddrs := window
    -- `addrs.length == readLog.length` rejects any non-read event on the
    -- receipt; `folds.all` pins every fold read to the fringe segment.
    foldSegmentsOk :=
      addrs.length == result.readLog.length && folds.all (fun p => p.1 == S)
    reachedExit := result.final.pc == 97 && result.final.halted
    modeledSteps := result.steps
    value := result.final.regs E1FringeArmBlock.fRV
    position := result.final.regs E1FringeArmBlock.fRP
    readsAgree := expectedReads == result.readLog.length
    windowAgrees := expectedWindow == window }

def armReports (salt : Nat) (build : List Instr -> List Instr) :
    List ArmReport :=
  armCases.map fun (w, S, c, L, base, relLo, relHi, seed, bb, start) =>
    runArm salt build w S c L base relLo relHi seed bb start

def armExitFailures (rs : List ArmReport) : Nat :=
  (rs.filter (fun r => !r.reachedExit)).length

/-- RECEIPT failures: read count or window addresses disagreeing with the
independent reference, or a fold read charged at the wrong segment. -/
def armReceiptFailures (rs : List ArmReport) : Nat :=
  (rs.filter
    (fun r => !r.readsAgree || !r.windowAgrees || !r.foldSegmentsOk)).length

/-- Anti-vacuity: the fixture set must reach BOTH epilogue arms.  The
seed-fallback arm leaves the seed's `start` in the position register; the
occupied arm leaves a window rebase.  A fixture set hitting only one would
make the arm phase blind to the epilogue branch. -/
def armEpilogueCoverage (rs : List ArmReport) : Nat :=
  (dedupList (rs.map (fun r => r.position == 900))).length

/-- Anti-vacuity: the fold's back edge must actually fire.  Distinct read
counts above the four window reads witness distinct pass counts. -/
def armPassCoverage (rs : List ArmReport) : Nat :=
  (dedupList (rs.map (fun r => r.machineReads))).length

def goodArm : List Instr -> List Instr := id

/-- MUTANT E: charge the fold's chunk-table read to the NEXT segment.

One field change; same program length; same opcode-category sequence; and
because the witness store answers every segment identically, the decoded
word, every branch, the exit pc, the halted flag, the modeled step count
AND the computed value are all UNCHANGED.  Only the segment recorded in
the receipt differs.

This is the exact mirror of mutant D: D was invisible to the receipt and
caught only by the value; E is invisible to the value and caught only by
the receipt.  Together they show neither discriminator subsumes the
other. -/
def mutatedArmSegment (program : List Instr) : List Instr :=
  program.map fun instr =>
    match instr with
    | .readMem d s a => if s == 7 then .readMem d (s + 1) a else .readMem d s a
    | other => other

/-- The mutation is real: it changes the program, preserves its length,
and preserves the whole opcode-category sequence. -/
def armMutationIsReal : Bool :=
  let honest := E1FringeArmProgram.armWitnessProgram 7 2 4
  let mutant := mutatedArmSegment honest
  honest != mutant && honest.length == mutant.length &&
    honest.map Instr.category == mutant.map Instr.category

/-- Mutant E is RECEIPT-ONLY: case for case it agrees with the honest run
on exit pc, halted flag, modeled step count and computed value.  Checked,
not asserted -- this is what makes "only the receipt rejects it" evidence. -/
def armMutantEIsReceiptOnly (salt : Nat) : Bool :=
  let honest := armReports salt goodArm
  let mutant := armReports salt mutatedArmSegment
  (honest.zip mutant).all fun (h, m) =>
    h.reachedExit == m.reachedExit && h.modeledSteps == m.modeledSteps &&
      h.value == m.value && h.position == m.position

/-! ## Phase 3g/4f: the CROSS-BLOCK range preambles, where the VALUE is
the discriminator

`crossLeftRange` and `crossRightRange` (`E1CrossBlockArm.lean`) are new
this session and READ-FREE, so the receipt has no power over them at all
-- exactly the merge's situation.  They are validated against an
independent reference for the route's left- and right-fringe window
ranges, computed from `blockStartOf`/`blockOfClose` rather than from the
machine's `(c / bs + 1) * bs` form.

When this phase was written the two blocks had no `_runsTo` theorems, so
execution was the only evidence their arithmetic was right.  M3d-9 has
since proved `crossLeftRange_runsTo` / `crossRightRange_runsTo`, and this
phase's independent reference is now a genuine CROSS-CHECK of them rather
than the sole evidence -- the reference and the theorem's route-side
statement were written from `blockStartOf`/`blockOfClose` independently of
the machine's fused `(c / bs + 1) * bs` form.
-/

/-- INDEPENDENT reference for the LEFT cross-block fringe range, read off
`fringeLeg_trace_eq_leftArm` (`E1FringeArmBlock.lean:618`).  Structurally
different from the machine's form: it uses the route's `blockStartOf` and
`blockOfClose` and adds `blockSize` separately, where the machine folds
both into one `(leftBlock + 1) * blockSize`. -/
def refCrossLeftRange (blockSize bb leftClose : Nat) : Nat × Nat × Nat :=
  let start := leftClose + 1
  let count :=
    RMQ.SuccinctClose.blockStartOf blockSize
        (RMQ.SuccinctClose.blockOfClose blockSize leftClose) +
      blockSize - leftClose
  (start, start - bb, start + count - 1 - bb)

/-- INDEPENDENT reference for the RIGHT cross-block fringe range, read off
`fringeLeg_trace_eq_rightArm` (`E1FringeArmBlock.lean:647`). -/
def refCrossRightRange (blockSize bb rightClose : Nat) : Nat × Nat × Nat :=
  let blockStart :=
    RMQ.SuccinctClose.blockStartOf blockSize
      (RMQ.SuccinctClose.blockOfClose blockSize rightClose)
  (blockStart, blockStart - bb,
    blockStart + (rightClose - blockStart + 2) - 1 - bb)

/-- Range fixtures as `(blockSize, bb, close)`.  The closes straddle block
boundaries in both directions so that the `divConst`/`mulConst` chain is
exercised at exact multiples of `blockSize` and strictly inside blocks. -/
def rangeCases : List (Nat × Nat × Nat) :=
  [4, 6, 8].flatMap fun bs =>
    [0, 1, 5].flatMap fun bb =>
      [8, 9, 11, 12, 17, 24].map fun close => (bs, bb, close)

/-- What one range-preamble run reports.  `expected` is computed from the
independent reference BEFORE the program is built or run. -/
structure RangeReport where
  expected : Nat × Nat × Nat
  machine : Nat × Nat × Nat
  reachedExit : Bool
  modeledSteps : Nat
  machineReads : Nat
  agrees : Bool
deriving Repr

/-- RUN one range preamble and compare against the independent reference. -/
def runRange (salt : Nat) (isLeft : Bool)
    (build : List Instr -> List Instr) (blockSize bb close : Nat) :
    RangeReport :=
  -- EXPECTATION FIRST.
  let expected :=
    if isLeft then refCrossLeftRange blockSize bb close
    else refCrossRightRange blockSize bb close
  -- ONLY NOW the machine.
  let block :=
    if isLeft then E1CrossBlockArm.crossLeftRange blockSize
    else E1CrossBlockArm.crossRightRange blockSize
  let program := build block ++ [Instr.halt]
  let regs :=
    RegFile.write (RegFile.write (fun _ => 0)
      E1SameBlockArm.fClose close) E1FringeArmBlock.fBB bb
  let result :=
    E1Machine.run ⟨fun _ _ => none⟩ program (64 + salt) ⟨regs, 0, false⟩
  let got :=
    (result.final.regs E1FringeArmBlock.fStart,
      result.final.regs E1FringeFoldBlock.fLo,
      result.final.regs E1FringeFoldBlock.fHi)
  { expected := expected
    machine := got
    reachedExit := result.final.pc == 10 && result.final.halted
    modeledSteps := result.steps
    machineReads := result.readLog.length
    agrees := expected == got }

def rangeReports (salt : Nat) (isLeft : Bool)
    (build : List Instr -> List Instr) : List RangeReport :=
  rangeCases.map fun (bs, bb, close) => runRange salt isLeft build bs bb close

def rangeMismatches (rs : List RangeReport) : Nat :=
  (rs.filter (fun r => !r.agrees)).length

def rangeExitFailures (rs : List RangeReport) : Nat :=
  (rs.filter (fun r => !r.reachedExit)).length

def rangeReads (rs : List RangeReport) : Nat :=
  (rs.map RangeReport.machineReads).foldl (· + ·) 0

def goodRange : List Instr -> List Instr := id

/-- MUTANT F: drop the `+ 1` that turns the left block INDEX into the
block's exclusive end, i.e. compute `leftBlock * blockSize - leftClose`
instead of `(leftBlock + 1) * blockSize - leftClose`.

This is the off-by-one an eye is least likely to catch in a range
preamble.  One operand change, same length, same opcode categories, and
the block is READ-FREE so no receipt exists to diff.  Only the independent
reference rejects it. -/
def mutatedRangeCount (program : List Instr) : List Instr :=
  program.map fun instr =>
    match instr with
    | .add d s1 s2 =>
        if d == E1FringeFoldBlock.fU && s1 == E1FringeFoldBlock.fU then
          .add d s1 s1
        else .add d s1 s2
    | other => other

def rangeMutationIsReal : Bool :=
  let honest := E1CrossBlockArm.crossLeftRange 4
  let mutant := mutatedRangeCount honest
  honest != mutant && honest.length == mutant.length &&
    honest.map Instr.category == mutant.map Instr.category

/-! ## Phase 3h/4g: REGISTER PRESERVATION, a THIRD discriminator

Phases 3e/4d and 3f/4e established that this harness had two
discriminators and that they are complementary: mutant D (value-only) is
invisible to the receipt, mutant E (receipt-only) is invisible to the
value.  Both were executed, in both directions.

Neither has any power over a mutation that computes the RIGHT answer,
performs the RIGHT reads, in the RIGHT number of steps, and merely
scribbles on a register it does not own.  That class is not hypothetical
here: `fringeArm_runsTo`'s register-preservation clause is the M3d-9
deliverable and the enabling fact for the whole cross-block composition,
which needs the left stash's `mLV`/`mLP` to survive the right arm some 194
instructions later.  A silent extra write is exactly the defect that
clause exists to exclude, and exactly the defect the other two
discriminators cannot see.

So this phase checks the clause itself: every register satisfying
`FringeArmUntouched` (`E1FringeArmBlock.lean:948`) must come out of the
arm holding what it went in with.

WHY THE SENTINELS MATTER.  Seeded from `fun _ => 0`, preservation is
vacuous -- a block that zeroes a register it does not own still "preserves"
it.  `presSentinel` is injective and nowhere zero, so a clobber is
detectable whatever value it writes, and a register copied from elsewhere
is distinguishable from one left alone.
-/

/-- Injective, nowhere-zero sentinel pattern (see the note above on why a
zero-seeded register file makes this phase vacuous). -/
def presSentinel (r : Nat) : Nat := r * 7 + 3

/-- Register file for a preservation fixture: every register carries its
distinct sentinel, then the arm's seven genuine inputs are written over. -/
def armPresRegs (base relLo relHi seed bb start : Nat) : RegFile :=
  RegFile.write (RegFile.write (RegFile.write (RegFile.write
    (RegFile.write (RegFile.write (RegFile.write
      presSentinel E1FringeArmBlock.fBase base)
        E1FringeFoldBlock.fLo relLo) E1FringeFoldBlock.fHi relHi)
        E1FringeFoldBlock.fAcc seed)
        E1FringeArmBlock.fBB bb) E1FringeArmBlock.fSeed seed)
        E1FringeArmBlock.fStart start

/-- The registers `FringeArmUntouched` claims survive the arm, as a
concrete list over the bank the machine actually uses.  Mirrors the
predicate `r < 40 ∨ (63 ≤ r ∧ r ≠ 67 ∧ r ≠ 68)` literally. -/
def armUntouchedRegs : List Nat :=
  (List.range 91).filter fun r =>
    r < 40 || (63 <= r && r != 67 && r != 68)

/-- What one preservation fixture reports. -/
structure PresReport where
  clobbered : List Nat
  checkedRegs : Nat
  reachedExit : Bool
  modeledSteps : Nat
  value : Nat
  position : Nat
  zeroSeedValue : Nat
  zeroSeedPosition : Nat
  preserved : Bool
  agreesWithZeroSeed : Bool
deriving Repr

/-- RUN THE ARM on a sentinel-seeded register file and check the
preservation clause register by register.

Also re-runs the SAME fixture zero-seeded and compares the answer: if the
arm depended on any register it does not initialise, the two runs would
disagree, so this doubles as evidence that the arm's inputs are exactly
the seven it declares. -/
def runPres (salt : Nat) (build : List Instr -> List Instr)
    (w : List Bool) (S c L base relLo relHi seed bb start : Nat) :
    PresReport :=
  let program := build (E1FringeArmProgram.armWitnessProgram S c L)
  let regs0 := armPresRegs base relLo relHi seed bb start
  let result :=
    E1Machine.run (E1FringeArmProgram.armWitnessStore w) program
      (4000 + salt) ⟨regs0, 0, false⟩
  let zeroResult :=
    E1Machine.run (E1FringeArmProgram.armWitnessStore w) program
      (4000 + salt)
      ⟨E1FringeArmProgram.armWitnessRegs base relLo relHi seed bb start,
        0, false⟩
  let clobbered :=
    armUntouchedRegs.filter fun r => result.final.regs r != regs0 r
  { clobbered := clobbered
    checkedRegs := armUntouchedRegs.length
    reachedExit := result.final.pc == 97 && result.final.halted
    modeledSteps := result.steps
    value := result.final.regs E1FringeArmBlock.fRV
    position := result.final.regs E1FringeArmBlock.fRP
    zeroSeedValue := zeroResult.final.regs E1FringeArmBlock.fRV
    zeroSeedPosition := zeroResult.final.regs E1FringeArmBlock.fRP
    preserved := clobbered.isEmpty
    agreesWithZeroSeed :=
      result.final.regs E1FringeArmBlock.fRV ==
          zeroResult.final.regs E1FringeArmBlock.fRV &&
        result.final.regs E1FringeArmBlock.fRP ==
          zeroResult.final.regs E1FringeArmBlock.fRP }

def presReports (salt : Nat) (build : List Instr -> List Instr) :
    List PresReport :=
  armCases.map fun (w, S, c, L, base, relLo, relHi, seed, bb, start) =>
    runPres salt build w S c L base relLo relHi seed bb start

def presFailures (rs : List PresReport) : Nat :=
  (rs.filter (fun r => !r.preserved)).length

def presExitFailures (rs : List PresReport) : Nat :=
  (rs.filter (fun r => !r.reachedExit)).length

def presSeedDisagreements (rs : List PresReport) : Nat :=
  (rs.filter (fun r => !r.agreesWithZeroSeed)).length

/-- Every register any fixture found clobbered, deduplicated -- so a
failure names the offending registers rather than just counting. -/
def presClobberedRegs (rs : List PresReport) : List Nat :=
  dedupList (rs.flatMap PresReport.clobbered)

def goodPres : List Instr -> List Instr := id

/-- MUTANT G: rename the global-rebase epilogue's SCRATCH register from
`fT` (60, inside the fold bank) to 70, consistently across all three of
its occurrences.

The epilogue (`E1FringeArmBlock.lean:715`) uses `fT` as a private unit
constant: `const fT 1`, `brNZ fT (E+7)`, `sub fRV fBV fT`.  Renaming it
consistently computes the IDENTICAL `fRV`/`fRP`, in the identical number
of steps, on the identical control path, with the identical (empty)
epilogue receipt -- the mutant is invisible to phase 3f's receipt check
and to any value check whatsoever.

What it does do is scribble on register 70, which `FringeArmUntouched`
claims survives.  In the cross-block layout 70 is `fClose`, the query
operand the repoint and both right-hand preambles read -- so this is not
a contrived target: this exact clobber would silently compute the right
answer here and the wrong window on the other side of the interior.

The arm sits at host base `2` and its epilogue occupies indices 90..96,
which is the whole tail of `armWitnessProgram`. -/
def renameEpilogueScratch : Instr -> Instr
  | .const d v => if d == 60 then .const 70 v else .const d v
  | .brNZ c t => if c == 60 then .brNZ 70 t else .brNZ c t
  | .sub d s1 s2 => if s2 == 60 then .sub d s1 70 else .sub d s1 s2
  | other => other

def mutatedArmScratch (program : List Instr) : List Instr :=
  program.take 90 ++ (program.drop 90).map renameEpilogueScratch

def presMutationIsReal : Bool :=
  let honest := E1FringeArmProgram.armWitnessProgram 7 2 4
  let mutant := mutatedArmScratch honest
  honest != mutant && honest.length == mutant.length &&
    honest.map Instr.category == mutant.map Instr.category

/-- Mutant G is PRESERVATION-ONLY: case for case its exit pc, halted flag,
modeled step count, value and position all match the honest sweep, so
neither of this harness's earlier two discriminators can see it.

This is the third corner of the complementarity argument, executed rather
than asserted: D was value-only, E was receipt-only, G is
preservation-only. -/
def presMutantGIsPreservationOnly (salt : Nat) : Bool :=
  let honest := presReports salt goodPres
  let mutant := presReports salt mutatedArmScratch
  honest.length == mutant.length &&
    (List.zip honest mutant).all fun (h, m) =>
      h.reachedExit == m.reachedExit && h.modeledSteps == m.modeledSteps &&
        h.value == m.value && h.position == m.position

/-! ## Phase 3i/4h: the INTERIOR chunk fold's preservation clause, executed

Phase 3h executes the FRINGE ARM's preservation clause.  The interior's
eight-capped chunk fold states the same kind of clause --
`ChunkFoldUntouched` (`E1InteriorChunkFold.lean:928`), carried by the
headline `interiorChunkFold_runsTo` (`E1InteriorChunkFold.lean:1835`) --
and until this phase NOTHING executed it.

A CORRECTION THIS PHASE FORCES, AND ITS OWN LATER SUPERSESSION.  It is
natural to describe this phase as porting a check the fringe side already
runs on its fold.  When this phase landed, the fringe side did not run
one: phase 3h runs `FringeArmUntouched` (`E1FringeArmBlock.lean:951`),
the ARM's write set, and the fringe FOLD's own clause,
`FringeFoldUntouched` (`E1FringeFoldBlock.lean:962`), was unexecuted.  So
this WAS the first executed fold-level preservation check in the tree, on
either side, and not a port of an existing one.

That is now history rather than current fact, and the sentence this note
originally carried -- "the string `FringeFoldUntouched` does not occur in
this file" -- became FALSE when phases 3k/4j landed below (`:2010`
onward), which execute exactly that clause.  Corrected here rather than
left standing: a note that asserts its own file's contents is checkable by
`grep`, and one that has stopped being true is worse than no note.

WHY THE SENTINELS MATTER, restated for the interior's bank rather than
borrowed.  The fold's own hosting witness seeds `fun _ => 0` and writes
only `iIdx` (`witnessRegs`, `E1InteriorChunkFold.lean:1924`).  On that
register file a preservation check is VACUOUS in the exact sense M3d-9
named: a fold that ZEROED a register it does not own would still
"preserve" it, because the register was already zero.  `presSentinel` is
injective and nowhere zero, so a clobber is detectable whatever value it
writes, and a register copied in from elsewhere stays distinguishable
from one left alone.

WHY THE FOLD'S OWN BANK IS SEEDED TOO.  `presSentinel` also seeds
`89..99`, with values the fold must overwrite before it reads them.  The
zero-seeded re-run then tests exactly that: `cW` (94), `cT` (95), `cU`
(96) and `cOut` (99) are the four bank slots `interiorChunkInit` does NOT
initialise, so if any were read before being written, the two seedings
would disagree.  That is a second obligation, not a restatement of the
first.

WHY THE FIXTURES ARE MULTI-CHUNK.  A single-chunk fixture does not
exercise the fold as a fold -- it degenerates to the atom the predecessor
block already covers.  Three of the four indices below read TWO chunks
(`chunkFoldWitness_readCounts` = `[2, 2, 2, 1]`), and
`chunkPresMultiChunkCases` reports that count rather than assuming it.
-/

/-- The registers `ChunkFoldUntouched` claims survive the fold, as a
concrete list.  Mirrors the predicate `r < 89 ∨ 99 < r` LITERALLY.

The range runs past the summary group's bank (`sBlock`..`sArg`, 100..104,
`E1InteriorSummaryGroup.lean:76-84`) so that the slots the interior's own
composition carries ACROSS a fold call are actually among the registers
checked -- otherwise the phase would check only the registers below the
bank and miss the composition's real exposure. -/
def chunkUntouchedRegs : List Nat :=
  (List.range 110).filter fun r => r < 89 || 99 < r

/-- Register file for an interior preservation fixture: every register
carries its distinct sentinel, then the fold's ONE genuine input -- the
logical index `iIdx` (85) -- is written over.
`interiorChunkFold_runsTo` declares exactly that one input
(`hIdx : regs iIdx = i`), which is why one write suffices here where the
arm's fixture needed seven. -/
def chunkPresRegs (i : Nat) : RegFile :=
  RegFile.write presSentinel E1InteriorReadBlock.iIdx i

/-- The four executed paths of the fold's hosting witness: both chunks
present, second chunk missing, both missing, and the dead path.  Taken
from `chunkFoldWitness_path_*` (`E1InteriorChunkFold.lean:1938-1963`). -/
def chunkPresCases : List Nat := [0, 1, 2, 5]

/-- What one interior preservation fixture reports. -/
structure ChunkPresReport where
  index : Nat
  clobbered : List Nat
  checkedRegs : Nat
  reachedExit : Bool
  modeledSteps : Nat
  cell : Nat
  reads : List TraceEvent
  zeroSeedCell : Nat
  zeroSeedReads : List TraceEvent
  preserved : Bool
  agreesWithZeroSeed : Bool
deriving Repr

/-- RUN THE INTERIOR FOLD on a sentinel-seeded register file and check the
preservation clause register by register.

Also re-runs the SAME fixture zero-seeded -- on the fold's own
`witnessRegs` -- and compares both the returned cell AND the read log
event by event. -/
def runChunkPres (salt : Nat) (build : List Instr -> List Instr) (i : Nat) :
    ChunkPresReport :=
  let program := build E1InteriorChunkFold.chunkFoldWitness
  let regs0 := chunkPresRegs i
  let result :=
    E1Machine.run E1InteriorChunkFold.witnessStore program (128 + salt)
      ⟨regs0, 0, false⟩
  let zeroResult :=
    E1Machine.run E1InteriorChunkFold.witnessStore program (128 + salt)
      ⟨E1InteriorChunkFold.witnessRegs i, 0, false⟩
  let clobbered :=
    chunkUntouchedRegs.filter fun r => result.final.regs r != regs0 r
  { index := i
    clobbered := clobbered
    checkedRegs := chunkUntouchedRegs.length
    reachedExit := result.final.pc == 37 && result.final.halted
    modeledSteps := result.steps
    cell := result.final.regs E1InteriorChunkFold.cOut
    reads := result.readLog
    zeroSeedCell := zeroResult.final.regs E1InteriorChunkFold.cOut
    zeroSeedReads := zeroResult.readLog
    preserved := clobbered.isEmpty
    agreesWithZeroSeed :=
      result.final.regs E1InteriorChunkFold.cOut ==
          zeroResult.final.regs E1InteriorChunkFold.cOut &&
        result.readLog == zeroResult.readLog }

def chunkPresReports (salt : Nat) (build : List Instr -> List Instr) :
    List ChunkPresReport :=
  chunkPresCases.map (runChunkPres salt build)

def chunkPresFailures (rs : List ChunkPresReport) : Nat :=
  (rs.filter (fun r => !r.preserved)).length

def chunkPresExitFailures (rs : List ChunkPresReport) : Nat :=
  (rs.filter (fun r => !r.reachedExit)).length

def chunkPresSeedDisagreements (rs : List ChunkPresReport) : Nat :=
  (rs.filter (fun r => !r.agreesWithZeroSeed)).length

/-- Every register any fixture found clobbered, deduplicated. -/
def chunkPresClobberedRegs (rs : List ChunkPresReport) : List Nat :=
  dedupList (rs.flatMap ChunkPresReport.clobbered)

/-- ANTI-VACUITY: how many fixtures read more than one chunk.  A sweep of
single-chunk fixtures would exercise the atom, not the fold. -/
def chunkPresMultiChunkCases (rs : List ChunkPresReport) : Nat :=
  (rs.filter (fun r => r.reads.length > 1)).length

def goodChunkPres : List Instr -> List Instr := id

/-- Substitute register `a` by register `b` in REGISTER POSITIONS ONLY.

The non-register fields are left alone by construction: `const`'s value,
`mulConst`/`divConst`'s scale, `readMem`'s segment, and -- the one a
blanket numeral rewrite would silently corrupt -- `brNZ`'s absolute
branch TARGET. -/
def substReg (a b : Nat) : Instr -> Instr :=
  let m := fun r => if r == a then b else r
  fun
  | .readMem d seg ar => .readMem (m d) seg (m ar)
  | .const d v => .const (m d) v
  | .move d s => .move (m d) (m s)
  | .add d s1 s2 => .add (m d) (m s1) (m s2)
  | .sub d s1 s2 => .sub (m d) (m s1) (m s2)
  | .mulConst d s k => .mulConst (m d) (m s) k
  | .divConst d s k => .divConst (m d) (m s) k
  | .natLt d s1 s2 => .natLt (m d) (m s1) (m s2)
  | .natLe d s1 s2 => .natLe (m d) (m s1) (m s2)
  | .natEq d s1 s2 => .natEq (m d) (m s1) (m s2)
  | .brNZ c t => .brNZ (m c) t
  | .halt => .halt

/-- The register mutant H scribbles on: `102`, which is
`E1InteriorSummaryGroup.sMin` (`E1InteriorSummaryGroup.lean:80`).

Stated as a LITERAL rather than as the symbol, deliberately: this
validator does not import the summary group, so the phase's build does
not depend on a module outside this lane.  What the discriminator needs
of `102` is only that it satisfies `ChunkFoldUntouched` (`99 < 102`) and
is not a fold input, both of which are local facts.  The `sMin`
identification below is the LEGITIMACY argument, not a soundness
dependency. -/
def chunkClobberTarget : Nat := 102

/-- MUTANT H: rename the COMBINE loop's private scratch `cU` (96, inside
the fold bank `89..99`) to `102`, consistently across its three
occurrences, and ONLY within the combine segment.

WHY IT IS INVISIBLE TO THE VALUE.  In `interiorChunkCombine`
(`E1InteriorChunkFold.lean:316`) `cU` is written at `MB+1`
(`mulConst cU cT wordScale`) before it is read at `MB+2`
(`sub cU cAcc cU`) and `MB+4` (`add cRev cRev cU`), and is never read
after.  So it is a pure private temp whose incoming value cannot matter
and whose outgoing value nothing consumes; renaming it consistently
performs the identical arithmetic into `cRev`.

WHY IT IS INVISIBLE TO THE RECEIPT.  The combine loop is READ-FREE by
construction -- no `readMem` appears in it -- so the mutation cannot
move, add or drop a single trace event.  Its trip count is driven by
`cN`, not by `cU`, so the step count and control path are identical too.

WHY `102` IS NOT A CONTRIVED TARGET.  This is the register at which the
interior's OWN composition consumes the clause: the summary group's proof
instantiates the fold's preservation hypotheses at exactly this slot --
`hPres4 sMin`, `hPres3 sMin` (`E1InteriorSummaryGroup.lean:427-429`) --
to carry a staged minimum across LATER fold invocations.  A clobber here
computes the right cell for this invocation and destroys the running
minimum the next one needs, which is precisely the defect the clause
exists to exclude and precisely what the other two discriminators cannot
see.

WHY THE CLOBBER IS ROBUSTLY DETECTED.  The target is not a fold input, so
it carries `presSentinel 102 = 717`.  The value the combine loop writes
is a base-`wordScale` digit, which on this witness is `0` or `1`.  So
detection does not depend on the mutant happening to write a value that
differs from the seed -- the ranges are disjoint.

The combine segment occupies fold indices `26..33` (init 17 + read body
9), and `chunkFoldWitness` hosts the fold at base `0`, so those are
program indices too. -/
def mutatedCombineScratch (program : List Instr) : List Instr :=
  program.take 26
    ++ ((program.drop 26).take 8).map
        (substReg E1InteriorChunkFold.cU chunkClobberTarget)
    ++ program.drop 34

def chunkPresMutationIsReal : Bool :=
  let honest := E1InteriorChunkFold.chunkFoldWitness
  let mutant := mutatedCombineScratch honest
  honest != mutant && honest.length == mutant.length &&
    honest.map Instr.category == mutant.map Instr.category

/-- Mutant H is PRESERVATION-ONLY: case for case its exit pc, halted flag,
modeled step count, returned cell AND read log all match the honest
sweep, so neither the value discriminator nor the receipt discriminator
can see it.

The receipt is compared event by event, not by length or count.  That
matters on this block specifically: `chunkFoldWitness_paths_distinguishable`
(`E1InteriorChunkFold.lean:2004`) records that its paths 2 and 3 agree on
BOTH modeled steps and returned cell and are separated ONLY by the read
log, so a weaker receipt check would be the wrong instrument here. -/
def chunkMutantHIsPreservationOnly (salt : Nat) : Bool :=
  let honest := chunkPresReports salt goodChunkPres
  let mutant := chunkPresReports salt mutatedCombineScratch
  honest.length == mutant.length &&
    (List.zip honest mutant).all fun (h, m) =>
      h.reachedExit == m.reachedExit && h.modeledSteps == m.modeledSteps &&
        h.cell == m.cell && h.reads == m.reads

/-! ### The same three facts, KERNEL-CHECKED rather than printed

`mainImpl` prints these counts, which makes them reproducible but not
proved: a printed `0` is evidence, and the kernel has not seen it.  The
quantities are closed and computable, so they are also stated as theorems
and discharged by `rfl` -- no `decide`, no compiler-evaluated escape
hatch, no raised heartbeat budget.  (The escape hatch is named in
`AGENTS.md`; the name is kept out of `RMQ/` so the house scan for it
stays at zero, per CHK-B4-02.)

The salt is `0` here on purpose.  Its only job in `mainImpl` is to stop
Lean folding the sweeps before `main` starts, which would make the
wall-clock readings meaningless; in a theorem compile-time evaluation is
exactly what is wanted.
-/

/-- The honest fold disturbs NOTHING outside its bank, on all four paths.
This is `ChunkFoldUntouched`'s content at the fold's own witness. -/
theorem chunkPres_honest_clobbers_nothing :
    chunkPresClobberedRegs (chunkPresReports 0 goodChunkPres) = [] := rfl

/-- Mutant H disturbs EXACTLY register `102` and nothing else -- so the
phase does not merely report a failure, it names the register the
interior's composition would have lost. -/
theorem chunkPres_mutantH_clobbers_exactly_102 :
    chunkPresClobberedRegs (chunkPresReports 0 mutatedCombineScratch)
      = [102] := rfl

/-- Every one of the four fixtures catches mutant H. -/
theorem chunkPres_mutantH_caught_on_every_case :
    chunkPresFailures (chunkPresReports 0 mutatedCombineScratch) = 4 := rfl

/-- ...and none of them catches it by exit pc, which is what makes the
previous theorem a statement about PRESERVATION rather than about the
mutant merely crashing. -/
theorem chunkPres_mutantH_reaches_exit_everywhere :
    chunkPresExitFailures (chunkPresReports 0 mutatedCombineScratch) = 0 :=
  rfl

/-- THE DISCRIMINATOR STATEMENT, kernel-checked: mutant H agrees with the
honest sweep case for case on exit pc, halted flag, modeled steps,
returned cell and read log.  With the two theorems above, this says the
mutation is caught by preservation and by nothing else this harness
has. -/
theorem chunkPres_mutantH_is_preservation_only :
    chunkMutantHIsPreservationOnly 0 = true := rfl

/-- ANTI-VACUITY, kernel-checked: three of the four fixtures read more
than one chunk, so the sweep exercises the FOLD and not the single-chunk
atom that `E1InteriorReadBlock` already covers. -/
theorem chunkPres_sweep_is_multiChunk :
    chunkPresMultiChunkCases (chunkPresReports 0 goodChunkPres) = 3 := rfl

/-- ANTI-VACUITY, kernel-checked: the seeded file is nowhere zero at the
clobber target, and the seed lies outside the range of values the combine
loop can write there (`cAcc % wordScale`, so `0` or `1` on this witness).
Detection therefore does not depend on the mutant writing a value that
happens to differ from the seed. -/
theorem chunkPres_target_seed_outside_written_range :
    presSentinel chunkClobberTarget = 717 := rfl

/-! ## REQ-E1-05: the guard skeleton, EXECUTED on invalid fixtures

REQ-E1-05's Evidence-needed column asks for the invalid guard to be
"exercised on empty, reversed, and out-of-bounds fixtures in Lean examples
and in the validator".  The Lean examples exist
(`programSkeleton_invalid_matches_public_guard`, `E1QueryBridge.lean:55`,
universally quantified over `validPath`).  The validator half did not: nothing
outside `E1QueryProgram.lean`, `E1QueryBridge.lean` and
`E1WholeQueryPublic.lean` mentioned `programSkeleton`, and this harness never
ran it.  These fixtures RUN it.

**WHY THERE ARE VALID CONTROLS, and why the phase would be worthless without
them.**  A sweep containing only invalid ranges cannot distinguish the real
guard from a machine that rejects EVERYTHING -- `const regOut 0; halt` at
`pc = 0` passes every invalid check below.  So the sweep carries valid
controls whose required outcome is the OPPOSITE: they must reach the stub
valid path and leave a non-`none` packet.  `guardAcceptedCount` is the
anti-vacuity metric, and it is asserted `> 0` in the verdict rather than
merely printed.
-/

/-- Stub valid path for the guard fixtures: write a non-`none` packet and
halt.  Its only job is to be DISTINGUISHABLE from the invalid exit, so that a
valid control which reaches it is visibly not a rejection. -/
def guardStubValidPath : List Instr :=
  [ .const E1Query.regOut 1, .halt ]

/-- Any store: the guard performs no read.  This one answers every address
with a non-empty word, so a stray read would both register in the receipt AND
perturb a value -- a store answering `none` would hide the second effect. -/
def guardStore : ReadStore := ⟨fun _ _ => some [true]⟩

structure GuardReport where
  family : String
  expectedValid : Bool
  n : Nat
  left : Nat
  right : Nat
  halted : Bool
  modeledSteps : Nat
  readCount : Nat
  memoryReadCharges : Nat
  packetIsNone : Bool
  ok : Bool
deriving Repr

/-- RUN the guard skeleton on one fixture and check the whole REQ-E1-05
clause list: halts, `none` packet, EMPTY receipt, zero memory-read charge,
and at most ten charged steps.  Valid controls are checked for the opposite
outcome. -/
def runGuard (salt : Nat) (build : E1Machine.Program -> E1Machine.Program)
    (family : String) (expectedValid : Bool)
    (n left right : Nat) : GuardReport :=
  let program := build (E1Query.programSkeleton n guardStubValidPath)
  let result :=
    E1Machine.run guardStore program (64 + salt)
      (E1Query.initialState left right)
  let isNone :=
    E1Query.decodePacket (result.final.regs E1Query.regOut) == none
  { family := family
    expectedValid := expectedValid
    n := n, left := left, right := right
    halted := result.final.halted
    modeledSteps := result.steps
    readCount := result.readLog.length
    memoryReadCharges := catCount result.catLog Category.memoryRead
    packetIsNone := isNone
    ok :=
      if expectedValid then
        result.final.halted && !isNone
      else
        result.final.halted && isNone && result.readLog.isEmpty &&
          catCount result.catLog Category.memoryRead == 0 &&
          result.steps <= 10 }

/-- The three invalid families REQ-E1-05 names, plus valid controls.
`n` is the modelled input length; `left`/`right` the query operands. -/
def guardCases : List (String × Bool × Nat × Nat × Nat) :=
  [ ("empty",        false, 0, 0, 0)
  , ("empty",        false, 0, 0, 1)
  , ("emptyRange",   false, 8, 3, 3)
  , ("emptyRange",   false, 8, 0, 0)
  , ("reversed",     false, 8, 5, 2)
  , ("reversed",     false, 8, 7, 1)
  , ("outOfBounds",  false, 8, 0, 9)
  , ("outOfBounds",  false, 8, 3, 100)
  , ("valid",        true,  8, 0, 8)
  , ("valid",        true,  8, 2, 5)
  , ("valid",        true,  1, 0, 1) ]

def goodGuard : E1Machine.Program -> E1Machine.Program := id

/--
MUTANT J: disable the OUT-OF-BOUNDS half of the guard, leaving the
empty/reversed half intact.

Instruction `7` of the skeleton is `brNZ regG invalidBase`, the branch taken
when `right <= n` FAILS.  The mutant repoints its CONDITION register from
`regG` (the live negation flag) to `regZero`, which the prologue pins to `0`,
so the branch is never taken and an out-of-bounds query falls through into
the valid path.

It is the "right shape, wrong content" defect class at the guard: the program
has the SAME length and the SAME per-instruction category log -- a `brNZ` is
still a `brNZ` -- so neither a length check nor a category-shape check can see
it.  What sees it is that two of the eight invalid fixtures stop being
rejected.
-/
def mutatedGuardBounds (p : E1Machine.Program) : E1Machine.Program :=
  p.set 7 (.brNZ E1Query.regZero (8 + guardStubValidPath.length))

def guardMutationIsReal : Bool :=
  let honest := E1Query.programSkeleton 8 guardStubValidPath
  let mutant := mutatedGuardBounds honest
  honest != mutant && honest.length == mutant.length &&
    honest.map Instr.category == mutant.map Instr.category

def guardReports (salt : Nat)
    (build : E1Machine.Program -> E1Machine.Program) : List GuardReport :=
  guardCases.map fun (family, expectedValid, n, left, right) =>
    runGuard salt build family expectedValid n left right

def guardFailures (rs : List GuardReport) : Nat :=
  (rs.filter (fun r => !r.ok)).length

/-- Invalid fixtures that actually reached the guarded `none` packet. -/
def guardRejectedCount (rs : List GuardReport) : Nat :=
  (rs.filter (fun r => !r.expectedValid && r.packetIsNone)).length

/-- ANTI-VACUITY METRIC: valid controls the guard did NOT reject.  A machine
that rejects everything scores `0` here and passes every other check in this
phase. -/
def guardAcceptedCount (rs : List GuardReport) : Nat :=
  (rs.filter (fun r => r.expectedValid && !r.packetIsNone)).length

/-- Worst charged step count over the invalid fixtures, against the frozen
`<= 10` of `guardRejectCats_length_le`. -/
def guardMaxInvalidSteps (rs : List GuardReport) : Nat :=
  (rs.filter (fun r => !r.expectedValid)).foldl
    (fun acc r => Nat.max acc r.modeledSteps) 0

/-- Every fixture, invalid and valid alike, meets its own clause list. -/
theorem guard_all_cases_ok : guardFailures (guardReports 0 goodGuard) = 0 :=
  rfl

/-- All eight invalid fixtures reach the guarded `none` packet. -/
theorem guard_invalid_all_rejected :
    guardRejectedCount (guardReports 0 goodGuard) = 8 := rfl

/-- ANTI-VACUITY, kernel-checked: all three valid controls are ACCEPTED, so
the phase is not passing merely because the machine rejects everything. -/
theorem guard_valid_controls_accepted :
    guardAcceptedCount (guardReports 0 goodGuard) = 3 := rfl

/-- The invalid path's charged step count never exceeds the frozen `10`. -/
theorem guard_invalid_steps_within_ten :
    guardMaxInvalidSteps (guardReports 0 goodGuard) = 10 := rfl

/-- The mutation is REAL and SHAPE-PRESERVING: a different program, of the
same length, with the identical per-instruction category log. -/
theorem guard_mutation_is_real : guardMutationIsReal = true := rfl

/-- MUTANT J IS CAUGHT: the THREE fixtures whose rejection depends on the
`right <= n` test stop being rejected -- the two labelled `outOfBounds` plus
`("empty", n = 0, 0, 1)`, which is an out-of-bounds query at an empty list --
so the rejected count falls from `8` to `5`. -/
theorem guard_mutantJ_caught :
    guardRejectedCount (guardReports 0 mutatedGuardBounds) = 5 := rfl

/-- ...and it is caught by REJECTION, not by the phase falling over: the
mutant still ACCEPTS all three valid controls, exactly as the honest guard
does.  So the discriminator is the invalid half specifically, and a harness
checking only that valid queries survive would MISS this defect entirely. -/
theorem guard_mutantJ_still_accepts_valid_controls :
    guardAcceptedCount (guardReports 0 mutatedGuardBounds) = 3 := rfl

/-! ## Phase 3k/4j: the FRINGE fold's OWN preservation clause, executed

Phase 3h runs the fringe ARM and checks `FringeArmUntouched`.  Phase 3i
runs the INTERIOR fold and checks `ChunkFoldUntouched`.  The fringe FOLD's
own clause, `FringeFoldUntouched` (`E1FringeFoldBlock.lean:962`), was
executed by neither, and the note at the head of phase 3i says so.

WHY IT CANNOT BE FOLDED INTO PHASE 3H.  `FringeFoldUntouched`
(`r < 40 ∨ 63 ≤ r`) is STRICTLY STRONGER than `FringeArmUntouched`
(`r < 40 ∨ (63 ≤ r ∧ r ≠ 67 ∧ r ≠ 68)`).  Running the whole arm and
checking the fold's predicate would FAIL at `67` and `68` -- and fail
CORRECTLY, because the arm's prologue writes them while the fold does not.
The observation would say nothing about the fold.  So the fold is run
STANDALONE at its own loop base, on
`E1FringeFoldProgram.foldWitnessProgram` (base `2`, exit `69`), whose four
hosting facts are discharged against `fringeFoldLoop_runsTo_accepted`'s
hypotheses in `foldWitnessProgram_hosts`.

The checked bank is `40..62` exactly, which is the fold's OWN write set
(`fOne = 40` through `fX = 62`), so this is the block's own clause and not
a neighbour's borrowed one.
-/

/-- Register file for a fringe-fold fixture: every register carries its
distinct sentinel, then the fold's twelve declared inputs are written over.
Seeded from `fun _ => 0` this phase would be VACUOUS -- a block that zeroes
a register it does not own still "preserves" it -- so `presSentinel` is
reused here for the same reason phase 3h gives. -/
def foldPresRegs (c relLo relHi seed count w0 w1 w2 w3 : Nat) : RegFile :=
  RegFile.write (RegFile.write (RegFile.write (RegFile.write
    (RegFile.write (RegFile.write (RegFile.write (RegFile.write
      (RegFile.write (RegFile.write (RegFile.write (RegFile.write
        presSentinel E1FringeFoldBlock.fOne 1) E1FringeFoldBlock.fC c)
        E1FringeFoldBlock.fLo relLo) E1FringeFoldBlock.fHi relHi)
        E1FringeFoldBlock.fJC 0) E1FringeFoldBlock.fCnt count)
        E1FringeFoldBlock.fAcc seed) E1FringeFoldBlock.fBV 0)
        E1FringeFoldBlock.fW0 w0) E1FringeFoldBlock.fW1 w1)
        E1FringeFoldBlock.fW2 w2) E1FringeFoldBlock.fW3 w3

/-- The registers `FringeFoldUntouched` claims survive the fold, as a
concrete list over the bank the machine actually uses.  Mirrors the
predicate `r < 40 ∨ 63 ≤ r` literally. -/
def foldUntouchedRegs : List Nat :=
  (List.range 110).filter fun r => r < 40 || 63 <= r

/-- Fixtures: window word, segment, chunk width, word width, then the
fold's range, seed, trip count and four window registers.  The trip counts
are all `> 0`, so every fixture runs at least one full pass. -/
def foldPresCases :
    List (List Bool × Nat × Nat × Nat × Nat × Nat × Nat ×
      Nat × Nat × Nat × Nat × Nat) :=
  [[true, false, true, false], [false, false, false, false],
    [true, true, true, true]].flatMap fun w =>
    [(2, 5), (1, 3), (2, 1)].flatMap fun (c, relHi) =>
      [(1 : Nat), 2, 3].map fun count =>
        (w, 7, c, 4, 0, relHi, 0, count, 11, 5, 9, 3)

/-- What one fringe-fold preservation fixture reports. -/
structure FoldPresReport where
  clobbered : List Nat
  checkedRegs : Nat
  reachedExit : Bool
  modeledSteps : Nat
  acc : Nat
  bestValue : Nat
  bestPos : Nat
  reads : List TraceEvent
  zeroSeedAcc : Nat
  zeroSeedReads : List TraceEvent
  preserved : Bool
  agreesWithZeroSeed : Bool
deriving Repr

/-- RUN THE FRINGE FOLD STANDALONE on a sentinel-seeded register file and
check its own preservation clause register by register.

Also re-runs the SAME fixture zero-seeded, on the fold's own
`foldWitnessRegs`, and compares both the accumulator AND the read log event
by event -- so this doubles as evidence that the fold reads no register it
does not initialise. -/
def runFoldPres (salt : Nat) (build : List Instr -> List Instr)
    (w : List Bool) (S c L relLo relHi seed count w0 w1 w2 w3 : Nat) :
    FoldPresReport :=
  let program := build (E1FringeFoldProgram.foldWitnessProgram S c L)
  let regs0 := foldPresRegs c relLo relHi seed count w0 w1 w2 w3
  let store := E1FringeFoldProgram.foldWitnessStore w
  let result := E1Machine.run store program (4000 + salt) ⟨regs0, 2, false⟩
  let zeroResult :=
    E1Machine.run store program (4000 + salt)
      ⟨E1FringeFoldProgram.foldWitnessRegs c relLo relHi seed count
        w0 w1 w2 w3, 2, false⟩
  let clobbered :=
    foldUntouchedRegs.filter fun r => result.final.regs r != regs0 r
  { clobbered := clobbered
    checkedRegs := foldUntouchedRegs.length
    reachedExit := result.final.pc == 69
    modeledSteps := result.steps
    acc := result.final.regs E1FringeFoldBlock.fAcc
    bestValue := result.final.regs E1FringeFoldBlock.fBV
    bestPos := result.final.regs E1FringeFoldBlock.fBP
    reads := result.readLog
    zeroSeedAcc := zeroResult.final.regs E1FringeFoldBlock.fAcc
    zeroSeedReads := zeroResult.readLog
    preserved := clobbered.isEmpty
    agreesWithZeroSeed :=
      result.final.regs E1FringeFoldBlock.fAcc ==
          zeroResult.final.regs E1FringeFoldBlock.fAcc &&
        result.readLog == zeroResult.readLog }

def foldPresReports (salt : Nat) (build : List Instr -> List Instr) :
    List FoldPresReport :=
  foldPresCases.map fun (w, S, c, L, relLo, relHi, seed, count, a, b, d, e) =>
    runFoldPres salt build w S c L relLo relHi seed count a b d e

def foldPresFailures (rs : List FoldPresReport) : Nat :=
  (rs.filter (fun r => !r.preserved)).length

def foldPresExitFailures (rs : List FoldPresReport) : Nat :=
  (rs.filter (fun r => !r.reachedExit)).length

def foldPresSeedDisagreements (rs : List FoldPresReport) : Nat :=
  (rs.filter (fun r => !r.agreesWithZeroSeed)).length

def foldPresClobberedRegs (rs : List FoldPresReport) : List Nat :=
  (rs.flatMap (fun r => r.clobbered)).eraseDups

/-- Fixtures whose read log is nonempty -- the fold is READ-BEARING, one
charged read per pass, so a sweep with an empty log would be observing
nothing. -/
def foldPresReadBearingCases (rs : List FoldPresReport) : Nat :=
  (rs.filter (fun r => !r.reads.isEmpty)).length

def goodFoldPres : List Instr -> List Instr := id

/-- The register mutant K scribbles on: `105`, outside the fold's bank and
so inside `FringeFoldUntouched`. -/
def foldClobberTarget : Nat := 105

/-- MUTANT K: rename the fold's private scratch `fX` (62, inside the bank
`40..62`) to `105`, consistently across every occurrence in the loop body.

WHY IT IS INVISIBLE TO THE VALUE.  `fX` is WRITE-FIRST wherever it appears.
In `fringePrefix` (`E1FringeFoldBlock.lean:146`) its first mention is
`sub fX fT fU`, a write, before the read in `sub fB fT fX`.  In
`fringeShift` (`E1FringeFoldBlock.lean:223`) each of the three window
groups opens with `mulConst fX fU (2 ^ c)`, again a write, before the two
reads that consume it, and nothing reads it after `add fW2 fT fX`.  So its
incoming value cannot matter and its outgoing value is consumed by nobody
-- a consistent rename performs the identical arithmetic.

WHY IT IS INVISIBLE TO THE RECEIPT.  This one needs care rather than the
usual read-free argument, because the fold is NOT read-free.  `fX` does
reach the read: it feeds `fB`, which feeds `fSlot`, which is the address of
the single `readMem fE S fSlot`.  But the rename is CONSISTENT, so `fSlot`
receives the identical value and the read address is unchanged.  The trip
count is driven by `fCnt`, not `fX`, so the control path and step count are
identical too.

WHY `105` IS DETECTED ROBUSTLY.  It is not a fold input, so it carries
`presSentinel 105 = 738`, and it is above the bank, so
`FringeFoldUntouched 105` holds and the clause genuinely claims it. -/
def mutatedFoldScratch (program : List Instr) : List Instr :=
  program.map (substReg E1FringeFoldBlock.fX foldClobberTarget)

def foldPresMutationIsReal : Bool :=
  let honest := E1FringeFoldProgram.foldWitnessProgram 7 2 4
  let mutant := mutatedFoldScratch honest
  honest != mutant && honest.length == mutant.length &&
    honest.map Instr.category == mutant.map Instr.category

/-- Mutant K is PRESERVATION-ONLY: case for case its exit pc, modeled step
count, accumulator, best pair AND read log all match the honest sweep, so
neither the value discriminator nor the receipt discriminator can see it. -/
def foldMutantKIsPreservationOnly (salt : Nat) : Bool :=
  let honest := foldPresReports salt goodFoldPres
  let mutant := foldPresReports salt mutatedFoldScratch
  honest.length == mutant.length &&
    (List.zip honest mutant).all fun (h, m) =>
      h.reachedExit == m.reachedExit && h.modeledSteps == m.modeledSteps &&
        h.acc == m.acc && h.bestValue == m.bestValue &&
        h.bestPos == m.bestPos && h.reads == m.reads

/-! ### The same facts, KERNEL-CHECKED rather than printed

`mainImpl` prints these counts, which makes them reproducible but not
proved.  The quantities are closed and computable, so they are also stated
as theorems and discharged by `rfl`.  Every literal here was EVALUATED
first and then written down, per the standing rule on computable
quantities; none was predicted. -/

/-- The honest fold disturbs NOTHING outside its bank, on all 27 fixtures.
This is `FringeFoldUntouched`'s content at the fold's own witness, and it is
the first time that predicate has been executed anywhere. -/
theorem foldPres_honest_clobbers_nothing :
    foldPresClobberedRegs (foldPresReports 0 goodFoldPres) = [] := rfl

/-- The sweep is READ-BEARING on every fixture, so preservation is being
checked against a fold that actually ran and charged. -/
theorem foldPres_all_cases_read_bearing :
    foldPresReadBearingCases (foldPresReports 0 goodFoldPres) = 27 := rfl

/-- Mutant K disturbs EXACTLY register `105` and nothing else -- the phase
names the register rather than merely reporting a failure. -/
theorem foldPres_mutantK_clobbers_target :
    foldPresClobberedRegs (foldPresReports 0 mutatedFoldScratch) = [105] :=
  rfl

/-- ...and it is caught on EVERY fixture, not just one. -/
theorem foldPres_mutantK_caught :
    foldPresFailures (foldPresReports 0 mutatedFoldScratch) = 27 := rfl

/-- ...while the exit-pc discriminator sees NOTHING.  This is the
non-entailment that justifies the phase existing: a harness checking only
that the block reaches its exit would miss this defect completely. -/
theorem foldPres_mutantK_invisible_to_exit :
    foldPresExitFailures (foldPresReports 0 mutatedFoldScratch) = 0 := rfl

/-! ## Phase 3l/4k: STORE-VALUE DEPENDENCY, the missing anti-vacuity
witness for REQ-E1-03's `INV-VALUE-DEPENDENCY`

Every mutation this harness ran before this phase perturbs the PROGRAM:
mutant D (`:898`) an operand, mutant F (`:1344`) an instruction, mutant E a
branch target.  **None of them perturbs what the machine READS.**  So
nothing here yet separated a machine computing its answer from its own
reads from one whose answer never depended on a stored word at all -- both
survive an operand mutation in exactly the same way when the read is
decorative.

This phase perturbs the STORE.  It runs the fringe arm against
`armWitnessStore`, takes the `(segment, address)` cells the RECEIPT says
the machine actually read, and re-runs the arm once per cell with THAT CELL
ALONE returning a different word.  The claim established is a DEPENDENCY,
not a value: the answer MOVES when a word the machine read is corrupted.
Value correctness remains phase 3f's job, and this phase does not restate
it.

**The control is what makes this evidence rather than vandalism.**  A cell
the machine did NOT read is perturbed on the same terms, and the answer
must NOT move.  Without that control the phase could pass by corrupting the
store so violently that every run breaks; with it, the dependency is pinned
to exactly the cells on the receipt.  `controlCellUnread` checks the
control cell really is absent from the receipt rather than assuming it.

### THE DEPENDENCE IS A BICONDITIONAL, NOT A MAJORITY

The first version of this phase demanded that EVERY fixture be
read-dependent, and 21 of the 36 are not.  That was the check being wrong,
not the machine: the arm has two epilogue arms, and on the SEED-FALLBACK
arm the answer is the seed the caller supplied, which by construction does
not depend on any word read.  Phase 3f already relies on both arms
occurring (`armEpilogueCoverage`, `:1186`).

So the claim this phase establishes is sharper than "the answer usually
depends on the reads".  It is:

> corrupting a read cell moves the answer **exactly when** the arm takes
> its occupied (window-rebase) epilogue arm, and never otherwise.

Both directions are checked on every fixture by `dependenceMatchesArm`,
and the biconditional holds `36/36`.  The anti-vacuity clause is that BOTH
arms must actually occur in the sweep -- if every fixture took the
seed-fallback arm the biconditional would hold trivially and demonstrate
nothing, so `depOccupiedFixtures` and `depFallbackFixtures` must both be
positive.  They are `15` and `21`.

Note on the discipline: the perturbation is in the machine's INPUT, which
is the only place a read-dependency can be probed from.  It is not a
fixture edit -- the fixture, the program and the expectation are all held
fixed, and the reference side of this phase is the structural claim above,
which is not computed by calling the machine. -/

/-- `armWitnessStore w` with ONE cell returning a different word.  Bitwise
negation is used so the perturbed word has the same LENGTH as the honest
one: a shorter or longer word would change `decodeRead`'s magnitude for
reasons unrelated to the cell's contents. -/
def perturbedArmStore (w : List Bool) (seg addr : Nat) : ReadStore :=
  ⟨fun s a =>
    if s == seg && a == addr then some (w.map (fun b => !b)) else some w⟩

/-- What one store-dependency fixture reports. -/
structure DepReport where
  distinctReadCells : Nat
  movedCells : Nat
  controlMoved : Bool
  controlCellUnread : Bool
  wordDiffers : Bool
  readBearing : Bool
  /-- The arm ended on its SEED-FALLBACK epilogue arm, identified the way
  phase 3f identifies it (`:1182`): the position register still holds the
  seed's `start` rather than a window rebase. -/
  seedFallback : Bool
  /-- THE BICONDITIONAL: read-dependence is present exactly when the arm
  did NOT take the seed-fallback arm. -/
  dependenceMatchesArm : Bool
deriving Repr

/-- Run the arm honestly, then once per distinct receipt cell with that
cell alone corrupted, then once more on a cell it never read. -/
def runDep (salt : Nat) (w : List Bool)
    (S c L base relLo relHi seed bb start : Nat) : DepReport :=
  let program := E1FringeArmProgram.armWitnessProgram S c L
  let regs := E1FringeArmProgram.armWitnessRegs base relLo relHi seed bb start
  let honest :=
    E1Machine.run (E1FringeArmProgram.armWitnessStore w) program (4000 + salt)
      ⟨regs, 0, false⟩
  let cells := dedupList (honest.readLog.filterMap eventAddr)
  let baseV := honest.final.regs E1FringeArmBlock.fRV
  let baseP := honest.final.regs E1FringeArmBlock.fRP
  let moved := cells.filter fun cell =>
    let r :=
      E1Machine.run (perturbedArmStore w cell.1 cell.2) program (4000 + salt)
        ⟨regs, 0, false⟩
    r.final.regs E1FringeArmBlock.fRV != baseV ||
      r.final.regs E1FringeArmBlock.fRP != baseP
  -- CONTROL: a cell the machine did not read, perturbed on the same terms.
  let ctlCell : Nat × Nat := (0, base + 100000)
  let ctl :=
    E1Machine.run (perturbedArmStore w ctlCell.1 ctlCell.2) program
      (4000 + salt) ⟨regs, 0, false⟩
  let fallback := baseP == start
  { distinctReadCells := cells.length
    movedCells := moved.length
    controlMoved :=
      ctl.final.regs E1FringeArmBlock.fRV != baseV ||
        ctl.final.regs E1FringeArmBlock.fRP != baseP
    controlCellUnread := !cells.contains ctlCell
    wordDiffers := w.map (fun b => !b) != w
    readBearing := !honest.readLog.isEmpty
    seedFallback := fallback
    dependenceMatchesArm := (moved.length == 0) == fallback }

def depReports (salt : Nat) : List DepReport :=
  armCases.map fun (w, S, c, L, base, relLo, relHi, seed, bb, start) =>
    runDep salt w S c L base relLo relHi seed bb start

/-- Fixtures violating the biconditional: read-dependent on the fallback
arm, or read-INdependent on the occupied arm.  Must be `0`. -/
def depArmMismatches (rs : List DepReport) : Nat :=
  (rs.filter (fun r => !r.dependenceMatchesArm)).length

/-- Fixtures on the OCCUPIED epilogue arm, where the answer is a window
rebase and read-dependence is therefore required. -/
def depOccupiedFixtures (rs : List DepReport) : Nat :=
  (rs.filter (fun r => !r.seedFallback)).length

/-- Fixtures on the SEED-FALLBACK arm, where the answer is the caller's
seed and read-independence is correct rather than a defect. -/
def depFallbackFixtures (rs : List DepReport) : Nat :=
  (rs.filter (fun r => r.seedFallback)).length

/-- Fixtures where corrupting an UNREAD cell moved the answer.  Must be
`0`: a nonzero count would mean the perturbation is not localised and the
phase proves nothing about the receipt. -/
def depControlLeaks (rs : List DepReport) : Nat :=
  (rs.filter (fun r => r.controlMoved)).length

/-- Fixtures whose control cell turned out to be ON the receipt after all,
which would make `depControlLeaks` meaningless.  Must be `0`. -/
def depControlUnsound (rs : List DepReport) : Nat :=
  (rs.filter (fun r => !r.controlCellUnread)).length

/-- Total read cells whose corruption moved the answer, across the sweep. -/
def depTotalMovedCells (rs : List DepReport) : Nat :=
  rs.foldl (fun a r => a + r.movedCells) 0

/-- Total distinct read cells probed across the sweep. -/
def depTotalCells (rs : List DepReport) : Nat :=
  rs.foldl (fun a r => a + r.distinctReadCells) 0

/-- Fixtures where the perturbed word is not actually different, or the run
charged no read at all -- either makes the fixture vacuous.  Must be `0`. -/
def depVacuous (rs : List DepReport) : Nat :=
  (rs.filter (fun r => !r.wordDiffers || !r.readBearing)).length

/-! ## Phase 3m/4l: THE CATEGORY LOG as a discriminator in its own right

Before this phase the category log was **not a discriminator anywhere in
this file**.  `catLog` and `catCount` appeared four times in total, all
four inside `runGuard` (`:1902`, `:1909`), and both uses count ONE category
(`memoryRead`) rather than comparing logs.  Value, receipt and preservation
each had a mutant proved invisible to the other two; category accounting
had none.

This phase supplies one.

**MUTANT L is a category-neutral rewrite of a single instruction.**
`execInstr` gives `move d s` the value `R s` and the category
`registerWrite`, and `mulConst d s k` the value `R s * k` and the category
`arithmetic` (`E1Machine.lean:170` and `:178`).  At `k = 1` the two write
THE SAME VALUE into THE SAME REGISTER in ONE step, performing no read and
changing no control flow.  So the mutant agrees with the honest arm on
every observable this harness had: value, position, full receipt, exit pc,
halted flag, modeled step count, the LENGTH of the category log, and the
`memoryRead` charge count that is the only category statistic the file
computed before now.  What it changes is WHICH CATEGORY IS CHARGED at one
position.

**Scope, stated rather than left to be discovered.**  A category log
constrains which KINDS of instruction ran; it never constrains their
operands.  `mergePos_catLogs_agree` (`E1InteriorMerge.lean:519`) is the
proved counterexample in the other direction -- mutant-D-style operand
substitution takes the identical path and is invisible to a positional
category log, which is exactly why this phase does not replace the value
comparison but sits beside it.  A per-category CENSUS would also catch
mutant L (it moves one charge from `registerWrite` to `arithmetic`); what
no census, no length check and no step count can catch is nothing here --
the honest claim is that the positional log catches it and every
discriminator this harness ALREADY RAN does not.  `catMutantIsCategoryOnly`
checks that last clause case by case rather than asserting it. -/

/-- MUTANT L: the arm's FIRST `move dst src` becomes `mulConst dst src 1`.
Rewriting exactly one instruction, at the first `move` in program order
(index `60` in `armWitnessProgram`, inside the arm body -- the two padding
instructions at `0` and `1` are `const`, not `move`). -/
def moveToMulConst (program : List Instr) : List Instr :=
  match (List.range program.length).find? (fun i =>
      match program[i]? with
      | some (.move _ _) => true
      | _ => false) with
  | none => program
  | some i =>
      program.take i ++
        (match program[i]? with
         | some (.move d s) => [Instr.mulConst d s 1]
         | some other => [other]
         | none => []) ++
        program.drop (i + 1)

/-- The arm's category log for one fixture, under a given builder. -/
def armCatLogOf (salt : Nat) (build : List Instr -> List Instr)
    (w : List Bool) (S c L base relLo relHi seed bb start : Nat) :
    List Category :=
  (E1Machine.run (E1FringeArmProgram.armWitnessStore w)
    (build (E1FringeArmProgram.armWitnessProgram S c L)) (4000 + salt)
    ⟨E1FringeArmProgram.armWitnessRegs base relLo relHi seed bb start,
      0, false⟩).catLog

def armCatLogs (salt : Nat) (build : List Instr -> List Instr) :
    List (List Category) :=
  armCases.map fun (w, S, c, L, base, relLo, relHi, seed, bb, start) =>
    armCatLogOf salt build w S c L base relLo relHi seed bb start

/-- The arm's full RECEIPT for one fixture, under a given builder -- used to
check mutant L against receipt EQUALITY rather than receipt length. -/
def armReadLogOf (salt : Nat) (build : List Instr -> List Instr)
    (w : List Bool) (S c L base relLo relHi seed bb start : Nat) :
    List TraceEvent :=
  (E1Machine.run (E1FringeArmProgram.armWitnessStore w)
    (build (E1FringeArmProgram.armWitnessProgram S c L)) (4000 + salt)
    ⟨E1FringeArmProgram.armWitnessRegs base relLo relHi seed bb start,
      0, false⟩).readLog

def armReadLogs (salt : Nat) (build : List Instr -> List Instr) :
    List (List TraceEvent) :=
  armCases.map fun (w, S, c, L, base, relLo, relHi, seed, bb, start) =>
    armReadLogOf salt build w S c L base relLo relHi seed bb start

/-- THE DISCRIMINATOR: fixtures whose category log differs POSITIONALLY
from the honest run's. -/
def catLogMismatches (salt : Nat) (build : List Instr -> List Instr) : Nat :=
  (((armCatLogs salt goodArm).zip (armCatLogs salt build)).filter
    (fun p => p.1 != p.2)).length

/-- Mutant L genuinely changes the program, keeps its LENGTH, and -- unlike
every other mutant in this file -- genuinely changes the opcode-category
sequence.  That last clause is the point of the mutant, so it is asserted
in the opposite direction from `mergeMutationsAreReal` (`:944`). -/
def catMutationIsReal : Bool :=
  let honest := E1FringeArmProgram.armWitnessProgram 7 2 4
  let mutant := moveToMulConst honest
  honest != mutant && honest.length == mutant.length &&
    honest.map Instr.category != mutant.map Instr.category

/-- MUTANT L IS CATEGORY-ONLY.  Checked case by case against the reports
the earlier phases already build, not asserted:

* phase 3f's `ArmReport` -- value, position, receipt length, window
  addresses, fold segments, exit pc and modeled steps all agree;
* the full `readLog`, compared event for event, agrees;
* phase 3h's `PresReport` -- clobbered set, preservation verdict and
  zero-seed agreement all agree;
* the two blunt category statistics agree: the logs have the SAME LENGTH
  (so a step count cannot see it) and the SAME `memoryRead` charge count
  (so the only category machinery this file had before now cannot see it).

This is the fourth corner of the complementarity argument: D was
value-only, E receipt-only, G preservation-only, L category-only. -/
def catMutantIsCategoryOnly (salt : Nat) : Bool :=
  let ha := armReports salt goodArm
  let ma := armReports salt moveToMulConst
  let hp := presReports salt goodPres
  let mp := presReports salt moveToMulConst
  let hc := armCatLogs salt goodArm
  let mc := armCatLogs salt moveToMulConst
  let hr := armReadLogs salt goodArm
  let mr := armReadLogs salt moveToMulConst
  let armOk :=
    (ha.zip ma).all fun (h, m) =>
      h.reachedExit == m.reachedExit && h.modeledSteps == m.modeledSteps &&
        h.value == m.value && h.position == m.position &&
        h.machineReads == m.machineReads &&
        h.machineWindowAddrs == m.machineWindowAddrs &&
        h.foldSegmentsOk == m.foldSegmentsOk
  let presOk :=
    (hp.zip mp).all fun (h, m) =>
      h.clobbered == m.clobbered && h.preserved == m.preserved &&
        h.agreesWithZeroSeed == m.agreesWithZeroSeed &&
        h.value == m.value && h.position == m.position
  let receiptOk := (hr.zip mr).all fun (h, m) => h == m
  let blindOk :=
    (hc.zip mc).all fun (h, m) =>
      h.length == m.length &&
        catCount h Category.memoryRead == catCount m Category.memoryRead
  armOk && presOk && receiptOk && blindOk

/-! ### The category-log facts, KERNEL-CHECKED rather than printed

`catMutationIsReal` is pure list surgery on a program value, so the kernel
can settle it directly; the run-based clauses stay in the executed report
where the fold's arithmetic is compiled rather than reduced. -/

theorem catMutation_isReal : catMutationIsReal = true := rfl

theorem catMutation_changesCategorySequence :
    (E1FringeArmProgram.armWitnessProgram 7 2 4).map Instr.category !=
      (moveToMulConst (E1FringeArmProgram.armWitnessProgram 7 2 4)).map
        Instr.category := rfl

theorem catMutation_preservesLength :
    (moveToMulConst (E1FringeArmProgram.armWitnessProgram 7 2 4)).length =
      (E1FringeArmProgram.armWitnessProgram 7 2 4).length := rfl

/-! ## Phase 3n/5: the WHOLE-QUERY comparison, the named fixture CLASSES,
and the step literal EXERCISED (REQ-E1-08)

Three gaps close here at once, because they are the same gap seen from
three sides.

**(a) The fixture classes.**  REQ-E1-08 names "empty, singleton, size-two,
same-block, threshold-boundary, cross-interior, invalid, plus generated
cases".  Before this phase, `same-block` and `cross-interior` existed only
as dispatch-route OUTCOMES observed in phases 3b/3d, never as named
fixture classes; `threshold-boundary` did not appear in this file at all.

They are named here, and -- this is the part that matters -- **a case's
class is COMPUTED from the route's own closes, not hand-labelled**.
`classifyQuery` asks `wholeQueryBranch` for the closes the route actually
selects, divides them by the shape's own block size, and reads the class
off the two block indices.  A hand-written label would record what the
author BELIEVED; this records what the route does.  That distinction is
not theoretical: the measurement note below exists because a hand-supplied
branch literal disagreed with the computed one.

**(b) The comparison.**  `wholeQueryProgram` (`E1WholeQueryProgram.lean:876`)
is a plain `E1Machine.Program` -- 5646 instructions, no proof arguments --
so it RUNS.  This phase runs it against the canonical store on every case
and compares its decoded output packet with `refRMQ`.  The expectation is
computed FIRST, from the reference alone, before the shape, the store or
the program is built, following `:643`/`:851`/`:1140`/`:1296`.

**(c) The step literal, EXERCISED.**  `wholeQueryCats_machineS_length_le`
(`E1WholeQueryCostLiteral.lean:538`) proves the all-size bound `11886` and
nothing ran against it.  This phase measures TWO step counts per valid
case -- the executed `run`'s `steps`, and the cost model's
`wholeQueryCats` length -- and checks both that they AGREE and that the
executed count is within the bound.  The agreement is the sharper of the
two: it is an independent cross-check of the cost algebra against
execution, and neither side is derived from the other.

### THE PRIOR MEASUREMENT DOES NOT REPRODUCE, and the discrepancy is
attributed

`E1_LIVE_STATE.md` §15 and `E1WholeQueryCostLiteral.lean:572-592` record a
measured `1270` steps at the validator's own fixture shape
(`stackCartesianShape [3,1,4,1,5]`, query `[0,4)`), on branch
`.full 0 4 3`, and attribute the bound's looseness to "the bound assumes
the cross-block arm while a small shape takes the same-block arm".

**Evaluated here, that fixture measures `1765`, and it takes the CROSS-block
arm.**  The route's own branch at that shape and query is `.full 2 7 3`:
the closes are `2` and `7`, not `0` and `4`.  The block size is `6`, so
`blockOfClose 6 2 = 0` and `blockOfClose 6 7 = 1` -- DIFFERENT blocks.
The prior table passed the QUERY ENDPOINTS `0` and `4` where the branch
constructor expects CLOSES; those two do fall in the same block
(`blockOfClose 6 0 = blockOfClose 6 4 = 0`), which is where the
same-block reading came from.  The close/LCA slot measures `969` at the
real closes against `474` at the endpoint pair, and `1765 - 1270 = 495 =
969 - 474` accounts for the whole difference.

Both totals decompose exactly, so neither number is in doubt -- only the
branch they belong to:

```
  real   9 + 335 + 2 + 387 + 969 + 2 + 59 + 2 = 1765   (.full 2 7 3, CROSS)
  prior  9 + 335 + 2 + 387 + 474 + 2 + 59 + 2 = 1270   (.full 0 4 3, same)
```

The consequence for REQ-E1-06's looseness story is that the five-element
fixture never demonstrated the same-block arm at all, and the "about nine
times loose" figure is measured at the smallest fixture in the set.  At
the cross-interior fixtures this phase adds, the measured count rises to
`3267`, which is about `3.6` times inside the bound.  The looseness is
real and the bound is genuinely all-size; the ATTRIBUTION was wrong.

This phase carries no hand-transcribed step figure of its own: every
number it reports is measured at run time, and the bound constant is tied
to the theorem by `wholeQueryStepBound_isTheProvedBound` below. -/

/-- The proved all-size step bound.  NOT an asserted constant: the theorem
directly below fails to typecheck unless this is exactly the bound
`wholeQueryCats_machineS_length_le` proves, so changing this numeral
breaks the build rather than silently mis-reporting. -/
def wholeQueryStepBound : Nat := 11886

theorem wholeQueryStepBound_isTheProvedBound
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    (E1Query.wholeQueryCats (E1Query.wholeQueryMachineS shape) shape left
      right).length ≤ wholeQueryStepBound :=
  E1WholeQueryCostLiteral.wholeQueryCats_machineS_length_le shape left right

/-- The fixture classes REQ-E1-08 names, as a computed classification of a
query rather than a label attached to it. -/
inductive QueryClass where
  /-- The guard rejects: empty range, reversed, or past the end. -/
  | invalid
  /-- Both closes in one block; the close/LCA leg takes the same-block arm. -/
  | sameBlock
  /-- Closes in consecutive blocks; cross-block arm, EMPTY interior. -/
  | crossAdjacent
  /-- Closes at least two blocks apart; cross-block arm with a NONEMPTY
  interior -- the arm the `11886` bound is priced for. -/
  | crossInterior
  /-- A select leg missed, so the close/LCA leg never runs. -/
  | selectMiss
deriving Repr, DecidableEq, BEq

def queryClassName : QueryClass → String
  | .invalid => "invalid"
  | .sameBlock => "same-block"
  | .crossAdjacent => "cross-adjacent"
  | .crossInterior => "cross-interior"
  | .selectMiss => "select-miss"

/-- The arm class of a close pair, from the block indices alone. -/
def armClassOf (blockSize leftClose rightClose : Nat) : QueryClass :=
  let bl := SuccinctClose.blockOfClose blockSize leftClose
  let br := SuccinctClose.blockOfClose blockSize rightClose
  if bl == br then .sameBlock
  else if br == bl + 1 then .crossAdjacent
  else .crossInterior

/-- THRESHOLD-BOUNDARY: a close sitting on the first or last slot of its
block -- the exact positions the block dispatch's comparisons turn on, and
where an off-by-one in `blockOfClose` would first show.  Orthogonal to the
arm class, so it is reported as its own flag rather than as a sixth
constructor. -/
def atBlockThreshold (blockSize leftClose rightClose : Nat) : Bool :=
  blockSize != 0 &&
    (leftClose % blockSize == 0 || rightClose % blockSize == 0 ||
      leftClose % blockSize == blockSize - 1 ||
      rightClose % blockSize == blockSize - 1)

/-- Classify one query BY ASKING THE ROUTE.  Validity is decided first, on
the query alone, because `wholeQueryBranch` is not meaningful on a query
the guard rejects. -/
def classifyQuery (xs : List Int) (l r : Nat) : QueryClass × Bool :=
  if !(decide (l < r) && decide (r <= xs.length)) then (.invalid, false)
  else
    let shape := Cartesian.stackCartesianShape xs
    let bs := SuccinctClose.canonicalBPRelativeSummaryBlockSizeRaw shape
    match SuccinctFinal.wholeQueryBranch shape l r with
    | .leftSelectNone => (.selectMiss, false)
    | .rightSelectNone _ => (.selectMiss, false)
    | .lcaNone lc rc => (armClassOf bs lc rc, atBlockThreshold bs lc rc)
    | .full lc rc _ => (armClassOf bs lc rc, atBlockThreshold bs lc rc)

/-- A twelve-element fixture and a twenty-four-element one, kept as named
values because the cross-interior classes need shapes big enough to have
an interior at all -- at five elements the block size is `6` and no query
reaches a third block. -/
def wqWide : List Int := [8, 6, 7, 5, 3, 0, 9, 1, 4, 2, 6, 6]

def wqRamp : List Int := (List.range 24).map (fun i => Int.ofNat ((i * 7) % 13))

/-- The whole-query corpus.  Every class REQ-E1-08 names appears, and the
phase CHECKS that rather than trusting this list -- see
`wqClassPopulation` and `okWholeQueryCoverage`. -/
def wholeQueryCases : List (String × List Int × Nat × Nat) :=
  [ ("empty", [], 0, 0)
  , ("singleton", [42], 0, 1)
  , ("size-two-inc", [1, 2], 0, 2)
  , ("size-two-dec", [2, 1], 0, 2)
  , ("size-two-left", [1, 2], 0, 1)
  , ("same-block-lo", [3, 1, 4, 1, 5], 0, 2)
  , ("same-block-hi", [3, 1, 4, 1, 5], 2, 4)
  , ("same-block-point", [3, 1, 4, 1, 5], 0, 1)
  , ("cross-adjacent", [3, 1, 4, 1, 5], 0, 4)
  , ("cross-adjacent-mid", [3, 1, 4, 1, 5], 1, 3)
  , ("full-span-five", [3, 1, 4, 1, 5], 0, 5)
  , ("same-block-wide", wqWide, 0, 2)
  , ("cross-adjacent-wide", wqWide, 0, 4)
  , ("cross-interior-wide", wqWide, 0, 12)
  , ("cross-interior-wide-mid", wqWide, 6, 12)
  , ("same-block-ramp", wqRamp, 0, 4)
  , ("cross-interior-ramp", wqRamp, 0, 12)
  , ("cross-interior-ramp-deep", wqRamp, 0, 24)
  , ("cross-interior-ramp-off", wqRamp, 8, 16)
  , ("invalid-empty-range", [3, 1, 4, 1, 5], 2, 2)
  , ("invalid-reversed", [3, 1, 4, 1, 5], 3, 1)
  , ("invalid-past-end", [3, 1, 4, 1, 5], 0, 6)
  , ("gen-6-1", generatedInput 6 1, 0, 6)
  , ("gen-9-2", generatedInput 9 2, 1, 8) ]

/-- What one whole-query case reports. -/
structure WQReport where
  name : String
  cls : QueryClass
  threshold : Bool
  expected : Option Nat
  machine : Option Nat
  agrees : Bool
  halted : Bool
  executedSteps : Nat
  modelSteps : Option Nat
  stepsAgree : Bool
  withinBound : Bool
  reads : Nat
deriving Repr

/-- RUN THE WHOLE QUERY end to end and compare against the reference.

Expectation first, from `refRMQ` alone; only then the shape, the store,
the program and the run. -/
def runWholeQuery (salt : Nat) (build : List Instr -> List Instr)
    (name : String) (xs : List Int) (l r : Nat) : WQReport :=
  -- EXPECTATION FIRST, from the independent reference alone.
  let expected := refRMQ xs l r
  let (cls, thr) := classifyQuery xs l r
  -- ONLY NOW the machine.
  let shape := Cartesian.stackCartesianShape xs
  let program := build (E1Query.wholeQueryProgram shape xs.length)
  let result :=
    E1Machine.run (legStore shape) program (wholeQueryStepBound + salt)
      (E1Query.initialState l r)
  let machine := E1Query.decodePacket (result.final.regs E1Query.regOut)
  -- The cost model's own count, on the VALID cases only: on a rejected
  -- query the guard exits before the route's stage record applies, and
  -- comparing the model there would be a comparison with itself.
  let modelSteps : Option Nat :=
    if cls == .invalid then none
    else
      some (E1Query.wholeQueryCats (E1Query.wholeQueryMachineS shape) shape
        l r).length
  { name := name
    cls := cls
    threshold := thr
    expected := expected
    machine := machine
    agrees := expected == machine
    halted := result.final.halted
    executedSteps := result.steps
    modelSteps := modelSteps
    stepsAgree :=
      match modelSteps with
      | none => true
      | some m => m == result.steps
    withinBound := result.steps <= wholeQueryStepBound
    reads := result.readLog.length }

/-- The honest whole-query builder: identity. -/
def goodWholeQuery : List Instr -> List Instr := id

def wholeQueryReports (salt : Nat) (build : List Instr -> List Instr) :
    List WQReport :=
  wholeQueryCases.map fun (name, xs, l, r) =>
    runWholeQuery salt build name xs l r

/-- Cases whose machine answer disagrees with the reference. -/
def wqMismatches (rs : List WQReport) : List WQReport :=
  rs.filter (fun r => !r.agrees)

def wqNotHalted (rs : List WQReport) : Nat :=
  (rs.filter (fun r => !r.halted)).length

/-- Cases where the executed step count and the cost model's count
disagree.  Must be `0`. -/
def wqStepDisagreements (rs : List WQReport) : Nat :=
  (rs.filter (fun r => !r.stepsAgree)).length

/-- How many cases actually COMPARED the two step counts.  If this is `0`
the agreement above is vacuous, so the verdict requires it positive. -/
def wqStepsCompared (rs : List WQReport) : Nat :=
  (rs.filter (fun r => r.modelSteps.isSome)).length

def wqBoundViolations (rs : List WQReport) : Nat :=
  (rs.filter (fun r => !r.withinBound)).length

/-- The largest executed step count observed, for reporting against the
bound.  A maximum well under `11886` is not a failure -- the bound is
all-size -- but it is the number that says how loose the bound is HERE. -/
def wqMaxSteps (rs : List WQReport) : Nat :=
  rs.foldl (fun a r => Nat.max a r.executedSteps) 0

def wqTotalSteps (rs : List WQReport) : Nat :=
  rs.foldl (fun a r => a + r.executedSteps) 0

def wqTotalReads (rs : List WQReport) : Nat :=
  rs.foldl (fun a r => a + r.reads) 0

/-- Population of one class in the corpus. -/
def wqClassPopulation (rs : List WQReport) (c : QueryClass) : Nat :=
  (rs.filter (fun r => r.cls == c)).length

def wqThresholdPopulation (rs : List WQReport) : Nat :=
  (rs.filter (fun r => r.threshold)).length

/-- Cases whose fixture is empty or a singleton, by the fixture itself --
the two classes REQ-E1-08 names that are properties of the INPUT rather
than of the route. -/
def wqSizeClassPopulation (rs : List WQReport) (n : Nat) : Nat :=
  ((wholeQueryCases.zip rs).filter
    (fun (c, _) => c.2.1.length == n)).length

/-- ANTI-VACUITY FOR THE FIXTURE CLASSES: every class REQ-E1-08 names is
actually POPULATED.  A named class with no members is not a fixture class,
and this is the check that stops the corpus above from silently drifting
into one. -/
def wqClassesAllPopulated (rs : List WQReport) : Bool :=
  wqClassPopulation rs .sameBlock > 0 &&
    wqClassPopulation rs .crossInterior > 0 &&
      wqClassPopulation rs .invalid > 0 &&
        wqThresholdPopulation rs > 0 &&
          wqSizeClassPopulation rs 0 > 0 &&
            wqSizeClassPopulation rs 1 > 0 &&
              wqSizeClassPopulation rs 2 > 0

/-- **Availability, DERIVED rather than declared.**

The four previous versions of this flag were hand-set to `false` beside a
hand-written sentence explaining why, and the sentence went stale three
times because nothing recomputed it.  This computes it: the comparison is
available exactly when there is a corpus and every case in it produced a
report.  If the corpus were emptied, this would go `false` on its own and
say so, without anyone editing a docstring. -/
def wholeQueryComparisonAvailable : Bool :=
  wholeQueryCases.length > 0 &&
    (wholeQueryReports 0 goodWholeQuery).length == wholeQueryCases.length

/-- The disagreements, or `none` when no comparison is available. -/
def wholeQueryMismatches (salt : Nat) : Option (List WQReport) :=
  if wholeQueryComparisonAvailable then
    some (wqMismatches (wholeQueryReports salt goodWholeQuery))
  else
    none

/-! ### MUTANT M: the whole-query comparison is FALSIFIABLE

A phase that prints a pass without comparing is worse than an honest OPEN,
so this is the check that the comparison above is live.

**MUTANT M turns every `natLt` in the whole-query program into `natLe`.**
The specification's answer is the LEFTMOST minimiser, and `refRMQ`
(`:78`) is written to match: its fold "replaces the incumbent only on a
STRICTLY smaller value".  Relaxing `<` to `≤` makes the machine replace the
incumbent on a TIE as well, so it answers with a later minimiser.

What makes this the right mutant rather than merely a broken one:

* **it still HALTS**, on every case, and still writes a well-formed answer
  packet -- so an exit-pc check, a halted-flag check, a receipt check and a
  step-count check would all pass it.  `wqMutantStillHalts` asserts this,
  which is what stops the phase claiming credit for catching a crash;
* it is caught **only** by the value comparison against the independent
  reference;
* and it is NOT caught on every case -- a window with no tie answers
  identically under `<` and `≤`.  So the corpus having tie-bearing
  fixtures is load-bearing, exactly as `mergePathCoverage` (`:936`) is
  load-bearing for mutant D. -/

def mutatedWholeQuery (program : List Instr) : List Instr :=
  program.map fun instr =>
    match instr with
    | .natLt d a b => .natLe d a b
    | other => other

/-- Mutant M genuinely changes the program and preserves its length. -/
def wholeQueryMutationIsReal : Bool :=
  let honest := E1Query.wholeQueryProgram (Cartesian.stackCartesianShape [3, 1, 4, 1, 5]) 5
  let mutant := mutatedWholeQuery honest
  honest != mutant && honest.length == mutant.length

/-- Cases on which the answer comparison REJECTS mutant M. -/
def wqMutantCaught (rs : List WQReport) : Nat := (wqMismatches rs).length

/-- Mutant M halts on every case, so nothing here is credit for a crash. -/
def wqMutantStillHalts (rs : List WQReport) : Bool :=
  rs.all (fun r => r.halted)

/-- **The status line, RENDERED FROM THE CONDITION rather than stored.**

This is the durable fix for the defect that made phase 5's reason wrong in
both directions across four rounds: there is no sentence here to go stale,
because every clause is computed from the reports the phase just produced. -/
def wholeQueryStatusLine (rs : List WQReport) : String :=
  if !wholeQueryComparisonAvailable then
    "OPEN (no comparison surface: the case corpus is empty, so nothing was compared; NOT a pass)"
  else
    let bad := (wqMismatches rs).length
    let compared := rs.length
    if bad == 0 then
      s!"COMPARED ({compared} cases, {wqStepsCompared rs} of them step-checked against the cost model; 0 answer mismatches)"
    else
      s!"MISMATCH ({bad} of {compared} cases disagree with refRMQ)"

def renderWQ (r : WQReport) : String :=
  s!"    {r.name} [{queryClassName r.cls}]" ++
    (if r.threshold then " (threshold)" else "") ++
    s!" expected={repr r.expected} machine={repr r.machine} " ++
    s!"steps={r.executedSteps} model={repr r.modelSteps}"

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

  -- STEP 3f: the fringe ARM, judged by its RECEIPT.
  IO.println "-- phase 3f: fringe ARM at base 2 vs an independent read reference --"
  let ta0 <- IO.monoMsNow
  let armHonest := armReports salt goodArm
  let armExitFails := armExitFailures armHonest
  let armReceiptFails := armReceiptFailures armHonest
  let armEpiCov := armEpilogueCoverage armHonest
  let armPassCov := armPassCoverage armHonest
  let armSteps := (armHonest.map ArmReport.modeledSteps).foldl (· + ·) 0
  let armReadsTotal := (armHonest.map ArmReport.machineReads).foldl (· + ·) 0
  IO.println s!"armCases={armCases.length}"
  IO.println s!"armExitFailures={armExitFails}   (proved exit is pc 97, halted)"
  IO.println s!"armReceiptFailures={armReceiptFails}   (read count, window addresses, fold segment; must be 0)"
  IO.println s!"armEpilogueCoverage={armEpiCov}   (must be 2: occupied rebase AND seed fallback)"
  IO.println s!"armPassCoverage={armPassCov}   (must be > 1: the fold back edge fires)"
  IO.println s!"armModeledSteps={armSteps}   (machine-modeled, reproducible)"
  IO.println s!"armModeledReads={armReadsTotal}   (must be > 0: the arm is read-BEARING)"
  let ta1 <- IO.monoMsNow
  IO.println s!"armWallClockMs={ta1 - ta0}   (this binary on this host; NOT evidence)"
  IO.println ""

  -- STEP 4e: mutating the ARM, where the VALUE cannot help.
  IO.println "-- phase 4e: deliberate mutation of the ARM (receipt-only visible) --"
  let tam0 <- IO.monoMsNow
  let mutEReports := armReports salt mutatedArmSegment
  let mutEExit := armExitFailures mutEReports
  let mutEReceipt := armReceiptFailures mutEReports
  let mutEReceiptOnly := armMutantEIsReceiptOnly salt
  IO.println s!"armMutationIsReal={armMutationIsReal}   (differs; same length AND same opcode categories)"
  IO.println s!"mutantE_segment_exitFailures={mutEExit}   (0 expected: exit pc alone MISSES this)"
  IO.println s!"mutantE_segment_receiptFailures={mutEReceipt}   (must be > 0: ONLY the receipt catches it)"
  IO.println s!"mutantE_isReceiptOnly={mutEReceiptOnly}   (pc, steps, value and position all agree with honest)"
  IO.println s!"armMutationERejected={mutEReceipt != 0}"
  let tam1 <- IO.monoMsNow
  IO.println s!"armMutationWallClockMs={tam1 - tam0}"
  IO.println ""

  -- STEP 3g: the two cross-block range preambles, judged by their VALUE.
  IO.println "-- phase 3g: cross-block RANGE preambles vs an independent reference --"
  let tr0 <- IO.monoMsNow
  let leftRangeReports := rangeReports salt true goodRange
  let rightRangeReports := rangeReports salt false goodRange
  let lrMismatch := rangeMismatches leftRangeReports
  let lrExit := rangeExitFailures leftRangeReports
  let rrMismatch := rangeMismatches rightRangeReports
  let rrExit := rangeExitFailures rightRangeReports
  let rangeReadsTotal := rangeReads leftRangeReports + rangeReads rightRangeReports
  IO.println s!"rangeCases={rangeCases.length}   (each preamble)"
  IO.println s!"crossLeftRangeExitFailures={lrExit}   (exit is pc 10, halted)"
  IO.println s!"crossLeftRangeMismatches={lrMismatch}   (start/relLo/relHi vs refCrossLeftRange; must be 0)"
  IO.println s!"crossRightRangeExitFailures={rrExit}"
  IO.println s!"crossRightRangeMismatches={rrMismatch}   (vs refCrossRightRange; must be 0)"
  IO.println s!"rangeModeledReads={rangeReadsTotal}   (must be 0: both preambles are read-free)"
  let tr1 <- IO.monoMsNow
  IO.println s!"rangeWallClockMs={tr1 - tr0}"
  IO.println ""

  -- STEP 4f: mutating a range preamble, where no receipt exists to diff.
  IO.println "-- phase 4f: deliberate mutation of the LEFT range (value-only visible) --"
  let trm0 <- IO.monoMsNow
  let mutFReports := rangeReports salt true mutatedRangeCount
  let mutFMismatch := rangeMismatches mutFReports
  let mutFExit := rangeExitFailures mutFReports
  IO.println s!"rangeMutationIsReal={rangeMutationIsReal}   (differs; same length AND same opcode categories)"
  IO.println s!"mutantF_blockEnd_exitFailures={mutFExit}   (0 expected: exit pc alone MISSES this)"
  IO.println s!"mutantF_blockEnd_mismatches={mutFMismatch}   (must be > 0: the value catches it)"
  IO.println s!"rangeMutationFRejected={mutFMismatch != 0}   (no receipt exists to diff: the block is read-free)"
  let trm1 <- IO.monoMsNow
  IO.println s!"rangeMutationWallClockMs={trm1 - trm0}"
  IO.println ""

  -- STEP 3h: the preservation clause this session added, checked by
  -- execution register by register.
  IO.println "-- phase 3h: fringe-arm REGISTER PRESERVATION (third discriminator) --"
  let tp0 <- IO.monoMsNow
  let presRs := presReports salt goodPres
  let presFails := presFailures presRs
  let presExitFails := presExitFailures presRs
  let presSeedDis := presSeedDisagreements presRs
  IO.println s!"presCases={presRs.length}"
  IO.println s!"presCheckedRegs={armUntouchedRegs.length}   (registers FringeArmUntouched claims survive)"
  IO.println s!"presSentinelNonZero={presSentinel 0 != 0}   (a zero-seeded file makes this phase vacuous)"
  IO.println s!"presExitFailures={presExitFails}"
  IO.println s!"presFailures={presFails}   (must be 0: the arm's preservation clause, executed)"
  IO.println s!"presClobberedRegs={presClobberedRegs presRs}   (must be empty)"
  IO.println s!"presSeedDisagreements={presSeedDis}   (must be 0: sentinel and zero seeding give the same answer)"
  let tp1 <- IO.monoMsNow
  IO.println s!"presWallClockMs={tp1 - tp0}"
  IO.println ""

  -- STEP 4g: a mutation NO earlier discriminator in this harness can see.
  IO.println "-- phase 4g: deliberate mutation of the epilogue SCRATCH register (preservation-only visible) --"
  let tpm0 <- IO.monoMsNow
  let mutGReports := presReports salt mutatedArmScratch
  let mutGFails := presFailures mutGReports
  let mutGExit := presExitFailures mutGReports
  let mutGPresOnly := presMutantGIsPreservationOnly salt
  IO.println s!"presMutationIsReal={presMutationIsReal}   (differs; same length AND same opcode categories)"
  IO.println s!"mutantG_scratch_exitFailures={mutGExit}   (0 expected: exit pc alone MISSES this)"
  IO.println s!"mutantG_scratch_preservationFailures={mutGFails}   (must be > 0: preservation catches it)"
  IO.println s!"mutantG_clobberedRegs={presClobberedRegs mutGReports}   (expect [70] -- fClose in the cross layout)"
  IO.println s!"mutantG_isPreservationOnly={mutGPresOnly}   (exit pc, steps, value and position ALL match the honest sweep)"
  let tpm1 <- IO.monoMsNow
  IO.println s!"presMutationWallClockMs={tpm1 - tpm0}"
  IO.println ""

  -- STEP 3i: the INTERIOR fold's preservation clause -- stated since
  -- M3d-13, executed here for the first time.
  IO.println "-- phase 3i: interior CHUNK FOLD register preservation (first executed fold-level check) --"
  let tc0 <- IO.monoMsNow
  let cPresRs := chunkPresReports salt goodChunkPres
  let cPresFails := chunkPresFailures cPresRs
  let cPresExitFails := chunkPresExitFailures cPresRs
  let cPresSeedDis := chunkPresSeedDisagreements cPresRs
  let cPresMulti := chunkPresMultiChunkCases cPresRs
  IO.println s!"chunkPresCases={cPresRs.length}"
  IO.println s!"chunkPresCheckedRegs={chunkUntouchedRegs.length}   (registers ChunkFoldUntouched claims survive)"
  IO.println s!"chunkPresSentinelNonZero={presSentinel 0 != 0}   (a zero-seeded file makes this phase vacuous)"
  IO.println s!"chunkPresTargetSeed={presSentinel chunkClobberTarget}   (seed at 102; the combine digit is 0 or 1, so ranges are disjoint)"
  IO.println s!"chunkPresMultiChunkCases={cPresMulti}   (must be > 0: a single-chunk sweep exercises the atom, not the fold)"
  IO.println s!"chunkPresExitFailures={cPresExitFails}"
  IO.println s!"chunkPresFailures={cPresFails}   (must be 0: the fold's preservation clause, executed)"
  IO.println s!"chunkPresClobberedRegs={chunkPresClobberedRegs cPresRs}   (must be empty)"
  IO.println s!"chunkPresSeedDisagreements={cPresSeedDis}   (must be 0: cell AND read log agree under both seedings)"
  let tc1 <- IO.monoMsNow
  IO.println s!"chunkPresWallClockMs={tc1 - tc0}"
  IO.println ""

  -- STEP 4h: a mutation invisible to BOTH of this harness's other
  -- discriminators, on the interior side.
  IO.println "-- phase 4h: deliberate mutation of the COMBINE loop's scratch register (preservation-only visible) --"
  let tcm0 <- IO.monoMsNow
  let mutHReports := chunkPresReports salt mutatedCombineScratch
  let mutHFails := chunkPresFailures mutHReports
  let mutHExit := chunkPresExitFailures mutHReports
  let mutHPresOnly := chunkMutantHIsPreservationOnly salt
  IO.println s!"chunkPresMutationIsReal={chunkPresMutationIsReal}   (differs; same length AND same opcode categories)"
  IO.println s!"mutantH_combine_exitFailures={mutHExit}   (0 expected: exit pc alone MISSES this)"
  IO.println s!"mutantH_combine_preservationFailures={mutHFails}   (must be > 0: preservation catches it)"
  IO.println s!"mutantH_clobberedRegs={chunkPresClobberedRegs mutHReports}   (expect [102] -- sMin in the summary group's bank)"
  IO.println s!"mutantH_isPreservationOnly={mutHPresOnly}   (exit pc, steps, cell AND read log ALL match the honest sweep)"
  let tcm1 <- IO.monoMsNow
  IO.println s!"chunkPresMutationWallClockMs={tcm1 - tcm0}"
  IO.println ""

  -- STEP 3k: the FRINGE fold's OWN preservation clause -- stated at
  -- `E1FringeFoldBlock.lean:962`, executed NOWHERE until now, and NOT
  -- reachable through phase 3h because the fold's predicate is strictly
  -- stronger than the arm's.
  IO.println "-- phase 3k: FRINGE FOLD register preservation, run STANDALONE (FringeFoldUntouched, first execution) --"
  let tf0 <- IO.monoMsNow
  let fPresRs := foldPresReports salt goodFoldPres
  let fPresFails := foldPresFailures fPresRs
  let fPresExitFails := foldPresExitFailures fPresRs
  let fPresSeedDis := foldPresSeedDisagreements fPresRs
  let fPresReadBearing := foldPresReadBearingCases fPresRs
  IO.println s!"foldPresCases={fPresRs.length}"
  IO.println s!"foldPresCheckedRegs={foldUntouchedRegs.length}   (registers FringeFoldUntouched claims survive)"
  IO.println s!"foldPresSentinelNonZero={presSentinel 0 != 0}   (a zero-seeded file makes this phase vacuous)"
  IO.println s!"foldPresTargetSeed={presSentinel foldClobberTarget}   (seed at 105, outside the fold bank 40..62)"
  IO.println s!"foldPresReadBearingCases={fPresReadBearing}   (must equal the case count: the fold charges one read per pass)"
  IO.println s!"foldPresExitFailures={fPresExitFails}"
  IO.println s!"foldPresFailures={fPresFails}   (must be 0: the FRINGE fold's own preservation clause, executed)"
  IO.println s!"foldPresClobberedRegs={foldPresClobberedRegs fPresRs}   (must be empty)"
  IO.println s!"foldPresSeedDisagreements={fPresSeedDis}   (must be 0: accumulator AND read log agree under both seedings)"
  let tf1 <- IO.monoMsNow
  IO.println s!"foldPresWallClockMs={tf1 - tf0}"
  IO.println ""

  -- STEP 4j: a mutation of the fringe fold's private scratch, visible to
  -- preservation and to nothing else this harness checks.
  IO.println "-- phase 4j: deliberate rename of the FRINGE FOLD's scratch register fX (preservation-only visible) --"
  let tfm0 <- IO.monoMsNow
  let mutKReports := foldPresReports salt mutatedFoldScratch
  let mutKFails := foldPresFailures mutKReports
  let mutKExit := foldPresExitFailures mutKReports
  let mutKPresOnly := foldMutantKIsPreservationOnly salt
  IO.println s!"foldPresMutationIsReal={foldPresMutationIsReal}   (differs; same length AND same opcode categories)"
  IO.println s!"mutantK_fold_exitFailures={mutKExit}   (0 expected: exit pc alone MISSES this)"
  IO.println s!"mutantK_fold_preservationFailures={mutKFails}   (must be > 0: preservation catches it)"
  IO.println s!"mutantK_clobberedRegs={foldPresClobberedRegs mutKReports}   (expect [105])"
  IO.println s!"mutantK_isPreservationOnly={mutKPresOnly}   (exit pc, steps, accumulator, best pair AND read log ALL match)"
  let tfm1 <- IO.monoMsNow
  IO.println s!"foldPresMutationWallClockMs={tfm1 - tfm0}"
  IO.println ""

  -- STEP 3j: REQ-E1-05's five-word residual, "and in the validator".
  IO.println "-- phase 3j: INVALID GUARD skeleton on empty/reversed/out-of-bounds fixtures (REQ-E1-05) --"
  let tg0 <- IO.monoMsNow
  let gRs := guardReports salt goodGuard
  let gFails := guardFailures gRs
  let gRejected := guardRejectedCount gRs
  let gAccepted := guardAcceptedCount gRs
  IO.println s!"guardCases={gRs.length}"
  IO.println s!"guardFamilies=empty,emptyRange,reversed,outOfBounds + valid controls"
  IO.println s!"guardFailures={gFails}   (must be 0: every fixture meets its own clause list)"
  IO.println s!"guardRejected={gRejected}   (invalid fixtures reaching the guarded none-packet)"
  IO.println s!"guardValidControlsAccepted={gAccepted}   (must be > 0: a reject-everything machine scores 0 here and passes every other check in this phase)"
  IO.println s!"guardMaxInvalidSteps={guardMaxInvalidSteps gRs}   (frozen bound is 10, guardRejectCats_length_le)"
  IO.println s!"guardReadsTotal={(gRs.filter (fun r => r.readCount != 0)).length}   (must be 0: the guard reads nothing)"
  IO.println s!"guardMemoryReadCharges={(gRs.filter (fun r => r.memoryReadCharges != 0)).length}   (must be 0: zero memory-read category charge)"
  let tg1 <- IO.monoMsNow
  IO.println s!"guardWallClockMs={tg1 - tg0}"
  IO.println ""

  -- STEP 4i: a guard mutation with the same length and the same category log.
  IO.println "-- phase 4i: deliberate mutation of the OUT-OF-BOUNDS guard branch (rejection-only visible) --"
  let tgm0 <- IO.monoMsNow
  let mutJRs := guardReports salt mutatedGuardBounds
  let mutJRejected := guardRejectedCount mutJRs
  let mutJAccepted := guardAcceptedCount mutJRs
  IO.println s!"guardMutationIsReal={guardMutationIsReal}   (differs; same length AND same instruction categories)"
  IO.println s!"mutantJ_rejected={mutJRejected}   (5 expected: the three fixtures needing the right<=n test escape)"
  IO.println s!"mutantJ_validControlsAccepted={mutJAccepted}   (3 expected: valid queries are UNAFFECTED, so a valid-only harness MISSES this)"
  IO.println s!"mutantJ_caught={mutJRejected != 8}   (must be true)"
  let tgm1 <- IO.monoMsNow
  IO.println s!"guardMutationWallClockMs={tgm1 - tgm0}"
  IO.println ""

  -- STEP 3l: the store-value dependency witness (REQ-E1-03).
  IO.println "-- phase 3l: STORE-VALUE DEPENDENCY (perturb a word the machine READ) --"
  let td0 <- IO.monoMsNow
  let depRs := depReports salt
  let depArmMis := depArmMismatches depRs
  let depOcc := depOccupiedFixtures depRs
  let depFall := depFallbackFixtures depRs
  let depLeaks := depControlLeaks depRs
  let depUnsound := depControlUnsound depRs
  let depVac := depVacuous depRs
  IO.println s!"depCases={depRs.length}"
  IO.println s!"depDistinctReadCellsProbed={depTotalCells depRs}   (cells taken from the RECEIPT, not guessed)"
  IO.println s!"depCellsWhoseCorruptionMovedTheAnswer={depTotalMovedCells depRs}   (must be > 0: this IS the dependency)"
  IO.println s!"depArmMismatches={depArmMis}   (must be 0: read-dependence occurs EXACTLY on the occupied epilogue arm)"
  IO.println s!"depOccupiedFixtures={depOcc}   (must be > 0: else the biconditional holds trivially)"
  IO.println s!"depSeedFallbackFixtures={depFall}   (must be > 0: else the read-INdependent direction is never exercised)"
  IO.println s!"depControlLeaks={depLeaks}   (must be 0: corrupting an UNREAD cell must not move the answer)"
  IO.println s!"depControlCellUnsound={depUnsound}   (must be 0: the control cell must really be off the receipt)"
  IO.println s!"depVacuousFixtures={depVac}   (must be 0: perturbed word differs AND the run charged reads)"
  let td1 <- IO.monoMsNow
  IO.println s!"depWallClockMs={td1 - td0}   (this binary on this host; NOT evidence)"
  IO.println ""

  -- STEP 4l: the CATEGORY LOG as a discriminator (REQ-E1-06).
  IO.println "-- phase 4l: deliberate mutation caught ONLY by the positional CATEGORY LOG --"
  let tc0 <- IO.monoMsNow
  let catCaught := catLogMismatches salt moveToMulConst
  let catHonest := catLogMismatches salt goodArm
  let catOnly := catMutantIsCategoryOnly salt
  IO.println s!"catMutationIsReal={catMutationIsReal}   (differs; SAME length; DIFFERENT opcode categories -- the point of mutant L)"
  IO.println s!"catLogMismatches_honest={catHonest}   (must be 0: the log is stable under the identity builder)"
  IO.println s!"mutantL_catLogMismatches={catCaught}   (must be > 0: the positional category log catches it)"
  IO.println s!"mutantL_isCategoryOnly={catOnly}   (value, position, FULL receipt, preservation, exit pc, modeled steps, catLog LENGTH and memoryRead charge ALL match)"
  let tc1 <- IO.monoMsNow
  IO.println s!"catWallClockMs={tc1 - tc0}   (this binary on this host; NOT evidence)"
  IO.println ""

  -- STEP 5: the whole-query comparison, its fixture classes, and the
  -- step literal exercised.  No longer a hole.
  IO.println "-- phase 5: WHOLE-QUERY comparison, fixture classes, and the 11886 step bound --"
  let tw0 <- IO.monoMsNow
  let wqRs := wholeQueryReports salt goodWholeQuery
  let wqBad := wqMismatches wqRs
  let wqSteps := wqStepDisagreements wqRs
  let wqCompared := wqStepsCompared wqRs
  let wqBound := wqBoundViolations wqRs
  let wqHalt := wqNotHalted wqRs
  let wqCov := wqClassesAllPopulated wqRs
  IO.println s!"wholeQueryComparisonAvailable={wholeQueryComparisonAvailable}   (DERIVED from the corpus, not declared)"
  IO.println s!"wholeQueryComparison={wholeQueryStatusLine wqRs}"
  IO.println s!"wholeQueryCases={wqRs.length}"
  IO.println s!"wholeQueryAnswerMismatches={wqBad.length}   (machine output packet vs refRMQ)"
  IO.println s!"wholeQueryNotHalted={wqHalt}   (must be 0)"
  IO.println s!"wholeQueryModeledSteps={wqTotalSteps wqRs}   (machine-modeled, reproducible)"
  IO.println s!"wholeQueryModeledReads={wqTotalReads wqRs}   (machine-modeled receipt events)"
  IO.println s!"wholeQueryMaxModeledSteps={wqMaxSteps wqRs}   (measured; the proved all-size bound is {wholeQueryStepBound})"
  IO.println s!"wholeQueryStepModelDisagreements={wqSteps}   (must be 0: executed steps vs wholeQueryCats length)"
  IO.println s!"wholeQueryStepComparisons={wqCompared}   (must be > 0, else the line above is vacuous)"
  IO.println s!"wholeQueryBoundViolations={wqBound}   (must be 0: executed steps within {wholeQueryStepBound})"
  IO.println "-- fixture classes, COMPUTED from the route's own closes --"
  IO.println s!"class_same-block={wqClassPopulation wqRs .sameBlock}"
  IO.println s!"class_cross-adjacent={wqClassPopulation wqRs .crossAdjacent}"
  IO.println s!"class_cross-interior={wqClassPopulation wqRs .crossInterior}"
  IO.println s!"class_select-miss={wqClassPopulation wqRs .selectMiss}"
  IO.println s!"class_invalid={wqClassPopulation wqRs .invalid}"
  IO.println s!"class_threshold-boundary={wqThresholdPopulation wqRs}   (a close on the first or last slot of its block)"
  IO.println s!"class_empty={wqSizeClassPopulation wqRs 0}   class_singleton={wqSizeClassPopulation wqRs 1}   class_size-two={wqSizeClassPopulation wqRs 2}"
  IO.println s!"wholeQueryClassesAllPopulated={wqCov}   (must be true: a named class with no members is not a fixture class)"
  for m in wqBad.take 10 do
    IO.println (renderWQ m)
  let tw1 <- IO.monoMsNow
  IO.println s!"wholeQueryWallClockMs={tw1 - tw0}   (this binary on this host; NOT evidence)"
  IO.println ""

  -- STEP 4m: mutant M, the proof that phase 5 actually compares.
  IO.println "-- phase 4m: deliberate mutation of the WHOLE-QUERY program (value-only visible) --"
  let twm0 <- IO.monoMsNow
  let wqMutRs := wholeQueryReports salt mutatedWholeQuery
  let wqMutCaught := wqMutantCaught wqMutRs
  let wqMutHalts := wqMutantStillHalts wqMutRs
  IO.println s!"wholeQueryMutationIsReal={wholeQueryMutationIsReal}   (differs; SAME length)"
  IO.println s!"mutantM_answerMismatches={wqMutCaught}   (must be > 0: the refRMQ comparison catches it)"
  IO.println s!"mutantM_stillHalts={wqMutHalts}   (must be true: exit pc, halted flag and step count all MISS it)"
  IO.println s!"mutantM_casesUnaffected={wqMutRs.length - wqMutCaught}   (windows with no tie answer identically under < and <=)"
  let twm1 <- IO.monoMsNow
  IO.println s!"wholeQueryMutationWallClockMs={twm1 - twm0}   (this binary on this host; NOT evidence)"
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
  -- The fringe arm: RECEIPT agreement with the independent read
  -- reference, both epilogue arms reached, the fold back edge fired, and
  -- reads actually charged (a read-free arm would make phase 3f vacuous).
  let okArm :=
    armExitFails == 0 && armReceiptFails == 0 && armEpiCov == 2 &&
      armPassCov > 1 && armReadsTotal > 0
  -- Mutant E rejected, and confirmed invisible to every observable except
  -- the receipt -- the mirror of mutant D.
  let okArmMutations :=
    armMutationIsReal && mutEReceipt != 0 && mutEReceiptOnly
  -- The two new cross-block range preambles: VALUE agreement with the
  -- independent reference, and read-freedom observed in execution.
  let okRange :=
    lrMismatch == 0 && lrExit == 0 && rrMismatch == 0 && rrExit == 0 &&
      rangeReadsTotal == 0
  let okRangeMutations := rangeMutationIsReal && mutFMismatch != 0
  -- The arm's PRESERVATION clause, executed: nothing outside the write set
  -- moves, and sentinel seeding does not change the answer (so the arm
  -- reads no register it does not initialise).
  let okPres :=
    presFails == 0 && presExitFails == 0 && presSeedDis == 0 &&
      presSentinel 0 != 0
  -- Mutant G rejected, and confirmed invisible to BOTH earlier
  -- discriminators -- the third corner of the complementarity argument.
  let okPresMutations :=
    presMutationIsReal && mutGFails != 0 && mutGPresOnly
  -- The INTERIOR fold's preservation clause, executed: nothing outside
  -- `89..99` moves, sentinel seeding does not change the cell or the read
  -- log, and the sweep is genuinely multi-chunk rather than a disguised
  -- single-chunk atom sweep.
  let okChunkPres :=
    cPresFails == 0 && cPresExitFails == 0 && cPresSeedDis == 0 &&
      cPresMulti > 0 && presSentinel 0 != 0
  -- Mutant H rejected, and confirmed invisible to BOTH other
  -- discriminators on the interior side.
  let okChunkPresMutations :=
    chunkPresMutationIsReal && mutHFails != 0 && mutHPresOnly
  -- REQ-E1-05: every fixture meets its own clause list, all eight invalid
  -- ones reach the guarded none-packet, AND the valid controls are accepted
  -- -- the last conjunct is what stops a reject-everything machine passing.
  let okGuard :=
    gFails == 0 && gRejected == 8 && gAccepted > 0 &&
      guardMaxInvalidSteps gRs <= 10
  -- Mutant J rejected, and confirmed shape-preserving and invisible to a
  -- valid-query-only harness.
  let okGuardMutations :=
    guardMutationIsReal && mutJRejected != 8 && mutJAccepted == 3
  -- The FRINGE fold's own preservation clause, executed standalone:
  -- nothing outside the bank 40..62 moves, sentinel seeding changes
  -- neither the accumulator nor the read log, and every fixture is
  -- genuinely read-bearing rather than a run that charged nothing.
  let okFoldPres :=
    fPresFails == 0 && fPresExitFails == 0 && fPresSeedDis == 0 &&
      fPresReadBearing == fPresRs.length && presSentinel 0 != 0
  -- Mutant K rejected, and confirmed shape-preserving and invisible to
  -- both the value and the receipt discriminators.
  let okFoldPresMutations :=
    foldPresMutationIsReal && mutKFails != 0 && mutKPresOnly
  -- REQ-E1-03's store-value dependency: the answer MOVES when a word the
  -- machine actually read is corrupted, does NOT move when an unread cell
  -- is corrupted on the same terms, and no fixture is vacuous.
  let okDependence :=
    depArmMis == 0 && depLeaks == 0 && depUnsound == 0 && depVac == 0 &&
      depTotalMovedCells depRs > 0 && depOcc > 0 && depFall > 0
  -- REQ-E1-06's category-log discriminator: mutant L caught by the
  -- positional log, invisible to value, receipt, preservation, steps and
  -- the memoryRead charge count.
  let okCategory :=
    catMutationIsReal && catHonest == 0 && catCaught > 0 && catOnly
  -- REQ-E1-08's whole-query comparison: answers agree with refRMQ, the
  -- executed step count agrees with the cost model on a nonempty set of
  -- cases, every run is within the proved bound, and every named fixture
  -- class is populated.
  let okWholeQuery :=
    wholeQueryComparisonAvailable && wqBad.isEmpty && wqHalt == 0 &&
      wqSteps == 0 && wqCompared > 0 && wqBound == 0
  let okWholeQueryCoverage := wqCov
  -- Mutant M rejected BY THE VALUE COMPARISON while still halting: this is
  -- what makes phase 5 a comparison rather than a printed pass.
  let okWholeQueryMutation :=
    wholeQueryMutationIsReal && wqMutCaught > 0 && wqMutHalts
  let okCore := okReference && okLengths && okDispatch && okLeg
  let okComposite := okSelect && okCompose && okComposeCoverage && okMerge
  let okAdversarial := okMutations && okMutantSetup && okMergeMutations
  let okNew := okArm && okArmMutations && okRange && okRangeMutations
  let okPreservation := okPres && okPresMutations
  let okChunkPreservation := okChunkPres && okChunkPresMutations
  let okNewDiscriminators :=
    okDependence && okCategory && okWholeQuery && okWholeQueryCoverage &&
      okWholeQueryMutation
  let ok :=
    okCore && okComposite && okAdversarial && okNew && okPreservation &&
      okChunkPreservation && okGuard && okGuardMutations &&
      okFoldPres && okFoldPresMutations && okNewDiscriminators
  if ok then
    IO.println "RESULT: PASS (whole-query comparison EXECUTED; see phase 5)"
    return 0
  else
    IO.println "RESULT: FAIL"
    return 1

end RMQ.Validation.E1MachineValidate

def main : IO UInt32 := RMQ.Validation.E1MachineValidate.mainImpl
