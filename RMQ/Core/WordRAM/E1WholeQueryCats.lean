import RMQ.Core.WordRAM.E1RouteDecomposition
import RMQ.Core.WordRAM.E1Machine

/-!
# E1 amended machine: the WHOLE-QUERY category function

The route-indexed prediction of the machine's whole-query category log,
following the per-component precedent (`fringeArmCats`, `crossBlockArmCats`,
`sameBlockDispatchCats`): a function of the route's branch conditions, never
a numeral.

**This module is written BEFORE the whole-query machine side exists, and
that ordering is deliberate.**  A category function written after the machine
exists is a category function fitted to the machine: it would agree by
construction and could never report anything.  Written from the route alone,
it is a prediction.  If it later fails to match the machine, that is a
finding ABOUT THE MACHINE, and it can only be a finding if this came first.

## Why this is the whole-query obligation with no other instrument

On the `lcaNone` and the two `selectNone` branches the route value is `none`.
Result agreement therefore degenerates to `none = none`, which any impostor
that also answers `none` satisfies.  A machine that ran a leg it should have
skipped still answers `none`, because the output instruction branches on the
LCA result and not on the skipped leg.  So on those branches:

* the VALUE cannot see the spurious leg - it does not mention it;
* the RECEIPT cannot see a spurious leg that performs no read;
* a read-COUNT check cannot see it either, for the same reason;
* a LENGTH check cannot see it when the spurious leg charges as many ticks
  as the skip arm it replaced.

Only a POSITIONAL, per-constructor comparison of the category log separates
honest from impostor.  `lcaNone_impostor_*` below establishes exactly that,
by evaluation, with the four non-entailments stated rather than implied -
the shape of `spanNoneArm_discriminates`.

## The stage charges are parameters, and why

The select, close/LCA and rank machine legs belong to other lanes and their
category functions are not final.  Following `crossBlockArmCats`, which
takes `interiorCats` as a PARAMETER for exactly this reason, the per-stage
logs here are parameters.  What is asserted by this module is not their
content but the CONTROL STRUCTURE: which stages appear, in which order, on
which branch.  That is the part read off the route, and it is the part a
spurious leg violates.
-/

namespace RMQ
namespace WordRAM
namespace E1Query

open E1Machine
open RMQ.SuccinctFinal

/-! ## Per-stage charges -/

/--
The per-stage machine category logs the whole-query glue will supply, one
field per arm the route's five-instruction control program can take.

The `Skipped` fields are not padding.  The evaluator's `lcaClose` writes
`none` WITHOUT running its leaf when either select missed, and its
`rankCloseIfSome` returns the state untouched when the LCA missed; both are
executed instructions, so both charge.  A machine that charged nothing there
would be as wrong as one that ran the leg.
-/
structure WholeQueryStageCats where
  /-- The validity guard's accepting fall-through to the valid-path block. -/
  prologue : List Category
  /-- One select-close leg, indexed by the position it selects. -/
  select : Nat → List Category
  /-- The close/LCA leg when it RUNS, indexed by the closes it joins. -/
  lcaRun : Nat → Nat → List Category
  /-- The `lcaClose` instruction when it writes `none` without its leaf. -/
  lcaSkipped : List Category
  /-- The rank-close leg when it RUNS, indexed by the position it ranks. -/
  rankRun : Nat → List Category
  /-- The `rankCloseIfSome` instruction when it skips its leaf. -/
  rankSkipped : List Category
  /-- The output instruction on the answering arm. -/
  outputSome : List Category
  /-- The output instruction on the `none` arm. -/
  outputNone : List Category

/-! ## The category function

Indexed by `WholeQueryBranch` - the route's own classifier - so "a function
of the route's branch conditions" holds by construction.  The branch is an
ARGUMENT rather than something recomputed here, which additionally keeps the
fixtures below kernel-evaluable: `wholeQueryBranch` unfolds into the concrete
store and thence into `machineWordBits`/`Nat.log2`, which the kernel cannot
reduce, so a definition that computed the branch could not be evaluated at a
literal.
-/

/-- The whole-query machine category log on a given route branch. -/
def wholeQueryBranchCats (S : WholeQueryStageCats) (left right : Nat) :
    WholeQueryBranch → List Category
  | .leftSelectNone =>
      S.prologue ++ S.select left ++ S.select (right - 1) ++
        S.lcaSkipped ++ S.rankSkipped ++ S.outputNone
  | .rightSelectNone _ =>
      S.prologue ++ S.select left ++ S.select (right - 1) ++
        S.lcaSkipped ++ S.rankSkipped ++ S.outputNone
  | .lcaNone leftClose rightClose =>
      S.prologue ++ S.select left ++ S.select (right - 1) ++
        S.lcaRun leftClose rightClose ++ S.rankSkipped ++ S.outputNone
  | .full leftClose rightClose answerClose =>
      S.prologue ++ S.select left ++ S.select (right - 1) ++
        S.lcaRun leftClose rightClose ++ S.rankRun (answerClose + 1) ++
        S.outputSome

/-- The whole-query machine category log at the branch the route takes. -/
def wholeQueryCats (S : WholeQueryStageCats)
    (shape : Cartesian.CartesianShape) (left right : Nat) : List Category :=
  wholeQueryBranchCats S left right (wholeQueryBranch shape left right)

/-! ## What the control structure asserts

Each of these is a statement about WHICH stages appear on a branch, phrased
as independence: if the log does not mention a stage, then changing that
stage cannot change the log.  Independence is the sharpest available form -
it is exactly the claim a spurious leg falsifies.
-/

/-- On the `lcaNone` branch the log does not mention the rank leg: changing
the rank stage arbitrarily leaves it unchanged. -/
theorem wholeQueryBranchCats_lcaNone_independent_of_rankRun
    (S : WholeQueryStageCats) (f : Nat → List Category)
    (left right leftClose rightClose : Nat) :
    wholeQueryBranchCats { S with rankRun := f } left right
        (.lcaNone leftClose rightClose) =
      wholeQueryBranchCats S left right (.lcaNone leftClose rightClose) :=
  rfl

/-- On the `leftSelectNone` branch the log mentions neither the close/LCA leg
nor the rank leg. -/
theorem wholeQueryBranchCats_leftSelectNone_independent_of_legs
    (S : WholeQueryStageCats) (f : Nat → List Category)
    (g : Nat → Nat → List Category) (left right : Nat) :
    wholeQueryBranchCats { S with rankRun := f, lcaRun := g } left right
        .leftSelectNone =
      wholeQueryBranchCats S left right .leftSelectNone :=
  rfl

/-- On the `rightSelectNone` branch, likewise. -/
theorem wholeQueryBranchCats_rightSelectNone_independent_of_legs
    (S : WholeQueryStageCats) (f : Nat → List Category)
    (g : Nat → Nat → List Category) (left right leftClose : Nat) :
    wholeQueryBranchCats { S with rankRun := f, lcaRun := g } left right
        (.rightSelectNone leftClose) =
      wholeQueryBranchCats S left right (.rightSelectNone leftClose) :=
  rfl

/-- The full path is the ONLY branch whose log mentions the rank leg: on
every other branch the whole-query log is independent of it, at the route's
own classification. -/
theorem wholeQueryCats_independent_of_rankRun_off_full
    (S : WholeQueryStageCats) (f : Nat → List Category)
    (shape : Cartesian.CartesianShape) (left right : Nat)
    (hshort :
      ∀ leftClose rightClose answerClose,
        wholeQueryBranch shape left right ≠
          .full leftClose rightClose answerClose) :
    wholeQueryCats { S with rankRun := f } shape left right =
      wholeQueryCats S shape left right := by
  unfold wholeQueryCats
  cases hb : wholeQueryBranch shape left right with
  | leftSelectNone => rfl
  | rightSelectNone leftClose => rfl
  | lcaNone leftClose rightClose => rfl
  | full leftClose rightClose answerClose =>
      exact absurd hb (hshort leftClose rightClose answerClose)

/-! ## The `lcaNone` impostor, and the four non-entailments

The impostor is the third variety of the right-shape/wrong-content class: it
runs a leg the route skips.  Concretely it charges its spurious rank leg in
place of the skip arm, and it is built so that everything except a positional
category comparison agrees.

The stage charges below are a FIXTURE, not the real legs.  What the fixture
establishes is that the three other checks are formally incapable of
rejecting SOME impostor - which is what "the category log is the sole
remaining discriminator" means.  It does not claim the real legs charge these
particular ticks.
-/

/-- Fixture stage charges: one distinct tick per stage, so any positional
confusion between stages is visible.  The spurious rank leg is READ-FREE
(`.arithmetic`) and charges exactly as many ticks as the skip arm it
displaces, which is what defeats the read-count and length checks. -/
def fixtureStageCats : WholeQueryStageCats where
  prologue := [.registerWrite]
  select := fun _ => [.memoryRead]
  lcaRun := fun _ _ => [.comparison]
  lcaSkipped := [.branch]
  rankRun := fun _ => [.arithmetic]
  rankSkipped := [.branch]
  outputSome := [.control]
  outputNone := [.control]

/-- The honest log on the route's `lcaNone` branch: the rank leg is skipped. -/
def lcaNoneHonestCats : List Category :=
  wholeQueryBranchCats fixtureStageCats 4 9 (.lcaNone 3 5)

/-- The impostor's log: identical except that it RAN the rank leg where the
route skips it. -/
def lcaNoneImpostorCats : List Category :=
  fixtureStageCats.prologue ++ fixtureStageCats.select 4 ++
    fixtureStageCats.select 8 ++ fixtureStageCats.lcaRun 3 5 ++
    fixtureStageCats.rankRun 6 ++ fixtureStageCats.outputNone

/-! The two fixture logs, spelled out.  Kept as checked equations so that a
later edit to `fixtureStageCats` which accidentally collapsed the two logs -
and so made every discriminator below vacuous - fails here first. -/

theorem lcaNoneHonestCats_eq :
    lcaNoneHonestCats =
      [.registerWrite, .memoryRead, .memoryRead, .comparison, .branch,
        .control] := rfl

theorem lcaNoneImpostorCats_eq :
    lcaNoneImpostorCats =
      [.registerWrite, .memoryRead, .memoryRead, .comparison, .arithmetic,
        .control] := rfl

/-- THE DISCRIMINATOR: the two logs differ, positionally. -/
theorem lcaNone_impostor_catLogs_differ :
    lcaNoneImpostorCats ≠ lcaNoneHonestCats := by
  decide

/-- NON-ENTAILMENT 1 - a LENGTH check cannot reject the impostor. -/
theorem lcaNone_impostor_lengths_agree :
    lcaNoneImpostorCats.length = lcaNoneHonestCats.length := by
  decide

/-- NON-ENTAILMENT 2 - a memory-read COUNT check cannot reject it: the
spurious leg reads nothing, so both charge the same two reads. -/
theorem lcaNone_impostor_memoryRead_counts_agree :
    catCount lcaNoneImpostorCats .memoryRead =
      catCount lcaNoneHonestCats .memoryRead := by
  decide

/-- The count both logs report is `2`, so the agreement above is not the
degenerate `0 = 0`. -/
theorem lcaNone_impostor_memoryRead_count_is_two :
    catCount lcaNoneHonestCats .memoryRead = 2 := by
  decide

/-- NON-ENTAILMENT 3 - a VALUE check cannot reject it.  On the `lcaNone`
branch the route value is `none` for EVERY shape, and the value function does
not mention the rank stage at all, so no value comparison can detect a
spurious rank leg. -/
theorem lcaNone_value_is_none
    (shape : Cartesian.CartesianShape) (leftClose rightClose : Nat) :
    wholeQueryBranchValue shape (.lcaNone leftClose rightClose) = none :=
  rfl

/-- NON-ENTAILMENT 4 - the exact reach of a RECEIPT check.

An impostor that runs a spurious leg appends that leg's receipt to the
honest one.  So the receipt check rejects it if and only if the spurious leg
performs AT LEAST ONE read: a read-free spurious leg is receipt-invisible.

Stated as an iff rather than as `t ++ [] = t`, which is true of any list and
would say nothing about this machine.  The `only if` direction is the
non-entailment; the `if` direction records that the receipt check is not
useless, merely blind in exactly this case - which is the case the category
log alone must catch. -/
theorem impostor_traces_agree_iff_readFree
    (honest spurious : List WordRAM.TraceEvent) :
    honest ++ spurious = honest ↔ spurious = [] := by
  constructor
  · intro h
    have h' : honest ++ spurious = honest ++ [] := by
      rw [h, List.append_nil]
    exact List.append_cancel_left h'
  · intro h
    rw [h, List.append_nil]

/-- The route's own `lcaNone` receipt is the three-leg concatenation, with no
rank leg in it - so the impostor's spurious rank leg is precisely the
`spurious` of the iff above. -/
theorem lcaNone_trace_has_no_rank_leg
    (shape : Cartesian.CartesianShape) (left right leftClose rightClose : Nat) :
    wholeQueryBranchTrace shape left right (.lcaNone leftClose rightClose) =
      (concreteBPNativeSelectCloseGlobalWordTraceResult shape left).trace ++
        (concreteBPNativeSelectCloseGlobalWordTraceResult shape
          (right - 1)).trace ++
        (concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
          shape leftClose rightClose).trace :=
  rfl

/-- The honest and impostor logs differ at exactly ONE position, and it is
the position of the skipped leg - so the defect is the leg, not a global
shift.  (Position 4, zero-indexed.) -/
theorem lcaNone_impostor_differ_at_rank_slot :
    lcaNoneImpostorCats[4]? = some .arithmetic ∧
      lcaNoneHonestCats[4]? = some .branch ∧
      lcaNoneImpostorCats.take 4 = lcaNoneHonestCats.take 4 ∧
      lcaNoneImpostorCats.drop 5 = lcaNoneHonestCats.drop 5 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-! ## The same statement for the `selectNone` branches

There the machine runs FEWER legs still - both the close/LCA leg and the rank
leg are skipped - so there are two spurious legs available to an impostor.
-/

/-- The honest log on the route's `leftSelectNone` branch. -/
def leftSelectNoneHonestCats : List Category :=
  wholeQueryBranchCats fixtureStageCats 4 9 .leftSelectNone

/-- An impostor that ran BOTH skipped legs. -/
def leftSelectNoneImpostorCats : List Category :=
  fixtureStageCats.prologue ++ fixtureStageCats.select 4 ++
    fixtureStageCats.select 8 ++ fixtureStageCats.lcaRun 3 5 ++
    fixtureStageCats.rankRun 6 ++ fixtureStageCats.outputNone

/-- THE DISCRIMINATOR on the left-select-none branch. -/
theorem leftSelectNone_impostor_catLogs_differ :
    leftSelectNoneImpostorCats ≠ leftSelectNoneHonestCats := by
  decide

/-- Same length: a length check cannot reject it. -/
theorem leftSelectNone_impostor_lengths_agree :
    leftSelectNoneImpostorCats.length = leftSelectNoneHonestCats.length := by
  decide

/-- Same read count, and it is not the degenerate `0 = 0`. -/
theorem leftSelectNone_impostor_memoryRead_counts_agree :
    catCount leftSelectNoneImpostorCats .memoryRead =
      catCount leftSelectNoneHonestCats .memoryRead ∧
    catCount leftSelectNoneHonestCats .memoryRead = 2 := by
  refine ⟨by decide, by decide⟩

/-- The route value is `none` on both select-miss branches, for every shape:
a value check cannot reject either impostor. -/
theorem selectNone_values_are_none
    (shape : Cartesian.CartesianShape) (leftClose : Nat) :
    wholeQueryBranchValue shape .leftSelectNone = none ∧
      wholeQueryBranchValue shape (.rightSelectNone leftClose) = none :=
  ⟨rfl, rfl⟩

end E1Query
end WordRAM
end RMQ
