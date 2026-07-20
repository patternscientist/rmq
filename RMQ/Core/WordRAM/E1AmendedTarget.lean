/-
# REQ-E1-07: the amended familiar-machine target Prop, and its supersession note

This module STATES `E1AmendedFamiliarMachineTarget` and records precisely how
it relates to the refuted `E1R3FamiliarMachineTarget`.  It does not prove the
target.  The STATEMENT does not need the proof, and stating it is what lets
downstream rows name a real consumer instead of a hypothetical one.

What IS proved here:

* `amendedTarget_invalidGuard` -- the target's INVALID conjunct, discharged
  outright for every `validPath`, so that conjunct is known satisfiable at the
  intended instantiation rather than merely written down;
* `amendedTarget_of_wholeQueryAgreement` -- the REDUCTION: supply whole-query
  agreement on valid ranges and the derived literal cap, and the target
  follows.

## STATUS OF THE TARGET, corrected 2026-07-19 (E1-LaneJ, DD-20260719-247)

TWO SENTENCES THAT STOOD HERE WERE FALSE AT THIS HEAD AND ARE CORRECTED
RATHER THAN LEFT, because this module is the supersession note's home and a
note that misdescribes its own subject is the defect REQ-E1-07 exists to
prevent.

1. This header said the proof "needs the whole-query program, which does not
   exist in the tree".  IT EXISTS: `wholeQueryValidPath`
   (`E1WholeQueryProgram.lean:518`, length `5636` at `:523`), run by
   `wholeQueryMachineAgrees_of_bounds` (`E1WholeQueryAgreement.lean:64`).
2. The reduction's blurb said "Nothing else is owed."  MORE IS OWED, and it is
   not a matter of filling the two slots.  `E1AmendedFamiliarMachineTarget` is
   NOT PROVED anywhere in the tree -- it appears only in this file -- and
   `amendedTarget_of_wholeQueryAgreement` HAS NO CONSUMER.  Three quantifier
   mismatches separate the reduction's `hagree` from what is discharged, and
   each is a property of the STATEMENTS, not of the proofs:

   * **Store.**  `hagree` demands agreement for `∀ (store : ReadStore)`.
     `wholeQueryMachineAgrees_of_bounds` supplies it only at
     `concreteBPNativeSuccinctRMQGlobalReadStore shape`.  The universal form
     is moreover not merely unproved: `WholeQueryMachineAgrees` pins the run's
     receipt to `wholeQueryRouteTrace shape left right`, a list of values
     fixed by the shape, so a store answering differently falsifies it.  The
     invalid conjunct survives `∀ store` only because the guard path performs
     no read.
   * **`validPath`.**  The target binds ONE `validPath : List Instr` outside
     the quantification over `xs`; the discharged agreement runs the
     SHAPE-INDEXED `wholeQueryValidPath shape wholeQueryNoneExit`.
   * **`S`.**  The target binds ONE `S : WholeQueryStageCats` outside the
     quantification over `xs`; both the agreement and the literal
     (`wholeQueryCats_machineS_length_le`,
     `E1WholeQueryCostLiteral.lean:538`) are stated at the SHAPE-INDEXED
     `wholeQueryMachineS shape` (`E1WholeQueryAgreement.lean:49`).

   Recorded, not repaired.  Whether the target's binders should move inside
   the `xs` quantification -- making `validPath` and `S` functions of the
   shape -- changes a Prop that REQ-E1-07 names, so it is a coordinator
   decision and not this lane's to take.

   This module also does not import `E1WholeQueryAgreement`; its only import
   is `E1CostAlgebra`.  That is a consequence of the above, not the cause.

## THE SUPERSESSION NOTE

`E1R3FamiliarMachineTarget` (recoverable as a git object at commit `7fe5b8b`,
`RMQ/Core/SuccinctFinalSmallStep.lean:37016`; absent from HEAD sources) was
REFUTED by `e1R3FamiliarMachineTarget_obstruction` (`:37046`).  This target
supersedes it.  The old target is superseded, NOT proved; nothing here claims
otherwise.

**WHICH CLAUSE FAILED.**  The refuted Prop had THREE top-level conjuncts.  The
first two -- the invalid-guard clause and the valid-path accounting clause --
were not what failed.  What failed is the **THIRD** conjunct, the familiar
local-iteration LOWER bound:

    (∀ xs left right localCount,
      E1R3CanonicalSameBlockInvocation xs left right localCount →
        localCount ≤ (execute xs left right).localBPSteps)

**THE REFUTING WITNESS** is `e1R3CanonicalSameBlockInvocation_unbounded`
(`7fe5b8b:RMQ/Core/SuccinctFinalSmallStep.lean:36941`), which produces, for
ANY proposed `literalTotal`, a canonical same-block invocation whose
`localCount` EXCEEDS it.  The obstruction is then immediate: the third
conjunct forces `localCount ≤ localBPSteps`, the second forces
`localBPSteps ≤ totalSmallSteps ≤ literalTotal`, and the witness makes
`localCount > literalTotal`.  So the refutation is of the CONJUNCTION -- an
all-size literal step cap and an unbounded local-iteration lower bound cannot
both hold -- and not of either clause alone.

**HOW THE AMENDMENT RESOLVES IT, precisely.**  Not by weakening the cap, and
not by deleting an inconvenient clause.  The amended route performs no
familiar local-BP iteration at all: the same-block close is a charged-table
lookup, so `E1R3CanonicalSameBlockInvocation`'s domain -- the scan whose
length the third conjunct was charging -- does not exist on the amended
machine.  The clause is eliminated because its SUBJECT is gone, which is why
the amended Prop omits it rather than restating it with a bound.

**THE CATEGORY SET IS REFROZEN, NOT INHERITED.**  The refuted target carried
FIVE step categories, as fields of `E1R3FamiliarRunPacket`: `controllerSteps`,
`decodingSteps`, `arithmeticSteps`, `localBPSteps`, `mergeSteps`.  The amended
machine freezes SIX (DD-20260718-005), as constructors of `Category`:
`memoryRead`, `registerWrite`, `arithmetic`, `comparison`, `branch`,
`control`.  These are different partitions of different machines -- note that
`localBPSteps`, the category the refutation turned on, has NO successor in the
six -- so the accounting conjunct below is stated against the six and its
identity is `catCount_partition`, not an inherited five-way sum.

**THE COST CLAUSE STAYS AN EQUALITY.**  The refuted target demanded
`packet.publicModeledCost = accepted.toCosted.cost`.  That is preserved here
as an equality (`catCount cats .memoryRead = (queryCosted xs left right).cost`)
and deliberately NOT weakened to `≤`.  Only the TOTAL-STEP clause is an
inequality, and that is the shape REQ-E1-06 conjunct (c) itself asks for.

**ON THE ROW'S OWN PHRASE "literal cap 33/8".**  REQ-E1-07's frozen text
describes the amended route as one where "every loop is a chunk fold with
literal cap 33/8".  That sentence is true after B7 but its numerals are
ambiguous, and this note does not repeat it unqualified.

THERE ARE THREE `33`s.  All three were checked at source, 2026-07-19
(E1-LaneJ, DD-20260719-246); the first two had never been flagged as
distinct, and they are the dangerous pair because one sits INSIDE the other's
sibling term in the same sum.

* the **fringe-window chunk-read cap**, the literal `33` in the chunk count
  `Nat.min (relHi / c + 1) 33` (`ChargedFringeChunks.lean:1647`, `:1665`),
  discharged to a bound by `Nat.add_le_add_left (Nat.min_le_right _ 33) 4`
  (`:1676`, `:1687`).  It does NOT appear in the whole-query sum on its own:
  it sits inside `endpointFringe`, whose constant is declared as the literal
  `bpChunkedEndpointFringeChargedTraceCost : Nat := 37`
  (`ChargedFringeSubstitution.lean:25`).  The reading `37 = 4 + 33` is the
  JUSTIFICATION -- four window-word reads plus the capped fold -- and not the
  declaration.
* the **whole-interior-directory read cap**,
  `canonicalRelativeRmmPrincipledInteriorChargedTraceCost : Nat := 33`
  (`InteriorDirectory.lean:1934`).  This one DOES appear in the sum, as the
  `interiorDirectory` field (`SuccinctFinalRAM.lean:8817`).
* `3 * rankClose = 33`, a pure coincidence of value: `rankClose := 11`
  (`SuccinctFinalRAM.lean:8814`).  Nothing multiplies `rankClose` by three;
  the sum uses it twice inside `closeLCA` and once outside.

The whole-query algebra in which two of the three sit is
`2*35 + (2*11 + 2*37 + 33) + 11 = 210`, with `closeLCA = 129`
(`concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost_eq`,
`SuccinctFinalRAM.lean:8828`; `...CloseCost_eq`, `:8823`).

THERE ARE TWO `8`s, already flagged distinct by the M3d-11/M3d-12 matrix
notes and re-checked here: the fringe's per-word chunk cap
(`machineWordBits_le_8_mul_bpFringeChunkBits`, `ChargedWordChunks.lean:39`,
with `bpWordChunkCount_le_eight` at `:153` capping inside the definition at
`:150`), and the interior table adapter's per-read chunk cap
(`interiorChunkCount_le_eight`, `E1InteriorChunkFold.lean:189` -- note the
FILE, which earlier drafts of this note omitted; it is not in
`E1InteriorChunkCap.lean` despite that module's name).  The loop the row's
`8` must mean, for the sentence to be true, is the interior adapter's.

`11886` -- the derived all-size STEP literal -- is none of these and is not
comparable with `210`, which bounds READS.  Recorded here because the two
numerals will now sit near each other in every summary of this work, and
adjacency is exactly how the two `33`s came to be conflated.
-/
import RMQ.Core.WordRAM.E1CostAlgebra

namespace RMQ
namespace WordRAM
namespace E1Amended

open E1Machine
open E1Query

/--
THE AMENDED FAMILIAR-MACHINE TARGET.

Existentially: a query program (as a `validPath` filling the skeleton's valid
branch), a route-side stage assignment `S` fixing the category log, and one
all-size literal step bound.  Then two conjuncts.

**WHY THERE IS NO WIDTH CONJUNCT HERE, stated rather than quietly omitted.**
REQ-E1-02's width accounting is deliberately NOT folded into this Prop,
because neither available spelling is honest:

* `ProgramFits (SuccinctRank.machineWordBits n) (programSkeleton n validPath)`
  is FALSE at small `n`.  `machineWordBits n = Nat.log2 n + 1`, so at `n = 4`
  the modeled width is `3` and the fitting bound is `2 ^ 3 = 8`, while the
  register file this construction allocates reaches `152`.  A target
  asserting it would be unsatisfiable for a reason that has nothing to do
  with the machine being right.
* `∀ n, ∃ w, ProgramFits w (programSkeleton n validPath)` is VACUOUS: every
  finite instruction list fits some width, so the conjunct would exclude
  nothing and would be a decorative hypothesis.

The tree's own width certificates resolve this by taking `w` as a PARAMETER
carrying explicit side conditions -- `sameBlockLegProgramAt_fits`
(`E1ProgramWidth.lean:57`) takes eleven, including `74 < 2 ^ w` and
`SuccinctRank.machineWordBits shape.bpCode.length < 2 ^ w`.  Those side
conditions cannot be collapsed into this Prop without picking one of the two
bad spellings above.  Width accounting therefore stays where it already
lives, as REQ-E1-02's row against `E1ProgramWidth`, and this Prop does not
restate it.  DD-20260719-142.

**(1) The invalid guard.**  Empty, reversed and out-of-bounds ranges reach the
guarded none-packet with an EMPTY receipt and a memory-read charge equal to
the accepted invalid cost.  The guard's category log is NAMED
(`guardRejectCats`), not quantified away.

**(2) The valid path.**  Result agreement, POSITIONAL receipt equality with
the accepted trace, the modeled-cost EQUALITY, the six-category accounting
identity, and the derived literal total.

The category log is `wholeQueryCats S shape left right` -- a function of the
ROUTE's own branch classification, named rather than existentially quantified.
This matters and is not stylistic: quantified away and reduced to a read count
plus a length bound, the clause could not reject an impostor whose log has one
slot changed from `.comparison` to `.branch`, since both aggregates are exactly
preserved by such a change.  It is also the only clause with any force on the
`none` branches, where result agreement degenerates to `none = none`.

The quantification is over ALL lists and ALL valid ranges, not a demo fixture.
-/
def E1AmendedFamiliarMachineTarget : Prop :=
  ∃ (validPath : List Instr) (S : WholeQueryStageCats) (literalTotal : Nat),
    -- (1) THE INVALID GUARD
    (∀ (store : ReadStore) (xs : List Int) (left right : Nat),
      ¬ ValidRange xs left right →
        ∃ final : State,
          RunsTo store (programSkeleton xs.length validPath)
              (initialState left right) final []
              (guardRejectCats left right) ∧
            final.halted = true ∧
            decodePacket (final.regs regOut) =
              (SuccinctClassic.queryCosted xs left right).value ∧
            ([] : List TraceEvent) =
              (SuccinctClassic.queryTraceResult xs left right).trace ∧
            catCount (guardRejectCats left right) Category.memoryRead =
              (SuccinctClassic.queryCosted xs left right).cost) ∧
    -- (2) THE VALID PATH
    (∀ (store : ReadStore) (xs : List Int) (left right : Nat),
      ValidRange xs left right →
        ∃ final : State,
          RunsTo store (programSkeleton xs.length validPath)
              (initialState left right) final
              (SuccinctClassic.queryTraceResult xs left right).trace
              (wholeQueryCats S (SuccinctClassic.cartesianShape xs)
                left right) ∧
            final.halted = true ∧
            decodePacket (final.regs regOut) =
              (SuccinctClassic.queryCosted xs left right).value ∧
            -- the modeled-cost EQUALITY, preserved from the refuted target
            catCount (wholeQueryCats S (SuccinctClassic.cartesianShape xs)
                left right) Category.memoryRead =
              (SuccinctClassic.queryCosted xs left right).cost ∧
            -- the SIX-category accounting identity
            (wholeQueryCats S (SuccinctClassic.cartesianShape xs)
                left right).length =
              catCount (wholeQueryCats S (SuccinctClassic.cartesianShape xs)
                  left right) Category.memoryRead +
                catCount (wholeQueryCats S (SuccinctClassic.cartesianShape xs)
                  left right) Category.registerWrite +
                catCount (wholeQueryCats S (SuccinctClassic.cartesianShape xs)
                  left right) Category.arithmetic +
                catCount (wholeQueryCats S (SuccinctClassic.cartesianShape xs)
                  left right) Category.comparison +
                catCount (wholeQueryCats S (SuccinctClassic.cartesianShape xs)
                  left right) Category.branch +
                catCount (wholeQueryCats S (SuccinctClassic.cartesianShape xs)
                  left right) Category.control ∧
            -- the DERIVED all-size literal total, an INEQUALITY
            (wholeQueryCats S (SuccinctClassic.cartesianShape xs)
                left right).length ≤ literalTotal)

/--
THE INVALID CONJUNCT, DISCHARGED.

Conjunct (2) of the target holds for EVERY `validPath`, with no hypothesis on
the valid branch at all -- the guard rejects before reaching it.  So that
conjunct is known SATISFIABLE at the intended instantiation, not merely
written down.

This is the whole of REQ-E1-05's Lean-side obligation, restated at the target
Prop; the row's remaining residual is that it be exercised in the VALIDATOR,
which is a harness obligation and not a proof obligation.
-/
theorem amendedTarget_invalidGuard (validPath : List Instr) :
    ∀ (store : ReadStore) (xs : List Int) (left right : Nat),
      ¬ ValidRange xs left right →
        ∃ final : State,
          RunsTo store (programSkeleton xs.length validPath)
              (initialState left right) final []
              (guardRejectCats left right) ∧
            final.halted = true ∧
            decodePacket (final.regs regOut) =
              (SuccinctClassic.queryCosted xs left right).value ∧
            ([] : List TraceEvent) =
              (SuccinctClassic.queryTraceResult xs left right).trace ∧
            catCount (guardRejectCats left right) Category.memoryRead =
              (SuccinctClassic.queryCosted xs left right).cost := by
  intro store xs left right hbad
  obtain ⟨final, hrun, hhalted, hout, htrace, hcost, _hlen⟩ :=
    programSkeleton_invalid_matches_public_guard store xs validPath hbad
  exact ⟨final, hrun, hhalted, hout, htrace, hcost⟩

/--
THE REDUCTION: exactly what the target still owes.

Two inputs, each a real outstanding item, and nothing else:

* `hagree` -- whole-query agreement on every valid range, which is the
  whole-query PROGRAM's simulation and the single blocking item for assembly;
* `hcap` -- the DERIVED all-size literal, which is the summation over the
  per-block addends in `E1CostAlgebra`.

The invalid conjunct needs no input: it is already discharged above.

Stating the reduction is what makes this Prop a usable consumer.  A row that
names `E1AmendedFamiliarMachineTarget` as its downstream consumer can now
point at a theorem saying what would discharge it, rather than at a
definition that nothing connects to.
-/
theorem amendedTarget_of_wholeQueryAgreement
    (validPath : List Instr) (S : WholeQueryStageCats) (literalTotal : Nat)
    (hagree : ∀ (store : ReadStore) (xs : List Int) (left right : Nat),
      ValidRange xs left right →
        WholeQueryMachineAgrees store xs.length validPath S
          (SuccinctClassic.cartesianShape xs) left right)
    (hcap : ∀ (xs : List Int) (left right : Nat),
      ValidRange xs left right →
        (wholeQueryCats S (SuccinctClassic.cartesianShape xs)
          left right).length ≤ literalTotal) :
    E1AmendedFamiliarMachineTarget := by
  refine ⟨validPath, S, literalTotal,
    amendedTarget_invalidGuard validPath, ?_⟩
  intro store xs left right hvalid
  obtain ⟨final, hrun, hhalted, hout, hcost⟩ :=
    programSkeleton_valid_matches_public store xs validPath S hvalid
      (hagree store xs left right hvalid)
  exact ⟨final, hrun, hhalted, hout, hcost,
    (catCount_partition _).symm, hcap xs left right hvalid⟩

end E1Amended
end WordRAM
end RMQ
