/-
# REQ-E1-07: the amended familiar-machine target Prop, and its supersession note

This module STATES `E1AmendedFamiliarMachineTarget`, PROVES it by exhibiting
the construction, and records precisely how it relates to the refuted
`E1R3FamiliarMachineTarget`.

What is proved here:

* `amendedTarget_invalidGuard` -- the target's INVALID conjunct, discharged
  outright for every `validPath`, so that conjunct is known satisfiable at the
  intended instantiation rather than merely written down;
* `amendedTarget_of_wholeQueryAgreement` -- the REDUCTION: supply whole-query
  agreement on valid ranges and the derived literal cap, and the target
  follows;
* `amendedFamiliarMachineTarget_holds` -- **THE TARGET ITSELF**, discharged by
  feeding the reduction the landed whole-query construction.  This is the
  reduction's consumer;
* `uniformStore_amendedTarget_refuted` -- the SUPERSEDED spelling of the
  target, refuted as a checked theorem.

## THE STORE REPAIR, 2026-07-19 (E1-LaneK, DD-20260719-260)

An earlier form of this Prop quantified its VALID-PATH conjunct over
`∀ (store : ReadStore)`.  **That form is false**, and it is refuted below
rather than merely avoided.

`WholeQueryMachineAgrees` pins the run's receipt to
`wholeQueryRouteTrace shape left right` -- a list of values fixed by the
SHAPE, carrying each read's answer.  But `execInstr` writes the answer the
SUPPLIED store gives (`E1Machine.lean:160`), so every event of a `RunsTo`
receipt is `readWord segment index (store.readWord? segment index)`
(`run_readLog_readWord_shape`, `E1Machine.lean:430`).  A receipt fixed
independently of the store therefore cannot be produced under every store as
soon as it is NONEMPTY -- two stores that answer differently would have to
yield the same event.  That is `no_uniform_store_run` below, and the
whole-query receipt is nonempty on every valid range because the machine
charges at least one read there (`wholeQueryCats_machineS_memoryRead_pos`).

The invalid conjunct KEEPS `∀ store`, and that asymmetry is the point: the
guard rejects before reaching any `readMem`, so its receipt is `[]` and the
universal form is both true and strictly stronger.  Retaining it where it
holds and dropping it where it fails is what makes the repair a correction
rather than a weakening.

Two further binder repairs, from the same audit:

* **`validPath`.**  Was ONE `List Instr` bound outside the quantification
  over `xs`; the discharged agreement runs the SHAPE-INDEXED
  `wholeQueryValidPath shape wholeQueryNoneExit`.  It is now a FUNCTION
  `Cartesian.CartesianShape → List Instr`.
* **`S`.**  Was ONE `WholeQueryStageCats` bound outside the quantification
  over `xs`; the agreement and the literal
  (`wholeQueryCats_machineS_length_le`, `E1WholeQueryCostLiteral.lean:538`)
  are stated at the SHAPE-INDEXED `wholeQueryMachineS shape`
  (`E1WholeQueryAgreement.lean:49`).  It is now a FUNCTION
  `Cartesian.CartesianShape → WholeQueryStageCats`.

**The binders became FUNCTIONS OF THE SHAPE rather than moving inside the
`xs` quantification, and the difference is load-bearing.**  Moving the
existential inside would assert only that each input has SOME program, which
is not one machine; keeping the binders outside as functions asserts ONE
uniform construction that every input is run against.  The weaker spelling
would have been easier to prove and would not have been the claim.

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
import RMQ.Core.WordRAM.E1WholeQueryCostLiteral

namespace RMQ
namespace WordRAM
namespace E1Amended

open E1Machine
open E1Query
open E1SelectBridge
open E1SelectDispatch
open RMQ.SuccinctFinal
open RMQ.SuccinctClose
open RMQ.SuccinctSelect
open RMQ.GenericSelect

/-! ## The store-uniformity obstruction

Stated before the target so the target's shape can cite it. -/

/-- Every event of a `RunsTo` receipt is a `readWord` against the SUPPLIED
store, at the address the run executed.  The relational form of
`run_readLog_readWord_shape` (`E1Machine.lean:430`). -/
theorem runsTo_readLog_readWord_shape
    {store : ReadStore} {program : E1Machine.Program} {s s' : State}
    {reads : List TraceEvent} {cats : List Category}
    (h : RunsTo store program s s' reads cats) :
    ∀ event ∈ reads, ∃ segment index,
      event = TraceEvent.readWord segment index
        (store.readWord? segment index) := by
  intro event hmem
  have hrun : run store program cats.length s =
      ⟨s', reads, cats, cats.length⟩ := h
  have hmem' : event ∈ (run store program cats.length s).readLog := by
    rw [hrun]; exact hmem
  exact run_readLog_readWord_shape store program cats.length s event hmem'

/--
**A RECEIPT FIXED INDEPENDENTLY OF THE STORE CANNOT BE PRODUCED UNDER EVERY
STORE, once it is nonempty.**

This is the whole content of the store repair recorded in the header.  The
two witnesses answer `none` and `some []` at every address, so a single
event cannot agree with both.

Nonemptiness is LOAD-BEARING and not a technicality: on an empty receipt the
statement is false, which is exactly why the target's INVALID conjunct
survives `∀ store`. -/
theorem no_uniform_store_run
    {program : E1Machine.Program} {s : State}
    {reads : List TraceEvent} {cats : List Category}
    (hne : reads ≠ [])
    (h : ∀ store : ReadStore,
      ∃ s' : State, RunsTo store program s s' reads cats) :
    False := by
  obtain ⟨e, he⟩ : ∃ e, e ∈ reads := by
    cases reads with
    | nil => exact absurd rfl hne
    | cons a t => exact ⟨a, List.mem_cons_self ..⟩
  obtain ⟨s₁, h₁⟩ := h ⟨fun _ _ => none⟩
  obtain ⟨s₂, h₂⟩ := h ⟨fun _ _ => some []⟩
  obtain ⟨g₁, i₁, he₁⟩ := runsTo_readLog_readWord_shape h₁ e he
  obtain ⟨g₂, i₂, he₂⟩ := runsTo_readLog_readWord_shape h₂ e he
  rw [he₁] at he₂
  simp at he₂

/-! ## The whole-query receipt is nonempty on a valid range

Not by evaluation: the concrete traces do not reduce in the kernel (the
branch classifier unfolds into `machineWordBits`/`Nat.log2`, as
`E1WholeQueryCats.lean:129` records).  It is derived instead from the
machine's own CHARGE, which is symbolic. -/

/-- Category counts add over `++`. -/
theorem catCount_append (a b : List Category) (t : Category) :
    catCount (a ++ b) t = catCount a t + catCount b t := by
  induction a with
  | nil => simp [catCount]
  | cons c rest ih => simp [catCount_cons, ih]; omega

/-- **THE SELECT LEG CHARGES A READ whenever its index is in range.**  The
in-range arm reaches `entryReadCats` (`E1SelectBridge.lean:258`), whose first
four entries are `memoryRead`; the out-of-range arm charges no read at all,
which is why the hypothesis cannot be dropped. -/
theorem selectCloseCats_memoryRead_pos
    {bits : List Bool} {target : Bool} {rso rbo : Nat}
    (data : SparseExceptionSelectData bits target rso rbo)
    (layout : SparseExceptionSelectTraceSegmentLayout)
    (G ST : Nat) (store : ReadStore) (c idx : Nat)
    (hidx : idx < occurrenceCount bits target) :
    0 < catCount (selectCloseCats data layout G ST store c idx)
      Category.memoryRead := by
  unfold selectCloseCats
  rw [if_pos hidx]
  simp [catCount_cons, entryReadCats, selectPrologueCats,
    selectSuperSlotCats, catCount]
  omega

/-- **THE WHOLE-QUERY MACHINE CHARGES AT LEAST ONE READ on every valid
range**, on whichever of the four branches the route takes -- every branch
runs the left select leg.  `occurrenceCount shape.bpCode false` is
`shape.size` (`falseSelectOccurrenceCount_eq_size`), which is what puts
`left` in range. -/
theorem wholeQueryCats_machineS_memoryRead_pos
    (shape : Cartesian.CartesianShape) (left right : Nat)
    (hlt : left < right) (hshape : right ≤ shape.size) :
    0 < catCount (wholeQueryCats (wholeQueryMachineS shape) shape left right)
      Category.memoryRead := by
  have hocc : left < occurrenceCount shape.bpCode false := by
    have h1 : falseSelectOccurrenceCount shape = shape.size :=
      falseSelectOccurrenceCount_eq_size shape
    have h2 : falseSelectOccurrenceCount shape =
        occurrenceCount shape.bpCode false := rfl
    omega
  have hsel := selectCloseCats_memoryRead_pos (wholeQuerySelData shape)
    concreteBPNativeSelectCloseTraceSegmentLayout
    concreteBPNativeRankCloseTraceSegmentBase
    concreteBPNativeSelectChunkTraceSegment
    (concreteBPNativeSuccinctRMQGlobalReadStore shape)
    (bpFringeChunkBits shape.bpCode.length) left hocc
  unfold wholeQueryCats
  cases hb : wholeQueryBranch shape left right <;>
    simp only [wholeQueryBranchCats, wholeQueryMachineS,
      wholeQueryMachineStageCats, catCount_append] <;>
    omega

/-- **THE PUBLIC RECEIPT IS NONEMPTY on every valid range.**  Via the landed
agreement: the machine's receipt IS that trace, and its length is the
machine's `memoryRead` count, which the lemma above puts above zero. -/
theorem queryTraceResult_trace_ne_nil
    (xs : List Int) {left right : Nat} (hvalid : ValidRange xs left right) :
    (SuccinctClassic.queryTraceResult xs left right).trace ≠ [] := by
  have hsize : (SuccinctClassic.cartesianShape xs).size = xs.length :=
    Cartesian.shape_size xs
  obtain ⟨final, hrun, _, _, _⟩ :=
    programSkeleton_valid_matches_public_at_machineS xs hvalid
  have hlen := RunsTo.readLog_length_eq_memoryRead_count hrun
  have hpos := wholeQueryCats_machineS_memoryRead_pos
    (SuccinctClassic.cartesianShape xs) left right hvalid.1
    (by rw [hsize]; exact hvalid.2)
  intro hnil
  rw [hnil] at hlen
  simp at hlen
  omega

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
  ∃ (validPath : Cartesian.CartesianShape → List Instr)
    (S : Cartesian.CartesianShape → WholeQueryStageCats)
    (literalTotal : Nat),
    -- (1) THE INVALID GUARD, at EVERY store: the guard reads nothing, so the
    -- universal form is true here and is kept.
    (∀ (store : ReadStore) (xs : List Int) (left right : Nat),
      ¬ ValidRange xs left right →
        ∃ final : State,
          RunsTo store
              (programSkeleton xs.length
                (validPath (SuccinctClassic.cartesianShape xs)))
              (initialState left right) final []
              (guardRejectCats left right) ∧
            final.halted = true ∧
            decodePacket (final.regs regOut) =
              (SuccinctClassic.queryCosted xs left right).value ∧
            ([] : List TraceEvent) =
              (SuccinctClassic.queryTraceResult xs left right).trace ∧
            catCount (guardRejectCats left right) Category.memoryRead =
              (SuccinctClassic.queryCosted xs left right).cost) ∧
    -- (2) THE VALID PATH, at THE CANONICAL STORE the agreement is about.
    (∀ (xs : List Int) (left right : Nat),
      ValidRange xs left right →
        ∃ final : State,
          RunsTo
              (concreteBPNativeSuccinctRMQGlobalReadStore
                (SuccinctClassic.cartesianShape xs))
              (programSkeleton xs.length
                (validPath (SuccinctClassic.cartesianShape xs)))
              (initialState left right) final
              (SuccinctClassic.queryTraceResult xs left right).trace
              (wholeQueryCats (S (SuccinctClassic.cartesianShape xs))
                (SuccinctClassic.cartesianShape xs) left right) ∧
            final.halted = true ∧
            decodePacket (final.regs regOut) =
              (SuccinctClassic.queryCosted xs left right).value ∧
            -- the modeled-cost EQUALITY, preserved from the refuted target
            catCount (wholeQueryCats (S (SuccinctClassic.cartesianShape xs))
                (SuccinctClassic.cartesianShape xs) left right)
                Category.memoryRead =
              (SuccinctClassic.queryCosted xs left right).cost ∧
            -- the SIX-category accounting identity
            (wholeQueryCats (S (SuccinctClassic.cartesianShape xs))
                (SuccinctClassic.cartesianShape xs) left right).length =
              catCount (wholeQueryCats (S (SuccinctClassic.cartesianShape xs))
                  (SuccinctClassic.cartesianShape xs) left right)
                  Category.memoryRead +
                catCount (wholeQueryCats (S (SuccinctClassic.cartesianShape xs))
                  (SuccinctClassic.cartesianShape xs) left right)
                  Category.registerWrite +
                catCount (wholeQueryCats (S (SuccinctClassic.cartesianShape xs))
                  (SuccinctClassic.cartesianShape xs) left right)
                  Category.arithmetic +
                catCount (wholeQueryCats (S (SuccinctClassic.cartesianShape xs))
                  (SuccinctClassic.cartesianShape xs) left right)
                  Category.comparison +
                catCount (wholeQueryCats (S (SuccinctClassic.cartesianShape xs))
                  (SuccinctClassic.cartesianShape xs) left right)
                  Category.branch +
                catCount (wholeQueryCats (S (SuccinctClassic.cartesianShape xs))
                  (SuccinctClassic.cartesianShape xs) left right)
                  Category.control ∧
            -- the DERIVED all-size literal total, an INEQUALITY
            (wholeQueryCats (S (SuccinctClassic.cartesianShape xs))
                (SuccinctClassic.cartesianShape xs) left right).length ≤
              literalTotal)

/--
**THE SUPERSEDED SPELLING**, kept so the refutation below has a subject.

Identical to the target above except that the VALID-PATH conjunct quantifies
over `∀ (store : ReadStore)` and the two binders are not shape-indexed.  This
is the form the 2026-07-19 audit found; it is FALSE, and
`uniformStore_amendedTarget_refuted` proves so.

It is recorded rather than deleted for the reason the tree records
`E1R3FamiliarMachineTarget`: a superseded claim that is merely removed leaves
no way to check what was superseded.
-/
def E1AmendedFamiliarMachineTargetUniformStore : Prop :=
  ∃ (validPath : List Instr) (S : WholeQueryStageCats) (literalTotal : Nat),
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
            catCount (wholeQueryCats S (SuccinctClassic.cartesianShape xs)
                left right) Category.memoryRead =
              (SuccinctClassic.queryCosted xs left right).cost ∧
            (wholeQueryCats S (SuccinctClassic.cartesianShape xs)
                left right).length ≤ literalTotal)

/--
**THE SUPERSEDED SPELLING IS FALSE, as a checked theorem.**

Not "unproved", and not "avoided": no `validPath`, no `S` and no
`literalTotal` can satisfy it.  The witness range is `[0, 0]` with
`0 < 2 ≤ 2`, on which the machine charges at least one read, so the receipt
the conjunct pins is nonempty and `no_uniform_store_run` applies.

This is what licenses `E1AmendedFamiliarMachineTarget` to differ from it.  A
Prop whose universal-store clause is false cannot be proved, and proving a
different Prop instead is only honest if the difference is stated and the old
form's failure is exhibited rather than asserted.
-/
theorem uniformStore_amendedTarget_refuted :
    ¬ E1AmendedFamiliarMachineTargetUniformStore := by
  rintro ⟨validPath, S, literalTotal, -, hvalidPath⟩
  have hvalid : ValidRange [(0 : Int), 0] 0 2 := ⟨by omega, by simp⟩
  have hall : ∀ store : ReadStore, ∃ s' : State,
      RunsTo store
        (programSkeleton ([(0 : Int), 0] : List Int).length validPath)
        (initialState 0 2) s'
        (SuccinctClassic.queryTraceResult [(0 : Int), 0] 0 2).trace
        (wholeQueryCats S
          (SuccinctClassic.cartesianShape [(0 : Int), 0]) 0 2) := by
    intro store
    obtain ⟨final, hrun, _⟩ := hvalidPath store [(0 : Int), 0] 0 2 hvalid
    exact ⟨final, hrun⟩
  exact no_uniform_store_run
    (queryTraceResult_trace_ne_nil [(0 : Int), 0] hvalid) hall

/--
THE INVALID CONJUNCT, DISCHARGED.

Conjunct (1) of the target holds for EVERY `validPath` AND EVERY store, with
no hypothesis on the valid branch at all -- the guard rejects before reaching
it.  So that conjunct is known SATISFIABLE at the intended instantiation, not
merely written down.

The `∀ store` here is exactly the quantifier the VALID-PATH conjunct had to
give up (`uniformStore_amendedTarget_refuted`), and it survives here for a
stated reason: this run's receipt is `[]`, so there is no event whose value a
store could disagree about.

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
    (validPath : Cartesian.CartesianShape → List Instr)
    (S : Cartesian.CartesianShape → WholeQueryStageCats)
    (literalTotal : Nat)
    (hagree : ∀ (xs : List Int) (left right : Nat),
      ValidRange xs left right →
        WholeQueryMachineAgrees
          (concreteBPNativeSuccinctRMQGlobalReadStore
            (SuccinctClassic.cartesianShape xs))
          xs.length (validPath (SuccinctClassic.cartesianShape xs))
          (S (SuccinctClassic.cartesianShape xs))
          (SuccinctClassic.cartesianShape xs) left right)
    (hcap : ∀ (xs : List Int) (left right : Nat),
      ValidRange xs left right →
        (wholeQueryCats (S (SuccinctClassic.cartesianShape xs))
          (SuccinctClassic.cartesianShape xs) left right).length ≤
            literalTotal) :
    E1AmendedFamiliarMachineTarget := by
  refine ⟨validPath, S, literalTotal,
    fun store xs => amendedTarget_invalidGuard
      (validPath (SuccinctClassic.cartesianShape xs)) store xs, ?_⟩
  intro xs left right hvalid
  obtain ⟨final, hrun, hhalted, hout, hcost⟩ :=
    programSkeleton_valid_matches_public
      (concreteBPNativeSuccinctRMQGlobalReadStore
        (SuccinctClassic.cartesianShape xs))
      xs (validPath (SuccinctClassic.cartesianShape xs))
      (S (SuccinctClassic.cartesianShape xs)) hvalid
      (hagree xs left right hvalid)
  exact ⟨final, hrun, hhalted, hout, hcost,
    (catCount_partition _).symm, hcap xs left right hvalid⟩

/--
**THE AMENDED TARGET, DISCHARGED.**

REQ-E1-07 asks for the Prop to be proved BY EXHIBITING THE CONSTRUCTION, and
this is that: the three existentials are filled with the landed whole-query
objects -- `wholeQueryValidPath` (`E1WholeQueryProgram.lean:518`, `5636`
instructions at `:523`), the arm-dispatching stage record
`wholeQueryMachineS` (`E1WholeQueryAgreement.lean:49`), and the derived
all-size step literal `11886` (`E1WholeQueryCostLiteral.lean:538`).

Nothing here is a stand-in: `wholeQueryMachineAgrees_of_bounds`
(`E1WholeQueryAgreement.lean:64`) is the whole-query simulation on the real
program at the real store, and `11886` is summed by `omega` from the cost
algebra rather than transcribed.

This is also `amendedTarget_of_wholeQueryAgreement`'s CONSUMER, which the
audit found it lacked.
-/
theorem amendedFamiliarMachineTarget_holds :
    E1AmendedFamiliarMachineTarget := by
  refine amendedTarget_of_wholeQueryAgreement
    (fun shape => wholeQueryValidPath shape wholeQueryNoneExit)
    wholeQueryMachineS 11886 (fun xs left right hvalid => ?_)
    (fun xs left right _ =>
      E1WholeQueryCostLiteral.wholeQueryCats_machineS_length_le _ _ _)
  have hsize : (SuccinctClassic.cartesianShape xs).size = xs.length :=
    Cartesian.shape_size xs
  exact wholeQueryMachineAgrees_of_bounds (SuccinctClassic.cartesianShape xs)
    hvalid.1 hvalid.2 (by rw [hsize]; exact hvalid.2)

end E1Amended
end WordRAM
end RMQ
