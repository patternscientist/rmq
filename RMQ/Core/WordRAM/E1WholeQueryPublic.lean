import RMQ.Core.WordRAM.E1WholeQueryCats
import RMQ.Core.WordRAM.E1QueryBridge

/-!
# E1 amended machine: the public `List Int` plumbing for the whole query

The whole-query glue will be proved at the SHAPE level - the route
decompositions speak about `shape : Cartesian.CartesianShape`, while the
machine and the guard speak about `xs : List Int`.  This module crosses that
gap once, so the crossing is debugged before the theorem it consumes exists.

Two halves, deliberately separated:

* the ROUTE half is unconditional and proved here in full.  On a valid range
  the public object IS the shape-level route object
  (`SuccinctClassic.queryTraceResult_valid`), so the public trace, value and
  cost are exactly the route's - no machine, no hypothesis beyond validity;
* the MACHINE half is stated against a NAMED hypothesis
  (`WholeQueryMachineAgrees`) rather than proved.  That hypothesis is what
  the whole-query glue will discharge.  Stating the corollary now means the
  plumbing is checked, and the shape of the obligation is fixed, before the
  glue lands.

Nothing here asserts the machine half.  `WholeQueryMachineAgrees` is a
`def … : Prop`, not an assumed principle and not a hypothesis in scope: every theorem
below that uses it takes it as an explicit premise.
-/

namespace RMQ
namespace WordRAM
namespace E1Query

open E1Machine
open RMQ.SuccinctFinal

/-! ## Read accounting for `RunsTo`

`run_readLog_length_eq_memoryRead_count` (`E1Machine.lean:356`) already
proves that the receipt length is exactly the `memoryRead` category count.
The `RunsTo` form is what the composition layer actually uses, so it is
derived here.

Kept in this module rather than pushed into `E1MachineCalculus.lean`, which
is shared with two live sibling lanes.  It is a candidate for promotion into
the calculus once the lanes converge.
-/

/-- Receipt length is exactly the `memoryRead` category count, in relational
form.  This is what ties the route's COST (a trace length) to the machine's
CHARGE (a category count) without either side having to be recomputed. -/
theorem RunsTo.readLog_length_eq_memoryRead_count
    {store : ReadStore} {program : E1Machine.Program} {s s' : State}
    {reads : List TraceEvent} {cats : List Category}
    (h : RunsTo store program s s' reads cats) :
    reads.length = catCount cats .memoryRead := by
  unfold E1Machine.RunsTo at h
  have hrun :=
    run_readLog_length_eq_memoryRead_count store program cats.length s
  rw [h] at hrun
  exact hrun

/-! ## The route half: unconditional on a valid range -/

/-- On a valid range the public trace and value are exactly the route's,
positionally.  This is the single rewrite that lands the whole-query
decomposition on the public surface. -/
theorem queryTraceResult_valid_decompose
    (xs : List Int) {left right : Nat} (hvalid : ValidRange xs left right) :
    (SuccinctClassic.queryTraceResult xs left right).trace =
        wholeQueryRouteTrace (SuccinctClassic.cartesianShape xs) left right ∧
      (SuccinctClassic.queryTraceResult xs left right).value =
        wholeQueryRouteValue (SuccinctClassic.cartesianShape xs) left right := by
  rw [SuccinctClassic.queryTraceResult_valid xs left right hvalid]
  exact
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_decompose
      (SuccinctClassic.cartesianShape xs) left right

/-- The public value on a valid range, in route vocabulary. -/
theorem queryCosted_valid_value
    (xs : List Int) {left right : Nat} (hvalid : ValidRange xs left right) :
    (SuccinctClassic.queryCosted xs left right).value =
      wholeQueryRouteValue (SuccinctClassic.cartesianShape xs) left right :=
  (queryTraceResult_valid_decompose xs hvalid).2

/-- The public COST on a valid range is the route receipt's length.  The
public cost carrier is `trace.length` by construction (`TraceResult.toCosted`
via `steps`), so a cost claim at this boundary is a claim about the receipt,
not an independent number. -/
theorem queryCosted_valid_cost
    (xs : List Int) {left right : Nat} (hvalid : ValidRange xs left right) :
    (SuccinctClassic.queryCosted xs left right).cost =
      (wholeQueryRouteTrace (SuccinctClassic.cartesianShape xs)
        left right).length := by
  show (SuccinctClassic.queryTraceResult xs left right).trace.length = _
  rw [(queryTraceResult_valid_decompose xs hvalid).1]

/-! ## The machine half: stated against a named hypothesis -/

/--
The whole-query agreement the glue owes, named once so the public corollary
can be written and checked before it is discharged.

It says: on the query start state the skeleton runs, with exact fuel, to a
halted state whose receipt is POSITIONALLY the route's whole-query receipt,
whose charge is POSITIONALLY the route-indexed category log, and whose output
packet decodes to the route's whole-query value.

All three clauses are positional equalities on the nose.  In particular the
category clause is `wholeQueryCats`, which is a function of the route's own
branch classification - so an impostor that ran a leg the route skips
violates this hypothesis even on the branches where the value degenerates to
`none = none`.
-/
def WholeQueryMachineAgrees
    (store : ReadStore) (n : Nat) (validPath : List Instr)
    (S : WholeQueryStageCats) (shape : Cartesian.CartesianShape)
    (left right : Nat) : Prop :=
  ∃ final : State,
    RunsTo store (programSkeleton n validPath) (initialState left right)
        final
        (wholeQueryRouteTrace shape left right)
        (wholeQueryCats S shape left right) ∧
      final.halted = true ∧
      decodePacket (final.regs regOut) = wholeQueryRouteValue shape left right

/--
THE PUBLIC `List Int` COROLLARY, against the hypothesised agreement.

Given the whole-query agreement at the shape level, the machine skeleton
meets the public `List Int` surface on every VALID range, in the same four
clauses the invalid boundary already meets it in: same value packet, receipt
positionally the public trace, memory-read charge equal to the public cost,
and the charge named positionally rather than quantified away.

The cost clause is where the read-accounting lemma earns its place: the
public cost is a trace LENGTH and the machine charge is a category COUNT, and
`RunsTo.readLog_length_eq_memoryRead_count` is what identifies them.  Neither
side is recomputed and no numeral is asserted.
-/
theorem programSkeleton_valid_matches_public
    (store : ReadStore) (xs : List Int) (validPath : List Instr)
    (S : WholeQueryStageCats) {left right : Nat}
    (hvalid : ValidRange xs left right)
    (hagree :
      WholeQueryMachineAgrees store xs.length validPath S
        (SuccinctClassic.cartesianShape xs) left right) :
    ∃ final : State,
      RunsTo store (programSkeleton xs.length validPath)
          (initialState left right) final
          (SuccinctClassic.queryTraceResult xs left right).trace
          (wholeQueryCats S (SuccinctClassic.cartesianShape xs)
            left right) ∧
        final.halted = true ∧
        decodePacket (final.regs regOut) =
          (SuccinctClassic.queryCosted xs left right).value ∧
        catCount
            (wholeQueryCats S (SuccinctClassic.cartesianShape xs) left right)
            .memoryRead =
          (SuccinctClassic.queryCosted xs left right).cost := by
  obtain ⟨final, hrun, hhalted, hout⟩ := hagree
  have htrace := (queryTraceResult_valid_decompose xs hvalid).1
  refine ⟨final, ?_, hhalted, ?_, ?_⟩
  · rw [htrace]
    exact hrun
  · rw [hout, queryCosted_valid_value xs hvalid]
  · rw [queryCosted_valid_cost xs hvalid]
    exact (RunsTo.readLog_length_eq_memoryRead_count hrun).symm

/-! ## The prepared-input entry crosses the same gap

`prepareInput` stores its own Cartesian shape, and
`prepareInput_shape_eq_cartesianShape` says it is the canonical one.  So the
plumbing above applies to the prepared entry with a single rewrite; recorded
here so the glue does not rediscover it.
-/

/-- The prepared builder's stored shape is the shape the decompositions
speak about, so a whole-query agreement stated at `cartesianShape xs`
transfers to it verbatim. -/
theorem preparedInput_shape_agrees
    (xs : List Int) (S : WholeQueryStageCats)
    (store : ReadStore) (validPath : List Instr) (left right : Nat) :
    WholeQueryMachineAgrees store xs.length validPath S
        (SuccinctClassic.prepareInput xs).shape left right ↔
      WholeQueryMachineAgrees store xs.length validPath S
        (SuccinctClassic.cartesianShape xs) left right := by
  rw [SuccinctClassic.prepareInput_shape_eq_cartesianShape xs]

end E1Query
end WordRAM
end RMQ
