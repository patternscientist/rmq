import RMQ.Core.WordRAM.E1WholeQuerySameBlockRoute

/-!
# THE `.full` VALUE DISAGREEMENT IS VACUOUS

**THE DISAGREEMENT.**  `decodePacket` (`E1QueryProgram.lean:93`) is
`if v = 0 then none else some (v - 1)`, while the route's `.full` value
(`E1RouteDecomposition.lean:330`) is `some (rank.value - 1)`
UNCONDITIONALLY.  Since `0 - 1 = 0` in `Nat`, the two disagree at exactly
one point: `rank.value = 0`, where the machine says `none` and the route
says `some 0`.  `E1_LIVE_STATE.md` §10f reported this as an obstruction and
declined to assume it away.

**THIS MODULE DISCHARGES IT BY PROOF, AND NEITHER SIDE IS WEAKENED.**
`decodePacket` keeps its guard, the route keeps its unconditional `- 1`, and
no hypothesis `rank.value ≠ 0` is carried anywhere.  What is proved instead
is that the rank leg's value is `scanWindow … + 1` at every position the
`.full` branch can actually be taken -- so the disagreement point is never
reached and the agreement is unconditional on the branch.

**READ THE SITUATION CORRECTLY.**  The answer index is `rank(answerClose+1) - 1`;
for that to denote anything the rank must be at least `1`.  The route's `- 1`
silently presupposes it; `decodePacket` encodes the same presupposition as
`none`.  Where the route is meaningful the two agree, and this module says
where that is.

**THE READ-FAILURE FALLBACK IS RULED OUT, NOT ASSUMED AWAY.**
`bpChunkedRankTraceResultWithStore` (`ChargedRankSelectLeafTrace.lean:181`)
falls through to `WordRAM.TraceResult.pure 0` when any of its three sample
reads misses, so a SECOND route to `0` genuinely exists.  It is closed by
`…_refines_interpretedCosted` (`SuccinctFinalRAM.lean:1516`), which is
UNCONDITIONAL and base-generic: the store is definitionally
`concreteBPNativeChunkedRankCloseSeedReadStore shape rankSegmentBase`, so the
four agreement side conditions are discharged by construction and the reads
cannot miss.  `rankCloseTrace_value_eq_rankPrefix` below is that fact stated
once, as a reusable lemma, for the first time.

**THE SEMANTIC LINK THAT WAS MISSING.**  `wholeQueryBranch`'s `answerClose`
is a pattern binder on a trace result (`E1RouteDecomposition.lean:236`); the
whole `RMQ/Core/WordRAM/` layer never mentions `bpCloseOfInorder?`.  The link
is supplied here in the CONSTRUCTIVE direction -- rather than inverting the
branch, `wholeQueryBranch_eq_full_of_bounds` PROVES the branch is `.full`
with closes that are `bpCloseOfInorder?` values by construction.  That is
strictly stronger than an inversion lemma and doubles as the reachability
witness for the `.full` branch, which nothing in the tree previously had.
-/

namespace RMQ
namespace SuccinctFinal

open RMQ.SuccinctSpace

/-! ## The rank leg's value is a `rankPrefix`, unconditionally -/

/--
THE MISSING NAMED LEMMA: the chunked rank-close leg's TRACE value is exactly
the `rankPrefix` it is supposed to compute, at EVERY segment base and EVERY
position, with NO hypotheses.

This composition was assembled ad hoc inside two larger proofs
(`BPNavigationRAM.lean:1969` and `SuccinctFinalRAM.lean:9186`) and never
stated reusably.  Both hops are unconditional:
`…_refines_interpretedCosted` (`SuccinctFinalRAM.lean:1516`) needs no store
agreement because the store is definitionally the seed store, and
`concreteBPNativeRankCloseInterpretedCosted_exact`
(`SuccinctFinalRAM.lean:8701`) is a plain equation.

Its force here is that it CLOSES THE READ-FAILURE FALLBACK: the `pure 0`
branch of `bpChunkedRankTraceResultWithStore` cannot be the value, because
the value is a `rankPrefix` on the nose.
-/
theorem rankCloseTrace_value_eq_rankPrefix
    (shape : Cartesian.CartesianShape) (rankSegmentBase pos : Nat) :
    (concreteBPNativeRankCloseWordTraceResultAtSegment
        shape rankSegmentBase pos).value =
      Succinct.rankPrefix false shape.bpCode pos := by
  have hrefine :=
    concreteBPNativeRankCloseWordTraceResultAtSegment_refines_interpretedCosted
      shape rankSegmentBase pos
  have hvalue := congrArg Costed.value hrefine
  have hexact := concreteBPNativeRankCloseInterpretedCosted_exact shape pos
  simpa [WordRAM.TraceResult.toCosted, Costed.erase] using
    Eq.trans hvalue hexact

/-! ## The select and LCA legs, in `bpCloseOfInorder?` vocabulary -/

/-- The select-close leg's TRACE value is `bpCloseOfInorder?`, unconditionally. -/
theorem selectCloseTrace_value_eq_bpCloseOfInorder
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    (concreteBPNativeSelectCloseGlobalWordTraceResult shape idx).value =
      bpCloseOfInorder? shape idx := by
  have hrefine :=
    concreteBPNativeSelectCloseGlobalWordTraceResult_refines_interpretedCosted
      shape idx
  have hvalue := congrArg Costed.value hrefine
  have hexact := concreteBPNativeSelectCloseInterpretedCosted_exact shape idx
  simpa [WordRAM.TraceResult.toCosted, Costed.erase] using
    Eq.trans hvalue hexact

/--
The LCA leg's TRACE value is the query's answer close, given the query
triple in `bpCloseOfInorder?` vocabulary.

This is the trace-level form of the `have hlca` that
`SuccinctFinalRAM.lean:9175` builds and discards inside
`concreteBPNativeSuccinctRMQCanonicalQueryInterpretedCosted_exact`.  The
rank-seed hypothesis `canonicalLcaCloseCostedWithRankSeed_exact_of_query`
(`ChargedFringeWiring.lean:190`) demands is discharged by
`concreteBPNativeRankCloseInterpretedCosted_exact`, so it does not surface.
-/
theorem lcaCloseTrace_value_eq_some_of_query
    {shape : Cartesian.CartesianShape} {left len leftClose rightClose answerClose : Nat}
    (hlen : 0 < len)
    (hbound : left + len <= shape.size)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright : bpCloseOfInorder? shape (left + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder? shape (scanWindow shape.representative left len) =
        some answerClose) :
    (concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
        shape leftClose rightClose).value = some answerClose := by
  have hrankExact :
      forall pos,
        (concreteBPNativeRankCloseInterpretedCosted shape pos).erase =
          Succinct.rankPrefix false shape.bpCode pos := by
    intro pos
    exact concreteBPNativeRankCloseInterpretedCosted_exact shape pos
  have hcosted :=
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.canonicalLcaCloseCostedWithRankSeed_exact_of_query
      (concreteBPNativeRankCloseInterpretedCosted shape)
      hrankExact hlen hbound hleft hright hanswer
  have hrefine :=
    concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural_refines_interpretedCosted
      shape leftClose rightClose
  have hvalue := congrArg Costed.value hrefine
  simpa [WordRAM.TraceResult.toCosted,
    concreteBPNativeLCACloseCanonicalInterpretedCosted, Costed.erase] using
    Eq.trans hvalue hcosted

/-! ## The `.full` branch is REACHED, with semantically identified closes -/

/--
THE `.full` BRANCH IS REACHED ON EVERY NONEMPTY IN-RANGE QUERY, AND ITS
THREE CLOSES ARE `bpCloseOfInorder?` VALUES.

Constructive rather than inverting: this does not assume
`wholeQueryBranch … = .full …` and take it apart, it PROVES the equation.
So it is simultaneously the semantic identification of `answerClose` and the
satisfiability witness that the `.full` branch is not vacuous -- neither of
which the tree previously had at this layer.
-/
theorem wholeQueryBranch_eq_full_of_bounds
    {shape : Cartesian.CartesianShape} {left right leftClose rightClose answerClose : Nat}
    (hlt : left < right)
    (hbound : right <= shape.size)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright : bpCloseOfInorder? shape (right - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder? shape
          (scanWindow shape.representative left (right - left)) =
        some answerClose) :
    wholeQueryBranch shape left right =
      WholeQueryBranch.full leftClose rightClose answerClose := by
  have hlen : 0 < right - left := by omega
  have hboundLen : left + (right - left) <= shape.size := by omega
  have hrightIdx : left + (right - left) - 1 = right - 1 := by omega
  have hright' :
      bpCloseOfInorder? shape (left + (right - left) - 1) = some rightClose := by
    rw [hrightIdx]; exact hright
  refine wholeQueryBranch_eq_full shape left right ?_ ?_ ?_
  · rw [selectCloseTrace_value_eq_bpCloseOfInorder]; exact hleft
  · rw [selectCloseTrace_value_eq_bpCloseOfInorder]; exact hright
  · exact lcaCloseTrace_value_eq_some_of_query hlen hboundLen hleft hright' hanswer

/-! ## The rank value is positive, so the disagreement is vacuous -/

/--
THE RANK LEG'S VALUE AT THE ANSWER POSITION IS `scanWindow … + 1`.

`bpCloseOfInorder?_rankFalse_succ` (`BPShape.lean:156`) is the whole content:
a close position's `rankPrefix` at `pos + 1` counts itself, so it is a
successor and cannot be `0`.
-/
theorem rankCloseTrace_answer_value_eq_succ
    {shape : Cartesian.CartesianShape} {left len answerClose : Nat}
    (rankSegmentBase : Nat)
    (hanswer :
      bpCloseOfInorder? shape (scanWindow shape.representative left len) =
        some answerClose) :
    (concreteBPNativeRankCloseWordTraceResultAtSegment
        shape rankSegmentBase (answerClose + 1)).value =
      scanWindow shape.representative left len + 1 := by
  rw [rankCloseTrace_value_eq_rankPrefix]
  exact bpCloseOfInorder?_rankFalse_succ shape hanswer

/--
**THE VACUITY WITNESS.**  On every nonempty in-range query the route takes
the `.full` branch, the rank leg's value there is a SUCCESSOR, and therefore
`decodePacket` agrees with the route's value on the nose.

The `1 <= …` conjunct is stated explicitly rather than left implicit in the
rewrite: it is the exact proposition §10f named as undischarged, and it is
what makes the disagreement point unreachable rather than merely unreached.

Note what is NOT here: no hypothesis `rank.value ≠ 0`, no weakening of
`decodePacket`, no weakening of `wholeQueryBranchValue`.  The `.full` closes
are existentially bound because they are DERIVED from the shape, not chosen.
-/
theorem decodePacket_rankClose_eq_wholeQueryRouteValue_of_bounds
    {shape : Cartesian.CartesianShape} {left right : Nat}
    (hlt : left < right)
    (hbound : right <= shape.size) :
    exists leftClose rightClose answerClose,
      wholeQueryBranch shape left right =
          WholeQueryBranch.full leftClose rightClose answerClose /\
        1 <=
          (concreteBPNativeRankCloseWordTraceResultAtSegment shape
            concreteBPNativeRankCloseTraceSegmentBase (answerClose + 1)).value /\
        WordRAM.E1Query.decodePacket
            ((concreteBPNativeRankCloseWordTraceResultAtSegment shape
              concreteBPNativeRankCloseTraceSegmentBase
              (answerClose + 1)).value) =
          wholeQueryRouteValue shape left right := by
  have hleftLt : left < shape.size := by omega
  have hrightLt : right - 1 < shape.size := by omega
  have hscanBounds :=
    Cartesian.scanWindow_bounds shape.representative left (right - left)
      (by omega : 0 < right - left)
  have hscanLt : scanWindow shape.representative left (right - left) < shape.size := by
    omega
  obtain ⟨leftClose, hleftClose⟩ := bpCloseOfInorder?_some_of_lt shape hleftLt
  obtain ⟨rightClose, hrightClose⟩ := bpCloseOfInorder?_some_of_lt shape hrightLt
  obtain ⟨answerClose, hanswerClose⟩ := bpCloseOfInorder?_some_of_lt shape hscanLt
  have hbranch :=
    wholeQueryBranch_eq_full_of_bounds hlt hbound hleftClose hrightClose hanswerClose
  have hrank :=
    rankCloseTrace_answer_value_eq_succ (shape := shape)
      concreteBPNativeRankCloseTraceSegmentBase hanswerClose
  refine ⟨leftClose, rightClose, answerClose, hbranch, ?_, ?_⟩
  · rw [hrank]; omega
  · rw [wholeQueryRouteValue, hbranch, wholeQueryBranchValue, hrank]
    simp [WordRAM.E1Query.decodePacket]

end SuccinctFinal
end RMQ
