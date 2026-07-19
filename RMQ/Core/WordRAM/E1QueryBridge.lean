import RMQ.Core.WordRAM.E1QueryProgram
import RMQ.Core.SuccinctRMQClassic

/-!
# E1 amended machine: public invalid-guard parity (REQ-E1-05)

Bridge between the machine-level charged guard of
`RMQ.Core.WordRAM.E1QueryProgram` and the accepted public invalid
semantics `SuccinctClassic.queryCosted_invalid`: for every invalid query
range (empty, reversed, or out of bounds) the machine program skeleton runs
to the halted `none` packet whose decoded value equals the public guarded
query value, whose receipt log is POSITIONALLY the accepted (empty) invalid
trace, and whose memory-read category count equals the accepted (zero)
invalid cost.

The machine computes the rejection with charged comparisons and branches on
its input registers; the accepted route rejects at the Lean-level
`withValidRange` boundary before its controller runs.  The parity statement
below is therefore exactly the REQ-E1-05 shape: same value packet, same
(empty) read projection, same zero memory-read cost - while the machine
additionally charges its bounded guard bookkeeping (at most ten steps in
the frozen non-read categories), which the amended charge policy demands.
-/

namespace RMQ
namespace WordRAM
namespace E1Query

open E1Machine

/--
REQ-E1-05 public parity: on every invalid range for the input list `xs`
(with the machine size constant `n = xs.length` and ANY valid-path block),
the machine skeleton runs - with exact fuel, and charging EXACTLY the
category log `guardRejectCats left right` - to a halted state such that

* the decoded output packet equals the accepted guarded query value
  (`none`),
* the machine receipt log (empty) is positionally the accepted invalid
  trace,
* the machine memory-read category count equals the accepted invalid cost
  (`0`), and
* the whole rejection charges at most ten bookkeeping steps.

The category log is NAMED here rather than existentially quantified.  This
is the only category statement the E1 machine puts on the public surface, so
whatever it can distinguish is the whole of what the public boundary can
distinguish about charge.  Quantified away and reduced to a read count plus
a length bound, it could not distinguish the guard's real log from one with
a slot changed from `.comparison` to `.branch` - both aggregates are exactly
preserved by such a change.  The aggregates are still asserted, as the last
two clauses; they are now consequences carried alongside the exact log
rather than a replacement for it.
-/
theorem programSkeleton_invalid_matches_public_guard
    (store : ReadStore) (xs : List Int) (validPath : List Instr)
    {left right : Nat} (hbad : ¬ ValidRange xs left right) :
    ∃ final : State,
      RunsTo store (programSkeleton xs.length validPath)
          (initialState left right) final []
          (guardRejectCats left right) ∧
        final.halted = true ∧
        decodePacket (final.regs regOut) =
          (SuccinctClassic.queryCosted xs left right).value ∧
        ([] : List TraceEvent) =
          (SuccinctClassic.queryTraceResult xs left right).trace ∧
        catCount (guardRejectCats left right) .memoryRead =
          (SuccinctClassic.queryCosted xs left right).cost ∧
        (guardRejectCats left right).length ≤ 10 := by
  have hbad' : ¬ (left < right ∧ right ≤ xs.length) := hbad
  obtain ⟨final, hrun, hhalted, hout⟩ :=
    programSkeleton_reject_of_invalid store xs.length validPath hbad'
  refine ⟨final, hrun, hhalted, ?_, ?_, ?_,
    guardRejectCats_length_le left right⟩
  · rw [hout, SuccinctClassic.queryCosted_invalid xs left right hbad]
    rfl
  · rw [SuccinctClassic.queryTraceResult_invalid xs left right hbad]
    rfl
  · rw [SuccinctClassic.queryCosted_invalid xs left right hbad]
    exact guardRejectCats_memoryRead left right

/-! ### The three named specializations

Each of these previously dropped clauses the general theorem had already
established - the trace clause in all three, and the cost clause and
bookkeeping bound in two of them - which left the named boundary cases
weaker than the general statement they were derived from.  They now carry
the full clause set.

Two of the three can say more than the general theorem rather than less: an
empty range and a reversed range both fail `left < right`, so the exact log
is known to be `guardRejectRangeCats` and is named as such.  The
out-of-bounds case genuinely cannot be sharpened this way - `xs.length <
right` does not decide `left < right` - so it keeps the branch-indexed form,
which is the honest statement there.
-/

/-- Empty-range specialization (`[left, left)` is always rejected).  The
exact log is known: an empty range fails the `left < right` test, so the
FIRST branch fires and the bounds test never runs. -/
theorem programSkeleton_empty_range_matches_public_guard
    (store : ReadStore) (xs : List Int) (validPath : List Instr)
    (left : Nat) :
    ∃ final : State,
      RunsTo store (programSkeleton xs.length validPath)
          (initialState left left) final [] guardRejectRangeCats ∧
        final.halted = true ∧
        decodePacket (final.regs regOut) =
          (SuccinctClassic.queryCosted xs left left).value ∧
        ([] : List TraceEvent) =
          (SuccinctClassic.queryTraceResult xs left left).trace ∧
        catCount guardRejectRangeCats .memoryRead =
          (SuccinctClassic.queryCosted xs left left).cost ∧
        guardRejectRangeCats.length ≤ 10 := by
  have hnot : ¬ left < left := Nat.lt_irrefl left
  obtain ⟨final, hrun, hhalted, hvalue, htrace, hcost, hlen⟩ :=
    programSkeleton_invalid_matches_public_guard store xs validPath
      (left := left) (right := left)
      (by intro h; exact Nat.lt_irrefl left h.1)
  rw [guardRejectCats_of_not_lt hnot] at hrun hcost hlen
  exact ⟨final, hrun, hhalted, hvalue, htrace, hcost, hlen⟩

/-- Reversed-range specialization (`right ≤ left` is always rejected).  As
with the empty range, the `left < right` test fails, so the exact log is
`guardRejectRangeCats`. -/
theorem programSkeleton_reversed_range_matches_public_guard
    (store : ReadStore) (xs : List Int) (validPath : List Instr)
    {left right : Nat} (hreverse : right ≤ left) :
    ∃ final : State,
      RunsTo store (programSkeleton xs.length validPath)
          (initialState left right) final [] guardRejectRangeCats ∧
        final.halted = true ∧
        decodePacket (final.regs regOut) =
          (SuccinctClassic.queryCosted xs left right).value ∧
        ([] : List TraceEvent) =
          (SuccinctClassic.queryTraceResult xs left right).trace ∧
        catCount guardRejectRangeCats .memoryRead =
          (SuccinctClassic.queryCosted xs left right).cost ∧
        guardRejectRangeCats.length ≤ 10 := by
  have hnot : ¬ left < right := by omega
  obtain ⟨final, hrun, hhalted, hvalue, htrace, hcost, hlen⟩ :=
    programSkeleton_invalid_matches_public_guard store xs validPath
      (left := left) (right := right)
      (by intro h; omega)
  rw [guardRejectCats_of_not_lt hnot] at hrun hcost hlen
  exact ⟨final, hrun, hhalted, hvalue, htrace, hcost, hlen⟩

/-- Out-of-bounds specialization (`xs.length < right` is always rejected).
The exact log stays branch-indexed: `xs.length < right` does not decide
`left < right`, so BOTH rejection logs are reachable here, and naming either
one would be false. -/
theorem programSkeleton_out_of_bounds_matches_public_guard
    (store : ReadStore) (xs : List Int) (validPath : List Instr)
    {left right : Nat} (hout : xs.length < right) :
    ∃ final : State,
      RunsTo store (programSkeleton xs.length validPath)
          (initialState left right) final []
          (guardRejectCats left right) ∧
        final.halted = true ∧
        decodePacket (final.regs regOut) =
          (SuccinctClassic.queryCosted xs left right).value ∧
        ([] : List TraceEvent) =
          (SuccinctClassic.queryTraceResult xs left right).trace ∧
        catCount (guardRejectCats left right) .memoryRead =
          (SuccinctClassic.queryCosted xs left right).cost ∧
        (guardRejectCats left right).length ≤ 10 :=
  programSkeleton_invalid_matches_public_guard store xs validPath
    (left := left) (right := right) (by intro h; omega)

/-- Both rejection logs really are reachable under the out-of-bounds
hypothesis, so the branch-indexed form above is necessary rather than
merely cautious: `[0, 9)` on a size-5 input takes the bounds branch, and
`[9, 9)` on the same input is out of bounds too yet takes the range
branch. -/
theorem out_of_bounds_reaches_both_reject_logs :
    guardRejectCats 0 9 = guardRejectBoundsCats ∧
      guardRejectCats 9 9 = guardRejectRangeCats := by
  refine ⟨by decide, by decide⟩

end E1Query
end WordRAM
end RMQ
