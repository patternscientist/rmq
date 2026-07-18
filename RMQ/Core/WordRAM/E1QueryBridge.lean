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
the machine skeleton runs - with exact fuel - to a halted state such that

* the decoded output packet equals the accepted guarded query value
  (`none`),
* the machine receipt log (empty) is positionally the accepted invalid
  trace,
* the machine memory-read category count equals the accepted invalid cost
  (`0`), and
* the whole rejection charges at most ten bookkeeping steps.
-/
theorem programSkeleton_invalid_matches_public_guard
    (store : ReadStore) (xs : List Int) (validPath : List Instr)
    {left right : Nat} (hbad : ¬ ValidRange xs left right) :
    ∃ (final : State) (cats : List Category),
      RunsTo store (programSkeleton xs.length validPath)
          (initialState left right) final [] cats ∧
        final.halted = true ∧
        decodePacket (final.regs regOut) =
          (SuccinctClassic.queryCosted xs left right).value ∧
        ([] : List TraceEvent) =
          (SuccinctClassic.queryTraceResult xs left right).trace ∧
        catCount cats .memoryRead =
          (SuccinctClassic.queryCosted xs left right).cost ∧
        cats.length ≤ 10 := by
  have hbad' : ¬ (left < right ∧ right ≤ xs.length) := hbad
  obtain ⟨final, cats, hrun, hhalted, hout, hreads, hlen⟩ :=
    programSkeleton_reject_of_invalid store xs.length validPath hbad'
  refine ⟨final, cats, hrun, hhalted, ?_, ?_, ?_, hlen⟩
  · rw [hout, SuccinctClassic.queryCosted_invalid xs left right hbad]
    rfl
  · rw [SuccinctClassic.queryTraceResult_invalid xs left right hbad]
    rfl
  · rw [SuccinctClassic.queryCosted_invalid xs left right hbad]
    exact hreads

/-- Empty-range specialization (`[left, left)` is always rejected). -/
theorem programSkeleton_empty_range_matches_public_guard
    (store : ReadStore) (xs : List Int) (validPath : List Instr)
    (left : Nat) :
    ∃ (final : State) (cats : List Category),
      RunsTo store (programSkeleton xs.length validPath)
          (initialState left left) final [] cats ∧
        final.halted = true ∧
        decodePacket (final.regs regOut) =
          (SuccinctClassic.queryCosted xs left left).value ∧
        catCount cats .memoryRead = 0 := by
  obtain ⟨final, cats, hrun, hhalted, hvalue, _, hcost, _⟩ :=
    programSkeleton_invalid_matches_public_guard store xs validPath
      (left := left) (right := left)
      (by intro h; exact Nat.lt_irrefl left h.1)
  refine ⟨final, cats, hrun, hhalted, hvalue, ?_⟩
  rw [hcost, SuccinctClassic.queryCosted_invalid xs left left
    (by intro h; exact Nat.lt_irrefl left h.1)]
  rfl

/-- Reversed-range specialization (`right ≤ left` is always rejected). -/
theorem programSkeleton_reversed_range_matches_public_guard
    (store : ReadStore) (xs : List Int) (validPath : List Instr)
    {left right : Nat} (hreverse : right ≤ left) :
    ∃ (final : State) (cats : List Category),
      RunsTo store (programSkeleton xs.length validPath)
          (initialState left right) final [] cats ∧
        final.halted = true ∧
        decodePacket (final.regs regOut) =
          (SuccinctClassic.queryCosted xs left right).value := by
  obtain ⟨final, cats, hrun, hhalted, hvalue, _, _, _⟩ :=
    programSkeleton_invalid_matches_public_guard store xs validPath
      (left := left) (right := right)
      (by intro h; omega)
  exact ⟨final, cats, hrun, hhalted, hvalue⟩

/-- Out-of-bounds specialization (`xs.length < right` is always rejected). -/
theorem programSkeleton_out_of_bounds_matches_public_guard
    (store : ReadStore) (xs : List Int) (validPath : List Instr)
    {left right : Nat} (hout : xs.length < right) :
    ∃ (final : State) (cats : List Category),
      RunsTo store (programSkeleton xs.length validPath)
          (initialState left right) final [] cats ∧
        final.halted = true ∧
        decodePacket (final.regs regOut) =
          (SuccinctClassic.queryCosted xs left right).value := by
  obtain ⟨final, cats, hrun, hhalted, hvalue, _, _, _⟩ :=
    programSkeleton_invalid_matches_public_guard store xs validPath
      (left := left) (right := right)
      (by intro h; omega)
  exact ⟨final, cats, hrun, hhalted, hvalue⟩

end E1Query
end WordRAM
end RMQ
