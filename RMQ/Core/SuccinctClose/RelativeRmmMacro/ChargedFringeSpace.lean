import RMQ.Core.SuccinctRMQClassic
import RMQ.Core.SuccinctClose.RelativeRmmMacro.ChargedFringeChunks
import RMQ.Core.SuccinctClose.RelativeRmmMacro.ChargedFringeTableFacts

/-!
# Charged fringe chunk-table space accounting (o(n) composition)

`SuccinctRMQClassic`-facing space accounting for the charged fringe chunk
table: the reviewer word-width restatement and the committed candidate
`buildPayload`/`overhead` amendment pair.

The pure table facts (payload length identity, physical erasure, row-count
linear bound, entry-width bounds, and the `LittleOLinear` budget) live in
`ChargedFringeTableFacts.lean`, below the reviewer physical store, so the
reviewer-source extension can consume them without an import cycle.
-/

namespace RMQ

namespace SuccinctClose

open SuccinctSpace

/--
The packed table word fits the declared reviewer machine word at every
input size.
-/
theorem bpFringeChunkEntryWidth_le_reviewerWordBits (n : Nat) :
    bpFringeChunkEntryWidth (bpFringeChunkBits (2 * n)) <=
      SuccinctFinal.concreteBPNativeSuccinctRMQReviewerWordBits n := by
  simpa [SuccinctFinal.concreteBPNativeSuccinctRMQReviewerWordBits,
    SuccinctFinal.concreteBPNativeSuccinctRMQReviewerCapacity] using
    bpFringeChunkEntryWidth_le_machineWordBits_capacity n

/-! ## Committed candidate amendment (consumed by the wiring rung) -/

/-- Candidate amended overhead: accepted overhead plus the table budget. -/
def bpChunkedOverheadCandidate (n : Nat) : Nat :=
  SuccinctClassic.overhead n + bpFringeTableOverhead n

/-- Candidate amended payload: accepted payload plus the counted table. -/
def bpChunkedBuildPayloadCandidate (xs : List Int) : List Bool :=
  SuccinctClassic.buildPayload xs ++
    (bpFringeChunkTable
      (bpFringeChunkBits
        (SuccinctClassic.cartesianShape xs).bpCode.length)).payload

/-- The amended overhead stays `o(n)`. -/
theorem bpChunkedOverheadCandidate_littleO :
    SuccinctSpace.LittleOLinear bpChunkedOverheadCandidate :=
  SuccinctClassic.overhead_littleO.add bpFringeTableOverhead_littleO

/-- The amended payload keeps the public `2n + o(n)` statement shape. -/
theorem bpChunkedBuildPayloadCandidate_length (xs : List Int) :
    (bpChunkedBuildPayloadCandidate xs).length <=
      2 * xs.length + bpChunkedOverheadCandidate xs.length := by
  have hbase := SuccinctClassic.buildPayload_length xs
  have hshape :
      (SuccinctClassic.cartesianShape xs).bpCode.length =
        2 * xs.length := by
    rw [Cartesian.CartesianShape.bpCode_length]
    rw [show (SuccinctClassic.cartesianShape xs).size = xs.length from
      Cartesian.shape_size xs]
  have htable :
      (bpFringeChunkTable
        (bpFringeChunkBits
          (SuccinctClassic.cartesianShape xs).bpCode.length)).payload.length =
        bpFringeTableOverhead xs.length := by
    rw [hshape]
    exact bpFringeChunkTable_payload_length _
  unfold bpChunkedBuildPayloadCandidate bpChunkedOverheadCandidate
  rw [List.length_append]
  omega

end SuccinctClose

end RMQ
