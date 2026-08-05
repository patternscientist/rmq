import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReviewerClosedGeometry
import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReviewerLogicalProtocol

/-!
# Physical lowering of one reviewer logical request

This module is the closed routing table between the logical whole-query
protocol and the single reviewer-memory cell array.  Segments `0` and `19`
share the balanced-parenthesis payload but retain their distinct word
geometries; segments `1` through `18` use the exact consumed access sources;
and segments `20`, `21`, and `22` use the ragged interior, fringe, and select
chunk geometries respectively.

The controller stores the logical request and prior cell replies.  It does not
store a shape, a semantic store, a source list, or a precomputed bit offset:
`packedReviewerLogicalPlan` recomputes every physical address from `n`, the two
decoded counts, and the request.
-/

namespace RMQ
namespace SuccinctFinal
namespace PackedCellProbe

/-! ## The two balanced-parenthesis aliases -/

/-- The BP-backed source named by each of the two shared-payload segments. -/
def packedReviewerBPSource? : Nat ->
    Option ConcreteBPNativeSuccinctRMQFlatPayloadSource
  | 0 => some .bpCode
  | 19 => some .finalRankBPCodeAlias
  | _ => none

/-- Absolute padded-bit address of a BP-backed logical word. -/
def packedReviewerBPBitAddress
    (n : Nat) (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
    (index : Nat) : Nat :=
  packedReviewerCellWidth n + index * packedSourceStride n source

/-- One BP-backed word's exact (possibly zero) payload width. -/
def packedReviewerBPReadWidth
    (n : Nat) (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
    (index : Nat) : Nat :=
  packedSourceReadWidth n 0 source index

/-- The raw one-or-two-cell plan for a BP-backed word. -/
def packedReviewerBPRawPlan
    (n : Nat) (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
    (index : Nat) : List Nat :=
  packedReviewerProbePlan n (packedReviewerBPBitAddress n source index)
    (packedReviewerBPReadWidth n source index)

/-- One BP-backed logical word, read only from the supplied cell array. -/
def packedReviewerBPRead
    (n : Nat) (memory : List (List Bool))
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource) (index : Nat) :
    Option (List Bool) :=
  if index < packedSourceWordCount n 0 source then
    (packedFetch memory (packedReviewerBPRawPlan n source index)).map
      (packedReviewerDecodeSpan n
        (packedReviewerBPBitAddress n source index)
        (packedReviewerBPReadWidth n source index))
  else
    none

/-! ## Closed legacy-segment geometry -/

/-- The exact logical word count of one segment below `20`. -/
def packedReviewerLegacyWordCount
    (n longCount sparseCount : Nat)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource) : Nat :=
  packedReviewerSourceWordCount n longCount sparseCount source

/--
The raw plan for one in-range legacy segment.  The two BP aliases are located
at the start of the consumed payload; every other executed source is located
in the access prefix following those `2*n` bits.
-/
def packedReviewerLegacyRawPlan
    (n longCount sparseCount : Nat)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource) (index : Nat) :
    List Nat :=
  match source with
  | .bpCode => packedReviewerBPRawPlan n .bpCode index
  | .finalRankBPCodeAlias =>
      packedReviewerBPRawPlan n .finalRankBPCodeAlias index
  | _ =>
      packedReviewerClosedSourceReadPlan n longCount sparseCount source index

/-- Decode the replies of one in-range legacy logical word. -/
def packedReviewerLegacyDecode
    (n longCount sparseCount : Nat)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource) (index : Nat)
    (cells : List (List Bool)) : List Bool :=
  match source with
  | .bpCode =>
      packedReviewerDecodeSpan n
        (packedReviewerBPBitAddress n .bpCode index)
        (packedReviewerBPReadWidth n .bpCode index) cells
  | .finalRankBPCodeAlias =>
      packedReviewerDecodeSpan n
        (packedReviewerBPBitAddress n .finalRankBPCodeAlias index)
        (packedReviewerBPReadWidth n .finalRankBPCodeAlias index) cells
  | _ =>
      packedReviewerDecodeSpan n
        (packedReviewerClosedStridedBitAddress n longCount source index
          (packedSourceStride n source))
        (packedReviewerSourceReadWidth n longCount sparseCount source index)
        cells

/--
The non-BP legacy branch is definitionally the closed source plan.  Combined
with `packedReviewerClosedSourceReadPlan_eq`, this pins the exact former plan
for every live source while keeping the executable path list-free.
-/
theorem packedReviewerLegacyRawPlan_eq_closed
    (n longCount sparseCount : Nat)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource) (index : Nat)
    (hbp : source != ConcreteBPNativeSuccinctRMQFlatPayloadSource.bpCode)
    (halias :
      source !=
        ConcreteBPNativeSuccinctRMQFlatPayloadSource.finalRankBPCodeAlias) :
    packedReviewerLegacyRawPlan n longCount sparseCount source index =
      packedReviewerClosedSourceReadPlan n longCount sparseCount source index := by
  cases source <;> simp_all [packedReviewerLegacyRawPlan]

/-- Every canonical live legacy source retains its exact former probe plan. -/
theorem packedReviewerLegacyRawPlan_eq_sourceGeometry
    (n longCount sparseCount : Nat)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource) (index : Nat)
    (hsource :
      source ∈ concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources) :
    packedReviewerLegacyRawPlan n longCount sparseCount source index =
      packedReviewerSourceReadPlan n longCount sparseCount source index := by
  have hbp :
      source != ConcreteBPNativeSuccinctRMQFlatPayloadSource.bpCode := by
    by_cases h :
        source = ConcreteBPNativeSuccinctRMQFlatPayloadSource.bpCode
    · subst source
      simp [concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources] at hsource
    · simp [h]
  have halias :
      source !=
        ConcreteBPNativeSuccinctRMQFlatPayloadSource.finalRankBPCodeAlias := by
    by_cases h :
        source =
          ConcreteBPNativeSuccinctRMQFlatPayloadSource.finalRankBPCodeAlias
    · subst source
      simp [concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources] at hsource
    · simp [h]
  rw [packedReviewerLegacyRawPlan_eq_closed n longCount sparseCount source
    index hbp halias]
  exact packedReviewerClosedSourceReadPlan_eq n longCount sparseCount source
    index hsource

/-- The non-BP decoder uses exactly the closed source bit address and width. -/
theorem packedReviewerLegacyDecode_eq_closed
    (n longCount sparseCount : Nat)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource) (index : Nat)
    (cells : List (List Bool))
    (hbp : source != ConcreteBPNativeSuccinctRMQFlatPayloadSource.bpCode)
    (halias :
      source !=
        ConcreteBPNativeSuccinctRMQFlatPayloadSource.finalRankBPCodeAlias) :
    packedReviewerLegacyDecode n longCount sparseCount source index cells =
      packedReviewerDecodeSpan n
        (packedReviewerClosedStridedBitAddress n longCount source index
          (packedSourceStride n source))
        (packedReviewerSourceReadWidth n longCount sparseCount source index)
        cells := by
  cases source <;> simp_all [packedReviewerLegacyDecode]

/--
For a canonical live source, the closed decoder is exactly the former
list-derived decoder expression.
-/
theorem packedReviewerLegacyDecode_eq_sourceGeometry
    (n longCount sparseCount : Nat)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource) (index : Nat)
    (cells : List (List Bool))
    (hsource :
      source ∈ concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources) :
    packedReviewerLegacyDecode n longCount sparseCount source index cells =
      packedReviewerDecodeSpan n
        (packedReviewerStridedBitAddress n longCount source index
          (packedSourceStride n source))
        (packedReviewerSourceReadWidth n longCount sparseCount source index)
        cells := by
  have hbp :
      source != ConcreteBPNativeSuccinctRMQFlatPayloadSource.bpCode := by
    by_cases h :
        source = ConcreteBPNativeSuccinctRMQFlatPayloadSource.bpCode
    · subst source
      simp [concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources] at hsource
    · simp [h]
  have halias :
      source !=
        ConcreteBPNativeSuccinctRMQFlatPayloadSource.finalRankBPCodeAlias := by
    by_cases h :
        source =
          ConcreteBPNativeSuccinctRMQFlatPayloadSource.finalRankBPCodeAlias
    · subst source
      simp [concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources] at hsource
    · simp [h]
  rw [packedReviewerLegacyDecode_eq_closed n longCount sparseCount source index
    cells hbp halias]
  rw [packedReviewerClosedStridedBitAddress_eq n longCount source index
    (packedSourceStride n source) hsource]

/-! ## One total logical plan and decoder -/

/--
The physical cell plan of one logical request.  An absent logical word has the
empty plan and is supplied to the logical protocol as `none` without a
decorative physical read.
-/
def packedReviewerLogicalPlan
    (n longCount sparseCount : Nat)
    (request : PackedReviewerLogicalRequest) : List Nat :=
  match request.segment with
  | 20 =>
      packedReviewerClosedInteriorReadPlan n longCount sparseCount request.index
  | 21 =>
      if request.index < packedReviewerFringeCount n then
        packedReviewerProbePlan n
          (packedReviewerClosedFringeAddress n longCount sparseCount request.index)
          (packedReviewerFringeWidth n)
      else []
  | 22 =>
      if request.index < packedReviewerSelectChunkCount n then
        packedReviewerProbePlan n
          (packedReviewerClosedSelectChunkAddress n longCount sparseCount
            request.index)
          (packedReviewerSelectChunkWidth n)
      else []
  | segment =>
      if segment < 20 then
        match packedSegmentSource? segment with
        | none => []
        | some source =>
            if request.index <
                packedReviewerLegacyWordCount n longCount sparseCount source then
              packedReviewerLegacyRawPlan n longCount sparseCount source request.index
            else []
      else []

/--
Decode exactly the replies belonging to `packedReviewerLogicalPlan`.  The
option guard is the logical-store word-count guard; it is independent of the
success or failure of an external memory lookup.
-/
def packedReviewerLogicalDecode
    (n longCount sparseCount : Nat)
    (request : PackedReviewerLogicalRequest) (cells : List (List Bool)) :
    Option (List Bool) :=
  match request.segment with
  | 20 =>
      match packedReviewerInteriorClassify n request.index with
      | none => none
      | some location =>
          some (packedReviewerDecodeSpan n
            (packedReviewerClosedInteriorBitAddress n longCount sparseCount
              location)
            location.readWidth cells)
  | 21 =>
      if request.index < packedReviewerFringeCount n then
        some (packedReviewerDecodeSpan n
          (packedReviewerClosedFringeAddress n longCount sparseCount
            request.index)
          (packedReviewerFringeWidth n) cells)
      else none
  | 22 =>
      if request.index < packedReviewerSelectChunkCount n then
        some (packedReviewerDecodeSpan n
          (packedReviewerClosedSelectChunkAddress n longCount sparseCount
            request.index)
          (packedReviewerSelectChunkWidth n) cells)
      else none
  | segment =>
      if segment < 20 then
        match packedSegmentSource? segment with
        | none => none
        | some source =>
            if request.index <
                packedReviewerLegacyWordCount n longCount sparseCount source then
              some (packedReviewerLegacyDecode n longCount sparseCount source
                request.index cells)
            else none
      else none

/-! ## Drift receipts for the three ragged/close branches -/

theorem packedReviewerLogicalPlan_segment20_eq
    (n longCount sparseCount : Nat)
    (request : PackedReviewerLogicalRequest)
    (hsegment : request.segment = 20) :
    packedReviewerLogicalPlan n longCount sparseCount request =
      packedReviewerInteriorReadPlan n longCount sparseCount request.index := by
  simp [packedReviewerLogicalPlan, hsegment,
    packedReviewerClosedInteriorReadPlan_eq]

theorem packedReviewerLogicalPlan_segment21_eq
    (n longCount sparseCount : Nat)
    (request : PackedReviewerLogicalRequest)
    (hsegment : request.segment = 21) :
    packedReviewerLogicalPlan n longCount sparseCount request =
      if request.index < packedReviewerFringeCount n then
        packedReviewerProbePlan n
          (packedReviewerFringeAddress n longCount sparseCount request.index)
          (packedReviewerFringeWidth n)
      else [] := by
  simp [packedReviewerLogicalPlan, hsegment,
    packedReviewerClosedFringeAddress_eq]

theorem packedReviewerLogicalPlan_segment22_eq
    (n longCount sparseCount : Nat)
    (request : PackedReviewerLogicalRequest)
    (hsegment : request.segment = 22) :
    packedReviewerLogicalPlan n longCount sparseCount request =
      if request.index < packedReviewerSelectChunkCount n then
        packedReviewerProbePlan n
          (packedReviewerSelectChunkAddress n longCount sparseCount request.index)
          (packedReviewerSelectChunkWidth n)
      else [] := by
  simp [packedReviewerLogicalPlan, hsegment,
    packedReviewerClosedSelectChunkAddress_eq]

theorem packedReviewerLogicalDecode_segment20_eq
    (n longCount sparseCount : Nat)
    (request : PackedReviewerLogicalRequest) (cells : List (List Bool))
    (hsegment : request.segment = 20) :
    packedReviewerLogicalDecode n longCount sparseCount request cells =
      match packedReviewerInteriorClassify n request.index with
      | none => none
      | some location =>
          some (packedReviewerDecodeSpan n
            (packedReviewerInteriorBitAddress n longCount sparseCount location)
            location.readWidth cells) := by
  simp [packedReviewerLogicalDecode, hsegment,
    packedReviewerClosedInteriorBitAddress_eq]

theorem packedReviewerLogicalDecode_segment21_eq
    (n longCount sparseCount : Nat)
    (request : PackedReviewerLogicalRequest) (cells : List (List Bool))
    (hsegment : request.segment = 21) :
    packedReviewerLogicalDecode n longCount sparseCount request cells =
      if request.index < packedReviewerFringeCount n then
        some (packedReviewerDecodeSpan n
          (packedReviewerFringeAddress n longCount sparseCount request.index)
          (packedReviewerFringeWidth n) cells)
      else none := by
  simp [packedReviewerLogicalDecode, hsegment,
    packedReviewerClosedFringeAddress_eq]

theorem packedReviewerLogicalDecode_segment22_eq
    (n longCount sparseCount : Nat)
    (request : PackedReviewerLogicalRequest) (cells : List (List Bool))
    (hsegment : request.segment = 22) :
    packedReviewerLogicalDecode n longCount sparseCount request cells =
      if request.index < packedReviewerSelectChunkCount n then
        some (packedReviewerDecodeSpan n
          (packedReviewerSelectChunkAddress n longCount sparseCount request.index)
          (packedReviewerSelectChunkWidth n) cells)
      else none := by
  simp [packedReviewerLogicalDecode, hsegment,
    packedReviewerClosedSelectChunkAddress_eq]

/-- Execute one logical request against an external cell array. -/
def packedReviewerLogicalRead
    (n longCount sparseCount : Nat) (memory : List (List Bool))
    (request : PackedReviewerLogicalRequest) : Option (List Bool) :=
  match packedFetch memory
      (packedReviewerLogicalPlan n longCount sparseCount request) with
  | none => none
  | some cells =>
      packedReviewerLogicalDecode n longCount sparseCount request cells

/-- Every logical request lowers to at most two physical cells. -/
theorem packedReviewerLogicalPlan_length_le_two
    (n longCount sparseCount : Nat) (request : PackedReviewerLogicalRequest) :
    (packedReviewerLogicalPlan n longCount sparseCount request).length <= 2 := by
  unfold packedReviewerLogicalPlan
  split
  next =>
    rw [packedReviewerClosedInteriorReadPlan_eq]
    exact packedReviewerInteriorReadPlan_length_le_two _ _ _ _
  next =>
    split
    next => exact packedReviewerProbeCount_le_two _ _ _
    next => simp
  next =>
    split
    next => exact packedReviewerProbeCount_le_two _ _ _
    next => simp
  next segment =>
    split
    next =>
      split
      next => simp
      next source =>
        split
        next =>
          unfold packedReviewerLegacyRawPlan packedReviewerBPRawPlan
            packedReviewerClosedSourceReadPlan
          split <;> exact packedReviewerProbeCount_le_two _ _ _
        next => simp
    next => simp

end PackedCellProbe
end SuccinctFinal
end RMQ
