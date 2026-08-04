import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.WordWidth

/-!
# The physical read

Everything needed to answer a logical word read by probing `packedMemory` is now
available: the word geometry (`SourceGeometry`), the fact that every stride fits
one cell (`WordWidth`), and the conditional one-or-two-cell plan (`Probe`). This
module joins them.

`packedSourceRead` is executable and takes only the input size, the decoded long
count, the packed memory, the typed source and the index. It issues the probe
plan, fetches, and decodes. `packedSourceRead_of_some` proves that whenever the
flat payload store answers a read, this answers it with the same word.

The direction is an implication, not an equation, for the reason recorded in
`DD-20260804-022`: at an index between the sparse relative table's actual entry
count and its size-only capacity the packed read answers where the store would
have failed. Every **successful** logical read lowers exactly.
-/

namespace RMQ

namespace SuccinctFinal

namespace PackedCellProbe

open Cartesian
open SuccinctSpace

/-! ## The read -/

/-- The physical probe plan of one logical word read. -/
def packedSourceReadPlan (n longCount : Nat)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource) (index : Nat) :
    List Nat :=
  packedProbePlan n
    (packedStridedBitAddress n longCount source index
      (packedSourceStride n source))
    (packedSourceReadWidth n longCount source index)

/-- One logical word read, answered by probing the packed memory. -/
def packedSourceRead (n longCount : Nat) (memory : List (List Bool))
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource) (index : Nat) :
    Option (List Bool) :=
  if index < packedSourceWordCount n longCount source then
    (packedFetch memory (packedSourceReadPlan n longCount source index)).map
      (packedDecodeSpan n
        (packedStridedBitAddress n longCount source index
          (packedSourceStride n source))
        (packedSourceReadWidth n longCount source index))
  else
    none

/-- A logical word read never issues more than two physical probes. -/
theorem packedSourceReadPlan_length_le_two (n longCount : Nat)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource) (index : Nat) :
    (packedSourceReadPlan n longCount source index).length <= 2 :=
  packedProbeCount_le_two _ _ _

/-! ## The sparse relative table's actual extent -/

theorem packedSparseRelativeRead_fits
    (shape : CartesianShape) {index : Nat} {word : List Bool}
    (hget :
      (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape
        .selectSparseRelative)[index]? = some word) :
    index * packedLocalWidth shape.size + packedLocalWidth shape.size <=
      (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape
        .selectSparseRelative).length := by
  have hlen : shape.bpCode.length = 2 * shape.size :=
    CartesianShape.bpCode_length shape
  have hw :
      GenericSelect.sparseExceptionRelativeWidth shape.bpCode =
        packedLocalWidth shape.size := by
    unfold GenericSelect.sparseExceptionRelativeWidth packedLocalWidth
    rw [hlen]
  have hget' :
      (GenericSelect.sparseExceptionRelativeTable shape.bpCode
        false).store.words[index]? = some word := hget
  rw [packedFixedWidthTable_getElem?] at hget'
  have hlt :
      index <
        (GenericSelect.sparseExceptionRelativeEntries shape.bpCode false).length := by
    by_cases h : index <
        (GenericSelect.sparseExceptionRelativeEntries shape.bpCode false).length
    · exact h
    · rw [packedWordSlice_of_le (by omega)] at hget'
      exact absurd hget' (by simp)
  have hplen :
      (GenericSelect.sparseExceptionRelativeTable shape.bpCode false).payload.length =
        (GenericSelect.sparseExceptionRelativeEntries shape.bpCode false).length *
          GenericSelect.sparseExceptionRelativeWidth shape.bpCode :=
    (GenericSelect.sparseExceptionRelativeTable shape.bpCode false).payload_length_eq
  have hmul :
      (index + 1) *
          GenericSelect.sparseExceptionRelativeWidth shape.bpCode <=
        (GenericSelect.sparseExceptionRelativeEntries shape.bpCode false).length *
          GenericSelect.sparseExceptionRelativeWidth shape.bpCode :=
    Nat.mul_le_mul_right _ hlt
  have hsucc :
      (index + 1) * GenericSelect.sparseExceptionRelativeWidth shape.bpCode =
        index * GenericSelect.sparseExceptionRelativeWidth shape.bpCode +
          GenericSelect.sparseExceptionRelativeWidth shape.bpCode :=
    Nat.succ_mul _ _
  show
    index * packedLocalWidth shape.size + packedLocalWidth shape.size <=
      (GenericSelect.sparseExceptionRelativeTable shape.bpCode false).payload.length
  rw [← hw]
  omega

/-! ## The read width is the actual window

`packedSourceReadWidth` is computed from the size-only bit length. On a successful
read it agrees with the window the source payload actually has left, which is what
the decode has to produce.
-/

theorem packedSourceBitLength_ge (shape : CartesianShape)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource) :
    (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape source).length <=
      packedSourceBitLength shape.size (longCount shape) source := by
  by_cases hsparse : source = ConcreteBPNativeSuccinctRMQFlatPayloadSource.selectSparseRelative
  · subst hsparse
    have hlen : shape.bpCode.length = 2 * shape.size :=
      CartesianShape.bpCode_length shape
    have hw :
        GenericSelect.sparseExceptionRelativeWidth shape.bpCode =
          packedLocalWidth shape.size := by
      unfold GenericSelect.sparseExceptionRelativeWidth packedLocalWidth
      rw [hlen]
    have hplen :
        (GenericSelect.sparseExceptionRelativeTable shape.bpCode false).payload.length =
          (GenericSelect.sparseExceptionRelativeEntries shape.bpCode false).length *
            GenericSelect.sparseExceptionRelativeWidth shape.bpCode :=
      (GenericSelect.sparseExceptionRelativeTable shape.bpCode false).payload_length_eq
    have hbound := packedSparseRelativeEntries_le_capacity shape
    have hmul :
        (GenericSelect.sparseExceptionRelativeEntries shape.bpCode false).length *
            GenericSelect.sparseExceptionRelativeWidth shape.bpCode <=
          packedSparseRelativeCapacity shape.size *
            GenericSelect.sparseExceptionRelativeWidth shape.bpCode :=
      Nat.mul_le_mul_right _ hbound
    show
      (GenericSelect.sparseExceptionRelativeTable shape.bpCode false).payload.length <=
        packedSparseRelativeCapacity shape.size * packedLocalWidth shape.size
    rw [← hw]
    omega
  · rw [packedSourceBitLength_eq shape source (by simp [hsparse])]
    omega

theorem packedSourceReadWidth_eq_window
    (shape : CartesianShape)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
    {index : Nat} {word : List Bool}
    (hget :
      (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape source)[index]? =
        some word) :
    packedSourceReadWidth shape.size (longCount shape) source index =
      min (packedSourceStride shape.size source)
        ((concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape source).length -
          index * packedSourceStride shape.size source) := by
  by_cases hsparse : source = ConcreteBPNativeSuccinctRMQFlatPayloadSource.selectSparseRelative
  · subst hsparse
    have hfits := packedSparseRelativeRead_fits shape hget
    have hge := packedSourceBitLength_ge shape .selectSparseRelative
    show
      min (packedLocalWidth shape.size)
          (packedSparseRelativeCapacity shape.size * packedLocalWidth shape.size -
            index * packedLocalWidth shape.size) =
        min (packedLocalWidth shape.size)
          ((concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape
            .selectSparseRelative).length -
            index * packedLocalWidth shape.size)
    have hcap :
        packedSourceBitLength shape.size (longCount shape)
            ConcreteBPNativeSuccinctRMQFlatPayloadSource.selectSparseRelative =
          packedSparseRelativeCapacity shape.size *
            packedLocalWidth shape.size := rfl
    rw [hcap] at hge
    omega
  · unfold packedSourceReadWidth
    rw [← packedSourceBitLength_eq shape source (by simp [hsparse])]

/-! ## The lowering -/

set_option maxHeartbeats 1000000 in
/--
**Every successful logical word read lowers to the physical probe plan.** The
fetched cells decode to exactly the word the flat payload store returns.
-/
theorem packedSourceRead_of_some
    (shape : CartesianShape)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
    {index : Nat} {word : List Bool}
    (hcounted : PackedSourceCounted shape.size source)
    (hget :
      (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape source)[index]? =
        some word) :
    packedSourceRead shape.size (longCount shape) (packedMemory shape) source
        index =
      some word := by
  have hslice := packedSourceWords_of_some shape source hget
  have hlt :
      index < packedSourceWordCount shape.size (longCount shape) source := by
    by_cases h : index < packedSourceWordCount shape.size (longCount shape) source
    · exact h
    · rw [packedWordSlice_of_le (by omega)] at hslice
      exact absurd hslice (by simp)
  have hword :
      word =
        (((concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape source).drop
            (index * packedSourceStride shape.size source)).take
          (packedSourceStride shape.size source)) := by
    rw [packedWordSlice_of_lt hlt] at hslice
    exact (Option.some.inj hslice).symm
  have hwindow := packedSourceReadWidth_eq_window shape source hget
  have hcnt :
      concreteBPNativeSuccinctRMQFlatPayloadSourceCountedInFlat shape source :=
    (sourceCounted_iff_packed shape source).mpr hcounted
  have hflat := concreteBPNativeSuccinctRMQFlatPayloadSource_flat_slice shape source hcnt
  have hoff := packedSourceFlatOffset_eq shape source
  have hpaylen := packedPayloadLength_eq shape
  have hwidth :=
    packedSourceStride_le_cellWidth shape.size source hcounted
  -- the source payload sits inside the canonical payload
  have hsrc :
      ((packedPayloadBits shape).drop
          (packedSourceFlatOffset shape.size (longCount shape) source)).take
        (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape source).length =
        concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape source := by
    rw [← hoff]
    exact hflat
  have hwindowLength := congrArg List.length hsrc
  rw [List.length_take, List.length_drop,
    packedPayloadBits_length shape] at hwindowLength
  by_cases hzero :
      packedSourceReadWidth shape.size (longCount shape) source index = 0
  · -- A zero-width read issues no probe at all, and the stored word is empty for
    -- exactly the reason the width is zero.
    have hempty : word = [] := by
      rw [hword]
      rw [hzero] at hwindow
      by_cases hstride : packedSourceStride shape.size source = 0
      · rw [hstride]
        simp
      · have hpast :
            (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape source).length <=
              index * packedSourceStride shape.size source := by
          omega
        rw [List.drop_eq_nil_of_le hpast]
        simp
    have hplan :
        packedProbePlan shape.size
            (packedStridedBitAddress shape.size (longCount shape) source index
              (packedSourceStride shape.size source)) 0 = [] := by
      simp [packedProbePlan]
    unfold packedSourceRead packedSourceReadPlan
    rw [if_pos hlt, hzero, hplan, hempty]
    simp [packedFetch, packedDecodeSpan]
  · -- A positive-width read is contained in the source payload, hence in the
    -- canonical payload, hence in the allocated cells.
    have hpos :
        0 < packedSourceReadWidth shape.size (longCount shape) source index := by
      omega
    have hminle :
        packedSourceReadWidth shape.size (longCount shape) source index <=
          (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape source).length -
            index * packedSourceStride shape.size source := by
      rw [hwindow]
      omega
    have hinside :
        index * packedSourceStride shape.size source <
          (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape source).length := by
      omega
    have hcontain :
        packedSourceFlatOffset shape.size (longCount shape) source +
            (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape source).length <=
          packedPayloadLength shape.size := by
      omega
    have hfit2 :
        packedSourceFlatOffset shape.size (longCount shape) source +
            index * packedSourceStride shape.size source +
            packedSourceReadWidth shape.size (longCount shape) source index <=
          packedPayloadLength shape.size := by
      omega
    have hserial := packedSerialized_le_allocated shape.size
    have haddr :
        packedStridedBitAddress shape.size (longCount shape) source index
            (packedSourceStride shape.size source) =
          packedCellWidth shape.size +
            (packedSourceFlatOffset shape.size (longCount shape) source +
              index * packedSourceStride shape.size source) := by
      unfold packedStridedBitAddress
      omega
    have hfitalloc :
        packedStridedBitAddress shape.size (longCount shape) source index
            (packedSourceStride shape.size source) +
            packedSourceReadWidth shape.size (longCount shape) source index <=
          packedAllocatedBits shape.size := by
      rw [haddr]
      omega
    have hwle :
        packedSourceReadWidth shape.size (longCount shape) source index <=
          packedCellWidth shape.size :=
      Nat.le_trans
        (packedSourceReadWidth_le_stride shape.size (longCount shape) source index)
        hwidth
    have hdecode := packedProbePlan_decode shape hwle hfitalloc
    have hpayslice :=
      packedPayloadSlice shape
        (packedSourceFlatOffset shape.size (longCount shape) source +
          index * packedSourceStride shape.size source)
        (packedSourceReadWidth shape.size (longCount shape) source index) hfit2
    -- the canonical-payload window is the stored word
    have hchain :
        ((packedPayloadBits shape).drop
              (packedSourceFlatOffset shape.size (longCount shape) source +
                index * packedSourceStride shape.size source)).take
            (packedSourceReadWidth shape.size (longCount shape) source index) =
          word := by
      obtain ⟨L, hL⟩ :
          exists L,
            (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape source).length =
              L :=
        ⟨_, rfl⟩
      rw [hL] at hsrc hwindow
      rw [hword, hwindow, ← hsrc, List.drop_take, List.drop_drop,
        List.take_take, Nat.add_comm]
    unfold packedSourceRead packedSourceReadPlan
    rw [if_pos hlt, hdecode, haddr, hpayslice, hchain]

/-! ## The packed memory as a read store

The whole-query evaluator consumes a `WordRAM.ReadStore`. `packedBackedStore`
presents the packed memory as one, by routing a logical `(segment, index)` through
the already shape-free segment-to-source map and answering it with a physical
probe.

The theorem below is again one-directional, and now for two reasons rather than
one: `DD-20260804-022`'s sparse relative capacity, and the close interior sources,
whose stored words exist even when the interior is not ready but whose bits are
then not in the counted payload. The second is exactly the readiness guard `FG-07`
requires the controller to consult, so it appears here as a hypothesis on the two
segments that need it -- the same shape the pre-existing
`concreteBPNativeSuccinctRMQFlatPayloadReadStore_successful_read_segment_counted`
already uses.
-/

/-- The packed memory, presented as the read store the evaluator expects. -/
def packedBackedStore (n longCount : Nat) (memory : List (List Bool)) :
    WordRAM.ReadStore where
  readWord? segment index :=
    match packedSegmentSource? segment with
    | none => none
    | some source => packedSourceRead n longCount memory source index

/--
**Every successful store read is answered identically by probing the packed
memory.**
-/
theorem packedBackedStore_of_some
    (shape : CartesianShape) {segment index : Nat} {word : List Bool}
    (h24 :
      segment = 24 -> SuccinctClose.concreteBPRelativeRmmInteriorReady shape)
    (h25 :
      segment = 25 -> SuccinctClose.concreteBPRelativeRmmInteriorReady shape)
    (hread :
      (concreteBPNativeSuccinctRMQFlatPayloadReadStore shape).readWord? segment
          index = some word) :
    (packedBackedStore shape.size (longCount shape)
        (packedMemory shape)).readWord? segment index = some word := by
  have hcounted :=
    concreteBPNativeSuccinctRMQFlatPayloadReadStore_successful_read_segment_counted
      shape hread h24 h25
  have hread' :
      (match concreteBPNativeSuccinctRMQFlatPayloadSegmentSource? segment with
        | some source =>
            (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape source)[index]?
        | none => none) = some word := hread
  have hcounted' :
      (match concreteBPNativeSuccinctRMQFlatPayloadSegmentSource? segment with
        | some source =>
            concreteBPNativeSuccinctRMQFlatPayloadSourceCountedInFlat shape source
        | none => False) := hcounted
  show
    (match packedSegmentSource? segment with
      | none => none
      | some source =>
          packedSourceRead shape.size (longCount shape) (packedMemory shape)
            source index) = some word
  unfold packedSegmentSource?
  cases hsrc :
      concreteBPNativeSuccinctRMQFlatPayloadSegmentSource? segment with
  | none =>
      rw [hsrc] at hread'
      exact absurd hread' (by simp)
  | some source =>
      rw [hsrc] at hread' hcounted'
      exact
        packedSourceRead_of_some shape source
          ((sourceCounted_iff_packed shape source).mp hcounted') hread'

/--
**The two stores agree exactly, away from the one non-size-only source.**

For every segment other than the sparse relative table's, and under the readiness
guard on the two close interior segments, the packed memory answers a logical read
exactly as the flat payload store does -- including when the store has nothing to
answer with, because past the word count neither side produces a word.
-/
theorem packedBackedStore_eq_readWord
    (shape : CartesianShape) {segment index : Nat}
    (hsparse :
      packedSegmentSource? segment !=
        some ConcreteBPNativeSuccinctRMQFlatPayloadSource.selectSparseRelative)
    (h24 :
      segment = 24 -> SuccinctClose.concreteBPRelativeRmmInteriorReady shape)
    (h25 :
      segment = 25 -> SuccinctClose.concreteBPRelativeRmmInteriorReady shape) :
    (packedBackedStore shape.size (longCount shape)
        (packedMemory shape)).readWord? segment index =
      (concreteBPNativeSuccinctRMQFlatPayloadReadStore shape).readWord? segment
        index := by
  cases hflat :
      (concreteBPNativeSuccinctRMQFlatPayloadReadStore shape).readWord? segment
        index with
  | some word => exact packedBackedStore_of_some shape h24 h25 hflat
  | none =>
      have hflat' :
          (match concreteBPNativeSuccinctRMQFlatPayloadSegmentSource? segment with
            | some source =>
                (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape
                  source)[index]?
            | none => none) = none := hflat
      show
        (match packedSegmentSource? segment with
          | none => none
          | some source =>
              packedSourceRead shape.size (longCount shape) (packedMemory shape)
                source index) = none
      unfold packedSegmentSource? at hsparse ⊢
      cases hsrc :
          concreteBPNativeSuccinctRMQFlatPayloadSegmentSource? segment with
      | none => rfl
      | some source =>
          rw [hsrc] at hflat' hsparse
          show
            packedSourceRead shape.size (longCount shape) (packedMemory shape)
              source index = none
          have hne :
              source !=
                ConcreteBPNativeSuccinctRMQFlatPayloadSource.selectSparseRelative := by
            simpa using hsparse
          have hcount := packedSourceWords_of_none shape source hne hflat'
          have hnot :
              ¬ index <
                packedSourceWordCount shape.size (longCount shape) source := by
            omega
          unfold packedSourceRead
          rw [if_neg hnot]

end PackedCellProbe

end SuccinctFinal

end RMQ
