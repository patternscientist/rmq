import RMQ.Core.SuccinctFinal.RAM.ReviewerPhysical
import RMQ.Core.SuccinctClose.RelativeRmmMacro.ChargedFringeWiring
import RMQ.Core.SuccinctClose.RelativeRmmMacro.ChargedRankSelectWiring

/-!
# Word-RAM bridge for the final BP-native succinct RMQ query

This module is an additive refinement layer over `SuccinctFinal`.  The existing
final capstone remains the reference theorem; the definitions below replay the
same final query shape with interpreted close-select, rank-seed, and answer-rank
leaves, then prove that the interpreted query refines the existing `Costed`
query.

The concrete global segment map and flat-payload backing manifest live in
`RMQ.Core.SuccinctFinal.RAM.Segments` and
`RMQ.Core.SuccinctFinal.RAM.FlatPayload`; this module remains the compatibility
root for the final RAM theorem surface.
-/

namespace RMQ
namespace SuccinctFinal

/-- Interpreted close-select leg: the charged chunked route select-close
execution (B3 swap; the retired register-interpreted evaluator remains
available as `SparseExceptionSelectData.selectInterpretedCosted`). -/
def concreteBPNativeSelectCloseInterpretedCosted
    (shape : Cartesian.CartesianShape)
    (idx : Nat) : Costed (Option Nat) :=
  concreteBPNativeChunkedSelectCloseCosted shape idx

/-- Interpreted false-rank leg: the charged chunked rank-close seed (B3
swap; the retired register-interpreted evaluator remains available as
`TwoLevelPayloadLiveStoredWordRankData.rankRegisterInterpretedCosted`). -/
def concreteBPNativeRankCloseInterpretedCosted
    (shape : Cartesian.CartesianShape)
    (pos : Nat) : Costed Nat :=
  concreteBPNativeChunkedRankCloseCosted shape pos

/-- Retired register-interpreted close-select leg.  Legacy/compatibility
surfaces (the pre-canonical `QueryInterpretedCosted` chain) keep the
word-primitive instructions per REQ-B3-04; the accepted route uses the
swapped chunked consumer above. -/
def concreteBPNativeSelectCloseRegisterInterpretedCosted
    (shape : Cartesian.CartesianShape)
    (idx : Nat) : Costed (Option Nat) :=
  (GenericSelect.sparseExceptionSelectData shape.bpCode false)
    |>.selectInterpretedCosted idx

/-- Retired register-interpreted false-rank leg (legacy/compatibility
surfaces only; the accepted route uses the swapped chunked seed above). -/
def concreteBPNativeRankCloseRegisterInterpretedCosted
    (shape : Cartesian.CartesianShape)
    (pos : Nat) : Costed Nat :=
  (builtRelativeSplitBPCloseRankData shape)
    |>.rankRegisterInterpretedCosted false pos

/-- Structural `WordRAM.TraceEvent` replay for the close-select leg (B3:
the chunked select-close trace against the canonical global store). -/
def concreteBPNativeSelectCloseWordTraceResult
    (shape : Cartesian.CartesianShape)
    (idx : Nat) : WordRAM.TraceResult (Option Nat) :=
  concreteBPNativeChunkedSelectCloseGlobalWordTraceResult shape idx

theorem concreteBPNativeSelectCloseWordTraceResult_refines_interpretedCosted
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    (concreteBPNativeSelectCloseWordTraceResult shape idx).toCosted =
      concreteBPNativeSelectCloseInterpretedCosted shape idx :=
  concreteBPNativeChunkedSelectCloseGlobalWordTraceResult_refines shape idx

/-- Retired structural replay for the close-select leg (legacy/compatibility
surfaces only, REQ-B3-04). -/
def concreteBPNativeSelectCloseRegisterWordTraceResult
    (shape : Cartesian.CartesianShape)
    (idx : Nat) : WordRAM.TraceResult (Option Nat) :=
  (GenericSelect.sparseExceptionSelectData shape.bpCode false)
    |>.selectTraceResult idx

theorem concreteBPNativeSelectCloseRegisterWordTraceResult_refines_registerInterpretedCosted
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    (concreteBPNativeSelectCloseRegisterWordTraceResult shape idx).toCosted =
      concreteBPNativeSelectCloseRegisterInterpretedCosted shape idx := by
  simp [concreteBPNativeSelectCloseRegisterWordTraceResult,
    concreteBPNativeSelectCloseRegisterInterpretedCosted,
    GenericSelect.SparseExceptionSelectData.selectTraceResult_refines_interpretedCosted]

private theorem
    concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead_relabelReadSegmentWith
    (segmentMap : Nat -> Nat)
    (h26 : forall segment, segmentMap segment ≠ 26)
    (h27 : forall segment, segmentMap segment ≠ 27)
    (event : WordRAM.TraceEvent) :
    concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead
      (event.relabelReadSegmentWith segmentMap) := by
  cases event with
  | readWord segment index word? =>
      cases word? with
      | none =>
          simp [WordRAM.TraceEvent.relabelReadSegmentWith,
            concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead]
      | some word =>
          have hnot26 := h26 segment
          have hnot27 := h27 segment
          simp [WordRAM.TraceEvent.relabelReadSegmentWith,
            concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead,
            hnot26, hnot27]
  | wordRank target limit result =>
      simp [WordRAM.TraceEvent.relabelReadSegmentWith,
        concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead]
  | wordSelect target occurrence result =>
      simp [WordRAM.TraceEvent.relabelReadSegmentWith,
        concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead]
  | syntheticCostOnlyPrimitive =>
      simp [WordRAM.TraceEvent.relabelReadSegmentWith,
        concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead]

private theorem
    concreteBPNativeSuccinctRMQTraceResult_relabelReadSegmentsWith_noFiniteSmallInteriorSuccessfulRead
    {α : Type} (segmentMap : Nat -> Nat)
    (result : WordRAM.TraceResult α)
    (h26 : forall segment, segmentMap segment ≠ 26)
    (h27 : forall segment, segmentMap segment ≠ 27) :
    forall event,
      List.Mem event
          (WordRAM.TraceResult.relabelReadSegmentsWith
            segmentMap result).trace ->
        concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead
          event := by
  intro event hmem
  rcases List.mem_map.mp hmem with ⟨localEvent, _hlocal, hrelabeled⟩
  subst event
  exact
    concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead_relabelReadSegmentWith
      segmentMap h26 h27 localEvent

private theorem
    concreteBPNativeSuccinctRMQSingletonSegmentMap_ne_of_bases_ne
    (base dead : Nat)
    (hbase : base ≠ 26) (hdead : dead ≠ 26) :
    forall segment, WordRAM.singletonSegmentMap base dead segment ≠ 26 := by
  intro segment
  cases segment with
  | zero =>
      simpa [WordRAM.singletonSegmentMap] using hbase
  | succ segment =>
      simpa [WordRAM.singletonSegmentMap] using hdead

private theorem
    concreteBPNativeSuccinctRMQSingletonSegmentMap_ne27_of_bases_ne
    (base dead : Nat)
    (hbase : base ≠ 27) (hdead : dead ≠ 27) :
    forall segment, WordRAM.singletonSegmentMap base dead segment ≠ 27 := by
  intro segment
  cases segment with
  | zero =>
      simpa [WordRAM.singletonSegmentMap] using hbase
  | succ segment =>
      simpa [WordRAM.singletonSegmentMap] using hdead

private theorem
    concreteBPNativeFixedWidthNatTable_readTraceResultAtSegment_noFiniteSmallInteriorSuccessfulRead
    {entries : List Nat} {width : Nat}
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (segmentBase deadSegment i : Nat)
    (h26 :
      forall segment,
        WordRAM.singletonSegmentMap segmentBase deadSegment segment ≠ 26)
    (h27 :
      forall segment,
        WordRAM.singletonSegmentMap segmentBase deadSegment segment ≠ 27) :
    forall event,
      List.Mem event
          (table.readTraceResultAtSegment
            segmentBase deadSegment i).trace ->
        concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead
          event := by
  unfold SuccinctSpace.FixedWidthNatTable.readTraceResultAtSegment
  exact
    concreteBPNativeSuccinctRMQTraceResult_relabelReadSegmentsWith_noFiniteSmallInteriorSuccessfulRead
      (WordRAM.singletonSegmentMap segmentBase deadSegment)
      (table.readTraceResult i) h26 h27

private theorem
    concreteBPNativeFixedWidthOptionNatTable_readTraceResultAtSegment_noFiniteSmallInteriorSuccessfulRead
    {entries : List (Option Nat)} {width : Nat}
    (table : SuccinctSpace.FixedWidthOptionNatTable entries width)
    (segmentBase deadSegment i : Nat)
    (h26 :
      forall segment,
        WordRAM.singletonSegmentMap segmentBase deadSegment segment ≠ 26)
    (h27 :
      forall segment,
        WordRAM.singletonSegmentMap segmentBase deadSegment segment ≠ 27) :
    forall event,
      List.Mem event
          (table.readTraceResultAtSegment
            segmentBase deadSegment i).trace ->
        concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead
          event := by
  unfold SuccinctSpace.FixedWidthOptionNatTable.readTraceResultAtSegment
  exact
    concreteBPNativeSuccinctRMQTraceResult_relabelReadSegmentsWith_noFiniteSmallInteriorSuccessfulRead
      (WordRAM.singletonSegmentMap segmentBase deadSegment)
      (table.readTraceResult i) h26 h27

private theorem
    concreteBPNativeSuccinctRMQTripleSegmentMap_ne_of_bases_ne
    (base dead : Nat)
    (h0 : base ≠ 26) (h1 : base + 1 ≠ 26)
    (h2 : base + 2 ≠ 26) (hdead : dead ≠ 26) :
    forall segment, WordRAM.tripleSegmentMap base dead segment ≠ 26 := by
  intro segment
  cases segment with
  | zero =>
      simpa [WordRAM.tripleSegmentMap] using h0
  | succ segment =>
      cases segment with
      | zero =>
          intro heq
          exact h1 (by
            simpa [WordRAM.tripleSegmentMap,
              WordRAM.TraceEvent.tripleSegmentMap] using heq)
      | succ segment =>
          cases segment with
          | zero =>
              intro heq
              exact h2 (by
                simpa [WordRAM.tripleSegmentMap,
                  WordRAM.TraceEvent.tripleSegmentMap] using heq)
          | succ segment =>
              simpa [WordRAM.tripleSegmentMap] using hdead

private theorem
    concreteBPNativeSuccinctRMQTripleSegmentMap_ne27_of_bases_ne
    (base dead : Nat)
    (h0 : base ≠ 27) (h1 : base + 1 ≠ 27)
    (h2 : base + 2 ≠ 27) (hdead : dead ≠ 27) :
    forall segment, WordRAM.tripleSegmentMap base dead segment ≠ 27 := by
  intro segment
  cases segment with
  | zero =>
      simpa [WordRAM.tripleSegmentMap] using h0
  | succ segment =>
      cases segment with
      | zero =>
          intro heq
          exact h1 (by
            simpa [WordRAM.tripleSegmentMap,
              WordRAM.TraceEvent.tripleSegmentMap] using heq)
      | succ segment =>
          cases segment with
          | zero =>
              intro heq
              exact h2 (by
                simpa [WordRAM.tripleSegmentMap,
                  WordRAM.TraceEvent.tripleSegmentMap] using heq)
          | succ segment =>
              simpa [WordRAM.tripleSegmentMap] using hdead

private def concreteBPNativeSuccinctRMQSegmentMapAvoidsReadyClose
    (segmentMap : Nat -> Nat) : Prop :=
  (forall segment, segmentMap segment ≠ 20) /\
    (forall segment, segmentMap segment ≠ 21) /\
    (forall segment, segmentMap segment ≠ 22) /\
    (forall segment, segmentMap segment ≠ 23) /\
    (forall segment, segmentMap segment ≠ 24) /\
    (forall segment, segmentMap segment ≠ 25)

private theorem
    concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead_relabelReadSegmentWith
    (segmentMap : Nat -> Nat)
    (havoid :
      concreteBPNativeSuccinctRMQSegmentMapAvoidsReadyClose segmentMap)
    (event : WordRAM.TraceEvent) :
    concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead
      (event.relabelReadSegmentWith segmentMap) := by
  rcases havoid with ⟨h20, h21, h22, h23, h24, h25⟩
  cases event with
  | readWord segment index word? =>
      cases word? with
      | none =>
          simp [WordRAM.TraceEvent.relabelReadSegmentWith,
            concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead]
      | some word =>
          have hnot24 := h24 segment
          have hnot25 := h25 segment
          simp [WordRAM.TraceEvent.relabelReadSegmentWith,
            concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead,
            hnot24, hnot25]
  | wordRank target limit result =>
      simp [WordRAM.TraceEvent.relabelReadSegmentWith,
        concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead]
  | wordSelect target occurrence result =>
      simp [WordRAM.TraceEvent.relabelReadSegmentWith,
        concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead]
  | syntheticCostOnlyPrimitive =>
      simp [WordRAM.TraceEvent.relabelReadSegmentWith,
        concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead]

private theorem
    concreteBPNativeSuccinctRMQTraceResult_relabelReadSegmentsWith_noReadyCloseSuccessfulRead
    {α : Type} (segmentMap : Nat -> Nat)
    (result : WordRAM.TraceResult α)
    (havoid :
      concreteBPNativeSuccinctRMQSegmentMapAvoidsReadyClose segmentMap) :
    forall event,
      List.Mem event
          (WordRAM.TraceResult.relabelReadSegmentsWith
            segmentMap result).trace ->
        concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead
          event := by
  intro event hmem
  rcases List.mem_map.mp hmem with ⟨localEvent, _hlocal, hrelabeled⟩
  subst event
  exact
    concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead_relabelReadSegmentWith
      segmentMap havoid localEvent

private theorem
    concreteBPNativeSuccinctRMQSingletonSegmentMap_ne_target_of_bases_ne
    (base dead target : Nat)
    (hbase : base ≠ target) (hdead : dead ≠ target) :
    forall segment, WordRAM.singletonSegmentMap base dead segment ≠ target := by
  intro segment
  cases segment with
  | zero =>
      simpa [WordRAM.singletonSegmentMap] using hbase
  | succ segment =>
      simpa [WordRAM.singletonSegmentMap] using hdead

private theorem
    concreteBPNativeSuccinctRMQTripleSegmentMap_ne_target_of_bases_ne
    (base dead target : Nat)
    (h0 : base ≠ target) (h1 : base + 1 ≠ target)
    (h2 : base + 2 ≠ target) (hdead : dead ≠ target) :
    forall segment, WordRAM.tripleSegmentMap base dead segment ≠ target := by
  intro segment
  cases segment with
  | zero =>
      simpa [WordRAM.tripleSegmentMap] using h0
  | succ segment =>
      cases segment with
      | zero =>
          intro heq
          exact h1 (by
            simpa [WordRAM.tripleSegmentMap,
              WordRAM.TraceEvent.tripleSegmentMap] using heq)
      | succ segment =>
          cases segment with
          | zero =>
              intro heq
              exact h2 (by
                simpa [WordRAM.tripleSegmentMap,
                  WordRAM.TraceEvent.tripleSegmentMap] using heq)
          | succ segment =>
              simpa [WordRAM.tripleSegmentMap] using hdead

private theorem
    concreteBPNativeSuccinctRMQSingletonSegmentMap_avoidsReadyClose_of_bases_ne
    (base dead : Nat)
    (hbase20 : base ≠ 20) (hdead20 : dead ≠ 20)
    (hbase21 : base ≠ 21) (hdead21 : dead ≠ 21)
    (hbase22 : base ≠ 22) (hdead22 : dead ≠ 22)
    (hbase23 : base ≠ 23) (hdead23 : dead ≠ 23)
    (hbase24 : base ≠ 24) (hdead24 : dead ≠ 24)
    (hbase25 : base ≠ 25) (hdead25 : dead ≠ 25) :
    concreteBPNativeSuccinctRMQSegmentMapAvoidsReadyClose
      (WordRAM.singletonSegmentMap base dead) := by
  exact
    ⟨concreteBPNativeSuccinctRMQSingletonSegmentMap_ne_target_of_bases_ne
        base dead 20 hbase20 hdead20,
      concreteBPNativeSuccinctRMQSingletonSegmentMap_ne_target_of_bases_ne
        base dead 21 hbase21 hdead21,
      concreteBPNativeSuccinctRMQSingletonSegmentMap_ne_target_of_bases_ne
        base dead 22 hbase22 hdead22,
      concreteBPNativeSuccinctRMQSingletonSegmentMap_ne_target_of_bases_ne
        base dead 23 hbase23 hdead23,
      concreteBPNativeSuccinctRMQSingletonSegmentMap_ne_target_of_bases_ne
        base dead 24 hbase24 hdead24,
      concreteBPNativeSuccinctRMQSingletonSegmentMap_ne_target_of_bases_ne
        base dead 25 hbase25 hdead25⟩

private theorem
    concreteBPNativeSuccinctRMQTripleSegmentMap_avoidsReadyClose_of_bases_ne
    (base dead : Nat)
    (h020 : base ≠ 20) (h120 : base + 1 ≠ 20)
    (h220 : base + 2 ≠ 20) (hdead20 : dead ≠ 20)
    (h021 : base ≠ 21) (h121 : base + 1 ≠ 21)
    (h221 : base + 2 ≠ 21) (hdead21 : dead ≠ 21)
    (h022 : base ≠ 22) (h122 : base + 1 ≠ 22)
    (h222 : base + 2 ≠ 22) (hdead22 : dead ≠ 22)
    (h023 : base ≠ 23) (h123 : base + 1 ≠ 23)
    (h223 : base + 2 ≠ 23) (hdead23 : dead ≠ 23)
    (h024 : base ≠ 24) (h124 : base + 1 ≠ 24)
    (h224 : base + 2 ≠ 24) (hdead24 : dead ≠ 24)
    (h025 : base ≠ 25) (h125 : base + 1 ≠ 25)
    (h225 : base + 2 ≠ 25) (hdead25 : dead ≠ 25) :
    concreteBPNativeSuccinctRMQSegmentMapAvoidsReadyClose
      (WordRAM.tripleSegmentMap base dead) := by
  exact
    ⟨concreteBPNativeSuccinctRMQTripleSegmentMap_ne_target_of_bases_ne
        base dead 20 h020 h120 h220 hdead20,
      concreteBPNativeSuccinctRMQTripleSegmentMap_ne_target_of_bases_ne
        base dead 21 h021 h121 h221 hdead21,
      concreteBPNativeSuccinctRMQTripleSegmentMap_ne_target_of_bases_ne
        base dead 22 h022 h122 h222 hdead22,
      concreteBPNativeSuccinctRMQTripleSegmentMap_ne_target_of_bases_ne
        base dead 23 h023 h123 h223 hdead23,
      concreteBPNativeSuccinctRMQTripleSegmentMap_ne_target_of_bases_ne
        base dead 24 h024 h124 h224 hdead24,
      concreteBPNativeSuccinctRMQTripleSegmentMap_ne_target_of_bases_ne
        base dead 25 h025 h125 h225 hdead25⟩

private theorem
    concreteBPNativeNat_ne_readyClose_of_outside
    {n target : Nat} (houtside : n < 20 ∨ 25 < n)
    (htarget : target = 20 ∨ target = 21 ∨ target = 22 ∨
      target = 23 ∨ target = 24 ∨ target = 25) :
    n ≠ target := by
  rcases htarget with htarget | htarget | htarget | htarget | htarget | htarget <;>
    subst target <;> omega

private theorem
    concreteBPNativeSuccinctRMQSingletonSegmentMap_avoidsReadyClose_of_outside
    (base dead : Nat)
    (hbase : base < 20 ∨ 25 < base)
    (hdead : dead < 20 ∨ 25 < dead) :
    concreteBPNativeSuccinctRMQSegmentMapAvoidsReadyClose
      (WordRAM.singletonSegmentMap base dead) := by
  exact
    concreteBPNativeSuccinctRMQSingletonSegmentMap_avoidsReadyClose_of_bases_ne
      base dead
      (concreteBPNativeNat_ne_readyClose_of_outside hbase (Or.inl rfl))
      (concreteBPNativeNat_ne_readyClose_of_outside hdead (Or.inl rfl))
      (concreteBPNativeNat_ne_readyClose_of_outside hbase (Or.inr (Or.inl rfl)))
      (concreteBPNativeNat_ne_readyClose_of_outside hdead (Or.inr (Or.inl rfl)))
      (concreteBPNativeNat_ne_readyClose_of_outside hbase (Or.inr (Or.inr (Or.inl rfl))))
      (concreteBPNativeNat_ne_readyClose_of_outside hdead (Or.inr (Or.inr (Or.inl rfl))))
      (concreteBPNativeNat_ne_readyClose_of_outside hbase (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      (concreteBPNativeNat_ne_readyClose_of_outside hdead (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      (concreteBPNativeNat_ne_readyClose_of_outside hbase (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
      (concreteBPNativeNat_ne_readyClose_of_outside hdead (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
      (concreteBPNativeNat_ne_readyClose_of_outside hbase (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
      (concreteBPNativeNat_ne_readyClose_of_outside hdead (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))

private theorem
    concreteBPNativeSuccinctRMQTripleSegmentMap_avoidsReadyClose_of_outside
    (base dead : Nat)
    (hbase : base < 20 ∨ 25 < base)
    (hbase1 : base + 1 < 20 ∨ 25 < base + 1)
    (hbase2 : base + 2 < 20 ∨ 25 < base + 2)
    (hdead : dead < 20 ∨ 25 < dead) :
    concreteBPNativeSuccinctRMQSegmentMapAvoidsReadyClose
      (WordRAM.tripleSegmentMap base dead) := by
  exact
    concreteBPNativeSuccinctRMQTripleSegmentMap_avoidsReadyClose_of_bases_ne
      base dead
      (concreteBPNativeNat_ne_readyClose_of_outside hbase (Or.inl rfl))
      (concreteBPNativeNat_ne_readyClose_of_outside hbase1 (Or.inl rfl))
      (concreteBPNativeNat_ne_readyClose_of_outside hbase2 (Or.inl rfl))
      (concreteBPNativeNat_ne_readyClose_of_outside hdead (Or.inl rfl))
      (concreteBPNativeNat_ne_readyClose_of_outside hbase (Or.inr (Or.inl rfl)))
      (concreteBPNativeNat_ne_readyClose_of_outside hbase1 (Or.inr (Or.inl rfl)))
      (concreteBPNativeNat_ne_readyClose_of_outside hbase2 (Or.inr (Or.inl rfl)))
      (concreteBPNativeNat_ne_readyClose_of_outside hdead (Or.inr (Or.inl rfl)))
      (concreteBPNativeNat_ne_readyClose_of_outside hbase (Or.inr (Or.inr (Or.inl rfl))))
      (concreteBPNativeNat_ne_readyClose_of_outside hbase1 (Or.inr (Or.inr (Or.inl rfl))))
      (concreteBPNativeNat_ne_readyClose_of_outside hbase2 (Or.inr (Or.inr (Or.inl rfl))))
      (concreteBPNativeNat_ne_readyClose_of_outside hdead (Or.inr (Or.inr (Or.inl rfl))))
      (concreteBPNativeNat_ne_readyClose_of_outside hbase (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      (concreteBPNativeNat_ne_readyClose_of_outside hbase1 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      (concreteBPNativeNat_ne_readyClose_of_outside hbase2 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      (concreteBPNativeNat_ne_readyClose_of_outside hdead (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      (concreteBPNativeNat_ne_readyClose_of_outside hbase (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
      (concreteBPNativeNat_ne_readyClose_of_outside hbase1 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
      (concreteBPNativeNat_ne_readyClose_of_outside hbase2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
      (concreteBPNativeNat_ne_readyClose_of_outside hdead (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
      (concreteBPNativeNat_ne_readyClose_of_outside hbase (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
      (concreteBPNativeNat_ne_readyClose_of_outside hbase1 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
      (concreteBPNativeNat_ne_readyClose_of_outside hbase2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
      (concreteBPNativeNat_ne_readyClose_of_outside hdead (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))

private theorem
    concreteBPNativeFixedWidthNatTable_readTraceResultAtSegment_noReadyCloseSuccessfulRead
    {entries : List Nat} {width : Nat}
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (segmentBase deadSegment i : Nat)
    (havoid :
      concreteBPNativeSuccinctRMQSegmentMapAvoidsReadyClose
        (WordRAM.singletonSegmentMap segmentBase deadSegment)) :
    forall event,
      List.Mem event
          (table.readTraceResultAtSegment
            segmentBase deadSegment i).trace ->
        concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead
          event := by
  unfold SuccinctSpace.FixedWidthNatTable.readTraceResultAtSegment
  exact
    concreteBPNativeSuccinctRMQTraceResult_relabelReadSegmentsWith_noReadyCloseSuccessfulRead
      (WordRAM.singletonSegmentMap segmentBase deadSegment)
      (table.readTraceResult i) havoid

private theorem
    concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead_relabelReadSegmentWith_payload
    (segmentMap : Nat -> Nat)
    (h24 : forall segment, segmentMap segment ≠ 24)
    (h25 : forall segment, segmentMap segment ≠ 25)
    (event : WordRAM.TraceEvent) :
    concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead
      (event.relabelReadSegmentWith segmentMap) := by
  cases event with
  | readWord segment index word? =>
      cases word? with
      | none =>
          simp [WordRAM.TraceEvent.relabelReadSegmentWith,
            concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead]
      | some word =>
          have hnot24 := h24 segment
          have hnot25 := h25 segment
          simp [WordRAM.TraceEvent.relabelReadSegmentWith,
            concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead,
            hnot24, hnot25]
  | wordRank target limit result =>
      simp [WordRAM.TraceEvent.relabelReadSegmentWith,
        concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead]
  | wordSelect target occurrence result =>
      simp [WordRAM.TraceEvent.relabelReadSegmentWith,
        concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead]
  | syntheticCostOnlyPrimitive =>
      simp [WordRAM.TraceEvent.relabelReadSegmentWith,
        concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead]

private theorem
    concreteBPNativeSuccinctRMQTraceResult_relabelReadSegmentsWith_noReadyClosePayloadSuccessfulRead
    {α : Type} (segmentMap : Nat -> Nat)
    (result : WordRAM.TraceResult α)
    (h24 : forall segment, segmentMap segment ≠ 24)
    (h25 : forall segment, segmentMap segment ≠ 25) :
    forall event,
      List.Mem event
          (WordRAM.TraceResult.relabelReadSegmentsWith
            segmentMap result).trace ->
        concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead
          event := by
  intro event hmem
  rcases List.mem_map.mp hmem with ⟨localEvent, _hlocal, hrelabeled⟩
  subst event
  exact
    concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead_relabelReadSegmentWith_payload
      segmentMap h24 h25 localEvent

private theorem
    concreteBPNativeFixedWidthNatTable_readTraceResultAtSegment_noReadyClosePayloadSuccessfulRead
    {entries : List Nat} {width : Nat}
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (segmentBase deadSegment i : Nat)
    (h24 :
      forall segment,
        WordRAM.singletonSegmentMap segmentBase deadSegment segment ≠ 24)
    (h25 :
      forall segment,
        WordRAM.singletonSegmentMap segmentBase deadSegment segment ≠ 25) :
    forall event,
      List.Mem event
          (table.readTraceResultAtSegment
            segmentBase deadSegment i).trace ->
        concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead
          event := by
  unfold SuccinctSpace.FixedWidthNatTable.readTraceResultAtSegment
  exact
    concreteBPNativeSuccinctRMQTraceResult_relabelReadSegmentsWith_noReadyClosePayloadSuccessfulRead
      (WordRAM.singletonSegmentMap segmentBase deadSegment)
      (table.readTraceResult i) h24 h25

private theorem
    concreteBPNativeFixedWidthOptionNatTable_readTraceResultAtSegment_noReadyCloseSuccessfulRead
    {entries : List (Option Nat)} {width : Nat}
    (table : SuccinctSpace.FixedWidthOptionNatTable entries width)
    (segmentBase deadSegment i : Nat)
    (havoid :
      concreteBPNativeSuccinctRMQSegmentMapAvoidsReadyClose
        (WordRAM.singletonSegmentMap segmentBase deadSegment)) :
    forall event,
      List.Mem event
          (table.readTraceResultAtSegment
            segmentBase deadSegment i).trace ->
        concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead
          event := by
  unfold SuccinctSpace.FixedWidthOptionNatTable.readTraceResultAtSegment
  exact
    concreteBPNativeSuccinctRMQTraceResult_relabelReadSegmentsWith_noReadyCloseSuccessfulRead
      (WordRAM.singletonSegmentMap segmentBase deadSegment)
      (table.readTraceResult i) havoid

private theorem
    concreteBPNativeSuccinctRMQBpCodeWordReadTraceResult_noFiniteSmallInteriorSuccessfulRead
    (shape : Cartesian.CartesianShape) (index : Nat) :
    forall event,
      List.Mem event
        (SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpCodeWordReadTraceResult
          shape index).trace ->
        concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead
          event := by
  intro event hmem
  simp [SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpCodeWordReadTraceResult,
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpCodeReadWordTraceEvent,
    concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead]
    at hmem ⊢
  cases hmem with
  | head =>
      simp
  | tail _ htail =>
      cases htail

private theorem
    concreteBPNativeSuccinctRMQBpCodeReadWordTraceEvent_noFiniteSmallInteriorSuccessfulRead
    (shape : Cartesian.CartesianShape) (index : Nat) :
    concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead
      (SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpCodeReadWordTraceEvent
        shape index) := by
  simp [SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpCodeReadWordTraceEvent,
    concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead]

private theorem
    concreteBPNativeSuccinctRMQBpCodeWordReadTraceResult_noReadyCloseSuccessfulRead
    (shape : Cartesian.CartesianShape) (index : Nat) :
    forall event,
      List.Mem event
        (SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpCodeWordReadTraceResult
          shape index).trace ->
        concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead
          event := by
  intro event hmem
  simp [SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpCodeWordReadTraceResult,
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpCodeReadWordTraceEvent,
    concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead]
    at hmem ⊢
  cases hmem with
  | head =>
      simp
  | tail _ htail =>
      cases htail

private theorem
    concreteBPNativeSuccinctRMQBpCodeReadWordTraceEvent_noReadyCloseSuccessfulRead
    (shape : Cartesian.CartesianShape) (index : Nat) :
    concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead
      (SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpCodeReadWordTraceEvent
        shape index) := by
  simp [SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpCodeReadWordTraceEvent,
    concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead]

private theorem
    concreteBPNativeSuccinctRMQLocalBPBlockWordsTraceResult_noFiniteSmallInteriorSuccessfulRead
    (shape : Cartesian.CartesianShape) (blockSize close : Nat) :
    forall event,
      List.Mem event
        (SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPBlockWordsTraceResult
          shape blockSize close).trace ->
        concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead
          event := by
  unfold SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPBlockWordsTraceResult
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      concreteBPNativeSuccinctRMQBpCodeWordReadTraceResult_noFiniteSmallInteriorSuccessfulRead
        shape
        (SuccinctClose.blockStartOf blockSize
            (SuccinctClose.blockOfClose blockSize close) /
          SuccinctRank.machineWordBits shape.bpCode.length)
  · apply WordRAM.TraceResult.bind_trace_forall
    · exact
        concreteBPNativeSuccinctRMQBpCodeWordReadTraceResult_noFiniteSmallInteriorSuccessfulRead
          shape
          (SuccinctClose.blockStartOf blockSize
              (SuccinctClose.blockOfClose blockSize close) /
            SuccinctRank.machineWordBits shape.bpCode.length + 1)
    · apply WordRAM.TraceResult.bind_trace_forall
      · exact
          concreteBPNativeSuccinctRMQBpCodeWordReadTraceResult_noFiniteSmallInteriorSuccessfulRead
            shape
            (SuccinctClose.blockStartOf blockSize
                (SuccinctClose.blockOfClose blockSize close) /
              SuccinctRank.machineWordBits shape.bpCode.length + 2)
      · apply WordRAM.TraceResult.map_trace_forall
        exact
          concreteBPNativeSuccinctRMQBpCodeWordReadTraceResult_noFiniteSmallInteriorSuccessfulRead
            shape
            (SuccinctClose.blockStartOf blockSize
                (SuccinctClose.blockOfClose blockSize close) /
              SuccinctRank.machineWordBits shape.bpCode.length + 3)

private theorem
    concreteBPNativeSuccinctRMQLocalBPWindowBitsTraceResult_noFiniteSmallInteriorSuccessfulRead
    (shape : Cartesian.CartesianShape) (blockSize close : Nat) :
    forall event,
      List.Mem event
        (SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPWindowBitsTraceResult
          shape blockSize close).trace ->
        concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead
          event := by
  unfold SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPWindowBitsTraceResult
  exact WordRAM.TraceResult.map_trace_forall
    concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead
    _ _
    (concreteBPNativeSuccinctRMQLocalBPBlockWordsTraceResult_noFiniteSmallInteriorSuccessfulRead
      shape blockSize close)

private theorem
    concreteBPNativeSuccinctRMQLocalBPBlockWordsTraceResult_noReadyCloseSuccessfulRead
    (shape : Cartesian.CartesianShape) (blockSize close : Nat) :
    forall event,
      List.Mem event
        (SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPBlockWordsTraceResult
          shape blockSize close).trace ->
        concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead
          event := by
  unfold SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPBlockWordsTraceResult
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      concreteBPNativeSuccinctRMQBpCodeWordReadTraceResult_noReadyCloseSuccessfulRead
        shape
        (SuccinctClose.blockStartOf blockSize
            (SuccinctClose.blockOfClose blockSize close) /
          SuccinctRank.machineWordBits shape.bpCode.length)
  · apply WordRAM.TraceResult.bind_trace_forall
    · exact
        concreteBPNativeSuccinctRMQBpCodeWordReadTraceResult_noReadyCloseSuccessfulRead
          shape
          (SuccinctClose.blockStartOf blockSize
              (SuccinctClose.blockOfClose blockSize close) /
            SuccinctRank.machineWordBits shape.bpCode.length + 1)
    · apply WordRAM.TraceResult.bind_trace_forall
      · exact
          concreteBPNativeSuccinctRMQBpCodeWordReadTraceResult_noReadyCloseSuccessfulRead
            shape
            (SuccinctClose.blockStartOf blockSize
                (SuccinctClose.blockOfClose blockSize close) /
              SuccinctRank.machineWordBits shape.bpCode.length + 2)
      · apply WordRAM.TraceResult.map_trace_forall
        exact
          concreteBPNativeSuccinctRMQBpCodeWordReadTraceResult_noReadyCloseSuccessfulRead
            shape
            (SuccinctClose.blockStartOf blockSize
                (SuccinctClose.blockOfClose blockSize close) /
              SuccinctRank.machineWordBits shape.bpCode.length + 3)

private theorem
    concreteBPNativeSuccinctRMQLocalBPWindowBitsTraceResult_noReadyCloseSuccessfulRead
    (shape : Cartesian.CartesianShape) (blockSize close : Nat) :
    forall event,
      List.Mem event
        (SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPWindowBitsTraceResult
          shape blockSize close).trace ->
        concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead
          event := by
  unfold SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPWindowBitsTraceResult
  exact WordRAM.TraceResult.map_trace_forall
    concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead
    _ _
    (concreteBPNativeSuccinctRMQLocalBPBlockWordsTraceResult_noReadyCloseSuccessfulRead
      shape blockSize close)

private theorem
    concreteBPNativeSuccinctRMQFixedWidthSparseDenseEntryTable_readTraceResultRelabeled_noFiniteSmallInteriorSuccessfulRead
    {entries : List GenericSelect.SparseDenseSelectDenseLocalEntry}
    {fieldWidth : Nat}
    (table :
      GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable
        entries fieldWidth)
    (layout : GenericSelect.SparseDenseEntryTableTraceSegmentBases)
    (i : Nat)
    (hbaseOccurrence26 :
      forall segment,
        WordRAM.singletonSegmentMap layout.baseOccurrence layout.deadSegment
          segment ≠ 26)
    (hbaseOccurrence27 :
      forall segment,
        WordRAM.singletonSegmentMap layout.baseOccurrence layout.deadSegment
          segment ≠ 27)
    (hbaseWordIndex26 :
      forall segment,
        WordRAM.singletonSegmentMap layout.baseWordIndex layout.deadSegment
          segment ≠ 26)
    (hbaseWordIndex27 :
      forall segment,
        WordRAM.singletonSegmentMap layout.baseWordIndex layout.deadSegment
          segment ≠ 27)
    (hrankBefore26 :
      forall segment,
        WordRAM.singletonSegmentMap layout.rankBefore layout.deadSegment
          segment ≠ 26)
    (hrankBefore27 :
      forall segment,
        WordRAM.singletonSegmentMap layout.rankBefore layout.deadSegment
          segment ≠ 27)
    (hfirstOffset26 :
      forall segment,
        WordRAM.singletonSegmentMap layout.firstOffset layout.deadSegment
          segment ≠ 26)
    (hfirstOffset27 :
      forall segment,
        WordRAM.singletonSegmentMap layout.firstOffset layout.deadSegment
          segment ≠ 27) :
    forall event,
      List.Mem event
        (table.readTraceResultRelabeled layout i).trace ->
        concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead
          event := by
  unfold GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable.readTraceResultRelabeled
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      concreteBPNativeSuccinctRMQTraceResult_relabelReadSegmentsWith_noFiniteSmallInteriorSuccessfulRead
        (WordRAM.singletonSegmentMap layout.baseOccurrence
          layout.deadSegment)
        (WordRAM.TraceResult.ofResult
          ((table.baseOccurrenceTable.readProgram i).eval
            table.baseOccurrenceTable.wordRAMStore))
        hbaseOccurrence26 hbaseOccurrence27
  · apply WordRAM.TraceResult.bind_trace_forall
    · exact
        concreteBPNativeSuccinctRMQTraceResult_relabelReadSegmentsWith_noFiniteSmallInteriorSuccessfulRead
          (WordRAM.singletonSegmentMap layout.baseWordIndex
            layout.deadSegment)
          (WordRAM.TraceResult.ofResult
            ((table.baseWordIndexTable.readProgram i).eval
              table.baseWordIndexTable.wordRAMStore))
          hbaseWordIndex26 hbaseWordIndex27
    · apply WordRAM.TraceResult.bind_trace_forall
      · exact
          concreteBPNativeSuccinctRMQTraceResult_relabelReadSegmentsWith_noFiniteSmallInteriorSuccessfulRead
            (WordRAM.singletonSegmentMap layout.rankBefore
              layout.deadSegment)
            (WordRAM.TraceResult.ofResult
              ((table.rankBeforeTable.readProgram i).eval
                table.rankBeforeTable.wordRAMStore))
            hrankBefore26 hrankBefore27
      · apply WordRAM.TraceResult.map_trace_forall
        exact
          concreteBPNativeSuccinctRMQTraceResult_relabelReadSegmentsWith_noFiniteSmallInteriorSuccessfulRead
            (WordRAM.singletonSegmentMap layout.firstOffset
              layout.deadSegment)
            (WordRAM.TraceResult.ofResult
              ((table.firstOffsetTable.readProgram i).eval
                table.firstOffsetTable.wordRAMStore))
            hfirstOffset26 hfirstOffset27

private theorem
    concreteBPNativeSuccinctRMQRelativeOffsetReadTraceResultRelabeled_noFiniteSmallInteriorSuccessfulRead
    {entries : List Nat} {width : Nat}
    (segmentBase deadSegment : Nat)
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (base slot : Nat)
    (h26 :
      forall segment,
        WordRAM.singletonSegmentMap segmentBase deadSegment segment ≠ 26)
    (h27 :
      forall segment,
        WordRAM.singletonSegmentMap segmentBase deadSegment segment ≠ 27) :
    forall event,
      List.Mem event
        (GenericSelect.relativeOffsetReadTraceResultRelabeled
          segmentBase deadSegment table base slot).trace ->
        concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead
          event := by
  unfold GenericSelect.relativeOffsetReadTraceResultRelabeled
  apply WordRAM.TraceResult.map_trace_forall
  exact
    concreteBPNativeSuccinctRMQTraceResult_relabelReadSegmentsWith_noFiniteSmallInteriorSuccessfulRead
      (WordRAM.singletonSegmentMap segmentBase deadSegment)
      (WordRAM.TraceResult.ofResult
        ((table.readProgram slot).eval table.wordRAMStore))
      h26 h27

private theorem
    concreteBPNativeSuccinctRMQFixedWidthSparseDenseEntryTable_readTraceResultRelabeled_noReadyCloseSuccessfulRead
    {entries : List GenericSelect.SparseDenseSelectDenseLocalEntry}
    {fieldWidth : Nat}
    (table :
      GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable
        entries fieldWidth)
    (layout : GenericSelect.SparseDenseEntryTableTraceSegmentBases)
    (i : Nat)
    (hbaseOccurrence :
      concreteBPNativeSuccinctRMQSegmentMapAvoidsReadyClose
        (WordRAM.singletonSegmentMap layout.baseOccurrence
          layout.deadSegment))
    (hbaseWordIndex :
      concreteBPNativeSuccinctRMQSegmentMapAvoidsReadyClose
        (WordRAM.singletonSegmentMap layout.baseWordIndex
          layout.deadSegment))
    (hrankBefore :
      concreteBPNativeSuccinctRMQSegmentMapAvoidsReadyClose
        (WordRAM.singletonSegmentMap layout.rankBefore
          layout.deadSegment))
    (hfirstOffset :
      concreteBPNativeSuccinctRMQSegmentMapAvoidsReadyClose
        (WordRAM.singletonSegmentMap layout.firstOffset
          layout.deadSegment)) :
    forall event,
      List.Mem event
        (table.readTraceResultRelabeled layout i).trace ->
        concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead
          event := by
  unfold GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable.readTraceResultRelabeled
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      concreteBPNativeSuccinctRMQTraceResult_relabelReadSegmentsWith_noReadyCloseSuccessfulRead
        (WordRAM.singletonSegmentMap layout.baseOccurrence
          layout.deadSegment)
        (WordRAM.TraceResult.ofResult
          ((table.baseOccurrenceTable.readProgram i).eval
            table.baseOccurrenceTable.wordRAMStore))
        hbaseOccurrence
  · apply WordRAM.TraceResult.bind_trace_forall
    · exact
        concreteBPNativeSuccinctRMQTraceResult_relabelReadSegmentsWith_noReadyCloseSuccessfulRead
          (WordRAM.singletonSegmentMap layout.baseWordIndex
            layout.deadSegment)
          (WordRAM.TraceResult.ofResult
            ((table.baseWordIndexTable.readProgram i).eval
              table.baseWordIndexTable.wordRAMStore))
          hbaseWordIndex
    · apply WordRAM.TraceResult.bind_trace_forall
      · exact
          concreteBPNativeSuccinctRMQTraceResult_relabelReadSegmentsWith_noReadyCloseSuccessfulRead
            (WordRAM.singletonSegmentMap layout.rankBefore
              layout.deadSegment)
            (WordRAM.TraceResult.ofResult
              ((table.rankBeforeTable.readProgram i).eval
                table.rankBeforeTable.wordRAMStore))
            hrankBefore
      · apply WordRAM.TraceResult.map_trace_forall
        exact
          concreteBPNativeSuccinctRMQTraceResult_relabelReadSegmentsWith_noReadyCloseSuccessfulRead
            (WordRAM.singletonSegmentMap layout.firstOffset
              layout.deadSegment)
            (WordRAM.TraceResult.ofResult
              ((table.firstOffsetTable.readProgram i).eval
                table.firstOffsetTable.wordRAMStore))
            hfirstOffset

private theorem
    concreteBPNativeSuccinctRMQRelativeOffsetReadTraceResultRelabeled_noReadyCloseSuccessfulRead
    {entries : List Nat} {width : Nat}
    (segmentBase deadSegment : Nat)
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (base slot : Nat)
    (havoid :
      concreteBPNativeSuccinctRMQSegmentMapAvoidsReadyClose
        (WordRAM.singletonSegmentMap segmentBase deadSegment)) :
    forall event,
      List.Mem event
        (GenericSelect.relativeOffsetReadTraceResultRelabeled
          segmentBase deadSegment table base slot).trace ->
        concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead
          event := by
  unfold GenericSelect.relativeOffsetReadTraceResultRelabeled
  apply WordRAM.TraceResult.map_trace_forall
  exact
    concreteBPNativeSuccinctRMQTraceResult_relabelReadSegmentsWith_noReadyCloseSuccessfulRead
      (WordRAM.singletonSegmentMap segmentBase deadSegment)
      (WordRAM.TraceResult.ofResult
        ((table.readProgram slot).eval table.wordRAMStore))
      havoid

private theorem
    concreteBPNativeSuccinctRMQSparseExceptionDirectory_readTraceResultRelabeled_noFiniteSmallInteriorSuccessfulRead
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      GenericSelect.SparseExceptionDirectory
        bits target rankSuperOverhead rankBlockOverhead)
    (layout : GenericSelect.SparseExceptionDirectoryTraceSegmentBases)
    (base localSlot localOccurrence : Nat)
    (hrank26 :
      forall segment,
        WordRAM.tripleSegmentMap layout.rankBase layout.deadSegment segment ≠
          26)
    (hrank27 :
      forall segment,
        WordRAM.tripleSegmentMap layout.rankBase layout.deadSegment segment ≠
          27)
    (hrelative26 :
      forall segment,
        WordRAM.singletonSegmentMap layout.relativeBase layout.deadSegment
          segment ≠ 26)
    (hrelative27 :
      forall segment,
        WordRAM.singletonSegmentMap layout.relativeBase layout.deadSegment
          segment ≠ 27) :
    forall event,
      List.Mem event
        (directory.readTraceResultRelabeled
          layout base localSlot localOccurrence).trace ->
        concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead
          event := by
  unfold GenericSelect.SparseExceptionDirectory.readTraceResultRelabeled
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      concreteBPNativeSuccinctRMQTraceResult_relabelReadSegmentsWith_noFiniteSmallInteriorSuccessfulRead
        (WordRAM.tripleSegmentMap layout.rankBase layout.deadSegment)
        (directory.rankData.rankTraceResult true localSlot)
        hrank26 hrank27
  · exact
      concreteBPNativeSuccinctRMQRelativeOffsetReadTraceResultRelabeled_noFiniteSmallInteriorSuccessfulRead
        layout.relativeBase layout.deadSegment directory.relativeTable base
        (GenericSelect.relativeSplitSelectSparseCompactSlot
          (directory.rankData.rankTraceResult true localSlot).value
          localOccurrence directory.localStride)
        hrelative26 hrelative27

private theorem
    concreteBPNativeSuccinctRMQSparseExceptionDirectory_readTraceResultRelabeled_noReadyCloseSuccessfulRead
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      GenericSelect.SparseExceptionDirectory
        bits target rankSuperOverhead rankBlockOverhead)
    (layout : GenericSelect.SparseExceptionDirectoryTraceSegmentBases)
    (base localSlot localOccurrence : Nat)
    (hrank :
      concreteBPNativeSuccinctRMQSegmentMapAvoidsReadyClose
        (WordRAM.tripleSegmentMap layout.rankBase layout.deadSegment))
    (hrelative :
      concreteBPNativeSuccinctRMQSegmentMapAvoidsReadyClose
        (WordRAM.singletonSegmentMap layout.relativeBase
          layout.deadSegment)) :
    forall event,
      List.Mem event
        (directory.readTraceResultRelabeled
          layout base localSlot localOccurrence).trace ->
        concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead
          event := by
  unfold GenericSelect.SparseExceptionDirectory.readTraceResultRelabeled
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      concreteBPNativeSuccinctRMQTraceResult_relabelReadSegmentsWith_noReadyCloseSuccessfulRead
        (WordRAM.tripleSegmentMap layout.rankBase layout.deadSegment)
        (directory.rankData.rankTraceResult true localSlot)
        hrank
  · exact
      concreteBPNativeSuccinctRMQRelativeOffsetReadTraceResultRelabeled_noReadyCloseSuccessfulRead
        layout.relativeBase layout.deadSegment directory.relativeTable base
        (GenericSelect.relativeSplitSelectSparseCompactSlot
          (directory.rankData.rankTraceResult true localSlot).value
          localOccurrence directory.localStride)
        hrelative

private theorem
    concreteBPNativeSelectCloseTraceResultRelabeled_noFiniteSmallInteriorSuccessfulRead
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    forall event,
      List.Mem event
        ((GenericSelect.sparseExceptionSelectData shape.bpCode false)
          |>.selectTraceResultRelabeled
            concreteBPNativeSelectCloseTraceSegmentLayout idx).trace ->
        concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead
          event := by
  let data := GenericSelect.sparseExceptionSelectData shape.bpCode false
  change forall event,
      event ∈
          (data.selectTraceResultRelabeled
            concreteBPNativeSelectCloseTraceSegmentLayout idx).trace ->
        concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead
          event
  apply
    GenericSelect.SparseExceptionSelectData.selectTraceResultRelabeled_trace_forall
      data concreteBPNativeSelectCloseTraceSegmentLayout idx
      concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead
  · intro slot event hmem
    exact
      concreteBPNativeSuccinctRMQFixedWidthSparseDenseEntryTable_readTraceResultRelabeled_noFiniteSmallInteriorSuccessfulRead
        data.superTable concreteBPNativeSelectCloseTraceSegmentLayout.superTable
        slot
        (concreteBPNativeSuccinctRMQSingletonSegmentMap_ne_of_bases_ne
          concreteBPNativeSelectCloseTraceSegmentLayout.superTable.baseOccurrence
          concreteBPNativeSelectCloseTraceSegmentLayout.superTable.deadSegment
          (by decide) (by decide))
        (concreteBPNativeSuccinctRMQSingletonSegmentMap_ne27_of_bases_ne
          concreteBPNativeSelectCloseTraceSegmentLayout.superTable.baseOccurrence
          concreteBPNativeSelectCloseTraceSegmentLayout.superTable.deadSegment
          (by decide) (by decide))
        (concreteBPNativeSuccinctRMQSingletonSegmentMap_ne_of_bases_ne
          concreteBPNativeSelectCloseTraceSegmentLayout.superTable.baseWordIndex
          concreteBPNativeSelectCloseTraceSegmentLayout.superTable.deadSegment
          (by decide) (by decide))
        (concreteBPNativeSuccinctRMQSingletonSegmentMap_ne27_of_bases_ne
          concreteBPNativeSelectCloseTraceSegmentLayout.superTable.baseWordIndex
          concreteBPNativeSelectCloseTraceSegmentLayout.superTable.deadSegment
          (by decide) (by decide))
        (concreteBPNativeSuccinctRMQSingletonSegmentMap_ne_of_bases_ne
          concreteBPNativeSelectCloseTraceSegmentLayout.superTable.rankBefore
          concreteBPNativeSelectCloseTraceSegmentLayout.superTable.deadSegment
          (by decide) (by decide))
        (concreteBPNativeSuccinctRMQSingletonSegmentMap_ne27_of_bases_ne
          concreteBPNativeSelectCloseTraceSegmentLayout.superTable.rankBefore
          concreteBPNativeSelectCloseTraceSegmentLayout.superTable.deadSegment
          (by decide) (by decide))
        (concreteBPNativeSuccinctRMQSingletonSegmentMap_ne_of_bases_ne
          concreteBPNativeSelectCloseTraceSegmentLayout.superTable.firstOffset
          concreteBPNativeSelectCloseTraceSegmentLayout.superTable.deadSegment
          (by decide) (by decide))
        (concreteBPNativeSuccinctRMQSingletonSegmentMap_ne27_of_bases_ne
          concreteBPNativeSelectCloseTraceSegmentLayout.superTable.firstOffset
          concreteBPNativeSelectCloseTraceSegmentLayout.superTable.deadSegment
          (by decide) (by decide))
        event hmem
  · intro slot event hmem
    exact
      concreteBPNativeSuccinctRMQTraceResult_relabelReadSegmentsWith_noFiniteSmallInteriorSuccessfulRead
        (WordRAM.tripleSegmentMap
          concreteBPNativeSelectCloseTraceSegmentLayout.longFlagRankBase
          concreteBPNativeSelectCloseTraceSegmentLayout.deadSegment)
        (data.longFlagRankData.rankTraceResult true slot)
        (concreteBPNativeSuccinctRMQTripleSegmentMap_ne_of_bases_ne
          concreteBPNativeSelectCloseTraceSegmentLayout.longFlagRankBase
          concreteBPNativeSelectCloseTraceSegmentLayout.deadSegment
          (by decide) (by decide) (by decide) (by decide))
        (concreteBPNativeSuccinctRMQTripleSegmentMap_ne27_of_bases_ne
          concreteBPNativeSelectCloseTraceSegmentLayout.longFlagRankBase
          concreteBPNativeSelectCloseTraceSegmentLayout.deadSegment
          (by decide) (by decide) (by decide) (by decide))
        event hmem
  · intro base slot event hmem
    exact
      concreteBPNativeSuccinctRMQRelativeOffsetReadTraceResultRelabeled_noFiniteSmallInteriorSuccessfulRead
        concreteBPNativeSelectCloseTraceSegmentLayout.longRelativeBase
        concreteBPNativeSelectCloseTraceSegmentLayout.deadSegment
        data.longSuperRelativeTable base slot
        (concreteBPNativeSuccinctRMQSingletonSegmentMap_ne_of_bases_ne
          concreteBPNativeSelectCloseTraceSegmentLayout.longRelativeBase
          concreteBPNativeSelectCloseTraceSegmentLayout.deadSegment
          (by decide) (by decide))
        (concreteBPNativeSuccinctRMQSingletonSegmentMap_ne27_of_bases_ne
          concreteBPNativeSelectCloseTraceSegmentLayout.longRelativeBase
          concreteBPNativeSelectCloseTraceSegmentLayout.deadSegment
          (by decide) (by decide))
        event hmem
  · intro slot event hmem
    exact
      concreteBPNativeSuccinctRMQFixedWidthSparseDenseEntryTable_readTraceResultRelabeled_noFiniteSmallInteriorSuccessfulRead
        data.localTable concreteBPNativeSelectCloseTraceSegmentLayout.localTable
        slot
        (concreteBPNativeSuccinctRMQSingletonSegmentMap_ne_of_bases_ne
          concreteBPNativeSelectCloseTraceSegmentLayout.localTable.baseOccurrence
          concreteBPNativeSelectCloseTraceSegmentLayout.localTable.deadSegment
          (by decide) (by decide))
        (concreteBPNativeSuccinctRMQSingletonSegmentMap_ne27_of_bases_ne
          concreteBPNativeSelectCloseTraceSegmentLayout.localTable.baseOccurrence
          concreteBPNativeSelectCloseTraceSegmentLayout.localTable.deadSegment
          (by decide) (by decide))
        (concreteBPNativeSuccinctRMQSingletonSegmentMap_ne_of_bases_ne
          concreteBPNativeSelectCloseTraceSegmentLayout.localTable.baseWordIndex
          concreteBPNativeSelectCloseTraceSegmentLayout.localTable.deadSegment
          (by decide) (by decide))
        (concreteBPNativeSuccinctRMQSingletonSegmentMap_ne27_of_bases_ne
          concreteBPNativeSelectCloseTraceSegmentLayout.localTable.baseWordIndex
          concreteBPNativeSelectCloseTraceSegmentLayout.localTable.deadSegment
          (by decide) (by decide))
        (concreteBPNativeSuccinctRMQSingletonSegmentMap_ne_of_bases_ne
          concreteBPNativeSelectCloseTraceSegmentLayout.localTable.rankBefore
          concreteBPNativeSelectCloseTraceSegmentLayout.localTable.deadSegment
          (by decide) (by decide))
        (concreteBPNativeSuccinctRMQSingletonSegmentMap_ne27_of_bases_ne
          concreteBPNativeSelectCloseTraceSegmentLayout.localTable.rankBefore
          concreteBPNativeSelectCloseTraceSegmentLayout.localTable.deadSegment
          (by decide) (by decide))
        (concreteBPNativeSuccinctRMQSingletonSegmentMap_ne_of_bases_ne
          concreteBPNativeSelectCloseTraceSegmentLayout.localTable.firstOffset
          concreteBPNativeSelectCloseTraceSegmentLayout.localTable.deadSegment
          (by decide) (by decide))
        (concreteBPNativeSuccinctRMQSingletonSegmentMap_ne27_of_bases_ne
          concreteBPNativeSelectCloseTraceSegmentLayout.localTable.firstOffset
          concreteBPNativeSelectCloseTraceSegmentLayout.localTable.deadSegment
          (by decide) (by decide))
        event hmem
  · intro base localSlot localOccurrence event hmem
    exact
      concreteBPNativeSuccinctRMQSparseExceptionDirectory_readTraceResultRelabeled_noFiniteSmallInteriorSuccessfulRead
        data.sparseDirectory
        concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory
        base localSlot localOccurrence
        (concreteBPNativeSuccinctRMQTripleSegmentMap_ne_of_bases_ne
          concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.rankBase
          concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.deadSegment
          (by decide) (by decide) (by decide) (by decide))
        (concreteBPNativeSuccinctRMQTripleSegmentMap_ne27_of_bases_ne
          concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.rankBase
          concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.deadSegment
          (by decide) (by decide) (by decide) (by decide))
        (concreteBPNativeSuccinctRMQSingletonSegmentMap_ne_of_bases_ne
          concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.relativeBase
          concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.deadSegment
          (by decide) (by decide))
        (concreteBPNativeSuccinctRMQSingletonSegmentMap_ne27_of_bases_ne
          concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.relativeBase
          concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.deadSegment
          (by decide) (by decide))
        event hmem
  · intro basePosition baseOccurrence q event hmem
    exact
      concreteBPNativeSuccinctRMQTraceResult_relabelReadSegmentsWith_noFiniteSmallInteriorSuccessfulRead
        (WordRAM.singletonSegmentMap
          concreteBPNativeSelectCloseTraceSegmentLayout.bitWordBase
          concreteBPNativeSelectCloseTraceSegmentLayout.deadSegment)
        (GenericSelect.denseTwoWordSelectTraceResult false data.bitWords
          basePosition baseOccurrence q)
        (concreteBPNativeSuccinctRMQSingletonSegmentMap_ne_of_bases_ne
          concreteBPNativeSelectCloseTraceSegmentLayout.bitWordBase
          concreteBPNativeSelectCloseTraceSegmentLayout.deadSegment
          (by decide) (by decide))
        (concreteBPNativeSuccinctRMQSingletonSegmentMap_ne27_of_bases_ne
          concreteBPNativeSelectCloseTraceSegmentLayout.bitWordBase
          concreteBPNativeSelectCloseTraceSegmentLayout.deadSegment
          (by decide) (by decide))
        event hmem

private theorem
    concreteBPNativeSelectCloseTraceResultRelabeled_noReadyCloseSuccessfulRead
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    forall event,
      List.Mem event
        ((GenericSelect.sparseExceptionSelectData shape.bpCode false)
          |>.selectTraceResultRelabeled
            concreteBPNativeSelectCloseTraceSegmentLayout idx).trace ->
        concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead
          event := by
  let data := GenericSelect.sparseExceptionSelectData shape.bpCode false
  change forall event,
      event ∈
          (data.selectTraceResultRelabeled
            concreteBPNativeSelectCloseTraceSegmentLayout idx).trace ->
        concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead
          event
  apply
    GenericSelect.SparseExceptionSelectData.selectTraceResultRelabeled_trace_forall
      data concreteBPNativeSelectCloseTraceSegmentLayout idx
      concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead
  · intro slot event hmem
    exact
      concreteBPNativeSuccinctRMQFixedWidthSparseDenseEntryTable_readTraceResultRelabeled_noReadyCloseSuccessfulRead
        data.superTable concreteBPNativeSelectCloseTraceSegmentLayout.superTable
        slot
        (concreteBPNativeSuccinctRMQSingletonSegmentMap_avoidsReadyClose_of_outside
          concreteBPNativeSelectCloseTraceSegmentLayout.superTable.baseOccurrence
          concreteBPNativeSelectCloseTraceSegmentLayout.superTable.deadSegment
          (by decide) (by decide))
        (concreteBPNativeSuccinctRMQSingletonSegmentMap_avoidsReadyClose_of_outside
          concreteBPNativeSelectCloseTraceSegmentLayout.superTable.baseWordIndex
          concreteBPNativeSelectCloseTraceSegmentLayout.superTable.deadSegment
          (by decide) (by decide))
        (concreteBPNativeSuccinctRMQSingletonSegmentMap_avoidsReadyClose_of_outside
          concreteBPNativeSelectCloseTraceSegmentLayout.superTable.rankBefore
          concreteBPNativeSelectCloseTraceSegmentLayout.superTable.deadSegment
          (by decide) (by decide))
        (concreteBPNativeSuccinctRMQSingletonSegmentMap_avoidsReadyClose_of_outside
          concreteBPNativeSelectCloseTraceSegmentLayout.superTable.firstOffset
          concreteBPNativeSelectCloseTraceSegmentLayout.superTable.deadSegment
          (by decide) (by decide))
        event hmem
  · intro slot event hmem
    exact
      concreteBPNativeSuccinctRMQTraceResult_relabelReadSegmentsWith_noReadyCloseSuccessfulRead
        (WordRAM.tripleSegmentMap
          concreteBPNativeSelectCloseTraceSegmentLayout.longFlagRankBase
          concreteBPNativeSelectCloseTraceSegmentLayout.deadSegment)
        (data.longFlagRankData.rankTraceResult true slot)
        (concreteBPNativeSuccinctRMQTripleSegmentMap_avoidsReadyClose_of_outside
          concreteBPNativeSelectCloseTraceSegmentLayout.longFlagRankBase
          concreteBPNativeSelectCloseTraceSegmentLayout.deadSegment
          (by decide) (by decide) (by decide) (by decide))
        event hmem
  · intro base slot event hmem
    exact
      concreteBPNativeSuccinctRMQRelativeOffsetReadTraceResultRelabeled_noReadyCloseSuccessfulRead
        concreteBPNativeSelectCloseTraceSegmentLayout.longRelativeBase
        concreteBPNativeSelectCloseTraceSegmentLayout.deadSegment
        data.longSuperRelativeTable base slot
        (concreteBPNativeSuccinctRMQSingletonSegmentMap_avoidsReadyClose_of_outside
          concreteBPNativeSelectCloseTraceSegmentLayout.longRelativeBase
          concreteBPNativeSelectCloseTraceSegmentLayout.deadSegment
          (by decide) (by decide))
        event hmem
  · intro slot event hmem
    exact
      concreteBPNativeSuccinctRMQFixedWidthSparseDenseEntryTable_readTraceResultRelabeled_noReadyCloseSuccessfulRead
        data.localTable concreteBPNativeSelectCloseTraceSegmentLayout.localTable
        slot
        (concreteBPNativeSuccinctRMQSingletonSegmentMap_avoidsReadyClose_of_outside
          concreteBPNativeSelectCloseTraceSegmentLayout.localTable.baseOccurrence
          concreteBPNativeSelectCloseTraceSegmentLayout.localTable.deadSegment
          (by decide) (by decide))
        (concreteBPNativeSuccinctRMQSingletonSegmentMap_avoidsReadyClose_of_outside
          concreteBPNativeSelectCloseTraceSegmentLayout.localTable.baseWordIndex
          concreteBPNativeSelectCloseTraceSegmentLayout.localTable.deadSegment
          (by decide) (by decide))
        (concreteBPNativeSuccinctRMQSingletonSegmentMap_avoidsReadyClose_of_outside
          concreteBPNativeSelectCloseTraceSegmentLayout.localTable.rankBefore
          concreteBPNativeSelectCloseTraceSegmentLayout.localTable.deadSegment
          (by decide) (by decide))
        (concreteBPNativeSuccinctRMQSingletonSegmentMap_avoidsReadyClose_of_outside
          concreteBPNativeSelectCloseTraceSegmentLayout.localTable.firstOffset
          concreteBPNativeSelectCloseTraceSegmentLayout.localTable.deadSegment
          (by decide) (by decide))
        event hmem
  · intro base localSlot localOccurrence event hmem
    exact
      concreteBPNativeSuccinctRMQSparseExceptionDirectory_readTraceResultRelabeled_noReadyCloseSuccessfulRead
        data.sparseDirectory
        concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory
        base localSlot localOccurrence
        (concreteBPNativeSuccinctRMQTripleSegmentMap_avoidsReadyClose_of_outside
          concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.rankBase
          concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.deadSegment
          (by decide) (by decide) (by decide) (by decide))
        (concreteBPNativeSuccinctRMQSingletonSegmentMap_avoidsReadyClose_of_outside
          concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.relativeBase
          concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.deadSegment
          (by decide) (by decide))
        event hmem
  · intro basePosition baseOccurrence q event hmem
    exact
      concreteBPNativeSuccinctRMQTraceResult_relabelReadSegmentsWith_noReadyCloseSuccessfulRead
        (WordRAM.singletonSegmentMap
          concreteBPNativeSelectCloseTraceSegmentLayout.bitWordBase
          concreteBPNativeSelectCloseTraceSegmentLayout.deadSegment)
        (GenericSelect.denseTwoWordSelectTraceResult false data.bitWords
          basePosition baseOccurrence q)
        (concreteBPNativeSuccinctRMQSingletonSegmentMap_avoidsReadyClose_of_outside
          concreteBPNativeSelectCloseTraceSegmentLayout.bitWordBase
          concreteBPNativeSelectCloseTraceSegmentLayout.deadSegment
          (by decide) (by decide))
        event hmem

/--
Close-select trace with payload-read segments in the final global layout
(B3: the chunked select-close trace against the canonical global store).
The packed BP-code reads remain at segment `0` so the final query can share
one BP-code payload segment instead of copying the code per component;
chunk-table reads land at segment `21` and select-table reads at segment
`22`.
-/
def concreteBPNativeSelectCloseGlobalWordTraceResult
    (shape : Cartesian.CartesianShape)
    (idx : Nat) : WordRAM.TraceResult (Option Nat) :=
  concreteBPNativeChunkedSelectCloseGlobalWordTraceResult shape idx

theorem concreteBPNativeSelectCloseGlobalWordTraceResult_refines_interpretedCosted
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    (concreteBPNativeSelectCloseGlobalWordTraceResult shape idx).toCosted =
      concreteBPNativeSelectCloseInterpretedCosted shape idx :=
  concreteBPNativeChunkedSelectCloseGlobalWordTraceResult_refines shape idx

theorem concreteBPNativeSelectCloseGlobalWordTraceResult_matchesReadStore
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    forall event,
      event ∈
          (concreteBPNativeSelectCloseGlobalWordTraceResult shape idx).trace ->
        event.matchesReadStore
          (concreteBPNativeSuccinctRMQGlobalReadStore shape) :=
  concreteBPNativeChunkedSelectCloseGlobalWordTraceResult_matchesReadStore
    shape idx

theorem concreteBPNativeSelectCloseGlobalWordTraceResult_no_syntheticCostOnlyPrimitive
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    forall event,
      event ∈
          (concreteBPNativeSelectCloseGlobalWordTraceResult shape idx).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive :=
  concreteBPNativeChunkedSelectCloseGlobalWordTraceResult_no_syntheticCostOnlyPrimitive
    shape idx

/-- The canonical global store resolves no words at the retired ready-close
and finite-small interior segments `24`--`27`. -/
private theorem concreteBPNativeSuccinctRMQGlobalReadStore_retiredTail_none
    (shape : Cartesian.CartesianShape) (index : Nat) :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 24 index =
        none /\
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 25 index =
        none /\
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 26 index =
        none /\
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 27 index =
        none := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [concreteBPNativeSuccinctRMQGlobalReadStore]

/-- Any event matching the canonical global store has no successful read at
the retired finite-small interior segments. -/
private theorem
    concreteBPNativeSuccinctRMQGlobalStoreMatch_noFiniteSmallInteriorSuccessfulRead
    (shape : Cartesian.CartesianShape) {event : WordRAM.TraceEvent}
    (hmatch :
      event.matchesReadStore
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)) :
    concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead
      event := by
  cases event with
  | readWord segment index word? =>
      cases word? with
      | none =>
          simp [concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead]
      | some word =>
          have hmatch' :
              (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
                  segment index = some word := hmatch
          have hnot26 : segment ≠ 26 := by
            intro hseg
            subst hseg
            have hnone :=
              (concreteBPNativeSuccinctRMQGlobalReadStore_retiredTail_none
                shape index).2.2.1
            rw [hmatch'] at hnone
            exact Option.noConfusion hnone
          have hnot27 : segment ≠ 27 := by
            intro hseg
            subst hseg
            have hnone :=
              (concreteBPNativeSuccinctRMQGlobalReadStore_retiredTail_none
                shape index).2.2.2
            rw [hmatch'] at hnone
            exact Option.noConfusion hnone
          simp [concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead,
            hnot26, hnot27]
  | wordRank target limit result => trivial
  | wordSelect target occurrence result => trivial
  | syntheticCostOnlyPrimitive => trivial

/-- Any event matching the canonical global store has no successful read at
the retired ready-close segments. -/
private theorem
    concreteBPNativeSuccinctRMQGlobalStoreMatch_noReadyCloseSuccessfulRead
    (shape : Cartesian.CartesianShape) {event : WordRAM.TraceEvent}
    (hmatch :
      event.matchesReadStore
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)) :
    concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead
      event := by
  cases event with
  | readWord segment index word? =>
      cases word? with
      | none =>
          simp [concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead]
      | some word =>
          have hmatch' :
              (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
                  segment index = some word := hmatch
          have hnot24 : segment ≠ 24 := by
            intro hseg
            subst hseg
            have hnone :=
              (concreteBPNativeSuccinctRMQGlobalReadStore_retiredTail_none
                shape index).1
            rw [hmatch'] at hnone
            exact Option.noConfusion hnone
          have hnot25 : segment ≠ 25 := by
            intro hseg
            subst hseg
            have hnone :=
              (concreteBPNativeSuccinctRMQGlobalReadStore_retiredTail_none
                shape index).2.1
            rw [hmatch'] at hnone
            exact Option.noConfusion hnone
          simp [concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead,
            hnot24, hnot25]
  | wordRank target limit result => trivial
  | wordSelect target occurrence result => trivial
  | syntheticCostOnlyPrimitive => trivial

private theorem
    concreteBPNativeSelectCloseGlobalWordTraceResult_noFiniteSmallInteriorSuccessfulRead
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    forall event,
      List.Mem event
        (concreteBPNativeSelectCloseGlobalWordTraceResult shape idx).trace ->
        concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead
          event := by
  intro event hmem
  exact
    concreteBPNativeSuccinctRMQGlobalStoreMatch_noFiniteSmallInteriorSuccessfulRead
      shape
      (concreteBPNativeSelectCloseGlobalWordTraceResult_matchesReadStore
        shape idx event hmem)

private theorem
    concreteBPNativeSelectCloseGlobalWordTraceResult_noReadyCloseSuccessfulRead
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    forall event,
      List.Mem event
        (concreteBPNativeSelectCloseGlobalWordTraceResult shape idx).trace ->
        concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead
          event := by
  intro event hmem
  exact
    concreteBPNativeSuccinctRMQGlobalStoreMatch_noReadyCloseSuccessfulRead
      shape
      (concreteBPNativeSelectCloseGlobalWordTraceResult_matchesReadStore
        shape idx event hmem)

/--
Final false-rank trace at a caller-supplied global segment base (B3: the
chunked rank-close seed trace against the base-parameterized seed store;
sample/word reads at `rankSegmentBase .. rankSegmentBase + 2`, chunk-table
reads at `rankSegmentBase + 4`, which the canonical base `17` places at the
counted fringe chunk segment `21`).
-/
def concreteBPNativeRankCloseWordTraceResultAtSegment
    (shape : Cartesian.CartesianShape)
    (rankSegmentBase pos : Nat) : WordRAM.TraceResult Nat :=
  (builtRelativeSplitBPCloseRankData shape)
    |>.bpChunkedRankTraceResultWithStore
      (concreteBPNativeChunkedRankCloseSeedReadStore shape rankSegmentBase)
      rankSegmentBase (rankSegmentBase + 1) (rankSegmentBase + 2)
      (rankSegmentBase + 4)
      (SuccinctClose.bpFringeChunkBits shape.bpCode.length) false pos

theorem concreteBPNativeRankCloseWordTraceResultAtSegment_refines_interpretedCosted
    (shape : Cartesian.CartesianShape)
    (rankSegmentBase pos : Nat) :
    (concreteBPNativeRankCloseWordTraceResultAtSegment
      shape rankSegmentBase pos).toCosted =
      concreteBPNativeRankCloseInterpretedCosted shape pos :=
  (builtRelativeSplitBPCloseRankData
      shape).bpChunkedRankTraceResultWithStore_toCosted_of_agree
    (concreteBPNativeChunkedRankCloseSeedReadStore_super
      shape rankSegmentBase)
    (concreteBPNativeChunkedRankCloseSeedReadStore_block
      shape rankSegmentBase)
    (concreteBPNativeChunkedRankCloseSeedReadStore_word
      shape rankSegmentBase)
    (concreteBPNativeChunkedRankCloseSeedReadStore_chunk
      shape rankSegmentBase)
    pos

/-- Real chunked trace for the final false-rank leg at the local segment
base `0` (B3: sample/word reads at `0..2`, chunk-table reads at `4`). -/
def concreteBPNativeRankCloseWordTraceResult
    (shape : Cartesian.CartesianShape)
    (pos : Nat) : WordRAM.TraceResult Nat :=
  concreteBPNativeRankCloseWordTraceResultAtSegment shape 0 pos

theorem concreteBPNativeRankCloseWordTraceResult_refines_interpretedCosted
    (shape : Cartesian.CartesianShape) (pos : Nat) :
    (concreteBPNativeRankCloseWordTraceResult shape pos).toCosted =
      concreteBPNativeRankCloseInterpretedCosted shape pos :=
  concreteBPNativeRankCloseWordTraceResultAtSegment_refines_interpretedCosted
    shape 0 pos

/-- At the canonical base `17`, the swapped rank-close trace is exactly the
chunked rank-close global word trace against the canonical store. -/
theorem concreteBPNativeRankCloseWordTraceResultAtSegment_canonical_eq
    (shape : Cartesian.CartesianShape) (pos : Nat) :
    concreteBPNativeRankCloseWordTraceResultAtSegment shape
        concreteBPNativeRankCloseTraceSegmentBase pos =
      concreteBPNativeChunkedRankCloseGlobalWordTraceResult shape pos := by
  unfold concreteBPNativeRankCloseWordTraceResultAtSegment
    concreteBPNativeChunkedRankCloseGlobalWordTraceResult
  apply
    (builtRelativeSplitBPCloseRankData
        shape).bpChunkedRankTraceResultWithStore_store_parametric
  · intro address
    rw [concreteBPNativeChunkedRankCloseSeedReadStore_super shape
      concreteBPNativeRankCloseTraceSegmentBase address]
    rw [concreteBPNativeSuccinctRMQGlobalReadStore_rankCloseSuper shape
      address]
  · intro address
    rw [concreteBPNativeChunkedRankCloseSeedReadStore_block shape
      concreteBPNativeRankCloseTraceSegmentBase address]
    rw [concreteBPNativeSuccinctRMQGlobalReadStore_rankCloseBlock shape
      address]
  · intro address
    rw [concreteBPNativeChunkedRankCloseSeedReadStore_word shape
      concreteBPNativeRankCloseTraceSegmentBase address]
    rw [concreteBPNativeSuccinctRMQGlobalReadStore_rankCloseWord shape
      address]
  · intro address
    rw [concreteBPNativeChunkedRankCloseSeedReadStore_chunk shape
      concreteBPNativeRankCloseTraceSegmentBase address]
    rw [show concreteBPNativeRankCloseTraceSegmentBase + 4 =
      concreteBPNativeFringeChunkTraceSegment from rfl]
    rw [concreteBPNativeSuccinctRMQGlobalReadStore_fringeChunkTable shape
      address]

theorem concreteBPNativeRankCloseCanonicalGlobalWordTraceResult_matchesReadStore
    (shape : Cartesian.CartesianShape) (pos : Nat) :
    forall event,
      event ∈
          (concreteBPNativeRankCloseWordTraceResultAtSegment
            shape concreteBPNativeRankCloseTraceSegmentBase pos).trace ->
        event.matchesReadStore
          (concreteBPNativeSuccinctRMQGlobalReadStore shape) := by
  intro event hmem
  rw [concreteBPNativeRankCloseWordTraceResultAtSegment_canonical_eq]
    at hmem
  exact
    concreteBPNativeChunkedRankCloseGlobalWordTraceResult_matchesReadStore
      shape pos event hmem

theorem concreteBPNativeRankCloseGlobalWordTraceResult_no_syntheticCostOnlyPrimitive
    (shape : Cartesian.CartesianShape) (pos : Nat) :
    forall event,
      event ∈
          (concreteBPNativeRankCloseWordTraceResultAtSegment
            shape concreteBPNativeRankCloseTraceSegmentBase pos).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive :=
  (builtRelativeSplitBPCloseRankData
      shape).bpChunkedRankTraceResultWithStore_no_syntheticCostOnlyPrimitive
    (concreteBPNativeChunkedRankCloseSeedReadStore shape
      concreteBPNativeRankCloseTraceSegmentBase)
    concreteBPNativeRankCloseTraceSegmentBase
    (concreteBPNativeRankCloseTraceSegmentBase + 1)
    (concreteBPNativeRankCloseTraceSegmentBase + 2)
    (concreteBPNativeRankCloseTraceSegmentBase + 4)
    (SuccinctClose.bpFringeChunkBits shape.bpCode.length) false pos

private theorem
    concreteBPNativeSuccinctRMQRankCloseGlobalWordTraceResult_noFiniteSmallInteriorSuccessfulRead
    (shape : Cartesian.CartesianShape) (pos : Nat) :
    forall event,
      List.Mem event
        (concreteBPNativeRankCloseWordTraceResultAtSegment
          shape concreteBPNativeRankCloseTraceSegmentBase pos).trace ->
        concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead
          event := by
  intro event hmem
  exact
    concreteBPNativeSuccinctRMQGlobalStoreMatch_noFiniteSmallInteriorSuccessfulRead
      shape
      (concreteBPNativeRankCloseCanonicalGlobalWordTraceResult_matchesReadStore
        shape pos event hmem)

private theorem
    concreteBPNativeSuccinctRMQRankCloseGlobalWordTraceResult_noReadyCloseSuccessfulRead
    (shape : Cartesian.CartesianShape) (pos : Nat) :
    forall event,
      List.Mem event
        (concreteBPNativeRankCloseWordTraceResultAtSegment
          shape concreteBPNativeRankCloseTraceSegmentBase pos).trace ->
        concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead
          event := by
  intro event hmem
  exact
    concreteBPNativeSuccinctRMQGlobalStoreMatch_noReadyCloseSuccessfulRead
      shape
      (concreteBPNativeRankCloseCanonicalGlobalWordTraceResult_matchesReadStore
        shape pos event hmem)

private theorem
    concreteBPNativeInteriorSummaryMinCandidateTraceResult_noFiniteSmallInteriorSuccessfulRead
    (shape : Cartesian.CartesianShape) (block : Nat) :
    forall event,
      List.Mem event
          ((SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable_canonical
            shape).minCandidateTraceResultAtSegments
              concreteBPNativeInteriorTraceSegments.summary block).trace ->
        concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead
          event := by
  exact
    SuccinctClose.PayloadLiveBPRelativeMinMaxArgSummaryTable.minCandidateTraceResultAtSegments_trace_forall
      (SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable_canonical shape)
      concreteBPNativeInteriorTraceSegments.summary block
      concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead
      (SuccinctClose.PayloadLiveBPRelativeMinMaxArgSummaryTable.summaryTraceResultAtSegments_trace_forall
        (SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable_canonical shape)
        concreteBPNativeInteriorTraceSegments.summary block
        concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead
        (by
          intro event hmem
          exact
            concreteBPNativeFixedWidthNatTable_readTraceResultAtSegment_noFiniteSmallInteriorSuccessfulRead
              (SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable_canonical
                shape).baselineTable
              concreteBPNativeInteriorTraceSegments.summary.baseline
              concreteBPNativeInteriorTraceSegments.summary.deadSegment
              _
              (concreteBPNativeSuccinctRMQSingletonSegmentMap_ne_of_bases_ne
                concreteBPNativeInteriorTraceSegments.summary.baseline
                concreteBPNativeInteriorTraceSegments.summary.deadSegment
                (by decide) (by decide))
              (concreteBPNativeSuccinctRMQSingletonSegmentMap_ne27_of_bases_ne
                concreteBPNativeInteriorTraceSegments.summary.baseline
                concreteBPNativeInteriorTraceSegments.summary.deadSegment
                (by decide) (by decide))
              event hmem)
        (by
          intro event hmem
          exact
            concreteBPNativeFixedWidthNatTable_readTraceResultAtSegment_noFiniteSmallInteriorSuccessfulRead
              (SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable_canonical
                shape).minRelTable
              concreteBPNativeInteriorTraceSegments.summary.minRel
              concreteBPNativeInteriorTraceSegments.summary.deadSegment
              _
              (concreteBPNativeSuccinctRMQSingletonSegmentMap_ne_of_bases_ne
                concreteBPNativeInteriorTraceSegments.summary.minRel
                concreteBPNativeInteriorTraceSegments.summary.deadSegment
                (by decide) (by decide))
              (concreteBPNativeSuccinctRMQSingletonSegmentMap_ne27_of_bases_ne
                concreteBPNativeInteriorTraceSegments.summary.minRel
                concreteBPNativeInteriorTraceSegments.summary.deadSegment
                (by decide) (by decide))
              event hmem)
        (by
          intro event hmem
          exact
            concreteBPNativeFixedWidthNatTable_readTraceResultAtSegment_noFiniteSmallInteriorSuccessfulRead
              (SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable_canonical
                shape).maxRelTable
              concreteBPNativeInteriorTraceSegments.summary.maxRel
              concreteBPNativeInteriorTraceSegments.summary.deadSegment
              _
              (concreteBPNativeSuccinctRMQSingletonSegmentMap_ne_of_bases_ne
                concreteBPNativeInteriorTraceSegments.summary.maxRel
                concreteBPNativeInteriorTraceSegments.summary.deadSegment
                (by decide) (by decide))
              (concreteBPNativeSuccinctRMQSingletonSegmentMap_ne27_of_bases_ne
                concreteBPNativeInteriorTraceSegments.summary.maxRel
                concreteBPNativeInteriorTraceSegments.summary.deadSegment
                (by decide) (by decide))
              event hmem)
        (by
          intro event hmem
          exact
            concreteBPNativeFixedWidthNatTable_readTraceResultAtSegment_noFiniteSmallInteriorSuccessfulRead
              (SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable_canonical
                shape).argOffsetTable
              concreteBPNativeInteriorTraceSegments.summary.argOffset
              concreteBPNativeInteriorTraceSegments.summary.deadSegment
              _
              (concreteBPNativeSuccinctRMQSingletonSegmentMap_ne_of_bases_ne
                concreteBPNativeInteriorTraceSegments.summary.argOffset
                concreteBPNativeInteriorTraceSegments.summary.deadSegment
                (by decide) (by decide))
              (concreteBPNativeSuccinctRMQSingletonSegmentMap_ne27_of_bases_ne
                concreteBPNativeInteriorTraceSegments.summary.argOffset
                concreteBPNativeInteriorTraceSegments.summary.deadSegment
                (by decide) (by decide))
              event hmem))

private theorem
    concreteBPNativeInteriorSummaryMinCandidateTraceResult_noReadyCloseSuccessfulRead
    (shape : Cartesian.CartesianShape) (block : Nat) :
    forall event,
      List.Mem event
          ((SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable_canonical
            shape).minCandidateTraceResultAtSegments
              concreteBPNativeInteriorTraceSegments.summary block).trace ->
        concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead
          event := by
  exact
    SuccinctClose.PayloadLiveBPRelativeMinMaxArgSummaryTable.minCandidateTraceResultAtSegments_trace_forall
      (SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable_canonical shape)
      concreteBPNativeInteriorTraceSegments.summary block
      concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead
      (SuccinctClose.PayloadLiveBPRelativeMinMaxArgSummaryTable.summaryTraceResultAtSegments_trace_forall
        (SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable_canonical shape)
        concreteBPNativeInteriorTraceSegments.summary block
        concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead
        (by
          intro event hmem
          exact
            concreteBPNativeFixedWidthNatTable_readTraceResultAtSegment_noReadyClosePayloadSuccessfulRead
              (SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable_canonical
                shape).baselineTable
              concreteBPNativeInteriorTraceSegments.summary.baseline
              concreteBPNativeInteriorTraceSegments.summary.deadSegment
              _
              (concreteBPNativeSuccinctRMQSingletonSegmentMap_ne_target_of_bases_ne
                concreteBPNativeInteriorTraceSegments.summary.baseline
                concreteBPNativeInteriorTraceSegments.summary.deadSegment
                24 (by decide) (by decide))
              (concreteBPNativeSuccinctRMQSingletonSegmentMap_ne_target_of_bases_ne
                concreteBPNativeInteriorTraceSegments.summary.baseline
                concreteBPNativeInteriorTraceSegments.summary.deadSegment
                25 (by decide) (by decide))
              event hmem)
        (by
          intro event hmem
          exact
            concreteBPNativeFixedWidthNatTable_readTraceResultAtSegment_noReadyClosePayloadSuccessfulRead
              (SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable_canonical
                shape).minRelTable
              concreteBPNativeInteriorTraceSegments.summary.minRel
              concreteBPNativeInteriorTraceSegments.summary.deadSegment
              _
              (concreteBPNativeSuccinctRMQSingletonSegmentMap_ne_target_of_bases_ne
                concreteBPNativeInteriorTraceSegments.summary.minRel
                concreteBPNativeInteriorTraceSegments.summary.deadSegment
                24 (by decide) (by decide))
              (concreteBPNativeSuccinctRMQSingletonSegmentMap_ne_target_of_bases_ne
                concreteBPNativeInteriorTraceSegments.summary.minRel
                concreteBPNativeInteriorTraceSegments.summary.deadSegment
                25 (by decide) (by decide))
              event hmem)
        (by
          intro event hmem
          exact
            concreteBPNativeFixedWidthNatTable_readTraceResultAtSegment_noReadyClosePayloadSuccessfulRead
              (SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable_canonical
                shape).maxRelTable
              concreteBPNativeInteriorTraceSegments.summary.maxRel
              concreteBPNativeInteriorTraceSegments.summary.deadSegment
              _
              (concreteBPNativeSuccinctRMQSingletonSegmentMap_ne_target_of_bases_ne
                concreteBPNativeInteriorTraceSegments.summary.maxRel
                concreteBPNativeInteriorTraceSegments.summary.deadSegment
                24 (by decide) (by decide))
              (concreteBPNativeSuccinctRMQSingletonSegmentMap_ne_target_of_bases_ne
                concreteBPNativeInteriorTraceSegments.summary.maxRel
                concreteBPNativeInteriorTraceSegments.summary.deadSegment
                25 (by decide) (by decide))
              event hmem)
        (by
          intro event hmem
          exact
            concreteBPNativeFixedWidthNatTable_readTraceResultAtSegment_noReadyClosePayloadSuccessfulRead
              (SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable_canonical
                shape).argOffsetTable
              concreteBPNativeInteriorTraceSegments.summary.argOffset
              concreteBPNativeInteriorTraceSegments.summary.deadSegment
              _
              (concreteBPNativeSuccinctRMQSingletonSegmentMap_ne_target_of_bases_ne
                concreteBPNativeInteriorTraceSegments.summary.argOffset
                concreteBPNativeInteriorTraceSegments.summary.deadSegment
                24 (by decide) (by decide))
              (concreteBPNativeSuccinctRMQSingletonSegmentMap_ne_target_of_bases_ne
                concreteBPNativeInteriorTraceSegments.summary.argOffset
                concreteBPNativeInteriorTraceSegments.summary.deadSegment
                25 (by decide) (by decide))
              event hmem))

private theorem
    concreteBPNativeInteriorGlobalWordTraceResultOfReady_noFiniteSmallInteriorSuccessfulRead
    (shape : Cartesian.CartesianShape)
    (hready : SuccinctClose.concreteBPRelativeRmmInteriorReady shape)
    (startBlock count : Nat) :
    forall event,
      List.Mem event
          (SuccinctClose.ConcreteCompactBPCloseLCADirectory.concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfReady
            shape hready concreteBPNativeInteriorTraceSegments
            startBlock count).trace ->
        concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead
          event := by
  exact
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfReady_trace_forall
      shape hready concreteBPNativeInteriorTraceSegments startBlock count
      concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead
      (concreteBPNativeInteriorSummaryMinCandidateTraceResult_noFiniteSmallInteriorSuccessfulRead
        shape)
      (by
        intro macroIdx localStart level event hmem
        unfold SuccinctClose.PayloadLiveBPLocalSparseOffsetTable.readOffsetTraceResultAtSegment at hmem
        exact
          concreteBPNativeFixedWidthNatTable_readTraceResultAtSegment_noFiniteSmallInteriorSuccessfulRead
            (SuccinctClose.concreteBPRelativeRmmInteriorLocalTable
              shape).table
            concreteBPNativeInteriorTraceSegments.localOffset
            concreteBPNativeInteriorTraceSegments.deadSegment
            _
            (concreteBPNativeSuccinctRMQSingletonSegmentMap_ne_of_bases_ne
              concreteBPNativeInteriorTraceSegments.localOffset
              concreteBPNativeInteriorTraceSegments.deadSegment
              (by decide) (by decide))
            (concreteBPNativeSuccinctRMQSingletonSegmentMap_ne27_of_bases_ne
              concreteBPNativeInteriorTraceSegments.localOffset
              concreteBPNativeInteriorTraceSegments.deadSegment
              (by decide) (by decide))
            event hmem)
      (by
        intro macroStart level event hmem
        unfold SuccinctClose.PayloadLiveBPGlobalSparseBlockTable.readBlockTraceResultAtSegment at hmem
        exact
          concreteBPNativeFixedWidthNatTable_readTraceResultAtSegment_noFiniteSmallInteriorSuccessfulRead
            (SuccinctClose.concreteBPRelativeRmmInteriorGlobalTable
              shape).table
            concreteBPNativeInteriorTraceSegments.globalBlock
            concreteBPNativeInteriorTraceSegments.deadSegment
            _
            (concreteBPNativeSuccinctRMQSingletonSegmentMap_ne_of_bases_ne
              concreteBPNativeInteriorTraceSegments.globalBlock
              concreteBPNativeInteriorTraceSegments.deadSegment
              (by decide) (by decide))
            (concreteBPNativeSuccinctRMQSingletonSegmentMap_ne27_of_bases_ne
              concreteBPNativeInteriorTraceSegments.globalBlock
              concreteBPNativeInteriorTraceSegments.deadSegment
              (by decide) (by decide))
            event hmem)

private theorem
    concreteBPNativeInteriorGlobalWordTraceResultAllSizeStructural_noFiniteSmallInteriorSuccessfulRead_of_ready
    (shape : Cartesian.CartesianShape)
    (_hready : SuccinctClose.concreteBPRelativeRmmInteriorReady shape)
    (startBlock count : Nat) :
    forall event,
      List.Mem event
          (SuccinctClose.ConcreteCompactBPCloseLCADirectory.concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructural
            shape concreteBPNativeInteriorTraceSegments
            startBlock count).trace ->
        concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead
          event := by
  intro event hmem
  unfold SuccinctClose.ConcreteCompactBPCloseLCADirectory.concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructural at hmem
  unfold SuccinctClose.ConcreteCompactBPCloseLCADirectory.canonicalRelativeRmmInteriorRangeMinTraceResultAtSegment at hmem
  unfold SuccinctClose.flatStoreExecutionTraceResultAtSegment at hmem
  cases List.mem_map.mp hmem with
  | intro read hrest =>
      cases hrest with
      | intro _ hevent =>
          subst event
          simp [concreteBPNativeInteriorTraceSegments,
            concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead]

theorem
    concreteBPNativeInteriorGlobalWordTraceResultAllSizeStructural_noFiniteSmallInteriorSuccessfulRead
    (shape : Cartesian.CartesianShape)
    (startBlock count : Nat) :
    forall event,
      List.Mem event
          (SuccinctClose.ConcreteCompactBPCloseLCADirectory.concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructural
            shape concreteBPNativeInteriorTraceSegments
            startBlock count).trace ->
        concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead
          event := by
  intro event hmem
  unfold SuccinctClose.ConcreteCompactBPCloseLCADirectory.concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructural at hmem
  unfold SuccinctClose.ConcreteCompactBPCloseLCADirectory.canonicalRelativeRmmInteriorRangeMinTraceResultAtSegment at hmem
  unfold SuccinctClose.flatStoreExecutionTraceResultAtSegment at hmem
  cases List.mem_map.mp hmem with
  | intro read hrest =>
      cases hrest with
      | intro _ hevent =>
          subst event
          simp [concreteBPNativeInteriorTraceSegments,
            concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead]

private theorem
    concreteBPNativeFiniteSmallInteriorRangeMinTraceResultAtSegments_noReadyCloseSuccessfulRead
    (shape : Cartesian.CartesianShape)
    (startBlock count : Nat) :
    forall event,
      List.Mem event
          (SuccinctClose.ConcreteCompactBPCloseLCADirectory.concreteBPFiniteSmallInteriorRangeMinTraceResultAtSegments
            shape concreteBPNativeInteriorTraceSegments
            startBlock count).trace ->
        concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead
          event := by
  unfold SuccinctClose.ConcreteCompactBPCloseLCADirectory.concreteBPFiniteSmallInteriorRangeMinTraceResultAtSegments
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      concreteBPNativeFixedWidthNatTable_readTraceResultAtSegment_noReadyCloseSuccessfulRead
        (SuccinctClose.concreteBPFiniteSmallInteriorRangeMinTable shape).minTable
        concreteBPNativeInteriorTraceSegments.finiteSmallMin
        concreteBPNativeInteriorTraceSegments.deadSegment
        _
        (concreteBPNativeSuccinctRMQSingletonSegmentMap_avoidsReadyClose_of_outside
          concreteBPNativeInteriorTraceSegments.finiteSmallMin
          concreteBPNativeInteriorTraceSegments.deadSegment
          (by decide) (by decide))
  · apply WordRAM.TraceResult.map_trace_forall
    exact
      concreteBPNativeFixedWidthNatTable_readTraceResultAtSegment_noReadyCloseSuccessfulRead
        (SuccinctClose.concreteBPFiniteSmallInteriorRangeMinTable shape).argTable
        concreteBPNativeInteriorTraceSegments.finiteSmallArg
        concreteBPNativeInteriorTraceSegments.deadSegment
        _
        (concreteBPNativeSuccinctRMQSingletonSegmentMap_avoidsReadyClose_of_outside
          concreteBPNativeInteriorTraceSegments.finiteSmallArg
          concreteBPNativeInteriorTraceSegments.deadSegment
          (by decide) (by decide))

private theorem
    concreteBPNativeInteriorGlobalWordTraceResultAllSizeStructural_noReadyCloseSuccessfulRead_of_not_ready
    (shape : Cartesian.CartesianShape)
    (_hnotReady : ¬ SuccinctClose.concreteBPRelativeRmmInteriorReady shape)
    (startBlock count : Nat) :
    forall event,
      List.Mem event
          (SuccinctClose.ConcreteCompactBPCloseLCADirectory.concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructural
            shape concreteBPNativeInteriorTraceSegments
            startBlock count).trace ->
        concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead
          event := by
  intro event hmem
  unfold SuccinctClose.ConcreteCompactBPCloseLCADirectory.concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructural at hmem
  unfold SuccinctClose.ConcreteCompactBPCloseLCADirectory.canonicalRelativeRmmInteriorRangeMinTraceResultAtSegment at hmem
  unfold SuccinctClose.flatStoreExecutionTraceResultAtSegment at hmem
  cases List.mem_map.mp hmem with
  | intro read hrest =>
      cases hrest with
      | intro _ hevent =>
          subst event
          simp [concreteBPNativeInteriorTraceSegments,
            concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead]

private theorem
    concreteBPNativeFiniteSmallSameBlockCloseGlobalTraceResult_noFiniteSmallInteriorSuccessfulRead
    (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) :
    forall event,
      List.Mem event
          (SuccinctClose.ConcreteCompactBPCloseLCADirectory.finiteSmallSameBlockCloseTraceResultAtSegment
            shape concreteBPNativeFiniteSmallSameBlockCloseTraceSegment
            concreteBPNativeInteriorTraceSegments.deadSegment
            leftClose rightClose).trace ->
        concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead
          event := by
  exact
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.finiteSmallSameBlockCloseTraceResultAtSegment_trace_forall
      shape concreteBPNativeFiniteSmallSameBlockCloseTraceSegment
      concreteBPNativeInteriorTraceSegments.deadSegment
      leftClose rightClose
      concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead
      (by
        intro event hmem
        exact
          SuccinctClose.ConcreteCompactBPCloseLCADirectory.finiteSmallSameBlockCloseReadTraceResultAtSegment_trace_forall
            shape concreteBPNativeFiniteSmallSameBlockCloseTraceSegment
            concreteBPNativeInteriorTraceSegments.deadSegment
            leftClose rightClose
            concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead
            (concreteBPNativeFixedWidthOptionNatTable_readTraceResultAtSegment_noFiniteSmallInteriorSuccessfulRead
              (SuccinctClose.concreteBPFiniteSmallSameBlockCloseTable shape)
              concreteBPNativeFiniteSmallSameBlockCloseTraceSegment
              concreteBPNativeInteriorTraceSegments.deadSegment
              _
              (concreteBPNativeSuccinctRMQSingletonSegmentMap_ne_of_bases_ne
                concreteBPNativeFiniteSmallSameBlockCloseTraceSegment
                concreteBPNativeInteriorTraceSegments.deadSegment
                (by decide) (by decide))
              (concreteBPNativeSuccinctRMQSingletonSegmentMap_ne27_of_bases_ne
                concreteBPNativeFiniteSmallSameBlockCloseTraceSegment
                concreteBPNativeInteriorTraceSegments.deadSegment
                (by decide) (by decide)))
            event hmem)

private theorem
    concreteBPNativeFiniteSmallSameBlockCloseGlobalTraceResult_noReadyCloseSuccessfulRead
    (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) :
    forall event,
      List.Mem event
          (SuccinctClose.ConcreteCompactBPCloseLCADirectory.finiteSmallSameBlockCloseTraceResultAtSegment
            shape concreteBPNativeFiniteSmallSameBlockCloseTraceSegment
            concreteBPNativeInteriorTraceSegments.deadSegment
            leftClose rightClose).trace ->
        concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead
          event := by
  exact
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.finiteSmallSameBlockCloseTraceResultAtSegment_trace_forall
      shape concreteBPNativeFiniteSmallSameBlockCloseTraceSegment
      concreteBPNativeInteriorTraceSegments.deadSegment
      leftClose rightClose
      concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead
      (by
        intro event hmem
        exact
          SuccinctClose.ConcreteCompactBPCloseLCADirectory.finiteSmallSameBlockCloseReadTraceResultAtSegment_trace_forall
            shape concreteBPNativeFiniteSmallSameBlockCloseTraceSegment
            concreteBPNativeInteriorTraceSegments.deadSegment
            leftClose rightClose
            concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead
            (concreteBPNativeFixedWidthOptionNatTable_readTraceResultAtSegment_noReadyCloseSuccessfulRead
              (SuccinctClose.concreteBPFiniteSmallSameBlockCloseTable shape)
              concreteBPNativeFiniteSmallSameBlockCloseTraceSegment
              concreteBPNativeInteriorTraceSegments.deadSegment
              _
              (concreteBPNativeSuccinctRMQSingletonSegmentMap_avoidsReadyClose_of_outside
                concreteBPNativeFiniteSmallSameBlockCloseTraceSegment
                concreteBPNativeInteriorTraceSegments.deadSegment
                (by decide) (by decide)))
            event hmem)

/-- Retired register-program trace for the legacy false-rank leg
(legacy/compatibility surfaces only, REQ-B3-04). -/
def concreteBPNativeRankCloseRegisterWordTraceResult
    (shape : Cartesian.CartesianShape)
    (pos : Nat) : WordRAM.TraceResult Nat :=
  WordRAM.TraceResult.ofResult
    (((builtRelativeSplitBPCloseRankData shape)
      |>.rankRegisterProgram false (WordRAM.Register.NatExpr.reg 0)).eval
        ((builtRelativeSplitBPCloseRankData shape)
          |>.rankRegisterWordRAMStore false)
        (WordRAM.Register.RegFile.withNat1 pos))

theorem concreteBPNativeRankCloseRegisterWordTraceResult_refines_registerInterpretedCosted
    (shape : Cartesian.CartesianShape) (pos : Nat) :
    (concreteBPNativeRankCloseRegisterWordTraceResult shape pos).toCosted =
      concreteBPNativeRankCloseRegisterInterpretedCosted shape pos := by
  rfl

/-- Retired register-program rank trace relabeled into a caller-supplied
global segment range (legacy/compatibility surfaces only). -/
def concreteBPNativeRankCloseRegisterWordTraceResultAtSegment
    (shape : Cartesian.CartesianShape)
    (rankSegmentBase pos : Nat) : WordRAM.TraceResult Nat :=
  WordRAM.TraceResult.relabelReadSegmentsWith
    (WordRAM.tripleSegmentMap rankSegmentBase
      concreteBPNativeDeadTraceSegment)
    (concreteBPNativeRankCloseRegisterWordTraceResult shape pos)

theorem concreteBPNativeRankCloseRegisterWordTraceResultAtSegment_refines_registerInterpretedCosted
    (shape : Cartesian.CartesianShape)
    (rankSegmentBase pos : Nat) :
    (concreteBPNativeRankCloseRegisterWordTraceResultAtSegment
      shape rankSegmentBase pos).toCosted =
      concreteBPNativeRankCloseRegisterInterpretedCosted shape pos := by
  simp [concreteBPNativeRankCloseRegisterWordTraceResultAtSegment,
    concreteBPNativeRankCloseRegisterWordTraceResult_refines_registerInterpretedCosted]

theorem concreteBPNativeRankCloseRegisterGlobalWordTraceResult_matchesReadStore
    (shape : Cartesian.CartesianShape) (pos : Nat) :
    forall event,
      event ∈
          (concreteBPNativeRankCloseRegisterWordTraceResultAtSegment
            shape concreteBPNativeRankCloseTraceSegmentBase pos).trace ->
        event.matchesReadStore
          (concreteBPNativeSuccinctRMQGlobalReadStoreLegacy shape) := by
  apply
    WordRAM.TraceResult.relabelReadSegmentsWith_matchesReadStore
      (concreteBPNativeRankCloseRegisterWordTraceResult shape pos)
      (WordRAM.ReadStore.ofStore
        ((builtRelativeSplitBPCloseRankData shape)
          |>.rankRegisterWordRAMStore false))
      (concreteBPNativeSuccinctRMQGlobalReadStoreLegacy shape)
      (WordRAM.tripleSegmentMap concreteBPNativeRankCloseTraceSegmentBase
        concreteBPNativeDeadTraceSegment)
  · intro segment index
    cases segment with
    | zero =>
        simp [concreteBPNativeSuccinctRMQGlobalReadStoreLegacy,
          concreteBPNativeRankCloseTraceSegmentBase,
          WordRAM.tripleSegmentMap, WordRAM.TraceEvent.tripleSegmentMap,
          WordRAM.ReadStore.ofStore]
    | succ segment =>
        cases segment with
        | zero =>
            simp [concreteBPNativeSuccinctRMQGlobalReadStoreLegacy,
              concreteBPNativeRankCloseTraceSegmentBase,
              WordRAM.tripleSegmentMap, WordRAM.TraceEvent.tripleSegmentMap,
              WordRAM.ReadStore.ofStore]
        | succ segment =>
            cases segment with
            | zero =>
                simp [concreteBPNativeSuccinctRMQGlobalReadStoreLegacy,
                  concreteBPNativeRankCloseTraceSegmentBase,
                  WordRAM.tripleSegmentMap, WordRAM.TraceEvent.tripleSegmentMap,
                  WordRAM.ReadStore.ofStore]
            | succ segment =>
                simp [concreteBPNativeSuccinctRMQGlobalReadStoreLegacy,
                  concreteBPNativeDeadTraceSegment,
                  WordRAM.tripleSegmentMap, WordRAM.TraceEvent.tripleSegmentMap,
                  WordRAM.ReadStore.ofStore,
                  SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.rankRegisterWordRAMStore,
                  WordRAM.Store.readWord?]
  · intro event hmem
    simpa [concreteBPNativeRankCloseRegisterWordTraceResult,
      WordRAM.TraceResult.ofResult_trace,
      WordRAM.TraceEvent.matchesReadStore_ofStore] using
      WordRAM.Register.NatProgram.eval_reads_subset_payload
        ((builtRelativeSplitBPCloseRankData shape)
          |>.rankRegisterProgram false (WordRAM.Register.NatExpr.reg 0))
        ((builtRelativeSplitBPCloseRankData shape)
          |>.rankRegisterWordRAMStore false)
        (WordRAM.Register.RegFile.withNat1 pos)
        event hmem

/--
Interpreted compact LCA-close leg (legacy/compatibility presentation: the
compact close directory with the retired register-interpreted rank seed,
REQ-B3-04; the accepted route uses the canonical dispatcher below).
-/
def concreteBPNativeLCACloseInterpretedCosted
    (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) : Costed (Option Nat) :=
  (concreteBPNativeCloseDirectory shape).lcaCloseCostedWithRankSeed
    (concreteBPNativeRankCloseRegisterInterpretedCosted shape)
    leftClose rightClose

/--
Trace-preserving replay for the compact close/LCA leg.

The rank seed reads inside this leg are structural register-program traces. The
bounded local BP decoders, endpoint-fringe decoders, and relative-rmM interior
query are still charged decoder leaves, so this is a partially structural
close/LCA replay rather than the final fully payload-read-derived navigator.
-/
def concreteBPNativeLCACloseWordTraceResult
    (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) : WordRAM.TraceResult (Option Nat) :=
  (concreteBPNativeCloseDirectory shape).lcaCloseTraceResultWithRankSeed
    (concreteBPNativeRankCloseRegisterWordTraceResult shape)
    leftClose rightClose

theorem concreteBPNativeLCACloseWordTraceResult_refines_interpretedCosted
    (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) :
    (concreteBPNativeLCACloseWordTraceResult
      shape leftClose rightClose).toCosted =
      concreteBPNativeLCACloseInterpretedCosted shape leftClose rightClose := by
  simp [concreteBPNativeLCACloseWordTraceResult,
    concreteBPNativeLCACloseInterpretedCosted,
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.lcaCloseTraceResultWithRankSeed_refines,
    concreteBPNativeRankCloseRegisterWordTraceResult_refines_registerInterpretedCosted]

/--
Large-regime structural replay for the compact LCA-close leg.

The size hypothesis lets the close directory dispatch through the positive
summary-block path, so the zero-block structural scan is absent and the
cross-block interior relative-rmM leg uses its concrete trace replay.
-/
def concreteBPNativeLCACloseWordTraceResultOfSizeGe
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (leftClose rightClose : Nat) : WordRAM.TraceResult (Option Nat) :=
  SuccinctClose.ConcreteCompactBPCloseLCADirectory.lcaCloseTraceResultWithRankSeedOfSizeGe
    shape (concreteBPNativeRankCloseRegisterWordTraceResult shape)
    hsize leftClose rightClose

theorem concreteBPNativeLCACloseWordTraceResultOfSizeGe_refines_interpretedCosted
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (leftClose rightClose : Nat) :
    (concreteBPNativeLCACloseWordTraceResultOfSizeGe
      shape hsize leftClose rightClose).toCosted =
      concreteBPNativeLCACloseInterpretedCosted shape leftClose rightClose := by
  simp [concreteBPNativeLCACloseWordTraceResultOfSizeGe,
    concreteBPNativeLCACloseInterpretedCosted,
    concreteBPNativeCloseDirectory,
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.lcaCloseTraceResultWithRankSeedOfSizeGe_refines,
    concreteBPNativeRankCloseRegisterWordTraceResult_refines_registerInterpretedCosted]

/--
Large-regime LCA-close trace with caller-controlled global segment bases.

The rank-seed callback is shifted by `rankSegmentBase`; local BP-code reads
stay at segment 0; and relative-rmM interior tables use `interiorSegments`.
-/
def concreteBPNativeLCACloseWordTraceResultAtSegmentsOfSizeGe
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (rankSegmentBase : Nat)
    (interiorSegments : SuccinctClose.BPRelativeRmmInteriorTraceSegments)
    (leftClose rightClose : Nat) : WordRAM.TraceResult (Option Nat) :=
  SuccinctClose.ConcreteCompactBPCloseLCADirectory.lcaCloseTraceResultWithRankSeedAtSegmentsOfSizeGe
    shape
    (concreteBPNativeRankCloseRegisterWordTraceResultAtSegment
      shape rankSegmentBase)
    hsize interiorSegments leftClose rightClose

theorem concreteBPNativeLCACloseWordTraceResultAtSegmentsOfSizeGe_refines_interpretedCosted
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (rankSegmentBase : Nat)
    (interiorSegments : SuccinctClose.BPRelativeRmmInteriorTraceSegments)
    (leftClose rightClose : Nat) :
    (concreteBPNativeLCACloseWordTraceResultAtSegmentsOfSizeGe
      shape hsize rankSegmentBase interiorSegments leftClose rightClose).toCosted =
      concreteBPNativeLCACloseInterpretedCosted shape leftClose rightClose := by
  simp [concreteBPNativeLCACloseWordTraceResultAtSegmentsOfSizeGe,
    concreteBPNativeLCACloseInterpretedCosted,
    concreteBPNativeCloseDirectory,
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.lcaCloseTraceResultWithRankSeedAtSegmentsOfSizeGe_refines,
    concreteBPNativeRankCloseRegisterWordTraceResultAtSegment_refines_registerInterpretedCosted]

/--
All-size compact LCA-close trace with the rank-seed callback relabeled into the
final global rank segments. Local BP-code reads stay at segment `0`; tiny or
inactive fallback work contributes synthetic word-primitive events rather than
payload reads.
-/
def concreteBPNativeLCACloseGlobalWordTraceResult
    (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) : WordRAM.TraceResult (Option Nat) :=
  (concreteBPNativeCloseDirectory shape).lcaCloseTraceResultWithRankSeed
    (concreteBPNativeRankCloseRegisterWordTraceResultAtSegment
      shape concreteBPNativeRankCloseTraceSegmentBase)
    leftClose rightClose

theorem concreteBPNativeLCACloseGlobalWordTraceResult_refines_interpretedCosted
    (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) :
    (concreteBPNativeLCACloseGlobalWordTraceResult
      shape leftClose rightClose).toCosted =
      concreteBPNativeLCACloseInterpretedCosted shape leftClose rightClose := by
  simp [concreteBPNativeLCACloseGlobalWordTraceResult,
    concreteBPNativeLCACloseInterpretedCosted,
    concreteBPNativeCloseDirectory,
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.lcaCloseTraceResultWithRankSeed_refines,
    concreteBPNativeRankCloseRegisterWordTraceResultAtSegment_refines_registerInterpretedCosted]

theorem concreteBPNativeLCACloseGlobalWordTraceResult_matchesReadStore_total
    (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) :
    forall event,
      List.Mem event
          (concreteBPNativeLCACloseGlobalWordTraceResult
            shape leftClose rightClose).trace ->
        event.matchesReadStore
          (concreteBPNativeSuccinctRMQGlobalReadStoreLegacy shape) := by
  exact
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.lcaCloseTraceResultWithRankSeed_matchesReadStore
      (concreteBPNativeCloseDirectory shape)
      (concreteBPNativeRankCloseRegisterWordTraceResultAtSegment
        shape concreteBPNativeRankCloseTraceSegmentBase)
      leftClose rightClose
      (concreteBPNativeSuccinctRMQGlobalReadStoreLegacy shape)
      (fun pos =>
        concreteBPNativeRankCloseRegisterGlobalWordTraceResult_matchesReadStore
          shape pos)
      (concreteBPNativeSuccinctRMQGlobalReadStoreLegacy_bpCode shape)
      (fun blockSize close =>
        SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPWindowBitsTraceResult_matchesReadStore
          shape blockSize close
          (concreteBPNativeSuccinctRMQGlobalReadStoreLegacy shape)
          (concreteBPNativeSuccinctRMQGlobalReadStoreLegacy_bpCode shape))

/-
All-size structural compact LCA-close trace under the final global segment
layout.  Unlike `concreteBPNativeLCACloseGlobalWordTraceResult`, this path
replaces both old `TraceResult.ofCosted` boundaries with payload-table traces.
-/
/-- Canonical all-size modeled close/LCA cost, with no zero-block dispatch. -/
def concreteBPNativeLCACloseCanonicalInterpretedCosted
    (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) : Costed (Option Nat) :=
  SuccinctClose.ConcreteCompactBPCloseLCADirectory.canonicalLcaCloseCostedWithRankSeed
    shape (concreteBPNativeRankCloseInterpretedCosted shape)
    leftClose rightClose

def concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
    (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) : WordRAM.TraceResult (Option Nat) :=
  SuccinctClose.ConcreteCompactBPCloseLCADirectory.lcaCloseTraceResultWithRankSeedAllSizeStructural
    shape
    (concreteBPNativeRankCloseWordTraceResultAtSegment
      shape concreteBPNativeRankCloseTraceSegmentBase)
    concreteBPNativeInteriorTraceSegments
    concreteBPNativeFringeChunkTraceSegment
    concreteBPNativeFiniteSmallSameBlockCloseTraceSegment
    leftClose rightClose

theorem concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural_refines_interpretedCosted
    (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) :
    (concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
      shape leftClose rightClose).toCosted =
      concreteBPNativeLCACloseCanonicalInterpretedCosted shape leftClose rightClose := by
  simp [concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural,
    concreteBPNativeLCACloseCanonicalInterpretedCosted,
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.lcaCloseTraceResultWithRankSeedAllSizeStructural_refines,
    concreteBPNativeRankCloseWordTraceResultAtSegment_refines_interpretedCosted]

private theorem
    concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural_noFiniteSmallInteriorSuccessfulRead_of_ready
    (shape : Cartesian.CartesianShape)
    (hready : SuccinctClose.concreteBPRelativeRmmInteriorReady shape)
    (leftClose rightClose : Nat) :
    forall event,
      List.Mem event
          (concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
            shape leftClose rightClose).trace ->
        concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead
          event := by
  exact
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.lcaCloseTraceResultWithRankSeedAllSizeStructural_trace_forall
      shape
      (concreteBPNativeRankCloseWordTraceResultAtSegment
        shape concreteBPNativeRankCloseTraceSegmentBase)
      concreteBPNativeInteriorTraceSegments
      concreteBPNativeFringeChunkTraceSegment
      concreteBPNativeFiniteSmallSameBlockCloseTraceSegment
      leftClose rightClose
      concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead
      (fun pos =>
        concreteBPNativeSuccinctRMQRankCloseGlobalWordTraceResult_noFiniteSmallInteriorSuccessfulRead
          shape pos)
      (fun blockSize close =>
        concreteBPNativeSuccinctRMQLocalBPWindowBitsTraceResult_noFiniteSmallInteriorSuccessfulRead
          shape blockSize close)
      (fun blockSize close seed =>
        SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedLeftFringeCandidateSeededTraceResultAtSegment_trace_forall
          shape concreteBPNativeFringeChunkTraceSegment blockSize close seed
          concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead
          (concreteBPNativeSuccinctRMQLocalBPWindowBitsTraceResult_noFiniteSmallInteriorSuccessfulRead
            shape blockSize close)
          (fun address _hlt => by
            simp [concreteBPNativeFringeChunkTraceSegment,
              concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead]))
      (fun blockSize close seed =>
        SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedRightFringeCandidateSeededTraceResultAtSegment_trace_forall
          shape concreteBPNativeFringeChunkTraceSegment blockSize close seed
          concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead
          (concreteBPNativeSuccinctRMQLocalBPWindowBitsTraceResult_noFiniteSmallInteriorSuccessfulRead
            shape blockSize close)
          (fun address _hlt => by
            simp [concreteBPNativeFringeChunkTraceSegment,
              concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead]))
      (fun startBlock count =>
        concreteBPNativeInteriorGlobalWordTraceResultAllSizeStructural_noFiniteSmallInteriorSuccessfulRead_of_ready
          shape hready startBlock count)

private theorem
    concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural_noFiniteSmallInteriorSuccessfulRead
    (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) :
    forall event,
      List.Mem event
          (concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
            shape leftClose rightClose).trace ->
        concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead
          event := by
  exact
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.lcaCloseTraceResultWithRankSeedAllSizeStructural_trace_forall
      shape
      (concreteBPNativeRankCloseWordTraceResultAtSegment
        shape concreteBPNativeRankCloseTraceSegmentBase)
      concreteBPNativeInteriorTraceSegments
      concreteBPNativeFringeChunkTraceSegment
      concreteBPNativeFiniteSmallSameBlockCloseTraceSegment
      leftClose rightClose
      concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead
      (fun pos =>
        concreteBPNativeSuccinctRMQRankCloseGlobalWordTraceResult_noFiniteSmallInteriorSuccessfulRead
          shape pos)
      (fun blockSize close =>
        concreteBPNativeSuccinctRMQLocalBPWindowBitsTraceResult_noFiniteSmallInteriorSuccessfulRead
          shape blockSize close)
      (fun blockSize close seed =>
        SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedLeftFringeCandidateSeededTraceResultAtSegment_trace_forall
          shape concreteBPNativeFringeChunkTraceSegment blockSize close seed
          concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead
          (concreteBPNativeSuccinctRMQLocalBPWindowBitsTraceResult_noFiniteSmallInteriorSuccessfulRead
            shape blockSize close)
          (fun address _hlt => by
            simp [concreteBPNativeFringeChunkTraceSegment,
              concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead]))
      (fun blockSize close seed =>
        SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedRightFringeCandidateSeededTraceResultAtSegment_trace_forall
          shape concreteBPNativeFringeChunkTraceSegment blockSize close seed
          concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead
          (concreteBPNativeSuccinctRMQLocalBPWindowBitsTraceResult_noFiniteSmallInteriorSuccessfulRead
            shape blockSize close)
          (fun address _hlt => by
            simp [concreteBPNativeFringeChunkTraceSegment,
              concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead]))
      (fun startBlock count =>
        concreteBPNativeInteriorGlobalWordTraceResultAllSizeStructural_noFiniteSmallInteriorSuccessfulRead
          shape startBlock count)

private theorem
    concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural_noReadyCloseSuccessfulRead_of_not_ready
    (shape : Cartesian.CartesianShape)
    (hnotReady : ¬ SuccinctClose.concreteBPRelativeRmmInteriorReady shape)
    (leftClose rightClose : Nat) :
    forall event,
      List.Mem event
          (concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
            shape leftClose rightClose).trace ->
        concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead
          event := by
  exact
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.lcaCloseTraceResultWithRankSeedAllSizeStructural_trace_forall
      shape
      (concreteBPNativeRankCloseWordTraceResultAtSegment
        shape concreteBPNativeRankCloseTraceSegmentBase)
      concreteBPNativeInteriorTraceSegments
      concreteBPNativeFringeChunkTraceSegment
      concreteBPNativeFiniteSmallSameBlockCloseTraceSegment
      leftClose rightClose
      concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead
      (fun pos =>
        concreteBPNativeSuccinctRMQRankCloseGlobalWordTraceResult_noReadyCloseSuccessfulRead
          shape pos)
      (fun blockSize close =>
        concreteBPNativeSuccinctRMQLocalBPWindowBitsTraceResult_noReadyCloseSuccessfulRead
          shape blockSize close)
      (fun blockSize close seed =>
        SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedLeftFringeCandidateSeededTraceResultAtSegment_trace_forall
          shape concreteBPNativeFringeChunkTraceSegment blockSize close seed
          concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead
          (concreteBPNativeSuccinctRMQLocalBPWindowBitsTraceResult_noReadyCloseSuccessfulRead
            shape blockSize close)
          (fun address _hlt => by
            simp [concreteBPNativeFringeChunkTraceSegment,
              concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead]))
      (fun blockSize close seed =>
        SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedRightFringeCandidateSeededTraceResultAtSegment_trace_forall
          shape concreteBPNativeFringeChunkTraceSegment blockSize close seed
          concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead
          (concreteBPNativeSuccinctRMQLocalBPWindowBitsTraceResult_noReadyCloseSuccessfulRead
            shape blockSize close)
          (fun address _hlt => by
            simp [concreteBPNativeFringeChunkTraceSegment,
              concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead]))
      (fun startBlock count =>
        concreteBPNativeInteriorGlobalWordTraceResultAllSizeStructural_noReadyCloseSuccessfulRead_of_not_ready
          shape hnotReady startBlock count)

theorem concreteBPNativeInteriorGlobalWordTraceResult_matchesReadStore
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (startBlock count : Nat) :
    forall event,
      List.Mem event
          (SuccinctClose.ConcreteCompactBPCloseLCADirectory.concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfSizeGe
            shape hsize concreteBPNativeInteriorTraceSegments
            startBlock count).trace ->
        event.matchesReadStore
          (concreteBPNativeSuccinctRMQGlobalReadStoreLegacy shape) := by
  exact
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfSizeGe_matchesReadStore
      shape hsize concreteBPNativeInteriorTraceSegments
      (concreteBPNativeSuccinctRMQGlobalReadStoreLegacy shape)
      (by
        intro segment index
        cases segment <;>
          simp [concreteBPNativeSuccinctRMQGlobalReadStoreLegacy,
            concreteBPNativeInteriorTraceSegments,
            concreteBPNativeDeadTraceSegment,
            WordRAM.singletonSegmentMap,
            WordRAM.TraceEvent.singletonSegmentMap,
            SuccinctSpace.FixedWidthNatTable.wordRAMStore,
            SuccinctSpace.PayloadWordStore.wordRAMStore,
            WordRAM.Store.readWord?])
      (by
        intro segment index
        cases segment <;>
          simp [concreteBPNativeSuccinctRMQGlobalReadStoreLegacy,
            concreteBPNativeInteriorTraceSegments,
            concreteBPNativeDeadTraceSegment,
            WordRAM.singletonSegmentMap,
            WordRAM.TraceEvent.singletonSegmentMap,
            SuccinctSpace.FixedWidthNatTable.wordRAMStore,
            SuccinctSpace.PayloadWordStore.wordRAMStore,
            WordRAM.Store.readWord?])
      (by
        intro segment index
        cases segment <;>
          simp [concreteBPNativeSuccinctRMQGlobalReadStoreLegacy,
            concreteBPNativeInteriorTraceSegments,
            concreteBPNativeDeadTraceSegment,
            WordRAM.singletonSegmentMap,
            WordRAM.TraceEvent.singletonSegmentMap,
            SuccinctSpace.FixedWidthNatTable.wordRAMStore,
            SuccinctSpace.PayloadWordStore.wordRAMStore,
            WordRAM.Store.readWord?])
      (by
        intro segment index
        cases segment <;>
          simp [concreteBPNativeSuccinctRMQGlobalReadStoreLegacy,
            concreteBPNativeInteriorTraceSegments,
            concreteBPNativeDeadTraceSegment,
            WordRAM.singletonSegmentMap,
            WordRAM.TraceEvent.singletonSegmentMap,
            SuccinctSpace.FixedWidthNatTable.wordRAMStore,
            SuccinctSpace.PayloadWordStore.wordRAMStore,
            WordRAM.Store.readWord?])
      (by
        intro segment index
        cases segment <;>
          simp [concreteBPNativeSuccinctRMQGlobalReadStoreLegacy,
            concreteBPNativeInteriorTraceSegments,
            concreteBPNativeDeadTraceSegment,
            WordRAM.singletonSegmentMap,
            WordRAM.TraceEvent.singletonSegmentMap,
            SuccinctSpace.FixedWidthNatTable.wordRAMStore,
            SuccinctSpace.PayloadWordStore.wordRAMStore,
            WordRAM.Store.readWord?])
      (by
        intro segment index
        cases segment <;>
          simp [concreteBPNativeSuccinctRMQGlobalReadStoreLegacy,
            concreteBPNativeInteriorTraceSegments,
            concreteBPNativeDeadTraceSegment,
            WordRAM.singletonSegmentMap,
            WordRAM.TraceEvent.singletonSegmentMap,
            SuccinctSpace.FixedWidthNatTable.wordRAMStore,
            SuccinctSpace.PayloadWordStore.wordRAMStore,
            WordRAM.Store.readWord?])
      startBlock count

theorem concreteBPNativeInteriorGlobalWordTraceResultAllSizeStructural_matchesReadStore
    (shape : Cartesian.CartesianShape)
    (startBlock count : Nat) :
    forall event,
      List.Mem event
          (SuccinctClose.ConcreteCompactBPCloseLCADirectory.concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructural
            shape concreteBPNativeInteriorTraceSegments
            startBlock count).trace ->
        event.matchesReadStore
          (concreteBPNativeSuccinctRMQGlobalReadStore shape) := by
  exact
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructural_matchesReadStore
      shape concreteBPNativeInteriorTraceSegments
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (concreteBPNativeSuccinctRMQGlobalReadStore_canonicalComponent shape)
      startBlock count

theorem concreteBPNativeLCACloseGlobalWordTraceResult_matchesReadStore
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (leftClose rightClose : Nat) :
    forall event,
      List.Mem event
          (concreteBPNativeLCACloseWordTraceResultAtSegmentsOfSizeGe
            shape hsize concreteBPNativeRankCloseTraceSegmentBase
            concreteBPNativeInteriorTraceSegments
            leftClose rightClose).trace ->
        event.matchesReadStore
          (concreteBPNativeSuccinctRMQGlobalReadStoreLegacy shape) := by
  exact
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.lcaCloseTraceResultWithRankSeedAtSegmentsOfSizeGe_matchesReadStore
      shape
      (concreteBPNativeRankCloseRegisterWordTraceResultAtSegment
        shape concreteBPNativeRankCloseTraceSegmentBase)
      hsize concreteBPNativeInteriorTraceSegments leftClose rightClose
      (concreteBPNativeSuccinctRMQGlobalReadStoreLegacy shape)
      (fun pos =>
        concreteBPNativeRankCloseRegisterGlobalWordTraceResult_matchesReadStore
          shape pos)
      (concreteBPNativeSuccinctRMQGlobalReadStoreLegacy_bpCode shape)
      (fun startBlock count =>
        concreteBPNativeInteriorGlobalWordTraceResult_matchesReadStore
          shape hsize startBlock count)

theorem concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural_matchesReadStore
    (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) :
    forall event,
      List.Mem event
          (concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
            shape leftClose rightClose).trace ->
        event.matchesReadStore
          (concreteBPNativeSuccinctRMQGlobalReadStore shape) := by
  exact
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.lcaCloseTraceResultWithRankSeedAllSizeStructural_matchesReadStore
      shape
      (concreteBPNativeRankCloseWordTraceResultAtSegment
        shape concreteBPNativeRankCloseTraceSegmentBase)
      concreteBPNativeInteriorTraceSegments
      concreteBPNativeFringeChunkTraceSegment
      concreteBPNativeFiniteSmallSameBlockCloseTraceSegment
      leftClose rightClose
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (fun pos =>
        concreteBPNativeRankCloseCanonicalGlobalWordTraceResult_matchesReadStore
          shape pos)
      (concreteBPNativeSuccinctRMQGlobalReadStore_bpCode shape)
      (concreteBPNativeSuccinctRMQGlobalReadStore_fringeChunkTable shape)
      (fun startBlock count =>
        concreteBPNativeInteriorGlobalWordTraceResultAllSizeStructural_matchesReadStore
          shape startBlock count)

theorem concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural_no_syntheticCostOnlyPrimitive
    (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) :
    forall event,
      List.Mem event
          (concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
            shape leftClose rightClose).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  exact
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.lcaCloseTraceResultWithRankSeedAllSizeStructural_no_syntheticCostOnlyPrimitive
      shape
      (concreteBPNativeRankCloseWordTraceResultAtSegment
        shape concreteBPNativeRankCloseTraceSegmentBase)
      concreteBPNativeInteriorTraceSegments
      concreteBPNativeFringeChunkTraceSegment
      concreteBPNativeFiniteSmallSameBlockCloseTraceSegment
      leftClose rightClose
      (fun pos =>
        concreteBPNativeRankCloseGlobalWordTraceResult_no_syntheticCostOnlyPrimitive
          shape pos)

/--
Final BP-native RMQ query with interpreted close-select, compact close/LCA, and
answer-rank leaves (legacy/compatibility presentation over the retired
register-interpreted legs, REQ-B3-04; the accepted route is the canonical
whole query below).
-/
def concreteBPNativeSuccinctRMQQueryInterpretedCosted
    (shape : Cartesian.CartesianShape)
    (left right : Nat) : Costed (Option Nat) :=
  Costed.bind
    (concreteBPNativeSelectCloseRegisterInterpretedCosted shape left)
    fun leftClose? =>
      Costed.bind
        (concreteBPNativeSelectCloseRegisterInterpretedCosted
          shape (right - 1))
        fun rightClose? =>
          match leftClose?, rightClose? with
          | some leftClose, some rightClose =>
              Costed.bind
                (concreteBPNativeLCACloseInterpretedCosted shape
                  leftClose rightClose)
                fun answerClose? =>
                  match answerClose? with
                  | some answerClose =>
                      Costed.map (fun closeRank => some (closeRank - 1))
                        (concreteBPNativeRankCloseRegisterInterpretedCosted
                          shape (answerClose + 1))
                  | none => Costed.pure none
          | _, _ => Costed.pure none

/-- Optional-natural registers used by the final whole-query control program. -/
inductive WholeQueryOptReg where
  | leftClose
  | rightClose
  | answerClose
  | output
deriving Repr, DecidableEq

/-- Natural registers used by the final whole-query control program. -/
inductive WholeQueryNatReg where
  | closeRank
deriving Repr, DecidableEq

/-- Concrete register state for the final BP-native RMQ query program. -/
structure WholeQueryState where
  leftClose? : Option Nat := none
  rightClose? : Option Nat := none
  answerClose? : Option Nat := none
  closeRank : Nat := 0
  output? : Option Nat := none
deriving Repr

namespace WholeQueryState

/-- Empty initial register state. -/
def empty : WholeQueryState where

/-- Read an optional-natural register. -/
def opt (state : WholeQueryState) : WholeQueryOptReg -> Option Nat
  | .leftClose => state.leftClose?
  | .rightClose => state.rightClose?
  | .answerClose => state.answerClose?
  | .output => state.output?

/-- Read a natural register. -/
def nat (state : WholeQueryState) : WholeQueryNatReg -> Nat
  | .closeRank => state.closeRank

/-- Write an optional-natural register. -/
def setOpt (state : WholeQueryState) (reg : WholeQueryOptReg)
    (value : Option Nat) : WholeQueryState :=
  match reg with
  | .leftClose => { state with leftClose? := value }
  | .rightClose => { state with rightClose? := value }
  | .answerClose => { state with answerClose? := value }
  | .output => { state with output? := value }

/-- Write a natural register. -/
def setNat (state : WholeQueryState) (reg : WholeQueryNatReg)
    (value : Nat) : WholeQueryState :=
  match reg with
  | .closeRank => { state with closeRank := value }

end WholeQueryState

/--
First-order natural expressions for the final query-control program.

These expressions may inspect the two public query inputs and the program's own
registers. They do not contain Lean callbacks.
-/
inductive WholeQueryNatExpr where
  | const (value : Nat)
  | inputLeft
  | inputRight
  | optNatD (reg : WholeQueryOptReg) (fallback : Nat)
  | natReg (reg : WholeQueryNatReg)
  | add (left right : WholeQueryNatExpr)
  | sub (left right : WholeQueryNatExpr)
deriving Repr, DecidableEq

namespace WholeQueryNatExpr

/-- Evaluate a first-order query expression. -/
def eval (left right : Nat) (state : WholeQueryState) :
    WholeQueryNatExpr -> Nat
  | .const value => value
  | .inputLeft => left
  | .inputRight => right
  | .optNatD reg fallback => (state.opt reg).getD fallback
  | .natReg reg => state.nat reg
  | .add a b => a.eval left right state + b.eval left right state
  | .sub a b => a.eval left right state - b.eval left right state

end WholeQueryNatExpr

/--
Closed instruction set for the final BP-native RMQ query.

This is first-order control over already-interpreted component leaves: it has
fixed instruction constructors, register operands, and arithmetic expressions,
not higher-order continuations or arbitrary callbacks.
-/
inductive WholeQueryInstr where
  | selectClose (dst : WholeQueryOptReg) (idx : WholeQueryNatExpr)
  | lcaClose (dst leftReg rightReg : WholeQueryOptReg)
  | rankCloseIfSome
      (dst : WholeQueryNatReg) (guard : WholeQueryOptReg)
      (pos : WholeQueryNatExpr)
  | outputPredIfSome
      (dst guard : WholeQueryOptReg) (src : WholeQueryNatReg)
deriving Repr

namespace WholeQueryInstr

/-- Execute one whole-query instruction. -/
def eval (shape : Cartesian.CartesianShape) (left right : Nat)
    (instr : WholeQueryInstr) (state : WholeQueryState) :
    Costed WholeQueryState :=
  match instr with
  | .selectClose dst idx =>
      Costed.map
        (fun close? => state.setOpt dst close?)
        (concreteBPNativeSelectCloseRegisterInterpretedCosted shape
          (idx.eval left right state))
  | .lcaClose dst leftReg rightReg =>
      match state.opt leftReg, state.opt rightReg with
      | some leftClose, some rightClose =>
          Costed.map
            (fun answer? => state.setOpt dst answer?)
            (concreteBPNativeLCACloseInterpretedCosted shape
              leftClose rightClose)
      | _, _ => Costed.pure (state.setOpt dst none)
  | .rankCloseIfSome dst guard pos =>
      match state.opt guard with
      | some _ =>
          Costed.map
            (fun closeRank => state.setNat dst closeRank)
            (concreteBPNativeRankCloseRegisterInterpretedCosted shape
              (pos.eval left right state))
      | none => Costed.pure state
  | .outputPredIfSome dst guard src =>
      match state.opt guard with
      | some _ => Costed.pure (state.setOpt dst (some (state.nat src - 1)))
      | none => Costed.pure (state.setOpt dst none)

/-- Canonical modeled instruction semantics used by the global replay. -/
def evalCanonical (shape : Cartesian.CartesianShape) (left right : Nat)
    (instr : WholeQueryInstr) (state : WholeQueryState) :
    Costed WholeQueryState :=
  match instr with
  | .selectClose dst idx =>
      Costed.map
        (fun close? => state.setOpt dst close?)
        (concreteBPNativeSelectCloseInterpretedCosted shape
          (idx.eval left right state))
  | .lcaClose dst leftReg rightReg =>
      match state.opt leftReg, state.opt rightReg with
      | some leftClose, some rightClose =>
          Costed.map
            (fun answer? => state.setOpt dst answer?)
            (concreteBPNativeLCACloseCanonicalInterpretedCosted shape
              leftClose rightClose)
      | _, _ => Costed.pure (state.setOpt dst none)
  | .rankCloseIfSome dst guard pos =>
      match state.opt guard with
      | some _ =>
          Costed.map
            (fun closeRank => state.setNat dst closeRank)
            (concreteBPNativeRankCloseInterpretedCosted shape
              (pos.eval left right state))
      | none => Costed.pure state
  | .outputPredIfSome dst guard src =>
      match state.opt guard with
      | some _ => Costed.pure (state.setOpt dst (some (state.nat src - 1)))
      | none => Costed.pure (state.setOpt dst none)

end WholeQueryInstr

/-- First-order whole-query control programs for the final RMQ path. -/
abbrev WholeQueryProgram := List WholeQueryInstr

namespace WholeQueryProgram

/-- Execute a whole-query control program. -/
def eval (shape : Cartesian.CartesianShape) (left right : Nat) :
    WholeQueryProgram -> WholeQueryState -> Costed WholeQueryState
  | [], state => Costed.pure state
  | instr :: rest, state =>
      Costed.bind (instr.eval shape left right state) fun state' =>
        eval shape left right rest state'

/-- Execute a whole-query program with the canonical LCA cost model. -/
def evalCanonical (shape : Cartesian.CartesianShape) (left right : Nat) :
    WholeQueryProgram -> WholeQueryState -> Costed WholeQueryState
  | [], state => Costed.pure state
  | instr :: rest, state =>
      Costed.bind (instr.evalCanonical shape left right state) fun state' =>
        evalCanonical shape left right rest state'

end WholeQueryProgram

/--
Trace events for the first flattened whole-query layer.

This trace records the closed controller's domain leaves and their modeled
costs.  It is intentionally not yet a single payload-store `WordRAM.TraceEvent`
list: the select-close and compact close/LCA leaves still expose interpreted
`Costed` queries.  The point of this layer is to stop collapsing the whole
query directly to `Costed`, so later passes can replace these leaf summaries by
lower-level payload traces one component at a time.
-/
inductive WholeQueryLeafTraceEvent where
  | selectClose (idx : Nat) (result : Option Nat) (cost : Nat)
  | lcaClose (leftClose rightClose : Nat) (result : Option Nat) (cost : Nat)
  | rankClose (pos result cost : Nat)
deriving Repr, DecidableEq

namespace WholeQueryLeafTraceEvent

/-- Modeled cost contributed by one whole-query leaf event. -/
def cost : WholeQueryLeafTraceEvent -> Nat
  | selectClose _ _ cost => cost
  | lcaClose _ _ _ cost => cost
  | rankClose _ _ cost => cost

end WholeQueryLeafTraceEvent

/-- Sum of modeled costs recorded in a whole-query leaf trace. -/
def wholeQueryLeafTraceCost : List WholeQueryLeafTraceEvent -> Nat
  | [] => 0
  | event :: rest => event.cost + wholeQueryLeafTraceCost rest

@[simp] theorem wholeQueryLeafTraceCost_nil :
    wholeQueryLeafTraceCost [] = 0 := by
  rfl

@[simp] theorem wholeQueryLeafTraceCost_cons
    (event : WholeQueryLeafTraceEvent)
    (rest : List WholeQueryLeafTraceEvent) :
    wholeQueryLeafTraceCost (event :: rest) =
      event.cost + wholeQueryLeafTraceCost rest := by
  rfl

theorem wholeQueryLeafTraceCost_append
    (leftTrace rightTrace : List WholeQueryLeafTraceEvent) :
    wholeQueryLeafTraceCost (leftTrace ++ rightTrace) =
      wholeQueryLeafTraceCost leftTrace +
        wholeQueryLeafTraceCost rightTrace := by
  induction leftTrace with
  | nil =>
      simp [wholeQueryLeafTraceCost]
  | cons event rest ih =>
      simp [wholeQueryLeafTraceCost, ih, Nat.add_assoc]

/-- Result of evaluating whole-query control while preserving leaf trace data. -/
structure WholeQueryLeafTraceResult where
  state : WholeQueryState
  trace : List WholeQueryLeafTraceEvent
deriving Repr

namespace WholeQueryLeafTraceResult

/-- Project a leaf-trace result back to the theorem-facing `Costed` carrier. -/
def toCosted (result : WholeQueryLeafTraceResult) : Costed WholeQueryState where
  value := result.state
  cost := wholeQueryLeafTraceCost result.trace

@[simp] theorem toCosted_value (result : WholeQueryLeafTraceResult) :
    result.toCosted.value = result.state := by
  rfl

@[simp] theorem toCosted_cost (result : WholeQueryLeafTraceResult) :
    result.toCosted.cost = wholeQueryLeafTraceCost result.trace := by
  rfl

end WholeQueryLeafTraceResult

namespace WholeQueryInstr

/-- Execute one instruction while preserving a domain-leaf trace. -/
def evalLeafTrace (shape : Cartesian.CartesianShape) (left right : Nat)
    (instr : WholeQueryInstr) (state : WholeQueryState) :
    WholeQueryLeafTraceResult :=
  match instr with
  | .selectClose dst idx =>
      let query :=
        concreteBPNativeSelectCloseRegisterInterpretedCosted shape
          (idx.eval left right state)
      { state := state.setOpt dst query.value
        trace :=
          [WholeQueryLeafTraceEvent.selectClose
            (idx.eval left right state) query.value query.cost] }
  | .lcaClose dst leftReg rightReg =>
      match state.opt leftReg, state.opt rightReg with
      | some leftClose, some rightClose =>
          let query :=
            concreteBPNativeLCACloseInterpretedCosted shape
              leftClose rightClose
          { state := state.setOpt dst query.value
            trace :=
              [WholeQueryLeafTraceEvent.lcaClose
                leftClose rightClose query.value query.cost] }
      | _, _ =>
          { state := state.setOpt dst none, trace := [] }
  | .rankCloseIfSome dst guard pos =>
      match state.opt guard with
      | some _ =>
          let query :=
            concreteBPNativeRankCloseRegisterInterpretedCosted shape
              (pos.eval left right state)
          { state := state.setNat dst query.value
            trace :=
              [WholeQueryLeafTraceEvent.rankClose
                (pos.eval left right state) query.value query.cost] }
      | none => { state := state, trace := [] }
  | .outputPredIfSome dst guard src =>
      match state.opt guard with
      | some _ =>
          { state := state.setOpt dst (some (state.nat src - 1))
            trace := [] }
      | none =>
          { state := state.setOpt dst none, trace := [] }

theorem evalLeafTrace_refines_eval
    (shape : Cartesian.CartesianShape) (left right : Nat)
    (instr : WholeQueryInstr) (state : WholeQueryState) :
    (instr.evalLeafTrace shape left right state).toCosted =
      instr.eval shape left right state := by
  cases instr with
  | selectClose dst idx =>
      apply Costed.ext <;>
        simp [evalLeafTrace, eval, WholeQueryLeafTraceResult.toCosted,
          wholeQueryLeafTraceCost, WholeQueryLeafTraceEvent.cost,
          Costed.map, Costed.bind, Costed.pure]
  | lcaClose dst leftReg rightReg =>
      cases hleft : state.opt leftReg <;>
        cases hright : state.opt rightReg <;>
          apply Costed.ext <;>
            simp [evalLeafTrace, eval, hleft, hright,
              WholeQueryLeafTraceResult.toCosted, wholeQueryLeafTraceCost,
              WholeQueryLeafTraceEvent.cost, Costed.map, Costed.bind,
              Costed.pure]
  | rankCloseIfSome dst guard pos =>
      cases hguard : state.opt guard <;>
        apply Costed.ext <;>
          simp [evalLeafTrace, eval, hguard,
            WholeQueryLeafTraceResult.toCosted, wholeQueryLeafTraceCost,
            WholeQueryLeafTraceEvent.cost, Costed.map, Costed.bind,
            Costed.pure]
  | outputPredIfSome dst guard src =>
      cases hguard : state.opt guard <;>
        apply Costed.ext <;>
          simp [evalLeafTrace, eval, hguard,
            WholeQueryLeafTraceResult.toCosted, Costed.pure]

end WholeQueryInstr

namespace WholeQueryProgram

/-- Execute a whole-query control program while preserving leaf trace data. -/
def evalLeafTrace (shape : Cartesian.CartesianShape) (left right : Nat) :
    WholeQueryProgram -> WholeQueryState -> WholeQueryLeafTraceResult
  | [], state => { state := state, trace := [] }
  | instr :: rest, state =>
      let first := instr.evalLeafTrace shape left right state
      let tail := evalLeafTrace shape left right rest first.state
      { state := tail.state, trace := first.trace ++ tail.trace }

theorem evalLeafTrace_refines_eval
    (shape : Cartesian.CartesianShape) (left right : Nat)
    (program : WholeQueryProgram) (state : WholeQueryState) :
    (evalLeafTrace shape left right program state).toCosted =
      eval shape left right program state := by
  induction program generalizing state with
  | nil =>
      simp [evalLeafTrace, eval, WholeQueryLeafTraceResult.toCosted,
        Costed.pure]
  | cons instr rest ih =>
      unfold evalLeafTrace eval
      let first := instr.evalLeafTrace shape left right state
      let tail := evalLeafTrace shape left right rest first.state
      have hfirst :
          first.toCosted = instr.eval shape left right state := by
        simpa [first] using
          WholeQueryInstr.evalLeafTrace_refines_eval shape left right instr
            state
      have htail :
          tail.toCosted = eval shape left right rest first.state := by
        simpa [tail] using ih first.state
      apply Costed.ext
      · rw [← hfirst]
        simpa [WholeQueryLeafTraceResult.toCosted, Costed.bind] using
          congrArg Costed.value htail
      · rw [← hfirst]
        change
          wholeQueryLeafTraceCost (first.trace ++ tail.trace) =
            first.toCosted.cost +
              (eval shape left right rest first.state).cost
        rw [wholeQueryLeafTraceCost_append]
        have htailCost :
            wholeQueryLeafTraceCost tail.trace =
              (eval shape left right rest first.state).cost := by
          simpa [WholeQueryLeafTraceResult.toCosted] using
            congrArg Costed.cost htail
        simp [WholeQueryLeafTraceResult.toCosted, htailCost]

end WholeQueryProgram

namespace WholeQueryInstr

/-- Execute one instruction while preserving a unified `WordRAM.TraceEvent` stream. -/
def evalWordTrace (shape : Cartesian.CartesianShape) (left right : Nat)
    (instr : WholeQueryInstr) (state : WholeQueryState) :
    WordRAM.TraceResult WholeQueryState :=
  match instr with
  | .selectClose dst idx =>
      WordRAM.TraceResult.map
        (fun close? => state.setOpt dst close?)
        (concreteBPNativeSelectCloseRegisterWordTraceResult shape
          (idx.eval left right state))
  | .lcaClose dst leftReg rightReg =>
      match state.opt leftReg, state.opt rightReg with
      | some leftClose, some rightClose =>
          WordRAM.TraceResult.map
            (fun answer? => state.setOpt dst answer?)
            (concreteBPNativeLCACloseWordTraceResult shape
              leftClose rightClose)
      | _, _ => WordRAM.TraceResult.pure (state.setOpt dst none)
  | .rankCloseIfSome dst guard pos =>
      match state.opt guard with
      | some _ =>
          WordRAM.TraceResult.map
            (fun closeRank => state.setNat dst closeRank)
            (concreteBPNativeRankCloseRegisterWordTraceResult shape
              (pos.eval left right state))
      | none => WordRAM.TraceResult.pure state
  | .outputPredIfSome dst guard src =>
      match state.opt guard with
      | some _ =>
          WordRAM.TraceResult.pure
            (state.setOpt dst (some (state.nat src - 1)))
      | none =>
          WordRAM.TraceResult.pure (state.setOpt dst none)

theorem evalWordTrace_refines_eval
    (shape : Cartesian.CartesianShape) (left right : Nat)
    (instr : WholeQueryInstr) (state : WholeQueryState) :
    (instr.evalWordTrace shape left right state).toCosted =
      instr.eval shape left right state := by
  cases instr with
  | selectClose dst idx =>
      simp [evalWordTrace, eval,
        concreteBPNativeSelectCloseRegisterWordTraceResult_refines_registerInterpretedCosted,
        WordRAM.TraceResult.map_toCosted, Costed.map]
  | lcaClose dst leftReg rightReg =>
      cases hleft : state.opt leftReg <;>
        cases hright : state.opt rightReg <;>
          simp [evalWordTrace, eval, hleft, hright,
            concreteBPNativeLCACloseWordTraceResult_refines_interpretedCosted,
            WordRAM.TraceResult.map_toCosted,
            WordRAM.TraceResult.pure_toCosted, Costed.map, Costed.pure]
  | rankCloseIfSome dst guard pos =>
      cases hguard : state.opt guard <;>
        simp [evalWordTrace, eval, hguard,
          concreteBPNativeRankCloseRegisterWordTraceResult_refines_registerInterpretedCosted,
          WordRAM.TraceResult.map_toCosted,
          WordRAM.TraceResult.pure_toCosted, Costed.map, Costed.pure]
  | outputPredIfSome dst guard src =>
      cases hguard : state.opt guard <;>
        simp [evalWordTrace, eval, hguard,
          WordRAM.TraceResult.pure_toCosted, Costed.pure]

/--
Execute one instruction in the all-size global-segment replay.

This uses the same global segment convention as the large-regime replay, but
the compact close/LCA instruction follows the total all-size structural close
trace. The old tiny/zero fallback work is replayed through payload-backed
finite-small tables rather than synthetic cost-only events.
-/
def evalGlobalWordTrace (shape : Cartesian.CartesianShape)
    (left right : Nat) (instr : WholeQueryInstr)
    (state : WholeQueryState) : WordRAM.TraceResult WholeQueryState :=
  match instr with
  | .selectClose dst idx =>
      WordRAM.TraceResult.map
        (fun close? => state.setOpt dst close?)
        (concreteBPNativeSelectCloseGlobalWordTraceResult shape
          (idx.eval left right state))
  | .lcaClose dst leftReg rightReg =>
      match state.opt leftReg, state.opt rightReg with
      | some leftClose, some rightClose =>
          WordRAM.TraceResult.map
            (fun answer? => state.setOpt dst answer?)
            (concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
              shape leftClose rightClose)
      | _, _ => WordRAM.TraceResult.pure (state.setOpt dst none)
  | .rankCloseIfSome dst guard pos =>
      match state.opt guard with
      | some _ =>
          WordRAM.TraceResult.map
            (fun closeRank => state.setNat dst closeRank)
            (concreteBPNativeRankCloseWordTraceResultAtSegment
              shape concreteBPNativeRankCloseTraceSegmentBase
              (pos.eval left right state))
      | none => WordRAM.TraceResult.pure state
  | .outputPredIfSome dst guard src =>
      match state.opt guard with
      | some _ =>
          WordRAM.TraceResult.pure
            (state.setOpt dst (some (state.nat src - 1)))
      | none =>
          WordRAM.TraceResult.pure (state.setOpt dst none)

/-- Read-producing reviewer leaf selected by the actual global evaluator
instruction branch.  Output-only instructions have no read leaf. -/
def reviewerReadLeaf? : WholeQueryInstr -> Option ReviewerReadLeaf
  | .selectClose _ _ => some .selectClose
  | .lcaClose _ _ _ => some .canonicalClose
  | .rankCloseIfSome _ _ _ => some .rankClose
  | .outputPredIfSome _ _ _ => none

/--
Checked expansion of a reviewer leaf into the branch executed by
`evalGlobalWordTrace`.  This predicate mentions the actual evaluator result,
so a free-standing controller label cannot inhabit it.
 -/
def reviewerReadLeafEvaluatorBranch
    (shape : Cartesian.CartesianShape) (left right : Nat)
    (state : WholeQueryState) (leaf : ReviewerReadLeaf)
    (instr : WholeQueryInstr) : Prop :=
  match leaf with
  | .selectClose =>
      ∃ dst idx,
        instr = .selectClose dst idx ∧
        instr.evalGlobalWordTrace shape left right state =
          WordRAM.TraceResult.map
            (fun close? => state.setOpt dst close?)
            (concreteBPNativeSelectCloseGlobalWordTraceResult shape
              (idx.eval left right state))
  | .canonicalClose =>
      ∃ dst leftReg rightReg,
        instr = .lcaClose dst leftReg rightReg ∧
        instr.evalGlobalWordTrace shape left right state =
          match state.opt leftReg, state.opt rightReg with
          | some leftClose, some rightClose =>
              WordRAM.TraceResult.map
                (fun answer? => state.setOpt dst answer?)
                (concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
                  shape leftClose rightClose)
          | _, _ => WordRAM.TraceResult.pure (state.setOpt dst none)
  | .rankClose =>
      ∃ dst guard pos,
        instr = .rankCloseIfSome dst guard pos ∧
        instr.evalGlobalWordTrace shape left right state =
          match state.opt guard with
          | some _ =>
              WordRAM.TraceResult.map
                (fun closeRank => state.setNat dst closeRank)
                (concreteBPNativeRankCloseWordTraceResultAtSegment
                  shape concreteBPNativeRankCloseTraceSegmentBase
                  (pos.eval left right state))
          | none => WordRAM.TraceResult.pure state

theorem reviewerReadLeaf?_some_evaluatorBranch
    (shape : Cartesian.CartesianShape) (left right : Nat)
    (state : WholeQueryState) (leaf : ReviewerReadLeaf)
    (instr : WholeQueryInstr)
    (hleaf : instr.reviewerReadLeaf? = some leaf) :
    reviewerReadLeafEvaluatorBranch shape left right state leaf instr := by
  cases instr with
  | selectClose dst idx =>
      simp [reviewerReadLeaf?] at hleaf
      subst leaf
      exact ⟨dst, idx, rfl, rfl⟩
  | lcaClose dst leftReg rightReg =>
      simp [reviewerReadLeaf?] at hleaf
      subst leaf
      exact ⟨dst, leftReg, rightReg, rfl, rfl⟩
  | rankCloseIfSome dst guard pos =>
      simp [reviewerReadLeaf?] at hleaf
      subst leaf
      exact ⟨dst, guard, pos, rfl, rfl⟩
  | outputPredIfSome dst guard src =>
      simp [reviewerReadLeaf?] at hleaf

theorem evalGlobalWordTrace_refines_eval
    (shape : Cartesian.CartesianShape)
    (left right : Nat) (instr : WholeQueryInstr)
    (state : WholeQueryState) :
    (instr.evalGlobalWordTrace shape left right state).toCosted =
      instr.evalCanonical shape left right state := by
  cases instr with
  | selectClose dst idx =>
      simp [evalGlobalWordTrace, evalCanonical,
        concreteBPNativeSelectCloseGlobalWordTraceResult_refines_interpretedCosted,
        WordRAM.TraceResult.map_toCosted, Costed.map]
  | lcaClose dst leftReg rightReg =>
      cases hleft : state.opt leftReg <;>
        cases hright : state.opt rightReg <;>
          simp [evalGlobalWordTrace, evalCanonical, hleft, hright,
            concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural_refines_interpretedCosted,
            WordRAM.TraceResult.map_toCosted,
            WordRAM.TraceResult.pure_toCosted, Costed.map, Costed.pure]
  | rankCloseIfSome dst guard pos =>
      cases hguard : state.opt guard <;>
        simp [evalGlobalWordTrace, evalCanonical, hguard,
          concreteBPNativeRankCloseWordTraceResultAtSegment_refines_interpretedCosted,
          WordRAM.TraceResult.map_toCosted,
          WordRAM.TraceResult.pure_toCosted, Costed.map, Costed.pure]
  | outputPredIfSome dst guard src =>
      cases hguard : state.opt guard <;>
        simp [evalGlobalWordTrace, evalCanonical, hguard,
          WordRAM.TraceResult.pure_toCosted, Costed.pure]

theorem evalGlobalWordTrace_matchesReadStore
    (shape : Cartesian.CartesianShape)
    (left right : Nat) (instr : WholeQueryInstr)
    (state : WholeQueryState) :
    forall event,
      List.Mem event
          (instr.evalGlobalWordTrace shape left right state).trace ->
        event.matchesReadStore
          (concreteBPNativeSuccinctRMQGlobalReadStore shape) := by
  cases instr with
  | selectClose dst idx =>
      simp [evalGlobalWordTrace]
      exact
        concreteBPNativeSelectCloseGlobalWordTraceResult_matchesReadStore
          shape (idx.eval left right state)
  | lcaClose dst leftReg rightReg =>
      cases hleft : state.opt leftReg with
      | none =>
          cases hright : state.opt rightReg <;>
            simp [evalGlobalWordTrace, hleft, hright] <;>
            intro event hmem <;> cases hmem
      | some leftClose =>
          cases hright : state.opt rightReg with
          | none =>
              simp [evalGlobalWordTrace, hleft, hright]
              intro event hmem
              cases hmem
          | some rightClose =>
              simp [evalGlobalWordTrace, hleft, hright]
              exact
                concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural_matchesReadStore
                  shape leftClose rightClose
  | rankCloseIfSome dst guard pos =>
      cases hguard : state.opt guard with
      | none =>
          simp [evalGlobalWordTrace, hguard]
          intro event hmem
          cases hmem
      | some _ =>
        simp [evalGlobalWordTrace, hguard]
        exact
          concreteBPNativeRankCloseCanonicalGlobalWordTraceResult_matchesReadStore
            shape (pos.eval left right state)
  | outputPredIfSome dst guard src =>
      cases hguard : state.opt guard <;>
        simp [evalGlobalWordTrace, hguard] <;>
        intro event hmem <;> cases hmem

theorem evalGlobalWordTrace_no_syntheticCostOnlyPrimitive
    (shape : Cartesian.CartesianShape)
    (left right : Nat) (instr : WholeQueryInstr)
    (state : WholeQueryState) :
    forall event,
      List.Mem event
          (instr.evalGlobalWordTrace shape left right state).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  cases instr with
  | selectClose dst idx =>
      simp [evalGlobalWordTrace]
      exact
        concreteBPNativeSelectCloseGlobalWordTraceResult_no_syntheticCostOnlyPrimitive
          shape (idx.eval left right state)
  | lcaClose dst leftReg rightReg =>
      cases hleft : state.opt leftReg with
      | none =>
          cases hright : state.opt rightReg <;>
            simp [evalGlobalWordTrace, hleft, hright] <;>
            intro event hmem <;> cases hmem
      | some leftClose =>
          cases hright : state.opt rightReg with
          | none =>
              simp [evalGlobalWordTrace, hleft, hright]
              intro event hmem
              cases hmem
          | some rightClose =>
              simp [evalGlobalWordTrace, hleft, hright]
              exact
                concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural_no_syntheticCostOnlyPrimitive
                  shape leftClose rightClose
  | rankCloseIfSome dst guard pos =>
      cases hguard : state.opt guard with
      | none =>
          simp [evalGlobalWordTrace, hguard]
          intro event hmem
          cases hmem
      | some _ =>
        simp [evalGlobalWordTrace, hguard]
        exact
          concreteBPNativeRankCloseGlobalWordTraceResult_no_syntheticCostOnlyPrimitive
            shape (pos.eval left right state)
  | outputPredIfSome dst guard src =>
      cases hguard : state.opt guard <;>
        simp [evalGlobalWordTrace, hguard] <;>
        intro event hmem <;> cases hmem

theorem evalGlobalWordTrace_noFiniteSmallInteriorSuccessfulRead_of_ready
    (shape : Cartesian.CartesianShape)
    (hready : SuccinctClose.concreteBPRelativeRmmInteriorReady shape)
    (left right : Nat) (instr : WholeQueryInstr)
    (state : WholeQueryState) :
    forall event,
      List.Mem event
          (instr.evalGlobalWordTrace shape left right state).trace ->
        concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead
          event := by
  cases instr with
  | selectClose dst idx =>
      simp [evalGlobalWordTrace]
      exact
        concreteBPNativeSelectCloseGlobalWordTraceResult_noFiniteSmallInteriorSuccessfulRead
          shape (idx.eval left right state)
  | lcaClose dst leftReg rightReg =>
      cases hleft : state.opt leftReg with
      | none =>
          cases hright : state.opt rightReg <;>
            simp [evalGlobalWordTrace, hleft, hright] <;>
            intro event hmem <;> cases hmem
      | some leftClose =>
          cases hright : state.opt rightReg with
          | none =>
              simp [evalGlobalWordTrace, hleft, hright]
              intro event hmem
              cases hmem
          | some rightClose =>
              simp [evalGlobalWordTrace, hleft, hright]
              exact
                concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural_noFiniteSmallInteriorSuccessfulRead_of_ready
                  shape hready leftClose rightClose
  | rankCloseIfSome dst guard pos =>
      cases hguard : state.opt guard with
      | none =>
          simp [evalGlobalWordTrace, hguard]
          intro event hmem
          cases hmem
      | some _ =>
        simp [evalGlobalWordTrace, hguard]
        exact
          concreteBPNativeSuccinctRMQRankCloseGlobalWordTraceResult_noFiniteSmallInteriorSuccessfulRead
            shape (pos.eval left right state)
  | outputPredIfSome dst guard src =>
      cases hguard : state.opt guard <;>
        simp [evalGlobalWordTrace, hguard] <;>
        intro event hmem <;> cases hmem

theorem evalGlobalWordTrace_noFiniteSmallInteriorSuccessfulRead
    (shape : Cartesian.CartesianShape)
    (left right : Nat) (instr : WholeQueryInstr)
    (state : WholeQueryState) :
    forall event,
      List.Mem event
          (instr.evalGlobalWordTrace shape left right state).trace ->
        concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead
          event := by
  cases instr with
  | selectClose dst idx =>
      simp [evalGlobalWordTrace]
      exact
        concreteBPNativeSelectCloseGlobalWordTraceResult_noFiniteSmallInteriorSuccessfulRead
          shape (idx.eval left right state)
  | lcaClose dst leftReg rightReg =>
      cases hleft : state.opt leftReg with
      | none =>
          cases hright : state.opt rightReg <;>
            simp [evalGlobalWordTrace, hleft, hright] <;>
            intro event hmem <;> cases hmem
      | some leftClose =>
          cases hright : state.opt rightReg with
          | none =>
              simp [evalGlobalWordTrace, hleft, hright]
              intro event hmem
              cases hmem
          | some rightClose =>
              simp [evalGlobalWordTrace, hleft, hright]
              exact
                concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural_noFiniteSmallInteriorSuccessfulRead
                  shape leftClose rightClose
  | rankCloseIfSome dst guard pos =>
      cases hguard : state.opt guard with
      | none =>
          simp [evalGlobalWordTrace, hguard]
          intro event hmem
          cases hmem
      | some _ =>
        simp [evalGlobalWordTrace, hguard]
        exact
          concreteBPNativeSuccinctRMQRankCloseGlobalWordTraceResult_noFiniteSmallInteriorSuccessfulRead
            shape (pos.eval left right state)
  | outputPredIfSome dst guard src =>
      cases hguard : state.opt guard <;>
        simp [evalGlobalWordTrace, hguard] <;>
        intro event hmem <;> cases hmem

theorem evalGlobalWordTrace_noReadyCloseSuccessfulRead_of_not_ready
    (shape : Cartesian.CartesianShape)
    (hnotReady : ¬ SuccinctClose.concreteBPRelativeRmmInteriorReady shape)
    (left right : Nat) (instr : WholeQueryInstr)
    (state : WholeQueryState) :
    forall event,
      List.Mem event
          (instr.evalGlobalWordTrace shape left right state).trace ->
        concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead
          event := by
  cases instr with
  | selectClose dst idx =>
      simp [evalGlobalWordTrace]
      exact
        concreteBPNativeSelectCloseGlobalWordTraceResult_noReadyCloseSuccessfulRead
          shape (idx.eval left right state)
  | lcaClose dst leftReg rightReg =>
      cases hleft : state.opt leftReg with
      | none =>
          cases hright : state.opt rightReg <;>
            simp [evalGlobalWordTrace, hleft, hright] <;>
            intro event hmem <;> cases hmem
      | some leftClose =>
          cases hright : state.opt rightReg with
          | none =>
              simp [evalGlobalWordTrace, hleft, hright]
              intro event hmem
              cases hmem
          | some rightClose =>
              simp [evalGlobalWordTrace, hleft, hright]
              exact
                concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural_noReadyCloseSuccessfulRead_of_not_ready
                  shape hnotReady leftClose rightClose
  | rankCloseIfSome dst guard pos =>
      cases hguard : state.opt guard with
      | none =>
          simp [evalGlobalWordTrace, hguard]
          intro event hmem
          cases hmem
      | some _ =>
        simp [evalGlobalWordTrace, hguard]
        exact
          concreteBPNativeSuccinctRMQRankCloseGlobalWordTraceResult_noReadyCloseSuccessfulRead
            shape (pos.eval left right state)
  | outputPredIfSome dst guard src =>
      cases hguard : state.opt guard <;>
        simp [evalGlobalWordTrace, hguard] <;>
        intro event hmem <;> cases hmem

/--
Execute one instruction in the large-regime replay.

Only the compact close/LCA instruction differs from `evalWordTrace`: it uses the
large-regime LCA-close trace, which expands the positive-block interior path
instead of the all-size structural branch split.
-/
def evalWordTraceOfSizeGe (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size) (left right : Nat)
    (instr : WholeQueryInstr) (state : WholeQueryState) :
    WordRAM.TraceResult WholeQueryState :=
  match instr with
  | .selectClose dst idx =>
      WordRAM.TraceResult.map
        (fun close? => state.setOpt dst close?)
        (concreteBPNativeSelectCloseRegisterWordTraceResult shape
          (idx.eval left right state))
  | .lcaClose dst leftReg rightReg =>
      match state.opt leftReg, state.opt rightReg with
      | some leftClose, some rightClose =>
          WordRAM.TraceResult.map
            (fun answer? => state.setOpt dst answer?)
            (concreteBPNativeLCACloseWordTraceResultOfSizeGe shape hsize
              leftClose rightClose)
      | _, _ => WordRAM.TraceResult.pure (state.setOpt dst none)
  | .rankCloseIfSome dst guard pos =>
      match state.opt guard with
      | some _ =>
          WordRAM.TraceResult.map
            (fun closeRank => state.setNat dst closeRank)
            (concreteBPNativeRankCloseRegisterWordTraceResult shape
              (pos.eval left right state))
      | none => WordRAM.TraceResult.pure state
  | .outputPredIfSome dst guard src =>
      match state.opt guard with
      | some _ =>
          WordRAM.TraceResult.pure
            (state.setOpt dst (some (state.nat src - 1)))
      | none =>
          WordRAM.TraceResult.pure (state.setOpt dst none)

theorem evalWordTraceOfSizeGe_refines_eval
    (shape : Cartesian.CartesianShape) (hsize : 2 ^ 128 <= shape.size)
    (left right : Nat) (instr : WholeQueryInstr) (state : WholeQueryState) :
    (instr.evalWordTraceOfSizeGe shape hsize left right state).toCosted =
      instr.eval shape left right state := by
  cases instr with
  | selectClose dst idx =>
      simp [evalWordTraceOfSizeGe, eval,
        concreteBPNativeSelectCloseRegisterWordTraceResult_refines_registerInterpretedCosted,
        WordRAM.TraceResult.map_toCosted, Costed.map]
  | lcaClose dst leftReg rightReg =>
      cases hleft : state.opt leftReg <;>
        cases hright : state.opt rightReg <;>
          simp [evalWordTraceOfSizeGe, eval, hleft, hright,
            concreteBPNativeLCACloseWordTraceResultOfSizeGe_refines_interpretedCosted,
            WordRAM.TraceResult.map_toCosted,
            WordRAM.TraceResult.pure_toCosted, Costed.map, Costed.pure]
  | rankCloseIfSome dst guard pos =>
      cases hguard : state.opt guard <;>
        simp [evalWordTraceOfSizeGe, eval, hguard,
          concreteBPNativeRankCloseRegisterWordTraceResult_refines_registerInterpretedCosted,
          WordRAM.TraceResult.map_toCosted,
          WordRAM.TraceResult.pure_toCosted, Costed.map, Costed.pure]
  | outputPredIfSome dst guard src =>
      cases hguard : state.opt guard <;>
        simp [evalWordTraceOfSizeGe, eval, hguard,
          WordRAM.TraceResult.pure_toCosted, Costed.pure]

/--
Execute one instruction in the large-regime global-segment replay.

This is the first whole-query evaluator whose structural leaves agree on a
single segment layout: shared BP code at segment `0`, close-select auxiliary
segments `1` through `16`, rank segments `17` through `19`, and compact
close/LCA interior segments `20` through `25`.
-/
def evalGlobalWordTraceOfSizeGe (shape : Cartesian.CartesianShape)
    (_hsize : 2 ^ 128 <= shape.size) (left right : Nat)
    (instr : WholeQueryInstr) (state : WholeQueryState) :
    WordRAM.TraceResult WholeQueryState :=
  match instr with
  | .selectClose dst idx =>
      WordRAM.TraceResult.map
        (fun close? => state.setOpt dst close?)
        (concreteBPNativeSelectCloseGlobalWordTraceResult shape
          (idx.eval left right state))
  | .lcaClose dst leftReg rightReg =>
      match state.opt leftReg, state.opt rightReg with
      | some leftClose, some rightClose =>
          WordRAM.TraceResult.map
            (fun answer? => state.setOpt dst answer?)
            (concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
              shape
              leftClose rightClose)
      | _, _ => WordRAM.TraceResult.pure (state.setOpt dst none)
  | .rankCloseIfSome dst guard pos =>
      match state.opt guard with
      | some _ =>
          WordRAM.TraceResult.map
            (fun closeRank => state.setNat dst closeRank)
            (concreteBPNativeRankCloseWordTraceResultAtSegment
              shape concreteBPNativeRankCloseTraceSegmentBase
              (pos.eval left right state))
      | none => WordRAM.TraceResult.pure state
  | .outputPredIfSome dst guard src =>
      match state.opt guard with
      | some _ =>
          WordRAM.TraceResult.pure
            (state.setOpt dst (some (state.nat src - 1)))
      | none =>
          WordRAM.TraceResult.pure (state.setOpt dst none)

theorem evalGlobalWordTraceOfSizeGe_refines_eval
    (shape : Cartesian.CartesianShape) (hsize : 2 ^ 128 <= shape.size)
    (left right : Nat) (instr : WholeQueryInstr) (state : WholeQueryState) :
    (instr.evalGlobalWordTraceOfSizeGe shape hsize left right state).toCosted =
      instr.evalCanonical shape left right state := by
  cases instr with
  | selectClose dst idx =>
      simp [evalGlobalWordTraceOfSizeGe, evalCanonical,
        concreteBPNativeSelectCloseGlobalWordTraceResult_refines_interpretedCosted,
        WordRAM.TraceResult.map_toCosted, Costed.map]
  | lcaClose dst leftReg rightReg =>
      cases hleft : state.opt leftReg <;>
        cases hright : state.opt rightReg <;>
          simp [evalGlobalWordTraceOfSizeGe, evalCanonical, hleft, hright,
            concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural_refines_interpretedCosted,
            WordRAM.TraceResult.map_toCosted,
            WordRAM.TraceResult.pure_toCosted, Costed.map, Costed.pure]
  | rankCloseIfSome dst guard pos =>
      cases hguard : state.opt guard <;>
        simp [evalGlobalWordTraceOfSizeGe, evalCanonical, hguard,
          concreteBPNativeRankCloseWordTraceResultAtSegment_refines_interpretedCosted,
          WordRAM.TraceResult.map_toCosted,
          WordRAM.TraceResult.pure_toCosted, Costed.map, Costed.pure]
  | outputPredIfSome dst guard src =>
      cases hguard : state.opt guard <;>
        simp [evalGlobalWordTraceOfSizeGe, evalCanonical, hguard,
          WordRAM.TraceResult.pure_toCosted, Costed.pure]

theorem evalGlobalWordTraceOfSizeGe_matchesReadStore
    (shape : Cartesian.CartesianShape) (hsize : 2 ^ 128 <= shape.size)
    (left right : Nat) (instr : WholeQueryInstr)
    (state : WholeQueryState) :
    forall event,
      List.Mem event
          (instr.evalGlobalWordTraceOfSizeGe
            shape hsize left right state).trace ->
        event.matchesReadStore
          (concreteBPNativeSuccinctRMQGlobalReadStore shape) := by
  cases instr with
  | selectClose dst idx =>
      simp [evalGlobalWordTraceOfSizeGe]
      exact
        concreteBPNativeSelectCloseGlobalWordTraceResult_matchesReadStore
          shape (idx.eval left right state)
  | lcaClose dst leftReg rightReg =>
      cases hleft : state.opt leftReg with
      | none =>
          cases hright : state.opt rightReg <;>
            simp [evalGlobalWordTraceOfSizeGe, hleft, hright] <;>
            intro event hmem <;> cases hmem
      | some leftClose =>
          cases hright : state.opt rightReg with
          | none =>
              simp [evalGlobalWordTraceOfSizeGe, hleft, hright]
              intro event hmem
              cases hmem
          | some rightClose =>
              simp [evalGlobalWordTraceOfSizeGe, hleft, hright]
              exact
                concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural_matchesReadStore
                  shape leftClose rightClose
  | rankCloseIfSome dst guard pos =>
      cases hguard : state.opt guard with
      | none =>
          simp [evalGlobalWordTraceOfSizeGe, hguard]
          intro event hmem
          cases hmem
      | some _ =>
        simp [evalGlobalWordTraceOfSizeGe, hguard]
        exact
          concreteBPNativeRankCloseCanonicalGlobalWordTraceResult_matchesReadStore
            shape (pos.eval left right state)
  | outputPredIfSome dst guard src =>
      cases hguard : state.opt guard <;>
        simp [evalGlobalWordTraceOfSizeGe, hguard] <;>
        intro event hmem <;> cases hmem

end WholeQueryInstr

namespace WholeQueryProgram

/-- Execute a whole-query program while preserving one `WordRAM.TraceEvent` list. -/
def evalWordTrace (shape : Cartesian.CartesianShape) (left right : Nat) :
    WholeQueryProgram -> WholeQueryState -> WordRAM.TraceResult WholeQueryState
  | [], state => WordRAM.TraceResult.pure state
  | instr :: rest, state =>
      WordRAM.TraceResult.bind
        (instr.evalWordTrace shape left right state) fun state' =>
          evalWordTrace shape left right rest state'

theorem evalWordTrace_refines_eval
    (shape : Cartesian.CartesianShape) (left right : Nat)
    (program : WholeQueryProgram) (state : WholeQueryState) :
    (evalWordTrace shape left right program state).toCosted =
      eval shape left right program state := by
  induction program generalizing state with
  | nil =>
      simp [evalWordTrace, eval, WordRAM.TraceResult.pure_toCosted,
        Costed.pure]
  | cons instr rest ih =>
      simp [evalWordTrace, eval, WordRAM.TraceResult.bind_toCosted,
        WholeQueryInstr.evalWordTrace_refines_eval, ih, Costed.bind]

/--
Execute a whole-query program in the all-size global-segment replay.

This preserves one `WordRAM.TraceEvent` stream under the final query's shared
payload-store layout. The close/LCA instruction uses the total all-size
structural trace, so events come from payload-backed reads or charged word
primitives while payload reads retain global segment addresses.
-/
def evalGlobalWordTrace (shape : Cartesian.CartesianShape)
    (left right : Nat) :
    WholeQueryProgram -> WholeQueryState -> WordRAM.TraceResult WholeQueryState
  | [], state => WordRAM.TraceResult.pure state
  | instr :: rest, state =>
      WordRAM.TraceResult.bind
        (instr.evalGlobalWordTrace shape left right state)
        fun state' =>
      evalGlobalWordTrace shape left right rest state'

/--
Indexed occurrence witness for one event emitted by one instruction in a
closed program fold.  Besides the concrete program split and folded pre-state,
the relation retains the instruction index, instruction-local index, and the
prefix-length equation embedding that local occurrence at the original global
position.  Equal event values at different positions therefore remain
different proof obligations.
-/
def ProducesEventAt
    (shape : Cartesian.CartesianShape) (left right : Nat)
    (event : WordRAM.TraceEvent) (program : WholeQueryProgram)
    (state : WholeQueryState) (globalPos : Nat)
    (instrPos : Nat) (instr : WholeQueryInstr) (preState : WholeQueryState)
    (localPos : Nat) : Prop :=
  ∃ before after,
    program = before ++ instr :: after ∧
    instrPos = before.length ∧
    preState =
      (evalGlobalWordTrace shape left right before state).value ∧
    globalPos =
      (evalGlobalWordTrace shape left right before state).trace.length +
        localPos ∧
    (instr.evalGlobalWordTrace shape left right preState).trace[localPos]? =
      some event

/-- Every indexed program-trace occurrence exposes the exact instruction
occurrence, folded pre-state, and local occurrence embedded at that position. -/
theorem evalGlobalWordTrace_getElem?_producer
    (shape : Cartesian.CartesianShape) (left right : Nat)
    (program : WholeQueryProgram) (state : WholeQueryState)
    (globalPos : Nat) (event : WordRAM.TraceEvent)
    (hget : (evalGlobalWordTrace shape left right program state).trace[globalPos]? =
      some event) :
    ∃ instrPos instr preState localPos,
      ProducesEventAt shape left right event program state globalPos
        instrPos instr preState localPos := by
  induction program generalizing state globalPos with
  | nil =>
      simp [evalGlobalWordTrace] at hget
  | cons first rest ih =>
      simp only [evalGlobalWordTrace, WordRAM.TraceResult.bind_trace] at hget
      by_cases hfirst : globalPos <
          (first.evalGlobalWordTrace shape left right state).trace.length
      · have hlocal :
            (first.evalGlobalWordTrace shape left right state).trace[globalPos]? =
              some event := by
          simpa [List.getElem?_append, hfirst] using hget
        refine ⟨0, first, state, globalPos, [], rest, rfl, rfl, rfl, ?_, hlocal⟩
        simp [evalGlobalWordTrace]
      · have htail :
            (evalGlobalWordTrace shape left right rest
              (first.evalGlobalWordTrace shape left right state).value).trace[
                globalPos -
                  (first.evalGlobalWordTrace shape left right state).trace.length]? =
              some event := by
          simpa [List.getElem?_append, hfirst] using hget
        rcases ih
            (first.evalGlobalWordTrace shape left right state).value
            (globalPos -
              (first.evalGlobalWordTrace shape left right state).trace.length)
            htail with ⟨instrPos, instr, preState, localPos, before, after,
              hprogram, hinstrPos, hstate, hpos, hlocal⟩
        refine ⟨instrPos + 1, instr, preState, localPos,
          first :: before, after, ?_, ?_, ?_, ?_, hlocal⟩
        · simp [hprogram]
        · simp [hinstrPos]
        · simpa [evalGlobalWordTrace] using hstate
        · simp only [evalGlobalWordTrace, WordRAM.TraceResult.bind_trace,
            List.length_append]
          omega

/--
Compatibility W18 event-value producer.  This relation reaches an instruction
at its actual folded state, but does not retain a global or local occurrence
position.  New occurrence-level consumers use `ProducesEventAt`.
-/
inductive ProducesEvent
    (shape : Cartesian.CartesianShape) (left right : Nat)
    (event : WordRAM.TraceEvent) :
    WholeQueryProgram -> WholeQueryState ->
      WholeQueryInstr -> WholeQueryState -> Prop
  | head {instr rest state}
      (hmem : event ∈
        (instr.evalGlobalWordTrace shape left right state).trace) :
      ProducesEvent shape left right event
        (instr :: rest) state instr state
  | tail {instr rest state producer preState}
      (hproducer : ProducesEvent shape left right event rest
        (instr.evalGlobalWordTrace shape left right state).value
        producer preState) :
      ProducesEvent shape left right event
        (instr :: rest) state producer preState

/-- Compatibility W18 theorem for event-value membership.  Use
`evalGlobalWordTrace_getElem?_producer` for occurrence-level provenance. -/
theorem evalGlobalWordTrace_event_producer
    (shape : Cartesian.CartesianShape) (left right : Nat)
    (program : WholeQueryProgram) (state : WholeQueryState)
    (event : WordRAM.TraceEvent)
    (hmem : event ∈
      (evalGlobalWordTrace shape left right program state).trace) :
    ∃ instr preState,
      ProducesEvent shape left right event program state instr preState := by
  induction program generalizing state with
  | nil =>
      simp [evalGlobalWordTrace] at hmem
  | cons instr rest ih =>
      simp only [evalGlobalWordTrace, WordRAM.TraceResult.bind_trace,
        List.mem_append] at hmem
      rcases hmem with hhead | htail
      · exact ⟨instr, state, ProducesEvent.head hhead⟩
      · rcases ih _ htail with ⟨producer, preState, hproducer⟩
        exact ⟨producer, preState, ProducesEvent.tail hproducer⟩

/-- The producer relation retains membership of the same event in the local
instruction trace. -/
theorem ProducesEvent.event_mem_instruction_trace
    {shape : Cartesian.CartesianShape} {left right : Nat}
    {event : WordRAM.TraceEvent} {program : WholeQueryProgram}
    {state : WholeQueryState} {instr : WholeQueryInstr}
    {preState : WholeQueryState}
    (hproducer : ProducesEvent
      shape left right event program state instr preState) :
    event ∈ (instr.evalGlobalWordTrace
      shape left right preState).trace := by
  induction hproducer with
  | head hmem => exact hmem
  | tail _ ih => exact ih

/-- A producer occurrence also exposes a prefix whose actual fold value is the
instruction's pre-execution state. -/
theorem ProducesEvent.prefix_state
    {shape : Cartesian.CartesianShape} {left right : Nat}
    {event : WordRAM.TraceEvent} {program : WholeQueryProgram}
    {state : WholeQueryState} {instr : WholeQueryInstr}
    {preState : WholeQueryState}
    (hproducer : ProducesEvent
      shape left right event program state instr preState) :
    ∃ before after,
      program = before ++ instr :: after ∧
      preState = (evalGlobalWordTrace
        shape left right before state).value := by
  induction hproducer with
  | @head instr rest state hmem =>
      exact ⟨[], rest, rfl, rfl⟩
  | @tail first rest state producer preState htail ih =>
      rcases ih with ⟨before, after, hrest, hstate⟩
      refine ⟨first :: before, after, ?_, ?_⟩
      · simp [hrest]
      · simpa [evalGlobalWordTrace] using hstate

theorem evalGlobalWordTrace_refines_eval
    (shape : Cartesian.CartesianShape)
    (left right : Nat)
    (program : WholeQueryProgram) (state : WholeQueryState) :
    (evalGlobalWordTrace shape left right program state).toCosted =
      evalCanonical shape left right program state := by
  induction program generalizing state with
  | nil =>
      simp [evalGlobalWordTrace, evalCanonical,
        WordRAM.TraceResult.pure_toCosted, Costed.pure]
  | cons instr rest ih =>
      simp [evalGlobalWordTrace, evalCanonical,
        WordRAM.TraceResult.bind_toCosted,
        WholeQueryInstr.evalGlobalWordTrace_refines_eval, ih,
        Costed.bind]

theorem evalGlobalWordTrace_matchesReadStore
    (shape : Cartesian.CartesianShape)
    (left right : Nat)
    (program : WholeQueryProgram) (state : WholeQueryState) :
    forall event,
      List.Mem event
          (evalGlobalWordTrace
            shape left right program state).trace ->
        event.matchesReadStore
          (concreteBPNativeSuccinctRMQGlobalReadStore shape) := by
  induction program generalizing state with
  | nil =>
      simp [evalGlobalWordTrace]
      exact WordRAM.TraceResult.pure_trace_forall _ state
  | cons instr rest ih =>
      unfold evalGlobalWordTrace
      apply WordRAM.TraceResult.bind_trace_forall
      · exact
          WholeQueryInstr.evalGlobalWordTrace_matchesReadStore
            shape left right instr state
      · exact ih
          (instr.evalGlobalWordTrace shape left right state).value

theorem evalGlobalWordTrace_no_syntheticCostOnlyPrimitive
    (shape : Cartesian.CartesianShape)
    (left right : Nat)
    (program : WholeQueryProgram) (state : WholeQueryState) :
    forall event,
      List.Mem event
          (evalGlobalWordTrace
            shape left right program state).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  induction program generalizing state with
  | nil =>
      simp [evalGlobalWordTrace]
      exact WordRAM.TraceResult.pure_trace_forall _ state
  | cons instr rest ih =>
      unfold evalGlobalWordTrace
      apply WordRAM.TraceResult.bind_trace_forall
      · exact
          WholeQueryInstr.evalGlobalWordTrace_no_syntheticCostOnlyPrimitive
            shape left right instr state
      · exact ih
          (instr.evalGlobalWordTrace shape left right state).value

theorem evalGlobalWordTrace_noFiniteSmallInteriorSuccessfulRead_of_ready
    (shape : Cartesian.CartesianShape)
    (hready : SuccinctClose.concreteBPRelativeRmmInteriorReady shape)
    (left right : Nat)
    (program : WholeQueryProgram) (state : WholeQueryState) :
    forall event,
      List.Mem event
          (evalGlobalWordTrace
            shape left right program state).trace ->
        concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead
          event := by
  induction program generalizing state with
  | nil =>
      simp [evalGlobalWordTrace]
      exact WordRAM.TraceResult.pure_trace_forall _ state
  | cons instr rest ih =>
      unfold evalGlobalWordTrace
      apply WordRAM.TraceResult.bind_trace_forall
      · exact
          WholeQueryInstr.evalGlobalWordTrace_noFiniteSmallInteriorSuccessfulRead_of_ready
            shape hready left right instr state
      · exact ih
          (instr.evalGlobalWordTrace shape left right state).value

theorem evalGlobalWordTrace_noFiniteSmallInteriorSuccessfulRead
    (shape : Cartesian.CartesianShape)
    (left right : Nat)
    (program : WholeQueryProgram) (state : WholeQueryState) :
    forall event,
      List.Mem event
          (evalGlobalWordTrace
            shape left right program state).trace ->
        concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead
          event := by
  induction program generalizing state with
  | nil =>
      simp [evalGlobalWordTrace]
      exact WordRAM.TraceResult.pure_trace_forall _ state
  | cons instr rest ih =>
      unfold evalGlobalWordTrace
      apply WordRAM.TraceResult.bind_trace_forall
      · exact
          WholeQueryInstr.evalGlobalWordTrace_noFiniteSmallInteriorSuccessfulRead
            shape left right instr state
      · exact ih
          (instr.evalGlobalWordTrace shape left right state).value

theorem evalGlobalWordTrace_noReadyCloseSuccessfulRead_of_not_ready
    (shape : Cartesian.CartesianShape)
    (hnotReady : ¬ SuccinctClose.concreteBPRelativeRmmInteriorReady shape)
    (left right : Nat)
    (program : WholeQueryProgram) (state : WholeQueryState) :
    forall event,
      List.Mem event
          (evalGlobalWordTrace
            shape left right program state).trace ->
        concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead
          event := by
  induction program generalizing state with
  | nil =>
      simp [evalGlobalWordTrace]
      exact WordRAM.TraceResult.pure_trace_forall _ state
  | cons instr rest ih =>
      unfold evalGlobalWordTrace
      apply WordRAM.TraceResult.bind_trace_forall
      · exact
          WholeQueryInstr.evalGlobalWordTrace_noReadyCloseSuccessfulRead_of_not_ready
            shape hnotReady left right instr state
      · exact ih
          (instr.evalGlobalWordTrace shape left right state).value

/--
Execute a whole-query program in the large-regime replay.

This preserves one `WordRAM.TraceEvent` stream while using the size-indexed
compact close/LCA replay for the LCA instruction.
-/
def evalWordTraceOfSizeGe (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size) (left right : Nat) :
    WholeQueryProgram -> WholeQueryState -> WordRAM.TraceResult WholeQueryState
  | [], state => WordRAM.TraceResult.pure state
  | instr :: rest, state =>
      WordRAM.TraceResult.bind
        (instr.evalWordTraceOfSizeGe shape hsize left right state)
        fun state' =>
          evalWordTraceOfSizeGe shape hsize left right rest state'

theorem evalWordTraceOfSizeGe_refines_eval
    (shape : Cartesian.CartesianShape) (hsize : 2 ^ 128 <= shape.size)
    (left right : Nat)
    (program : WholeQueryProgram) (state : WholeQueryState) :
    (evalWordTraceOfSizeGe shape hsize left right program state).toCosted =
      eval shape left right program state := by
  induction program generalizing state with
  | nil =>
      simp [evalWordTraceOfSizeGe, eval, WordRAM.TraceResult.pure_toCosted,
        Costed.pure]
  | cons instr rest ih =>
      simp [evalWordTraceOfSizeGe, eval, WordRAM.TraceResult.bind_toCosted,
        WholeQueryInstr.evalWordTraceOfSizeGe_refines_eval, ih, Costed.bind]

/--
Execute a whole-query program in the large-regime global-segment replay.

The trace is still a `WordRAM.TraceEvent` stream, but payload reads from the
select, rank, and compact close/LCA leaves are now assembled under one shared
segment convention instead of each leaf using local segment numbers.
-/
def evalGlobalWordTraceOfSizeGe (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size) (left right : Nat) :
    WholeQueryProgram -> WholeQueryState -> WordRAM.TraceResult WholeQueryState
  | [], state => WordRAM.TraceResult.pure state
  | instr :: rest, state =>
      WordRAM.TraceResult.bind
        (instr.evalGlobalWordTraceOfSizeGe shape hsize left right state)
        fun state' =>
          evalGlobalWordTraceOfSizeGe shape hsize left right rest state'

theorem evalGlobalWordTraceOfSizeGe_refines_eval
    (shape : Cartesian.CartesianShape) (hsize : 2 ^ 128 <= shape.size)
    (left right : Nat)
    (program : WholeQueryProgram) (state : WholeQueryState) :
    (evalGlobalWordTraceOfSizeGe shape hsize left right program state).toCosted =
      evalCanonical shape left right program state := by
  induction program generalizing state with
  | nil =>
      simp [evalGlobalWordTraceOfSizeGe, evalCanonical,
        WordRAM.TraceResult.pure_toCosted, Costed.pure]
  | cons instr rest ih =>
      simp [evalGlobalWordTraceOfSizeGe, evalCanonical,
        WordRAM.TraceResult.bind_toCosted,
        WholeQueryInstr.evalGlobalWordTraceOfSizeGe_refines_eval, ih,
        Costed.bind]

theorem evalGlobalWordTraceOfSizeGe_matchesReadStore
    (shape : Cartesian.CartesianShape) (hsize : 2 ^ 128 <= shape.size)
    (left right : Nat)
    (program : WholeQueryProgram) (state : WholeQueryState) :
    forall event,
      List.Mem event
          (evalGlobalWordTraceOfSizeGe
            shape hsize left right program state).trace ->
        event.matchesReadStore
          (concreteBPNativeSuccinctRMQGlobalReadStore shape) := by
  induction program generalizing state with
  | nil =>
      simp [evalGlobalWordTraceOfSizeGe]
      exact WordRAM.TraceResult.pure_trace_forall _ state
  | cons instr rest ih =>
      unfold evalGlobalWordTraceOfSizeGe
      apply WordRAM.TraceResult.bind_trace_forall
      · exact
          WholeQueryInstr.evalGlobalWordTraceOfSizeGe_matchesReadStore
            shape hsize left right instr state
      · exact ih
          (instr.evalGlobalWordTraceOfSizeGe
            shape hsize left right state).value

end WholeQueryProgram

/-- The closed whole-query control program for the final BP-native RMQ query. -/
def concreteBPNativeSuccinctRMQWholeQueryProgram : WholeQueryProgram :=
  [ WholeQueryInstr.selectClose .leftClose .inputLeft
  , WholeQueryInstr.selectClose .rightClose
      (.sub .inputRight (.const 1))
  , WholeQueryInstr.lcaClose .answerClose .leftClose .rightClose
  , WholeQueryInstr.rankCloseIfSome .closeRank .answerClose
      (.add (.optNatD .answerClose 0) (.const 1))
  , WholeQueryInstr.outputPredIfSome .output .answerClose .closeRank
  ]

/-- Every operational reviewer leaf is present in the concrete closed query
program, as classified from the instruction constructors themselves. -/
theorem concreteBPNativeSuccinctRMQWholeQueryProgram_contains_reviewerReadLeaf
    (leaf : ReviewerReadLeaf) :
    ∃ instr,
      instr ∈ concreteBPNativeSuccinctRMQWholeQueryProgram ∧
      instr.reviewerReadLeaf? = some leaf := by
  cases leaf <;>
    simp [concreteBPNativeSuccinctRMQWholeQueryProgram,
      WholeQueryInstr.reviewerReadLeaf?]

/--
Compatibility category connection.  It chooses a matching instruction but
does not tie source and consumer through one produced event; use
`ReviewerSharedBPConsumer.ProducerConnected` for reviewer evidence.
-/
theorem concreteBPNativeSuccinctRMQReviewerSharedBPConsumer_evaluator_connection
    (shape : Cartesian.CartesianShape) (left right : Nat)
    (state : WholeQueryState) (consumer : ReviewerSharedBPConsumer) :
    consumer.Checked ∧
      ∃ instr,
        instr ∈ concreteBPNativeSuccinctRMQWholeQueryProgram ∧
        instr.reviewerReadLeaf? = some consumer.leaf ∧
        WholeQueryInstr.reviewerReadLeafEvaluatorBranch
          shape left right state consumer.leaf instr := by
  refine ⟨concreteBPNativeSuccinctRMQReviewerSharedBPConsumer_all_checked
      consumer, ?_⟩
  rcases
      concreteBPNativeSuccinctRMQWholeQueryProgram_contains_reviewerReadLeaf
        consumer.leaf with ⟨instr, hmem, hleaf⟩
  exact ⟨instr, hmem, hleaf,
    WholeQueryInstr.reviewerReadLeaf?_some_evaluatorBranch
      shape left right state consumer.leaf instr hleaf⟩

/--
Compatibility category connection.  It does not exhibit a possible read event
from the source; use `ReviewerSource.HasProducerMayPath`.
-/
theorem concreteBPNativeSuccinctRMQReviewerSource_counted_evaluator_connection
    (shape : Cartesian.CartesianShape) (left right : Nat)
    (state : WholeQueryState) (source : ReviewerSource)
    (hcounted : source.Counted) :
    (source = .sharedBPCode ∧
      ∃ consumer : ReviewerSharedBPConsumer,
      ∃ instr,
        consumer.Checked ∧
        instr ∈ concreteBPNativeSuccinctRMQWholeQueryProgram ∧
        instr.reviewerReadLeaf? = some consumer.leaf ∧
        WholeQueryInstr.reviewerReadLeafEvaluatorBranch
          shape left right state consumer.leaf instr) ∨
    (∃ leaf : ReviewerReadLeaf,
      ∃ instr,
        source.OperationallyOwnedBy leaf ∧
        instr ∈ concreteBPNativeSuccinctRMQWholeQueryProgram ∧
        instr.reviewerReadLeaf? = some leaf ∧
        WholeQueryInstr.reviewerReadLeafEvaluatorBranch
          shape left right state leaf instr) := by
  rcases
      concreteBPNativeSuccinctRMQReviewerSource_counted_operational_connection
        source hcounted with hshared | ⟨leaf, howned⟩
  · rcases hshared with ⟨hsource, consumer, hchecked⟩
    rcases
        concreteBPNativeSuccinctRMQWholeQueryProgram_contains_reviewerReadLeaf
          consumer.leaf with ⟨instr, hmem, hleaf⟩
    refine Or.inl ⟨hsource, consumer, instr, hchecked, hmem, hleaf, ?_⟩
    exact WholeQueryInstr.reviewerReadLeaf?_some_evaluatorBranch
      shape left right state consumer.leaf instr hleaf
  · rcases
        concreteBPNativeSuccinctRMQWholeQueryProgram_contains_reviewerReadLeaf
          leaf with ⟨instr, hmem, hleaf⟩
    refine Or.inr ⟨leaf, instr, howned, hmem, hleaf, ?_⟩
    exact WholeQueryInstr.reviewerReadLeaf?_some_evaluatorBranch
      shape left right state leaf instr hleaf

/--
Final BP-native RMQ query as one closed whole-query control program.

The component leaves remain the existing interpreted select-close, compact
close/LCA, and two-level register-backed rank leaves; the surrounding query
control is now a first-order instruction list rather than open Lean-side
continuations.
-/
def concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted
    (shape : Cartesian.CartesianShape)
    (left right : Nat) : Costed (Option Nat) :=
  Costed.map WholeQueryState.output?
    (WholeQueryProgram.eval shape left right
      concreteBPNativeSuccinctRMQWholeQueryProgram
      WholeQueryState.empty)

/-- Canonical modeled whole-query execution consumed by the global trace. -/
def concreteBPNativeSuccinctRMQWholeQueryCanonicalInterpretedCosted
    (shape : Cartesian.CartesianShape)
    (left right : Nat) : Costed (Option Nat) :=
  Costed.map WholeQueryState.output?
    (WholeQueryProgram.evalCanonical shape left right
      concreteBPNativeSuccinctRMQWholeQueryProgram
      WholeQueryState.empty)
/--
Direct bind presentation of the canonical whole query. This is the proof
bridge for cost and exactness: its close/LCA leaf is the uniform canonical
consumer, while select-close and answer-rank retain the accepted interpreted
leaves.
-/
def concreteBPNativeSuccinctRMQCanonicalQueryInterpretedCosted
    (shape : Cartesian.CartesianShape)
    (left right : Nat) : Costed (Option Nat) :=
  Costed.bind
    (concreteBPNativeSelectCloseInterpretedCosted shape left)
    fun leftClose? =>
      Costed.bind
        (concreteBPNativeSelectCloseInterpretedCosted shape (right - 1))
        fun rightClose? =>
          match leftClose?, rightClose? with
          | some leftClose, some rightClose =>
              Costed.bind
                (concreteBPNativeLCACloseCanonicalInterpretedCosted
                  shape leftClose rightClose)
                fun answerClose? =>
                  match answerClose? with
                  | some answerClose =>
                      Costed.map (fun closeRank => some (closeRank - 1))
                        (concreteBPNativeRankCloseInterpretedCosted
                          shape (answerClose + 1))
                  | none => Costed.pure none
          | _, _ => Costed.pure none

/--
Final BP-native RMQ query with a preserved controller-level leaf trace.

Projecting this result to `Costed` refines the existing closed whole-query
interpreter.  The trace is deliberately a domain-leaf trace, not yet one shared
payload-store `WordRAM.TraceEvent` list.
-/
def concreteBPNativeSuccinctRMQWholeQueryLeafTraceCosted
    (shape : Cartesian.CartesianShape)
    (left right : Nat) : Costed (Option Nat) :=
  Costed.map WholeQueryState.output?
    ((WholeQueryProgram.evalLeafTrace shape left right
      concreteBPNativeSuccinctRMQWholeQueryProgram
      WholeQueryState.empty).toCosted)

/--
Final BP-native RMQ query with one unified `WordRAM.TraceEvent` stream.

This is a real `TraceEvent` stream for the closed query controller. Its
select-close, answer-rank, and compact-close rank-seed reads are structural
payload/register traces. The bounded local BP decoders, endpoint-fringe
decoders, and relative-rmM interior query remain explicit charged decoder
leaves, which are the remaining payload-read replay target.
-/
def concreteBPNativeSuccinctRMQWholeQueryWordTraceCosted
    (shape : Cartesian.CartesianShape)
    (left right : Nat) : Costed (Option Nat) :=
  Costed.map WholeQueryState.output?
    ((WholeQueryProgram.evalWordTrace shape left right
      concreteBPNativeSuccinctRMQWholeQueryProgram
      WholeQueryState.empty).toCosted)

/--
All-size final BP-native RMQ query as one globally segmented
`WordRAM.TraceEvent` result.

Unlike `concreteBPNativeSuccinctRMQWholeQueryWordTraceCosted`, the component
payload reads already use the final shared segment layout. The close-navigation
leg uses the all-size structural replay, including on small shapes, rather than
emitting synthetic fallback events.
-/
def concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
    (shape : Cartesian.CartesianShape)
    (left right : Nat) : WordRAM.TraceResult (Option Nat) :=
  WordRAM.TraceResult.map WholeQueryState.output?
    (WholeQueryProgram.evalGlobalWordTrace shape left right
      concreteBPNativeSuccinctRMQWholeQueryProgram
      WholeQueryState.empty)

/-- `Costed` projection of the all-size globally segmented trace. -/
def concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
    (shape : Cartesian.CartesianShape)
    (left right : Nat) : Costed (Option Nat) :=
  (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
    shape left right).toCosted

/--
Large-regime final BP-native RMQ query with one unified `WordRAM.TraceEvent`
stream.

Compared with `concreteBPNativeSuccinctRMQWholeQueryWordTraceCosted`, the
compact close/LCA instruction now uses the large-regime structural replay, so
the positive-block local/fringe/interior path is represented by trace events
instead of the all-size structural branch split.
-/
def concreteBPNativeSuccinctRMQWholeQueryWordTraceCostedOfSizeGe
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (left right : Nat) : Costed (Option Nat) :=
  Costed.map WholeQueryState.output?
    ((WholeQueryProgram.evalWordTraceOfSizeGe shape hsize left right
      concreteBPNativeSuccinctRMQWholeQueryProgram
      WholeQueryState.empty).toCosted)

/--
Large-regime final BP-native RMQ query as a trace result, before projection to
`Costed`.

The trace is one list of `WordRAM.TraceEvent`s. Its component traces still use
local segment numbering, so this is not yet a proof that all reads target one
globally laid-out payload store.
-/
def concreteBPNativeSuccinctRMQWholeQueryWordTraceResultOfSizeGe
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (left right : Nat) : WordRAM.TraceResult (Option Nat) :=
  WordRAM.TraceResult.map WholeQueryState.output?
    (WholeQueryProgram.evalWordTraceOfSizeGe shape hsize left right
      concreteBPNativeSuccinctRMQWholeQueryProgram
      WholeQueryState.empty)

/--
Large-regime final BP-native RMQ query as one globally segmented
`WordRAM.TraceEvent` result.

Unlike `concreteBPNativeSuccinctRMQWholeQueryWordTraceResultOfSizeGe`, this
uses the relabeled select/rank/close leaves, so payload-read segment numbers
are globally meaningful across the whole query: BP code at segment `0`, select
auxiliary tables at `1..16`, rank tables at `17..19`, and close-interior tables
at `20..25`.
-/
def concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultOfSizeGe
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (left right : Nat) : WordRAM.TraceResult (Option Nat) :=
  WordRAM.TraceResult.map WholeQueryState.output?
    (WholeQueryProgram.evalGlobalWordTraceOfSizeGe shape hsize left right
      concreteBPNativeSuccinctRMQWholeQueryProgram
      WholeQueryState.empty)

/-- `Costed` projection of the globally segmented large-regime trace. -/
def concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedOfSizeGe
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (left right : Nat) : Costed (Option Nat) :=
  (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultOfSizeGe
    shape hsize left right).toCosted

/--
Component-local provenance for large-regime final RMQ trace events.

This predicate is intentionally weaker than a global-store theorem: it records
that each event in the assembled stream comes from one of the concrete
close-select, compact close/LCA, or answer-rank component traces. A future
global-store theorem should add segment relabeling and prove the same reads
agree with one combined payload layout.
-/
def concreteBPNativeLargeRegimeTraceEventAdmissible
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (left right : Nat)
    (event : WordRAM.TraceEvent) : Prop :=
  List.Mem event
      (concreteBPNativeSelectCloseRegisterWordTraceResult shape left).trace \/
    List.Mem event
      (concreteBPNativeSelectCloseRegisterWordTraceResult
        shape (right - 1)).trace \/
    (exists leftClose rightClose,
      List.Mem event
        (concreteBPNativeLCACloseWordTraceResultOfSizeGe
          shape hsize leftClose rightClose).trace) \/
    (exists answerClose,
      List.Mem event
        (concreteBPNativeRankCloseRegisterWordTraceResult
          shape (answerClose + 1)).trace) \/
    Not event.isReadWord

/--
Small numeric envelope for the natural data carried by one `WordRAM` trace
event.  It is intentionally syntactic: payload reads contribute their segment
and index; word-local primitives contribute the natural operands and result
positions they expose in the trace.
-/
def concreteBPNativeTraceEventNatEnvelope :
    WordRAM.TraceEvent -> Nat
  | WordRAM.TraceEvent.readWord segment index _ => Nat.max segment index
  | WordRAM.TraceEvent.wordRank _ limit result => Nat.max limit result
  | WordRAM.TraceEvent.wordSelect _ occurrence none => occurrence
  | WordRAM.TraceEvent.wordSelect _ occurrence (some result) =>
      Nat.max occurrence result
  | WordRAM.TraceEvent.syntheticCostOnlyPrimitive => 0

/-- Maximum natural envelope over a trace. -/
def concreteBPNativeTraceNatEnvelope :
    List WordRAM.TraceEvent -> Nat
  | [] => 0
  | event :: rest =>
      Nat.max (concreteBPNativeTraceEventNatEnvelope event)
        (concreteBPNativeTraceNatEnvelope rest)

/--
Declared bit width large enough for every natural datum exposed by this trace.
This is a trace-local bound, not an asymptotic machine-word theorem.
-/
def concreteBPNativeTraceEventBitWidth
    (trace : List WordRAM.TraceEvent) : Nat :=
  Nat.log2 (concreteBPNativeTraceNatEnvelope trace) + 1

/-- Read addresses exposed by an event fit in the declared bit width. -/
def concreteBPNativeTraceEventReadAddressFitsInBits
    (bits : Nat) : WordRAM.TraceEvent -> Prop
  | WordRAM.TraceEvent.readWord segment index _ =>
      WordRAM.Register.AddressFitsInBits bits segment index
  | WordRAM.TraceEvent.wordRank _ _ _ => True
  | WordRAM.TraceEvent.wordSelect _ _ _ => True
  | WordRAM.TraceEvent.syntheticCostOnlyPrimitive => True

/-- Word-primitive natural operands/results exposed by an event fit in bits. -/
def concreteBPNativeTraceEventPrimitiveOperandsFitInBits
    (bits : Nat) : WordRAM.TraceEvent -> Prop
  | WordRAM.TraceEvent.readWord _ _ _ => True
  | WordRAM.TraceEvent.wordRank _ limit result =>
      WordRAM.Register.FitsInBits bits limit /\
        WordRAM.Register.FitsInBits bits result
  | WordRAM.TraceEvent.wordSelect _ occurrence result =>
      WordRAM.Register.FitsInBits bits occurrence /\
        forall value, result = some value ->
          WordRAM.Register.FitsInBits bits value
  | WordRAM.TraceEvent.syntheticCostOnlyPrimitive => True

private theorem wordRankTraceResult_primitiveOperandsFitInBits
    (width : Nat) (target : Bool) (word : List Bool) (limit : Nat)
    (hlimit : WordRAM.Register.FitsInBits width limit) :
    forall event,
      event ∈
          (SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult
            target word limit).trace ->
        concreteBPNativeTraceEventPrimitiveOperandsFitInBits width event := by
  intro event hmem
  simp [SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult,
    WordRAM.Program.eval] at hmem
  subst event
  constructor
  · exact hlimit
  · unfold WordRAM.Register.FitsInBits
    rw [Succinct.ram_boolRankPrefix_eq_rankPrefix]
    exact Nat.lt_of_le_of_lt
      (Succinct.rankPrefix_le_limit target word limit) hlimit

private theorem wordSelectTraceResult_primitiveOperandsFitInBits
    (width : Nat) (target : Bool) (word : List Bool) (occurrence : Nat)
    (hoccurrence : WordRAM.Register.FitsInBits width occurrence)
    (hword : word.length < 2 ^ width) :
    forall event,
      event ∈ (GenericSelect.wordSelectTraceResult target word occurrence).trace ->
        concreteBPNativeTraceEventPrimitiveOperandsFitInBits width event := by
  intro event hmem
  simp [GenericSelect.wordSelectTraceResult, WordRAM.Program.eval] at hmem
  subst event
  constructor
  · exact hoccurrence
  · intro value hvalue
    unfold WordRAM.Register.FitsInBits
    rw [Succinct.ram_boolSelectInWord_eq_select] at hvalue
    exact Nat.lt_trans (Succinct.select_bounds hvalue) hword

private theorem denseTwoWordSelectTraceResult_primitiveOperandsFitInBits
    (width : Nat) (target : Bool) {bits : List Bool} {wordSize : Nat}
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (basePosition baseOccurrence q : Nat)
    (hwordSizePos : 0 < wordSize)
    (hwordSize : wordSize < 2 ^ width)
    (hq : q < 2 ^ width)
    (hbudget : wordSize + q < 2 ^ width) :
    forall event,
      event ∈
          (GenericSelect.denseTwoWordSelectTraceResult
            target bitWords basePosition baseOccurrence q).trace ->
        concreteBPNativeTraceEventPrimitiveOperandsFitInBits width event := by
  unfold GenericSelect.denseTwoWordSelectTraceResult
  apply WordRAM.TraceResult.bind_trace_forall
  · intro event hmem
    simp [SuccinctSpace.PayloadWordStore.readProgram, WordRAM.Program.eval] at hmem
    subst event
    trivial
  · cases hfirst :
      (WordRAM.TraceResult.ofResult
        ((bitWords.store.readProgram (basePosition / wordSize)).eval
          bitWords.store.wordRAMStore)).value with
    | none =>
        exact WordRAM.TraceResult.pure_trace_forall _ none
    | some firstWord =>
        have hfirstRead :
            bitWords.wordRAMStore.readWord? 0 (basePosition / wordSize) =
              some firstWord := by
          simpa [SuccinctSpace.BoundedPayloadWordStore.wordRAMStore,
            SuccinctSpace.PayloadWordStore.readProgram,
            WordRAM.Program.eval] using hfirst
        have hfirstLength : firstWord.length <= wordSize :=
          (SuccinctSpace.BoundedPayloadWordStore.wordRAMStore_wordsBounded
            bitWords) hfirstRead
        have hoffset :
            basePosition - basePosition / wordSize * wordSize < wordSize := by
          simpa [Nat.mod_eq_sub_div_mul] using
            Nat.mod_lt basePosition hwordSizePos
        apply WordRAM.TraceResult.bind_trace_forall
        · exact wordRankTraceResult_primitiveOperandsFitInBits
            width target firstWord
            (basePosition - basePosition / wordSize * wordSize)
            (Nat.lt_trans hoffset hwordSize)
        · apply WordRAM.TraceResult.bind_trace_forall
          · exact wordRankTraceResult_primitiveOperandsFitInBits
              width target firstWord firstWord.length
              (Nat.lt_of_le_of_lt hfirstLength hwordSize)
          · by_cases hlt :
                q - baseOccurrence <
                  (SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult
                    target firstWord firstWord.length).value -
                    (SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult
                      target firstWord
                      (basePosition - basePosition / wordSize * wordSize)).value
            · intro event hmem
              simp [hlt] at hmem
              have hbefore :
                  (SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult
                    target firstWord
                    (basePosition - basePosition / wordSize * wordSize)).value <=
                      firstWord.length := by
                simp [SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult,
                  WordRAM.Program.eval,
                  Succinct.ram_boolRankPrefix_eq_rankPrefix]
                exact Succinct.rankPrefix_le_length target firstWord _
              have hoccurrence :
                  WordRAM.Register.FitsInBits width
                    ((SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult
                      target firstWord
                      (basePosition - basePosition / wordSize * wordSize)).value +
                        (q - baseOccurrence)) := by
                unfold WordRAM.Register.FitsInBits
                omega
              exact
                (WordRAM.TraceResult.map_trace_forall
                  (concreteBPNativeTraceEventPrimitiveOperandsFitInBits width)
                  (fun local? =>
                    local?.map fun offset =>
                      basePosition / wordSize * wordSize + offset)
                  (GenericSelect.wordSelectTraceResult target firstWord
                    ((SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult
                      target firstWord
                      (basePosition - basePosition / wordSize * wordSize)).value +
                        (q - baseOccurrence)))
                      (wordSelectTraceResult_primitiveOperandsFitInBits
                    width target firstWord
                    ((SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult
                      target firstWord
                      (basePosition - basePosition / wordSize * wordSize)).value +
                        (q - baseOccurrence))
                    hoccurrence
                    (Nat.lt_of_le_of_lt hfirstLength hwordSize))) event hmem
            · intro event hmem
              simp [hlt] at hmem
              rcases hmem with hmem | hmem
              · subst event
                trivial
              · cases hsecond :
                    bitWords.store.words[basePosition / wordSize + 1]? with
                | none =>
                    simp [hsecond] at hmem
                | some secondWord =>
                    have hsecondRead :
                        bitWords.wordRAMStore.readWord? 0
                            (basePosition / wordSize + 1) = some secondWord := by
                      simpa [SuccinctSpace.BoundedPayloadWordStore.wordRAMStore,
                        SuccinctSpace.PayloadWordStore.wordRAMStore,
                        WordRAM.Store.readWord?] using hsecond
                    have hsecondLength : secondWord.length <= wordSize :=
                      (SuccinctSpace.BoundedPayloadWordStore.wordRAMStore_wordsBounded
                        bitWords) hsecondRead
                    simp [hsecond] at hmem
                    have hoccurrence :
                        WordRAM.Register.FitsInBits width
                          (q - baseOccurrence -
                            ((SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult
                              target firstWord firstWord.length).value -
                              (SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult
                                target firstWord
                                (basePosition - basePosition / wordSize * wordSize)).value)) := by
                      unfold WordRAM.Register.FitsInBits
                      omega
                    exact
                      (WordRAM.TraceResult.map_trace_forall
                        (concreteBPNativeTraceEventPrimitiveOperandsFitInBits width)
                        (fun local? =>
                          local?.map fun offset =>
                            (basePosition / wordSize + 1) * wordSize + offset)
                        (GenericSelect.wordSelectTraceResult target secondWord
                          (q - baseOccurrence -
                            ((SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult
                              target firstWord firstWord.length).value -
                              (SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult
                                target firstWord
                                (basePosition - basePosition / wordSize * wordSize)).value)))
                        (wordSelectTraceResult_primitiveOperandsFitInBits
                          width target secondWord
                          (q - baseOccurrence -
                            ((SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult
                              target firstWord firstWord.length).value -
                              (SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult
                                target firstWord
                                (basePosition - basePosition / wordSize * wordSize)).value))
                          hoccurrence
                          (Nat.lt_of_le_of_lt hsecondLength hwordSize))) event hmem

private theorem rankTraceResult_primitiveOperandsFitInBits
    (width : Nat) {bits : List Bool}
    {superOverhead blockOverhead queryCost : Nat}
    (data :
      SuccinctRank.TwoLevelPayloadLiveStoredWordRankData
        bits superOverhead blockOverhead queryCost)
    (target : Bool) (pos : Nat)
    (hbits : bits.length < 2 ^ width) :
    forall event,
      event ∈ (data.rankTraceResult target pos).trace ->
        concreteBPNativeTraceEventPrimitiveOperandsFitInBits width event := by
  intro event hmem
  let regs := WordRAM.Register.RegFile.withNat1 pos
  let offset :=
    (data.wordOffsetExpr (WordRAM.Register.NatExpr.reg 0)).eval regs
  have hoffsetLe : offset <= bits.length := by
    dsimp only [offset, regs]
    unfold SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordOffsetExpr
      SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordIndexExpr
      SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.queryPosExpr
    simpa [WordRAM.Register.NatExpr.eval] using
      Nat.le_trans
        (Nat.sub_le (Nat.min pos bits.length)
          (Nat.min pos bits.length / data.wordSize * data.wordSize))
        (Nat.min_le_right pos bits.length)
  have hoffset : WordRAM.Register.FitsInBits width offset :=
    Nat.lt_of_le_of_lt hoffsetLe hbits
  have hlocalRank (word : List Bool) :
      WordRAM.Register.FitsInBits width
        (RAM.boolRankPrefix target word offset) := by
    unfold WordRAM.Register.FitsInBits
    rw [Succinct.ram_boolRankPrefix_eq_rankPrefix]
    exact Nat.lt_of_le_of_lt
      (Succinct.rankPrefix_le_limit target word offset) hoffset
  unfold SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.rankTraceResult
    SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.rankRegisterProgram at hmem
  simp only [WordRAM.TraceResult.ofResult_trace,
    WordRAM.Register.NatProgram.eval] at hmem
  cases event with
  | readWord segment index word? => trivial
  | wordRank eventTarget limit result =>
      split at hmem <;>
        simp_all [offset,
          concreteBPNativeTraceEventPrimitiveOperandsFitInBits]
      rcases hmem with ⟨rfl, rfl, rfl⟩
      exact ⟨hoffset, hlocalRank _⟩
  | wordSelect eventTarget occurrence result =>
      split at hmem <;> simp_all
  | syntheticCostOnlyPrimitive => trivial

private theorem relabelReadSegmentsWith_primitiveOperandsFitInBits
    (width : Nat) {alpha : Type}
    (segmentMap : Nat -> Nat) (result : WordRAM.TraceResult alpha)
    (hresult : forall event, event ∈ result.trace ->
      concreteBPNativeTraceEventPrimitiveOperandsFitInBits width event) :
    forall event,
      event ∈
          (WordRAM.TraceResult.relabelReadSegmentsWith segmentMap result).trace ->
        concreteBPNativeTraceEventPrimitiveOperandsFitInBits width event := by
  intro event hmem
  simp only [WordRAM.TraceResult.relabelReadSegmentsWith, List.mem_map] at hmem
  rcases hmem with ⟨source, hsource, rfl⟩
  have hfit := hresult _ hsource
  cases source <;>
    simp [WordRAM.TraceEvent.relabelReadSegmentWith,
      concreteBPNativeTraceEventPrimitiveOperandsFitInBits] at hfit ⊢ <;>
    exact hfit

private theorem fixedWidthNatTableReadRelabeled_primitiveOperandsFitInBits
    (width : Nat) {entries : List Nat} {fieldWidth : Nat}
    (table : SuccinctSpace.FixedWidthNatTable entries fieldWidth)
    (segmentMap : Nat -> Nat) (i : Nat) :
    forall event,
      event ∈
          (WordRAM.TraceResult.relabelReadSegmentsWith segmentMap
            (WordRAM.TraceResult.ofResult
              ((table.readProgram i).eval table.wordRAMStore))).trace ->
        concreteBPNativeTraceEventPrimitiveOperandsFitInBits width event := by
  apply relabelReadSegmentsWith_primitiveOperandsFitInBits
  intro event hmem
  simp [SuccinctSpace.FixedWidthNatTable.readProgram,
    SuccinctSpace.PayloadWordStore.readProgram, WordRAM.Program.eval] at hmem
  subst event
  trivial

private theorem selectEntryReadRelabeled_primitiveOperandsFitInBits
    (width : Nat)
    {entries : List GenericSelect.SparseDenseSelectDenseLocalEntry}
    {fieldWidth : Nat}
    (table : GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable
      entries fieldWidth)
    (layout : GenericSelect.SparseDenseEntryTableTraceSegmentBases)
    (i : Nat) :
    forall event,
      event ∈ (table.readTraceResultRelabeled layout i).trace ->
        concreteBPNativeTraceEventPrimitiveOperandsFitInBits width event := by
  unfold GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable.readTraceResultRelabeled
  apply WordRAM.TraceResult.bind_trace_forall
  · exact fixedWidthNatTableReadRelabeled_primitiveOperandsFitInBits _ _ _ _
  · apply WordRAM.TraceResult.bind_trace_forall
    · exact fixedWidthNatTableReadRelabeled_primitiveOperandsFitInBits _ _ _ _
    · apply WordRAM.TraceResult.bind_trace_forall
      · exact fixedWidthNatTableReadRelabeled_primitiveOperandsFitInBits _ _ _ _
      · apply WordRAM.TraceResult.map_trace_forall
        exact fixedWidthNatTableReadRelabeled_primitiveOperandsFitInBits _ _ _ _

private theorem relativeOffsetReadRelabeled_primitiveOperandsFitInBits
    (machineWidth : Nat) {entries : List Nat} {width : Nat}
    (segmentBase deadSegment : Nat)
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (base slot : Nat) :
    forall event,
      event ∈
          (GenericSelect.relativeOffsetReadTraceResultRelabeled
            segmentBase deadSegment table base slot).trace ->
        concreteBPNativeTraceEventPrimitiveOperandsFitInBits
          machineWidth event := by
  unfold GenericSelect.relativeOffsetReadTraceResultRelabeled
  apply WordRAM.TraceResult.map_trace_forall
  exact fixedWidthNatTableReadRelabeled_primitiveOperandsFitInBits _ _ _ _

private theorem sparseDirectoryReadRelabeled_primitiveOperandsFitInBits
    (width : Nat) {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory : GenericSelect.SparseExceptionDirectory
      bits target rankSuperOverhead rankBlockOverhead)
    (layout : GenericSelect.SparseExceptionDirectoryTraceSegmentBases)
    (base localSlot localOccurrence : Nat)
    (hbits : directory.flagBits.length < 2 ^ width) :
    forall event,
      event ∈
          (directory.readTraceResultRelabeled
            layout base localSlot localOccurrence).trace ->
        concreteBPNativeTraceEventPrimitiveOperandsFitInBits width event := by
  unfold GenericSelect.SparseExceptionDirectory.readTraceResultRelabeled
  apply WordRAM.TraceResult.bind_trace_forall
  · apply relabelReadSegmentsWith_primitiveOperandsFitInBits
    exact rankTraceResult_primitiveOperandsFitInBits
      width directory.rankData true localSlot hbits
  · exact relativeOffsetReadRelabeled_primitiveOperandsFitInBits _ _ _ _ _ _

private theorem denseTwoWordSelectRelabeled_primitiveOperandsFitInBits
    (width bitWordSegmentBase deadSegment : Nat)
    (target : Bool) {bits : List Bool} {wordSize : Nat}
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (basePosition baseOccurrence q : Nat)
    (hwordSizePos : 0 < wordSize)
    (hwordSize : wordSize < 2 ^ width)
    (hq : q < 2 ^ width)
    (hbudget : wordSize + q < 2 ^ width) :
    forall event,
      event ∈
          (GenericSelect.denseTwoWordSelectTraceResultRelabeled
            bitWordSegmentBase deadSegment target bitWords
            basePosition baseOccurrence q).trace ->
        concreteBPNativeTraceEventPrimitiveOperandsFitInBits width event := by
  unfold GenericSelect.denseTwoWordSelectTraceResultRelabeled
  apply relabelReadSegmentsWith_primitiveOperandsFitInBits
  exact denseTwoWordSelectTraceResult_primitiveOperandsFitInBits
    width target bitWords basePosition baseOccurrence q
    hwordSizePos hwordSize hq hbudget

private theorem concreteBPNativeSuccinctRMQ_bpCodeLength_fits_reviewerWordBits
    (shape : Cartesian.CartesianShape) :
    shape.bpCode.length <
      2 ^ concreteBPNativeSuccinctRMQReviewerWordBits shape.size := by
  have hle :
      shape.bpCode.length <=
        concreteBPNativeSuccinctRMQReviewerCapacity shape.size := by
    rw [Cartesian.CartesianShape.bpCode_length]
    unfold concreteBPNativeSuccinctRMQReviewerCapacity
    omega
  exact Nat.lt_of_le_of_lt hle
    (concreteBPNativeSuccinctRMQReviewerCapacity_lt_two_pow_wordBits _)

private theorem concreteBPNativeSuccinctRMQ_twoBpCodeLength_fits_reviewerWordBits
    (shape : Cartesian.CartesianShape) :
    2 * shape.bpCode.length <
      2 ^ concreteBPNativeSuccinctRMQReviewerWordBits shape.size := by
  have hle :
      2 * shape.bpCode.length <=
        concreteBPNativeSuccinctRMQReviewerCapacity shape.size := by
    rw [Cartesian.CartesianShape.bpCode_length]
    unfold concreteBPNativeSuccinctRMQReviewerCapacity
    omega
  exact Nat.lt_of_le_of_lt hle
    (concreteBPNativeSuccinctRMQReviewerCapacity_lt_two_pow_wordBits _)

private theorem concreteBPNativeSelectCloseGlobalWordTraceResult_primitiveOperandsFit_reviewerWordBits
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    forall event,
      event ∈
          (concreteBPNativeSelectCloseGlobalWordTraceResult shape idx).trace ->
        concreteBPNativeTraceEventPrimitiveOperandsFitInBits
          (concreteBPNativeSuccinctRMQReviewerWordBits shape.size) event := by
  intro event hmem
  have hread :=
    concreteBPNativeChunkedSelectCloseGlobalWordTraceResult_events_readWord
      shape idx event hmem
  cases event with
  | readWord segment index word? => trivial
  | wordRank target limit result => exact hread.elim
  | wordSelect target occurrence result => exact hread.elim
  | syntheticCostOnlyPrimitive => trivial


private theorem concreteBPNativeLocalBPWindowBitsTraceResult_primitiveOperandsFit_reviewerWordBits
    (shape : Cartesian.CartesianShape) (blockSize close : Nat) :
    forall event,
      event ∈
          (SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPWindowBitsTraceResult
            shape blockSize close).trace ->
        concreteBPNativeTraceEventPrimitiveOperandsFitInBits
          (concreteBPNativeSuccinctRMQReviewerWordBits shape.size) event := by
  unfold SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPWindowBitsTraceResult
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPBlockWordsTraceResult
  apply WordRAM.TraceResult.map_trace_forall
  apply WordRAM.TraceResult.bind_trace_forall
  · intro event hmem
    simp [SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpCodeWordReadTraceResult] at hmem
    subst event
    trivial
  · apply WordRAM.TraceResult.bind_trace_forall
    · intro event hmem
      simp [SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpCodeWordReadTraceResult] at hmem
      subst event
      trivial
    · apply WordRAM.TraceResult.bind_trace_forall
      · intro event hmem
        simp [SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpCodeWordReadTraceResult] at hmem
        subst event
        trivial
      · apply WordRAM.TraceResult.map_trace_forall
        intro event hmem
        simp [SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpCodeWordReadTraceResult] at hmem
        subst event
        trivial

private theorem concreteBPNativeInteriorGlobalWordTraceResultAllSizeStructural_primitiveOperandsFit_reviewerWordBits
    (shape : Cartesian.CartesianShape) (startBlock count : Nat) :
    forall event,
      event ∈
          (SuccinctClose.ConcreteCompactBPCloseLCADirectory.concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructural
            shape concreteBPNativeInteriorTraceSegments startBlock count).trace ->
        concreteBPNativeTraceEventPrimitiveOperandsFitInBits
          (concreteBPNativeSuccinctRMQReviewerWordBits shape.size) event := by
  intro event hmem
  unfold SuccinctClose.ConcreteCompactBPCloseLCADirectory.concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructural at hmem
  unfold SuccinctClose.ConcreteCompactBPCloseLCADirectory.canonicalRelativeRmmInteriorRangeMinTraceResultAtSegment at hmem
  unfold SuccinctClose.flatStoreExecutionTraceResultAtSegment at hmem
  rcases List.mem_map.mp hmem with ⟨read, hread, rfl⟩
  trivial

private theorem concreteBPNativeRankCloseWordTraceResultAtSegment_primitiveOperandsFit_reviewerWordBits
    (shape : Cartesian.CartesianShape) (rankSegmentBase pos : Nat) :
    forall event,
      event ∈
          (concreteBPNativeRankCloseWordTraceResultAtSegment
            shape rankSegmentBase pos).trace ->
        concreteBPNativeTraceEventPrimitiveOperandsFitInBits
          (concreteBPNativeSuccinctRMQReviewerWordBits shape.size) event := by
  apply
    (builtRelativeSplitBPCloseRankData
        shape).bpChunkedRankTraceResultWithStore_trace_forall
  · intro address
    trivial
  · intro address
    trivial
  · intro address
    trivial
  · intro address _hlt
    trivial

private theorem concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural_primitiveOperandsFit_reviewerWordBits
    (shape : Cartesian.CartesianShape) (leftClose rightClose : Nat) :
    forall event,
      event ∈
          (concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
            shape leftClose rightClose).trace ->
        concreteBPNativeTraceEventPrimitiveOperandsFitInBits
          (concreteBPNativeSuccinctRMQReviewerWordBits shape.size) event := by
  exact
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.lcaCloseTraceResultWithRankSeedAllSizeStructural_trace_forall
      shape
      (concreteBPNativeRankCloseWordTraceResultAtSegment
        shape concreteBPNativeRankCloseTraceSegmentBase)
      concreteBPNativeInteriorTraceSegments
      concreteBPNativeFringeChunkTraceSegment
      concreteBPNativeFiniteSmallSameBlockCloseTraceSegment
      leftClose rightClose
      (concreteBPNativeTraceEventPrimitiveOperandsFitInBits
        (concreteBPNativeSuccinctRMQReviewerWordBits shape.size))
      (fun pos =>
        concreteBPNativeRankCloseWordTraceResultAtSegment_primitiveOperandsFit_reviewerWordBits
          shape concreteBPNativeRankCloseTraceSegmentBase pos)
      (fun blockSize close =>
        concreteBPNativeLocalBPWindowBitsTraceResult_primitiveOperandsFit_reviewerWordBits
          shape blockSize close)
      (fun blockSize close seed =>
        SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedLeftFringeCandidateSeededTraceResultAtSegment_trace_forall
          shape concreteBPNativeFringeChunkTraceSegment blockSize close seed
          (concreteBPNativeTraceEventPrimitiveOperandsFitInBits
            (concreteBPNativeSuccinctRMQReviewerWordBits shape.size))
          (concreteBPNativeLocalBPWindowBitsTraceResult_primitiveOperandsFit_reviewerWordBits
            shape blockSize close)
          (fun address _hlt => by trivial))
      (fun blockSize close seed =>
        SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedRightFringeCandidateSeededTraceResultAtSegment_trace_forall
          shape concreteBPNativeFringeChunkTraceSegment blockSize close seed
          (concreteBPNativeTraceEventPrimitiveOperandsFitInBits
            (concreteBPNativeSuccinctRMQReviewerWordBits shape.size))
          (concreteBPNativeLocalBPWindowBitsTraceResult_primitiveOperandsFit_reviewerWordBits
            shape blockSize close)
          (fun address _hlt => by trivial))
      (fun startBlock count =>
        concreteBPNativeInteriorGlobalWordTraceResultAllSizeStructural_primitiveOperandsFit_reviewerWordBits
          shape startBlock count)

namespace WholeQueryInstr

private theorem evalGlobalWordTrace_primitiveOperandsFit_reviewerWordBits
    (shape : Cartesian.CartesianShape) (left right : Nat)
    (instr : WholeQueryInstr) (state : WholeQueryState) :
    forall event,
      event ∈ (instr.evalGlobalWordTrace shape left right state).trace ->
        concreteBPNativeTraceEventPrimitiveOperandsFitInBits
          (concreteBPNativeSuccinctRMQReviewerWordBits shape.size) event := by
  cases instr with
  | selectClose dst idx =>
      unfold evalGlobalWordTrace
      apply WordRAM.TraceResult.map_trace_forall
      exact concreteBPNativeSelectCloseGlobalWordTraceResult_primitiveOperandsFit_reviewerWordBits
        shape (idx.eval left right state)
  | lcaClose dst leftReg rightReg =>
      cases hleft : state.opt leftReg with
      | none =>
          cases hright : state.opt rightReg <;>
            simp [evalGlobalWordTrace, hleft, hright]
      | some leftClose =>
          cases hright : state.opt rightReg with
          | none => simp [evalGlobalWordTrace, hleft, hright]
          | some rightClose =>
              simp only [evalGlobalWordTrace, hleft, hright]
              apply WordRAM.TraceResult.map_trace_forall
              exact concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural_primitiveOperandsFit_reviewerWordBits
                shape leftClose rightClose
  | rankCloseIfSome dst guard pos =>
      cases hguard : state.opt guard with
      | none => simp [evalGlobalWordTrace, hguard]
      | some value =>
          simp only [evalGlobalWordTrace, hguard]
          apply WordRAM.TraceResult.map_trace_forall
          exact concreteBPNativeRankCloseWordTraceResultAtSegment_primitiveOperandsFit_reviewerWordBits
            shape concreteBPNativeRankCloseTraceSegmentBase
            (pos.eval left right state)
  | outputPredIfSome dst guard src =>
      cases hguard : state.opt guard <;>
        simp [evalGlobalWordTrace, hguard]

end WholeQueryInstr

namespace WholeQueryProgram

private theorem evalGlobalWordTrace_primitiveOperandsFit_reviewerWordBits
    (shape : Cartesian.CartesianShape) (left right : Nat)
    (program : WholeQueryProgram) (state : WholeQueryState) :
    forall event,
      event ∈
          (evalGlobalWordTrace shape left right program state).trace ->
        concreteBPNativeTraceEventPrimitiveOperandsFitInBits
          (concreteBPNativeSuccinctRMQReviewerWordBits shape.size) event := by
  induction program generalizing state with
  | nil => simp [evalGlobalWordTrace]
  | cons instr rest ih =>
      unfold evalGlobalWordTrace
      apply WordRAM.TraceResult.bind_trace_forall
      · exact WholeQueryInstr.evalGlobalWordTrace_primitiveOperandsFit_reviewerWordBits
          shape left right instr state
      · exact ih
          (instr.evalGlobalWordTrace shape left right state).value

end WholeQueryProgram

theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_primitiveOperandsFit_reviewerWordBits
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    forall event,
      event ∈
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
            shape left right).trace ->
        concreteBPNativeTraceEventPrimitiveOperandsFitInBits
          (concreteBPNativeSuccinctRMQReviewerWordBits shape.size) event := by
  unfold concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
  apply WordRAM.TraceResult.map_trace_forall
  exact WholeQueryProgram.evalGlobalWordTrace_primitiveOperandsFit_reviewerWordBits
    shape left right concreteBPNativeSuccinctRMQWholeQueryProgram
    WholeQueryState.empty

theorem concreteBPNativeTraceEventNatEnvelope_le_traceNatEnvelope_of_mem
    {trace : List WordRAM.TraceEvent} {event : WordRAM.TraceEvent}
    (hmem : List.Mem event trace) :
    concreteBPNativeTraceEventNatEnvelope event <=
      concreteBPNativeTraceNatEnvelope trace := by
  induction trace with
  | nil =>
      cases hmem
  | cons head tail ih =>
      cases hmem with
      | head =>
          exact Nat.le_max_left _ _
      | tail _ htail =>
          exact Nat.le_trans (ih htail) (Nat.le_max_right _ _)

theorem concreteBPNativeTraceEventNatEnvelope_lt_two_pow_bitWidth_of_mem
    {trace : List WordRAM.TraceEvent} {event : WordRAM.TraceEvent}
    (hmem : List.Mem event trace) :
    concreteBPNativeTraceEventNatEnvelope event <
      2 ^ concreteBPNativeTraceEventBitWidth trace := by
  have hle :=
    concreteBPNativeTraceEventNatEnvelope_le_traceNatEnvelope_of_mem
      (trace := trace) (event := event) hmem
  have hlt :
      concreteBPNativeTraceNatEnvelope trace <
        2 ^ concreteBPNativeTraceEventBitWidth trace := by
    unfold concreteBPNativeTraceEventBitWidth
    exact Nat.lt_log2_self
  exact Nat.lt_of_le_of_lt hle hlt

theorem concreteBPNativeTraceEventReadAddressFitsInBits_of_mem
    {trace : List WordRAM.TraceEvent} {event : WordRAM.TraceEvent}
    (hmem : List.Mem event trace) :
    concreteBPNativeTraceEventReadAddressFitsInBits
      (concreteBPNativeTraceEventBitWidth trace) event := by
  have hlt :=
    concreteBPNativeTraceEventNatEnvelope_lt_two_pow_bitWidth_of_mem
      (trace := trace) (event := event) hmem
  cases event with
  | readWord segment index word? =>
      have hmax :
          Nat.max segment index <
            2 ^ concreteBPNativeTraceEventBitWidth trace := by
        simpa [concreteBPNativeTraceEventNatEnvelope] using hlt
      constructor
      · exact Nat.lt_of_le_of_lt (Nat.le_max_left segment index) hmax
      · exact Nat.lt_of_le_of_lt (Nat.le_max_right segment index) hmax
  | wordRank target limit result =>
      trivial
  | wordSelect target occurrence result =>
      trivial
  | syntheticCostOnlyPrimitive =>
      trivial

theorem concreteBPNativeTraceEventPrimitiveOperandsFitInBits_of_mem
    {trace : List WordRAM.TraceEvent} {event : WordRAM.TraceEvent}
    (hmem : List.Mem event trace) :
    concreteBPNativeTraceEventPrimitiveOperandsFitInBits
      (concreteBPNativeTraceEventBitWidth trace) event := by
  have hlt :=
    concreteBPNativeTraceEventNatEnvelope_lt_two_pow_bitWidth_of_mem
      (trace := trace) (event := event) hmem
  cases event with
  | readWord segment index word? =>
      trivial
  | wordRank target limit result =>
      have hmax :
          Nat.max limit result <
            2 ^ concreteBPNativeTraceEventBitWidth trace := by
        simpa [concreteBPNativeTraceEventNatEnvelope] using hlt
      constructor
      · exact Nat.lt_of_le_of_lt (Nat.le_max_left limit result) hmax
      · exact Nat.lt_of_le_of_lt (Nat.le_max_right limit result) hmax
  | wordSelect target occurrence result =>
      cases result with
      | none =>
          constructor
          · simpa [WordRAM.Register.FitsInBits,
              concreteBPNativeTraceEventNatEnvelope] using hlt
          · intro value hvalue
            cases hvalue
      | some result =>
          have hmax :
              Nat.max occurrence result <
                2 ^ concreteBPNativeTraceEventBitWidth trace := by
            simpa [concreteBPNativeTraceEventNatEnvelope] using hlt
          constructor
          · exact Nat.lt_of_le_of_lt
              (Nat.le_max_left occurrence result) hmax
          · intro value hvalue
            cases hvalue
            exact Nat.lt_of_le_of_lt
              (Nat.le_max_right occurrence result) hmax
  | syntheticCostOnlyPrimitive =>
      trivial

/--
Trace-local bit width for the final all-size global payload-store trace.  It is
the finite bound consumed by the bounded execution-story theorem below.
-/
def concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceEventBits
    (shape : Cartesian.CartesianShape)
    (left right : Nat) : Nat :=
  concreteBPNativeTraceEventBitWidth
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
      shape left right).trace

/-- Large-regime companion trace-local bit width. -/
def concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceEventBitsOfSizeGe
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (left right : Nat) : Nat :=
  concreteBPNativeTraceEventBitWidth
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultOfSizeGe
      shape hsize left right).trace

theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_eq_traceResult_toCosted
    (shape : Cartesian.CartesianShape)
    (left right : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
      shape left right =
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).toCosted := by
  rfl

theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_refines_canonicalInterpretedCosted
    (shape : Cartesian.CartesianShape)
    (left right : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
      shape left right =
      concreteBPNativeSuccinctRMQWholeQueryCanonicalInterpretedCosted shape left right := by
  unfold concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
    concreteBPNativeSuccinctRMQWholeQueryCanonicalInterpretedCosted
  rw [WordRAM.TraceResult.map_toCosted]
  rw [
    WholeQueryProgram.evalGlobalWordTrace_refines_eval
      shape left right concreteBPNativeSuccinctRMQWholeQueryProgram
      WholeQueryState.empty]

/-! ### Producer call-site provenance -/

/--
A concrete may-read path inside a read-producing instruction.

Every constructor carries membership of the same read event in an actual
component subtrace used by the instruction evaluator.  This is deliberately a
relation: the LCA and final-rank producers both have paths through segments
`17`--`19`, and the shared BP source has select, LCA, and final-rank paths.
-/
inductive ReviewerProducerReadPath
    (shape : Cartesian.CartesianShape) :
    ReviewerReadLeaf -> Nat -> Nat -> Option WordRAM.Word -> Prop
  | selectSuper {slot segment index word?}
      (hmem : WordRAM.TraceEvent.readWord segment index word? ∈
        (((GenericSelect.sparseExceptionSelectData shape.bpCode false).superTable).readTraceResultRelabeledWithStore
          concreteBPNativeSelectCloseTraceSegmentLayout.superTable
          (concreteBPNativeSuccinctRMQGlobalReadStore shape) slot).trace) :
      ReviewerProducerReadPath shape .selectClose segment index word?
  | selectLongRank {pos segment index word?}
      (hmem : WordRAM.TraceEvent.readWord segment index word? ∈
        ((GenericSelect.sparseExceptionSelectData shape.bpCode
            false).longFlagRankData.bpChunkedRankTraceResultWithStore
          (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          concreteBPNativeSelectCloseTraceSegmentLayout.longFlagRankBase
          (concreteBPNativeSelectCloseTraceSegmentLayout.longFlagRankBase + 1)
          (concreteBPNativeSelectCloseTraceSegmentLayout.longFlagRankBase + 2)
          concreteBPNativeFringeChunkTraceSegment
          (SuccinctClose.bpFringeChunkBits shape.bpCode.length) true
          pos).trace) :
      ReviewerProducerReadPath shape .selectClose segment index word?
  | selectLongRelative {base slot segment index word?}
      (hmem : WordRAM.TraceEvent.readWord segment index word? ∈
        (GenericSelect.bpRelativeOffsetReadTraceResultWithStore
          (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          concreteBPNativeSelectCloseTraceSegmentLayout.longRelativeBase
          base slot).trace) :
      ReviewerProducerReadPath shape .selectClose segment index word?
  | selectLocal {slot segment index word?}
      (hmem : WordRAM.TraceEvent.readWord segment index word? ∈
        (((GenericSelect.sparseExceptionSelectData shape.bpCode false).localTable).readTraceResultRelabeledWithStore
          concreteBPNativeSelectCloseTraceSegmentLayout.localTable
          (concreteBPNativeSuccinctRMQGlobalReadStore shape) slot).trace) :
      ReviewerProducerReadPath shape .selectClose segment index word?
  | selectSparse {base localSlot localOccurrence segment index word?}
      (hmem : WordRAM.TraceEvent.readWord segment index word? ∈
        (((GenericSelect.sparseExceptionSelectData shape.bpCode false).sparseDirectory).bpChunkedReadTraceResultWithStore
          concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory
          concreteBPNativeFringeChunkTraceSegment
          (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          (SuccinctClose.bpFringeChunkBits shape.bpCode.length)
          base localSlot localOccurrence).trace) :
      ReviewerProducerReadPath shape .selectClose segment index word?
  | selectDense {basePosition baseOccurrence q segment index word?}
      (hmem : WordRAM.TraceEvent.readWord segment index word? ∈
        (GenericSelect.bpChunkedDenseTwoWordSelectTraceResultWithStore
          concreteBPNativeSelectCloseTraceSegmentLayout.bitWordBase
          concreteBPNativeFringeChunkTraceSegment
          concreteBPNativeSelectChunkTraceSegment
          (SuccinctClose.bpFringeChunkBits shape.bpCode.length) false
          (GenericSelect.sparseExceptionSelectData shape.bpCode false).bitWords
          (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          basePosition baseOccurrence q).trace) :
      ReviewerProducerReadPath shape .selectClose segment index word?
  | selectDenseInWord {word occurrence segment index word?}
      (hmem : WordRAM.TraceEvent.readWord segment index word? ∈
        (SuccinctClose.bpChunkedWordSelectTraceResultAtSegmentsWithStore
          (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          concreteBPNativeFringeChunkTraceSegment
          concreteBPNativeSelectChunkTraceSegment
          (SuccinctClose.bpFringeChunkBits shape.bpCode.length) false
          word occurrence).trace) :
      ReviewerProducerReadPath shape .selectClose segment index word?
  | lcaRank {pos segment index word?}
      (hmem : WordRAM.TraceEvent.readWord segment index word? ∈
        (concreteBPNativeRankCloseWordTraceResultAtSegment shape
          concreteBPNativeRankCloseTraceSegmentBase pos).trace) :
      ReviewerProducerReadPath shape .canonicalClose segment index word?
  | lcaBP {blockSize close segment index word?}
      (hmem : WordRAM.TraceEvent.readWord segment index word? ∈
        (SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPWindowBitsTraceResult
          shape blockSize close).trace) :
      ReviewerProducerReadPath shape .canonicalClose segment index word?
  | lcaInterior {startBlock count segment index word?}
      (hmem : WordRAM.TraceEvent.readWord segment index word? ∈
        (SuccinctClose.ConcreteCompactBPCloseLCADirectory.concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructural
          shape concreteBPNativeInteriorTraceSegments startBlock count).trace) :
      ReviewerProducerReadPath shape .canonicalClose segment index word?
  | finalRank {pos segment index word?}
      (hmem : WordRAM.TraceEvent.readWord segment index word? ∈
        (concreteBPNativeRankCloseWordTraceResultAtSegment shape
          concreteBPNativeRankCloseTraceSegmentBase pos).trace) :
      ReviewerProducerReadPath shape .rankClose segment index word?
  | lcaFringeLeft {blockSize close seed segment index word?}
      (hmem : WordRAM.TraceEvent.readWord segment index word? ∈
        (SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedLeftFringeCandidateSeededTraceResultAtSegment
          shape concreteBPNativeFringeChunkTraceSegment blockSize close
          seed).trace) :
      ReviewerProducerReadPath shape .canonicalClose segment index word?
  | lcaFringeRight {blockSize close seed segment index word?}
      (hmem : WordRAM.TraceEvent.readWord segment index word? ∈
        (SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedRightFringeCandidateSeededTraceResultAtSegment
          shape concreteBPNativeFringeChunkTraceSegment blockSize close
          seed).trace) :
      ReviewerProducerReadPath shape .canonicalClose segment index word?

private def reviewerProducerReadPathEvent
    (shape : Cartesian.CartesianShape) (leaf : ReviewerReadLeaf) :
    WordRAM.TraceEvent -> Prop
  | .readWord segment index word? =>
      ReviewerProducerReadPath shape leaf segment index word?
  | _ => True

private theorem selectCloseGlobalWordTraceResult_producerReadPath
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    ∀ event,
      event ∈
          (concreteBPNativeSelectCloseGlobalWordTraceResult shape idx).trace ->
        reviewerProducerReadPathEvent shape .selectClose event := by
  apply
    (GenericSelect.sparseExceptionSelectData
        shape.bpCode false).bpChunkedSelectTraceResultWithStore_trace_forall
  · intro slot event hmem
    cases event with
    | readWord => exact ReviewerProducerReadPath.selectSuper hmem
    | wordRank => trivial
    | wordSelect => trivial
    | syntheticCostOnlyPrimitive => trivial
  · intro pos event hmem
    cases event with
    | readWord => exact ReviewerProducerReadPath.selectLongRank hmem
    | wordRank => trivial
    | wordSelect => trivial
    | syntheticCostOnlyPrimitive => trivial
  · intro base slot event hmem
    cases event with
    | readWord => exact ReviewerProducerReadPath.selectLongRelative hmem
    | wordRank => trivial
    | wordSelect => trivial
    | syntheticCostOnlyPrimitive => trivial
  · intro slot event hmem
    cases event with
    | readWord => exact ReviewerProducerReadPath.selectLocal hmem
    | wordRank => trivial
    | wordSelect => trivial
    | syntheticCostOnlyPrimitive => trivial
  · intro base localSlot localOccurrence event hmem
    cases event with
    | readWord => exact ReviewerProducerReadPath.selectSparse hmem
    | wordRank => trivial
    | wordSelect => trivial
    | syntheticCostOnlyPrimitive => trivial
  · intro basePosition baseOccurrence q event hmem
    cases event with
    | readWord => exact ReviewerProducerReadPath.selectDense hmem
    | wordRank => trivial
    | wordSelect => trivial
    | syntheticCostOnlyPrimitive => trivial

private theorem rankCloseGlobalWordTraceResult_producerReadPath
    (shape : Cartesian.CartesianShape) (pos : Nat) :
    ∀ event,
      event ∈
          (concreteBPNativeRankCloseWordTraceResultAtSegment shape
            concreteBPNativeRankCloseTraceSegmentBase pos).trace ->
        reviewerProducerReadPathEvent shape .rankClose event := by
  intro event hmem
  cases event with
  | readWord => exact ReviewerProducerReadPath.finalRank hmem
  | wordRank => trivial
  | wordSelect => trivial
  | syntheticCostOnlyPrimitive => trivial

private theorem lcaCloseGlobalWordTraceResult_producerReadPath
    (shape : Cartesian.CartesianShape) (leftClose rightClose : Nat) :
    ∀ event,
      event ∈
          (concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
            shape leftClose rightClose).trace ->
        reviewerProducerReadPathEvent shape .canonicalClose event := by
  unfold concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
  apply
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.lcaCloseTraceResultWithRankSeedAllSizeStructural_trace_forall
      shape
      (concreteBPNativeRankCloseWordTraceResultAtSegment
        shape concreteBPNativeRankCloseTraceSegmentBase)
      concreteBPNativeInteriorTraceSegments
      concreteBPNativeFringeChunkTraceSegment
      concreteBPNativeFiniteSmallSameBlockCloseTraceSegment
      leftClose rightClose
      (reviewerProducerReadPathEvent shape .canonicalClose)
  · intro pos event hmem
    cases event with
    | readWord => exact ReviewerProducerReadPath.lcaRank hmem
    | wordRank => trivial
    | wordSelect => trivial
    | syntheticCostOnlyPrimitive => trivial
  · intro blockSize close event hmem
    cases event with
    | readWord => exact ReviewerProducerReadPath.lcaBP hmem
    | wordRank => trivial
    | wordSelect => trivial
    | syntheticCostOnlyPrimitive => trivial
  · intro blockSize close seed event hmem
    cases event with
    | readWord => exact ReviewerProducerReadPath.lcaFringeLeft hmem
    | wordRank => trivial
    | wordSelect => trivial
    | syntheticCostOnlyPrimitive => trivial
  · intro blockSize close seed event hmem
    cases event with
    | readWord => exact ReviewerProducerReadPath.lcaFringeRight hmem
    | wordRank => trivial
    | wordSelect => trivial
    | syntheticCostOnlyPrimitive => trivial
  · intro startBlock count event hmem
    cases event with
    | readWord => exact ReviewerProducerReadPath.lcaInterior hmem
    | wordRank => trivial
    | wordSelect => trivial
    | syntheticCostOnlyPrimitive => trivial

/-- Every read from one instruction is decomposed through the exact component
subtrace that produced it. -/
theorem WholeQueryInstr.evalGlobalWordTrace_read_producer_path
    (shape : Cartesian.CartesianShape) (left right : Nat)
    (instr : WholeQueryInstr) (state : WholeQueryState)
    {segment index : Nat} {word? : Option WordRAM.Word}
    (hmem : WordRAM.TraceEvent.readWord segment index word? ∈
      (instr.evalGlobalWordTrace shape left right state).trace) :
    ∃ leaf : ReviewerReadLeaf,
      instr.reviewerReadLeaf? = some leaf ∧
      ReviewerProducerReadPath shape leaf segment index word? := by
  cases instr with
  | selectClose dst idx =>
      refine ⟨.selectClose, rfl, ?_⟩
      exact selectCloseGlobalWordTraceResult_producerReadPath shape
        (idx.eval left right state)
        (WordRAM.TraceEvent.readWord segment index word?)
        (by simpa [WholeQueryInstr.evalGlobalWordTrace] using hmem)
  | lcaClose dst leftReg rightReg =>
      cases hleft : state.opt leftReg with
      | none =>
          simp [WholeQueryInstr.evalGlobalWordTrace, hleft] at hmem
      | some leftClose =>
          cases hright : state.opt rightReg with
          | none =>
              simp [WholeQueryInstr.evalGlobalWordTrace, hleft, hright] at hmem
          | some rightClose =>
              refine ⟨.canonicalClose, rfl, ?_⟩
              exact lcaCloseGlobalWordTraceResult_producerReadPath
                shape leftClose rightClose
                (WordRAM.TraceEvent.readWord segment index word?)
                (by
                  simpa [WholeQueryInstr.evalGlobalWordTrace, hleft, hright]
                    using hmem)
  | rankCloseIfSome dst guard pos =>
      cases hguard : state.opt guard with
      | none =>
          simp [WholeQueryInstr.evalGlobalWordTrace, hguard] at hmem
      | some guardValue =>
          refine ⟨.rankClose, rfl, ?_⟩
          exact rankCloseGlobalWordTraceResult_producerReadPath shape
            (pos.eval left right state)
            (WordRAM.TraceEvent.readWord segment index word?)
            (by simpa [WholeQueryInstr.evalGlobalWordTrace, hguard] using hmem)
  | outputPredIfSome dst guard src =>
      cases hguard : state.opt guard <;>
        simp [WholeQueryInstr.evalGlobalWordTrace, hguard] at hmem

/-- Exact parameter tuple used by one read-producing whole-query instruction. -/
inductive ReviewerReadInvocation where
  | selectClose (idx : Nat)
  | canonicalClose (leftClose rightClose : Nat)
  | rankClose (pos : Nat)
deriving Repr

namespace ReviewerReadInvocation

/-- Reviewer leaf selected by an exact invocation. -/
def leaf : ReviewerReadInvocation -> ReviewerReadLeaf
  | .selectClose _ => .selectClose
  | .canonicalClose _ _ => .canonicalClose
  | .rankClose _ => .rankClose

/-- Exact component trace used by an invocation. -/
def componentTrace
    (shape : Cartesian.CartesianShape) :
    ReviewerReadInvocation -> List WordRAM.TraceEvent
  | .selectClose idx =>
      (concreteBPNativeSelectCloseGlobalWordTraceResult shape idx).trace
  | .canonicalClose leftClose rightClose =>
      (concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
        shape leftClose rightClose).trace
  | .rankClose pos =>
      (concreteBPNativeRankCloseWordTraceResultAtSegment
        shape concreteBPNativeRankCloseTraceSegmentBase pos).trace

end ReviewerReadInvocation

namespace WholeQueryInstr

/-- The exact invocation computed by an instruction from its real pre-state. -/
inductive InvokesReviewerRead
    (left right : Nat) (state : WholeQueryState) :
    WholeQueryInstr -> ReviewerReadInvocation -> Prop
  | selectClose (dst : WholeQueryOptReg) (idx : WholeQueryNatExpr) :
      InvokesReviewerRead left right state (.selectClose dst idx)
        (.selectClose (idx.eval left right state))
  | canonicalClose
      (dst leftReg rightReg : WholeQueryOptReg)
      (leftClose rightClose : Nat)
      (hleft : state.opt leftReg = some leftClose)
      (hright : state.opt rightReg = some rightClose) :
      InvokesReviewerRead left right state (.lcaClose dst leftReg rightReg)
        (.canonicalClose leftClose rightClose)
  | rankClose
      (dst : WholeQueryNatReg) (guard : WholeQueryOptReg)
      (pos : WholeQueryNatExpr) (guardValue : Nat)
      (hguard : state.opt guard = some guardValue) :
      InvokesReviewerRead left right state (.rankCloseIfSome dst guard pos)
        (.rankClose (pos.eval left right state))

/-- A local indexed read retains the exact component invocation and the same
local position inside that invocation's component trace. -/
theorem evalGlobalWordTrace_getElem?_read_invocation
    (shape : Cartesian.CartesianShape) (left right : Nat)
    (instr : WholeQueryInstr) (state : WholeQueryState)
    (localPos segment index : Nat) (word? : Option WordRAM.Word)
    (hget : (instr.evalGlobalWordTrace shape left right state).trace[localPos]? =
      some (.readWord segment index word?)) :
    ∃ invocation : ReviewerReadInvocation,
      InvokesReviewerRead left right state instr invocation ∧
      (invocation.componentTrace shape)[localPos]? =
        some (.readWord segment index word?) := by
  cases instr with
  | selectClose dst idx =>
      exact ⟨.selectClose (idx.eval left right state),
        InvokesReviewerRead.selectClose dst idx,
        by simpa [WholeQueryInstr.evalGlobalWordTrace,
          ReviewerReadInvocation.componentTrace] using hget⟩
  | lcaClose dst leftReg rightReg =>
      cases hleft : state.opt leftReg with
      | none =>
          simp [WholeQueryInstr.evalGlobalWordTrace, hleft] at hget
      | some leftClose =>
          cases hright : state.opt rightReg with
          | none =>
              simp [WholeQueryInstr.evalGlobalWordTrace, hleft, hright] at hget
          | some rightClose =>
              exact ⟨.canonicalClose leftClose rightClose,
                InvokesReviewerRead.canonicalClose
                  dst leftReg rightReg leftClose rightClose hleft hright,
                by simpa [WholeQueryInstr.evalGlobalWordTrace, hleft, hright,
                  ReviewerReadInvocation.componentTrace] using hget⟩
  | rankCloseIfSome dst guard pos =>
      cases hguard : state.opt guard with
      | none =>
          simp [WholeQueryInstr.evalGlobalWordTrace, hguard] at hget
      | some guardValue =>
          exact ⟨.rankClose (pos.eval left right state),
            InvokesReviewerRead.rankClose dst guard pos guardValue hguard,
            by simpa [WholeQueryInstr.evalGlobalWordTrace, hguard,
              ReviewerReadInvocation.componentTrace] using hget⟩
  | outputPredIfSome dst guard src =>
      cases hguard : state.opt guard <;>
        simp [WholeQueryInstr.evalGlobalWordTrace, hguard] at hget

theorem InvokesReviewerRead.reviewerReadLeaf?_eq
    {left right : Nat} {state : WholeQueryState}
    {instr : WholeQueryInstr} {invocation : ReviewerReadInvocation}
    (hinvocation : InvokesReviewerRead left right state instr invocation) :
    instr.reviewerReadLeaf? = some invocation.leaf := by
  cases hinvocation <;>
    simp [WholeQueryInstr.reviewerReadLeaf?, ReviewerReadInvocation.leaf]

end WholeQueryInstr

private theorem fixedWidthNatTableMachineChunkCount_pos
    {width wordSize : Nat} (hwidth : 0 < width) :
    0 < SuccinctSpace.fixedWidthNatTableMachineChunkCount width wordSize := by
  by_cases hmod : width % wordSize = 0
  · have hdecomp := Nat.mod_add_div width wordSize
    have hdiv : width / wordSize ≠ 0 := by
      intro hzero
      simp [hmod, hzero] at hdecomp
      omega
    simpa [SuccinctSpace.fixedWidthNatTableMachineChunkCount, hmod] using
      Nat.pos_of_ne_zero hdiv
  · simp [SuccinctSpace.fixedWidthNatTableMachineChunkCount, hmod]

private theorem machineReadComputationAt_mayRead
    {entries : List Nat} {width : Nat}
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (wordSize base deadAddress i : Nat)
    (hwidth : 0 < width)
    (store : SuccinctSpace.FlatWordStore) :
    ∃ address word?, (address, word?) ∈
      ((table.machineReadComputationAt wordSize base deadAddress i).run
        store).reads := by
  let count := SuccinctSpace.fixedWidthNatTableMachineChunkCount width wordSize
  have hcount : 0 < count :=
    fixedWidthNatTableMachineChunkCount_pos hwidth
  unfold SuccinctSpace.FixedWidthNatTable.machineReadComputationAt
  by_cases hvalid : i < entries.length
  · obtain ⟨tail, hcountEq⟩ := Nat.exists_eq_succ_of_ne_zero
      (Nat.ne_of_gt hcount)
    refine ⟨base + i * count, store (base + i * count), ?_⟩
    simp only [hvalid, if_true,
      SuccinctSpace.FlatStoreComputation.map_run_reads,
      SuccinctSpace.FlatStoreComputation.readMany_run_reads,
      List.mem_map]
    refine ⟨base + i * count, ?_, rfl⟩
    unfold SuccinctSpace.fixedWidthNatTableMachineFootprintAt
    apply List.mem_map_of_mem (f := fun address => base + address)
    unfold SuccinctSpace.fixedWidthNatTableMachineFootprint
    change i * count ∈ SuccinctSpace.consecutiveWordIndices (i * count) count
    rw [hcountEq]
    exact List.Mem.head _
  · refine ⟨deadAddress, store deadAddress, ?_⟩
    simp [hvalid, SuccinctSpace.FlatStoreComputation.map_run_reads,
      SuccinctSpace.FlatStoreComputation.readMany_run_reads]

private theorem selectEntryTableWithStore_mayRead
    {entries : List GenericSelect.SparseDenseSelectDenseLocalEntry}
    {fieldWidth : Nat}
    (table :
      GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable
        entries fieldWidth)
    (layout : GenericSelect.SparseDenseEntryTableTraceSegmentBases)
    (store : WordRAM.ReadStore) :
    (∃ word?, WordRAM.TraceEvent.readWord layout.baseOccurrence 0 word? ∈
      (table.readTraceResultRelabeledWithStore layout store 0).trace) ∧
    (∃ word?, WordRAM.TraceEvent.readWord layout.baseWordIndex 0 word? ∈
      (table.readTraceResultRelabeledWithStore layout store 0).trace) ∧
    (∃ word?, WordRAM.TraceEvent.readWord layout.rankBefore 0 word? ∈
      (table.readTraceResultRelabeledWithStore layout store 0).trace) ∧
    (∃ word?, WordRAM.TraceEvent.readWord layout.firstOffset 0 word? ∈
      (table.readTraceResultRelabeledWithStore layout store 0).trace) := by
  refine ⟨⟨store.readWord? layout.baseOccurrence 0, ?_⟩,
    ⟨store.readWord? layout.baseWordIndex 0, ?_⟩,
    ⟨store.readWord? layout.rankBefore 0, ?_⟩,
    ⟨store.readWord? layout.firstOffset 0, ?_⟩⟩
  all_goals
    simp [GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable.readTraceResultRelabeledWithStore,
      WordRAM.TraceResult.ofProgramWithStore,
      SuccinctSpace.FixedWidthNatTable.readProgram,
      SuccinctSpace.PayloadWordStore.readProgram,
      WordRAM.Program.evalR, WordRAM.TraceResult.bind,
      WordRAM.TraceResult.map, WordRAM.TraceResult.pure,
      WordRAM.TraceResult.relabelReadSegmentsWith,
      WordRAM.TraceResult.ofResult,
      WordRAM.TraceEvent.relabelReadSegmentWith,
      WordRAM.singletonSegmentMap, WordRAM.TraceEvent.singletonSegmentMap,
      WordRAM.ReadStore.pullback]

private theorem chunkedRankTraceWithStore_mayRead
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data : SuccinctRank.TwoLevelPayloadLiveStoredWordRankData
      bits superOverhead blockOverhead queryCost)
    (store : WordRAM.ReadStore)
    (superSegment blockSegment wordSegment chunkSegment c : Nat)
    (target : Bool) :
    (∃ index word?, WordRAM.TraceEvent.readWord superSegment index word? ∈
      (data.bpChunkedRankTraceResultWithStore store superSegment
        blockSegment wordSegment chunkSegment c target 0).trace) ∧
    (∃ index word?, WordRAM.TraceEvent.readWord blockSegment index word? ∈
      (data.bpChunkedRankTraceResultWithStore store superSegment
        blockSegment wordSegment chunkSegment c target 0).trace) ∧
    (∃ index word?, WordRAM.TraceEvent.readWord wordSegment index word? ∈
      (data.bpChunkedRankTraceResultWithStore store superSegment
        blockSegment wordSegment chunkSegment c target 0).trace) := by
  refine ⟨⟨data.superIndex 0, store.readWord? superSegment
      (data.superIndex 0), ?_⟩,
    ⟨data.wordIndex 0, store.readWord? blockSegment (data.wordIndex 0), ?_⟩,
    ⟨data.wordIndex 0, store.readWord? wordSegment (data.wordIndex 0), ?_⟩⟩
  · simp [SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.bpChunkedRankTraceResultWithStore,
      WordRAM.TraceResult.bind_trace, List.mem_append,
      SuccinctClose.bpChunkReadTraceResult, List.mem_singleton]
  · simp [SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.bpChunkedRankTraceResultWithStore,
      WordRAM.TraceResult.bind_trace, List.mem_append,
      SuccinctClose.bpChunkReadTraceResult, List.mem_singleton]
  · simp [SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.bpChunkedRankTraceResultWithStore,
      WordRAM.TraceResult.bind_trace, List.mem_append,
      SuccinctClose.bpChunkReadTraceResult,
      SuccinctClose.bpWordReadTraceResult, List.mem_singleton]

private theorem chunkedRelativeOffsetWithStore_mayRead
    (store : WordRAM.ReadStore) (segment base slot : Nat) :
    ∃ word?, WordRAM.TraceEvent.readWord segment slot word? ∈
      (GenericSelect.bpRelativeOffsetReadTraceResultWithStore store
        segment base slot).trace := by
  refine ⟨store.readWord? segment slot, ?_⟩
  show WordRAM.TraceEvent.readWord segment slot
      (store.readWord? segment slot) ∈
    (WordRAM.TraceResult.map
      (fun offset? => offset?.map (fun offset => base + offset))
      (SuccinctClose.bpChunkReadTraceResult store segment slot)).trace
  rw [WordRAM.TraceResult.map_trace]
  exact List.Mem.head _

private theorem chunkedSparseDirectoryWithStore_mayRead
    (shape : Cartesian.CartesianShape) :
    (∃ index word?, WordRAM.TraceEvent.readWord 13 index word? ∈
      (((GenericSelect.sparseExceptionSelectData shape.bpCode false).sparseDirectory).bpChunkedReadTraceResultWithStore
        concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory
        concreteBPNativeFringeChunkTraceSegment
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (SuccinctClose.bpFringeChunkBits shape.bpCode.length)
        0 0 0).trace) ∧
    (∃ index word?, WordRAM.TraceEvent.readWord 14 index word? ∈
      (((GenericSelect.sparseExceptionSelectData shape.bpCode false).sparseDirectory).bpChunkedReadTraceResultWithStore
        concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory
        concreteBPNativeFringeChunkTraceSegment
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (SuccinctClose.bpFringeChunkBits shape.bpCode.length)
        0 0 0).trace) ∧
    (∃ index word?, WordRAM.TraceEvent.readWord 15 index word? ∈
      (((GenericSelect.sparseExceptionSelectData shape.bpCode false).sparseDirectory).bpChunkedReadTraceResultWithStore
        concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory
        concreteBPNativeFringeChunkTraceSegment
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (SuccinctClose.bpFringeChunkBits shape.bpCode.length)
        0 0 0).trace) ∧
    (∃ index word?, WordRAM.TraceEvent.readWord 16 index word? ∈
      (((GenericSelect.sparseExceptionSelectData shape.bpCode false).sparseDirectory).bpChunkedReadTraceResultWithStore
        concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory
        concreteBPNativeFringeChunkTraceSegment
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (SuccinctClose.bpFringeChunkBits shape.bpCode.length)
        0 0 0).trace) := by
  rcases chunkedRankTraceWithStore_mayRead
      (GenericSelect.sparseExceptionSelectData shape.bpCode
        false).sparseDirectory.rankData
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.rankBase
      (concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.rankBase +
        1)
      (concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.rankBase +
        2)
      concreteBPNativeFringeChunkTraceSegment
      (SuccinctClose.bpFringeChunkBits shape.bpCode.length) true with
    ⟨⟨index13, word13, h13⟩, ⟨index14, word14, h14⟩,
      ⟨index15, word15, h15⟩⟩
  refine ⟨⟨index13, word13, ?_⟩, ⟨index14, word14, ?_⟩,
    ⟨index15, word15, ?_⟩, ?_⟩
  · simp only [GenericSelect.SparseExceptionDirectory.bpChunkedReadTraceResultWithStore,
      WordRAM.TraceResult.bind_trace, List.mem_append]
    exact Or.inl h13
  · simp only [GenericSelect.SparseExceptionDirectory.bpChunkedReadTraceResultWithStore,
      WordRAM.TraceResult.bind_trace, List.mem_append]
    exact Or.inl h14
  · simp only [GenericSelect.SparseExceptionDirectory.bpChunkedReadTraceResultWithStore,
      WordRAM.TraceResult.bind_trace, List.mem_append]
    exact Or.inl h15
  · rcases chunkedRelativeOffsetWithStore_mayRead
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.relativeBase
        0
        (GenericSelect.relativeSplitSelectSparseCompactSlot
          (((GenericSelect.sparseExceptionSelectData shape.bpCode
              false).sparseDirectory.rankData.bpChunkedRankTraceResultWithStore
            (concreteBPNativeSuccinctRMQGlobalReadStore shape)
            concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.rankBase
            (concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.rankBase +
              1)
            (concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.rankBase +
              2)
            concreteBPNativeFringeChunkTraceSegment
            (SuccinctClose.bpFringeChunkBits shape.bpCode.length) true
            0).value)
          0
          (GenericSelect.sparseExceptionSelectData shape.bpCode
            false).sparseDirectory.localStride) with
      ⟨word16, h16⟩
    refine ⟨GenericSelect.relativeSplitSelectSparseCompactSlot
        (((GenericSelect.sparseExceptionSelectData shape.bpCode
            false).sparseDirectory.rankData.bpChunkedRankTraceResultWithStore
          (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.rankBase
          (concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.rankBase +
            1)
          (concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.rankBase +
            2)
          concreteBPNativeFringeChunkTraceSegment
          (SuccinctClose.bpFringeChunkBits shape.bpCode.length) true
          0).value)
        0
        (GenericSelect.sparseExceptionSelectData shape.bpCode
          false).sparseDirectory.localStride, word16, ?_⟩
    simp only [GenericSelect.SparseExceptionDirectory.bpChunkedReadTraceResultWithStore,
      WordRAM.TraceResult.bind_trace, List.mem_append]
    exact Or.inr h16

private theorem chunkedDenseTwoWordSelectWithStore_mayRead
    {bits : List Bool} {wordSize : Nat}
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (bitWordSegment rankTableSegment selectTableSegment c : Nat)
    (target : Bool) (basePosition baseOccurrence q : Nat)
    (store : WordRAM.ReadStore) :
    ∃ word?, WordRAM.TraceEvent.readWord bitWordSegment
        (basePosition / wordSize) word? ∈
      (GenericSelect.bpChunkedDenseTwoWordSelectTraceResultWithStore
        bitWordSegment rankTableSegment selectTableSegment c target
        bitWords store basePosition baseOccurrence q).trace := by
  refine ⟨store.readWord? bitWordSegment (basePosition / wordSize), ?_⟩
  simp [GenericSelect.bpChunkedDenseTwoWordSelectTraceResultWithStore,
    WordRAM.TraceResult.bind_trace, List.mem_append,
    SuccinctClose.bpWordReadTraceResult, List.mem_singleton]

private theorem reviewerLocalBPWindow_mayRead
    (shape : Cartesian.CartesianShape) :
    ∃ index word?, WordRAM.TraceEvent.readWord 0 index word? ∈
      (SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPWindowBitsTraceResult
        shape 1 0).trace := by
  let wordSize := SuccinctRank.machineWordBits shape.bpCode.length
  let index := SuccinctClose.blockStartOf 1
    (SuccinctClose.blockOfClose 1 0) / wordSize
  let words := SuccinctSpace.chunkPayloadWords wordSize shape.bpCode
  refine ⟨index, words.toArray[index]?, ?_⟩
  simp [SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPWindowBitsTraceResult,
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPBlockWordsTraceResult,
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpCodeWordReadTraceResult,
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpCodeReadWordTraceEvent,
    WordRAM.TraceResult.bind, WordRAM.TraceResult.map,
    WordRAM.TraceResult.pure, index, wordSize, words]

private theorem reviewerCanonicalInterior_mayRead
    (shape : Cartesian.CartesianShape) :
    ∃ index word?, WordRAM.TraceEvent.readWord 20 index word? ∈
      (SuccinctClose.ConcreteCompactBPCloseLCADirectory.concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructural
        shape concreteBPNativeInteriorTraceSegments 0 1).trace := by
  have hraw := SuccinctClose.canonicalBPRelativeSummaryBlocksPerSuperRaw_pos shape
  have hmacro : 1 ≤
      SuccinctClose.canonicalBPRelativeSummaryBlocksPerSuperRaw shape *
        SuccinctClose.canonicalBPRelativeSummaryBlocksPerSuperRaw shape := by
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero
      (Nat.ne_of_gt hraw) (Nat.ne_of_gt hraw))
  let layout := SuccinctClose.RelativeRmm.canonicalLayout shape
  let table := SuccinctClose.canonicalRelativeRmmInteriorLocalTable shape
  let offsets := SuccinctClose.canonicalRelativeRmmInteriorComponentOffsets shape
  let array :=
    (SuccinctClose.canonicalRelativeRmmInteriorComponentStore shape).store.words
  let store := SuccinctSpace.FlatWordStore.ofArray array
  let slot := SuccinctClose.bpLocalSparseCellSlot layout.macroSize
    layout.levelCount 0 0 (Nat.log2 1)
  rcases machineReadComputationAt_mayRead table.table
      (SuccinctRank.machineWordBits shape.bpCode.length)
      offsets.localOffset offsets.deadAddress slot
      (SuccinctRank.machineWordBits_pos layout.macroSize) store with
    ⟨address, word?, hfirst⟩
  have hlocalSpan : (address, word?) ∈
      ((SuccinctClose.canonicalRelativeRmmMachineLocalSpanCandidateComputation
        shape 0 0 (Nat.log2 1)).run store).reads := by
    unfold SuccinctClose.canonicalRelativeRmmMachineLocalSpanCandidateComputation
    simp only [SuccinctSpace.FlatStoreComputation.bind_run,
      SuccinctSpace.FlatStoreExecution.append]
    apply List.mem_append_left
    simpa [SuccinctClose.canonicalRelativeRmmMachineReadNatComputation,
      table, offsets, layout, slot] using hfirst
  have htwo : (address, word?) ∈
      ((SuccinctClose.canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation
        shape 0 0 1).run store).reads := by
    unfold SuccinctClose.canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation
    simp only [SuccinctSpace.FlatStoreComputation.bind_run,
      SuccinctSpace.FlatStoreExecution.append]
    exact List.mem_append_left _ hlocalSpan
  have hexec : (address, word?) ∈
      (SuccinctClose.canonicalRelativeRmmInteriorRangeMinExecutionWithStore
        shape array 0 1).reads := by
    simpa [SuccinctClose.canonicalRelativeRmmInteriorRangeMinExecutionWithStore,
      SuccinctClose.canonicalRelativeRmmInteriorRangeMinExecutionWithRead,
      SuccinctClose.canonicalRelativeRmmInteriorRangeMinComputation,
      hmacro, array, store] using htwo
  refine ⟨address, word?, ?_⟩
  unfold SuccinctClose.ConcreteCompactBPCloseLCADirectory.concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructural
  unfold SuccinctClose.ConcreteCompactBPCloseLCADirectory.canonicalRelativeRmmInteriorRangeMinTraceResultAtSegment
  unfold SuccinctClose.flatStoreExecutionTraceResultAtSegment
  apply List.mem_map.mpr
  exact ⟨(address, word?), hexec, by
    simp [concreteBPNativeInteriorTraceSegments]⟩

/-- A counted source is may-live only through one exact callable component
read path, with the source and segment joined on that same event. -/
def ReviewerSource.HasProducerMayPath
    (shape : Cartesian.CartesianShape) (source : ReviewerSource) : Prop :=
  ∃ leaf : ReviewerReadLeaf,
  ∃ segment index : Nat,
  ∃ word? : Option WordRAM.Word,
    concreteBPNativeSuccinctRMQReviewerSegmentSource? segment = some source ∧
    ReviewerProducerReadPath shape leaf segment index word?

/-- Reverse reviewer liveness: every counted physical source has a concrete
attempted-read path in the select, rank, or compact-close construction. -/
theorem concreteBPNativeSuccinctRMQReviewerSource_counted_producer_may_path
    (shape : Cartesian.CartesianShape) (source : ReviewerSource)
    (_hcounted : source.Counted) : source.HasProducerMayPath shape := by
  rcases selectEntryTableWithStore_mayRead
      (GenericSelect.sparseExceptionSelectData shape.bpCode
        false).superTable
      concreteBPNativeSelectCloseTraceSegmentLayout.superTable
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) with
    ⟨⟨word1, h1⟩, ⟨word2, h2⟩, ⟨word3, h3⟩, ⟨word4, h4⟩⟩
  rcases selectEntryTableWithStore_mayRead
      (GenericSelect.sparseExceptionSelectData shape.bpCode
        false).localTable
      concreteBPNativeSelectCloseTraceSegmentLayout.localTable
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) with
    ⟨⟨word5, h5⟩, ⟨word6, h6⟩, ⟨word7, h7⟩, ⟨word8, h8⟩⟩
  rcases chunkedRankTraceWithStore_mayRead
      (GenericSelect.sparseExceptionSelectData shape.bpCode
        false).longFlagRankData
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      concreteBPNativeSelectCloseTraceSegmentLayout.longFlagRankBase
      (concreteBPNativeSelectCloseTraceSegmentLayout.longFlagRankBase + 1)
      (concreteBPNativeSelectCloseTraceSegmentLayout.longFlagRankBase + 2)
      concreteBPNativeFringeChunkTraceSegment
      (SuccinctClose.bpFringeChunkBits shape.bpCode.length) true with
    ⟨⟨index9, word9, h9⟩, ⟨index10, word10, h10⟩,
      ⟨index11, word11, h11⟩⟩
  rcases chunkedRelativeOffsetWithStore_mayRead
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      concreteBPNativeSelectCloseTraceSegmentLayout.longRelativeBase
      0 0 with ⟨word12, h12⟩
  rcases chunkedSparseDirectoryWithStore_mayRead shape with
    ⟨⟨index13, word13, h13⟩, ⟨index14, word14, h14⟩,
      ⟨index15, word15, h15⟩, index16, word16, h16⟩
  rcases chunkedRankTraceWithStore_mayRead
      (builtRelativeSplitBPCloseRankData shape)
      (concreteBPNativeChunkedRankCloseSeedReadStore shape
        concreteBPNativeRankCloseTraceSegmentBase)
      concreteBPNativeRankCloseTraceSegmentBase
      (concreteBPNativeRankCloseTraceSegmentBase + 1)
      (concreteBPNativeRankCloseTraceSegmentBase + 2)
      (concreteBPNativeRankCloseTraceSegmentBase + 4)
      (SuccinctClose.bpFringeChunkBits shape.bpCode.length) false with
    ⟨⟨index17, word17, h17⟩, ⟨index18, word18, h18⟩,
      ⟨index19, word19, h19⟩⟩
  rcases chunkedDenseTwoWordSelectWithStore_mayRead
      (GenericSelect.sparseExceptionSelectData shape.bpCode false).bitWords
      concreteBPNativeSelectCloseTraceSegmentLayout.bitWordBase
      concreteBPNativeFringeChunkTraceSegment
      concreteBPNativeSelectChunkTraceSegment
      (SuccinctClose.bpFringeChunkBits shape.bpCode.length) false 0 0 0
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) with ⟨word0, h0⟩
  rcases reviewerCanonicalInterior_mayRead shape with
    ⟨index20, word20, h20⟩
  cases source with
  | sharedBPCode =>
      exact ⟨.selectClose, 0, _, word0, rfl,
        ReviewerProducerReadPath.selectDense h0⟩
  | finalRankSuperFalse =>
      exact ⟨.rankClose, 17, index17, word17, rfl,
        ReviewerProducerReadPath.finalRank h17⟩
  | finalRankBlockFalse =>
      exact ⟨.rankClose, 18, index18, word18, rfl,
        ReviewerProducerReadPath.finalRank h18⟩
  | selectSuperBaseOccurrence =>
      exact ⟨.selectClose, 1, 0, word1, rfl,
        ReviewerProducerReadPath.selectSuper h1⟩
  | selectSuperBaseWordIndex =>
      exact ⟨.selectClose, 2, 0, word2, rfl,
        ReviewerProducerReadPath.selectSuper h2⟩
  | selectSuperRankBefore =>
      exact ⟨.selectClose, 3, 0, word3, rfl,
        ReviewerProducerReadPath.selectSuper h3⟩
  | selectSuperFirstOffset =>
      exact ⟨.selectClose, 4, 0, word4, rfl,
        ReviewerProducerReadPath.selectSuper h4⟩
  | selectLocalBaseOccurrence =>
      exact ⟨.selectClose, 5, 0, word5, rfl,
        ReviewerProducerReadPath.selectLocal h5⟩
  | selectLocalBaseWordIndex =>
      exact ⟨.selectClose, 6, 0, word6, rfl,
        ReviewerProducerReadPath.selectLocal h6⟩
  | selectLocalRankBefore =>
      exact ⟨.selectClose, 7, 0, word7, rfl,
        ReviewerProducerReadPath.selectLocal h7⟩
  | selectLocalFirstOffset =>
      exact ⟨.selectClose, 8, 0, word8, rfl,
        ReviewerProducerReadPath.selectLocal h8⟩
  | selectLongFlagRankSuperTrue =>
      exact ⟨.selectClose, 9, index9, word9, rfl,
        ReviewerProducerReadPath.selectLongRank h9⟩
  | selectLongFlagRankBlockTrue =>
      exact ⟨.selectClose, 10, index10, word10, rfl,
        ReviewerProducerReadPath.selectLongRank h10⟩
  | selectLongFlagBits =>
      exact ⟨.selectClose, 11, index11, word11, rfl,
        ReviewerProducerReadPath.selectLongRank h11⟩
  | selectLongRelative =>
      exact ⟨.selectClose, 12, 0, word12, rfl,
        ReviewerProducerReadPath.selectLongRelative h12⟩
  | selectSparseRankSuperTrue =>
      exact ⟨.selectClose, 13, index13, word13, rfl,
        ReviewerProducerReadPath.selectSparse h13⟩
  | selectSparseRankBlockTrue =>
      exact ⟨.selectClose, 14, index14, word14, rfl,
        ReviewerProducerReadPath.selectSparse h14⟩
  | selectSparseFlagBits =>
      exact ⟨.selectClose, 15, index15, word15, rfl,
        ReviewerProducerReadPath.selectSparse h15⟩
  | selectSparseRelative =>
      exact ⟨.selectClose, 16, index16, word16, rfl,
        ReviewerProducerReadPath.selectSparse h16⟩
  | canonicalClose =>
      exact ⟨.canonicalClose, 20, index20, word20, rfl,
        ReviewerProducerReadPath.lcaInterior h20⟩
  | fringeChunkTable =>
      rcases
        SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedLeftFringeCandidateSeededTraceResultAtSegment_fringe_mayRead
          shape concreteBPNativeFringeChunkTraceSegment 1 0 0 with
        ⟨index21, word21, h21⟩
      exact ⟨.canonicalClose, 21, index21, word21, rfl,
        ReviewerProducerReadPath.lcaFringeLeft h21⟩
  | selectChunkTable =>
      rcases concreteBPNativeChunkedInWordSelect_selectTable_mayRead shape
        with ⟨index22, word22, h22⟩
      exact ⟨.selectClose, 22, index22, word22, rfl,
        ReviewerProducerReadPath.selectDenseInWord h22⟩

/-- Producer/source connection for a named shared-BP consumer.  Both the BP
source and the consumer leaf are witnessed by one read event at one call site. -/
def ReviewerSharedBPConsumer.ProducerConnected
    (shape : Cartesian.CartesianShape)
    (consumer : ReviewerSharedBPConsumer) : Prop :=
  ∃ index word?,
    concreteBPNativeSuccinctRMQReviewerSegmentSource? consumer.segment =
      some .sharedBPCode ∧
    ReviewerProducerReadPath shape consumer.leaf consumer.segment index word?

theorem concreteBPNativeSuccinctRMQReviewerSharedBPConsumer_all_producer_connected
    (shape : Cartesian.CartesianShape) (consumer : ReviewerSharedBPConsumer) :
    consumer.ProducerConnected shape := by
  cases consumer with
  | selectClose =>
      rcases chunkedDenseTwoWordSelectWithStore_mayRead
          (GenericSelect.sparseExceptionSelectData shape.bpCode
            false).bitWords
          concreteBPNativeSelectCloseTraceSegmentLayout.bitWordBase
          concreteBPNativeFringeChunkTraceSegment
          concreteBPNativeSelectChunkTraceSegment
          (SuccinctClose.bpFringeChunkBits shape.bpCode.length) false 0 0 0
          (concreteBPNativeSuccinctRMQGlobalReadStore shape) with
        ⟨word?, hmem⟩
      exact ⟨_, word?, rfl, ReviewerProducerReadPath.selectDense hmem⟩
  | rankClose =>
      rcases chunkedRankTraceWithStore_mayRead
          (builtRelativeSplitBPCloseRankData shape)
          (concreteBPNativeChunkedRankCloseSeedReadStore shape
            concreteBPNativeRankCloseTraceSegmentBase)
          concreteBPNativeRankCloseTraceSegmentBase
          (concreteBPNativeRankCloseTraceSegmentBase + 1)
          (concreteBPNativeRankCloseTraceSegmentBase + 2)
          (concreteBPNativeRankCloseTraceSegmentBase + 4)
          (SuccinctClose.bpFringeChunkBits shape.bpCode.length) false with
        ⟨_, _, ⟨index19, word?, hmem⟩⟩
      exact ⟨index19, word?, rfl, ReviewerProducerReadPath.finalRank hmem⟩
  | canonicalClose =>
      rcases reviewerLocalBPWindow_mayRead shape with
        ⟨index, word?, hmem⟩
      exact ⟨index, word?, rfl, ReviewerProducerReadPath.lcaBP hmem⟩

/-- Reviewer-live segment coverage for every read event, successful or failed. -/
private def concreteBPNativeSuccinctRMQReviewerReadSegmentLive :
    WordRAM.TraceEvent -> Prop
  | WordRAM.TraceEvent.readWord segment _ _ => segment < 23
  | _ => True

private def concreteBPNativeSuccinctRMQReviewerMappedReadSegmentLive
    (segmentMap : Nat -> Nat) : WordRAM.TraceEvent -> Prop
  | WordRAM.TraceEvent.readWord segment _ _ => segmentMap segment < 23
  | _ => True

private theorem relabelReadSegmentsWith_reviewerReadSegmentLive
    (segmentMap : Nat -> Nat) (result : WordRAM.TraceResult alpha)
    (hread :
      forall {segment index : Nat} {word? : Option WordRAM.Word},
        WordRAM.TraceEvent.readWord segment index word? ∈ result.trace ->
          segmentMap segment < 23) :
    forall event,
      event ∈
          (WordRAM.TraceResult.relabelReadSegmentsWith
            segmentMap result).trace ->
        concreteBPNativeSuccinctRMQReviewerReadSegmentLive event := by
  intro event hmem
  simp only [WordRAM.TraceResult.relabelReadSegmentsWith_trace,
    List.mem_map] at hmem
  rcases hmem with ⟨source, hsource, rfl⟩
  cases source with
  | readWord segment index word? =>
      exact hread hsource
  | wordRank => trivial
  | wordSelect => trivial
  | syntheticCostOnlyPrimitive => trivial

private theorem wordProgram_relabel_reviewerReadSegmentLive
    (program : WordRAM.Program ty) (store : WordRAM.Store)
    (segmentMap : Nat -> Nat)
    (haddress :
      forall {segment index : Nat},
        (segment, index) ∈ program.readAddresses ->
          segmentMap segment < 23) :
    forall event,
      event ∈
          (WordRAM.TraceResult.relabelReadSegmentsWith segmentMap
            (WordRAM.TraceResult.ofResult (program.eval store))).trace ->
        concreteBPNativeSuccinctRMQReviewerReadSegmentLive event := by
  apply relabelReadSegmentsWith_reviewerReadSegmentLive
  intro segment index word? hmem
  exact haddress
    (WordRAM.Program.eval_readWord_address_mem program store hmem)

private theorem wordProgram_reviewerMappedReadSegmentLive
    (program : WordRAM.Program ty) (store : WordRAM.Store)
    (segmentMap : Nat -> Nat)
    (haddress :
      forall {segment index : Nat},
        (segment, index) ∈ program.readAddresses ->
          segmentMap segment < 23) :
    forall event,
      event ∈ (WordRAM.TraceResult.ofResult (program.eval store)).trace ->
        concreteBPNativeSuccinctRMQReviewerMappedReadSegmentLive
          segmentMap event := by
  intro event hmem
  cases event with
  | readWord segment index word? =>
      exact haddress
        (WordRAM.Program.eval_readWord_address_mem program store hmem)
  | wordRank => trivial
  | wordSelect => trivial
  | syntheticCostOnlyPrimitive => trivial

private theorem natProgram_relabel_reviewerReadSegmentLive
    (program : WordRAM.Register.NatProgram)
    (store : WordRAM.Store) (regs : WordRAM.Register.RegFile)
    (segmentMap : Nat -> Nat)
    (haddress :
      forall {segment index : Nat},
        (segment, index) ∈ program.readAddresses regs ->
          segmentMap segment < 23) :
    forall event,
      event ∈
          (WordRAM.TraceResult.relabelReadSegmentsWith segmentMap
            (WordRAM.TraceResult.ofResult
              (program.eval store regs))).trace ->
        concreteBPNativeSuccinctRMQReviewerReadSegmentLive event := by
  apply relabelReadSegmentsWith_reviewerReadSegmentLive
  intro segment index word? hmem
  exact haddress
    (WordRAM.Register.NatProgram.eval_readWord_address_mem
      program store regs hmem)

private theorem fixedWidthNatTable_relabel_reviewerReadSegmentLive
    {entries : List Nat} {width : Nat}
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (segmentBase deadSegment slot : Nat)
    (hbase : segmentBase < 23) :
    forall event,
      event ∈
          (WordRAM.TraceResult.relabelReadSegmentsWith
            (WordRAM.singletonSegmentMap segmentBase deadSegment)
            (WordRAM.TraceResult.ofResult
              ((table.readProgram slot).eval table.wordRAMStore))).trace ->
        concreteBPNativeSuccinctRMQReviewerReadSegmentLive event := by
  apply wordProgram_relabel_reviewerReadSegmentLive
  intro segment index hmem
  simp [SuccinctSpace.FixedWidthNatTable.readProgram,
    SuccinctSpace.PayloadWordStore.readProgram,
    WordRAM.Program.readAddresses] at hmem
  rcases hmem with ⟨rfl, _⟩
  simpa [WordRAM.singletonSegmentMap] using hbase

private theorem rankTraceResult_relabel_reviewerReadSegmentLive
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      SuccinctRank.TwoLevelPayloadLiveStoredWordRankData
        bits superOverhead blockOverhead queryCost)
    (target : Bool) (segmentBase deadSegment pos : Nat)
    (hbase : segmentBase + 2 < 23) :
    forall event,
      event ∈
          (WordRAM.TraceResult.relabelReadSegmentsWith
            (WordRAM.tripleSegmentMap segmentBase deadSegment)
            (data.rankTraceResult target pos)).trace ->
        concreteBPNativeSuccinctRMQReviewerReadSegmentLive event := by
  unfold SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.rankTraceResult
  apply natProgram_relabel_reviewerReadSegmentLive
  intro segment index hmem
  simp [SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.rankRegisterProgram,
    WordRAM.Register.NatProgram.readAddresses] at hmem
  rcases hmem with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;>
    simp [WordRAM.tripleSegmentMap,
      WordRAM.TraceEvent.tripleSegmentMap] <;> omega

private theorem denseTwoWordSelectTraceResultRelabeled_reviewerReadSegmentLive
    (bitWordSegmentBase deadSegment : Nat)
    (target : Bool) {bits : List Bool} {wordSize : Nat}
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (basePosition baseOccurrence q : Nat)
    (hbase : bitWordSegmentBase < 23) :
    forall event,
      event ∈
          (GenericSelect.denseTwoWordSelectTraceResultRelabeled
            bitWordSegmentBase deadSegment target bitWords
            basePosition baseOccurrence q).trace ->
        concreteBPNativeSuccinctRMQReviewerReadSegmentLive event := by
  unfold GenericSelect.denseTwoWordSelectTraceResultRelabeled
  apply relabelReadSegmentsWith_reviewerReadSegmentLive
  have hlocal :
      forall event,
        event ∈
            (GenericSelect.denseTwoWordSelectTraceResult
              target bitWords basePosition baseOccurrence q).trace ->
          concreteBPNativeSuccinctRMQReviewerMappedReadSegmentLive
            (WordRAM.singletonSegmentMap bitWordSegmentBase deadSegment)
            event := by
    unfold GenericSelect.denseTwoWordSelectTraceResult
    apply WordRAM.TraceResult.bind_trace_forall
    · apply wordProgram_reviewerMappedReadSegmentLive
      intro segment index hmem
      simp [SuccinctSpace.PayloadWordStore.readProgram,
        WordRAM.Program.readAddresses] at hmem
      rcases hmem with ⟨rfl, _⟩
      simpa [WordRAM.singletonSegmentMap] using hbase
    · cases hfirst :
        (WordRAM.TraceResult.ofResult
          ((bitWords.store.readProgram (basePosition / wordSize)).eval
            bitWords.store.wordRAMStore)).value with
      | none =>
          exact WordRAM.TraceResult.pure_trace_forall _ none
      | some firstWord =>
          apply WordRAM.TraceResult.bind_trace_forall
          · intro event hmem
            simp [SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult,
              WordRAM.Program.eval] at hmem
            subst event
            trivial
          · apply WordRAM.TraceResult.bind_trace_forall
            · intro event hmem
              simp [SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult,
                WordRAM.Program.eval] at hmem
              subst event
              trivial
            · by_cases hlt :
                  q - baseOccurrence <
                    (SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult
                      target firstWord firstWord.length).value -
                      (SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult
                        target firstWord
                        (basePosition - basePosition / wordSize * wordSize)).value
              · intro event hmem
                simp [hlt] at hmem
                exact
                  WordRAM.TraceResult.map_trace_forall
                    (concreteBPNativeSuccinctRMQReviewerMappedReadSegmentLive
                      (WordRAM.singletonSegmentMap
                        bitWordSegmentBase deadSegment))
                    (fun local? =>
                      local?.map fun offset =>
                        basePosition / wordSize * wordSize + offset)
                    (GenericSelect.wordSelectTraceResult target firstWord
                      ((SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult
                        target firstWord
                        (basePosition - basePosition / wordSize * wordSize)).value +
                        (q - baseOccurrence)))
                    (by
                      intro source hsource
                      simp [GenericSelect.wordSelectTraceResult,
                        WordRAM.Program.eval] at hsource
                      subst source
                      trivial)
                    event hmem
              · intro event hmem
                simp [hlt] at hmem
                rcases hmem with hmem | hmem
                · subst event
                  simpa [concreteBPNativeSuccinctRMQReviewerMappedReadSegmentLive,
                    WordRAM.singletonSegmentMap] using hbase
                · cases hsecond :
                      bitWords.store.words[basePosition / wordSize + 1]? with
                  | none => simp [hsecond] at hmem
                  | some secondWord =>
                      simp [hsecond] at hmem
                      exact
                        WordRAM.TraceResult.map_trace_forall
                          (concreteBPNativeSuccinctRMQReviewerMappedReadSegmentLive
                            (WordRAM.singletonSegmentMap
                              bitWordSegmentBase deadSegment))
                          (fun local? => local?.map fun offset =>
                            (basePosition / wordSize + 1) * wordSize + offset)
                          (GenericSelect.wordSelectTraceResult target secondWord
                            (q - baseOccurrence -
                              ((SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult
                                target firstWord firstWord.length).value -
                                (SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult
                                  target firstWord
                                  (basePosition -
                                    basePosition / wordSize * wordSize)).value)))
                          (by
                            intro source hsource
                            simp [GenericSelect.wordSelectTraceResult,
                              WordRAM.Program.eval] at hsource
                            subst source
                            trivial)
                          event hmem
  intro segment index word? hmem
  exact hlocal (WordRAM.TraceEvent.readWord segment index word?) hmem

private theorem ofProgramWithStore_natTableRead_reviewerReadSegmentLive
    {entries : List Nat} {width : Nat}
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (base dead : Nat) (store : WordRAM.ReadStore) (i : Nat)
    (hbase : base < 23) :
    forall event,
      List.Mem event
          (WordRAM.TraceResult.ofProgramWithStore
            (WordRAM.singletonSegmentMap base dead) store
            (table.readProgram i)).trace ->
        concreteBPNativeSuccinctRMQReviewerReadSegmentLive event := by
  intro event hmem
  simp only [WordRAM.TraceResult.ofProgramWithStore,
    WordRAM.TraceResult.relabelReadSegmentsWith_trace,
    WordRAM.TraceResult.ofResult_trace] at hmem
  rcases List.mem_map.mp hmem with ⟨inner, hinner, rfl⟩
  simp only [SuccinctSpace.FixedWidthNatTable.readProgram,
    SuccinctSpace.PayloadWordStore.readProgram,
    WordRAM.Program.evalR, List.mem_singleton] at hinner
  subst inner
  simpa [WordRAM.TraceEvent.relabelReadSegmentWith,
    WordRAM.singletonSegmentMap,
    concreteBPNativeSuccinctRMQReviewerReadSegmentLive] using hbase

private theorem selectEntryTableWithStore_reviewerReadSegmentLive
    {entries : List GenericSelect.SparseDenseSelectDenseLocalEntry}
    {fieldWidth : Nat}
    (table :
      GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable
        entries fieldWidth)
    (layout : GenericSelect.SparseDenseEntryTableTraceSegmentBases)
    (store : WordRAM.ReadStore) (i : Nat)
    (hbaseOccurrence : layout.baseOccurrence < 23)
    (hbaseWordIndex : layout.baseWordIndex < 23)
    (hrankBefore : layout.rankBefore < 23)
    (hfirstOffset : layout.firstOffset < 23) :
    forall event,
      List.Mem event
          (table.readTraceResultRelabeledWithStore layout store i).trace ->
        concreteBPNativeSuccinctRMQReviewerReadSegmentLive event := by
  unfold
    GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable.readTraceResultRelabeledWithStore
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      ofProgramWithStore_natTableRead_reviewerReadSegmentLive
        table.baseOccurrenceTable _ _ store i hbaseOccurrence
  · intro baseOccurrence?
    apply WordRAM.TraceResult.bind_trace_forall
    · exact
        ofProgramWithStore_natTableRead_reviewerReadSegmentLive
          table.baseWordIndexTable _ _ store i hbaseWordIndex
    · intro baseWordIndex?
      apply WordRAM.TraceResult.bind_trace_forall
      · exact
          ofProgramWithStore_natTableRead_reviewerReadSegmentLive
            table.rankBeforeTable _ _ store i hrankBefore
      · intro rankBefore?
        apply WordRAM.TraceResult.map_trace_forall
        exact
          ofProgramWithStore_natTableRead_reviewerReadSegmentLive
            table.firstOffsetTable _ _ store i hfirstOffset

private theorem concreteBPNativeSelectCloseGlobalWordTraceResult_reviewerReadSegmentLive
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    forall event,
      event ∈
          (concreteBPNativeSelectCloseGlobalWordTraceResult shape idx).trace ->
        concreteBPNativeSuccinctRMQReviewerReadSegmentLive event := by
  apply
    (GenericSelect.sparseExceptionSelectData
        shape.bpCode false).bpChunkedSelectTraceResultWithStore_trace_forall
  · intro slot
    exact
      selectEntryTableWithStore_reviewerReadSegmentLive
        (GenericSelect.sparseExceptionSelectData
          shape.bpCode false).superTable
        concreteBPNativeSelectCloseTraceSegmentLayout.superTable
        (concreteBPNativeSuccinctRMQGlobalReadStore shape) slot
        (by decide) (by decide) (by decide) (by decide)
  · intro slot
    apply
      (GenericSelect.sparseExceptionSelectData
          shape.bpCode
            false).longFlagRankData.bpChunkedRankTraceResultWithStore_trace_forall
    · intro address
      simp [concreteBPNativeSelectCloseTraceSegmentLayout,
        concreteBPNativeSuccinctRMQReviewerReadSegmentLive]
    · intro address
      simp [concreteBPNativeSelectCloseTraceSegmentLayout,
        concreteBPNativeSuccinctRMQReviewerReadSegmentLive]
    · intro address
      simp [concreteBPNativeSelectCloseTraceSegmentLayout,
        concreteBPNativeSuccinctRMQReviewerReadSegmentLive]
    · intro address _hlt
      simp [concreteBPNativeFringeChunkTraceSegment,
        concreteBPNativeSuccinctRMQReviewerReadSegmentLive]
  · intro base slot
    apply GenericSelect.bpRelativeOffsetReadTraceResultWithStore_trace_forall
    intro address
    simp [concreteBPNativeSelectCloseTraceSegmentLayout,
      concreteBPNativeSuccinctRMQReviewerReadSegmentLive]
  · intro slot
    exact
      selectEntryTableWithStore_reviewerReadSegmentLive
        (GenericSelect.sparseExceptionSelectData
          shape.bpCode false).localTable
        concreteBPNativeSelectCloseTraceSegmentLayout.localTable
        (concreteBPNativeSuccinctRMQGlobalReadStore shape) slot
        (by decide) (by decide) (by decide) (by decide)
  · intro base localSlot localOccurrence
    apply
      (GenericSelect.sparseExceptionSelectData
          shape.bpCode
            false).sparseDirectory.bpChunkedReadTraceResultWithStore_trace_forall
    · apply
        (GenericSelect.sparseExceptionSelectData
            shape.bpCode
              false).sparseDirectory.rankData.bpChunkedRankTraceResultWithStore_trace_forall
      · intro address
        simp [concreteBPNativeSelectCloseTraceSegmentLayout,
          concreteBPNativeSuccinctRMQReviewerReadSegmentLive]
      · intro address
        simp [concreteBPNativeSelectCloseTraceSegmentLayout,
          concreteBPNativeSuccinctRMQReviewerReadSegmentLive]
      · intro address
        simp [concreteBPNativeSelectCloseTraceSegmentLayout,
          concreteBPNativeSuccinctRMQReviewerReadSegmentLive]
      · intro address _hlt
        simp [concreteBPNativeFringeChunkTraceSegment,
          concreteBPNativeSuccinctRMQReviewerReadSegmentLive]
    · intro slot
      apply
        GenericSelect.bpRelativeOffsetReadTraceResultWithStore_trace_forall
      intro address
      simp [concreteBPNativeSelectCloseTraceSegmentLayout,
        concreteBPNativeSuccinctRMQReviewerReadSegmentLive]
  · intro basePosition baseOccurrence q
    apply
      GenericSelect.bpChunkedDenseTwoWordSelectTraceResultWithStore_trace_forall
    · intro address
      simp [concreteBPNativeSelectCloseTraceSegmentLayout,
        concreteBPNativeSuccinctRMQReviewerReadSegmentLive]
    · intro address _hlt
      simp [concreteBPNativeFringeChunkTraceSegment,
        concreteBPNativeSuccinctRMQReviewerReadSegmentLive]
    · intro address
      simp [concreteBPNativeSelectChunkTraceSegment,
        concreteBPNativeSuccinctRMQReviewerReadSegmentLive]

private theorem concreteBPNativeRankCloseGlobalWordTraceResult_reviewerReadSegmentLive
    (shape : Cartesian.CartesianShape) (pos : Nat) :
    forall event,
      event ∈
          (concreteBPNativeRankCloseWordTraceResultAtSegment
            shape concreteBPNativeRankCloseTraceSegmentBase pos).trace ->
        concreteBPNativeSuccinctRMQReviewerReadSegmentLive event := by
  apply
    (builtRelativeSplitBPCloseRankData
        shape).bpChunkedRankTraceResultWithStore_trace_forall
  · intro address
    simp [concreteBPNativeRankCloseTraceSegmentBase,
      concreteBPNativeSuccinctRMQReviewerReadSegmentLive]
  · intro address
    simp [concreteBPNativeRankCloseTraceSegmentBase,
      concreteBPNativeSuccinctRMQReviewerReadSegmentLive]
  · intro address
    simp [concreteBPNativeRankCloseTraceSegmentBase,
      concreteBPNativeSuccinctRMQReviewerReadSegmentLive]
  · intro address _hlt
    simp [concreteBPNativeRankCloseTraceSegmentBase,
      concreteBPNativeSuccinctRMQReviewerReadSegmentLive]

private theorem concreteBPNativeLocalBPWindowBitsTraceResult_reviewerReadSegmentLive
    (shape : Cartesian.CartesianShape) (blockSize close : Nat) :
    forall event,
      event ∈
          (SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPWindowBitsTraceResult
            shape blockSize close).trace ->
        concreteBPNativeSuccinctRMQReviewerReadSegmentLive event := by
  intro event hmem
  unfold SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPWindowBitsTraceResult
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPBlockWordsTraceResult
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpCodeWordReadTraceResult
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpCodeReadWordTraceEvent
    at hmem
  simp [WordRAM.TraceResult.bind, WordRAM.TraceResult.map,
    WordRAM.TraceResult.pure] at hmem
  rcases hmem with hmem | hmem | hmem | hmem <;>
    subst event <;>
      simp [concreteBPNativeSuccinctRMQReviewerReadSegmentLive]

private theorem concreteBPNativeInteriorGlobalWordTraceResultAllSizeStructural_reviewerReadSegmentLive
    (shape : Cartesian.CartesianShape) (startBlock count : Nat) :
    forall event,
      event ∈
          (SuccinctClose.ConcreteCompactBPCloseLCADirectory.concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructural
            shape concreteBPNativeInteriorTraceSegments
            startBlock count).trace ->
        concreteBPNativeSuccinctRMQReviewerReadSegmentLive event := by
  intro event hmem
  unfold SuccinctClose.ConcreteCompactBPCloseLCADirectory.concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructural
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.canonicalRelativeRmmInteriorRangeMinTraceResultAtSegment
    SuccinctClose.flatStoreExecutionTraceResultAtSegment at hmem
  simp only [List.mem_map] at hmem
  rcases hmem with ⟨read, _hread, rfl⟩
  simp [concreteBPNativeSuccinctRMQReviewerReadSegmentLive,
    concreteBPNativeInteriorTraceSegments]

private theorem concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural_reviewerReadSegmentLive
    (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) :
    forall event,
      event ∈
          (concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
            shape leftClose rightClose).trace ->
        concreteBPNativeSuccinctRMQReviewerReadSegmentLive event := by
  unfold concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
  apply
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.lcaCloseTraceResultWithRankSeedAllSizeStructural_trace_forall
      shape
      (concreteBPNativeRankCloseWordTraceResultAtSegment
        shape concreteBPNativeRankCloseTraceSegmentBase)
      concreteBPNativeInteriorTraceSegments
      concreteBPNativeFringeChunkTraceSegment
      concreteBPNativeFiniteSmallSameBlockCloseTraceSegment
      leftClose rightClose
      concreteBPNativeSuccinctRMQReviewerReadSegmentLive
  · intro pos
    exact
      concreteBPNativeRankCloseGlobalWordTraceResult_reviewerReadSegmentLive
        shape pos
  · intro blockSize close
    exact
      concreteBPNativeLocalBPWindowBitsTraceResult_reviewerReadSegmentLive
        shape blockSize close
  · intro blockSize close seed
    exact
      SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedLeftFringeCandidateSeededTraceResultAtSegment_trace_forall
        shape concreteBPNativeFringeChunkTraceSegment blockSize close seed
        concreteBPNativeSuccinctRMQReviewerReadSegmentLive
        (concreteBPNativeLocalBPWindowBitsTraceResult_reviewerReadSegmentLive
          shape blockSize close)
        (fun address _hlt => by
          simp [concreteBPNativeFringeChunkTraceSegment,
            concreteBPNativeSuccinctRMQReviewerReadSegmentLive])
  · intro blockSize close seed
    exact
      SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedRightFringeCandidateSeededTraceResultAtSegment_trace_forall
        shape concreteBPNativeFringeChunkTraceSegment blockSize close seed
        concreteBPNativeSuccinctRMQReviewerReadSegmentLive
        (concreteBPNativeLocalBPWindowBitsTraceResult_reviewerReadSegmentLive
          shape blockSize close)
        (fun address _hlt => by
          simp [concreteBPNativeFringeChunkTraceSegment,
            concreteBPNativeSuccinctRMQReviewerReadSegmentLive])
  · intro startBlock count
    exact
      concreteBPNativeInteriorGlobalWordTraceResultAllSizeStructural_reviewerReadSegmentLive
        shape startBlock count

private theorem WholeQueryInstr.evalGlobalWordTrace_reviewerReadSegmentLive
    (shape : Cartesian.CartesianShape)
    (left right : Nat) (instr : WholeQueryInstr)
    (state : WholeQueryState) :
    forall event,
      event ∈ (instr.evalGlobalWordTrace shape left right state).trace ->
        concreteBPNativeSuccinctRMQReviewerReadSegmentLive event := by
  cases instr with
  | selectClose dst idx =>
      simp [WholeQueryInstr.evalGlobalWordTrace]
      exact
        concreteBPNativeSelectCloseGlobalWordTraceResult_reviewerReadSegmentLive
          shape (idx.eval left right state)
  | lcaClose dst leftReg rightReg =>
      cases hleft : state.opt leftReg with
      | none =>
          cases hright : state.opt rightReg <;>
            simp [WholeQueryInstr.evalGlobalWordTrace, hleft, hright] <;>
            intro event hmem <;> cases hmem
      | some leftClose =>
          cases hright : state.opt rightReg with
          | none =>
              simp [WholeQueryInstr.evalGlobalWordTrace, hleft, hright]
          | some rightClose =>
              simp [WholeQueryInstr.evalGlobalWordTrace, hleft, hright]
              exact
                concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural_reviewerReadSegmentLive
                  shape leftClose rightClose
  | rankCloseIfSome dst guard pos =>
      cases hguard : state.opt guard with
      | none =>
          simp [WholeQueryInstr.evalGlobalWordTrace, hguard]
      | some _ =>
          simp [WholeQueryInstr.evalGlobalWordTrace, hguard]
          exact
            concreteBPNativeRankCloseGlobalWordTraceResult_reviewerReadSegmentLive
              shape (pos.eval left right state)
  | outputPredIfSome dst guard src =>
      cases hguard : state.opt guard <;>
        simp [WholeQueryInstr.evalGlobalWordTrace, hguard] <;>
        intro event hmem <;> cases hmem

private theorem WholeQueryProgram.evalGlobalWordTrace_reviewerReadSegmentLive
    (shape : Cartesian.CartesianShape)
    (left right : Nat)
    (program : WholeQueryProgram) (state : WholeQueryState) :
    forall event,
      event ∈
          (WholeQueryProgram.evalGlobalWordTrace
            shape left right program state).trace ->
        concreteBPNativeSuccinctRMQReviewerReadSegmentLive event := by
  induction program generalizing state with
  | nil =>
      simp [WholeQueryProgram.evalGlobalWordTrace]
  | cons instr rest ih =>
      unfold WholeQueryProgram.evalGlobalWordTrace
      apply WordRAM.TraceResult.bind_trace_forall
      · exact
          WholeQueryInstr.evalGlobalWordTrace_reviewerReadSegmentLive
            shape left right instr state
      · exact ih
          (instr.evalGlobalWordTrace shape left right state).value

/-- Every logical payload read emitted by the canonical whole-query evaluator,
including a failed read, has a logical segment number from `0` through `20`. -/
theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_read_segment_lt
    (shape : Cartesian.CartesianShape)
    (left right : Nat) :
    forall {segment index : Nat} {word? : Option WordRAM.Word},
      WordRAM.TraceEvent.readWord segment index word? ∈
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
            shape left right).trace ->
        segment < 23 := by
  intro segment index word? hmem
  have hlive :
      concreteBPNativeSuccinctRMQReviewerReadSegmentLive
        (WordRAM.TraceEvent.readWord segment index word?) := by
    unfold concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult at hmem
    exact
      WordRAM.TraceResult.map_trace_forall
        concreteBPNativeSuccinctRMQReviewerReadSegmentLive
        WholeQueryState.output?
        (WholeQueryProgram.evalGlobalWordTrace shape left right
          concreteBPNativeSuccinctRMQWholeQueryProgram WholeQueryState.empty)
        (WholeQueryProgram.evalGlobalWordTrace_reviewerReadSegmentLive
          shape left right concreteBPNativeSuccinctRMQWholeQueryProgram
          WholeQueryState.empty)
        (WordRAM.TraceEvent.readWord segment index word?) hmem
  exact hlive

/-- One segment/leaf claim in the common closed-valid-execution producer
domain. -/
structure ReviewerProducerClaim where
  segment : Nat
  leaf : ReviewerReadLeaf

namespace ReviewerProducerClaim

/--
The common operational producer/reachability predicate used by both canonical
sources and counterfactual mutations.  The witness is an indexed occurrence in
the closed whole-query execution of an ordinary valid `List Int` query, tied
to the exact invocation and the same component-local position.  The explicit
`word?` parameter lets positive source coverage demand a successful `some`
read while the fresh mutation rules out both successful and failed reads.
-/
def HasClosedValidOccurrence
    (claim : ReviewerProducerClaim) (word? : Option WordRAM.Word) : Prop :=
  ∃ xs : List Int,
  ∃ left right globalPos index : Nat,
    ValidRange xs left right ∧
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
      (Cartesian.shape xs) left right).trace[globalPos]? =
        some (.readWord claim.segment index word?) ∧
    ∃ instrPos : Nat,
    ∃ instr : WholeQueryInstr,
    ∃ preState : WholeQueryState,
    ∃ localPos : Nat,
    ∃ invocation : ReviewerReadInvocation,
      WholeQueryProgram.ProducesEventAt
        (Cartesian.shape xs) left right
        (.readWord claim.segment index word?)
        concreteBPNativeSuccinctRMQWholeQueryProgram WholeQueryState.empty
        globalPos instrPos instr preState localPos ∧
      instr.InvokesReviewerRead left right preState invocation ∧
      invocation.leaf = claim.leaf ∧
      (invocation.componentTrace (Cartesian.shape xs))[localPos]? =
        some (.readWord claim.segment index word?)

/-- Positive producer predicate `P` on a segment/leaf claim: some valid closed
whole-query execution successfully reads the claim. -/
def HasSuccessfulClosedValidOccurrence
    (claim : ReviewerProducerClaim) : Prop :=
  ∃ word : WordRAM.Word, claim.HasClosedValidOccurrence (some word)

/-- Mutation predicate `Q` on a segment/leaf claim: some valid closed
whole-query execution emits the claim, whether the read succeeds or fails. -/
def HasOperationalProducer (claim : ReviewerProducerClaim) : Prop :=
  ∃ word? : Option WordRAM.Word, claim.HasClosedValidOccurrence word?

/-- Checked `P → Q` bridge.  `P` and `Q` intentionally are not definitionally
equal because accepted canonical sources must exhibit a successful read while
the fresh mutation is rejected even as a failed attempted read. -/
theorem hasOperationalProducer_of_successful
    {claim : ReviewerProducerClaim}
    (hclaim : claim.HasSuccessfulClosedValidOccurrence) :
    claim.HasOperationalProducer := by
  rcases hclaim with ⟨word, hword⟩
  exact ⟨some word, hword⟩

end ReviewerProducerClaim

/-- A canonical source is operationally live only when some ordinary valid
top-level query successfully reads it through the common indexed occurrence
predicate. -/
def ReviewerSource.HasSuccessfulClosedValidOccurrence
    (source : ReviewerSource) : Prop :=
  ∃ claim : ReviewerProducerClaim,
    concreteBPNativeSuccinctRMQReviewerSegmentSource? claim.segment =
      some source ∧
    claim.HasSuccessfulClosedValidOccurrence

/-- The canonical claim for one named shared-BP consumer. -/
def ReviewerSharedBPConsumer.producerClaim
    (consumer : ReviewerSharedBPConsumer) : ReviewerProducerClaim where
  segment := consumer.segment
  leaf := consumer.leaf

/-- Shared-BP consumer reachability through the same successful valid-query
occurrence predicate. -/
def ReviewerSharedBPConsumer.HasSuccessfulClosedValidOccurrence
    (consumer : ReviewerSharedBPConsumer) : Prop :=
  consumer.producerClaim.HasSuccessfulClosedValidOccurrence

/-- A mutation candidate outside the closed source universe.  Its leaf label
may be plausible; acceptance still requires the common valid occurrence. -/
structure ReviewerUnusedSourceMutation where
  segment : Nat
  allegedLeaf : ReviewerReadLeaf

def ReviewerUnusedSourceMutation.toProducerClaim
    (candidate : ReviewerUnusedSourceMutation) : ReviewerProducerClaim where
  segment := candidate.segment
  leaf := candidate.allegedLeaf

/-- The W18 arbitrary-state instruction-local predicate, retained only as an
accurately named compatibility fact. -/
def ReviewerUnusedSourceMutation.HasArbitraryStateInstructionProducer
    (candidate : ReviewerUnusedSourceMutation) : Prop :=
  ∃ shape : Cartesian.CartesianShape,
  ∃ left right : Nat,
  ∃ instr : WholeQueryInstr,
  ∃ preState : WholeQueryState,
  ∃ index : Nat,
  ∃ word? : Option WordRAM.Word,
    instr.reviewerReadLeaf? = some candidate.allegedLeaf ∧
    WordRAM.TraceEvent.readWord candidate.segment index word? ∈
      (instr.evalGlobalWordTrace shape left right preState).trace

/-- The fresh counterfactual: segment `23` paired with the existing
canonical-close leaf label. -/
def concreteBPNativeSuccinctRMQFreshUnusedCanonicalSource :
    ReviewerUnusedSourceMutation where
  segment := 23
  allegedLeaf := .canonicalClose

/-- Compatibility W18 rejection for the stronger arbitrary-state predicate. -/
theorem concreteBPNativeSuccinctRMQFreshUnusedCanonicalSource_no_arbitraryStateInstructionProducer :
    ¬ concreteBPNativeSuccinctRMQFreshUnusedCanonicalSource.HasArbitraryStateInstructionProducer := by
  intro hproducer
  rcases hproducer with
    ⟨shape, left, right, instr, preState, index, word?, _hleaf, hmem⟩
  have hlive :=
    WholeQueryInstr.evalGlobalWordTrace_reviewerReadSegmentLive
      shape left right instr preState
      (WordRAM.TraceEvent.readWord
        concreteBPNativeSuccinctRMQFreshUnusedCanonicalSource.segment
        index word?) hmem
  simp [concreteBPNativeSuccinctRMQReviewerReadSegmentLive,
    concreteBPNativeSuccinctRMQFreshUnusedCanonicalSource] at hlive

/-- The mutation-side use of the common operational predicate. -/
def ReviewerUnusedSourceMutation.HasOperationalProducer
    (candidate : ReviewerUnusedSourceMutation) : Prop :=
  candidate.toProducerClaim.HasOperationalProducer

/-- Fresh segment `23` is rejected by the exact common valid-occurrence
predicate used for accepted canonical sources. -/
theorem concreteBPNativeSuccinctRMQFreshUnusedCanonicalSource_no_producer :
    ¬ concreteBPNativeSuccinctRMQFreshUnusedCanonicalSource.HasOperationalProducer := by
  intro hproducer
  rcases hproducer with
    ⟨word?, xs, left, right, globalPos, index, _hvalid, hget,
      _instrPos, _instr, _preState, _localPos, _invocation,
      _hproduces, _hinvokes, _hleaf, _hcomponent⟩
  have hsegment :=
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_read_segment_lt
      (Cartesian.shape xs) left right (List.mem_of_getElem? hget)
  simp [ReviewerUnusedSourceMutation.toProducerClaim,
    concreteBPNativeSuccinctRMQFreshUnusedCanonicalSource] at hsegment

/--
Relational source ownership for one produced read.  The source, logical
segment, physical region, producer instruction, actual pre-state, and exact
event membership are all facts about the same read event.  In particular this
relation permits segments `17`--`19` to be produced by either the LCA
instruction or the final rank instruction.
-/
def ReviewerSource.ProducedReadBy
    (shape : Cartesian.CartesianShape) (left right : Nat)
    (source : ReviewerSource) (instr : WholeQueryInstr)
    (preState : WholeQueryState) (segment index : Nat)
    (word? : Option WordRAM.Word) : Prop :=
  concreteBPNativeSuccinctRMQReviewerSegmentSource? segment = some source ∧
    concreteBPNativeSuccinctRMQReviewerSegmentRegion? segment =
      some source.region ∧
    WordRAM.TraceEvent.readWord segment index word? ∈
      (instr.evalGlobalWordTrace shape left right preState).trace

/-- Complete indexed receipt for one canonical read occurrence. -/
def ReviewerReadOccurrenceReceipt
    (shape : Cartesian.CartesianShape) (left right globalPos segment index : Nat)
    (word? : Option WordRAM.Word) : Prop :=
  ∃ source : ReviewerSource,
  ∃ instrPos : Nat,
  ∃ instr : WholeQueryInstr,
  ∃ preState : WholeQueryState,
  ∃ localPos : Nat,
  ∃ invocation : ReviewerReadInvocation,
    WholeQueryProgram.ProducesEventAt shape left right
      (.readWord segment index word?)
      concreteBPNativeSuccinctRMQWholeQueryProgram WholeQueryState.empty
      globalPos instrPos instr preState localPos ∧
    concreteBPNativeSuccinctRMQReviewerSegmentSource? segment =
      some source ∧
    concreteBPNativeSuccinctRMQReviewerSegmentRegion? segment =
      some source.region ∧
    instr.InvokesReviewerRead left right preState invocation ∧
    (invocation.componentTrace shape)[localPos]? =
      some (.readWord segment index word?) ∧
    ReviewerProducerReadPath shape invocation.leaf segment index word? ∧
    source.Counted

/-- Occurrence-preserving producer provenance for every emitted canonical
read, including failed reads. -/
def ConcreteBPNativeSuccinctRMQWholeQueryOccurrenceProvenance
    (shape : Cartesian.CartesianShape) (left right : Nat) : Prop :=
  ∀ {globalPos segment index : Nat} {word? : Option WordRAM.Word},
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
      shape left right).trace[globalPos]? =
        some (.readWord segment index word?) ->
      ReviewerReadOccurrenceReceipt
        shape left right globalPos segment index word?

theorem concreteBPNativeSuccinctRMQWholeQueryOccurrenceProvenance_checked
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    ConcreteBPNativeSuccinctRMQWholeQueryOccurrenceProvenance
      shape left right := by
  intro globalPos segment index word? hget
  have hprogramGet :
      (WholeQueryProgram.evalGlobalWordTrace shape left right
        concreteBPNativeSuccinctRMQWholeQueryProgram
        WholeQueryState.empty).trace[globalPos]? =
          some (.readWord segment index word?) := by
    simpa [concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult] using hget
  rcases WholeQueryProgram.evalGlobalWordTrace_getElem?_producer
      shape left right concreteBPNativeSuccinctRMQWholeQueryProgram
      WholeQueryState.empty globalPos
      (.readWord segment index word?) hprogramGet with
    ⟨instrPos, instr, preState, localPos, hproducer⟩
  rcases hproducer with
    ⟨before, after, hprogram, hinstrPos, hpreState, hglobalPos, hlocalGet⟩
  rcases WholeQueryInstr.evalGlobalWordTrace_getElem?_read_invocation
      shape left right instr preState localPos segment index word? hlocalGet with
    ⟨invocation, hinvocation, hinvocationGet⟩
  have hmem : WordRAM.TraceEvent.readWord segment index word? ∈
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).trace :=
    List.mem_of_getElem? hget
  have hsegment : segment < 23 :=
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_read_segment_lt
      shape left right hmem
  rcases (concreteBPNativeSuccinctRMQReviewerSegmentSource?_coverage segment).2
      hsegment with ⟨source, hsource⟩
  have hregion :
      concreteBPNativeSuccinctRMQReviewerSegmentRegion? segment =
        some source.region := by
    simp [concreteBPNativeSuccinctRMQReviewerSegmentRegion?, hsource]
  rcases WholeQueryInstr.evalGlobalWordTrace_read_producer_path
      shape left right instr preState (List.mem_of_getElem? hlocalGet) with
    ⟨leaf, hleaf, hpath⟩
  have hinvocationLeaf := hinvocation.reviewerReadLeaf?_eq
  have hleafEq : leaf = invocation.leaf := by
    rw [hleaf] at hinvocationLeaf
    exact Option.some.inj hinvocationLeaf
  subst leaf
  refine ⟨source, instrPos, instr, preState, localPos, invocation,
    ⟨before, after, hprogram, hinstrPos, hpreState, hglobalPos, hlocalGet⟩,
    hsource, hregion, hinvocation, hinvocationGet, hpath, ?_⟩
  exact concreteBPNativeSuccinctRMQReviewerSegmentSource_counted hsource

/-- Equal read values at different global positions remain two separately
indexed provenance obligations. -/
theorem repeated_equal_read_occurrences_have_distinct_receipts
    (shape : Cartesian.CartesianShape) (left right : Nat)
    (firstPos secondPos segment index : Nat) (word? : Option WordRAM.Word)
    (hne : firstPos ≠ secondPos)
    (hfirst :
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).trace[firstPos]? =
          some (.readWord segment index word?))
    (hsecond :
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).trace[secondPos]? =
          some (.readWord segment index word?)) :
    firstPos ≠ secondPos ∧
      ReviewerReadOccurrenceReceipt
        shape left right firstPos segment index word? ∧
      ReviewerReadOccurrenceReceipt
        shape left right secondPos segment index word? := by
  refine ⟨hne, ?_, ?_⟩
  · exact
      concreteBPNativeSuccinctRMQWholeQueryOccurrenceProvenance_checked
        shape left right hfirst
  · exact
      concreteBPNativeSuccinctRMQWholeQueryOccurrenceProvenance_checked
        shape left right hsecond

/--
Compatibility W18 event-value provenance for every emitted canonical read.

The returned prefix is the prefix of the concrete closed program that was
actually folded before `instr`; `preState` is exactly that fold's value; and
the same read event belongs to `instr`'s evaluation trace and resolves to the
returned physical source/region.  It does not retain global or local positions;
new public consumers use the occurrence-level receipt above.
-/
theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_read_producer_provenance
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    ∀ {segment index : Nat} {word? : Option WordRAM.Word},
      WordRAM.TraceEvent.readWord segment index word? ∈
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
            shape left right).trace ->
        ∃ source : ReviewerSource,
        ∃ leaf : ReviewerReadLeaf,
        ∃ instr : WholeQueryInstr,
        ∃ preState : WholeQueryState,
        ∃ before after : WholeQueryProgram,
          concreteBPNativeSuccinctRMQWholeQueryProgram =
              before ++ instr :: after ∧
          preState =
            (WholeQueryProgram.evalGlobalWordTrace
              shape left right before WholeQueryState.empty).value ∧
          source.ProducedReadBy
            shape left right instr preState segment index word? ∧
          instr.reviewerReadLeaf? = some leaf ∧
          ReviewerProducerReadPath shape leaf segment index word? ∧
          source.Counted := by
  intro segment index word? hmem
  have hprogramMem :
      WordRAM.TraceEvent.readWord segment index word? ∈
        (WholeQueryProgram.evalGlobalWordTrace shape left right
          concreteBPNativeSuccinctRMQWholeQueryProgram
          WholeQueryState.empty).trace := by
    simpa [concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult] using hmem
  rcases
      WholeQueryProgram.evalGlobalWordTrace_event_producer
        shape left right concreteBPNativeSuccinctRMQWholeQueryProgram
        WholeQueryState.empty
        (WordRAM.TraceEvent.readWord segment index word?) hprogramMem with
    ⟨instr, preState, hproducer⟩
  rcases hproducer.prefix_state with
    ⟨before, after, hprogram, hpreState⟩
  have hsegment : segment < 23 :=
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_read_segment_lt
      shape left right hmem
  rcases
      (concreteBPNativeSuccinctRMQReviewerSegmentSource?_coverage segment).2
        hsegment with ⟨source, hsource⟩
  have hregion :
      concreteBPNativeSuccinctRMQReviewerSegmentRegion? segment =
        some source.region := by
    simp [concreteBPNativeSuccinctRMQReviewerSegmentRegion?, hsource]
  have hlocal := hproducer.event_mem_instruction_trace
  rcases
      WholeQueryInstr.evalGlobalWordTrace_read_producer_path
        shape left right instr preState hlocal with
    ⟨leaf, hleaf, hpath⟩
  refine ⟨source, leaf, instr, preState, before, after, hprogram, hpreState,
    ⟨hsource, hregion, hlocal⟩, hleaf, hpath, ?_⟩
  exact concreteBPNativeSuccinctRMQReviewerSegmentSource_counted hsource

/-- Compatibility W18 name for the event-value producer obligation. -/
def ConcreteBPNativeSuccinctRMQWholeQueryProducerProvenance
    (shape : Cartesian.CartesianShape) (left right : Nat) : Prop :=
  ∀ {segment index : Nat} {word? : Option WordRAM.Word},
    WordRAM.TraceEvent.readWord segment index word? ∈
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          shape left right).trace ->
      ∃ source : ReviewerSource,
      ∃ leaf : ReviewerReadLeaf,
      ∃ instr : WholeQueryInstr,
      ∃ preState : WholeQueryState,
      ∃ before after : WholeQueryProgram,
        concreteBPNativeSuccinctRMQWholeQueryProgram =
            before ++ instr :: after ∧
        preState =
          (WholeQueryProgram.evalGlobalWordTrace
            shape left right before WholeQueryState.empty).value ∧
        source.ProducedReadBy
          shape left right instr preState segment index word? ∧
        instr.reviewerReadLeaf? = some leaf ∧
        ReviewerProducerReadPath shape leaf segment index word? ∧
        source.Counted

theorem concreteBPNativeSuccinctRMQWholeQueryProducerProvenance_checked
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    ConcreteBPNativeSuccinctRMQWholeQueryProducerProvenance
      shape left right := by
  unfold ConcreteBPNativeSuccinctRMQWholeQueryProducerProvenance
  exact
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_read_producer_provenance
      shape left right

/--
Compatibility W17 category join.  It does not identify the instruction that
produced the event or that instruction's actual pre-state; use
`concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_read_producer_provenance`.
-/
theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_read_operational_source
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    ∀ {segment index : Nat} {word? : Option WordRAM.Word},
      WordRAM.TraceEvent.readWord segment index word? ∈
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
            shape left right).trace →
        ∃ source : ReviewerSource,
        ∃ leaf : ReviewerReadLeaf,
        ∃ instr : WholeQueryInstr,
          concreteBPNativeSuccinctRMQReviewerSegmentSource? segment =
              some source ∧
          concreteBPNativeSuccinctRMQReviewerSegmentLeaf? segment =
              some leaf ∧
          source.Counted ∧
          source.Live ∧
          source.OperationallyOwnedBy leaf ∧
          instr ∈ concreteBPNativeSuccinctRMQWholeQueryProgram ∧
          instr.reviewerReadLeaf? = some leaf ∧
          WholeQueryInstr.reviewerReadLeafEvaluatorBranch
            shape left right WholeQueryState.empty leaf instr := by
  intro segment index word? hmem
  have hsegment : segment < 23 :=
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_read_segment_lt
      shape left right hmem
  rcases
      (concreteBPNativeSuccinctRMQReviewerSegmentSource?_coverage segment).2
        hsegment with ⟨source, hsource⟩
  rcases
      (concreteBPNativeSuccinctRMQReviewerSegmentLeaf?_coverage segment).2
        hsegment with ⟨leaf, hleafSegment⟩
  have hcounted : source.Counted :=
    concreteBPNativeSuccinctRMQReviewerSegmentSource_counted hsource
  have hlive : source.Live :=
    (concreteBPNativeSuccinctRMQReviewerSource_counted_iff_live source).1
      hcounted
  rcases
      concreteBPNativeSuccinctRMQWholeQueryProgram_contains_reviewerReadLeaf
        leaf with ⟨instr, hinstr, hleafInstr⟩
  refine ⟨source, leaf, instr, hsource, hleafSegment, hcounted, hlive,
    ⟨segment, hsource, hleafSegment⟩, hinstr, hleafInstr, ?_⟩
  exact WholeQueryInstr.reviewerReadLeaf?_some_evaluatorBranch
    shape left right WholeQueryState.empty leaf instr hleafInstr

theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_event_read_or_primitive
    (shape : Cartesian.CartesianShape)
    (left right : Nat) :
    forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          shape left right).trace ->
        event.isReadWord \/ event.isWordPrimitive := by
  intro event _hmem
  exact WordRAM.TraceEvent.isReadWord_or_isWordPrimitive event

theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_matchesReadStore
    (shape : Cartesian.CartesianShape)
    (left right : Nat) :
    forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          shape left right).trace ->
        event.matchesReadStore
          (concreteBPNativeSuccinctRMQGlobalReadStore shape) := by
  unfold concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
  apply WordRAM.TraceResult.map_trace_forall
  exact
    WholeQueryProgram.evalGlobalWordTrace_matchesReadStore
      shape left right concreteBPNativeSuccinctRMQWholeQueryProgram
      WholeQueryState.empty

theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_no_syntheticCostOnlyPrimitive
    (shape : Cartesian.CartesianShape)
    (left right : Nat) :
    forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          shape left right).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  unfold concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
  apply WordRAM.TraceResult.map_trace_forall
  exact
    WholeQueryProgram.evalGlobalWordTrace_no_syntheticCostOnlyPrimitive
      shape left right concreteBPNativeSuccinctRMQWholeQueryProgram
      WholeQueryState.empty

/--
Every event emitted by the accepted canonical whole-query execution is an
actual attempted payload read, executed word-rank primitive, or executed
word-select primitive.  Unlike `isReadWord \/ isWordPrimitive`, this explicit
classification excludes the synthetic fallback constructor.
-/
theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_event_readWord_or_wordRank_or_wordSelect
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    forall event,
      event ∈
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
            shape left right).trace ->
        (Exists fun segment : Nat => Exists fun index : Nat =>
          Exists fun word? : Option WordRAM.Word =>
            event = WordRAM.TraceEvent.readWord segment index word?) \/
        (Exists fun target : Bool => Exists fun limit : Nat =>
          Exists fun result : Nat =>
            event = WordRAM.TraceEvent.wordRank target limit result) \/
        (Exists fun target : Bool => Exists fun occurrence : Nat =>
          Exists fun result : Option Nat =>
            event = WordRAM.TraceEvent.wordSelect target occurrence result) := by
  intro event hmem
  have hnot :=
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_no_syntheticCostOnlyPrimitive
      shape left right event hmem
  cases event with
  | readWord segment index word? =>
      exact Or.inl ⟨segment, index, word?, rfl⟩
  | wordRank target limit result =>
      exact Or.inr (Or.inl ⟨target, limit, result, rfl⟩)
  | wordSelect target occurrence result =>
      exact Or.inr (Or.inr ⟨target, occurrence, result, rfl⟩)
  | syntheticCostOnlyPrimitive =>
      simp [WordRAM.TraceEvent.isSyntheticCostOnlyPrimitive] at hnot

/-- Every actually emitted canonical event has unit non-synthetic certificate weight. -/
theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_event_nonSyntheticWeight_eq_one
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    forall event,
      event ∈
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
            shape left right).trace ->
        event.nonSyntheticWeight = 1 := by
  intro event hmem
  rcases
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_event_readWord_or_wordRank_or_wordSelect
        shape left right event hmem with hread | hrank | hselect
  · rcases hread with ⟨segment, index, word?, rfl⟩
    simp
  · rcases hrank with ⟨target, limit, result, rfl⟩
    simp
  · rcases hselect with ⟨target, occurrence, result, rfl⟩
    simp

/-- The synthetic fallback marker is absent from the actual canonical trace. -/
theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_syntheticCostOnlyPrimitive_not_mem
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    WordRAM.TraceEvent.syntheticCostOnlyPrimitive ∉
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).trace := by
  intro hmem
  exact
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_no_syntheticCostOnlyPrimitive
      shape left right WordRAM.TraceEvent.syntheticCostOnlyPrimitive hmem
      (by simp [WordRAM.TraceEvent.isSyntheticCostOnlyPrimitive])

theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_noFiniteSmallInteriorSuccessfulRead_of_ready
    (shape : Cartesian.CartesianShape)
    (hready : SuccinctClose.concreteBPRelativeRmmInteriorReady shape)
    (left right : Nat) :
    forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          shape left right).trace ->
        concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead
          event := by
  unfold concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
  apply WordRAM.TraceResult.map_trace_forall
  exact
    WholeQueryProgram.evalGlobalWordTrace_noFiniteSmallInteriorSuccessfulRead_of_ready
      shape hready left right concreteBPNativeSuccinctRMQWholeQueryProgram
      WholeQueryState.empty

theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_noFiniteSmallInteriorSuccessfulRead
    (shape : Cartesian.CartesianShape)
    (left right : Nat) :
    forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          shape left right).trace ->
        concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead
          event := by
  unfold concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
  apply WordRAM.TraceResult.map_trace_forall
  exact
    WholeQueryProgram.evalGlobalWordTrace_noFiniteSmallInteriorSuccessfulRead
      shape left right concreteBPNativeSuccinctRMQWholeQueryProgram
      WholeQueryState.empty

theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_noReadyCloseSuccessfulRead_of_not_ready
    (shape : Cartesian.CartesianShape)
    (hnotReady : ¬ SuccinctClose.concreteBPRelativeRmmInteriorReady shape)
    (left right : Nat) :
    forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          shape left right).trace ->
        concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead
          event := by
  have _hsmall :
      shape.size <
        SuccinctClose.concreteBPRelativeRmmInteriorReadyThreshold :=
    SuccinctClose.concreteBPRelativeRmmInterior_size_lt_readyThreshold_of_not_ready
      hnotReady
  unfold concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
  apply WordRAM.TraceResult.map_trace_forall
  exact
    WholeQueryProgram.evalGlobalWordTrace_noReadyCloseSuccessfulRead_of_not_ready
      shape hnotReady left right concreteBPNativeSuccinctRMQWholeQueryProgram
      WholeQueryState.empty

/--
Store-extensional variant of the all-size global trace store theorem. If a
candidate read store agrees with the concrete global store at every read event
that the final query trace actually emits, then the same trace is validated by
that candidate store too.
-/
theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_matchesReadStore_of_trace_read_agreement
    (shape : Cartesian.CartesianShape)
    (left right : Nat)
    (store : WordRAM.ReadStore)
    (hagree :
      forall segment index word?,
        List.Mem (WordRAM.TraceEvent.readWord segment index word?)
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
            shape left right).trace ->
          store.readWord? segment index =
            (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
              segment index) :
    forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          shape left right).trace ->
        event.matchesReadStore store := by
  intro event hmem
  cases event with
  | readWord segment index word? =>
      have hconcrete :=
        concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_matchesReadStore
          shape left right
          (WordRAM.TraceEvent.readWord segment index word?) hmem
      have hagree' := hagree segment index word? hmem
      have hconcrete' :
          (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
            segment index = word? := by
        simpa [WordRAM.TraceEvent.matchesReadStore] using hconcrete
      exact Eq.trans hagree' hconcrete'
  | wordRank target limit result =>
      simp [WordRAM.TraceEvent.matchesReadStore]
  | wordSelect target occurrence result =>
      simp [WordRAM.TraceEvent.matchesReadStore]
  | syntheticCostOnlyPrimitive =>
      simp [WordRAM.TraceEvent.matchesReadStore]

/-
theorem
/-
The following readiness-split backing lemmas are retained in source history only.
The canonical reviewer route has one unconditional backing theorem below.
-/
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_successful_read_events_backed_by_counted_flat_payload_of_ready
    (shape : Cartesian.CartesianShape)
    (hready : SuccinctClose.concreteBPRelativeRmmInteriorReady shape)
    (left right : Nat) :
    forall {segment index : Nat} {word : List Bool},
      List.Mem (WordRAM.TraceEvent.readWord segment index (some word))
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          shape left right).trace ->
        concreteBPNativeSuccinctRMQFlatPayloadSegmentCountedInFlat
          shape segment /\
        concreteBPNativeSuccinctRMQFlatPayloadReadBacked
          shape segment index word := by
  intro segment index word hmem
  have hflatStore :
      forall event,
        List.Mem event
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
            shape left right).trace ->
          event.matchesReadStore
            (concreteBPNativeSuccinctRMQFlatPayloadReadStore shape) := by
    exact
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_matchesReadStore_of_trace_read_agreement
        shape left right
        (concreteBPNativeSuccinctRMQFlatPayloadReadStore shape)
        (by
          intro segment index word? _hmem
          exact
            concreteBPNativeSuccinctRMQFlatPayloadReadStore_eq_global
              shape segment index)
  have hbackedEvent :
      concreteBPNativeSuccinctRMQFlatPayloadTraceEventSuccessfulReadBacked
        shape (WordRAM.TraceEvent.readWord segment index (some word)) :=
    concreteBPNativeSuccinctRMQFlatPayloadTraceEventSuccessfulReadBacked_of_flatStore_match
      shape
      (hflatStore
        (WordRAM.TraceEvent.readWord segment index (some word)) hmem)
      (fun _ _ _ => hready)
      (fun _ _ _ => hready)
  simpa [concreteBPNativeSuccinctRMQFlatPayloadTraceEventSuccessfulReadBacked]
    using hbackedEvent

theorem
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_successful_read_events_backed_by_counted_flat_payload_of_noFiniteSmallInterior
    (shape : Cartesian.CartesianShape)
    (hready : SuccinctClose.concreteBPRelativeRmmInteriorReady shape)
    (left right : Nat)
    (_hnoFiniteSmallInterior :
      forall event,
        List.Mem event
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
            shape left right).trace ->
          concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead
            event) :
    forall {segment index : Nat} {word : List Bool},
      List.Mem (WordRAM.TraceEvent.readWord segment index (some word))
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          shape left right).trace ->
        concreteBPNativeSuccinctRMQFlatPayloadSegmentCountedInFlat
          shape segment /\
        concreteBPNativeSuccinctRMQFlatPayloadReadBacked
          shape segment index word :=
  concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_successful_read_events_backed_by_counted_flat_payload_of_ready
    shape hready left right

theorem
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_successful_read_events_backed_by_counted_flat_payload_of_not_ready
    (shape : Cartesian.CartesianShape)
    (_hnotReady : ¬ SuccinctClose.concreteBPRelativeRmmInteriorReady shape)
    (left right : Nat) :
    (forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          shape left right).trace ->
        concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead
          event) ->
    forall {segment index : Nat} {word : List Bool},
      List.Mem (WordRAM.TraceEvent.readWord segment index (some word))
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          shape left right).trace ->
        concreteBPNativeSuccinctRMQFlatPayloadSegmentCountedInFlat
          shape segment /\
        concreteBPNativeSuccinctRMQFlatPayloadReadBacked
          shape segment index word := by
  intro hnoReadyClose segment index word hmem
  have hflatStore :
      forall event,
        List.Mem event
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
            shape left right).trace ->
          event.matchesReadStore
            (concreteBPNativeSuccinctRMQFlatPayloadReadStore shape) := by
    exact
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_matchesReadStore_of_trace_read_agreement
        shape left right
        (concreteBPNativeSuccinctRMQFlatPayloadReadStore shape)
        (by
          intro segment index word? _hmem
          exact
            concreteBPNativeSuccinctRMQFlatPayloadReadStore_eq_global
              shape segment index)
  have hbackedEvent :
      concreteBPNativeSuccinctRMQFlatPayloadTraceEventSuccessfulReadBacked
        shape (WordRAM.TraceEvent.readWord segment index (some word)) :=
    concreteBPNativeSuccinctRMQFlatPayloadTraceEventSuccessfulReadBacked_of_flatStore_match
      shape
      (hflatStore
        (WordRAM.TraceEvent.readWord segment index (some word)) hmem)
      (fun readIndex readWord hreadEvent =>
        False.elim (by
          have hno :=
            hnoReadyClose
              (WordRAM.TraceEvent.readWord segment index (some word)) hmem
          cases hreadEvent
          simp [concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead] at hno))
      (fun readIndex readWord hreadEvent =>
        False.elim (by
          have hno :=
            hnoReadyClose
              (WordRAM.TraceEvent.readWord segment index (some word)) hmem
          cases hreadEvent
          simp [concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead] at hno))
  simpa [concreteBPNativeSuccinctRMQFlatPayloadTraceEventSuccessfulReadBacked]
    using hbackedEvent

theorem
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_successful_read_events_backed_by_counted_flat_payload
    (shape : Cartesian.CartesianShape)
    (left right : Nat) :
    forall {segment index : Nat} {word : List Bool},
      List.Mem (WordRAM.TraceEvent.readWord segment index (some word))
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          shape left right).trace ->
        concreteBPNativeSuccinctRMQFlatPayloadSegmentCountedInFlat
          shape segment /\
        concreteBPNativeSuccinctRMQFlatPayloadReadBacked
          shape segment index word := by
  by_cases hready :
      SuccinctClose.concreteBPRelativeRmmInteriorReady shape
  · intro hmem
    exact
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_successful_read_events_backed_by_counted_flat_payload_of_ready
        shape hready left right
        hmem
  · have _hsmall :
        shape.size <
          SuccinctClose.concreteBPRelativeRmmInteriorReadyThreshold :=
      SuccinctClose.concreteBPRelativeRmmInterior_size_lt_readyThreshold_of_not_ready
        hready
    intro hmem
    exact
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_successful_read_events_backed_by_counted_flat_payload_of_not_ready
        shape hready left right
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_noReadyCloseSuccessfulRead_of_not_ready
          shape hready left right)
        hmem

theorem
-/

/-- Every successful canonical reviewer read is backed by its counted source. -/
theorem
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_successful_read_events_backed_by_counted_flat_payload
    (shape : Cartesian.CartesianShape)
    (left right : Nat) :
    forall {segment index : Nat} {word : List Bool},
      List.Mem (WordRAM.TraceEvent.readWord segment index (some word))
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          shape left right).trace ->
        concreteBPNativeSuccinctRMQCanonicalReviewerReadBacked
          shape segment index word := by
  intro segment index word hmem
  have hmatch :=
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_matchesReadStore
      shape left right
      (WordRAM.TraceEvent.readWord segment index (some word)) hmem
  apply
    concreteBPNativeSuccinctRMQCanonicalReviewerReadStore_successful_read_backed
  rw [concreteBPNativeSuccinctRMQCanonicalReviewerReadStore_eq_global]
  simpa [WordRAM.TraceEvent.matchesReadStore] using hmatch

theorem
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_successful_read_events_backed_by_counted_flat_payload_of_ready
    (shape : Cartesian.CartesianShape)
    (_hready : SuccinctClose.concreteBPRelativeRmmInteriorReady shape)
    (left right : Nat) :
    forall {segment index : Nat} {word : List Bool},
      List.Mem (WordRAM.TraceEvent.readWord segment index (some word))
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          shape left right).trace ->
        concreteBPNativeSuccinctRMQCanonicalReviewerReadBacked
          shape segment index word :=
  concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_successful_read_events_backed_by_counted_flat_payload
    shape left right

theorem
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_successful_read_events_backed_by_counted_flat_payload_of_noFiniteSmallInterior
    (shape : Cartesian.CartesianShape)
    (_hready : SuccinctClose.concreteBPRelativeRmmInteriorReady shape)
    (left right : Nat)
    (_hnoFiniteSmallInterior :
      forall event,
        List.Mem event
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
            shape left right).trace ->
          concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead
            event) :
    forall {segment index : Nat} {word : List Bool},
      List.Mem (WordRAM.TraceEvent.readWord segment index (some word))
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          shape left right).trace ->
        concreteBPNativeSuccinctRMQCanonicalReviewerReadBacked
          shape segment index word :=
  concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_successful_read_events_backed_by_counted_flat_payload
    shape left right

theorem
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_successful_read_events_backed_by_counted_flat_payload_of_not_ready
    (shape : Cartesian.CartesianShape)
    (_hnotReady : ¬ SuccinctClose.concreteBPRelativeRmmInteriorReady shape)
    (left right : Nat) :
    (forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          shape left right).trace ->
        concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead event) ->
    forall {segment index : Nat} {word : List Bool},
      List.Mem (WordRAM.TraceEvent.readWord segment index (some word))
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          shape left right).trace ->
        concreteBPNativeSuccinctRMQCanonicalReviewerReadBacked
          shape segment index word := by
  intro _hnoReady
  exact
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_successful_read_events_backed_by_counted_flat_payload
      shape left right
theorem
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_noFiniteSmallSameBlockSuccessfulRead
    (shape : Cartesian.CartesianShape)
    (left right : Nat) :
    forall {index : Nat} {word : List Bool},
      ¬ List.Mem (WordRAM.TraceEvent.readWord
          concreteBPNativeFiniteSmallSameBlockCloseTraceSegment index
          (some word))
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          shape left right).trace := by
  intro index word hmem
  have hmatch :=
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_matchesReadStore
      shape left right
      (WordRAM.TraceEvent.readWord
        concreteBPNativeFiniteSmallSameBlockCloseTraceSegment index
        (some word)) hmem
  have hnone :
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          concreteBPNativeFiniteSmallSameBlockCloseTraceSegment index = none := by
    simp [concreteBPNativeSuccinctRMQGlobalReadStore,
      concreteBPNativeFiniteSmallSameBlockCloseTraceSegment]
  rw [WordRAM.TraceEvent.matchesReadStore] at hmatch
  rw [hnone] at hmatch
  cases hmatch

/--
Public all-size execution-story packet for the globally segmented final RMQ
trace. It removes the large-regime premise from the store-backed story: every
actual payload read in the final query agrees with the concrete global read
store, and the close-navigation leg uses the same structural route at every
size.
-/
theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTrace_execution_story
    (shape : Cartesian.CartesianShape)
    (left right : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
      shape left right =
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).toCosted /\
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
      shape left right =
      concreteBPNativeSuccinctRMQWholeQueryCanonicalInterpretedCosted shape left right /\
    (forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          shape left right).trace ->
        event.isReadWord \/ event.isWordPrimitive) /\
    (forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          shape left right).trace ->
        event.matchesReadStore
          (concreteBPNativeSuccinctRMQGlobalReadStore shape)) := by
  constructor
  · exact
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_eq_traceResult_toCosted
        shape left right
  constructor
  · exact
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_refines_canonicalInterpretedCosted
        shape left right
  constructor
  · exact
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_event_read_or_primitive
        shape left right
  · exact
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_matchesReadStore
        shape left right

/--
Store-extensional all-size execution-story packet. Besides the ordinary
global-store theorem shape, this version may be instantiated with any read store
that agrees with the concrete global store on the payload-read events present in
the emitted final-query trace.
-/
theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTrace_store_extensional_execution_story
    (shape : Cartesian.CartesianShape)
    (left right : Nat)
    (store : WordRAM.ReadStore)
    (hagree :
      forall segment index word?,
        List.Mem (WordRAM.TraceEvent.readWord segment index word?)
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
            shape left right).trace ->
          store.readWord? segment index =
            (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
              segment index) :
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
      shape left right =
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).toCosted /\
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
      shape left right =
      concreteBPNativeSuccinctRMQWholeQueryCanonicalInterpretedCosted shape left right /\
    (forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          shape left right).trace ->
        event.isReadWord \/ event.isWordPrimitive) /\
    (forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          shape left right).trace ->
        event.matchesReadStore store) := by
  constructor
  case left =>
    exact
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_eq_traceResult_toCosted
        shape left right
  case right =>
    constructor
    case left =>
      exact
        concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_refines_canonicalInterpretedCosted
          shape left right
    case right =>
      constructor
      case left =>
        exact
          concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_event_read_or_primitive
            shape left right
      case right =>
        exact
          concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_matchesReadStore_of_trace_read_agreement
            shape left right store hagree

theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_event_bounds
    (shape : Cartesian.CartesianShape)
    (left right : Nat) :
    forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          shape left right).trace ->
        concreteBPNativeTraceEventReadAddressFitsInBits
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceEventBits
            shape left right) event /\
        concreteBPNativeTraceEventPrimitiveOperandsFitInBits
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceEventBits
            shape left right) event := by
  intro event hmem
  constructor
  · exact
      concreteBPNativeTraceEventReadAddressFitsInBits_of_mem
        (trace :=
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
            shape left right).trace)
        (event := event) hmem
  · exact
      concreteBPNativeTraceEventPrimitiveOperandsFitInBits_of_mem
        (trace :=
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
            shape left right).trace)
        (event := event) hmem

/--
Bounded all-size execution-story packet for the globally segmented final RMQ
trace.  It extends the store-backed execution story with a concrete finite
event width: every payload-read address and every word-primitive natural
operand/result appearing in the final trace fits that width.
-/
theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTrace_bounded_execution_story
    (shape : Cartesian.CartesianShape)
    (left right : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
      shape left right =
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).toCosted /\
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
      shape left right =
      concreteBPNativeSuccinctRMQWholeQueryCanonicalInterpretedCosted shape left right /\
    (forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          shape left right).trace ->
        event.isReadWord \/ event.isWordPrimitive) /\
    (forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          shape left right).trace ->
        event.matchesReadStore
          (concreteBPNativeSuccinctRMQGlobalReadStore shape)) /\
    (forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          shape left right).trace ->
        concreteBPNativeTraceEventReadAddressFitsInBits
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceEventBits
            shape left right) event) /\
    (forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          shape left right).trace ->
        concreteBPNativeTraceEventPrimitiveOperandsFitInBits
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceEventBits
            shape left right) event) := by
  rcases
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTrace_execution_story
      shape left right with
    ⟨hcost, hrefine, hclass, hstore⟩
  exact
    ⟨hcost, hrefine, hclass, hstore,
      (fun event hmem =>
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_event_bounds
          shape left right event hmem).1),
      (fun event hmem =>
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_event_bounds
          shape left right event hmem).2)⟩

/--
All-size structural execution-story packet for the final globally segmented
RMQ trace.

The all-size global interpreter now consumes
`concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural`, so the two
former close-navigation fallback leaves are replaced by structural BP-code,
bounded-summary, or two-level table traces.
-/
theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTrace_allSizeStructural_execution_story
    (shape : Cartesian.CartesianShape)
    (left right : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
      shape left right =
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).toCosted /\
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
      shape left right =
      concreteBPNativeSuccinctRMQWholeQueryCanonicalInterpretedCosted shape left right /\
    (forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          shape left right).trace ->
        event.isReadWord \/ event.isWordPrimitive) /\
    (forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          shape left right).trace ->
        event.matchesReadStore
          (concreteBPNativeSuccinctRMQGlobalReadStore shape)) /\
    (forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          shape left right).trace ->
        concreteBPNativeTraceEventReadAddressFitsInBits
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceEventBits
            shape left right) event) /\
    (forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          shape left right).trace ->
        concreteBPNativeTraceEventPrimitiveOperandsFitInBits
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceEventBits
            shape left right) event) := by
  exact
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTrace_bounded_execution_story
      shape left right

/--
All-size no-synthetic execution-story packet for the final globally segmented
RMQ trace.

This is the public close of the former `TraceResult.ofCosted` fallback boundary:
the final all-size trace refines the interpreted query, reads from the concrete
global payload store, has bounded read/primitive operands, and contains no
dedicated synthetic cost-only marker events.
-/
theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTrace_noSynthetic_execution_story
    (shape : Cartesian.CartesianShape)
    (left right : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
      shape left right =
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).toCosted /\
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
      shape left right =
      concreteBPNativeSuccinctRMQWholeQueryCanonicalInterpretedCosted shape left right /\
    (forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          shape left right).trace ->
        event.isReadWord \/ event.isWordPrimitive) /\
    (forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          shape left right).trace ->
        event.matchesReadStore
          (concreteBPNativeSuccinctRMQGlobalReadStore shape)) /\
    (forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          shape left right).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive) /\
    (forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          shape left right).trace ->
        concreteBPNativeTraceEventReadAddressFitsInBits
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceEventBits
            shape left right) event) /\
    (forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          shape left right).trace ->
        concreteBPNativeTraceEventPrimitiveOperandsFitInBits
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceEventBits
            shape left right) event) := by
  rcases
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTrace_bounded_execution_story
      shape left right with
    ⟨hcost, hrefine, hclass, hstore, hreadBits, hprimitiveBits⟩
  exact
    ⟨hcost, hrefine, hclass, hstore,
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_no_syntheticCostOnlyPrimitive
        shape left right,
      hreadBits, hprimitiveBits⟩

/-
/--
Flat-payload, no-synthetic all-size execution-story packet for the final
globally segmented RMQ trace.

This is the combined public hardening theorem: the current query-independent
flat payload layout backs the global read store with source manifests for all
successful reads, counted successful reads carry positional flat-slice evidence,
the final query refines the whole-query interpreter, every event is a payload
read or word-local primitive, no event is the synthetic cost-only marker, and
the read/primitive natural data are bounded by the trace-local bit width.
-/
/-
theorem concreteBPNativeSuccinctRMQWholeQueryFlatPayloadStore_noSynthetic_execution_story
    (shape : Cartesian.CartesianShape)
    (left right : Nat) :
    (concreteBPNativeSuccinctRMQFlatPayloadLayout shape).payload =
        concreteBPNativeSuccinctRMQPayload
          builtGenericSparseExceptionSelectBPCloseAccessFamily shape /\
      (let layout := concreteBPNativeSuccinctRMQFlatPayloadLayout shape
       layout.payload =
        layout.bpCodePayload ++ layout.accessRankPayload ++
          layout.selectPayload ++ layout.accessPadding ++
            layout.closePayload ++ layout.closePadding) /\
      concreteBPNativeSuccinctRMQFlatPayloadSegmentBackingsAll shape /\
      (forall {segment index : Nat} {word : List Bool},
        (concreteBPNativeSuccinctRMQFlatPayloadReadStore shape).readWord?
            segment index = some word ->
          concreteBPNativeSuccinctRMQFlatPayloadReadSourceManifest
            shape segment index word) /\
      (forall {segment index : Nat} {word : List Bool},
        (concreteBPNativeSuccinctRMQFlatPayloadReadStore shape).readWord?
            segment index = some word ->
          concreteBPNativeSuccinctRMQFlatPayloadSegmentCountedInFlat
            shape segment ->
          concreteBPNativeSuccinctRMQFlatPayloadReadBacked
            shape segment index word) /\
      (forall {segment index : Nat} {word : List Bool},
        List.Mem (WordRAM.TraceEvent.readWord segment index (some word))
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
            shape left right).trace ->
          concreteBPNativeSuccinctRMQFlatPayloadSegmentCountedInFlat
            shape segment /\
          concreteBPNativeSuccinctRMQFlatPayloadReadBacked
            shape segment index word) /\
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
        shape left right =
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          shape left right).toCosted /\
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
        shape left right =
        concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted
          shape left right /\
      (forall event,
        List.Mem event
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
            shape left right).trace ->
          event.isReadWord \/ event.isWordPrimitive) /\
      (forall event,
        List.Mem event
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
            shape left right).trace ->
          event.matchesReadStore
            (concreteBPNativeSuccinctRMQFlatPayloadReadStore shape)) /\
      (forall event,
        List.Mem event
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
            shape left right).trace ->
          ¬ event.isSyntheticCostOnlyPrimitive) /\
      (forall event,
        List.Mem event
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
            shape left right).trace ->
          concreteBPNativeTraceEventReadAddressFitsInBits
            (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceEventBits
              shape left right) event) /\
      (forall event,
        List.Mem event
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
            shape left right).trace ->
          concreteBPNativeTraceEventPrimitiveOperandsFitInBits
            (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceEventBits
              shape left right) event) := by
  rcases
    concreteBPNativeSuccinctRMQFlatPayloadReadStore_successful_reads_have_source_manifest
      shape with
    ⟨hpayload, hcomponents, hreadBacked⟩
  have hreadBackedCounted :
      forall {segment index : Nat} {word : List Bool},
        (concreteBPNativeSuccinctRMQFlatPayloadReadStore shape).readWord?
            segment index = some word ->
          concreteBPNativeSuccinctRMQFlatPayloadSegmentCountedInFlat
            shape segment ->
          concreteBPNativeSuccinctRMQFlatPayloadReadBacked
            shape segment index word := by
    exact
      (concreteBPNativeSuccinctRMQFlatPayloadReadStore_successful_counted_reads_backed_by_counted_payload
        shape).2.2
  have hflatStore :
      forall event,
        List.Mem event
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
            shape left right).trace ->
          event.matchesReadStore
            (concreteBPNativeSuccinctRMQFlatPayloadReadStore shape) := by
    exact
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_matchesReadStore_of_trace_read_agreement
        shape left right
        (concreteBPNativeSuccinctRMQFlatPayloadReadStore shape)
        (by
          intro segment index word? _hmem
          exact
            concreteBPNativeSuccinctRMQFlatPayloadReadStore_eq_global
              shape segment index)
  rcases
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTrace_noSynthetic_execution_story
      shape left right with
    ⟨hcost, hrefine, hclass, _hglobalStore, hnoSynthetic,
      hreadBits, hprimitiveBits⟩
  exact
    ⟨hpayload, hcomponents,
      concreteBPNativeSuccinctRMQFlatPayloadSegmentBackings_all shape,
      hreadBacked, hreadBackedCounted,
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_successful_read_events_backed_by_counted_flat_payload
        shape left right,
      hcost, hrefine, hclass, hflatStore,
      hnoSynthetic,
      hreadBits, hprimitiveBits⟩

-/
-/

/--
Canonical counted-store execution packet.  The counted payload is the unique
canonical reviewer layout, whose close component is erased by exactly the
words served at segment 20.  The old flat layout is compatibility-only.
-/
theorem concreteBPNativeSuccinctRMQWholeQueryFlatPayloadStore_noSynthetic_execution_story
    (shape : Cartesian.CartesianShape)
    (left right : Nat) :
    concreteBPNativeSuccinctRMQCanonicalReviewerPayload shape =
        (concreteBPNativeSuccinctRMQCanonicalReviewerPayloadLayout
          shape).payload /\
      SuccinctSpace.flattenPayloadWords
          (SuccinctClose.canonicalRelativeRmmInteriorComponentStore
            shape).store.words.toList =
        (SuccinctClose.canonicalRelativeRmmInteriorDirectory shape).payload /\
      (forall {segment index : Nat} {word : List Bool},
        List.Mem (WordRAM.TraceEvent.readWord segment index (some word))
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
            shape left right).trace ->
          concreteBPNativeSuccinctRMQCanonicalReviewerReadBacked
            shape segment index word) /\
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
        shape left right =
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          shape left right).toCosted /\
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
        shape left right =
        concreteBPNativeSuccinctRMQWholeQueryCanonicalInterpretedCosted
          shape left right /\
      (forall event,
        List.Mem event
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
            shape left right).trace ->
          event.isReadWord \/ event.isWordPrimitive) /\
      (forall event,
        List.Mem event
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
            shape left right).trace ->
          event.matchesReadStore
            (concreteBPNativeSuccinctRMQCanonicalReviewerReadStore shape)) /\
      (forall event,
        List.Mem event
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
            shape left right).trace ->
          ¬ event.isSyntheticCostOnlyPrimitive) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [SuccinctClose.canonicalRelativeRmmInteriorDirectory] using
      SuccinctClose.canonicalRelativeRmmInteriorComponentStore_flattens_payload
        shape
  · exact
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_successful_read_events_backed_by_counted_flat_payload
        shape left right
  · exact
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_eq_traceResult_toCosted
        shape left right
  · exact
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_refines_canonicalInterpretedCosted
        shape left right
  · exact
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_event_read_or_primitive
        shape left right
  · exact
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_matchesReadStore_of_trace_read_agreement
        shape left right
        (concreteBPNativeSuccinctRMQCanonicalReviewerReadStore shape)
        (by
          intro segment index word? _hmem
          exact
            concreteBPNativeSuccinctRMQCanonicalReviewerReadStore_eq_global
              shape segment index)
  · exact
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_no_syntheticCostOnlyPrimitive
        shape left right
theorem concreteBPNativeSuccinctRMQWholeQueryWordTraceCostedOfSizeGe_eq_traceResult_toCosted
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (left right : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryWordTraceCostedOfSizeGe
      shape hsize left right =
      (concreteBPNativeSuccinctRMQWholeQueryWordTraceResultOfSizeGe
        shape hsize left right).toCosted := by
  simp [concreteBPNativeSuccinctRMQWholeQueryWordTraceCostedOfSizeGe,
    concreteBPNativeSuccinctRMQWholeQueryWordTraceResultOfSizeGe,
    Costed.map]

theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedOfSizeGe_eq_traceResult_toCosted
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (left right : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedOfSizeGe
      shape hsize left right =
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultOfSizeGe
        shape hsize left right).toCosted := by
  rfl

theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedOfSizeGe_refines_canonicalInterpretedCosted
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (left right : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedOfSizeGe
      shape hsize left right =
      concreteBPNativeSuccinctRMQWholeQueryCanonicalInterpretedCosted shape left right := by
  unfold concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedOfSizeGe
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultOfSizeGe
    concreteBPNativeSuccinctRMQWholeQueryCanonicalInterpretedCosted
  rw [WordRAM.TraceResult.map_toCosted]
  rw [
    WholeQueryProgram.evalGlobalWordTraceOfSizeGe_refines_eval
      shape hsize left right concreteBPNativeSuccinctRMQWholeQueryProgram
      WholeQueryState.empty]

theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultOfSizeGe_event_read_or_primitive
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (left right : Nat) :
    forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultOfSizeGe
          shape hsize left right).trace ->
        event.isReadWord \/ event.isWordPrimitive := by
  intro event _hmem
  exact WordRAM.TraceEvent.isReadWord_or_isWordPrimitive event

theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultOfSizeGe_matchesReadStore
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (left right : Nat) :
    forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultOfSizeGe
          shape hsize left right).trace ->
        event.matchesReadStore
          (concreteBPNativeSuccinctRMQGlobalReadStore shape) := by
  unfold concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultOfSizeGe
  apply WordRAM.TraceResult.map_trace_forall
  exact
    WholeQueryProgram.evalGlobalWordTraceOfSizeGe_matchesReadStore
      shape hsize left right concreteBPNativeSuccinctRMQWholeQueryProgram
      WholeQueryState.empty

/--
Public execution-story packet for the globally segmented final RMQ trace.
It states that the globally segmented trace is the public query after `Costed`
projection, refines the existing whole-query interpreter, contains only
payload-read or word-primitive events, and every event agrees with the single
concrete global read store assembled from the final RMQ payload components.
-/
theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceOfSizeGe_execution_story
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (left right : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedOfSizeGe
      shape hsize left right =
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultOfSizeGe
        shape hsize left right).toCosted /\
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedOfSizeGe
      shape hsize left right =
      concreteBPNativeSuccinctRMQWholeQueryCanonicalInterpretedCosted shape left right /\
    (forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultOfSizeGe
          shape hsize left right).trace ->
        event.isReadWord \/ event.isWordPrimitive) /\
    (forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultOfSizeGe
          shape hsize left right).trace ->
        event.matchesReadStore
          (concreteBPNativeSuccinctRMQGlobalReadStore shape)) := by
  exact
    ⟨concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedOfSizeGe_eq_traceResult_toCosted
        shape hsize left right,
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedOfSizeGe_refines_canonicalInterpretedCosted
        shape hsize left right,
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultOfSizeGe_event_read_or_primitive
        shape hsize left right,
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultOfSizeGe_matchesReadStore
        shape hsize left right⟩

theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultOfSizeGe_event_bounds
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (left right : Nat) :
    forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultOfSizeGe
          shape hsize left right).trace ->
        concreteBPNativeTraceEventReadAddressFitsInBits
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceEventBitsOfSizeGe
            shape hsize left right) event /\
        concreteBPNativeTraceEventPrimitiveOperandsFitInBits
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceEventBitsOfSizeGe
            shape hsize left right) event := by
  intro event hmem
  constructor
  · exact
      concreteBPNativeTraceEventReadAddressFitsInBits_of_mem
        (trace :=
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultOfSizeGe
            shape hsize left right).trace)
        (event := event) hmem
  · exact
      concreteBPNativeTraceEventPrimitiveOperandsFitInBits_of_mem
        (trace :=
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultOfSizeGe
            shape hsize left right).trace)
        (event := event) hmem

/--
Bounded large-regime companion to the all-size global execution story.
-/
theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceOfSizeGe_bounded_execution_story
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (left right : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedOfSizeGe
      shape hsize left right =
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultOfSizeGe
        shape hsize left right).toCosted /\
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedOfSizeGe
      shape hsize left right =
      concreteBPNativeSuccinctRMQWholeQueryCanonicalInterpretedCosted shape left right /\
    (forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultOfSizeGe
          shape hsize left right).trace ->
        event.isReadWord \/ event.isWordPrimitive) /\
    (forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultOfSizeGe
          shape hsize left right).trace ->
        event.matchesReadStore
          (concreteBPNativeSuccinctRMQGlobalReadStore shape)) /\
    (forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultOfSizeGe
          shape hsize left right).trace ->
        concreteBPNativeTraceEventReadAddressFitsInBits
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceEventBitsOfSizeGe
            shape hsize left right) event) /\
    (forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultOfSizeGe
          shape hsize left right).trace ->
        concreteBPNativeTraceEventPrimitiveOperandsFitInBits
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceEventBitsOfSizeGe
            shape hsize left right) event) := by
  rcases
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceOfSizeGe_execution_story
      shape hsize left right with
    ⟨hcost, hrefine, hclass, hstore⟩
  exact
    ⟨hcost, hrefine, hclass, hstore,
      (fun event hmem =>
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultOfSizeGe_event_bounds
          shape hsize left right event hmem).1),
      (fun event hmem =>
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultOfSizeGe_event_bounds
          shape hsize left right event hmem).2)⟩

theorem concreteBPNativeSuccinctRMQWholeQueryWordTraceResultOfSizeGe_event_admissible
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (left right : Nat) :
    forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryWordTraceResultOfSizeGe
          shape hsize left right).trace ->
        concreteBPNativeLargeRegimeTraceEventAdmissible
          shape hsize left right event := by
  intro event hmem
  unfold concreteBPNativeSuccinctRMQWholeQueryWordTraceResultOfSizeGe at hmem
  unfold concreteBPNativeLargeRegimeTraceEventAdmissible
  simp [concreteBPNativeSuccinctRMQWholeQueryProgram,
    WholeQueryProgram.evalWordTraceOfSizeGe,
    WholeQueryInstr.evalWordTraceOfSizeGe,
    WholeQueryNatExpr.eval, WholeQueryState.empty, WholeQueryState.opt,
    WholeQueryState.setOpt, WordRAM.TraceResult.bind,
    WordRAM.TraceResult.map, WordRAM.TraceResult.pure] at hmem ⊢
  rcases List.mem_append.mp hmem with hleftMem | hmem
  · exact Or.inl hleftMem
  rcases List.mem_append.mp hmem with hrightMem | hmem
  · exact Or.inr (Or.inl hrightMem)
  cases hleftVal :
      (concreteBPNativeSelectCloseRegisterWordTraceResult shape left).value with
  | none =>
      simp [hleftVal] at hmem
  | some leftClose =>
      cases hrightVal :
          (concreteBPNativeSelectCloseRegisterWordTraceResult
            shape (right - 1)).value with
      | none =>
          simp [hleftVal, hrightVal] at hmem
      | some rightClose =>
          simp [hleftVal, hrightVal, List.mem_append] at hmem
          rcases hmem with hlcaMem | hmem
          · exact Or.inr (Or.inr (Or.inl
              (Exists.intro leftClose
                (Exists.intro rightClose hlcaMem))))
          cases hanswerVal :
              (concreteBPNativeLCACloseWordTraceResultOfSizeGe
                shape hsize leftClose rightClose).value with
          | none =>
              simp [hanswerVal] at hmem
          | some answerClose =>
              simp [hanswerVal, WholeQueryState.setNat] at hmem
              exact Or.inr (Or.inr (Or.inr (Or.inl
                (Exists.intro answerClose hmem))))

/--
Large-regime trace-event accounting for the current final RMQ word trace.

This is still component-local provenance: every event in the unified stream is
traced to one of the concrete component traces or is a non-read primitive, and
every event is classified as either a payload read or a word primitive.  The
stronger global-store theorem further relabels component-local payload-read
segments into one shared payload layout.
-/
def concreteBPNativeLargeRegimeTraceEventSourceAccounted
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (left right : Nat)
    (event : WordRAM.TraceEvent) : Prop :=
  concreteBPNativeLargeRegimeTraceEventAdmissible
    shape hsize left right event /\
    (event.isReadWord \/ event.isWordPrimitive)

theorem concreteBPNativeSuccinctRMQWholeQueryWordTraceResultOfSizeGe_event_source_accounted
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (left right : Nat) :
    forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryWordTraceResultOfSizeGe
          shape hsize left right).trace ->
        concreteBPNativeLargeRegimeTraceEventSourceAccounted
          shape hsize left right event := by
  intro event hmem
  constructor
  · exact
      concreteBPNativeSuccinctRMQWholeQueryWordTraceResultOfSizeGe_event_admissible
        shape hsize left right event hmem
  · exact WordRAM.TraceEvent.isReadWord_or_isWordPrimitive event

/--
Single public execution-story packet for the current large-regime final RMQ
word trace.

The packet ties together the trace result, its `Costed` projection, and the
component-local provenance/classification theorem.  It is intentionally named
`source_accounted`: the remaining strengthening is the global-store version
that relabels local component segments into one concrete shared payload store.
-/
theorem concreteBPNativeSuccinctRMQWholeQueryWordTraceOfSizeGe_source_accounted_execution_story
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (left right : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryWordTraceCostedOfSizeGe
      shape hsize left right =
      (concreteBPNativeSuccinctRMQWholeQueryWordTraceResultOfSizeGe
        shape hsize left right).toCosted /\
    (forall event,
      List.Mem event
        (concreteBPNativeSuccinctRMQWholeQueryWordTraceResultOfSizeGe
          shape hsize left right).trace ->
        concreteBPNativeLargeRegimeTraceEventSourceAccounted
          shape hsize left right event) := by
  constructor
  · exact
      concreteBPNativeSuccinctRMQWholeQueryWordTraceCostedOfSizeGe_eq_traceResult_toCosted
        shape hsize left right
  · exact
      concreteBPNativeSuccinctRMQWholeQueryWordTraceResultOfSizeGe_event_source_accounted
        shape hsize left right

theorem concreteBPNativeSuccinctRMQWholeQueryLeafTraceCosted_refines_wholeQueryInterpretedCosted
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryLeafTraceCosted shape left right =
      concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted shape left right := by
  unfold concreteBPNativeSuccinctRMQWholeQueryLeafTraceCosted
    concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted
  rw [
    WholeQueryProgram.evalLeafTrace_refines_eval
      shape left right concreteBPNativeSuccinctRMQWholeQueryProgram
      WholeQueryState.empty]

theorem concreteBPNativeSuccinctRMQWholeQueryWordTraceCosted_refines_wholeQueryInterpretedCosted
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryWordTraceCosted shape left right =
      concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted shape left right := by
  unfold concreteBPNativeSuccinctRMQWholeQueryWordTraceCosted
    concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted
  rw [
    WholeQueryProgram.evalWordTrace_refines_eval
      shape left right concreteBPNativeSuccinctRMQWholeQueryProgram
      WholeQueryState.empty]

theorem concreteBPNativeSuccinctRMQWholeQueryWordTraceCostedOfSizeGe_refines_wholeQueryInterpretedCosted
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (left right : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryWordTraceCostedOfSizeGe
      shape hsize left right =
      concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted shape left right := by
  unfold concreteBPNativeSuccinctRMQWholeQueryWordTraceCostedOfSizeGe
    concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted
  rw [
    WholeQueryProgram.evalWordTraceOfSizeGe_refines_eval
      shape hsize left right concreteBPNativeSuccinctRMQWholeQueryProgram
      WholeQueryState.empty]

theorem concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted_refines_queryInterpretedCosted
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted shape left right =
      concreteBPNativeSuccinctRMQQueryInterpretedCosted shape left right := by
  unfold concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted
    concreteBPNativeSuccinctRMQWholeQueryProgram
    WholeQueryProgram.eval WholeQueryInstr.eval
    concreteBPNativeSuccinctRMQQueryInterpretedCosted
  apply Costed.ext
  · cases hleft :
        (concreteBPNativeSelectCloseRegisterInterpretedCosted shape left).value with
    | none =>
        simp [hleft, WholeQueryProgram.eval, WholeQueryInstr.eval,
          WholeQueryNatExpr.eval, WholeQueryState.empty,
          WholeQueryState.opt, WholeQueryState.setOpt, Costed.bind,
          Costed.map, Costed.pure]
    | some leftClose =>
        cases hright :
            (concreteBPNativeSelectCloseRegisterInterpretedCosted
              shape (right - 1)).value with
        | none =>
            simp [hleft, hright, WholeQueryProgram.eval,
              WholeQueryInstr.eval, WholeQueryNatExpr.eval,
              WholeQueryState.empty, WholeQueryState.opt,
              WholeQueryState.setOpt, Costed.bind, Costed.map, Costed.pure]
        | some rightClose =>
            cases hanswer :
                (concreteBPNativeLCACloseInterpretedCosted
                  shape leftClose rightClose).value with
            | none =>
                simp [hleft, hright, hanswer, WholeQueryProgram.eval,
                  WholeQueryInstr.eval, WholeQueryNatExpr.eval,
                  WholeQueryState.empty, WholeQueryState.opt,
                  WholeQueryState.setOpt, Costed.bind, Costed.map,
                  Costed.pure]
            | some answerClose =>
                simp [hleft, hright, hanswer, WholeQueryProgram.eval,
                  WholeQueryInstr.eval, WholeQueryNatExpr.eval,
                  WholeQueryState.empty, WholeQueryState.opt,
                  WholeQueryState.nat, WholeQueryState.setOpt,
                  WholeQueryState.setNat, Costed.bind, Costed.map,
                  Costed.pure]
  · cases hleft :
        (concreteBPNativeSelectCloseRegisterInterpretedCosted shape left).value with
    | none =>
        simp [hleft, WholeQueryProgram.eval, WholeQueryInstr.eval,
          WholeQueryNatExpr.eval, WholeQueryState.empty,
          WholeQueryState.opt, WholeQueryState.setOpt, Costed.bind,
          Costed.map, Costed.pure]
    | some leftClose =>
        cases hright :
            (concreteBPNativeSelectCloseRegisterInterpretedCosted
              shape (right - 1)).value with
        | none =>
            simp [hleft, hright, WholeQueryProgram.eval,
              WholeQueryInstr.eval, WholeQueryNatExpr.eval,
              WholeQueryState.empty, WholeQueryState.opt,
              WholeQueryState.setOpt, Costed.bind, Costed.map, Costed.pure]
        | some rightClose =>
            cases hanswer :
                (concreteBPNativeLCACloseInterpretedCosted
                  shape leftClose rightClose).value with
            | none =>
                simp [hleft, hright, hanswer, WholeQueryProgram.eval,
                  WholeQueryInstr.eval, WholeQueryNatExpr.eval,
                  WholeQueryState.empty, WholeQueryState.opt,
                  WholeQueryState.setOpt, Costed.bind, Costed.map,
                  Costed.pure]
            | some answerClose =>
                simp [hleft, hright, hanswer, WholeQueryProgram.eval,
                  WholeQueryInstr.eval, WholeQueryNatExpr.eval,
                  WholeQueryState.empty, WholeQueryState.opt,
                  WholeQueryState.nat, WholeQueryState.setOpt,
                  WholeQueryState.setNat, Costed.bind, Costed.map,
                  Costed.pure]

theorem concreteBPNativeSelectCloseInterpretedCosted_refines_selectCloseCosted
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    concreteBPNativeSelectCloseRegisterInterpretedCosted shape idx =
      concreteBPNativeSelectCloseCosted
        builtGenericSparseExceptionSelectBPCloseAccessFamily shape idx := by
  unfold concreteBPNativeSelectCloseRegisterInterpretedCosted
    concreteBPNativeSelectCloseCosted
    builtGenericSparseExceptionSelectBPCloseAccessFamily
    builtGenericSparseExceptionSelectBPCloseAccessDirectory
  simpa [GenericSelect.sparseExceptionSelectSource,
    GenericSelect.SparseExceptionSelectData.toChargedSelectPositionSource]
    using
      (GenericSelect.SparseExceptionSelectData.selectInterpretedCosted_refines_selectCosted
        (GenericSelect.sparseExceptionSelectData shape.bpCode false) idx)

theorem concreteBPNativeRankCloseInterpretedCosted_refines_rankCloseCosted
    (shape : Cartesian.CartesianShape) (pos : Nat) :
    concreteBPNativeRankCloseRegisterInterpretedCosted shape pos =
      concreteBPNativeRankCloseCosted
        builtGenericSparseExceptionSelectBPCloseAccessFamily shape pos := by
  unfold concreteBPNativeRankCloseRegisterInterpretedCosted
    concreteBPNativeRankCloseCosted
    builtGenericSparseExceptionSelectBPCloseAccessFamily
    builtGenericSparseExceptionSelectBPCloseAccessDirectory
  rw [
    (builtRelativeSplitBPCloseRankData shape)
      |>.rankRegisterInterpretedCosted_refines_rankInterpretedCosted false pos]
  exact
    (builtRelativeSplitBPCloseRankData shape)
      |>.rankInterpretedCosted_refines_rankCosted false pos

theorem concreteBPNativeLCACloseInterpretedCosted_refines_lcaCloseCosted
    (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) :
    concreteBPNativeLCACloseInterpretedCosted shape leftClose rightClose =
      concreteBPNativeLCACloseCosted
        builtGenericSparseExceptionSelectBPCloseAccessFamily
        shape leftClose rightClose := by
  unfold concreteBPNativeLCACloseInterpretedCosted
    concreteBPNativeLCACloseCosted
  have hfun :
      concreteBPNativeRankCloseRegisterInterpretedCosted shape =
        concreteBPNativeRankCloseCosted
          builtGenericSparseExceptionSelectBPCloseAccessFamily shape := by
    funext pos
    exact concreteBPNativeRankCloseInterpretedCosted_refines_rankCloseCosted
      shape pos
  simp [hfun]

/-- Exact-value substitution for the swapped chunked select-close leg. -/
theorem concreteBPNativeSelectCloseInterpretedCosted_exact
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    (concreteBPNativeSelectCloseInterpretedCosted shape idx).erase =
      SuccinctSpace.bpCloseOfInorder? shape idx := by
  show (concreteBPNativeChunkedSelectCloseCosted shape idx).erase = _
  rw [concreteBPNativeChunkedSelectCloseCosted_exact shape idx]
  exact SuccinctSpace.select_false_bpCode_eq_bpCloseOfInorder? shape idx

/-- Exact-value substitution for the swapped chunked rank-close seed. -/
theorem concreteBPNativeRankCloseInterpretedCosted_exact
    (shape : Cartesian.CartesianShape) (pos : Nat) :
    (concreteBPNativeRankCloseInterpretedCosted shape pos).erase =
      Succinct.rankPrefix false shape.bpCode pos :=
  concreteBPNativeChunkedRankCloseCosted_exact shape pos

theorem concreteBPNativeSuccinctRMQWholeQueryCanonicalInterpretedCosted_refines_canonicalQueryInterpretedCosted
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryCanonicalInterpretedCosted
        shape left right =
      concreteBPNativeSuccinctRMQCanonicalQueryInterpretedCosted
        shape left right := by
  unfold concreteBPNativeSuccinctRMQWholeQueryCanonicalInterpretedCosted
    concreteBPNativeSuccinctRMQWholeQueryProgram
    WholeQueryProgram.evalCanonical WholeQueryInstr.evalCanonical
    concreteBPNativeSuccinctRMQCanonicalQueryInterpretedCosted
  apply Costed.ext
  case hvalue =>
    cases hleft :
        (concreteBPNativeSelectCloseInterpretedCosted shape left).value with
    | none =>
        simp [hleft, WholeQueryProgram.evalCanonical,
          WholeQueryInstr.evalCanonical, WholeQueryNatExpr.eval,
          WholeQueryState.empty, WholeQueryState.opt,
          WholeQueryState.setOpt, Costed.bind, Costed.map, Costed.pure]
    | some leftClose =>
        cases hright :
            (concreteBPNativeSelectCloseInterpretedCosted
              shape (right - 1)).value with
        | none =>
            simp [hleft, hright, WholeQueryProgram.evalCanonical,
              WholeQueryInstr.evalCanonical, WholeQueryNatExpr.eval,
              WholeQueryState.empty, WholeQueryState.opt,
              WholeQueryState.setOpt, Costed.bind, Costed.map, Costed.pure]
        | some rightClose =>
            cases hanswer :
                (concreteBPNativeLCACloseCanonicalInterpretedCosted
                  shape leftClose rightClose).value with
            | none =>
                simp [hleft, hright, hanswer,
                  WholeQueryProgram.evalCanonical,
                  WholeQueryInstr.evalCanonical, WholeQueryNatExpr.eval,
                  WholeQueryState.empty, WholeQueryState.opt,
                  WholeQueryState.setOpt, Costed.bind, Costed.map,
                  Costed.pure]
            | some answerClose =>
                simp [hleft, hright, hanswer,
                  WholeQueryProgram.evalCanonical,
                  WholeQueryInstr.evalCanonical, WholeQueryNatExpr.eval,
                  WholeQueryState.empty, WholeQueryState.opt,
                  WholeQueryState.nat, WholeQueryState.setOpt,
                  WholeQueryState.setNat, Costed.bind, Costed.map,
                  Costed.pure]
  case hcost =>
    cases hleft :
        (concreteBPNativeSelectCloseInterpretedCosted shape left).value with
    | none =>
        simp [hleft, WholeQueryProgram.evalCanonical,
          WholeQueryInstr.evalCanonical, WholeQueryNatExpr.eval,
          WholeQueryState.empty, WholeQueryState.opt,
          WholeQueryState.setOpt, Costed.bind, Costed.map, Costed.pure]
    | some leftClose =>
        cases hright :
            (concreteBPNativeSelectCloseInterpretedCosted
              shape (right - 1)).value with
        | none =>
            simp [hleft, hright, WholeQueryProgram.evalCanonical,
              WholeQueryInstr.evalCanonical, WholeQueryNatExpr.eval,
              WholeQueryState.empty, WholeQueryState.opt,
              WholeQueryState.setOpt, Costed.bind, Costed.map, Costed.pure]
        | some rightClose =>
            cases hanswer :
                (concreteBPNativeLCACloseCanonicalInterpretedCosted
                  shape leftClose rightClose).value with
            | none =>
                simp [hleft, hright, hanswer,
                  WholeQueryProgram.evalCanonical,
                  WholeQueryInstr.evalCanonical, WholeQueryNatExpr.eval,
                  WholeQueryState.empty, WholeQueryState.opt,
                  WholeQueryState.setOpt, Costed.bind, Costed.map,
                  Costed.pure]
            | some answerClose =>
                simp [hleft, hright, hanswer,
                  WholeQueryProgram.evalCanonical,
                  WholeQueryInstr.evalCanonical, WholeQueryNatExpr.eval,
                  WholeQueryState.empty, WholeQueryState.opt,
                  WholeQueryState.nat, WholeQueryState.setOpt,
                  WholeQueryState.setNat, Costed.bind, Costed.map,
                  Costed.pure]

/-- Named component algebra for the accepted canonical charged trace. -/
structure CanonicalRMQChargedTraceCostAlgebra where
  selectClose : Nat
  rankClose : Nat
  endpointFringe : Nat
  interiorDirectory : Nat

namespace CanonicalRMQChargedTraceCostAlgebra

def closeLCA (cost : CanonicalRMQChargedTraceCostAlgebra) : Nat :=
  2 * cost.rankClose + 2 * cost.endpointFringe + cost.interiorDirectory

def wholeQuery (cost : CanonicalRMQChargedTraceCostAlgebra) : Nat :=
  2 * cost.selectClose + cost.closeLCA + cost.rankClose

end CanonicalRMQChargedTraceCostAlgebra

/-- Tight operation-wise caps for the accepted B3 chunked execution: the
select and rank components are the derived chunked bounds `35` and `11`
(`bpChunkedSelectCosted_cost_le` / `bpChunkedRankCosted_cost_le`). -/
def concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCostAlgebra :
    CanonicalRMQChargedTraceCostAlgebra where
  selectClose := 35
  rankClose := 11
  endpointFringe :=
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedEndpointFringeChargedTraceCost
  interiorDirectory :=
    SuccinctClose.canonicalRelativeRmmPrincipledInteriorChargedTraceCost

def concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost : Nat :=
  concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCostAlgebra.wholeQuery

theorem concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCloseCost_eq :
    concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCostAlgebra.closeLCA =
      126 := by
  rfl

theorem concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost_eq :
    concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost = 207 := by
  rfl

/--
Frozen historical algebra of the retired event-silent fringe route
(pattern: `canonicalTransitionalQueryCost = 328`).  The retired route's
fringe leaves computed their min-excess/argmin scan without charged reads;
the chunked route replaces the two 4-read fringes by two 37-read fringes.
-/
def concreteBPNativeSuccinctRMQSilentFringeChargedTraceCostAlgebra :
    CanonicalRMQChargedTraceCostAlgebra where
  selectClose := 13
  rankClose := 4
  endpointFringe :=
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.canonicalEndpointFringeChargedTraceCost
  interiorDirectory :=
    SuccinctClose.canonicalRelativeRmmPrincipledInteriorChargedTraceCost

/-- Frozen historical whole-query literal of the retired silent-fringe route. -/
def concreteBPNativeSuccinctRMQSilentFringeChargedTraceCost : Nat :=
  concreteBPNativeSuccinctRMQSilentFringeChargedTraceCostAlgebra.wholeQuery

theorem concreteBPNativeSuccinctRMQSilentFringeChargedTraceCost_eq :
    concreteBPNativeSuccinctRMQSilentFringeChargedTraceCost = 76 := by
  rfl

/--
Frozen historical algebra of the retired silent in-word rank/select route
(the B2 candidate: charged fringe chunks, but rank/select decoded in-word
without charged reads; pattern: `canonicalSilentFringeQueryCost = 76`).
The B3 chunked route replaces the 13-tick select closes and 4-tick rank
seeds by 35-tick and 11-tick charged chunk-table executions.
-/
def concreteBPNativeSuccinctRMQSilentWordRankSelectChargedTraceCostAlgebra :
    CanonicalRMQChargedTraceCostAlgebra where
  selectClose := 13
  rankClose := 4
  endpointFringe :=
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedEndpointFringeChargedTraceCost
  interiorDirectory :=
    SuccinctClose.canonicalRelativeRmmPrincipledInteriorChargedTraceCost

/-- Frozen historical whole-query literal of the retired silent in-word
rank/select route (the B2 candidate value). -/
def concreteBPNativeSuccinctRMQSilentWordRankSelectChargedTraceCost : Nat :=
  concreteBPNativeSuccinctRMQSilentWordRankSelectChargedTraceCostAlgebra.wholeQuery

theorem concreteBPNativeSuccinctRMQSilentWordRankSelectChargedTraceCost_eq :
    concreteBPNativeSuccinctRMQSilentWordRankSelectChargedTraceCost = 142 := by
  rfl

theorem concreteBPNativeSelectCloseInterpretedCosted_cost_le_thirteen
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    (concreteBPNativeSelectCloseRegisterInterpretedCosted shape idx).cost <=
      13 := by
  rw [concreteBPNativeSelectCloseInterpretedCosted_refines_selectCloseCosted]
  simpa [concreteBPNativeSelectCloseCosted,
    builtGenericSparseExceptionSelectBPCloseAccessFamily,
    builtGenericSparseExceptionSelectBPCloseAccessDirectory] using
    GenericSelect.sparseExceptionSelectSource_selectPositionCosted_cost_le_thirteen
      shape.bpCode false idx

theorem concreteBPNativeRankCloseInterpretedCosted_cost_le_four
    (shape : Cartesian.CartesianShape) (pos : Nat) :
    (concreteBPNativeRankCloseRegisterInterpretedCosted shape pos).cost <=
      4 := by
  rw [concreteBPNativeRankCloseInterpretedCosted_refines_rankCloseCosted]
  simpa [concreteBPNativeRankCloseCosted,
    builtGenericSparseExceptionSelectBPCloseAccessFamily,
    builtGenericSparseExceptionSelectBPCloseAccessDirectory] using
    (builtRelativeSplitBPCloseRankData shape).rankCosted_cost_le_four false pos

/-- Derived chunked select-close component bound (from
`bpChunkedSelectCosted_cost_le`). -/
theorem concreteBPNativeSelectCloseInterpretedCosted_cost_le_thirtyFive
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    (concreteBPNativeSelectCloseInterpretedCosted shape idx).cost <= 35 :=
  concreteBPNativeChunkedSelectCloseCosted_cost_le shape idx

/-- Derived chunked rank-close component bound (from
`bpChunkedRankCosted_cost_le`). -/
theorem concreteBPNativeRankCloseInterpretedCosted_cost_le_eleven
    (shape : Cartesian.CartesianShape) (pos : Nat) :
    (concreteBPNativeRankCloseInterpretedCosted shape pos).cost <= 11 :=
  concreteBPNativeChunkedRankCloseCosted_cost_le shape pos

/--
Principled U3 cap for the exact direct-bind presentation of the accepted
canonical execution.  The proof obtains endpoint bounds from the selected
values themselves and invokes the same close/LCA computation used by U2.
-/
theorem concreteBPNativeSuccinctRMQCanonicalQueryInterpretedCosted_cost_le_principledAllSizeChargedTrace
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    (concreteBPNativeSuccinctRMQCanonicalQueryInterpretedCosted
      shape left right).cost <=
        concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost := by
  unfold concreteBPNativeSuccinctRMQCanonicalQueryInterpretedCosted
  have hleft :=
    concreteBPNativeSelectCloseInterpretedCosted_cost_le_thirtyFive shape left
  have hright :=
    concreteBPNativeSelectCloseInterpretedCosted_cost_le_thirtyFive
      shape (right - 1)
  have hrankCost : forall pos,
      (concreteBPNativeRankCloseInterpretedCosted shape pos).cost <= 11 := by
    intro pos
    exact concreteBPNativeRankCloseInterpretedCosted_cost_le_eleven shape pos
  cases hleftValue :
      (concreteBPNativeSelectCloseInterpretedCosted shape left).value with
  | none =>
      simp [Costed.bind, hleftValue]
      rw [concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost_eq]
      omega
  | some leftClose =>
      cases hrightValue :
          (concreteBPNativeSelectCloseInterpretedCosted
            shape (right - 1)).value with
      | none =>
          simp [Costed.bind, hleftValue, hrightValue]
          rw [concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost_eq]
          omega
      | some rightClose =>
          have hleftExact :=
            concreteBPNativeSelectCloseInterpretedCosted_exact shape left
          have hrightExact :=
            concreteBPNativeSelectCloseInterpretedCosted_exact
              shape (right - 1)
          have hleftSome :
              SuccinctSpace.bpCloseOfInorder? shape left = some leftClose := by
            symm
            simpa [Costed.erase, hleftValue] using hleftExact
          have hrightSome :
              SuccinctSpace.bpCloseOfInorder? shape (right - 1) =
                some rightClose := by
            symm
            simpa [Costed.erase, hrightValue] using hrightExact
          have hleftBound :=
            SuccinctSpace.bpCloseOfInorder?_bounds shape hleftSome
          have hrightBound :=
            SuccinctSpace.bpCloseOfInorder?_bounds shape hrightSome
          have hlca :=
            SuccinctClose.ConcreteCompactBPCloseLCADirectory.canonicalLcaCloseCostedWithRankSeed_cost_le_principled
              shape (concreteBPNativeRankCloseInterpretedCosted shape)
              leftClose rightClose 11 hleftBound hrightBound hrankCost
          have hlcaBound :
              (SuccinctClose.ConcreteCompactBPCloseLCADirectory.canonicalLcaCloseCostedWithRankSeed
                shape (concreteBPNativeRankCloseInterpretedCosted shape)
                leftClose rightClose).cost <= 126 := by
            simpa [
              SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedPrincipledBPCloseChargedTraceCostWithRankSeed,
              SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedEndpointFringeChargedTraceCost,
              SuccinctClose.canonicalRelativeRmmPrincipledInteriorChargedTraceCost]
              using hlca
          cases hlcaValue :
              (SuccinctClose.ConcreteCompactBPCloseLCADirectory.canonicalLcaCloseCostedWithRankSeed
                shape (concreteBPNativeRankCloseInterpretedCosted shape)
                leftClose rightClose).value with
          | none =>
              simp [concreteBPNativeLCACloseCanonicalInterpretedCosted,
                Costed.bind, hleftValue, hrightValue, hlcaValue]
              rw [concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost_eq]
              omega
          | some answerClose =>
              have hrank := hrankCost (answerClose + 1)
              simp [concreteBPNativeLCACloseCanonicalInterpretedCosted,
                Costed.bind, Costed.map, hleftValue, hrightValue,
                hlcaValue]
              rw [concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost_eq]
              omega

/-- Honest transitional all-size cost bound for the canonical whole query. -/
theorem concreteBPNativeSuccinctRMQCanonicalQueryInterpretedCosted_cost_le
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    (concreteBPNativeSuccinctRMQCanonicalQueryInterpretedCosted
      shape left right).cost <=
        3 * SuccinctSelect.sparseDenseFalseSelectQueryCost +
          SuccinctClose.ConcreteCompactBPCloseLCADirectory.canonicalCompactBPCloseQueryCostWithRankSeed
            SuccinctSelect.sparseDenseFalseSelectQueryCost := by
  have hprincipled :=
    concreteBPNativeSuccinctRMQCanonicalQueryInterpretedCosted_cost_le_principledAllSizeChargedTrace
      shape left right
  rw [concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost_eq]
    at hprincipled
  have htransitional :
      3 * SuccinctSelect.sparseDenseFalseSelectQueryCost +
          SuccinctClose.ConcreteCompactBPCloseLCADirectory.canonicalCompactBPCloseQueryCostWithRankSeed
            SuccinctSelect.sparseDenseFalseSelectQueryCost = 328 := by
    rfl
  omega

/-- Exact canonical direct query for every valid half-open RMQ window. -/
theorem concreteBPNativeSuccinctRMQCanonicalQueryInterpretedCosted_exact
    {n : Nat} {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    {left len : Nat} (hlen : 0 < len) (hbound : left + len <= n) :
    (concreteBPNativeSuccinctRMQCanonicalQueryInterpretedCosted
      shape left (left + len)).erase =
        some (scanWindow shape.representative left len) := by
  have hshapeSize := Cartesian.mem_shapesOfSize_shapeOfSize hshape
  have hleftLt : left < n := by omega
  have hrightLt : left + len - 1 < n := by omega
  have hboundShape : left + len <= shape.size := by
    rw [Cartesian.ShapeOfSize.size_eq hshapeSize]
    exact hbound
  have hleftLtShape : left < shape.size := by
    rw [Cartesian.ShapeOfSize.size_eq hshapeSize]
    exact hleftLt
  have hrightLtShape : left + len - 1 < shape.size := by
    rw [Cartesian.ShapeOfSize.size_eq hshapeSize]
    exact hrightLt
  have hscanBounds :=
    Cartesian.scanWindow_bounds shape.representative left len hlen
  have hscanLt :
      scanWindow shape.representative left len < shape.size := by
    rw [Cartesian.ShapeOfSize.size_eq hshapeSize]
    omega
  let leftClose :=
    Exists.choose
      (SuccinctSpace.bpCloseOfInorder?_some_of_lt shape hleftLtShape)
  have hleftClose :=
    Exists.choose_spec
      (SuccinctSpace.bpCloseOfInorder?_some_of_lt shape hleftLtShape)
  let rightClose :=
    Exists.choose
      (SuccinctSpace.bpCloseOfInorder?_some_of_lt shape hrightLtShape)
  have hrightClose :=
    Exists.choose_spec
      (SuccinctSpace.bpCloseOfInorder?_some_of_lt shape hrightLtShape)
  let answerClose :=
    Exists.choose
      (SuccinctSpace.bpCloseOfInorder?_some_of_lt shape hscanLt)
  have hanswerClose :=
    Exists.choose_spec
      (SuccinctSpace.bpCloseOfInorder?_some_of_lt shape hscanLt)
  have hselectLeft :
      (concreteBPNativeSelectCloseInterpretedCosted
        shape left).value = some leftClose := by
    have h :=
      concreteBPNativeSelectCloseInterpretedCosted_exact shape left
    simpa only [Costed.erase] using Eq.trans h hleftClose
  have hselectRight :
      (concreteBPNativeSelectCloseInterpretedCosted
        shape (left + len - 1)).value = some rightClose := by
    have h :=
      concreteBPNativeSelectCloseInterpretedCosted_exact
        shape (left + len - 1)
    simpa only [Costed.erase] using Eq.trans h hrightClose
  have hrankExact :
      forall pos,
        (concreteBPNativeRankCloseInterpretedCosted shape pos).erase =
          Succinct.rankPrefix false shape.bpCode pos := by
    intro pos
    exact concreteBPNativeRankCloseInterpretedCosted_exact shape pos
  have hlca :
      (concreteBPNativeLCACloseCanonicalInterpretedCosted
        shape leftClose rightClose).value = some answerClose := by
    have h :=
      SuccinctClose.ConcreteCompactBPCloseLCADirectory.canonicalLcaCloseCostedWithRankSeed_exact_of_query
        (concreteBPNativeRankCloseInterpretedCosted shape)
        hrankExact hlen hboundShape hleftClose hrightClose hanswerClose
    simpa [concreteBPNativeLCACloseCanonicalInterpretedCosted,
      Costed.erase] using h
  have hrank :
      (concreteBPNativeRankCloseInterpretedCosted
        shape (answerClose + 1)).value =
          scanWindow shape.representative left len + 1 := by
    have hrankRecover :=
      SuccinctSpace.bpCloseOfInorder?_rankFalse_succ shape hanswerClose
    calc
      (concreteBPNativeRankCloseInterpretedCosted
          shape (answerClose + 1)).value =
          Succinct.rankPrefix false shape.bpCode (answerClose + 1) := by
        simpa [Costed.erase] using hrankExact (answerClose + 1)
      _ = scanWindow shape.representative left len + 1 := hrankRecover
  have hrankSub :
      scanWindow shape.representative left len + 1 - 1 =
        scanWindow shape.representative left len := by
    omega
  unfold concreteBPNativeSuccinctRMQCanonicalQueryInterpretedCosted
  simp [Costed.erase, Costed.bind, Costed.map, Costed.pure,
    hselectLeft, hselectRight, hlca, hrank, hrankSub]

theorem concreteBPNativeSuccinctRMQWholeQueryCanonicalInterpretedCosted_cost_le
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    (concreteBPNativeSuccinctRMQWholeQueryCanonicalInterpretedCosted
      shape left right).cost <=
        3 * SuccinctSelect.sparseDenseFalseSelectQueryCost +
          SuccinctClose.ConcreteCompactBPCloseLCADirectory.canonicalCompactBPCloseQueryCostWithRankSeed
            SuccinctSelect.sparseDenseFalseSelectQueryCost := by
  rw [
    concreteBPNativeSuccinctRMQWholeQueryCanonicalInterpretedCosted_refines_canonicalQueryInterpretedCosted]
  exact concreteBPNativeSuccinctRMQCanonicalQueryInterpretedCosted_cost_le
    shape left right

theorem concreteBPNativeSuccinctRMQWholeQueryCanonicalInterpretedCosted_cost_le_principledAllSizeChargedTrace
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    (concreteBPNativeSuccinctRMQWholeQueryCanonicalInterpretedCosted
      shape left right).cost <=
        concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost := by
  rw [
    concreteBPNativeSuccinctRMQWholeQueryCanonicalInterpretedCosted_refines_canonicalQueryInterpretedCosted]
  exact
    concreteBPNativeSuccinctRMQCanonicalQueryInterpretedCosted_cost_le_principledAllSizeChargedTrace
      shape left right

theorem concreteBPNativeSuccinctRMQWholeQueryCanonicalInterpretedCosted_exact
    {n : Nat} {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    {left len : Nat} (hlen : 0 < len) (hbound : left + len <= n) :
    (concreteBPNativeSuccinctRMQWholeQueryCanonicalInterpretedCosted
      shape left (left + len)).erase =
        some (scanWindow shape.representative left len) := by
  rw [
    concreteBPNativeSuccinctRMQWholeQueryCanonicalInterpretedCosted_refines_canonicalQueryInterpretedCosted]
  exact concreteBPNativeSuccinctRMQCanonicalQueryInterpretedCosted_exact
    hshape hlen hbound
theorem concreteBPNativeSuccinctRMQQueryInterpretedCosted_refines_queryCosted
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    concreteBPNativeSuccinctRMQQueryInterpretedCosted shape left right =
      concreteBPNativeSuccinctRMQQueryCosted
        builtGenericSparseExceptionSelectBPCloseAccessFamily
        shape left right := by
  unfold concreteBPNativeSuccinctRMQQueryInterpretedCosted
    concreteBPNativeSuccinctRMQQueryCosted
  simp only [
    concreteBPNativeSelectCloseInterpretedCosted_refines_selectCloseCosted,
    concreteBPNativeLCACloseInterpretedCosted_refines_lcaCloseCosted,
    concreteBPNativeRankCloseInterpretedCosted_refines_rankCloseCosted]
  rfl

theorem concreteBPNativeSuccinctRMQQueryInterpretedCosted_cost_le
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    (concreteBPNativeSuccinctRMQQueryInterpretedCosted
      shape left right).cost <=
        concreteBPNativeSuccinctRMQQueryCost
          SuccinctSelect.sparseDenseFalseSelectQueryCost := by
  rw [concreteBPNativeSuccinctRMQQueryInterpretedCosted_refines_queryCosted]
  exact
    concreteBPNativeSuccinctRMQQueryCosted_cost_le
      builtGenericSparseExceptionSelectBPCloseAccessFamily shape left right

theorem concreteBPNativeSuccinctRMQQueryInterpretedCosted_cost_le_of_ready
    (shape : Cartesian.CartesianShape)
    (hready : SuccinctClose.concreteBPRelativeRmmInteriorReady shape)
    (left right : Nat) :
    (concreteBPNativeSuccinctRMQQueryInterpretedCosted
      shape left right).cost <=
        concreteBPNativeSuccinctRMQFastRegimeQueryCost := by
  rw [concreteBPNativeSuccinctRMQQueryInterpretedCosted_refines_queryCosted]
  exact
    concreteBPNativeSuccinctRMQQueryCosted_cost_le_of_ready
      builtGenericSparseExceptionSelectBPCloseAccessFamily
      shape hready left right

theorem concreteBPNativeSuccinctRMQQueryInterpretedCosted_cost_le_routeSplit
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    (concreteBPNativeSuccinctRMQQueryInterpretedCosted
      shape left right).cost <=
        concreteBPNativeSuccinctRMQRouteSplitQueryCost shape := by
  rw [concreteBPNativeSuccinctRMQQueryInterpretedCosted_refines_queryCosted]
  exact
    concreteBPNativeSuccinctRMQQueryCosted_cost_le_routeSplit
      builtGenericSparseExceptionSelectBPCloseAccessFamily shape left right

theorem concreteBPNativeSuccinctRMQQueryInterpretedCosted_cost_le_cleanAllSize
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    (concreteBPNativeSuccinctRMQQueryInterpretedCosted
      shape left right).cost <=
        concreteBPNativeSuccinctRMQCleanAllSizeQueryCost := by
  exact Nat.le_trans
    (concreteBPNativeSuccinctRMQQueryInterpretedCosted_cost_le_routeSplit
      shape left right)
    (concreteBPNativeSuccinctRMQRouteSplitQueryCost_le_cleanAllSize shape)

theorem concreteBPNativeSuccinctRMQQueryInterpretedCosted_exact
    {n : Nat} {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    {left len : Nat} (hlen : 0 < len) (hbound : left + len <= n) :
    (concreteBPNativeSuccinctRMQQueryInterpretedCosted
      shape left (left + len)).erase =
        some (scanWindow shape.representative left len) := by
  rw [concreteBPNativeSuccinctRMQQueryInterpretedCosted_refines_queryCosted]
  exact
    concreteBPNativeSuccinctRMQQueryCosted_exact
      builtGenericSparseExceptionSelectBPCloseAccessFamily
      hshape hlen hbound

theorem concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted_cost_le
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    (concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted
      shape left right).cost <=
        concreteBPNativeSuccinctRMQQueryCost
          SuccinctSelect.sparseDenseFalseSelectQueryCost := by
  rw [
    concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted_refines_queryInterpretedCosted]
  exact
    concreteBPNativeSuccinctRMQQueryInterpretedCosted_cost_le
      shape left right

theorem concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted_cost_le_of_ready
    (shape : Cartesian.CartesianShape)
    (hready : SuccinctClose.concreteBPRelativeRmmInteriorReady shape)
    (left right : Nat) :
    (concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted
      shape left right).cost <=
        concreteBPNativeSuccinctRMQFastRegimeQueryCost := by
  rw [
    concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted_refines_queryInterpretedCosted]
  exact
    concreteBPNativeSuccinctRMQQueryInterpretedCosted_cost_le_of_ready
      shape hready left right

theorem concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted_cost_le_routeSplit
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    (concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted
      shape left right).cost <=
        concreteBPNativeSuccinctRMQRouteSplitQueryCost shape := by
  rw [
    concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted_refines_queryInterpretedCosted]
  exact
    concreteBPNativeSuccinctRMQQueryInterpretedCosted_cost_le_routeSplit
      shape left right

theorem concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted_cost_le_cleanAllSize
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    (concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted
      shape left right).cost <=
        concreteBPNativeSuccinctRMQCleanAllSizeQueryCost := by
  exact Nat.le_trans
    (concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted_cost_le_routeSplit
      shape left right)
    (concreteBPNativeSuccinctRMQRouteSplitQueryCost_le_cleanAllSize shape)

theorem concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted_exact
    {n : Nat} {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    {left len : Nat} (hlen : 0 < len) (hbound : left + len <= n) :
    (concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted
      shape left (left + len)).erase =
        some (scanWindow shape.representative left len) := by
  rw [
    concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted_refines_queryInterpretedCosted]
  exact
    concreteBPNativeSuccinctRMQQueryInterpretedCosted_exact
      hshape hlen hbound

theorem concreteBPNativeSuccinctRMQWholeQueryLeafTraceCosted_cost_le
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    (concreteBPNativeSuccinctRMQWholeQueryLeafTraceCosted
      shape left right).cost <=
        concreteBPNativeSuccinctRMQQueryCost
          SuccinctSelect.sparseDenseFalseSelectQueryCost := by
  rw [
    concreteBPNativeSuccinctRMQWholeQueryLeafTraceCosted_refines_wholeQueryInterpretedCosted]
  exact
    concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted_cost_le
      shape left right

theorem concreteBPNativeSuccinctRMQWholeQueryLeafTraceCosted_exact
    {n : Nat} {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    {left len : Nat} (hlen : 0 < len) (hbound : left + len <= n) :
    (concreteBPNativeSuccinctRMQWholeQueryLeafTraceCosted
      shape left (left + len)).erase =
        some (scanWindow shape.representative left len) := by
  rw [
    concreteBPNativeSuccinctRMQWholeQueryLeafTraceCosted_refines_wholeQueryInterpretedCosted]
  exact
    concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted_exact
      hshape hlen hbound

theorem concreteBPNativeSuccinctRMQWholeQueryWordTraceCosted_cost_le
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    (concreteBPNativeSuccinctRMQWholeQueryWordTraceCosted
      shape left right).cost <=
        concreteBPNativeSuccinctRMQQueryCost
          SuccinctSelect.sparseDenseFalseSelectQueryCost := by
  rw [
    concreteBPNativeSuccinctRMQWholeQueryWordTraceCosted_refines_wholeQueryInterpretedCosted]
  exact
    concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted_cost_le
      shape left right

theorem concreteBPNativeSuccinctRMQWholeQueryWordTraceCosted_exact
    {n : Nat} {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    {left len : Nat} (hlen : 0 < len) (hbound : left + len <= n) :
    (concreteBPNativeSuccinctRMQWholeQueryWordTraceCosted
      shape left (left + len)).erase =
        some (scanWindow shape.representative left len) := by
  rw [
    concreteBPNativeSuccinctRMQWholeQueryWordTraceCosted_refines_wholeQueryInterpretedCosted]
  exact
    concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted_exact
      hshape hlen hbound

/-- The uniform global trace has the direct canonical transitional cost. -/
theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_le_canonicalTransitional
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
      shape left right).cost <=
        3 * SuccinctSelect.sparseDenseFalseSelectQueryCost +
          SuccinctClose.ConcreteCompactBPCloseLCADirectory.canonicalCompactBPCloseQueryCostWithRankSeed
            SuccinctSelect.sparseDenseFalseSelectQueryCost := by
  rw [
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_refines_canonicalInterpretedCosted]
  exact
    concreteBPNativeSuccinctRMQWholeQueryCanonicalInterpretedCosted_cost_le
      shape left right

/--
The globally segmented accepted U2 trace has the principled uniform U3 charged
trace bound.  This is the paper-facing all-size cost theorem.
-/
theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_le_principledAllSizeChargedTrace
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
      shape left right).cost <=
        concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost := by
  rw [
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_refines_canonicalInterpretedCosted]
  exact
    concreteBPNativeSuccinctRMQWholeQueryCanonicalInterpretedCosted_cost_le_principledAllSizeChargedTrace
      shape left right

/-- The modeled cost is exactly the number of emitted charged trace events. -/
theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_eq_trace_length
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
      shape left right).cost =
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          shape left right).trace.length := by
  rfl

/--
The non-synthetic certificate weights on the events actually emitted by the
canonical execution sum to exactly that trace's length.
-/
theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_nonSyntheticWeight_sum_eq_trace_length
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    ((concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).trace.map WordRAM.TraceEvent.nonSyntheticWeight).sum =
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).trace.length := by
  apply WordRAM.TraceEvent.sum_nonSyntheticWeight_eq_length_of_forall_eq_one
  exact
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_event_nonSyntheticWeight_eq_one
      shape left right

/--
The non-synthetic certificate-weight sum equals the `Costed.cost` of the same
canonical execution. This uses the canonical no-synthetic trace; arbitrary
traces with synthetic compatibility markers are still counted by
`TraceResult.toCosted` through their full trace length.
-/
theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_nonSyntheticWeight_sum_eq_cost
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    ((concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).trace.map WordRAM.TraceEvent.nonSyntheticWeight).sum =
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
        shape left right).cost := by
  calc
    ((concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).trace.map WordRAM.TraceEvent.nonSyntheticWeight).sum =
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          shape left right).trace.length :=
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_nonSyntheticWeight_sum_eq_trace_length
        shape left right
    _ = (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
          shape left right).cost := by
      symm
      exact
        concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_eq_trace_length
          shape left right

/-- The non-synthetic-weighted actual trace is bounded by the named U3 cap. -/
theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_nonSyntheticWeight_sum_le_principledAllSizeChargedTrace
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    ((concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).trace.map WordRAM.TraceEvent.nonSyntheticWeight).sum <=
      concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost := by
  rw [
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_nonSyntheticWeight_sum_eq_cost]
  exact
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_le_principledAllSizeChargedTrace
      shape left right

/-- The non-synthetic-weighted actual canonical trace has the checked literal bound `207`. -/
theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_nonSyntheticWeight_sum_le_207
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    ((concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).trace.map WordRAM.TraceEvent.nonSyntheticWeight).sum <= 207 := by
  calc
    ((concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).trace.map WordRAM.TraceEvent.nonSyntheticWeight).sum <=
        concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost :=
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_nonSyntheticWeight_sum_le_principledAllSizeChargedTrace
        shape left right
    _ = 207 :=
      concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost_eq

/-! ### The B3 vocabulary theorem: `readWord`-only charged events -/

private theorem concreteBPNativeLocalBPWindowBitsTraceResult_events_readWord
    (shape : Cartesian.CartesianShape) (blockSize close : Nat) :
    forall event,
      event ∈
          (SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPWindowBitsTraceResult
            shape blockSize close).trace ->
        event.isReadWord := by
  intro event hmem
  unfold SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPWindowBitsTraceResult
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPBlockWordsTraceResult
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpCodeWordReadTraceResult
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpCodeReadWordTraceEvent
    at hmem
  simp [WordRAM.TraceResult.bind, WordRAM.TraceResult.map,
    WordRAM.TraceResult.pure] at hmem
  rcases hmem with hmem | hmem | hmem | hmem <;>
    subst event <;>
      trivial

private theorem concreteBPNativeInteriorGlobalWordTraceResultAllSizeStructural_events_readWord
    (shape : Cartesian.CartesianShape) (startBlock count : Nat) :
    forall event,
      event ∈
          (SuccinctClose.ConcreteCompactBPCloseLCADirectory.concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructural
            shape concreteBPNativeInteriorTraceSegments
            startBlock count).trace ->
        event.isReadWord := by
  intro event hmem
  unfold SuccinctClose.ConcreteCompactBPCloseLCADirectory.concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructural
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.canonicalRelativeRmmInteriorRangeMinTraceResultAtSegment
    SuccinctClose.flatStoreExecutionTraceResultAtSegment at hmem
  simp only [List.mem_map] at hmem
  rcases hmem with ⟨read, _hread, rfl⟩
  trivial

private theorem concreteBPNativeRankCloseWordTraceResultAtSegment_events_readWord
    (shape : Cartesian.CartesianShape) (rankSegmentBase pos : Nat) :
    forall event,
      event ∈
          (concreteBPNativeRankCloseWordTraceResultAtSegment
            shape rankSegmentBase pos).trace ->
        event.isReadWord := by
  apply
    (builtRelativeSplitBPCloseRankData
        shape).bpChunkedRankTraceResultWithStore_trace_forall
  · intro address
    trivial
  · intro address
    trivial
  · intro address
    trivial
  · intro address _hlt
    trivial

private theorem concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural_events_readWord
    (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) :
    forall event,
      event ∈
          (concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
            shape leftClose rightClose).trace ->
        event.isReadWord := by
  unfold concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
  apply
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.lcaCloseTraceResultWithRankSeedAllSizeStructural_trace_forall
      shape
      (concreteBPNativeRankCloseWordTraceResultAtSegment
        shape concreteBPNativeRankCloseTraceSegmentBase)
      concreteBPNativeInteriorTraceSegments
      concreteBPNativeFringeChunkTraceSegment
      concreteBPNativeFiniteSmallSameBlockCloseTraceSegment
      leftClose rightClose
      WordRAM.TraceEvent.isReadWord
  · intro pos
    exact
      concreteBPNativeRankCloseWordTraceResultAtSegment_events_readWord
        shape concreteBPNativeRankCloseTraceSegmentBase pos
  · intro blockSize close
    exact
      concreteBPNativeLocalBPWindowBitsTraceResult_events_readWord
        shape blockSize close
  · intro blockSize close seed
    exact
      SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedLeftFringeCandidateSeededTraceResultAtSegment_trace_forall
        shape concreteBPNativeFringeChunkTraceSegment blockSize close seed
        WordRAM.TraceEvent.isReadWord
        (concreteBPNativeLocalBPWindowBitsTraceResult_events_readWord
          shape blockSize close)
        (fun address _hlt => by trivial)
  · intro blockSize close seed
    exact
      SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedRightFringeCandidateSeededTraceResultAtSegment_trace_forall
        shape concreteBPNativeFringeChunkTraceSegment blockSize close seed
        WordRAM.TraceEvent.isReadWord
        (concreteBPNativeLocalBPWindowBitsTraceResult_events_readWord
          shape blockSize close)
        (fun address _hlt => by trivial)
  · intro startBlock count
    exact
      concreteBPNativeInteriorGlobalWordTraceResultAllSizeStructural_events_readWord
        shape startBlock count

private theorem WholeQueryInstr.evalGlobalWordTrace_events_readWord
    (shape : Cartesian.CartesianShape)
    (left right : Nat) (instr : WholeQueryInstr)
    (state : WholeQueryState) :
    forall event,
      event ∈ (instr.evalGlobalWordTrace shape left right state).trace ->
        event.isReadWord := by
  cases instr with
  | selectClose dst idx =>
      simp [WholeQueryInstr.evalGlobalWordTrace]
      exact
        concreteBPNativeChunkedSelectCloseGlobalWordTraceResult_events_readWord
          shape (idx.eval left right state)
  | lcaClose dst leftReg rightReg =>
      cases hleft : state.opt leftReg with
      | none =>
          cases hright : state.opt rightReg <;>
            simp [WholeQueryInstr.evalGlobalWordTrace, hleft, hright] <;>
            intro event hmem <;> cases hmem
      | some leftClose =>
          cases hright : state.opt rightReg with
          | none =>
              simp [WholeQueryInstr.evalGlobalWordTrace, hleft, hright]
          | some rightClose =>
              simp [WholeQueryInstr.evalGlobalWordTrace, hleft, hright]
              exact
                concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural_events_readWord
                  shape leftClose rightClose
  | rankCloseIfSome dst guard pos =>
      cases hguard : state.opt guard with
      | none =>
          simp [WholeQueryInstr.evalGlobalWordTrace, hguard]
      | some _ =>
          simp [WholeQueryInstr.evalGlobalWordTrace, hguard]
          exact
            concreteBPNativeRankCloseWordTraceResultAtSegment_events_readWord
              shape concreteBPNativeRankCloseTraceSegmentBase
              (pos.eval left right state)
  | outputPredIfSome dst guard src =>
      cases hguard : state.opt guard <;>
        simp [WholeQueryInstr.evalGlobalWordTrace, hguard] <;>
        intro event hmem <;> cases hmem

private theorem WholeQueryProgram.evalGlobalWordTrace_events_readWord
    (shape : Cartesian.CartesianShape)
    (left right : Nat)
    (program : WholeQueryProgram) (state : WholeQueryState) :
    forall event,
      event ∈
          (WholeQueryProgram.evalGlobalWordTrace
            shape left right program state).trace ->
        event.isReadWord := by
  induction program generalizing state with
  | nil =>
      simp [WholeQueryProgram.evalGlobalWordTrace]
  | cons instr rest ih =>
      unfold WholeQueryProgram.evalGlobalWordTrace
      apply WordRAM.TraceResult.bind_trace_forall
      · exact
          WholeQueryInstr.evalGlobalWordTrace_events_readWord
            shape left right instr state
      · exact ih
          (instr.evalGlobalWordTrace shape left right state).value

/--
The B3 vocabulary theorem (the B-campaign signature result): every event of
the accepted whole-query global word trace is a `readWord` constructor.  No
`wordRank`, `wordSelect`, or synthetic marker survives on the accepted
route: every charged unit is a genuine payload-store read.  Universal over
all shapes and query endpoints, over the same trace object named by the
cost and adequacy theorems.
-/
theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_readWord_only
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    forall event,
      event ∈
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
            shape left right).trace ->
        event.isReadWord := by
  intro event hmem
  unfold concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult at hmem
  exact
    WordRAM.TraceResult.map_trace_forall
      WordRAM.TraceEvent.isReadWord WholeQueryState.output?
      (WholeQueryProgram.evalGlobalWordTrace
        shape left right concreteBPNativeSuccinctRMQWholeQueryProgram
        WholeQueryState.empty)
      (WholeQueryProgram.evalGlobalWordTrace_events_readWord
        shape left right concreteBPNativeSuccinctRMQWholeQueryProgram
        WholeQueryState.empty)
      event hmem

/-- The canonical transitional whole-query cap computes to 328 modeled ticks. -/
theorem concreteBPNativeSuccinctRMQCanonicalTransitionalQueryCost_eq :
    3 * SuccinctSelect.sparseDenseFalseSelectQueryCost +
        SuccinctClose.ConcreteCompactBPCloseLCADirectory.canonicalCompactBPCloseQueryCostWithRankSeed
          SuccinctSelect.sparseDenseFalseSelectQueryCost =
      328 := by
  rfl

/-- Compatibility with the older conservative aggregate bound. -/
theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_le
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
      shape left right).cost <=
        concreteBPNativeSuccinctRMQQueryCost
          SuccinctSelect.sparseDenseFalseSelectQueryCost := by
  exact Nat.le_trans
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_le_canonicalTransitional
      shape left right)
    (by
      rw [concreteBPNativeSuccinctRMQCanonicalTransitionalQueryCost_eq,
        concreteBPNativeSuccinctRMQQueryCost_eq]
      omega)

/-- Legacy 118 bound for the pre-canonical interpreted route. -/
theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedLegacy_cost_le_of_ready
    (shape : Cartesian.CartesianShape)
    (hready : SuccinctClose.concreteBPRelativeRmmInteriorReady shape)
    (left right : Nat) :
    (concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted
      shape left right).cost <=
        concreteBPNativeSuccinctRMQFastRegimeQueryCost :=
  concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted_cost_le_of_ready
    shape hready left right

/-- Legacy threshold corollary for the pre-canonical interpreted route. -/
theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedLegacy_cost_le_of_size_ge_readyThreshold
    (shape : Cartesian.CartesianShape)
    (hsize :
      SuccinctClose.concreteBPRelativeRmmInteriorReadyThreshold <=
        shape.size)
    (left right : Nat) :
    (concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted
      shape left right).cost <=
        concreteBPNativeSuccinctRMQFastRegimeQueryCost :=
  concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted_cost_le_of_ready
    shape
    (SuccinctClose.concreteBPRelativeRmmInteriorReady_of_size_ge_readyThreshold
      shape hsize)
    left right

/-- Legacy route-split bound for the pre-canonical interpreted route. -/
theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedLegacy_cost_le_routeSplit
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    (concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted
      shape left right).cost <=
        concreteBPNativeSuccinctRMQRouteSplitQueryCost shape :=
  concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted_cost_le_routeSplit
    shape left right

/-- The principled U3 cap implies the older clean all-size envelope. -/
theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_le_cleanAllSize
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
      shape left right).cost <=
        concreteBPNativeSuccinctRMQCleanAllSizeQueryCost := by
  exact Nat.le_trans
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_le_principledAllSizeChargedTrace
      shape left right)
    (by
      rw [concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost_eq,
        concreteBPNativeSuccinctRMQCleanAllSizeQueryCost_eq]
      omega)

theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_exact
    {n : Nat} {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    {left len : Nat} (hlen : 0 < len) (hbound : left + len <= n) :
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
      shape left (left + len)).erase =
        some (scanWindow shape.representative left len) := by
  rw [
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_refines_canonicalInterpretedCosted]
  exact
    concreteBPNativeSuccinctRMQWholeQueryCanonicalInterpretedCosted_exact
      hshape hlen hbound

/--
Canonical construction-facing two-sided profile for the accepted reviewer
payload and execution.  The space clause counts exactly the payload erased by
the physical reviewer words, while every query clause names the canonical
global trace whose non-synthetic certificate weight equals its `Costed.cost`
and is bounded by `207`.

The numeric lower comparisons are space envelopes.  The query bound remains
scoped to the explicit charged-trace model; this theorem does not charge
controller operations or assert conventional word-RAM complexity.
-/
theorem concreteBPNativeSuccinctRMQCanonicalReviewerPayload_globalWordTrace_two_sided_profile :
    SuccinctSpace.LittleOLinear
        concreteBPNativeSuccinctRMQCanonicalReviewerOverhead /\
      concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost = 207 /\
      forall n : Nat,
        EncodingLowerBound.doubledLogSlackLower n <=
          2 *
            (2 * n +
              concreteBPNativeSuccinctRMQCanonicalReviewerOverhead n) /\
        EncodingLowerBound.logSlackLower n <=
          2 * n +
            concreteBPNativeSuccinctRMQCanonicalReviewerOverhead n /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            (concreteBPNativeSuccinctRMQCanonicalReviewerPayload
              shape).length <=
              2 * n +
                concreteBPNativeSuccinctRMQCanonicalReviewerOverhead n) /\
        (forall shape : Cartesian.CartesianShape,
          SuccinctSpace.flattenPayloadWords
              (concreteBPNativeSuccinctRMQReviewerPhysicalWords shape) =
            concreteBPNativeSuccinctRMQCanonicalReviewerPayload shape) /\
        (forall shape left right {segment index : Nat} {word : List Bool},
          WordRAM.TraceEvent.readWord segment index (some word) ∈
              (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
                shape left right).trace ->
            let address :=
              concreteBPNativeSuccinctRMQReviewerPhysicalAddress
                shape segment index
            address <
                (concreteBPNativeSuccinctRMQReviewerPhysicalWords shape).length /\
              (concreteBPNativeSuccinctRMQReviewerPhysicalWords shape)[address]? =
                some word) /\
        (forall shape left right event,
          event ∈
              (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
                shape left right).trace ->
            (Exists fun segment : Nat => Exists fun index : Nat =>
              Exists fun word? : Option WordRAM.Word =>
                event = WordRAM.TraceEvent.readWord segment index word?) \/
            (Exists fun target : Bool => Exists fun limit : Nat =>
              Exists fun result : Nat =>
                event = WordRAM.TraceEvent.wordRank target limit result) \/
            (Exists fun target : Bool => Exists fun occurrence : Nat =>
              Exists fun result : Option Nat =>
                event = WordRAM.TraceEvent.wordSelect target occurrence result)) /\
        (forall shape left right,
          WordRAM.TraceEvent.syntheticCostOnlyPrimitive ∉
            (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
              shape left right).trace) /\
        (forall shape left right,
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
            shape left right).cost <= 207) /\
        (forall shape left right,
          ((concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
              shape left right).trace.map
              WordRAM.TraceEvent.nonSyntheticWeight).sum =
              (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
                shape left right).trace.length /\
          ((concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
              shape left right).trace.map
              WordRAM.TraceEvent.nonSyntheticWeight).sum =
              (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
                shape left right).cost /\
          ((concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
              shape left right).trace.map
              WordRAM.TraceEvent.nonSyntheticWeight).sum <= 207) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            forall {left len : Nat},
              0 < len ->
                left + len <= n ->
                  (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
                    shape left (left + len)).erase =
                    some (scanWindow shape.representative left len)) := by
  refine
    ⟨concreteBPNativeSuccinctRMQCanonicalReviewerOverhead_littleO,
      concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost_eq, ?_⟩
  intro n
  have hdoubledBase :
      EncodingLowerBound.doubledLogSlackLower n <= 2 * (2 * n) :=
    (EncodingLowerBound.exactRMQ_tight_fixed_length_payload_space_bound_doubled_catalan_slack
      n).1 (EncodingLowerBound.canonicalRepresentativeStateEncoding n)
  have hsingleBase : EncodingLowerBound.logSlackLower n <= 2 * n :=
    EncodingLowerBound.canonicalRepresentativePayloadSpaceBounds_lower_le_upper n
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Nat.le_trans hdoubledBase (by omega)
  · exact Nat.le_trans hsingleBase (by omega)
  · intro shape hshape
    exact concreteBPNativeSuccinctRMQCanonicalReviewerPayload_length_le hshape
  · intro shape
    exact concreteBPNativeSuccinctRMQReviewerPhysicalWords_erases shape
  · intro shape left right segment index word hmem
    apply concreteBPNativeSuccinctRMQReviewerSuccessfulRead_physical
    have hmatch :=
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_matchesReadStore
        shape left right
        (WordRAM.TraceEvent.readWord segment index (some word)) hmem
    simpa [WordRAM.TraceEvent.matchesReadStore] using hmatch
  · intro shape left right event hmem
    exact
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_event_readWord_or_wordRank_or_wordSelect
        shape left right event hmem
  · intro shape left right
    exact
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_syntheticCostOnlyPrimitive_not_mem
        shape left right
  · intro shape left right
    simpa [concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost_eq] using
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_le_principledAllSizeChargedTrace
        shape left right
  · intro shape left right
    exact
      ⟨concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_nonSyntheticWeight_sum_eq_trace_length
          shape left right,
        concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_nonSyntheticWeight_sum_eq_cost
          shape left right,
        concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_nonSyntheticWeight_sum_le_207
          shape left right⟩
  · intro shape hshape left len hlen hbound
    exact concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_exact
      hshape hlen hbound

theorem concreteBPNativeSuccinctRMQWholeQueryWordTraceCostedOfSizeGe_cost_le
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (left right : Nat) :
    (concreteBPNativeSuccinctRMQWholeQueryWordTraceCostedOfSizeGe
      shape hsize left right).cost <=
        concreteBPNativeSuccinctRMQQueryCost
          SuccinctSelect.sparseDenseFalseSelectQueryCost := by
  rw [
    concreteBPNativeSuccinctRMQWholeQueryWordTraceCostedOfSizeGe_refines_wholeQueryInterpretedCosted]
  exact
    concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted_cost_le
      shape left right

theorem concreteBPNativeSuccinctRMQWholeQueryWordTraceCostedOfSizeGe_exact
    {n : Nat} {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    (hsize : 2 ^ 128 <= shape.size)
    {left len : Nat} (hlen : 0 < len) (hbound : left + len <= n) :
    (concreteBPNativeSuccinctRMQWholeQueryWordTraceCostedOfSizeGe
      shape hsize left (left + len)).erase =
        some (scanWindow shape.representative left len) := by
  rw [
    concreteBPNativeSuccinctRMQWholeQueryWordTraceCostedOfSizeGe_refines_wholeQueryInterpretedCosted]
  exact
    concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted_exact
      hshape hlen hbound

theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedOfSizeGe_cost_le_canonicalTransitional
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (left right : Nat) :
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedOfSizeGe
      shape hsize left right).cost <=
        3 * SuccinctSelect.sparseDenseFalseSelectQueryCost +
          SuccinctClose.ConcreteCompactBPCloseLCADirectory.canonicalCompactBPCloseQueryCostWithRankSeed
            SuccinctSelect.sparseDenseFalseSelectQueryCost := by
  rw [
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedOfSizeGe_refines_canonicalInterpretedCosted]
  exact
    concreteBPNativeSuccinctRMQWholeQueryCanonicalInterpretedCosted_cost_le
      shape left right

theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedOfSizeGe_cost_le
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size)
    (left right : Nat) :
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedOfSizeGe
      shape hsize left right).cost <=
        concreteBPNativeSuccinctRMQQueryCost
          SuccinctSelect.sparseDenseFalseSelectQueryCost := by
  exact Nat.le_trans
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedOfSizeGe_cost_le_canonicalTransitional
      shape hsize left right)
    (by
      rw [concreteBPNativeSuccinctRMQCanonicalTransitionalQueryCost_eq,
        concreteBPNativeSuccinctRMQQueryCost_eq]
      omega)

theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedOfSizeGe_exact
    {n : Nat} {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    (hsize : 2 ^ 128 <= shape.size)
    {left len : Nat} (hlen : 0 < len) (hbound : left + len <= n) :
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedOfSizeGe
      shape hsize left (left + len)).erase =
        some (scanWindow shape.representative left len) := by
  rw [
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedOfSizeGe_refines_canonicalInterpretedCosted]
  exact
    concreteBPNativeSuccinctRMQWholeQueryCanonicalInterpretedCosted_exact
      hshape hlen hbound

/--
Interpreter-backed two-sided public capstone for the built generic-select
BP-native succinct RMQ path.

This theorem has the same lower-bound, payload, cost, and exactness shape as the
current public generic sparse-exception capstone, but its query clause is the
interpreted query defined in this module.
-/
theorem builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_interpreted_profile :
    SuccinctSpace.LittleOLinear
        (concreteBPNativeSuccinctRMQOverhead
          genericSparseExceptionBPCloseAccessOverhead) /\
      forall n : Nat,
        EncodingLowerBound.doubledLogSlackLower n <=
          2 *
            (2 * n +
              concreteBPNativeSuccinctRMQOverhead
                genericSparseExceptionBPCloseAccessOverhead n) /\
        EncodingLowerBound.logSlackLower n <=
          2 * n +
            concreteBPNativeSuccinctRMQOverhead
              genericSparseExceptionBPCloseAccessOverhead n /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            (builtGenericSparseExceptionSelectBPCloseAccessFamily
              |>.directory shape).payload.length <=
              genericSparseExceptionBPCloseAccessOverhead n) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            (concreteBPNativeSuccinctRMQPayload
              builtGenericSparseExceptionSelectBPCloseAccessFamily
              shape).length =
              2 * n +
                concreteBPNativeSuccinctRMQOverhead
                  genericSparseExceptionBPCloseAccessOverhead n) /\
        (forall shape left right,
          (concreteBPNativeSuccinctRMQQueryInterpretedCosted
            shape left right).cost <=
              concreteBPNativeSuccinctRMQQueryCost
                SuccinctSelect.sparseDenseFalseSelectQueryCost) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            forall {left len : Nat},
              0 < len ->
                left + len <= n ->
                  (concreteBPNativeSuccinctRMQQueryInterpretedCosted
                    shape left (left + len)).erase =
                    some (scanWindow shape.representative left len)) := by
  have h :=
    builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_profile
  dsimp only at h
  constructor
  · exact h.1
  · intro n
    rcases h.2 n with
      ⟨hdoubled, hlog, hpayloadLe, hpayloadLen, hcost, hexact⟩
    exact
      ⟨hdoubled, hlog, hpayloadLe, hpayloadLen,
        (by
          intro shape left right
          exact
            concreteBPNativeSuccinctRMQQueryInterpretedCosted_cost_le
              shape left right),
        (by
          intro shape hshape left len hlen hbound
          exact
            concreteBPNativeSuccinctRMQQueryInterpretedCosted_exact
              hshape hlen hbound)⟩

/--
Whole-query-interpreted two-sided public capstone for the built generic-select
BP-native succinct RMQ path.

This strengthens the interpreted capstone by routing the query-level control
itself through the closed `WholeQueryProgram`; the component leaves are still
the interpreted select-close, compact close/LCA, and register-backed rank
queries.
-/
theorem builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_whole_query_interpreted_profile :
    SuccinctSpace.LittleOLinear
        (concreteBPNativeSuccinctRMQOverhead
          genericSparseExceptionBPCloseAccessOverhead) /\
      forall n : Nat,
        EncodingLowerBound.doubledLogSlackLower n <=
          2 *
            (2 * n +
              concreteBPNativeSuccinctRMQOverhead
                genericSparseExceptionBPCloseAccessOverhead n) /\
        EncodingLowerBound.logSlackLower n <=
          2 * n +
            concreteBPNativeSuccinctRMQOverhead
              genericSparseExceptionBPCloseAccessOverhead n /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            (builtGenericSparseExceptionSelectBPCloseAccessFamily
              |>.directory shape).payload.length <=
              genericSparseExceptionBPCloseAccessOverhead n) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            (concreteBPNativeSuccinctRMQPayload
              builtGenericSparseExceptionSelectBPCloseAccessFamily
              shape).length =
              2 * n +
                concreteBPNativeSuccinctRMQOverhead
                  genericSparseExceptionBPCloseAccessOverhead n) /\
        (forall shape left right,
          (concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted
            shape left right).cost <=
              concreteBPNativeSuccinctRMQQueryCost
                SuccinctSelect.sparseDenseFalseSelectQueryCost) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            forall {left len : Nat},
              0 < len ->
                left + len <= n ->
                  (concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted
                    shape left (left + len)).erase =
                    some (scanWindow shape.representative left len)) := by
  have h :=
    builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_interpreted_profile
  constructor
  · exact h.1
  · intro n
    rcases h.2 n with
      ⟨hdoubled, hlog, hpayloadLe, hpayloadLen, _hcost, _hexact⟩
    exact
      ⟨hdoubled, hlog, hpayloadLe, hpayloadLen,
        (by
          intro shape left right
          exact
            concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted_cost_le
              shape left right),
        (by
          intro shape hshape left len hlen hbound
          exact
            concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted_exact
              hshape hlen hbound)⟩

/--
Leaf-trace-preserving two-sided capstone for the built generic-select
BP-native succinct RMQ path.

This is the next flattening checkpoint after the closed whole-query controller:
the same fixed instruction list now evaluates to a domain-leaf trace before it
is projected back to `Costed`.  The trace still records interpreted leaf
queries, not one unified payload-store trace.
-/
theorem builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_whole_query_leaf_trace_profile :
    SuccinctSpace.LittleOLinear
        (concreteBPNativeSuccinctRMQOverhead
          genericSparseExceptionBPCloseAccessOverhead) /\
      forall n : Nat,
        EncodingLowerBound.doubledLogSlackLower n <=
          2 *
            (2 * n +
              concreteBPNativeSuccinctRMQOverhead
                genericSparseExceptionBPCloseAccessOverhead n) /\
        EncodingLowerBound.logSlackLower n <=
          2 * n +
            concreteBPNativeSuccinctRMQOverhead
              genericSparseExceptionBPCloseAccessOverhead n /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            (builtGenericSparseExceptionSelectBPCloseAccessFamily
              |>.directory shape).payload.length <=
              genericSparseExceptionBPCloseAccessOverhead n) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            (concreteBPNativeSuccinctRMQPayload
              builtGenericSparseExceptionSelectBPCloseAccessFamily
              shape).length =
              2 * n +
                concreteBPNativeSuccinctRMQOverhead
                  genericSparseExceptionBPCloseAccessOverhead n) /\
        (forall shape left right,
          (concreteBPNativeSuccinctRMQWholeQueryLeafTraceCosted
            shape left right).cost <=
              concreteBPNativeSuccinctRMQQueryCost
                SuccinctSelect.sparseDenseFalseSelectQueryCost) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            forall {left len : Nat},
              0 < len ->
                left + len <= n ->
                  (concreteBPNativeSuccinctRMQWholeQueryLeafTraceCosted
                    shape left (left + len)).erase =
                    some (scanWindow shape.representative left len)) := by
  have h :=
    builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_whole_query_interpreted_profile
  constructor
  · exact h.1
  · intro n
    rcases h.2 n with
      ⟨hdoubled, hlog, hpayloadLe, hpayloadLen, _hcost, _hexact⟩
    exact
      ⟨hdoubled, hlog, hpayloadLe, hpayloadLen,
        (by
          intro shape left right
          exact
            concreteBPNativeSuccinctRMQWholeQueryLeafTraceCosted_cost_le
              shape left right),
        (by
          intro shape hshape left len hlen hbound
          exact
            concreteBPNativeSuccinctRMQWholeQueryLeafTraceCosted_exact
              hshape hlen hbound)⟩

/--
Unified-`WordRAM.TraceEvent` two-sided capstone for the built generic-select
BP-native succinct RMQ path.

This keeps the same payload and exactness theorem surface, but the public query
is now evaluated through `WholeQueryProgram.evalWordTrace`. Select-close,
answer-rank, and compact-close rank-seed reads contribute structural
payload/register traces; bounded local/fringe/interior close-navigation leaves
remain explicit charged decoder leaves.
-/
theorem builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_whole_query_word_trace_profile :
    SuccinctSpace.LittleOLinear
        (concreteBPNativeSuccinctRMQOverhead
          genericSparseExceptionBPCloseAccessOverhead) /\
      forall n : Nat,
        EncodingLowerBound.doubledLogSlackLower n <=
          2 *
            (2 * n +
              concreteBPNativeSuccinctRMQOverhead
                genericSparseExceptionBPCloseAccessOverhead n) /\
        EncodingLowerBound.logSlackLower n <=
          2 * n +
            concreteBPNativeSuccinctRMQOverhead
              genericSparseExceptionBPCloseAccessOverhead n /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            (builtGenericSparseExceptionSelectBPCloseAccessFamily
              |>.directory shape).payload.length <=
              genericSparseExceptionBPCloseAccessOverhead n) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            (concreteBPNativeSuccinctRMQPayload
              builtGenericSparseExceptionSelectBPCloseAccessFamily
              shape).length =
              2 * n +
                concreteBPNativeSuccinctRMQOverhead
                  genericSparseExceptionBPCloseAccessOverhead n) /\
        (forall shape left right,
          (concreteBPNativeSuccinctRMQWholeQueryWordTraceCosted
            shape left right).cost <=
              concreteBPNativeSuccinctRMQQueryCost
                SuccinctSelect.sparseDenseFalseSelectQueryCost) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            forall {left len : Nat},
              0 < len ->
                left + len <= n ->
                  (concreteBPNativeSuccinctRMQWholeQueryWordTraceCosted
                    shape left (left + len)).erase =
                    some (scanWindow shape.representative left len)) := by
  have h :=
    builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_whole_query_interpreted_profile
  constructor
  · exact h.1
  · intro n
    rcases h.2 n with
      ⟨hdoubled, hlog, hpayloadLe, hpayloadLen, _hcost, _hexact⟩
    exact
      ⟨hdoubled, hlog, hpayloadLe, hpayloadLen,
        (by
          intro shape left right
          exact
            concreteBPNativeSuccinctRMQWholeQueryWordTraceCosted_cost_le
              shape left right),
        (by
          intro shape hshape left len hlen hbound
          exact
            concreteBPNativeSuccinctRMQWholeQueryWordTraceCosted_exact
              hshape hlen hbound)⟩

/--
Large-regime unified-`WordRAM.TraceEvent` two-sided capstone for the built
generic-select BP-native succinct RMQ path.

This is the structural close-navigation strengthening of
`..._whole_query_word_trace_profile`: in the query clauses, the size hypothesis
routes the compact close/LCA leg through the positive-block local/fringe and
relative-rmM interior trace replay rather than through the all-size fallback.
-/
theorem builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_whole_query_word_trace_large_regime_profile :
    SuccinctSpace.LittleOLinear
        (concreteBPNativeSuccinctRMQOverhead
          genericSparseExceptionBPCloseAccessOverhead) /\
      forall n : Nat,
        EncodingLowerBound.doubledLogSlackLower n <=
          2 *
            (2 * n +
              concreteBPNativeSuccinctRMQOverhead
                genericSparseExceptionBPCloseAccessOverhead n) /\
        EncodingLowerBound.logSlackLower n <=
          2 * n +
            concreteBPNativeSuccinctRMQOverhead
              genericSparseExceptionBPCloseAccessOverhead n /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            (builtGenericSparseExceptionSelectBPCloseAccessFamily
              |>.directory shape).payload.length <=
              genericSparseExceptionBPCloseAccessOverhead n) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            (concreteBPNativeSuccinctRMQPayload
              builtGenericSparseExceptionSelectBPCloseAccessFamily
              shape).length =
              2 * n +
                concreteBPNativeSuccinctRMQOverhead
                  genericSparseExceptionBPCloseAccessOverhead n) /\
        (forall (shape : Cartesian.CartesianShape),
          (hsize : 2 ^ 128 <= shape.size) ->
            forall left right,
              (concreteBPNativeSuccinctRMQWholeQueryWordTraceCostedOfSizeGe
                shape hsize left right).cost <=
                  concreteBPNativeSuccinctRMQQueryCost
                    SuccinctSelect.sparseDenseFalseSelectQueryCost) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            (hsize : 2 ^ 128 <= shape.size) ->
              forall {left len : Nat},
                0 < len ->
                  left + len <= n ->
                    (concreteBPNativeSuccinctRMQWholeQueryWordTraceCostedOfSizeGe
                      shape hsize left (left + len)).erase =
                      some (scanWindow shape.representative left len)) := by
  have h :=
    builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_whole_query_interpreted_profile
  constructor
  · exact h.1
  · intro n
    rcases h.2 n with
      ⟨hdoubled, hlog, hpayloadLe, hpayloadLen, _hcost, _hexact⟩
    exact
      ⟨hdoubled, hlog, hpayloadLe, hpayloadLen,
        (by
          intro shape hsize left right
          exact
            concreteBPNativeSuccinctRMQWholeQueryWordTraceCostedOfSizeGe_cost_le
              shape hsize left right),
        (by
          intro shape hshape hsize left len hlen hbound
          exact
            concreteBPNativeSuccinctRMQWholeQueryWordTraceCostedOfSizeGe_exact
              hshape hsize hlen hbound)⟩

/--
Globally segmented large-regime word-trace capstone for the built
generic-select BP-native succinct RMQ path.

This keeps the same two-sided `2*n + o(n)`, constant-query, exactness surface as
the large-regime word-trace capstone, but the query clauses use the relabeled
global-segment trace result.  Payload-read segment IDs are now consistent
across the final query.  The remaining execution-story hardening is the
`matchesReadStore` proof for the concrete global payload store.
-/
theorem builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_whole_query_global_word_trace_large_regime_profile :
    SuccinctSpace.LittleOLinear
        (concreteBPNativeSuccinctRMQOverhead
          genericSparseExceptionBPCloseAccessOverhead) /\
      forall n : Nat,
        EncodingLowerBound.doubledLogSlackLower n <=
          2 *
            (2 * n +
              concreteBPNativeSuccinctRMQOverhead
                genericSparseExceptionBPCloseAccessOverhead n) /\
        EncodingLowerBound.logSlackLower n <=
          2 * n +
            concreteBPNativeSuccinctRMQOverhead
              genericSparseExceptionBPCloseAccessOverhead n /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            (builtGenericSparseExceptionSelectBPCloseAccessFamily
              |>.directory shape).payload.length <=
              genericSparseExceptionBPCloseAccessOverhead n) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            (concreteBPNativeSuccinctRMQPayload
              builtGenericSparseExceptionSelectBPCloseAccessFamily
              shape).length =
              2 * n +
                concreteBPNativeSuccinctRMQOverhead
                  genericSparseExceptionBPCloseAccessOverhead n) /\
        (forall (shape : Cartesian.CartesianShape),
          (hsize : 2 ^ 128 <= shape.size) ->
            forall left right,
              (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedOfSizeGe
                shape hsize left right).cost <=
                  concreteBPNativeSuccinctRMQQueryCost
                    SuccinctSelect.sparseDenseFalseSelectQueryCost) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            (hsize : 2 ^ 128 <= shape.size) ->
              forall {left len : Nat},
                0 < len ->
                  left + len <= n ->
                    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedOfSizeGe
                      shape hsize left (left + len)).erase =
                      some (scanWindow shape.representative left len)) := by
  have h :=
    builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_whole_query_interpreted_profile
  constructor
  · exact h.1
  · intro n
    rcases h.2 n with
      ⟨hdoubled, hlog, hpayloadLe, hpayloadLen, _hcost, _hexact⟩
    exact
      ⟨hdoubled, hlog, hpayloadLe, hpayloadLen,
        (by
          intro shape hsize left right
          exact
            concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedOfSizeGe_cost_le
              shape hsize left right),
        (by
          intro shape hshape hsize left len hlen hbound
          exact
            concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedOfSizeGe_exact
              hshape hsize hlen hbound)⟩

/-! ### Compatibility translation scaffold for the later flat physical machine -/

/-- The canonical pre-execution physical store has one segment: the flat word
array whose erasure is the public payload. -/
def concreteBPNativeSuccinctRMQReviewerPhysicalReadStore
    (shape : Cartesian.CartesianShape) : WordRAM.ReadStore where
  readWord? segment address :=
    if segment = 0 then
      (concreteBPNativeSuccinctRMQReviewerPhysicalWords shape)[address]?
    else none

/-- Translate a logical segmented event to its checked flat physical address.
The returned `word?` is preserved, including `none`, and primitives are left
unchanged. -/
def concreteBPNativeSuccinctRMQReviewerPhysicalizeEvent
    (shape : Cartesian.CartesianShape) :
    WordRAM.TraceEvent -> WordRAM.TraceEvent
  | WordRAM.TraceEvent.readWord segment index word? =>
      WordRAM.TraceEvent.readWord 0
        (concreteBPNativeSuccinctRMQReviewerPhysicalAddress
          shape segment index) word?
  | WordRAM.TraceEvent.wordRank target limit result =>
      WordRAM.TraceEvent.wordRank target limit result
  | WordRAM.TraceEvent.wordSelect target occurrence result =>
      WordRAM.TraceEvent.wordSelect target occurrence result
  | WordRAM.TraceEvent.syntheticCostOnlyPrimitive =>
      WordRAM.TraceEvent.syntheticCostOnlyPrimitive

/--
Compatibility-only post-hoc translation scaffold.  This copies the logical
value and relabels its trace; it is not the reviewer-facing physical execution.
The genuine supplied-flat-store evaluator is
`concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore` in
`SuccinctFinalStoreParam`.
-/
def concreteBPNativeSuccinctRMQWholeQueryReviewerPhysicalTraceResult
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    WordRAM.TraceResult (Option Nat) where
  value :=
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
      shape left right).value
  trace :=
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
      shape left right).trace.map
        (concreteBPNativeSuccinctRMQReviewerPhysicalizeEvent shape)

/-- Compatibility translated-trace footprint.  The genuine execution-derived
physical footprint lives in `SuccinctFinalStoreParam`. -/
def concreteBPNativeSuccinctRMQWholeQueryReviewerPhysicalFootprint
    (shape : Cartesian.CartesianShape) (left right : Nat) : List Nat :=
  (concreteBPNativeSuccinctRMQWholeQueryReviewerPhysicalTraceResult
      shape left right).trace.filterMap fun event =>
    match event with
    | WordRAM.TraceEvent.readWord 0 address _ => some address
    | WordRAM.TraceEvent.readWord _ _ _ => none
    | _ => none

theorem concreteBPNativeSuccinctRMQWholeQueryReviewerPhysicalFootprint_recorded
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryReviewerPhysicalFootprint
        shape left right =
      (concreteBPNativeSuccinctRMQWholeQueryReviewerPhysicalTraceResult
          shape left right).trace.filterMap fun event =>
        match event with
        | WordRAM.TraceEvent.readWord 0 address _ => some address
        | WordRAM.TraceEvent.readWord _ _ _ => none
        | _ => none := by
  rfl

theorem concreteBPNativeSuccinctRMQReviewerPhysicalizeEvent_matchesReadStore
    (shape : Cartesian.CartesianShape) (event : WordRAM.TraceEvent)
    (hmatch : event.matchesReadStore
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)) :
    (concreteBPNativeSuccinctRMQReviewerPhysicalizeEvent shape event)
      |>.matchesReadStore
        (concreteBPNativeSuccinctRMQReviewerPhysicalReadStore shape) := by
  cases event with
  | readWord segment index word? =>
      simp only [concreteBPNativeSuccinctRMQReviewerPhysicalizeEvent,
        WordRAM.TraceEvent.matchesReadStore,
        concreteBPNativeSuccinctRMQReviewerPhysicalReadStore, if_pos]
      rw [← concreteBPNativeSuccinctRMQGlobalReadStore_eq_reviewerPhysical]
      exact hmatch
  | wordRank target limit result => trivial
  | wordSelect target occurrence result => trivial
  | syntheticCostOnlyPrimitive => trivial

theorem concreteBPNativeSuccinctRMQWholeQueryReviewerPhysicalTraceResult_matchesReadStore
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    forall event,
      event ∈
          (concreteBPNativeSuccinctRMQWholeQueryReviewerPhysicalTraceResult
            shape left right).trace ->
        event.matchesReadStore
          (concreteBPNativeSuccinctRMQReviewerPhysicalReadStore shape) := by
  intro event hmem
  simp only [concreteBPNativeSuccinctRMQWholeQueryReviewerPhysicalTraceResult,
    List.mem_map] at hmem
  rcases hmem with ⟨logical, hlogical, rfl⟩
  apply concreteBPNativeSuccinctRMQReviewerPhysicalizeEvent_matchesReadStore
  exact concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_matchesReadStore
    shape left right logical hlogical

/-- Full segmented-to-flat refinement. It preserves the decoded result, cost,
ordered trace (modulo the explicit address translation), and every success or
failure result carried by a read event. -/
theorem concreteBPNativeSuccinctRMQWholeQueryReviewerPhysical_refines_logical
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    (concreteBPNativeSuccinctRMQWholeQueryReviewerPhysicalTraceResult
        shape left right).value =
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).value /\
    (concreteBPNativeSuccinctRMQWholeQueryReviewerPhysicalTraceResult
        shape left right).trace =
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).trace.map
          (concreteBPNativeSuccinctRMQReviewerPhysicalizeEvent shape) /\
    (concreteBPNativeSuccinctRMQWholeQueryReviewerPhysicalTraceResult
        shape left right).toCosted =
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).toCosted /\
    (forall segment index word?,
      WordRAM.TraceEvent.readWord segment index word? ∈
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
            shape left right).trace ->
        WordRAM.TraceEvent.readWord 0
            (concreteBPNativeSuccinctRMQReviewerPhysicalAddress
              shape segment index) word? ∈
          (concreteBPNativeSuccinctRMQWholeQueryReviewerPhysicalTraceResult
            shape left right).trace) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · simp [concreteBPNativeSuccinctRMQWholeQueryReviewerPhysicalTraceResult,
      WordRAM.TraceResult.toCosted, WordRAM.TraceResult.steps]
  · intro segment index word? hmem
    simp only [concreteBPNativeSuccinctRMQWholeQueryReviewerPhysicalTraceResult,
      List.mem_map]
    exact ⟨WordRAM.TraceEvent.readWord segment index word?, hmem, rfl⟩

/-- Every successful physical read is an in-range positional read from the one
pre-execution physical array. -/
theorem concreteBPNativeSuccinctRMQWholeQueryReviewerPhysical_successful_read_backed
    (shape : Cartesian.CartesianShape) (left right : Nat)
    {address : Nat} {word : List Bool}
    (hmem : WordRAM.TraceEvent.readWord 0 address (some word) ∈
      (concreteBPNativeSuccinctRMQWholeQueryReviewerPhysicalTraceResult
        shape left right).trace) :
    address <
        (concreteBPNativeSuccinctRMQReviewerPhysicalWords shape).length /\
      (concreteBPNativeSuccinctRMQReviewerPhysicalWords shape)[address]? =
        some word := by
  have hmatch :=
    concreteBPNativeSuccinctRMQWholeQueryReviewerPhysicalTraceResult_matchesReadStore
      shape left right (WordRAM.TraceEvent.readWord 0 address (some word)) hmem
  have hread :
      (concreteBPNativeSuccinctRMQReviewerPhysicalWords shape)[address]? =
        some word := by
    simpa [WordRAM.TraceEvent.matchesReadStore,
      concreteBPNativeSuccinctRMQReviewerPhysicalReadStore] using hmatch
  exact ⟨(List.getElem?_eq_some_iff.mp hread).1, hread⟩

theorem concreteBPNativeSuccinctRMQWholeQueryReviewerPhysicalTraceResult_primitiveOperandsFit_reviewerWordBits
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    forall event,
      event ∈
          (concreteBPNativeSuccinctRMQWholeQueryReviewerPhysicalTraceResult
            shape left right).trace ->
        concreteBPNativeTraceEventPrimitiveOperandsFitInBits
          (concreteBPNativeSuccinctRMQReviewerWordBits shape.size) event := by
  intro event hmem
  simp only [concreteBPNativeSuccinctRMQWholeQueryReviewerPhysicalTraceResult,
    List.mem_map] at hmem
  rcases hmem with ⟨logical, hlogical, rfl⟩
  have hfit :=
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_primitiveOperandsFit_reviewerWordBits
      shape left right logical hlogical
  cases logical <;>
    simp [concreteBPNativeSuccinctRMQReviewerPhysicalizeEvent,
      concreteBPNativeTraceEventPrimitiveOperandsFitInBits] at hfit ⊢ <;>
    exact hfit

/-- Every address in the ordered footprint actually consumed by the flat
reviewer execution fits the one query-independent reviewer word width. -/
theorem concreteBPNativeSuccinctRMQWholeQueryReviewerPhysicalFootprint_address_fits_reviewerWordBits
    (shape : Cartesian.CartesianShape) (left right address : Nat)
    (hmem :
      address ∈
        concreteBPNativeSuccinctRMQWholeQueryReviewerPhysicalFootprint
          shape left right) :
    address <
      2 ^ concreteBPNativeSuccinctRMQReviewerWordBits shape.size := by
  unfold concreteBPNativeSuccinctRMQWholeQueryReviewerPhysicalFootprint at hmem
  simp only [List.mem_filterMap] at hmem
  rcases hmem with ⟨event, hevent, hproject⟩
  cases event with
  | readWord segment index word? =>
      cases segment with
      | zero =>
          simp only at hproject
          cases hproject
          simp only [
            concreteBPNativeSuccinctRMQWholeQueryReviewerPhysicalTraceResult,
            List.mem_map] at hevent
          rcases hevent with ⟨logical, hlogical, heq⟩
          cases logical with
          | readWord logicalSegment logicalIndex logicalWord? =>
              simp only [
                concreteBPNativeSuccinctRMQReviewerPhysicalizeEvent,
                WordRAM.TraceEvent.readWord.injEq] at heq
              rcases heq with ⟨_, rfl, _⟩
              exact concreteBPNativeSuccinctRMQReviewerPhysicalAddress_fits
                shape logicalSegment logicalIndex
          | wordRank target limit result =>
              simp [concreteBPNativeSuccinctRMQReviewerPhysicalizeEvent] at heq
          | wordSelect target occurrence result =>
              simp [concreteBPNativeSuccinctRMQReviewerPhysicalizeEvent] at heq
          | syntheticCostOnlyPrimitive =>
              simp [concreteBPNativeSuccinctRMQReviewerPhysicalizeEvent] at heq
      | succ segment => simp at hproject
  | wordRank target limit result => simp at hproject
  | wordSelect target occurrence result => simp at hproject
  | syntheticCostOnlyPrimitive => simp at hproject

end SuccinctFinal
end RMQ
