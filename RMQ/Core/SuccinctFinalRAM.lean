import RMQ.Core.SuccinctFinal.RAM.FlatPayload

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

/-- Interpreted close-select leg for the built generic sparse-exception source. -/
def concreteBPNativeSelectCloseInterpretedCosted
    (shape : Cartesian.CartesianShape)
    (idx : Nat) : Costed (Option Nat) :=
  (GenericSelect.sparseExceptionSelectData shape.bpCode false)
    |>.selectInterpretedCosted idx

/-- Interpreted false-rank leg for the built BP-close rank component. -/
def concreteBPNativeRankCloseInterpretedCosted
    (shape : Cartesian.CartesianShape)
    (pos : Nat) : Costed Nat :=
  (builtRelativeSplitBPCloseRankData shape)
    |>.rankRegisterInterpretedCosted false pos

/-- Structural `WordRAM.TraceEvent` replay for the close-select leg. -/
def concreteBPNativeSelectCloseWordTraceResult
    (shape : Cartesian.CartesianShape)
    (idx : Nat) : WordRAM.TraceResult (Option Nat) :=
  (GenericSelect.sparseExceptionSelectData shape.bpCode false)
    |>.selectTraceResult idx

theorem concreteBPNativeSelectCloseWordTraceResult_refines_interpretedCosted
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    (concreteBPNativeSelectCloseWordTraceResult shape idx).toCosted =
      concreteBPNativeSelectCloseInterpretedCosted shape idx := by
  simp [concreteBPNativeSelectCloseWordTraceResult,
    concreteBPNativeSelectCloseInterpretedCosted,
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
Close-select trace with payload-read segments shifted into the final global
layout.  The packed BP-code reads remain at segment `0` so the final query can
share one BP-code payload segment instead of copying the code per component.
-/
def concreteBPNativeSelectCloseGlobalWordTraceResult
    (shape : Cartesian.CartesianShape)
    (idx : Nat) : WordRAM.TraceResult (Option Nat) :=
  (GenericSelect.sparseExceptionSelectData shape.bpCode false)
    |>.selectTraceResultRelabeled
      concreteBPNativeSelectCloseTraceSegmentLayout idx

theorem concreteBPNativeSelectCloseGlobalWordTraceResult_refines_interpretedCosted
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    (concreteBPNativeSelectCloseGlobalWordTraceResult shape idx).toCosted =
      concreteBPNativeSelectCloseInterpretedCosted shape idx := by
  simp [concreteBPNativeSelectCloseGlobalWordTraceResult,
    concreteBPNativeSelectCloseInterpretedCosted,
    GenericSelect.SparseExceptionSelectData.selectTraceResultRelabeled_refines_interpretedCosted]

theorem concreteBPNativeSelectCloseGlobalWordTraceResult_matchesReadStore
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    forall event,
      event ∈
          (concreteBPNativeSelectCloseGlobalWordTraceResult shape idx).trace ->
        event.matchesReadStore
          (concreteBPNativeSuccinctRMQGlobalReadStore shape) := by
  let data := GenericSelect.sparseExceptionSelectData shape.bpCode false
  change forall event,
      event ∈
          (data.selectTraceResultRelabeled
            concreteBPNativeSelectCloseTraceSegmentLayout idx).trace ->
        event.matchesReadStore
          (concreteBPNativeSuccinctRMQGlobalReadStore shape)
  apply
    GenericSelect.SparseExceptionSelectData.selectTraceResultRelabeled_trace_forall
      data concreteBPNativeSelectCloseTraceSegmentLayout idx
      (fun event =>
        event.matchesReadStore
          (concreteBPNativeSuccinctRMQGlobalReadStore shape))
  · intro slot event hmem
    exact
      data.superTable.readTraceResultRelabeled_matchesReadStore
        concreteBPNativeSelectCloseTraceSegmentLayout.superTable
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (by
          intro segment index
          cases segment <;>
            simp [data, concreteBPNativeSuccinctRMQGlobalReadStore,
              concreteBPNativeSelectCloseTraceSegmentLayout,
              concreteBPNativeDeadTraceSegment,
              WordRAM.singletonSegmentMap,
              WordRAM.TraceEvent.singletonSegmentMap,
              SuccinctSpace.FixedWidthNatTable.wordRAMStore,
              SuccinctSpace.PayloadWordStore.wordRAMStore,
              WordRAM.Store.readWord?])
        (by
          intro segment index
          cases segment <;>
            simp [data, concreteBPNativeSuccinctRMQGlobalReadStore,
              concreteBPNativeSelectCloseTraceSegmentLayout,
              concreteBPNativeDeadTraceSegment,
              WordRAM.singletonSegmentMap,
              WordRAM.TraceEvent.singletonSegmentMap,
              SuccinctSpace.FixedWidthNatTable.wordRAMStore,
              SuccinctSpace.PayloadWordStore.wordRAMStore,
              WordRAM.Store.readWord?])
        (by
          intro segment index
          cases segment <;>
            simp [data, concreteBPNativeSuccinctRMQGlobalReadStore,
              concreteBPNativeSelectCloseTraceSegmentLayout,
              concreteBPNativeDeadTraceSegment,
              WordRAM.singletonSegmentMap,
              WordRAM.TraceEvent.singletonSegmentMap,
              SuccinctSpace.FixedWidthNatTable.wordRAMStore,
              SuccinctSpace.PayloadWordStore.wordRAMStore,
              WordRAM.Store.readWord?])
        (by
          intro segment index
          cases segment <;>
            simp [data, concreteBPNativeSuccinctRMQGlobalReadStore,
              concreteBPNativeSelectCloseTraceSegmentLayout,
              concreteBPNativeDeadTraceSegment,
              WordRAM.singletonSegmentMap,
              WordRAM.TraceEvent.singletonSegmentMap,
              SuccinctSpace.FixedWidthNatTable.wordRAMStore,
              SuccinctSpace.PayloadWordStore.wordRAMStore,
              WordRAM.Store.readWord?])
        slot event hmem
  · intro slot event hmem
    exact
      WordRAM.TraceResult.relabelReadSegmentsWith_matchesReadStore
        (data.longFlagRankData.rankTraceResult true slot)
        (WordRAM.ReadStore.ofStore
          (data.longFlagRankData.rankRegisterWordRAMStore true))
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (WordRAM.tripleSegmentMap
          concreteBPNativeSelectCloseTraceSegmentLayout.longFlagRankBase
          concreteBPNativeSelectCloseTraceSegmentLayout.deadSegment)
        (by
          intro segment index
          cases segment with
          | zero =>
              simp [data, concreteBPNativeSuccinctRMQGlobalReadStore,
                concreteBPNativeSelectCloseTraceSegmentLayout,
                WordRAM.tripleSegmentMap,
                WordRAM.TraceEvent.tripleSegmentMap,
                WordRAM.ReadStore.ofStore]
          | succ segment =>
              cases segment with
              | zero =>
                  simp [data, concreteBPNativeSuccinctRMQGlobalReadStore,
                    concreteBPNativeSelectCloseTraceSegmentLayout,
                    WordRAM.tripleSegmentMap,
                    WordRAM.TraceEvent.tripleSegmentMap,
                    WordRAM.ReadStore.ofStore]
              | succ segment =>
                  cases segment with
                  | zero =>
                      simp [data, concreteBPNativeSuccinctRMQGlobalReadStore,
                        concreteBPNativeSelectCloseTraceSegmentLayout,
                        WordRAM.tripleSegmentMap,
                        WordRAM.TraceEvent.tripleSegmentMap,
                        WordRAM.ReadStore.ofStore]
                  | succ segment =>
                      simp [data, concreteBPNativeSuccinctRMQGlobalReadStore,
                        concreteBPNativeSelectCloseTraceSegmentLayout,
                        concreteBPNativeDeadTraceSegment,
                        WordRAM.tripleSegmentMap,
                        WordRAM.TraceEvent.tripleSegmentMap,
                        WordRAM.ReadStore.ofStore,
                        SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.rankRegisterWordRAMStore,
                        WordRAM.Store.readWord?])
        (data.longFlagRankData.rankTraceResult_matchesReadStore true slot)
        event hmem
  · intro base slot event hmem
    exact
      GenericSelect.relativeOffsetReadTraceResultRelabeled_matchesReadStore
        concreteBPNativeSelectCloseTraceSegmentLayout.longRelativeBase
        concreteBPNativeSelectCloseTraceSegmentLayout.deadSegment
        data.longSuperRelativeTable
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (by
          intro segment index
          cases segment <;>
            simp [data, concreteBPNativeSuccinctRMQGlobalReadStore,
              concreteBPNativeSelectCloseTraceSegmentLayout,
              concreteBPNativeDeadTraceSegment,
              WordRAM.singletonSegmentMap,
              WordRAM.TraceEvent.singletonSegmentMap,
              SuccinctSpace.FixedWidthNatTable.wordRAMStore,
              SuccinctSpace.PayloadWordStore.wordRAMStore,
              WordRAM.Store.readWord?])
        base slot event hmem
  · intro slot event hmem
    exact
      data.localTable.readTraceResultRelabeled_matchesReadStore
        concreteBPNativeSelectCloseTraceSegmentLayout.localTable
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (by
          intro segment index
          cases segment <;>
            simp [data, concreteBPNativeSuccinctRMQGlobalReadStore,
              concreteBPNativeSelectCloseTraceSegmentLayout,
              concreteBPNativeDeadTraceSegment,
              WordRAM.singletonSegmentMap,
              WordRAM.TraceEvent.singletonSegmentMap,
              SuccinctSpace.FixedWidthNatTable.wordRAMStore,
              SuccinctSpace.PayloadWordStore.wordRAMStore,
              WordRAM.Store.readWord?])
        (by
          intro segment index
          cases segment <;>
            simp [data, concreteBPNativeSuccinctRMQGlobalReadStore,
              concreteBPNativeSelectCloseTraceSegmentLayout,
              concreteBPNativeDeadTraceSegment,
              WordRAM.singletonSegmentMap,
              WordRAM.TraceEvent.singletonSegmentMap,
              SuccinctSpace.FixedWidthNatTable.wordRAMStore,
              SuccinctSpace.PayloadWordStore.wordRAMStore,
              WordRAM.Store.readWord?])
        (by
          intro segment index
          cases segment <;>
            simp [data, concreteBPNativeSuccinctRMQGlobalReadStore,
              concreteBPNativeSelectCloseTraceSegmentLayout,
              concreteBPNativeDeadTraceSegment,
              WordRAM.singletonSegmentMap,
              WordRAM.TraceEvent.singletonSegmentMap,
              SuccinctSpace.FixedWidthNatTable.wordRAMStore,
              SuccinctSpace.PayloadWordStore.wordRAMStore,
              WordRAM.Store.readWord?])
        (by
          intro segment index
          cases segment <;>
            simp [data, concreteBPNativeSuccinctRMQGlobalReadStore,
              concreteBPNativeSelectCloseTraceSegmentLayout,
              concreteBPNativeDeadTraceSegment,
              WordRAM.singletonSegmentMap,
              WordRAM.TraceEvent.singletonSegmentMap,
              SuccinctSpace.FixedWidthNatTable.wordRAMStore,
              SuccinctSpace.PayloadWordStore.wordRAMStore,
              WordRAM.Store.readWord?])
        slot event hmem
  · intro base localSlot localOccurrence event hmem
    exact
      data.sparseDirectory.readTraceResultRelabeled_matchesReadStore
        concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (by
          intro segment index
          cases segment with
          | zero =>
              simp [data, concreteBPNativeSuccinctRMQGlobalReadStore,
                concreteBPNativeSelectCloseTraceSegmentLayout,
                WordRAM.tripleSegmentMap,
                WordRAM.TraceEvent.tripleSegmentMap]
          | succ segment =>
              cases segment with
              | zero =>
                  simp [data, concreteBPNativeSuccinctRMQGlobalReadStore,
                    concreteBPNativeSelectCloseTraceSegmentLayout,
                    WordRAM.tripleSegmentMap,
                    WordRAM.TraceEvent.tripleSegmentMap]
              | succ segment =>
                  cases segment with
                  | zero =>
                      simp [data, concreteBPNativeSuccinctRMQGlobalReadStore,
                        concreteBPNativeSelectCloseTraceSegmentLayout,
                        WordRAM.tripleSegmentMap,
                        WordRAM.TraceEvent.tripleSegmentMap]
                  | succ segment =>
                      simp [data, concreteBPNativeSuccinctRMQGlobalReadStore,
                        concreteBPNativeSelectCloseTraceSegmentLayout,
                        concreteBPNativeDeadTraceSegment,
                        WordRAM.tripleSegmentMap,
                        WordRAM.TraceEvent.tripleSegmentMap,
                        SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.rankRegisterWordRAMStore,
                        WordRAM.Store.readWord?])
        (by
          intro segment index
          cases segment <;>
            simp [data, concreteBPNativeSuccinctRMQGlobalReadStore,
              concreteBPNativeSelectCloseTraceSegmentLayout,
              concreteBPNativeDeadTraceSegment,
              WordRAM.singletonSegmentMap,
              WordRAM.TraceEvent.singletonSegmentMap,
              SuccinctSpace.FixedWidthNatTable.wordRAMStore,
              SuccinctSpace.PayloadWordStore.wordRAMStore,
              WordRAM.Store.readWord?])
        base localSlot localOccurrence event hmem
  · intro basePosition baseOccurrence q event hmem
    exact
      GenericSelect.denseTwoWordSelectTraceResultRelabeled_matchesReadStore
        concreteBPNativeSelectCloseTraceSegmentLayout.bitWordBase
        concreteBPNativeSelectCloseTraceSegmentLayout.deadSegment
        false data.bitWords
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (by
          intro segment index
          cases segment <;>
            simp [data, concreteBPNativeSuccinctRMQGlobalReadStore,
              concreteBPNativeSelectCloseTraceSegmentLayout,
              concreteBPNativeDeadTraceSegment,
              WordRAM.singletonSegmentMap,
              WordRAM.TraceEvent.singletonSegmentMap,
              SuccinctSpace.PayloadWordStore.wordRAMStore,
              WordRAM.Store.readWord?])
        basePosition baseOccurrence q event hmem

theorem concreteBPNativeSelectCloseGlobalWordTraceResult_no_syntheticCostOnlyPrimitive
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    forall event,
      event ∈
          (concreteBPNativeSelectCloseGlobalWordTraceResult shape idx).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  let data := GenericSelect.sparseExceptionSelectData shape.bpCode false
  change forall event,
      event ∈
          (data.selectTraceResultRelabeled
            concreteBPNativeSelectCloseTraceSegmentLayout idx).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive
  apply
    GenericSelect.SparseExceptionSelectData.selectTraceResultRelabeled_trace_forall
      data concreteBPNativeSelectCloseTraceSegmentLayout idx
      (fun event => ¬ event.isSyntheticCostOnlyPrimitive)
  · intro slot event hmem
    exact
      data.superTable.readTraceResultRelabeled_no_syntheticCostOnlyPrimitive
        concreteBPNativeSelectCloseTraceSegmentLayout.superTable slot
        event hmem
  · intro slot event hmem
    exact
      WordRAM.TraceResult.relabelReadSegmentsWith_no_syntheticCostOnlyPrimitive
        (WordRAM.tripleSegmentMap
          concreteBPNativeSelectCloseTraceSegmentLayout.longFlagRankBase
          concreteBPNativeSelectCloseTraceSegmentLayout.deadSegment)
        (data.longFlagRankData.rankTraceResult true slot)
        (data.longFlagRankData.rankTraceResult_no_syntheticCostOnlyPrimitive
          true slot)
        event hmem
  · intro base slot event hmem
    exact
      GenericSelect.relativeOffsetReadTraceResultRelabeled_no_syntheticCostOnlyPrimitive
        concreteBPNativeSelectCloseTraceSegmentLayout.longRelativeBase
        concreteBPNativeSelectCloseTraceSegmentLayout.deadSegment
        data.longSuperRelativeTable base slot event hmem
  · intro slot event hmem
    exact
      data.localTable.readTraceResultRelabeled_no_syntheticCostOnlyPrimitive
        concreteBPNativeSelectCloseTraceSegmentLayout.localTable slot
        event hmem
  · intro base localSlot localOccurrence event hmem
    exact
      data.sparseDirectory.readTraceResultRelabeled_no_syntheticCostOnlyPrimitive
        concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory
        base localSlot localOccurrence event hmem
  · intro basePosition baseOccurrence q event hmem
    exact
      GenericSelect.denseTwoWordSelectTraceResultRelabeled_no_syntheticCostOnlyPrimitive
        concreteBPNativeSelectCloseTraceSegmentLayout.bitWordBase
        concreteBPNativeSelectCloseTraceSegmentLayout.deadSegment
        false data.bitWords basePosition baseOccurrence q event hmem

private theorem
    concreteBPNativeSelectCloseGlobalWordTraceResult_noFiniteSmallInteriorSuccessfulRead
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    forall event,
      List.Mem event
        (concreteBPNativeSelectCloseGlobalWordTraceResult shape idx).trace ->
        concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead
          event := by
  simpa [concreteBPNativeSelectCloseGlobalWordTraceResult] using
    concreteBPNativeSelectCloseTraceResultRelabeled_noFiniteSmallInteriorSuccessfulRead
      shape idx

private theorem
    concreteBPNativeSelectCloseGlobalWordTraceResult_noReadyCloseSuccessfulRead
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    forall event,
      List.Mem event
        (concreteBPNativeSelectCloseGlobalWordTraceResult shape idx).trace ->
        concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead
          event := by
  simpa [concreteBPNativeSelectCloseGlobalWordTraceResult] using
    concreteBPNativeSelectCloseTraceResultRelabeled_noReadyCloseSuccessfulRead
      shape idx

/-- Real register-program trace for the final false-rank leg. -/
def concreteBPNativeRankCloseWordTraceResult
    (shape : Cartesian.CartesianShape)
    (pos : Nat) : WordRAM.TraceResult Nat :=
  WordRAM.TraceResult.ofResult
    (((builtRelativeSplitBPCloseRankData shape)
      |>.rankRegisterProgram false (WordRAM.Register.NatExpr.reg 0)).eval
        ((builtRelativeSplitBPCloseRankData shape)
          |>.rankRegisterWordRAMStore false)
        (WordRAM.Register.RegFile.withNat1 pos))

theorem concreteBPNativeRankCloseWordTraceResult_refines_interpretedCosted
    (shape : Cartesian.CartesianShape) (pos : Nat) :
    (concreteBPNativeRankCloseWordTraceResult shape pos).toCosted =
      concreteBPNativeRankCloseInterpretedCosted shape pos := by
  rfl

/--
Final false-rank trace relabeled into a caller-supplied global segment range.

The value and modeled cost are unchanged; only payload-read segment identifiers
are shifted for later assembly into one global store.
-/
def concreteBPNativeRankCloseWordTraceResultAtSegment
    (shape : Cartesian.CartesianShape)
    (rankSegmentBase pos : Nat) : WordRAM.TraceResult Nat :=
  WordRAM.TraceResult.relabelReadSegmentsWith
    (WordRAM.tripleSegmentMap rankSegmentBase
      concreteBPNativeDeadTraceSegment)
    (concreteBPNativeRankCloseWordTraceResult shape pos)

theorem concreteBPNativeRankCloseWordTraceResultAtSegment_refines_interpretedCosted
    (shape : Cartesian.CartesianShape)
    (rankSegmentBase pos : Nat) :
    (concreteBPNativeRankCloseWordTraceResultAtSegment
      shape rankSegmentBase pos).toCosted =
      concreteBPNativeRankCloseInterpretedCosted shape pos := by
  simp [concreteBPNativeRankCloseWordTraceResultAtSegment,
    concreteBPNativeRankCloseWordTraceResult_refines_interpretedCosted]

theorem concreteBPNativeRankCloseGlobalWordTraceResult_matchesReadStore
    (shape : Cartesian.CartesianShape) (pos : Nat) :
    forall event,
      event ∈
          (concreteBPNativeRankCloseWordTraceResultAtSegment
            shape concreteBPNativeRankCloseTraceSegmentBase pos).trace ->
        event.matchesReadStore
          (concreteBPNativeSuccinctRMQGlobalReadStoreLegacy shape) := by
  apply
    WordRAM.TraceResult.relabelReadSegmentsWith_matchesReadStore
      (concreteBPNativeRankCloseWordTraceResult shape pos)
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
    simpa [concreteBPNativeRankCloseWordTraceResult,
      WordRAM.TraceResult.ofResult_trace,
      WordRAM.TraceEvent.matchesReadStore_ofStore] using
      WordRAM.Register.NatProgram.eval_reads_subset_payload
        ((builtRelativeSplitBPCloseRankData shape)
          |>.rankRegisterProgram false (WordRAM.Register.NatExpr.reg 0))
        ((builtRelativeSplitBPCloseRankData shape)
          |>.rankRegisterWordRAMStore false)
        (WordRAM.Register.RegFile.withNat1 pos)
        event hmem

theorem concreteBPNativeRankCloseCanonicalGlobalWordTraceResult_matchesReadStore
    (shape : Cartesian.CartesianShape) (pos : Nat) :
    forall event,
      event ∈
          (concreteBPNativeRankCloseWordTraceResultAtSegment
            shape concreteBPNativeRankCloseTraceSegmentBase pos).trace ->
        event.matchesReadStore
          (concreteBPNativeSuccinctRMQGlobalReadStore shape) := by
  apply
    WordRAM.TraceResult.relabelReadSegmentsWith_matchesReadStore
      (concreteBPNativeRankCloseWordTraceResult shape pos)
      (WordRAM.ReadStore.ofStore
        ((builtRelativeSplitBPCloseRankData shape)
          |>.rankRegisterWordRAMStore false))
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (WordRAM.tripleSegmentMap concreteBPNativeRankCloseTraceSegmentBase
        concreteBPNativeDeadTraceSegment)
  case hread =>
    intro segment index
    cases segment with
    | zero =>
        simp [concreteBPNativeSuccinctRMQGlobalReadStore,
          concreteBPNativeSuccinctRMQGlobalReadStore,
          concreteBPNativeRankCloseTraceSegmentBase,
          WordRAM.tripleSegmentMap, WordRAM.TraceEvent.tripleSegmentMap,
          WordRAM.ReadStore.ofStore]
    | succ segment =>
        cases segment with
        | zero =>
            simp [concreteBPNativeSuccinctRMQGlobalReadStore,
              concreteBPNativeSuccinctRMQGlobalReadStore,
              concreteBPNativeRankCloseTraceSegmentBase,
              WordRAM.tripleSegmentMap, WordRAM.TraceEvent.tripleSegmentMap,
              WordRAM.ReadStore.ofStore]
        | succ segment =>
            cases segment with
            | zero =>
                simp [concreteBPNativeSuccinctRMQGlobalReadStore,
                  concreteBPNativeSuccinctRMQGlobalReadStore,
                  concreteBPNativeRankCloseTraceSegmentBase,
                  WordRAM.tripleSegmentMap, WordRAM.TraceEvent.tripleSegmentMap,
                  WordRAM.ReadStore.ofStore]
            | succ segment =>
                simp [concreteBPNativeSuccinctRMQGlobalReadStore,
                  concreteBPNativeSuccinctRMQGlobalReadStore,
                  concreteBPNativeDeadTraceSegment,
                  WordRAM.tripleSegmentMap, WordRAM.TraceEvent.tripleSegmentMap,
                  WordRAM.ReadStore.ofStore,
                  SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.rankRegisterWordRAMStore,
                  WordRAM.Store.readWord?]
  case hresult =>
    intro event hmem
    simpa [concreteBPNativeRankCloseWordTraceResult,
      WordRAM.TraceResult.ofResult_trace,
      WordRAM.TraceEvent.matchesReadStore_ofStore] using
      WordRAM.Register.NatProgram.eval_reads_subset_payload
        ((builtRelativeSplitBPCloseRankData shape)
          |>.rankRegisterProgram false (WordRAM.Register.NatExpr.reg 0))
        ((builtRelativeSplitBPCloseRankData shape)
          |>.rankRegisterWordRAMStore false)
        (WordRAM.Register.RegFile.withNat1 pos)
        event hmem

theorem concreteBPNativeRankCloseGlobalWordTraceResult_no_syntheticCostOnlyPrimitive
    (shape : Cartesian.CartesianShape) (pos : Nat) :
    forall event,
      event ∈
          (concreteBPNativeRankCloseWordTraceResultAtSegment
            shape concreteBPNativeRankCloseTraceSegmentBase pos).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  unfold concreteBPNativeRankCloseWordTraceResultAtSegment
  exact
    WordRAM.TraceResult.relabelReadSegmentsWith_no_syntheticCostOnlyPrimitive
      (WordRAM.tripleSegmentMap concreteBPNativeRankCloseTraceSegmentBase
        concreteBPNativeDeadTraceSegment)
      (concreteBPNativeRankCloseWordTraceResult shape pos)
      (by
        intro event hmem
        simpa [concreteBPNativeRankCloseWordTraceResult,
          WordRAM.TraceResult.ofResult_trace] using
          WordRAM.Register.NatProgram.eval_no_syntheticCostOnlyPrimitive
            ((builtRelativeSplitBPCloseRankData shape)
              |>.rankRegisterProgram false (WordRAM.Register.NatExpr.reg 0))
            ((builtRelativeSplitBPCloseRankData shape)
              |>.rankRegisterWordRAMStore false)
            (WordRAM.Register.RegFile.withNat1 pos)
            event hmem)

private theorem
    concreteBPNativeSuccinctRMQRankCloseGlobalWordTraceResult_noFiniteSmallInteriorSuccessfulRead
    (shape : Cartesian.CartesianShape) (pos : Nat) :
    forall event,
      List.Mem event
        (concreteBPNativeRankCloseWordTraceResultAtSegment
          shape concreteBPNativeRankCloseTraceSegmentBase pos).trace ->
        concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead
          event := by
  unfold concreteBPNativeRankCloseWordTraceResultAtSegment
  exact
    concreteBPNativeSuccinctRMQTraceResult_relabelReadSegmentsWith_noFiniteSmallInteriorSuccessfulRead
      (WordRAM.tripleSegmentMap concreteBPNativeRankCloseTraceSegmentBase
        concreteBPNativeDeadTraceSegment)
      (concreteBPNativeRankCloseWordTraceResult shape pos)
      (concreteBPNativeSuccinctRMQTripleSegmentMap_ne_of_bases_ne
        concreteBPNativeRankCloseTraceSegmentBase
        concreteBPNativeDeadTraceSegment
        (by decide) (by decide) (by decide) (by decide))
      (concreteBPNativeSuccinctRMQTripleSegmentMap_ne27_of_bases_ne
        concreteBPNativeRankCloseTraceSegmentBase
        concreteBPNativeDeadTraceSegment
        (by decide) (by decide) (by decide) (by decide))

private theorem
    concreteBPNativeSuccinctRMQRankCloseGlobalWordTraceResult_noReadyCloseSuccessfulRead
    (shape : Cartesian.CartesianShape) (pos : Nat) :
    forall event,
      List.Mem event
        (concreteBPNativeRankCloseWordTraceResultAtSegment
          shape concreteBPNativeRankCloseTraceSegmentBase pos).trace ->
        concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead
          event := by
  unfold concreteBPNativeRankCloseWordTraceResultAtSegment
  exact
    concreteBPNativeSuccinctRMQTraceResult_relabelReadSegmentsWith_noReadyCloseSuccessfulRead
      (WordRAM.tripleSegmentMap concreteBPNativeRankCloseTraceSegmentBase
        concreteBPNativeDeadTraceSegment)
      (concreteBPNativeRankCloseWordTraceResult shape pos)
      (concreteBPNativeSuccinctRMQTripleSegmentMap_avoidsReadyClose_of_outside
        concreteBPNativeRankCloseTraceSegmentBase
        concreteBPNativeDeadTraceSegment
        (by decide) (by decide) (by decide) (by decide))

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

/--
Interpreted compact LCA-close leg.

The compact close directory is unchanged; the rank seed callback it consumes is
now the interpreted false-rank query above.
-/
def concreteBPNativeLCACloseInterpretedCosted
    (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) : Costed (Option Nat) :=
  (concreteBPNativeCloseDirectory shape).lcaCloseCostedWithRankSeed
    (concreteBPNativeRankCloseInterpretedCosted shape)
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
    (concreteBPNativeRankCloseWordTraceResult shape) leftClose rightClose

theorem concreteBPNativeLCACloseWordTraceResult_refines_interpretedCosted
    (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) :
    (concreteBPNativeLCACloseWordTraceResult
      shape leftClose rightClose).toCosted =
      concreteBPNativeLCACloseInterpretedCosted shape leftClose rightClose := by
  simp [concreteBPNativeLCACloseWordTraceResult,
    concreteBPNativeLCACloseInterpretedCosted,
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.lcaCloseTraceResultWithRankSeed_refines,
    concreteBPNativeRankCloseWordTraceResult_refines_interpretedCosted]

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
    shape (concreteBPNativeRankCloseWordTraceResult shape)
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
    concreteBPNativeRankCloseWordTraceResult_refines_interpretedCosted]

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
    (concreteBPNativeRankCloseWordTraceResultAtSegment shape rankSegmentBase)
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
    concreteBPNativeRankCloseWordTraceResultAtSegment_refines_interpretedCosted]

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
    (concreteBPNativeRankCloseWordTraceResultAtSegment
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
    concreteBPNativeRankCloseWordTraceResultAtSegment_refines_interpretedCosted]

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
      concreteBPNativeFiniteSmallSameBlockCloseTraceSegment
      leftClose rightClose
      concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead
      (fun pos =>
        concreteBPNativeSuccinctRMQRankCloseGlobalWordTraceResult_noFiniteSmallInteriorSuccessfulRead
          shape pos)
      (fun blockSize close =>
        concreteBPNativeSuccinctRMQLocalBPWindowBitsTraceResult_noFiniteSmallInteriorSuccessfulRead
          shape blockSize close)
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
      concreteBPNativeFiniteSmallSameBlockCloseTraceSegment
      leftClose rightClose
      concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead
      (fun pos =>
        concreteBPNativeSuccinctRMQRankCloseGlobalWordTraceResult_noFiniteSmallInteriorSuccessfulRead
          shape pos)
      (fun blockSize close =>
        concreteBPNativeSuccinctRMQLocalBPWindowBitsTraceResult_noFiniteSmallInteriorSuccessfulRead
          shape blockSize close)
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
      concreteBPNativeFiniteSmallSameBlockCloseTraceSegment
      leftClose rightClose
      concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead
      (fun pos =>
        concreteBPNativeSuccinctRMQRankCloseGlobalWordTraceResult_noReadyCloseSuccessfulRead
          shape pos)
      (fun blockSize close =>
        concreteBPNativeSuccinctRMQLocalBPWindowBitsTraceResult_noReadyCloseSuccessfulRead
          shape blockSize close)
      (fun startBlock count =>
        concreteBPNativeInteriorGlobalWordTraceResultAllSizeStructural_noReadyCloseSuccessfulRead_of_not_ready
          shape hnotReady startBlock count)

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
      (concreteBPNativeRankCloseWordTraceResultAtSegment
        shape concreteBPNativeRankCloseTraceSegmentBase)
      leftClose rightClose
      (concreteBPNativeSuccinctRMQGlobalReadStoreLegacy shape)
      (fun pos =>
        concreteBPNativeRankCloseGlobalWordTraceResult_matchesReadStore
          shape pos)
      (concreteBPNativeSuccinctRMQGlobalReadStoreLegacy_bpCode shape)
      (fun blockSize close =>
        SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPWindowBitsTraceResult_matchesReadStore
          shape blockSize close
          (concreteBPNativeSuccinctRMQGlobalReadStoreLegacy shape)
          (concreteBPNativeSuccinctRMQGlobalReadStoreLegacy_bpCode shape))

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
      concreteBPNativeFiniteSmallSameBlockCloseTraceSegment
      leftClose rightClose
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (fun pos =>
        concreteBPNativeRankCloseCanonicalGlobalWordTraceResult_matchesReadStore
          shape pos)
      (concreteBPNativeSuccinctRMQGlobalReadStore_bpCode shape)
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
      concreteBPNativeFiniteSmallSameBlockCloseTraceSegment
      leftClose rightClose
      (fun pos =>
        concreteBPNativeRankCloseGlobalWordTraceResult_no_syntheticCostOnlyPrimitive
          shape pos)

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
      (concreteBPNativeRankCloseWordTraceResultAtSegment
        shape concreteBPNativeRankCloseTraceSegmentBase)
      hsize concreteBPNativeInteriorTraceSegments leftClose rightClose
      (concreteBPNativeSuccinctRMQGlobalReadStoreLegacy shape)
      (fun pos =>
        concreteBPNativeRankCloseGlobalWordTraceResult_matchesReadStore
          shape pos)
      (concreteBPNativeSuccinctRMQGlobalReadStoreLegacy_bpCode shape)
      (fun startBlock count =>
        concreteBPNativeInteriorGlobalWordTraceResult_matchesReadStore
          shape hsize startBlock count)

/--
Final BP-native RMQ query with interpreted close-select, compact close/LCA, and
answer-rank leaves.
-/
def concreteBPNativeSuccinctRMQQueryInterpretedCosted
    (shape : Cartesian.CartesianShape)
    (left right : Nat) : Costed (Option Nat) :=
  Costed.bind (concreteBPNativeSelectCloseInterpretedCosted shape left)
    fun leftClose? =>
      Costed.bind
        (concreteBPNativeSelectCloseInterpretedCosted shape (right - 1))
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
                        (concreteBPNativeRankCloseInterpretedCosted
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
        (concreteBPNativeSelectCloseInterpretedCosted shape
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
            (concreteBPNativeRankCloseInterpretedCosted shape
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
        concreteBPNativeSelectCloseInterpretedCosted shape
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
            concreteBPNativeRankCloseInterpretedCosted shape
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
        (concreteBPNativeSelectCloseWordTraceResult shape
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
            (concreteBPNativeRankCloseWordTraceResult shape
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
        concreteBPNativeSelectCloseWordTraceResult_refines_interpretedCosted,
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
          concreteBPNativeRankCloseWordTraceResult_refines_interpretedCosted,
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
        (concreteBPNativeSelectCloseWordTraceResult shape
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
            (concreteBPNativeRankCloseWordTraceResult shape
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
        concreteBPNativeSelectCloseWordTraceResult_refines_interpretedCosted,
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
          concreteBPNativeRankCloseWordTraceResult_refines_interpretedCosted,
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
payload-store layout. The close/LCA instruction uses the total all-size trace,
so tiny/inactive fallback work is kept as synthetic word primitives while real
payload reads retain global segment addresses.
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
payload reads already use the final shared segment layout. Unlike the
large-regime result below, tiny/inactive close-navigation fallback work is
retained as synthetic word-primitive events rather than structurally replaying
the positive close navigator.
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
      (concreteBPNativeSelectCloseWordTraceResult shape left).trace \/
    List.Mem event
      (concreteBPNativeSelectCloseWordTraceResult shape (right - 1)).trace \/
    (exists leftClose rightClose,
      List.Mem event
        (concreteBPNativeLCACloseWordTraceResultOfSizeGe
          shape hsize leftClose rightClose).trace) \/
    (exists answerClose,
      List.Mem event
        (concreteBPNativeRankCloseWordTraceResult
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
store, and any tiny/inactive fallback events are explicit word primitives.
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
Canonical counted-store execution packet.  The appended canonical interior
payload is erased by exactly the words served at segment 20; the old flat
layout is a compatibility prefix and is not consulted for canonical close
reads.
-/
theorem concreteBPNativeSuccinctRMQWholeQueryFlatPayloadStore_noSynthetic_execution_story
    (shape : Cartesian.CartesianShape)
    (left right : Nat) :
    concreteBPNativeSuccinctRMQCanonicalReviewerPayload shape =
        (concreteBPNativeSuccinctRMQFlatPayloadLayout shape).payload ++
          (SuccinctClose.canonicalRelativeRmmInteriorDirectory shape).payload /\
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
      (concreteBPNativeSelectCloseWordTraceResult shape left).value with
  | none =>
      simp [hleftVal] at hmem
  | some leftClose =>
      cases hrightVal :
          (concreteBPNativeSelectCloseWordTraceResult shape (right - 1)).value with
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
        (concreteBPNativeSelectCloseInterpretedCosted shape left).value with
    | none =>
        simp [hleft, WholeQueryProgram.eval, WholeQueryInstr.eval,
          WholeQueryNatExpr.eval, WholeQueryState.empty,
          WholeQueryState.opt, WholeQueryState.setOpt, Costed.bind,
          Costed.map, Costed.pure]
    | some leftClose =>
        cases hright :
            (concreteBPNativeSelectCloseInterpretedCosted
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
        (concreteBPNativeSelectCloseInterpretedCosted shape left).value with
    | none =>
        simp [hleft, WholeQueryProgram.eval, WholeQueryInstr.eval,
          WholeQueryNatExpr.eval, WholeQueryState.empty,
          WholeQueryState.opt, WholeQueryState.setOpt, Costed.bind,
          Costed.map, Costed.pure]
    | some leftClose =>
        cases hright :
            (concreteBPNativeSelectCloseInterpretedCosted
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
    concreteBPNativeSelectCloseInterpretedCosted shape idx =
      concreteBPNativeSelectCloseCosted
        builtGenericSparseExceptionSelectBPCloseAccessFamily shape idx := by
  unfold concreteBPNativeSelectCloseInterpretedCosted
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
    concreteBPNativeRankCloseInterpretedCosted shape pos =
      concreteBPNativeRankCloseCosted
        builtGenericSparseExceptionSelectBPCloseAccessFamily shape pos := by
  unfold concreteBPNativeRankCloseInterpretedCosted
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
      concreteBPNativeRankCloseInterpretedCosted shape =
        concreteBPNativeRankCloseCosted
          builtGenericSparseExceptionSelectBPCloseAccessFamily shape := by
    funext pos
    exact concreteBPNativeRankCloseInterpretedCosted_refines_rankCloseCosted
      shape pos
  simp [hfun]

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

/-- Honest transitional all-size cost bound for the canonical whole query. -/
theorem concreteBPNativeSuccinctRMQCanonicalQueryInterpretedCosted_cost_le
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    (concreteBPNativeSuccinctRMQCanonicalQueryInterpretedCosted
      shape left right).cost <=
        3 * SuccinctSelect.sparseDenseFalseSelectQueryCost +
          SuccinctClose.ConcreteCompactBPCloseLCADirectory.canonicalCompactBPCloseQueryCostWithRankSeed
            SuccinctSelect.sparseDenseFalseSelectQueryCost := by
  unfold concreteBPNativeSuccinctRMQCanonicalQueryInterpretedCosted
  have hleft :
      (concreteBPNativeSelectCloseInterpretedCosted shape left).cost <=
        SuccinctSelect.sparseDenseFalseSelectQueryCost := by
    rw [concreteBPNativeSelectCloseInterpretedCosted_refines_selectCloseCosted]
    exact concreteBPNativeSelectCloseCosted_cost_le
      builtGenericSparseExceptionSelectBPCloseAccessFamily shape left
  have hright :
      (concreteBPNativeSelectCloseInterpretedCosted
        shape (right - 1)).cost <=
          SuccinctSelect.sparseDenseFalseSelectQueryCost := by
    rw [concreteBPNativeSelectCloseInterpretedCosted_refines_selectCloseCosted]
    exact concreteBPNativeSelectCloseCosted_cost_le
      builtGenericSparseExceptionSelectBPCloseAccessFamily shape (right - 1)
  have hrankCost :
      forall pos,
        (concreteBPNativeRankCloseInterpretedCosted shape pos).cost <=
          SuccinctSelect.sparseDenseFalseSelectQueryCost := by
    intro pos
    rw [concreteBPNativeRankCloseInterpretedCosted_refines_rankCloseCosted]
    exact concreteBPNativeRankCloseCosted_cost_le
      builtGenericSparseExceptionSelectBPCloseAccessFamily shape pos
  cases hleftValue :
      (concreteBPNativeSelectCloseInterpretedCosted shape left).value with
  | none =>
      simp [Costed.bind, hleftValue]
      omega
  | some leftClose =>
      cases hrightValue :
          (concreteBPNativeSelectCloseInterpretedCosted
            shape (right - 1)).value with
      | none =>
          simp [Costed.bind, hleftValue, hrightValue]
          omega
      | some rightClose =>
          have hlca :=
            SuccinctClose.ConcreteCompactBPCloseLCADirectory.canonicalLcaCloseCostedWithRankSeed_cost_le
              shape (concreteBPNativeRankCloseInterpretedCosted shape)
              leftClose rightClose
              SuccinctSelect.sparseDenseFalseSelectQueryCost hrankCost
          cases hlcaValue :
              (SuccinctClose.ConcreteCompactBPCloseLCADirectory.canonicalLcaCloseCostedWithRankSeed
                shape (concreteBPNativeRankCloseInterpretedCosted shape)
                leftClose rightClose).value with
          | none =>
              simp [concreteBPNativeLCACloseCanonicalInterpretedCosted,
                Costed.bind, hleftValue, hrightValue, hlcaValue]
              omega
          | some answerClose =>
              have hrank := hrankCost (answerClose + 1)
              simp [concreteBPNativeLCACloseCanonicalInterpretedCosted,
                Costed.bind, Costed.map, hleftValue, hrightValue,
                hlcaValue]
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
    have h :
        (concreteBPNativeSelectCloseInterpretedCosted shape left).erase =
          SuccinctSpace.bpCloseOfInorder? shape left := by
      rw [concreteBPNativeSelectCloseInterpretedCosted_refines_selectCloseCosted]
      exact concreteBPNativeSelectCloseCosted_exact
        builtGenericSparseExceptionSelectBPCloseAccessFamily shape left
    simpa only [Costed.erase] using Eq.trans h hleftClose
  have hselectRight :
      (concreteBPNativeSelectCloseInterpretedCosted
        shape (left + len - 1)).value = some rightClose := by
    have h :
        (concreteBPNativeSelectCloseInterpretedCosted
          shape (left + len - 1)).erase =
            SuccinctSpace.bpCloseOfInorder? shape (left + len - 1) := by
      rw [concreteBPNativeSelectCloseInterpretedCosted_refines_selectCloseCosted]
      exact concreteBPNativeSelectCloseCosted_exact
        builtGenericSparseExceptionSelectBPCloseAccessFamily
        shape (left + len - 1)
    simpa only [Costed.erase] using Eq.trans h hrightClose
  have hrankExact :
      forall pos,
        (concreteBPNativeRankCloseInterpretedCosted shape pos).erase =
          Succinct.rankPrefix false shape.bpCode pos := by
    intro pos
    rw [concreteBPNativeRankCloseInterpretedCosted_refines_rankCloseCosted]
    exact concreteBPNativeRankCloseCosted_exact
      builtGenericSparseExceptionSelectBPCloseAccessFamily shape pos
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

/-- Conservative checked corollary retained during U3 cost cleanup. -/
theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_le_cleanAllSize
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
      shape left right).cost <=
        concreteBPNativeSuccinctRMQCleanAllSizeQueryCost := by
  exact Nat.le_trans
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_le_canonicalTransitional
      shape left right)
    (by
      rw [concreteBPNativeSuccinctRMQCanonicalTransitionalQueryCost_eq,
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

end SuccinctFinal
end RMQ
