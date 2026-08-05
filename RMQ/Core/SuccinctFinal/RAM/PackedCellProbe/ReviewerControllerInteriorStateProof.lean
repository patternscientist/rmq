import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReviewerControllerAtomicStateProof

/-!
# Canonical scalar bounds for the reviewer interior protocol

This module is the proof-side scalar/provenance layer for the first-order
segment-20 interior protocol.  It does not change executable state.  The
origin parameters remain visible throughout the invariant so a controller
consumer can reconnect an in-flight `.middle` state to the exact block range
that created it.

## Frozen acceptance rows

* `INT-CANDIDATE` -- both fields of every stored candidate fit one reviewer
  cell; candidate merge, three-way merge, and close preserve the corresponding
  projections.
* `INT-ORIGIN` -- the invariant remains parameterized by the original
  invocation, `startBlock`, and `spanCount`, and retains the canonical range
  premise `startBlock + spanCount <= packedSummaryBlockCountRaw shape.size`.
* `INT-START` -- the canonical smart constructor establishes the invariant
  from invocation operands and the canonical range premise.
* `INT-CONSUME` -- one reply from literally
  `concreteBPNativeSuccinctRMQGlobalReadStore shape` at the request emitted by
  `packedReviewerInteriorNextRequest` preserves the same origin.
* `INT-SCALARS` -- every member of
  `packedReviewerInteriorStateNatFields state` fits one reviewer cell.
* `INT-RESULT` -- every successful `packedReviewerInteriorResult` satisfies
  `PackedReviewerCandidateScalarFits`.
* `INT-CONSUMER` -- LCA `.middle` composition, including the
  left-fringe-to-middle-to-right-seed chain, remains consumer-owned.

The proof distinguishes decoded table values, arithmetic locators, and
candidate pairs.  No decoded multiword payload is assumed to fit merely from
the width of one physical reply.
-/

namespace RMQ
namespace SuccinctFinal
namespace PackedCellProbe

open RMQ.Cartesian

/-- Both scalar components of an optional interior candidate fit one cell. -/
def PackedReviewerCandidateScalarFits
    (shape : CartesianShape) : PackedReviewerCandidate -> Prop
  | none => True
  | some candidate =>
      PackedReviewerNatFits shape.size candidate.1 ∧
        PackedReviewerNatFits shape.size candidate.2

theorem PackedReviewerCandidateScalarFits.scalar_fields
    {shape : CartesianShape} {candidate : PackedReviewerCandidate}
    (hcandidate : PackedReviewerCandidateScalarFits shape candidate) :
    forall value,
      value ∈ packedReviewerCandidateNatFields candidate ->
        PackedReviewerNatFits shape.size value := by
  cases candidate with
  | none =>
      simp [packedReviewerCandidateNatFields]
  | some candidate =>
      rcases candidate with ⟨candidateValue, candidateIndex⟩
      intro value hmem
      simp [packedReviewerCandidateNatFields] at hmem
      rcases hmem with rfl | rfl
      · exact hcandidate.1
      · exact hcandidate.2

theorem PackedReviewerCandidateScalarFits.merge
    {shape : CartesianShape} {left right : PackedReviewerCandidate}
    (hleft : PackedReviewerCandidateScalarFits shape left)
    (hright : PackedReviewerCandidateScalarFits shape right) :
    PackedReviewerCandidateScalarFits shape
      (SuccinctClose.bpCandidateMerge? left right) := by
  cases left with
  | none =>
      simpa [SuccinctClose.bpCandidateMerge?] using hright
  | some left =>
      cases right with
      | none =>
          simpa [SuccinctClose.bpCandidateMerge?] using hleft
      | some right =>
          by_cases hbetter : right.1 < left.1
          · simpa [SuccinctClose.bpCandidateMerge?,
              SuccinctClose.bpCandidateBetter, hbetter] using hright
          · simpa [SuccinctClose.bpCandidateMerge?,
              SuccinctClose.bpCandidateBetter, hbetter] using hleft

theorem PackedReviewerCandidateScalarFits.merge3
    {shape : CartesianShape}
    {left middle right : PackedReviewerCandidate}
    (hleft : PackedReviewerCandidateScalarFits shape left)
    (hmiddle : PackedReviewerCandidateScalarFits shape middle)
    (hright : PackedReviewerCandidateScalarFits shape right) :
    PackedReviewerCandidateScalarFits shape
      (SuccinctClose.bpCandidateMerge3? left middle right) := by
  simpa [SuccinctClose.bpCandidateMerge3?] using
    (hleft.merge hmiddle).merge hright

theorem PackedReviewerCandidateScalarFits.close
    {shape : CartesianShape} {candidate : PackedReviewerCandidate}
    (hcandidate : PackedReviewerCandidateScalarFits shape candidate) :
    forall value,
      SuccinctClose.bpCandidateClose? candidate = some value ->
        PackedReviewerNatFits shape.size value := by
  cases candidate with
  | none =>
      simp [SuccinctClose.bpCandidateClose?]
  | some candidate =>
      rcases candidate with ⟨candidateValue, candidateIndex⟩
      intro value hvalue
      simp [SuccinctClose.bpCandidateClose?] at hvalue
      subst value
      have hindex := hcandidate.2
      omega

/-! ## Canonical segment-20 primitive coherence -/

private def PackedReviewerInteriorInvocationScalarFits
    (shape : CartesianShape) (invocation : PackedReviewerInvocation) : Prop :=
  forall operand,
    operand ∈ packedReviewerInvocationOperands invocation ->
      PackedReviewerNatFits shape.size operand

private theorem PackedReviewerInteriorInvocationScalarFits.nat_fields
    {shape : CartesianShape} {invocation : PackedReviewerInvocation}
    (hinvocation :
      PackedReviewerInteriorInvocationScalarFits shape invocation) :
    forall value,
      value ∈ packedReviewerInvocationNatFields invocation ->
        PackedReviewerNatFits shape.size value := by
  simpa [PackedReviewerInteriorInvocationScalarFits,
    packedReviewerInvocationNatFields, packedReviewerInvocationOperands] using
    hinvocation

/-- Proof-side execution of exactly the canonical replies for one Nat child. -/
private def packedReviewerInteriorNatCanonicalRun
    (shape : CartesianShape) :
    Nat -> PackedReviewerInteriorNatState -> PackedReviewerInteriorNatState
  | 0, state => state
  | fuel + 1, state =>
      match packedReviewerInteriorNatNextRequest state with
      | none => state
      | some request =>
          packedReviewerInteriorNatCanonicalRun shape fuel
            (packedReviewerInteriorNatConsumeReply state
              ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
                request.segment request.index))

private theorem packedReviewerInteriorNatCanonicalRun_read
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (n start next tail : Nat)
    (repliesRev : List (Option (List Bool))) :
    packedReviewerInteriorNatResult
        (packedReviewerInteriorNatCanonicalRun shape (tail + 1)
          (.read invocation n start next (tail + 1) repliesRev)) =
      some
        (SuccinctSpace.fixedWidthNatTableMachineDecode
          (repliesRev.reverse ++
            (SuccinctSpace.consecutiveWordIndices (start + next) (tail + 1)).map
              (fun address =>
                (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
                  20 address))) := by
  induction tail generalizing next repliesRev with
  | zero =>
      simp [packedReviewerInteriorNatCanonicalRun,
        packedReviewerInteriorNatNextRequest,
        packedReviewerInteriorNatConsumeReply,
        packedReviewerInteriorNatResult,
        SuccinctSpace.consecutiveWordIndices, List.reverse_cons]
  | succ tail ih =>
      rw [packedReviewerInteriorNatCanonicalRun]
      simp only [packedReviewerInteriorNatNextRequest,
        packedReviewerInteriorNatConsumeReply, Nat.succ_ne_zero, if_false]
      rw [ih]
      simp [SuccinctSpace.consecutiveWordIndices, List.reverse_cons,
        List.append_assoc, Nat.add_assoc]

private theorem packedReviewerConsecutiveWordIndices_map_add
    (base start count : Nat) :
    (SuccinctSpace.consecutiveWordIndices start count).map
        (fun index => base + index) =
      SuccinctSpace.consecutiveWordIndices (base + start) count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
      simp [SuccinctSpace.consecutiveWordIndices, ih, Nat.add_assoc]

private theorem packedReviewerInteriorNatCanonicalRun_start
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (entryCount width base index : Nat) :
    let state :=
      packedReviewerInteriorNatStart invocation shape.size entryCount width
        base index
    packedReviewerInteriorNatResult
        (packedReviewerInteriorNatCanonicalRun shape
          (packedReviewerInteriorNatRemaining state) state) =
      some
        (((packedInteriorReadNatOf shape.size entryCount width base index).run
          (SuccinctClose.flatWordStoreOfReadStore
            (concreteBPNativeSuccinctRMQGlobalReadStore shape) 20)).value) := by
  dsimp only
  by_cases hindex : index < entryCount
  · by_cases hcount :
        SuccinctSpace.fixedWidthNatTableMachineChunkCount width
            (packedBpCodeWordWidth shape.size) = 0
    · have hstateEq :
          packedReviewerInteriorNatStart invocation shape.size entryCount width
              base index =
            .done (SuccinctSpace.fixedWidthNatTableMachineDecode []) := by
        simp [packedReviewerInteriorNatStart, hindex, hcount]
      have hreadValue :
          ((packedInteriorReadNatOf shape.size entryCount width base index).run
              (SuccinctClose.flatWordStoreOfReadStore
                (concreteBPNativeSuccinctRMQGlobalReadStore shape) 20)).value =
            SuccinctSpace.fixedWidthNatTableMachineDecode [] := by
        simp [packedInteriorReadNatOf, hindex,
          SuccinctSpace.fixedWidthNatTableMachineFootprintAt,
          SuccinctSpace.fixedWidthNatTableMachineFootprint, hcount,
          SuccinctSpace.consecutiveWordIndices]
      rw [hstateEq, hreadValue]
      rfl
    · cases hchunks :
        SuccinctSpace.fixedWidthNatTableMachineChunkCount width
          (packedBpCodeWordWidth shape.size) with
      | zero => contradiction
      | succ tail =>
          have hstateEq :
              packedReviewerInteriorNatStart invocation shape.size entryCount
                  width base index =
                .read invocation shape.size
                  (base + index * (tail + 1)) 0 (tail + 1) [] := by
            simp [packedReviewerInteriorNatStart, hindex, hcount, hchunks]
          have hrun :=
            packedReviewerInteriorNatCanonicalRun_read shape invocation
              shape.size (base + index * (tail + 1)) 0 tail []
          have hrun' :
              packedReviewerInteriorNatResult
                  (packedReviewerInteriorNatCanonicalRun shape (tail + 1)
                    (.read invocation shape.size
                      (base + index * (tail + 1)) 0 (tail + 1) [])) =
                some
                  (SuccinctSpace.fixedWidthNatTableMachineDecode
                    ((SuccinctSpace.consecutiveWordIndices
                      (base + index * (tail + 1)) (tail + 1)).map
                        (fun address =>
                          (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
                            20 address))) := by
            simpa only [List.reverse_nil, List.nil_append, Nat.add_zero] using
              hrun
          have hfootprint :
              SuccinctSpace.fixedWidthNatTableMachineFootprintAt base width
                  (packedBpCodeWordWidth shape.size) index =
                SuccinctSpace.consecutiveWordIndices
                  (base + index * (tail + 1)) (tail + 1) := by
            simp [SuccinctSpace.fixedWidthNatTableMachineFootprintAt,
              SuccinctSpace.fixedWidthNatTableMachineFootprint, hchunks,
              packedReviewerConsecutiveWordIndices_map_add]
          have hreadValue :
              ((packedInteriorReadNatOf shape.size entryCount width base
                    index).run
                  (SuccinctClose.flatWordStoreOfReadStore
                    (concreteBPNativeSuccinctRMQGlobalReadStore shape) 20)).value =
                SuccinctSpace.fixedWidthNatTableMachineDecode
                  ((SuccinctSpace.consecutiveWordIndices
                    (base + index * (tail + 1)) (tail + 1)).map
                      (fun address =>
                        (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
                          20 address)) := by
            simp only [packedInteriorReadNatOf,
              SuccinctSpace.FlatStoreComputation.map_run_value, hindex,
              if_true, SuccinctSpace.FlatStoreComputation.readMany_run_value,
              hfootprint, SuccinctClose.flatWordStoreOfReadStore]
          rw [hstateEq, packedReviewerInteriorNatRemaining, hreadValue]
          exact hrun'
  · have hstateEq :
        packedReviewerInteriorNatStart invocation shape.size entryCount width
            base index =
          .read invocation shape.size
            (packedInteriorOffsets shape.size).deadAddress 0 1 [] := by
      simp [packedReviewerInteriorNatStart, hindex]
    have hrun :=
      packedReviewerInteriorNatCanonicalRun_read shape invocation shape.size
        (packedInteriorOffsets shape.size).deadAddress 0 0 []
    have hrun' :
        packedReviewerInteriorNatResult
            (packedReviewerInteriorNatCanonicalRun shape 1
              (.read invocation shape.size
                (packedInteriorOffsets shape.size).deadAddress 0 1 [])) =
          some
            (SuccinctSpace.fixedWidthNatTableMachineDecode
              [(concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20
                (packedInteriorOffsets shape.size).deadAddress]) := by
      simpa only [SuccinctSpace.consecutiveWordIndices, List.map,
        List.reverse_nil, List.nil_append, Nat.add_zero] using hrun
    have hreadValue :
        ((packedInteriorReadNatOf shape.size entryCount width base index).run
            (SuccinctClose.flatWordStoreOfReadStore
              (concreteBPNativeSuccinctRMQGlobalReadStore shape) 20)).value =
          SuccinctSpace.fixedWidthNatTableMachineDecode
            [(concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20
              (packedInteriorOffsets shape.size).deadAddress] := by
      simp [packedInteriorReadNatOf, hindex,
        SuccinctClose.flatWordStoreOfReadStore]
    rw [hstateEq, packedReviewerInteriorNatRemaining, hreadValue]
    exact hrun'

/-- Which one of the eight canonical interior table columns is being read. -/
private inductive PackedReviewerInteriorNatSpec where
  | baseline (block : Nat)
  | minRel (block : Nat)
  | maxRel (block : Nat)
  | argOffset (block : Nat)
  | localOffset (macroIdx localStart level : Nat)
  | globalBlock (macroStart level : Nat)
  | localLevel (count : Nat)
  | globalLevel (macroSpanCount : Nat)

private def PackedReviewerInteriorNatSpec.start
    (shape : CartesianShape) (invocation : PackedReviewerInvocation) :
    PackedReviewerInteriorNatSpec -> PackedReviewerInteriorNatState
  | .baseline block =>
      packedReviewerInteriorNatStart invocation shape.size
        (packedInteriorLayout shape.size).superSampleCount
        (packedBpCodeWordWidth shape.size)
        (packedInteriorOffsets shape.size).baseline
        (block / (packedInteriorLayout shape.size).blocksPerSuper)
  | .minRel block =>
      packedReviewerInteriorNatStart invocation shape.size
        (packedInteriorLayout shape.size).blockCount
        (packedInteriorLayout shape.size).relativeWidth
        (packedInteriorOffsets shape.size).minRel block
  | .maxRel block =>
      packedReviewerInteriorNatStart invocation shape.size
        (packedInteriorLayout shape.size).blockCount
        (packedInteriorLayout shape.size).relativeWidth
        (packedInteriorOffsets shape.size).maxRel block
  | .argOffset block =>
      packedReviewerInteriorNatStart invocation shape.size
        (packedInteriorLayout shape.size).blockCount
        (packedInteriorLayout shape.size).relativeWidth
        (packedInteriorOffsets shape.size).argOffset block
  | .localOffset macroIdx localStart level =>
      packedReviewerInteriorNatStart invocation shape.size
        ((packedInteriorLayout shape.size).macroSampleCount *
          ((packedInteriorLayout shape.size).levelCount *
            (packedInteriorLayout shape.size).macroSize))
        (packedInteriorLayout shape.size).offsetWidth
        (packedInteriorOffsets shape.size).localOffset
        (SuccinctClose.bpLocalSparseCellSlot
          (packedInteriorLayout shape.size).macroSize
          (packedInteriorLayout shape.size).levelCount macroIdx localStart level)
  | .globalBlock macroStart level =>
      packedReviewerInteriorNatStart invocation shape.size
        ((packedInteriorLayout shape.size).globalLevelCount *
          (packedInteriorLayout shape.size).macroSampleCount)
        (packedInteriorLayout shape.size).blockAddressWidth
        (packedInteriorOffsets shape.size).globalBlock
        (SuccinctClose.bpGlobalSparseCellSlot
          (packedInteriorLayout shape.size).macroSampleCount macroStart level)
  | .localLevel count =>
      let domain :=
        SuccinctClose.bpSparseLevelDomain
          (packedInteriorLayout shape.size).macroSize
      packedReviewerInteriorNatStart invocation shape.size domain
        (SuccinctClose.bpSparseLevelWidth domain)
        (packedInteriorOffsets shape.size).localLevel count
  | .globalLevel macroSpanCount =>
      let domain :=
        SuccinctClose.bpSparseLevelDomain
          (packedInteriorLayout shape.size).macroSampleCount
      packedReviewerInteriorNatStart invocation shape.size domain
        (SuccinctClose.bpSparseLevelWidth domain)
        (packedInteriorOffsets shape.size).globalLevel macroSpanCount

private def PackedReviewerInteriorNatSpec.expected
    (shape : CartesianShape) : PackedReviewerInteriorNatSpec -> Option Nat
  | .baseline block =>
      ((SuccinctClose.canonicalRelativeRmmSummaryTable shape).baselineTable.readCosted
          (block /
            (SuccinctClose.RelativeRmm.canonicalLayout shape).blocksPerSuper)).erase
  | .minRel block =>
      ((SuccinctClose.canonicalRelativeRmmSummaryTable shape).minRelTable.readCosted
        block).erase
  | .maxRel block =>
      ((SuccinctClose.canonicalRelativeRmmSummaryTable shape).maxRelTable.readCosted
        block).erase
  | .argOffset block =>
      ((SuccinctClose.canonicalRelativeRmmSummaryTable shape).argOffsetTable.readCosted
        block).erase
  | .localOffset macroIdx localStart level =>
      ((SuccinctClose.canonicalRelativeRmmInteriorLocalTable shape).table.readCosted
          (SuccinctClose.bpLocalSparseCellSlot
            (SuccinctClose.RelativeRmm.canonicalLayout shape).macroSize
            (SuccinctClose.RelativeRmm.canonicalLayout shape).levelCount
            macroIdx localStart level)).erase
  | .globalBlock macroStart level =>
      ((SuccinctClose.canonicalRelativeRmmInteriorGlobalTable shape).table.readCosted
          (SuccinctClose.bpGlobalSparseCellSlot
            (SuccinctClose.RelativeRmm.canonicalLayout shape).macroSampleCount
            macroStart level)).erase
  | .localLevel count =>
      ((SuccinctClose.canonicalRelativeRmmInteriorLocalLevelTable shape).table.readCosted
        count).erase
  | .globalLevel macroSpanCount =>
      ((SuccinctClose.canonicalRelativeRmmInteriorGlobalLevelTable shape).table.readCosted
        macroSpanCount).erase

private theorem PackedReviewerInteriorNatSpec.start_exact
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (spec : PackedReviewerInteriorNatSpec) :
    packedReviewerInteriorNatResult
        (packedReviewerInteriorNatCanonicalRun shape
          (packedReviewerInteriorNatRemaining (spec.start shape invocation))
          (spec.start shape invocation)) =
      some (spec.expected shape) := by
  have hstore :
      SuccinctClose.flatWordStoreOfReadStore
          (concreteBPNativeSuccinctRMQGlobalReadStore shape) 20 =
        (SuccinctClose.canonicalRelativeRmmInteriorComponentStore
          shape).store.words := by
    funext address
    simpa using
      concreteBPNativeSuccinctRMQGlobalReadStore_canonicalComponent shape
        address
  cases spec with
  | baseline block =>
      rw [PackedReviewerInteriorNatSpec.start,
        PackedReviewerInteriorNatSpec.expected]
      rw [packedReviewerInteriorNatCanonicalRun_start]
      have href :=
        SuccinctClose.canonicalRelativeRmmBaselineReadComputation_refines shape
          (block /
            (SuccinctClose.RelativeRmm.canonicalLayout shape).blocksPerSuper)
      have hvalue := congrArg Costed.erase href
      simpa only [SuccinctSpace.FlatStoreExecution.toCosted_erase,
        SuccinctClose.canonicalRelativeRmmMachineReadNatCosted_erase,
        packedInteriorReadNatOf_eq,
        SuccinctClose.bpSuperblockBaselineEntries_length,
        SuccinctClose.RelativeRmm.Layout.superWidth,
        packedBpCodeWordWidth, packedInteriorLayout_eq,
        packedInteriorOffsets_eq, CartesianShape.bpCode_length, hstore] using
        (congrArg some hvalue)
  | minRel block =>
      rw [PackedReviewerInteriorNatSpec.start,
        PackedReviewerInteriorNatSpec.expected]
      rw [packedReviewerInteriorNatCanonicalRun_start]
      have href :=
        SuccinctClose.canonicalRelativeRmmMinRelReadComputation_refines shape
          block
      have hvalue := congrArg Costed.erase href
      simpa only [SuccinctSpace.FlatStoreExecution.toCosted_erase,
        SuccinctClose.canonicalRelativeRmmMachineReadNatCosted_erase,
        packedInteriorReadNatOf_eq,
        SuccinctClose.bpBlockRelativeMinExcessEntries_length,
        packedInteriorLayout_eq, packedInteriorOffsets_eq, hstore] using
        (congrArg some hvalue)
  | maxRel block =>
      rw [PackedReviewerInteriorNatSpec.start,
        PackedReviewerInteriorNatSpec.expected]
      rw [packedReviewerInteriorNatCanonicalRun_start]
      have href :=
        SuccinctClose.canonicalRelativeRmmMaxRelReadComputation_refines shape
          block
      have hvalue := congrArg Costed.erase href
      simpa only [SuccinctSpace.FlatStoreExecution.toCosted_erase,
        SuccinctClose.canonicalRelativeRmmMachineReadNatCosted_erase,
        packedInteriorReadNatOf_eq,
        SuccinctClose.bpBlockRelativeMaxExcessEntries_length,
        packedInteriorLayout_eq, packedInteriorOffsets_eq, hstore] using
        (congrArg some hvalue)
  | argOffset block =>
      rw [PackedReviewerInteriorNatSpec.start,
        PackedReviewerInteriorNatSpec.expected]
      rw [packedReviewerInteriorNatCanonicalRun_start]
      have href :=
        SuccinctClose.canonicalRelativeRmmArgOffsetReadComputation_refines shape
          block
      have hvalue := congrArg Costed.erase href
      simpa only [SuccinctSpace.FlatStoreExecution.toCosted_erase,
        SuccinctClose.canonicalRelativeRmmMachineReadNatCosted_erase,
        packedInteriorReadNatOf_eq,
        SuccinctClose.bpBlockArgMinLocalOffsetEntries_length,
        packedInteriorLayout_eq, packedInteriorOffsets_eq, hstore] using
        (congrArg some hvalue)
  | localOffset macroIdx localStart level =>
      rw [PackedReviewerInteriorNatSpec.start,
        PackedReviewerInteriorNatSpec.expected]
      rw [packedReviewerInteriorNatCanonicalRun_start]
      have href :=
        SuccinctClose.canonicalRelativeRmmLocalReadComputation_refines shape
          (SuccinctClose.bpLocalSparseCellSlot
            (SuccinctClose.RelativeRmm.canonicalLayout shape).macroSize
            (SuccinctClose.RelativeRmm.canonicalLayout shape).levelCount
            macroIdx localStart level)
      have hvalue := congrArg Costed.erase href
      simpa only [SuccinctSpace.FlatStoreExecution.toCosted_erase,
        SuccinctClose.canonicalRelativeRmmMachineReadNatCosted_erase,
        packedInteriorReadNatOf_eq,
        SuccinctClose.bpLocalSparseOffsetEntries_length,
        packedInteriorLayout_eq, packedInteriorOffsets_eq, hstore] using
        (congrArg some hvalue)
  | globalBlock macroStart level =>
      rw [PackedReviewerInteriorNatSpec.start,
        PackedReviewerInteriorNatSpec.expected]
      rw [packedReviewerInteriorNatCanonicalRun_start]
      have href :=
        SuccinctClose.canonicalRelativeRmmGlobalReadComputation_refines shape
          (SuccinctClose.bpGlobalSparseCellSlot
            (SuccinctClose.RelativeRmm.canonicalLayout shape).macroSampleCount
            macroStart level)
      have hvalue := congrArg Costed.erase href
      simpa only [SuccinctSpace.FlatStoreExecution.toCosted_erase,
        SuccinctClose.canonicalRelativeRmmMachineReadNatCosted_erase,
        packedInteriorReadNatOf_eq,
        SuccinctClose.bpGlobalSparseBlockEntries_length,
        packedInteriorLayout_eq, packedInteriorOffsets_eq, hstore] using
        (congrArg some hvalue)
  | localLevel count =>
      rw [PackedReviewerInteriorNatSpec.start,
        PackedReviewerInteriorNatSpec.expected]
      rw [packedReviewerInteriorNatCanonicalRun_start]
      have href :=
        SuccinctClose.canonicalRelativeRmmLocalLevelReadComputation_refines shape
          count
      have hvalue := congrArg Costed.erase href
      simpa only [SuccinctSpace.FlatStoreExecution.toCosted_erase,
        SuccinctClose.canonicalRelativeRmmMachineReadNatCosted_erase,
        packedInteriorReadNatOf_eq, SuccinctClose.bpSparseLevelEntries_length,
        packedInteriorLayout_eq, packedInteriorOffsets_eq, hstore] using
        (congrArg some hvalue)
  | globalLevel macroSpanCount =>
      rw [PackedReviewerInteriorNatSpec.start,
        PackedReviewerInteriorNatSpec.expected]
      rw [packedReviewerInteriorNatCanonicalRun_start]
      have href :=
        SuccinctClose.canonicalRelativeRmmGlobalLevelReadComputation_refines
          shape macroSpanCount
      have hvalue := congrArg Costed.erase href
      simpa only [SuccinctSpace.FlatStoreExecution.toCosted_erase,
        SuccinctClose.canonicalRelativeRmmMachineReadNatCosted_erase,
        packedInteriorReadNatOf_eq, SuccinctClose.bpSparseLevelEntries_length,
        packedInteriorLayout_eq, packedInteriorOffsets_eq, hstore] using
        (congrArg some hvalue)

/-! ## Numeric bridges from canonical decoded values to one reviewer cell -/

private theorem packedReviewerTwoMul_add_fiveTwelve_le_cellBound (n : Nat) :
    2 * n + 512 <= packedReviewerCellBound n := by
  unfold packedReviewerCellBound
    concreteBPNativeSuccinctRMQCanonicalReviewerOverhead
    genericSparseExceptionBPCloseAccessOverhead
    GenericSelect.canonicalSparseExceptionSelectOverhead
    GenericSelect.canonicalSparseExceptionDirectoryOverhead
    GenericSelect.sparseExceptionRelativeTableOverhead
  omega

private theorem packedReviewerInteriorOverhead_le_cellBound (n : Nat) :
    SuccinctClose.canonicalRelativeRmmInteriorOverhead n <=
      packedReviewerCellBound n := by
  unfold packedReviewerCellBound
    concreteBPNativeSuccinctRMQCanonicalReviewerOverhead
  omega

private theorem packedReviewerNatFits_of_le_twoMul_add_fiveTwelve
    (n value : Nat) (hvalue : value <= 2 * n + 512) :
    PackedReviewerNatFits n value := by
  have hbound := packedReviewerTwoMul_add_fiveTwelve_le_cellBound n
  have hcapacity := packedReviewerCellBound_lt_two_pow_width n
  omega

private theorem packedReviewerNatFits_of_le_interiorOverhead
    (n value : Nat)
    (hvalue :
      value <= SuccinctClose.canonicalRelativeRmmInteriorOverhead n) :
    PackedReviewerNatFits n value := by
  have hbound := packedReviewerInteriorOverhead_le_cellBound n
  have hcapacity := packedReviewerCellBound_lt_two_pow_width n
  omega

theorem packedReviewerLog2SuccSquare_le_self_add_twoFiftySix
    (n : Nat) :
    (Nat.log2 n + 1) * (Nat.log2 n + 1) <= n + 256 := by
  by_cases hlog : 6 <= Nat.log2 n
  · have hn : n ≠ 0 := by
      intro hn
      subst n
      simp at hlog
    have hsquare :=
      SuccinctClose.nat_log2_succ_square_le_self_of_log2_ge_six hn hlog
    omega
  · have hsmall : Nat.log2 n + 1 <= 6 := by omega
    have hsquare := Nat.mul_le_mul hsmall hsmall
    omega

private theorem packedReviewerTwoMulLog2SuccSquare_le_self_add_twoFiftySix
    (n : Nat) :
    2 * ((Nat.log2 n + 1) * (Nat.log2 n + 1)) <= n + 256 := by
  have hpow : forall q : Nat, 8 <= q ->
      2 * ((q + 1) * (q + 1)) <= 2 ^ q := by
    intro q
    induction q with
    | zero => omega
    | succ q ih =>
      intro hq
      by_cases hbase : q = 7
      · subst q
        decide
      · have hq' : 8 <= q := by omega
        have ih' := ih hq'
        have hqq : 2 <= q * q := by
          exact Nat.le_trans (by omega : 2 <= q)
            (Nat.le_mul_of_pos_right q (by omega : 0 < q))
        have hsquare :
            (q + 2) * (q + 2) <= 2 * ((q + 1) * (q + 1)) := by
          simp only [Nat.add_mul, Nat.mul_add]
          omega
        calc
          2 * ((Nat.succ q + 1) * (Nat.succ q + 1)) =
              2 * ((q + 2) * (q + 2)) := by
                simp [Nat.succ_eq_add_one, Nat.add_assoc]
          _ <= 2 * (2 * ((q + 1) * (q + 1))) :=
            Nat.mul_le_mul_left 2 hsquare
          _ <= 2 * (2 ^ q) := Nat.mul_le_mul_left 2 ih'
          _ = 2 ^ (Nat.succ q) := by
            simp [Nat.pow_succ, Nat.mul_comm]
  by_cases hlog : 8 <= Nat.log2 n
  · have hn : n ≠ 0 := by
      intro hn
      subst n
      simp at hlog
    have hself := Nat.log2_self_le hn
    exact Nat.le_trans (hpow (Nat.log2 n) hlog) (by omega)
  · have hsmall : Nat.log2 n + 1 <= 8 := by omega
    have hsquare := Nat.mul_le_mul hsmall hsmall
    omega

private theorem packedReviewerInteriorRelativeEntry_fits
    (shape : CartesianShape) (value : Nat)
    (hvalue :
      value <=
        2 * SuccinctClose.bpSuperblockSpan
          (packedInteriorLayout shape.size).blockSize
          (packedInteriorLayout shape.size).blocksPerSuper) :
    PackedReviewerNatFits shape.size value := by
  have hsquare :=
    packedReviewerTwoMulLog2SuccSquare_le_self_add_twoFiftySix shape.size
  have hspan :
      2 * SuccinctClose.bpSuperblockSpan
          (packedInteriorLayout shape.size).blockSize
          (packedInteriorLayout shape.size).blocksPerSuper <=
        2 * shape.size + 512 := by
    have hscaled := Nat.mul_le_mul_left 2 hsquare
    have hspanEq :
        2 * SuccinctClose.bpSuperblockSpan
            (packedInteriorLayout shape.size).blockSize
            (packedInteriorLayout shape.size).blocksPerSuper =
          2 * (2 * ((Nat.log2 shape.size + 1) *
            (Nat.log2 shape.size + 1))) := by
      simp only [SuccinctClose.bpSuperblockSpan, packedInteriorLayout,
        packedSummaryBlockSizeRaw, packedSummaryBase]
      rw [Nat.mul_left_comm (Nat.log2 shape.size + 1) 2
        (Nat.log2 shape.size + 1)]
    calc
      2 * SuccinctClose.bpSuperblockSpan
          (packedInteriorLayout shape.size).blockSize
          (packedInteriorLayout shape.size).blocksPerSuper =
        2 * (2 * ((Nat.log2 shape.size + 1) *
          (Nat.log2 shape.size + 1))) := hspanEq
      _ <= 2 * (shape.size + 256) := hscaled
      _ = 2 * shape.size + 512 := by omega
  have hbound : value <= 2 * shape.size + 512 := by
    exact Nat.le_trans hvalue hspan
  exact
    packedReviewerNatFits_of_le_twoMul_add_fiveTwelve shape.size value hbound

private theorem packedReviewerSparseLevelCell_fits_of_overhead
    (shape : CartesianShape) (domain count : Nat)
    (hdomain : 2 <= domain) (hcount : count < domain)
    (htable :
      domain * SuccinctClose.bpSparseLevelWidth domain <=
        SuccinctClose.canonicalRelativeRmmInteriorOverhead shape.size) :
    PackedReviewerNatFits shape.size
      (SuccinctClose.bpSparseLevelCell domain count) := by
  have hcell := SuccinctClose.bpSparseLevelCell_lt hdomain hcount
  have hfactor :
      Nat.log2 domain + 1 <= SuccinctClose.bpSparseLevelWidth domain := by
    have hpositive : 0 < Nat.log2 domain + 1 := by omega
    have hdomainLe :
        domain <= domain * (Nat.log2 domain + 1) := by
      simpa using Nat.le_mul_of_pos_right domain hpositive
    have hmono := SuccinctRank.machineWordBits_mono_le hdomainLe
    simpa [SuccinctClose.bpSparseLevelWidth,
      SuccinctRank.machineWordBits] using hmono
  have hvalue :
      SuccinctClose.bpSparseLevelCell domain count <=
        SuccinctClose.canonicalRelativeRmmInteriorOverhead shape.size := by
    have hmul := Nat.mul_le_mul_left domain hfactor
    exact Nat.le_trans (Nat.le_of_lt hcell) (Nat.le_trans hmul htable)
  exact packedReviewerNatFits_of_le_interiorOverhead shape.size _ hvalue

private theorem packedReviewerLocalSparseLevelCell_fits
    (shape : CartesianShape) (count : Nat)
    (hcount :
      count < SuccinctClose.bpSparseLevelDomain
        (packedInteriorLayout shape.size).macroSize) :
    PackedReviewerNatFits shape.size
      (SuccinctClose.bpSparseLevelCell
        (SuccinctClose.bpSparseLevelDomain
          (packedInteriorLayout shape.size).macroSize) count) := by
  apply packedReviewerSparseLevelCell_fits_of_overhead shape
  · exact SuccinctClose.two_le_bpSparseLevelDomain _
  · exact hcount
  · have hlevel :
        SuccinctClose.bpSparseLevelDomain
              (packedInteriorLayout shape.size).macroSize *
            SuccinctClose.bpSparseLevelWidth
              (SuccinctClose.bpSparseLevelDomain
                (packedInteriorLayout shape.size).macroSize) <=
          SuccinctClose.canonicalRelativeRmmInteriorLevelTableOverhead shape := by
      unfold SuccinctClose.canonicalRelativeRmmInteriorLevelTableOverhead
      rw [packedInteriorLayout_eq shape]
      unfold SuccinctClose.bpSparseLevelTableOverhead
      exact Nat.le_add_right _ _
    have htotal :
        SuccinctClose.canonicalRelativeRmmInteriorLevelTableOverhead shape <=
          SuccinctClose.canonicalRelativeRmmInteriorOverhead shape.size := by
      rw [SuccinctClose.canonicalRelativeRmmInteriorLevelTableOverhead_eq_levelPart]
      unfold SuccinctClose.canonicalRelativeRmmInteriorOverhead
      rw [SuccinctClose.canonicalRelativeRmmInteriorRawPayloadOverhead_eq_parts]
      exact Nat.le_add_left _ _
    exact Nat.le_trans hlevel htotal

private theorem packedReviewerGlobalSparseLevelCell_fits
    (shape : CartesianShape) (count : Nat)
    (hcount :
      count < SuccinctClose.bpSparseLevelDomain
        (packedInteriorLayout shape.size).macroSampleCount) :
    PackedReviewerNatFits shape.size
      (SuccinctClose.bpSparseLevelCell
        (SuccinctClose.bpSparseLevelDomain
          (packedInteriorLayout shape.size).macroSampleCount) count) := by
  apply packedReviewerSparseLevelCell_fits_of_overhead shape
  · exact SuccinctClose.two_le_bpSparseLevelDomain _
  · exact hcount
  · have hlevel :
        SuccinctClose.bpSparseLevelDomain
              (packedInteriorLayout shape.size).macroSampleCount *
            SuccinctClose.bpSparseLevelWidth
              (SuccinctClose.bpSparseLevelDomain
                (packedInteriorLayout shape.size).macroSampleCount) <=
          SuccinctClose.canonicalRelativeRmmInteriorLevelTableOverhead shape := by
      unfold SuccinctClose.canonicalRelativeRmmInteriorLevelTableOverhead
      rw [packedInteriorLayout_eq shape]
      unfold SuccinctClose.bpSparseLevelTableOverhead
      exact Nat.le_add_left _ _
    have htotal :
        SuccinctClose.canonicalRelativeRmmInteriorLevelTableOverhead shape <=
          SuccinctClose.canonicalRelativeRmmInteriorOverhead shape.size := by
      rw [SuccinctClose.canonicalRelativeRmmInteriorLevelTableOverhead_eq_levelPart]
      unfold SuccinctClose.canonicalRelativeRmmInteriorOverhead
      rw [SuccinctClose.canonicalRelativeRmmInteriorRawPayloadOverhead_eq_parts]
      exact Nat.le_add_left _ _
    exact Nat.le_trans hlevel htotal

private theorem packedReviewerLocalSparseCellOffset_le_macroSize
    (shape : CartesianShape)
    (blockSize blockCount macroSize macroIdx localStart level : Nat) :
    SuccinctClose.bpLocalSparseCellOffset shape blockSize blockCount macroSize
        macroIdx localStart level <= macroSize := by
  unfold SuccinctClose.bpLocalSparseCellOffset
  by_cases hvalid :
      localStart + 2 ^ level <= macroSize ∧
        macroIdx * macroSize + localStart + 2 ^ level <= blockCount
  · simp only [hvalid, if_true]
    have hmem :=
      SuccinctClose.bpRangeArgMinBlock_mem shape blockSize
        (macroIdx * macroSize + localStart) (2 ^ level)
        (Nat.pow_pos (by omega : 0 < 2))
    have hargMin :
        SuccinctClose.bpRangeArgMinBlock shape blockSize
              (macroIdx * macroSize + localStart) (2 ^ level) <=
            macroIdx * macroSize + macroSize := by
      apply Nat.le_trans (Nat.le_of_lt hmem.2)
      simpa only [Nat.add_assoc] using
        Nat.add_le_add_left hvalid.1 (macroIdx * macroSize)
    have hsub := Nat.sub_le_sub_right hargMin (macroIdx * macroSize)
    simpa using hsub
  · simp [hvalid]

private theorem packedReviewerGlobalSparseCellBlock_le_blockCount
    (shape : CartesianShape)
    (blockSize blockCount macroSize macroCount macroStart level : Nat) :
    SuccinctClose.bpGlobalSparseCellBlock shape blockSize blockCount macroSize
        macroCount macroStart level <= blockCount := by
  unfold SuccinctClose.bpGlobalSparseCellBlock
  by_cases hvalid :
      macroStart + 2 ^ level <= macroCount ∧
        macroStart * macroSize + 2 ^ level * macroSize <= blockCount
  · simp only [hvalid, if_true]
    by_cases hmacro : macroSize = 0
    · subst macroSize
      simp [SuccinctClose.bpRangeArgMinBlock]
    · have hspan : 0 < 2 ^ level * macroSize :=
        Nat.mul_pos (Nat.pow_pos (by omega : 0 < 2)) (by omega)
      have hmem :=
        SuccinctClose.bpRangeArgMinBlock_mem shape blockSize
          (macroStart * macroSize) (2 ^ level * macroSize) hspan
      exact Nat.le_trans (Nat.le_of_lt hmem.2) hvalid.2
  · simp [hvalid]

private theorem PackedReviewerInteriorNatSpec.expected_fits
    (shape : CartesianShape) (spec : PackedReviewerInteriorNatSpec)
    {value : Nat} (hvalue : spec.expected shape = some value) :
    PackedReviewerNatFits shape.size value := by
  let layout := SuccinctClose.RelativeRmm.canonicalLayout shape
  have hvalid := SuccinctClose.RelativeRmm.canonicalLayout_valid shape
  cases spec with
  | baseline block =>
      rw [PackedReviewerInteriorNatSpec.expected,
        SuccinctSpace.FixedWidthNatTable.readCosted_erase] at hvalue
      have hmem := List.mem_of_getElem? hvalue
      unfold SuccinctClose.bpSuperblockBaselineEntries at hmem
      rcases List.mem_map.mp hmem with ⟨super, _hsuper, rfl⟩
      apply packedReviewerNatFits_of_le_twoMul_add_fiveTwelve
      have hexcess := SuccinctClose.bpExcessAt_le_length shape
        (SuccinctClose.blockStartOf
          (SuccinctClose.RelativeRmm.canonicalLayout shape).blockSize
          (super *
            (SuccinctClose.RelativeRmm.canonicalLayout shape).blocksPerSuper))
      rw [CartesianShape.bpCode_length] at hexcess
      exact Nat.le_trans hexcess (by omega)
  | minRel block =>
      rw [PackedReviewerInteriorNatSpec.expected,
        SuccinctSpace.FixedWidthNatTable.readCosted_erase] at hvalue
      have hmem := List.mem_of_getElem? hvalue
      unfold SuccinctClose.bpBlockRelativeMinExcessEntries at hmem
      rcases List.mem_map.mp hmem with ⟨entryBlock, hentryBlock, rfl⟩
      have hblock : entryBlock < layout.blockCount := by
        simpa using hentryBlock
      apply packedReviewerInteriorRelativeEntry_fits
      rw [← packedInteriorLayout_eq shape]
      unfold SuccinctClose.bpBlockRelativeMinExcess
      apply SuccinctClose.bpRelativeExcessEntry_le_two_span
      · exact SuccinctClose.bpBlockMinExcess_le_baseline_add_span
          shape hvalid.blocksPerSuper_pos hblock hvalid.fullBlocks_fit
      · exact SuccinctClose.bpBlockMinExcess_baseline_le_add_span
          shape hvalid.blocksPerSuper_pos hblock hvalid.fullBlocks_fit
  | maxRel block =>
      rw [PackedReviewerInteriorNatSpec.expected,
        SuccinctSpace.FixedWidthNatTable.readCosted_erase] at hvalue
      have hmem := List.mem_of_getElem? hvalue
      unfold SuccinctClose.bpBlockRelativeMaxExcessEntries at hmem
      rcases List.mem_map.mp hmem with ⟨entryBlock, hentryBlock, rfl⟩
      have hblock : entryBlock < layout.blockCount := by
        simpa using hentryBlock
      apply packedReviewerInteriorRelativeEntry_fits
      rw [← packedInteriorLayout_eq shape]
      unfold SuccinctClose.bpBlockRelativeMaxExcess
      apply SuccinctClose.bpRelativeExcessEntry_le_two_span
      · exact SuccinctClose.bpBlockMaxExcess_le_baseline_add_span
          shape hvalid.blocksPerSuper_pos hblock hvalid.fullBlocks_fit
      · exact SuccinctClose.bpBlockMaxExcess_baseline_le_add_span
          shape hvalid.blocksPerSuper_pos hblock hvalid.fullBlocks_fit
  | argOffset block =>
      rw [PackedReviewerInteriorNatSpec.expected,
        SuccinctSpace.FixedWidthNatTable.readCosted_erase] at hvalue
      have hmem := List.mem_of_getElem? hvalue
      unfold SuccinctClose.bpBlockArgMinLocalOffsetEntries at hmem
      rcases List.mem_map.mp hmem with ⟨entryBlock, hentryBlock, rfl⟩
      have hblock : entryBlock < layout.blockCount := by
        simpa using hentryBlock
      have hoffset :=
        SuccinctClose.bpBlockArgMinLocalOffset_le_blockSize shape hblock
          hvalid.fullBlocks_fit
      have hsquare :=
        packedReviewerLog2SuccSquare_le_self_add_twoFiftySix shape.size
      apply packedReviewerNatFits_of_le_twoMul_add_fiveTwelve
      have hbasePos : 0 < Nat.log2 shape.size + 1 := by omega
      have hbaseLeSquare :
          Nat.log2 shape.size + 1 <=
            (Nat.log2 shape.size + 1) * (Nat.log2 shape.size + 1) := by
        simpa using Nat.le_mul_of_pos_right (Nat.log2 shape.size + 1) hbasePos
      have htwoBaseLe :
          2 * (Nat.log2 shape.size + 1) <=
            2 * ((Nat.log2 shape.size + 1) *
              (Nat.log2 shape.size + 1)) :=
        Nat.mul_le_mul_left 2 hbaseLeSquare
      have htwoSquare :
          2 * ((Nat.log2 shape.size + 1) *
              (Nat.log2 shape.size + 1)) <=
            2 * shape.size + 512 := by
        omega
      simpa [layout, SuccinctClose.RelativeRmm.canonicalLayout,
        SuccinctClose.canonicalBPRelativeSummaryBlockSizeRaw,
        SuccinctClose.canonicalBPRelativeSummaryBase] using
        (Nat.le_trans hoffset (Nat.le_trans htwoBaseLe htwoSquare))
  | localOffset macroIdx localStart level =>
      rw [PackedReviewerInteriorNatSpec.expected,
        SuccinctSpace.FixedWidthNatTable.readCosted_erase] at hvalue
      have hmem := List.mem_of_getElem? hvalue
      unfold SuccinctClose.bpLocalSparseOffsetEntries at hmem
      rcases List.mem_map.mp hmem with ⟨slot, _hslot, rfl⟩
      have hoffset := packedReviewerLocalSparseCellOffset_le_macroSize shape
        layout.blockSize layout.blockCount layout.macroSize
        (slot / (layout.levelCount * layout.macroSize))
        (slot % (layout.levelCount * layout.macroSize) % layout.macroSize)
        (slot % (layout.levelCount * layout.macroSize) / layout.macroSize)
      have hsquare :=
        packedReviewerLog2SuccSquare_le_self_add_twoFiftySix shape.size
      apply packedReviewerNatFits_of_le_twoMul_add_fiveTwelve
      simpa [layout, SuccinctClose.RelativeRmm.canonicalLayout,
        SuccinctClose.RelativeRmm.Layout.macroSize,
        SuccinctClose.canonicalBPRelativeSummaryBase] using
        (Nat.le_trans hoffset (by omega :
          (Nat.log2 shape.size + 1) * (Nat.log2 shape.size + 1) <=
            2 * shape.size + 512))
  | globalBlock macroStart level =>
      rw [PackedReviewerInteriorNatSpec.expected,
        SuccinctSpace.FixedWidthNatTable.readCosted_erase] at hvalue
      have hmem := List.mem_of_getElem? hvalue
      unfold SuccinctClose.bpGlobalSparseBlockEntries at hmem
      rcases List.mem_map.mp hmem with ⟨slot, _hslot, rfl⟩
      have hblock := packedReviewerGlobalSparseCellBlock_le_blockCount shape
        layout.blockSize layout.blockCount layout.macroSize
        layout.macroSampleCount (slot % layout.macroSampleCount)
        (slot / layout.macroSampleCount)
      apply packedReviewerNatFits_of_le_twoMul_add_fiveTwelve
      have hcount :=
        SuccinctClose.canonicalBPRelativeSummaryBlockCountRaw_le_bpCode_length
          shape
      rw [CartesianShape.bpCode_length] at hcount
      have hlayoutCount : layout.blockCount <= 2 * shape.size := by
        simpa [layout, SuccinctClose.RelativeRmm.canonicalLayout] using hcount
      have hbound :
          SuccinctClose.bpGlobalSparseCellBlock shape layout.blockSize
                layout.blockCount layout.macroSize layout.macroSampleCount
                (slot % layout.macroSampleCount)
                (slot / layout.macroSampleCount) <=
            2 * shape.size + 512 :=
        Nat.le_trans hblock (Nat.le_trans hlayoutCount (by omega))
      simpa [layout] using hbound
  | localLevel count =>
      rw [PackedReviewerInteriorNatSpec.expected,
        SuccinctSpace.FixedWidthNatTable.readCosted_erase] at hvalue
      have hmem := List.mem_of_getElem? hvalue
      unfold SuccinctClose.bpSparseLevelEntries at hmem
      rcases List.mem_map.mp hmem with ⟨entry, hentry, rfl⟩
      apply packedReviewerLocalSparseLevelCell_fits shape
      simpa [layout, ← packedInteriorLayout_eq shape] using
        (List.mem_range.mp hentry)
  | globalLevel macroSpanCount =>
      rw [PackedReviewerInteriorNatSpec.expected,
        SuccinctSpace.FixedWidthNatTable.readCosted_erase] at hvalue
      have hmem := List.mem_of_getElem? hvalue
      unfold SuccinctClose.bpSparseLevelEntries at hmem
      rcases List.mem_map.mp hmem with ⟨entry, hentry, rfl⟩
      apply packedReviewerGlobalSparseLevelCell_fits shape
      simpa [layout, ← packedInteriorLayout_eq shape] using
        (List.mem_range.mp hentry)

private def PackedReviewerInteriorNatSpec.component :
    PackedReviewerInteriorNatSpec -> PackedReviewerInteriorComponentTag
  | .baseline _ => .baseline
  | .minRel _ => .minRel
  | .maxRel _ => .maxRel
  | .argOffset _ => .argOffset
  | .localOffset _ _ _ => .localOffset
  | .globalBlock _ _ => .globalBlock
  | .localLevel _ => .localLevel
  | .globalLevel _ => .globalLevel

/-- Shape-indexed table slot selected by an exact primitive specification. -/
private def PackedReviewerInteriorNatSpec.indexAt
    (n : Nat) : PackedReviewerInteriorNatSpec -> Nat
  | .baseline block => block / (packedInteriorLayout n).blocksPerSuper
  | .minRel block | .maxRel block | .argOffset block => block
  | .localOffset macroIdx localStart level =>
      SuccinctClose.bpLocalSparseCellSlot
        (packedInteriorLayout n).macroSize
        (packedInteriorLayout n).levelCount macroIdx localStart level
  | .globalBlock macroStart level =>
      SuccinctClose.bpGlobalSparseCellSlot
        (packedInteriorLayout n).macroSampleCount macroStart level
  | .localLevel count => count
  | .globalLevel macroSpanCount => macroSpanCount

private theorem PackedReviewerInteriorNatSpec.start_eq_component
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (spec : PackedReviewerInteriorNatSpec) :
    spec.start shape invocation =
      packedReviewerInteriorNatStart invocation shape.size
        (packedReviewerInteriorEntryCount shape.size spec.component)
        (packedReviewerInteriorEntryWidth shape.size spec.component)
        (packedReviewerInteriorComponentWordPrefix shape.size spec.component)
        (spec.indexAt shape.size) := by
  cases spec <;>
    rfl

private theorem packedReviewerInteriorComponentWordSpan_le_dead
    (n : Nat) (component : PackedReviewerInteriorComponentTag) :
    packedReviewerInteriorComponentWordPrefix n component +
        packedReviewerInteriorComponentWordCount n component <=
      (packedInteriorOffsets n).deadAddress := by
  cases component <;>
    simp [packedReviewerInteriorComponentWordPrefix,
      packedReviewerInteriorComponentWordCount_eq, packedInteriorOffsets,
      packedInteriorComponentWords] <;>
    omega

private theorem packedReviewerInteriorComponentMachineSpan_le_dead
    (n : Nat) (component : PackedReviewerInteriorComponentTag) :
    packedReviewerInteriorComponentWordPrefix n component +
        packedReviewerInteriorEntryCount n component *
          SuccinctSpace.fixedWidthNatTableMachineChunkCount
            (packedReviewerInteriorEntryWidth n component)
            (packedBpCodeWordWidth n) <=
      (packedInteriorOffsets n).deadAddress := by
  have hword := packedBpCodeWordWidth_pos n
  have hspan := packedReviewerInteriorComponentWordSpan_le_dead n component
  have hcountEq :
      packedReviewerInteriorComponentWordCount n component =
        packedReviewerInteriorEntryCount n component *
          SuccinctSpace.fixedWidthNatTableMachineChunkCount
            (packedReviewerInteriorEntryWidth n component)
            (packedBpCodeWordWidth n) := by
    unfold packedReviewerInteriorComponentWordCount
    rw [packedReviewerInteriorTableWords_eq_chunkCount _ _ _ hword]
    rfl
  rw [hcountEq] at hspan
  exact hspan

private theorem packedReviewerMachineChunkCount_le_eight
    (width wordSize : Nat) (hwordSize : 0 < wordSize)
    (hwidth : width <= 7 * wordSize) :
    SuccinctSpace.fixedWidthNatTableMachineChunkCount width wordSize <= 8 := by
  have hdiv : width / wordSize <= 7 := by
    apply Nat.div_le_of_le_mul
    simpa [Nat.mul_comm] using hwidth
  unfold SuccinctSpace.fixedWidthNatTableMachineChunkCount
  split <;> omega

private theorem packedReviewerInteriorComponentEntryWidth_le_seven
    (shape : CartesianShape) (component : PackedReviewerInteriorComponentTag) :
    packedReviewerInteriorEntryWidth shape.size component <=
      7 * packedBpCodeWordWidth shape.size := by
  cases component with
  | baseline =>
      have hword := packedBpCodeWordWidth_pos shape.size
      simp [packedReviewerInteriorEntryWidth]
      omega
  | minRel | maxRel | argOffset =>
      simpa [packedReviewerInteriorEntryWidth, packedBpCodeWordWidth,
        packedInteriorLayout_eq, CartesianShape.bpCode_length] using
        SuccinctClose.canonicalRelativeRmmRelativeWidth_le_seven_machine shape
  | localOffset =>
      simpa [packedReviewerInteriorEntryWidth, packedBpCodeWordWidth,
        packedInteriorLayout_eq, CartesianShape.bpCode_length] using
        SuccinctClose.canonicalRelativeRmmOffsetWidth_le_seven_machine shape
  | globalBlock =>
      simpa [packedReviewerInteriorEntryWidth, packedBpCodeWordWidth,
        packedInteriorLayout_eq, CartesianShape.bpCode_length] using
        SuccinctClose.canonicalRelativeRmmBlockWidth_le_seven_machine shape
  | localLevel =>
      simpa [packedReviewerInteriorEntryWidth, packedBpCodeWordWidth,
        packedInteriorLayout_eq, CartesianShape.bpCode_length] using
        SuccinctClose.bpSparseLevelLocalWidth_le_seven_machine shape
  | globalLevel =>
      simpa [packedReviewerInteriorEntryWidth, packedBpCodeWordWidth,
        packedInteriorLayout_eq, CartesianShape.bpCode_length] using
        SuccinctClose.bpSparseLevelGlobalWidth_le_seven_machine shape

private theorem PackedReviewerInteriorNatSpec.chunkCount_le_eight
    (shape : CartesianShape) (spec : PackedReviewerInteriorNatSpec) :
    SuccinctSpace.fixedWidthNatTableMachineChunkCount
        (packedReviewerInteriorEntryWidth shape.size spec.component)
        (packedBpCodeWordWidth shape.size) <= 8 :=
  packedReviewerMachineChunkCount_le_eight _ _
    (packedBpCodeWordWidth_pos shape.size)
    (packedReviewerInteriorComponentEntryWidth_le_seven shape spec.component)

private theorem PackedReviewerInteriorNatSpec.start_requests_fit
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (spec : PackedReviewerInteriorNatSpec)
    (hinvocation :
      PackedReviewerInteriorInvocationScalarFits shape invocation) :
    PackedReviewerRequestsFitFrom shape.size
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      packedReviewerInteriorNatNextRequest
      packedReviewerInteriorNatConsumeReply
      (packedReviewerInteriorNatRemaining (spec.start shape invocation))
      (spec.start shape invocation) := by
  rw [spec.start_eq_component shape invocation]
  apply packedReviewerInteriorNatStart_requests_fit
  · exact hinvocation
  · exact packedReviewerInteriorComponentMachineSpan_le_dead shape.size
      spec.component

private theorem packedReviewerInteriorNatStart_progress
    (invocation : PackedReviewerInvocation)
    (n entryCount width base index : Nat) :
    let state :=
      packedReviewerInteriorNatStart invocation n entryCount width base index
    packedReviewerInteriorNatResult state ≠ none ∨
      0 < packedReviewerInteriorNatRemaining state := by
  unfold packedReviewerInteriorNatStart
  by_cases hindex : index < entryCount
  · simp only [hindex, if_true]
    by_cases hcount :
        SuccinctSpace.fixedWidthNatTableMachineChunkCount width
            (packedBpCodeWordWidth n) = 0
    · simp [hcount, packedReviewerInteriorNatResult]
    · right
      simp [hcount, packedReviewerInteriorNatRemaining]
      omega
  · simp [hindex, packedReviewerInteriorNatRemaining]

private theorem packedReviewerInteriorNatStart_read_control
    (invocation : PackedReviewerInvocation)
    (n entryCount width base index : Nat)
    (hcount :
      SuccinctSpace.fixedWidthNatTableMachineChunkCount width
          (packedBpCodeWordWidth n) <= 8) :
    match packedReviewerInteriorNatStart invocation n entryCount width base
        index with
    | .read childInvocation stateN _ next remaining _ =>
        childInvocation = invocation ∧ stateN = n ∧
          0 < remaining ∧ next + remaining <= 8
    | .done _ => True := by
  by_cases hindex : index < entryCount
  · by_cases hzero :
      SuccinctSpace.fixedWidthNatTableMachineChunkCount width
          (packedBpCodeWordWidth n) = 0
    · simp [packedReviewerInteriorNatStart, hindex, hzero]
    · simp only [packedReviewerInteriorNatStart, hindex, if_true,
        hzero, if_false]
      exact ⟨trivial, trivial, Nat.pos_of_ne_zero hzero,
        by simpa using hcount⟩
  · simp [packedReviewerInteriorNatStart, hindex]

private structure PackedReviewerInteriorNatCanonicalScalarFits
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (spec : PackedReviewerInteriorNatSpec)
    (state : PackedReviewerInteriorNatState) : Prop where
  control :
    match state with
    | .read childInvocation n start next remaining _ =>
        childInvocation = invocation ∧ n = shape.size ∧
          PackedReviewerNatFits shape.size start ∧
            0 < remaining ∧ next + remaining <= 8
    | .done value => value = spec.expected shape
  requests :
    PackedReviewerRequestsFitFrom shape.size
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      packedReviewerInteriorNatNextRequest
      packedReviewerInteriorNatConsumeReply
      (packedReviewerInteriorNatRemaining state) state
  exact :
    packedReviewerInteriorNatResult
        (packedReviewerInteriorNatCanonicalRun shape
          (packedReviewerInteriorNatRemaining state) state) =
      some (spec.expected shape)

private theorem PackedReviewerInteriorNatCanonicalScalarFits.scalar_fields
    {shape : CartesianShape} {invocation : PackedReviewerInvocation}
    {spec : PackedReviewerInteriorNatSpec}
    {state : PackedReviewerInteriorNatState}
    (hinvocation :
      PackedReviewerInteriorInvocationScalarFits shape invocation)
    (hstate :
      PackedReviewerInteriorNatCanonicalScalarFits shape invocation spec state) :
    forall value,
      value ∈ packedReviewerInteriorNatStateNatFields state ->
        PackedReviewerNatFits shape.size value := by
  cases state with
  | done result =>
      intro value hmem
      have hcontrol : result = spec.expected shape := hstate.control
      cases result with
      | none =>
          simp [packedReviewerInteriorNatStateNatFields,
            packedReviewerOptionNatFields] at hmem
      | some result =>
          have hvalue : value = result := by
            simpa [packedReviewerInteriorNatStateNatFields,
              packedReviewerOptionNatFields] using hmem
          subst value
          exact spec.expected_fits shape hcontrol.symm
  | read childInvocation n start next remaining repliesRev =>
      have hcontrol := hstate.control
      change childInvocation = invocation ∧ n = shape.size ∧
        PackedReviewerNatFits shape.size start ∧
          0 < remaining ∧ next + remaining <= 8 at hcontrol
      rcases hcontrol with
        ⟨hchildInvocation, hn, hstart, hremaining, hcounter⟩
      subst childInvocation
      subst n
      intro value hmem
      simp [packedReviewerInteriorNatStateNatFields] at hmem
      rcases hmem with hinv | rfl | rfl | rfl | rfl
      · exact hinvocation.nat_fields value hinv
      · exact packedReviewerInputSize_lt_two_pow_cellWidth shape.size
      · exact hstart
      · apply packedReviewerFixedScalar_fits
        omega
      · apply packedReviewerFixedScalar_fits
        omega

private theorem PackedReviewerInteriorNatSpec.start_canonicalScalarFits
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (spec : PackedReviewerInteriorNatSpec)
    (hinvocation :
      PackedReviewerInteriorInvocationScalarFits shape invocation) :
    PackedReviewerInteriorNatCanonicalScalarFits shape invocation spec
      (spec.start shape invocation) := by
  have hrequests := spec.start_requests_fit shape invocation hinvocation
  have hexact := spec.start_exact shape invocation
  have hcontrolStart :=
    packedReviewerInteriorNatStart_read_control invocation shape.size
      (packedReviewerInteriorEntryCount shape.size spec.component)
      (packedReviewerInteriorEntryWidth shape.size spec.component)
      (packedReviewerInteriorComponentWordPrefix shape.size spec.component)
      (spec.indexAt shape.size) (spec.chunkCount_le_eight shape)
  rw [← spec.start_eq_component shape invocation] at hcontrolStart
  cases hstate : spec.start shape invocation with
  | done result =>
      have hexactDone := hexact
      rw [hstate] at hexactDone
      have hcontrol : result = spec.expected shape := by
        simpa [packedReviewerInteriorNatRemaining,
          packedReviewerInteriorNatCanonicalRun,
          packedReviewerInteriorNatResult] using hexactDone
      refine ⟨hcontrol, ?_, hexactDone⟩
      simpa [hstate, packedReviewerInteriorNatRemaining,
        PackedReviewerRequestsFitFrom] using hrequests
  | read childInvocation stateN start next remaining repliesRev =>
      have hexactRead := hexact
      rw [hstate] at hexactRead
      have hreadControl :
          childInvocation = invocation ∧ stateN = shape.size ∧
            0 < remaining ∧ next + remaining <= 8 := by
        simpa [hstate] using hcontrolStart
      rcases hreadControl with
        ⟨hchildInvocation, hstateN, hremaining, hcounter⟩
      cases remaining with
      | zero => omega
      | succ tail =>
          let request : PackedReviewerLogicalRequest :=
            { invocation := childInvocation
              site := .interiorChunk (start + next)
              segment := 20
              index := start + next }
          have hrequest :
              packedReviewerInteriorNatNextRequest
                  (.read childInvocation stateN start next (tail + 1)
                    repliesRev) =
                some request := by
            rfl
          have hrequestsRead :
              PackedReviewerRequestsFitFrom shape.size
                (concreteBPNativeSuccinctRMQGlobalReadStore shape)
                packedReviewerInteriorNatNextRequest
                packedReviewerInteriorNatConsumeReply (tail + 1)
                (.read childInvocation stateN start next (tail + 1)
                  repliesRev) := by
            simpa [hstate, packedReviewerInteriorNatRemaining] using hrequests
          have hfirst :=
            PackedReviewerRequestsFitFrom.step shape.size
              (concreteBPNativeSuccinctRMQGlobalReadStore shape)
              packedReviewerInteriorNatNextRequest
              packedReviewerInteriorNatConsumeReply tail
              (.read childInvocation stateN start next (tail + 1) repliesRev)
              request hrequestsRead hrequest
          have hslot : PackedReviewerNatFits shape.size (start + next) := by
            apply hfirst.1.operands_fit
            simp [request, packedReviewerLogicalRequestOperands,
              packedReviewerReadSiteOperands]
          have hstart : PackedReviewerNatFits shape.size start :=
            Nat.lt_of_le_of_lt (Nat.le_add_right start next) hslot
          exact ⟨⟨hchildInvocation, hstateN, hstart, hremaining, hcounter⟩,
            hrequestsRead, hexactRead⟩

private theorem PackedReviewerInteriorNatCanonicalScalarFits.consume
    {shape : CartesianShape} {invocation : PackedReviewerInvocation}
    {spec : PackedReviewerInteriorNatSpec}
    {state : PackedReviewerInteriorNatState}
    (hstate :
      PackedReviewerInteriorNatCanonicalScalarFits shape invocation spec state) :
    let request := packedReviewerInteriorNatNextRequest state
    let reply := request.bind fun request =>
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
        request.segment request.index
    PackedReviewerInteriorNatCanonicalScalarFits shape invocation spec
      (packedReviewerInteriorNatConsumeReply state reply) := by
  dsimp only
  cases state with
  | done result =>
      simpa [packedReviewerInteriorNatNextRequest,
        packedReviewerInteriorNatConsumeReply] using hstate
  | read childInvocation stateN start next remaining repliesRev =>
      rcases hstate.control with
        ⟨hchildInvocation, hstateN, hstart, hremaining, hcounter⟩
      subst childInvocation
      subst stateN
      cases remaining with
      | zero => omega
      | succ tail =>
          let request : PackedReviewerLogicalRequest :=
            { invocation := invocation
              site := .interiorChunk (start + next)
              segment := 20
              index := start + next }
          let reply :=
            (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
              request.segment request.index
          let nextState :=
            packedReviewerInteriorNatConsumeReply
              (.read invocation shape.size start next (tail + 1) repliesRev)
              reply
          have hrequest :
              packedReviewerInteriorNatNextRequest
                  (.read invocation shape.size start next (tail + 1)
                    repliesRev) =
                some request := by
            rfl
          have hstep :=
            PackedReviewerRequestsFitFrom.step shape.size
              (concreteBPNativeSuccinctRMQGlobalReadStore shape)
              packedReviewerInteriorNatNextRequest
              packedReviewerInteriorNatConsumeReply tail
              (.read invocation shape.size start next (tail + 1) repliesRev)
              request hstate.requests hrequest
          have hexact :
              packedReviewerInteriorNatResult
                  (packedReviewerInteriorNatCanonicalRun shape tail nextState) =
                some (spec.expected shape) := by
            simpa [packedReviewerInteriorNatCanonicalRun,
              packedReviewerInteriorNatNextRequest, request, reply, nextState]
              using hstate.exact
          have hreplyEq :
              (packedReviewerInteriorNatNextRequest
                (.read invocation shape.size start next (tail + 1)
                  repliesRev)).bind
                  (fun emitted =>
                    (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
                      emitted.segment emitted.index) = reply := by
            rw [hrequest]
            rfl
          rw [hreplyEq]
          change PackedReviewerInteriorNatCanonicalScalarFits shape invocation
            spec nextState
          by_cases hlast : tail = 0
          · subst tail
            have hnext :
                nextState =
                  .done (SuccinctSpace.fixedWidthNatTableMachineDecode
                    (reply :: repliesRev).reverse) := by
              simp [nextState, packedReviewerInteriorNatConsumeReply]
            have hcontrol :
                SuccinctSpace.fixedWidthNatTableMachineDecode
                    (reply :: repliesRev).reverse = spec.expected shape := by
              have h := hexact
              rw [hnext] at h
              simpa [packedReviewerInteriorNatCanonicalRun,
                packedReviewerInteriorNatResult] using h
            refine ⟨?_, ?_, ?_⟩
            · rw [hnext]
              exact hcontrol
            · simpa only [hnext, packedReviewerInteriorNatRemaining] using
                hstep.2
            · simpa only [hnext, packedReviewerInteriorNatRemaining] using
                hexact
          · have hnext :
                nextState =
                  .read invocation shape.size start (next + 1) tail
                    (reply :: repliesRev) := by
              simp [nextState, packedReviewerInteriorNatConsumeReply, hlast]
            refine ⟨?_, ?_, ?_⟩
            · rw [hnext]
              exact ⟨rfl, rfl, hstart, Nat.pos_of_ne_zero hlast, by omega⟩
            · simpa [nextState, reply, request,
                packedReviewerInteriorNatConsumeReply, hlast,
                packedReviewerInteriorNatRemaining] using hstep.2
            · simpa only [hnext, packedReviewerInteriorNatRemaining] using
                hexact

/-! ## Higher continuation certificate -/

/-- One literal segment-20 controller step against the canonical global store. -/
private def packedReviewerInteriorCanonicalStep
    (shape : CartesianShape)
    (state : PackedReviewerInteriorState) : PackedReviewerInteriorState :=
  match packedReviewerInteriorNextRequest state with
  | none => state
  | some request =>
      packedReviewerInteriorConsumeReply state
        ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          request.segment request.index)

/-- Three mutually dependent proof objects represented by one positive index. -/
private inductive PackedReviewerInteriorScalarNode where
  | state (state : PackedReviewerInteriorState)
  | candidateContinuation
      (continuation : PackedReviewerCandidateContinuation)
  | natContinuation
      (spec : PackedReviewerInteriorNatSpec)
      (continuation : PackedReviewerInteriorNatContinuation)

/--
A proof-carrying scalar certificate for an interior state or continuation.
Continuation constructors store their exact one-step consumer, so the recursive
occurrence always follows the executable defunctionalized continuation tree.
-/
private inductive PackedReviewerInteriorScalarCertificate
    (shape : CartesianShape) (invocation : PackedReviewerInvocation) :
    PackedReviewerInteriorScalarNode -> Prop where
  | stateDone (candidate : PackedReviewerCandidate)
      (candidate_fits : PackedReviewerCandidateScalarFits shape candidate) :
      PackedReviewerInteriorScalarCertificate shape invocation
        (.state (.done candidate))
  | stateRead
      (spec : PackedReviewerInteriorNatSpec)
      (read : PackedReviewerInteriorNatState)
      (continuation : PackedReviewerInteriorNatContinuation)
      (read_fits :
        PackedReviewerInteriorNatCanonicalScalarFits shape invocation spec read)
      (continuation_fits :
        PackedReviewerInteriorScalarCertificate shape invocation
          (.natContinuation spec continuation)) :
      PackedReviewerInteriorScalarCertificate shape invocation
        (.state (.readNat invocation read continuation))
  | candidateContinuation
      (continuation : PackedReviewerCandidateContinuation)
      (scalar_fields :
        forall value,
          value ∈ packedReviewerCandidateContinuationNatFields continuation ->
            PackedReviewerNatFits shape.size value)
      (finish :
        forall candidate,
          PackedReviewerCandidateScalarFits shape candidate ->
            PackedReviewerInteriorScalarCertificate shape invocation
              (.state
                (packedReviewerInteriorFinishCandidate invocation candidate
                  continuation))) :
      PackedReviewerInteriorScalarCertificate shape invocation
        (.candidateContinuation continuation)
  | natContinuation
      (spec : PackedReviewerInteriorNatSpec)
      (continuation : PackedReviewerInteriorNatContinuation)
      (scalar_fields :
        forall value,
          value ∈
              packedReviewerInteriorNatContinuationNatFields continuation ->
            PackedReviewerNatFits shape.size value)
      (finish :
        PackedReviewerInteriorScalarCertificate shape invocation
          (.state
            (packedReviewerInteriorFinishNat invocation (spec.expected shape)
              continuation))) :
      PackedReviewerInteriorScalarCertificate shape invocation
        (.natContinuation spec continuation)

private theorem PackedReviewerInteriorScalarCertificate.state_scalar_fields
    {shape : CartesianShape} {invocation : PackedReviewerInvocation}
    {state : PackedReviewerInteriorState}
    (hinvocation :
      PackedReviewerInteriorInvocationScalarFits shape invocation)
    (hstate :
      PackedReviewerInteriorScalarCertificate shape invocation (.state state)) :
    forall value,
      value ∈ packedReviewerInteriorStateNatFields state ->
        PackedReviewerNatFits shape.size value := by
  cases hstate with
  | stateDone candidate hcandidate =>
      simpa [packedReviewerInteriorStateNatFields] using
        hcandidate.scalar_fields
  | stateRead spec read continuation hread hcontinuation =>
      cases hcontinuation with
      | natContinuation _ _ hcontinuationFields _ =>
          intro value hmem
          simp [packedReviewerInteriorStateNatFields] at hmem
          rcases hmem with hinv | hreadMem | hcontinuationMem
          · exact hinvocation.nat_fields value hinv
          · exact hread.scalar_fields hinvocation value hreadMem
          · exact hcontinuationFields value hcontinuationMem

private theorem PackedReviewerInteriorScalarCertificate.state_result_fits
    {shape : CartesianShape} {invocation : PackedReviewerInvocation}
    {state : PackedReviewerInteriorState}
    (hstate :
      PackedReviewerInteriorScalarCertificate shape invocation (.state state)) :
    forall candidate,
      packedReviewerInteriorResult state = some candidate ->
        PackedReviewerCandidateScalarFits shape candidate := by
  cases hstate with
  | stateDone candidate hcandidate =>
      intro result hresult
      simp [packedReviewerInteriorResult] at hresult
      subst result
      exact hcandidate
  | stateRead spec read continuation hread hcontinuation =>
      simp [packedReviewerInteriorResult]

private theorem PackedReviewerInteriorScalarCertificate.normalize
    {shape : CartesianShape} {invocation : PackedReviewerInvocation}
    (fuel : Nat) {state : PackedReviewerInteriorState}
    (hstate :
      PackedReviewerInteriorScalarCertificate shape invocation (.state state)) :
    PackedReviewerInteriorScalarCertificate shape invocation
      (.state (packedReviewerInteriorNormalize fuel state)) := by
  induction fuel generalizing state with
  | zero => simpa [packedReviewerInteriorNormalize] using hstate
  | succ fuel ih =>
      cases hstate with
      | stateDone candidate hcandidate =>
          simpa [packedReviewerInteriorNormalize] using
            PackedReviewerInteriorScalarCertificate.stateDone
              (invocation := invocation) candidate hcandidate
      | stateRead spec read continuation hread hcontinuation =>
          cases hresult : packedReviewerInteriorNatResult read with
          | none =>
              simpa [packedReviewerInteriorNormalize, hresult] using
                PackedReviewerInteriorScalarCertificate.stateRead
                  (invocation := invocation) spec read continuation hread
                  hcontinuation
          | some value =>
              have hvalue : value = spec.expected shape := by
                cases read with
                | read childInvocation n start next remaining repliesRev =>
                    simp [packedReviewerInteriorNatResult] at hresult
                | done result =>
                    simp [packedReviewerInteriorNatResult] at hresult
                    subst value
                    exact hread.control
              subst value
              cases hcontinuation with
              | natContinuation _ _ _ hfinish =>
                  simpa [packedReviewerInteriorNormalize, hresult] using
                    ih hfinish

private theorem PackedReviewerInteriorScalarCertificate.canonicalStep
    {shape : CartesianShape} {invocation : PackedReviewerInvocation}
    {state : PackedReviewerInteriorState}
    (hstate :
      PackedReviewerInteriorScalarCertificate shape invocation (.state state)) :
    PackedReviewerInteriorScalarCertificate shape invocation
      (.state (packedReviewerInteriorCanonicalStep shape state)) := by
  cases hstate with
  | stateDone candidate hcandidate =>
      simpa [packedReviewerInteriorCanonicalStep,
        packedReviewerInteriorNextRequest] using
        PackedReviewerInteriorScalarCertificate.stateDone
          (invocation := invocation) candidate hcandidate
  | stateRead spec read continuation hread hcontinuation =>
      cases read with
      | done result =>
          simpa [packedReviewerInteriorCanonicalStep,
            packedReviewerInteriorNextRequest,
            packedReviewerInteriorNatNextRequest] using
            PackedReviewerInteriorScalarCertificate.stateRead
              (invocation := invocation) spec (.done result) continuation hread
              hcontinuation
      | read childInvocation n start next remaining repliesRev =>
          rcases hread.control with
            ⟨hchildInvocation, hn, hstart, hremaining, hcounter⟩
          subst childInvocation
          subst n
          cases remaining with
          | zero => omega
          | succ tail =>
              let request : PackedReviewerLogicalRequest :=
                { invocation := invocation
                  site := .interiorChunk (start + next)
                  segment := 20
                  index := start + next }
              let reply :=
                (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
                  request.segment request.index
              let read' :=
                packedReviewerInteriorNatConsumeReply
                  (.read invocation shape.size start next (tail + 1) repliesRev)
                  reply
              have hread' :
                  PackedReviewerInteriorNatCanonicalScalarFits shape invocation
                    spec read' := by
                simpa [packedReviewerInteriorNatNextRequest, request, reply,
                  read'] using hread.consume
              cases hresult : packedReviewerInteriorNatResult read' with
              | none =>
                  simpa [packedReviewerInteriorCanonicalStep,
                    packedReviewerInteriorNextRequest,
                    packedReviewerInteriorNatNextRequest,
                    packedReviewerInteriorConsumeReply, request, reply, read',
                    hresult] using
                    PackedReviewerInteriorScalarCertificate.stateRead
                      (invocation := invocation) spec read' continuation hread'
                      hcontinuation
              | some value =>
                  have hvalue : value = spec.expected shape := by
                    cases hreadState : read' with
                    | read nextInvocation nextN nextStart nextNext
                        nextRemaining nextRepliesRev =>
                        simp [hreadState, packedReviewerInteriorNatResult] at hresult
                    | done result =>
                        have hresultEq : result = value := by
                          simpa [hreadState,
                            packedReviewerInteriorNatResult] using hresult
                        have hcontrol : result = spec.expected shape := by
                          have h := hread'.control
                          simpa [hreadState] using h
                        exact hresultEq.symm.trans hcontrol
                  subst value
                  cases hcontinuation with
                  | natContinuation _ _ _ hfinish =>
                      simpa [packedReviewerInteriorCanonicalStep,
                        packedReviewerInteriorNextRequest,
                        packedReviewerInteriorNatNextRequest,
                        packedReviewerInteriorConsumeReply, request, reply,
                        read', hresult] using
                        hfinish.normalize
                          (packedReviewerInteriorRemaining
                            (packedReviewerInteriorFinishNat invocation
                              (spec.expected shape) continuation) + 1)

private def packedReviewerInteriorExpectedSummaryCandidate
    (shape : CartesianShape) (block : Nat) : PackedReviewerCandidate :=
  let baseline := (PackedReviewerInteriorNatSpec.baseline block).expected shape
  let minRel := (PackedReviewerInteriorNatSpec.minRel block).expected shape
  let maxRel := (PackedReviewerInteriorNatSpec.maxRel block).expected shape
  let argOffset :=
    (PackedReviewerInteriorNatSpec.argOffset block).expected shape
  let summary : Option (Nat × Nat × Nat × Nat) :=
    match baseline, minRel, maxRel, argOffset with
    | some b, some mn, some mx, some arg => some (b, mn, mx, arg)
    | _, _, _, _ => none
  summary.map
    (SuccinctClose.bpRelativeSummaryMinCandidate
      (packedInteriorLayout shape.size).blockSize
      (packedInteriorLayout shape.size).blocksPerSuper block)

private theorem packedReviewerInteriorExpectedSummaryCandidate_fits
    (shape : CartesianShape) (block : Nat) :
    PackedReviewerCandidateScalarFits shape
      (packedReviewerInteriorExpectedSummaryCandidate shape block) := by
  let layout := SuccinctClose.RelativeRmm.canonicalLayout shape
  let table := SuccinctClose.canonicalRelativeRmmSummaryTable shape
  have hvalid := SuccinctClose.RelativeRmm.canonicalLayout_valid shape
  by_cases hblock : block < layout.blockCount
  · have hsuper : block / layout.blocksPerSuper < layout.superSampleCount := by
      have hdiv :
          block / layout.blocksPerSuper <=
            layout.blockCount / layout.blocksPerSuper :=
        Nat.div_le_div_right (Nat.le_of_lt hblock)
      simp [SuccinctClose.RelativeRmm.Layout.superSampleCount]
      omega
    have hread :=
      RMQ.SuccinctClose.PayloadLiveBPRelativeMinMaxArgSummaryTable.minCandidateCosted_erase_arg_excess_of_bounds
        table hvalid.blocksPerSuper_pos hblock hvalid.fullBlocks_fit hsuper
    have hcand :
        packedReviewerInteriorExpectedSummaryCandidate shape block =
          some
            (SuccinctClose.bpExcessAt shape
              (SuccinctClose.bpBlockArgMinPrefixPos shape layout.blockSize
                block),
             SuccinctClose.bpBlockArgMinPrefixPos shape layout.blockSize
               block) := by
      simpa [packedReviewerInteriorExpectedSummaryCandidate,
        PackedReviewerInteriorNatSpec.expected,
        RMQ.SuccinctClose.PayloadLiveBPRelativeMinMaxArgSummaryTable.minCandidateCosted,
        RMQ.SuccinctClose.PayloadLiveBPRelativeMinMaxArgSummaryTable.summaryCosted,
        Costed.erase, Costed.bind, Costed.map, table, layout,
        ← packedInteriorLayout_eq shape] using hread
    rw [hcand]
    constructor
    · apply packedReviewerNatFits_of_le_twoMul_add_fiveTwelve
      have hexcess := SuccinctClose.bpExcessAt_le_length shape
        (SuccinctClose.bpBlockArgMinPrefixPos shape layout.blockSize block)
      rw [CartesianShape.bpCode_length] at hexcess
      omega
    · apply packedReviewerNatFits_of_le_twoMul_add_fiveTwelve
      have harg :=
        SuccinctClose.bpBlockArgMinPrefixPos_le_length shape layout.blockSize
          block
      rw [CartesianShape.bpCode_length] at harg
      omega
  · have hminNone :
        (PackedReviewerInteriorNatSpec.minRel block).expected shape = none := by
      rw [PackedReviewerInteriorNatSpec.expected,
        SuccinctSpace.FixedWidthNatTable.readCosted_erase]
      apply List.getElem?_eq_none
      rw [SuccinctClose.bpBlockRelativeMinExcessEntries_length]
      simpa [layout] using Nat.le_of_not_gt hblock
    simp [packedReviewerInteriorExpectedSummaryCandidate, hminNone,
      PackedReviewerCandidateScalarFits]

private theorem PackedReviewerInteriorScalarCertificate.candidate_scalar_fields
    {shape : CartesianShape} {invocation : PackedReviewerInvocation}
    {continuation : PackedReviewerCandidateContinuation}
    (hcontinuation :
      PackedReviewerInteriorScalarCertificate shape invocation
        (.candidateContinuation continuation)) :
    forall value,
      value ∈ packedReviewerCandidateContinuationNatFields continuation ->
        PackedReviewerNatFits shape.size value := by
  cases hcontinuation with
  | candidateContinuation _ hfields _ => exact hfields

private theorem PackedReviewerInteriorScalarCertificate.candidate_finish
    {shape : CartesianShape} {invocation : PackedReviewerInvocation}
    {continuation : PackedReviewerCandidateContinuation}
    (hcontinuation :
      PackedReviewerInteriorScalarCertificate shape invocation
        (.candidateContinuation continuation))
    (candidate : PackedReviewerCandidate)
    (hcandidate : PackedReviewerCandidateScalarFits shape candidate) :
    PackedReviewerInteriorScalarCertificate shape invocation
      (.state
        (packedReviewerInteriorFinishCandidate invocation candidate
          continuation)) := by
  cases hcontinuation with
  | candidateContinuation _ _ hfinish => exact hfinish candidate hcandidate

private theorem packedReviewerOptionNatFields_eq_some_of_mem
    {stored : Option Nat} {value : Nat}
    (hmem : value ∈ packedReviewerOptionNatFields stored) :
    stored = some value := by
  cases stored with
  | none =>
      simp [packedReviewerOptionNatFields] at hmem
  | some stored =>
      simp [packedReviewerOptionNatFields] at hmem
      subst value
      rfl

private theorem packedReviewerInteriorStartMinCandidate_scalarCertificate
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (block : Nat) (hblock : PackedReviewerNatFits shape.size block)
    (outer : PackedReviewerCandidateContinuation)
    (houter :
      PackedReviewerInteriorScalarCertificate shape invocation
        (.candidateContinuation outer))
    (hinvocation :
      PackedReviewerInteriorInvocationScalarFits shape invocation) :
    PackedReviewerInteriorScalarCertificate shape invocation
      (.state
        (packedReviewerInteriorStartMinCandidate invocation shape.size block
          outer)) := by
  let baselineSpec := PackedReviewerInteriorNatSpec.baseline block
  let minSpec := PackedReviewerInteriorNatSpec.minRel block
  let maxSpec := PackedReviewerInteriorNatSpec.maxRel block
  let argSpec := PackedReviewerInteriorNatSpec.argOffset block
  have hbaseline := baselineSpec.start_canonicalScalarFits shape invocation
    hinvocation
  have hmin := minSpec.start_canonicalScalarFits shape invocation hinvocation
  have hmax := maxSpec.start_canonicalScalarFits shape invocation hinvocation
  have harg := argSpec.start_canonicalScalarFits shape invocation hinvocation
  have hbaselineValue : forall value,
      value ∈ packedReviewerOptionNatFields (baselineSpec.expected shape) ->
        PackedReviewerNatFits shape.size value := by
    intro value hmem
    exact baselineSpec.expected_fits shape
      (packedReviewerOptionNatFields_eq_some_of_mem hmem)
  have hminValue : forall value,
      value ∈ packedReviewerOptionNatFields (minSpec.expected shape) ->
        PackedReviewerNatFits shape.size value := by
    intro value hmem
    exact minSpec.expected_fits shape
      (packedReviewerOptionNatFields_eq_some_of_mem hmem)
  have hmaxValue : forall value,
      value ∈ packedReviewerOptionNatFields (maxSpec.expected shape) ->
        PackedReviewerNatFits shape.size value := by
    intro value hmem
    exact maxSpec.expected_fits shape
      (packedReviewerOptionNatFields_eq_some_of_mem hmem)
  apply PackedReviewerInteriorScalarCertificate.stateRead baselineSpec
    (baselineSpec.start shape invocation)
    (.summaryBaseline shape.size block outer) hbaseline
  apply PackedReviewerInteriorScalarCertificate.natContinuation
  · intro value hmem
    simp [packedReviewerInteriorNatContinuationNatFields] at hmem
    rcases hmem with rfl | rfl | houterMem
    · exact packedReviewerInputSize_lt_two_pow_cellWidth shape.size
    · exact hblock
    · exact houter.candidate_scalar_fields value houterMem
  · apply PackedReviewerInteriorScalarCertificate.stateRead minSpec
      (minSpec.start shape invocation)
      (.summaryMin shape.size block (baselineSpec.expected shape) outer) hmin
    apply PackedReviewerInteriorScalarCertificate.natContinuation
    · intro value hmem
      simp [packedReviewerInteriorNatContinuationNatFields] at hmem
      rcases hmem with rfl | rfl | hbaselineMem | houterMem
      · exact packedReviewerInputSize_lt_two_pow_cellWidth shape.size
      · exact hblock
      · exact hbaselineValue value hbaselineMem
      · exact houter.candidate_scalar_fields value houterMem
    · apply PackedReviewerInteriorScalarCertificate.stateRead maxSpec
        (maxSpec.start shape invocation)
        (.summaryMax shape.size block (baselineSpec.expected shape)
          (minSpec.expected shape) outer) hmax
      apply PackedReviewerInteriorScalarCertificate.natContinuation
      · intro value hmem
        simp [packedReviewerInteriorNatContinuationNatFields] at hmem
        rcases hmem with rfl | rfl | hbaselineMem | hminMem | houterMem
        · exact packedReviewerInputSize_lt_two_pow_cellWidth shape.size
        · exact hblock
        · exact hbaselineValue value hbaselineMem
        · exact hminValue value hminMem
        · exact houter.candidate_scalar_fields value houterMem
      · apply PackedReviewerInteriorScalarCertificate.stateRead argSpec
          (argSpec.start shape invocation)
          (.summaryArg shape.size block (baselineSpec.expected shape)
            (minSpec.expected shape) (maxSpec.expected shape) outer) harg
        apply PackedReviewerInteriorScalarCertificate.natContinuation
        · intro value hmem
          simp [packedReviewerInteriorNatContinuationNatFields] at hmem
          rcases hmem with rfl | rfl | hbaselineMem | hminMem | hmaxMem |
              houterMem
          · exact packedReviewerInputSize_lt_two_pow_cellWidth shape.size
          · exact hblock
          · exact hbaselineValue value hbaselineMem
          · exact hminValue value hminMem
          · exact hmaxValue value hmaxMem
          · exact houter.candidate_scalar_fields value houterMem
        · simpa [baselineSpec, minSpec, maxSpec, argSpec,
            packedReviewerInteriorFinishNat,
            packedReviewerInteriorExpectedSummaryCandidate] using
            houter.candidate_finish
              (packedReviewerInteriorExpectedSummaryCandidate shape block)
              (packedReviewerInteriorExpectedSummaryCandidate_fits shape block)

private theorem packedReviewerInteriorStartLocalSpan_scalarCertificate
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (macroIdx localStart level : Nat)
    (outer : PackedReviewerCandidateContinuation)
    (houter :
      PackedReviewerInteriorScalarCertificate shape invocation
        (.candidateContinuation outer))
    (hinvocation :
      PackedReviewerInteriorInvocationScalarFits shape invocation)
    (hmacro : macroIdx < (packedInteriorLayout shape.size).macroSampleCount)
    (hlevel : level < (packedInteriorLayout shape.size).levelCount)
    (hlocal : localStart < (packedInteriorLayout shape.size).macroSize)
    (hlocalSpan :
      localStart + 2 ^ level <= (packedInteriorLayout shape.size).macroSize)
    (hblockSpan :
      macroIdx * (packedInteriorLayout shape.size).macroSize + localStart +
          2 ^ level <=
        (packedInteriorLayout shape.size).blockCount) :
    PackedReviewerInteriorScalarCertificate shape invocation
      (.state
        (packedReviewerInteriorStartLocalSpan invocation shape.size macroIdx
          localStart level outer)) := by
  let spec := PackedReviewerInteriorNatSpec.localOffset macroIdx localStart level
  have hread := spec.start_canonicalScalarFits shape invocation hinvocation
  have hoffset :
      spec.expected shape =
        some
          (SuccinctClose.bpLocalSparseCellOffset shape
            (packedInteriorLayout shape.size).blockSize
            (packedInteriorLayout shape.size).blockCount
            (packedInteriorLayout shape.size).macroSize macroIdx localStart
            level) := by
    simp only [spec, PackedReviewerInteriorNatSpec.expected,
      SuccinctSpace.FixedWidthNatTable.readCosted_erase]
    simpa [← packedInteriorLayout_eq shape] using
      SuccinctClose.bpLocalSparseOffsetEntries_get?_of_valid
        (shape := shape) (blockSize :=
          (SuccinctClose.RelativeRmm.canonicalLayout shape).blockSize)
        (blockCount :=
          (SuccinctClose.RelativeRmm.canonicalLayout shape).blockCount)
        (macroSize :=
          (SuccinctClose.RelativeRmm.canonicalLayout shape).macroSize)
        (macroCount :=
          (SuccinctClose.RelativeRmm.canonicalLayout shape).macroSampleCount)
        (levelCount :=
          (SuccinctClose.RelativeRmm.canonicalLayout shape).levelCount)
        hmacro hlevel hlocal
  have hblockEq :=
    SuccinctClose.bpLocalSparseCellOffset_valid_add
      (shape := shape)
      (blockSize := (packedInteriorLayout shape.size).blockSize)
      (blockCount := (packedInteriorLayout shape.size).blockCount)
      (macroSize := (packedInteriorLayout shape.size).macroSize)
      (macroIdx := macroIdx) (localStart := localStart) (level := level)
      hlocalSpan hblockSpan
  have hblockMem :=
    SuccinctClose.bpRangeArgMinBlock_mem shape
      (packedInteriorLayout shape.size).blockSize
      (macroIdx * (packedInteriorLayout shape.size).macroSize + localStart)
      (2 ^ level) (Nat.pow_pos (by omega : 0 < 2))
  have hcountPacked :
      (packedInteriorLayout shape.size).blockCount <= 2 * shape.size := by
    have hcount :=
      SuccinctClose.canonicalBPRelativeSummaryBlockCountRaw_le_bpCode_length
        shape
    rw [CartesianShape.bpCode_length] at hcount
    simpa [← packedInteriorLayout_eq shape] using hcount
  have hblockFits :
      PackedReviewerNatFits shape.size
        (macroIdx * (packedInteriorLayout shape.size).macroSize +
          SuccinctClose.bpLocalSparseCellOffset shape
            (packedInteriorLayout shape.size).blockSize
            (packedInteriorLayout shape.size).blockCount
            (packedInteriorLayout shape.size).macroSize macroIdx localStart
            level) := by
    apply packedReviewerNatFits_of_le_twoMul_add_fiveTwelve
    rw [hblockEq]
    omega
  apply PackedReviewerInteriorScalarCertificate.stateRead spec
    (spec.start shape invocation)
    (.localOffset shape.size macroIdx localStart level outer) hread
  apply PackedReviewerInteriorScalarCertificate.natContinuation
  · intro value hmem
    simp [packedReviewerInteriorNatContinuationNatFields] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | houterMem
    · exact packedReviewerInputSize_lt_two_pow_cellWidth shape.size
    · apply packedReviewerNatFits_of_le_twoMul_add_fiveTwelve
      have hmacroCount :
          (packedInteriorLayout shape.size).macroSampleCount <=
            (packedInteriorLayout shape.size).blockCount + 1 := by
        simp [SuccinctClose.RelativeRmm.Layout.macroSampleCount]
        exact Nat.div_le_self _ _
      omega
    · apply packedReviewerNatFits_of_le_twoMul_add_fiveTwelve
      have hsquare :=
        packedReviewerLog2SuccSquare_le_self_add_twoFiftySix shape.size
      have hmacroSizePacked :
          (packedInteriorLayout shape.size).macroSize <= shape.size + 256 := by
        simpa [packedInteriorLayout,
          SuccinctClose.RelativeRmm.Layout.macroSize,
          packedSummaryBase] using hsquare
      omega
    · apply packedReviewerNatFits_of_le_twoMul_add_fiveTwelve
      have hpow : value < 2 ^ value := Nat.lt_two_pow_self
      omega
    · exact houter.candidate_scalar_fields value houterMem
  · rw [hoffset]
    simpa [spec, packedReviewerInteriorFinishNat] using
      packedReviewerInteriorStartMinCandidate_scalarCertificate shape invocation
        (macroIdx * (packedInteriorLayout shape.size).macroSize +
          SuccinctClose.bpLocalSparseCellOffset shape
            (packedInteriorLayout shape.size).blockSize
            (packedInteriorLayout shape.size).blockCount
            (packedInteriorLayout shape.size).macroSize macroIdx localStart
            level)
        hblockFits outer houter hinvocation

private theorem packedReviewerInteriorStartGlobalSpan_scalarCertificate
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (macroStart level : Nat) (outer : PackedReviewerCandidateContinuation)
    (houter :
      PackedReviewerInteriorScalarCertificate shape invocation
        (.candidateContinuation outer))
    (hinvocation :
      PackedReviewerInteriorInvocationScalarFits shape invocation)
    (hmacro : macroStart < (packedInteriorLayout shape.size).macroSampleCount)
    (hlevel : level < (packedInteriorLayout shape.size).globalLevelCount)
    (hmacroSpan :
      macroStart + 2 ^ level <=
        (packedInteriorLayout shape.size).macroSampleCount)
    (hblockSpan :
      macroStart * (packedInteriorLayout shape.size).macroSize +
          2 ^ level * (packedInteriorLayout shape.size).macroSize <=
        (packedInteriorLayout shape.size).blockCount) :
    PackedReviewerInteriorScalarCertificate shape invocation
      (.state
        (packedReviewerInteriorStartGlobalSpan invocation shape.size macroStart
          level outer)) := by
  let spec := PackedReviewerInteriorNatSpec.globalBlock macroStart level
  have hread := spec.start_canonicalScalarFits shape invocation hinvocation
  have hblock :
      spec.expected shape =
        some
          (SuccinctClose.bpGlobalSparseCellBlock shape
            (packedInteriorLayout shape.size).blockSize
            (packedInteriorLayout shape.size).blockCount
            (packedInteriorLayout shape.size).macroSize
            (packedInteriorLayout shape.size).macroSampleCount macroStart
            level) := by
    simp only [spec, PackedReviewerInteriorNatSpec.expected,
      SuccinctSpace.FixedWidthNatTable.readCosted_erase]
    simpa [← packedInteriorLayout_eq shape] using
      SuccinctClose.bpGlobalSparseBlockEntries_get?_of_valid
        (shape := shape)
        (blockSize :=
          (SuccinctClose.RelativeRmm.canonicalLayout shape).blockSize)
        (blockCount :=
          (SuccinctClose.RelativeRmm.canonicalLayout shape).blockCount)
        (macroSize :=
          (SuccinctClose.RelativeRmm.canonicalLayout shape).macroSize)
        (macroCount :=
          (SuccinctClose.RelativeRmm.canonicalLayout shape).macroSampleCount)
        (levelCount :=
          (SuccinctClose.RelativeRmm.canonicalLayout shape).globalLevelCount)
        hlevel hmacro
  have hblockEq := SuccinctClose.bpGlobalSparseCellBlock_valid_eq
    (shape := shape)
    (blockSize := (packedInteriorLayout shape.size).blockSize)
    (blockCount := (packedInteriorLayout shape.size).blockCount)
    (macroSize := (packedInteriorLayout shape.size).macroSize)
    (macroCount := (packedInteriorLayout shape.size).macroSampleCount)
    (macroStart := macroStart) (level := level) hmacroSpan hblockSpan
  have hmacroSizePos :
      0 < (packedInteriorLayout shape.size).macroSize := by
    simpa [← packedInteriorLayout_eq shape] using
      (SuccinctClose.RelativeRmm.canonicalLayout_valid shape).macroSize_pos
  have hblockMem :=
    SuccinctClose.bpRangeArgMinBlock_mem shape
      (packedInteriorLayout shape.size).blockSize
      (macroStart * (packedInteriorLayout shape.size).macroSize)
      (2 ^ level * (packedInteriorLayout shape.size).macroSize)
      (Nat.mul_pos (Nat.pow_pos (by omega : 0 < 2)) hmacroSizePos)
  have hcountPacked :
      (packedInteriorLayout shape.size).blockCount <= 2 * shape.size := by
    have hcount :=
      SuccinctClose.canonicalBPRelativeSummaryBlockCountRaw_le_bpCode_length
        shape
    rw [CartesianShape.bpCode_length] at hcount
    simpa [← packedInteriorLayout_eq shape] using hcount
  have hblockFits :
      PackedReviewerNatFits shape.size
        (SuccinctClose.bpGlobalSparseCellBlock shape
          (packedInteriorLayout shape.size).blockSize
          (packedInteriorLayout shape.size).blockCount
          (packedInteriorLayout shape.size).macroSize
          (packedInteriorLayout shape.size).macroSampleCount macroStart level) := by
    apply packedReviewerNatFits_of_le_twoMul_add_fiveTwelve
    rw [hblockEq]
    omega
  apply PackedReviewerInteriorScalarCertificate.stateRead spec
    (spec.start shape invocation)
    (.globalBlock shape.size macroStart level outer) hread
  apply PackedReviewerInteriorScalarCertificate.natContinuation
  · intro value hmem
    simp [packedReviewerInteriorNatContinuationNatFields] at hmem
    rcases hmem with rfl | rfl | rfl | houterMem
    · exact packedReviewerInputSize_lt_two_pow_cellWidth shape.size
    · apply packedReviewerNatFits_of_le_twoMul_add_fiveTwelve
      have hmacroCount :
          (packedInteriorLayout shape.size).macroSampleCount <=
            (packedInteriorLayout shape.size).blockCount + 1 := by
        simp [SuccinctClose.RelativeRmm.Layout.macroSampleCount]
        exact Nat.div_le_self _ _
      omega
    · apply packedReviewerNatFits_of_le_twoMul_add_fiveTwelve
      have hpow : value < 2 ^ value := Nat.lt_two_pow_self
      have hpowMul :
          2 ^ value <=
            2 ^ value * (packedInteriorLayout shape.size).macroSize :=
        Nat.le_mul_of_pos_right _ hmacroSizePos
      omega
    · exact houter.candidate_scalar_fields value houterMem
  · rw [hblock]
    simpa [spec, packedReviewerInteriorFinishNat] using
      packedReviewerInteriorStartMinCandidate_scalarCertificate shape invocation
        (SuccinctClose.bpGlobalSparseCellBlock shape
          (packedInteriorLayout shape.size).blockSize
          (packedInteriorLayout shape.size).blockCount
          (packedInteriorLayout shape.size).macroSize
          (packedInteriorLayout shape.size).macroSampleCount macroStart level)
        hblockFits outer houter hinvocation

private structure PackedReviewerLocalTwoGeo
    (shape : CartesianShape) (macroIdx localStart count : Nat) : Prop where
  count_pos : 0 < count
  local_bound :
    localStart + count <= (packedInteriorLayout shape.size).macroSize
  block_bound :
    macroIdx * (packedInteriorLayout shape.size).macroSize + localStart +
        count <=
      (packedInteriorLayout shape.size).blockCount

private structure PackedReviewerGlobalTwoGeo
    (shape : CartesianShape) (macroStart macroSpanCount : Nat) : Prop where
  count_pos : 0 < macroSpanCount
  macro_bound :
    macroStart + macroSpanCount <=
      (packedInteriorLayout shape.size).macroSampleCount
  block_bound :
    (macroStart + macroSpanCount) *
        (packedInteriorLayout shape.size).macroSize <=
      (packedInteriorLayout shape.size).blockCount

private theorem packedReviewerInteriorStartLocalTwo_scalarCertificate
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (macroIdx localStart count : Nat)
    (outer : PackedReviewerCandidateContinuation)
    (houter :
      PackedReviewerInteriorScalarCertificate shape invocation
        (.candidateContinuation outer))
    (hinvocation :
      PackedReviewerInteriorInvocationScalarFits shape invocation)
    (hgeo : PackedReviewerLocalTwoGeo shape macroIdx localStart count) :
    PackedReviewerInteriorScalarCertificate shape invocation
      (.state
        (packedReviewerInteriorStartLocalTwo invocation shape.size macroIdx
          localStart count outer)) := by
  let layout := packedInteriorLayout shape.size
  let domain := SuccinctClose.bpSparseLevelDomain layout.macroSize
  let encoded := SuccinctClose.bpSparseLevelCell domain count
  let level := Nat.log2 count
  let span := SuccinctClose.bpSparseLogSpan count
  let rightStart := localStart + count - span
  let spec := PackedReviewerInteriorNatSpec.localLevel count
  have hvalid := SuccinctClose.RelativeRmm.canonicalLayout_valid shape
  have hlocalBound : localStart + count <= layout.macroSize := by
    simpa [layout] using hgeo.local_bound
  have hblockBound :
      macroIdx * layout.macroSize + localStart + count <=
        layout.blockCount := by
    simpa [layout] using hgeo.block_bound
  have hcountPos : 0 < count := hgeo.count_pos
  have hcountLe : count <= layout.macroSize := by omega
  have hmacroSizePos : 0 < layout.macroSize := by
    simpa [layout, ← packedInteriorLayout_eq shape] using hvalid.macroSize_pos
  have hcountPacked : layout.blockCount <= 2 * shape.size := by
    have hcount :=
      SuccinctClose.canonicalBPRelativeSummaryBlockCountRaw_le_bpCode_length
        shape
    rw [CartesianShape.bpCode_length] at hcount
    simpa [layout, ← packedInteriorLayout_eq shape] using hcount
  have hmacroCount :
      layout.macroSampleCount <= layout.blockCount + 1 := by
    simp [SuccinctClose.RelativeRmm.Layout.macroSampleCount]
    exact Nat.div_le_self _ _
  have hmacroSizePacked : layout.macroSize <= shape.size + 256 := by
    have hsquare :=
      packedReviewerLog2SuccSquare_le_self_add_twoFiftySix shape.size
    simpa [layout, packedInteriorLayout,
      SuccinctClose.RelativeRmm.Layout.macroSize, packedSummaryBase] using
      hsquare
  have hdomain : 2 <= domain :=
    SuccinctClose.two_le_bpSparseLevelDomain _
  have hcountDomain : count < domain := by
    simpa only [domain] using
      (SuccinctClose.bpSparseLevelDomain_covers
        (bound := layout.macroSize) (count := count) hcountLe)
  have hencoded : spec.expected shape = some encoded := by
    simp only [spec, PackedReviewerInteriorNatSpec.expected,
      SuccinctSpace.FixedWidthNatTable.readCosted_erase]
    simpa [domain, encoded, layout, ← packedInteriorLayout_eq shape] using
      SuccinctClose.bpSparseLevelEntries_getElem? hcountDomain
  have hlevelProjection : encoded / domain = level := by
    exact SuccinctClose.bpSparseLevelCell_div hdomain hcountDomain
  have hspanProjection : encoded % domain = span := by
    exact SuccinctClose.bpSparseLevelCell_mod hdomain hcountDomain
  have hspanEq : span = 2 ^ level := by
    simp [span, level, SuccinctClose.bpSparseLogSpan]
  have hspanPos : 0 < span := by
    simpa [span] using SuccinctClose.bpSparseLogSpan_pos count
  have hspanLe : span <= count := by
    simpa [span] using
      SuccinctClose.bpSparseLogSpan_le_self hgeo.count_pos
  have hmacro : macroIdx < layout.macroSampleCount := by
    have hmul : macroIdx * layout.macroSize <= layout.blockCount := by omega
    have hdiv : macroIdx <= layout.blockCount / layout.macroSize :=
      (Nat.le_div_iff_mul_le hmacroSizePos).2 hmul
    simpa [SuccinctClose.RelativeRmm.Layout.macroSampleCount] using
      (Nat.lt_succ_of_le hdiv)
  have hlocal : localStart < layout.macroSize := by omega
  have hlevel : level < layout.levelCount := by
    have hmono := SuccinctRank.machineWordBits_mono_le
      hcountLe
    have hlog : Nat.log2 count <= Nat.log2 layout.macroSize := by
      simpa [SuccinctRank.machineWordBits] using hmono
    simpa [level, layout, SuccinctClose.RelativeRmm.Layout.levelCount,
      SuccinctClose.RelativeRmm.Layout.offsetWidth,
      SuccinctRank.machineWordBits] using (Nat.lt_succ_of_le hlog)
  have hleftLocal : localStart + 2 ^ level <= layout.macroSize := by
    rw [← hspanEq]
    omega
  have hleftBlock :
      macroIdx * layout.macroSize + localStart + 2 ^ level <=
        layout.blockCount := by
    rw [← hspanEq]
    omega
  have hrightLocal : rightStart < layout.macroSize := by
    simp [rightStart]
    omega
  have hrightLocalSpan : rightStart + 2 ^ level <= layout.macroSize := by
    rw [← hspanEq]
    simp [rightStart]
    omega
  have hrightBlock :
      macroIdx * layout.macroSize + rightStart + 2 ^ level <=
        layout.blockCount := by
    rw [← hspanEq]
    simp [rightStart]
    omega
  have hencodedFits : PackedReviewerNatFits shape.size encoded := by
    exact packedReviewerLocalSparseLevelCell_fits shape count (by
      simpa [domain, layout] using hcountDomain)
  have hmacroIdxFits : PackedReviewerNatFits shape.size macroIdx := by
    apply packedReviewerNatFits_of_le_twoMul_add_fiveTwelve
    omega
  have hlocalStartFits : PackedReviewerNatFits shape.size localStart := by
    apply packedReviewerNatFits_of_le_twoMul_add_fiveTwelve
    omega
  have hcountFits : PackedReviewerNatFits shape.size count := by
    apply packedReviewerNatFits_of_le_twoMul_add_fiveTwelve
    omega
  have hrightCont : forall left : PackedReviewerCandidate,
      PackedReviewerCandidateScalarFits shape left ->
        PackedReviewerInteriorScalarCertificate shape invocation
          (.candidateContinuation (.localTwoRight left outer)) := by
    intro left hleft
    apply PackedReviewerInteriorScalarCertificate.candidateContinuation
    · intro value hmem
      simp [packedReviewerCandidateContinuationNatFields] at hmem
      rcases hmem with hleftMem | houterMem
      · exact hleft.scalar_fields value hleftMem
      · exact houter.candidate_scalar_fields value houterMem
    · intro right hright
      simpa [packedReviewerInteriorFinishCandidate] using
        houter.candidate_finish (SuccinctClose.bpCandidateMerge? left right)
          (hleft.merge hright)
  have hleftCont :
      PackedReviewerInteriorScalarCertificate shape invocation
        (.candidateContinuation
          (.localTwoLeft shape.size macroIdx localStart count encoded outer)) := by
    apply PackedReviewerInteriorScalarCertificate.candidateContinuation
    · intro value hmem
      simp [packedReviewerCandidateContinuationNatFields] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl | houterMem
      · exact packedReviewerInputSize_lt_two_pow_cellWidth shape.size
      · exact hmacroIdxFits
      · exact hlocalStartFits
      · exact hcountFits
      · exact hencodedFits
      · exact houter.candidate_scalar_fields value houterMem
    · intro left hleft
      have hright := hrightCont left hleft
      have hstart :=
        packedReviewerInteriorStartLocalSpan_scalarCertificate shape invocation
          macroIdx rightStart level (.localTwoRight left outer) hright
          hinvocation hmacro hlevel hrightLocal hrightLocalSpan hrightBlock
      simpa [packedReviewerInteriorFinishCandidate, domain, encoded, level,
        span, rightStart, layout, hlevelProjection, hspanProjection] using hstart
  have hleftStart :=
    packedReviewerInteriorStartLocalSpan_scalarCertificate shape invocation
      macroIdx localStart level
      (.localTwoLeft shape.size macroIdx localStart count encoded outer)
      hleftCont hinvocation hmacro hlevel hlocal hleftLocal hleftBlock
  have hread := spec.start_canonicalScalarFits shape invocation hinvocation
  apply PackedReviewerInteriorScalarCertificate.stateRead spec
    (spec.start shape invocation)
    (.localLevel shape.size macroIdx localStart count outer) hread
  apply PackedReviewerInteriorScalarCertificate.natContinuation
  · intro value hmem
    simp [packedReviewerInteriorNatContinuationNatFields] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | houterMem
    · exact packedReviewerInputSize_lt_two_pow_cellWidth shape.size
    · exact hmacroIdxFits
    · exact hlocalStartFits
    · exact hcountFits
    · exact houter.candidate_scalar_fields value houterMem
  · rw [hencoded]
    simpa [spec, packedReviewerInteriorFinishNat, domain, encoded, layout,
      hlevelProjection] using hleftStart

private theorem packedReviewerInteriorStartGlobalTwo_scalarCertificate
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (macroStart macroSpanCount : Nat)
    (outer : PackedReviewerCandidateContinuation)
    (houter :
      PackedReviewerInteriorScalarCertificate shape invocation
        (.candidateContinuation outer))
    (hinvocation :
      PackedReviewerInteriorInvocationScalarFits shape invocation)
    (hgeo : PackedReviewerGlobalTwoGeo shape macroStart macroSpanCount) :
    PackedReviewerInteriorScalarCertificate shape invocation
      (.state
        (packedReviewerInteriorStartGlobalTwo invocation shape.size macroStart
          macroSpanCount outer)) := by
  let layout := packedInteriorLayout shape.size
  let domain := SuccinctClose.bpSparseLevelDomain layout.macroSampleCount
  let encoded := SuccinctClose.bpSparseLevelCell domain macroSpanCount
  let level := Nat.log2 macroSpanCount
  let span := SuccinctClose.bpSparseLogSpan macroSpanCount
  let rightStart := macroStart + macroSpanCount - span
  let spec := PackedReviewerInteriorNatSpec.globalLevel macroSpanCount
  have hvalid := SuccinctClose.RelativeRmm.canonicalLayout_valid shape
  have hcountPos : 0 < macroSpanCount := hgeo.count_pos
  have hmacroBound :
      macroStart + macroSpanCount <= layout.macroSampleCount := by
    simpa [layout] using hgeo.macro_bound
  have hblockBound :
      (macroStart + macroSpanCount) * layout.macroSize <=
        layout.blockCount := by
    simpa [layout] using hgeo.block_bound
  have hcountLe : macroSpanCount <= layout.macroSampleCount := by omega
  have hmacroSizePos : 0 < layout.macroSize := by
    simpa [layout, ← packedInteriorLayout_eq shape] using hvalid.macroSize_pos
  have hcountPacked : layout.blockCount <= 2 * shape.size := by
    have hcount :=
      SuccinctClose.canonicalBPRelativeSummaryBlockCountRaw_le_bpCode_length
        shape
    rw [CartesianShape.bpCode_length] at hcount
    simpa [layout, ← packedInteriorLayout_eq shape] using hcount
  have hmacroCount :
      layout.macroSampleCount <= layout.blockCount + 1 := by
    simp [SuccinctClose.RelativeRmm.Layout.macroSampleCount]
    exact Nat.div_le_self _ _
  have hdomain : 2 <= domain :=
    SuccinctClose.two_le_bpSparseLevelDomain _
  have hcountDomain : macroSpanCount < domain := by
    simpa only [domain] using
      (SuccinctClose.bpSparseLevelDomain_covers
        (bound := layout.macroSampleCount) (count := macroSpanCount) hcountLe)
  have hencoded : spec.expected shape = some encoded := by
    simp only [spec, PackedReviewerInteriorNatSpec.expected,
      SuccinctSpace.FixedWidthNatTable.readCosted_erase]
    simpa [domain, encoded, layout, ← packedInteriorLayout_eq shape] using
      SuccinctClose.bpSparseLevelEntries_getElem? hcountDomain
  have hlevelProjection : encoded / domain = level := by
    exact SuccinctClose.bpSparseLevelCell_div hdomain hcountDomain
  have hspanProjection : encoded % domain = span := by
    exact SuccinctClose.bpSparseLevelCell_mod hdomain hcountDomain
  have hspanEq : span = 2 ^ level := by
    simp [span, level, SuccinctClose.bpSparseLogSpan]
  have hspanPos : 0 < span := by
    simpa [span] using SuccinctClose.bpSparseLogSpan_pos macroSpanCount
  have hspanLe : span <= macroSpanCount := by
    simpa [span] using
      SuccinctClose.bpSparseLogSpan_le_self hgeo.count_pos
  have hmacro : macroStart < layout.macroSampleCount := by omega
  have hlevel : level < layout.globalLevelCount := by
    have hmono := SuccinctRank.machineWordBits_mono_le
      hcountLe
    have hlog : Nat.log2 macroSpanCount <=
        Nat.log2 layout.macroSampleCount := by
      simpa [SuccinctRank.machineWordBits] using hmono
    simpa [level, layout,
      SuccinctClose.RelativeRmm.Layout.globalLevelCount,
      SuccinctRank.machineWordBits] using (Nat.lt_succ_of_le hlog)
  have hleftMacro : macroStart + 2 ^ level <= layout.macroSampleCount := by
    rw [← hspanEq]
    omega
  have hleftBlock :
      macroStart * layout.macroSize + 2 ^ level * layout.macroSize <=
        layout.blockCount := by
    calc
      macroStart * layout.macroSize + 2 ^ level * layout.macroSize =
          (macroStart + 2 ^ level) * layout.macroSize := by
            rw [Nat.add_mul]
      _ <= (macroStart + macroSpanCount) * layout.macroSize :=
        Nat.mul_le_mul_right layout.macroSize (by
          rw [← hspanEq]
          omega)
      _ <= layout.blockCount := hblockBound
  have hrightMacro : rightStart < layout.macroSampleCount := by
    simp [rightStart]
    omega
  have hrightMacroSpan :
      rightStart + 2 ^ level <= layout.macroSampleCount := by
    rw [← hspanEq]
    simp [rightStart]
    omega
  have hrightBlock :
      rightStart * layout.macroSize + 2 ^ level * layout.macroSize <=
        layout.blockCount := by
    rw [← hspanEq]
    have hrightEnd : rightStart + span = macroStart + macroSpanCount := by
      simp [rightStart]
      omega
    calc
      rightStart * layout.macroSize + span * layout.macroSize =
          (rightStart + span) * layout.macroSize := by
            rw [Nat.add_mul]
      _ = (macroStart + macroSpanCount) * layout.macroSize := by
        rw [hrightEnd]
      _ <= layout.blockCount := hblockBound
  have hencodedFits : PackedReviewerNatFits shape.size encoded := by
    exact packedReviewerGlobalSparseLevelCell_fits shape macroSpanCount (by
      simpa [domain, layout] using hcountDomain)
  have hmacroStartFits : PackedReviewerNatFits shape.size macroStart := by
    apply packedReviewerNatFits_of_le_twoMul_add_fiveTwelve
    omega
  have hmacroSpanCountFits :
      PackedReviewerNatFits shape.size macroSpanCount := by
    apply packedReviewerNatFits_of_le_twoMul_add_fiveTwelve
    omega
  have hrightCont : forall left : PackedReviewerCandidate,
      PackedReviewerCandidateScalarFits shape left ->
        PackedReviewerInteriorScalarCertificate shape invocation
          (.candidateContinuation (.globalTwoRight left outer)) := by
    intro left hleft
    apply PackedReviewerInteriorScalarCertificate.candidateContinuation
    · intro value hmem
      simp [packedReviewerCandidateContinuationNatFields] at hmem
      rcases hmem with hleftMem | houterMem
      · exact hleft.scalar_fields value hleftMem
      · exact houter.candidate_scalar_fields value houterMem
    · intro right hright
      simpa [packedReviewerInteriorFinishCandidate] using
        houter.candidate_finish (SuccinctClose.bpCandidateMerge? left right)
          (hleft.merge hright)
  have hleftCont :
      PackedReviewerInteriorScalarCertificate shape invocation
        (.candidateContinuation
          (.globalTwoLeft shape.size macroStart macroSpanCount encoded
            outer)) := by
    apply PackedReviewerInteriorScalarCertificate.candidateContinuation
    · intro value hmem
      simp [packedReviewerCandidateContinuationNatFields] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | houterMem
      · exact packedReviewerInputSize_lt_two_pow_cellWidth shape.size
      · exact hmacroStartFits
      · exact hmacroSpanCountFits
      · exact hencodedFits
      · exact houter.candidate_scalar_fields value houterMem
    · intro left hleft
      have hright := hrightCont left hleft
      have hstart :=
        packedReviewerInteriorStartGlobalSpan_scalarCertificate shape
          invocation rightStart level (.globalTwoRight left outer) hright
          hinvocation hrightMacro hlevel hrightMacroSpan hrightBlock
      simpa [packedReviewerInteriorFinishCandidate, domain, encoded, level,
        span, rightStart, layout, hlevelProjection, hspanProjection] using hstart
  have hleftStart :=
    packedReviewerInteriorStartGlobalSpan_scalarCertificate shape invocation
      macroStart level
      (.globalTwoLeft shape.size macroStart macroSpanCount encoded outer)
      hleftCont hinvocation hmacro hlevel hleftMacro hleftBlock
  have hread := spec.start_canonicalScalarFits shape invocation hinvocation
  apply PackedReviewerInteriorScalarCertificate.stateRead spec
    (spec.start shape invocation)
    (.globalLevel shape.size macroStart macroSpanCount outer) hread
  apply PackedReviewerInteriorScalarCertificate.natContinuation
  · intro value hmem
    simp [packedReviewerInteriorNatContinuationNatFields] at hmem
    rcases hmem with rfl | rfl | rfl | houterMem
    · exact packedReviewerInputSize_lt_two_pow_cellWidth shape.size
    · exact hmacroStartFits
    · exact hmacroSpanCountFits
    · exact houter.candidate_scalar_fields value houterMem
  · rw [hencoded]
    simpa [spec, packedReviewerInteriorFinishNat, domain, encoded, layout,
      hlevelProjection] using hleftStart

private theorem packedReviewerInteriorBlockCoordinate_fits
    (shape : CartesianShape) (value : Nat)
    (hvalue :
      value <= (packedInteriorLayout shape.size).blockCount + 1) :
    PackedReviewerNatFits shape.size value := by
  apply packedReviewerNatFits_of_le_twoMul_add_fiveTwelve
  have hcount :=
    SuccinctClose.canonicalBPRelativeSummaryBlockCountRaw_le_bpCode_length
      shape
  rw [CartesianShape.bpCode_length] at hcount
  have hcountPacked :
      (packedInteriorLayout shape.size).blockCount <= 2 * shape.size := by
    simpa [← packedInteriorLayout_eq shape] using hcount
  omega

private theorem packedReviewerInteriorLocalCoordinate_fits
    (shape : CartesianShape) (value : Nat)
    (hvalue : value <= (packedInteriorLayout shape.size).macroSize) :
    PackedReviewerNatFits shape.size value := by
  apply packedReviewerNatFits_of_le_twoMul_add_fiveTwelve
  have hsquare :=
    packedReviewerLog2SuccSquare_le_self_add_twoFiftySix shape.size
  have hmacroSizePacked :
      (packedInteriorLayout shape.size).macroSize <= shape.size + 256 := by
    simpa [packedInteriorLayout,
      SuccinctClose.RelativeRmm.Layout.macroSize, packedSummaryBase] using
      hsquare
  omega

private theorem packedReviewerFinish_scalarCertificate
    (shape : CartesianShape) (invocation : PackedReviewerInvocation) :
    PackedReviewerInteriorScalarCertificate shape invocation
      (.candidateContinuation .finish) := by
  apply PackedReviewerInteriorScalarCertificate.candidateContinuation
  · simp [packedReviewerCandidateContinuationNatFields]
  · intro candidate hcandidate
    simpa [packedReviewerInteriorFinishCandidate] using
      PackedReviewerInteriorScalarCertificate.stateDone
        (invocation := invocation) candidate hcandidate

private theorem packedReviewerAdjacentLeft_scalarCertificate
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (macroStart rightCount : Nat)
    (hinvocation :
      PackedReviewerInteriorInvocationScalarFits shape invocation)
    (hmacroStart : PackedReviewerNatFits shape.size macroStart)
    (hrightCount : PackedReviewerNatFits shape.size rightCount)
    (hrightGeo :
      PackedReviewerLocalTwoGeo shape (macroStart + 1) 0 rightCount) :
    PackedReviewerInteriorScalarCertificate shape invocation
      (.candidateContinuation
        (.adjacentLeft shape.size macroStart rightCount .finish)) := by
  have hrightCont : forall left : PackedReviewerCandidate,
      PackedReviewerCandidateScalarFits shape left ->
        PackedReviewerInteriorScalarCertificate shape invocation
          (.candidateContinuation (.adjacentRight left .finish)) := by
    intro left hleft
    apply PackedReviewerInteriorScalarCertificate.candidateContinuation
    · intro value hmem
      simp [packedReviewerCandidateContinuationNatFields] at hmem
      exact hleft.scalar_fields value hmem
    · intro right hright
      simpa [packedReviewerInteriorFinishCandidate] using
        PackedReviewerInteriorScalarCertificate.stateDone
          (invocation := invocation)
          (SuccinctClose.bpCandidateMerge? left right) (hleft.merge hright)
  apply PackedReviewerInteriorScalarCertificate.candidateContinuation
  · intro value hmem
    simp [packedReviewerCandidateContinuationNatFields] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact packedReviewerInputSize_lt_two_pow_cellWidth shape.size
    · exact hmacroStart
    · exact hrightCount
  · intro left hleft
    have hstart :=
      packedReviewerInteriorStartLocalTwo_scalarCertificate shape invocation
        (macroStart + 1) 0 rightCount (.adjacentRight left .finish)
        (hrightCont left hleft) hinvocation hrightGeo
    simpa [packedReviewerInteriorFinishCandidate] using hstart

private theorem packedReviewerLeftMiddleLeft_scalarCertificate
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (macroStart middleCount : Nat)
    (hinvocation :
      PackedReviewerInteriorInvocationScalarFits shape invocation)
    (hmacroStart : PackedReviewerNatFits shape.size macroStart)
    (hmiddleCount : PackedReviewerNatFits shape.size middleCount)
    (hmiddleGeo :
      PackedReviewerGlobalTwoGeo shape (macroStart + 1) middleCount) :
    PackedReviewerInteriorScalarCertificate shape invocation
      (.candidateContinuation
        (.leftMiddleLeft shape.size macroStart middleCount .finish)) := by
  have hmiddleCont : forall left : PackedReviewerCandidate,
      PackedReviewerCandidateScalarFits shape left ->
        PackedReviewerInteriorScalarCertificate shape invocation
          (.candidateContinuation (.leftMiddleMiddle left .finish)) := by
    intro left hleft
    apply PackedReviewerInteriorScalarCertificate.candidateContinuation
    · intro value hmem
      simp [packedReviewerCandidateContinuationNatFields] at hmem
      exact hleft.scalar_fields value hmem
    · intro middle hmiddle
      simpa [packedReviewerInteriorFinishCandidate] using
        PackedReviewerInteriorScalarCertificate.stateDone
          (invocation := invocation)
          (SuccinctClose.bpCandidateMerge? left middle)
          (hleft.merge hmiddle)
  apply PackedReviewerInteriorScalarCertificate.candidateContinuation
  · intro value hmem
    simp [packedReviewerCandidateContinuationNatFields] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact packedReviewerInputSize_lt_two_pow_cellWidth shape.size
    · exact hmacroStart
    · exact hmiddleCount
  · intro left hleft
    have hstart :=
      packedReviewerInteriorStartGlobalTwo_scalarCertificate shape invocation
        (macroStart + 1) middleCount (.leftMiddleMiddle left .finish)
        (hmiddleCont left hleft) hinvocation hmiddleGeo
    simpa [packedReviewerInteriorFinishCandidate] using hstart

private theorem packedReviewerCrossLeft_scalarCertificate
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (macroStart middleCount rightCount : Nat)
    (hinvocation :
      PackedReviewerInteriorInvocationScalarFits shape invocation)
    (hmacroStart : PackedReviewerNatFits shape.size macroStart)
    (hmiddleCount : PackedReviewerNatFits shape.size middleCount)
    (hrightCount : PackedReviewerNatFits shape.size rightCount)
    (hmiddleGeo :
      PackedReviewerGlobalTwoGeo shape (macroStart + 1) middleCount)
    (hrightGeo :
      PackedReviewerLocalTwoGeo shape
        (macroStart + 1 + middleCount) 0 rightCount) :
    PackedReviewerInteriorScalarCertificate shape invocation
      (.candidateContinuation
        (.crossLeft shape.size macroStart middleCount rightCount .finish)) := by
  have hrightCont : forall left middle : PackedReviewerCandidate,
      PackedReviewerCandidateScalarFits shape left ->
        PackedReviewerCandidateScalarFits shape middle ->
          PackedReviewerInteriorScalarCertificate shape invocation
            (.candidateContinuation (.crossRight left middle .finish)) := by
    intro left middle hleft hmiddle
    apply PackedReviewerInteriorScalarCertificate.candidateContinuation
    · intro value hmem
      simp [packedReviewerCandidateContinuationNatFields] at hmem
      rcases hmem with hleftMem | hmiddleMem
      · exact hleft.scalar_fields value hleftMem
      · exact hmiddle.scalar_fields value hmiddleMem
    · intro right hright
      simpa [packedReviewerInteriorFinishCandidate] using
        PackedReviewerInteriorScalarCertificate.stateDone
          (invocation := invocation)
          (SuccinctClose.bpCandidateMerge3? left middle right)
          (hleft.merge3 hmiddle hright)
  have hmiddleCont : forall left : PackedReviewerCandidate,
      PackedReviewerCandidateScalarFits shape left ->
        PackedReviewerInteriorScalarCertificate shape invocation
          (.candidateContinuation
            (.crossMiddle shape.size macroStart middleCount rightCount left
              .finish)) := by
    intro left hleft
    apply PackedReviewerInteriorScalarCertificate.candidateContinuation
    · intro value hmem
      simp [packedReviewerCandidateContinuationNatFields] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | hleftMem
      · exact packedReviewerInputSize_lt_two_pow_cellWidth shape.size
      · exact hmacroStart
      · exact hmiddleCount
      · exact hrightCount
      · exact hleft.scalar_fields value hleftMem
    · intro middle hmiddle
      have hstart :=
        packedReviewerInteriorStartLocalTwo_scalarCertificate shape invocation
          (macroStart + 1 + middleCount) 0 rightCount
          (.crossRight left middle .finish)
          (hrightCont left middle hleft hmiddle) hinvocation hrightGeo
      simpa [packedReviewerInteriorFinishCandidate] using hstart
  apply PackedReviewerInteriorScalarCertificate.candidateContinuation
  · intro value hmem
    simp [packedReviewerCandidateContinuationNatFields] at hmem
    rcases hmem with rfl | rfl | rfl | rfl
    · exact packedReviewerInputSize_lt_two_pow_cellWidth shape.size
    · exact hmacroStart
    · exact hmiddleCount
    · exact hrightCount
  · intro left hleft
    have hstart :=
      packedReviewerInteriorStartGlobalTwo_scalarCertificate shape invocation
        (macroStart + 1) middleCount
        (.crossMiddle shape.size macroStart middleCount rightCount left
          .finish)
        (hmiddleCont left hleft) hinvocation hmiddleGeo
    simpa [packedReviewerInteriorFinishCandidate] using hstart

private theorem packedReviewerInteriorStartRaw_scalarCertificate
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (startBlock spanCount : Nat)
    (hinvocation :
      PackedReviewerInteriorInvocationScalarFits shape invocation)
    (hrange :
      startBlock + spanCount <= packedSummaryBlockCountRaw shape.size) :
    PackedReviewerInteriorScalarCertificate shape invocation
      (.state
        (packedReviewerInteriorStartRaw invocation shape.size startBlock
          spanCount)) := by
  let layout := packedInteriorLayout shape.size
  let macroStart := startBlock / layout.macroSize
  let localStart := startBlock % layout.macroSize
  let firstCount := layout.macroSize - localStart
  let rest := spanCount - firstCount
  let middleCount := rest / layout.macroSize
  let rightCount := rest % layout.macroSize
  have hvalid := SuccinctClose.RelativeRmm.canonicalLayout_valid shape
  have hmacroSizePos : 0 < layout.macroSize := by
    simpa [layout, ← packedInteriorLayout_eq shape] using
      hvalid.macroSize_pos
  have hrangeLayout : startBlock + spanCount <= layout.blockCount := by
    simpa [layout, packedInteriorLayout] using hrange
  have hlocalStart : localStart < layout.macroSize := by
    exact Nat.mod_lt startBlock hmacroSizePos
  have hstartEq :
      macroStart * layout.macroSize + localStart = startBlock := by
    simpa [macroStart, localStart, Nat.mul_comm] using
      Nat.div_add_mod startBlock layout.macroSize
  have hfinish :=
    packedReviewerFinish_scalarCertificate shape invocation
  by_cases hzero : spanCount = 0
  · have hnone : PackedReviewerCandidateScalarFits shape none := by trivial
    simpa [packedReviewerInteriorStartRaw, hzero] using
      PackedReviewerInteriorScalarCertificate.stateDone
        (invocation := invocation) none hnone
  · have hspanPos : 0 < spanCount := Nat.pos_of_ne_zero hzero
    by_cases hwithin :
        spanCount <= layout.macroSize - startBlock % layout.macroSize
    · have hgeo :
          PackedReviewerLocalTwoGeo shape macroStart localStart spanCount := by
        refine ⟨hspanPos, ?_, ?_⟩
        · have hmacroEq : (packedInteriorLayout shape.size).macroSize =
              layout.macroSize := rfl
          have hlocalDef : localStart = startBlock % layout.macroSize := rfl
          omega
        · simpa [layout] using (by omega :
            macroStart * layout.macroSize + localStart + spanCount <=
              layout.blockCount)
      have hstart :=
        packedReviewerInteriorStartLocalTwo_scalarCertificate shape invocation
          macroStart localStart spanCount .finish hfinish hinvocation hgeo
      simpa [packedReviewerInteriorStartRaw, hzero, hwithin, layout,
        macroStart, localStart] using hstart
    · have hfirstPos : 0 < firstCount := by
        simp [firstCount]
        omega
      have hfirstLt : firstCount < spanCount := by
        simp [firstCount, localStart] at hwithin
        omega
      have hrestPos : 0 < rest := by
        simp [rest]
        omega
      have hspanEq : spanCount = firstCount + rest := by
        simp [rest]
        omega
      have hleftEnd :
          macroStart * layout.macroSize + localStart + firstCount =
            (macroStart + 1) * layout.macroSize := by
        rw [Nat.add_mul]
        simp [firstCount]
        omega
      have hrestDivMod :
          rest = middleCount * layout.macroSize + rightCount := by
        simpa [middleCount, rightCount, Nat.mul_comm] using
          (Nat.div_add_mod rest layout.macroSize).symm
      have hleftGeo :
          PackedReviewerLocalTwoGeo shape macroStart localStart firstCount := by
        refine ⟨hfirstPos, ?_, ?_⟩
        · have hmacroEq : (packedInteriorLayout shape.size).macroSize =
              layout.macroSize := rfl
          simp [firstCount]
          omega
        · simpa [layout] using (by omega :
            macroStart * layout.macroSize + localStart + firstCount <=
              layout.blockCount)
      have hmacroStartFits :
          PackedReviewerNatFits shape.size macroStart := by
        apply packedReviewerInteriorBlockCoordinate_fits
        have hdiv : macroStart <= startBlock := by
          simpa [macroStart] using
            Nat.div_le_self startBlock layout.macroSize
        have hblockEq : (packedInteriorLayout shape.size).blockCount =
            packedSummaryBlockCountRaw shape.size := rfl
        have hmacroDef : macroStart = startBlock / layout.macroSize := rfl
        omega
      have hmiddleCountFits :
          PackedReviewerNatFits shape.size middleCount := by
        apply packedReviewerInteriorBlockCoordinate_fits
        have hdiv : middleCount <= rest := by
          simpa [middleCount] using Nat.div_le_self rest layout.macroSize
        have hblockEq : (packedInteriorLayout shape.size).blockCount =
            packedSummaryBlockCountRaw shape.size := rfl
        have hmiddleDef : middleCount = rest / layout.macroSize := rfl
        have hrestLe : rest <= spanCount := Nat.sub_le _ _
        omega
      have hrightCountFits :
          PackedReviewerNatFits shape.size rightCount := by
        apply packedReviewerInteriorLocalCoordinate_fits
        have hmod : rightCount < layout.macroSize := by
          exact Nat.mod_lt rest hmacroSizePos
        have hmacroEq : (packedInteriorLayout shape.size).macroSize =
            layout.macroSize := rfl
        have hrightDef : rightCount = rest % layout.macroSize := rfl
        omega
      by_cases hmiddle : middleCount = 0
      · have hmiddleZero : middleCount * layout.macroSize = 0 := by
          rw [hmiddle, Nat.zero_mul]
        have hrightEq : rightCount = rest := by omega
        have hrightGeo :
            PackedReviewerLocalTwoGeo shape (macroStart + 1) 0
              rightCount := by
          refine ⟨by omega, ?_, ?_⟩
          · have hmod : rightCount < layout.macroSize := by
              exact Nat.mod_lt rest hmacroSizePos
            have hmacroEq : (packedInteriorLayout shape.size).macroSize =
                layout.macroSize := rfl
            have hrightDef : rightCount = rest % layout.macroSize := rfl
            omega
          · simpa [layout] using (by omega :
              (macroStart + 1) * layout.macroSize + 0 + rightCount <=
                layout.blockCount)
        have hadjacent :=
          packedReviewerAdjacentLeft_scalarCertificate shape invocation
            macroStart rightCount hinvocation hmacroStartFits
            hrightCountFits hrightGeo
        have hstart :=
          packedReviewerInteriorStartLocalTwo_scalarCertificate shape
            invocation macroStart localStart firstCount
            (.adjacentLeft shape.size macroStart rightCount .finish)
            hadjacent hinvocation hleftGeo
        simpa [packedReviewerInteriorStartRaw, hzero, hwithin, layout,
          macroStart, localStart, firstCount, rest, middleCount, rightCount,
          hmiddle] using hstart
      · have hmiddlePos : 0 < middleCount := Nat.pos_of_ne_zero hmiddle
        by_cases hright : rightCount = 0
        · have hmiddleEnd :
              (macroStart + 1 + middleCount) * layout.macroSize =
                startBlock + spanCount := by
            calc
              (macroStart + 1 + middleCount) * layout.macroSize =
                  (macroStart + 1) * layout.macroSize +
                    middleCount * layout.macroSize := by rw [Nat.add_mul]
              _ = startBlock + spanCount := by omega
          have hmiddleBlock :
              (macroStart + 1 + middleCount) * layout.macroSize <=
                layout.blockCount := by omega
          have hmiddleMacro :
              macroStart + 1 + middleCount <= layout.macroSampleCount := by
            have hdiv :
                macroStart + 1 + middleCount <=
                  layout.blockCount / layout.macroSize :=
              (Nat.le_div_iff_mul_le hmacroSizePos).2 hmiddleBlock
            simp [SuccinctClose.RelativeRmm.Layout.macroSampleCount]
            omega
          have hmiddleGeo :
              PackedReviewerGlobalTwoGeo shape (macroStart + 1)
                middleCount := by
            exact ⟨hmiddlePos, hmiddleMacro, hmiddleBlock⟩
          have hleftMiddle :=
            packedReviewerLeftMiddleLeft_scalarCertificate shape invocation
              macroStart middleCount hinvocation hmacroStartFits
              hmiddleCountFits hmiddleGeo
          have hstart :=
            packedReviewerInteriorStartLocalTwo_scalarCertificate shape
              invocation macroStart localStart firstCount
              (.leftMiddleLeft shape.size macroStart middleCount .finish)
              hleftMiddle hinvocation hleftGeo
          simpa [packedReviewerInteriorStartRaw, hzero, hwithin, layout,
            macroStart, localStart, firstCount, rest, middleCount, rightCount,
            hmiddle, hright] using hstart
        · have hrightPos : 0 < rightCount := Nat.pos_of_ne_zero hright
          have htotalEnd :
              (macroStart + 1 + middleCount) * layout.macroSize +
                  rightCount =
                startBlock + spanCount := by
            calc
              (macroStart + 1 + middleCount) * layout.macroSize +
                    rightCount =
                  (macroStart + 1) * layout.macroSize +
                    middleCount * layout.macroSize + rightCount := by
                      rw [Nat.add_mul]
              _ = startBlock + spanCount := by omega
          have hmiddleBlock :
              (macroStart + 1 + middleCount) * layout.macroSize <=
                layout.blockCount := by omega
          have hmiddleMacro :
              macroStart + 1 + middleCount <= layout.macroSampleCount := by
            have hdiv :
                macroStart + 1 + middleCount <=
                  layout.blockCount / layout.macroSize :=
              (Nat.le_div_iff_mul_le hmacroSizePos).2 hmiddleBlock
            simp [SuccinctClose.RelativeRmm.Layout.macroSampleCount]
            omega
          have hmiddleGeo :
              PackedReviewerGlobalTwoGeo shape (macroStart + 1)
                middleCount := by
            exact ⟨hmiddlePos, hmiddleMacro, hmiddleBlock⟩
          have hrightGeo :
              PackedReviewerLocalTwoGeo shape
                (macroStart + 1 + middleCount) 0 rightCount := by
            refine ⟨hrightPos, ?_, ?_⟩
            · have hmod : rightCount < layout.macroSize := by
                exact Nat.mod_lt rest hmacroSizePos
              have hmacroEq : (packedInteriorLayout shape.size).macroSize =
                  layout.macroSize := rfl
              have hrightDef : rightCount = rest % layout.macroSize := rfl
              omega
            · simpa [layout] using (by omega :
                (macroStart + 1 + middleCount) * layout.macroSize + 0 +
                    rightCount <= layout.blockCount)
          have hcross :=
            packedReviewerCrossLeft_scalarCertificate shape invocation
              macroStart middleCount rightCount hinvocation hmacroStartFits
              hmiddleCountFits hrightCountFits hmiddleGeo hrightGeo
          have hstart :=
            packedReviewerInteriorStartLocalTwo_scalarCertificate shape
              invocation macroStart localStart firstCount
              (.crossLeft shape.size macroStart middleCount rightCount .finish)
              hcross hinvocation hleftGeo
          simpa [packedReviewerInteriorStartRaw, hzero, hwithin, layout,
            macroStart, localStart, firstCount, rest, middleCount, rightCount,
            hmiddle, hright] using hstart

private theorem packedReviewerInteriorStart_scalarCertificate
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (startBlock spanCount : Nat)
    (hinvocation :
      PackedReviewerInteriorInvocationScalarFits shape invocation)
    (hrange :
      startBlock + spanCount <= packedSummaryBlockCountRaw shape.size) :
    PackedReviewerInteriorScalarCertificate shape invocation
      (.state
        (packedReviewerInteriorStart invocation shape.size startBlock
          spanCount)) := by
  have hraw :=
    packedReviewerInteriorStartRaw_scalarCertificate shape invocation
      startBlock spanCount hinvocation hrange
  simpa [packedReviewerInteriorStart] using
    hraw.normalize
      (packedReviewerInteriorRemaining
        (packedReviewerInteriorStartRaw invocation shape.size startBlock
          spanCount) + 1)
/-! ## Origin-preserving canonical orbit -/

/-- The exact proof-side orbit generated by repeated canonical controller steps. -/
private def packedReviewerInteriorCanonicalRun
    (shape : CartesianShape) : Nat -> PackedReviewerInteriorState ->
      PackedReviewerInteriorState
  | 0, state => state
  | fuel + 1, state =>
      packedReviewerInteriorCanonicalStep shape
        (packedReviewerInteriorCanonicalRun shape fuel state)

/--
The single semantic scalar lemma needed by the public orbit interface.

Its proof is deliberately organized around the eight exact `NatSpec` reads
above.  In particular, a sparse-level decoded cell is bounded through its
corresponding level-table overhead term, rather than by comparing its declared
multiword width with one reviewer cell.
-/
private theorem packedReviewerInteriorCanonicalRun_scalar_and_result
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (startBlock spanCount fuel : Nat)
    (hinvocation :
      PackedReviewerInteriorInvocationScalarFits shape invocation)
    (hrange :
      startBlock + spanCount <= packedSummaryBlockCountRaw shape.size) :
    let state :=
      packedReviewerInteriorCanonicalRun shape fuel
        (packedReviewerInteriorStart invocation shape.size startBlock spanCount)
    (forall value,
        value ∈ packedReviewerInteriorStateNatFields state ->
          PackedReviewerNatFits shape.size value) ∧
      (forall candidate,
        packedReviewerInteriorResult state = some candidate ->
          PackedReviewerCandidateScalarFits shape candidate) := by
  have hstart :=
    packedReviewerInteriorStart_scalarCertificate shape invocation startBlock
      spanCount hinvocation hrange
  have hrun : forall runFuel : Nat,
      PackedReviewerInteriorScalarCertificate shape invocation
        (.state
          (packedReviewerInteriorCanonicalRun shape runFuel
            (packedReviewerInteriorStart invocation shape.size startBlock
              spanCount))) := by
    intro runFuel
    induction runFuel with
    | zero =>
        simpa [packedReviewerInteriorCanonicalRun] using hstart
    | succ runFuel ih =>
        simpa [packedReviewerInteriorCanonicalRun] using ih.canonicalStep
  have hstate := hrun fuel
  exact ⟨hstate.state_scalar_fields hinvocation,
    hstate.state_result_fits⟩

/--
Canonical scalar/provenance invariant for the first-order interior protocol.
The existential is an exact orbit witness from the displayed origin; no forged
in-flight state can change `invocation`, `startBlock`, or `spanCount`.
-/
structure PackedReviewerInteriorCanonicalScalarFits
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (startBlock spanCount : Nat) (state : PackedReviewerInteriorState) : Prop where
  range : startBlock + spanCount <= packedSummaryBlockCountRaw shape.size
  invocation_operands :
    forall operand,
      operand ∈ packedReviewerInvocationOperands invocation ->
        PackedReviewerNatFits shape.size operand
  canonical_orbit :
    exists fuel,
      state =
        packedReviewerInteriorCanonicalRun shape fuel
          (packedReviewerInteriorStart invocation shape.size startBlock
            spanCount)

/-- The canonical smart constructor is the zero-step state of its own orbit. -/
theorem packedReviewerInteriorStart_canonicalScalarFits
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (startBlock spanCount : Nat)
    (hinvocation :
      forall operand,
        operand ∈ packedReviewerInvocationOperands invocation ->
          PackedReviewerNatFits shape.size operand)
    (hrange :
      startBlock + spanCount <= packedSummaryBlockCountRaw shape.size) :
    PackedReviewerInteriorCanonicalScalarFits shape invocation startBlock
      spanCount
      (packedReviewerInteriorStart invocation shape.size startBlock
        spanCount) := by
  refine ⟨hrange, hinvocation, ?_⟩
  exact ⟨0, rfl⟩

/-- One reply at the literally emitted request advances the same exact orbit. -/
theorem PackedReviewerInteriorCanonicalScalarFits.consume
    {shape : CartesianShape} {invocation : PackedReviewerInvocation}
    {startBlock spanCount : Nat} {state : PackedReviewerInteriorState}
    (hstate :
      PackedReviewerInteriorCanonicalScalarFits shape invocation startBlock
        spanCount state)
    {request : PackedReviewerLogicalRequest}
    (hrequest : packedReviewerInteriorNextRequest state = some request) :
    PackedReviewerInteriorCanonicalScalarFits shape invocation startBlock
      spanCount
      (packedReviewerInteriorConsumeReply state
        ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          request.segment request.index)) := by
  rcases hstate.canonical_orbit with ⟨fuel, hstateEq⟩
  refine ⟨hstate.range, hstate.invocation_operands, fuel + 1, ?_⟩
  rw [packedReviewerInteriorCanonicalRun]
  rw [← hstateEq]
  simp [packedReviewerInteriorCanonicalStep, hrequest]

/-- Every scalar field exposed by a canonically reachable interior state fits. -/
theorem PackedReviewerInteriorCanonicalScalarFits.scalar_fields
    {shape : CartesianShape} {invocation : PackedReviewerInvocation}
    {startBlock spanCount : Nat} {state : PackedReviewerInteriorState}
    (hstate :
      PackedReviewerInteriorCanonicalScalarFits shape invocation startBlock
        spanCount state) :
    forall value,
      value ∈ packedReviewerInteriorStateNatFields state ->
        PackedReviewerNatFits shape.size value := by
  rcases hstate.canonical_orbit with ⟨fuel, rfl⟩
  exact
    (packedReviewerInteriorCanonicalRun_scalar_and_result shape invocation
      startBlock spanCount fuel hstate.invocation_operands hstate.range).1

/-- Every successful canonical interior result has two fitting candidate fields. -/
theorem PackedReviewerInteriorCanonicalScalarFits.result_fits
    {shape : CartesianShape} {invocation : PackedReviewerInvocation}
    {startBlock spanCount : Nat} {state : PackedReviewerInteriorState}
    (hstate :
      PackedReviewerInteriorCanonicalScalarFits shape invocation startBlock
        spanCount state)
    {candidate : PackedReviewerCandidate}
    (hresult : packedReviewerInteriorResult state = some candidate) :
    PackedReviewerCandidateScalarFits shape candidate := by
  rcases hstate.canonical_orbit with ⟨fuel, rfl⟩
  exact
    (packedReviewerInteriorCanonicalRun_scalar_and_result shape invocation
      startBlock spanCount fuel hstate.invocation_operands hstate.range).2
      candidate hresult

/-! ## Canonical orbit budget and pending-request width

The structural interior measure can grow for forged table widths, so the
whole-machine budget uses these orbit-only facts instead of a descent lemma:
the pending read keeps at most eight chunks, and the continuation potential
never rises along canonical steps.
-/

private def packedReviewerInteriorPotential :
    PackedReviewerInteriorState -> Nat
  | .done _ => 0
  | .readNat _ _ continuation =>
      packedReviewerInteriorNatContinuationRemaining continuation

private theorem packedReviewerInteriorFinishCandidate_done_or_potential_lt
    (invocation : PackedReviewerInvocation)
    (value : PackedReviewerCandidate)
    (continuation : PackedReviewerCandidateContinuation) :
    (exists result,
        packedReviewerInteriorFinishCandidate invocation value continuation =
          .done result) ∨
      packedReviewerInteriorPotential
          (packedReviewerInteriorFinishCandidate invocation value
            continuation) <
        packedReviewerCandidateContinuationRemaining continuation := by
  induction continuation generalizing value with
  | finish =>
      exact Or.inl ⟨value, by simp [packedReviewerInteriorFinishCandidate]⟩
  | localTwoLeft n macroIdx localStart count encoded outer ih =>
      right
      simp [packedReviewerInteriorFinishCandidate,
        packedReviewerInteriorStartLocalSpan,
        packedReviewerInteriorReadNat,
        packedReviewerInteriorPotential,
        packedReviewerInteriorNatContinuationRemaining,
        packedReviewerCandidateContinuationRemaining]
  | localTwoRight left outer ih =>
      simpa [packedReviewerInteriorFinishCandidate,
        packedReviewerCandidateContinuationRemaining] using
        ih (SuccinctClose.bpCandidateMerge? left value)
  | globalTwoLeft n macroStart macroSpanCount encoded outer ih =>
      right
      simp [packedReviewerInteriorFinishCandidate,
        packedReviewerInteriorStartGlobalSpan,
        packedReviewerInteriorReadNat,
        packedReviewerInteriorPotential,
        packedReviewerInteriorNatContinuationRemaining,
        packedReviewerCandidateContinuationRemaining]
  | globalTwoRight left outer ih =>
      simpa [packedReviewerInteriorFinishCandidate,
        packedReviewerCandidateContinuationRemaining] using
        ih (SuccinctClose.bpCandidateMerge? left value)
  | adjacentLeft n macroStart rightCount outer ih =>
      right
      simp [packedReviewerInteriorFinishCandidate,
        packedReviewerInteriorStartLocalTwo,
        packedReviewerInteriorReadNat,
        packedReviewerInteriorPotential,
        packedReviewerInteriorNatContinuationRemaining,
        packedReviewerCandidateContinuationRemaining]
  | adjacentRight left outer ih =>
      simpa [packedReviewerInteriorFinishCandidate,
        packedReviewerCandidateContinuationRemaining] using
        ih (SuccinctClose.bpCandidateMerge? left value)
  | leftMiddleLeft n macroStart middleCount outer ih =>
      right
      simp [packedReviewerInteriorFinishCandidate,
        packedReviewerInteriorStartGlobalTwo,
        packedReviewerInteriorReadNat,
        packedReviewerInteriorPotential,
        packedReviewerInteriorNatContinuationRemaining,
        packedReviewerCandidateContinuationRemaining]
  | leftMiddleMiddle left outer ih =>
      simpa [packedReviewerInteriorFinishCandidate,
        packedReviewerCandidateContinuationRemaining] using
        ih (SuccinctClose.bpCandidateMerge? left value)
  | crossLeft n macroStart middleCount rightCount outer ih =>
      right
      simp only [packedReviewerInteriorFinishCandidate,
        packedReviewerInteriorStartGlobalTwo,
        packedReviewerInteriorReadNat,
        packedReviewerInteriorPotential,
        packedReviewerInteriorNatContinuationRemaining,
        packedReviewerCandidateContinuationRemaining]
      omega
  | crossMiddle n macroStart middleCount rightCount left outer ih =>
      right
      simp [packedReviewerInteriorFinishCandidate,
        packedReviewerInteriorStartLocalTwo,
        packedReviewerInteriorReadNat,
        packedReviewerInteriorPotential,
        packedReviewerInteriorNatContinuationRemaining,
        packedReviewerCandidateContinuationRemaining]
  | crossRight left middle outer ih =>
      simpa [packedReviewerInteriorFinishCandidate,
        packedReviewerCandidateContinuationRemaining] using
        ih (SuccinctClose.bpCandidateMerge3? left middle value)

private theorem packedReviewerInteriorFinishNat_done_or_potential_lt
    (invocation : PackedReviewerInvocation) (value : Option Nat)
    (continuation : PackedReviewerInteriorNatContinuation) :
    (exists result,
        packedReviewerInteriorFinishNat invocation value continuation =
          .done result) ∨
      packedReviewerInteriorPotential
          (packedReviewerInteriorFinishNat invocation value continuation) <
        packedReviewerInteriorNatContinuationRemaining continuation := by
  cases continuation with
  | summaryBaseline n block outer =>
      right
      simp [packedReviewerInteriorFinishNat,
        packedReviewerInteriorReadNat,
        packedReviewerInteriorPotential,
        packedReviewerInteriorNatContinuationRemaining]
  | summaryMin n block baseline outer =>
      right
      simp [packedReviewerInteriorFinishNat,
        packedReviewerInteriorReadNat,
        packedReviewerInteriorPotential,
        packedReviewerInteriorNatContinuationRemaining]
  | summaryMax n block baseline minRel outer =>
      right
      simp [packedReviewerInteriorFinishNat,
        packedReviewerInteriorReadNat,
        packedReviewerInteriorPotential,
        packedReviewerInteriorNatContinuationRemaining]
  | summaryArg n block baseline minRel maxRel outer =>
      simpa [packedReviewerInteriorFinishNat,
        packedReviewerInteriorNatContinuationRemaining] using
        packedReviewerInteriorFinishCandidate_done_or_potential_lt invocation
          ((match baseline, minRel, maxRel, value with
            | some b, some mn, some mx, some arg => some (b, mn, mx, arg)
            | _, _, _, _ => none).map
              (SuccinctClose.bpRelativeSummaryMinCandidate
                (packedInteriorLayout n).blockSize
                (packedInteriorLayout n).blocksPerSuper block)) outer
  | localOffset n macroIdx localStart level outer =>
      cases value with
      | none =>
          have hcandidate :=
            packedReviewerInteriorFinishCandidate_done_or_potential_lt
              invocation none outer
          rcases hcandidate with hdone | hlt
          · exact Or.inl (by
              simpa [packedReviewerInteriorFinishNat] using hdone)
          · exact Or.inr (by
              simp only [packedReviewerInteriorFinishNat,
                packedReviewerInteriorNatContinuationRemaining]
              omega)
      | some offset =>
          right
          simp [packedReviewerInteriorFinishNat,
            packedReviewerInteriorStartMinCandidate,
            packedReviewerInteriorReadNat,
            packedReviewerInteriorPotential,
            packedReviewerInteriorNatContinuationRemaining]
  | globalBlock n macroStart level outer =>
      cases value with
      | none =>
          have hcandidate :=
            packedReviewerInteriorFinishCandidate_done_or_potential_lt
              invocation none outer
          rcases hcandidate with hdone | hlt
          · exact Or.inl (by
              simpa [packedReviewerInteriorFinishNat] using hdone)
          · exact Or.inr (by
              simp only [packedReviewerInteriorFinishNat,
                packedReviewerInteriorNatContinuationRemaining]
              omega)
      | some block =>
          right
          simp [packedReviewerInteriorFinishNat,
            packedReviewerInteriorStartMinCandidate,
            packedReviewerInteriorReadNat,
            packedReviewerInteriorPotential,
            packedReviewerInteriorNatContinuationRemaining]
  | localLevel n macroIdx localStart count outer =>
      cases value with
      | none =>
          have hcandidate :=
            packedReviewerInteriorFinishCandidate_done_or_potential_lt
              invocation none outer
          rcases hcandidate with hdone | hlt
          · exact Or.inl (by
              simpa [packedReviewerInteriorFinishNat] using hdone)
          · exact Or.inr (by
              simp only [packedReviewerInteriorFinishNat,
                packedReviewerInteriorNatContinuationRemaining]
              omega)
      | some encoded =>
          right
          simp only [packedReviewerInteriorFinishNat,
            packedReviewerInteriorStartLocalSpan,
            packedReviewerInteriorReadNat,
            packedReviewerInteriorPotential,
            packedReviewerInteriorNatContinuationRemaining,
            packedReviewerCandidateContinuationRemaining]
          omega
  | globalLevel n macroStart macroSpanCount outer =>
      cases value with
      | none =>
          have hcandidate :=
            packedReviewerInteriorFinishCandidate_done_or_potential_lt
              invocation none outer
          rcases hcandidate with hdone | hlt
          · exact Or.inl (by
              simpa [packedReviewerInteriorFinishNat] using hdone)
          · exact Or.inr (by
              simp only [packedReviewerInteriorFinishNat,
                packedReviewerInteriorNatContinuationRemaining]
              omega)
      | some encoded =>
          right
          simp only [packedReviewerInteriorFinishNat,
            packedReviewerInteriorStartGlobalSpan,
            packedReviewerInteriorReadNat,
            packedReviewerInteriorPotential,
            packedReviewerInteriorNatContinuationRemaining,
            packedReviewerCandidateContinuationRemaining]
          omega

private theorem packedReviewerInteriorNormalize_done_eq
    (fuel : Nat) (value : PackedReviewerCandidate) :
    packedReviewerInteriorNormalize fuel (.done value) = .done value := by
  cases fuel <;> simp [packedReviewerInteriorNormalize]

private theorem packedReviewerInteriorNormalize_potential_le
    (fuel : Nat) (state : PackedReviewerInteriorState) :
    packedReviewerInteriorPotential
        (packedReviewerInteriorNormalize fuel state) <=
      packedReviewerInteriorPotential state := by
  induction fuel generalizing state with
  | zero => simp [packedReviewerInteriorNormalize]
  | succ fuel ih =>
      cases state with
      | done value => simp [packedReviewerInteriorNormalize]
      | readNat invocation read continuation =>
          cases hresult : packedReviewerInteriorNatResult read with
          | none =>
              simp [packedReviewerInteriorNormalize, hresult]
          | some value =>
              simp only [packedReviewerInteriorNormalize, hresult]
              have hstep :=
                packedReviewerInteriorFinishNat_done_or_potential_lt
                  invocation value continuation
              rcases hstep with ⟨result, heq⟩ | hlt
              · rw [heq, packedReviewerInteriorNormalize_done_eq]
                simp [packedReviewerInteriorPotential]
              · have htail :=
                  ih (packedReviewerInteriorFinishNat invocation value
                    continuation)
                simp only [packedReviewerInteriorPotential] at *
                omega

private theorem packedReviewerInteriorCanonicalStep_potential_le
    (shape : CartesianShape) (state : PackedReviewerInteriorState) :
    packedReviewerInteriorPotential
        (packedReviewerInteriorCanonicalStep shape state) <=
      packedReviewerInteriorPotential state := by
  unfold packedReviewerInteriorCanonicalStep
  cases hrequest : packedReviewerInteriorNextRequest state with
  | none => exact Nat.le_refl _
  | some request =>
      cases state with
      | done value =>
          simp [packedReviewerInteriorConsumeReply,
            packedReviewerInteriorPotential]
      | readNat invocation read continuation =>
          simp only [packedReviewerInteriorConsumeReply]
          cases hresult :
              packedReviewerInteriorNatResult
                (packedReviewerInteriorNatConsumeReply read
                  ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
                    request.segment request.index)) with
          | none =>
              simp [hresult, packedReviewerInteriorPotential]
          | some value =>
              simp only [hresult]
              have hnormalize :=
                packedReviewerInteriorNormalize_potential_le
                  (packedReviewerInteriorRemaining
                    (packedReviewerInteriorFinishNat invocation value
                      continuation) + 1)
                  (packedReviewerInteriorFinishNat invocation value
                    continuation)
              have hstep :=
                packedReviewerInteriorFinishNat_done_or_potential_lt
                  invocation value continuation
              rcases hstep with ⟨result, heq⟩ | hlt
              · rw [heq, packedReviewerInteriorNormalize_done_eq]
                simp [packedReviewerInteriorPotential]
              · simp only [packedReviewerInteriorPotential] at *
                omega

private theorem packedReviewerInteriorCanonicalRun_potential_le
    (shape : CartesianShape) (fuel : Nat)
    (state : PackedReviewerInteriorState) :
    packedReviewerInteriorPotential
        (packedReviewerInteriorCanonicalRun shape fuel state) <=
      packedReviewerInteriorPotential state := by
  induction fuel with
  | zero => simp [packedReviewerInteriorCanonicalRun]
  | succ fuel ih =>
      have hrun :
          packedReviewerInteriorCanonicalRun shape (fuel + 1) state =
            packedReviewerInteriorCanonicalStep shape
              (packedReviewerInteriorCanonicalRun shape fuel state) := rfl
      rw [hrun]
      exact Nat.le_trans
        (packedReviewerInteriorCanonicalStep_potential_le shape
          (packedReviewerInteriorCanonicalRun shape fuel state)) ih

private theorem packedReviewerInteriorStartRaw_potential_le_thirtyTwo
    (invocation : PackedReviewerInvocation) (n startBlock count : Nat) :
    packedReviewerInteriorPotential
        (packedReviewerInteriorStartRaw invocation n startBlock count) <=
      32 := by
  unfold packedReviewerInteriorStartRaw
  by_cases hzero : count = 0
  · simp [hzero, packedReviewerInteriorPotential]
  · by_cases hwithin :
        count <=
          (packedInteriorLayout n).macroSize -
            startBlock % (packedInteriorLayout n).macroSize
    · simp [hzero, hwithin, packedReviewerInteriorStartLocalTwo,
        packedReviewerInteriorReadNat, packedReviewerInteriorPotential,
        packedReviewerInteriorNatContinuationRemaining,
        packedReviewerCandidateContinuationRemaining]
    · by_cases hmiddle :
          (count -
              ((packedInteriorLayout n).macroSize -
                startBlock % (packedInteriorLayout n).macroSize)) /
            (packedInteriorLayout n).macroSize = 0
      · simp [hzero, hwithin, hmiddle, packedReviewerInteriorStartLocalTwo,
          packedReviewerInteriorReadNat, packedReviewerInteriorPotential,
          packedReviewerInteriorNatContinuationRemaining,
          packedReviewerCandidateContinuationRemaining]
      · by_cases hright :
            (count -
                ((packedInteriorLayout n).macroSize -
                  startBlock % (packedInteriorLayout n).macroSize)) %
              (packedInteriorLayout n).macroSize = 0
        · simp [hzero, hwithin, hmiddle, hright,
            packedReviewerInteriorStartLocalTwo,
            packedReviewerInteriorReadNat, packedReviewerInteriorPotential,
            packedReviewerInteriorNatContinuationRemaining,
            packedReviewerCandidateContinuationRemaining]
        · simp [hzero, hwithin, hmiddle, hright,
            packedReviewerInteriorStartLocalTwo,
            packedReviewerInteriorReadNat, packedReviewerInteriorPotential,
            packedReviewerInteriorNatContinuationRemaining,
            packedReviewerCandidateContinuationRemaining]

private theorem packedReviewerInteriorStart_potential_le_thirtyTwo
    (invocation : PackedReviewerInvocation) (n startBlock count : Nat) :
    packedReviewerInteriorPotential
        (packedReviewerInteriorStart invocation n startBlock count) <= 32 := by
  unfold packedReviewerInteriorStart
  exact Nat.le_trans
    (packedReviewerInteriorNormalize_potential_le _ _)
    (packedReviewerInteriorStartRaw_potential_le_thirtyTwo invocation n
      startBlock count)

private theorem packedReviewerInteriorStart_canonicalRun_certificate
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (startBlock spanCount fuel : Nat)
    (hinvocation :
      PackedReviewerInteriorInvocationScalarFits shape invocation)
    (hrange :
      startBlock + spanCount <= packedSummaryBlockCountRaw shape.size) :
    PackedReviewerInteriorScalarCertificate shape invocation
      (.state
        (packedReviewerInteriorCanonicalRun shape fuel
          (packedReviewerInteriorStart invocation shape.size startBlock
            spanCount))) := by
  induction fuel with
  | zero =>
      simpa [packedReviewerInteriorCanonicalRun] using
        packedReviewerInteriorStart_scalarCertificate shape invocation
          startBlock spanCount hinvocation hrange
  | succ fuel ih =>
      simpa [packedReviewerInteriorCanonicalRun] using ih.canonicalStep

private theorem PackedReviewerInteriorScalarCertificate.read_remaining_le_eight
    {shape : CartesianShape} {invocation : PackedReviewerInvocation}
    {read : PackedReviewerInteriorNatState}
    {continuation : PackedReviewerInteriorNatContinuation}
    (hstate :
      PackedReviewerInteriorScalarCertificate shape invocation
        (.state (.readNat invocation read continuation))) :
    packedReviewerInteriorNatRemaining read <= 8 := by
  cases hstate with
  | stateRead spec _ _ hread hcontinuation =>
      cases read with
      | done result => simp [packedReviewerInteriorNatRemaining]
      | read childInvocation n2 start next remaining repliesRev =>
          have hcontrol := hread.control
          simp only [packedReviewerInteriorNatRemaining]
          omega

/-- Canonical orbit states keep the structural interior budget within `40`. -/
theorem PackedReviewerInteriorCanonicalScalarFits.remaining_le_forty
    {shape : CartesianShape} {invocation : PackedReviewerInvocation}
    {startBlock spanCount : Nat} {state : PackedReviewerInteriorState}
    (hstate :
      PackedReviewerInteriorCanonicalScalarFits shape invocation startBlock
        spanCount state) :
    packedReviewerInteriorRemaining state <= 40 := by
  rcases hstate.canonical_orbit with ⟨fuel, rfl⟩
  have hpotential :=
    Nat.le_trans
      (packedReviewerInteriorCanonicalRun_potential_le shape fuel
        (packedReviewerInteriorStart invocation shape.size startBlock
          spanCount))
      (packedReviewerInteriorStart_potential_le_thirtyTwo invocation
        shape.size startBlock spanCount)
  have hcertificate :=
    packedReviewerInteriorStart_canonicalRun_certificate shape invocation
      startBlock spanCount fuel hstate.invocation_operands hstate.range
  cases hrun :
      packedReviewerInteriorCanonicalRun shape fuel
        (packedReviewerInteriorStart invocation shape.size startBlock
          spanCount) with
  | done value =>
      simp [hrun, packedReviewerInteriorRemaining]
  | readNat invocation2 read continuation =>
      have hinvocation2 : invocation2 = invocation := by
        rw [hrun] at hcertificate
        cases hcertificate with
        | stateRead _ _ _ _ _ => rfl
      subst hinvocation2
      rw [hrun] at hcertificate hpotential
      have hread := hcertificate.read_remaining_le_eight
      simp only [packedReviewerInteriorRemaining,
        packedReviewerInteriorPotential] at *
      omega

/-- The pending request of a canonical orbit state has fitting operands. -/
theorem PackedReviewerInteriorCanonicalScalarFits.nextRequest_operands_fit
    {shape : CartesianShape} {invocation : PackedReviewerInvocation}
    {startBlock spanCount : Nat} {state : PackedReviewerInteriorState}
    (hstate :
      PackedReviewerInteriorCanonicalScalarFits shape invocation startBlock
        spanCount state)
    {request : PackedReviewerLogicalRequest}
    (hrequest : packedReviewerInteriorNextRequest state = some request) :
    PackedReviewerLogicalRequestOperandsFit shape.size request := by
  rcases hstate.canonical_orbit with ⟨fuel, rfl⟩
  have hcertificate :=
    packedReviewerInteriorStart_canonicalRun_certificate shape invocation
      startBlock spanCount fuel hstate.invocation_operands hstate.range
  cases hrun :
      packedReviewerInteriorCanonicalRun shape fuel
        (packedReviewerInteriorStart invocation shape.size startBlock
          spanCount) with
  | done value =>
      rw [hrun] at hrequest
      simp [packedReviewerInteriorNextRequest] at hrequest
  | readNat invocation2 read continuation =>
      rw [hrun] at hcertificate hrequest
      cases hcertificate with
      | stateRead spec _ _ hread hcontinuation =>
          simp only [packedReviewerInteriorNextRequest] at hrequest
          cases read with
          | done result =>
              simp [packedReviewerInteriorNatNextRequest] at hrequest
          | read childInvocation n2 start next remaining repliesRev =>
              cases remaining with
              | zero =>
                  simp [packedReviewerInteriorNatNextRequest] at hrequest
              | succ remaining =>
                  have hrequests := hread.requests
                  simp only [packedReviewerInteriorNatRemaining] at hrequests
                  exact
                    (PackedReviewerRequestsFitFrom.step shape.size
                      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
                      packedReviewerInteriorNatNextRequest
                      packedReviewerInteriorNatConsumeReply remaining
                      (.read childInvocation n2 start next (remaining + 1)
                        repliesRev)
                      request hrequests hrequest).1

end PackedCellProbe
end SuccinctFinal
end RMQ
