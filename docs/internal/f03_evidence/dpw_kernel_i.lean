import RMQ.Core.SuccinctFinal.RAM.GeometryClosure

/-!
F03 classification, QUERY-TIME half.

A constant is QUERY-TIME if the executed store-parametric controller evaluates
it.  For F03 those must be size-only.  Every statement below has the same
shape --

    a.size = b.size  ->  c a args... = c b args...

-- and each is discharged from the in-tree `GeometryClosure` module, so the
classification is proved, not asserted.  The two buckets are provably
disjoint: a constant with a kernel-checked separation at two equal-size shapes
(see `dpw_kernel_f.lean`) cannot satisfy any statement of this form.
-/

namespace DPWKernelI

open RMQ RMQ.Cartesian RMQ.SuccinctClose RMQ.SuccinctFinal
open RMQ.SuccinctFinal.GeometryClosure

variable {a b : CartesianShape}

/-! ### QT-01 .. QT-11 : interior directory geometry and its computations -/

/-- QT-11 the interior component offset block: all nine addresses. -/
theorem qt11_componentOffsets (h : a.size = b.size) :
    canonicalRelativeRmmInteriorComponentOffsets a =
      canonicalRelativeRmmInteriorComponentOffsets b :=
  GeometryClosure.offsets_congr h

/-- QT-43 the interior fixed-width table read primitive. -/
theorem qt43_machineReadNat (h : a.size = b.size)
    {entries : List Nat} {width : Nat}
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (base i : Nat) :
    canonicalRelativeRmmMachineReadNatComputation a table base i =
      canonicalRelativeRmmMachineReadNatComputation b table base i :=
  GeometryClosure.readNat_congr h table table rfl rfl base i

theorem qt46_summaryComputation (h : a.size = b.size) (block : Nat) :
    canonicalRelativeRmmMachineSummaryComputation a block =
      canonicalRelativeRmmMachineSummaryComputation b block :=
  GeometryClosure.summaryComputation_congr h block

theorem qt45_minCandidate (h : a.size = b.size) (block : Nat) :
    canonicalRelativeRmmMachineMinCandidateComputation a block =
      canonicalRelativeRmmMachineMinCandidateComputation b block :=
  GeometryClosure.minCandidateComputation_congr h block

theorem qt44_localSpanCandidate (h : a.size = b.size)
    (macroIdx localStart level : Nat) :
    canonicalRelativeRmmMachineLocalSpanCandidateComputation a
        macroIdx localStart level =
      canonicalRelativeRmmMachineLocalSpanCandidateComputation b
        macroIdx localStart level :=
  GeometryClosure.localSpanCandidateComputation_congr h macroIdx localStart level

theorem qt50_globalSpanCandidate (h : a.size = b.size)
    (macroStart level : Nat) :
    canonicalRelativeRmmMachineGlobalSpanCandidateComputation a macroStart level =
      canonicalRelativeRmmMachineGlobalSpanCandidateComputation b macroStart level :=
  GeometryClosure.globalSpanCandidateComputation_congr h macroStart level

theorem qt10_localTwoSpanCandidate (h : a.size = b.size)
    (macroIdx localStart count : Nat) :
    canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation a
        macroIdx localStart count =
      canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation b
        macroIdx localStart count :=
  GeometryClosure.localTwoSpanCandidateComputation_congr h macroIdx localStart count

theorem qt49_globalTwoSpanCandidate (h : a.size = b.size)
    (macroStart macroSpanCount : Nat) :
    canonicalRelativeRmmMachineGlobalTwoSpanCandidateComputation a
        macroStart macroSpanCount =
      canonicalRelativeRmmMachineGlobalTwoSpanCandidateComputation b
        macroStart macroSpanCount :=
  GeometryClosure.globalTwoSpanCandidateComputation_congr h macroStart macroSpanCount

theorem qt47_adjacentMacroCandidate (h : a.size = b.size)
    (macroStart localStart rightCount : Nat) :
    canonicalRelativeRmmMachineAdjacentMacroCandidateComputation a
        macroStart localStart rightCount =
      canonicalRelativeRmmMachineAdjacentMacroCandidateComputation b
        macroStart localStart rightCount :=
  GeometryClosure.adjacentMacroCandidateComputation_congr h macroStart localStart rightCount

theorem qt48_leftMiddleMacroCandidate (h : a.size = b.size)
    (macroStart localStart middleMacroCount : Nat) :
    canonicalRelativeRmmMachineLeftMiddleMacroCandidateComputation a
        macroStart localStart middleMacroCount =
      canonicalRelativeRmmMachineLeftMiddleMacroCandidateComputation b
        macroStart localStart middleMacroCount :=
  GeometryClosure.leftMiddleMacroCandidateComputation_congr h
    macroStart localStart middleMacroCount

theorem qt51_crossMacroCandidate (h : a.size = b.size)
    (macroStart localStart middleMacroCount rightCount : Nat) :
    canonicalRelativeRmmMachineCrossMacroCandidateComputation a
        macroStart localStart middleMacroCount rightCount =
      canonicalRelativeRmmMachineCrossMacroCandidateComputation b
        macroStart localStart middleMacroCount rightCount :=
  GeometryClosure.crossMacroCandidateComputation_congr h
    macroStart localStart middleMacroCount rightCount

theorem qt09_interiorRangeMinComputation (h : a.size = b.size)
    (startBlock count : Nat) :
    canonicalRelativeRmmInteriorRangeMinComputation a startBlock count =
      canonicalRelativeRmmInteriorRangeMinComputation b startBlock count :=
  GeometryClosure.interiorRangeMinComputation_congr h startBlock count

theorem qt08_interiorRangeMinWithStore (h : a.size = b.size)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (store : WordRAM.ReadStore) (startBlock count : Nat) :
    ConcreteCompactBPCloseLCADirectory.concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore
        a segments store startBlock count =
      ConcreteCompactBPCloseLCADirectory.concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore
        b segments store startBlock count :=
  GeometryClosure.interiorRangeMinWithStore_congr h segments store startBlock count

/-! ### QT-04 .. QT-07, QT-52 : the three controller leaves and the L2 arms -/

theorem qt04_selectCloseLeaf (h : a.size = b.size)
    (store : WordRAM.ReadStore) (idx : Nat) :
    concreteBPNativeSelectCloseGlobalWordTraceResultWithStore a store idx =
      concreteBPNativeSelectCloseGlobalWordTraceResultWithStore b store idx :=
  GeometryClosure.SelectLeaf.L1_route_shape_size_only h store idx

theorem qt52_rankCloseLeaf (h : a.size = b.size)
    (store : WordRAM.ReadStore) (rankSegmentBase pos : Nat) :
    concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore a store rankSegmentBase pos =
      concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore b store rankSegmentBase pos :=
  GeometryClosure.L3_rankClose_size_only h store rankSegmentBase pos

theorem qt07_crossBlockArm (h : a.size = b.size)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (fringeSegment : Nat) (store : WordRAM.ReadStore)
    (leftClose rightClose : Nat) :
    ConcreteCompactBPCloseLCADirectory.bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
        a rankCloseTrace segments fringeSegment store leftClose rightClose =
      ConcreteCompactBPCloseLCADirectory.bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
        b rankCloseTrace segments fringeSegment store leftClose rightClose :=
  GeometryClosure.L2_crossBlock_size_only h rankCloseTrace segments fringeSegment
    store leftClose rightClose

theorem qt06_lcaCloseDispatcher (h : a.size = b.size)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (fringeSegment : Nat) (store : WordRAM.ReadStore)
    (sameBlockSegment leftClose rightClose : Nat) :
    ConcreteCompactBPCloseLCADirectory.lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore
        a rankCloseTrace segments fringeSegment store sameBlockSegment
        leftClose rightClose =
      ConcreteCompactBPCloseLCADirectory.lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore
        b rankCloseTrace segments fringeSegment store sameBlockSegment
        leftClose rightClose :=
  GeometryClosure.L2_lcaClose_size_only h rankCloseTrace segments fringeSegment
    store sameBlockSegment leftClose rightClose

theorem qt05_lcaCloseLeaf (h : a.size = b.size)
    (store : WordRAM.ReadStore) (leftClose rightClose : Nat) :
    concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
        a store leftClose rightClose =
      concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
        b store leftClose rightClose :=
  GeometryClosure.L2_route_size_only h store leftClose rightClose

/-! ### QT-01 .. QT-03 : the universal consumers -/

theorem qt03_instr (h : a.size = b.size)
    (store : WordRAM.ReadStore) (left right : Nat)
    (instr : WholeQueryInstr) (state : WholeQueryState) :
    instr.evalGlobalWordTraceWithStore a store left right state =
      instr.evalGlobalWordTraceWithStore b store left right state :=
  GeometryClosure.wholeQueryInstr_congr h store left right instr state

theorem qt02_program (h : a.size = b.size)
    (store : WordRAM.ReadStore) (left right : Nat)
    (program : WholeQueryProgram) (state : WholeQueryState) :
    program.evalGlobalWordTraceWithStore a store left right state =
      program.evalGlobalWordTraceWithStore b store left right state :=
  GeometryClosure.wholeQueryProgram_congr h store left right program state

theorem qt01_wholeQuery (h : a.size = b.size)
    (store : WordRAM.ReadStore) (l r : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore a store l r =
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore b store l r :=
  GeometryClosure.T4_wholeQuery_trace_size_only h store l r

#print axioms qt11_componentOffsets
#print axioms qt43_machineReadNat
#print axioms qt46_summaryComputation
#print axioms qt45_minCandidate
#print axioms qt44_localSpanCandidate
#print axioms qt50_globalSpanCandidate
#print axioms qt10_localTwoSpanCandidate
#print axioms qt49_globalTwoSpanCandidate
#print axioms qt47_adjacentMacroCandidate
#print axioms qt48_leftMiddleMacroCandidate
#print axioms qt51_crossMacroCandidate
#print axioms qt09_interiorRangeMinComputation
#print axioms qt08_interiorRangeMinWithStore
#print axioms qt04_selectCloseLeaf
#print axioms qt52_rankCloseLeaf
#print axioms qt07_crossBlockArm
#print axioms qt06_lcaCloseDispatcher
#print axioms qt05_lcaCloseLeaf
#print axioms qt03_instr
#print axioms qt02_program
#print axioms qt01_wholeQuery

end DPWKernelI
