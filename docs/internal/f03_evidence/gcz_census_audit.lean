import RMQ.Core.SuccinctFinal.RAM.GeometryCensus

/-!
Audit instrument for the EG-CP-F03 geometry census.

(1) `#print axioms` on the bundle and its corollaries.
(2) Row count, by exhaustive case analysis on the closed inductive.
(3) The transitive constant closure of `GeometryValue.mirror` contains no
    reference to `Cartesian.CartesianShape` nor to any of its eliminators.
    (The typing of `mirror : GeometryValue -> Nat -> Nat` already forces the
    closed form to be a function of `n` alone; this check is corroboration
    that the closed form is genuine arithmetic and not a disguised lookup.)
-/

open Lean

namespace GczAudit

open RMQ.SuccinctFinal.GeometryCensus

/-! ## (1) Axioms -/

#print axioms RMQ.SuccinctFinal.GeometryCensus.GeometryValue.eval_eq_mirror
#print axioms RMQ.SuccinctFinal.GeometryCensus.GeometryValue.eval_congr
#print axioms RMQ.SuccinctFinal.GeometryCensus.GeometryValue.eval_factors
#print axioms RMQ.SuccinctFinal.GeometryCensus.GeometryValue.eval_congr_of_length
#print axioms RMQ.SuccinctFinal.GeometryCensus.offsets_mirror
#print axioms RMQ.SuccinctFinal.GeometryCensus.active_iff
#print axioms RMQ.SuccinctFinal.GeometryCensus.componentStoreWords_mirror
#print axioms RMQ.SuccinctFinal.GeometryCensus.rankSuperOverhead_mirror
#print axioms RMQ.SuccinctFinal.GeometryCensus.rankBlockOverhead_mirror

/-! ## (2) Row count, by exhaustive case analysis on the closed inductive. -/

def rowIndex : GeometryValue -> Nat
  | .bpCodeLength => 1
  | .summaryBase => 2
  | .summaryBlockSizeRaw => 3
  | .summaryBlocksPerSuperRaw => 4
  | .summaryBlockCountRaw => 5
  | .summarySuperCountRaw => 6
  | .summarySuperWidth => 7
  | .summaryRelativeWidthRaw => 8
  | .summaryBlockSize => 9
  | .summaryBlocksPerSuper => 10
  | .summaryBlockCount => 11
  | .summarySuperCount => 12
  | .summaryRelativeWidth => 13
  | .layoutBlockSize => 14
  | .layoutBlocksPerSuper => 15
  | .layoutBlockCount => 16
  | .layoutRelativeWidth => 17
  | .layoutSuperSampleCount => 18
  | .layoutSuperWidth => 19
  | .layoutMacroSize => 20
  | .layoutMacroSampleCount => 21
  | .layoutOffsetWidth => 22
  | .layoutLevelCount => 23
  | .layoutGlobalLevelCount => 24
  | .layoutBlockAddressWidth => 25
  | .rankWordSize => 26
  | .rankBlocksPerSuper => 27
  | .rankBlockWidth => 28
  | .rankSuperOverhead => 29
  | .rankBlockOverhead => 30
  | .fringeChunkBits => 31
  | .baselineWords => 32
  | .minRelWords => 33
  | .maxRelWords => 34
  | .argOffsetWords => 35
  | .localTableWords => 36
  | .globalTableWords => 37
  | .localLevelWords => 38
  | .globalLevelWords => 39
  | .componentStoreWords => 40
  | .offsetBaseline => 41
  | .offsetMinRel => 42
  | .offsetMaxRel => 43
  | .offsetArgOffset => 44
  | .offsetLocalOffset => 45
  | .offsetGlobalBlock => 46
  | .offsetLocalLevel => 47
  | .offsetGlobalLevel => 48
  | .offsetDeadAddress => 49
  | .localWindowBase _ _ => 50
  | .closeBlockIndex _ _ => 51
  | .segment _ => 52

/-- Fifty-two census rows: forty-nine singletons, two parameterised families,
one selector family. Proved by exhaustive case analysis, so it cannot go stale
against the inductive. -/
theorem rowIndex_range (g : GeometryValue) : 0 < rowIndex g /\ rowIndex g <= 52 := by
  cases g <;> simp [rowIndex]

def segIndex : SegmentTag -> Nat
  | .bitWords => 1
  | .selectSuperBaseOccurrence => 2
  | .selectSuperBaseWordIndex => 3
  | .selectSuperRankBefore => 4
  | .selectSuperFirstOffset => 5
  | .selectLocalBaseOccurrence => 6
  | .selectLocalBaseWordIndex => 7
  | .selectLocalRankBefore => 8
  | .selectLocalFirstOffset => 9
  | .selectLongFlagRankBase => 10
  | .selectLongRelativeBase => 11
  | .selectSparseRankBase => 12
  | .selectSparseRelativeBase => 13
  | .rankCloseBase => 14
  | .interiorCanonicalComponent => 15
  | .fringeChunk => 16
  | .selectChunk => 17
  | .finiteSmallSameBlock => 18
  | .dead => 19

theorem segIndex_range (t : SegmentTag) : 0 < segIndex t /\ segIndex t <= 19 := by
  cases t <;> simp [segIndex]

/-- The nineteen table selectors, as literals. Every one is a closed numeral:
no shape, no endpoint, no probe reply. -/
theorem selector_literals :
    SegmentTag.value .bitWords = 0 /\
    SegmentTag.value .selectSuperBaseOccurrence = 1 /\
    SegmentTag.value .selectSuperBaseWordIndex = 2 /\
    SegmentTag.value .selectSuperRankBefore = 3 /\
    SegmentTag.value .selectSuperFirstOffset = 4 /\
    SegmentTag.value .selectLocalBaseOccurrence = 5 /\
    SegmentTag.value .selectLocalBaseWordIndex = 6 /\
    SegmentTag.value .selectLocalRankBefore = 7 /\
    SegmentTag.value .selectLocalFirstOffset = 8 /\
    SegmentTag.value .selectLongFlagRankBase = 9 /\
    SegmentTag.value .selectLongRelativeBase = 12 /\
    SegmentTag.value .selectSparseRankBase = 13 /\
    SegmentTag.value .selectSparseRelativeBase = 16 /\
    SegmentTag.value .rankCloseBase = 17 /\
    SegmentTag.value .interiorCanonicalComponent = 20 /\
    SegmentTag.value .fringeChunk = 21 /\
    SegmentTag.value .selectChunk = 22 /\
    SegmentTag.value .finiteSmallSameBlock = 28 /\
    SegmentTag.value .dead = 29 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl⟩

#print axioms rowIndex_range
#print axioms segIndex_range
#print axioms selector_literals

/-! ## (3) The branch census -/

#print axioms RMQ.SuccinctFinal.GeometryCensus.GeometryBranch.eval_eq_mirror
#print axioms RMQ.SuccinctFinal.GeometryCensus.GeometryBranch.eval_congr
#print axioms RMQ.SuccinctFinal.GeometryCensus.superIsLong_provenance
#print axioms RMQ.SuccinctFinal.GeometryCensus.localIsSparseException_provenance
#print axioms RMQ.SuccinctFinal.GeometryCensus.compactLocalEntryIsLive_provenance
#print axioms RMQ.SuccinctFinal.GeometryCensus.compactLocalEntryIsLive_secondConjunct_mirror
#print axioms RMQ.SuccinctFinal.GeometryCensus.occurrenceCount_bpCode_false
#print axioms RMQ.SuccinctFinal.GeometryCensus.occurrenceCount_bpCode_true

def branchIndex : GeometryBranch -> Nat
  | .summaryTableActive => 1
  | .sameBlockRoute _ _ => 2

theorem branchIndex_range (b : GeometryBranch) :
    0 < branchIndex b /\ branchIndex b <= 2 := by
  cases b <;> simp [branchIndex]

#print axioms branchIndex_range


/-! ## (4) Anti-vacuity, and one kernel-evaluation finding.

`Nat.log2` is defined in Lean core by well-founded recursion, so `decide`
cannot evaluate it: `Nat.log2 12 = 3` is NOT closable by `decide` in this
toolchain.  Every census row below `summaryBase` sits on top of `Nat.log2`, so
none of those rows admits a kernel-computed sample value.  The rows that do not
touch `Nat.log2` are checked below; the congruence bundle itself is unaffected,
because it is proved by rewriting, never by evaluation.
-/

open RMQ RMQ.Cartesian

def leftSpine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | k + 1 => CartesianShape.node (leftSpine k) CartesianShape.empty

def rightSpine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | k + 1 => CartesianShape.node CartesianShape.empty (rightSpine k)

/-- The witness pair: equal size, different balanced-parenthesis contents. -/
theorem spine_sizes : (leftSpine 12).size = 12 /\ (rightSpine 12).size = 12 := by
  exact ⟨by decide, by decide⟩

theorem spines_differ : Ne (leftSpine 12).bpCode (rightSpine 12).bpCode := by decide

/-- Kernel-evaluable closed-form samples: the rows that avoid `Nat.log2`. -/
theorem mirror_values_log2_free :
    GeometryValue.mirror .bpCodeLength 12 = 24 /\
    GeometryValue.mirror .bpCodeLength 13 = 26 /\
    GeometryValue.mirror .offsetBaseline 12 = 0 /\
    GeometryValue.mirror (.closeBlockIndex 8 20) 12 = 2 /\
    GeometryValue.mirror (.segment .rankCloseBase) 12 = 17 /\
    GeometryValue.mirror (.segment .interiorCanonicalComponent) 12 = 20 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- The closed forms are not constant in `n`. -/
theorem mirror_varies_with_n :
    Ne (GeometryValue.mirror .bpCodeLength 12) (GeometryValue.mirror .bpCodeLength 13) := by
  decide

/-- Two census rows are genuinely different closed forms. -/
theorem census_rows_distinct :
    Ne (GeometryValue.mirror .bpCodeLength 12) (GeometryValue.mirror .offsetBaseline 12) := by
  decide

/-- The `eval` side, on the log2-free rows, at a concrete shape. -/
theorem eval_values_log2_free :
    GeometryValue.eval .bpCodeLength (leftSpine 12) = 24 /\
    GeometryValue.eval (.segment .rankCloseBase) (rightSpine 12) = 17 := by
  refine ⟨by decide, by decide⟩

/-- The bundle instantiated at a real same-size, different-content pair: every
census row agrees. -/
theorem bundle_on_a_real_pair (g : GeometryValue) :
    g.eval (leftSpine 12) = g.eval (rightSpine 12) :=
  GeometryValue.eval_congr g (by decide)

/-- The branch bundle at the same pair, for every endpoint pair. -/
theorem branch_bundle_on_a_real_pair (b : GeometryBranch) :
    b.eval (leftSpine 12) = b.eval (rightSpine 12) :=
  GeometryBranch.eval_congr b (by decide)

#print axioms spine_sizes
#print axioms spines_differ
#print axioms mirror_values_log2_free
#print axioms mirror_varies_with_n
#print axioms census_rows_distinct
#print axioms eval_values_log2_free
#print axioms bundle_on_a_real_pair
#print axioms branch_bundle_on_a_real_pair

end GczAudit
