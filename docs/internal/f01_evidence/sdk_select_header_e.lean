import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
EG-CP-F01, part E.

(1) An ELABORATOR-CHECKED exhaustive classification of every flat-payload
    segment source.  The `match` has no wildcard, so Lean rejects the file if a
    constructor is missed: this is a closed-inductive exhaustiveness check, not
    an argument.

(2) The select-side segment lengths that are size-only, including the flag-rank
    auxiliary payloads, and the exact statement of what the two content-
    dependent ones depend on.
-/

namespace SdkE

open RMQ
open RMQ.Cartesian
open RMQ.GenericSelect
open RMQ.SuccinctFinal

inductive Verdict where
  | sizeOnlyLength      -- segment LENGTH is a closed function of n
  | contentDependent    -- segment LENGTH varies at fixed n
  | notSelectSide       -- rank / close / bpCode segment, out of scope here
deriving DecidableEq, Repr

/-- Exhaustive by elaboration: no wildcard branch. -/
def classify :
    ConcreteBPNativeSuccinctRMQFlatPayloadSource -> Verdict
  | .bpCode => .notSelectSide
  | .selectSuperBaseOccurrence => .sizeOnlyLength
  | .selectSuperBaseWordIndex => .sizeOnlyLength
  | .selectSuperRankBefore => .sizeOnlyLength
  | .selectSuperFirstOffset => .sizeOnlyLength
  | .selectLocalBaseOccurrence => .sizeOnlyLength
  | .selectLocalBaseWordIndex => .sizeOnlyLength
  | .selectLocalRankBefore => .sizeOnlyLength
  | .selectLocalFirstOffset => .sizeOnlyLength
  | .selectLongFlagRankSuperTrue => .sizeOnlyLength
  | .selectLongFlagRankBlockTrue => .sizeOnlyLength
  | .selectLongFlagBits => .sizeOnlyLength
  | .selectLongRelative => .contentDependent
  | .selectSparseRankSuperTrue => .sizeOnlyLength
  | .selectSparseRankBlockTrue => .sizeOnlyLength
  | .selectSparseFlagBits => .sizeOnlyLength
  | .selectSparseRelative => .contentDependent
  | .finalRankSuperFalse => .notSelectSide
  | .finalRankBlockFalse => .notSelectSide
  | .finalRankBPCodeAlias => .notSelectSide
  | .closeSummaryBaseline => .notSelectSide
  | .closeSummaryMinRel => .notSelectSide
  | .closeSummaryMaxRel => .notSelectSide
  | .closeSummaryArgOffset => .notSelectSide
  | .closeInteriorLocal => .notSelectSide
  | .closeInteriorGlobal => .notSelectSide
  | .closeFiniteSmallInteriorMin => .notSelectSide
  | .closeFiniteSmallInteriorArg => .notSelectSide
  | .closeFiniteSmallSameBlock => .notSelectSide

/-- Over the 18 sources the canonical reviewer execution actually reads,
exactly two are content dependent. -/
example :
    (concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources.filter
      (fun s => classify s = .contentDependent)) =
    [ .selectLongRelative, .selectSparseRelative ] := by decide

/-- ... and the other sixteen have size-only lengths. -/
example :
    (concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources.filter
      (fun s => classify s = .sizeOnlyLength)).length = 14 /\
    (concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources.filter
      (fun s => classify s = .notSelectSide)).length = 2 /\
    concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources.length = 18 :=
  by decide

/-! ## The flag-rank auxiliary payload lengths -/

theorem longFlagRank_auxPayload_length (bits : List Bool) (target : Bool) :
    (longFlagRankData bits target).auxPayload.length =
      longFlagRankSuperOverhead bits target +
        longFlagRankBlockOverhead bits target :=
  (longFlagRankData bits target).auxPayload_length

theorem sparseFlagRank_auxPayload_length (bits : List Bool) (target : Bool) :
    (sparseExceptionEffectiveFlagRankData bits target).auxPayload.length =
      sparseExceptionEffectiveFlagRankSuperOverhead bits target +
        sparseExceptionEffectiveFlagRankBlockOverhead bits target :=
  (sparseExceptionEffectiveFlagRankData bits target).auxPayload_length

/-! ## What the two content-dependent lengths actually depend on -/

/-- `selLongRelative` length = (number of LONG supers) x superStride x wordBits.
Only the first factor reads content. -/
theorem long_relative_length (bits : List Bool) (target : Bool) :
    (longSuperRelativeTable bits target).payload.length =
      RMQ.Succinct.rankPrefix true (longSuperFlagBits bits target)
          (superSlotCount bits target) *
        superStride bits.length * longSuperRelativeWidth bits :=
  longSuperRelativeTable_payload_length bits target

/-- `selSparseRelative` length = (number of SPARSE-EXCEPTION local blocks)
x localStride x relativeWidth.  Only the first factor reads content. -/
theorem sparse_relative_length (bits : List Bool) (target : Bool) :
    (sparseExceptionRelativeTable bits target).payload.length =
      RMQ.Succinct.rankPrefix true (sparseExceptionFlagBits bits target)
          (localSlotCount bits target) *
        localStride bits.length * sparseExceptionRelativeWidth bits :=
  sparseExceptionRelativeTable_payload_expanded_length bits target

/-! ## The padding budgets ARE proved upper bounds, unconditionally -/

theorem long_padding_is_sound (bits : List Bool) (target : Bool) :
    (longSuperRelativeTable bits target).payload.length <=
      longSuperRelativeTableOverhead bits.length :=
  longSuperRelativeTable_payload_le_overhead bits target

theorem sparse_padding_is_sound (bits : List Bool) (target : Bool) :
    (sparseExceptionRelativeTable bits target).payload.length <=
      sparseExceptionRelativeTableOverhead bits.length :=
  sparseExceptionRelativeTable_payload_le_overhead bits target

/-- Both padding budgets are `o(n)`, so padding to them keeps `rho(n) = o(n)`. -/
theorem both_budgets_littleO :
    SuccinctSpace.LittleOLinear longSuperRelativeTableOverhead /\
      SuccinctSpace.LittleOLinear sparseExceptionRelativeTableOverhead :=
  ⟨longSuperRelativeTableOverhead_littleO,
    sparseExceptionRelativeTableOverhead_littleO⟩

end SdkE
