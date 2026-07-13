import RMQ.Core.SuccinctFinal.RAM.FlatPayload

/-!
# Canonical reviewer physical store

The public payload is represented by one pre-execution word list.  The BP
region is stored once using the sentinel-capable segment-19 store; segment 0
is a guarded prefix alias.  Every invalid logical address is translated to the
one-past-end physical dead address, so it cannot alias the next component.
-/

namespace RMQ
namespace SuccinctFinal

open SuccinctSpace

abbrev ReviewerSource := ConcreteBPNativeSuccinctRMQFlatPayloadSource

/-- Unique payload sources, in canonical public order. -/
def concreteBPNativeSuccinctRMQReviewerPhysicalSources : List ReviewerSource :=
  [ .finalRankBPCodeAlias
  , .finalRankSuperFalse
  , .finalRankBlockFalse
  , .selectSuperBaseOccurrence
  , .selectSuperBaseWordIndex
  , .selectSuperRankBefore
  , .selectSuperFirstOffset
  , .selectLocalBaseOccurrence
  , .selectLocalBaseWordIndex
  , .selectLocalRankBefore
  , .selectLocalFirstOffset
  , .selectLongFlagRankSuperTrue
  , .selectLongFlagRankBlockTrue
  , .selectLongFlagBits
  , .selectLongRelative
  , .selectSparseRankSuperTrue
  , .selectSparseRankBlockTrue
  , .selectSparseFlagBits
  , .selectSparseRelative ]

def concreteBPNativeSuccinctRMQReviewerSourceWords
    (shape : Cartesian.CartesianShape) (source : ReviewerSource) :
    List (List Bool) :=
  (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape source).toList

def concreteBPNativeSuccinctRMQReviewerSourcePayload
    (shape : Cartesian.CartesianShape) (source : ReviewerSource) : List Bool :=
  concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape source

def concreteBPNativeSuccinctRMQReviewerCloseWords
    (shape : Cartesian.CartesianShape) : List (List Bool) :=
  (SuccinctClose.canonicalRelativeRmmInteriorComponentStore
    shape).store.words.toList

/-- Physical regions: nineteen unique outer sources followed by canonical close. -/
def concreteBPNativeSuccinctRMQReviewerPhysicalRegions
    (shape : Cartesian.CartesianShape) : List (List (List Bool)) :=
  concreteBPNativeSuccinctRMQReviewerPhysicalSources.map
      (concreteBPNativeSuccinctRMQReviewerSourceWords shape) ++
    [concreteBPNativeSuccinctRMQReviewerCloseWords shape]

/-- One pre-execution physical machine-word list. -/
def concreteBPNativeSuccinctRMQReviewerPhysicalWords
    (shape : Cartesian.CartesianShape) : List (List Bool) :=
  (concreteBPNativeSuccinctRMQReviewerPhysicalRegions shape).flatten

/-- Bit erasure of the unique live-source manifest. -/
def concreteBPNativeSuccinctRMQReviewerLivePayload
    (shape : Cartesian.CartesianShape) : List Bool :=
  concreteBPNativeSuccinctRMQReviewerPhysicalSources.flatMap
      (concreteBPNativeSuccinctRMQReviewerSourcePayload shape) ++
    (SuccinctClose.canonicalRelativeRmmInteriorDirectory shape).payload

private theorem reviewerSources_erases
    (shape : Cartesian.CartesianShape) (sources : List ReviewerSource) :
    flattenPayloadWords
        (sources.flatMap
          (concreteBPNativeSuccinctRMQReviewerSourceWords shape)) =
      sources.flatMap
        (concreteBPNativeSuccinctRMQReviewerSourcePayload shape) := by
  induction sources with
  | nil => rfl
  | cons source sources ih =>
      simp only [List.flatMap_cons, flattenPayloadWords_append]
      change
        flattenPayloadWords
            (concreteBPNativeSuccinctRMQFlatPayloadSourceWords
              shape source).toList ++ _ =
          concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape source ++ _
      rw [concreteBPNativeSuccinctRMQFlatPayloadSourceWords_erases]
      exact congrArg
        (fun tail =>
          concreteBPNativeSuccinctRMQReviewerSourcePayload shape source ++ tail)
        ih

theorem concreteBPNativeSuccinctRMQReviewerPhysicalWords_components
    (shape : Cartesian.CartesianShape) :
    concreteBPNativeSuccinctRMQReviewerPhysicalWords shape =
      concreteBPNativeSuccinctRMQReviewerPhysicalSources.flatMap
          (concreteBPNativeSuccinctRMQReviewerSourceWords shape) ++
        concreteBPNativeSuccinctRMQReviewerCloseWords shape := by
  have hmap :
      (concreteBPNativeSuccinctRMQReviewerPhysicalSources.map
        (concreteBPNativeSuccinctRMQReviewerSourceWords shape)).flatten =
      concreteBPNativeSuccinctRMQReviewerPhysicalSources.flatMap
        (concreteBPNativeSuccinctRMQReviewerSourceWords shape) := by
    induction concreteBPNativeSuccinctRMQReviewerPhysicalSources with
    | nil => rfl
    | cons source sources ih => simp [ih]
  simp [concreteBPNativeSuccinctRMQReviewerPhysicalWords,
    concreteBPNativeSuccinctRMQReviewerPhysicalRegions, hmap]

theorem concreteBPNativeSuccinctRMQReviewerPhysicalWords_erases_live
    (shape : Cartesian.CartesianShape) :
    flattenPayloadWords
        (concreteBPNativeSuccinctRMQReviewerPhysicalWords shape) =
      concreteBPNativeSuccinctRMQReviewerLivePayload shape := by
  rw [concreteBPNativeSuccinctRMQReviewerPhysicalWords_components,
    flattenPayloadWords_append, reviewerSources_erases]
  rw [show
    flattenPayloadWords
        (concreteBPNativeSuccinctRMQReviewerCloseWords shape) =
      (SuccinctClose.canonicalRelativeRmmInteriorDirectory shape).payload by
      simpa [concreteBPNativeSuccinctRMQReviewerCloseWords,
        SuccinctClose.canonicalRelativeRmmInteriorDirectory] using
        SuccinctClose.canonicalRelativeRmmInteriorComponentStore_flattens_payload
          shape]
  rfl

/-- The manifest payload is literally the canonical public payload. -/
theorem concreteBPNativeSuccinctRMQReviewerLivePayload_eq_public
    (shape : Cartesian.CartesianShape) :
    concreteBPNativeSuccinctRMQReviewerLivePayload shape =
      concreteBPNativeSuccinctRMQCanonicalReviewerPayload shape := by
  rfl

/-- The physical erasure is literally the canonical public payload. -/
theorem concreteBPNativeSuccinctRMQReviewerPhysicalWords_erases
    (shape : Cartesian.CartesianShape) :
    flattenPayloadWords
        (concreteBPNativeSuccinctRMQReviewerPhysicalWords shape) =
      concreteBPNativeSuccinctRMQCanonicalReviewerPayload shape := by
  rw [concreteBPNativeSuccinctRMQReviewerPhysicalWords_erases_live,
    concreteBPNativeSuccinctRMQReviewerLivePayload_eq_public]

/-! ### Logical segment map and guarded address translation -/

def concreteBPNativeSuccinctRMQReviewerSegmentRegion? : Nat -> Option Nat
  | 0 => some 0
  | 1 => some 3
  | 2 => some 4
  | 3 => some 5
  | 4 => some 6
  | 5 => some 7
  | 6 => some 8
  | 7 => some 9
  | 8 => some 10
  | 9 => some 11
  | 10 => some 12
  | 11 => some 13
  | 12 => some 14
  | 13 => some 15
  | 14 => some 16
  | 15 => some 17
  | 16 => some 18
  | 17 => some 1
  | 18 => some 2
  | 19 => some 0
  | 20 => some 19
  | _ + 21 => none

def concreteBPNativeSuccinctRMQReviewerSegmentWords
    (shape : Cartesian.CartesianShape) (segment : Nat) : List (List Bool) :=
  if segment < 20 then
    match concreteBPNativeSuccinctRMQFlatPayloadSegmentSource? segment with
    | some source => concreteBPNativeSuccinctRMQReviewerSourceWords shape source
    | none => []
  else if segment = 20 then
    concreteBPNativeSuccinctRMQReviewerCloseWords shape
  else []

def concreteBPNativeSuccinctRMQReviewerRegionOffset
    (shape : Cartesian.CartesianShape) (region : Nat) : Nat :=
  ((concreteBPNativeSuccinctRMQReviewerPhysicalRegions shape).take region)
    |>.flatten.length

def concreteBPNativeSuccinctRMQReviewerSegmentOffset?
    (shape : Cartesian.CartesianShape) (segment : Nat) : Option Nat :=
  (concreteBPNativeSuccinctRMQReviewerSegmentRegion? segment).map
    (concreteBPNativeSuccinctRMQReviewerRegionOffset shape)

def concreteBPNativeSuccinctRMQReviewerPhysicalDeadAddress
    (shape : Cartesian.CartesianShape) : Nat :=
  (concreteBPNativeSuccinctRMQReviewerPhysicalWords shape).length

def concreteBPNativeSuccinctRMQReviewerPhysicalAddress
    (shape : Cartesian.CartesianShape) (segment index : Nat) : Nat :=
  match concreteBPNativeSuccinctRMQReviewerSegmentOffset? shape segment with
  | some offset =>
      if index <
          (concreteBPNativeSuccinctRMQReviewerSegmentWords shape segment).length
      then offset + index
      else concreteBPNativeSuccinctRMQReviewerPhysicalDeadAddress shape
  | none => concreteBPNativeSuccinctRMQReviewerPhysicalDeadAddress shape

/-- Every segment outside the live `0..20` universe translates to the unique
one-past-end physical dead address. -/
theorem concreteBPNativeSuccinctRMQReviewerPhysicalAddress_deadSegment
    (shape : Cartesian.CartesianShape) (segment index : Nat)
    (hsegment : 21 <= segment) :
    concreteBPNativeSuccinctRMQReviewerPhysicalAddress shape segment index =
      concreteBPNativeSuccinctRMQReviewerPhysicalDeadAddress shape := by
  match segment with
  | 0 => omega
  | 1 => omega
  | 2 => omega
  | 3 => omega
  | 4 => omega
  | 5 => omega
  | 6 => omega
  | 7 => omega
  | 8 => omega
  | 9 => omega
  | 10 => omega
  | 11 => omega
  | 12 => omega
  | 13 => omega
  | 14 => omega
  | 15 => omega
  | 16 => omega
  | 17 => omega
  | 18 => omega
  | 19 => omega
  | 20 => omega
  | _ + 21 => rfl

/-- An out-of-range local index cannot spill into the following region: it
translates to the same one-past-end dead address. -/
theorem concreteBPNativeSuccinctRMQReviewerPhysicalAddress_indexOutOfRange
    (shape : Cartesian.CartesianShape) (segment index : Nat)
    (hindex :
      (concreteBPNativeSuccinctRMQReviewerSegmentWords shape segment).length <=
        index) :
    concreteBPNativeSuccinctRMQReviewerPhysicalAddress shape segment index =
      concreteBPNativeSuccinctRMQReviewerPhysicalDeadAddress shape := by
  unfold concreteBPNativeSuccinctRMQReviewerPhysicalAddress
    concreteBPNativeSuccinctRMQReviewerSegmentOffset?
  cases hregion :
      concreteBPNativeSuccinctRMQReviewerSegmentRegion? segment <;>
    simp [Nat.not_lt.mpr hindex]

/-- The physical dead address is genuinely one past the array, hence never
returns a stored word. -/
theorem concreteBPNativeSuccinctRMQReviewerPhysicalDeadAddress_getElem?_eq_none
    (shape : Cartesian.CartesianShape) :
    (concreteBPNativeSuccinctRMQReviewerPhysicalWords shape)[
        concreteBPNativeSuccinctRMQReviewerPhysicalDeadAddress shape]? = none := by
  simp [concreteBPNativeSuccinctRMQReviewerPhysicalDeadAddress]

/-- Whenever the physical array is nonempty, both endpoint addresses are
checked positional reads: address zero and the predecessor of the dead address
each return the corresponding array element. -/
theorem concreteBPNativeSuccinctRMQReviewerPhysicalWords_first_last_positional
    (shape : Cartesian.CartesianShape)
    (hnonempty :
      0 < concreteBPNativeSuccinctRMQReviewerPhysicalDeadAddress shape) :
    (∃ firstWord,
      (concreteBPNativeSuccinctRMQReviewerPhysicalWords shape)[0]? =
        some firstWord) /\
    (∃ lastWord,
      (concreteBPNativeSuccinctRMQReviewerPhysicalWords shape)[
          concreteBPNativeSuccinctRMQReviewerPhysicalDeadAddress shape - 1]? =
        some lastWord) := by
  have hfirst :
      0 < (concreteBPNativeSuccinctRMQReviewerPhysicalWords shape).length := by
    simpa [concreteBPNativeSuccinctRMQReviewerPhysicalDeadAddress] using
      hnonempty
  have hlast :
      concreteBPNativeSuccinctRMQReviewerPhysicalDeadAddress shape - 1 <
        (concreteBPNativeSuccinctRMQReviewerPhysicalWords shape).length := by
    rw [concreteBPNativeSuccinctRMQReviewerPhysicalDeadAddress] at hnonempty ⊢
    omega
  constructor
  · exact ⟨_, List.getElem?_eq_some_iff.mpr ⟨hfirst, rfl⟩⟩
  · exact ⟨_, List.getElem?_eq_some_iff.mpr ⟨hlast, rfl⟩⟩

private theorem list_flatten_region_slice
    {alpha : Type} (regions : List (List alpha))
    {region : Nat} {words : List alpha}
    (hget : regions[region]? = some words) :
    (regions.flatten.drop ((regions.take region).flatten.length)).take
        words.length = words := by
  induction regions generalizing region with
  | nil => simp at hget
  | cons head tail ih =>
      cases region with
      | zero =>
          simp at hget
          subst words
          simp
      | succ region =>
          simp only [List.getElem?_cons_succ] at hget
          have hdrop :
              (head ++ tail.flatten).drop
                  (head.length + (tail.take region).flatten.length) =
                tail.flatten.drop (tail.take region).flatten.length := by
            simp
          simpa [List.flatten_cons, List.take_succ_cons, hdrop] using ih hget

theorem concreteBPNativeSuccinctRMQReviewerSegmentRegion_get_of_ne_zero
    (shape : Cartesian.CartesianShape) (segment region : Nat)
    (hsegment : segment ≠ 0)
    (hregion :
      concreteBPNativeSuccinctRMQReviewerSegmentRegion? segment = some region) :
    (concreteBPNativeSuccinctRMQReviewerPhysicalRegions shape)[region]? =
      some (concreteBPNativeSuccinctRMQReviewerSegmentWords shape segment) := by
  match segment with
  | 0 => contradiction
  | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
      15 | 16 | 17 | 18 | 19 | 20 =>
      simp [concreteBPNativeSuccinctRMQReviewerSegmentRegion?] at hregion
      subst region
      rfl
  | _ + 21 => simp [concreteBPNativeSuccinctRMQReviewerSegmentRegion?] at hregion

/-- Segment 0 is exactly the ordinary-chunk prefix of the sentinel BP region. -/
theorem concreteBPNativeSuccinctRMQReviewerBP_prefix
    (shape : Cartesian.CartesianShape) :
    (concreteBPNativeSuccinctRMQReviewerSourceWords
        shape .finalRankBPCodeAlias).take
        (concreteBPNativeSuccinctRMQReviewerSourceWords shape .bpCode).length =
      concreteBPNativeSuccinctRMQReviewerSourceWords shape .bpCode := by
  simp [concreteBPNativeSuccinctRMQReviewerSourceWords,
    concreteBPNativeSuccinctRMQFlatPayloadSourceWords,
    builtRelativeSplitBPCloseRankData,
    builtRelativeSplitBPCloseRankWordSize,
    SuccinctRank.canonicalTwoLevelRankDataOfChunksExactLocalBlock,
    SuccinctRank.canonicalTwoLevelRankDataOfBridgeLocalBlock,
    SuccinctRank.canonicalRankWordBridgeOfChunksWithSentinel,
    SuccinctSpace.BoundedPayloadWordStore.ofChunksWithSentinel]

theorem concreteBPNativeSuccinctRMQReviewerSegment_slice
    (shape : Cartesian.CartesianShape) (segment region : Nat)
    (hregion :
      concreteBPNativeSuccinctRMQReviewerSegmentRegion? segment = some region) :
    let offset := concreteBPNativeSuccinctRMQReviewerRegionOffset shape region
    ((concreteBPNativeSuccinctRMQReviewerPhysicalWords shape).drop offset).take
        (concreteBPNativeSuccinctRMQReviewerSegmentWords shape segment).length =
      concreteBPNativeSuccinctRMQReviewerSegmentWords shape segment := by
  by_cases hzero : segment = 0
  · subst segment
    simp [concreteBPNativeSuccinctRMQReviewerSegmentRegion?] at hregion
    subst region
    have hle :
        (concreteBPNativeSuccinctRMQReviewerSourceWords shape .bpCode).length <=
          (concreteBPNativeSuccinctRMQReviewerSourceWords
            shape .finalRankBPCodeAlias).length := by
      simp [concreteBPNativeSuccinctRMQReviewerSourceWords,
        concreteBPNativeSuccinctRMQFlatPayloadSourceWords,
        builtRelativeSplitBPCloseRankData,
        builtRelativeSplitBPCloseRankWordSize,
        SuccinctRank.canonicalTwoLevelRankDataOfChunksExactLocalBlock,
        SuccinctRank.canonicalTwoLevelRankDataOfBridgeLocalBlock,
        SuccinctRank.canonicalRankWordBridgeOfChunksWithSentinel,
        SuccinctSpace.BoundedPayloadWordStore.ofChunksWithSentinel]
    simpa [concreteBPNativeSuccinctRMQReviewerRegionOffset,
      concreteBPNativeSuccinctRMQReviewerPhysicalWords,
      concreteBPNativeSuccinctRMQReviewerPhysicalRegions,
      concreteBPNativeSuccinctRMQReviewerPhysicalSources,
      concreteBPNativeSuccinctRMQReviewerSegmentWords,
      concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?,
      List.take_append_of_le_length hle] using
      concreteBPNativeSuccinctRMQReviewerBP_prefix shape
  · exact list_flatten_region_slice _
      (concreteBPNativeSuccinctRMQReviewerSegmentRegion_get_of_ne_zero
        shape segment region hzero hregion)

theorem concreteBPNativeSuccinctRMQReviewerSegment_getElem
    (shape : Cartesian.CartesianShape) (segment region index : Nat)
    (hregion :
      concreteBPNativeSuccinctRMQReviewerSegmentRegion? segment = some region)
    (hindex : index <
      (concreteBPNativeSuccinctRMQReviewerSegmentWords shape segment).length) :
    (concreteBPNativeSuccinctRMQReviewerPhysicalWords shape)[
        concreteBPNativeSuccinctRMQReviewerRegionOffset shape region + index]? =
      (concreteBPNativeSuccinctRMQReviewerSegmentWords shape segment)[index]? := by
  have hslice := concreteBPNativeSuccinctRMQReviewerSegment_slice
    shape segment region hregion
  have hget := congrArg (fun words : List (List Bool) => words[index]?) hslice
  simpa [List.getElem?_take, List.getElem?_drop, hindex] using hget

theorem concreteBPNativeSuccinctRMQReviewerSegmentWords_readStore
    (shape : Cartesian.CartesianShape) (segment index : Nat) :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? segment index =
      (concreteBPNativeSuccinctRMQReviewerSegmentWords shape segment)[index]? := by
  rw [← concreteBPNativeSuccinctRMQCanonicalReviewerReadStore_eq_global]
  by_cases hlt : segment < 20
  case pos =>
    cases hsource :
        concreteBPNativeSuccinctRMQFlatPayloadSegmentSource? segment <;>
      simp [concreteBPNativeSuccinctRMQCanonicalReviewerReadStore,
        concreteBPNativeSuccinctRMQReviewerSegmentWords, hlt,
        concreteBPNativeInteriorTraceSegments,
        concreteBPNativeSuccinctRMQFlatPayloadReadStore,
        concreteBPNativeSuccinctRMQReviewerSourceWords, hsource,
        Array.getElem?_toList]
  case neg =>
    by_cases heq : segment = 20
    case pos =>
      subst segment
      simp [concreteBPNativeSuccinctRMQCanonicalReviewerReadStore,
        concreteBPNativeSuccinctRMQReviewerSegmentWords,
        concreteBPNativeInteriorTraceSegments,
        concreteBPNativeSuccinctRMQReviewerCloseWords,
        Array.getElem?_toList]
    case neg =>
      simp [concreteBPNativeSuccinctRMQCanonicalReviewerReadStore,
        concreteBPNativeSuccinctRMQReviewerSegmentWords, hlt, heq,
        concreteBPNativeInteriorTraceSegments]

/-- All canonical logical reads, including failures, are physical positional reads. -/
theorem concreteBPNativeSuccinctRMQGlobalReadStore_eq_reviewerPhysical
    (shape : Cartesian.CartesianShape) (segment index : Nat) :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? segment index =
      (concreteBPNativeSuccinctRMQReviewerPhysicalWords shape)[
        concreteBPNativeSuccinctRMQReviewerPhysicalAddress
          shape segment index]? := by
  rw [concreteBPNativeSuccinctRMQReviewerSegmentWords_readStore]
  unfold concreteBPNativeSuccinctRMQReviewerPhysicalAddress
    concreteBPNativeSuccinctRMQReviewerSegmentOffset?
  cases hregion : concreteBPNativeSuccinctRMQReviewerSegmentRegion? segment with
  | none =>
      have hempty :
          concreteBPNativeSuccinctRMQReviewerSegmentWords shape segment = [] := by
        match segment with
        | 0 => simp [concreteBPNativeSuccinctRMQReviewerSegmentRegion?] at hregion
        | 1 => simp [concreteBPNativeSuccinctRMQReviewerSegmentRegion?] at hregion
        | 2 => simp [concreteBPNativeSuccinctRMQReviewerSegmentRegion?] at hregion
        | 3 => simp [concreteBPNativeSuccinctRMQReviewerSegmentRegion?] at hregion
        | 4 => simp [concreteBPNativeSuccinctRMQReviewerSegmentRegion?] at hregion
        | 5 => simp [concreteBPNativeSuccinctRMQReviewerSegmentRegion?] at hregion
        | 6 => simp [concreteBPNativeSuccinctRMQReviewerSegmentRegion?] at hregion
        | 7 => simp [concreteBPNativeSuccinctRMQReviewerSegmentRegion?] at hregion
        | 8 => simp [concreteBPNativeSuccinctRMQReviewerSegmentRegion?] at hregion
        | 9 => simp [concreteBPNativeSuccinctRMQReviewerSegmentRegion?] at hregion
        | 10 => simp [concreteBPNativeSuccinctRMQReviewerSegmentRegion?] at hregion
        | 11 => simp [concreteBPNativeSuccinctRMQReviewerSegmentRegion?] at hregion
        | 12 => simp [concreteBPNativeSuccinctRMQReviewerSegmentRegion?] at hregion
        | 13 => simp [concreteBPNativeSuccinctRMQReviewerSegmentRegion?] at hregion
        | 14 => simp [concreteBPNativeSuccinctRMQReviewerSegmentRegion?] at hregion
        | 15 => simp [concreteBPNativeSuccinctRMQReviewerSegmentRegion?] at hregion
        | 16 => simp [concreteBPNativeSuccinctRMQReviewerSegmentRegion?] at hregion
        | 17 => simp [concreteBPNativeSuccinctRMQReviewerSegmentRegion?] at hregion
        | 18 => simp [concreteBPNativeSuccinctRMQReviewerSegmentRegion?] at hregion
        | 19 => simp [concreteBPNativeSuccinctRMQReviewerSegmentRegion?] at hregion
        | 20 => simp [concreteBPNativeSuccinctRMQReviewerSegmentRegion?] at hregion
        | n + 21 =>
            have hnot : ¬ n + 21 < 20 := by omega
            simp [concreteBPNativeSuccinctRMQReviewerSegmentWords, hnot]
      simp [hempty,
        concreteBPNativeSuccinctRMQReviewerPhysicalDeadAddress]
  | some region =>
      simp only [Option.map_some]
      by_cases hindex : index <
          (concreteBPNativeSuccinctRMQReviewerSegmentWords shape segment).length
      · simp only [if_pos hindex]
        exact (concreteBPNativeSuccinctRMQReviewerSegment_getElem
          shape segment region index hregion hindex).symm
      · have hsourceNone :
          (concreteBPNativeSuccinctRMQReviewerSegmentWords
            shape segment)[index]? = none :=
          List.getElem?_eq_none (Nat.le_of_not_gt hindex)
        rw [hsourceNone]
        simp [if_neg hindex,
          concreteBPNativeSuccinctRMQReviewerPhysicalDeadAddress]

/-- Successful logical reads are backed at their translated physical address. -/
theorem concreteBPNativeSuccinctRMQReviewerSuccessfulRead_physical
    (shape : Cartesian.CartesianShape) {segment index : Nat} {word : List Bool}
    (hread :
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
        segment index = some word) :
    let address := concreteBPNativeSuccinctRMQReviewerPhysicalAddress
      shape segment index
    address < (concreteBPNativeSuccinctRMQReviewerPhysicalWords shape).length /\
      (concreteBPNativeSuccinctRMQReviewerPhysicalWords shape)[address]? =
        some word := by
  have hphysical := hread
  rw [concreteBPNativeSuccinctRMQGlobalReadStore_eq_reviewerPhysical] at hphysical
  refine ⟨?_, hphysical⟩
  exact (List.getElem?_eq_some_iff.mp hphysical).1

/-! ### Query-independent physical capacity and word width -/

private theorem list_length_le_flattenPayloadWords_length_of_mem_length_pos
    (words : List (List Bool))
    (hpos : forall word, List.Mem word words -> 0 < word.length) :
    words.length <= (flattenPayloadWords words).length := by
  induction words with
  | nil => exact Nat.le_refl 0
  | cons head tail ih =>
      have hhead : 0 < head.length := hpos head List.mem_cons_self
      have htail : forall word, List.Mem word tail -> 0 < word.length := by
        intro word hmem
        exact hpos word (List.mem_cons_of_mem head hmem)
      simp only [List.length_cons, flattenPayloadWords, List.length_append]
      have hrec := ih htail
      omega

private theorem chunkPayloadWords_mem_length_pos
    {wordSize : Nat} (hwordSize : 0 < wordSize) (payload word : List Bool)
    (hmem : List.Mem word (chunkPayloadWords wordSize payload)) :
    0 < word.length := by
  unfold chunkPayloadWords at hmem
  generalize payload.length + 1 = fuel at hmem
  induction fuel generalizing payload with
  | zero =>
      change List.Mem word [] at hmem
      exact False.elim (List.not_mem_nil hmem)
  | succ fuel ih =>
      cases payload with
      | nil =>
          change List.Mem word [] at hmem
          exact False.elim (List.not_mem_nil hmem)
      | cons bit rest =>
          change
            List.Mem word
              ((bit :: rest).take wordSize ::
                chunkPayloadWordsFuel wordSize fuel
                  ((bit :: rest).drop wordSize)) at hmem
          cases hmem with
          | head =>
              rw [List.length_take]
              cases wordSize with
              | zero => contradiction
              | succ wordSize => simp
          | tail _ htail => exact ih _ htail

private theorem chunkPayloadWords_length_le_payload_length
    {wordSize : Nat} (hwordSize : 0 < wordSize) (payload : List Bool) :
    (chunkPayloadWords wordSize payload).length <= payload.length := by
  calc
    (chunkPayloadWords wordSize payload).length <=
        (flattenPayloadWords (chunkPayloadWords wordSize payload)).length := by
      apply list_length_le_flattenPayloadWords_length_of_mem_length_pos
      intro word hmem
      exact chunkPayloadWords_mem_length_pos hwordSize payload word hmem
    _ = payload.length := by
      rw [flattenPayloadWords_chunkPayloadWords hwordSize]

private theorem fixedWidthNatTable_words_length_le_payload_length
    {entries : List Nat} {width : Nat}
    (table : FixedWidthNatTable entries width) (hwidth : 0 < width) :
    table.store.words.size <= table.payload.length := by
  have hpos : forall word,
      List.Mem word table.store.words.toList -> 0 < word.length := by
    intro word hmem
    rcases List.mem_iff_getElem?.mp hmem with ⟨i, hi⟩
    have hlen := table.word_length_of_get? (by
      simpa [Array.getElem?_toList] using hi)
    omega
  calc
    table.store.words.size = table.store.words.toList.length := by simp
    _ <= (flattenPayloadWords table.store.words.toList).length :=
      list_length_le_flattenPayloadWords_length_of_mem_length_pos
        table.store.words.toList hpos
    _ = table.payload.length := by rw [table.store.erases]

private theorem fixedWidthNatTable_machineWords_length_le_payload_length
    {entries : List Nat} {width wordSize : Nat}
    (table : FixedWidthNatTable entries width) (hwordSize : 0 < wordSize) :
    (fixedWidthNatTableMachineWords table wordSize).length <=
      table.payload.length := by
  calc
    (fixedWidthNatTableMachineWords table wordSize).length <=
        (flattenPayloadWords
          (fixedWidthNatTableMachineWords table wordSize)).length := by
      apply list_length_le_flattenPayloadWords_length_of_mem_length_pos
      intro word hmem
      rcases List.mem_flatMap.mp hmem with ⟨logical, _hlogical, hchunk⟩
      exact chunkPayloadWords_mem_length_pos hwordSize logical word hchunk
    _ = table.payload.length := by
      unfold fixedWidthNatTableMachineWords
      rw [flattenPayloadWords_flatMap_chunkPayloadWords hwordSize]
      exact congrArg List.length table.store.erases

private theorem canonicalSuperRankFalseWords_length_le
    (bits : List Bool) (wordSize blocksPerSuper width : Nat)
    (hwidth : bits.length < 2 ^ width) :
    (SuccinctRank.canonicalSuperRankSampleTables bits wordSize blocksPerSuper
      width hwidth).falseTable.store.words.size <= bits.length + 1 := by
  have hdiv0 : bits.length / wordSize <= bits.length := Nat.div_le_self _ _
  have hdiv1 : bits.length / wordSize / blocksPerSuper <= bits.length :=
    Nat.le_trans (Nat.div_le_self _ _) hdiv0
  simp [SuccinctRank.canonicalSuperRankSampleTables,
    SuccinctSpace.FixedWidthRankSampleTables.ofEntries,
    SuccinctSpace.FixedWidthNatTable.ofEntries,
    SuccinctSpace.FixedWidthNatTable.ofEncodedWords,
    SuccinctRank.canonicalSuperRankEntries_length]
  omega

private theorem canonicalBlockRankFalseWords_length_le
    (bits : List Bool) (wordSize blocksPerSuper width : Nat)
    (hblocks : 0 < blocksPerSuper)
    (hwidth : blocksPerSuper * wordSize < 2 ^ width) :
    (SuccinctRank.canonicalBlockRankSampleTablesOfLocalSpan bits wordSize
      blocksPerSuper width hblocks hwidth).falseTable.store.words.size <=
        bits.length + 1 := by
  have hdiv : bits.length / wordSize <= bits.length := Nat.div_le_self _ _
  simp [SuccinctRank.canonicalBlockRankSampleTablesOfLocalSpan,
    SuccinctSpace.FixedWidthRankSampleTables.ofEntries,
    SuccinctSpace.FixedWidthNatTable.ofEntries,
    SuccinctSpace.FixedWidthNatTable.ofEncodedWords,
    SuccinctRank.canonicalBlockRankEntries_length]
  omega

private theorem canonicalSuperRankTrueWords_length_le
    (bits : List Bool) (wordSize blocksPerSuper width : Nat)
    (hwidth : bits.length < 2 ^ width) :
    (SuccinctRank.canonicalSuperRankSampleTables bits wordSize blocksPerSuper
      width hwidth).trueTable.store.words.size <= bits.length + 1 := by
  have hdiv0 : bits.length / wordSize <= bits.length := Nat.div_le_self _ _
  have hdiv1 : bits.length / wordSize / blocksPerSuper <= bits.length :=
    Nat.le_trans (Nat.div_le_self _ _) hdiv0
  simp [SuccinctRank.canonicalSuperRankSampleTables,
    SuccinctSpace.FixedWidthRankSampleTables.ofEntries,
    SuccinctSpace.FixedWidthNatTable.ofEntries,
    SuccinctSpace.FixedWidthNatTable.ofEncodedWords,
    SuccinctRank.canonicalSuperRankEntries_length]
  omega

private theorem canonicalBlockRankTrueWords_length_le
    (bits : List Bool) (wordSize blocksPerSuper width : Nat)
    (hblocks : 0 < blocksPerSuper)
    (hwidth : blocksPerSuper * wordSize < 2 ^ width) :
    (SuccinctRank.canonicalBlockRankSampleTablesOfLocalSpan bits wordSize
      blocksPerSuper width hblocks hwidth).trueTable.store.words.size <=
        bits.length + 1 := by
  have hdiv : bits.length / wordSize <= bits.length := Nat.div_le_self _ _
  simp [SuccinctRank.canonicalBlockRankSampleTablesOfLocalSpan,
    SuccinctSpace.FixedWidthRankSampleTables.ofEntries,
    SuccinctSpace.FixedWidthNatTable.ofEntries,
    SuccinctSpace.FixedWidthNatTable.ofEncodedWords,
    SuccinctRank.canonicalBlockRankEntries_length]
  omega

/-- A single all-size capacity envelope for the canonical physical store. -/
def concreteBPNativeSuccinctRMQReviewerCapacity (n : Nat) : Nat :=
  400000 * (n + 1)

/-- The one pre-execution reviewer word width. -/
def concreteBPNativeSuccinctRMQReviewerWordBits (n : Nat) : Nat :=
  SuccinctRank.machineWordBits
    (concreteBPNativeSuccinctRMQReviewerCapacity n)

theorem concreteBPNativeSuccinctRMQReviewerWordBits_eq
    (n : Nat) :
    concreteBPNativeSuccinctRMQReviewerWordBits n =
      Nat.log2 (400000 * (n + 1)) + 1 := by
  simp [concreteBPNativeSuccinctRMQReviewerWordBits,
    concreteBPNativeSuccinctRMQReviewerCapacity, SuccinctRank.machineWordBits]

theorem concreteBPNativeSuccinctRMQReviewerCapacity_pos (n : Nat) :
    0 < concreteBPNativeSuccinctRMQReviewerCapacity n := by
  unfold concreteBPNativeSuccinctRMQReviewerCapacity
  omega

theorem concreteBPNativeSuccinctRMQReviewerCapacity_lt_two_pow_wordBits
    (n : Nat) :
    concreteBPNativeSuccinctRMQReviewerCapacity n <
      2 ^ concreteBPNativeSuccinctRMQReviewerWordBits n := by
  exact SuccinctRank.self_lt_two_pow_machineWordBits _

/-- The chosen capacity is concretely linear in the input size. -/
theorem concreteBPNativeSuccinctRMQReviewerCapacity_linear (n : Nat) :
    concreteBPNativeSuccinctRMQReviewerCapacity n = 400000 * (n + 1) := by
  rfl

/-- Explicit all-size logarithmic scaling of the one reviewer width. -/
theorem concreteBPNativeSuccinctRMQReviewerWordBits_le_log (n : Nat) :
    concreteBPNativeSuccinctRMQReviewerWordBits n <=
      20 * (Nat.log2 (n + 2) + 1) := by
  let q := Nat.log2 (n + 2) + 1
  have hq : 0 < q := by omega
  have hn : n + 1 < 2 ^ q := by
    have := SuccinctRank.self_lt_two_pow_machineWordBits (n + 2)
    simpa [q, SuccinctRank.machineWordBits] using
      Nat.lt_of_le_of_lt (by omega : n + 1 <= n + 2) this
  have hc : 400000 < 2 ^ 19 := by decide
  have hmul : 400000 * (n + 1) < 2 ^ 19 * 2 ^ q := by
    exact Nat.mul_lt_mul_of_lt_of_lt hc hn
  have hpow : concreteBPNativeSuccinctRMQReviewerCapacity n <
      2 ^ (19 + q) := by
    simpa [concreteBPNativeSuccinctRMQReviewerCapacity, Nat.pow_add] using hmul
  have hlog :
      Nat.log2 (concreteBPNativeSuccinctRMQReviewerCapacity n) < 19 + q :=
    (Nat.log2_lt
      (Nat.ne_of_gt (concreteBPNativeSuccinctRMQReviewerCapacity_pos n))).2 hpow
  unfold concreteBPNativeSuccinctRMQReviewerWordBits
    SuccinctRank.machineWordBits
  omega

theorem concreteBPNativeSuccinctRMQReviewerInputOperand_fits
    (n operand : Nat) (hoperand : operand <= n) :
    operand < 2 ^ concreteBPNativeSuccinctRMQReviewerWordBits n := by
  apply Nat.lt_of_le_of_lt hoperand
  exact Nat.lt_of_le_of_lt (by
      show n <= concreteBPNativeSuccinctRMQReviewerCapacity n
      unfold concreteBPNativeSuccinctRMQReviewerCapacity
      omega)
    (concreteBPNativeSuccinctRMQReviewerCapacity_lt_two_pow_wordBits n)

/-- All live segment encodings and the retained dead segment universe fit. -/
theorem concreteBPNativeSuccinctRMQReviewerSegmentEncoding_fits
    (n segment : Nat) (hsegment : segment <= concreteBPNativeDeadTraceSegment) :
    segment < 2 ^ concreteBPNativeSuccinctRMQReviewerWordBits n := by
  apply Nat.lt_of_le_of_lt hsegment
  exact Nat.lt_of_le_of_lt (by
      show concreteBPNativeDeadTraceSegment <=
        concreteBPNativeSuccinctRMQReviewerCapacity n
      unfold concreteBPNativeSuccinctRMQReviewerCapacity
        concreteBPNativeDeadTraceSegment
      omega)
    (concreteBPNativeSuccinctRMQReviewerCapacity_lt_two_pow_wordBits n)

private theorem concreteBPNativeSuccinctRMQReviewerBPWords_length_le
    (shape : Cartesian.CartesianShape) :
    (concreteBPNativeSuccinctRMQReviewerSourceWords
      shape .finalRankBPCodeAlias).length <= 2 * shape.bpCode.length + 1 := by
  have hchunks := chunkPayloadWords_length_le_payload_length
    (SuccinctRank.machineWordBits_pos shape.bpCode.length) shape.bpCode
  simp [concreteBPNativeSuccinctRMQReviewerSourceWords,
    concreteBPNativeSuccinctRMQFlatPayloadSourceWords,
    builtRelativeSplitBPCloseRankData,
    builtRelativeSplitBPCloseRankWordSize,
    SuccinctRank.canonicalTwoLevelRankDataOfChunksExactLocalBlock,
    SuccinctRank.canonicalTwoLevelRankDataOfBridgeLocalBlock,
    SuccinctRank.canonicalRankWordBridgeOfChunksWithSentinel,
    SuccinctSpace.BoundedPayloadWordStore.ofChunksWithSentinel]
  omega

private theorem concreteBPNativeSuccinctRMQReviewerSelectSuperBaseOccurrence_length_le
    (shape : Cartesian.CartesianShape) :
    (concreteBPNativeSuccinctRMQReviewerSourceWords
      shape .selectSuperBaseOccurrence).length <=
        2 * shape.bpCode.length + 1 := by
  have hsuperCount :
      GenericSelect.superSlotCount shape.bpCode false <=
        shape.bpCode.length := by
    simpa [GenericSelect.longSuperFlagBits] using
      GenericSelect.longSuperFlagBits_length_le_length shape.bpCode false
  have hentries :
      (GenericSelect.superEntries shape.bpCode false).length <=
        shape.bpCode.length := by
    simpa [GenericSelect.superEntries_length] using hsuperCount
  simp [concreteBPNativeSuccinctRMQReviewerSourceWords,
    concreteBPNativeSuccinctRMQFlatPayloadSourceWords,
    GenericSelect.sparseExceptionSelectData,
    GenericSelect.superTable,
    GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable.ofEntries,
    GenericSelect.SparseDenseSelectDenseLocalEntry.baseOccurrences,
    SuccinctSpace.FixedWidthNatTable.ofEntries,
    SuccinctSpace.FixedWidthNatTable.ofEncodedWords]
  omega

private theorem concreteBPNativeSuccinctRMQReviewerSelectSuperFields_length_le
    (shape : Cartesian.CartesianShape) :
    (concreteBPNativeSuccinctRMQReviewerSourceWords
      shape .selectSuperBaseWordIndex).length <= 2 * shape.bpCode.length + 1 /\
    (concreteBPNativeSuccinctRMQReviewerSourceWords
      shape .selectSuperRankBefore).length <= 2 * shape.bpCode.length + 1 /\
    (concreteBPNativeSuccinctRMQReviewerSourceWords
      shape .selectSuperFirstOffset).length <= 2 * shape.bpCode.length + 1 := by
  have h :=
    concreteBPNativeSuccinctRMQReviewerSelectSuperBaseOccurrence_length_le shape
  simp [concreteBPNativeSuccinctRMQReviewerSourceWords,
    concreteBPNativeSuccinctRMQFlatPayloadSourceWords,
    GenericSelect.sparseExceptionSelectData,
    GenericSelect.superTable,
    GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable.ofEntries,
    GenericSelect.SparseDenseSelectDenseLocalEntry.baseOccurrences,
    GenericSelect.SparseDenseSelectDenseLocalEntry.baseWordIndices,
    GenericSelect.SparseDenseSelectDenseLocalEntry.ranksBefore,
    GenericSelect.SparseDenseSelectDenseLocalEntry.firstOffsets,
    SuccinctSpace.FixedWidthNatTable.ofEntries,
    SuccinctSpace.FixedWidthNatTable.ofEncodedWords] at h ⊢
  omega

private theorem concreteBPNativeSuccinctRMQReviewerSelectLocalFields_length_le
    (shape : Cartesian.CartesianShape) :
    (concreteBPNativeSuccinctRMQReviewerSourceWords
      shape .selectLocalBaseOccurrence).length <= 10 * shape.bpCode.length + 1 /\
    (concreteBPNativeSuccinctRMQReviewerSourceWords
      shape .selectLocalBaseWordIndex).length <= 10 * shape.bpCode.length + 1 /\
    (concreteBPNativeSuccinctRMQReviewerSourceWords
      shape .selectLocalRankBefore).length <= 10 * shape.bpCode.length + 1 /\
    (concreteBPNativeSuccinctRMQReviewerSourceWords
      shape .selectLocalFirstOffset).length <= 10 * shape.bpCode.length + 1 := by
  have hscaled := GenericSelect.localSlotCount_mul_localStride_le_const_length
    shape.bpCode false
  have hstride := GenericSelect.localStride_pos shape.bpCode.length
  have hslots : GenericSelect.localSlotCount shape.bpCode false <=
      10 * shape.bpCode.length := by
    exact Nat.le_trans (Nat.le_mul_of_pos_right _ hstride) hscaled
  have hentries : (GenericSelect.localEntries shape.bpCode false).length <=
      10 * shape.bpCode.length := by
    simpa [GenericSelect.localEntries_length] using hslots
  simp [concreteBPNativeSuccinctRMQReviewerSourceWords,
    concreteBPNativeSuccinctRMQFlatPayloadSourceWords,
    GenericSelect.sparseExceptionSelectData,
    GenericSelect.localTable,
    GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable.ofEntries,
    GenericSelect.SparseDenseSelectDenseLocalEntry.baseOccurrences,
    GenericSelect.SparseDenseSelectDenseLocalEntry.baseWordIndices,
    GenericSelect.SparseDenseSelectDenseLocalEntry.ranksBefore,
    GenericSelect.SparseDenseSelectDenseLocalEntry.firstOffsets,
    SuccinctSpace.FixedWidthNatTable.ofEntries,
    SuccinctSpace.FixedWidthNatTable.ofEncodedWords]
  omega

private theorem concreteBPNativeSuccinctRMQReviewerSelectFlagBitWords_length_le
    (shape : Cartesian.CartesianShape) :
    (concreteBPNativeSuccinctRMQReviewerSourceWords
      shape .selectLongFlagBits).length <= 2 * shape.bpCode.length + 1 /\
    (concreteBPNativeSuccinctRMQReviewerSourceWords
      shape .selectSparseFlagBits).length <= 2 * shape.bpCode.length + 1 := by
  have hlongFlags := GenericSelect.longSuperFlagBits_length_le_length
    shape.bpCode false
  have hsparseFlags :=
    GenericSelect.sparseExceptionEffectiveFlagBits_length_le_length
      shape.bpCode false
  have hlongChunks := chunkPayloadWords_length_le_payload_length
    (GenericSelect.longFlagRankWordSize_pos shape.bpCode false)
    (GenericSelect.longSuperFlagBits shape.bpCode false)
  have hsparseChunks := chunkPayloadWords_length_le_payload_length
    (GenericSelect.sparseExceptionEffectiveFlagRankWordSize_pos
      shape.bpCode false)
    (GenericSelect.sparseExceptionEffectiveFlagBits shape.bpCode false)
  simp [concreteBPNativeSuccinctRMQReviewerSourceWords,
    concreteBPNativeSuccinctRMQFlatPayloadSourceWords,
    GenericSelect.sparseExceptionSelectData,
    GenericSelect.longFlagRankData,
    GenericSelect.sparseExceptionDirectory,
    GenericSelect.sparseExceptionEffectiveFlagRankData,
    SuccinctRank.canonicalTwoLevelRankDataOfChunksExactLocalBlock,
    SuccinctRank.canonicalTwoLevelRankDataOfBridgeLocalBlock,
    SuccinctRank.canonicalRankWordBridgeOfChunksWithSentinel,
    SuccinctSpace.BoundedPayloadWordStore.ofChunksWithSentinel]
  omega

private theorem concreteBPNativeSuccinctRMQReviewerRankTableSources_length_le
    (shape : Cartesian.CartesianShape) :
    (concreteBPNativeSuccinctRMQReviewerSourceWords
      shape .finalRankSuperFalse).length <= shape.bpCode.length + 1 /\
    (concreteBPNativeSuccinctRMQReviewerSourceWords
      shape .finalRankBlockFalse).length <= shape.bpCode.length + 1 /\
    (concreteBPNativeSuccinctRMQReviewerSourceWords
      shape .selectLongFlagRankSuperTrue).length <= shape.bpCode.length + 1 /\
    (concreteBPNativeSuccinctRMQReviewerSourceWords
      shape .selectLongFlagRankBlockTrue).length <= shape.bpCode.length + 1 /\
    (concreteBPNativeSuccinctRMQReviewerSourceWords
      shape .selectSparseRankSuperTrue).length <= shape.bpCode.length + 1 /\
    (concreteBPNativeSuccinctRMQReviewerSourceWords
      shape .selectSparseRankBlockTrue).length <= shape.bpCode.length + 1 := by
  have hfinalSuper := canonicalSuperRankFalseWords_length_le shape.bpCode
    (builtRelativeSplitBPCloseRankWordSize shape)
    (builtRelativeSplitBPCloseRankBlocksPerSuper shape)
    (builtRelativeSplitBPCloseRankWordSize shape)
    (builtRelativeSplitBPCloseRank_bpCode_length_lt_word_pow shape)
  have hfinalBlock := canonicalBlockRankFalseWords_length_le shape.bpCode
    (builtRelativeSplitBPCloseRankWordSize shape)
    (builtRelativeSplitBPCloseRankBlocksPerSuper shape)
    (builtRelativeSplitBPCloseRankBlockWidth shape)
    (builtRelativeSplitBPCloseRankBlocksPerSuper_pos shape)
    (builtRelativeSplitBPCloseRankBlockSpan_lt_pow shape)
  have hlongSuper := canonicalSuperRankTrueWords_length_le
    (GenericSelect.longSuperFlagBits shape.bpCode false)
    (GenericSelect.longFlagRankWordSize shape.bpCode false)
    (GenericSelect.longFlagRankBlocksPerSuper shape.bpCode false)
    (GenericSelect.longFlagRankWordSize shape.bpCode false)
    (GenericSelect.longSuperFlagBits_length_lt_rank_word_pow shape.bpCode false)
  have hlongBlock := canonicalBlockRankTrueWords_length_le
    (GenericSelect.longSuperFlagBits shape.bpCode false)
    (GenericSelect.longFlagRankWordSize shape.bpCode false)
    (GenericSelect.longFlagRankBlocksPerSuper shape.bpCode false)
    (GenericSelect.longFlagRankBlockWidth shape.bpCode false)
    (GenericSelect.longFlagRankBlocksPerSuper_pos shape.bpCode false)
    (GenericSelect.longFlagRankBlockSpan_lt_pow shape.bpCode false)
  have hsparseSuper := canonicalSuperRankTrueWords_length_le
    (GenericSelect.sparseExceptionEffectiveFlagBits shape.bpCode false)
    (GenericSelect.sparseExceptionEffectiveFlagRankWordSize shape.bpCode false)
    (GenericSelect.sparseExceptionEffectiveFlagRankBlocksPerSuper shape.bpCode false)
    (GenericSelect.sparseExceptionEffectiveFlagRankWordSize shape.bpCode false)
    (GenericSelect.sparseExceptionEffectiveFlagBits_length_lt_rank_word_pow
      shape.bpCode false)
  have hsparseBlock := canonicalBlockRankTrueWords_length_le
    (GenericSelect.sparseExceptionEffectiveFlagBits shape.bpCode false)
    (GenericSelect.sparseExceptionEffectiveFlagRankWordSize shape.bpCode false)
    (GenericSelect.sparseExceptionEffectiveFlagRankBlocksPerSuper shape.bpCode false)
    (GenericSelect.sparseExceptionEffectiveFlagRankBlockWidth shape.bpCode false)
    (GenericSelect.sparseExceptionEffectiveFlagRankBlocksPerSuper_pos
      shape.bpCode false)
    (GenericSelect.sparseExceptionEffectiveFlagRankBlockSpan_lt_pow
      shape.bpCode false)
  have hlongFlags := GenericSelect.longSuperFlagBits_length_le_length
    shape.bpCode false
  have hsparseFlags :=
    GenericSelect.sparseExceptionEffectiveFlagBits_length_le_length
      shape.bpCode false
  simp [concreteBPNativeSuccinctRMQReviewerSourceWords,
    concreteBPNativeSuccinctRMQFlatPayloadSourceWords,
    builtRelativeSplitBPCloseRankData,
    GenericSelect.sparseExceptionSelectData,
    GenericSelect.longFlagRankData,
    GenericSelect.sparseExceptionDirectory,
    GenericSelect.sparseExceptionEffectiveFlagRankData,
    SuccinctRank.canonicalTwoLevelRankDataOfChunksExactLocalBlock,
    SuccinctRank.canonicalTwoLevelRankDataOfBridgeLocalBlock] at
      *
  omega

private theorem concreteBPNativeSuccinctRMQReviewerRelativeSources_length_le
    (shape : Cartesian.CartesianShape) :
    (concreteBPNativeSuccinctRMQReviewerSourceWords
      shape .selectLongRelative).length <= 19906 * shape.size + 561 /\
    (concreteBPNativeSuccinctRMQReviewerSourceWords
      shape .selectSparseRelative).length <= 19906 * shape.size + 561 := by
  have hlongWords := fixedWidthNatTable_words_length_le_payload_length
    (GenericSelect.longSuperRelativeTable shape.bpCode false)
    (by simp [GenericSelect.longSuperRelativeWidth,
      SuccinctRank.machineWordBits_pos])
  have hsparseWords := fixedWidthNatTable_words_length_le_payload_length
    (GenericSelect.sparseExceptionRelativeTable shape.bpCode false)
    (by simp [GenericSelect.sparseExceptionRelativeWidth,
      SuccinctRank.machineWordBits_pos])
  have hlongPayload :
      (GenericSelect.longSuperRelativeTable shape.bpCode false).payload.length <=
        (concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessPayload
          shape).length := by
    simp [concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessPayload,
      concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources,
      concreteBPNativeSuccinctRMQFlatPayloadSourcePayload,
      GenericSelect.sparseExceptionSelectData]
    omega
  have hsparsePayload :
      (GenericSelect.sparseExceptionRelativeTable shape.bpCode false).payload.length <=
        (concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessPayload
          shape).length := by
    simp [concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessPayload,
      concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources,
      concreteBPNativeSuccinctRMQFlatPayloadSourcePayload,
      GenericSelect.sparseExceptionSelectData,
      GenericSelect.sparseExceptionDirectory]
    omega
  have hlive :=
    concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessPayload_length_le shape
  have haccess :=
    (builtGenericSparseExceptionSelectBPCloseAccessDirectory
      shape).payload_length_le_overhead
  have hlinear := genericSparseExceptionBPCloseAccessOverhead_le_linear shape.size
  simp [concreteBPNativeSuccinctRMQReviewerSourceWords,
    concreteBPNativeSuccinctRMQFlatPayloadSourceWords,
    GenericSelect.sparseExceptionSelectData,
    GenericSelect.sparseExceptionDirectory] at hlongWords hsparseWords ⊢
  omega

private theorem concreteBPNativeSuccinctRMQReviewerCloseWords_length_le
    (shape : Cartesian.CartesianShape) :
    (concreteBPNativeSuccinctRMQReviewerCloseWords shape).length <=
      (SuccinctClose.canonicalRelativeRmmInteriorDirectory shape).payload.length := by
  let summary := SuccinctClose.canonicalRelativeRmmSummaryTable shape
  let localTable := SuccinctClose.canonicalRelativeRmmInteriorLocalTable shape
  let global := SuccinctClose.canonicalRelativeRmmInteriorGlobalTable shape
  let hword := SuccinctRank.machineWordBits_pos shape.bpCode.length
  have hbase := fixedWidthNatTable_machineWords_length_le_payload_length
    summary.baselineTable hword
  have hmin := fixedWidthNatTable_machineWords_length_le_payload_length
    summary.minRelTable hword
  have hmax := fixedWidthNatTable_machineWords_length_le_payload_length
    summary.maxRelTable hword
  have harg := fixedWidthNatTable_machineWords_length_le_payload_length
    summary.argOffsetTable hword
  have hlocal := fixedWidthNatTable_machineWords_length_le_payload_length
    localTable.table hword
  have hglobal := fixedWidthNatTable_machineWords_length_le_payload_length
    global.table hword
  unfold concreteBPNativeSuccinctRMQReviewerCloseWords
  simp only [Array.length_toList]
  change
    (SuccinctClose.canonicalRelativeRmmInteriorComponentStore
      shape).store.words.toList.length <=
      (SuccinctClose.canonicalRelativeRmmInteriorDirectory shape).payload.length
  rw [show
    (SuccinctClose.canonicalRelativeRmmInteriorComponentStore
      shape).store.words.toList =
      (summary.baselineTable.machineStore hword).store.words.toList ++
        (summary.minRelTable.machineStore hword).store.words.toList ++
          (summary.maxRelTable.machineStore hword).store.words.toList ++
            (summary.argOffsetTable.machineStore hword).store.words.toList ++
              (localTable.table.machineStore hword).store.words.toList ++
                (global.table.machineStore hword).store.words.toList by
      simpa [summary, localTable, global, hword] using
        SuccinctClose.canonicalRelativeRmmInteriorComponentStore_words_toList
          shape]
  simp only [List.length_append, Array.length_toList]
  simp [SuccinctClose.canonicalRelativeRmmInteriorDirectory,
    SuccinctSpace.FixedWidthNatTable.machineStore,
    SuccinctClose.PayloadLiveBPRelativeMinMaxArgSummaryTable.payload,
    SuccinctClose.PayloadLiveBPLocalSparseOffsetTable.payload,
    SuccinctClose.PayloadLiveBPGlobalSparseBlockTable.payload,
    summary, localTable, global] at *
  omega

theorem concreteBPNativeSuccinctRMQReviewerPhysicalWords_length_le_capacity
    (shape : Cartesian.CartesianShape) :
    (concreteBPNativeSuccinctRMQReviewerPhysicalWords shape).length <=
      concreteBPNativeSuccinctRMQReviewerCapacity shape.size := by
  have hbp := concreteBPNativeSuccinctRMQReviewerBPWords_length_le shape
  have hsuper0 :=
    concreteBPNativeSuccinctRMQReviewerSelectSuperBaseOccurrence_length_le shape
  rcases concreteBPNativeSuccinctRMQReviewerSelectSuperFields_length_le shape with
    ⟨hsuper1, hsuper2, hsuper3⟩
  rcases concreteBPNativeSuccinctRMQReviewerSelectLocalFields_length_le shape with
    ⟨hlocal0, hlocal1, hlocal2, hlocal3⟩
  rcases concreteBPNativeSuccinctRMQReviewerSelectFlagBitWords_length_le shape with
    ⟨hflag0, hflag1⟩
  rcases concreteBPNativeSuccinctRMQReviewerRankTableSources_length_le shape with
    ⟨hrank0, hrank1, hrank2, hrank3, hrank4, hrank5⟩
  rcases concreteBPNativeSuccinctRMQReviewerRelativeSources_length_le shape with
    ⟨hrel0, hrel1⟩
  have hclose := concreteBPNativeSuccinctRMQReviewerCloseWords_length_le shape
  have hraw :=
    SuccinctClose.canonicalRelativeRmmInteriorDirectory_payload_length_eq_raw shape
  have hcloseLinear :=
    SuccinctClose.canonicalRelativeRmmInteriorRawPayloadOverhead_le_linear
      shape.size
  have hdirLinear :
      (SuccinctClose.canonicalRelativeRmmInteriorDirectory shape).payload.length <=
        218 * (shape.size + 1) := by
    omega
  have hcloseBound :
      (concreteBPNativeSuccinctRMQReviewerCloseWords shape).length <=
        218 * (shape.size + 1) :=
    Nat.le_trans hclose hdirLinear
  rw [concreteBPNativeSuccinctRMQReviewerPhysicalWords_components]
  simp [concreteBPNativeSuccinctRMQReviewerPhysicalSources]
  rw [Cartesian.CartesianShape.bpCode_length] at *
  unfold concreteBPNativeSuccinctRMQReviewerCapacity
  omega

theorem concreteBPNativeSuccinctRMQReviewerPhysicalAddress_le_dead
    (shape : Cartesian.CartesianShape) (segment index : Nat) :
    concreteBPNativeSuccinctRMQReviewerPhysicalAddress shape segment index <=
      concreteBPNativeSuccinctRMQReviewerPhysicalDeadAddress shape := by
  unfold concreteBPNativeSuccinctRMQReviewerPhysicalAddress
    concreteBPNativeSuccinctRMQReviewerSegmentOffset?
  cases hregion : concreteBPNativeSuccinctRMQReviewerSegmentRegion? segment with
  | none => simp
  | some region =>
      simp only [Option.map_some]
      by_cases hindex : index <
          (concreteBPNativeSuccinctRMQReviewerSegmentWords shape segment).length
      · simp only [if_pos hindex]
        let word :=
          (concreteBPNativeSuccinctRMQReviewerSegmentWords shape segment).get
            ⟨index, hindex⟩
        have hsource :
            (concreteBPNativeSuccinctRMQReviewerSegmentWords
              shape segment)[index]? = some word := by
          simp [word, hindex]
        have hphysical := concreteBPNativeSuccinctRMQReviewerSegment_getElem
          shape segment region index hregion hindex
        rw [hsource] at hphysical
        have hlt := (List.getElem?_eq_some_iff.mp hphysical).1
        simpa [concreteBPNativeSuccinctRMQReviewerPhysicalDeadAddress] using
          Nat.le_of_lt hlt
      · simp [if_neg hindex]

theorem concreteBPNativeSuccinctRMQReviewerPhysicalDeadAddress_fits
    (shape : Cartesian.CartesianShape) :
    concreteBPNativeSuccinctRMQReviewerPhysicalDeadAddress shape <
      2 ^ concreteBPNativeSuccinctRMQReviewerWordBits shape.size := by
  apply Nat.lt_of_le_of_lt
  · exact concreteBPNativeSuccinctRMQReviewerPhysicalWords_length_le_capacity
      shape
  · exact concreteBPNativeSuccinctRMQReviewerCapacity_lt_two_pow_wordBits
      shape.size

/-- Every translated address, including failed/dead translations, fits. -/
theorem concreteBPNativeSuccinctRMQReviewerPhysicalAddress_fits
    (shape : Cartesian.CartesianShape) (segment index : Nat) :
    concreteBPNativeSuccinctRMQReviewerPhysicalAddress shape segment index <
      2 ^ concreteBPNativeSuccinctRMQReviewerWordBits shape.size := by
  exact Nat.lt_of_le_of_lt
    (concreteBPNativeSuccinctRMQReviewerPhysicalAddress_le_dead
      shape segment index)
    (concreteBPNativeSuccinctRMQReviewerPhysicalDeadAddress_fits shape)

private theorem concreteBPNativeSuccinctRMQReviewerMachineWordBits_le_wordBits
    (shape : Cartesian.CartesianShape) :
    SuccinctRank.machineWordBits shape.bpCode.length <=
      concreteBPNativeSuccinctRMQReviewerWordBits shape.size := by
  unfold concreteBPNativeSuccinctRMQReviewerWordBits
  apply SuccinctRank.machineWordBits_mono_le
  rw [Cartesian.CartesianShape.bpCode_length]
  unfold concreteBPNativeSuccinctRMQReviewerCapacity
  omega

private theorem concreteBPNativeSuccinctRMQReviewerFinalBlockWidth_le_wordBits
    (shape : Cartesian.CartesianShape) :
    builtRelativeSplitBPCloseRankBlockWidth shape <=
      concreteBPNativeSuccinctRMQReviewerWordBits shape.size := by
  unfold builtRelativeSplitBPCloseRankBlockWidth
    concreteBPNativeSuccinctRMQReviewerWordBits
  apply SuccinctRank.machineWordBits_mono_le
  by_cases hzero : shape.bpCode.length = 0
  · simp [builtRelativeSplitBPCloseRankWordSize,
      SuccinctRank.machineWordBits, hzero,
      concreteBPNativeSuccinctRMQReviewerCapacity]
    omega
  · have hsquare :=
      SuccinctSelect.machineWordBits_sq_le_four_mul_self_of_pos
        (Nat.pos_of_ne_zero hzero)
    apply Nat.le_trans hsquare
    rw [Cartesian.CartesianShape.bpCode_length]
    unfold concreteBPNativeSuccinctRMQReviewerCapacity
    omega

private theorem concreteBPNativeSuccinctRMQReviewerSelectSuperWord_length_le
    (shape : Cartesian.CartesianShape) {word : List Bool}
    (hword : List.Mem word
      (GenericSelect.sparseExceptionSelectData
        shape.bpCode false).superTable.readWords) :
    word.length <= concreteBPNativeSuccinctRMQReviewerWordBits shape.size := by
  apply Nat.le_trans
    ((GenericSelect.sparseExceptionSelectData
      shape.bpCode false).read_word_length_le_machine (by
        unfold GenericSelect.SparseExceptionSelectData.readWords
        apply List.mem_append_left
        apply List.mem_append_left
        apply List.mem_append_left
        apply List.mem_append_left
        apply List.mem_append_left
        exact hword))
  exact concreteBPNativeSuccinctRMQReviewerMachineWordBits_le_wordBits shape

private theorem concreteBPNativeSuccinctRMQReviewerSelectLongRankWord_length_le
    (shape : Cartesian.CartesianShape) {word : List Bool}
    (hword : List.Mem word
      (GenericSelect.sparseExceptionSelectData
        shape.bpCode false).longFlagRankReadWords) :
    word.length <= concreteBPNativeSuccinctRMQReviewerWordBits shape.size := by
  apply Nat.le_trans
    ((GenericSelect.sparseExceptionSelectData
      shape.bpCode false).read_word_length_le_machine (by
        unfold GenericSelect.SparseExceptionSelectData.readWords
        apply List.mem_append_left
        apply List.mem_append_left
        apply List.mem_append_left
        apply List.mem_append_left
        apply List.mem_append_right
        exact hword))
  exact concreteBPNativeSuccinctRMQReviewerMachineWordBits_le_wordBits shape

private theorem concreteBPNativeSuccinctRMQReviewerSelectLongRelativeWord_length_le
    (shape : Cartesian.CartesianShape) {word : List Bool}
    (hword : List.Mem word
      (GenericSelect.sparseExceptionSelectData
        shape.bpCode false).longSuperRelativeTable.store.words.toList) :
    word.length <= concreteBPNativeSuccinctRMQReviewerWordBits shape.size := by
  apply Nat.le_trans
    ((GenericSelect.sparseExceptionSelectData
      shape.bpCode false).read_word_length_le_machine (by
        unfold GenericSelect.SparseExceptionSelectData.readWords
        apply List.mem_append_left
        apply List.mem_append_left
        apply List.mem_append_left
        apply List.mem_append_right
        exact hword))
  exact concreteBPNativeSuccinctRMQReviewerMachineWordBits_le_wordBits shape

private theorem concreteBPNativeSuccinctRMQReviewerSelectLocalWord_length_le
    (shape : Cartesian.CartesianShape) {word : List Bool}
    (hword : List.Mem word
      (GenericSelect.sparseExceptionSelectData
        shape.bpCode false).localTable.readWords) :
    word.length <= concreteBPNativeSuccinctRMQReviewerWordBits shape.size := by
  apply Nat.le_trans
    ((GenericSelect.sparseExceptionSelectData
      shape.bpCode false).read_word_length_le_machine (by
        unfold GenericSelect.SparseExceptionSelectData.readWords
        apply List.mem_append_left
        apply List.mem_append_left
        apply List.mem_append_right
        exact hword))
  exact concreteBPNativeSuccinctRMQReviewerMachineWordBits_le_wordBits shape

private theorem concreteBPNativeSuccinctRMQReviewerSelectSparseWord_length_le
    (shape : Cartesian.CartesianShape) {word : List Bool}
    (hword : List.Mem word
      (GenericSelect.sparseExceptionSelectData
        shape.bpCode false).sparseDirectory.readWords) :
    word.length <= concreteBPNativeSuccinctRMQReviewerWordBits shape.size := by
  apply Nat.le_trans
    ((GenericSelect.sparseExceptionSelectData
      shape.bpCode false).read_word_length_le_machine (by
        unfold GenericSelect.SparseExceptionSelectData.readWords
        apply List.mem_append_left
        apply List.mem_append_right
        exact hword))
  exact concreteBPNativeSuccinctRMQReviewerMachineWordBits_le_wordBits shape

/-- Every word in the one pre-execution physical store fits the one reviewer width. -/
theorem concreteBPNativeSuccinctRMQReviewerPhysicalWord_length_le_wordBits
    (shape : Cartesian.CartesianShape) {word : List Bool}
    (hmem : List.Mem word
      (concreteBPNativeSuccinctRMQReviewerPhysicalWords shape)) :
    word.length <= concreteBPNativeSuccinctRMQReviewerWordBits shape.size := by
  rw [concreteBPNativeSuccinctRMQReviewerPhysicalWords_components] at hmem
  rcases List.mem_append.mp hmem with houter | hclose
  · simp only [concreteBPNativeSuccinctRMQReviewerPhysicalSources,
      List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.mem_append] at houter
    rcases houter with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 |
      h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18
    · change List.Mem word
        (builtRelativeSplitBPCloseRankData
          shape).bitWords.store.words.toList at h0
      exact Nat.le_trans
        ((builtRelativeSplitBPCloseRankData
          shape).payload_word_length_le_machine h0)
        (concreteBPNativeSuccinctRMQReviewerMachineWordBits_le_wordBits shape)
    · change List.Mem word
        (builtRelativeSplitBPCloseRankData
          shape).superTables.falseTable.store.words.toList at h1
      apply GenericSelect.fixedWidthNatTable_word_length_le_of_mem
        (builtRelativeSplitBPCloseRankData shape).superTables.falseTable
        ?_ h1
      simpa [builtRelativeSplitBPCloseRankData,
        builtRelativeSplitBPCloseRankWordSize,
        SuccinctRank.canonicalTwoLevelRankDataOfChunksExactLocalBlock,
        SuccinctRank.canonicalTwoLevelRankDataOfBridgeLocalBlock] using
          concreteBPNativeSuccinctRMQReviewerMachineWordBits_le_wordBits shape
    · change List.Mem word
        (builtRelativeSplitBPCloseRankData
          shape).blockTables.falseTable.store.words.toList at h2
      apply GenericSelect.fixedWidthNatTable_word_length_le_of_mem
        (builtRelativeSplitBPCloseRankData shape).blockTables.falseTable
        ?_ h2
      simpa [builtRelativeSplitBPCloseRankData,
        SuccinctRank.canonicalTwoLevelRankDataOfChunksExactLocalBlock,
        SuccinctRank.canonicalTwoLevelRankDataOfBridgeLocalBlock] using
          concreteBPNativeSuccinctRMQReviewerFinalBlockWidth_le_wordBits shape
    · apply concreteBPNativeSuccinctRMQReviewerSelectSuperWord_length_le shape
      unfold GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable.readWords
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      exact h3
    · apply concreteBPNativeSuccinctRMQReviewerSelectSuperWord_length_le shape
      unfold GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable.readWords
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_right
      exact h4
    · apply concreteBPNativeSuccinctRMQReviewerSelectSuperWord_length_le shape
      unfold GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable.readWords
      apply List.mem_append_left
      apply List.mem_append_right
      exact h5
    · apply concreteBPNativeSuccinctRMQReviewerSelectSuperWord_length_le shape
      unfold GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable.readWords
      apply List.mem_append_right
      exact h6
    · apply concreteBPNativeSuccinctRMQReviewerSelectLocalWord_length_le shape
      unfold GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable.readWords
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      exact h7
    · apply concreteBPNativeSuccinctRMQReviewerSelectLocalWord_length_le shape
      unfold GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable.readWords
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_right
      exact h8
    · apply concreteBPNativeSuccinctRMQReviewerSelectLocalWord_length_le shape
      unfold GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable.readWords
      apply List.mem_append_left
      apply List.mem_append_right
      exact h9
    · apply concreteBPNativeSuccinctRMQReviewerSelectLocalWord_length_le shape
      unfold GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable.readWords
      apply List.mem_append_right
      exact h10
    · apply concreteBPNativeSuccinctRMQReviewerSelectLongRankWord_length_le shape
      unfold GenericSelect.SparseExceptionSelectData.longFlagRankReadWords
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      exact h11
    · apply concreteBPNativeSuccinctRMQReviewerSelectLongRankWord_length_le shape
      unfold GenericSelect.SparseExceptionSelectData.longFlagRankReadWords
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_right
      exact h12
    · apply concreteBPNativeSuccinctRMQReviewerSelectLongRankWord_length_le shape
      unfold GenericSelect.SparseExceptionSelectData.longFlagRankReadWords
      apply List.mem_append_right
      exact h13
    · exact
        concreteBPNativeSuccinctRMQReviewerSelectLongRelativeWord_length_le
          shape h14
    · apply concreteBPNativeSuccinctRMQReviewerSelectSparseWord_length_le shape
      unfold GenericSelect.SparseExceptionDirectory.readWords
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      exact h15
    · apply concreteBPNativeSuccinctRMQReviewerSelectSparseWord_length_le shape
      unfold GenericSelect.SparseExceptionDirectory.readWords
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_right
      exact h16
    · apply concreteBPNativeSuccinctRMQReviewerSelectSparseWord_length_le shape
      unfold GenericSelect.SparseExceptionDirectory.readWords
      apply List.mem_append_left
      apply List.mem_append_right
      exact h17
    · apply concreteBPNativeSuccinctRMQReviewerSelectSparseWord_length_le shape
      unfold GenericSelect.SparseExceptionDirectory.readWords
      apply List.mem_append_right
      exact h18
  · change List.Mem word
      (SuccinctClose.canonicalRelativeRmmInteriorComponentStore
        shape).store.words.toList at hclose
    exact Nat.le_trans
      (SuccinctClose.canonicalRelativeRmmInteriorComponentStore_words_bounded
        shape hclose)
      (concreteBPNativeSuccinctRMQReviewerMachineWordBits_le_wordBits shape)

/-- Every successful logical read returns a word bounded by the reviewer width. -/
theorem concreteBPNativeSuccinctRMQReviewerSuccessfulRead_word_length_le_wordBits
    (shape : Cartesian.CartesianShape) {segment index : Nat} {word : List Bool}
    (hread :
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
        segment index = some word) :
    word.length <= concreteBPNativeSuccinctRMQReviewerWordBits shape.size := by
  have hphysical :=
    concreteBPNativeSuccinctRMQReviewerSuccessfulRead_physical shape hread
  apply concreteBPNativeSuccinctRMQReviewerPhysicalWord_length_le_wordBits shape
  exact List.mem_iff_getElem?.2 ⟨_, hphysical.2⟩

end SuccinctFinal
end RMQ
