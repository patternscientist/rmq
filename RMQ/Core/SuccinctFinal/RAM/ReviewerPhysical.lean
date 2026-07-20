import RMQ.Core.SuccinctFinal.RAM.FlatPayload
import RMQ.Core.SuccinctClose.RelativeRmmMacro.ChargedFringeTableFacts

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

/--
The exhaustive live-source universe of the canonical reviewer machine.

The shared BP-code source occurs once even though logical segments `0` and
`19` both read it.  The canonical concatenated close component is a first-class
source rather than a special region appended after an outer-source list.
-/
inductive ReviewerSource where
  | sharedBPCode
  | finalRankSuperFalse
  | finalRankBlockFalse
  | selectSuperBaseOccurrence
  | selectSuperBaseWordIndex
  | selectSuperRankBefore
  | selectSuperFirstOffset
  | selectLocalBaseOccurrence
  | selectLocalBaseWordIndex
  | selectLocalRankBefore
  | selectLocalFirstOffset
  | selectLongFlagRankSuperTrue
  | selectLongFlagRankBlockTrue
  | selectLongFlagBits
  | selectLongRelative
  | selectSparseRankSuperTrue
  | selectSparseRankBlockTrue
  | selectSparseFlagBits
  | selectSparseRelative
  | canonicalClose
  | fringeChunkTable
  | selectChunkTable
deriving DecidableEq

/-- Unique live payload sources, in canonical public order. -/
def concreteBPNativeSuccinctRMQReviewerPhysicalSources : List ReviewerSource :=
  [ .sharedBPCode
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
  , .selectSparseRelative
  , .canonicalClose
  , .fringeChunkTable
  , .selectChunkTable ]

/--
The actual globally segmented evaluator leaves that can issue reviewer reads.
This type follows the three read-producing branches of
`WholeQueryInstr.evalGlobalWordTrace`; the RAM module proves that connection
against the concrete closed program.
 -/
inductive ReviewerReadLeaf where
  | selectClose
  | rankClose
  | canonicalClose
deriving DecidableEq

/-- Complete typed logical-segment-to-source map for the canonical route. -/
def concreteBPNativeSuccinctRMQReviewerSegmentSource? :
    Nat -> Option ReviewerSource
  | 0 => some .sharedBPCode
  | 1 => some .selectSuperBaseOccurrence
  | 2 => some .selectSuperBaseWordIndex
  | 3 => some .selectSuperRankBefore
  | 4 => some .selectSuperFirstOffset
  | 5 => some .selectLocalBaseOccurrence
  | 6 => some .selectLocalBaseWordIndex
  | 7 => some .selectLocalRankBefore
  | 8 => some .selectLocalFirstOffset
  | 9 => some .selectLongFlagRankSuperTrue
  | 10 => some .selectLongFlagRankBlockTrue
  | 11 => some .selectLongFlagBits
  | 12 => some .selectLongRelative
  | 13 => some .selectSparseRankSuperTrue
  | 14 => some .selectSparseRankBlockTrue
  | 15 => some .selectSparseFlagBits
  | 16 => some .selectSparseRelative
  | 17 => some .finalRankSuperFalse
  | 18 => some .finalRankBlockFalse
  | 19 => some .sharedBPCode
  | 20 => some .canonicalClose
  | 21 => some .fringeChunkTable
  | 22 => some .selectChunkTable
  | _ + 23 => none

/--
Compatibility category map for the historically designated consumer of each
logical segment.  It is not producer ownership: segments `17`--`19` can also
be read inside LCA evaluation.  The `21 ↦ canonicalClose` row is likewise
only the compat primary-consumer label: segment `21` (the fringe chunk
table) is also read by the select and rank legs, whose chunked in-word
folds route every chunk decode through the same table.  The load-bearing
operational relation is `ReviewerProducerReadPath` in `SuccinctFinalRAM`.
-/
def concreteBPNativeSuccinctRMQReviewerSegmentLeaf? :
    Nat -> Option ReviewerReadLeaf
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
      15 | 16 => some .selectClose
  | 17 | 18 | 19 => some .rankClose
  | 20 | 21 => some .canonicalClose
  | 22 => some .selectClose
  | _ + 23 => none

/-- A source is owned by a leaf exactly when a logical segment read by that
leaf resolves to the source in the canonical source map. -/
def ReviewerSource.OperationallyOwnedBy
    (source : ReviewerSource) (leaf : ReviewerReadLeaf) : Prop :=
  ∃ segment,
    concreteBPNativeSuccinctRMQReviewerSegmentSource? segment = some source ∧
    concreteBPNativeSuccinctRMQReviewerSegmentLeaf? segment = some leaf

/-- The evaluator leaves that deliberately share the single BP-code
physical source. -/
inductive ReviewerSharedBPConsumer where
  | selectClose
  | rankClose
  | canonicalClose
deriving DecidableEq

def ReviewerSharedBPConsumer.segment : ReviewerSharedBPConsumer -> Nat
  | .selectClose => 0
  | .rankClose => 19
  | .canonicalClose => 0

def ReviewerSharedBPConsumer.leaf :
    ReviewerSharedBPConsumer -> ReviewerReadLeaf
  | .selectClose => .selectClose
  | .rankClose => .rankClose
  | .canonicalClose => .canonicalClose

/-- Representative segment proving that the named read-producing leaf is part
of the operational segment universe.  Canonical close shares BP segment zero
for local decoding and has its own representative canonical segment 20. -/
def ReviewerSharedBPConsumer.leafSegment :
    ReviewerSharedBPConsumer -> Nat
  | .selectClose => 0
  | .rankClose => 19
  | .canonicalClose => 20

/--
Compatibility check against the two static maps.  This does not connect the
BP source and consumer through one event; `ReviewerSharedBPConsumer.ProducerConnected`
is the load-bearing same-event relation.
-/
def ReviewerSharedBPConsumer.Checked
    (consumer : ReviewerSharedBPConsumer) : Prop :=
  concreteBPNativeSuccinctRMQReviewerSegmentSource? consumer.segment =
      some .sharedBPCode ∧
    concreteBPNativeSuccinctRMQReviewerSegmentLeaf? consumer.leafSegment =
      some consumer.leaf

/-- All select, rank, and canonical-close BP-code dependencies are checked
against the source map and the operational leaf universe. -/
theorem concreteBPNativeSuccinctRMQReviewerSharedBPConsumer_all_checked
    (consumer : ReviewerSharedBPConsumer) : consumer.Checked := by
  cases consumer <;>
    simp [ReviewerSharedBPConsumer.Checked,
      ReviewerSharedBPConsumer.segment, ReviewerSharedBPConsumer.leaf,
      ReviewerSharedBPConsumer.leafSegment,
      concreteBPNativeSuccinctRMQReviewerSegmentSource?,
      concreteBPNativeSuccinctRMQReviewerSegmentLeaf?]

/-- Every constructor of the canonical live-source universe is listed. -/
theorem concreteBPNativeSuccinctRMQReviewerPhysicalSources_all
    (source : ReviewerSource) :
    source ∈ concreteBPNativeSuccinctRMQReviewerPhysicalSources := by
  cases source <;>
    simp [concreteBPNativeSuccinctRMQReviewerPhysicalSources]

/-- Canonical countedness is exactly membership in the exhaustive manifest. -/
def ReviewerSource.Counted (source : ReviewerSource) : Prop :=
  source ∈ concreteBPNativeSuccinctRMQReviewerPhysicalSources

/--
Compatibility category liveness retained for older clients.  It only joins
the static segment maps and is not reviewer evidence that an instruction
actually may read the source.  Use `ReviewerSource.HasProducerMayPath`.
-/
def ReviewerSource.Live (source : ReviewerSource) : Prop :=
  (source = .sharedBPCode ∧
      ∃ consumer : ReviewerSharedBPConsumer, consumer.Checked) ∨
    (source ≠ .sharedBPCode ∧
      ∃ leaf : ReviewerReadLeaf, source.OperationallyOwnedBy leaf)

theorem concreteBPNativeSuccinctRMQReviewerSource_operationally_live
    (source : ReviewerSource) : source.Live := by
  cases source with
  | sharedBPCode =>
      exact Or.inl ⟨rfl, .selectClose,
        concreteBPNativeSuccinctRMQReviewerSharedBPConsumer_all_checked
          .selectClose⟩
  | finalRankSuperFalse =>
      exact Or.inr ⟨by decide, .rankClose, 17, rfl, rfl⟩
  | finalRankBlockFalse =>
      exact Or.inr ⟨by decide, .rankClose, 18, rfl, rfl⟩
  | selectSuperBaseOccurrence =>
      exact Or.inr ⟨by decide, .selectClose, 1, rfl, rfl⟩
  | selectSuperBaseWordIndex =>
      exact Or.inr ⟨by decide, .selectClose, 2, rfl, rfl⟩
  | selectSuperRankBefore =>
      exact Or.inr ⟨by decide, .selectClose, 3, rfl, rfl⟩
  | selectSuperFirstOffset =>
      exact Or.inr ⟨by decide, .selectClose, 4, rfl, rfl⟩
  | selectLocalBaseOccurrence =>
      exact Or.inr ⟨by decide, .selectClose, 5, rfl, rfl⟩
  | selectLocalBaseWordIndex =>
      exact Or.inr ⟨by decide, .selectClose, 6, rfl, rfl⟩
  | selectLocalRankBefore =>
      exact Or.inr ⟨by decide, .selectClose, 7, rfl, rfl⟩
  | selectLocalFirstOffset =>
      exact Or.inr ⟨by decide, .selectClose, 8, rfl, rfl⟩
  | selectLongFlagRankSuperTrue =>
      exact Or.inr ⟨by decide, .selectClose, 9, rfl, rfl⟩
  | selectLongFlagRankBlockTrue =>
      exact Or.inr ⟨by decide, .selectClose, 10, rfl, rfl⟩
  | selectLongFlagBits =>
      exact Or.inr ⟨by decide, .selectClose, 11, rfl, rfl⟩
  | selectLongRelative =>
      exact Or.inr ⟨by decide, .selectClose, 12, rfl, rfl⟩
  | selectSparseRankSuperTrue =>
      exact Or.inr ⟨by decide, .selectClose, 13, rfl, rfl⟩
  | selectSparseRankBlockTrue =>
      exact Or.inr ⟨by decide, .selectClose, 14, rfl, rfl⟩
  | selectSparseFlagBits =>
      exact Or.inr ⟨by decide, .selectClose, 15, rfl, rfl⟩
  | selectSparseRelative =>
      exact Or.inr ⟨by decide, .selectClose, 16, rfl, rfl⟩
  | canonicalClose =>
      exact Or.inr ⟨by decide, .canonicalClose, 20, rfl, rfl⟩
  | fringeChunkTable =>
      exact Or.inr ⟨by decide, .canonicalClose, 21, rfl, rfl⟩
  | selectChunkTable =>
      exact Or.inr ⟨by decide, .selectClose, 22, rfl, rfl⟩

/-- Compatibility theorem; not part of the load-bearing reviewer surface. -/
theorem concreteBPNativeSuccinctRMQReviewerSource_counted_iff_live
    (source : ReviewerSource) :
    source.Counted ↔ source.Live := by
  constructor
  · intro _
    exact concreteBPNativeSuccinctRMQReviewerSource_operationally_live source
  · intro _
    exact concreteBPNativeSuccinctRMQReviewerPhysicalSources_all source

theorem concreteBPNativeSuccinctRMQReviewerPhysicalSources_nodup :
    concreteBPNativeSuccinctRMQReviewerPhysicalSources.Nodup := by
  decide

theorem concreteBPNativeSuccinctRMQReviewerPhysicalSources_length :
    concreteBPNativeSuccinctRMQReviewerPhysicalSources.length = 22 := by
  rfl

/-- Named controller families that consume canonical reviewer sources. -/
inductive ReviewerConsumer where
  | selectClose
  | rankClose
  | canonicalClose
deriving DecidableEq

/-- Public controller name obtained from an operational evaluator leaf. -/
def ReviewerReadLeaf.consumer : ReviewerReadLeaf -> ReviewerConsumer
  | .selectClose => .selectClose
  | .rankClose => .rankClose
  | .canonicalClose => .canonicalClose

/--
Static source ownership by the closed whole-query controller.  BP code is
intentionally `none`: it is the explicitly shared source used by select-close,
rank-close, and local BP close decoding.
-/
def ReviewerSource.consumer? : ReviewerSource -> Option ReviewerConsumer
  | .sharedBPCode => none
  | .finalRankSuperFalse => some .rankClose
  | .finalRankBlockFalse => some .rankClose
  | .selectSuperBaseOccurrence => some .selectClose
  | .selectSuperBaseWordIndex => some .selectClose
  | .selectSuperRankBefore => some .selectClose
  | .selectSuperFirstOffset => some .selectClose
  | .selectLocalBaseOccurrence => some .selectClose
  | .selectLocalBaseWordIndex => some .selectClose
  | .selectLocalRankBefore => some .selectClose
  | .selectLocalFirstOffset => some .selectClose
  | .selectLongFlagRankSuperTrue => some .selectClose
  | .selectLongFlagRankBlockTrue => some .selectClose
  | .selectLongFlagBits => some .selectClose
  | .selectLongRelative => some .selectClose
  | .selectSparseRankSuperTrue => some .selectClose
  | .selectSparseRankBlockTrue => some .selectClose
  | .selectSparseFlagBits => some .selectClose
  | .selectSparseRelative => some .selectClose
  | .canonicalClose => some .canonicalClose
  | .fringeChunkTable => some .canonicalClose
  | .selectChunkTable => some .selectClose

/-- A consumer claim is accepted only with a segment-derived operational leaf
witness.  The compatibility `consumer?` label alone is not evidence. -/
def ReviewerSource.CheckedConsumerClaim
    (source : ReviewerSource) (consumer : ReviewerConsumer) : Prop :=
  ∃ leaf : ReviewerReadLeaf,
    source.OperationallyOwnedBy leaf ∧ leaf.consumer = consumer

/-- Every counted source has an operational connection.  The shared BP source
uses its separately checked dependency relation; all others name an evaluator
leaf reached through the segment map. -/
theorem concreteBPNativeSuccinctRMQReviewerSource_counted_operational_connection
    (source : ReviewerSource) (_hcounted : source.Counted) :
    (source = .sharedBPCode ∧
      ∃ consumer : ReviewerSharedBPConsumer, consumer.Checked) ∨
    (∃ leaf : ReviewerReadLeaf, source.OperationallyOwnedBy leaf) := by
  rcases concreteBPNativeSuccinctRMQReviewerSource_operationally_live source with
    hshared | howned
  · exact Or.inl hshared
  · exact Or.inr howned.2

/-- For a non-shared source, operational segment ownership determines the
compatibility consumer label. -/
theorem concreteBPNativeSuccinctRMQReviewerSource_operational_owner_consumer
    {source : ReviewerSource} {leaf : ReviewerReadLeaf}
    (hnotShared : source ≠ .sharedBPCode)
    (howned : source.OperationallyOwnedBy leaf) :
    source.consumer? = some leaf.consumer := by
  rcases howned with ⟨segment, hsource, hleaf⟩
  match segment with
  | 0 =>
      simp [concreteBPNativeSuccinctRMQReviewerSegmentSource?] at hsource
      exact (hnotShared hsource.symm).elim
  | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 |
      16 | 17 | 18 | 20 | 21 | 22 =>
      simp [concreteBPNativeSuccinctRMQReviewerSegmentSource?,
        concreteBPNativeSuccinctRMQReviewerSegmentLeaf?] at hsource hleaf
      subst source
      subst leaf
      rfl
  | 19 =>
      simp [concreteBPNativeSuccinctRMQReviewerSegmentSource?] at hsource
      exact (hnotShared hsource.symm).elim
  | _ + 23 =>
      simp [concreteBPNativeSuccinctRMQReviewerSegmentSource?] at hsource

/-- A forged compatibility label is rejected because it cannot carry the
segment-derived operational ownership witness. -/
theorem concreteBPNativeSuccinctRMQReviewerSource_forged_consumer_rejected
    (source : ReviewerSource) (actual forged : ReviewerConsumer)
    (hactual : source.consumer? = some actual)
    (hforged : forged ≠ actual) :
    ¬ source.CheckedConsumerClaim forged := by
  intro hclaim
  rcases hclaim with ⟨leaf, howned, hleafConsumer⟩
  have hnotShared : source ≠ .sharedBPCode := by
    intro hshared
    subst source
    simp [ReviewerSource.consumer?] at hactual
  have hderived :=
    concreteBPNativeSuccinctRMQReviewerSource_operational_owner_consumer
      hnotShared howned
  have hleafActual : leaf.consumer = actual := by
    exact Option.some.inj (hderived.symm.trans hactual)
  exact hforged (hleafConsumer.symm.trans hleafActual)

theorem concreteBPNativeSuccinctRMQReviewerSource_counted_consumer_or_sharedBP
    (source : ReviewerSource) (_hcounted : source.Counted) :
    source = .sharedBPCode ∨
      ∃ consumer, source.consumer? = some consumer := by
  cases source <;> simp [ReviewerSource.consumer?]

/-! ### Semantic manifest anti-vacuity mutations -/

/-- Completeness means that every operationally live source is listed. -/
def ReviewerSource.ManifestComplete (manifest : List ReviewerSource) : Prop :=
  ∀ source, source.Live → source ∈ manifest

/-- Candidate entries make an attempted dead-source addition expressible
without polluting the closed `ReviewerSource` universe. -/
inductive ReviewerSourceCandidate where
  | source (value : ReviewerSource)
  | dead
deriving DecidableEq

def ReviewerSourceCandidate.Live : ReviewerSourceCandidate -> Prop
  | ReviewerSourceCandidate.source value => ReviewerSource.Live value
  | ReviewerSourceCandidate.dead => False

def ReviewerSourceCandidate.ManifestSound
    (manifest : List ReviewerSourceCandidate) : Prop :=
  ∀ entry, entry ∈ manifest → entry.Live

/-- Deliberately vacuous liveness mutant used by the acceptance challenge. -/
def ReviewerSourceCandidate.VacuousLive
    (_entry : ReviewerSourceCandidate) : Prop := True

/-- Deliberately circular enumeration mutant used by the acceptance challenge. -/
def ReviewerSourceCandidate.Enumerated
    (manifest : List ReviewerSourceCandidate)
    (entry : ReviewerSourceCandidate) : Prop := entry ∈ manifest

/-- Replacing operational liveness by `True` accepts the dead candidate. -/
theorem concreteBPNativeSuccinctRMQReviewerManifest_vacuousLive_accepts_dead :
    ReviewerSourceCandidate.VacuousLive .dead := by
  trivial

/-- Replacing liveness by enumeration membership also accepts the dead
candidate as soon as it is added. -/
theorem concreteBPNativeSuccinctRMQReviewerManifest_enumeration_accepts_dead
    (manifest : List ReviewerSourceCandidate) :
    ReviewerSourceCandidate.Enumerated (.dead :: manifest) .dead := by
  simp [ReviewerSourceCandidate.Enumerated]

/-- Replacing reviewer liveness by `False` cannot satisfy counted/live
equivalence even for the shared BP-code source. -/
theorem concreteBPNativeSuccinctRMQReviewerManifest_falseLive_rejected :
    ¬ (∀ source : ReviewerSource, source.Counted ↔ False) := by
  intro hfalse
  exact (hfalse .sharedBPCode).1
    (concreteBPNativeSuccinctRMQReviewerPhysicalSources_all .sharedBPCode)

/-- Anti-vacuity mutation: adjoining a dead candidate falsifies manifest
soundness immediately. -/
theorem concreteBPNativeSuccinctRMQReviewerManifest_add_dead_rejected
    (manifest : List ReviewerSourceCandidate) :
    ¬ ReviewerSourceCandidate.ManifestSound (.dead :: manifest) := by
  intro hsound
  exact hsound .dead (by simp)

def concreteBPNativeSuccinctRMQReviewerManifestWithout
    (removed : ReviewerSource) : List ReviewerSource :=
  concreteBPNativeSuccinctRMQReviewerPhysicalSources.filter
    (fun source => source ≠ removed)

/-- Anti-vacuity mutation: removing any used source falsifies operational
completeness. -/
theorem concreteBPNativeSuccinctRMQReviewerManifest_remove_used_rejected
    (removed : ReviewerSource) :
    ¬ ReviewerSource.ManifestComplete
      (concreteBPNativeSuccinctRMQReviewerManifestWithout removed) := by
  intro hcomplete
  have hmem := hcomplete removed
    (concreteBPNativeSuccinctRMQReviewerSource_operationally_live removed)
  simp [concreteBPNativeSuccinctRMQReviewerManifestWithout] at hmem

/-- Compatibility classification on the old, non-canonical source universe. -/
def ConcreteBPNativeSuccinctRMQFlatPayloadSource.LegacyCloseOrInterior :
    ConcreteBPNativeSuccinctRMQFlatPayloadSource -> Prop
  | .closeSummaryBaseline | .closeSummaryMinRel | .closeSummaryMaxRel |
      .closeSummaryArgOffset | .closeInteriorLocal | .closeInteriorGlobal |
      .closeFiniteSmallInteriorMin | .closeFiniteSmallInteriorArg |
      .closeFiniteSmallSameBlock => True
  | _ => False

/--
Bridge for the outer sources retained from the older source vocabulary.
Canonical close deliberately has no legacy-source image: it is one new
concatenated live component, not any of the duplicate legacy close tables.
-/
def ReviewerSource.legacyOuterSource? : ReviewerSource ->
    Option ConcreteBPNativeSuccinctRMQFlatPayloadSource
  | .sharedBPCode => some .finalRankBPCodeAlias
  | .finalRankSuperFalse => some .finalRankSuperFalse
  | .finalRankBlockFalse => some .finalRankBlockFalse
  | .selectSuperBaseOccurrence => some .selectSuperBaseOccurrence
  | .selectSuperBaseWordIndex => some .selectSuperBaseWordIndex
  | .selectSuperRankBefore => some .selectSuperRankBefore
  | .selectSuperFirstOffset => some .selectSuperFirstOffset
  | .selectLocalBaseOccurrence => some .selectLocalBaseOccurrence
  | .selectLocalBaseWordIndex => some .selectLocalBaseWordIndex
  | .selectLocalRankBefore => some .selectLocalRankBefore
  | .selectLocalFirstOffset => some .selectLocalFirstOffset
  | .selectLongFlagRankSuperTrue => some .selectLongFlagRankSuperTrue
  | .selectLongFlagRankBlockTrue => some .selectLongFlagRankBlockTrue
  | .selectLongFlagBits => some .selectLongFlagBits
  | .selectLongRelative => some .selectLongRelative
  | .selectSparseRankSuperTrue => some .selectSparseRankSuperTrue
  | .selectSparseRankBlockTrue => some .selectSparseRankBlockTrue
  | .selectSparseFlagBits => some .selectSparseFlagBits
  | .selectSparseRelative => some .selectSparseRelative
  | .canonicalClose => none
  | .fringeChunkTable => none
  | .selectChunkTable => none

theorem concreteBPNativeSuccinctRMQReviewerSource_legacyBridge_excludes_close
    (source : ReviewerSource)
    (legacy : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
    (hbridge : source.legacyOuterSource? = some legacy) :
    ¬ legacy.LegacyCloseOrInterior := by
  cases source <;> simp [ReviewerSource.legacyOuterSource?,
    ConcreteBPNativeSuccinctRMQFlatPayloadSource.LegacyCloseOrInterior]
      at hbridge ⊢
  all_goals subst legacy <;>
    simp

theorem concreteBPNativeSuccinctRMQReviewerPhysicalSources_exclude_legacy_close
    (source : ReviewerSource)
    (_hsource : source ∈ concreteBPNativeSuccinctRMQReviewerPhysicalSources)
    (legacy : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
    (hbridge : source.legacyOuterSource? = some legacy) :
    ¬ legacy.LegacyCloseOrInterior :=
  concreteBPNativeSuccinctRMQReviewerSource_legacyBridge_excludes_close
    source legacy hbridge

def concreteBPNativeSuccinctRMQReviewerSourceWords
    (shape : Cartesian.CartesianShape) (source : ReviewerSource) :
    List (List Bool) :=
  let selectData := GenericSelect.sparseExceptionSelectData shape.bpCode false
  let rankData := builtRelativeSplitBPCloseRankData shape
  match source with
  | .sharedBPCode => rankData.bitWords.store.words.toList
  | .finalRankSuperFalse =>
      rankData.superTables.falseTable.store.words.toList
  | .finalRankBlockFalse =>
      rankData.blockTables.falseTable.store.words.toList
  | .selectSuperBaseOccurrence =>
      selectData.superTable.baseOccurrenceTable.store.words.toList
  | .selectSuperBaseWordIndex =>
      selectData.superTable.baseWordIndexTable.store.words.toList
  | .selectSuperRankBefore =>
      selectData.superTable.rankBeforeTable.store.words.toList
  | .selectSuperFirstOffset =>
      selectData.superTable.firstOffsetTable.store.words.toList
  | .selectLocalBaseOccurrence =>
      selectData.localTable.baseOccurrenceTable.store.words.toList
  | .selectLocalBaseWordIndex =>
      selectData.localTable.baseWordIndexTable.store.words.toList
  | .selectLocalRankBefore =>
      selectData.localTable.rankBeforeTable.store.words.toList
  | .selectLocalFirstOffset =>
      selectData.localTable.firstOffsetTable.store.words.toList
  | .selectLongFlagRankSuperTrue =>
      selectData.longFlagRankData.superTables.trueTable.store.words.toList
  | .selectLongFlagRankBlockTrue =>
      selectData.longFlagRankData.blockTables.trueTable.store.words.toList
  | .selectLongFlagBits =>
      selectData.longFlagRankData.bitWords.store.words.toList
  | .selectLongRelative =>
      selectData.longSuperRelativeTable.store.words.toList
  | .selectSparseRankSuperTrue =>
      selectData.sparseDirectory.rankData.superTables.trueTable.store.words.toList
  | .selectSparseRankBlockTrue =>
      selectData.sparseDirectory.rankData.blockTables.trueTable.store.words.toList
  | .selectSparseFlagBits =>
      selectData.sparseDirectory.rankData.bitWords.store.words.toList
  | .selectSparseRelative =>
      selectData.sparseDirectory.relativeTable.store.words.toList
  | .canonicalClose =>
      (SuccinctClose.canonicalRelativeRmmInteriorComponentStore
        shape).store.words.toList
  | .fringeChunkTable =>
      (SuccinctClose.bpFringeChunkTable
        (SuccinctClose.bpFringeChunkBits
          shape.bpCode.length)).store.words.toList
  | .selectChunkTable =>
      (SuccinctClose.bpChunkSelectTable
        (SuccinctClose.bpFringeChunkBits
          shape.bpCode.length) false).store.words.toList

def concreteBPNativeSuccinctRMQReviewerSourcePayload
    (shape : Cartesian.CartesianShape) (source : ReviewerSource) : List Bool :=
  let selectData := GenericSelect.sparseExceptionSelectData shape.bpCode false
  let rankData := builtRelativeSplitBPCloseRankData shape
  match source with
  | .sharedBPCode => shape.bpCode
  | .finalRankSuperFalse => rankData.superTables.falseTable.payload
  | .finalRankBlockFalse => rankData.blockTables.falseTable.payload
  | .selectSuperBaseOccurrence =>
      selectData.superTable.baseOccurrenceTable.payload
  | .selectSuperBaseWordIndex =>
      selectData.superTable.baseWordIndexTable.payload
  | .selectSuperRankBefore => selectData.superTable.rankBeforeTable.payload
  | .selectSuperFirstOffset => selectData.superTable.firstOffsetTable.payload
  | .selectLocalBaseOccurrence =>
      selectData.localTable.baseOccurrenceTable.payload
  | .selectLocalBaseWordIndex =>
      selectData.localTable.baseWordIndexTable.payload
  | .selectLocalRankBefore => selectData.localTable.rankBeforeTable.payload
  | .selectLocalFirstOffset => selectData.localTable.firstOffsetTable.payload
  | .selectLongFlagRankSuperTrue =>
      selectData.longFlagRankData.superTables.trueTable.payload
  | .selectLongFlagRankBlockTrue =>
      selectData.longFlagRankData.blockTables.trueTable.payload
  | .selectLongFlagBits => selectData.longFlagBits
  | .selectLongRelative => selectData.longSuperRelativeTable.payload
  | .selectSparseRankSuperTrue =>
      selectData.sparseDirectory.rankData.superTables.trueTable.payload
  | .selectSparseRankBlockTrue =>
      selectData.sparseDirectory.rankData.blockTables.trueTable.payload
  | .selectSparseFlagBits => selectData.sparseDirectory.flagBits
  | .selectSparseRelative => selectData.sparseDirectory.relativeTable.payload
  | .canonicalClose =>
      (SuccinctClose.canonicalRelativeRmmInteriorDirectory shape).payload
  | .fringeChunkTable =>
      (SuccinctClose.bpFringeChunkTable
        (SuccinctClose.bpFringeChunkBits shape.bpCode.length)).payload
  | .selectChunkTable =>
      (SuccinctClose.bpChunkSelectTable
        (SuccinctClose.bpFringeChunkBits shape.bpCode.length) false).payload

def concreteBPNativeSuccinctRMQReviewerCloseWords
    (shape : Cartesian.CartesianShape) : List (List Bool) :=
  concreteBPNativeSuccinctRMQReviewerSourceWords shape .canonicalClose

/-- Physical regions are exactly the exhaustive typed live-source universe. -/
def concreteBPNativeSuccinctRMQReviewerPhysicalRegions
    (shape : Cartesian.CartesianShape) : List (List (List Bool)) :=
  concreteBPNativeSuccinctRMQReviewerPhysicalSources.map
    (concreteBPNativeSuccinctRMQReviewerSourceWords shape)

/-- One pre-execution physical machine-word list. -/
def concreteBPNativeSuccinctRMQReviewerPhysicalWords
    (shape : Cartesian.CartesianShape) : List (List Bool) :=
  (concreteBPNativeSuccinctRMQReviewerPhysicalRegions shape).flatten

/-- Bit erasure of the unique live-source manifest. -/
def concreteBPNativeSuccinctRMQReviewerLivePayload
    (shape : Cartesian.CartesianShape) : List Bool :=
  concreteBPNativeSuccinctRMQReviewerPhysicalSources.flatMap
    (concreteBPNativeSuccinctRMQReviewerSourcePayload shape)

theorem concreteBPNativeSuccinctRMQReviewerSourceWords_erases
    (shape : Cartesian.CartesianShape) (source : ReviewerSource) :
    flattenPayloadWords
        (concreteBPNativeSuccinctRMQReviewerSourceWords shape source) =
      concreteBPNativeSuccinctRMQReviewerSourcePayload shape source := by
  cases source with
  | sharedBPCode =>
      simpa [concreteBPNativeSuccinctRMQReviewerSourceWords,
        concreteBPNativeSuccinctRMQReviewerSourcePayload] using
        (builtRelativeSplitBPCloseRankData shape).bitWords.erases
  | finalRankSuperFalse =>
      simpa [concreteBPNativeSuccinctRMQReviewerSourceWords,
        concreteBPNativeSuccinctRMQReviewerSourcePayload] using
        (builtRelativeSplitBPCloseRankData
          shape).superTables.falseTable.store.erases
  | finalRankBlockFalse =>
      simpa [concreteBPNativeSuccinctRMQReviewerSourceWords,
        concreteBPNativeSuccinctRMQReviewerSourcePayload] using
        (builtRelativeSplitBPCloseRankData
          shape).blockTables.falseTable.store.erases
  | selectSuperBaseOccurrence =>
      simpa [concreteBPNativeSuccinctRMQReviewerSourceWords,
        concreteBPNativeSuccinctRMQReviewerSourcePayload,
        GenericSelect.sparseExceptionSelectData] using
        (GenericSelect.superTable shape.bpCode false).baseOccurrenceTable.store.erases
  | selectSuperBaseWordIndex =>
      simpa [concreteBPNativeSuccinctRMQReviewerSourceWords,
        concreteBPNativeSuccinctRMQReviewerSourcePayload,
        GenericSelect.sparseExceptionSelectData] using
        (GenericSelect.superTable shape.bpCode false).baseWordIndexTable.store.erases
  | selectSuperRankBefore =>
      simpa [concreteBPNativeSuccinctRMQReviewerSourceWords,
        concreteBPNativeSuccinctRMQReviewerSourcePayload,
        GenericSelect.sparseExceptionSelectData] using
        (GenericSelect.superTable shape.bpCode false).rankBeforeTable.store.erases
  | selectSuperFirstOffset =>
      simpa [concreteBPNativeSuccinctRMQReviewerSourceWords,
        concreteBPNativeSuccinctRMQReviewerSourcePayload,
        GenericSelect.sparseExceptionSelectData] using
        (GenericSelect.superTable shape.bpCode false).firstOffsetTable.store.erases
  | selectLocalBaseOccurrence =>
      simpa [concreteBPNativeSuccinctRMQReviewerSourceWords,
        concreteBPNativeSuccinctRMQReviewerSourcePayload,
        GenericSelect.sparseExceptionSelectData] using
        (GenericSelect.localTable shape.bpCode false).baseOccurrenceTable.store.erases
  | selectLocalBaseWordIndex =>
      simpa [concreteBPNativeSuccinctRMQReviewerSourceWords,
        concreteBPNativeSuccinctRMQReviewerSourcePayload,
        GenericSelect.sparseExceptionSelectData] using
        (GenericSelect.localTable shape.bpCode false).baseWordIndexTable.store.erases
  | selectLocalRankBefore =>
      simpa [concreteBPNativeSuccinctRMQReviewerSourceWords,
        concreteBPNativeSuccinctRMQReviewerSourcePayload,
        GenericSelect.sparseExceptionSelectData] using
        (GenericSelect.localTable shape.bpCode false).rankBeforeTable.store.erases
  | selectLocalFirstOffset =>
      simpa [concreteBPNativeSuccinctRMQReviewerSourceWords,
        concreteBPNativeSuccinctRMQReviewerSourcePayload,
        GenericSelect.sparseExceptionSelectData] using
        (GenericSelect.localTable shape.bpCode false).firstOffsetTable.store.erases
  | selectLongFlagRankSuperTrue =>
      simpa [concreteBPNativeSuccinctRMQReviewerSourceWords,
        concreteBPNativeSuccinctRMQReviewerSourcePayload,
        GenericSelect.sparseExceptionSelectData] using
        (GenericSelect.longFlagRankData
          shape.bpCode false).superTables.trueTable.store.erases
  | selectLongFlagRankBlockTrue =>
      simpa [concreteBPNativeSuccinctRMQReviewerSourceWords,
        concreteBPNativeSuccinctRMQReviewerSourcePayload,
        GenericSelect.sparseExceptionSelectData] using
        (GenericSelect.longFlagRankData
          shape.bpCode false).blockTables.trueTable.store.erases
  | selectLongFlagBits =>
      simpa [concreteBPNativeSuccinctRMQReviewerSourceWords,
        concreteBPNativeSuccinctRMQReviewerSourcePayload,
        GenericSelect.sparseExceptionSelectData] using
        (GenericSelect.longFlagRankData shape.bpCode false).bitWords.erases
  | selectLongRelative =>
      simpa [concreteBPNativeSuccinctRMQReviewerSourceWords,
        concreteBPNativeSuccinctRMQReviewerSourcePayload,
        GenericSelect.sparseExceptionSelectData] using
        (GenericSelect.longSuperRelativeTable shape.bpCode false).store.erases
  | selectSparseRankSuperTrue =>
      simpa [concreteBPNativeSuccinctRMQReviewerSourceWords,
        concreteBPNativeSuccinctRMQReviewerSourcePayload,
        GenericSelect.sparseExceptionSelectData] using
        (GenericSelect.sparseExceptionDirectory
          shape.bpCode false).rankData.superTables.trueTable.store.erases
  | selectSparseRankBlockTrue =>
      simpa [concreteBPNativeSuccinctRMQReviewerSourceWords,
        concreteBPNativeSuccinctRMQReviewerSourcePayload,
        GenericSelect.sparseExceptionSelectData] using
        (GenericSelect.sparseExceptionDirectory
          shape.bpCode false).rankData.blockTables.trueTable.store.erases
  | selectSparseFlagBits =>
      simpa [concreteBPNativeSuccinctRMQReviewerSourceWords,
        concreteBPNativeSuccinctRMQReviewerSourcePayload,
        GenericSelect.sparseExceptionSelectData] using
        (GenericSelect.sparseExceptionDirectory
          shape.bpCode false).rankData.bitWords.erases
  | selectSparseRelative =>
      simpa [concreteBPNativeSuccinctRMQReviewerSourceWords,
        concreteBPNativeSuccinctRMQReviewerSourcePayload,
        GenericSelect.sparseExceptionSelectData] using
        (GenericSelect.sparseExceptionDirectory
          shape.bpCode false).relativeTable.store.erases
  | canonicalClose =>
      simpa [concreteBPNativeSuccinctRMQReviewerSourceWords,
        concreteBPNativeSuccinctRMQReviewerSourcePayload,
        SuccinctClose.canonicalRelativeRmmInteriorDirectory] using
        SuccinctClose.canonicalRelativeRmmInteriorComponentStore_flattens_payload
          shape
  | fringeChunkTable =>
      simpa [concreteBPNativeSuccinctRMQReviewerSourceWords,
        concreteBPNativeSuccinctRMQReviewerSourcePayload] using
        SuccinctClose.bpFringeChunkTable_store_erases
          (SuccinctClose.bpFringeChunkBits shape.bpCode.length)
  | selectChunkTable =>
      simpa [concreteBPNativeSuccinctRMQReviewerSourceWords,
        concreteBPNativeSuccinctRMQReviewerSourcePayload] using
        SuccinctClose.bpChunkSelectTable_store_erases
          (SuccinctClose.bpFringeChunkBits shape.bpCode.length) false

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
            (concreteBPNativeSuccinctRMQReviewerSourceWords shape source) ++ _ =
          concreteBPNativeSuccinctRMQReviewerSourcePayload shape source ++ _
      rw [concreteBPNativeSuccinctRMQReviewerSourceWords_erases]
      exact congrArg
        (fun tail =>
          concreteBPNativeSuccinctRMQReviewerSourcePayload shape source ++ tail)
        ih

theorem concreteBPNativeSuccinctRMQReviewerPhysicalWords_components
    (shape : Cartesian.CartesianShape) :
    concreteBPNativeSuccinctRMQReviewerPhysicalWords shape =
      concreteBPNativeSuccinctRMQReviewerPhysicalSources.flatMap
        (concreteBPNativeSuccinctRMQReviewerSourceWords shape) := by
  have hmap :
      (concreteBPNativeSuccinctRMQReviewerPhysicalSources.map
        (concreteBPNativeSuccinctRMQReviewerSourceWords shape)).flatten =
      concreteBPNativeSuccinctRMQReviewerPhysicalSources.flatMap
        (concreteBPNativeSuccinctRMQReviewerSourceWords shape) := by
    induction concreteBPNativeSuccinctRMQReviewerPhysicalSources with
    | nil => rfl
    | cons source sources ih => simp [ih]
  simpa [concreteBPNativeSuccinctRMQReviewerPhysicalWords,
    concreteBPNativeSuccinctRMQReviewerPhysicalRegions] using hmap

theorem concreteBPNativeSuccinctRMQReviewerPhysicalWords_erases_live
    (shape : Cartesian.CartesianShape) :
    flattenPayloadWords
        (concreteBPNativeSuccinctRMQReviewerPhysicalWords shape) =
      concreteBPNativeSuccinctRMQReviewerLivePayload shape := by
  rw [concreteBPNativeSuccinctRMQReviewerPhysicalWords_components,
    reviewerSources_erases]
  rfl

/-- The manifest payload is literally the canonical public payload. -/
theorem concreteBPNativeSuccinctRMQReviewerLivePayload_eq_public
    (shape : Cartesian.CartesianShape) :
    concreteBPNativeSuccinctRMQReviewerLivePayload shape =
      concreteBPNativeSuccinctRMQCanonicalReviewerPayload shape := by
  simp [concreteBPNativeSuccinctRMQReviewerLivePayload,
    concreteBPNativeSuccinctRMQReviewerPhysicalSources,
    concreteBPNativeSuccinctRMQReviewerSourcePayload,
    concreteBPNativeSuccinctRMQCanonicalReviewerPayload,
    concreteBPNativeSuccinctRMQCanonicalReviewerPayloadLayout,
    concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessPayload,
    concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources,
    concreteBPNativeSuccinctRMQFlatPayloadSourcePayload, List.append_assoc]

/-- The physical erasure is literally the canonical public payload. -/
theorem concreteBPNativeSuccinctRMQReviewerPhysicalWords_erases
    (shape : Cartesian.CartesianShape) :
    flattenPayloadWords
        (concreteBPNativeSuccinctRMQReviewerPhysicalWords shape) =
      concreteBPNativeSuccinctRMQCanonicalReviewerPayload shape := by
  rw [concreteBPNativeSuccinctRMQReviewerPhysicalWords_erases_live,
    concreteBPNativeSuccinctRMQReviewerLivePayload_eq_public]

/-! ### Logical segment map and guarded address translation -/

/-- The unique physical region occupied by a canonical live source. -/
def ReviewerSource.region : ReviewerSource -> Nat
  | .sharedBPCode => 0
  | .finalRankSuperFalse => 1
  | .finalRankBlockFalse => 2
  | .selectSuperBaseOccurrence => 3
  | .selectSuperBaseWordIndex => 4
  | .selectSuperRankBefore => 5
  | .selectSuperFirstOffset => 6
  | .selectLocalBaseOccurrence => 7
  | .selectLocalBaseWordIndex => 8
  | .selectLocalRankBefore => 9
  | .selectLocalFirstOffset => 10
  | .selectLongFlagRankSuperTrue => 11
  | .selectLongFlagRankBlockTrue => 12
  | .selectLongFlagBits => 13
  | .selectLongRelative => 14
  | .selectSparseRankSuperTrue => 15
  | .selectSparseRankBlockTrue => 16
  | .selectSparseFlagBits => 17
  | .selectSparseRelative => 18
  | .canonicalClose => 19
  | .fringeChunkTable => 20
  | .selectChunkTable => 21

theorem concreteBPNativeSuccinctRMQReviewerSource_region_injective
    {source other : ReviewerSource}
    (h : source.region = other.region) : source = other := by
  cases source <;> cases other <;>
    simp [ReviewerSource.region] at h ⊢

theorem concreteBPNativeSuccinctRMQReviewerSource_region_eq_iff
    (source other : ReviewerSource) :
    source.region = other.region ↔ source = other := by
  constructor
  · exact concreteBPNativeSuccinctRMQReviewerSource_region_injective
  · intro h
    cases h
    rfl

theorem concreteBPNativeSuccinctRMQReviewerPhysicalRegions_source_get
    (shape : Cartesian.CartesianShape) (source : ReviewerSource) :
    (concreteBPNativeSuccinctRMQReviewerPhysicalRegions shape)[source.region]? =
      some (concreteBPNativeSuccinctRMQReviewerSourceWords shape source) := by
  cases source <;>
    rfl

def concreteBPNativeSuccinctRMQReviewerSegmentRegion? (segment : Nat) :
    Option Nat :=
  (concreteBPNativeSuccinctRMQReviewerSegmentSource? segment).map
    ReviewerSource.region

theorem concreteBPNativeSuccinctRMQReviewerSegmentSource?_coverage
    (segment : Nat) :
    (∃ source,
      concreteBPNativeSuccinctRMQReviewerSegmentSource? segment = some source) ↔
      segment < 23 := by
  match segment with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
      15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 =>
      simp [concreteBPNativeSuccinctRMQReviewerSegmentSource?]
  | _ + 23 =>
      simp [concreteBPNativeSuccinctRMQReviewerSegmentSource?]

/-- The operational leaf map covers exactly the live logical segments. -/
theorem concreteBPNativeSuccinctRMQReviewerSegmentLeaf?_coverage
    (segment : Nat) :
    (∃ leaf,
      concreteBPNativeSuccinctRMQReviewerSegmentLeaf? segment = some leaf) ↔
      segment < 23 := by
  match segment with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
      15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 =>
      simp [concreteBPNativeSuccinctRMQReviewerSegmentLeaf?]
  | _ + 23 =>
      simp [concreteBPNativeSuccinctRMQReviewerSegmentLeaf?]

theorem concreteBPNativeSuccinctRMQReviewerSegmentRegion?_coverage
    (segment : Nat) :
    (∃ region,
      concreteBPNativeSuccinctRMQReviewerSegmentRegion? segment = some region) ↔
      segment < 23 := by
  match segment with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
      15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 =>
      simp [concreteBPNativeSuccinctRMQReviewerSegmentRegion?,
        concreteBPNativeSuccinctRMQReviewerSegmentSource?, ReviewerSource.region]
  | _ + 23 =>
      simp [concreteBPNativeSuccinctRMQReviewerSegmentRegion?,
        concreteBPNativeSuccinctRMQReviewerSegmentSource?]

theorem concreteBPNativeSuccinctRMQReviewerSegmentRegion?_dead
    (segment : Nat) (hsegment : 23 <= segment) :
    concreteBPNativeSuccinctRMQReviewerSegmentRegion? segment = none := by
  match segment with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
      15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 => omega
  | _ + 23 =>
      rfl

theorem concreteBPNativeSuccinctRMQReviewerSegmentSource_counted
    {segment : Nat} {source : ReviewerSource}
    (_hsource :
      concreteBPNativeSuccinctRMQReviewerSegmentSource? segment = some source) :
    source.Counted := by
  exact concreteBPNativeSuccinctRMQReviewerPhysicalSources_all source

/-- All legacy tail segments are inaccessible from the canonical read store. -/
theorem concreteBPNativeSuccinctRMQCanonicalReviewerReadStore_legacyTail_none
    (shape : Cartesian.CartesianShape) (segment index : Nat)
    (hsegment : 23 <= segment) :
    (concreteBPNativeSuccinctRMQCanonicalReviewerReadStore shape).readWord?
        segment index = none := by
  match segment with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
      15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 => omega
  | n + 23 =>
      have hnot20 : ¬ n + 23 < 20 := by omega
      have hnotFringe : ¬ (n + 23 = 21) := by omega
      have hnotSelect : ¬ (n + 23 = 22) := by omega
      simp [concreteBPNativeSuccinctRMQCanonicalReviewerReadStore,
        concreteBPNativeInteriorTraceSegments,
        concreteBPNativeFringeChunkTraceSegment,
        concreteBPNativeSelectChunkTraceSegment, hnot20, hnotFringe,
        hnotSelect]

def concreteBPNativeSuccinctRMQReviewerSegmentWords
    (shape : Cartesian.CartesianShape) (segment : Nat) : List (List Bool) :=
  if segment = 0 then
    SuccinctSpace.chunkPayloadWords
      (SuccinctRank.machineWordBits shape.bpCode.length) shape.bpCode
  else
    match concreteBPNativeSuccinctRMQReviewerSegmentSource? segment with
    | some source => concreteBPNativeSuccinctRMQReviewerSourceWords shape source
    | none => []

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
    (hsegment : 23 <= segment) :
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
  | 21 => omega
  | 22 => omega
  | _ + 23 => rfl

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
  unfold concreteBPNativeSuccinctRMQReviewerSegmentRegion? at hregion
  cases hsource :
      concreteBPNativeSuccinctRMQReviewerSegmentSource? segment with
  | none => simp [hsource] at hregion
  | some source =>
      simp [hsource] at hregion
      subst region
      rw [concreteBPNativeSuccinctRMQReviewerPhysicalRegions_source_get]
      congr 1
      simp [concreteBPNativeSuccinctRMQReviewerSegmentWords, hsegment, hsource]

/-- Segment 0 is exactly the ordinary-chunk prefix of the sentinel BP region. -/
theorem concreteBPNativeSuccinctRMQReviewerBP_prefix
    (shape : Cartesian.CartesianShape) :
    (concreteBPNativeSuccinctRMQReviewerSourceWords
        shape .sharedBPCode).take
        (concreteBPNativeSuccinctRMQReviewerSegmentWords shape 0).length =
      concreteBPNativeSuccinctRMQReviewerSegmentWords shape 0 := by
  simp [concreteBPNativeSuccinctRMQReviewerSourceWords,
    concreteBPNativeSuccinctRMQReviewerSegmentWords,
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
    have hregionZero : region = 0 := by
      simpa [concreteBPNativeSuccinctRMQReviewerSegmentRegion?,
        concreteBPNativeSuccinctRMQReviewerSegmentSource?,
        ReviewerSource.region] using hregion.symm
    subst region
    have hle :
        (concreteBPNativeSuccinctRMQReviewerSegmentWords shape 0).length <=
          (concreteBPNativeSuccinctRMQReviewerSourceWords
            shape .sharedBPCode).length := by
      simp [concreteBPNativeSuccinctRMQReviewerSourceWords,
        concreteBPNativeSuccinctRMQReviewerSegmentWords,
        builtRelativeSplitBPCloseRankData,
        builtRelativeSplitBPCloseRankWordSize,
        SuccinctRank.canonicalTwoLevelRankDataOfChunksExactLocalBlock,
        SuccinctRank.canonicalTwoLevelRankDataOfBridgeLocalBlock,
        SuccinctRank.canonicalRankWordBridgeOfChunksWithSentinel,
        SuccinctSpace.BoundedPayloadWordStore.ofChunksWithSentinel]
    change
      (concreteBPNativeSuccinctRMQReviewerPhysicalWords shape).take
          (concreteBPNativeSuccinctRMQReviewerSegmentWords shape 0).length =
        concreteBPNativeSuccinctRMQReviewerSegmentWords shape 0
    rw [concreteBPNativeSuccinctRMQReviewerPhysicalWords_components]
    simp only [concreteBPNativeSuccinctRMQReviewerPhysicalSources,
      List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [List.take_append_of_le_length hle]
    exact concreteBPNativeSuccinctRMQReviewerBP_prefix shape
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
  match segment with
  | 0 =>
      rw [concreteBPNativeSuccinctRMQGlobalReadStore_bpCode]
      simp [concreteBPNativeSuccinctRMQReviewerSegmentWords]
  | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
      15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 =>
      simp [concreteBPNativeSuccinctRMQGlobalReadStore,
        concreteBPNativeSuccinctRMQReviewerSegmentWords,
        concreteBPNativeSuccinctRMQReviewerSegmentSource?,
        concreteBPNativeSuccinctRMQReviewerSourceWords,
        SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.rankRegisterWordRAMStore,
        SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.superSampleWords,
        SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.blockSampleWords,
        SuccinctSpace.FixedWidthNatTable.wordRAMStore,
        SuccinctSpace.PayloadWordStore.wordRAMStore,
        WordRAM.Store.readWord?, Array.getElem?_toList]
  | _ + 23 =>
      simp [concreteBPNativeSuccinctRMQGlobalReadStore,
        concreteBPNativeSuccinctRMQReviewerSegmentWords,
        concreteBPNativeSuccinctRMQReviewerSegmentSource?]

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
        | 0 => simp [concreteBPNativeSuccinctRMQReviewerSegmentRegion?,
            concreteBPNativeSuccinctRMQReviewerSegmentSource?] at hregion
        | 1 => simp [concreteBPNativeSuccinctRMQReviewerSegmentRegion?,
            concreteBPNativeSuccinctRMQReviewerSegmentSource?] at hregion
        | 2 => simp [concreteBPNativeSuccinctRMQReviewerSegmentRegion?,
            concreteBPNativeSuccinctRMQReviewerSegmentSource?] at hregion
        | 3 => simp [concreteBPNativeSuccinctRMQReviewerSegmentRegion?,
            concreteBPNativeSuccinctRMQReviewerSegmentSource?] at hregion
        | 4 => simp [concreteBPNativeSuccinctRMQReviewerSegmentRegion?,
            concreteBPNativeSuccinctRMQReviewerSegmentSource?] at hregion
        | 5 => simp [concreteBPNativeSuccinctRMQReviewerSegmentRegion?,
            concreteBPNativeSuccinctRMQReviewerSegmentSource?] at hregion
        | 6 => simp [concreteBPNativeSuccinctRMQReviewerSegmentRegion?,
            concreteBPNativeSuccinctRMQReviewerSegmentSource?] at hregion
        | 7 => simp [concreteBPNativeSuccinctRMQReviewerSegmentRegion?,
            concreteBPNativeSuccinctRMQReviewerSegmentSource?] at hregion
        | 8 => simp [concreteBPNativeSuccinctRMQReviewerSegmentRegion?,
            concreteBPNativeSuccinctRMQReviewerSegmentSource?] at hregion
        | 9 => simp [concreteBPNativeSuccinctRMQReviewerSegmentRegion?,
            concreteBPNativeSuccinctRMQReviewerSegmentSource?] at hregion
        | 10 => simp [concreteBPNativeSuccinctRMQReviewerSegmentRegion?,
            concreteBPNativeSuccinctRMQReviewerSegmentSource?] at hregion
        | 11 => simp [concreteBPNativeSuccinctRMQReviewerSegmentRegion?,
            concreteBPNativeSuccinctRMQReviewerSegmentSource?] at hregion
        | 12 => simp [concreteBPNativeSuccinctRMQReviewerSegmentRegion?,
            concreteBPNativeSuccinctRMQReviewerSegmentSource?] at hregion
        | 13 => simp [concreteBPNativeSuccinctRMQReviewerSegmentRegion?,
            concreteBPNativeSuccinctRMQReviewerSegmentSource?] at hregion
        | 14 => simp [concreteBPNativeSuccinctRMQReviewerSegmentRegion?,
            concreteBPNativeSuccinctRMQReviewerSegmentSource?] at hregion
        | 15 => simp [concreteBPNativeSuccinctRMQReviewerSegmentRegion?,
            concreteBPNativeSuccinctRMQReviewerSegmentSource?] at hregion
        | 16 => simp [concreteBPNativeSuccinctRMQReviewerSegmentRegion?,
            concreteBPNativeSuccinctRMQReviewerSegmentSource?] at hregion
        | 17 => simp [concreteBPNativeSuccinctRMQReviewerSegmentRegion?,
            concreteBPNativeSuccinctRMQReviewerSegmentSource?] at hregion
        | 18 => simp [concreteBPNativeSuccinctRMQReviewerSegmentRegion?,
            concreteBPNativeSuccinctRMQReviewerSegmentSource?] at hregion
        | 19 => simp [concreteBPNativeSuccinctRMQReviewerSegmentRegion?,
            concreteBPNativeSuccinctRMQReviewerSegmentSource?] at hregion
        | 20 => simp [concreteBPNativeSuccinctRMQReviewerSegmentRegion?,
            concreteBPNativeSuccinctRMQReviewerSegmentSource?] at hregion
        | 21 => simp [concreteBPNativeSuccinctRMQReviewerSegmentRegion?,
            concreteBPNativeSuccinctRMQReviewerSegmentSource?] at hregion
        | 22 => simp [concreteBPNativeSuccinctRMQReviewerSegmentRegion?,
            concreteBPNativeSuccinctRMQReviewerSegmentSource?] at hregion
        | n + 23 =>
            simp [concreteBPNativeSuccinctRMQReviewerSegmentWords,
              concreteBPNativeSuccinctRMQReviewerSegmentSource?]
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
      shape .sharedBPCode).length <= 2 * shape.bpCode.length + 1 := by
  have hchunks := chunkPayloadWords_length_le_payload_length
    (SuccinctRank.machineWordBits_pos shape.bpCode.length) shape.bpCode
  simp [concreteBPNativeSuccinctRMQReviewerSourceWords,
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
  let localLevel :=
    SuccinctClose.canonicalRelativeRmmInteriorLocalLevelTable shape
  let globalLevel :=
    SuccinctClose.canonicalRelativeRmmInteriorGlobalLevelTable shape
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
  have hlocalLevel := fixedWidthNatTable_machineWords_length_le_payload_length
    localLevel.table hword
  have hglobalLevel := fixedWidthNatTable_machineWords_length_le_payload_length
    globalLevel.table hword
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
                (global.table.machineStore hword).store.words.toList ++
                  (localLevel.table.machineStore hword).store.words.toList ++
                    (globalLevel.table.machineStore hword).store.words.toList by
      simpa [summary, localTable, global, localLevel, globalLevel, hword] using
        SuccinctClose.canonicalRelativeRmmInteriorComponentStore_words_toList
          shape]
  simp only [List.length_append, Array.length_toList]
  simp [SuccinctClose.canonicalRelativeRmmInteriorDirectory,
    SuccinctSpace.FixedWidthNatTable.machineStore,
    SuccinctClose.PayloadLiveBPRelativeMinMaxArgSummaryTable.payload,
    SuccinctClose.PayloadLiveBPLocalSparseOffsetTable.payload,
    SuccinctClose.PayloadLiveBPGlobalSparseBlockTable.payload,
    SuccinctClose.PayloadLiveBPSparseLevelTable.payload,
    summary, localTable, global, localLevel, globalLevel] at *
  omega

private theorem concreteBPNativeSuccinctRMQReviewerFringeWords_length_le
    (shape : Cartesian.CartesianShape) :
    (concreteBPNativeSuccinctRMQReviewerSourceWords
      shape .fringeChunkTable).length <= 64 * (shape.size + 1) := by
  have hrows :
      (concreteBPNativeSuccinctRMQReviewerSourceWords
        shape .fringeChunkTable).length =
        SuccinctClose.bpFringeChunkRowCount
          (SuccinctClose.bpFringeChunkBits shape.bpCode.length) := by
    simp [concreteBPNativeSuccinctRMQReviewerSourceWords,
      SuccinctClose.bpFringeChunkTable,
      SuccinctSpace.FixedWidthNatTable.ofEntries,
      SuccinctSpace.FixedWidthNatTable.ofEncodedWords]
  rw [hrows, Cartesian.CartesianShape.bpCode_length]
  exact SuccinctClose.bpFringeChunkRowCount_le_linear shape.size

private theorem concreteBPNativeSuccinctRMQReviewerSelectChunkWords_length_le
    (shape : Cartesian.CartesianShape) :
    (concreteBPNativeSuccinctRMQReviewerSourceWords
      shape .selectChunkTable).length <= 16 * (shape.size + 1) := by
  have hrows :
      (concreteBPNativeSuccinctRMQReviewerSourceWords
        shape .selectChunkTable).length =
        SuccinctClose.bpChunkSelectRowCount
          (SuccinctClose.bpFringeChunkBits shape.bpCode.length) := by
    simp [concreteBPNativeSuccinctRMQReviewerSourceWords,
      SuccinctClose.bpChunkSelectTable,
      SuccinctSpace.FixedWidthNatTable.ofEntries,
      SuccinctSpace.FixedWidthNatTable.ofEncodedWords]
  rw [hrows, Cartesian.CartesianShape.bpCode_length]
  exact SuccinctClose.bpChunkSelectRowCount_le_linear shape.size

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
        527 * (shape.size + 1) := by
    omega
  have hcloseBound :
      (concreteBPNativeSuccinctRMQReviewerCloseWords shape).length <=
        527 * (shape.size + 1) :=
    Nat.le_trans hclose hdirLinear
  have hcanonicalCloseBound :
      (concreteBPNativeSuccinctRMQReviewerSourceWords
        shape .canonicalClose).length <= 527 * (shape.size + 1) := by
    simpa [concreteBPNativeSuccinctRMQReviewerCloseWords] using hcloseBound
  have hfringeBound :=
    concreteBPNativeSuccinctRMQReviewerFringeWords_length_le shape
  have hselectChunkBound :=
    concreteBPNativeSuccinctRMQReviewerSelectChunkWords_length_le shape
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
  rcases List.mem_flatMap.mp hmem with
    ⟨source, hsource, hsourceWord⟩
  simp [concreteBPNativeSuccinctRMQReviewerPhysicalSources] at hsource
  rcases hsource with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 |
    h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 |
    h21
  all_goals subst source
  · change List.Mem word
        (builtRelativeSplitBPCloseRankData
          shape).bitWords.store.words.toList at hsourceWord
    exact Nat.le_trans
      ((builtRelativeSplitBPCloseRankData
        shape).payload_word_length_le_machine hsourceWord)
      (concreteBPNativeSuccinctRMQReviewerMachineWordBits_le_wordBits shape)
  · change List.Mem word
        (builtRelativeSplitBPCloseRankData
          shape).superTables.falseTable.store.words.toList at hsourceWord
    apply GenericSelect.fixedWidthNatTable_word_length_le_of_mem
      (builtRelativeSplitBPCloseRankData shape).superTables.falseTable
      ?_ hsourceWord
    simpa [builtRelativeSplitBPCloseRankData,
      builtRelativeSplitBPCloseRankWordSize,
      SuccinctRank.canonicalTwoLevelRankDataOfChunksExactLocalBlock,
      SuccinctRank.canonicalTwoLevelRankDataOfBridgeLocalBlock] using
        concreteBPNativeSuccinctRMQReviewerMachineWordBits_le_wordBits shape
  · change List.Mem word
        (builtRelativeSplitBPCloseRankData
          shape).blockTables.falseTable.store.words.toList at hsourceWord
    apply GenericSelect.fixedWidthNatTable_word_length_le_of_mem
      (builtRelativeSplitBPCloseRankData shape).blockTables.falseTable
      ?_ hsourceWord
    simpa [builtRelativeSplitBPCloseRankData,
      SuccinctRank.canonicalTwoLevelRankDataOfChunksExactLocalBlock,
      SuccinctRank.canonicalTwoLevelRankDataOfBridgeLocalBlock] using
        concreteBPNativeSuccinctRMQReviewerFinalBlockWidth_le_wordBits shape
  · apply concreteBPNativeSuccinctRMQReviewerSelectSuperWord_length_le shape
    unfold GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable.readWords
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    exact hsourceWord
  · apply concreteBPNativeSuccinctRMQReviewerSelectSuperWord_length_le shape
    unfold GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable.readWords
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_right
    exact hsourceWord
  · apply concreteBPNativeSuccinctRMQReviewerSelectSuperWord_length_le shape
    unfold GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable.readWords
    apply List.mem_append_left
    apply List.mem_append_right
    exact hsourceWord
  · apply concreteBPNativeSuccinctRMQReviewerSelectSuperWord_length_le shape
    unfold GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable.readWords
    apply List.mem_append_right
    exact hsourceWord
  · apply concreteBPNativeSuccinctRMQReviewerSelectLocalWord_length_le shape
    unfold GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable.readWords
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    exact hsourceWord
  · apply concreteBPNativeSuccinctRMQReviewerSelectLocalWord_length_le shape
    unfold GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable.readWords
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_right
    exact hsourceWord
  · apply concreteBPNativeSuccinctRMQReviewerSelectLocalWord_length_le shape
    unfold GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable.readWords
    apply List.mem_append_left
    apply List.mem_append_right
    exact hsourceWord
  · apply concreteBPNativeSuccinctRMQReviewerSelectLocalWord_length_le shape
    unfold GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable.readWords
    apply List.mem_append_right
    exact hsourceWord
  · apply concreteBPNativeSuccinctRMQReviewerSelectLongRankWord_length_le shape
    unfold GenericSelect.SparseExceptionSelectData.longFlagRankReadWords
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    exact hsourceWord
  · apply concreteBPNativeSuccinctRMQReviewerSelectLongRankWord_length_le shape
    unfold GenericSelect.SparseExceptionSelectData.longFlagRankReadWords
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_right
    exact hsourceWord
  · apply concreteBPNativeSuccinctRMQReviewerSelectLongRankWord_length_le shape
    unfold GenericSelect.SparseExceptionSelectData.longFlagRankReadWords
    apply List.mem_append_right
    exact hsourceWord
  · exact
      concreteBPNativeSuccinctRMQReviewerSelectLongRelativeWord_length_le
        shape hsourceWord
  · apply concreteBPNativeSuccinctRMQReviewerSelectSparseWord_length_le shape
    unfold GenericSelect.SparseExceptionDirectory.readWords
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    exact hsourceWord
  · apply concreteBPNativeSuccinctRMQReviewerSelectSparseWord_length_le shape
    unfold GenericSelect.SparseExceptionDirectory.readWords
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_right
    exact hsourceWord
  · apply concreteBPNativeSuccinctRMQReviewerSelectSparseWord_length_le shape
    unfold GenericSelect.SparseExceptionDirectory.readWords
    apply List.mem_append_left
    apply List.mem_append_right
    exact hsourceWord
  · apply concreteBPNativeSuccinctRMQReviewerSelectSparseWord_length_le shape
    unfold GenericSelect.SparseExceptionDirectory.readWords
    apply List.mem_append_right
    exact hsourceWord
  · change List.Mem word
      (SuccinctClose.canonicalRelativeRmmInteriorComponentStore
        shape).store.words.toList at hsourceWord
    exact Nat.le_trans
      (SuccinctClose.canonicalRelativeRmmInteriorComponentStore_words_bounded
        shape hsourceWord)
      (concreteBPNativeSuccinctRMQReviewerMachineWordBits_le_wordBits shape)
  · change List.Mem word
      (SuccinctClose.bpFringeChunkTable
        (SuccinctClose.bpFringeChunkBits
          shape.bpCode.length)).store.words.toList at hsourceWord
    rcases List.mem_iff_getElem?.1 hsourceWord with ⟨i, hget⟩
    have hlen : word.length =
        SuccinctClose.bpFringeChunkEntryWidth
          (SuccinctClose.bpFringeChunkBits shape.bpCode.length) :=
      SuccinctClose.bpFringeChunkTable_word_length
        (by simpa [Array.getElem?_toList] using hget)
    rw [hlen]
    have hcap :=
      SuccinctClose.bpFringeChunkEntryWidth_le_machineWordBits_capacity
        shape.size
    rw [Cartesian.CartesianShape.bpCode_length]
    exact hcap
  · change List.Mem word
      (SuccinctClose.bpChunkSelectTable
        (SuccinctClose.bpFringeChunkBits
          shape.bpCode.length) false).store.words.toList at hsourceWord
    rcases List.mem_iff_getElem?.1 hsourceWord with ⟨i, hget⟩
    have hlen : word.length =
        SuccinctClose.bpChunkSelectEntryWidth
          (SuccinctClose.bpFringeChunkBits shape.bpCode.length) :=
      SuccinctClose.bpChunkSelectTable_word_length
        (by simpa [Array.getElem?_toList] using hget)
    rw [hlen]
    have hcap :=
      SuccinctClose.bpChunkSelectEntryWidth_le_machineWordBits_capacity
        shape.size
    rw [Cartesian.CartesianShape.bpCode_length]
    exact hcap

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

/--
**THE INTERIOR COMPONENT STORE'S WORD COUNT, BOUNDED LINEARLY IN THE SIZE.**

Every step of this chain already existed, but the conclusion did not: the
`527 * (n + 1)` bound was assembled only as a LOCAL `have` inside
`concreteBPNativeSuccinctRMQReviewerPhysicalWords_length_le_capacity`, where
nothing outside that proof could reach it.  Naming it here restates none of
its steps.

The consumer is the E1 width story.  `LayoutFits` requires
`L.deadAddress < 2 ^ w` of the canonical summary layout, and that
`deadAddress` is DEFINITIONALLY this word count
(`InteriorDirectory.lean:1646`); the other component offsets are partial sums
of the same eight machine stores.  Before this the only bound on `deadAddress`
was `canonicalRelativeRmmInteriorDeadAddress_fits_reviewerWordBits`
(`InteriorDirectory.lean:2771`), which is stated against
`canonicalRelativeRmmInteriorReviewerCapacity` -- a `Nat.max` that CONTAINS
`deadAddress` itself, so it is true of any store whatsoever and cannot be
compared with the pre-execution reviewer envelope.  This one can.

The slope `527` is not tight and is not meant to be; the envelope it is
compared against is `400000 * (n + 1)`.
-/
theorem canonicalRelativeRmmInteriorComponentStore_words_size_le_linear
    (shape : Cartesian.CartesianShape) :
    (SuccinctClose.canonicalRelativeRmmInteriorComponentStore
        shape).store.words.size <= 527 * (shape.size + 1) := by
  have hclose := concreteBPNativeSuccinctRMQReviewerCloseWords_length_le shape
  have hraw :=
    SuccinctClose.canonicalRelativeRmmInteriorDirectory_payload_length_eq_raw
      shape
  have hlin :=
    SuccinctClose.canonicalRelativeRmmInteriorRawPayloadOverhead_le_linear
      shape.size
  have hlen :
      (concreteBPNativeSuccinctRMQReviewerCloseWords shape).length =
        (SuccinctClose.canonicalRelativeRmmInteriorComponentStore
          shape).store.words.size := by
    simp [concreteBPNativeSuccinctRMQReviewerCloseWords,
      concreteBPNativeSuccinctRMQReviewerSourceWords]
  omega

end SuccinctFinal
end RMQ
