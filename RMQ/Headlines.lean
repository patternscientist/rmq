import RMQ.Headlines.RMQ
import RMQ.Core.BPNavigationPublic
import RMQ.Core.BPNavigationRAM
import RMQ.Core.RankSelectPublic
import RMQ.Core.RankSelectPublicRAM
import RMQ.Core.SuccinctSpace.BPCloseRMQNavigationRAM

/-!
Aggregate public headline aliases for the full repository.

The narrow RMQ paper surface lives in `RMQ.Headlines.RMQ`; this aggregate barrel
re-exports it and adds standalone rank/select and BP-navigation spoke aliases.
Existing public names under `RMQ.Headlines` are preserved.
-/

namespace RMQ.Headlines

/-- Standalone Jacobson/Clark rank/select family: `n + o(n)`, constant query. -/
abbrev rankSelectNPlusOConstantQuery :=
  RMQ.RankSelect.jacobsonClarkNPlusOConstantQuery

/--
Standalone Jacobson/Clark rank/select family with the same `n + o(n)`,
constant-query profile plus machine-word-bounded concrete payload reads.
-/
abbrev rankSelectWordBoundedNPlusOConstantQuery :=
  RMQ.RankSelect.jacobsonClarkWordBoundedNPlusOConstantQuery

/-- Fixed-weight compressed/FID rank/select, pointwise form. -/
abbrev rankSelectCompressedFIDFixedWeightConstantQuery :=
  RMQ.RankSelect.compressedFIDFixedWeightConstantQueryProfile

/-- Fixed-weight compressed/FID rank/select family: compressed payload plus `o(n)`, constant query. -/
abbrev rankSelectCompressedFIDFixedWeightFamilyProfile :=
  RMQ.RankSelect.compressedFIDFixedWeightFamilyProfile

/--
Interpreted fixed-weight compressed/FID rank/select family: same compressed
payload and constant-query theorem shape, with access/rank/select reads routed
through `WordRAM` bridges.
-/
abbrev rankSelectCompressedFIDFixedWeightInterpretedFamilyProfile :=
  RMQ.RankSelect.compressedFIDFixedWeightInterpretedFamilyProfile

/--
Fused fixed-weight compressed/FID rank/select capstone: compressed payload plus
`o(n)`, constant exact access/rank/select, interpreted WordRAM replay, one
target-independent global payload store, and bounded trace-local event widths.
-/
abbrev rankSelectCompressedFIDFixedWeightGlobalPayloadStoreFusedProfile :=
  RMQ.RankSelect.compressedFIDFixedWeightGlobalPayloadStoreFusedProfile

/--
No-synthetic fused fixed-weight compressed/FID rank/select capstone:
compressed payload plus `o(n)`, constant exact access/rank/select,
interpreted WordRAM replay, one target-independent global payload store,
bounded trace-local event widths, successful-read component backing, and no
synthetic cost-only trace events.
-/
abbrev rankSelectCompressedFIDFixedWeightGlobalPayloadStoreNoSyntheticFusedProfile :=
  RMQ.RankSelect.compressedFIDFixedWeightGlobalPayloadStoreNoSyntheticFusedProfile

/--
Target-independent global payload-store execution story for fixed-weight
compressed/FID rank/select. For each fixed `bits`, access, rank false/true,
and select false/true traces all read from one concrete global read store.
-/
abbrev rankSelectCompressedFIDFixedWeightGlobalPayloadStoreExecutionStory :=
  RMQ.RankSelect.compressedFIDFixedWeightGlobalPayloadStore_execution_story

/--
Bounded target-independent global payload-store execution story for
fixed-weight compressed/FID rank/select. It extends the shared access/rank
false/true/select false/true store packet with trace-local bit widths for
payload-read addresses and word-primitive operands/results.
-/
abbrev rankSelectCompressedFIDFixedWeightGlobalPayloadStoreBoundedExecutionStory :=
  RMQ.RankSelect.compressedFIDFixedWeightGlobalPayloadStore_bounded_execution_story

/--
Target-indexed global payload-store execution story for fixed-weight
compressed/FID rank/select. For each fixed `bits` and `target`, access, rank,
and select traces are relabeled into one concrete read store.
-/
abbrev rankSelectCompressedFIDFixedWeightTargetGlobalPayloadStoreExecutionStory :=
  RMQ.RankSelect.compressedFIDFixedWeightTargetGlobalPayloadStore_execution_story

/--
Bounded target-indexed global payload-store execution story for fixed-weight
compressed/FID rank/select. It extends the combined access/rank/select global
store packet with trace-local bit widths for payload-read addresses and
word-primitive operands/results.
-/
abbrev rankSelectCompressedFIDFixedWeightTargetGlobalPayloadStoreBoundedExecutionStory :=
  RMQ.RankSelect.compressedFIDFixedWeightTargetGlobalPayloadStore_bounded_execution_story

/--
Concrete payload-backed BP close-navigation profile. This is the preferred
current BP-close navigation citation: it fixes the concrete relative-split
close-access family and compact relative-rmM close/LCA directory, proving
`2*n + o(n)` payload, constant modeled query cost, exact Cartesian-shape RMQ
answer semantics, and machine-word-bounded component payload reads.
-/
abbrev concreteBPCloseNavigationProfile :=
  RMQ.BPNavigation.concreteBPCloseNavigationFamily_profile

/--
Concrete BP close-navigation global payload-store execution story. This
consumes `concreteBPCloseNavigationFamily_profile`'s concrete query surface and
proves the costed query is the `toCosted` projection of a globally segmented
`WordRAM.TraceResult` whose payload reads match one concrete store.
-/
abbrev concreteBPCloseNavigationGlobalPayloadStoreExecutionStory :=
  RMQ.BPNavigation.concreteBPCloseNavigationGlobalTrace_execution_story

/--
Bounded concrete BP close-navigation global payload-store execution story. This
adds a finite trace-local bit width bounding payload-read addresses and
word-primitive operands/results for the same concrete global trace.
-/
abbrev concreteBPCloseNavigationGlobalPayloadStoreBoundedExecutionStory :=
  RMQ.BPNavigation.concreteBPCloseNavigationGlobalTrace_bounded_execution_story

/--
Checked obstruction for the current close/LCA-store adapter route toward a
fuller succinct BP tree-navigation execution story. The existing concrete
close/LCA WordRAM trace cannot be reused as the matching-open leg required by
public parent/enclose/subtree navigation.
-/
abbrev concreteSuccinctBPTreeNavigationGlobalPayloadStoreBoundedExecutionStory_currentCloseStoreObstruction :=
  RMQ.BPNavigation.concreteSuccinctTreeNavigationGlobalPayloadStoreBoundedExecutionStory_currentCloseStore_obstruction

/--
Interpreter-backed BP close-navigation profile: `2*n + o(n)`, constant query,
with rank/select/LCA leaves routed through the first-order `WordRAM` bridges.

This is a conditional component-level profile: it requires a supplied
word-bounded sampled encoded close-navigation family. The final BP-native RMQ
capstone has its own constructed interpreter-backed headlines in
`RMQ.Headlines.RMQ`.
-/
abbrev bpCloseNavigationInterpretedTwoNPlusOConstantQuery
    {rankSlots selectSlots lcaSlots : Nat}
    (family :
      RMQ.SuccinctSpace.WordBoundedSampledEncodedPayloadLiveBPCloseRMQNavigationFamily
        rankSlots selectSlots lcaSlots) :=
  RMQ.SuccinctSpace.WordBoundedSampledEncodedPayloadLiveBPCloseRMQNavigationFamily.two_n_plus_o_interpreted_word_bounded_query_profile
    family

end RMQ.Headlines
