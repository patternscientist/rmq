import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
EG-CP-F01, part D: the flag-rank directory payloads (four more flat-payload
segments) are size-only too.  Rank sample table payload lengths depend on the
underlying bit vector only through its LENGTH, and the two flag vectors have
size-only lengths.
-/

namespace SdkD

open RMQ
open RMQ.Cartesian
open RMQ.GenericSelect

theorem occ_any (s : CartesianShape) (b : Bool) :
    occurrenceCount s.bpCode b = s.size := by
  cases b
  · exact SuccinctSpace.bpCode_rankFalse_full s
  · exact SuccinctClose.bpCode_rankTrue_full s

/-! ## Generic: rank overheads depend on the flag vector only through length -/

theorem longFlagRankSuperOverhead_of_flagLength
    {b1 b2 : List Bool} {t : Bool}
    (hfl : (longSuperFlagBits b1 t).length = (longSuperFlagBits b2 t).length) :
    longFlagRankSuperOverhead b1 t = longFlagRankSuperOverhead b2 t := by
  unfold longFlagRankSuperOverhead
  rw [SuccinctRank.canonicalSuperRankSampleTables_payload_length,
    SuccinctRank.canonicalSuperRankSampleTables_payload_length]
  simp [SuccinctRank.canonicalSuperRankEntries_length,
    longFlagRankWordSize, longFlagRankBlocksPerSuper, hfl]

theorem longFlagRankBlockOverhead_of_flagLength
    {b1 b2 : List Bool} {t : Bool}
    (hfl : (longSuperFlagBits b1 t).length = (longSuperFlagBits b2 t).length) :
    longFlagRankBlockOverhead b1 t = longFlagRankBlockOverhead b2 t := by
  unfold longFlagRankBlockOverhead
  rw [SuccinctRank.canonicalBlockRankSampleTablesOfLocalSpan_payload_length,
    SuccinctRank.canonicalBlockRankSampleTablesOfLocalSpan_payload_length]
  simp [SuccinctRank.canonicalBlockRankEntries_length,
    longFlagRankWordSize, longFlagRankBlockWidth,
    longFlagRankBlocksPerSuper, hfl]

theorem sparseFlagRankSuperOverhead_of_flagLength
    {b1 b2 : List Bool} {t : Bool}
    (hfl :
      (sparseExceptionEffectiveFlagBits b1 t).length =
        (sparseExceptionEffectiveFlagBits b2 t).length) :
    sparseExceptionEffectiveFlagRankSuperOverhead b1 t =
      sparseExceptionEffectiveFlagRankSuperOverhead b2 t := by
  unfold sparseExceptionEffectiveFlagRankSuperOverhead
  rw [SuccinctRank.canonicalSuperRankSampleTables_payload_length,
    SuccinctRank.canonicalSuperRankSampleTables_payload_length]
  simp [SuccinctRank.canonicalSuperRankEntries_length,
    sparseExceptionEffectiveFlagRankWordSize,
    sparseExceptionEffectiveFlagRankBlocksPerSuper, hfl]

theorem sparseFlagRankBlockOverhead_of_flagLength
    {b1 b2 : List Bool} {t : Bool}
    (hfl :
      (sparseExceptionEffectiveFlagBits b1 t).length =
        (sparseExceptionEffectiveFlagBits b2 t).length) :
    sparseExceptionEffectiveFlagRankBlockOverhead b1 t =
      sparseExceptionEffectiveFlagRankBlockOverhead b2 t := by
  unfold sparseExceptionEffectiveFlagRankBlockOverhead
  rw [SuccinctRank.canonicalBlockRankSampleTablesOfLocalSpan_payload_length,
    SuccinctRank.canonicalBlockRankSampleTablesOfLocalSpan_payload_length]
  simp [SuccinctRank.canonicalBlockRankEntries_length,
    sparseExceptionEffectiveFlagRankWordSize,
    sparseExceptionEffectiveFlagRankBlockWidth,
    sparseExceptionEffectiveFlagRankBlocksPerSuper, hfl]

/-! ## Specialised to the live BP route -/

theorem flagrank_overheads_size_only {s t : CartesianShape}
    (h : s.size = t.size) (b : Bool) :
    longFlagRankSuperOverhead s.bpCode b = longFlagRankSuperOverhead t.bpCode b /\
      longFlagRankBlockOverhead s.bpCode b =
        longFlagRankBlockOverhead t.bpCode b /\
      sparseExceptionEffectiveFlagRankSuperOverhead s.bpCode b =
        sparseExceptionEffectiveFlagRankSuperOverhead t.bpCode b /\
      sparseExceptionEffectiveFlagRankBlockOverhead s.bpCode b =
        sparseExceptionEffectiveFlagRankBlockOverhead t.bpCode b := by
  have hlen : s.bpCode.length = t.bpCode.length := by
    rw [CartesianShape.bpCode_length s, CartesianShape.bpCode_length t, h]
  have hocc : occurrenceCount s.bpCode b = occurrenceCount t.bpCode b := by
    rw [occ_any s b, occ_any t b, h]
  have hlong :
      (longSuperFlagBits s.bpCode b).length =
        (longSuperFlagBits t.bpCode b).length := by
    simp [longSuperFlagBits, superSlotCount, hlen, hocc]
  have hsparse :
      (sparseExceptionEffectiveFlagBits s.bpCode b).length =
        (sparseExceptionEffectiveFlagBits t.bpCode b).length := by
    simp [sparseExceptionEffectiveFlagBits,
      sparseExceptionEffectiveLocalSlotCount, localSlotCount, superSlotCount,
      hlen, hocc]
  exact ⟨longFlagRankSuperOverhead_of_flagLength hlong,
    longFlagRankBlockOverhead_of_flagLength hlong,
    sparseFlagRankSuperOverhead_of_flagLength hsparse,
    sparseFlagRankBlockOverhead_of_flagLength hsparse⟩

end SdkD
