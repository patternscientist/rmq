import RMQ.Core.SuccinctFinal.RAM.GeometryClosure

/-!
The two query-time taint candidates that `GeometryClosure` did not already
cover: the rank leaf's super- and block-table overhead scalars.  These are
`payload.length` of tables built from the bit vector, so the taint flags them;
they are in fact functions of `bpCode.length` alone.
-/

namespace DPWKernelI2

open RMQ RMQ.Cartesian RMQ.SuccinctFinal

variable {a b : CartesianShape}

theorem qt53_rankSuperOverhead (h : a.size = b.size) :
    builtRelativeSplitBPCloseRankSuperOverhead a =
      builtRelativeSplitBPCloseRankSuperOverhead b := by
  have hlen : a.bpCode.length = b.bpCode.length :=
    GeometryClosure.bpLen_congr h
  unfold builtRelativeSplitBPCloseRankSuperOverhead
  simp only [SuccinctRank.canonicalSuperRankSampleTables_payload_length,
    SuccinctRank.canonicalSuperRankEntries_length,
    builtRelativeSplitBPCloseRankBlocksPerSuper,
    builtRelativeSplitBPCloseRankWordSize, hlen]

theorem qt54_rankBlockOverhead (h : a.size = b.size) :
    builtRelativeSplitBPCloseRankBlockOverhead a =
      builtRelativeSplitBPCloseRankBlockOverhead b := by
  have hlen : a.bpCode.length = b.bpCode.length :=
    GeometryClosure.bpLen_congr h
  unfold builtRelativeSplitBPCloseRankBlockOverhead
  simp only [SuccinctRank.canonicalBlockRankSampleTablesOfLocalSpan_payload_length,
    SuccinctRank.canonicalBlockRankEntries_length,
    builtRelativeSplitBPCloseRankBlockWidth,
    builtRelativeSplitBPCloseRankBlocksPerSuper,
    builtRelativeSplitBPCloseRankWordSize, hlen]

#print axioms qt53_rankSuperOverhead
#print axioms qt54_rankBlockOverhead

end DPWKernelI2
