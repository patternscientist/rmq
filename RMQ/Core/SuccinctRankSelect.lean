import RMQ.Core.RankSelectSpec
import RMQ.Core.SuccinctRank
import RMQ.Core.SuccinctSelect
import RMQ.Core.GenericSelect

/-!
# Succinct rank/select barrel

This module gathers the bitvector rank/select specification, sampled
rank/select builders, and generic select implementation. Public aliases remain
terminal in `RMQ.Core.RankSelectPublic` and the standalone `RMQRankSelect` root.
-/
