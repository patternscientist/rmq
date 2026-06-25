import RMQ.Core.SuccinctRankSelect
import RMQ.Core.BPCloseNavigation
import RMQ.Core.SuccinctReduction
import RMQ.Core.SuccinctFinal

/-!
# Succinct RMQ barrel

This module gathers the reduction-facing plus-minus-one/BP bridge, generic
rank/select access path, compact BP close navigation, and final succinct RMQ
profiles. It is the live succinct-RMQ import surface; archived compatibility
surfaces remain under `RMQArchive`.
-/
