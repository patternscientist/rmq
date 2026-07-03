import RMQ.Core.RankSelectPublic
import RMQ.Core.RankSelectPublicRAM

/-!
# Standalone rank/select spoke

This import root exposes the plain-bitvector rank/select API and public
Jacobson/Clark theorem. It avoids the final RMQ capstone and backend roots, but
the current proof-support import closure still shares the succinct-space,
shape/lower-bound infrastructure. The exposed API is plain bitvector
access/rank/select rather than an RMQ/LCA/Fischer-Heun backend.

The public plain-bitvector headline theorem is
`RMQ.RankSelect.jacobsonClarkNPlusOConstantQuery`; the strengthened
word-bounded profile is
`RMQ.RankSelect.jacobsonClarkWordBoundedNPlusOConstantQuery`.

The fixed-weight compressed/FID capstone family surface is
`RMQ.RankSelect.compressedFIDFixedWeightFamilyProfile`, with headline alias
`RMQ.Headlines.rankSelectCompressedFIDFixedWeightFamilyProfile`.  It proves a
concrete compressed payload budget
`fixedWeightPayloadBudget bits + o(n)` with uniform constant modeled access,
rank, and select queries for every `bits : List Bool`.  The pointwise theorem
`RMQ.RankSelect.compressedFIDFixedWeightConstantQueryProfile` remains available.
The interpreted replay surface
`RMQ.RankSelect.compressedFIDFixedWeightInterpretedFamilyProfile` strengthens
the same theorem shape by routing access/rank/select reads through `WordRAM`
bridges.  These are word-RAM/indexed-read model theorems, not Lean runtime
claims.  The access, rank, and select legs additionally expose store-backed
trace packets:
`RMQ.RankSelect.compressedFIDFixedWeightAccessTraceResult_execution_story` and
`RMQ.RankSelect.compressedFIDFixedWeightRankTraceResult_execution_story`, and
`RMQ.RankSelect.compressedFIDFixedWeightSelectTraceResult_execution_story`.
For each fixed `bits` and `target`, the relabeled access/rank/select packets
are combined under one concrete target-indexed payload store by
`RMQ.RankSelect.compressedFIDFixedWeightTargetGlobalPayloadStore_execution_story`.
The bounded companion
`RMQ.RankSelect.compressedFIDFixedWeightTargetGlobalPayloadStore_bounded_execution_story`
adds trace-local finite-width bounds for every payload-read address and every
natural operand/result exposed by word-local rank/select primitives.
-/
