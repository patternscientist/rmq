import RMQ.Core.RankSelectPublic

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
Both are word-RAM/indexed-read model theorems, not Lean runtime claims.
-/
