import RMQ.Core.RankSelectPublic

/-!
# Standalone rank/select spoke

This import root exposes the plain-bitvector rank/select API and public
Jacobson/Clark theorem. It avoids the final RMQ capstone and backend roots, but
the current proof-support import closure still shares the succinct-space,
shape/lower-bound infrastructure. The exposed API is plain bitvector
access/rank/select rather than an RMQ/LCA/Fischer-Heun backend.

The public headline theorem is
`RMQ.RankSelect.jacobsonClarkNPlusOConstantQuery`; the strengthened
word-bounded profile is
`RMQ.RankSelect.jacobsonClarkWordBoundedNPlusOConstantQuery`.
-/
