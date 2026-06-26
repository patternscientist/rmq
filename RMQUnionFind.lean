import RMQ.Core.UnionFind

/-!
# Standalone union-find spoke

This import root exposes the first union-find specification and amortized
accounting surface. It is not yet a path-compression implementation: the public
API gives a finite partition state, exact costed reference `find`/`union`
operations, a backend interface where `find` may return an updated state, and
the potential-method shape future implementations must satisfy.

The current public profile theorems are
`RMQ.UnionFind.referenceBackend_profile` and
`RMQ.UnionFind.referenceAmortizedBackend_profile`.
-/
