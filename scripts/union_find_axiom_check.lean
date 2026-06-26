import RMQUnionFind

/-!
Focused trust-base check for the standalone union-find spoke.

The current surface is a specification/accounting layer: finite partition
states, exact costed reference operations, a backend interface for future
path-compression implementations, and potential-method profile theorems.
-/

#print axioms RMQ.Amortized.compose
#print axioms RMQ.Amortized.costed_bind
#print axioms RMQ.UnionFind.State.unionSpec_same_of_valid
#print axioms RMQ.UnionFind.referenceBackend_profile
#print axioms RMQ.UnionFind.referenceAmortizedBackend_profile
