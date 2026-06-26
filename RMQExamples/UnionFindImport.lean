import RMQUnionFind

/-!
# Minimal union-find import example

This checks the standalone non-succinct spoke import surface: partition states,
reference operations, backend profile, and amortized-accounting profile.
-/

namespace RMQ.Examples.UnionFindImport

abbrev State := RMQ.UnionFind.State

abbrev Backend := RMQ.UnionFind.Backend

abbrev AmortizedBackend := RMQ.UnionFind.AmortizedBackend

abbrev referenceBackend := RMQ.UnionFind.referenceBackend

abbrev referenceBackendProfile := RMQ.UnionFind.referenceBackend_profile

abbrev referenceAmortizedBackend :=
  RMQ.UnionFind.referenceAmortizedBackend

abbrev referenceAmortizedBackendProfile :=
  RMQ.UnionFind.referenceAmortizedBackend_profile

end RMQ.Examples.UnionFindImport
