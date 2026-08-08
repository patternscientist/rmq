import RMQUnionFind

/-!
# Minimal union-find import example

This checks the standalone non-succinct spoke import surface: partition states,
reference operations, backend profile, and amortized-accounting profile.
-/

namespace RMQ.Examples.UnionFindImport

abbrev State := VerifiedDS.UnionFind.State

abbrev Backend := VerifiedDS.UnionFind.Backend

abbrev AmortizedBackend := VerifiedDS.UnionFind.AmortizedBackend

abbrev referenceBackend := VerifiedDS.UnionFind.referenceBackend

abbrev referenceBackendProfile := VerifiedDS.UnionFind.referenceBackend_profile

abbrev referenceAmortizedBackend :=
  VerifiedDS.UnionFind.referenceAmortizedBackend

abbrev referenceAmortizedBackendProfile :=
  VerifiedDS.UnionFind.referenceAmortizedBackend_profile

end RMQ.Examples.UnionFindImport
