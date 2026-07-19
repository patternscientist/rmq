# Paper Related Work Draft

This is a paper-ready related-work draft for an ITP/CPP/JFR-style
formalization submission. It is deliberately conservative about priority: any
claim that this mechanizes a novel succinct RMQ theorem should be phrased as a
candidate contribution pending a referee-grade novelty search.

## Succinct RMQ, Cartesian Trees, And LCA

Range-minimum query is a classical static-data-structure problem. The
repository follows the standard half-open RMQ contract with leftmost ties and
uses the Cartesian-shape viewpoint: the array values can be discarded once the
Cartesian shape is known. The relevant classical line includes Vuillemin's
Cartesian trees, the Gabow-Bentley-Tarjan and Bender-Farach-Colton RMQ/LCA
reductions, and Fischer-Heun-style constant-query preprocessing schemes.

The paper contribution is not new asymptotic mathematics in this classical
line. The contribution candidate is a Lean 4 formalization that connects the
known story to explicit theorem surfaces: a list-facing succinct RMQ theorem,
a BP-native construction-facing theorem, a Catalan/Cartesian-shape
information-theoretic lower bound, and a model-scoped execution story for the
final query. Priority language should remain conditional until an external
novelty search checks both proof-assistant libraries and artifact supplements.

## Rank/Select And Balanced Parentheses

The succinct construction depends on the usual rank/select and
balanced-parentheses ingredients. The classical background includes Jacobson's
rank/select dictionaries, Clark and Munro-style constant-time rank/select with
sublinear redundancy, Munro-Raman balanced-parentheses navigation, and the
Raman-Raman-Rao compressed bitvector/FID line. Navarro's compact data
structures text is the natural modern reference point for the surrounding
succinct-toolkit vocabulary.

This repository does not claim a complete optimized succinct tree-navigation
library. Its BP/rank/select infrastructure is formalized to the extent needed
for the RMQ capstone and for standalone spoke theorems. The final RMQ theorem
uses a BP-native path with explicit payload accounting; the standalone
rank/select spoke includes Jacobson/Clark-style and fixed-weight compressed/FID
family surfaces. These support the RMQ proof and provide reusable checked
infrastructure, but constants and executable performance are not the point of
the current artifact.

## Lower Bounds

The lower-bound theorem mechanized here is the Cartesian/Catalan
information-theoretic counting lower bound for exact fixed-length RMQ encodings.
It supports the leading `2*n` payload story and is cited through
`RMQ.Headlines.exactRMQLowerBoundDoubledCatalanSlack`.

This should not be conflated with Liu-Yu/Liu-style cell-probe lower bounds.
Those are important related work for static data structures and range queries,
but they are not mechanized theorem content in this repository.

## Formalized Succinct Data Structures

Affeldt, Garrigue, and Tanaka's ITP 2019 paper, *Proving Tree Algorithms for
Succinct Data Structures*, is the closest formalization precedent. Their Coq
development verifies succinct tree algorithms around rank/select and LOUDS and
connects the development to executable extraction. The present repository is a
separate Lean 4, Mathlib-free development centered on RMQ, Cartesian shapes,
payload accounting, and a model-scoped WordRAM trace/read-store discipline.

The comparison should be made carefully. The Affeldt-Garrigue-Tanaka work has a
strong executable succinct-data-structure story. This repository's current
claim is different: it packages the RMQ theorem surface with explicit modeled
cost, payload-bit accounting, no-synthetic final traces, and successful-read
backing by counted flat payload. It does not verify generated machine code or
compiled Lean performance.

## Formalized Cost And Data-Structure Analysis

Nipkow's verified analyses of functional data structures, and the time-credit
tradition represented by Gueneau, Chargueraud, and Pottier and by
Chargueraud-Pottier's union-find verification, are important comparison points
for cost claims. Those developments tie cost to actual program steps in a
proof-assistant setting, often with executable functional programs or
separation-logic/time-credit reasoning.

The RMQ repository takes a different route. Its cost statements are
model-level: a `Costed` layer and explicit `WordRAM.TraceEvent` streams model
unit-cost indexed reads and word-local primitives. The paper should present
this as a distinct design point, not as a replacement for verified compiled
execution. The relevant adequacy claim is that the final modeled trace has
explicit read events, no synthetic cost-only markers, bounded event data, and
successful reads backed by counted flat payload words.

## Artifact And Provenance Positioning

The artifact uses AI-assisted audit-driven development as process provenance,
not as proof evidence. The proof trust base is Lean kernel checking under the
pinned toolchain. Axiom scripts, forbidden-token scans, shim lints, and the
reproduction script are reviewer and reproducibility checks. The ADD record is
useful for explaining how objections were found and repaired, but it does not
make a theorem true.

## Limitations To State In The Paper

- The cost model is not Lean runtime or compiled-code performance.
- No compiler, CPU, cache, extraction, benchmark, or production-serialization
  claim is made.
- The all-size modeled query-cost bound on the canonical reviewer route is the
  uniform checked charged-trace value `207`, derived as
  `2*35 + (2*11 + 2*37 + 30) + 11`. Controller operations remain
  uncharged; this is not conventional word-RAM complexity. Earlier checked
  cost, dispatch, size-premise, and proof-only chronology lives in the explicit
  [`compatibility history`](digests/SUCCINCT_RMQ_COST_COMPATIBILITY_HISTORY.md),
  not in the current paper proposition.
- The auxiliary logical layout footprint is a safe overapproximation. The
  reviewer flat-physical footprint is execution-derived and exactly the
  execution's ordered read projection.
- The current related-work and novelty story should avoid unqualified priority
  language until the novelty search is complete.

## References To Cite

- R. Affeldt, J. Garrigue, K. Tanaka. *Proving Tree Algorithms for Succinct
  Data Structures.* ITP 2019.
- M. A. Bender and M. Farach-Colton. *The LCA Problem Revisited.* 2000.
- J. Fischer and V. Heun. *Space-Efficient Preprocessing Schemes for Range
  Minimum Queries on Static Arrays.* 2011.
- H. N. Gabow, J. L. Bentley, and R. E. Tarjan. *Scaling and Related Techniques
  for Geometry Problems.* 1984.
- G. Jacobson. *Space-efficient Static Trees and Graphs.* 1989.
- J. I. Munro and V. Raman. *Succinct Representation of Balanced Parentheses
  and Static Trees.* 2001.
- R. Raman, V. Raman, and S. S. Rao. *Succinct Indexable Dictionaries with
  Applications to Encoding k-ary Trees and Multisets.* 2002.
- G. Navarro. *Compact Data Structures: A Practical Approach.* 2016.
- T. Nipkow. *Amortized Complexity Verified.* ITP 2015 / JAR.
- T. Nipkow. *Verified Analysis of Functional Data Structures.* FSCD 2016.
- A. Gueneau, A. Chargueraud, and F. Pottier. *A Fistful of Dollars:
  Formalizing Asymptotic Complexity Claims via Deductive Program
  Verification.* ESOP 2018.
- A. Chargueraud and F. Pottier. *Verifying the Correctness and Amortized
  Complexity of a Union-Find Implementation in Separation Logic with Time
  Credits.* JAR 2019.
