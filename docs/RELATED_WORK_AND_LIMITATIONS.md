# Related Work And Limitations

For a paper-ready related-work draft, see `PAPER_RELATED_WORK.md`. This file is
the compact limitations-oriented companion.

## Succinct RMQ And Tree Navigation

Fischer and Heun give the classic succinct/static RMQ setting that motivates
the repository's exact RMQ contract and constant-query target. This artifact's
final theorem is BP-native and payload-accounted, but it is still a formal model
surface, not an implementation-tuning campaign.

Navarro-Sadakane and Davoodi-style succinct tree-navigation work motivates the
balanced-parentheses, rank/select, close, and range-min/max ingredients. The
repository formalizes the final RMQ path through these components, including
structural trace replay, but it does not claim a full standalone succinct tree
navigation library or optimized constants.

Liu-Yu and Liu study stronger cell-probe lower-bound questions. This repository
does not mechanize those lower bounds. Its lower-bound story is the
information-theoretic Catalan/Cartesian-shape counting bound exposed through
`RMQ.Headlines.exactRMQLowerBoundDoubledCatalanSlack`.

## Formalization Context

Affeldt et al. and the `affeldt-aist/succinct` line are closely related in
spirit: they verify succinct-data-structure algorithms and representation
invariants in proof assistants. This repository is an independent Lean 4,
Mathlib-free development focused on RMQ, a payload-accounted upper-bound
construction, and a trace/read-store anti-oracle model.

Nipkow, Zhan-Haslbeck, and Chargueraud-Pottier represent complementary
traditions for verified algorithms, cost models, and program/separation-logic
reasoning. The RMQ artifact instead uses value-level list semantics plus an
explicit modeled WordRAM trace/store layer. It proves theorems about that model;
it does not verify generated machine code or compiled Lean execution
performance.

## Anti-Oracle Positioning

The final trace/store/payload model is designed to block oracle-like cost
claims. Successful read events must be tied to a read store and, for the final
flat-payload story, to counted payload backing. No synthetic cost-only marker is
used in the final public trace story. Footprint agreement gives supplied-store
replay and cost transfer, but the footprint is a safe layout overapproximation,
not an exact or minimal dynamic read-set theorem.

## Current Limitations

- No CPU, compiler, extraction, cache, or benchmarking claim is made.
- The cost model is the repository's explicit modeled WordRAM/query-cost layer.
- The current public all-size RMQ cost bound is the conservative constant
  `196727`; the fast-regime theorem under the real `2^15` readiness threshold
  proves the smaller modeled bound `118`, but constants are still not optimized.
- The final footprint is not claimed exact or minimal.
- Constants are not optimized in this pass.
- The cell-probe lower bounds of Liu-Yu/Liu are related work, not mechanized
  theorem content here.
