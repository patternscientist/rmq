# Known RMQ Proof Failure Modes

Read only the sections relevant to the assigned theorem. These are historical
constraints, not a substitute for inspecting current source.

## Complexity Fidelity

- Wrapping a pure semantic answer in a constant tick does not establish a
  constant-time algorithm.
- A successful read must be charged, machine-bounded, and backed by the counted
  payload used in the space theorem.
- Proof-only fields may carry invariants, never answers or uncharged routing
  oracles.
- Synthetic trace events and repeated decorative reads do not establish an
  execution story.
- Dense all-pairs tables need an actual sublinear budget; an eventuality theorem
  that excludes the branch being counted is not enough.

## Consumption

A helper closes a target only when the named downstream theorem consumes it.
Common incomplete endpoints include:

- a selector cell whose exactness assumes it already stores the semantic winner;
- a range witness exact only from a supplied answer/prefix position;
- endpoint-fringe exactness conditional on a supplied merged-candidate fact;
- an abstract profile whose concrete compact builder remains absent;
- a routing/index function that can hide search, predecessor, or oracle work;
- a new parameter or adapter with no concrete public instance.

## Select And Close History

For historical C1 descriptor-select work, proof fields such as
`descriptor_some_exact`, `descriptor_none_exact`, and
`descriptor_word_choice_exact` state obligations; they are not the compact
builder. A full per-occurrence local-delta payload also fails the intended
`LittleOLinear` budget.

For historical C2 BP-close work, direct scans over interior block summaries are
exact but not uniformly constant. The compact route requires charged local,
global, and top-level navigation plus endpoint repair and a theorem identifying
the leftmost minimum-excess prefix with the RMQ/LCA answer.

## Current Final-Route Constraint

The present architectural campaign separates total block geometry from optional
compact-storage readiness. A local patch that merely lowers the zero-block scan
constant preserves the wrong abstraction and does not advance the campaign.

## Obstruction Dossier

A worker may stop short of a requested positive target only when the target is
closed, a concrete theorem proves it mis-specified, an external dependency
blocks progress, or the coordinator must choose between genuine architecture
forks.

When local variants repeatedly fail for one structural reason, report an
obstruction dossier containing:

1. the exact target signature;
2. the materially distinct construction families attempted;
3. the smallest failed obligations or counterexamples;
4. why nearby syntactic variants cannot repair the failure;
5. the representation, invariant, cost-model, ownership, or theorem choice now
   required.

There is no magic attempt count. Repetition without materially new information
is not evidence; a minimal formal obstruction is stronger than a long list of
similar failed proofs.
