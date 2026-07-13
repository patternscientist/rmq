# Worker Integration Checklist

Use this after every submitted worker branch.

## Identity And Scope

- [ ] Handle/title, base, branch, worktree, and commit are exact.
- [ ] Changed files fit the write scope.
- [ ] The branch closes its named local rung and advances the roadmap join in
      spirit.
- [ ] Local-rung status and roadmap-node status are recorded separately.
- [ ] Unrelated or stale-base changes are absent.

## Target Closure

- [ ] The worker supplied a requirement-to-evidence matrix covering every
      prompt requirement, named consumer, applicable inherited invariant, and
      requested check.
- [ ] Matrix rows retain frozen IDs and verbatim requirements; the worker did
      not redefine requirements around the implementation.
- [ ] Every closed semantic row quotes a checked theorem type or exact
      hypotheses/conclusion. Declaration names alone are rejected.
- [ ] Every semantic liveness, coverage, ownership, refinement, or equivalence
      row expands its load-bearing definitions and records an attempted
      anti-vacuity mutation for every applicable semantic subclaim plus the
      theorem that rejects each one.
- [ ] The exact target exists and typechecks.
- [ ] Its declared downstream consumer uses it.
- [ ] No wrapper, proof field, alias, or conditional premise is counted as the
      requested concrete endpoint.
- [ ] If short of target, a formal obstruction or dossier forces a genuine
      coordinator decision.
- [ ] The worker was justified in stopping.
- [ ] A `CANDIDATE_COMPLETE` report contains the required provisional
      declaration and identifies no required follow-up for the same target.
- [ ] The report begins with the exact status/declaration. Informal claims such
      as "closed at worker/gate level" are treated as `INCOMPLETE`.

## Fidelity

- [ ] Counted payload is the payload read.
- [ ] If public claims combine space, execution, provenance, or machine facts,
      their theorem arguments concern the same object or a checked identity,
      erasure, or flattening chain connects them at the public consumer.
- [ ] Guarded public wrappers apply one validity domain to every combined field,
      or a checked equivalence connects guarded and raw executions; invalid,
      reversed, and out-of-bounds cases do not mix two execution stories.
- [ ] The returned value and routing depend on the charged reads; no semantic
      or wide-cell answer is obtained first and replayed afterward.
- [ ] Evidence about a returned value or route constrains that projection;
      aggregate record inequality is not accepted when only its log changes,
      and concrete witnesses do not close universally quantified claims.
- [ ] The trace/footprint is derived from the execution it describes.
- [ ] Successful reads are charged, store-backed, and word bounded.
- [ ] Every executed address, dead/sentinel address, and operand fits the
      modeled machine word; host array bounds alone are not accepted.
- [ ] A whole-machine claim embeds every read-producing segment in one
      pre-execution physical array and relates its one query-independent width
      and capacity to input size.
- [ ] Supplied-store agreement determines result, cost, and relevant trace.
- [ ] Proof-only fields do not contain answers or routing oracles.
- [ ] Cost is derived from primitives or checked trace length.
- [ ] Model ticks, Lean runtime, and measured performance remain distinct.
- [ ] No synthetic events or decorative reads support the claim.
- [ ] Public names match theorem strength.
- [ ] Small and boundary cases relevant to the target were tested or proved,
      including singleton and size two for machine/layout changes.

## Design And Architecture

- [ ] New abstractions match the final mathematical argument.
- [ ] Alternatives and rationale are logged when a real choice was made.
- [ ] Compatibility/history is isolated from the reviewer path.
- [ ] Public names are preserved with aliases when appropriate.
- [ ] The branch does not preserve the defect its roadmap node should remove.

## Verification

- [ ] Targeted build passed first.
- [ ] Full `lake build` passed after proof/implementation edits, or a concrete
      environment/blocker reason is recorded.
- [ ] Paper/headline checks ran when public surfaces changed.
- [ ] Hygiene/native-decision scans ran when relevant.
- [ ] Decision/claim scans ran when relevant.
- [ ] Claim policy/allowlist entries were checked against source; a green scan
      using stale expectations is not accepted.
- [ ] `git diff --check` passed.
- [ ] Skipped checks have a concrete reason.

## Disposition

Choose merge, port, same-worker correction, fresh-worker redesign, or reject.
Then record the integration/rejection, update roadmap and lifecycle state,
engineer the next prompts, and retire the worktree/branch when safe.

The coordinator report states findings first, then verdict, integration action,
roadmap delta, and next prompts.

Prefer a same-worker continuation when the architecture is sound and an
assigned criterion remains locally closable. A submitted commit with an open
criterion stays in the same lifecycle task; do not relabel the repair as a new
roadmap success.

Only the coordinator records `ACCEPTED`. Before accepting or merging a public
paper capstone, trust-boundary change, combined space/execution theorem, or
roadmap-node closure, require a fresh blind audit of the exact candidate commit.
