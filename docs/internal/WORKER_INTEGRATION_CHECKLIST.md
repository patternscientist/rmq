# Worker Integration Checklist

Use this after every submitted worker branch.

## Identity And Scope

- [ ] Handle/title, base, branch, worktree, and commit are exact.
- [ ] Changed files fit the write scope.
- [ ] The branch advances the named roadmap node and join in spirit.
- [ ] Unrelated or stale-base changes are absent.

## Target Closure

- [ ] The worker supplied a requirement-to-evidence matrix covering every
      prompt requirement, named consumer, applicable inherited invariant, and
      requested check.
- [ ] The exact target exists and typechecks.
- [ ] Its declared downstream consumer uses it.
- [ ] No wrapper, proof field, alias, or conditional premise is counted as the
      requested concrete endpoint.
- [ ] If short of target, a formal obstruction or dossier forces a genuine
      coordinator decision.
- [ ] The worker was justified in stopping.
- [ ] A `COMPLETE` report contains `No assigned or inherited acceptance
      criterion remains unmet` and does not identify required follow-up for the
      same target.

## Fidelity

- [ ] Counted payload is the payload read.
- [ ] The returned value and routing depend on the charged reads; no semantic
      or wide-cell answer is obtained first and replayed afterward.
- [ ] The trace/footprint is derived from the execution it describes.
- [ ] Successful reads are charged, store-backed, and word bounded.
- [ ] Every executed address, dead/sentinel address, and operand fits the
      modeled machine word; host array bounds alone are not accepted.
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
