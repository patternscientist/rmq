# Design Decisions

This is the internal design-decision ledger for the RMQ project. It records
architecture and proof-model choices that future coordinators and workers should
understand before changing the repo. It is process documentation, not a proof
artifact; entries should cite checked files, theorem surfaces, docs, commands,
or commits whenever possible.

For ADD process, audit, automation, delegation, or model-routing choices, use
`WORKFLOW_DESIGN_DECISIONS.md`. If a choice affects both proof/code architecture
and workflow, record it in the most relevant ledger and cross-link the other one.
Entries in either ledger should preserve enough rationale, rejected
alternatives, consequences, and evidence for a future paper exposition.

See also:

- [`AUDIT_PROTOCOL.md`](AUDIT_PROTOCOL.md)
- [`../ADD_PROVENANCE.md`](../ADD_PROVENANCE.md)
- [`../AI_ASSISTED_DEVELOPMENT_NOTE.md`](../AI_ASSISTED_DEVELOPMENT_NOTE.md)

## Current Decision Index

The active final-route architecture is DD-20260709-007 through
DD-20260709-010 together with DD-20260710-001 through DD-20260710-004.
Foundational decisions such as the Mathlib-free trust boundary,
list-facing reference semantics, narrow paper root, and cost/runtime separation
remain active where their individual status says so. Entries retain stable IDs
and historical insertion order; do not infer current priority from file order.
Use each entry's Status and the live roadmap.

## When To Update

Update this document when a branch:

- chooses or changes an abstraction boundary;
- introduces, retires, or renames a public theorem surface;
- changes the import root or reviewer-facing artifact path;
- changes the cost model, store model, payload accounting model, or trust
  boundary;
- accepts or rejects a major audit objection;
- chooses one serious implementation/proof route over another.

Do not update it for routine lemma names, local proof refactors, formatting,
unmerged scratch experiments, or tiny follow-on fixes unless they change the
project architecture.

Workers should either update this file on their branch or say in their report:
"No design-decision update needed." The coordinator owns final wording when a
branch is integrated.

## Entry Template

```text
## DD-YYYYMMDD-NNN: Title

Status: Proposed | Accepted | Superseded | Rejected
Date: YYYY-MM-DD
Scope:

Decision:

Context:

Options considered:

Rationale:

Consequences:

Evidence:

Follow-up:

Supersedes:
```

Backfilled entries should say so in the context or evidence. Backfill should
come first from commits, checked theorem names, docs, and digests. Sanitized
visible transcript excerpts can be useful provenance, but raw transcript dumps
and private model traces are not public artifact evidence and should not be used
as the authoritative source for a design decision.

## DD-20260708-001: Keep The Project Mathlib-Free

Status: Accepted
Date: 2026-07-08
Scope: Trust base and dependency footprint.

Decision:

The project remains a Lean 4 / Std / `omega` development pinned by
`lean-toolchain`, without importing Mathlib.

Context:

The RMQ spoke is intended to be a small, inspectable formal artifact. Adding a
large dependency would make some proof work easier but would also change the
review burden and artifact story.

Options considered:

- Keep the existing Lean/Std/omega footprint.
- Import Mathlib to reuse asymptotic, order, and data-structure infrastructure.

Rationale:

The current theorem surface is already checked in the smaller footprint, and
the public artifact emphasizes a narrow trust and dependency story. Preserving
that story is more valuable than shortening individual proofs.

Consequences:

Workers should not add Mathlib imports without an explicit coordinator decision
and a corresponding public trust-surface update.

Evidence:

- `AGENTS.md`
- `lakefile.toml`
- `docs/WHAT_IS_PROVED.md`
- `docs/TRUST_BASE.md`

Follow-up:

None.

Supersedes:

None.

## DD-20260708-002: Keep The List-Int RMQ Specification As Reference

Status: Accepted
Date: 2026-07-08
Scope: RMQ correctness specification.

Decision:

The reference RMQ contract remains half-open `List Int` range minimum query
semantics with the leftmost tie policy. Representation-specific structures are
refinements or adapters to this reference layer.

Context:

Several succinct and executable layers now sit above the basic specification.
The project needs one stable semantic target so storage and cost refinements do
not rewrite the problem statement.

Options considered:

- Preserve the value-level list reference and adapt representations to it.
- Replace the reference layer with an array, tree, or encoded-shape contract.

Rationale:

The list-level contract is easy for readers to inspect and remains independent
of the succinct representation. It also keeps the public theorem statements
connected to an ordinary RMQ specification.

Consequences:

New executable builders or optimized representations should prove agreement
with the reference layer rather than redefining correctness.

Evidence:

- `AGENTS.md`
- `RMQ/Core/Spec.lean`
- `RMQ/Core/SuccinctRMQClassic.lean`
- `RMQ/Headlines/RMQ.lean`

Follow-up:

None.

Supersedes:

None.

## DD-20260708-003: Separate Model Cost From Lean Runtime

Status: Accepted
Date: 2026-07-08
Scope: Cost model and executable evidence.

Decision:

Public constant-time claims are model-level cost claims about checked traces and
stores. Lean execution time, compiled benchmark time, and construction
performance are separate engineering evidence.

Context:

The repo now has theorem-policed trace and supplied-store surfaces plus growing
interest in runnable examples and benchmarks. Reviewers should not have to
infer which timing story a theorem claims.

Options considered:

- State query bounds only as trace/model-cost theorems and separately report
  executable behavior.
- Treat compiled Lean runtime as the cost theorem.

Rationale:

The trace model is the formal object already constrained by theorems. Runtime
measurements are useful for artifact confidence and future extraction work, but
they do not replace the model-cost theorem.

Consequences:

Docs and worker reports must keep payload bits, proof-only fields, model-cost
ticks, Lean runtime, and compiled performance separate.

Evidence:

- `AGENTS.md`
- `docs/PAPER_MODEL_ADEQUACY.md`
- `docs/RMQ_EXTRACTION_FRONTIER.md`
- `artifact/CLAIMS.md`

Follow-up:

Future executable and benchmark work should cite this decision and state which
layer it strengthens.

Supersedes:

None.

## DD-20260709-005: Theorem-Backed Stack Cartesian Builder For Prepared Input

Status: Accepted
Date: 2026-07-09
Scope: Executable RMQ prepared construction and Cartesian-shape building.

Decision:

`SuccinctClassic.prepareInput` may build its stored shape with
`Cartesian.stackCartesianShape` instead of directly calling the reference
`Cartesian.shape xs`, because the central agreement theorem
`Cartesian.stackCartesianShape_eq_shape` proves extensional equality to the
canonical shape. The list-facing theorem
`SuccinctClassic.stackCartesianShape_eq_cartesianShape` records the same bridge
at the prepared SuccinctClassic boundary.

Context:

DD-20260709-004 allowed the executable harness to reuse a prepared shape, but
kept `prepareInput` on the canonical `shapeRange`/`scanWindow` builder until a
faster constructor had a checked agreement theorem. That theorem now exists.

Options considered:

- Keep `prepareInput` on `cartesianShape xs` and leave the faster builder as a
  standalone executable helper.
- Route `prepareInput` through an unproved executable shortcut.
- Route `prepareInput` through the stack/right-spine builder only after proving
  equality to `Cartesian.shape xs`.

Rationale:

The accepted route preserves the public `List Int` reference semantics while
removing the reference `shapeRange` builder from the prepared executable path.
The proof uses a valued executable Cartesian tree, an inorder-values invariant,
and a validity invariant stating that each root is the leftmost minimum of its
subtree values. The prepared payload/query wrappers keep their existing
agreement theorems, so model-cost claims remain statements about the checked
WordRAM path rather than Lean runtime.

Consequences:

Prepared executable runs now construct their Cartesian shape through the
theorem-backed stack/right-spine builder before reusing it for payload and
query reporting. This is runtime engineering evidence, not a theorem about
wall-clock complexity, extracted-code performance, or a changed query-cost
model. Larger profiling runs should still report the exact phase output and
timings; payload construction and final-query execution may remain bottlenecks
after shape construction is no longer the reference recursive scan.

Evidence:

- `RMQ/Core/Shape.lean`
- `RMQ/Core/SuccinctRMQClassic.lean`
- `RMQ/Validation/SuccinctClassicCostHarness.lean`
- `docs/RMQ_EXTRACTION_FRONTIER.md`
- `lake build RMQ.Core.SuccinctRMQClassic`

Follow-up:

If executable profiling still bottlenecks in prepared construction, compare the
right-spine stack builder against a fully monotone Array-backed implementation,
but keep the same agreement-theorem boundary before routing any new builder
through `prepareInput`.

Supersedes:

Completes the fast-builder follow-up in DD-20260709-004 for the prepared
`SuccinctClassic` path.

## DD-20260709-004: Prepared SuccinctClassic Reuse Before Fast Shape Construction

Status: Accepted
Date: 2026-07-09
Scope: Executable RMQ cost harness and list-facing prepared construction.

Decision:

The executable `SuccinctClassic` cost harness may use the
`SuccinctClassic.PreparedInput` mirror instead of repeatedly calling the
list-facing `buildPayload` and `queryCosted` wrappers, but only through the
proved agreement theorems in `RMQ.Core.SuccinctRMQClassic`.

Context:

The previous harness rebuilt `Cartesian.shape xs` for metadata, payload
construction, route classification, route-cost bounds, and each query window.
This obscured the useful executable evidence with repeated reference-builder
work, while the theorem story already factors the final RMQ construction over a
Cartesian shape.

Options considered:

- Keep calling the public list-facing wrappers everywhere in the harness.
- Add a theorem-backed prepared mirror that reuses one canonical shape per
  fixture.
- Replace the reference shape builder with a new fast Array/stack builder in
  the harness before proving its agreement with `Cartesian.shape xs`.

Rationale:

The prepared mirror is the smallest sound abstraction boundary: it preserves
the public `List Int` reference contract, keeps the model-cost theorem surface
unchanged, and proves the prepared payload/query path equal to the canonical
path, including query model cost. A faster Array/stack Cartesian builder is
still valuable, but the harness should not silently use it until a central
shape-agreement theorem is checked.

Consequences:

Prepared harness runs now reuse the built shape across payload and query calls.
This improves executable profiling evidence but does not prove or claim a
better Lean runtime complexity for constructing `Cartesian.shape xs`.
Future fast builders should prove extensional equality to the canonical shape
before replacing `prepareInput`.

Evidence:

- `RMQ/Core/SuccinctRMQClassic.lean`
- `RMQ/Validation/SuccinctClassicCostHarness.lean`
- `docs/RMQ_EXTRACTION_FRONTIER.md`
- `lake build RMQ.Core.SuccinctRMQClassic`
- `lake exe rmq_succinct_classic_cost_harness -- --profile-size 1280`

Follow-up:

Completed for the prepared path by DD-20260709-005. Future variants should keep
the same theorem-backed replacement boundary.

Supersedes:

None.

## DD-20260708-004: Use A Narrow RMQ Paper Root

Status: Accepted
Date: 2026-07-08
Scope: Reviewer-facing imports and public theorem surface.

Decision:

The reviewer-facing RMQ root is `RMQPaper` / `RMQ.Headlines.RMQ`. The broader
`RMQ` root remains available for the whole checked project, including other
spokes, compatibility modules, and historical modules.

Context:

The project contains more than the RMQ paper spoke. A paper reviewer should be
able to inspect the RMQ artifact without reverse-engineering unrelated roots.

Options considered:

- Keep only the broad `RMQ` root as the artifact entry point.
- Add a narrow RMQ paper root while preserving the broad library root.

Rationale:

The narrow root reduces reviewer friction without deleting checked history or
other public spokes.

Consequences:

Paper docs and artifact scripts should prefer `lake build RMQPaper` for the
RMQ paper path. Changes to the paper theorem surface should update the narrow
root and its claim-correspondence docs.

Evidence:

- `RMQPaper.lean`
- `RMQ/Headlines/RMQ.lean`
- `docs/RMQ_IMPORT_CLOSURE.md`
- `artifact/README.md`

Follow-up:

If future work moves modules between paper and non-paper roots, update this
entry or add a superseding decision.

Supersedes:

None.

## DD-20260708-005: Treat ADD As Workflow, Not Trust Base

Status: Accepted
Date: 2026-07-08
Scope: AI-assisted development provenance.

Decision:

Audit-driven development records how the project was built and reviewed. It is
not part of the Lean trust base and does not prove mathematical claims.

Context:

The project relies heavily on coordinator and worker chats, external audits,
digests, and branch reviews. Those records are valuable for accountability and
future reconstruction, but the artifact must stand on checked source and
reproducible commands.

Options considered:

- Make ADD provenance a public proof-support layer.
- Keep ADD provenance as workflow evidence while the proof artifact remains the
  checked Lean development and reproducible scripts.

Rationale:

This keeps the strongest trust story: AI can help discover, write, and audit
proofs, but the reviewer need only trust Lean, the source, and the documented
commands.

Consequences:

Worker reports, digests, and transcript excerpts may justify why work was done
or how decisions were made. They should not be cited as proof of a theorem,
cost bound, or implementation claim.

Evidence:

- `docs/ADD_PROVENANCE.md`
- `docs/AI_ASSISTED_DEVELOPMENT_NOTE.md`
- `docs/internal/AUDIT_PROTOCOL.md`

Follow-up:

Backfill major ADD decisions from checked artifacts and sanitized summaries,
not from private model traces.

Supersedes:

None.

## DD-20260708-006: Use Supplied-Store And Footprint Model Adequacy

Status: Accepted
Date: 2026-07-08
Scope: Final RMQ execution story.

Decision:

The public final-query execution story is based on supplied-store and footprint
adequacy theorems, flat-payload successful-read backing, and no-synthetic
trace events rather than a claim about Lean runtime or a verified compiler.

Context:

Earlier audit work pushed the project away from dense-table relabeling and
synthetic trace padding toward a theorem surface where successful reads are
backed by counted payload components and final traces are structurally real.

Options considered:

- Claim correctness and cost directly from high-level Lean functions.
- Use a theorem-policed trace/store/footprint model as the paper-level cost
  surface.
- Immediately build a verified compiler or extraction story.

Rationale:

The supplied-store route gives a strong checked account of the current RMQ
query model while leaving executable and compiler-strengthening work as a clear
future ladder.

Consequences:

Future executable work should prove agreement with this model or clearly state
that it is benchmark/artifact evidence rather than a replacement theorem.

Evidence:

- `docs/PAPER_MODEL_ADEQUACY.md`
- `RMQ/Core/SuccinctFinalModelAdequacy.lean`
- `RMQ/Headlines/RMQ.lean`
- `artifact/CLAIMS.md`

Follow-up:

Pursue the executable ladder as a strengthening path: runnable Lean harness,
compiled trace interpreter, then translation validation or compiler work if it
still buys reviewer confidence.

Supersedes:

None.

## DD-20260708-007: State The Two Query-Cost Regimes Explicitly

Status: Superseded by DD-20260708-011
Date: 2026-07-08
Scope: RMQ cost claims.

Decision:

The public query-cost story distinguished the all-size constant bound from the
fast-regime bound: `196727` remained the all-size model-cost constant, while
`118` was the fast-regime constant under the readiness threshold. The old
`2^128` threshold was compatibility/history language, not the public activation
story. DD-20260708-011 later superseded the all-size alias with a route-split
theorem and fixed `65585` corollary.

Context:

Earlier audits found that threshold wording could make the execution story look
stronger than the theorem surface actually supported. Later work introduced a
cleaner readiness/cost-regime story.

Options considered:

- Hide the regime split behind prose.
- State both constants and their assumptions in public theorem maps and docs.
- Revert to the old `2^128` public route.

Rationale:

The explicit split is the least surprising reviewer story: a checked all-size
bound, a checked fast-regime bound, and no stale threshold language pretending
to be the main theorem.

Consequences:

Any future reduction of the all-size constant or threshold should update
headline aliases, claim correspondence, artifact claims, and this decision log.

Evidence:

- `docs/WHAT_IS_PROVED.md`
- `docs/PAPER_CLAIM_CORRESPONDENCE.md`
- `RMQ/Headlines/RMQ.lean`
- `artifact/CLAIMS.md`

Follow-up:

The highest-value proof improvement remains shrinking or simplifying the
all-size cost story without weakening the checked model.

Supersedes:

None.

## DD-20260708-008: Make The List-Facing Full-Model Lift The Next Proof Target

Status: Fulfilled; superseded as live guidance by the landed list-facing surface
Date: 2026-07-08
Scope: RMQ public theorem surface.

Decision:

The next RMQ proof target should lift the final supplied-store/footprint
model-adequacy theorem to the public `SuccinctClassic`/`List Int` interface.

Context:

The theorem stack already has a strong final shape-level store story. A
reviewer should not have to manually chase that story through the shape adapter
to understand what the classical list-facing RMQ theorem means under a supplied
payload store.

Options considered:

- Start external code generation first.
- Add more explanatory prose to the model-adequacy docs.
- Close the theorem-shaped gap at the public list-facing interface.

Rationale:

The gap is theorem-shaped, close to the paper surface, and likely cheaper than a
new executable/codegen ladder. It also sharpens every later executable claim by
pinning the public model theorem first.

Consequences:

The next proof worker should target `SuccinctClassic` wrappers and headline
aliases, not broad refactors or C/Rust generation.

Evidence:

- `RMQ/Core/SuccinctRMQClassic.lean`
- `RMQ/Headlines/RMQ.lean`
- `docs/internal/RMQ_FINAL_ROADMAP.md`

Follow-up:

Completed by the list-facing supplied-store/footprint theorems in
`SuccinctRMQClassic` and `RMQ.Headlines.RMQ`.

Supersedes:

None.

## DD-20260708-009: Clean The All-Size Cost Surface Rather Than Explain Around It

Status: Fulfilled; superseded by DD-20260708-011 and DD-20260709-001
Date: 2026-07-08
Scope: RMQ cost theorem surface.

Decision:

After the list-facing lift, prioritize a cleaner all-size cost theorem that
supersedes the distracting `196727` public surface if the formal route allows
it.

Context:

The current all-size theorem is correct, but the constant and nearby
compatibility history invite unnecessary audit effort. The fast-regime theorem
already shows the shape of the desired public story.

Options considered:

- Treat the ugly constant as only a documentation issue.
- Reintroduce uncounted dense answer tables or proof-only answer fields to make
  the constant look nicer.
- Prove a cleaner all-size theorem without weakening the execution-story
  guarantees.

Rationale:

The strongest paper version should expose a principled all-size theorem and
keep legacy thresholds private or compatibility-only.

Consequences:

Any worker reducing the public constant must preserve counted payload backing,
no-synthetic traces, and the retirement of `2^128` as a public activation
threshold.

Evidence:

- `RMQ/Headlines/RMQ.lean`
- `docs/internal/RMQ_FINAL_ROADMAP.md`

Follow-up:

Completed by the route-split theorem and current clean all-size constant
`4144`; the new roadmap targets the underlying uniform-route architecture.

Supersedes:

None.

## DD-20260708-011: Make The Route-Split Cost Bound The Public All-Size Alias

Status: Superseded by DD-20260709-001
Date: 2026-07-08
Scope: RMQ cost theorem surface.

Decision:

Expose the all-size final-query cost through a route-split theorem and a clean
fixed corollary `65585`. Keep the old `196727` aggregate under explicit legacy
compatibility aliases only.

Context:

R2 found that exact all-size `118` is not honest with the current structural
zero-block replay: the zero-block same-block branch really scans counted
BP-code chunks. However, the old all-size aggregate also added the zero-block
scan and interior fallback costs even though the close/LCA replay takes those
routes mutually exclusively.

Options considered:

- Keep explaining the `196727` aggregate in prose.
- Claim all-size `118` despite the zero-block scan.
- Make the theorem surface branch-sensitive, then publish the maximum of those
  checked branches as the fixed all-size constant.

Rationale:

The route-split theorem is the clearest reviewer story that is true today:
Ready remains `118`, active non-Ready is bounded by the newly checked `480`
scan leaf for total query cost `568`, inactive non-Ready is `88`, and the
zero-block structural BP-code scan gives the fixed all-size maximum `65585`.
No proof-only answer fields, synthetic events, uncounted payload, or public
`2^128` activation premise are introduced.

Consequences:

Paper-facing aliases should point to
`concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_le_routeSplit`
or its fixed corollary
`concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_le_cleanAllSize`.
The old `concreteBPNativeSuccinctRMQQueryCost_eq = 196727` remains checked, but
only as a compatibility surface.

Evidence:

- `RMQ/Core/SuccinctClose/RelativeRmmMacro/ConcreteDirectory.lean`
- `RMQ/Core/SuccinctFinal.lean`
- `RMQ/Core/SuccinctFinalRAM.lean`
- `RMQ/Core/SuccinctRMQClassic.lean`
- `RMQ/Headlines/RMQ.lean`
- `docs/PAPER_CLAIM_CORRESPONDENCE.md`

Follow-up:

The next constant-shrinking target is to replace the zero-block BP-code scan
with a smaller counted structural route, if one can be proved without hiding an
answer table.

Supersedes:

DD-20260708-009.

## DD-20260709-001: Sharpen The Zero-Block Route-Split Scan Cap

Status: Accepted
Date: 2026-07-09
Scope: RMQ cost theorem surface.

Decision:

Keep the legacy aggregate `concreteCompactBPCloseZeroBlockScanCost` unchanged,
but replace the zero-block branch of the public route-split cost expression
with the sharper counted cap
`SuccinctClose.concreteCompactBPCloseZeroBlockRouteScanCost = 4096`. The clean
all-size final-query constant is now
`SuccinctFinal.concreteBPNativeSuccinctRMQCleanAllSizeQueryCost = 4144`.

Context:

The structural zero-block same-block trace reads chunked BP-code payload words.
The earlier route-split corollary bounded those chunks by `2 * size + 1` under
`size < 2^15`, giving `65585` after final-query overhead. The trace already
uses machine-sized chunks, so the divisor by
`SuccinctRank.machineWordBits shape.bpCode.length` can be retained in the
uniform small-size proof.

Options considered:

- Keep the `65585` route-split corollary.
- Add or reactivate a finite same-block answer table.
- Prove the tighter chunk-count cap for the existing structural scan.

Rationale:

The new proof is still a counted BP-code scan: it adds no answer table, no
proof-only answer field, no synthetic trace event, and no public activation
premise. It proves the strongest local improvement available from the existing
trace shape: a zero-block close/LCA cap of `4096`, yielding whole-query bound
`4144`. The active non-Ready route remains checked at `568`, and exact
all-size `118` remains false for the current all-size route.

Consequences:

Paper-facing aliases should cite the `4144` clean fixed corollary. The legacy
`concreteBPNativeSuccinctRMQQueryCost_eq = 196727` aggregate remains checked
only as compatibility and deliberately keeps the older coarse scan component.

Evidence:

- `RMQ/Core/SuccinctClose/RelativeRmmMacro/LocalBPDecoder.lean`
- `RMQ/Core/SuccinctClose/RelativeRmmMacro/ConcreteDirectory.lean`
- `RMQ/Core/SuccinctFinal.lean`
- `RMQ/Headlines/RMQ.lean`

Follow-up:

The next theorem-shaped R3 target is a real zero-block interval navigator with
charged range-min evidence, or an obstruction theorem showing that the current
BP-code-only trace cannot beat the full chunk scan without new counted
structure.

Supersedes:

DD-20260708-011.

## DD-20260708-010: Treat Executable Evidence As A Ladder, Not The Trust Base

Status: Accepted
Date: 2026-07-08
Scope: RMQ executable and extraction frontier.

Decision:

Strengthen executable evidence in stages: runnable Lean validation first, then
a checked trace/register interpreter bridge, then a verified reference Word-RAM
machine, and only then translation-validated C/Rust if still useful.

Context:

Lean compilation means there is no Coq-style extraction gap to close for the
existing definitions, but reviewers still benefit from a familiar executable
path and a small-step machine bridge. Theorems about model cost remain distinct
from wall-clock timings.

Options considered:

- Jump straight to a verified backend.
- Present benchmarks as model-cost proofs.
- Build a staged artifact ladder with explicit trust boundaries.

Rationale:

The staged route gives reviewer-legible executable evidence without confusing
runtime measurements with the checked RAM cost model.

Consequences:

Executable work should report both theorem links and runtime measurements, but
only the former should be used as proof evidence.

Evidence:

- `docs/RMQ_EXTRACTION_FRONTIER.md`
- `docs/internal/RMQ_FINAL_ROADMAP.md`

Follow-up:

Start with the runnable Lean validation path after the public theorem surface
has been cleaned.

Supersedes:

None.

## DD-20260708-012: Refactor Only Around Stable Proof Boundaries

Status: Accepted
Date: 2026-07-08
Scope: RMQ source architecture.

Decision:

Perform major source reshaping after the list-facing and all-size theorem
boundaries are pinned, and preserve public names through aliases.

Context:

Some final RMQ files are large enough that proof architecture is harder to see
than it should be. Refactoring can improve reviewer trust, but broad movement
before theorem surfaces stabilize increases merge and audit risk.

Options considered:

- Broad renaming before theorem closure.
- Mix semantic strengthening with large file movement.
- Wait for stable public theorem boundaries, then split modules around proof
  roles.

Rationale:

Architecture should serve the final theorem argument. Stable aliases let the
paper and artifact docs remain steady while internals get cleaner.

Consequences:

Refactor workers should avoid semantic strengthening unless it is tiny,
separately documented, and verified by the same gates.

Evidence:

- `docs/RMQ_IMPORT_CLOSURE.md`
- `docs/internal/RMQ_FINAL_ROADMAP.md`

Follow-up:

Prepare a read-only module split proposal after R1/R2 are integrated.

Supersedes:

None.

## DD-20260708-013: Keep ADD Tooling Repo-Native And Model-Agnostic First

Status: Accepted
Date: 2026-07-08
Scope: ADD process tooling.

Decision:

Add worker/audit templates, audit-packet generation, claim-drift scans,
design-decision reminders, and CI artifacts before building model-specific
orchestration.

Context:

The project uses multiple agents and external audits, but public trust should
come from checked theorems, reproducible commands, and stable evidence classes.
Tool-specific automation is useful only after the process contract is stable.

Options considered:

- Treat raw chat exports or hidden model reasoning as public proof evidence.
- Start with a full SDK/MCP orchestrator.
- Standardize evidence and prompts first.

Rationale:

The workflow should improve because evidence is standardized, not because a
particular model is trusted.

Consequences:

The next process worker should implement templates and scripts before broader
automation experiments.

Evidence:

- `docs/internal/AUDIT_PROTOCOL.md`
- `docs/internal/ADD_WORKFLOW_TOOLING_PLAN.md`
- `docs/internal/WORKFLOW_DESIGN_DECISIONS.md`

Follow-up:

Create the prompt templates and advisory scripts, then consider skills or
non-interactive orchestration after two or more real uses.

Supersedes:

None.

## DD-20260709-002: Separate Differential Validation From Cost Reporting

Status: Accepted
Date: 2026-07-09
Scope: RMQ executable evidence.

Decision:

Keep the broad `SuccinctClassic` differential validator and add a separate
reviewer-facing cost harness that prints deterministic construction/query
reports, route metadata, and `queryCosted.cost`.

Context:

The existing validation executable is optimized for coverage: it checks many
deterministic windows and fails fast on a mismatch. DD-20260708-010 established
the staged executable-evidence ladder. Reviewers also need a small
human-readable artifact that shows specific inputs, windows, answers, model
costs, and reference agreement without implying new theorem trust.

Options considered:

- Extend the differential validator with verbose reports.
- Add theorem aliases or doc-only examples instead of an executable report.
- Keep validation and cost-reporting as separate executables.

Rationale:

Separate executables keep CI-style validation compact while giving reviewers a
stable command whose output can be pasted into an artifact report. The reported
cost remains the model trace/event count from `queryCosted.cost`, not Lean
runtime or hardware timing.

Consequences:

Runnable evidence must continue to state its non-proof status and must compare
answers directly with the `List Int` reference semantics. Larger fixtures that
target ready-regime behavior should be added only when construction cost is
profiled and documented.

Evidence:

- `RMQ/Validation/SuccinctClassic.lean`
- `RMQ/Validation/SuccinctClassicCostHarness.lean`
- `docs/RMQ_EXTRACTION_FRONTIER.md`

Follow-up:

Profile construction for larger ready-regime fixtures before making them part
of the default artifact gate.

Supersedes:

None.

## DD-20260709-003: Keep Ready-Threshold Executable Profiling Opt-In

Status: Accepted
Date: 2026-07-09
Scope: RMQ executable evidence and ready-regime artifact fixtures.

Decision:

Do not add a default `2^15` ready-threshold fixture to the artifact gate yet.
Keep ready-regime executable profiling behind an explicit
`lake exe rmq_succinct_classic_cost_harness -- --profile-size N` command until
the prepared builder demonstrates reviewer-friendly ready-threshold runtime.

Context:

The fast-regime theorem surface is already model-level: under the real
`SuccinctClose.concreteBPRelativeRmmInteriorReadyThreshold = 32768` premise,
the final query cost is bounded by the checked `118` trace/event constant. The
new executable harness is reviewer evidence for the public
`SuccinctClassic.buildPayload` / `queryCosted` path, not a runtime theorem.
Local profiling completed `N = 1024`, but an opt-in `N = 2048` profile did not
finish inside a five-minute worker budget. A default `32768` ready-threshold
fixture would therefore make artifact review about construction runtime rather
than the theorem-level model claim.

Options considered:

- Add a default `32768` ready-regime fixture to the cost harness.
- Add an opt-in size-parameterized profile and keep the default fixture set
  reviewer-friendly.
- Skip executable ready-regime evidence entirely until extraction work.

Rationale:

The canonical `buildPayload xs` and `queryCosted xs left right` interfaces may
recompute the reference shape. The prepared executable path now uses
`Cartesian.stackCartesianShape` once and reuses the resulting `PreparedInput`,
with agreement theorems back to the canonical semantics. That removes the old
reference-builder description from the prepared path, but ready-threshold
runtime has not yet been established as a default reviewer command. This
engineering question remains separate from the checked `queryCosted.cost`.

Consequences:

The default harness may report fast-regime applicability and bounds, but it
must not imply a Lean wall-clock claim. Ready-threshold experiments should remain explicit opt-in profiling runs. The
prepared stack builder and agreement theorems are now landed; the remaining
work is measurement and any theorem-backed construction optimization needed to
make a threshold fixture reviewer-friendly.

Evidence:

- `RMQ/Validation/SuccinctClassicCostHarness.lean`
- `docs/RMQ_EXTRACTION_FRONTIER.md`
- `artifact/README.md`
- Local command: `lake exe rmq_succinct_classic_cost_harness -- --profile-size 1024`
- Local timeout: `lake exe rmq_succinct_classic_cost_harness -- --profile-size 2048`
  exceeded 300 seconds on the worker machine.

Follow-up:

Profile the landed prepared builder at the ready threshold and promote a
fixture only when its runtime fits the documented artifact-review budget.

Supersedes:

None.

## DD-20260709-006: Split Final RAM Segment And Flat-Payload Layers

Status: Accepted
Date: 2026-07-09
Scope: Final RMQ RAM bridge module architecture.

Decision:

Keep `RMQ.Core.SuccinctFinalRAM` as the compatibility/root module for the
final RAM theorem surface, but move the concrete segment numbering and
canonical global read-store map to
`RMQ.Core.SuccinctFinal.RAM.Segments`, and move the query-independent flat
payload layout, flat read store, segment/source/backing manifest, and
successful-read backing predicates to
`RMQ.Core.SuccinctFinal.RAM.FlatPayload`.

Context:

`SuccinctFinalRAM.lean` had accumulated both theorem-heavy trace/program/cost
proofs and the lower-level storage manifest used by those proofs. The public
names and theorem statements were stable enough to make a mechanical split
around reviewer-legible storage boundaries.

Options considered:

- Leave the file monolithic until a semantic proof change needs it.
- Move segment layout and flat-payload backing into focused imported modules
  while leaving trace/program/cost semantics in the compatibility root.
- Rename public theorem surfaces while splitting.

Rationale:

The split lets reviewers inspect the storage story separately from the
whole-query replay proof, without changing public theorem names, aliases,
payload accounting, model-cost claims, or executable behavior.

Consequences:

Future changes to segment numbering or flat-payload backing should start in the
new `RAM/Segments.lean` and `RAM/FlatPayload.lean` modules. Changes to the
whole-query interpreter, execution-story packets, and cost theorem semantics
should remain in `SuccinctFinalRAM.lean` unless a later split establishes a new
stable proof boundary.

Evidence:

- `RMQ/Core/SuccinctFinal/RAM/Segments.lean`
- `RMQ/Core/SuccinctFinal/RAM/FlatPayload.lean`
- `RMQ/Core/SuccinctFinalRAM.lean`
- `lake build RMQ.Core.SuccinctFinalRAM`

Follow-up:

The next safe reviewer-legibility split is likely the whole-query
interpreter/program layer or the bounded-event/no-synthetic execution-story
packets, keeping public aliases unchanged.

Supersedes:

None.
## DD-20260709-007: Separate Total Geometry From Compact-Storage Readiness

Status: Accepted
Date: 2026-07-09
Scope: Relative rmM parameters and final RMQ routing architecture.

Decision:

The next final-route architecture must define total geometry with positive
routing divisors and widths, truthful semantic counts, and a separate
compact-storage readiness predicate. Inactivity must not overwrite geometry.
A legitimate empty-input count may remain zero.

Context:

The current canonical `Active` predicate combines geometry, storage budget,
and word-width facts. Its inactive branch collapses geometric values to zero,
which creates a top-level zero-block structural replay and the public all-size
cost split. The route is correct, but the abstraction makes a proof artifact
look like an algorithmic regime.

Options considered:

- Continue lowering the zero-block scan constant.
- Keep zero-valued parameters and hide the branch behind a public wrapper.
- Make layout total, let readiness govern storage only, and prove agreement with
  the current ready route.

Rationale:

Total geometry matches standard directory presentations and removes a
reviewer-visible proof accident. Agreement lemmas provide a conservative
migration path without weakening current payload, machine, or space theorems.

Consequences:

The next proof campaign begins with parameter design and agreement theorems.
Local zero-block constant patches do not count as advancing this decision.

Evidence:

- `docs/internal/RMQ_FINAL_ROADMAP.md`
- `RMQ/Core/SuccinctClose/RelativeSummary.lean`
- `RMQ/Core/SuccinctSpace/MachineChunkedTable.lean`
- `FixedWidthNatTable.machineReadCosted_erase`
- `FixedWidthNatTable.machineReadCostedWithStore_eq_of_agree`
- `FixedWidthNatTable.machineFootprint_successful_read_backed`
- `canonicalRelativeRmmInteriorRawPayloadOverhead_littleO`
- `RMQ/Core/SuccinctClose/RelativeRmmMacro/LocalBPDecoder.lean`

Follow-up:

The scouts are joined in `RELATIVE_RMM_LAYOUT_DESIGN.md`; proceed with its U1
interface and preserve truthful empty-input count semantics.

Supersedes:

The architectural endpoint implicit in DD-20260709-001; its checked cost
improvement remains valid as an intermediate theorem.

## DD-20260709-008: Use One Uniform Directory Abstraction At All Sizes

Status: Accepted
Date: 2026-07-09
Scope: Final local/interior RMQ query route.

Decision:

Empty, singleton, small, and ready inputs should use one directory abstraction.
Degenerate or packed representations may implement that abstraction, but the
reviewer path must not dispatch to an unbounded structural scan because a
layout parameter is zero.

Context:

The present all-size route is theorem-sound and payload-backed, but its
zero-block replay is an artifact of inactive geometry. Preserving that branch
while polishing constants would leave the central elegance problem intact.

Options considered:

- Retain the route split and explain it.
- Replace the small branch with an uncounted answer table.
- Provide one semantic directory interface, first attempting one total
  hierarchy and introducing a separate packed implementation only if a formal
  obstruction requires it.

Rationale:

A uniform abstraction makes the exactness and cost proof follow the mathematical
decomposition rather than threshold compatibility. A naturally degenerate
single hierarchy is preferred; counted representation selection remains an
implementation option only if formally necessary. Existing space and
execution-story truth must be preserved.

Consequences:

The all-size constant is rederived only after the uniform route lands. Dense
answers, proof-only answers, synthetic events, and decorative reads remain
forbidden.

Evidence:

- `docs/internal/RMQ_FINAL_ROADMAP.md`
- `docs/internal/audit_reports/2026-07-09_A02_rmq_pre_w10_frontier_audit.md`

Follow-up:

Use the joined scout design to pre-register the uniform-directory theorem
signatures.

Supersedes:

None.

## DD-20260709-009: Make Exact Dynamic Read Agreement The Primary Adequacy Surface

Status: Accepted
Date: 2026-07-09
Scope: Supplied-store and machine-model adequacy.

Decision:

After the uniform route stabilizes, make agreement on the actual dynamic read
set the primary supplied-store theorem. Retain conservative safe-footprint
agreement as a convenient corollary and bundle recurring machine invariants in
a named well-formedness certificate.

Context:

The current list-facing footprint lift is real and useful, but broad safe
footprints and repeated side conditions ask reviewers to reconstruct why they
are sufficient.

Options considered:

- Keep only the broad footprint theorem.
- Expose raw side conditions at every public layer.
- Lead with exact dynamic reads and derive broad-footprint convenience results.

Rationale:

Exact read agreement is the closest theorem to the execution semantics. A
certificate packages standard machine preconditions without hiding payload or
cost assumptions.

Consequences:

This is sequenced after the routing refactor so the dynamic read set is stable.

Evidence:

- `docs/internal/RMQ_FINAL_ROADMAP.md`
- `RMQ/Core/SuccinctRMQClassic.lean`

Follow-up:

Inventory existing exact-read lemmas during the dependency scout.

Supersedes:

None.

## DD-20260709-010: Prove A Small-Step Machine Bridge Before External Code Generation

Status: Accepted
Date: 2026-07-09
Scope: Executable and cost-model publication architecture.

Decision:

Use the existing first-order query controller as the source for a small,
familiar Word-RAM small-step semantics and prove result/step correspondence
before considering generated C or Rust.

Context:

The Lean definitions already execute. The remaining reviewer-friction gap is a
familiar machine refinement theorem, not a Coq-style extraction step. A custom
translation validator introduced too early could add more bespoke machinery
than it removes.

Options considered:

- Stop at executable Lean validation.
- Generate external code immediately.
- Prove the small-step simulation, complete executable evidence, then reassess
  whether external code lowers reviewer effort.

Rationale:

The reference-machine pattern is recognizable in formalization research and
directly connects the checked trace cost to machine steps. External code remains
available if venue or performance goals justify it.

Consequences:

C/Rust generation is not on the active path before the machine theorem.

Evidence:

- `docs/internal/RMQ_FINAL_ROADMAP.md`
- `docs/RMQ_EXTRACTION_FRONTIER.md`

Follow-up:

Pre-register the instruction set and simulation statement after the uniform
route stabilizes.

Supersedes:

None.
## DD-20260710-001: Use Computational Layout Data With Separate Validity And Readiness

Status: Accepted
Date: 2026-07-10
Scope: U1 relative-rmM interface.

Decision:

Represent the canonical relative-rmM layout with four computational Nat fields:
block size, blocks per superblock, block count, and relative width. Put
positivity, coverage, and codec facts in `Layout.Valid`; put payload-budget and
one-word facts in `Layout.SummaryFits`; define `Layout.CompactReady` by adding
the existing macro-size condition.

No layout projection may depend on SummaryFits or CompactReady. Counts retain
truthful zero semantics.

Context:

The P1 scout correctly found that the raw formulas are already total. The
current defect comes from Active-gated wrappers that overwrite those values.
The scout proposed a shape-indexed proof-carrying record, while the coordinator
audit found that a smaller computational record plus named predicates better
separates runtime data from proof certificates and simplifies extensional
agreement.

Options considered:

- Keep the existing Active-gated scalar definitions.
- Use a shape-indexed record carrying all proof fields.
- Use pure computational layout data with separate validity/readiness
  predicates.
- Scatter `max 1` across current formulas.
- Give `CompactReady` a global `Decidable` instance for convenient branching.

Rationale:

The chosen split matches the mathematical presentation, makes executable data
obvious, and keeps proof-only evidence out of the data representation. It also
lets canonical validity and legacy agreement be cited directly without making
arbitrary layouts silently valid.

The uniform-route plan deliberately leaves `CompactReady` without a global
`Decidable` instance. A local instance can be recovered through the checked
legacy equivalence if a real construction-time consumer needs it; routine
decidability would otherwise encourage the route split U2 is meant to remove.

Consequences:

U1 adds the interface and agreement theorems without changing query dispatch.
U2 first attempts one naturally total directory hierarchy. A separate packed
small implementation requires a formal obstruction showing that the total
hierarchy is inadequate.

U1 also relocates `canonicalBPRelativeSummaryBlockCountRaw_upper_cover` from
`RelativeRmmMacro/LocalBPDecoder.lean` to `RelativeSummary.lean`: its proof uses
only raw layout arithmetic, so the upstream location preserves dependency
direction without a duplicate helper or downstream import.

The accepted interface includes the named `Layout.Valid.macroSize_pos` accessor.
Named per-field legacy-agreement corollaries should be added only when U2
consumers demonstrate that they improve the proof surface.

Evidence:

- `docs/internal/RELATIVE_RMM_LAYOUT_DESIGN.md`
- `RMQ/Core/SuccinctClose/RelativeSummary.lean`
- `RMQ/Core/SuccinctSpace/MachineChunkedTable.lean`
- `FixedWidthNatTable.machineReadCosted_erase`
- `FixedWidthNatTable.machineReadCostedWithStore_eq_of_agree`
- `FixedWidthNatTable.machineFootprint_successful_read_backed`
- `canonicalRelativeRmmInteriorRawPayloadOverhead_littleO`
- `03043fe` (U1 implementation and relocation)
- `RMQ/Core/SuccinctClose/RelativeRmmMacro/ConcreteDirectory.lean`
- `docs/internal/audit_reports/2026-07-10_A03_u1_total_layout_audit.md`

Follow-up:

U1 and its named macro-size positivity accessor passed the proof gates; A03
accepted the interface. Begin U2 from the uniform-directory theorem target and
add agreement corollaries only for actual consumers.

Supersedes:

The overbroad phrase "total positive geometric parameters" in
DD-20260709-007; that decision remains active with truthful zero-count semantics.

## DD-20260710-002: Treat Declaration Closure As A Pruning Candidate Generator

Status: Accepted
Date: 2026-07-10
Scope: Reviewer-root import pruning, quarantine, and deletion.

Decision:

Use declaration-versus-import closure to identify exact-import and quarantine
experiments. Do not infer that an imported module is globally dead, removable,
or irrelevant merely because no named declaration from it occurs in the
headline theorem bodies.

Removal or quarantine requires a full-repository reverse-consumer check,
successful exact-import replacement, `RMQPaper` and full builds, public axiom
checks, regenerated closure measurements, and an explicit compatibility/public
alias disposition.

Context:

The F0 scout found 54 modules in the 126-module `RMQPaper` import closure that
contribute no declaration to any headline type or proof/value body. That is
strong evidence of import-DAG width, but elaboration dependencies, attributes,
instances, tactics, compatibility roots, and other public spokes are not
captured by the measured headline declaration closure.

Options considered:

- Delete or quarantine all 54 modules as unused.
- Ignore the closure result because it is not a deletion proof.
- Treat it as a ranked candidate list and require checked pruning experiments
  plus global reverse-consumer evidence before removal.

Rationale:

The chosen policy converts a valuable measurement into controlled architecture
work without confusing theorem-body reachability with repository-wide source,
elaboration, runtime, or compatibility reachability. It gives reviewers a
narrower path only when compilation and public-surface evidence support it.

Consequences:

F0 is complete for U1 planning but does not authorize deletion. Productionizing
the declaration probe and performing A1 import pruning remain later work after
the uniform route stabilizes.

Evidence:

- `docs/internal/RMQ_DECLARATION_CLOSURE_2026_07_10.md`
- `docs/RMQ_IMPORT_CLOSURE.md`
- `RMQPaper.lean`

Follow-up:

At A1, generate the full reverse-consumer graph, test exact imports one coherent
module boundary at a time, and record any removal or quarantine separately.

Supersedes:

None.

## DD-20260710-003: Freeze Conceptual Namespaces Before Physical Module Splits

Status: Accepted
Date: 2026-07-10
Scope: Final RMQ naming and module architecture.

Decision:

Use the conceptual namespaces recorded in `RELATIVE_RMM_LAYOUT_DESIGN.md` and
preserve stable public aliases, but defer broad physical file movement until U2
stabilizes the uniform route and its proof consumers. Split a file only when
declaration closure and a stable mathematical or execution-story boundary
justify a coherent unit.

Do not adopt the architecture scout's fine-grained file tree as a target by
itself, and do not create one-file-per-theorem-category fragmentation.

Context:

The N1 scout identified reviewer-legible concepts across relative-rmM layout,
BP close, payload, execution, cost, model adequacy, and the list-facing API. It
also proposed a detailed module tree before U1/U2 had fixed the final consumers.
Moving files now would mix semantic migration with import surgery and could
create parallel APIs or compatibility churn.

Options considered:

- Perform the complete fine-grained module split before U1.
- Leave names and module boundaries entirely unchanged.
- Freeze conceptual namespaces and compatibility policy now, then perform only
  evidence-backed physical splits after U2.

Rationale:

Conceptual names help proofs and paper exposition immediately. Delaying physical
movement keeps the semantic campaign reviewable and lets actual dependency
closure determine module boundaries instead of file size or speculative taste.

Consequences:

U1 stays in `RelativeSummary.lean`; U2 changes the route without broad movement;
A1 may later introduce coherent modules while retaining compatibility imports
and public aliases.

Evidence:

- `docs/internal/RELATIVE_RMM_LAYOUT_DESIGN.md`
- `docs/internal/RMQ_DECLARATION_CLOSURE_2026_07_10.md`
- `docs/RMQ_CODE_MAP.md`
- `RMQ/Core/SuccinctClose/RelativeSummary.lean`
- `RMQ/Core/SuccinctSpace/MachineChunkedTable.lean`
- `FixedWidthNatTable.machineReadCosted_erase`
- `FixedWidthNatTable.machineReadCostedWithStore_eq_of_agree`
- `FixedWidthNatTable.machineFootprint_successful_read_backed`
- `canonicalRelativeRmmInteriorRawPayloadOverhead_littleO`

Follow-up:

Re-run declaration closure after U2 and approve each physical split against its
stable consumers and paper-facing proof story.

Supersedes:

None.
## DD-20260710-004: Rechunk One Total Raw-Canonical Relative-rmM Hierarchy

Status: Accepted
Date: 2026-07-10
Scope: U2 all-size relative-rmM interior directory representation.
Closure amendment, 2026-07-11:

Whole-machine candidate amendment, 2026-07-12:

The list-facing construction has one live public payload,
`SuccinctClassic.buildPayload`. Reviewer physical words erase exactly to that
payload and supply the canonical execution; an appended sibling payload is not
an acceptable space/execution bridge. The uniform route keeps the checked
transitional bound `328`. Ready `118`, route-split `4144`, zero-block, and
`196727` are compatibility/history only.

This amendment records W15 worker-candidate evidence, not U2 acceptance. Only
the coordinator may accept U2 after independently reconstructing the frozen
completion matrix and obtaining a fresh blind exact-commit audit.

The decision now includes the downstream reviewer consumer, not only the
interior component. The canonical component store is embedded at global segment
`20`; its exact physical word offset is
`concreteBPNativeSuccinctRMQCanonicalInteriorWordOffset`. The all-size
cross-block, `lcaClose`, whole-query trace, supplied-store replay, model
adequacy packet, and ordinary-list surface consume the canonical directory.
The reviewer route contains no Ready/Active/inactive or zero-block dispatch.

The total machine abstraction is
`concreteBPNativeSuccinctRMQReviewerWordBits n = machineWordBits (400000 *
(n + 1))`, derived before execution from the input size and a linear bound on
the exact public physical store. It covers all stored and returned words,
segment encodings, primitive operands/results, and live, failed, and sentinel
addresses after translation into the global reviewer store. The physical
erasure/refinement and whole-query address/operand theorems, plus kernel-checked
empty, singleton, size-two, and symbolic threshold-boundary cases, close the
small-input addressability requirement.

Additional alternatives considered and rejected:

- Keep the trace-local post-hoc width: rejected because it does not establish a
  query-independent address-capacity story or cover canonical dead addresses.
- Use only `machineWordBits shape.bpCode.length`: rejected because tiny inputs
  need to address fixed global segments and the counted component store.
- Use a fixed 64- or 128-bit width: rejected as arbitrary for the unbounded
  mathematical model.
- Preserve the Ready `118` or route-split constant using padding/decorative
  reads: rejected because modeled cost must be the consumed trace.
- Embed six independent global segments: rejected because one concatenated
  component plus exact offsets gives the intended later flat-store transport.
- Prove only a segment-20 slice theorem: rejected because it would leave the
  other executed rank/select/BP segments disconnected from the one physical
  array and public payload.
- Use a safe static footprint overapproximation as the primary agreement
  theorem: retained only as compatibility because exact ordered execution
  agreement is stronger and preserves failed and repeated reads.

The checked transitional whole-query cost is the primitive sum proved by
`concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_le_canonicalTransitional`;
`concreteBPNativeSuccinctRMQCanonicalTransitionalQueryCost_eq` evaluates it to
`328`. U3, not U2, owns the final cost simplification. The old `118`,
route-split, `4144`, and `196727` statements remain compatibility history.
For paper exposition, the machine story must be presented in this order: the
public payload, its exact physical-word representation, the logical-to-physical
execution refinement, the execution-derived footprint, and only then the width
and cost bounds. This avoids conjoining facts about sibling objects.


Decision:

Instantiate one two-level local/global relative-rmM hierarchy unconditionally
from `RelativeRmm.canonicalLayout`. Store the canonical raw summary, local,
and global payloads for every shape, then rechunk all six fixed-width tables
into one bounded physical component store. Concatenate summary baseline,
min-relative, max-relative, arg-offset, local-offset, and global-block words in
directory-payload order with explicit offsets. Thread one supplied flat store
through every addressed read, and define the range footprint from that same
execution's ordered read log. Each fixed-width chunk has
`SuccinctRank.machineWordBits shape.bpCode.length` bits, with at most eight
reads per logical cell.
Empty, singleton, and small shapes use the same macro arithmetic as large
shapes. No top-level branch may inspect `Active`, `Ready`, or
`CompactReady`; readiness appears only in the checked agreement and payload
transport theorems.

Context:

U1 proved the raw canonical layout valid for every shape, and the existing
`bpTwoLevelInteriorCandidateCosted_erase_exact` join already needed only
geometry plus query count/bounds. The remaining blocker was representational:
for the singleton Cartesian shape, the raw relative width is five bits while
the modeled machine word is two bits. Thus the legacy one-cell/one-word codec
cannot be used raw at all sizes even though the hierarchy itself is correct.

Options considered:

- Keep the Ready/active-not-Ready/inactive top-level route split.
- Add a separate packed small directory.
- Store dense all-pairs range answers or scan the raw summaries.
- Keep one raw relative cell as one machine word.
- Rechunk every logical cell uniformly and preserve the hierarchy.
- Return semantic answers with proof-only or decorative read traces.

Rationale:

Uniform rechunking addresses the concrete singleton width mismatch without
changing the rmM geometry or introducing a second algorithm. The reusable
`FixedWidthNatTable.machineStore` and
`machineReadComputationAt_refines_machineReadCosted` remain the accepted
per-table adapter. The composed consumer
`canonicalRelativeRmmInteriorComponentStore` appends the six bounded stores
at explicit segment offsets. Its flattening is exactly the counted
summary/local/global directory payload.

`canonicalRelativeRmmInteriorRangeMinCostedWithStore` computes physical
addresses from the logical index, table width, and segment offset; every read
comes from its supplied flat array. Summary, local, and global candidates are
constructed only from the returned chunks. The physical footprint is the
ordered address projection of that execution's read log, including repeats and
failed reads, and its length equals the modeled cost. Thus
`payloadWordsRead` is an execution-derived projection rather than an
independent reviewer-facing witness.

`canonicalRelativeRmmInteriorRangeMinCostedWithStore_eq_of_agree` proves that
stores agreeing on the first execution's actual footprint produce the same
full execution after cost projection. This handles adaptive later addresses,
so result, cost, and recorded footprint all agree. Successful reads from the
canonical component store are in range and backed by its counted words; every
returned word is machine-width bounded.
`canonicalRelativeRmmInteriorRangeMinCostedWithStore_eq_current` connects the
composed execution to the prior canonical query, transferring unconditional
exactness and the 240-read cap. The exact raw payload overhead remains proved
little-o directly by
`canonicalRelativeRmmInteriorRawPayloadOverhead_littleO`; the threshold-spliced
overhead definition is retired. CompactReady is used only for checked legacy
agreement and eventual asymptotic domination, never construction or dispatch.

Consequences:

`canonicalRelativeRmmInteriorDirectory_rangeMinCosted_erase_exact` has no
Ready or Active premise. The strengthened all-size profile packages the
unconditional payload bound, constant modeled query cost, exactness, and
`CanonicalRelativeRmmInteriorStoreProfile`: exact component flattening,
canonical execution agreement, footprint determinacy of result and cost,
successful-read backing, returned-word bounds, recorded-footprint identity,
and cost/footprint equality. The canonical directory's `rangeMinCosted` and
`payloadWordsRead` are both projections of the one supplied-store execution;
there is no equally public competing directory with an independent trace.
U1's fieldwise CompactReady agreement corollaries and the generic machine-table
adapter remain as earlier-decision evidence because this composed path now
consumes them downstream.

This rung does not alter `lcaCloseCosted`, final-query dispatch, the zero-block
same-block route, or final all-size constants. Those remain a separate consumer
change.

Evidence:

- `RMQ/Core/SuccinctClose/RelativeSummary.lean`
- `RMQ/Core/SuccinctSpace/MachineChunkedTable.lean`
- `RMQ/Core/SuccinctSpace/MachineChunkedTableProgram.lean`
- `FixedWidthNatTable.machineReadComputationAt_refines_machineReadCosted`
- `BoundedPayloadWordStore.append_erases`
- `canonicalRelativeRmmInteriorRawPayloadOverhead_littleO`
- `RMQ/Core/SuccinctClose/EndpointFringe/InteriorCandidate/InteriorDirectory.lean`
- `canonicalRelativeRmmInteriorComponentStore_flattens_payload`
- `canonicalRelativeRmmInteriorRangeMinCostedWithStore_eq_current`
- `canonicalRelativeRmmInteriorRangeMinCostedWithStore_eq_of_agree`
- `canonicalRelativeRmmInteriorRange_successful_read_backed`
- `canonicalRelativeRmmInteriorRange_returned_word_bounded`
- `canonicalRelativeRmmInteriorRangeFootprint_recorded`
- `canonicalRelativeRmmInteriorRangeMinCostedWithStore_erase_exact`
- `canonicalRelativeRmmInteriorRangeMinCostedWithStore_cost_le`
- `canonicalRelativeRmmInteriorDirectory_profile_allSize`
- the singleton width audit: raw relative width 5, machine width 2

Follow-up:

Embed `canonicalRelativeRmmInteriorComponentStore` and its offsets as one
segment of the later global flat close/LCA store. Replace the three-way interior
route with the exact supplied-store execution and transport its recorded
footprint into the global trace. This decision does not itself remove the
zero-block route or change public final-query constants.

Supersedes:

The three-way interior routing consequence of DD-20260709-007 for the interior
directory abstraction. It does not supersede the still-live final-query route
until the consumer migration lands.

## DD-20260713-001: amend REQ-01 space equality to the public upper bound

Status: accepted coordinator amendment for W17.

Decision:

- Exact physical-word erasure to the public list-facing `buildPayload` remains
  mandatory.
- The public space clause is
  `buildPayload.length <= 2 * n + overhead n`, with `overhead = o(n)`.
- Exact length equality is not required, and the payload must not be padded to
  manufacture it.

Rationale:

The publication claim is an upper bound of `2*n + o(n)` bits.  Exact erasure
already establishes the important object-identity fact: the bits counted by
the public theorem are exactly the bits underlying physical execution.  An
additional exact-length equation is stronger than that claim and is unrelated
to execution provenance.  Padding would add unread or decorative bits solely
to satisfy an equation, weakening rather than strengthening the reviewer
story.

Consequences:

All W17 public theorem surfaces and prose use the upper-bound form.  Exact
equalities remain appropriate only for genuine representation identities such
as physical-word flattening to `buildPayload`; they are not manufactured for
the asymptotic budget.

## DD-20260713-002: operational liveness, guarded adequacy, and value evidence

Status: accepted coordinator amendment for the W17 semantic gate.

Decision:

- Define reviewer-source liveness from the actual logical segment map and its
  read-producing evaluator leaf.  A non-shared source is live only with a
  segment-derived `ReviewerReadLeaf` ownership witness; the single BP-code
  source is live only through the checked segment-0/segment-19 shared
  dependencies.
- Connect both directions to execution.  Every emitted read resolves to a
  counted/live source and an actual branch of
  `WholeQueryInstr.evalGlobalWordTrace`; every counted source reaches a branch
  in the closed whole-query program, with the checked shared-BP witness where
  applicable.  The older `consumer?` label remains compatibility metadata and
  is not acceptance evidence.
- Keep raw shape-level model adequacy under an explicit `ValidRange` premise at
  the list consumer.  The same list story has a separate all-invalid packet in
  which logical and physical results are `none`, traces and physical footprint
  are empty, cost is zero, and every supplied flat store yields that same
  guarded execution.
- State supplied-store dependency at the `.value` projection: the physical
  result is exactly the existing supplied-store evaluator result after checked
  address translation.  Use a valid singleton corruption at consumed physical
  address seven as the nontrivial witness; it changes the real answer from
  `some 0` to `none` and rejects a mutant that retains the supplied trace while
  substituting the canonical value.

Alternatives considered:

- `ReviewerSource.Live := True`: rejected because adding a dead source cannot
  falsify it and it says nothing about evaluator use.
- Manifest membership or a second hand-written consumer enumeration: rejected
  because it merely restates the payload list.  Forged labels must fail without
  changing the operational maps.
- One anti-vacuity check for the bundled manifest row: rejected because dead
  addition, used-source removal, forged ownership, emitted-read coverage, and
  counted-source reachability are different semantic subclaims.
- Aggregate `TraceResult` inequality after corrupting a consumed word: retained
  only as a lower-level trace-observability compatibility lemma.  It is not
  answer-dependency evidence because the trace alone can make the records
  unequal.
- Unconditional raw adequacy inside an otherwise guarded public record:
  rejected because an invalid public query executes the guarded
  `none`/empty/zero branch, not the raw shape evaluator.
- Claim that every consumed read changes every answer: rejected as false and
  unnecessary.  The dependency-transfer theorem is conditional on differing
  translated evaluator values, and the concrete witness identifies one
  decisive consumed word for one valid query.

Publication-facing rationale:

The paper theorem should describe one execution on each public input.  On a
valid range, that execution is the adapter-backed supplied-store evaluator and
its physical trace.  On an invalid range, it is the guarded empty execution.
Operational liveness makes the payload inventory falsifiable, and the
projection theorem plus corruption witness establishes answer provenance
without overstating universal sensitivity of every read.

Consequences:

- `ConcreteBPNativeSuccinctRMQFinalTraceModelAdequacy` contains operational
  read/source and counted-source/evaluator connections, and replaces aggregate
  disagreement as its dependency field with `.value`-level supplied-evaluator
  facts.
- `FlatPayloadStoreNoSyntheticExecutionStory` places raw adequacy behind
  `ValidRange`, packages invalid result/trace/cost/footprint/store behavior, and
  carries the projection-level dependency theorem for the same guarded
  physical execution.
- `RMQ.Headlines.listIntSuccinctRMQPaperMainTheorem` consumes the valid raw
  packet, invalid packet, and supplied-store value equality explicitly.  The
  curated axiom inventories expose the operational, mutation, guarded, and
  value-projection declarations.

Evidence:

- `ReviewerSource.Live`, `ReviewerSource.OperationallyOwnedBy`, and
  `ReviewerSharedBPConsumer.Checked`.
- `concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_read_operational_source`.
- `concreteBPNativeSuccinctRMQReviewerSource_counted_evaluator_connection`.
- `concreteBPNativeSuccinctRMQReviewerManifest_add_dead_rejected`.
- `concreteBPNativeSuccinctRMQReviewerManifest_remove_used_rejected`.
- `concreteBPNativeSuccinctRMQReviewerSource_forged_consumer_rejected`.
- `concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore_value_eq_suppliedStoreEvaluator`.
- `reviewerPhysicalTraceResultWithStore_value_eq_suppliedStoreEvaluator_of_valid`.
- `flatPayloadStoreNoSyntheticExecutionStory_invalid_semantics`.
- The six singleton corruption/mutant guards in
  `RMQ/Validation/SuccinctClassic.lean`.

## DD-20260713-003: producer-level provenance replaces category joins

Status: historical W18 checkpoint; superseded for the reviewer surface by
DD-20260713-004.

Decision:

- Represent occurrence-level production by
  `WholeQueryProgram.ProducesEvent`.  A witness carries one instruction from
  the concrete closed program, its actual pre-execution state after folding
  the exact preceding prefix, and membership of the same event in that
  instruction evaluation's trace.
- Resolve that same event to storage with `ReviewerSource.ProducedReadBy` and
  to its concrete component evaluation with the relational
  `ReviewerProducerReadPath`.  Source, segment, instruction, state, and leaf
  are not independently selected facts.
- Use a relation rather than a functional segment-to-leaf owner.  Logical
  segments `17`--`19` may be consumed both inside the LCA instruction and by
  the final rank instruction, while the shared BP source has select, LCA, and
  final-rank paths.
- State reverse liveness as `ReviewerSource.HasProducerMayPath`: every counted
  source has at least one concrete attempted-read path through the actual
  select/rank/LCA construction.  This is deliberately a may-read obligation;
  it does not say every query reads every source.
- State shared-BP ownership as
  `ReviewerSharedBPConsumer.ProducerConnected`, where one event simultaneously
  identifies the BP source and the named consumer's component path.
- Test nonvacuity with
  `concreteBPNativeSuccinctRMQFreshUnusedCanonicalSource`: fresh segment `21`
  carries a plausible `canonicalClose` label but has no
  `HasOperationalProducer` witness because no closed-program instruction trace
  can emit its event.

Rejected alternative:

The W17 category join selected a leaf from the static segment map and then
selected any closed-program instruction with that leaf label.  It did not show
that the selected instruction, at its actual prefix state, emitted the event.
In particular, `WholeQueryState.empty` is not producer evidence for later LCA
or rank instructions, and a source witness at shared-BP segment `0` cannot be
combined with an unrelated canonical-close label at segment `20`.  Static
`ReviewerSource.Live`, `ReviewerSource.OperationallyOwnedBy`,
`ReviewerSharedBPConsumer.Checked`, and the functional segment-leaf map remain
compatibility metadata only; they are not load-bearing reviewer evidence.

Consequences:

- Final adequacy, the valid `List Int` story, the paper theorem, headline
  aliases, and curated axiom inventories consume producer-level provenance,
  counted-source may paths, same-event shared-BP paths, and the unused-source
  rejection.
- Category-only headline aliases are removed from the load-bearing public
  surface.  The physical store, supplied-store value dependency, invalid-range
  packet, payload space, word width, and uniform modeled cost `328` are
  unchanged.

Evidence:

- `WholeQueryProgram.evalGlobalWordTrace_event_producer` and
  `WholeQueryProgram.ProducesEvent.prefix_state`.
- `WholeQueryInstr.evalGlobalWordTrace_read_producer_path`.
- `concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_read_producer_provenance`.
- `concreteBPNativeSuccinctRMQWholeQueryProducerProvenance_checked`.
- `concreteBPNativeSuccinctRMQReviewerSource_counted_producer_may_path`.
- `concreteBPNativeSuccinctRMQReviewerSharedBPConsumer_all_producer_connected`.
- `concreteBPNativeSuccinctRMQFreshUnusedCanonicalSource_no_producer`.

## DD-20260713-004: occurrence-indexed provenance and one operational source relation

Status: Accepted for U2 at `4f7ec8be47ecd65b2859a3784fadeab48a629e4e`
after coordinator reconstruction and the A04 blind audit.

Context:

W18 replaced W17's arbitrary-state category join with a real producing
instruction and folded prefix state. That is genuine progress, but the public
relation begins from event-value membership in the global trace, so equal
repeated events are not distinguished. Its `ReviewerProducerReadPath` also
forgets the concrete invocation parameters used to construct the witness.

The reverse-liveness acceptance theorem uses
`ReviewerSource.HasProducerMayPath`, a direct component attempted-read relation,
while the fresh-source mutation proves absence of the stronger
`ReviewerUnusedSourceMutation.HasOperationalProducer`, an actual instruction-
trace relation. Since W18 proves no implication from the positive predicate to
the mutation predicate, the negative theorem does not test the property used
to accept counted sources.

Decision:

- Represent reviewer producer provenance with an occurrence-preserving
  relation: a global trace position, or an equivalent list decomposition that
  preserves multiplicity, is connected to the producing instruction's local
  occurrence at the actual folded prefix state.
- Retain in the public path witness the concrete component invocation and the
  equalities showing that its parameters are exactly those computed by the
  producing instruction. Source and consumer labels are projections of that
  witness, not independently chosen metadata.
- Use one operational source relation for both positive coverage and
  counterfactual rejection. If the positive theorem intentionally states only
  component may-read, label it as such and test the mutation with that exact
  predicate. A reviewer-facing top-level liveness claim instead requires an
  existential valid top-level execution containing the source occurrence.
- Keep weaker event-value membership and component may-read theorems as
  accurately named compatibility or helper facts; do not use them to close an
  occurrence-level or top-level operational claim.

Alternatives considered:

- Retain W18 and explain that identical events are observationally
  interchangeable.
- Keep separate positive and negative relations and add prose saying they have
  the same intent.
- Add only a bridge from component may-read to operational production.
- Preserve occurrences and invocation parameters in the theorem surface and
  unify the relation used on both sides of the counterfactual.

Rationale:

Reviewer-facing provenance is easiest to audit when it follows the standard
interpreter decomposition: one program occurrence, one folded pre-state, one
local trace occurrence, and its position in the composed global trace. This
handles repeated equal reads without asking a reviewer to infer causality from
list membership. One relation for accepted and rejected sources makes the
nonvacuity test logically direct. It also forces the paper to distinguish the
useful but weaker component may-read fact from actual top-level reachability.

Consequences:

- W18 remains a proof checkpoint, not U2 acceptance evidence.
- W19 consumes the occurrence-preserving relation through final adequacy, the
  valid `List Int` theorem, paper theorem, headlines, acceptance matrix, and
  claim docs; U2 may now proceed to coordinator reconstruction and blind audit.
- Public wording must say event-value provenance when only `List.Mem` is
  available and reserve occurrence-level producer provenance for the W19
  relation.
- The physical store, payload identity, invalid-range semantics, word width,
  and checked modeled bound `328` are unaffected.

Evidence:

- W18 commit `63d503d24aadeb501284a658c303bf69861953df`.
- `WholeQueryProgram.ProducesEvent` and
  `WholeQueryProgram.evalGlobalWordTrace_event_producer`.
- `ReviewerProducerReadPath`.
- `ReviewerSource.HasProducerMayPath`.
- `ReviewerUnusedSourceMutation.HasOperationalProducer` and
  `concreteBPNativeSuccinctRMQFreshUnusedCanonicalSource_no_producer`.

Follow-up:

Run coordinator reconstruction and a fresh blind exact-commit audit using the
same-predicate and repeated-event regressions before coordinator acceptance.

## DD-20260713-005: closed-valid occurrence claims and symbolic source families

Status: Accepted for U2 at `4f7ec8be47ecd65b2859a3784fadeab48a629e4e`
after coordinator reconstruction and the A04 blind audit.

Decision:

- Use `WholeQueryProgram.ProducesEventAt` as the generic indexed interpreter
  decomposition. It records the global position, program instruction position,
  exact prefix-folded pre-state, component-local position, and the equality
  `globalPos = prefixTrace.length + localPos`.
- Represent the instruction-computed component call by
  `ReviewerReadInvocation` and `WholeQueryInstr.InvokesReviewerRead`. Select,
  rank, and canonical-close parameters remain in the public witness rather than
  being erased to a leaf label.
- Use `ReviewerProducerClaim.HasClosedValidOccurrence` as the common
  operational relation. Positive claim `P` existentially requires a successful
  `some word`; mutation claim `Q` permits any `word?`.
  `ReviewerProducerClaim.hasOperationalProducer_of_successful` is the checked
  `P -> Q` bridge. Fresh segment `21` is rejected under `Q` itself.
- Split the all-source proof into auditable witness families: executable-size
  symbolic witnesses cover sources 1--11 and 20, the symbolic long-super
  construction covers 12--15, and the symbolic sparse-local construction
  covers 16--19. All witnesses end in a successful indexed occurrence of the
  actual closed whole-query trace under `ValidRange`.
- Use `N = 2^15` for the long-super witness rather than the scout's advisory
  `2^128`: the smaller symbolic shape still proves word width 17, stride 289,
  threshold 24,565, and a strictly longer span, while avoiding irrelevant
  kernel expansion. Keep `N = 2^128` for the sparse-local witness because its
  larger word scale gives the required two-occurrence local stride. Both sets
  of arithmetic are proved in Lean.
- Keep W18 `List.Mem` event-value and direct component may-read declarations as
  compatibility facts only. They do not discharge W19 public fields.
- Package the all-source relation as the proof-only
  `ConcreteBPNativeSuccinctRMQFinalSemanticProvenanceAdequacy` extension and
  project it through `SuccinctRMQClassicProvenance.lean`. The paper/headline
  roots consume this extension, while native validation keeps importing the
  genuine `SuccinctRMQClassic` execution core. This preserves public
  composition without adding symbolic witness construction to the executable
  link closure.
  This composition choice is superseded by DD-20260713-006; the underlying
  occurrence and witness proofs remain accepted checkpoint evidence.

Audited design input:

`docs/internal/U2_POSITIONAL_PROVENANCE_SCOUT.md` was read at exact commit
`17287f25d1241ab6e4609f19863eced66dd9e62b` after fetching
`origin/codex/rmq-u2-provenance-reachability-scout`. It was used as design
input, not proof evidence or a contract amendment. Its prose source-number
summary was corrected from the authoritative table: small families cover
1--11 and 20, long-super covers 12--15, and sparse-local covers 16--19. The
Lean proofs establish the L/S arithmetic rather than importing the report's
calculations.

Rejected alternatives:

- Event-value `List.Mem` as an occurrence witness.
- A leaf/source path that discards the component arguments computed by the
  instruction.
- Component may-read or arbitrary-state instruction traces as top-level source
  reachability.
- A negative mutation predicate stronger than the accepted positive predicate
  without a checked bridge.

Consequences:

Final adequacy, valid `List Int` projections, the paper main theorem,
`RMQ.Headlines.RMQ`, `RMQPaper`, and curated axiom inventories consume the W19
relations. The physical evaluator, one public payload, invalid-range semantics,
logarithmic reviewer width, no-synthetic trace, and checked `328` bound are
unchanged. U3 remains unopened.

Evidence:

- `WholeQueryProgram.evalGlobalWordTrace_getElem?_producer`.
- `WholeQueryInstr.evalGlobalWordTrace_getElem?_read_invocation`.
- `concreteBPNativeSuccinctRMQWholeQueryOccurrenceProvenance_checked`.
- `repeated_equal_read_occurrences_have_distinct_receipts` and the singleton
  validator guard at distinct global positions 0 and 12.
- `concreteBPNativeSuccinctRMQReviewerSource_counted_successful_closed_valid_occurrence`.
- `concreteBPNativeSuccinctRMQReviewerSharedBPConsumer_successful_closed_valid_occurrence`.
- `concreteBPNativeSuccinctRMQFinalSemanticProvenanceAdequacy` and
  `flatPayloadStoreNoSyntheticExecutionStory_semanticProvenanceAdequacy_of_valid`.
- `RMQ/Core/SuccinctFinalSemanticProvenanceAdequacy.lean`.
- `RMQ/Core/SuccinctRMQClassicProvenance.lean`.
- `docs/CODE_MAP.md`.
- `ReviewerProducerClaim.hasOperationalProducer_of_successful`.
- `concreteBPNativeSuccinctRMQFreshUnusedCanonicalSource_no_producer`.

## DD-20260713-006: separate global manifest liveness from current-query provenance

Status: Accepted for U2 at `4f7ec8be47ecd65b2859a3784fadeab48a629e4e`
after coordinator reconstruction and the A04 blind audit.

Context:

`ReviewerProducerClaim.HasSuccessfulClosedValidOccurrence` existentially
chooses some ordinary list and valid closed query. It does not mention a
currently quantified `shape`, `xs`, `left`, or `right`. The W19 checkpoint
nevertheless bundled those global witnesses with parameterized final trace
adequacy and projected them through wrappers carrying an unused current-query
`ValidRange`. That theorem shape could be read as claiming every manifest
source is read by the current query, which is false and stronger than the
proved witness relation.

Decision:

- Keep `ConcreteBPNativeSuccinctRMQFinalTraceModelAdequacy shape left right`
  query-parameterized. Its indexed occurrence field concerns that exact global
  trace, instruction occurrence, folded state, invocation parameters, and
  multiplicity-preserving local embedding.
- Package counted-source reachability, exact shared-BP reachability, the
  checked `P -> Q` bridge, fresh-source rejection, and manifest structure in
  the non-parameterized proof-only
  `ConcreteBPNativeSuccinctRMQReviewerManifestSemanticAdequacy`.
- Remove `xs`/`left`/`right`/`ValidRange` wrappers whose conclusions are only
  global existential facts. Consume the global packet once as a top-level
  conjunct of `listIntSuccinctRMQPaperMainTheorem`; retain raw trace adequacy
  and indexed forward provenance under the current query's validity premise.
- Keep `SuccinctRMQClassicProvenance.lean` as a proof-import seam only. Native
  validation and the cost harness continue importing `SuccinctRMQClassic`
  directly, so symbolic long/sparse witness modules do not enter executable
  import closure.
- Classify `2^128` by role: it is not an activation premise of any current
  canonical execution theorem; it remains both an explicit premise on legacy
  compatibility companions and the symbolic size of W19's proof-only
  sparse-local nonvacuity witness. The witness is not a paper-route, payload,
  cost, or runtime premise.

Rejected alternatives:

- Retain the unused validity premise and repair only prose.
- Strengthen the global existential relation into the false claim that each
  source is read by every valid current query.
- Replace the closed whole-query witnesses with component may-read facts.
- Import symbolic witness modules into native executable roots.

Consequences:

The public theorem now exposes two honest quantifier scopes. The global packet
answers whether every reviewer source has some actual valid execution witness
and whether the segment-21 mutation fails the same operational predicate. The
per-query packet answers where every read of the current execution came from.
The physical evaluator, one public payload, invalid-range semantics,
logarithmic reviewer width, no-synthetic trace, and checked `328` bound remain
unchanged. U3 remains unopened.

Evidence:

- `concreteBPNativeSuccinctRMQReviewerManifestSemanticAdequacy`.
- `concreteBPNativeSuccinctRMQFinalTraceModelAdequacy`.
- `flatPayloadStoreNoSyntheticExecutionStory_rawAdequacy_of_valid` and
  `flatPayloadStoreNoSyntheticExecutionStory_occurrenceProvenance_of_valid`.
- `RMQ.Headlines.listIntSuccinctRMQPaperMainTheorem`.
- `RMQ.Headlines.succinctRMQReviewerManifestSemanticAdequacy`.
- The direct `SuccinctRMQClassic` imports in both validation roots.

## DD-20260714-007: derive U3 from charged operations in the accepted U2 execution

Status: Candidate complete on the U3 worker branch; coordinator exact-commit
reconstruction and blind audit remain separate.

Context:

U2 checked a uniform `328` upper bound by using the shared select constant
`16` for two selects and all three ranks, and the relative-rmM interface cap
`240` for the interior. That theorem was honest but not reviewer-legible as a
final operational derivation. U3 had to tighten the bound without changing the
payload, execution, public dispatch, invalid-range behavior, or trace events.

Decision:

- Keep the accepted canonical execution and define
  `CanonicalRMQChargedTraceCostAlgebra` with select-close, rank-close,
  endpoint-fringe, and interior-directory fields. Its whole-query expression
  is `2*select + (2*rank + 2*fringe + interior) + rank`.
- Use checked direct caps `select <= 13`, `rank <= 4`, and `fringe <= 4`.
- Tighten the physical interior by actual fixed-width chunk counts. On every
  size relevant to a cross-block middle query, relative cells occupy at most
  two words. When execution crosses a macro boundary, the structural fact
  `macroSize < blockCount` implies one-word relative cells. This gives local
  `<=18`, adjacent/left-middle `<=20`, cross-macro `<=30`, and uniform
  interior `<=30`.
- Set the paper-facing charged-trace cost to
  `2*13 + (2*4 + 2*4 + 30) + 4 = 76`. Retain `328` only under names containing
  `Transitional`; do not add work to preserve it.
- Define `WordRAM.TraceEvent.nonSyntheticWeight` directly on the actual emitted-event
  type as a certificate weight: payload reads and word-rank/select primitives
  have weight one, while the synthetic compatibility marker has weight zero.
  The name is deliberate. `TraceResult.toCosted` charges trace length and
  would count a synthetic marker if one were present; equality between
  `nonSyntheticWeight` and `Costed.cost` is proved only for the canonical
  no-synthetic whole-query trace. For that trace, prove genuine-event
  classification, no synthetic event, certificate weight sum equal to trace
  length, certificate weight sum equal to the `Costed` cost of the same
  execution, and the resulting bound by `76`.
- Keep controller dispatch, input/register access, arithmetic, branching,
  decoding, local scanning, candidate merging, trace assembly, and validity
  checking documentary and uncharged. They are not constructors of the current
  trace, so U3 does not make them a checked instruction inventory.
- Consume `76` through the actual global trace, supplied-store footprint
  transfer, final adequacy, ordinary-list API, headlines, paper root, examples,
  and axiom inventories. Preserve the U2 theorem and audit artifacts as
  historical evidence.

Rejected alternatives:

- Rename or re-document `328` without tightening its component inequalities.
- Preserve `328` with padding, decorative reads, or artificial controller
  events.
- Add a Ready/Active or numeric input-size activation threshold to obtain
  one-word fields.
- Swap in a new payload, alternate query execution, or semantic answer table.
- Introduce a parallel `CanonicalRMQCostOperation` type with hand-written
  charged and uncharged lists. Such a vocabulary is disconnected from the
  evaluator and can classify documentary controller work without proving that
  the accepted execution emits or simulates those operations. E1 must instead
  define its own richer instruction semantics and prove a simulation of the
  current execution.
- Keep the broader `chargedWeight` name for the direct `TraceEvent` certificate.
  It suggests the same semantics as `TraceResult.toCosted`, but `toCosted`
  charges full trace length and would count a synthetic compatibility marker.
  The narrower `nonSyntheticWeight` name records that equality to `Costed.cost`
  is a canonical no-synthetic theorem, not a general definition.
- Claim absolute optimality below `76` without a coexistence/lower-witness
  theorem. U3 proves the tight operation-wise compositional cap established by
  the current semantics, not global minimality among all correlated queries.
- Present `76` as conventional word-RAM time, serialized-payload query time, or
  preprocessing complexity.

Consequences:

The public constant is `76`; `328`, `4144`, `118`, and `196727` remain
transitional or compatibility/history. Exact modeled cost is the emitted trace
length. The direct `nonSyntheticWeight` certificate sum is checked equal to both
that length and the same `Costed` cost only because the canonical trace has no
synthetic marker. A synthetic event cannot satisfy the genuine classification
and would break the certificate-weight/length equality. Controller work remains
explicitly documentary and uncharged. E1 must define a fully charged small-step
machine and prove its simulation. M1 must still
connect querying to a serialized payload representation, and construction
work must still account for preprocessing.

Evidence:

- `GenericSelect.SparseExceptionSelectData.selectCosted_cost_le_thirteen`.
- `canonicalRelativeRmmRelativeWidth_le_machine_of_macroSize_lt_blockCount`.
- `canonicalRelativeRmmInteriorRangeMinCosted_cost_le_thirty_of_size_ge_four_of_bounded`.
- `canonicalLcaCloseCostedWithRankSeed_cost_le_principled`.
- `concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost_eq`.
- `concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_le_principledAllSizeChargedTrace`.
- `concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_eq_trace_length`.

## DD-20260714-008: make the paper topology name one canonical payload and execution

Status: Amended candidate complete on the W21 implementation branch; a fresh
blind exact-commit audit remains coordinator-owned.

Context:

The A05 blind report at `64cfd2dae2de9b8402fd5601b0e6d0b146a0ca61`
accepted the operational `76` derivation but rejected the publication topology.
`RMQPaper` still imported six unqualified direct/interpreted/leaf/word profiles
whose theorem types paired an older payload with differently executed queries
bounded by the legacy aggregate. Prose calling those results compatibility did
not prevent a reviewer from citing them as coequal paper capstones.

Decision:

- Prove
  `concreteBPNativeSuccinctRMQCanonicalReviewerPayload_globalWordTrace_two_sided_profile`.
  Its single checked type combines doubled-Catalan envelopes, the canonical
  reviewer payload bound, exact physical-word erasure to that payload, the
  canonical global trace, direct positional physical-word backing for every
  successful read, its literal `76` cost bound, non-synthetic certificate
  equality to both trace length and the same `Costed.cost`, and exact valid-query
  answers. These are conjuncts of the theorem's checked type, not nearby helper
  results.
- Expose that theorem as
  `Headlines.succinctRMQCanonicalReviewerPayloadGlobalWordTraceTwoSidedProfile`.
  Add `SuccinctClassic.queryCost = 76` directly to
  `listIntSuccinctRMQPaperMainTheorem`.
- Keep `RMQ.Headlines.RMQ` as the only RMQ module imported by `RMQPaper`.
  Remove the six historical aliases and the public transitional/regime cost
  aliases from that module.
- Create `RMQ.Headlines.RMQCompatibility`, imported explicitly only by the broad
  `RMQ.Headlines` barrel. Retained declarations in that module must contain
  `Legacy` or `Compatibility` in the public name.
- Preserve source theorems in their construction modules. The boundary is the
  curated alias and publication topology, not an attempt to hide transitively
  available Lean declarations.

Rejected alternatives:

- Keep the six aliases in the paper module and add stronger prose disclaimers.
- Point a new space theorem at the canonical payload while retaining query
  clauses over an older direct or size-premised execution.
- Delete or weaken the checked source theorems merely to make them unreachable.
- Import the compatibility module from `RMQPaper` and rely on alias spelling
  alone to signal which theorem is current.
- Rename the old direct profile as the new capstone without changing its
  checked payload/query objects.
- Claim that a combined capstone contains read backing or a weight equality
  merely because a neighboring theorem proves it.
- Treat removal from Lean aliases and selected claim rows as documentary
  migration closure without repository-wide old-name search and checked
  resolution of every documentary headline reference.
- Treat a mixed-role digest or audit-report directory as frozen history, or let
  an unvalidated marker word create an exception.

Consequences:

After `import RMQPaper`, the construction-facing, list-facing, adequacy, and
cost aliases all name the canonical reviewer payload and canonical global trace
whose actual non-synthetic event certificate equals the same modeled cost and
is bounded by `76`. Compatibility users retain the historical results through
the broad barrel, but no unqualified historical query capstone remains. This
does not strengthen the model boundary: controller operations remain uncharged,
and serialized-payload querying, preprocessing, and conventional word-RAM
complexity remain downstream obligations.

The documentary-history boundary is deliberately occurrence-level. Two dated
June snapshots retain one old spelling each through exact path, exact
case-sensitive marker-plus-line content, and an exactly-once check. The
README-linked current publication digest and audit reports receive no blanket
allowance and remain subject to headline resolution. This keeps historical
evidence readable without making directory placement or a forged marker a way
to reintroduce a current paper capstone.

Evidence:

- `concreteBPNativeSuccinctRMQCanonicalReviewerPayload_globalWordTrace_two_sided_profile`.
- `RMQ.Headlines.succinctRMQCanonicalReviewerPayloadGlobalWordTraceTwoSidedProfile`.
- `RMQ.Headlines.listIntSuccinctRMQPaperMainTheorem` and its `queryCost = 76`
  conjunct.
- `RMQ/Headlines/RMQCompatibility.lean` and the explicit compatibility import
  in `RMQ/Headlines.lean`.
- `scripts/paper_topology_lint.ps1`, its mutation regression, and the curated
  headline axiom inventory.

## DD-20260715-001: use one current digest and one compatibility history

Status: Accepted.
Date: 2026-07-15.
Scope: publication-facing exposition of the canonical succinct RMQ theorem.

Decision:

- `docs/digests/PROJECT_DIGESTION_CURRENT.md` is the sole current project
  digestion. Its undated name is stable across theorem improvements; Git
  history records prior versions.
- Detailed readiness, route-split, large-regime, zero-block, and superseded
  numeric chronology lives in
  `docs/digests/SUCCINCT_RMQ_COST_COMPATIBILITY_HISTORY.md`.
- Current reviewer documents state the canonical proposition directly: one
  reviewer payload, its exact physical erasure, one canonical global trace,
  exact valid answers, positional read backing, and charged-trace cost at most
  `76` under the explicit model boundary.
- Worker labels, candidate status, pending-audit notes, and branch names are
  development history. They do not belong in the current public theorem
  statement.

Rejected alternatives:

- Keep a dated file as the canonical current digest and replace it on each
  milestone.
- Repeat the full historical constant and route chronology in every trust,
  paper, and artifact document.
- Prefix unrelated documents with one identical canonical paragraph so that a
  lexical scan sees the desired proposition everywhere.
- Treat a document-role manifest or regular-expression classifier as evidence
  that English prose has the intended theorem semantics.

Consequences:

Reviewers encounter one current proposition and one explicitly non-current
history. The theorem map, model-adequacy note, trust packet, and artifact claim
packet retain distinct purposes rather than becoming copies of one another.
Automation remains useful for stale names and known wording hazards, but the
Lean theorem and theorem-directed review remain authoritative.

Publication-facing significance:

The paper can cite a stable current digest and move historical derivations to a
single appendix-style source. This makes the exposition easier to maintain and
prevents internal proof-campaign vocabulary from becoming part of the claimed
mathematical architecture.

Amendment after the A06 blind audit:

- A dated snapshot must be a separate historical document; it may not remain
  embedded as a second current narrative inside `docs/FAMILY_SUMMARY.md`.
- Canonical Lean comments use mathematical and interface terminology rather
  than worker or roadmap phase labels such as `W19` or `U3`.

This amendment keeps the source and publication exposition aligned: theorem
comments explain stable abstractions that a paper can name, while development
chronology remains recoverable from the decision log, audit reports, and Git
history.

## DD-20260717-C05-001: adopt the four-Russians charged route (Option B)

Date: 2026-07-17. Scope: cost model, charged instruction repertoire, table
region, E1 target amendment. Decided by: user + coordinator C05, on the
kernel-verified E1-01R3 obstruction (`e1R3FamiliarMachineTarget_obstruction`,
commit `7fe5b8b`) and the C05 architecture/velocity scouts (round log,
`AUDIT_AND_A_DESIGN.md`, 2026-07-17).

Decision: replace unit-cost `wordRank`/`wordSelect` and the event-silent
fringe min-excess extraction with charged lookups into o(n)-bit half-word
chunk tables, collapsing the charged event vocabulary to memory reads; state
the transdichotomous word-RAM model explicitly; freeze `76` as a historical
constant and derive a new literal. Full design and staging:
`docs/internal/OPTION_B_CHARGED_FRINGE_DESIGN.md`.

Alternatives rejected:
- Option A (charge word-level primitives incl. a word-min-excess instruction,
  keep the trace): minimal disruption, but a bespoke unit-cost min-excess
  primitive is exactly the precedent-free justification the project goal
  minimizes; retained only as the pivot fallback if B2 stalls (>1 week of
  repair rounds), with B1 tables as the primitives' realizability evidence.
- Shape-indexed or n-dependent total bounds: abandons the literal all-size
  bound and the constant-query headline.
- Constant-width blocks: breaks the o(n) summary overhead.
- Keeping the extraction event-silent while re-labeling the machine "fully
  charged": re-hides the scan E1 exists to expose; forbidden.

Consequences: new table sources in the reviewer store and `buildPayload`
(public space shape `<= 2n + o(n)` preserved); trace event vocabulary
collapses to `readWord` with uniform weight, simplifying the non-synthetic
certificate story; the accepted-route literal grows to an expected 150-250;
downstream provenance inductions regenerate mechanically; E1's familiar
machine becomes a standard {read, arithmetic, compare, branch} RAM and the
R3 obstruction remains valid evidence against the superseded contract only.

Publication significance: the paper's cost claim becomes chargeable end to
end in the standard succinct-data-structures model (Fischer-Heun precedent),
removing the largest reviewer-audit burden identified in the C05 roadmap
audit.

## DD-20260717-002: Charged fringe chunk geometry, packed table, and capped fold shape (B2 core)

Status: Proposed
Date: 2026-07-17
Scope: `RMQ/Core/SuccinctClose/RelativeRmmMacro/ChargedFringeChunks.lean`
(B1/B2 Option B core; worker B2-01, branch
`claude/b1-b2-charged-fringe-tables`).

Decision:

1. Chunk width `bpFringeChunkBits m = Nat.log2 m / 8 + 1` over the BP-code
   length `m` (the design doc's indicative `log2 n / 2 + 1` replaced by the
   `/8` sub-log scale of `RankSelectSpec.fixedWeightSubLogChunkBlockSize`).
2. Boundary handling by generalized mechanism 1 of
   `OPTION_B_CHARGED_FRINGE_DESIGN.md`: ONE table indexed by
   `(chunkValue v, startOff a, endOff b)` with `a, b <= c`, rows
   `2^c * (c+1)^2`, covering full chunks (`a=0, b=c`), partial first/last
   chunks, and short trailing slices uniformly; padding of short slices with
   `false` is proven harmless because reads only consult offsets
   `t <= slice.length` (`bpFringeChunkPattern_windowChunkValue_rankPrefix`).
3. Table field encoding: one packed `Nat` entry per row,
   `(deltaOffset * (2c+2) + rangeMinOffset) * (c+1) + rangeArgMin`, all
   excess fields offset-encoded by `+ c`, with proven mixed-radix unpack
   lemmas (`bpFringeChunkPacked_arg/_min/_delta`) and proven truncation-free
   offset characterization (`bpFringeChunkExcessOffsetAt_add_false`).
   Entry width `Nat.log2 (bpFringeChunkEntryBound c) + 1`.
4. Charged fold shape: one `FixedWidthNatTable.readCosted` (cost 1) per
   chunk, over exactly `Nat.min (relHi / c + 1) 33` chunks; the cap `33` is
   proven to be the identity on the reachable domain (window `<= 4`
   machine words `<= 32` chunks,
   `four_machineWordBits_le_32_mul_bpFringeChunkBits`) and makes the fringe
   read count a literal (`<= 37` including the 4 accepted window-word
   reads) for every argument with no size guard.

Context: the accepted endpoint fringe (`localBPLeft/RightFringeCandidate-
SeededCosted`, cost 4) computes its min-excess/argmin value by an
event-silent per-position scan; Option B replaces this with charged
four-Russians table lookups.

Options considered:

- `log2 n / 2 + 1` chunk width (design-doc default): 8 chunks/window and a
  smaller route literal, but the o(n) budget then needs a fresh
  sqrt-times-polylog product bound; rejected in favor of reusing the proven
  `/8` slack template (`fixedWeightSubLogChunkDenseDecoderBudget_littleO`).
  Revisit at B5 if the route literal matters.
- Separate delta/min/argmin tables (3 reads per chunk): simpler encodings
  but triples the read literal; rejected.
- Secondary `(value, offset)` boundary table plus a full-chunk table:
  two table shapes and a per-fringe case split; rejected as strictly more
  surface than the uniform `(v, a, b)` index.
- Machine-word chunked reads (`machineReadCosted`): entry width can exceed
  `machineWordBits m` only at tiny `m`, which would force a per-read chunk
  factor; deferred to the store-integration milestone where the reviewer
  word width (which absorbs the packed width at every size) is the declared
  machine word.

Rationale: minimize new proof surface by maximizing reuse of proven o(n)
slack; keep every charged read's decoded value flowing into the fold result
(REQ-B2-10); keep the read-count literal all-size with no dispatch.

Consequences: fringe cost constant becomes 37 (from 4); the whole-route
literal will grow accordingly at B5 re-derivation; table bits
`2^c * (c+1)^2 * width` must be folded into `overhead` (M5).

Evidence: `ChargedFringeChunks.lean` compiles clean at this commit;
key theorems `bpFringeChunkFold_eq_localBPSeeded`,
`bpChunkedLeft/RightFringeCandidateSeededCosted_value_eq`,
`bpChunkedLeft/RightFringeCandidateSeededCosted_cost_le` (<= 37),
`bpFringeChunkTable_corruption_changes_fringe_value`.

Follow-up: store region placement (reviewer source extension) and
buildPayload/overhead amendment recorded in a separate entry at the store
milestone; wiring/cost re-derivation at B5.

Supersedes: none (implements DD-20260717-001 direction).

## DD-20260717-003: Couple the reviewer-source extension and public payload amendment to the fringe wiring rung

Status: Proposed
Date: 2026-07-17
Scope: B2 store/space milestone (`ChargedFringeSpace.lean`,
`ChargedFringeSubstitution.lean`); reviewer store
(`RMQ/Core/SuccinctFinal/RAM/ReviewerPhysical.lean`) and public surface
(`RMQ/Core/SuccinctRMQClassic.lean`) unchanged on this branch.

Decision: the B2 core rung delivers the chunk-table store, erasure,
capacity-feed, word-width, o(n) budget, and the amended payload/overhead as
a committed CANDIDATE pair (`bpChunkedBuildPayloadCandidate`,
`bpChunkedOverheadCandidate`, with checked `2n + o(n)` shape), but does NOT
add the `ReviewerSource` constructor or swap the public
`buildPayload`/`overhead` definitions.  Both are coupled to the wiring rung
that makes the accepted execution actually read the table.

Context: the accepted public capstone conjunct
`concreteBPNativeSuccinctRMQCanonicalReviewerPayload (cartesianShape xs) =
buildPayload xs` is proved by `rfl` inside
`FlatPayloadStoreNoSyntheticExecutionStory`
(`SuccinctRMQClassic.lean:615/698`), and the reviewer manifest theorems
reject dead sources
(`concreteBPNativeSuccinctRMQReviewerManifest_add_dead_rejected`,
`ReviewerPhysical.lean:430`).  Amending the counted payload or the source
universe while the accepted execution performs no table read would either
falsify a checked public theorem or install exactly the dead counted region
the manifest layer is designed to reject.

Options considered:

- Amend `buildPayload` now and weaken the capstone conjunct: changes the
  public claim surface, which is B5 scope and not this worker's call;
  rejected.
- Add the `ReviewerSource` constructor now with a dead segment: breaks
  `canonical_segments_complete` (`segment < 21`) in
  `SuccinctFinalModelAdequacy` (anticipated B4 fallout) AND the live/dead
  manifest theorems in `ReviewerPhysical.lean`, i.e. more than the
  sanctioned adequacy breakage; rejected.
- Candidate-pair + coupling (chosen): everything the wiring rung needs is
  committed and checked (payload shape, o(n), erasure, per-source linear
  word count `<= 64*(n+1)`, word width `<=` reviewer word bits), and the
  accepted surface stays green.

Consequences: matrix rows REQ-B2-04/05/06 remain open at the
reviewer/public level with their component-level content closed; the
wiring successor performs (in one rung): TraceResult/WithStore chunked
fringe at a new segment, ReviewerSource extension + erasure/capacity fold
re-proof, public buildPayload/overhead swap, and cost-chain re-derivation.

Evidence: `ChargedFringeSpace.lean` theorems
(`bpFringeTableOverhead_littleO`, `bpChunkedBuildPayloadCandidate_length`,
`bpChunkedOverheadCandidate_littleO`, `bpFringeChunkRowCount_le_linear`,
`bpFringeChunkEntryWidth_le_reviewerWordBits`,
`bpFringeChunkTable_store_erases`); the `rfl` capstone conjunct at
`SuccinctRMQClassic.lean:698`.

Follow-up: coordinator to confirm the coupling or direct an in-rung
extension despite the public-surface breakage.

Supersedes: none (refines DD-20260717-002 follow-up).

## DD-20260717-004: Charged-fringe wiring swap, fringe segment 21, and route literal re-derivation (B2-02)

Status: Proposed
Date: 2026-07-17
Scope: B2-02 wiring milestone (branch `claude/b1-b2-charged-fringe-tables`):
`ChargedFringeWiring.lean` (new), `ChargedFringeTrace.lean`,
`ConcreteDirectoryRAM.lean`, `ConcreteDirectoryRAMStoreParam.lean`,
`Segments.lean`, `FlatPayload.lean`, `ReviewerPhysical.lean`,
`SuccinctFinalRAM.lean`, `SuccinctFinalStoreParam.lean`,
`SuccinctFinalModelAdequacy.lean`, `SuccinctFinalSemanticProvenanceAdequacy.lean`,
`ReviewerReachability(Small).lean`, `BPNavigationRAM.lean`,
`SuccinctRMQClassic.lean`, `Headlines/RMQ.lean`, `Validation/*`.

Decisions (executing coordinator ruling C05 — store extension coupled to the
wiring, every commit `lake build RMQ` green):

1. Dispatcher relocation, not in-place edit: the canonical dispatchers
   (`canonicalLcaCloseCostedWithRankSeed`,
   `lcaCloseTraceResultWithRankSeedAllSizeStructural(+WithStore)`) moved to
   the new downstream module `ChargedFringeWiring.lean` with their
   fully-qualified names unchanged, because their swapped cross-block branch
   consumes `bpChunkedCrossBlockClose*`, which lives below
   `ConcreteDirectoryRAM` in the import order.  The historical event-silent
   cross-block consumers (`canonicalCrossBlockCloseCostedWithRankSeed` and
   trace twins) remain untouched upstream and are still consumed by the
   substitution/exactness proofs.
2. Trace layer: the chunked fold is one `FlatStoreComputation` (interior
   component pattern), so store parametricity, footprint determinism, and
   read/store agreement are structural; the structural trace dispatcher
   gains one `fringeSegment : Nat` parameter (house `AtSegments` style).
3. Segment accounting (REQ-B2-17): fringe chunk table = global trace segment
   21 = reviewer logical segment 21; `ReviewerSource.fringeChunkTable`
   appended LAST so the amended reviewer payload is exactly
   `old payload ++ table payload` (the committed candidate shape); adequacy
   regenerated to `segment < 22` / tail-unreachable at `22 <=`; the
   dead-source anti-vacuity mutation witness moved from segment 21 to the
   new first dead segment 22.
4. Cost re-derivation (REQ-B2-15): `endpointFringe := 37` in the canonical
   algebra; derived route literal `wholeQuery = 2*13 + (2*4 + 2*37 + 30) + 4
   = 142` (checked by `rfl`, never asserted); every Lean consumer of 76
   re-proved at 142; 76 frozen as
   `concreteBPNativeSuccinctRMQSilentFringeChargedTraceCost(_eq)` /
   `SuccinctClassic.canonicalSilentFringeQueryCost_eq` following the
   `canonicalTransitionalQueryCost = 328` pattern.
5. The transitional close/LCA cap (`canonicalLcaCloseCostedWithRankSeed_cost_le`)
   now requires the genuine close-position bounds (the 2*37 fringe charge
   exceeds the old 8-tick slack; the interior principled bound 30 recovers
   the transitional constant: 2r + 104 <= 8 + 2r + 240).  The consumer proof
   derives the bounds from select exactness exactly as the principled path
   does.
6. Store-parametricity surface: `concreteBPNativeSuccinctRMQWholeQueryReadAgreement`
   gains a `fringeChunkTable` field (segment 21 agreement); the safe
   whole-query footprint (`segment <= 29`) already contains 21.
7. Provenance (REQ-B2-18): `ReviewerProducerReadPath` gains
   `lcaFringeLeft/lcaFringeRight` constructors carrying membership in the
   actual chunked fringe candidate component traces; the consumer-level
   `_trace_forall`s take candidate-trace-membership hypotheses so producer
   packets stay component-exact; the W19 successful-occurrence packet for
   the new source is witnessed by the existing increasing-length-16
   cross-block execution (every chunked fringe invocation performs at least
   one successful chunk-table read: visited slots are inside the stored row
   range).
8. BP close-navigation compatibility profile: its global store's legacy
   segment 21 (retired summary minRel alias, unread by the canonical trace)
   is remapped to the fringe chunk table, and its read-backing predicate
   gains the fringe component disjunct, keeping the navigation execution
   story green without weakening it.

Rationale: minimal-surface atomic swap per C05; the dead-source manifest
theorems and the `rfl` public capstone conjunct
(`reviewerPayload = buildPayload`) hold at every commit because the source,
the counted payload component, the store segment, and the executed reads all
land in the same commit.

Evidence: `lake build RMQ` green at the wiring commit; key theorems
`lcaCloseTraceResultWithRankSeedAllSizeStructural_refines`,
`canonicalLcaCloseCostedWithRankSeed_exact_of_query` (via
`bpChunkedCrossBlockCloseCostedWithRankSeed_value_eq`),
`concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost_eq : = 142`,
`concreteBPNativeSuccinctRMQSilentFringeChargedTraceCost_eq : = 76`,
extended `concreteBPNativeSuccinctRMQReviewerPhysicalWords_erases` /
`_length_le_capacity`, regenerated `ConcreteBPNativeSuccinctRMQFinalTraceModelAdequacy`.

Follow-up: full provenance audit pass (B4); prose/doc migration beyond
committed checks (B5).

Supersedes: none (executes DD-20260717-003's coupling under C05).

## DD-20260717-005: Chunked in-word rank/select recharge shape (B3 core)

Status: Proposed
Date: 2026-07-17
Scope: B3 rung (worker B3-01, branch `claude/b1-b2-charged-fringe-tables`,
base `d1d645e`): new modules
`RMQ/Core/SuccinctClose/RelativeRmmMacro/ChargedWordChunks.lean` and
`ChargedRankSelectLeaves.lean` (parallel layer); later-milestone swap
surface unchanged by this entry.

Decision:

1. In-word rank derives per-chunk popcounts from B2's EXISTING `(v, a, b)`
   fringe chunk table (segment 21) instead of a new popcount table: the
   entry at slot `(v, t, t)` has empty-range min field
   `bpFringeChunkExcessOffsetAt c v t = c + rankTrue(t) - rankFalse(t)`
   (empty-range argmin is `a`, so the min field at `a = b = t` is the
   prefix statistic itself), giving
   `rankTrue(t) = (minField + t - c) / 2` and
   `rankFalse(t) = t - rankTrue(t)`, both truncation-free by
   `bpFringeChunkExcessOffsetAt_add_false`.  One charged read per chunk.
2. The chunked in-word rank evaluator clamps the query offset to
   `effLimit = min limit word.length` and visits
   `min ((effLimit + c - 1) / c) 8` chunks, reading slot
   `(v_j, t_j, t_j)` with `t_j = min c (effLimit - j * c)`; the `8` cap is
   the identity on the reachable domain by the new lemma
   `machineWordBits m <= 8 * bpFringeChunkBits m` (same omega arithmetic
   as B2's 32-chunk window cap).  The clamp makes the evaluator agree with
   `RMQ.RAM.boolRankPrefix` (which also stops at the word end) without
   ever decoding `false` padding as data, so the universal value
   equivalence needs only `word.length <= 8 * c` — a hypothesis every
   accepted call site discharges from its structure's own
   `wordSize_le_machine` + `BoundedPayloadWordStore.word_length_le`.
3. In-word select is an early-exit fold: per chunk one existing-table read
   decodes the SLICE popcount `count_j` (same `(v_j, t_j, t_j)` slot with
   `t_j` = slice length); the routing branch `k < count_j` is decided by
   the decoded read; the containing chunk finishes with exactly one read
   of the NEW select table
   `bpChunkSelectTable c target : FixedWidthNatTable` (rows
   `2 ^ c * (c + 1)`, slot `v * (c + 1) + k`, entry = position of the k-th
   `target` bit of the c-bit pattern of `v`, sentinel `c` when absent).
   Because the routing count is the slice popcount, the selected position
   provably lies inside the slice (padding positions and sentinel entries
   unreachable on the honest route).  Read bound `8 + 1 = 9`.
4. The select table is stored once, instantiated at the route's
   `target = false` (the only select target on the accepted route), as
   reviewer/global segment 22, constructor appended last (B2 segment-21
   pattern; store extension coupled to the wiring swap per C05).
5. Leaf recharges keep the accepted evaluators' exact branch structure and
   replace only the word-primitive sub-computations:
   `bpChunkedRankCosted` (3 sample/word reads + rank fold, <= 11),
   `bpChunkedDenseTwoWordSelectCosted` (<= 27),
   `SparseExceptionDirectory.bpChunkedReadCosted` (<= 12),
   `SparseExceptionSelectData.bpChunkedSelectCosted` (<= 35).  Projected
   route literal `2*35 + (2*11 + 2*37 + 30) + 11 = 207`, DERIVED at the
   swap commit (the checked derivation wins).
6. Worklog: `B2_WORKLOG.md` stays frozen as the closed B2 record;
   B3 logs in `docs/internal/B3_WORKLOG.md` (the alternative rename to
   `B_WORKLOG.md` was rejected because the closed B2 matrix and ledger
   reference `B2_WORKLOG.md` by name and frozen rows may not be edited).

Context: B3 mission — eliminate the remaining `wordRank`/`wordSelect`
events from the accepted route (three `TwoLevelPayloadLiveStoredWordRankData`
rank seeds and the `denseTwoWordSelectCosted` leaf) so the charged
vocabulary collapses to `readWord` only.

Options considered:

- New popcount-per-chunk-value table (design doc's first suggestion):
  rejected — the existing `(v, a, b)` entries already determine every
  in-chunk prefix rank via the offset-encoded min field, so a new rank
  table would duplicate counted bits and add a second store region for
  zero proof savings.
- Adding a packed select field to the B2 entry (one table for both):
  rejected — a per-entry select answer needs the occurrence index `k` as
  input, so it cannot live in the `(v, a, b)` index without multiplying
  the row space by `(c+1)` anyway; widening the packed entry would also
  reopen the closed width-vs-reviewer-word rows (`bpFringeChunkEntryWidth`
  consumers) for no read-count gain.
- Select table indexed by `(target, v, k)` (both targets): rejected —
  the accepted route selects only `target = false`
  (`sparseExceptionSelectData shape.bpCode false`); the definition is
  target-generic, only the `false` instance is stored/counted.  A second
  instance can be appended as a further source if a future route needs it.
- Fixed non-clamped chunk count (`limit / c + 1` as in B2's fringe):
  rejected for rank in favor of the ceiling form — it avoids a guaranteed
  zero-information read when `c` divides the limit, and the select fold
  needs the ceiling form regardless (it scans the whole word).
- Reusing `Costed.tickValue` window packets for the sample reads:
  not applicable — the three rank sample reads are already genuine
  charged store reads in the accepted leaf; they are kept verbatim.

Rationale: minimal new counted bits (one small table), minimal new proof
surface (all decode lemmas reduce to B2's proven offset-encoding), exact
branch-structure mirroring so every value-equivalence proof is a local
leaf substitution under the accepted route's own hypotheses.

Consequences: route literal grows to the derived value (projection 207);
segment universe grows to 23 segments (0-22) at the swap milestone; the
B5 chunk-scale revisit can shrink both fringe and rank/select literals
together.

Evidence: matrix rows REQ-B3-01..14 (frozen this commit); implementation
evidence accrues in `B3_WORKLOG.md` per milestone.

Follow-up: swap-milestone entry (segment 22 placement, cost re-derivation,
vocabulary theorem naming) at M5, following the DD-20260717-004 pattern.

Supersedes: none (extends DD-20260717-002/-004 to the rank/select leaves).

## DD-20260718-001: Leaf trace twins retire the register-program presentation at the recharged sites (B3 M4b)

Status: Proposed
Date: 2026-07-18
Scope: B3 rung (worker B3-02, branch `claude/b1-b2-charged-fringe-tables`):
new module
`RMQ/Core/SuccinctClose/RelativeRmmMacro/ChargedRankSelectLeafTrace.lean`
(parallel layer; accepted evaluators untouched).

Decision:

1. The chunked leaf trace twins are store-parametric (`WithStore`) direct
   read-atom evaluators, not relabeled register programs: each accepted
   sample/word read is one `readWord segment slot` event of the supplied
   store emitted by `bpChunkReadTraceResult` (decoded table read) or the
   new `bpWordReadTraceResult` (raw packed-word read), followed by the
   M4a chunk folds at the caller's chunk/select-table segments.  The
   `NatProgram.twoLevelSampledRank` register presentation is retired at
   exactly the five recharged sites (the option B3-01 recorded in the
   worklog); the instruction itself and every legacy consumer stay
   defined and untouched (REQ-B3-04).
2. Segment parameterization: the rank-seed twin takes four explicit
   segments (`superSegment blockSegment wordSegment chunkSegment`); the
   directory and select twins consume the accepted
   `SparseExceptionDirectoryTraceSegmentBases` /
   `SparseExceptionSelectTraceSegmentLayout` records (rank sample
   segments = `rankBase`, `rankBase + 1`, `rankBase + 2`, matching the
   accepted `tripleSegmentMap` images) plus `chunkSegment` and
   `selectTableSegment` arguments, so the M5 instantiation is the house
   layout extended by the global chunk segment 21 and the new select
   segment 22 with no relabeling step.
3. The unchanged four-field super/local entry-table reads reuse the
   accepted `readTraceResultRelabeledWithStore` evaluators verbatim (no
   sibling read path); their refinement chains through the existing
   `_eq_of_pullback` + `_refines_interpretedCosted` +
   `readInterpretedCosted_refines_readCosted` lemmas.
4. The dense twin keeps the `bitWords` parameter as the statement-level
   name of the counted component store (its word segment must agree with
   `bitWords.store.words` in every refinement lemma) even though the
   executed reads are genuine reads of the supplied store; the unused
   binder is linter-silenced at the definition only.

Options considered:

- Relabeled register programs (`ofNatProgramWithStore` +
  `tripleSegmentMap`, the accepted presentation): rejected for the
  recharged sites — the register instruction emits the `wordRank` event
  the B3 mission removes, so the twin would need a new instruction
  anyway; direct atoms make `_matchesReadStore` and the vocabulary
  induction definitionally `readWord`-shaped.
- A new register instruction (`twoLevelChunkedRank`): rejected — it
  would extend the `Program`/`NatProgram` universe (public-surface
  churn) for zero proof gain; the data-dependent chunk addressing is
  exactly what `bpChunkReadTraceResult` already generalizes.
- Re-implementing the four-field entry-table reads as direct atoms:
  rejected — those reads are not recharged by B3; reusing the accepted
  evaluators keeps the super/local read paths literally identical to the
  accepted route (no sibling).

Rationale: every event of every twin is a genuine `readWord` of the
supplied store, so the REQ-B3-10 vocabulary theorem becomes a uniform
`_trace_forall` instance; refinement (`_toCosted_of_agree`) lands on the
M3 Costed twins under agreement hypotheses that the canonical global
store discharges segment-by-segment.

Consequences: M5 wires the route trace twins to these evaluators at the
house layout + segments 21/22 and discharges the agreement hypotheses
from `concreteBPNativeSuccinctRMQGlobalReadStore` facts; the
`_store_parametric` surface feeds the StoreParam determinism layer.

Evidence: `ChargedRankSelectLeafTrace.lean` (this commit), ledger entry
M4b in `B3_WORKLOG.md`.

Follow-up: none beyond the M5 entry already queued by DD-20260717-005.

Supersedes: none (implements the M4b plan of DD-20260717-005).

## DD-20260718-002: M5 atomic swap - chunked rank/select consumers, Register legacy split, segment-22 store extension (B3 M5)

Status: Proposed
Date: 2026-07-18
Scope: B3 rung (workers B3-03/B3-04, branch
`claude/b1-b2-charged-fringe-tables`): the M5 atomic swap commit
(`SuccinctFinalRAM.lean`, `SuccinctFinalStoreParam.lean`,
`Segments.lean`, `ReviewerPhysical.lean`, `FlatPayload.lean`,
`ChargedRankSelectWiring.lean`, `BPNavigationRAM.lean`, reviewer
reachability witnesses, adequacy modules, public/doc sync).

Decision:

1. Swap points: `concreteBPNativeSelectCloseInterpretedCosted` /
   `concreteBPNativeRankCloseInterpretedCosted` are redefined to the
   M5-prep chunked Costed consumers; the Global/AtSegment word-trace
   twins are redefined to the M4b chunked WithStore trace twins at the
   canonical store (select) and at the base-parameterized seed store
   with chunk segment at `base + 4` (rank; canonical base `17` lands the
   chunk reads on the counted segment `21`).
2. Register legacy split (REQ-B3-04): the retired register evaluators
   stay defined under NEW names
   (`concreteBPNativeSelectCloseRegisterInterpretedCosted`,
   `concreteBPNativeRankCloseRegisterInterpretedCosted`, Register trace
   twins), and the pre-canonical compatibility chain
   (`WholeQueryInstr.eval*`, legacy LCA replays, legacy-store matches,
   the `_refines_*CloseCosted` bridges) is rewired to the Register
   names, so the axiom-pinned legacy lattice keeps its statements
   verbatim while the canonical route consumes the chunked consumers via
   the NEW `concreteBPNative{Select,Rank}CloseInterpretedCosted_exact`.
3. Store extension (C05 coupling): `ReviewerSource.selectChunkTable` is
   appended as constructor/segment `22` in the same commit as the
   wiring; the dead-source witness moves to `23` at identical strength;
   reviewer payload gains `(bpChunkSelectTable c false).payload`
   appended last; the read-agreement record
   (`concreteBPNativeSuccinctRMQWholeQueryReadAgreement`) gains a
   `selectChunkTable` field.
4. StoreParam re-agreement architecture: the WithStore leaves are
   redefined to the chunked twins; `concreteBPNativeRankCloseSegmentMap`
   gains `| 3 => base + 4`; the `_eq_of_trace_read_agreement` chain is
   re-proved via compositional `StoreTraceLocal` lemmas over the chunked
   folds (bind/map combinators; no per-theorem trace inductions); the
   now-false register pullback lemma and the dead private select
   pullback section are deleted (their only consumers were the retired
   `_globalReadStore` proofs).
5. Reviewer reachability witnesses are recomputed over the chunked
   trace with a kernel-safety pattern: every defeq-heavy step (sample
   word existence, chunked rank value at slot 0, component membership
   lifts) is proven ONCE as a generic lemma over symbolic structures and
   instantiated at the huge symbolic shapes propositionally (the
   concrete-shape defeq route deep-recursed the kernel at the 2^128
   sparse witness).  The NEW segment-22 W19 witness is the singleton
   execution's dense route: word `[true, false]`, chunk bits `1`, the
   in-word select fold's found branch fires a SUCCESSFUL segment-22
   read (`reviewerSingleton_selectChunkTable_successful_read`).
6. BP close-navigation profile: the nav rank leg is rewired to the
   chunked consumer (nav store segments `21`/`22` carry the chunk/select
   tables, so the chunked cost semantics is the matching one); the
   B2-era bridge
   `concreteBPCloseNavigationRankCloseInterpretedCosted_refines_rankCloseCosted`
   is deleted as superseded (its equality is false against the chunked
   consumer; B2-deletion precedent), and
   `concreteBPCloseNavigationCanonicalCosted`'s rank component becomes
   `concreteBPNativeRankCloseInterpretedCosted`.
7. Cost algebra: `selectClose := 35`, `rankClose := 11`; the route
   literal is DERIVED by `rfl`
   (`concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost_eq =
   207`, projection `2*35 + (2*11 + 2*37 + 30) + 11`); `142` is frozen
   as `concreteBPNativeSuccinctRMQSilentWordRankSelectChargedTraceCost`
   (public abbrev `canonicalSilentWordRankSelectQueryCost`) following
   the 76/328 pattern; `nonSyntheticWeight_sum_le_142` renamed
   `_le_207`; headline abbrev `SumLe142` renamed `SumLe207`
   (coordinator-ratified current-anchor rename); NEW paper-facing
   vocabulary abbrev
   `succinctRMQWholeQueryGlobalWordTraceResultReadWordOnly` for
   `concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_readWord_only`.

Options considered:

- Keeping the old bridge statements over the swapped names (rejected:
  the Costed equalities against the register reference evaluators are
  false at the chunked costs; restating over Register names preserves
  the frozen statements verbatim).
- Deleting the register evaluators outright (rejected: REQ-B3-04 keeps
  the word-primitive instructions and their consumers defined).
- Proving the reviewer witnesses by concrete-shape defeq (rejected
  empirically: kernel deep recursion at the symbolic 2^128/2^15
  shapes; the generic-lemma instantiation pattern is kernel-cheap and
  reusable).
- A nav-profile-specific chunked reference evaluator (rejected: the
  canonical chunked interpreted consumer is definitionally the cost
  semantics the nav store executes; a sibling evaluator would duplicate
  the algebra).

Rationale: C05 atomicity (store extension coupled to wiring, library
green at the single swap commit); the checked derivation `207` wins
over the projection; every closed B2 row's evidence object is untouched
or restated over the Register names at identical strength.

Consequences: M6 battery runs on the candidate tree; matrix rows
REQ-B3-04/06/07/08/09/10/14 close against this commit; the
`B3_M5_WIP.patch` recovery file is deleted in the bookkeeping commit.

Evidence: the M5 swap commit (this tree), `B3_WORKLOG.md` M5 ledger.

Follow-up: none queued beyond B5 doc migration (out of scope per
REQ-B3-13).

Supersedes: none (implements the M5 plan of DD-20260717-005 /
DD-20260718-001).

## DD-20260718-003: B4 provenance-hardening shape (packet extension, per-leaf segment-21 claims, positional repeated-read witnesses)

Status: Proposed
Date: 2026-07-18
Scope: B4 rung (worker B4-01, branch `claude/b1-b2-charged-fringe-tables`,
base `6e105a5`): provenance hardening over the B2/B3 charged-table route.
Matrix rows REQ-B4-01..10 frozen this commit.

Decision:

1. Worklog: `B3_WORKLOG.md` stays frozen as the closed B3 record; B4 logs
   in `docs/internal/B4_WORKLOG.md` (mirrors the DD-20260717-005 item-6
   precedent; the closed B3 rows reference `B3_WORKLOG.md` by name and
   frozen rows may not be edited).
2. W19 hardening extends the EXISTING packets, never siblings: named
   per-segment corollaries for segments 21/22 are derived from
   `concreteBPNativeSuccinctRMQWholeQueryOccurrenceProvenance_checked`;
   the repeated-equal-read witnesses and the segment-21 per-leaf claims
   land as NEW fields of
   `ConcreteBPNativeSuccinctRMQReviewerManifestSemanticAdequacy` (the
   query-independent packet consumed by the paper chain), whose record
   construction is regenerated in the same commit.  Alternative (a
   standalone `B4ProvenancePacket` record): rejected - the delegation
   contract forbids sibling packets and the paper chain already consumes
   the manifest packet once, without a `ValidRange` premise.
3. Segment-21 multi-consumer accounting: segment 21 is operationally read
   by all three `ReviewerReadLeaf`s (select leg chunk pops, rank leg chunk
   segment `base + 4 = 21`, LCA fringe candidates).  Close the gap with
   `forall leaf : ReviewerReadLeaf,
   (ReviewerProducerClaim.mk 21 leaf).HasSuccessfulClosedValidOccurrence`
   using the SAME predicate as accepted sources.  The compat single-labels
   (`SegmentLeaf? 21 = some .canonicalClose`, `consumer? .fringeChunkTable
   = some .canonicalClose`) are kept UNCHANGED (closed B2/B3 rows record
   them) and documented with a caveat comment mirroring the segments-17-19
   note.  Alternative (re-label `consumer? := none` + a shared-consumer
   structure like `ReviewerSharedBPConsumer`): rejected - it would edit
   evidence objects of closed rows (REQ-B2-04) and the house treats
   `consumer?` as a primary-consumer compat label with a documented
   multi-reader caveat (the 17-19 precedent).
4. Repeated-equal-read witnesses are POSITIONAL (indexed `getElem?` at two
   distinct whole-trace positions with the composed-trace offset
   decomposition), obtained on the singleton query `[7], 0, 1` whose two
   select-close instruction occurrences run at the same index; receipts
   via `repeated_equal_read_occurrences_have_distinct_receipts`.
   Alternative (membership-only or compiled `#guard` evidence): rejected -
   the completion gate's provenance-information-preservation clause
   requires occurrence-level position retention, and `#guard` is compiled
   evaluation, not kernel evidence.
5. Chunk-width corners and the direct o(n) theorem are stated over the
   actual stored-table payload lengths (transported along the
   `_payload_length` equalities) with the `LittleOLinear.add` witness
   exhibited; small-size numerals go through the log2 house pattern
   (`simp [Nat.log2]` / sandwich) because kernel `decide` cannot reduce
   `Nat.log2` (M2 ledger, re-verified).
6. Bookkeeping renames: `concreteBPNativeSelectCloseInterpretedCosted_cost_le_thirteen`
   -> `concreteBPNativeSelectCloseRegisterInterpretedCosted_cost_le_thirteen`,
   `concreteBPNativeRankCloseInterpretedCosted_cost_le_four` ->
   `concreteBPNativeRankCloseRegisterInterpretedCosted_cost_le_four`
   (both bound the RETIRED Register evaluators; repo-wide grep found zero
   consumers and no frozen-registry hits, so direct rename without alias;
   the delegation's alias fallback is not needed).
7. Navigation (REQ-B4-08): audit outcome recorded in the matrix row - no
   inconsistent statements; repair = `docs/BP_NAVIGATION_FRONTIER.md`
   stale-line sync plus an explicit quarantine note that the nav PROFILE
   (over `concreteBPCloseNavigationCosted`) and the nav EXECUTION STORIES
   (over `concreteBPCloseNavigationCanonicalCosted`) are distinct cost
   models with no registered bridge after the B3 deletion, and that the
   chunk tables the stories read at segments 21/22 are counted by the
   reviewer route, not the nav profile overhead.  Alternative (building
   the missing nav-side counted-space bridge now): rejected as out of the
   B4 contract; recorded as frontier work.

Context: B4 mission (delegation prompt) - provenance-hardening pass over
the new charged-table route; matrix REQ-B4-01..10.

Rationale: minimal surface, maximal reuse of the checked generic W19
machinery; every new claim uses predicates already consumed by the paper
chain, so P = Q by identity for the mutation rows.

Consequences: manifest packet type gains fields (strengthening; statement
name and headline alias unchanged); no route code, store, or constant
changes in this rung.

Evidence: matrix rows REQ-B4-01..10 (frozen this commit); implementation
evidence accrues in `B4_WORKLOG.md` per milestone.

Follow-up: M2..M8 per the worklog milestone list.

Supersedes: none (extends the B2/B3 provenance rows to the B4 standard).

## DD-20260718-004: Navigation-family B4 audit outcome - doc repair plus explicit cost-model quarantine (REQ-B4-08)

Status: Proposed
Date: 2026-07-18
Scope: B4 rung (worker B4-01): `docs/BP_NAVIGATION_FRONTIER.md` repair;
no Lean statement changes.

Decision: the B4 navigation audit (statement-level diff `d1d645e..6e105a5`
over `BPNavigationRAM.lean`/`BPNavigationPublic.lean`, nav store segment-map
inventory, repo-wide greps for the deleted bridge and `maxRelTable`
segment-numbering survivors) found NO inconsistent statement: no registered
navigation execution story changed statement text, and no nav theorem counts
a region its store cannot read (the profile's counted padding is deliberate
slack; all counted close bits are readable via segment 20, with aliases at
23-25).  Two findings require action, both documentary:

1. STALE-DOC: `docs/BP_NAVIGATION_FRONTIER.md` described the execution
   stories as being about `concreteBPCloseNavigationCosted` and "the same
   concrete close-navigation query surface as the profile" - true when the
   doc was snapshotted (2026-07-01, verified at a342555) but false after
   the B3 rank-leg rewire.  Repaired: the story paragraph now names
   `concreteBPCloseNavigationCanonicalCosted` and the chunk-table store
   segments 21/22.
2. QUARANTINE: after the B3 deletion of
   `concreteBPCloseNavigationRankCloseInterpretedCosted_refines_rankCloseCosted`
   (equality false at chunked costs, DD-20260718-002), the nav PROFILE and
   the nav EXECUTION STORIES are two different cost models with no
   registered bridge, and the profile's `2*n + o(n)` payload does not count
   the chunk tables the stories' store serves at segments 21/22 (that
   counted budget lives on the reviewer route).  Recorded as an explicit
   QUARANTINE NOTE in the doc rather than repaired in Lean.

Options considered:

- Build the missing nav-side counted-space statement / cost-model bridge
  now: rejected as outside the B4 contract (provenance hardening); recorded
  as open frontier work in the doc's quarantine note.
- Retire the old profile: rejected - it is a registered public surface
  (`RMQ.Headlines.concreteBPCloseNavigationProfile`) and its statements
  remain true about its own query.
- Silence (doc-only staleness left in place): rejected - REQ-B4-08 requires
  repair or explicit quarantine with docs + DD.

Evidence: B4 session audit (findings recorded in the REQ-B4-08 matrix row
and `B4_WORKLOG.md`); repaired doc sections in `BP_NAVIGATION_FRONTIER.md`.

Follow-up: nav-side counted-space statement for the chunked story is
frontier work (doc note); no Lean follow-up queued in B4.

Supersedes: none (records the REQ-B4-08 audit disposition).

## DD-20260718-005: E1 amended-machine ISA and instruction encoding (E1-R4 M2)

Date: 2026-07-18. Scope: E1 familiar small-step machine instruction set,
operand encoding, charge categories. Decided by: worker E1-R4 under the
amended E1 contract (DD-20260717-C05-001; frozen matrix
`E1_AMENDED_MACHINE_ACCEPTANCE_MATRIX.md` REQ-E1-01/02/06).

Decision: `RMQ.WordRAM.E1Machine` (`RMQ/Core/WordRAM/E1Machine.lean`)
defines the machine with exactly twelve instruction constructors:
`readMem dst segment addrReg`, `const`, `move`, `add`, `sub`,
`mulConst dst src k`, `divConst dst src k`, `natLt`, `natLe`, `natEq`,
`brNZ cond target` (absolute target), `halt`.

- ISA inventory outcome: general register-by-register `mul`/`div`/`mod`
  are EXCLUDED. Every multiplier/divisor in the accepted route's address
  and decode arithmetic is a per-shape program constant (chunk width `c`,
  mixed radices `c + 1` / `2c + 1`, block sizes, strides, region bases),
  so constant-operand `mulConst`/`divConst` suffice; `x % k` compiles as
  `x - (x / k) * k` (three constant-form instructions). The old R3
  machine's composite constructors (`localBPWindow`, `wordRank`,
  `wordSelect`, `sparseSpan`, `candidateOfSummary`, typed option/word
  register banks) are deliberately absent - that granularity was the
  refuted defect.
- Read decode: one bounded expression `decodeRead` - a missing word
  decodes to `0`, a stored word to `bitsToNatLE word + 1`, so success is
  testable by one register comparison and no separate option channel or
  typed register bank exists. The raw `Option Word` is logged in the
  `readWord` trace event unchanged (receipt projection stays comparable
  with the accepted trace positionally).
- Charge categories (frozen, six): memoryRead, registerWrite (const/
  move), arithmetic (add/sub/mulConst/divConst), comparison (natLt/
  natLe/natEq), branch (brNZ), control (halt). Checked accounting:
  `run_steps_eq_catLog_length`, `catCount_partition`,
  `run_steps_eq_category_sum`, `run_readLog_length_eq_memoryRead_count`.
- Width accounting: `Instr.FieldsFit` is a constructor-exhaustive match
  (no wildcard arm); every encoded field (register ids, segment numbers,
  immediates, mul/div constants, branch targets) must be `< 2 ^ w`,
  divisors additionally positive; per-constructor oversizing rejection
  witnesses are kernel-checked (`fieldsFit_rejects_*`).

Alternatives rejected: typed register banks (re-imports the R3 macro
shape); relative branch offsets (absolute targets make program
concatenation lemmas simpler and the width bound is the same); a
separate read-success flag register written by `readMem` (two register
writes per instruction complicates one-write-per-step accounting; the
`+1` shift achieves the same with one write); general `mul`/`div`
(unneeded per inventory, and constant-only forms keep the
decode-hiding audit trivial).

Consequences: the fueled `run` is the only recursion; one step = one
category tick = at most one read event, checked. The program
representation and per-shape program-generation decision is deferred to
the E1 M3 DD entry.

Supersedes: the R3 machine ISA (rejected by the E1-01R3 obstruction
round; see DD-20260717-C05-001).
