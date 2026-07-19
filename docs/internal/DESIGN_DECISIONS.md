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

Decisions (executing coordinator ruling C05 â€” store extension coupled to the
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
   equivalence needs only `word.length <= 8 * c` â€” a hypothesis every
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

Context: B3 mission â€” eliminate the remaining `wordRank`/`wordSelect`
events from the accepted route (three `TwoLevelPayloadLiveStoredWordRankData`
rank seeds and the `denseTwoWordSelectCosted` leaf) so the charged
vocabulary collapses to `readWord` only.

Options considered:

- New popcount-per-chunk-value table (design doc's first suggestion):
  rejected â€” the existing `(v, a, b)` entries already determine every
  in-chunk prefix rank via the offset-encoded min field, so a new rank
  table would duplicate counted bits and add a second store region for
  zero proof savings.
- Adding a packed select field to the B2 entry (one table for both):
  rejected â€” a per-entry select answer needs the occurrence index `k` as
  input, so it cannot live in the `(v, a, b)` index without multiplying
  the row space by `(c+1)` anyway; widening the packed entry would also
  reopen the closed width-vs-reviewer-word rows (`bpFringeChunkEntryWidth`
  consumers) for no read-count gain.
- Select table indexed by `(target, v, k)` (both targets): rejected â€”
  the accepted route selects only `target = false`
  (`sparseExceptionSelectData shape.bpCode false`); the definition is
  target-generic, only the `false` instance is stored/counted.  A second
  instance can be appended as a further source if a future route needs it.
- Fixed non-clamped chunk count (`limit / c + 1` as in B2's fringe):
  rejected for rank in favor of the ceiling form â€” it avoids a guaranteed
  zero-information read when `c` divides the limit, and the select fold
  needs the ceiling form regardless (it scans the whole word).
- Reusing `Costed.tickValue` window packets for the sample reads:
  not applicable â€” the three rank sample reads are already genuine
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
  recharged sites â€” the register instruction emits the `wordRank` event
  the B3 mission removes, so the twin would need a new instruction
  anyway; direct atoms make `_matchesReadStore` and the vocabulary
  induction definitionally `readWord`-shaped.
- A new register instruction (`twoLevelChunkedRank`): rejected â€” it
  would extend the `Program`/`NatProgram` universe (public-surface
  churn) for zero proof gain; the data-dependent chunk addressing is
  exactly what `bpChunkReadTraceResult` already generalizes.
- Re-implementing the four-field entry-table reads as direct atoms:
  rejected â€” those reads are not recharged by B3; reusing the accepted
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

## DD-20260718-006: E1 query register map, packet encoding, program skeleton (E1-R4 M3b)

Date: 2026-07-18. Scope: E1 whole-query program representation - register
map, output packet convention, guard/exit layout. Decided by: worker
E1-R4b under the amended E1 contract (frozen matrix
`E1_AMENDED_MACHINE_ACCEPTANCE_MATRIX.md` REQ-E1-03/05; completes the
program-representation decision deferred by DD-20260718-005).

Decision (`RMQ/Core/WordRAM/E1QueryProgram.lean`, namespace
`RMQ.WordRAM.E1Query`):

- Frozen register map: `regLeft = 0` / `regRight = 1` (query operands,
  loaded by `initialRegs`/`initialState` before execution), `regOut = 2`
  (answer packet), `regZero = 3` (pinned zero), `regN = 4` (per-shape
  size constant), `regT1/regT2/regG = 5/6/7` (guard scratch);
  `firstComponentReg = 8` reserves everything upward for valid-path
  component blocks.
- Output packet: option shift, `decodePacket` - `0` decodes to `none`,
  `v + 1` to `some v` - the SAME convention as the machine's
  `decodeRead`, so option tests anywhere in the machine are ordinary
  register comparisons against zero and no typed option channel exists.
- Program representation: a concrete program is
  `programSkeleton n validPath = guardBlock n (8 + validPath.length) ++
  (validPath ++ invalidExitBlock)`. The charged guard prologue (8
  instructions) sits at base `0`; the valid path at base `8`; the
  two-instruction invalid exit at base `8 + validPath.length`, reachable
  ONLY through the guard's two `brNZ` branches (the valid path
  terminates by writing `regOut` and halting, never falling through).
  Branch targets are absolute (DD-20260718-005); generators receive
  explicit bases, with hosting facts provided by
  `programSkeleton_hosts_guardBlock/_hosts_validPath/_hosts_invalidExit`.
- The guard is computed by machine instructions on the input registers
  (natLt/natLe against `regN`, natEq negations against `regZero`, brNZ),
  so invalid rejection charges the frozen categories: exact logs
  `guardRejectRangeCats` (8 steps) / `guardRejectBoundsCats` (10 steps),
  zero memory reads, empty receipt log
  (`guard_reject_of_not_lt`, `guard_reject_of_out_of_bounds`,
  `guard_reject_of_invalid`). Public parity with
  `SuccinctClassic.queryCosted_invalid` is checked in
  `RMQ/Core/WordRAM/E1QueryBridge.lean`
  (`programSkeleton_invalid_matches_public_guard` and the
  empty/reversed/out-of-bounds specializations), REQ-E1-05's machine
  half; the guard lemmas are stated against any hosting program via
  `HostedAt`, so they survive valid-path landing unchanged.
- Width: `guardBlock_fits`/`invalidExitBlock_fits`/`programSkeleton_fits`
  give the constructor-exhaustive REQ-E1-02 certificate for the skeleton,
  with hypotheses `n < 2^w`, `8 + validPath.length < 2^w`, `8 <= 2^w`
  discharged at the reviewer width once the concrete valid path exists
  (`concreteBPNativeSuccinctRMQReviewerInputOperand_fits` covers `n`).

Alternatives rejected: a meta-level Lean `if` guard around an unguarded
machine (explicitly fails the REQ-E1-05 anti-vacuity challenge - the
guard must charge machine steps); a dedicated `some?` flag register per
optional value (doubles register writes and re-imports the typed option
banks rejected in DD-20260718-005); placing the invalid exit between
guard and valid path (would require an unconditional jump over it, which
the ISA deliberately lacks - `brNZ` on a pinned nonzero register would
charge a spurious branch on every valid query); per-query program
generation depending on `left`/`right` (the program must be per-shape
only, with operands in registers, or result agreement would be trivial).

Consequences: valid-path component generators emit blocks at explicit
bases `>= 8`, use registers `>= firstComponentReg`, and compose by
`RunsTo.trans`/`HostedAt.append_*`; the invalid path is closed and its
category algebra is already literal.

## DD-20260718-007: E1 select-close dispatch extension register bank and entry-field encoding (E1-R4 M3c-5a)

Date: 2026-07-18. Scope: E1 select-close dispatch state representation -
the register bank that survives hosted component folds, and the machine
encoding of optional entry-table fields. Decided by: worker E1-R4f under
the amended E1 contract (frozen matrix
`E1_AMENDED_MACHINE_ACCEPTANCE_MATRIX.md` REQ-E1-01/02/03/04; completes
the register-allocation decision flagged in the E1 worklog resume point).

Decision (`RMQ/Core/WordRAM/E1SelectBridge.lean`, namespace
`RMQ.WordRAM.E1SelectBridge`):

- Frozen EXTENSION BANK `28..39` for select-close dispatch state that
  must survive the hosted component folds: `xIdx/xQ = 28/29` (query
  occurrence index and occurrence `q`), super entry fields
  `xSF1..xSF4 = 30..33` (`baseOccurrence`/`baseWordIndex`/`rankBefore`/
  `firstOffset`), local entry fields `xLF1..xLF4 = 34..37`,
  `xBPos/xBOcc = 38/39` (branch base position/occurrence).  Rationale:
  the component bank `8..27` is fully owned by the rank/select folds;
  every fold preservation theorem in the tree covers `28 <= r`
  (`rankCloseBlock_runsTo_hit`/`rankTrueCloseBlock_runsTo_hit`:
  `r <= 8 âˆ¨ 28 <= r`; `rankFalseLoopFold_runsTo`/
  `rankAtSegmentBlock_runsTo` and `selectFoldBlock_runsTo`: write-set
  complements including `28 <= r`), so extension-bank state survives
  every hosted fold without new preservation obligations.
- Entry-table fields are stored in registers under the SHIFTED
  `decodeRead` encode (`0` = missing field, `field + 1` = present),
  identical to the machine's read decode and the query packet convention
  (DD-20260718-005/-006).  None-propagation is the miss-indicator sum
  (`const`/`natEq`/`add` chain, zero iff all four field reads succeeded,
  `missSum_eq_zero_iff`) and the marked test
  (`relativeSplitSelectEntryIsMarked`) is an ordinary nonzero test on
  the shifted `rankBefore` register minus one
  (`relativeSplitSelectEntryIsMarked_iff`).
- The entry-table 4-read sub-block (`entryReadBlock`) takes its FIELD
  DESTINATION registers as parameters (side conditions `28 <= F`,
  pairwise distinct) so one block and one simulation theorem
  (`entryReadBlock_runsTo`) serve both the super instantiation
  (`30..33`) and the local instantiation (`34..37`); the slot index
  arrives in `rP` (component bank, computed by the dispatch immediately
  before the reads and not required to survive folds), scratch is
  `rT/rA/rB`, and the relative-offset read sub-block
  (`relativeReadBlock`) assembles its answer packet from `xBPos` under
  the `decodePacket` convention.

Alternatives rejected: cloning the 4-read block per table (two more
60-line simulation proofs with no semantic difference); a packed
single-register entry encode (would need shifts/masks by non-constant
amounts and re-imports multi-field decode complexity the ISA forbids);
holding dispatch state in the component bank with per-fold save/restore
moves (charges spurious register writes and breaks the frozen fold
category logs); an unshifted field encode with a separate presence flag
register per field (doubles the bank footprint; rejected for the same
reason as the typed option channels in DD-20260718-005).

Consequences: the select-close dispatch block (worklog RESUME step 5)
keeps `idx`/`q`/entry fields/base position/base occurrence in `28..39`
across the seeded TRUE rank folds, the atomic FALSE folds, and the select
fold; the accepted entry-table read trace/value reduce definitionally to
the machine shapes (`entryRead_trace_eq`/`entryRead_value_eq`,
`relativeRead_trace_eq`/`relativeRead_value_eq`), so the dispatch
simulation composes receipts positionally with no decode gap.

## DD-20260718-008: charged same-block close swapped onto the accepted route; route literal 207 unmoved (B6 REQ-B6-05/-09)

Status: Proposed
Date: 2026-07-18
Scope: B6 rung (worker B6-02), branch `claude/b1-b2-charged-fringe-tables`:
`ChargedSameBlockTrace.lean`, `ChargedFringeWiring.lean`,
`SuccinctFinalRAM.lean`, `SuccinctFinalStoreParam.lean`,
`docs/PAPER_MODEL_ADEQUACY.md`.

Decision: the canonical close/LCA dispatchers now call the charged chunked
same-block consumers, closing the last event-silent computation on the
accepted route.  Four sub-decisions were forced and are recorded here.

1. THE ROUTE LITERAL DOES NOT MOVE.  The delegation authorized freezing 207
   as a historical constant "to at most 240" by the 142 pattern.  Read at
   source, the close/LCA principled cap is a MAX over the two branches, not
   a sum: the cross-block arm already pays
   `bpChunkedPrincipledBPCloseChargedTraceCostWithRankSeed rankCost
   = 2*rankCost + 2*37 + 30` (= 126 at `rankCost = 11`), while the charged
   same-block arm pays `rankCost + 4 + 33 = rankCost + 37` (= 48).  Since
   `rankCost + 37 <= 2*rankCost + 104` for every `rankCost`, the existing
   cap absorbs the new reads with no algebra field touched, and
   `concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost_eq`
   re-derives by `rfl` to 207 UNCHANGED (it depends on no axioms at all).
   Consequently NO historical constant is minted, `SuccinctClassic.queryCost
   = 207` and all 27 Lean consumers stand, the `SumLe207` topology anchor is
   not renamed, and no doc numeral migration occurs.  The authorization to
   move the literal went UNUSED - strictly less public-surface disruption
   than authorized, not more.  Alternative rejected: minting a historical
   207 and a new literal anyway "for symmetry with B2/B3", which would have
   asserted a constant the algebra does not derive.

2. NO NEW SEGMENT, TABLE, OR STORE OBLIGATION.  The same-block window is
   DEFINITIONALLY the B2 fringe window
   (`localBPWindowBits_eq_flatten_localBPBlockWordsRead`), so the same-block
   chunk reads go to the SAME segment-21 `bpFringeChunkTable` the
   cross-block fringe already reads.  The dispatchers therefore keep their
   names, parameter lists, and statement shapes byte-for-byte, the existing
   unused `_sameBlockSegment` parameter stays unused, and no store, payload,
   overhead, capacity, erasure, or `ReviewerSource` work arises.
   `canonical_segments_complete` is unchanged (still `< 22`).  This is
   stronger identity preservation than B2's own M9 achieved.  Alternative
   rejected: a dedicated same-block segment/table, which would have required
   the full space/erasure/capacity/o(n)/provenance treatment for reads that
   are bit-identical to reads already counted.

3. `_trace_forall` GAINS ONE HYPOTHESIS, IN MEMBERSHIP FORM.  The same-block
   branch is no longer read-free, so
   `lcaCloseTraceResultWithRankSeedAllSizeStructural_trace_forall` takes a
   new `hsameBlock`, stated as membership in
   `bpChunkedSameBlockCloseSeededTraceResultAtSegment` exactly as the
   existing `hfringeLeft`/`hfringeRight` are stated.  The cheaper raw form
   (`address < rowCount -> P (readWord fringeSegment address _)`) was
   REJECTED even though all seven accepted consumers already have that fact
   in hand: the raw form names a segment and an address but not a PRODUCER,
   and REQ-B6-04 requires provenance to cover the actual emitted events by
   producing component, not by segment membership.  The membership form is
   what lets `ReviewerProducerReadPath.lcaSameBlock` name the subtrace that
   produced each same-block read.  Consequence: `hbp` (window-word reads)
   became subsumed - every branch now reaches its window reads through the
   component subtrace that produced them - and is retained as `_hbp` so the
   seven consumers keep their argument shape.  It is documented as retained
   for statement stability rather than silently deleted.

4. EXACTNESS IS TRANSPORTED, NOT RE-PROVED.  The accepted same-block
   exactness theorem
   `localBPSameBlockCloseDecodedCostedWithRankSeed_exact_of_query_same_block`
   is kept and moved across the M3a substitution
   (`bpChunkedSameBlockCloseDecodedCostedWithRankSeed_value_eq_of_query`)
   by `rw [hvalue]; exact haccepted`, exactly as the cross-block case does.
   B2's "whole block lies inside the BP code" strictness argument is NOT
   imported: it is false for same-block queries because the final block may
   extend past `shape.bpCode.length`.  Each close position is covered
   separately instead, following B6-01.

Consequences: the accepted route's same-block executions now emit
`readWord 21 _ _` events; the cost harness confirms this empirically, with
`canonicalRoute=sameBlock` windows rising from modeledTraceCost 52-54 to
54-62 while `canonicalBoundIs207=true` holds on all 17 reported inputs and
all windows still agree with reference `List Int` RMQ semantics.  The
charge-policy section of `docs/PAPER_MODEL_ADEQUACY.md` (the paper-facing
point of the rung) is now TRUE as written and names the same-block leg, its
37-cap, and the residual uncharged register work explicitly.

Residual (inherited, not introduced): the retired silent store-locality
helpers `finalSameBlockLcaWithStore_storeTraceLocal` /
`localBPSameBlockSeededWithStore_storeTraceLocal` become unreferenced in
`SuccinctFinalStoreParam.lean`, exactly as B2's own
`finalCrossBlockLcaWithStore_storeTraceLocal` already is.  They are private
proofs about the retired silent objects, not counted payload sources, so
this is not a dead-source violation; B6 leaves them as B2 left its twins and
flags the pair as a single cleanup candidate for a later rung.

## DD-20260718-009: E1 charged fringe fold register bank, option-shifted best candidate, and the branching merge (E1-R4 M3d-1b)

Date: 2026-07-18. Scope: the machine realization of the charged chunked
fringe fold (`bpFringeChunkFoldComputationFrom`,
`RMQ/Core/SuccinctClose/RelativeRmmMacro/ChargedFringeTrace.lean:32`),
which BOTH arms of the close/LCA dispatcher consume after B6. Decided by:
worker E1-R4k under the amended E1 contract (frozen matrix
`E1_AMENDED_MACHINE_ACCEPTANCE_MATRIX.md` REQ-E1-01/02/04/06).

Decision (`RMQ/Core/WordRAM/E1FringeFoldBlock.lean`, namespace
`RMQ.WordRAM.E1FringeFoldBlock`):

- Frozen FRINGE BANK `40..62`, fresh above the skeleton (`0..7`),
  component (`8..27`) and select-extension (`28..39`) banks:
  `fOne/fC = 40/41` (pinned constants), `fW0..fW3 = 42..45` (the four
  window registers), `fAcc = 46`, `fBV/fBP = 47/48` (best candidate),
  `fJC = 49` (chunk cursor `j * c`), `fLo/fHi = 50/51`, `fCnt = 52`,
  `fV/fA/fB = 53/54/55` (chunk value, start/end offsets),
  `fSlot/fE = 56/57`, `fCV/fCP = 58/59` (candidate), `fT/fU/fX = 60..62`
  (scratch).  The LCA leg runs third, so `28..39` is dead by then and
  reuse would be sound; a fresh bank is still preferred so the whole-query
  glue never has to reason about liveness across legs.

- FOUR-REGISTER WINDOW, not one.  The fringe fold's window is the four
  payload words of `localBPWindowBits`, so its decode does NOT fit one
  modeled register and the machine may not hold `bitsToNatLE window` at
  all (REQ-E1-02 / INV-ADDRESS-WIDTH).  The window is carried in the
  fixed-stride Horner representation `windowRegsValue L R0 R1 R2 R3`
  (`E1FringeBridge.lean`) and advanced each pass by a four-register shift
  using only the per-shape CONSTANTS `2 ^ c` and `2 ^ (L - c)`
  (`windowRegsValue_shift`), so no variable-width shift is needed and the
  ISA's constant-only `mulConst`/`divConst` (DD-20260718-005) suffice.
  The side condition `c <= L` is unconditional at every size
  (`bpFringeChunkBits_le_machineWordBits`).

- OPTION-SHIFTED BEST CANDIDATE across two registers: `fBV = value + 1`
  with `0` meaning `none`, and `fBP` the position (`bestOfRegs`).  This is
  the same convention `decodeRead` uses for reads (DD-20260718-005), so
  the option test is one register comparison against zero and the fold's
  `cand.1 < best.1` becomes the shifted comparison `fCV + 1 < fBV`
  (`bestOfRegs_merge_some`).

- THE MERGE SEGMENT BRANCHES; this is forced, not chosen.
  `bpFringeMergeCand` (`ChargedFringeChunks.lean:892`) is a three-way
  match gated by `startOff < endOff`.  A branch-free encoding would need
  `take * X` with `take` a RUNTIME `0/1` value, and the ISA has
  `mulConst` (constant multiplier) only - deliberately, per
  DD-20260718-005.  So the merge is 13 instructions with four branch
  points, and the per-pass simulation is a FOUR-WAY case analysis
  (`fringeMerge_runsTo`) rather than one `RunsTo.straight` call.  Arms:
  gate closed -> 3 instructions; gate open with no incumbent -> 6;
  gate open and candidate better -> 8; gate open and not better -> 7.

- CONSEQUENCE FOR CHARGING: the per-pass category log is therefore NOT a
  constant list.  It is a FUNCTION of the route-side branch conditions
  (`fringeMergeArmCats` / `fringeMergeCatsAt` / `fringePassCats`),
  following the `selectFoldCats` / `denseLegCats` precedent.  No per-pass
  numeral is asserted anywhere; the whole-fold log `fringeFoldCats` is the
  execution-ordered concatenation of the per-pass logs via the new
  `ascLog` / `iterLog_desc` combinator.

Layout at loop base `LB` (66-instruction body, back edge at `LB + 66`):
prefix `LB+0..LB+31`, merge `LB+32..LB+44`, window shift `LB+45..LB+63`,
cursor/counter `LB+64..LB+65`.  Width certificate:
`fringeLoopBody_fits`.

## DD-20260718-010: E1 charged fringe ARM layout â€” window-read sub-block, derived 33-cap, and the locally-pinned epilogue (E1-R4l M3d-2)

Date: 2026-07-18. Scope: the machine realization of a whole charged
fringe arm â€” the four window-word reads, the 33-capped chunk fold, and
the `bpFringeCandGlobal` global rebase â€” i.e. the accepted objects
`bpChunkedLeftFringeCandidateSeededTraceResultAtSegmentWithStore` and
`bpChunkedRightFringeCandidateSeededTraceResultAtSegmentWithStore`
(`RMQ/Core/SuccinctClose/RelativeRmmMacro/ChargedFringeTrace.lean:708`
and `:731`). Decided by: worker E1-R4l under the amended E1 contract
(frozen matrix `E1_AMENDED_MACHINE_ACCEPTANCE_MATRIX.md`
REQ-E1-01/02/04/06). Extends DD-20260718-009.

Decision (`RMQ/Core/WordRAM/E1FringeArmBlock.lean`, namespace
`RMQ.WordRAM.E1FringeArmBlock`):

- BANK EXTENSION `63..68`, above the fringe fold bank `40..62`:
  `fBase = 63` (window base WORD index), `fBB = 64` (window BIT base, the
  route's `localBPWindowBase`), `fSeed = 65` and `fStart = 66` (the
  fallback candidate pair), `fRV = 67` and `fRP = 68` (the arm result).
  `fBase` and `fBB` are deliberately SEPARATE registers: the route's
  `localBPWindowBase` (`LocalBPDecoder.lean:205`) is the word index times
  the word width, and the arm needs the word index for addressing and the
  bit base for the rebase, in the same live range
  (`localBPWindowBase_eq`).

- WINDOW READ IS FOUR SEPARATE `readMem` INSTRUCTIONS, not a composite.
  `fringeWindowRead` is 11 instructions emitting exactly FOUR memory-read
  events at global segment `0`, indices `base .. base + 3`, each decoded
  out of the option-shift convention by an explicit `sub _ _ fOne`
  (`decodeRead - 1`, `E1RankBridge.lean:182`). This is the shape
  REQ-E1-01's anti-composite challenge demands: a hypothetical
  `readWindow` folding four reads into one step would be rejected by the
  per-instruction read-event count.

- THE ITERATION COUNT IS DERIVED, NEVER ASSERTED. The route's fold count
  is literally `Nat.min (relHi / c + 1) 33` (`ChargedFringeTrace.lean:728`
  and `:749`). `fringeArmInit` computes it in five instructions by the
  truncated-subtraction cap chain `x - (x - 33)`, the same chain
  `rankAtInit` uses for its 8-cap (`E1RankAtBlock.lean:56-62`), and
  `cap_chain_eq_min` proves that chain equals `Nat.min`. The literal `33`
  appears only as the route's own cap immediate, never as an asserted
  count; `cap_count_pos` then discharges the fold block's `hcount`.

- THE EPILOGUE PINS ITS OWN UNIT CONSTANT. `fringeCandGlobal` writes `1`
  into the scratch register `fT` at its first instruction and uses `fT`
  both as its unconditional-branch condition and as the unshift operand,
  rather than reading the pinned `fOne`. This is forced by composition,
  not stylistic: the fold block's preservation certificate
  `FringeFoldUntouched` (`E1FringeFoldBlock.lean:962`) is the conservative
  predicate `r < 40 âˆ¨ 63 â‰¤ r`, which does NOT certify `fOne = 40`. An
  epilogue depending on `fOne` therefore could not be composed with the
  fold without first strengthening the fold's certificate â€” a change to a
  block that is already closed. Pinning locally costs one register write
  and keeps the epilogue composable as written. The bank registers the
  epilogue does consume (`fBB`, `fSeed`, `fStart`) are all `â‰¥ 63` and so
  ARE certified by `FringeFoldUntouched`.

- THE EPILOGUE'S CATEGORY LOG IS ROUTE-INDEXED. `bpFringeCandGlobal`
  (`ChargedFringeChunks.lean:1617`) is a two-arm option rebase, so the
  epilogue branches and its charge is arm-dependent:
  `fringeCandGlobalArmCats occupied` is 4 ticks when the fold left an
  occupied best and 5 when it fell back. In the whole-arm log
  `fringeArmCats` that index is the `isSome` of the ACCEPTED fold
  object's best candidate â€” route-side data, not a machine register and
  not a numeral (`bestOfRegs_isSome` supplies the agreement). This
  follows the `fringeMergeCatsAt` precedent of DD-20260718-009.

- THE EPILOGUE EMITS NO RECEIPT. `bpFringeCandGlobal` performs no memory
  read, so the arm's receipt is exactly the leg's: four window reads
  followed positionally by the accepted fold object's own trace
  (`fringeLeg_trace_eq_leftArm` / `_rightArm`). It does still cost branch
  and arithmetic ticks, which the arm-indexed log records â€” charge and
  receipt are kept separate.

Arm layout at base `A` (95 instructions): prologue `A..A+20` (init
`A..A+9`, window read `A+10..A+20`), fold loop base `A+21` with exit
`A+88`, epilogue `A+88..A+94`, arm exit `A+95`. Width certificate:
`fringeArmPrologue_fits` (constructor-exhaustive, no wildcard arm).

Route-side residue deliberately left to canonical instantiation: the
Horner bridge `windowRegsValue_of_readBits` takes as hypotheses that the
first three window words have length exactly `L`. These are properties of
`chunkPayloadWords`, discharged at canonical instantiation exactly as the
dense select leg discharges its `hlen`
(`E1SelectCanonical.lean` `canonical_denseLen`).

## DD-20260718-011: E1 address preamble and same-block close arm Ã¢â‚¬â€ constant-divisor addressing, bank extension `69..70` (E1-R4m M3d-3)

Date: 2026-07-18. Scope: the machine realization of the accepted B6
same-block object
`bpChunkedSameBlockCloseSeededTraceResultAtSegmentWithStore`
(`RMQ/Core/SuccinctClose/RelativeRmmMacro/ChargedSameBlockTrace.lean:55`),
plus the address arithmetic that computes the window base registers from
the query operand. Decided by: worker E1-R4m under the amended E1 contract
(frozen matrix `E1_AMENDED_MACHINE_ACCEPTANCE_MATRIX.md`
REQ-E1-01/02/04/06). Extends DD-20260718-009 and DD-20260718-010.

Decision (`RMQ/Core/WordRAM/E1SameBlockArm.lean`, namespace
`RMQ.WordRAM.E1SameBlockArm`):

- BANK EXTENSION `69..70`, above the fringe arm bank `63..68`:
  `fRes = 69` (the `bpCandidateClose?` payload) and `fClose = 70` (the
  close position the address preamble consumes). Both are fresh; no
  existing register meaning is redefined.

- ADDRESSING USES CONSTANT DIVISORS ONLY, and this was verified before
  being relied on rather than assumed. The ISA deliberately has no
  variable-divisor instruction. `blockOfClose` and `blockStartOf`
  (`BlockLocal.lean:863`/`:866`) take `blockSize` as a parameter, and every
  accepted-route call site binds `canonicalBPRelativeSummaryBlockSizeRaw
  shape` (`ChargedFringeWiring.lean:36`/`:57`,
  `ChargedFringeTrace.lean:928`/`:1151`), which is
  `2 * (Nat.log2 shape.size + 1)` Ã¢â‚¬â€ a function of `shape` alone and always
  `>= 2`. The word width `machineWordBits shape.bpCode.length` is likewise
  shape-determined and positive. So `windowAddr` is FOUR instructions
  (`divConst`, `mulConst`, `divConst`, `mulConst`) whose immediates are
  per-shape program constants, and `windowAddr_fits` discharges
  `divConst`'s `0 < k` arm from those positivity facts.

  CONSEQUENCE THAT MUST BE RESPECTED BY LATER CODE: immediates must be
  generated from `canonicalBPRelativeSummaryBlockSizeRaw`, NOT from the
  guarded `canonicalBPRelativeSummaryBlockSize`
  (`RelativeSummary.lean:1469`), which is `0` on inactive shapes and would
  fail the width certificate for a leg that never executes. The guarded
  name belongs only to the legacy dispatcher behind the near-homonym
  `concreteBPNativeLCACloseGlobalWordTraceResult`
  (`SuccinctFinalRAM.lean:2271`), which the accepted route does not
  consume.

- THE CLOSE EPILOGUE IS TWO INSTRUCTIONS AND HAS NO OPTION DISPATCH.
  `bpCandidateClose?` is `candidate?.map fun c => c.2 - 1`
  (`Candidate.lean:28`), and the arm feeds it `bpFringeCandGlobal`, which
  is total into `some` (`ChargedFringeChunks.lean:1617` Ã¢â‚¬â€ both arms yield
  `some`). So no occupancy test is needed and none is emitted; the
  epilogue is `const` plus `sub`. Its category log `sameBlockCloseCats` is
  therefore unconditional, which is honest precisely BECAUSE the route-side
  function it mirrors has no branch Ã¢â‚¬â€ unlike `fringeCandGlobalArmCats`,
  which is route-indexed because its route-side counterpart does branch.

- THE EPILOGUE EMITS NO READ EVENT, matching the route: the accepted
  object applies `bpCandidateClose?` through `TraceResult.map`, which
  contributes no trace. `sameBlockSeeded_trace_eq` states the resulting
  receipt agreement POSITIONALLY, as a `List` equality.

Rejected alternative: computing the window base by a variable-divisor
instruction added to the ISA. Rejected because it is unnecessary Ã¢â‚¬â€ the
divisors are per-shape constants Ã¢â‚¬â€ and because widening the ISA without
need would weaken REQ-E1-01's "familiar repertoire" claim.

Related open item, recorded here because it is an ISA-level question of
the same kind: the INTERIOR leg computes `Nat.log2` and `2 ^ Nat.log2` of
a RUNTIME-derived count (`InteriorDirectory.lean:2112-2142`,
`SparseArgMin.lean:598-599`). The existing ISA can compute both by
halving/doubling with the constant `2`, so this is not an expressiveness
gap, but the resulting loop has no literal all-size iteration cap, which
is in tension with REQ-E1-06(c) as frozen. This is flagged for coordinator
adjudication in `docs/internal/E1_WORKLOG.md` (M3d-3 section 2) and is NOT
decided here.

## DD-20260718-014: E1 three-way candidate merge — biased option encoding as the cross-component interface, bank extension `75..84` (E1-R4q M3d-7)

Date: 2026-07-18. Scope: the machine realization of the fused epilogue of
the accepted cross-block close object
`bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore`
(`RMQ/Core/SuccinctClose/RelativeRmmMacro/ChargedFringeTrace.lean:1144`),
namely `bpCandidateClose? (bpCandidateMerge3? left? middle? right?)`.
Decided by: worker E1-R4q under the amended E1 contract (frozen matrix
`E1_AMENDED_MACHINE_ACCEPTANCE_MATRIX.md` REQ-E1-01/02/06/08). Extends
DD-20260718-009, -010 and -011.

Decision (`RMQ/Core/WordRAM/E1CandMerge3.lean`, namespace
`RMQ.WordRAM.E1CandMerge3`):

- BANK EXTENSION `75..84`, above the dispatch bank `72..74`: `mLV = 75`,
  `mLP = 76` (left candidate value/position), `mMV = 77`, `mMP = 78`
  (middle), `mRV = 79`, `mRP = 80` (right), `mAV = 81`, `mAP = 82`
  (accumulator), `mT = 83`, `mU = 84` (scratch). All fresh; no existing
  register meaning is redefined. The block writes its
  `bpCandidateClose?` payload into the EXISTING `fRes = 69`, the same
  register the same-block leg uses, so the two dispatch arms converge on
  one output register rather than introducing a second result surface.

- OPTIONAL CANDIDATES USE THE `+1` BIAS already established by
  DD-20260718-009 for the fold's best candidate (`0` encodes `none`,
  `v + 1` encodes `some v`, decoded by `E1FringeFoldBlock.bestOfRegs`).
  This is not merely consistency. The bias makes both comparisons DIRECT:
  for two occupied candidates the biased test `v₁ + 1 < v₂ + 1` is
  literally the route's `v₁ < v₂`, so no unbiasing arithmetic precedes
  either `natLt`. That is what makes the block 16 instructions rather
  than roughly 24, and it is why the accumulator invariant is stated in
  biased form (`candMerge3Mid_runsTo`, `E1CandMerge3.lean:365`).

- STRICT `natLt` AT BOTH COMPARISON SITES, never `natLe`.
  `bpCandidateBetter` (`EndpointFringe/InteriorCandidate/Candidate.lean:15`)
  uses strict `<`, so ties keep the LEFT candidate; since
  `bpCandidateMerge3?` associates to the left (`:24`), the left fringe
  wins ties over the interior and both win ties over the right fringe.
  Using `natLe` anywhere would silently invert the accepted route's
  leftmost tie-break.

- THE BLOCK IS READ-FREE, matching the route: the epilogue rides a
  `TraceResult.map`, which contributes no trace event. Recorded as
  `candMerge3_readFree` (`:206`) and observed in execution by
  `candMerge3Witness_readLogs_empty` (`:855`).

- ALL SIX CONTROL PATHS ARE HANDLED, and the block deliberately does NOT
  generalise from `E1SameBlockArm.sameBlockClose`. That epilogue is two
  instructions with no option dispatch because `bpFringeCandGlobal` is
  total into `some` (`ChargedFringeChunks.lean:1617`). Here `middle?` is
  genuinely optional — the interior leg sits behind the guard
  `leftBlock + 1 < rightBlock` whose else-branch is
  `TraceResult.pure none` (`ChargedFringeTrace.lean:1163`) — so a real
  three-way option-aware minimum is required.

- THE CROSS-COMPONENT INTERFACE THIS FIXES, binding on the interior leg
  when worker B7 unblocks it: `middle?` must be delivered as `mMV` (`77`)
  holding `0` for `none` and `v + 1` for `some (v, _)`, and `mMP` (`78`)
  holding the position, UNCONSTRAINED when absent (the block branches
  away at `E+2` before reading `mMP`). Two alternatives are rejected
  explicitly: an unbiased value plus a separate occupancy flag costs an
  extra register and an extra test, changing every category log; and a
  SENTINEL encoding (absent as a large value) would break the tie-break,
  because a sentinel that ties with a real candidate takes the wrong
  branch under strict `<`.

Consequence for the ISA: NONE. The block introduces no constructor, no
divisor, and no variable-operand arithmetic — it is `move`, `natLt`,
`brNZ`, `const` and one `sub`. The ISA decision of DD-20260718-005 is
unchanged.
## DD-20260718-012: B7 sparse-level mechanism determination - charged floor-log2/span table, one packed read per two-span call (B7 Milestone 0)

Date: 2026-07-18. Scope: the last known uncharged size-dependent
computation on the accepted RMQ query route - the sparse-table level.
Decided by: worker B7-01 (branch `claude/b7-charged-sparse-level`, base
`f6564ec`) under the B7 delegation prompt. This entry records the
MECHANISM DETERMINATION only; it is committed BEFORE implementation, and
before the B7 acceptance matrix is frozen. It resolves, on the route
side, the open item recorded at the end of DD-20260718-011 (E1-R4m),
which flagged the same `Nat.log2` / `2 ^ Nat.log2` computation as an
ISA-level question and explicitly did not decide it.

### The finding, verified at source in this worktree at `f6564ec`

FOUR executed evaluator sites bind the level by a `Nat.log2` recursion on
a runtime-derived argument:

- `PayloadLiveBPLocalSparseOffsetTable.twoSpanCandidateTraceResult`
  (`RMQ/Core/SuccinctClose/EndpointFringe/InteriorCandidate/InteriorRAM.lean:559`,
  `let level := Nat.log2 count` at `:573`)
- `...twoSpanCandidateTraceResultAtSegments` (`InteriorRAM.lean:606`, log2 at `:621`)
- `PayloadLiveBPGlobalSparseBlockTable.twoSpanCandidateTraceResult`
  (`InteriorRAM.lean:805`, `let level := Nat.log2 macroSpanCount` at `:819`)
- `...twoSpanCandidateTraceResultAtSegments` (`InteriorRAM.lean:852`, log2 at `:867`)

with cost-model twins `PayloadLiveBPLocalSparseOffsetTable.twoSpanCandidateCosted`
(`EndpointFringe/InteriorCandidate/LocalGlobalSparse.lean:17`, log2 at `:30`)
and `PayloadLiveBPGlobalSparseBlockTable.twoSpanCandidateCosted`
(`LocalGlobalSparse.lean:590`, log2 at `:603`), and store-parametric twins
`bpLocalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore`
(`RelativeRmmMacro/ConcreteDirectoryRAMStoreParam.lean:1405`) and
`bpGlobalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore` (`:1995`).

THE SPAN IS PART OF THE FINDING, not a separate issue. Each site also
evaluates `bpSparseLogSpan count = 2 ^ Nat.log2 count`
(`EndpointFringe/PrefixRange/SparseArgMin.lean:598-599`), consumed as
`rightLocalStart := localStart + count - span`. `Nat.pow` is a recursion
of `level` multiplications, so the span is a SECOND Theta(log n)
uncharged computation at the same site, and each site in fact evaluates
`Nat.log2 count` twice at the term level (once directly, once inside
`bpSparseLogSpan`). Any fix that charges only the level leaves the span
uncharged and does not close the rung.

The level reaches an accepted READ ADDRESS: `bpLocalSparseCellSlot
macroSize levelCount macroIdx localStart level = macroIdx * (levelCount *
macroSize) + level * macroSize + localStart`
(`EndpointFringe/PrefixRange/LocalSparseOffset.lean:15-17`) and
`bpGlobalSparseCellSlot macroCount macroStart level = level * macroCount +
macroStart` (`LocalGlobalSparse.lean:199-201`).

### Why this is ALGORITHMIC WORK, not a representation artifact

Under the project's round-7 principle a traversal is a representation
artifact only when its value is checked-equal to an input parameter or to
a charged read. The level fails that test in the strongest way: it is an
address INPUT computed from runtime data, and it is never checked against
anything. The argument provenance is arithmetic on the query operands
(`bpTwoLevelInteriorCandidateTraceResult`, `InteriorRAM.lean:1515-1525`;
identical in `TwoLevelCandidate.lean:32-42`):

    let macroStart := startBlock / macroSize
    let localStart := startBlock % macroSize
    let leftCount := macroSize - localStart
    let remaining := count - leftCount
    let middleMacroCount := remaining / macroSize
    let rightCount := remaining % macroSize

so the four arguments that reach a `Nat.log2` are `count` (within-macro
fast path, `InteriorRAM.lean:1520`), `leftCount` (`:1166`, `:1218`,
`:1278`), `rightCount` (`:1171`, `:1287`), and `middleMacroCount`
(`:1223`, `:1282`). None is a structural parameter and none is a charged
read. The ONLY facts the route ever establishes about them are the
monotonicity side conditions `0 < count /\ count <= macroSize` (local) and
`0 < macroSpanCount /\ macroSpanCount <= macroCount` (global), converted
to `Nat.log2 _ < levelCount` through the ASSUMED hypotheses `hlocalLevel`
/ `hglobalLevel` at `TwoLevelCandidate.lean:241-248`. The level is
therefore obtained from computation, never from data.

### DECISION: mechanism 3 (new o(n) charged table), in a single-source,
### single-read-per-call form

A new counted source `bpSparseLevelTable`, read once per two-span call,
returning a PACKED `(level, span)` pair unpacked by constant arithmetic.

- ONE table, ONE region, indexed directly by the count. Domain
  `bpSparseLevelDomain shape = macroSize + macroCount + 1`, which covers
  BOTH consumers: local counts satisfy `count <= macroSize` and global
  counts satisfy `macroSpanCount <= macroCount`, so a single region
  indexed by the raw count is in range for both. This avoids a `max` in
  the size bound (sums are what the erasure and littleO proofs want) and
  avoids a second counted source with its own erasure, capacity, littleO,
  and provenance obligations.
- Cell `i` stores `Nat.log2 i * D + bpSparseLogSpan i` where
  `D = bpSparseLevelDomain shape`, and `bpSparseLogSpan i <= i < D` for
  every index actually read, so `cell / D = Nat.log2 i` and
  `cell % D = bpSparseLogSpan i`. Unpacking is one division and one
  modulus by a per-shape constant. That is the SAME arithmetic the
  accepted route already performs uncharged at `InteriorRAM.lean:1515-1516`
  (`startBlock / macroSize`, `startBlock % macroSize`), and it is
  constant-divisor arithmetic in exactly the sense DD-20260718-011
  established for the E1 address preamble - so it introduces no new class
  of uncharged work and no ISA extension.
- ONE charged read per two-span call, not two. This matters for the cost
  cap: see the literal derivation below.

Entry width `machineWordBits (D * D)` bounds every stored cell, since
`Nat.log2 i * D + bpSparseLogSpan i < D * D` for `i < D`.

SIZE, and why it stays o(n). With `base = canonicalBPRelativeSummaryBase
shape = Nat.log2 shape.size + 1` (`RelativeSummary.lean:1238`),
`blockSize = 2 * base` (`:1242`), `macroSize = base * base`
(`RelativeSummary.lean:2733-2736`), and `macroCount = blockCount /
macroSize` with `blockCount ~ n / base`, the domain is
`D ~ base^2 + n / base^3` and the table is `D * machineWordBits (D * D)`
bits, i.e. `~ 2 n log n / base^3 = Theta(n / (log n)^2)` bits, plus a
polylogarithmic term. That is o(n) with room to spare, and it is sized
over the values that ACTUALLY OCCUR (the `count` / `macroSpanCount`
ranges) rather than over all of `Nat`, as the delegation required.

### Rejected alternatives, with the evidence that rejected them

MECHANISM 1 - already available from a charged read: REJECTED on a
structural argument, not a survey. The level is consumed by
`bpLocalSparseCellSlot` / `bpGlobalSparseCellSlot` to FORM the address of
the first read of the span, so it must be known strictly BEFORE any
charged read of that span occurs. There is no read at or before the
level-consumption point that could carry it. The reads that do occur
(`readOffsetCosted`, `LocalSparseOffset.lean:355-364`; `readBlockCosted`,
`LocalGlobalSparse.lean:405-414`) are `FixedWidthNatTable.readCosted`
(`SuccinctSpace/Tables.lean:86-91`), each returning a single
`Costed (Option Nat)` of width `offsetWidth` / `blockWidth` - one field,
no spare capacity.

MECHANISM 2 - widen an existing counted entry: REJECTED, and the reason is
arithmetic rather than aesthetic. A single widened entry cannot carry the
level, because ONE query needs the levels of up to THREE DIFFERENT runtime
values (`leftCount`, `middleMacroCount`, `rightCount` on the cross-macro
branch, `InteriorRAM.lean:1278-1287`). Carrying three runtime-indexed
values requires an object indexed by the count - which IS mechanism 3.
Widening the offset cell was checked and is independently impossible: it
is `offsetWidth = Nat.log2 macroSize + 1` bits holding a value `<
macroSize`, roughly one spare bit, not the `machineWordBits levelCount`
needed. A related observation, recorded but NOT relied on: `summaryCosted`
(`RelativeSummary.lean:735-754`) charges four reads and
`bpRelativeSummaryMinCandidate`
(`EndpointFringe/PrefixRange/RelativeSummaryCandidate.lean:15-22`) never
projects the `maxRel` field, so one of the four is dead at the
min-candidate site. That is a genuine finding about the accepted route,
but it is sequenced AFTER the level is needed and so cannot supply it; it
is logged for the B7 uncharged-computation inventory rather than used
here.

MECHANISM 4 - restructure so no runtime log2 is needed: REJECTED with a
size computation. The natural restructuring is to index the sparse cell by
the SPAN rather than the level, which removes the need for the level
entirely. It was costed and fails: the row count of the local table would
grow from `levelCount = Nat.log2 macroSize + 1` to `macroSize`, taking the
table from `macroCount * levelCount * macroSize` cells to `macroCount *
macroSize * macroSize ~ n * macroSize` bits, which is Theta(n polylog) and
destroys the o(n) overhead. A fixed maximal level was also considered and
does not type as an algorithm: the two-span cover is only correct when the
span is the largest power of two at most `count`, so a level fixed
independently of `count` either overshoots the range or fails to cover it.

EXPLICITLY NOT CONSIDERED, per the user decision recorded in the
delegation: adding an `msb`/`log2` machine instruction to the ISA, and
weakening any bound to accept Theta(log n) work. Both were declined by the
user in favour of the unimpeachable result, so neither was evaluated.

### The route literal MOVES: 207 -> 210. Derived, not assumed.

The cost chain is exactly tight, with no slack to absorb the new read:

- `spanCandidateCosted_cost_le_five` (`LocalSparseOffset.lean:450`,
  `LocalGlobalSparse.lean:494`): 1 offset/block read + 4 summary reads = 5.
- `twoSpanCandidateCosted_cost_le_ten` (`LocalGlobalSparse.lean:41`,
  `:613`): two span candidates = 10.
- `bpTwoLevelInteriorCandidateCosted_cost_le_thirty`
  (`TwoLevelCandidate.lean:53`): the cross-macro branch is THREE two-span
  calls = 30, and 30 is attained, so the cap is exactly met.
- `canonicalRelativeRmmPrincipledInteriorChargedTraceCost = 30`
  (`InteriorDirectory.lean:1783`).

Adding one packed table read per two-span call takes the two-span cap from
10 to 11 and the interior cap from 30 to 33 (the interior bound is a MAX
over the three branches, and the maximizing cross-macro branch carries all
three new reads). Feeding that through the named component algebra
(`concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCostAlgebra`,
`SuccinctFinalRAM.lean:8810-8820`, with `selectClose := 35`,
`rankClose := 11`, `endpointFringe := 37`):

    closeLCA  = 2*rankClose + 2*endpointFringe + interiorDirectory
              = 2*11 + 2*37 + 33 = 22 + 74 + 33 = 129   (was 126)
    wholeQuery = 2*selectClose + closeLCA + rankClose
              = 2*35 + 129 + 11 = 70 + 129 + 11 = 210   (was 207)

This is the first of the three uncharged-computation rungs whose literal
moves; B6 (DD-20260718-008) fit under the existing cap and left 207
unmoved, because it recharged a leaf that was NOT at the maximizing
branch. Per the delegation, 207 is therefore to be frozen as a named
historical constant with its `_eq` theorem and guards, following the
established 142/76/328 pattern already in
`SuccinctFinalRAM.lean:8825-8875`
(`concreteBPNativeSuccinctRMQSilentFringeChargedTraceCost = 76`,
`...SilentWordRankSelectChargedTraceCost = 142`), under the name
`concreteBPNativeSuccinctRMQSilentSparseLevelChargedTraceCost = 207`, and
every Lean consumer plus the topology anchor `SumLe207` in
`scripts/paper_topology_lint.ps1` and `scripts/headline_axiom_check.lean`
must move to 210. Frozen legacy anchors are not touched.

## DD-20260718-013: B7 correction of record - the executed sites are the FlatStoreComputation family, and the interior cap is genuinely tight (B7 Milestone 0b)

Date: 2026-07-18. Scope: corrects two factual errors in DD-20260718-012
and settles the decisive cost question the coordinator posed. Decided by:
worker B7-01, after a coordinator relay of read-only scout findings that
contradicted this worker's own subagent survey, and after verifying both
accounts at source. Supersedes the cited SITES of DD-20260718-012; the
MECHANISM decision in that entry stands, and the literal derivation in it
is now confirmed by reading the cap proof rather than inferred from a
docstring.

### CORRECTION 1: the four cited sites are cost-model twins, not executed

DD-20260718-012 cited `InteriorRAM.lean:573`, `:621`, `:819`, `:867` as
the executed evaluator sites. That is WRONG. Verified at source in this
worktree at `f6564ec`:

`canonicalRelativeRmmInteriorRangeMinTraceResultAtSegment`
(`RelativeRmmMacro/ConcreteDirectoryRAM.lean:1113-1119`) is defined as

    flatStoreExecutionTraceResultAtSegment componentSegment
      (canonicalRelativeRmmInteriorRangeMinExecutionWithStore shape
        (canonicalRelativeRmmInteriorComponentStore shape).store.words
        startBlock count)

so the executed object is the `FlatStoreComputation` family rooted at
`canonicalRelativeRmmInteriorRangeMinComputation`
(`InteriorDirectory.lean:2185`), NOT the `PayloadLive*` family. The
`PayloadLive*.twoSpanCandidateTraceResultAtSegments` chain is the
refinement/specification ladder; walking its callers up dead-ends at
`concreteBPNativeLCACloseWordTraceResultAtSegmentsOfSizeGe`
(`SuccinctFinalRAM.lean:2238`), which has no definition-level caller.

THE EXECUTED CLASS-(a) SITES ARE EXACTLY THREE:

- `canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation`,
  `let level := Nat.log2 count` (`InteriorDirectory.lean:2117`), whose
  level reaches `bpLocalSparseCellSlot` (`:2088`);
- `canonicalRelativeRmmMachineGlobalTwoSpanCandidateComputation`,
  `let level := Nat.log2 macroSpanCount` (`InteriorDirectory.lean:2131`),
  whose level reaches `bpGlobalSparseCellSlot` (`:2106`);
- `bpSparseLogSpan` (`SparseArgMin.lean:599`), invoked at `:2118` and
  `:2132`, setting `rightLocalStart` / `rightMacroStart` - the address
  argument of the SECOND span read.

The worst case is the cross-macro branch
(`canonicalRelativeRmmMachineCrossMacroCandidateComputation`, reached from
`InteriorDirectory.lean:2208`): two local two-spans and one global
two-span, i.e. SIX `Nat.log2` evaluations per query (each two-span
evaluates `Nat.log2` once directly and once inside `bpSparseLogSpan`).

This worker's own subagent survey found these same declarations but
classified them as a dead parallel family, which was exactly backwards.
Recorded because the error is instructive: the `Costed`/`TraceResult`
refinement ladder and the `FlatStoreComputation` execution ladder are
near-homonyms, and a caller-chain walk that starts from the wrong ladder
terminates plausibly rather than visibly failing.

### CORRECTION 2: no new segment and no new ReviewerSource are required

`flatStoreExecutionTraceResultAtSegment` (`InteriorRAM.lean:175-180`) maps
the WHOLE flat-store interior execution onto ONE component segment. The
new table therefore joins the existing interior component store
(`canonicalRelativeRmmInteriorComponentStore`, addressed through
`canonicalRelativeRmmInteriorComponentOffsets`) as an additional region,
exactly as the local and global sparse tables already do. This is the
property that made B6 cheap and it holds here. REQ-B7-04 is correspondingly
lighter than frozen: `canonical_segments_complete` does NOT move, and no
new `ReviewerSource` constructor is added.

### THE DECISIVE NUMBER: the interior cap is genuinely tight. 207 -> 210.

Settled by reading the cap proof
`canonicalRelativeRmmInteriorRangeMinCosted_cost_le_thirty_of_size_ge_four_of_bounded`
(`InteriorDirectory.lean:4451-4510`) rather than inferring it. The four
branches discharge against
`canonicalRelativeRmmPrincipledInteriorChargedTraceCost = 30`
(`InteriorDirectory.lean:1783`) as follows:

- within-macro: `...LocalTwoSpanCandidateCosted_cost_le_eighteen_of_size_ge_four`
  (`:4289`), then `Nat.le_trans` to 30. SLACK 12.
- adjacent: `...AdjacentMacroCandidateCosted_cost_le_twenty_of_macro_crossing`
  (`:4358`), then `Nat.le_trans` to 30. SLACK 10.
- left-middle: `...LeftMiddleMacroCandidateCosted_cost_le_twenty_of_macro_crossing`,
  then `Nat.le_trans` to 30. SLACK 10.
- cross-macro: `...CrossMacroCandidateCosted_cost_le_thirty_of_macro_crossing`
  applied DIRECTLY, with NO `Nat.le_trans` and no numeric slack. SLACK 0.

The cross-macro branch is three two-spans at
`...TwoSpanCandidateCosted_cost_le_ten_of_macro_crossing` (`:4310`,
`:4334`), each two span candidates at
`...SpanCandidateCosted_cost_le_five_of_macro_crossing` (`:4224`, `:4260`):
3 * 2 * 5 = 30, attained. THE CAP IS EXACTLY TIGHT AND HAS ZERO SLACK.

Note the machine family's caps differ from the `PayloadLive` family's
under a different hypothesis: `..._cost_le_eighteen_of_size_ge_four` (span
<= 9, `:4164`) versus `..._cost_le_ten_of_macro_crossing` (span <= 5).
DD-20260718-012 reasoned from the `PayloadLive` numbers and reached the
right conclusion for a partly wrong reason; the conclusion is now
established on the executed family.

Adding one packed level/span read per two-span call therefore gives, on
the maximizing cross-macro branch, 3 * 11 = 33, and through the named
algebra (`SuccinctFinalRAM.lean:8810-8820`):

    closeLCA   = 2*11 + 2*37 + 33 = 129   (was 126)
    wholeQuery = 2*35 + 129 + 11  = 210   (was 207)

The other three branches absorb their added read inside existing slack
(18 -> 20, 20 -> 22, 20 -> 22, all <= 30), so the cross-macro branch alone
drives the move. 207 is to be frozen as
`concreteBPNativeSuccinctRMQSilentSparseLevelChargedTraceCost` by the
142/76/328 pattern, with every consumer and the `SumLe207` topology anchor
migrated to 210, and frozen legacy anchors untouched.

CONSEQUENCE FOR PLANNING, recorded honestly: this makes the rung a
3-4 session job rather than a B6-shaped 2-session one, because the moved
literal drags the full claim-registry and documentation migration surface.

### CORRECTION 3: sizing should reuse the existing envelopes, via two
### instantiations of one generic table

DD-20260718-012 proposed a single merged table over
`macroSize + macroCount + 1`. That merged domain matches no existing
asymptotic envelope and would require a fresh `LittleOLinear` argument.
Superseded: build ONE generic count-indexed table construction and
INSTANTIATE IT TWICE - a local table indexed by `count <= macroSize`
(~`b^2` rows) and a global table indexed by
`macroSpanCount <= macroSampleCount` (~`n / b^3` rows), with
`b = Nat.log2 shape.size + 1`. The global instance's budget is exactly
`logLogSampledDirectoryOverhead_littleO` (`Asymptotics.lean:243`), the
envelope the existing global sparse block table already uses, dominated
via `LittleOLinear.of_le` (`:35`); the local instance repackages
`eventually_scale_log2_succ_cube_le_self` (`Asymptotics.lean:516`). One
set of lemmas, two sources, no new asymptotics.

Explicitly NOT to be copied: the chunk-table pattern
(`bpFringeTableOverhead_littleO`), whose exponential-slack threshold
argument exists only because chunk tables have `2^c` rows. Those steps are
vacuous for a count-indexed table. Analogues of the linear-capacity feeds
(`bpFringeChunkRowCount_le_linear`,
`bpChunkSelectEntryWidth_le_machineWordBits_capacity`) ARE still needed and
are easier here.

### Also superseded

The E1 note at `E1_WORKLOG.md:2340-2343`, which rejected a table read
because it "breaks REQ-E1-04 positional receipt equality", is over-strict
and is not a constraint on this rung: B2, B3 and B6 each added reads to
the accepted route. Changing the accepted trace is a re-freeze cost, not
an impossibility.

The msb/log2 ISA option is dead for a sharper reason than the user
decision alone: at the trace layer cost IS trace length, so an event-free
msb instruction costs ZERO there and buys nothing at the layer where the
route's charge policy lives. The standardness claim for a unit-cost msb is
also unsubstantiated anywhere in this repository.

## DD-20260719-001: B7 packed-cell width tightened rather than re-migrating the literal 210 -> 213 (B7 session 8)

Context. B7-07 derived, from the cost model rather than from the mechanism
prose, that the charged sparse-level cell did not fit in one machine word on
reachable shapes: `canonicalRelativeRmmMachineReadNatCosted_cost_le_one`
requires `width <= machineWordBits shape.bpCode.length`, and at `size = 2048`
the stored width was 15 against a 13-bit word, so each level read cost 2, not
1. That would have made the cross-macro branch `30 + 3*2 = 36` and the route
literal `213`, not the `210` commit A had already frozen and migrated.

Two routes were available: tighten the width so that commit A's `210` is
recovered, or re-migrate `210 -> 213` and freeze `210` as a second historical
constant. THE COORDINATOR RULED: tighten the width. The reasoning is a POLICY
point and is recorded here as such, not as a cost preference.

### The policy: the historical record must not accumulate fictions

A frozen historical constant records a value that GENUINELY DESCRIBED THE
ACCEPTED ROUTE at some point in its history. `76`, `142` and `207` each did.
`210` never did. It exists only inside commit A's staging window and is an
artifact of a deliberately loosened cap - commit A widened the interior cap to
`33` in anticipation of reads that had not yet landed, and the harness
confirmed at that commit that every interior window was unchanged. Freezing
`210` would place a value in the permanent historical record that never
described a real machine. That is worse than redoing a migration, which costs
only work.

### The engineering: the width fix is independently the better change

`bpSparseLevelCell domain i = bpSparseLogSpan i + domain * Nat.log2 i` was
bounded by `domain * domain`, which bounds the stored LEVEL by `domain`. But
the level is `Nat.log2 i` with `i < domain`, so it is bounded by
`Nat.log2 domain` - exponentially smaller. The old bound was slack by
construction, not by necessity. The honest bound, now proved as
`bpSparseLevelCell_lt`, is

    bpSparseLevelCell domain i < domain * (Nat.log2 domain + 1)

and the stored width is correspondingly

    bpSparseLevelWidth domain = Nat.log2 (domain * (Nat.log2 domain + 1)) + 1.

This makes the read genuinely ONE MACHINE WORD, which is what "one charged
read per two-span call" was always supposed to mean.

### CORRECTION OF RECORD, coordinator-initiated

The phrase "one charged read per two-span call" was the COORDINATOR'S, and it
was WRONG as stated: in this cost model a read costs one unit PER MACHINE WORD
TOUCHED, so the phrase asserts a width fact that nobody had checked. B7-07 was
right to compute actual widths against `machineWordBits` rather than trust it.
This is the second time this rung has corrected the coordinator (the first was
DD-20260718-013's executed-family correction, which went the other way).

### The fit is proved for ALL shapes, not sampled

B7-07's evidence was a table of three sizes. A sampled table is NOT sufficient
evidence for a width claim, and the fit PLAUSIBLY FAILS at small shapes: at
`size = 4` the base is 3, `macroSize` 9, the domain 11, and the tightened width
6 against a `machineWordBits` of 4. The claim is saved there not by the width
but by UNREACHABILITY - macro crossing needs `macroSize < blockCount`, and at
`size = 4` that is `9 < 1`, which is false.

So the all-size statement carries a reachability hypothesis, and getting that
hypothesis exactly right IS the work. The hypothesis used is the one THE
ROUTE'S OWN DISPATCH ALREADY ESTABLISHES, not a size threshold introduced for
convenience:

    theorem bpSparseLevelLocalWidth_le_machine_of_macro_crossing
        {shape : Cartesian.CartesianShape}
        (hmacro : (RelativeRmm.canonicalLayout shape).macroSize <
            (RelativeRmm.canonicalLayout shape).blockCount) :
        bpSparseLevelWidth
            (bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize) <=
          SuccinctRank.machineWordBits shape.bpCode.length

with the global twin
`bpSparseLevelGlobalWidth_le_machine_of_macro_crossing` over
`(RelativeRmm.canonicalLayout shape).macroSampleCount`.

`hmacro` is exactly what the interior dispatcher derives before it can reach a
cross-macro two-span call, from its own branch guard `hcross` together with the
route-level `hbound`. The precedent is
`canonicalRelativeRmmRelativeWidth_le_machine_of_macroSize_lt_blockCount`,
which carries the identical hypothesis for the relative summary field; the new
lemmas are its analogue and reuse its derivation shape.

The derivation, all steps checked in Lean with no threshold introduced:
macro crossing gives `base^3 < size`; `size < 2 ^ base` holds by definition of
`base = Nat.log2 size + 1`; together these force `10 <= base` by eliminating
`base <= 9` (at `base = 9`, `base^3 = 729` but `2^9 = 512`). With `10 <= base`
the local domain `base*base + 2` is below `2 ^ base`, so its level is at most
`base`, so the packed product is at most `2 * base^3 < 2 ^ (base+1)`, giving
width `<= base + 1 <= machineWordBits shape.bpCode.length` by the existing
`canonicalRelativeRmmBase_succ_le_machine_of_size_pos`. The global instance
runs the same way through `base * (size / base^3) <= size`.

The branches that do NOT carry `hmacro` are covered by two UNCONDITIONAL
theorems, `bpSparseLevelLocalWidth_le_seven_machine` and
`bpSparseLevelGlobalWidth_le_seven_machine`, which fit the width under
`7 * machineWordBits` and so charge those reads at the `cost_le_eight` rate.
Those branches only have to stay under the interior cap and have ample
headroom, so this is bookkeeping rather than a second obstruction.

### Space accounting re-derived, not assumed

The tighter width makes the table SMALLER, so every space bound gets easier -
but the four space-accounting links state the width SYNTACTICALLY (13
occurrences of `Nat.log2 ((x+2)*(x+2)) + 1` across the raw-overhead def, the
`527` linear feed and the envelope arithmetic), so they do not transport for
free. Rather than reprove them, a bridge is used:

    private theorem bpSparseLevelWidth_le_square_width
        {domain : Nat} (hpos : 0 < domain) :
        bpSparseLevelWidth domain <= Nat.log2 (domain * domain) + 1

so each existing bound is inherited through one `Nat.le_trans`. The `527`
capacity constant and the `LittleOLinear` envelopes are therefore UNCHANGED and
remain valid (they are now loose rather than tight, which is sound for upper
bounds). No row is weakened.

### What this does NOT decide

It does not re-derive the route literal. Commit A's `210` is EXPECTED to be
recovered, and the width fix is what makes that possible, but REQ-B7-05 demands
the literal be derived over the AMENDED route with the maximizing branch bound
exhibited. That derivation is commit B's and is not claimed here.

## DD-20260719-002: the interior's atomic table read is a seven-instruction branch block with a machine-decided validity test (E1 M3d-11)

Context. Every memory read the interior leg performs is one instance of
`FixedWidthNatTable.machineReadComputationAt`
(`MachineChunkedTableProgram.lean:343`), wrapped as
`canonicalRelativeRmmMachineReadNatComputation` (`InteriorDirectory.lean:2132`).
The maximising cross-macro branch makes thirty-three such calls
(`canonicalRelativeRmmMachineCrossMacroCandidateCosted_cost_le_thirty_three_of_macro_crossing`,
`InteriorDirectory.lean:5412`). A defect in the atom therefore multiplies by
thirty-three, so it is landed and certified on its own before any composite.

Decision. `interiorReadNat` (`E1InteriorReadBlock.lean`) is seven
instructions, ONE branch, exactly ONE `readMem`:

    Q+0 const iT entriesLen / Q+1 natLt iT iIdx iT / Q+2 const iA base
    Q+3 add iA iA iIdx / Q+4 brNZ iT (Q+6) / Q+5 const iA deadAddress
    Q+6 readMem iVal segment iA

THE VALIDITY TEST IS PERFORMED BY THE MACHINE, not by a Lean-level `if`
around the block: the route's `i < entries.length` is a `natLt` at `Q+1` on
the machine's own index register, branched on at `Q+4`. This is what
REQ-E1-05's anti-vacuity challenge demands of a guard, and it makes the
dead-address path a CHARGED path rather than a meta-level fallback. The
live path is the taken branch and the dead path the fall-through, so the
dead path costs one more controller step but NOT one more read
(`interiorReadNatCats_memoryRead_count`), matching the route's
`machineReadCostedWithStore_cost`, which charges `1` for an invalid index.

The category log `interiorReadNatCats` is INDEXED BY the route-side validity
condition and is never a numeral, per the standing discipline.

Register bank. `85 .. 88` (`iIdx`, `iVal`, `iA`, `iT`), opened fresh above
the three-way merge's `75 .. 84` (`E1CandMerge3.lean:97`) so that no interior
scratch overlaps the merge slots `mLV`/`mLP`/`mMV`/`mMP` that
`crossBlockArmProgramAt_runsTo`'s `hInterior` requires the interior to
preserve. `iIdx` is read-only, so a caller may keep an index live across a
read.

Option encoding. The route decodes with `fixedWidthNatTableMachineDecode`,
which at one chunk is `word?.map bitsToNatLE`; the machine decodes with
`decodeRead`, which is `bitsToNatLE word + 1` on a hit and `0` on a miss. The
machine register therefore carries the route's `Option Nat` in the
development's standing option-shift convention, and read success is testable
by one comparison against `0`. `interiorReadNat_route_atom` states that
correspondence together with the positional receipt equality.

## DD-20260719-003: the interior's single-chunk read shape is an EXPLICIT hypothesis, because the within-macro regime genuinely violates it (E1 M3d-11)

Context. `interiorReadNat` performs exactly one `readMem`. Whether that is
FAITHFUL to the route depends on the route's chunk count
`fixedWidthNatTableMachineChunkCount width wordSize`
(`MachineChunkedTable.lean:12`), which is variable in general.

FINDING, CHECKED NOT ASSUMED. The chunk count is NOT always one, and the two
regimes are already distinguished in the route's own cost lemmas:

* MACRO-CROSSING regime. `width <= machineWordBits` gives chunk count `1` and
  `canonicalRelativeRmmMachineReadNatCosted_cost_le_one`
  (`InteriorDirectory.lean:4060`). This is what yields `11` per two-span and
  the attained `33` on the cross-macro branch.
* WITHIN-MACRO regime. Only `width <= 7 * machineWordBits` is available, so
  chunk count is bounded by `8` and the rate is
  `canonicalRelativeRmmMachineReadNatCosted_cost_le_eight`
  (`InteriorDirectory.lean:4511`). Its consumer is the within-macro branch
  bound `canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted_cost_le_twenty_six_of_size_ge_four`
  (`:5196`), whose arithmetic is explicitly `26 = 8 + 9 + 9`. At small shapes
  ONE logical interior read can emit up to EIGHT physical read events.

Decision. `interiorReadNat`'s bridge theorem `interiorReadNat_route_atom`
carries `0 < width` and `width <= wordSize` as EXPLICIT hypotheses rather
than discharging them from the current tables. Two consequences are recorded
deliberately:

1. The block is correct but INSUFFICIENT ALONE. The interior simulation needs
   a second block: an eight-capped chunk fold for the within-macro regime.
   That is not a regression to the pre-B7 obstruction, because `8` is a
   LITERAL cap: the fold is the same truncated-subtraction cap chain
   `x - (x - 8)` that `fringeArmInit` (`E1FringeArmBlock.lean:118`) already
   uses for the fringe's `33`, so REQ-E1-06 conjunct (c) survives intact.
2. `0 < width` is the half the route's cost bound does NOT need, and it is
   stated anyway. At `width = 0` the route reads NOTHING while this block
   still reads once. An `<= 1` cost bound hides exactly that off-by-one, so
   the hypothesis is carried where a reader of the cost model would not think
   to look for it.

## DD-20260719-004: the interior chunk fold is TWO loops, and only one of them reads (E1 M3d-12)

Context. DD-20260719-003 established that the within-macro regime needs an
eight-capped chunk fold. The route's value for a multi-chunk cell is
`bitsToNatLE` of the CONCATENATION of the chunks in ascending address order
(`collectPayloadWords`, `MachineChunkedTable.lean:201`), which with
`wordSize`-bit chunks is `sum_j 2 ^ (j * wordSize) * chunk j` -- LITTLE-endian
in the chunk index.

CONSTRAINT, CHECKED NOT ASSUMED. The machine's arithmetic vocabulary
(`Instr`, `E1Machine.lean:76`) has `mulConst` and `divConst`, which scale a
register by a program CONSTANT, and no register-by-register multiply. The
little-endian term `2 ^ (j * wordSize) * chunk j` therefore cannot be formed:
it needs the running power TIMES the freshly read chunk, and both are
runtime registers. What `mulConst` alone supports is the Horner step
`acc := acc * 2 ^ wordSize + chunk j`, which accumulates BIG-endian.

Decision. The fold is two capped loops:

1. `interiorChunkReadBody` reads ASCENDING -- the order the receipt must
   match -- into a big-endian accumulator.
2. `interiorChunkCombine` reverses the base-`2 ^ wordSize` digits, restoring
   the route's little-endian value, under the same iteration count.

THE SECOND LOOP PERFORMS NO READS. It contains no `readMem`, so every
iteration contributes the empty receipt and the block's whole trace is the
read loop's trace; the reversal costs only `arithmetic` and `branch` charges.
`interiorChunkCombineCats_memoryRead_count` states the read-freeness and
`interiorChunkFoldCats_memoryRead_count` derives the block's total as exactly
the iteration count -- from the category algebra, not asserted.

Rejected alternative: reading DESCENDING so that one Horner loop suffices.
Rejected because the route's `readMany` issues ascending addresses and the
receipt obligation is POSITIONAL list equality, not set equality. Trading a
read-free arithmetic loop for a wrong trace order would have been the same
class of defect as B7's stale read order.

## DD-20260719-005: the cap is enforced BY THE MACHINE, not assumed of the constant (E1 M3d-12)

Context. Unlike the fringe's `33`, whose uncapped count derives from the
query-dependent register `fHi`, the interior's chunk count depends only on
the SHAPE (`width`, `wordSize`), so it reaches the machine as a per-shape
program constant -- like `base`, `deadAddress`, and `entriesLen` already do
in `E1InteriorReadBlock`.

The tempting simplification is to let the loop count BE that constant and
prove `chunkCount <= 8` about it. That would make the literal cap a property
of a theorem about the generator, not of the machine: a generator defect
supplying a larger constant would produce an unbounded fold with no
machine-level barrier.

Decision. `interiorChunkInit` computes the iteration count with the
truncated-subtraction cap chain `chunkCount - (chunkCount - 8)`, machine
executed, exactly as `fringeArmInit` (`E1FringeArmBlock.lean:118`) does for
`33`. The cap is therefore a property of the MACHINE: a shape presenting a
chunk count above `8` runs a SHORT fold, never an unbounded one.
`interiorChunkCount_le_eight` then separately proves no reachable shape does,
from the route's own within-macro width bound
(`canonicalRelativeRmmMachineReadNatCosted_cost_le_eight`,
`InteriorDirectory.lean:4511`), so the cap is exact rather than lossy.

Recorded deliberately: `interiorChunkCount_le_eight` carries NO `0 < wordSize`
hypothesis, because it does not need one. At `wordSize = 0` the route's own
definition gives `width / 0 = 0` and `width % 0 = width`, so the chunk count
is at most the indicator `1`. Stating the bound without a positivity side
condition keeps the cap UNCONDITIONAL, which is what the all-size claim needs.

## DD-20260719-006: the dead path is a one-chunk instance of the same fold (E1 M3d-12)

Context. `FixedWidthNatTable.machineReadComputationAt`
(`MachineChunkedTableProgram.lean:343`) splits on `i < entries.length` and
applies the SAME decode to both arms; the invalid arm reads the singleton
`[deadAddress]`. This differs from `machineReadCostedWithStore`
(`MachineChunkedTable.lean:240`), whose invalid arm maps to `fun _ => none`.
The interior consumes the COMPUTATION form, so its dead path decodes the dead
word normally rather than short-circuiting to `none`.

Decision. The machine realises the dead path by overriding `cAddr` and `cCnt`
before the loop (`interiorChunkInit` at `Q+10`/`Q+11`), making it a one-chunk
instance of the same fold, rather than branching around a separate read block.

Consequence, which is why this is worth recording: the receipt obligation
becomes UNIFORM in the validity condition.
`chunkAddrs_eq_consecutive` shows both arms of the route's split are one
consecutive index block -- `chunkCount` words from `base + i * chunkCount`, or
one word at `deadAddress` -- so a single positional equality covers both, with
no per-arm trace reasoning. The validity test itself remains machine
performed (`natLt` at `Q+1`, branched at `Q+9`), as REQ-E1-05's anti-vacuity
challenge requires of a guard.

## DD-20260719-007: interior chunk-fold register bank `89 .. 99` (E1 M3d-12)

The bank below `89` is fully allocated: `40 .. 62` fringe fold, `63 .. 68`
arm, `69 .. 71` same-block, `72 .. 74` dispatch, `75 .. 84` three-way merge
(`E1CandMerge3.lean:97`), `85 .. 88` the interior atom
(`E1InteriorReadBlock.lean:89`). The chunk fold opens at `89`.

Chosen so the fold's scratch is disjoint both from the merge slots
`mLV`/`mLP`/`mMV`/`mMP` that the cross-block composition requires the interior
to preserve, and from the atom's own bank: the fold READS `iIdx` (`85`) as its
logical index input and writes nothing below `89`.

## DD-20260719-008: the chunk fold's value bridge, and where `bitsToNatLE_append` lives (E1 M3d-13)

Context. `interiorChunkFold_runsTo` (`E1InteriorChunkFold.lean:1785`) proved
the fold's RECEIPT against the route positionally but stated its VALUE only in
the machine's own vocabulary (`chunkRevAt` of `chunkAcc`). Closing that gap
needs `bitsToNatLE` distributed over the chunk concatenation
`collectPayloadWords` builds, and the repository had no such lemma: only
`TablesRAM.lean:18` (the two namespaces' decoders agree) and
`WordStore.lean:53` (a fixed-width round trip) existed.

Decision 1 -- placement. `bitsToNatLE_append` is proved in the new module
`RMQ/Core/WordRAM/E1InteriorChunkValue.lean`, not added to
`RMQ/Core/SuccinctSpace/WordStore.lean` where `bitsToNatLE` is defined.
`WordStore.lean` sits near the root of the space-side import graph; adding to
it rebuilds essentially the whole tree for a lemma only the E1 machine bridge
consumes, and touches a frozen space-side module for no proof-side benefit.
If a second consumer appears the lemma should be promoted, and this entry is
the record of why it is where it is.

Decision 2 -- the reversal is generalised, and had to be.
`chunkRevAt` (`E1InteriorChunkFold.lean:1099`) peels a base-`scale` digit off
the BOTTOM of the accumulator; `chunkAcc` (`:656`) builds one ONTO the bottom.
The two recursions run in opposite directions, so no induction on `chunkRevAt`
alone lines them up. `chunkRevGen` exposes the partially built little-endian
result as a parameter and `chunkRevGen_succ_front` proves a step may be taken
at the FRONT instead of the end; that single identity is what collapses the
mismatch to one induction. `chunkRevAt_eq_gen` keeps the original definition
authoritative -- the generalisation is a proof device, not a redefinition of
what the machine computes.

Decision 3 -- the width premise is carried, not hidden.
`chunkFoldValue_eq_route_decode` and `interiorChunkFold_cOut_eq_routeDecode`
carry `∀ j < n, ∀ w, store.readWord? segment (start + j) = some w →
w.length = wordSize` as an explicit hypothesis. This is NOT decoration in the
sense DD-20260719-005 warned about: a ragged store makes the route's
concatenation carry a value no fixed-base digit reversal reproduces, so the
machine would be WRONG rather than merely unproved. It is discharged where the
fold meets a concrete `BoundedPayloadWordStore`, and until then it is visible
debt. `witnessWidth_cell0` discharges it on the existing witness store, and
`witnessCOut_cell0_via_bridge` derives `2` -- the value
`chunkFoldWitness_path_bothPresent` obtained by RUNNING the machine -- through
the bridge rather than by `rfl`, so the premise set is demonstrably
satisfiable.

## DD-20260719-009: the chunk fold's width premise is re-cut, because the stated one was unsatisfiable at the target store (E1 M3d-14)

Context. DD-20260719-008 recorded the value bridge's per-chunk width premise
as a visible debt, to be discharged "on the `BoundedPayloadWordStore` side"
where the fold meets `canonicalRelativeRmmInteriorComponentStore`. M3d-14 was
directed to source that fact BEFORE composing the summary group. Sourcing it
established that IT CANNOT BE SOURCED: the premise as stated is not merely
unproved there, it is FALSE there, so the bridge was vacuous at the one store
the interior composition needs it against.

The evidence, all read at source. `interiorChunkFold_cOut_eq_routeDecode`
demanded `w.length = wordSize` of EVERY chunk. But
`fixedWidthNatTableMachineWords` (`MachineChunkedTable.lean:15`) is a bare
`table.store.words.toList.flatMap (chunkPayloadWords wordSize)` -- no padding
at any point on the path -- and `chunkPayloadWords` is documented at
`WordStore.lean:153` as "The final word may be shorter". Accordingly
`BoundedPayloadWordStore` carries only `word_length_le` (`:552`), an
INEQUALITY, and that is the strongest fact available. Nor is the shortfall a
boundary case: `superWidth _ shape` (`RelativeSummary.lean:1290`) is
`machineWordBits shape.bpCode.length`, i.e. `wordSize` itself, but
`offsetWidth` (`:1299`) and `blockAddressWidth` (`:1308`) apply
`machineWordBits` to `layout.macroSize` and `layout.blockCount`, both strictly
smaller, so those chunks are strictly narrower than `wordSize` for any
nontrivial shape. Seven of the interior store's eight components fail the old
premise.

Decision -- the premise is SPLIT, not deleted, and the split is forced by
where exactness is actually consumed. Exactness enters at exactly one place:
`bitsToNatLE_append` produces `2 ^ w.length * bitsToNatLE tail`, and the old
`hw` was used only to turn `2 ^ w.length` into the fold's uniform digit weight
`2 ^ wordSize`. When the chunk is the LAST one, `tail` is empty, that term is
`2 ^ w.length * 0`, and the width is irrelevant. The premise was therefore
over-demanding by one index.

* `chunkFoldValue_eq_route_decode` asks equality only at `j + 1 < n`.
* `chunkDigit_lt` and `chunkRevAt_chunkAcc_eq_chunkLit` ask only
  `w.length <= wordSize`; the digit bound needs `2 ^ w.length <= 2 ^ wordSize`,
  never equality.
* `interiorChunkFold_cOut_eq_routeDecode` carries both: `hle` (bound, every
  chunk) and `hexact` (equality, non-final chunks).

Why this is the right cut rather than a convenient one. The ROUTE imposes no
width discipline at all -- `fixedWidthNatTableMachineDecode`
(`MachineChunkedTable.lean:215`) is `(collectPayloadWords words).map
bitsToNatLE`, plain concatenation -- and it MUST NOT, because the store's
`erases` obligation says the chunks flatten back to the exact `width`-bit
payload. Padding chunks up to `wordSize` would break `erases`. So raggedness
is a property of the design, not an accident to be legislated away, and the
machine-side premise had to be the thing that moved.

Both halves now discharge at the target store: `hle` is verbatim the store's
own `word_length_le` field, and `hexact` is VACUOUS there, because the
interior tables are single-chunk -- `canonicalRelativeRmmMachineReadNatCosted_cost_le_one`
(`InteriorDirectory.lean:4060`) derives `chunkCount <= 1` from
`width <= machineWordBits shape.bpCode.length`, note the inequality.

This is a strengthening: premises weakened, conclusions untouched, nothing
renamed or deleted. Anti-vacuity is preserved and was re-checked, not assumed:
the witness store is a genuine TWO-chunk fixture (`chunkIters 3 2 0 = 2`), so
`hexact` is still exercised at `j = 0`, and `witnessCOut_cell0_via_bridge`
still derives the machine's cell through the bridge onto the same `2` that
`chunkFoldWitness_path_bothPresent` obtains by RUNNING the machine.

Recorded because it generalises, in the same spirit as M3d-13's preservation
finding: a premise that is merely UNPROVED and a premise that is UNSATISFIABLE
look identical at the definition site, and both look like diligence. The
difference only appears when someone tries to discharge it against the
concrete object. A hypothesis stated as a visible debt should name the store
it is owed against and be checked for satisfiability there AT THE TIME IT IS
STATED, not at the time it is consumed.

## DD-20260719-010: the chunk fold's cap and positivity discharge unconditionally, and the interior is NOT single-chunk (E1 M3d-15)

Context. M3d-14's resume point directed that the `<= 8` cap receive the same
satisfiability audit the width premise had just failed, BEFORE anything was
composed on it. `interiorChunkFold_runsTo` (`E1InteriorChunkFold.lean:1795`)
carries two hypotheses that no consumer has yet discharged: `hccPos :
0 < chunkCount` and `hccCap : chunkCount <= 8`. Both are audited here, at
`canonicalRelativeRmmInteriorComponentStore`, for all eight of its tables.

Verdict. BOTH ARE SATISFIABLE, UNCONDITIONALLY IN `shape`. The discharge is
landed as executable Lean in `RMQ/Core/WordRAM/E1InteriorChunkCap.lean`, one
theorem per width, so the composition cites a proof rather than a note.

Decision -- the cap is discharged via `interiorChunkCount_le_eight`, NOT via
the anticipated `chunkCount <= 1`. The expected route was
`canonicalRelativeRmmMachineReadNatCosted_cost_le_one`
(`InteriorDirectory.lean:4060`). It fails three ways, the third fatally:

1. WRONG SHAPE. It concludes `(...).cost <= 1`, a statement about the route's
   COST. `hcap` is about `fixedWidthNatTableMachineChunkCount`. The two agree
   only on the valid arm of the `i < entries.length` split.
2. HYPOTHESIS UNAVAILABLE. It needs `width <= machineWordBits
   shape.bpCode.length`. For `minRelTable`, `maxRelTable` and
   `argOffsetTable` that bound is not unconditional: the only `relativeWidth`
   bounds against ONE word are `..._lt_two_machine_of_size_ge_four` (`:3970`)
   and `..._le_machine_of_macroSize_lt_blockCount` (`:4104`). The
   unconditional bound is `..._le_seven_machine` (`:3855`), against SEVEN.
3. FALSE AT REACHABLE SHAPES. See below.

The five `_le_seven_machine` lemmas (`:3855`, `:3875`, `:3899`, `:4240`,
`:4257`) are hypothesis-free apart from the shape, and together with the
`superWidth` case they cover all eight tables. `interiorChunkCount_le_eight`
wants exactly `width <= 7 * wordSize` and carries no positivity side
condition, so it composes directly. Positivity is likewise unconditional:
every width is `machineWordBits _` (positive by `machineWordBits_pos`),
`2 * _ + 3`, or `Nat.log2 _ + 1`.

THE FINDING THAT MATTERS MOST, and it corrects a previous decision. The
interior tables are NOT single-chunk. `machineWordBits n = Nat.log2 n + 1`
(`SuccinctRank.lean:38`), so the counts are computable, and evaluating
`(size, wordSize, relativeWidth, chunkCount)` gives `(1,2,5,3)`, `(2,3,7,3)`,
`(4,4,7,2)`, `(8,5,9,2)`, `(16,6,9,2)`, `(64,8,9,2)`, `(256,10,11,2)`,
`(1024,12,11,1)`, `(4096,14,11,1)`, `(65536,18,13,1)`. Every `shape.size`
below roughly `1024` is multi-chunk; the smallest are three-chunk. The tables
become single-chunk only asymptotically, as `2 * log2 (log2 size)` falls
behind `log2 (2 * size)`.

CONSEQUENCE FOR DD-20260719-009. That decision discharged the value bridge's
exactness premise `hexact` at this store by declaring it "VACUOUS there,
because the interior tables are single-chunk". That justification does not
hold. At `shape.size < 1024` the premise is LIVE, at precisely the small
shapes an all-size claim must cover. The CUT that DD-009 made -- exactness
only for non-final chunks -- remains correct and is untouched; only its
discharge story was wrong. `hexact` is still satisfiable, but substantively:
`chunkPayloadWords` emits chunks of length exactly `wordSize` except possibly
the last, and `chunkPayloadWords_get?_eq_take_drop` (`WordStore.lean:274`)
presents the chunk at index `k` as a `take wordSize` of a `drop`, which is
full whenever a later chunk exists. Whoever composes the value bridge must
discharge `hexact` from that, and must NOT cite vacuity. Nothing is retracted
and nothing weakened; a justification is replaced by a correct one.

Why the audit found this and a review did not. The satisfiability question
and the vacuity question are the same question asked from opposite ends, and
answering only one of them is what let both defects through. A premise can be
unsatisfiable (M3d-14's width premise), or satisfiable but believed vacuous
when it is live (this one). Neither is visible at the definition site, and
neither is visible from a bound alone -- a `<=` fact says nothing about
whether the quantity is ever large, and the fastest way to find out here was
to EVALUATE the count rather than reason about it.

## DD-20260719-011: non-final-chunk exactness is proved substantively, and the lemma it needed already existed (E1 M3d-16)

Context. DD-20260719-010 established that `hexact` -- the value bridge's
per-chunk width-equality premise
(`interiorChunkFold_cOut_eq_routeDecode`, `E1InteriorChunkValue.lean:526`)
-- is a LIVE obligation at `canonicalRelativeRmmInteriorComponentStore`,
not a vacuous one, because the interior tables are multi-chunk at every
`shape.size` below roughly `1024`. It directed that whoever composes the
value bridge must discharge it substantively from `chunkPayloadWords`'s own
structure and must not cite vacuity. That is done here.

Decision -- the discharge is landed as
`RMQ/Core/WordRAM/E1InteriorChunkExact.lean`, whose headline is

    machineWords_length_eq_of_succ_lt_chunkCount

the machine word at flat index `i * count + j`, for a cell index the table
holds and a chunk index with another chunk above it, has length exactly
`wordSize`. Its arithmetic core is factored out as
`succ_mul_le_of_succ_lt_chunkCount`: both arms of the `width % wordSize`
split give `j + 1 <= width / wordSize`, after which `Nat.div_mul_le_self`
finishes. The bridge-shaped corollary is `hexact_of_segment_agrees`.

CORRECTION TO THE M3d-16 RESUME DIRECTION, recorded because it was checked
rather than assumed. The delegation carried forward a claim that the
intended source lemma, `chunkPayloadWords_get?_eq_take_drop`
(`WordStore.lean:274`), "does not exist" and would have to be proved. IT
EXISTS, at exactly that file and line, with exactly the per-index
presentation needed (`word = (payload.drop (i * wordSize)).take wordSize`),
and four modules already cite it: `GenericSelect/DenseWord.lean:38`,
`RankSelectCompressed/Base/ClassLengthEnvelope.lean:2679`,
`RankSelectCompressed/Base/LogChunks.lean:681`,
`RankSelectCompressedSubLogDenseWord.lean:222`. The new module's proof
CALLS it and compiles, which settles the question by construction rather
than by grep. What was actually missing was only the arithmetic step above
and the flat-index bookkeeping; DD-20260719-010's original direction was
correct as written, and the "does not exist" gloss added downstream of it
was wrong.

The two length lemmas the same direction offered as the existing
alternatives -- `chunkPayloadWords_word_length_le` (`:234`) and
`chunkPayloadWords_length_eq_div_add_indicator` (`:390`) -- ARE, as
described, about bounds and counts rather than per-index exactness. That
half of the claim holds; it is the non-existence half that does not.

Anti-vacuity, applied to this module's own statement and not only to its
inputs, per the standing rule that where a quantity is computable it must
be EVALUATED. `exactFixture_*` executes the claim on the `shape.size = 1`
interior row (`wordSize = 2`, width `5`, `chunkCount = 3`), the most
multi-chunk reachable shape: the two non-final chunks have length exactly
`2`, and `exactFixture_final_length_lt` shows the FINAL chunk has length
`1`. So the `j + 1 < n` guard is load-bearing -- dropping it does not
weaken the statement, it makes it FALSE at a reachable shape. All four
fixture theorems depend on NO axioms.

The corollary's one carried premise, `hagree` (the segment-to-table
mapping), is left as a parameter deliberately: it is fixed by the interior
composition's segment assignment, not by this module, and stating a
concrete layout here would guess something this module cannot check.
Per the satisfiability rule it does not ship undischarged --
`segmentStore` / `segmentStore_agrees` exhibit a store meeting it, so
nothing composed on the corollary rests on an unmeetable hypothesis.

## DD-20260719-012: the fold's agreement premise was FALSE at the interior store; it is re-cut BOUNDED and discharged there (E1 M3d-17)

Context. `hexact_of_segment_agrees` (`E1InteriorChunkExact.lean`) reduced the
value bridge's exactness premise to one parameter, `hagree`: that the
machine's flat store agrees, at a table's base offset, with that table's
machine word list. DD-20260719-011's session exhibited a store meeting it
(`segmentStore_agrees`) and recorded, unprompted, that this shows the premise
SATISFIABLE and not that it HOLDS at
`canonicalRelativeRmmInteriorComponentStore`. Closing that gap was this
session's task.

Finding. THE PREMISE AS STATED IS FALSE AT THAT STORE -- for seven of its
eight tables. `hagree` was unbounded, asserting agreement at EVERY address
`base + a`. But `canonicalRelativeRmmInteriorComponentStore` is the
CONCATENATION of the eight tables' machine word lists
(`canonicalRelativeRmmInteriorComponentStore_words_toList`,
`InteriorDirectory.lean:1665`). Past the end of any one table the store still
answers `some` -- with the NEXT table's word -- while
`(fixedWidthNatTableMachineWords table wordSize)[a]?` has run out and answers
`none`. Only the final component, `globalLevel`, escapes.

Settled by EVALUATION before anything was built on it, per the standing rule.
`#eval` at the one-node shape gives `(baselineWords, storeWords) = (2, 31)`,
so the unbounded premise is wrong about twenty-nine addresses, not a boundary
one. Larger shapes are worse, not better: `(1, 38)`, `(1, 69)`, `(1, 133)`.

This is the SAME FAILURE CLASS DD-20260719-009 recorded one level down, and
the third consecutive instance: a hypothesis that looks merely unproved at
the definition site and is unmeetable at the intended instantiation. It
survived a session, a coordinator review and an explicit satisfiability
witness -- because the witness was honest and answered a different question.
`segmentStore` is a store built to hold ONE table, and one table is exactly
the case where the unbounded form is fine.

Decision -- BOUND the premise; do not weaken any conclusion. `hagree` now
reads

    forall a, a < (fixedWidthNatTableMachineWords table wordSize).length ->
      store.readWord? segment (base + a) =
        (fixedWidthNatTableMachineWords table wordSize)[a]?

and `machineWords_index_lt` (new, `E1InteriorChunkExact.lean`) supplies the
bound internally at the ONE index the proof uses, `i * chunkCount + j`, from
`List.mul_add_le_flatMap_length_of_constant_length`
(`MachineChunkedTable.lean:98`) for a cell the table holds and a chunk below
the count. STRENGTHENING ONLY: premise weakened, conclusion untouched,
nothing renamed, and the corollary is local so no external consumer moves.

Why bounded is the right cut and not a retreat. The bounded form is exactly
what an append decomposition yields, so it discharges at the interior store
for ALL EIGHT tables with no side conditions, from two facts: the store's
word list is the eight-fold append, and
`canonicalRelativeRmmInteriorComponentOffsets` (`InteriorDirectory.lean:1614`)
is the running prefix sums of that append. Those offsets are the same
constants the ROUTE's own read computations use (`:2282`, `:2317`, `:2335`),
so the agreement proved is agreement with the route's addressing, not with a
layout chosen here. Landed as `hagree_baseline` .. `hagree_globalLevel` in
`RMQ/Core/WordRAM/E1InteriorChunkStore.lean`, with `hexact` itself then
composed for the summary group's four reads (`hexact_baseline`,
`hexact_minRel`, `hexact_maxRel`, `hexact_argOffset`).

The bound is proved LOAD-BEARING, not asserted to be. `unbounded_agreement_refuted`
derives `False` from the unbounded form at any shape whose `minRel` table is
non-empty. Note what it is NOT: it is not a fixture. The numeric statement
was written first and does not compile -- the interior store's sizes run
through `Nat.log2`, which Lean defines by well-founded recursion, so the
compiler evaluates it but THE KERNEL CANNOT REDUCE IT and both `rfl` and
`decide` fail. `native_decide` would close it and is forbidden, correctly,
since it moves the check out of the kernel. Proving it generally is stronger
than the fixture would have been anyway: it holds at every reachable shape
rather than at one.

Residual, stated so it stays visible. `HoldsInteriorStore` -- that the
machine's flat store at `segment` holds the interior directory -- is carried
as a SETUP hypothesis, and every clause here is conditional on exactly it.
It is not a mathematical debt of the same kind: it says the machine was
loaded with the directory the route reads, and it is what the interior
program's own wiring will establish when the summary group is written.
Per the satisfiability rule it does not ship unwitnessed: `interiorReadStore`
/ `interiorReadStore_holds` exhibit a store meeting it. That witness is
subject to the same caution this entry records about `segmentStore` -- it
shows the hypothesis meetable, NOT that the eventual concrete machine store
meets it, and whoever wires the interior program owes the latter.

## DD-20260719-013: the interior store hypothesis is ELIMINATED BY INSTANTIATION at the store the route runs against (E1 M3d-18)

Context. DD-20260719-012 re-cut `hagree` bounded and supplied all eight
clauses at `canonicalRelativeRmmInteriorComponentStore`, but left twelve
clauses -- eight `hagree_*`, four `hexact_*` -- carrying the setup
hypothesis `HoldsInteriorStore store segment shape`, witnessed satisfiable
by `interiorReadStore` / `interiorReadStore_holds`. That session recorded
against its own output that this is the same shape of witness that hid the
false unbounded premise: a store built FOR the hypothesis, not found AT the
target.

Decision. The hypothesis is eliminated rather than witnessed. The delivered
clauses -- the ones the summary group consumes -- are unconditional.

The target is not a matter of choice. `crossBlockArmProgramAt_runsTo`
(`E1CrossBlockArm.lean:1143`) names the store in its own `hInterior`
premise: the interior leg's `RunsTo` must hold at
`concreteBPNativeSuccinctRMQGlobalReadStore shape`. No other store's
behaviour is relevant, and the interior's author does not get to pick one.

It holds there, and the tree already knew it.
`concreteBPNativeSuccinctRMQGlobalReadStore` answers segment `20` with
`(canonicalRelativeRmmInteriorComponentStore shape).store.words[index]?`
(`Segments.lean:221`); `concreteBPNativeInteriorTraceSegments`
(`Segments.lean:60`) sets `canonicalComponent := 20`. The projection
`concreteBPNativeSuccinctRMQGlobalReadStore_canonicalComponent`
(`Segments.lean:258`) was introduced by commit `b8ae4aa` ("Close U2 uniform
reviewer route") and is present at the branch base `d90b062` -- it predates
this campaign's interior work and was written for the flat reviewer layout,
not for this premise. `holdsInteriorStore_concrete` is that projection plus
the `Array`/`List` bridge, and nothing else.

So the discharge is FOUND at the target rather than BUILT for the premise,
which is the distinction DD-20260719-012's fifth standing rule turns on.
With no hypothesis left there is no witness to construct and no way for a
convenient witness to hide a false premise.

Checked, not assumed, that the segment is the right one. The `summary`
sub-record of `concreteBPNativeInteriorTraceSegments` carries
`minRel := 21`, `maxRel := 22`, which in the CANONICAL store are the fringe
and select chunk tables (`Segments.lean:224`, `:228`) -- reading there would
be silently wrong. It does not arise: the summary group
(`InteriorDirectory.lean:2277`) reads all four tables at OFFSETS
(`offsets.baseline`, `.minRel`, `.maxRel`, `.argOffset`) into one flat
store, and `FlatStoreComputation` (`MachineChunkedTableProgram.lean:66`)
runs over a single `FlatWordStore`. One segment, four offsets. The eight
`hagree_*_concrete` are stated in exactly that shape.

Scope. `E1InteriorChunkStore`'s parameterised forms are RETAINED as the
general lemmas these instantiate, exactly as `readWord?_slice` is retained
beneath them -- nothing is renamed or deleted. What changes is that the
delivered clauses carry no agreement hypothesis, matching every prior E1
module (`E1RankCanonical.lean:127`, `E1CrossBlockArm.lean:1143`,
`ChargedRankSelectWiring.lean:970`). No E1 module now carries one.

Still owed, and not disguised. `hexact_*_concrete` retain `hcount`,
`hvalid`, `hentries`. These are facts about the CALLER's index arithmetic,
fixed when the summary group's program is written, and were never debts
owed to the store -- but they are premises, and under the standing rule
they owe a witness at the intended instantiation when that program lands.

## DD-20260719-014: the summary group is composed on the FOLD, with a per-stage head CATEGORY, and the `hexact` residue is discharged by how the canonical layout is DEFINED (E1 M3d-19)

Claimed this session; the maximum OBSERVED in this file was
`DD-20260719-013`, checked before claiming.

Context. DD-20260719-013 eliminated the interior store hypothesis and
delivered twelve unconditional clauses, but closed by recording that
`hexact_*_concrete` still retain `hcount`, `hvalid` and `hentries` -- caller
index-arithmetic facts, but premises nonetheless, owing a witness at the
intended instantiation when the summary group's program lands. That program
is this entry.

Decision 1: compose on the fold, uniformly. `canonicalRelativeRmmMachineSummaryComputation`
(`InteriorDirectory.lean:2277`) makes four reads. Each stage runs
`interiorChunkFold`, never `interiorReadNat`, whose route bridge carries
`0 < width` and `width <= wordSize` (`E1InteriorReadBlock.lean:443`).

That is not a defensive choice, and this session has EXECUTED evidence it is
not. At `stackCartesianShape` inputs of size 8, 16, 64 and 256 the four
chunk counts are `(1, 2, 2, 2)` at EVERY one of those sizes: the baseline
table is single-chunk, and minRel, maxRel and argOffset are TWO-chunk. So
three of the summary group's four reads are multi-chunk at every shape
evaluated, and the single-chunk atom would have been unsound for them --
not at some exotic corner, but everywhere it was tried.

Decision 2: the stage's head category is a PARAMETER, not a constant. The
four stages set `iIdx` differently -- the baseline read is at
`block / blocksPerSuper` (`divConst`, charging `.arithmetic`), the other
three at `block` (`move`, charging `.registerWrite`). Both are one-element
category logs, so fixing the head at `registerWrite` would have produced a
category log of the RIGHT LENGTH and the WRONG CONTENT in exactly one slot,
and neither a length check nor a read-count check would have caught it. The
charge is carried per stage instead.

Decision 3: the `hexact` residue is discharged by the layout's DEFINITION,
not by an added hypothesis. `canonicalSummaryLayout` defines each table's
`chunkCount` field to BE the route's `fixedWidthNatTableMachineChunkCount`
at that table's width, and each `entriesLen` field to BE the route's own
entry-list length. Two consequences, both machine-checked by the four
bridge theorems compiling:

* `hcount` is discharged by `rfl`.
* `hvalid` and `hentries` become the SAME proposition, so one caller-side
  index fact supplies both -- the four bridges below pass the same `hvalid`
  term to both arguments.

What survives to the caller is a single `i < entriesLen` obligation per
read, which is the route's own validity condition. No store hypothesis, no
chunk-count hypothesis, and no width hypothesis remains: the eight
chunk-count premises are supplied from `E1InteriorChunkCap` (unconditional
in `shape`, predating this module), and `hle` from the interior component
store's own `word_length_le` field via the segment-20 projection.

Anti-vacuity. The four `hvalid` premises would be unsatisfiable, and all
four bridges vacuous, if any entry list were empty. Evaluated: the entry
lengths are `(1,2,2,2)`, `(1,3,3,3)`, `(2,9,9,9)` and `(4,28,28,28)` at
sizes 8, 16, 64 and 256. All non-empty at every shape, so no bridge is
vacuous. This is `#eval` reproduction evidence, not a kernel proof --
these quantities run through `Nat.log2`, which the compiler evaluates but
the kernel cannot reduce.

Not cited anywhere above, deliberately:
`canonicalRelativeRmmMachineReadNatCosted_cost_le_one`. It is a COST bound,
hence an upper bound only, and supplies neither the cap at the within-macro
widths nor `0 < chunkCount`.

Recorded discrepancy, not acted on. `E1InteriorChunkValue.lean:521-524`
still says `hexact` discharges "vacuously, because the interior tables are
single-chunk". That gloss is STALE: M3d-16 discharged `hexact`
substantively via `chunkPayloadWords_get?_eq_take_drop`, and this session's
evaluation shows three of the four summary tables are two-chunk at every
shape tried, so the single-chunk premise behind the gloss is false. The
theorem itself is correct and unaffected -- only its docstring's
justification is out of date. Left for the owner of that module rather than
edited here.

## DD-20260719-015: the min-candidate consumer implements ALL FOUR presence tests, because `maxRel` is discarded by the FUNCTION and load-bearing through the OPTION STRUCTURE (E1 M3d-21)

Claimed this session; the maximum OBSERVED in this file was
`DD-20260719-014`, checked before claiming.

Context. `canonicalRelativeRmmMachineMinCandidateComputation`
(`InteriorDirectory.lean:2300`) is `summary.map (bpRelativeSummaryMinCandidate
layout.blockSize layout.blocksPerSuper block)` over the summary group's
four cells. `bpRelativeSummaryMinCandidate`
(`EndpointFringe/PrefixRange/RelativeSummaryCandidate.lean:15`) reads
`summary.1`, `summary.2.1` and `summary.2.2.2`. `maxRel` is `summary.2.2.1`
and is NEVER READ -- confirmed at source, not taken on report.

Decision: test all four cells for presence anyway, and do not collapse the
`maxRel` test.

The ground is not only the positional receipt. The summary's own assembly
(`InteriorDirectory.lean:2293-2296`) is a four-way match whose sole `some`
arm requires all four to be `some`, with `| _, _, _, _ => none` as the
catch-all. So `maxRel = none` forces the summary to `none`, hence the
min-candidate to `none`. `maxRel` is discarded by the FUNCTION and
load-bearing through the OPTION STRUCTURE.

This matters because the receipt-only reading licenses an UNSOUND block. A
block that keeps the `maxRel` READ -- satisfying the positional receipt,
the read count, the trace length and the exit code -- but ignores its
VALUE returns `some` exactly where the route returns `none`. Right shape,
wrong content, invisible to every aggregate check. The prior session
recorded this as a live fork; this entry closes it.

The `none` arm is REACHABLE, not hypothetical.
`FixedWidthNatTable.machineReadComputationAt`
(`SuccinctSpace/MachineChunkedTableProgram.lean:343`) reads `[deadAddress]`
when the index is out of range, and that decodes to `none`.

The alternative considered and REJECTED. Proving
`maxRel.entriesLen = minRel.entriesLen` would let the four-way test
collapse to two. It is rejected on two independent grounds. The equality is
evaluated equal at four sizes -- `(1,2,2,2)`, `(1,3,3,3)`, `(2,9,9,9)`,
`(4,28,28,28)` -- and proved NOWHERE in the tree, so assuming it would be
unsound; and even once proved it would make the machine's control flow
DIVERGE from the route's, where the unimpeachable option is a structural
correspondence a reviewer can diff arm-for-arm. Assuming the equality
without proving it was the one unsound option available.

Consequence for the statement. The result is stated as the ROUTE'S OWN
EXPRESSION with the route's four reads replaced by the four saved cells:
`summaryOfCells` is arm-for-arm `InteriorDirectory.lean:2293-2296`, `mx`
binder present and unused on the left exactly as it is there. The `maxRel`
cell therefore appears on BOTH sides of the theorem and is not an argument
the statement could drop.

Decision 2: `none` is the FALLTHROUGH, not a branch destination. The block
writes the `none` encoding into the output pair first and conditionally
skips the value computation. That mirrors the route's catch-all arm, and it
costs one instruction less than the alternative because no unconditional
jump -- and so no always-nonzero register -- is needed.

Decision 3: the option shift is applied LAST. The saved cells are
option-shifted and so is the output value register, but the shifts do not
cancel: the route's value is `baseline + minRel - span` with TRUNCATING Nat
subtraction. The block computes `(cB + cMn) - (span + 2)` -- folding both
shifts into the constant, valid because `a + k - (b + k) = a - b` holds
unconditionally in `Nat` -- and only then adds `1`. Adding the `1` before
the subtraction would give `(b + mn + 1) - span`, which differs from
`(b + mn - span) + 1` at every `span > b + mn`.

Anti-vacuity, EXECUTED rather than argued. The kernel runs the block on
fixtures differing in exactly one cell and the outputs differ, for each of
the four cells in turn; the `maxRel` pair is the decisive one, since that
is the mutation a receipt-only block would survive. Both arms' read logs
are `[]` by kernel reduction, and the two arms charge different category
logs. The main theorem is also instantiated at the witness fixture, so its
hypotheses are shown satisfiable at the intended instantiation rather than
at a fixture built to fit them.

## DD-20260719-016: the interior's value bridges agree with the ROUTE at every index, rather than with `0` out of range (E1 M3d-22)

Claimed this session; the maximum OBSERVED in this file was
`DD-20260719-015`, checked before claiming.

Context. The four `geomCell_*_eq_routeDecode` bridges
(`E1InteriorSummaryGroup.lean`) carried a validity premise
`i < entriesLen`, inherited from routing their `hexact` obligation through
`E1InteriorStoreConcrete.hexact_*_concrete`. The min-candidate consumer's
`none` arm is reached when a cell is ABSENT, and absence includes the
out-of-range read, so the bridges as stated could not cover the arm that
most needed them. M3d-21 recorded this asymmetry and directed the
successor to supply a "`geomCell = 0` at invalid indices" fact.

Decision: do NOT prove the zero fact. State the bridges as agreement with
the ROUTE, holding at EVERY index, and drop the validity premise entirely.

The ground is that the zero fact is FALSE as a geometry fact, and the tree
already contained the disproof. `stageCell` is `0` out of range only when
`chunkBad store segment deadAddress 1 <> 0` -- i.e. only when the dead
address is unreadable IN THE STORE. `chunkFoldWitness_path_dead`
(`E1InteriorChunkFold.lean`), an `rfl`-checked theorem predating this
session, runs the real fold at index `5` past `entriesLen = 3` and leaves
`cOut = 2`, i.e. `some 1`, because `witnessStore` holds a word at the dead
address `99`. A development that took the zero route would have been
attempting to prove something false of that store, and would have had to
import a store-level obligation about `deadAddress` to escape.

The equality route incurs no such obligation. `geomCell_eq_routeDecode`'s
only substantive premise, `hexact`, constrains NON-FINAL chunks. Out of
range the fold runs exactly ONE iteration (`chunkIters_of_invalid`), so
there is no non-final chunk and the premise is VACUOUS -- dischargeable
knowing nothing about the store. The four bridges are therefore
unconditional, and the composite
`summaryMinCandidate_runsTo` (`E1InteriorMinCandidate.lean`) carries no
validity hypothesis and no store hypothesis.

This is a strengthening: a hypothesis was removed, no statement narrowed.
The four bridges had no callers, so nothing broke.

Anti-vacuity, EXECUTED. `chunkIters_witness_discriminates` shows the
iteration count is `1` out of range and `2` at a valid index of the same
two-chunk table, so `chunkIters_of_invalid` distinguishes the cases rather
than reporting a constant. `outOfRange_cell_not_always_zero` refutes the
zero claim on the witness store by kernel computation. The composite's
`hHost` and `hBlock` are shown JOINTLY satisfiable at the intended
instantiation by `summaryMinCandidate_premises_satisfiable`, which
instantiates the theorem at the self-hosting leg with `sBlock` actually
holding `block` and carries the existential through to a concrete
consequence.

Scope, stated because the name invites over-reading. `routeDecodedSummary`
is the summary assembled from the four route DECODES. Showing it equal to
the value of `canonicalRelativeRmmMachineSummaryComputation`
(`InteriorDirectory.lean:2277`) is a FURTHER step, through
`machineReadComputationAt`, and is NOT claimed.

## DD-20260719-017: the A-to-B link is stated PARAMETRICALLY in the word size, with the shape-level form as a corollary (E1 M3d-23)

Claimed this session; the maximum OBSERVED in this file was
`DD-20260719-016`, checked before claiming.

Context. DD-20260719-016 landed the four `geomCell_*_eq_routeDecode`
bridges, which state the machine's saved cell as `geomRouteDecode` -- a
decode of an address list. That object is route-SHAPED but is not the
`FlatStoreComputation` the route actually runs, and M3d-22 recorded
explicitly that equating the two was a FURTHER step and was not claimed.
This session takes that step.

The natural statement is at shape level: `geomRouteDecode` equals the
option-shifted `.value` of `canonicalRelativeRmmMachineReadNatComputation`,
whose word size is `SuccinctRank.machineWordBits shape.bpCode.length`.

Decision: do NOT state it only at shape level. State a PARAMETRIC core,
`routeDecode_eq_machineReadComputation_value`, taking `wordSize` as an
ordinary parameter, and derive the shape-level
`geomRouteDecode_eq_readComputation_value` from it as a corollary.

The ground is ANTI-VACUITY, and it is a real fork rather than a
preference. The link is an equation between two `match`es, a shape that
can hold because both sides are constant, so it owes an executed
discrimination witness. At shape level it cannot have one: the word size
goes through `machineWordBits`, hence `Nat.log2`, which is well-founded
recursion the KERNEL cannot evaluate, and `rfl`/`decide` fail on numeric
fixtures there. M3d-22 established that boundary and correctly declined to
cross it. Parametrising the word size moves the SAME equation into
kernel-reachable territory, where it can be run on concrete data; the
shape-level statement is then an instance, so the fixtures exercise the
equation the interior actually uses rather than an analogue of it.

What the fixtures establish, EXECUTED. The witness is deliberately
MULTI-CHUNK -- three entries at width `20`, word size `8`, giving three
chunks per cell -- which is the regime where `interiorReadNat_route_atom`
(`E1InteriorReadBlock.lean`) does not apply, so the fixture exercises the
reachable interior shape and not the single-chunk special case.
`linkWitness_executed` evaluates BOTH sides at four indices and gets
`[2, 3, 0, 6]` on each: a fully present three-chunk cell, a second
differing in one chunk, a cell with a missing chunk, and the dead path.
`linkWitness_discriminates_content` is the right-shape/wrong-content
guard: cells `0` and `1` have the SAME shape, three present chunks each,
and differ only in stored bits, and the link separates them.
`linkWitness_chunkCount_load_bearing` and
`linkWitness_entriesLen_load_bearing` show the two hypotheses are not
decorative -- a wrong `chunkCount` reads a shorter address list and a
wrong `entriesLen` diverts the index down the dead path, each decoding a
different value. `linkWitness_link_instantiated` discharges rule 1: both
hypotheses jointly satisfiable at a real instantiation, carried to a
concrete consequence rather than left existential.

No cap hypothesis enters the link. `chunkAddrs_eq_consecutive`'s `hcap` is
a different equation -- it relates `chunkAddrs` to what the MACHINE's fold
generates -- and it was already consumed inside `geomCell_eq_routeDecode`.
Nothing in the link mentions the fold, so nothing in it needs the cap. Nor
is the link `interiorReadNat_route_atom`, which carries `0 < width` and
`width <= wordSize`: it assumes one chunk per cell, and the interior's
reachable shapes are multi-chunk. The link bounds `width` nowhere.

Scope, stated because the name invites over-reading. These four
corollaries link ONE read each: the machine's saved cell to the value of
the corresponding single-table read computation. Equality of
`routeDecodedSummary` with the value of
`canonicalRelativeRmmMachineSummaryComputation`, which binds four such
reads into a tuple, is a FURTHER step and is still NOT claimed.

## DD-20260719-018: the option-shift gets a NAME, and the summary tuple is claimed (E1 M3d-23)

Claimed this session; the maximum OBSERVED in this file was
`DD-20260719-017`, this session's own earlier entry, checked before
claiming.

THIS ENTRY SUPERSEDES THE CLOSING SCOPE NOTE OF DD-20260719-017. That note
said equality of `routeDecodedSummary` with the value of
`canonicalRelativeRmmMachineSummaryComputation` was "a FURTHER step and is
still NOT claimed". It is now claimed and proved. The note was true when
written and is recorded here as superseded rather than edited away.

Context. With the four per-read links in hand, binding them into the
route's four-read tuple should have been immediate: `summaryOfCells`
inverts the shift through `cellOpt`, and the route's tuple `match`
(`InteriorDirectory.lean:2294`-`:2296`) is the same four-way split. It was
not immediate, and the reason is worth recording because it is a trap that
costs a session if it is not recognised.

The failure. The links originally stated the option-shift as an INLINE
`match v with | none => 0 | some x => x + 1`. An inline `match` elaborates
to a fresh auxiliary matcher per declaration. So the inversion lemma
`cellOpt (match v with ...) = v`, stated in the consumer, was DEFEQ to the
goal and still did not fire: `simp` saw two different functions. The
symptom is an "unsolved goals" error whose goal looks character-for-
character like something `simp` should have closed.

Decision: give the shift a NAME. `E1InteriorSummaryGroup.optShift` is
defined once, the links state their conclusions with it, and the inversion
`cellOpt_optShift` is a `simp` lemma that applies. The change is
definitional -- `optShift v` is defeq to the inline match it replaces -- so
no statement moved; the four canonical corollaries and every anti-vacuity
fixture went through the refactor unchanged in content.

The general rule this instances: a shift or wrapper that CONSUMERS must
invert belongs in a named definition with a named inversion lemma. Writing
it inline is not a smaller version of the same thing; it is a version that
cannot be reasoned about across declaration boundaries.

What is now claimed. `routeDecodedSummary_eq_summaryComputation_value`
(`E1InteriorMinCandidate.lean`): the summary tuple assembled from the four
route decodes IS the value of the computation the route runs, at the
canonical store and layout, with NO validity, cap or store hypothesis --
inherited from the unconditional bridges of DD-20260719-016 and the
hypothesis-free links of DD-20260719-017. The proof is the four links, the
shift inversion, `FlatStoreExecution.append`'s value projection, and a
closing `rfl` for the defeq spellings of the four bases and
`blocksPerSuper`. `maxHeartbeats` was NOT raised and no whnf timeout was
encountered.

Scope, stated because this one also invites over-reading. This is the
tuple's VALUE. The receipt -- positional trace equality for the four reads
in the route's bind order -- is a separate obligation and is NOT claimed
here, nor is any statement about the min-candidate consumer's own output
beyond what `summaryMinCandidate_runsTo` already carries.

## DD-20260719-019: the receipt is not a corollary of the value, and the separation is EXECUTED (E1 M3d-24)

Claimed this session; the maximum OBSERVED in this file before claiming was
`DD-20260719-018`, verified by scanning the tree for `DD-` identifiers.

THIS ENTRY SUPERSEDES THE CLOSING SCOPE NOTE OF DD-20260719-018. That note
said positional trace equality for the four reads in the route's bind order
"is a separate obligation and is NOT claimed here". It is separate, and it
is now claimed and proved. The note was true when written and is recorded
here as superseded rather than edited away.

Context. `routeDecodedSummary_eq_summaryComputation_value` settles what the
summary computation RETURNS. The harness compares what the machine LOGS.
The natural temptation is to treat the second as bookkeeping on the first --
the same four reads, so surely the same receipt.

Why that is wrong, demonstrated rather than argued. The fixtures
`receiptWitness_*` (`E1InteriorMinCandidate.lean`) exhibit two four-segment
receipts that agree on EVERY aggregate an implementation is likely to check
and still differ:

* same segment count (four), same total length (12), same per-segment
  lengths (`[3,3,3,3]` both) -- `receiptWitness_staleHead_lengths_agree`;
* the SAME DECODED VALUE -- `receiptWitness_staleHead_value_agrees`, so the
  value equation is formally incapable of rejecting the impostor;
* the same stored WORDS in the same order --
  `receiptWitness_staleHead_words_agree`;
* and yet different receipts -- `receiptWitness_staleHead_discriminates`,
  because the head logged `215,216,217` where the route logs `203,204,205`
  (`receiptWitness_staleHead_addresses_differ`).

THE DEFECT MODELLED IS THE ROUTE'S OWN MOST LIKELY ONE. The baseline read is
issued at `block / blocksPerSuper`; the other three at `block`. The head is
the one segment whose index differs from its neighbours', which makes
"copy the index from the segment below" a live error rather than a
hypothetical one. The fixture is that error, and it is deliberately built on
a SIX-entry table so that the stale index `5` is a VALID cell: had it fallen
off the end it would take the dead path, the segment lengths would diverge,
and a length check would have caught it. It must not.

Decision: state the receipt POSITIONALLY AND PER-CONSTRUCTOR, never as a
length, a count, or a membership. `summaryComputation_reads_eq_routeReceipt`
writes the four segments out in issue order with each segment's INDEX
visible in the statement -- so the head's `block / blocksPerSuper` is read
off the theorem rather than trusted to a definition.

What is now claimed. `summaryMachineTrace_eq_routeReads`
(`E1InteriorMinCandidate.lean`): the trace `summaryMinCandidate_runsTo`
emits IS the read log the route's summary computation records -- same
events, same positions, same segment, addresses and words -- at the
canonical store and layout, with NO validity, cap or store hypothesis. The
bridge is `geomEvents_eq_summaryReadReceipt_map`, one segment at a time; the
machine and route spellings differ only by the injection
`(address, word) => TraceEvent.readWord segment address word`.

The general rule this instances: a VALUE equation and a RECEIPT equation are
independent obligations, and an executed witness that they can come apart is
cheap to build and worth building. Where a component already has a value
bridge, the receipt still owes its own positional statement.

Kernel boundary, restated because it shaped the fixtures. The shape-level
receipt routes its word size through `machineWordBits`, hence `Nat.log2`,
which the kernel cannot evaluate. So the executable core is the parametric
`machineReadComputation_reads` (`E1InteriorSummaryGroup.lean`), taking
`wordSize` as a parameter; the shape-level `geomReadComputation_reads` is
its corollary, and the fixtures run the parametric form at `wordSize = 8`,
width `20`, three chunks per cell -- the multi-chunk regime, with the chunk
count EVALUATED (`receiptWitness_chunkCount`) rather than inherited.

Scope, stated because this one invites over-reading too. This is the SUMMARY
GROUP's receipt, four reads, at the canonical store and layout. It is not
the interior leg's receipt, not the whole-query receipt, and it does not
discharge REQ-E1-04, which is whole-query scoped and remains Open. Nothing
here touches the span blocks, the two-span blocks or the five-branch
dispatch, all of which remain unbuilt.

## DD-20260719-030: the interior fold's preservation mutation clobbers `102`, the register the composition instantiates the clause AT (E1 LaneC)

Phase 4h needs a register that (i) satisfies `ChunkFoldUntouched`
(`E1InteriorChunkFold.lean:928`), (ii) is not a fold input, so it carries a
sentinel and any write at all is detectable, and (iii) is genuinely consumed
downstream, so the clobber is a real composition hazard rather than a
contrived one.

Chosen: `102`, which is `E1InteriorSummaryGroup.sMin`
(`E1InteriorSummaryGroup.lean:80`). It satisfies (i) through the `99 < r`
disjunct. It satisfies (ii) because `interiorChunkFold_runsTo` declares
exactly ONE input, `hIdx : regs iIdx = i`. It satisfies (iii) in the
strongest available sense: the summary group's own proof instantiates the
fold's preservation hypotheses at exactly this slot -- `hPres4 sMin`,
`hPres3 sMin` (`E1InteriorSummaryGroup.lean:427-429`) -- to carry a staged
minimum across LATER fold invocations. The witness is therefore FOUND at the
target rather than CONSTRUCTED for the premise (rule 5).

REJECTED: `iIdx` (`85`). It satisfies (i) and (iii) -- it is the caller's
block index and the fold is composed more than once -- but it FAILS (ii): it
is the fold's one genuine input, so the fixture must seed it with the real
index `i` rather than a sentinel, and detection would then depend on the
mutant happening to write a value differing from `i`. With `102` the seed is
`presSentinel 102 = 717` and the combine loop can only write `cAcc %
wordScale`, i.e. `0` or `1` on this witness, so the ranges are provably
disjoint and detection is not luck.

## DD-20260719-031: the mutation is the COMBINE loop's private scratch, renamed within the combine segment only (E1 LaneC)

Mutant H renames `cU` (`96`) to `102` across its three occurrences in
`interiorChunkCombine` (`E1InteriorChunkFold.lean:316`), restricted to fold
indices `26..33`.

Why `cU` in COMBINE is the right locus. It is written at `MB+1` before it is
read at `MB+2` and `MB+4`, and never read after, so it is a pure private temp
whose incoming value cannot matter and whose outgoing value nothing consumes:
a consistent rename performs identical arithmetic into `cRev`. The combine
loop is also READ-FREE by construction, so the mutation cannot move, add or
drop a trace event, and its trip count is driven by `cN`, so steps and control
path are identical. That is what makes it invisible to BOTH other
discriminators.

Why the rename is SEGMENT-RESTRICTED. `cU` is also used by
`interiorChunkInitHead` at `Q+3, Q+4, Q+6, Q+7, Q+8`. A global rename would
still be value-invisible on this witness -- init reads `iIdx` at `Q+1`/`Q+2`,
before `Q+3` -- but it would make the mutation's locus a coincidence of
instruction order rather than a property of the block. Restricting to
`26..33` mirrors the fringe's `mutatedArmScratch`
(`E1MachineValidate.lean`, phase 4g) and keeps the locus stated rather than
inferred.

Why substitution is REGISTER-POSITION-ONLY. `substReg` rewrites register
operands and nothing else. A blanket numeral rewrite would also hit `const`'s
value, `mulConst`/`divConst`'s scale, `readMem`'s segment, and -- the one that
silently corrupts control flow rather than failing loudly -- `brNZ`'s absolute
branch TARGET.

## DD-20260719-032: the clobber target is a documented LITERAL, not an import of the sibling-owned module (E1 LaneC)

The validator does not import `E1InteriorSummaryGroup`; `chunkClobberTarget`
is the literal `102` with the `sMin` identification recorded in its docstring.

Rationale. What the discriminator NEEDS of `102` is only that it satisfies
`ChunkFoldUntouched` and is not a fold input -- both local facts, checked
locally. The `sMin` identification is the LEGITIMACY argument (DD-030), not a
soundness dependency, so the phase stays correct even if that identification
drifts. Importing the summary group to spell the target symbolically would
couple this validator's build to a module owned by a different lane and under
active edit, for no gain in what the check actually establishes.

KNOWN COST, recorded rather than hidden: if a later session renumbers `sMin`,
the literal goes stale silently and the phase's LEGITIMACY comment becomes
wrong while the phase itself keeps passing. The mitigation is that phase 4h
prints `mutantH_clobberedRegs` and the kernel theorem
`chunkPres_mutantH_clobbers_exactly_102` names the numeral, so the drift is
visible in the diff of both.

## DD-20260719-033: the phase's counts are ALSO kernel-checked, not only printed (E1 LaneC)

`mainImpl` prints seven counts; the same seven facts are stated as theorems
and discharged by `rfl`. A printed `0` is reproducible evidence that the
kernel has not seen; these quantities are closed and computable, so rule 3
says they get EVALUATED, and stating them as theorems is what makes the
evaluation a kernel fact rather than a runtime observation.

All seven come out depending on no axioms whatsoever -- not `propext`, not
`Classical.choice`. No `decide`, no compiler-evaluated escape hatch, and no
raised heartbeat budget: `rfl` alone. Cost recorded: the seven `rfl` proofs
take the validator module's build from roughly 20s to roughly 3m45s, which is
the price of kernel-reducing four two-run machine sweeps and a 99-register
filter.

The salt is `0` in the theorems on purpose. Its only job in `mainImpl` is to
stop Lean folding the sweeps before `main` starts, which would make the
wall-clock readings meaningless; in a theorem, compile-time evaluation is
exactly what is wanted.

## DD-20260719-034: the composed 177-instruction leg is NOT given this treatment, and why that is an obstruction rather than a choice (E1 LaneC)

The intended extension was to run the same preservation treatment on
`summaryMinCandidate_runsTo` (`E1InteriorMinCandidate.lean:929`). It was not
done, for two independent reasons, neither of which is budget.

FIRST: the composed leg states no preservation clause to execute. Its
conclusion is exactly two conjuncts -- the `RunsTo` and the `bestOfRegs`
value equation (`:937-974`). Both of its components DO carry one:
`canonicalSummaryGroup_runsTo` supplies `hpres1`, and
`minCandidateBlock_runsTo` concludes `(∀ r, MinCandUntouched r → regs' r =
regs r)`. The composed proof binds the latter as `_hpres2` at `:991` --
underscore-prefixed, i.e. deliberately discarded -- and re-exports neither.
This is the same defect M3d-13 found and fixed in `interiorChunkFold_runsTo`,
recurring one level up, and it contradicts the standing rule that every block
state its preservation clause in its HEADLINE and not only in its internal
segment lemmas.

SECOND, and independent: the leg is instantiated at
`canonicalSummaryLayout shape`, whose `wordScale` routes through
`SuccinctRank.machineWordBits`, hence `Nat.log2`, which the compiler
evaluates but the kernel cannot reduce. So even with a clause to execute, a
fixture over the leg's real instantiation could only be compiler-evaluated
evidence, never a `rfl`/`decide` kernel fact of the kind DD-033 supplies for
the fold.

`E1InteriorMinCandidate.lean` is owned by a different lane, so the first
obstruction is recorded as a CROSS-LANE DEPENDENCY and not fixed here.

## DD-20260719-050: the span block's `none` arm branches past the WHOLE leg, and the impostor that skips only the summary group is rejected by NOTHING but the value and a positional category log (E1 M3d-25)

Claimed by the M3d-25 session (E1-LaneB) and cited in
`E1InteriorSpanBlock.lean` at the module header and at the discriminator
section; the entry itself was omitted from this file at that session's
commits and is written here by its successor (E1-LaneB2, M3d-27) without
renumbering. The maximum OBSERVED in this file before writing was
`DD-20260719-019`; `020`-`049` are other lanes' bands and `050` is the
identifier the module already carries, so it is used as cited rather than
compacted. Substance is taken from the module and from the session's own
report, not reconstructed.

Context. The two span computations
(`canonicalRelativeRmmMachineLocalSpanCandidateComputation` and its global
twin, `InteriorDirectory.lean`) share one shape: a staged read, then
`some value => MinCandidateComputation (BLOCK value)` against
`none => FlatStoreComputation.pure none`. On the machine side the `some`
arm falls into the composed 177-instruction min-candidate leg. The `none`
arm must do two things at once -- branch past ALL 177 instructions, and
emit nothing.

The decision is a single numeral: `spanArms`' branch target at `Q + 42`.

Decision: the `none` arm targets the block's OWN EXIT at `Q + 222`, past
the summary group's 156 instructions AND the consumer's 21. The available
wrong numeral is `Q + 45 + 156`, which branches past the group only and
lands ON the consumer.

Why that wrong numeral is the dangerous one, demonstrated rather than
argued. The summary group is where the four READS are, so an arm that fell
into the GROUP would be caught by the receipt. The consumer is READ-FREE
(`minCandidateBlock_readFree`), so an arm that falls into the CONSUMER
leaves the receipt untouched while overwriting `mMV`/`mMP` from whatever
four cells happen to be sitting in `sBase`, `sMin`, `sMax`, `sArg`. It
returns `some` where the route returns `none`, with an identical receipt.
This is RIGHT SHAPE, WRONG CONTENT, third variety, and the impostor is not
invented for the fixture: it is the one wrong numeral the block admits.

What the fixture establishes, by EXECUTION on the empty store, holding
everything fixed but that numeral (`noneArmProgram target`, correct arm
`target = 23`, impostor `target = 2`, the real consumer at its own base):

* the values differ -- `armOut_correct` is `none`, `armOut_impostor` is
  `some (5, 6)`, and `spanNoneArm_discriminates` separates them;
* THE RECEIPTS ARE EQUAL -- `spanNoneArm_traces_agree`. A receipt equation
  is FORMALLY INCAPABLE of rejecting this impostor;
* both receipts are EMPTY -- `spanNoneArm_traces_empty` -- so the read
  COUNT does not separate them either;
* both arms HALT -- `spanNoneArm_both_halt` -- so the exit code does not
  separate them;
* PRESERVATION HOLDS ON BOTH -- `armOperands_preserved_correct` and
  `armOperands_preserved_impostor`, with the four cross-block-arm operands
  `70`, `71`, `75`, `76` seeded with distinct marks so survival is
  discriminating rather than trivially true at zero.

So of the four things one can check about this block -- receipt, read
count, exit code, preservation -- NOT ONE rejects the impostor.

The boundary is stated exactly rather than implied. The value is not the
sole instrument: `spanNoneArm_catLogs_differ` shows a POSITIONAL CATEGORY
comparison also catches it, because the impostor executes the consumer's
21 instructions and logs them. Recording that is the point of the
non-entailment discipline -- the claim is "receipt, read count, exit code
and preservation do not suffice", not "only the value can ever work".

What this decides for consumers. `spanBlock_runsTo`'s value clause is
stated against the ROUTE's own `spanValue` rather than against the block's
own arithmetic, and that choice is what makes the clause load-bearing. A
value clause phrased in the block's own terms would have been satisfied by
the impostor.

The general rule this instances, and it is the one to carry into the
two-span blocks and the merge combiners: for each new block, identify the
sub-leg whose branch target differs from its neighbours', build the
impostor THERE, and state the NON-ENTAILMENTS alongside the discriminator.
A discriminator alone says a check works; the non-entailments say which
checks do not, and only the pair locates the obligation.

Scope. This is the SPAN BLOCK's `none` arm, parametric in the read
geometry, at the canonical store and layout. It does not discharge any row
of `E1_AMENDED_MACHINE_ACCEPTANCE_MATRIX.md`, all of which are whole-query
scoped and remain Open. At the time of the decision the two `TableGeom`s
instantiating the block were not yet defined, the two-span blocks, the
macro combiners and the five-branch dispatch were unbuilt, and no two-way
merge block existed on the machine side.

## DD-20260719-051: the two span geometries are DEFINED as the route's own, so the span block's route-value link carries no surviving hypothesis (E1 M3d-27)

Claimed this session (E1-LaneB2) from band `051-069`; the maximum
OBSERVED in this file before claiming was `DD-20260719-050`, this
session's own earlier entry, written on its predecessor's behalf.

Context. `spanBlock` (DD-20260719-050) is parametric in a `TableGeom`,
and the claim that ONE block covers both span computations held. What
remained was to supply the two geometries and to link the block's value
function to each route computation's value.

Decision: define `localSpanGeom` and `globalSpanGeom` field-for-field as
`canonicalSummaryLayout` defines its four, i.e. with every field spelled
as the ROUTE's own quantity -- `entriesLen` as the route's entry-list
length, `chunkCount` as the route's own
`fixedWidthNatTableMachineChunkCount` at the table's width.

Why that spelling rather than any equivalent one. It makes three separate
obligations evaporate instead of travel:

* `geomRouteDecode_eq_readComputation_value`'s three hypotheses become
  `rfl` at both geometries, exactly as they are at the summary group's
  four;
* `hvalid` and `hentries` become the SAME PROPOSITION, so one validity
  split discharges both -- which is why each cell bridge is four lines;
* the cap is the already-proved `chunkCount_le_eight_offsetWidth` /
  `..._blockAddressWidth` applied directly, with no arithmetic in
  between.

An equivalent-but-differently-spelled geometry would have left all three
as obligations the caller must discharge at every call site.

The two missing store-side clauses were supplied on the same terms:
`hexact_local_concrete` and `hexact_global_concrete`, one line each,
composing the existing `hexact_local`/`hexact_global` with
`holdsInteriorStore_concrete`. The four summary twins already existed;
the two span twins simply had not been written.

What is now claimed. `spanValue_localSpan_eq_routeValue` and
`spanValue_globalSpan_eq_routeValue`: the span block's value function, at
the route's own slot and offset, IS the value of
`canonicalRelativeRmmMachineLocalSpanCandidateComputation` and of its
global twin respectively. NO VALIDITY, CAP OR STORE HYPOTHESIS SURVIVES.

One arithmetic detail, recorded because it is the kind of thing that
looks cosmetic and is not. The global twin needs `Nat.zero_add`
substantively: `Nat.add` recurses on its SECOND argument, so `0 + value`
is NOT definitionally `value`, while the route's global block-index map
is bare `value`. The local twin's map is `macroIdx * macroSize + value`
and needs nothing.

Correction of record, made while doing this. `E1_LIVE_STATE.md` cited
`geomCell_eq_routeDecode` and `geomRouteDecode_eq_readComputation_value`
as `E1InteriorChunkStore.lean:674` and `:904`. The LINE NUMBERS are
right; the FILE is wrong -- both are in `E1InteriorSummaryGroup.lean`,
and `E1InteriorChunkStore.lean` is only 619 lines long, so the citation
was refutable by `wc` alone. Fixed in that file.

Scope. This is `#2` and `#3` of the interior ladder, at the canonical
store and layout. It does not discharge any row of
`E1_AMENDED_MACHINE_ACCEPTANCE_MATRIX.md`, all of which are whole-query
scoped and remain Open. The two-span blocks `#4`/`#5`, the three macro
combiners `#6`/`#7`/`#8` and the five-branch dispatch `#9` remain
unbuilt, and no receipt or charge-log link is claimed here -- only the
VALUE. DD-20260719-019's rule applies: a value equation and a receipt
equation are independent obligations, and the span block's receipt clause
is stated but its route-side link is not yet written.

## DD-20260719-052: the interior's two-way candidate merge is a NEW 9-instruction block writing in place to the interior's output pair, and its sharpest impostor defeats the category log as well (E1 M3d-27)

Claimed this session; predecessor `DD-20260719-051`, this session's own
earlier entry, checked before claiming.

Context, and a correction that made the work bigger. `#4`, `#5`, `#6` and
`#7` all end in `bpCandidateMerge?` over two `Option`-valued sub-legs.
`E1_LIVE_STATE.md` had listed `candMerge3` as the reusable read-free
merge; its own later correction then established that `candMerge3` is
fringe-shaped and unusable, and that NO two-way merge block existed. That
correction is upheld. Its stated REASON is not, and the difference
matters.

THIS ENTRY SUPERSEDES THE SECOND HALF OF THAT CORRECTION. It said
`candMerge3`'s "epilogue writes the closed position where the combiners
need the candidate left in the bank". That is false as stated:
`candMerge3Close` is ADDITIVE, and `candMerge3_runsTo` already exports
`bestOfRegs (regs' mAV) (regs' mAP)` holding the merged candidate
alongside the `fRes` clause. The candidate IS left in the bank. The real
obstacles are (a) `candMerge3_runsTo` pins BOTH outer arms to occupied
biased form, matching `bpCandidateMerge3?_some_left_right`'s bare-pair
arguments -- the fringe's situation, not the interior's -- and (b) the
`fRes` (69) write, `fRes` being the shared dispatch output register,
which a combiner running mid-leg must not touch. The headline conclusion
is unaffected: the block had to be built.

Decision one: the result lands IN PLACE in `mMV`/`mMP`, the same pair
`spanBlock` and the 177-leg write. `crossBlockArmProgramAt_runsTo`'s
`hInterior` reads the interior's answer from
`bestOfRegs (regsI mMV) (regsI mMP)`, so one destination pair for every
interior producer is what lets `#4` through `#9` compose without
shuffling. The two arms that keep the RIGHT candidate therefore execute
NO writes at all -- it is already in the destination -- which is why
`Q + 2` and `Q + 6` both jump straight to the exit.

Decision two: the comparison is `natLt` on the BIASED registers, and
nothing is unbiased first. Both operands carry the same `+1`, so
`natLt qT mMV qLV` computes `right.1 < left.1` directly, which is exactly
`bpCandidateBetter`'s test. It is STRICT, so a tie keeps the LEFT
candidate, matching the route.

Decision three: the block sets its own unit register `qOne` rather than
inheriting an `hOne` hypothesis, following `spanBlock`'s `pOne`. The
fold's preservation certificate does not cover `fOne`, so a combiner that
runs after a fold cannot rely on it.

Register bank `123 .. 126`: `qLV` 123 and `qLP` 124 are the caller's
stashed left candidate, `qT` 125 and `qOne` 126 are scratch. Next free
opens at `127`. `mergeUntouched_at_crossBlockArm_operands` DECIDES that
all four registers `hInterior` needs survive; the write set is a numeral
predicate, so it evaluates rather than being eyeballed.

What is now claimed. `mergeBlock_runsTo`: exact simulation on ALL FOUR
option combinations, all exiting `Q + 9`, read-free with the receipt
stated as the literal empty list rather than as a length, value stated
against the route's own `bpCandidateMerge?`, plus preservation. No store
hypothesis.

THE DISCRIMINATORS, AND WHY THEY ARE A PAIR. DD-20260719-050 recorded
that of receipt, read count, exit code and preservation, not one rejected
the span block's `none`-arm impostor, and that a positional CATEGORY
comparison did. Read alone, that invites the conclusion that a category
log is a sufficient backstop. It is not, and this block proves it:

* IMPOSTOR ONE, `natLe` for `natLt`, differing only on TIES -- which are
  the generic case whenever two sub-ranges share a minimum excess.
  Receipts equal and empty (`mergeTie_traces_agree`); the value separates
  them (`mergeTie_discriminates`); and the CHARGE LOGS DIFFER
  (`mergeTie_catLogs_differ`), because the impostor branches where the
  correct block falls through. Caught by the category check.
* IMPOSTOR TWO, `qLV` for `qLP` as the position move's source. The two
  components of the left candidate sit in ADJACENT registers, so "copy
  the source from the instruction above" is a live error -- the same
  shape as the stale receipt head of DD-20260719-019. It takes the SAME
  PATH: receipts equal and empty, both halt, preservation holds on both
  (`mergeOperands_preserved_impostor`), AND THE CHARGE LOGS ARE EQUAL
  (`mergePos_catLogs_agree`). NOT caught by the category check.

The general rule this instances: a category log constrains WHICH
INSTRUCTIONS RAN and says nothing about their OPERANDS. Any defect that
preserves the control path is invisible to it, and for such defects the
value equation is the only instrument. State which checks fail, not only
which one succeeds -- the boundary is the content.

Preservation is EXECUTED on three arms, including the branch-to-exit arm,
which writes nothing and is therefore the arm where a preservation claim
is the weakest evidence and most needs running.

Scope. This is the two-way merge BLOCK. It is not yet composed with
anything: `#4` and `#5` need it wired to two `spanBlock` runs with the
level read as the unconditional head of the append chain, and that
composition is not built. No row of the matrix is closed. No receipt or
charge-log link to the route's `FlatStoreComputation.map` is claimed --
only the machine-side charge log as a function of the route's branch
conditions.

## DD-20260719-053: the two-span block is ONE parametric block covering both #4 and #5, and the two level tables' `hexact` clauses did not exist (E1 M3d-28)

Written by E1-LaneB4 on behalf of E1-LaneB3, which claimed this ID and
recorded its substance in commit `f86aa3b` but never entered it in this
file. Attributed to its author; not renumbered. Predecessor
`DD-20260719-052` checked before writing.

Context. `#4` (`...LocalTwoSpanCandidateComputation`) and `#5`
(`...GlobalTwoSpanCandidateComputation`) each read a level cell and then
run two span legs merged by `bpCandidateMerge?`. The campaign's
parametric-pattern claim -- that one block instantiated twice beats two
blocks -- had already held once, at `#2`/`#3`.

Decision: one `twoSpanBlock` (`E1InteriorTwoSpan.lean:185`), 509
instructions, exit `Q + 509` on BOTH arms, parametric in two `TableGeom`s
and in the level modulus/divisor. `twoSpanBlock_runsTo` gives receipt,
charge log, value against the route's own `bpCandidateMerge?`, and
preservation, with NO store and NO validity hypothesis -- the premises
are the hosting, four caller inputs and the two geometries' chunk-count
bounds.

The claim held for a slightly different reason than the live-state file
gave. `#4` and `#5` differ not only in which span block they call but
ALSO in the SLOT MAP; both maps are `A + level * M + start` for a
caller-supplied `A` and a program constant `M`, and that is what makes
one block cover both.

The staged level read is the UNCONDITIONAL HEAD of the append chain.
Putting it anywhere else encodes a stale read order and presents as a
whnf heartbeat timeout rather than as a wrong answer.

A coordinator claim failed inspection, and the counting lesson is the
point. The brief said everything `#4`/`#5` needed already existed.
`hexact_localLevel` and `hexact_globalLevel` did not exist anywhere in
the tree: all eight `hagree_*` clauses were present and six tables had
`hexact` twins, so the level tables LOOKED as fully served as the rest.
Counting `hagree`s counts the wrong thing -- a table is only as composed
as its LAST clause. Written at `E1InteriorChunkStore.lean:580`/`:601`
with concrete twins at `E1InteriorStoreConcrete.lean:280`/`:298`.

Scope. This is the two-span BLOCK and its two instantiations. No row of
the acceptance matrix is closed by it. The validator does not exercise it.

## DD-20260719-054: the two-span block's `none` arm admits an impostor PAIR that locates the receipt's boundary, which is whether the skipped code READS (E1 M3d-28)

Written by E1-LaneB4 on behalf of E1-LaneB3, which claimed this ID and
recorded its substance in commit `e34b750` but never entered it in this
file. Attributed to its author; not renumbered.

Context. Two earlier fixtures had each shown one instrument failing.
`spanNoneArm_discriminates` showed a receipt unable to reject a
`none`-arm impostor; `mergePos_discriminates` showed a category log
unable to reject an operand-level one. Read together they invite the
conclusion that the receipt is simply the weaker instrument.

Decision: state the boundary as a PAIR of impostors that are the SAME
defect -- a wrong branch target -- at two of the block's own live
numerals, falling on opposite sides of it.

* **A**, target `Q + 275`, past only the FIRST span block. The tail it
  falls into CONTAINS A READ, so it emits an event the route never
  emitted and the receipt CATCHES it
  (`twoSpanNoneArm_receipt_catches_impostorA`).
* **B**, target `Q + 500`, straight to the merge. `mergeBlock_readFree`
  makes that tail read-free, so receipt and read count are IDENTICAL to
  the correct arm's; it merges a STALE left candidate out of `qLV`/`qLP`
  and returns it where the route returns `none`. The receipt is formally
  INCAPABLE of catching it (`..._receipt_blind_to_impostorB`). Only the
  category log and the value reject it.

The rule this establishes: a receipt constrains WHICH READS HAPPENED, so
its power over a skipped-code defect is exactly whether the skipped code
READS. The receipt is not uniformly weak -- it is weak precisely there.
The four prior models all happened to skip read-free code, which is what
made it look uniformly weak.

Preservation is executed on all three arms with distinct marks.

Scope. Discriminators for the two-span block only. No matrix row closed.

## DD-20260719-055: every nesting level needs its OWN stash pair, because each combiner writes the pair one level below it (E1 M3d-28)

Written by E1-LaneB4 on behalf of E1-LaneB3, which claimed this ID and
recorded its substance in commit `5914260` but never entered it in this
file. Attributed to its author; not renumbered.

Context. `#6` and `#7` are two sub-legs merged. The natural combiner
design is to stash the first sub-leg's candidate in the two-way merge's
left-input pair `qLV`/`qLP` with `mergeShuttle`, run the second sub-leg,
then merge.

Decision, forced by a correction: THAT DESIGN IS WRONG. `twoSpanBlock`
CONTAINS a `mergeShuttle` and a `mergeBlock`, so it writes `qLV`/`qLP`
itself, and the second sub-leg destroys the stash.
`twoSpanUntouched_excludes_mergeStash` (`E1InteriorTwoSpan.lean:331`)
records this as a theorem rather than as a comment, because nothing about
the block's type says so. The live-state file's "chaining does need a
two-instruction shuttle, which exists" is true one level DOWN and NOT
sufficient one level UP.

So `twoLegBlock` carries its OWN stash pair, `uSV`/`uSP` at `142`/`143`,
and restores into `qLV`/`qLP` only after the second sub-leg has finished
-- two moves each, replacing the shuttle.

Caught by the TYPE CHECKER, not by a fixture: `TwoSpanUntouched qLV` is
unprovable because it is false. Worth recording as a case where a
preservation predicate did its job at the COMPOSITION SITE rather than at
the block that stated it.

Also landed: `twoSpanUntouched_of_ge` -- the two-span block's whole write
set lies below `136`, so a combiner can carry its own bank across a
sub-leg without re-deciding ten conjuncts. The numerals are spelled out
rather than written as the register `abbrev`s because `omega` collects an
`abbrev` as an OPAQUE ATOM and reports a counterexample against the name.

Scope. `legSetup_runsTo` is proved. `twoLegBlock` is DEFINED ONLY; at the
time of this entry `twoLegBlock_runsTo` did not exist and neither `#6`
nor `#7` was closed. (Both are closed as of `DD-20260719-057`.)

## DD-20260719-056: a preservation predicate can be too STRONG for its own block, and nothing executes it until a simulation quantifies over it (E1 M3d-29)

Claimed this session (E1-LaneB4) from band `056-069`; the maximum
OBSERVED in this file before claiming was `052`, and `053`-`055` were
written by this session on its predecessor's behalf immediately above.

Context. `TwoLegUntouched` was defined by the previous lane alongside
`twoLegBlock`, and evaluated at the four cross-block-arm operands. It
read

    TwoSpanUntouched r AND MergeUntouched r AND ShuttleUntouched r AND
      r != uT AND r != uZero AND r != uSV AND r != uSP

Decision: SUPERSEDE it, adding `r != tA AND r != tStart AND r != tN AND
r != tOff`.

Why the original was UNSOUND FOR ITS OWN BLOCK. `TwoSpanUntouched` omits
the four two-span inputs `tA`/`tStart`/`tN`/`tOff` (`127`-`130`)
DELIBERATELY and CORRECTLY: `twoSpanBlock` only READS them, and declining
to claim them is exactly what lets `#6`-`#9` chain two sub-legs with only
some inputs rewritten between. But `twoLegBlock` WRITES all four, TWICE,
in its two `legSetup`s. So the inherited predicate was provable at four
registers the combiner clobbers -- `TwoLegUntouched 127` closed by
`decide` -- and the preservation clause of `twoLegBlock_runsTo` stated
with it would have been FALSE and unprovable.

WHY NOTHING CAUGHT IT. A preservation predicate is not executed until a
simulation quantifies over it, and this block had none. The existing
`twoLegUntouched_at_crossBlockArm_operands` evaluation passes under BOTH
versions, because `70`/`71`/`75`/`76` are not among the registers at
issue. A green check is evidence only of what it examined, and what it
examined here was four numerals chosen for a different purpose.

The general rule, and it is the mirror of one already on record. The
`SpanUntouched`/`mLP` correction recorded in `E1_LIVE_STATE.md` section 9
was a predicate too WEAK -- it declined to claim a register the consumer
needed. This one is too STRONG -- it claims a register the block
destroys. Both typecheck; neither is caught by reading the predicate
alone. **Only the pairing of a predicate with the consumer's proof
obligation distinguishes the two, so a preservation predicate written
before its simulation should be treated as a conjecture.** Ask of every
such predicate not only whether it claims enough, but whether the block
actually leaves alone everything it claims.

Scope. The predicate and its two consumers. No matrix row is closed by
this entry.

## DD-20260719-057: #6 and #7 are ONE block, and the second leg's sources are taken as a FUNCTION of the combiner bank rather than as bare naturals (E1 M3d-29)

Claimed this session; predecessor `DD-20260719-056`, this session's own
earlier entry, checked before claiming.

Context. `#6` (`...AdjacentMacroCandidateComputation`) and `#7`
(`...LeftMiddleMacroCandidateComputation`) share a left leg and differ
only in whether the second leg is local or global. `legSetup`'s
`mulConst` by a program constant already made the two setups one
instruction shape with one category log.

Decision: prove ONE `twoLegBlock_runsTo` and instantiate it twice. Exit
`Q + 1044`; the receipt is the two sub-legs' receipts CONCATENATED and
nothing else, every instruction outside them being read-free, which is
what `#6`/`#7` being `bind`/`map` combinations of sub-legs means. The
value is the ROUTE's own `bpCandidateMerge?` of the two sub-legs' route
values. No store and no validity hypothesis.

THE DESIGN DECISION THAT MATTERS: the second leg's start and count come
from DIFFERENT REGISTERS at the two instantiations -- `(uZero, uRight)`
at `#6`, `(uT, uMid)` at `#7` -- so the block cannot name them. It takes
instead a FUNCTION from the six combiner-bank readings that hold when the
second setup runs to the value the source carries (`hS2`, `hN2`).

Why not take `start2`/`n2` as bare naturals with a register index
alongside. Because that premise would be satisfied by a setup reading the
WRONG register that happened to hold the right value, which is precisely
the "right shape, wrong content" class this campaign has been bitten by
three times. Tying the value to the READING makes the source index
load-bearing.

The premise is OWED, so its witnesses are exhibited at both
instantiations (`adjacentMacro_src_witnesses`,
`leftMiddleMacro_src_witnesses`) and both are PROJECTIONS of the six
readings -- discharged by picking a hypothesis, not by an argument. The
premise is demonstrably NOT vacuous: the six readings constrain six
DISTINCT registers, so a satisfying `RegFile` exists.

Two spellings recorded because each cost a compile cycle. `#7`'s global
leg takes `kA2 = kO2 = 0`, so its slot base arrives as
`(macroStart + 1) * 0`; that REDUCES to `0` because `Nat.mul` recurses on
its SECOND argument -- the mirror of the `0 + value` trap, falling the
convenient way -- but `rw` matches SYNTACTICALLY, so the reduction has to
be performed with `Nat.mul_zero` rather than relied upon. And
`legSetup_runsTo`'s `regs` is implicit and occurs ONLY in its conclusion,
so it must be supplied as `(regs := ...)` or it stays a metavariable and
every downstream rewrite fails against `?m uMacro`.

Scope. `#6` and `#7` are closed to the standard `#4`/`#5` were closed at:
the parametric simulation plus a route-value link carrying no validity,
cap or store hypothesis. `#9` and `hInterior` are NOT built, so no
whole-interior claim follows, and the validator does not exercise any of
it. No matrix row is closed.

## DD-20260719-058: #8 is the two-leg combiner plus one leg, and the stash-pair law is a LADDER -- each level writes the pair one level below (E1 M3d-29)

Claimed this session; predecessor `DD-20260719-057`, this session's own
earlier entry, checked before claiming.

Context. `#8` (`...CrossMacroCandidateComputation`) merges three sub-legs
with `bpCandidateMerge3?`, and its first two legs are exactly `#7`'s.
`merge3_eq_two_merges` had already established that
`bpCandidateMerge3? l m r` is DEFINITIONALLY
`bpCandidateMerge? (bpCandidateMerge? l m) r`.

Decision: build `crossLegBlock` as `twoLegBlock` at `#7`'s parameters,
UNCHANGED, followed by a third local leg and one more two-way merge --
1574 instructions of which 1044 are the two-leg combiner. Because the
reassociation is definitional, the route-value link needs no
reassociation step; the final `rfl` absorbs it.

THE LADDER. `DD-20260719-055` established that `twoSpanBlock` writes
`qLV`/`qLP`, so `twoLegBlock` needs its own pair `uSV`/`uSP`. The same
law applies one level up: `twoLegBlock` writes `uSV`/`uSP`, so
`crossLegBlock` needs a THIRD pair, `vSV`/`vSP` at `144`/`145`. This is
not a coincidence of two blocks -- **a combiner always writes the stash
pair of the level below it, because that pair is where its own sub-block
leaves its answer.** Any future nesting level must allocate a fresh pair
and must not reuse the one it is built on.

What makes the ladder cheap: `twoLegUntouched_of_ge` (write set below
`144`) lets the new pair survive the whole two-leg sub-block without
re-deciding eleven conjuncts, and it was written for exactly this.
`crossLegUntouched_of_ge` continues it at `146` for `#9`. Added
`twoLegUntouched_of_bank` because the four INPUT registers sit at
`136`-`139`, BELOW the block's own scratch, so the `of_ge` form does not
reach them although a chaining caller must carry them across.

One deliberate three-instruction cost. `rightMacroStart` is recomputed
from `uMacro`/`uMid` rather than read out of `uT`, and `uZero` is
re-seeded, although `twoLegBlock` does in fact leave the right values in
both. Its contract states what the block LEAVES ALONE and says NOTHING
about the final value of a register it writes; depending on that value
would mean strengthening the two-leg contract to save three instructions,
and a contract widened for a caller's convenience is how a block stops
being reusable.

Scope. `#8` is closed to the same standard as `#6`/`#7`. `#9`'s five-way
dispatch and the `hInterior` discharge are NOT built. No matrix row is
closed, and the validator does not exercise any of this.

## DD-20260719-059: `#9`'s five arms exit by explicit branch, except the last, which exits by POSITION -- and that exception is stated as a theorem (E1 M3d-30)

Claimed this session; predecessor `DD-20260719-058` checked before
claiming.

Context. Not one of the blocks `#9` dispatches into terminates.
`spanBlock`, `twoSpanBlock`, `twoLegBlock`, `crossLegBlock` and
`mergeBlock` all end `<regs', exit, false>` -- the halted flag is `false`
in every one -- although a `halt` instruction exists in the ISA
(`E1Machine.lean:103`). Each is built to be composed, so an arm that
ends at its sub-block's exit PC continues executing at whatever sits
there. The close-leg lane had already found this defect live in
`crossBlockArmProgramAt`, whose cross arm's exit PC landed exactly on the
next block's base.

Decision. Four of `#9`'s five arms end with an explicit unconditional
branch (`brNZ wOne <join>`, the idiom `twoSpanArms` already uses at
`Q + 42`). `#8` is placed physically last and exits by falling through to
the join.

A CORRECTION TO THE BRIEF THIS WAS BUILT FROM, recorded because the
instruction was explicit. The brief said "every one of `#9`'s five arms
needs an explicit branch to the join point". That is over-stated by
exactly one. Whichever arm is last exits by fall-through, and giving it a
branch would be a no-op at best; a branch to `join + 1` would be a fresh
defect. The real content of the rule is that **an arm's exit must be the
join, by branch or by position, and never by accident** -- so the
positional case is stated as `dispatchArm8_exit_is_join` rather than left
to an arithmetic coincidence that happens to hold.

Why `#8` is the one placed last: it is the longest arm (1574), so the
join offset is a single addition past it, and the arm whose exit must
coincide with the join is the one where that coincidence is cheapest to
state and check.

Why the `count = 0` arm is where the fixture is built: it is the
shortest (two instructions), so its missing terminator is the cheapest to
overlook, and its fall-through lands in `#4`'s code, which reads.

Anti-vacuity. `unterminatedDispatch_falls_through` EXECUTES the defect at
a witness layout with the real one's control shape: same nine-instruction
selector, same five arms in order, every arm ending un-halted exactly as
every real sub-block does. On a `count = 0` query the unterminated layout
runs off `ARM0` into `ARM4` and halts carrying `5`, so `bestOfRegs` reads
`some (4, _)` where the route reads `none`. A witness arm that HALTED at
its own end would be the one shape unable to exhibit this, which is how
the close-leg defect stayed invisible to every check in the battery.

Recorded limit. The witness's receipt is blind to the defect because no
witness arm reads. That is a property of the FIXTURE, not of the block:
in the real layout the fall-through lands on `twoSpanBlock`'s
unconditional head level read, so the real receipt would carry an event
the route never emitted. Per `E1_LIVE_STATE.md` §6's sixth model, a
receipt's power over a skipped-code defect is exactly whether the skipped
code reads, and here it does. The blindness must not be quoted as the
block's.

## DD-20260719-060: the dispatch bank opens at `146`, and `wOne`'s survival across an arm is the layout's single load-bearing register fact (E1 M3d-30)

Claimed this session; predecessor `DD-20260719-059`, this session's own
earlier entry, checked before claiming.

Context. There is no unconditional jump in the ISA. The idiom is
`brNZ cond target` with `cond` a register holding a nonzero constant. So
every arm's terminator depends on a register set BEFORE the arm and read
AFTER a sub-block of up to 1574 instructions has run.

Decision. `wOne` at `146`, with `wT` 147, `wStart` 148, `wCount` 149,
`wRem` 150, `wLeft` 151.

Why `146` and not lower. `crossLegUntouched_of_ge`
(`E1InteriorCombine.lean:997`) proves the three-leg write set lies below
`146`; `twoLegUntouched_of_ge` gives `144` and `twoSpanUntouched_of_ge`
gives `136`. So a register at `146`+ survives every arm, and `wOne` is
still nonzero at the trailing branch. **If the bank had opened anywhere
below `146`, an arm could clear its own terminator's condition and the
branch would silently become a fall-through** -- the DD-059 defect
reintroduced through the register file instead of through the layout.
The `of_ge` ladder was built for this and is used rather than re-decided.

THE WRITE-SET CHECK, done against the block's OWN writes and not against
a consumer's operands. `E1_LIVE_STATE.md` §6 records that
`..._at_crossBlockArm_operands` passes under both a sound and an unsound
preservation predicate, because the registers it checks are not the ones
at issue -- the inherited `TwoLegUntouched` claimed `127`-`130` while
`twoLegBlock` writes them twice. So `DispatchUntouched` was written by
enumerating what `#9` itself writes, not by inheriting:

* the dispatch bank `146`-`151`;
* `#4`'s input registers `tA`/`tStart`/`tN`/`tOff` (`127`-`130`), which
  the preamble writes -- note `TwoSpanUntouched` deliberately omits these
  because `twoSpanBlock` only READS them, so inheriting it here would
  have produced exactly the §6 unsoundness;
* the combiner input registers `uMacro`/`uLocal`/`uMid`/`uRight`
  (`136`-`139`), which the preamble writes and which `TwoLegUntouched`
  does NOT exclude, for the same reason;
* everything the five sub-blocks write, via `CrossLegUntouched`.

`dispatchUntouched_of_lt` then proves the whole stack leaves every
register below `77` alone -- `mMV` is the lowest register anything in the
interior writes -- which subsumes `hInterior`'s four operands
(`70`/`71`/`75`/`76`) and the close leg's `CloseLegUntouched`
(`r <= 7 \/ r = 28`) in one structural lemma instead of nine numeral
cases.

## DD-20260719-061: `#9`'s receipt and charge log are written as five-way `if`s in the ROUTE's condition order, and the value clause is ONE equation across all five arms (E1 LaneB6)

Claimed this session; band `061`-`069`, `059`/`060` spent by the
predecessor and checked before claiming.

Context. `interiorDispatchBlock_runsTo` has to carry a receipt, a
category log and a value that all differ per branch. Three shapes were
available: existentially quantify the trace and cats (weak, and it would
have let a wrong log through); state five separate theorems (no single
`hInterior` instantiation, since `hInterior` binds `interiorTrace` and
`interiorCats` OUTSIDE its quantifier over entry register files); or
define trace and cats as functions of the route's own inputs.

Decision. `dispatchEvents shape startBlock count` and
`dispatchCats shape startBlock count` are five-way `if`s testing
`count = 0`, `count <= macroSize - localStart`, `middleMacroCount = 0`,
`rightCount = 0` -- exactly the order
`canonicalRelativeRmmInteriorRangeMinComputation` tests them in and
exactly the order `dispatchSelector` branches on. Each branch's body is
the corresponding sub-block's own `twoSpanEvents` / `twoSpanCats` /
`twoLegCats` / `crossLegCats` at the ROUTE's own arguments.

Why route-first. `E1_LIVE_STATE.md` section 11 F: *a category function
written after the machine is a category function fitted to the machine.*
The same argument applies to a receipt. These two functions mention no
register, no `RunsTo` and no program base; the simulation then
case-splits against `interiorRangeMin_of_*` rather than against its own
shape.

The value clause is deliberately NOT a five-way function. It is the
single equation

    bestOfRegs (regs' mMV) (regs' mMP) = dispatchRouteValue shape startBlock count

with `dispatchRouteValue` the route's run-value at the canonical store.
Each arm reaches it by rewriting with its own `interiorRangeMin_of_*` and
then with the matching value link
(`twoSpanValue_local_eq_routeValue`,
`twoLegValue_adjacentMacro_eq_routeValue`,
`twoLegValue_leftMiddleMacro_eq_routeValue`,
`crossLegValue_crossMacro_eq_routeValue`). A five-way value function
would have been a second place for the branch conditions to be written
down, and therefore a second place for them to disagree with the route.

Consequence for the prologue. Because `rangePreamble`, `indexDecomp` and
`localArmSetup` are unconditional, every branch shares a 19-category
prefix, and `dispatchCats` is literally
`dispatchPrologueCats ++ dispatchArmCats ...`. `localArmSetup` writes
`#4`'s input bank `127`-`130` even on branches that never enter `#4`;
that is sound because `127`-`130` and `136`-`139` are disjoint and no arm
reads the other's bank, and it is what keeps the prologue's log
branch-independent. The cost is that `DispatchUntouched` must exclude
`127`-`130` on every branch, which it does.

## DD-20260719-062: `hInterior` is discharged by CONSUMING `crossBlockArmProgramAt_runsTo`, not by proving something with `hInterior`'s shape (E1 LaneB6)

Context. A premise-shaped theorem and a discharged premise are different
claims. `hInterior` mentions `interior`, `interiorTrace`, `interiorCats`
and `interiorValue` as parameters of `crossBlockArmProgramAt_runsTo`, and
the target PC is `A + 176 + interior.length`. A theorem stating
`hInterior`'s body at a chosen instantiation can typecheck while still
failing to unify with the premise -- for instance if `interior.length`
does not reduce, or if the route's
`canonicalBPRelativeSummaryBlockSizeRaw shape` and the sub-blocks'
`(RelativeRmm.canonicalLayout shape).blockSize` were not the same term.

Decision. Both are proved. `interiorDispatch_hInterior` states
`hInterior`'s body -- four register equalities, `fClose`, `fRight`,
`mLV`, `mLP`, and no fifth. `crossBlockArm_withCanonicalInterior_runsTo`
then APPLIES `crossBlockArmProgramAt_runsTo` to it, taking the interior's
hosting out of `crossBlockArmProgramAt_hosts`'s eighth component. Only
the second establishes that the premise fits.

Two facts it forced into the open, both now checked rather than assumed:

* `canonicalBlockSize_eq_layoutBlockSize` is `rfl`. An earlier lane
  flagged this as an open question and a later one recorded the answer as
  a remark; it is now a kernel check, and if the two definitions ever
  diverge that line stops compiling before any `hInterior` instantiation
  does.
* `canonicalInteriorDispatchBlock_length` is `4204`, so the premise's
  `A + 176 + interior.length` and the composition's `Q + 4204` are the
  same PC.

`CloseLegUntouched` is a SEPARATE ADDITIONAL EXPORT
(`interiorDispatch_preserves_closeLeg`), not a fifth conjunct. A
coordinator brief once relayed a sibling branch's proposal as if it were
this premise's actual shape; it is not, and a fifth conjunct does not
typecheck against a four-conjunct premise. Proving it separately means it
is already in hand when the close-leg branch merges and widens the
premise, without anyone widening `hInterior` to get it.

`E1CrossBlockArm.lean` is NOT edited. Discharging `hInterior` is
instantiation of that theorem's implicit parameters from the interior's
side.

## DD-20260719-063: the EIGHTH discriminator model -- right join, wrong arm -- and the receipt is the instrument that catches it (E1 LaneB6)

Context. `E1_LIVE_STATE.md` section 6 records seven models. The seventh
(`unterminatedDispatch_falls_through`) is a MISSING TERMINATOR. The
composition built this session could have shipped its sibling instead: a
selector branch that is present, correct in form and terminating, but
whose target is a DIFFERENT ARM'S BASE.

Why the obvious checks miss it. Every arm of `#9` reaches the same join;
every arm ends un-halted; every arm's write set lies inside
`DispatchUntouched`. So exit PC, halted flag and preservation are
identical under a mis-dispatch. That is the same non-entailment the
seventh model established for a missing terminator, arrived at from the
opposite direction.

Decision. `missSelector` / `missSelectorImpostor` differ in one branch
target (`missDispatch_differ_at_one_index`), over two witness arms of
IDENTICAL instruction shape that read DIFFERENT addresses. The result:

* exit PC and halted flag agree (`missDispatch_exit_and_halt_agree`);
* the positional category log agrees (`missDispatch_catLogs_agree`);
* preservation cannot separate them -- both arms write the same three
  registers;
* **the receipt separates them** (`missDispatch_receipts_differ`), at
  EVERY store, because a `readWord` event carries its address and the two
  addresses are different numerals whatever the store returns -- the
  inequality survives a store answering `none` to both;
* the value separates them (`missDispatch_values_differ`).

This is section 6's sixth-model rule in its favourable direction: *a
receipt's power over a skipped-code defect is exactly whether the skipped
code reads.* `#4`, `#6`, `#7` and `#8` all begin with an unconditional
level read, so at the real block a mis-dispatch changes the first event
of the receipt. Against `#9`, the receipt is a real instrument.

TWO SCOPE NOTES, because the fixture and the block differ and only one of
these limits is the block's.

1. The category-log AGREEMENT is the FIXTURE's, engineered by giving the
   two witness arms identical instruction shapes so that the receipt is
   left as the only non-value discriminator. `#9`'s real arms are 510,
   1045, 1045 and 1574 instructions long with different logs, so the real
   category log would ALSO catch a mis-dispatch. Quoting the fixture's
   agreement as the block's would understate the block.
2. Both witness arms end UN-HALTED, as every real sub-block does. A
   halting witness arm cannot exhibit a control-flow defect at all --
   which is exactly how the close-leg lane's cross-arm defect stayed
   invisible to the whole battery.

## DD-20260719-070: the close leg's chunk-width side condition was UNCONDITIONAL, so it is discharged rather than threaded (E1 LaneCL)

Claimed and written by the E1-LaneCL session (close/LCA composability),
base `bbd04de`. The four entries `070`-`073` correspond to that session's
four obligations and are written in one pass; substance is lifted from the
session's own commit bodies (`c7c26ad`, `be0291e`) rather than composed
fresh.

Context. `hc : sbChunkBits shape <= machineWordBits shape.bpCode.length`
was carried as an undischarged hypothesis on six composed headlines --
`sameBlockLeg_runsTo_canonical`, `sameBlockLegProgram_runsTo_canonical`,
`sameBlockLegProgramAt_runsTo_canonical`, `sameBlockDispatchProgram_runsTo`,
`sameBlockDispatchProgram_runsTo_witnessCross` and
`crossBlockArmProgramAt_runsTo` -- and on both width certificates in
`E1ProgramWidth.lean`.

Decision: it is removed from every headline that does not need it, and kept
ONLY on the genuinely `L`-parametric arm theorems.

The fact is unconditional. `bpFringeChunkBits_le_machineWordBits`
(`E1FringeBridge.lean:82`) proves `bpFringeChunkBits m <= machineWordBits m`
for EVERY `m`, by `unfold; omega`: the first is `Nat.log2 m / 8 + 1` and the
second is `Nat.log2 m + 1`. `sbChunkBits` (`E1SameBlockArm.lean:106`) is an
`abbrev` for `bpFringeChunkBits shape.bpCode.length`, hence reducible, so at
every canonical instantiation `hc` closes with the single term
`bpFringeChunkBits_le_machineWordBits shape.bpCode.length`.

The distinction that decides where it stays. `fringeLeg_runsTo`,
`fringeArm_runsTo`, `fringeArmProgramAt_runsTo` and `sameBlockArm_runsTo`
are parametric in the word width `L`, and at an arbitrary `L` the
inequality is a real obligation. The canonical headlines instantiate
`L := machineWordBits shape.bpCode.length`, and there it is free. So this
is not "delete a hypothesis" but "stop restating at the instance what is
already true in general".

Two further premises fell to the same test, found while making the change
rather than assumed. `sameBlockLegProgramAt_fits` (`E1ProgramWidth.lean:57`)
and `sameBlockDispatchProgram_fits` (`:145`) each also carried `hcpos`
(`0 < sbChunkBits shape`) and `hLpos` (`0 < machineWordBits ...`), which are
`bpFringeChunkBits_pos` (`ChargedFringeChunks.lean:45`) and
`machineWordBits_pos` (`SuccinctRank.lean:41`). Both certificates now derive
all three internally.

Recorded because a decorative hypothesis is invisible at the definition
site. `hc` typechecked, propagated cleanly, and looked like diligence at
every one of the eight declarations that carried it; nothing distinguishes
it from a real obligation except trying to discharge it. A side condition
should be checked for unconditionality WHERE IT IS INTRODUCED, not carried
until a consumer happens to need it.

## DD-20260719-071: the close leg's nine window full-width premises were FALSE at the canonical store, and the repair is DENSITY, not padding (E1 LaneCL)

Context. Nine premises shared one root -- three on the same-block side
(`h0`/`h1`/`h2`) and six on the cross side (`hL0`-`hR2`) -- each of the form
`(readBits (concreteBPNativeSuccinctRMQGlobalReadStore shape) (sbBase ... + k)).length
= machineWordBits shape.bpCode.length`, for `k = 0, 1, 2`. No discharge
existed anywhere in the tree; every consumer forwarded them unproved. They
funnelled through exactly one lemma, `windowRegsValue_of_readBits`
(`E1FringeArmBlock.lean:471`), used at exactly one site, which is what made
the repair local.

SETTLED BY EVALUATION BEFORE ANY REPAIR, not by argument. At the reachable
last close position of each shape -- `bpCode[close] = some false`, a genuine
CLOSE bit in every row, so these endpoints are reachable -- with
`L = machineWordBits |bpCode|`, `B = canonicalBPRelativeSummaryBlockSizeRaw`,
`firstWord = sbBase`:

| shape | bpCode length | `L` | `B` | close | `sbBase` | lens at +0/+1/+2/+3 | h0,h1,h2 |
|---|---|---|---|---|---|---|---|
| spine4 | 8 | 4 | 6 | 7 | 1 | 4,0,0,0 | T,F,F |
| spine8 | 16 | 5 | 8 | 15 | 1 | 5,5,1,0 | T,T,F |
| spine16 | 32 | 6 | 10 | 31 | 5 | 2,0,0,0 | F,F,F |
| spine32 | 64 | 7 | 12 | 63 | 8 | 7,1,0,0 | T,F,F |
| bal3 | 14 | 4 | 6 | 13 | 3 | 2,0,0,0 | F,F,F |
| bal4 | 30 | 5 | 8 | 29 | 4 | 5,5,0,0 | T,T,F |

The premises are FALSE, and not at an isolated boundary point. The failing
close positions form contiguous TRAILING REGIONS: `[8..15]` of 16 for
spine8, `[20..31]` of 32 for spine16, 4 of 64 for spine32, 6 of 30 for bal4.
At spine16 and bal3 even `h0` fails -- the FIRST window word is already
short. Interior positions are unaffected: close `4` at spine16 gives
`6,6,6,6` and all three hold. So the premises are true exactly away from the
tail, which is why they survived inspection for as long as they did.

The evaluation was run twice -- once with `readBits` and `sbBase` inlined
verbatim from their definitions, once against the real definitions -- with
identical results, and cross-checked through the proved store bridge
`concreteBPNativeSuccinctRMQGlobalReadStore_bpCode` (`Segments.lean:281`),
which reports 4 words for spine8 and 6 for spine16 at the same lengths.

Decision: exactness is asserted only where it genuinely holds. A word must
be full width WHENEVER THE NEXT WORD IS NONEMPTY, and nothing is claimed
about the fourth word or about a word whose successor is absent.

* `windowRegsValue_eq_bitsToNatLE_dense` (`E1FringeBridge.lean:177`) -- the
  Horner bridge under a short final word.
* `WindowDense` (`E1FringeArmBlock.lean:447`) -- that condition as ONE named
  predicate, replacing three premises at each parametric level.
* `canonicalWindowDense` (`E1SameBlockLeg.lean:114`) -- the discharge.

Why density suffices, which is the part that had to be verified rather than
hoped for. `bitsToNatLE_append` contributes `2 ^ w.length * bitsToNatLE tail`,
and a short word is by construction the LAST nonempty one, so its weight
multiplies zero. At spine8 the third window word has length `1` against a
required `5`, and Horner still agrees exactly. `0 < L` is needed, to
propagate emptiness downward from a full-width word.

Why the canonical store satisfies it unconditionally. `chunkPayloadWords`
(`WordStore.lean:154`) truncates only the FINAL word, so word `j + 1`
nonempty means `(j + 1) * L < m`, hence `(j + 1) * L <= m`, hence word `j`
is full. The premises therefore do not merely weaken and forward -- they are
REMOVED OUTRIGHT from all six headlines.

WHY PADDING THE BP CODE WAS REJECTED, argued rather than asserted, because
it is the obvious alternative and it would have made the original nine
premises literally true. (1) It inverts the direction of fit: the premise
was a machine-side convenience and the BP code is the ACCEPTED ARTIFACT, so
padding reshapes the object the theorem is about in order to spare the proof
about it. (2) It is not free. `bpCode_length` (`Shape.lean:51`) is the
frozen identity `shape.bpCode.length = 2 * shape.size`; padding to a
multiple of `L` changes the code's length, and `L` is `machineWordBits` OF
that length, so the padding target depends on the padded result. (3) It
would ripple into space accounting and the frozen constants, which are
stated against the unpadded length. (4) It is unnecessary, since the decode
is already correct on ragged input once the premise is cut where exactness
is actually consumed. The same reasoning appears at DD-20260719-009 from the
other side: raggedness there is load-bearing because padding would break the
store's `erases` obligation.

This exactly repeats the repair M3d-14 made one layer down
(DD-20260719-009): the interior chunk store demanded `w.length = wordSize`
where the store guarantees only `<=`, and was repaired by weakening plus
exactness only at non-final chunks. Applying the identical repair to the
identical defect means a reviewer pattern-matches it rather than auditing a
new argument. That a premise of this exact shape has now been found FALSE at
two different stores, one layer apart, is itself the finding worth carrying:
wherever a machine-side proof demands uniform word width from a
`chunkPayloadWords` payload, the demand is wrong at the tail.

Scope. The nine premises and `hc` are gone from the six close-leg headlines.
This discharges no row of `E1_AMENDED_MACHINE_ACCEPTANCE_MATRIX.md`, all of
which are whole-query scoped and remain Open.

## DD-20260719-072: the cross-block arm had NO TERMINATOR and fell through into the same-block leg; the fall-through is exhibited by EXECUTION (E1 LaneCL)

Context. Nothing in the tree recorded this.

The arithmetic, verified at source. `crossBlockArmProgramAt_length`
(`E1CrossBlockArm.lean:809`) is `370 + interior.length`.
`crossBlockArmProgramAt_runsTo` exits with `halted = false` at
`A + 370 + interior.length`. `closeDispatchProgram`
(`E1CloseDispatch.lean:277`) is `closeDispatch(4) ++ crossArm ++ sameArm`,
hosting the cross arm at `4` and the same-block arm at `4 + crossArm.length`.
Instantiating the arm at its own host base `A = 4` makes its exit address
`4 + 370 + interior.length`, which IS `4 + crossArm.length`, the same-block
arm's base. The real cross arm would run off its own end into the
same-block leg and execute all 173 of its instructions on the wrong data.

Why it was invisible. `witnessCrossArm` (`E1CloseDispatch.lean:320`) is
`[.const dSame 7, .halt]`. The witness composition works precisely BECAUSE
the witness ends in `.halt` -- it does the one thing the real arm does not,
so every existing anti-vacuity theorem passes while the defect sits in the
gap between the witness and the thing witnessed.

Decision, part one -- the defect is demonstrated by EXECUTION rather than by
layout argument. `unterminatedCrossArm_falls_through`
(`E1CloseDispatch.lean:469`) takes a query whose endpoints are in DIFFERENT
blocks -- so the dispatch correctly declines to branch and correctly enters
the cross arm -- and runs the machine end to end. It reaches the same-block
arm and halts carrying the SAME-BLOCK marker `9`. The impostor is not
invented for the fixture: `unterminatedCrossArm` is `witnessCrossArm` with
its `.halt` replaced by an ordinary register write, i.e. exactly the real
arm's exit condition, and one instruction separates it from
`witnessProgram_runs_cross`, which yields the cross marker `7`.

The non-entailments, stated so the boundary is exact rather than implied.
`unterminatedCrossArm_nonEntailments` conjoins the two REAL runs, so it is
readable off the type that BOTH layouts halt and BOTH receipts are EMPTY:
neither the halt flag, nor any receipt comparison, nor any read count
separates them. What does separate them is the final value and the category
log (`unterminatedCrossArm_catLogs_differ`). This is the right-shape /
wrong-content class at the PROGRAM LAYOUT level -- correct dispatch, correct
branch, correct arm, and still the other arm's answer.

Decision, part two -- the terminator. The machine has no unconditional jump
(`Instr`, `E1Machine.lean:76`, offers only `brNZ` and `halt`), so one is
synthesised: `jumpTo scratch target` is
`[.const scratch 1, .brNZ scratch target]`, with `jumpTo_runsTo` proving it
transfers control from ANY entry register file. `crossArmTerminated`
(`E1CloseDispatch.lean:625`) appends it to the cross arm, and
`crossArmTerminated_converges` (`:649`) shows the repaired layout reaches
the exit PAST the same-block arm.

Why it is appended to the `crossArm` ARGUMENT rather than built into the
layout: that is what keeps `closeDispatchProgram` and
`sameBlockDispatchProgram_runsTo` parametric and unchanged. `dSame` is the
dispatch's own scratch, dead once the branch is resolved, so the terminator
clobbers nothing live.

Scope. `crossArmTerminated` is defined and witnessed but not yet wired into
a real `crossBlockArmProgramAt` composition; that lands with the whole-query
glue.

## DD-20260719-073: the close leg exports a preservation clause in the SELECT leg's shape, and the cross arm is excluded because it cannot promise more than `hInterior` promises (E1 LaneCL)

Context. `sameBlockLeg_runsTo_canonical`,
`sameBlockLegProgramAt_runsTo_canonical`, `sameBlockDispatchProgram_runsTo`
and `crossBlockArmProgramAt_runsTo` all concluded only a `RunsTo` and a
value equation. Their components DO prove preservation --
`RankSeedLegUntouched`, `FringeArmUntouched` (`E1FringeArmBlock.lean:951`),
`CloseDispatchUntouched` -- and it was discarded at composition.
`E1SameBlockArm.lean` said so in a comment.

Decision: the leg exports `CloseLegUntouched r := r <= 7 \/ r = 28`
(`E1SameBlockArm.lean:72`), deliberately the SAME shape
`selectCloseBlock_runsTo_canonical` (`E1SelectCanonical.lean:212`) already
exports, so the whole-query glue chains `select; select; close` without a
translation step between the two clauses.

Stated against the real consumer rather than guessed. The glue must carry
the FIRST select's answer across the SECOND select and then across the close
leg. The second select preserves only `r <= 7 \/ r = 28`, and `28` is
`xIdx` (`E1SelectBridge.lean:69`), that select's OWN input -- so the first
answer has to be stashed in the query skeleton bank `0..7`
(`E1QueryProgram.lean:48`), which is exactly what this clause protects.

Adequacy EVALUATED, not argued, in the style of
`spanUntouched_at_crossBlockArm_operands` (`E1InteriorSpanBlock.lean:232`):
`closeLegUntouched_at_query_operands` (`E1SameBlockArm.lean:87`) covers the
two query operands, the output packet and `xIdx` (`0`, `1`, `2`, `28`), and
`closeLegUntouched_at_guard_scratch` (`:94`) covers the guard prologue's
scratch `3..7`, the slots the glue has available for the stash. Both by
`decide`. This is the check a sibling lane's too-WEAK predicate failed by
declining `mLP`: stating a band is not the same as confirming it covers what
the consumer needs.

Exported from five headlines: `sameBlockArm_runsTo`,
`sameBlockLeg_runsTo_canonical`, both wrappers,
`sameBlockDispatchProgram_runsTo` and its witness-cross corollary.

WHY THE CROSS ARM IS EXCLUDED, and why this is structural rather than
bookkeeping. `hInterior` promises preservation of exactly FOUR registers --
`fClose`, `fRight`, `mLV`, `mLP` -- and the interior sits in the MIDDLE of
the arm. Every register the arm might claim must survive that hole, and
`hInterior` says nothing about `0..7` or `28`. The thirteen `hpres*` facts
in the proof cover every segment EXCEPT the hole, so the clause is
unprovable there no matter how the composition is arranged. An arm cannot
promise more than its own hypotheses promise.

The unblocking change is one conjunct on `hInterior`'s consequent,
`(forall r, CloseLegUntouched r -> regsI r = regsS r)`, and it is
SATISFIABLE at the intended instantiation rather than a new obstruction:
`LegUntouched` (`E1InteriorMinCandidate.lean:934`) unfolds to
`ChunkFoldUntouched` (`E1InteriorChunkFold.lean:928`, `r < 89 \/ 99 < r`)
together with disequalities against the summary bank `100..104`, `mMV`/`mMP`
(`77`/`78`) and the range `105..117`, every one of which holds at `r <= 7`
and at `r = 28`; `SpanUntouched` (`E1InteriorSpanBlock.lean:226`) adds only
`118..122` and `100`. So the conjunct costs the interior lane no new
reasoning.

That interface is the interior lane's, so it is RECORDED with the exact
conjunct rather than changed unilaterally. An EXECUTED witness of the
entailment is owed at the point of composition, in a module downstream of
both `E1CrossBlockArm.lean` and `E1InteriorMinCandidate.lean` -- the cross
arm builds BEFORE the interior modules, so it cannot state one.

Recorded because the failure mode here is not a missing clause but a clause
that would have been too WEAK if written carelessly, and because "compose
the preservation facts already in hand" was true of the same-block side and
FALSE of the cross side for a reason visible only by reading the hypothesis
against the hole it has to cross.
## DD-20260719-090: the whole-query category function is written from the ROUTE, before the machine, and is indexed by a route-side branch classifier so that "a function of the route's branch conditions" holds by construction (E1 LaneG)

Claimed by the E1-LaneG session (whole-query glue foundations). The maximum
OBSERVED in this file before writing was `DD-20260719-052`; this lane's
assigned band is `090`-`109`, so numbering starts at `090` rather than
compacting into the gap.

Context. The whole-query control program
(`concreteBPNativeSuccinctRMQWholeQueryProgram`, `SuccinctFinalRAM.lean:4248`)
has five instructions. Its two `selectClose` instructions run
unconditionally; `lcaClose` scrutinises the two select results;
`rankCloseIfSome` and `outputPredIfSome` scrutinise the LCA result. So the
control flow is determined by exactly THREE `Option` scrutinees. The rank
leg's own result is a `Nat`, written with `setNat` and read back without
being tested, so it is NOT a fourth determinant. This was read off the
evaluator (`SuccinctFinalRAM.lean:3265`) and the program itself, not taken on
report.

Decision, and it is an ORDERING decision as much as a structural one: the
whole-query category function is written BEFORE any whole-query machine-side
statement exists.

Why the ordering is the substance. A category function written after the
machine exists is a category function fitted to the machine: it agrees by
construction and can never report anything. Written from the route alone it
is a PREDICTION. If it later fails to match the machine, that is a finding
about the machine -- and it can only be a finding if this came first. The
alternative available here was to wait for the machine legs and read the
charge off them, which would have been easier and worthless.

Structural half of the decision: `wholeQueryBranchCats` is indexed by
`WholeQueryBranch`, the route's own classifier (`E1RouteDecomposition.lean`),
rather than by the raw endpoints. So "always a function of the route's branch
conditions, never a numeral" is true by construction rather than by
convention, and no numeral appears anywhere in the definition.

Two sub-decisions worth recording because each had a wrong alternative.

* The two select-miss constructors are kept APART although they induce the
  same receipt and the same charge. Collapsing them would have been
  tempting. They record WHICH determinant fired, which is exactly what a
  category-level discriminator needs.
* The `lcaSkipped` and `rankSkipped` stages are NOT padding. The evaluator's
  `lcaClose` writes `none` WITHOUT running its leaf when either select
  missed, and `rankCloseIfSome` returns the state untouched when the LCA
  missed. Both are executed instructions, so both charge. A machine that
  charged nothing there would be as wrong as one that ran the leg, and a
  category function without these slots could not say so.

The per-stage charges are PARAMETERS, following `crossBlockArmCats`
(`E1CrossBlockArm.lean:1088`), which takes `interiorCats` as a parameter for
the same reason: the select/LCA/rank machine legs belong to other lanes and
are not final. What this module asserts is therefore not the legs' content
but the CONTROL STRUCTURE -- which stages appear, in which order, on which
branch. That is the part read off the route, and it is the part a spurious
leg violates.

THE DISCRIMINATOR, AND WHY IT MATTERS MORE HERE THAN ELSEWHERE. On the
`lcaNone` and both `selectNone` branches the route value is `none`, so result
agreement degenerates to `none = none` -- satisfied by any impostor that also
answers `none`. A machine that ran a leg it should have skipped STILL answers
`none`, because the output instruction branches on the LCA result and not on
the skipped leg. The impostor built here runs the skipped rank leg, and the
fixture establishes by EVALUATION that:

* the category logs DIFFER -- `lcaNone_impostor_catLogs_differ`;
* the LENGTHS AGREE (6 = 6) -- `lcaNone_impostor_lengths_agree` -- because
  the spurious leg charges as many ticks as the skip arm it displaced;
* the memory-read COUNTS AGREE, and are `2` rather than the degenerate `0` --
  `lcaNone_impostor_memoryRead_counts_agree` and
  `lcaNone_impostor_memoryRead_count_is_two` -- because the spurious leg is
  READ-FREE;
* the VALUE cannot see it -- `lcaNone_value_is_none` holds for EVERY shape,
  and the value function does not mention the rank stage at all;
* the RECEIPT cannot see it -- stated as an iff,
  `impostor_traces_agree_iff_readFree`: receipts agree if and only if the
  spurious leg is read-free.

That last is deliberately an iff rather than the trivial append-nil form. The
trivial form is true of any list and would say nothing about this machine;
the iff states the EXACT reach of the receipt check, recording that it is not
useless, merely blind in precisely the case the category log alone must
catch.

So of value, receipt, read count and length, NOT ONE rejects this impostor.
Only a positional, per-constructor category comparison does. This is the
`spanNoneArm_discriminates` shape (DD-20260719-050), applied at the whole
query, with the non-entailments stated rather than implied.

Scope. Nothing here is a machine-side claim and no matrix row is closed. The
function is a prediction awaiting the machine legs; if it disagrees with them
that disagreement is the deliverable.

## DD-20260719-091: the guard's accepting fall-through is a theorem with NO invalid-exit premise, and the rejection theorem names its category log positionally instead of quantifying it away (E1 LaneG)

Claimed by the E1-LaneG session; predecessor `DD-20260719-090`, this
session's own.

Context, and the gap. `E1QueryProgram.lean` proved what the charged validity
guard does on an INVALID range -- `guard_reject_of_not_lt` and
`guard_reject_of_out_of_bounds`, each pinning its exact category log. It
proved nothing at all about a VALID one. The module header asserted, in
prose, that the valid path terminates by writing `regOut` and halting so it
never falls through into the exit block, but no theorem established that a
valid range even REACHES the valid path. Grepped before acting:
`guard_accept`, `guard_pass`, `guardAccept`, `falls_through`, `_of_valid` --
no hit anywhere in the tree; every `RunsTo` from `initialState` in both query
modules sat under a rejection hypothesis.

Without an accept theorem the guard composes with NOTHING. `RunsTo.trans`
fixes one store across a composition, so the whole-query glue needs an actual
`RunsTo` segment landing at base `8`.

Decision 1: `guard_accept_of_valid` takes NO `hexit` premise.

Both rejection theorems require the invalid exit block to be hosted, and
symmetry would have suggested carrying it. The accepting run never fetches
from the exit block, so requiring it hosted would be a DECORATIVE PREMISE.
Dropping it also makes the accept theorem strictly more widely applicable
than its rejection siblings, which is the correct relationship: fewer
hypotheses for the path that does less.

The same discipline removed a decorative PARAMETER elsewhere in the lane:
`wholeQueryBranchValue` was first written taking `left right` and never using
them, because its sibling `wholeQueryBranchTrace` needs them. It is defined
without them. The whole-query value depends on the endpoints ONLY through the
branch classification, which is a real structural fact that the decorative
parameters would have hidden.

Decision 2: `guard_reject_of_invalid` names its category log.

The combined rejection theorem existentially quantified `cats` and kept only
two clauses constraining it: the memory-read count is zero, and the length is
at most ten. Both are AGGREGATES, and the exact logs already existed twenty
lines above and were discarded. A log of the right length with one slot
changed from `.comparison` to `.branch` satisfies the read count and the
length bound EXACTLY -- this is the right-shape, wrong-content class the
campaign has been bitten by repeatedly.

`guardRejectCats left right` now names the log as a function of which
invalidity holds. The size constant `n` is deliberately NOT a parameter: it
is what makes the range invalid, but `left < right` ALONE selects between the
two logs. The two aggregates are now corollaries
(`guardRejectCats_memoryRead`, `guardRejectCats_length_le`), so nothing is
lost and the implication runs one way only -- the exact log entails the
aggregates, the aggregates entail nothing about the log.

Decision 3: the weakening is repaired where it mattered most, at the public
surface. `E1QueryBridge.lean` carries the ONLY category statement the E1
machine puts on the public `List Int` boundary, so whatever it can
distinguish is the whole of what that boundary can distinguish about charge.
All four theorems there now carry the exact log. The three named
specializations had each dropped clauses the general theorem already
established -- the trace clause in all three, cost and the bookkeeping bound
in two -- leaving the named boundary cases WEAKER than the statement they
were derived from. They now carry the full clause set.

Two of the three say MORE than the general theorem rather than less: an empty
range and a reversed range both fail `left < right`, so their exact log is
known to be `guardRejectRangeCats` and is named as such. The out-of-bounds
case genuinely cannot be sharpened -- `xs.length < right` does not decide
`left < right` -- so it keeps the branch-indexed form.
`out_of_bounds_reaches_both_reject_logs` EVALUATES witnesses that both logs
are reachable there, so that choice is necessary rather than merely cautious.

Anti-vacuity. `guardAcceptCats_ne_rejectBoundsCats` is the pair worth
noting: the accept log and the out-of-bounds rejection log share their first
SIX entries and differ only from position six on, so a prefix check would not
separate them. The accept behaviour is additionally established by EXECUTION
rather than only by the hand-written `RunsTo` chain -- fall-through pc,
halted flag, empty read log, exact category log and surviving operands all by
`rfl` -- and the boundary cases `right = n` and `right = n + 1` are pinned
from both sides, where an off-by-one would otherwise be invisible to every
fixture.

## DD-20260719-092: the whole query's two object reconciliations were FOUND in the tree, not built, and the lane applies them instead of duplicating them (E1 LaneG)

Claimed by the E1-LaneG session; predecessor `DD-20260719-091`, this
session's own.

FINDING, CONTRARY TO THE LANE BRIEF, recorded because acting on the brief as
written would have duplicated frozen machinery.

The lane was briefed to BUILD two object reconciliations in a new module: the
rank leg's SEED-store versus GLOBAL-store mismatch, and the close/LCA arm's
`AtSegment` versus `AtSegmentWithStore` mismatch. The brief supplied the
ingredients -- `bpChunkedRankTraceResultWithStore_store_parametric`
(`ChargedRankSelectLeafTrace.lean:431`) and eight store-agreement witnesses
-- and prescribed routing through the full `TraceResult` equality rather than
any `_refines` or `toCosted` form.

Both reconciliations ALREADY EXIST, assembled, by exactly that route.

* `concreteBPNativeRankCloseWordTraceResultAtSegment_canonical_eq`
  (`SuccinctFinalRAM.lean:1550`) states as a FULL `TraceResult` equality that
  at the canonical base `17` the route's seed-store rank leg IS the
  global-store one. Its proof applies
  `bpChunkedRankTraceResultWithStore_store_parametric` and discharges the
  four goals with the four seed witnesses and the four global witnesses, with
  the chunk-segment bridge `17 + 4 = 21` by `rfl`. That is the prescribed
  construction, already in the tree.
* `concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore_globalReadStore`
  (`SuccinctFinalStoreParam.lean:1633`) glues the store-parametric close/LCA
  arm at the global store to the canonical arm the route names, routing the
  rank seed through the theorem above.

The machine target was verified independently rather than assumed:
`rankCloseBlock_runsTo_canonical` (`E1RankCanonical.lean:257`) emits receipts
from `concreteBPNativeChunkedRankCloseGlobalWordTraceResult`, which is the
right-hand side of the rank equality above. So the gap the brief described is
closed, in the direction the glue needs.

Decision: do not rebuild either. A reconciliation constructed FOR this lane's
premise, when one already exists AT the target, satisfies the letter of the
witness rule and defeats its purpose -- and a second, independently written
copy of a store-swap proof is a drift hazard against frozen machinery.

What was genuinely missing, and is what the new module supplies: the route's
BRANCH RECEIPT written in the objects the machine's own leg theorems produce.
No statement did that. `wholeQueryBranchTrace_full_machineObjects` performs
both swaps at once; `wholeQueryBranchTrace_lcaNone_machineObjects` performs
only the close/LCA swap, because the rank leg does not appear on that branch
-- which is the practical payoff of keeping the branches apart. Every proof
in the module is a rewrite by an existing theorem and cites the theorem it
uses.

Also recorded there, so the glue does not go looking for a reconciliation
that is not needed: the two select-miss branches need NO swap at all, since
the select legs are already named in global form by the route and neither the
close/LCA leg nor the rank leg appears.

Technique note. The three match-on-constructor goals needed a typed `show`
ascription rather than `unfold`, which leaves the match unreduced even on a
literal constructor. This is the defeq-conversion move from the live state's
technique section, in its cheapest form.

## DD-20260719-110: the interior wrapper DROPS the close leg's seven premises rather than retaining them as dead binders (E1 LaneM, five-branch merge)

Claimed by the five-branch merge session (E1-LaneM) merging
`claude/e1-close-leg-structural` into `claude/b1-b2-charged-fringe-tables`.

THE CONFLICT GIT COULD NOT SEE. `crossBlockArmProgramAt_runsTo`
(`E1CrossBlockArm.lean:1181`) changed signature on the close-leg branch:
`hc` was discharged and the six `readBits ... .length = machineWordBits`
window premises were REMOVED, because they were found FALSE across
contiguous regions of reachable close positions. Independently, on the
campaign branch, `crossBlockArm_withCanonicalInterior_runsTo`
(`E1InteriorDispatchCompose.lean:1274`) was written to APPLY that theorem,
supplying all seven arguments. The two edits are in DIFFERENT FILES, so git
merged them with no textual conflict and Lean then rejected the
application:

  Application type mismatch: ... the argument `hc` has type
  `sbChunkBits shape <= machineWordBits ...` but is expected to have type
  `HostedAt ...`

-- `hc` sliding into `hHost`'s position, the signature having shortened
under it.

THE DECISION. The wrapper did not merely pass those seven arguments; it
BOUND them itself, as its own hypotheses, and forwarded them. So there were
two repairs available:

1. Drop the seven arguments at the call site, KEEP the seven binders on the
   wrapper. Minimal diff; compiles.
2. Drop the seven arguments AND the seven binders.

(2) was taken. (1) compiles and is wrong in the direction that matters:
retaining the binders leaves every future caller of the wrapper obliged to
prove `hc` and six window-length facts that DO NOT HOLD at contiguous
regions of reachable close positions. That is precisely the defect the
close-leg lane spent a session removing, reintroduced one level up and
harder to see, because the premises would sit on a wrapper whose own proof
no longer uses them. A dead false premise is not inert: it is an
unsatisfiable obligation on the whole-query composition that will consume
this wrapper.

Re-ADDING the premises to `E1CrossBlockArm.lean` to make the application
typecheck was never a candidate and is recorded here as explicitly
rejected.

WHAT WAS CHECKED BEFORE DROPPING THEM. The wrapper had NO other callers
(`grep` across all `*.lean`, campaign branch and `claude/e1-glue-foundations`
both: the only occurrence is its own declaration), so the binder removal
breaks nothing downstream. `crossBlockArmProgramAt_hosts` was verified
UNCHANGED by the close-leg branch (empty diff on that theorem), so the
wrapper's hardcoded `.2.2.2.2.2.2.2.1` projection still selects the ninth
conjunct, `HostedAt program (A + 176) interior`, and did not silently
re-target under the merge.

CONSEQUENCE. The wrapper is strictly STRONGER: same conclusion, seven fewer
hypotheses. Nothing was weakened to make the merge compile; the theorem's
statement is unchanged apart from hypothesis removal. Its docstring, which
asserted the seven premises "belong to the fringe arms and are carried
through untouched", was FALSE after the merge and was rewritten rather than
left standing.

Recorded because this is the one merge hazard that no textual tool reports:
two branches, two files, no conflict, and a type error that only appears
after both land. A merge that had been resolved file-by-file and committed
on a green `git status` would have shipped it.

## DD-20260719-140: the `catCount`/`filter` vocabulary bridge lives in `E1Machine.lean` and is EXERCISED, not merely stated (E1-LaneA2)

Claimed by the cost-algebra lane on `claude/e1-cost-algebra`.

THE GAP, grep-verified before acting. Machine-level accounting is written
with `catCount` (`catCount_partition`, `run_steps_eq_category_sum`,
`run_readLog_length_eq_memoryRead_count`, all `E1Machine.lean`). Every
BLOCK-level cap is written with `(log.filter (· == c)).length` --
`interiorChunkFoldCats_memoryRead_count`, `fringeArmPrologueCats_memoryRead_count`,
`interiorReadNatCats_memoryRead_count` and the rest. A grep for any lemma
mentioning both vocabularies returned ZERO hits across `*.lean`. The two
halves of REQ-E1-06 could not be composed because nothing said the two
numbers were the same number.

WHERE IT LANDED AND WHY. `catCount_eq_filter_length` is in `E1Machine.lean`,
beside `catCount`'s own definition and its partition lemma, rather than in the
new cost-algebra module -- it is a fact about `catCount`, not about the cost
algebra, and a consumer in any other module would otherwise have to import the
algebra to get it. `catCount_le_of_filter_length_le` is the transport in the
direction block caps are actually stated in, so a call site needs no
rewriting step of its own.

WHY IT TYPECHECKS AT ALL, recorded because it is not obvious. `Category`
derives `DecidableEq` and NOT `BEq`, so `a == c` elaborates through
`instBEqOfDecidableEq` to `decide (a = c)`. Had `Category` derived a
hand-written `BEq`, the two sides would not have agreed definitionally and the
induction would have needed a lawfulness argument.

STATED AND UNUSED WOULD HAVE BEEN WORTH NOTHING, which is the campaign's own
recorded lesson (`E1_LIVE_STATE.md` §5: "a clause that is proved but never
executed passes every check in the battery"). So the bridge is carried across
the one gap it was written for: `interiorChunkFold_readLog_le_eight`
(`E1CostAlgebra.lean`) turns `interiorChunkFoldCats_memoryRead_le_eight` -- a
`filter` cap -- into a bound on the MACHINE'S OWN RECEIPT LENGTH, via
`RunsTo.readLog_length_eq_memoryRead_count`, which produces a `catCount`. The
first and last links of that chain existed already and could not be put next
to each other.

## DD-20260719-141: per-block charge bounds are stated as INEQUALITIES, and the two `33`s and two `8`s are kept apart in the module text (E1-LaneA2)

Claimed by the cost-algebra lane on `claude/e1-cost-algebra`.

INEQUALITIES, NOT EQUATIONS. REQ-E1-06 conjunct (c) demands
`totalSteps <= <literal>`. Three sessions were shaped by treating
`Nat.log2`'s kernel-irreducibility as an obstruction to the derived literal;
it is not, and the reason is a property of the STATEMENT'S SHAPE. The
boundary bites on EQUATIONS whose value passes through `machineWordBits`.
None of the bounds in `E1CostAlgebra.lean` passes through `machineWordBits` at
all -- they count instructions, not bits -- but they are stated as `<=`
regardless, because that is the shape the requirement asks for and the shape
that composes under `omega`. `interiorChunkFoldCats_length` is left as an
EQUATION deliberately, because it is the algebra the `<=` is derived FROM and
every quantity in it is an instruction count.

THE TWO `33`s ARE NOT THE SAME NUMERAL. The campaign shorthand "caps 33/8/8"
conflates them, and unlike the two `8`s -- flagged distinct in an M3d-11 note
-- the two `33`s had never been separated anywhere. They are:

* the FRINGE-WINDOW chunk-read cap, which sits INSIDE
  `endpointFringe = 4 + 33 = 37` (`ChargedFringeChunks.lean:1624-1687`);
* the WHOLE-INTERIOR-DIRECTORY read cap,
  `canonicalRelativeRmmPrincipledInteriorChargedTraceCost := 33`
  (`InteriorDirectory.lean:1934`);
* `3 * rankClose = 33`, a third and purely coincidental occurrence.

The dangerous pair is the first two, because one sits INSIDE the other's
sibling term in the same algebra
(`2*select35 + (2*rank11 + 2*endpointFringe37 + interior33) + rank11 = 210`).
`E1CostAlgebra.lean` therefore proves NOTHING against `33`, and says so in its
header. The `8` it does prove is the interior table adapter's per-read chunk
cap, which is a different `8` from the fringe's per-word chunk cap
(`machineWordBits_le_8_mul_bpFringeChunkBits`, `ChargedWordChunks.lean:39`).

THE OPERATIVE TOTAL IS `210`, NOT `207`. `207` at HEAD names a RETIRED route
(AMENDMENT A1, owner-approved). Nothing in this lane is proved against `207`.

## DD-20260719-142: `E1AmendedFamiliarMachineTarget` carries NO width conjunct, and that omission is a finding rather than an oversight (E1-LaneA2)

Claimed by the cost-algebra lane on `claude/e1-cost-algebra`.

THE PROBLEM. REQ-E1-07's evidence column asks the amended target Prop to
bundle "width accounting" alongside result agreement, receipt projection, the
invalid guard, category accounting and the derived literal. Both natural
spellings of that conjunct are unusable, and the reason is arithmetic, not
taste:

* `ProgramFits (SuccinctRank.machineWordBits n) (programSkeleton n validPath)`
  is FALSE at small `n`. `machineWordBits n = Nat.log2 n + 1`
  (`SuccinctRank.lean:38`), so at `n = 4` the modeled width is `3` and the
  fitting bound is `2 ^ 3 = 8`, while this construction's register file
  reaches `152` (`E1_LIVE_STATE.md` §3: "Next free block opens at `152`"). A
  target asserting it would be unsatisfiable for a reason having nothing to do
  with whether the machine is correct.
* `∀ n, ∃ w, ProgramFits w (programSkeleton n validPath)` is VACUOUS. Every
  finite instruction list fits SOME width, so the conjunct excludes nothing.
  Under the campaign's own rule -- a VACUOUS premise owes a witness of vacuity
  on the same terms -- this one's witness of vacuity is immediate, which is
  exactly why it must not be shipped as evidence.

HOW THE TREE ALREADY RESOLVES IT, and why that cannot be folded in. The
existing width certificates take `w` as a PARAMETER with explicit side
conditions: `sameBlockLegProgramAt_fits` (`E1ProgramWidth.lean:57`) carries
eleven, including `74 < 2 ^ w`, `hcode`, `hpowL` and two positivity arms.
Those conditions are properties of the SHAPE and the allocation, not of the
query, and collapsing them into a Prop quantified over `xs left right` forces
one of the two bad spellings above.

DECISION. Width accounting stays where it lives, as REQ-E1-02's row against
`E1ProgramWidth`'s parametric certificates, and `E1AmendedFamiliarMachineTarget`
does not restate it. The omission is documented in the Prop's own docstring
rather than left for a reader to notice, because a target Prop that silently
drops a conjunct its row names is indistinguishable from one that forgot.
Carrying it as a decorative hypothesis was considered and REJECTED under the
standing rule against decorative hypotheses.

## DD-20260719-143: REQ-E1-05's validator phase carries VALID CONTROLS, because an invalid-only sweep cannot distinguish the guard from a reject-everything machine (E1-LaneA2)

Claimed by the cost-algebra lane on `claude/e1-cost-algebra`.

WHAT WAS MISSING, grep-verified. REQ-E1-05's Evidence-needed column asks for
the invalid guard "exercised on empty, reversed, and out-of-bounds fixtures in
Lean examples AND IN THE VALIDATOR". The Lean examples existed
(`programSkeleton_invalid_matches_public_guard`, `E1QueryBridge.lean:55`,
universally quantified over `validPath`). The validator half did not: this
harness never ran `programSkeleton`.

CORRECTION TO THE DELEGATION'S PREMISE, recorded because it was acted on.
The brief stated `programSkeleton` "has no consumer outside its own two
files". It has THREE: `E1QueryProgram.lean`, `E1QueryBridge.lean` AND
`E1WholeQueryPublic.lean`, the last of which carries a real consumer,
`programSkeleton_valid_matches_public` (`:140`). The residual the row names
-- the VALIDATOR -- was genuinely absent, so the conclusion held; the count
did not.

THE DESIGN POINT. A sweep containing only invalid ranges is worth nothing on
its own: `const regOut 0; halt` at `pc = 0` -- a machine that rejects
EVERYTHING -- passes every invalid clause the row lists (halts, `none`
packet, empty receipt, zero memory-read charge, at most ten steps). Phase 3j
therefore carries three VALID controls whose required outcome is the
opposite, and `guardAcceptedCount` is asserted `> 0` in the verdict rather
than merely printed. This is the campaign's own vacuity rule applied before
the fact instead of after: the anti-vacuity witness is on the same terms as
the claim.

THE MUTATION, and what it says about instrument power. Phase 4i's mutant J
repoints instruction `7`'s branch CONDITION from `regG` (the live negation
flag) to `regZero` (pinned `0` by the prologue), disabling the `right <= n`
half of the guard. It is shape-preserving: same program length, same
per-instruction category log, `guardMutationIsReal = true`. Rejections fall
from `8` to `5` -- and the count is `5`, not the `6` this lane first
predicted, because the fixture labelled `("empty", n = 0, 0, 1)` is
genuinely an OUT-OF-BOUNDS query at an empty list and escapes with the two
labelled ones. The figure was EVALUATED rather than reasoned to, per the
standing rule on computable quantities; the first guess was wrong and the
kernel caught it.

The sharpest thing the mutant shows is a NON-ENTAILMENT:
`mutantJ_validControlsAccepted = 3`, identical to the honest guard. Every
valid query behaves exactly as before. A harness that checked only that
valid queries still work -- which is the natural thing to check -- would miss
this defect completely.

## DD-20260719-144: the width question is settled by EVALUATION, and it settles at the REVIEWER width, not the size-indexed one (E1-LaneA4)

REQ-E1-02's evidence column asks for a checked theorem that every
instruction of the concrete program fits the modeled width AT EVERY SIZE.
Two predecessor claims made this look unsatisfiable. Both were wrong, and
the correction came from numbers rather than from argument, per the standing
rule that a computable quantity is evaluated and not reasoned about.

WHAT WAS EVALUATED. A scratchpad driver assembled the concrete program at
canonical parameters -- `blockSize = canonicalBPRelativeSummaryBlockSizeRaw
shape`, `fringeSegment = 5`, the same instantiation `E1MachineValidate.lean`
uses at `:361` and `:383` -- and computed the maximum `ProgramFits`-
constrained FIELD, constructor by constructor, at sizes `1` through `1024`.

THREE CORRECTIONS TO THE RECORD.

1. The register file reaches `84`, NOT `152`. `152` appears nowhere as a
   register index; `crossBlockArmProgramAt_fits` (`E1CrossBlockArm.lean:915`)
   independently carries `84 < 2 ^ w` and no certificate anywhere carries a
   larger register hypothesis. The largest `hreg` in the tree is `117`.

2. THE BINDING FIELD IS NOT A REGISTER. `ProgramFits` constrains every
   field, including `const` VALUES and `brNZ` TARGETS, not merely register
   indices. Up to size `256` the maximum field is `555`, the guard's
   invalid-exit branch target `8 + validPath.length`. From size `512` upward
   it is instead `2 ^ machineWordBits shape.bpCode.length`, the fold's
   stride constant, which grows linearly.

3. `ProgramFits (machineWordBits n) ...` IS FALSE AT EVERY SIZE, not "at
   small `n`". Because the program carries the field
   `2 ^ machineWordBits shape.bpCode.length` and
   `shape.bpCode.length = 2 * shape.size`, the field the program needs
   always exceeds the bound the model supplies. There is NO crossover size.
   This matters for governance: had it failed only below a threshold, a size
   dispatch would have looked tempting, and size dispatch on the public
   route is forbidden in this campaign. It fails everywhere, so the spelling
   is simply wrong and nothing is to be repaired by thresholding.

THE DECISION. Width accounting is stated at
`concreteBPNativeSuccinctRMQReviewerWordBits` (`ReviewerPhysical.lean:1474`),
the one pre-execution reviewer word width, which is already a frozen public
quantity and is NOT invented for this purpose. It holds at every evaluated
shape with three orders of magnitude of headroom.

WHY THE OTHER DIRECTION OF THE ARGUMENT WAS BACKWARDS. It was put to this
lane that register `152` needs `2 ^ w > 152`, hence `w >= 8`, hence
"capacity `>= 128`", as though the capacity might fail to be large enough.
The capacity envelope is `400000 * (n + 1)`, so it is at least `400000` at
`n = 0` and grows from there. It is never near `128`. `capacity_ge`
(`E1ReviewerWidth.lean`) records this because the inference is easy to run
in the wrong direction.

WHY THE KERNEL BOUNDARY DOES NOT BITE. Everything reduces through one step,
`lt_reviewerWordBits_of_lt_capacity`: a quantity fits the reviewer width as
soon as it is below the capacity envelope. Past that reduction no goal
mentions `Nat.log2`, so its irreducibility is never reached. Only two
monotone facts about it survive, and they are isolated at the top of the
module (`two_pow_machineWordBits_le`, `machineWordBits_le`).

THE ONE PLACE THE LOGARITHM HAD TO BE USED HONESTLY. The `hmix` side
condition is `(c + 1) * (2 * c + 2)`, QUADRATIC in the chunk width, while
the envelope is only LINEAR in the size. It cannot be closed by bounding the
chunk width crudely. It closes because
`bpFringeChunkBits m = Nat.log2 m / 8 + 1` is genuinely logarithmic: below
`Nat.log2 L = 41` the product is under the absolute constant `98`, and above
it the quadratic is dominated via `m * m <= 2 ^ m`, proved here by
Mathlib-free induction (`sq_le_two_pow`) because the step inequality needs
`4 * k <= k * k` and `omega` cannot supply a nonlinear step on its own.

A FINDING ABOUT THE EXISTING CERTIFICATES, which is the reason this module
is worth more than its statement. `sameBlockLegProgramAt_fits`,
`sameBlockDispatchProgram_fits` and `crossBlockArmProgramAt_fits` take `w`
parametrically with eleven to seventeen side conditions each. Grepping for
their names finds only their own statements and ONE internal use
(`E1ProgramWidth.lean:164`). NOTHING IN THE TREE HAD EVER DISCHARGED THOSE
SIDE CONDITIONS AT ANY INSTANTIATION. They were OWED premises with no
satisfiability witness, so a reader could not tell whether the width story
closes or is vacuous. This module supplies the missing witness on the same
terms as the premises.
