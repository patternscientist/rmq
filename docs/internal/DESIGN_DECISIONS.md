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

NOTE (added 2026-07-19, owner-approved; the Consequences text above is
UNCHANGED). Two corrections to this block, neither altering the decision it
records.

1. **The M1 sentence was a scope disclaimer, not an amendment to M1.** It read
   as though it added a requirement to rung `M1`, and `RMQ_FINAL_ROADMAP.md`'s
   `M1` section — authored 2026-07-09 and unchanged since — never carried one.
   The worker who drafted this block was asked directly and recalls the intent
   as a `U3` scope disclaimer: that the `76` result covered the then-current
   explicit trace-cost model while serialization, preprocessing and a fully
   charged machine remained downstream. It specifically does **not** recall
   assigning serialized-payload querying to `M1`, and does **not** recall
   distinguishing a word-addressed from a bit-addressed target — "I do not think
   I distinguished those targets when drafting that sentence." So the ambiguity
   later found in the sentence was in the writing, not in anyone's reading of
   it. DD-20260714-008, the next record the same day, restates the same
   obligation neutrally as a "downstream obligation" with no `M1` attribution;
   the drafting worker does not recall that removal as deliberate either.
   **Disposition:** bit-addressed serialized-payload querying is now rung `S1`
   in `RMQ_FINAL_ROADMAP.md`, deferred and explicitly not gating `V1`. `M1`'s
   scope is its four roadmap clauses.

2. **This block's constant is superseded.** Its Consequences still say the
   public constant is `76`. `DD-20260717-C05-001` froze `76` as a historical
   constant, and the live all-size bound is `210`
   (`concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost_eq`), migrated
   by commit `f6000c3`. The reasoning recorded here remains valid for the model
   it was written about; only the numeral is historical. Frozen historical
   constants are not edited, so this note records the supersession rather than
   rewriting the block.

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

## DD-20260719-002: historical canonical 328 is literal-pinned; the live raw-expression compatibility cap is named 352 (B7-R3)

Context. The public name
`RMQ.SuccinctClassic.canonicalTransitionalQueryCost` historically denoted
`328`, but the definition at the R3 base named live component constants and
therefore reduced to `352`. Several direct consumers consequently attached
`Compatibility328` vocabulary to propositions about the live `352` value.
That silently rewrote an audit datum whenever a live component moved.

Decision. Preserve the public historical name as the literal-pinned definition
`328`, with
`RMQ.SuccinctClassic.canonicalTransitionalQueryCost_eq :
canonicalTransitionalQueryCost = 328`. Define the current raw component
expression separately as `liveCompatibilityQueryCost`, with an exact `= 352`
theorem. The source/store/full-model/list/headline layers each expose distinct
historical-328 and live-352 bounds, and every `Compatibility328` declaration
now has a checked proposition about `328`.

Rejected alternatives. (1) Keeping the live expression under the historical
name was rejected because the next component change would move history again.
(2) Renaming the historical theorem was rejected because its stable public
identity is itself part of the audit contract. (3) Deleting the live bound was
rejected because it remains a useful compatibility comparison and because the
trust inventory should retain semantic coverage rather than become green by
subtraction.

Consequences. Historical and live compatibility facts are intentionally not
definitionally coupled. Consumers must choose which claim they mean; topology
diagnostics and claim policy label both roles explicitly. The current paper
cap remains `210`, so neither compatibility constant is a current capstone.
Evidence is the exact `328`/`352` theorem pair in
`SuccinctFinalRAM.lean` and `SuccinctRMQClassic.lean`, the paired supplied-store
and full-model theorems, the paired headline aliases, and the WordRAM axiom
inventory.

## DD-20260719-003: one typed 21-case registry is the executable B7 replay contract (B7-R3)

Context. The earlier cost harness stored windows inside fixtures and executed
them recursively, but it had no stable case identity, no pinned pre/post cost
pair, and no selector. A future filtered run could therefore execute zero cases
and inherit the recursive base's successful result. Counting fixture windows
in prose could not reject duplicates, reordering, or a missing load-bearing tie
case.

Decision. Make `replayRegistry : List ReplayCase` the sole default replay
source. Each typed entry records stable ID, fixture, half-open window, exact
answer, route, pre-repair cost, post-repair cost, and disposition. A separate
literal ordered ID list, de-duplication check, pinned pre-cost vector, and
disposition checks validate registry structure before query execution. The
executor returns its actual count. Default mode requires 21 executions in
registry order; `--case` requires exactly one match; unknown IDs and zero-match
`--fixture` selections exit nonzero.

Rejected alternatives. (1) A count-only assertion was rejected because a
duplicate could replace a missing case. (2) Recomputing the pre-repair cost on
the repaired tree was rejected because that destroys the comparison datum.
(3) Keeping selectors outside the Lean executable was rejected because a shell
filter could pass without invoking any case. (4) Spawning replay children from
Lean was rejected; deadlines and process-tree ownership belong to the external
verification layer, while the harness stays child-free.

Consequences. The registry is deliberately duplicated only where independence
is useful: expected IDs and pre-costs are literal guard vectors, while answers
are also checked against the independent `List Int` reference semantics. The
load-bearing interior leftmost-tie fixture is a named entry rather than a prose
claim. Missing/duplicate IDs fail before execution, and known/unknown/zero
selector controls provide mechanical non-vacuity evidence.

## DD-20260719-004: closed corruption-witness data stays theorem-local (B7-R3)

Context. The B7 returned-value dependency proof initially exposed two closed
definitions for the canonical size-3469 local-level address and its dropped
component store. Their values were useful only inside one theorem, but because
they lived in an imported executable module they entered generated runtime
initialization. The cost harness then spent more than 120 seconds before even
completing a shape-only size-5 probe. This host-runtime cost is unrelated to
the WordRAM trace cost proved by the theorem.

Decision. Keep the address and one-word-dropped store as explicit `let`s in
both the proposition and proof of
`canonicalRelativeRmmInteriorCost33LocalLevelDrop_changes_returned_candidate`.
The theorem still places the identical concrete expressions on its accepted
and rejected sides, and still proves both read memberships, exact canonical
`some`, dropped `none`, and returned-value inequality. No separately callable
closed runtime constant is minted for proof-only witness data.

Rejected alternatives. (1) Keep the closed definitions and increase replay
deadlines; that would conflate proof-witness initialization with modeled query
cost. (2) Remove the corruption theorem; that would reopen
`INV-VALUE-DEPENDENCY`. (3) Replace the exact witness with a smaller or
different object; that would break the frozen identical-object challenge.
(4) Hide the definitions with an execution escape hatch; the project trust
and hygiene contract forbids such shortcuts.

Consequences. Focused elaboration preserves the exact theorem proposition and
WordRAM trust name. After rebuilding its consumers, the same shape-only size-5
probe fell from a 120.034-second timeout to 2.135 seconds, and the exact
21-case replay completed in 29.158 seconds. Payload bits, proof fields, modeled
ticks, traces, allocated cells, Lean runtime, and measured wall time remain
separate categories.

## DD-20260719-005: B7 execution bridges retain literal objects and positions in additive propositions (B7-R4)

Context. Exact-commit audit of the R3 candidate found two semantic facts that
were true only as separately reconstructed components. The cost-33 interior
trace was proved in isolation but no proposition placed that identical trace
inside the accepted whole/list query. The singleton repeated-read proof knew
global positions `0`/`15` and instruction positions `0`/`1`, but its exported
compatibility theorem erased those constants behind existential receipts. A
fresh reconstruction also separated two equal-read phenomena: global
positions `0`/`15` are the segment-`1`, index-`0` select-directory read, while
the pre-existing segment-`22` select-chunk witness is at positions `14`/`29`.

Decision. Add two named, reducible proposition definitions and checked
inhabitants rather than changing the older compatibility theorem types.
`ConcreteBPNativeB7Cost33WholeQueryReachability` retains the actual two
select-close instructions, their values `3409`/`6937`, the position-2 LCA
instruction and its folded pre-state, the real cross-block middle conditional
at `(143,146)`, append decompositions into both the LCA-instruction trace and
the complete whole-query trace, and exact `33`/length-`33`/not-`<=30` facts on
the identical segment-20 component. The public Classic proposition additionally
equates the guarded `List Int` `queryTraceResult` for `[1704,3469)` with that
whole trace.

`ConcreteBPNativeSuccinctRMQSingletonRepeatedReadExactPositions` retains the
actual singleton execution, global positions `0` and `15`, producing
instruction positions `0` and `1`, both distinct select-close instructions,
the empty and one-instruction-folded states, local position `0`, the two
`ProducesEventAt` derivations, and complete receipts for the same segment-`1`,
index-`0` successful read. Its Classic proposition likewise retains the valid
guarded query equality. Headline aliases preserve these proposition names;
validation, example, and both curated trust files unfold them into independent
literal expected types.

Rejected alternatives. (1) Re-export only the isolated interior evaluator;
that does not prove reachability from the accepted query object. (2) Rebuild a
sibling aggregate harness; that would not identify the production execution.
(3) Keep the literal positions only in proof bodies or existentially quantify
them; that cannot be checked by a downstream consumer. (4) Relabel the old
segment-22 theorem as the `0`/`15` witness; executable reconstruction shows its
positions are `14`/`29`. (5) mutate the old compatibility theorem type; two
outside-scope semantic-provenance consumers rely on it, and an additive exact
proposition gives the required stronger surface without breaking them.

Consequences. The new public import from `SuccinctRMQClassic` to
`ReviewerReachabilitySmall` is intentional and therefore triggers the ordered
startup/selector/full-registry replay required by WDD-20260719-010. No query
algorithm, payload/store geometry, trace event, modeled cost, `210`, historical
`328`, live `352`, or reference semantics changes. The exact propositions are
larger than compatibility aliases because object identity is now part of the
checked contract; downstream expected-type consumers will fail if the whole
query is replaced by the component evaluator, `(143,146)` changes, `15`/`1`
changes, the producers collapse, folded-state/local-position evidence is
removed, or the literal positions are existentially hidden.

## DD-20260719-006: make strong trace claims name their exact carrying theorem (R1-R4)

Status: Accepted on the R1-R4 exact candidate and integrated. The worker branch
originally used `DD-20260719-003`; integration remapped the identifier because
the independent B7-R3 lineage already owns that number. The decision content is
unchanged.

Date: 2026-07-19

Context: policy version 18 exposed a semantic attribution gap left by the
rejected R1-R3 candidate. Seven registered current surfaces stated the true
readWord-only project fact without naming the theorem that carries it. Five
also placed the fact beside a declaration whose checked type is weaker: the
generic execution story proves only `isReadWord ∨ isWordPrimitive`, while the
compatibility alias and construction capstone event field prove the explicit
`readWord`/`wordRank`/`wordSelect` disjunction.

Decision:

Every current reader-facing readWord-only statement must name
`RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultReadWordOnly` in the
same unit. Keep the generic story, compatibility theorem, and construction
capstone visible where useful, but describe only their checked propositions.
When a sentence combines the strong event fact with capstone fields, say
explicitly that a separate theorem strengthens the exact same canonical trace.

Rejected alternatives:

- Insert the strong alias in an unrelated inventory while leaving the local
  attribution ambiguous.
- Treat truth of the strong project-level theorem as proof that a nearby
  weaker declaration contains that conjunct.
- Remove the strong claim merely to satisfy a lexical policy.
- Strengthen or wrap the Lean declarations, even though the required strong
  theorem already exists on the exact trace object.
- Delete the weaker declarations from documentation; they remain accurate
  compatibility and construction evidence when properly scoped.

Consequences and evidence:

- Seven current surfaces name the strong alias locally and distinguish its
  conclusion from the generic disjunction and capstone/compatibility
  three-constructor fields.
- The capstone remains the construction-facing join for payload, physical
  erasure/backing, certificate equalities, cost, and exactness; readWord-only is
  a separate theorem over the same trace.
- `TraceEvent.nonSyntheticWeight` remains a certificate assigning one to all
  three genuine constructors and zero to the synthetic marker; it is neither
  the cost definition nor a readWord-only restriction.
- The accepted R1-R4 candidate changed documentation and evidence only. The
  integrated tree additionally carries the inherited R1 semantic repair
  lineage and preserves the later B7 cost `210`, source, freshness, and
  occurrence facts. Exact current-tree claim, topology, design, trust, and
  build checks certify the combined frontier.

## DD-20260719-007: synchronize the live publication strategy with the checked 210 cap

Status: Candidate decision; coordinator acceptance pending.

Date: 2026-07-19

Context:

`docs/PUBLICATION_STRATEGY.md` is one of the exact 18 registered current-fact
surfaces. Its historical-status paragraph still said, across two adjacent
lines, that the current theorem's checked charged-trace cap was `207`. The
checked current theorem and the other current surfaces say `210`; `207`
belongs to the explicit compatibility chronology.

Decision:

Change that one live numeral to `210`. Keep the paragraph current and keep the
path in the registered current-surface contract. Historical `76`, `142`,
`207`, and `328` evidence remains in explicitly historical roles, and the
distinct live compatibility expression remains `352`.

Rejected alternatives:

- Reclassify the live paragraph as history merely to preserve the stale
  numeral.
- Remove `docs/PUBLICATION_STRATEGY.md` from the current-surface registry.
- Change a Lean declaration, theorem identity, cost algebra, trace, payload,
  or model field to agree with the stale prose.
- Repair only the sentence without adding an adjacent-line production
  mutation that would have caught it.

Consequences and evidence:

- The publication strategy now agrees with the checked `210` theorem and the
  exact 18-path registry is unchanged.
- The production claim classifier and replay harness own the line-boundary
  enforcement; this entry records the factual public-surface synchronization,
  not a new mathematical or machine-model decision.
- Exact production verdicts and final-tree timings are recorded in
  `docs/internal/P1_POLICY_HARDENING_WORKLOG.md`.

## DD-20260719-008: reviewer-native adequacy uses a direct same-execution 210 field

Status: Candidate decision; coordinator acceptance pending.

Date: 2026-07-19

Context:

The useful R4 semantic delta packaged 24 reviewer-machine facts, an independent
typed consumer, exact supplied-store determinism, and a guarded list chain, but
its cost field named and stated the then-live bound `76`. Current governance
instead has 22 physical sources over logical segments `0..22`, fresh rejected
segment `23`, and the checked principled charged-trace identity `210`.

Decision:

Keep the R4 certificate, required-facts, and guarded-list proposition shapes,
renaming their cost fields to `certificate_weight_le_210` and
`requires_certificate_weight_le_210`. Their proposition is the direct
`nonSyntheticWeight` sum `<= 210` over the exact canonical execution carried by
the surrounding certificate. Populate the canonical certificate only from
`concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_nonSyntheticWeight_sum_le_210`,
whose source proof factors through the principled charged-trace inequality and
`concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost_eq`. Make the
paper theorem consume the guarded required-facts projection and the direct
`<= 210` proposition literally. Keep complete `TraceResult` equality under the
first execution's ordered dynamic reads primary; safe-layout agreement remains
a corollary through that exact theorem.

Rejected alternatives:

- Retain the historical 76 field or bridge it through a frozen compatibility theorem.
- Fill a copied `<= 210` assertion by `rfl`, `decide`, `omega`, or a sibling aggregate.
- Weaken complete-result determinism to value or cost equality.
- Rebuild the certificate from current broad facts while discarding R4's
  independent projection and public dependency.
- Describe the word-addressed supplied-store route as serialized-payload querying.

Consequences and evidence:

- The 24 certificate fields and 24 independently named consumer fields refer to
  the same payload, shape, query, stores, trace, cost, and word-width objects.
- The guarded list packet preserves the half-open leftmost `List Int` contract,
  exact four-link execution chain, value dependency, and coherent invalid route.
- `scripts/headline_axiom_check.lean` pins the entire public proposition with a
  proof term consisting solely of `listIntSuccinctRMQPaperMainTheorem`.
- M1 mutation F14 first deletes the field, then compiles a weakened 211
  certificate and paper theorem before the independent 210 consumer rejects it.
- No payload bit, source manifest, trace event, charged tick, B7 behavior, E1
  declaration, or frozen compatibility identity is changed.

Publication-facing significance:

Reviewers can cite one proposition-level certificate and guarded list packet
without inferring that a nearby cost theorem applies to the same execution.
S1 raw serialized-payload querying and E1 charged-controller simulation remain
separate theorem obligations.

## DD-20260720-001: derive safe-store equality from execution-structural source containment

Status: Candidate decision; coordinator acceptance pending.

Date: 2026-07-20

Context:

The rejected M1-R5 candidate ended at a true safe-store equality, but its
purportedly primary route was circular. Its supplied-store read-containment
proof first used the legacy safe complete-result equality, then recovered the
read set of the changed execution, and only afterward invoked the ordered
dynamic-read theorem. Reordering wrappers downstream did not remove that
load-bearing dependency. The public packet also carried only the dynamic
logical agreement, so a reader could not inspect the intended safe corollary
at the literal paper-theorem boundary.

Decision:

Prove
`concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_read_segment_lt`
directly by following the actual supplied-store evaluator: fixed-width select
tables, rank callbacks, BP-window reads, charged fringe and select chunks, the
segment-20 interior evaluator, LCA branching, individual whole-query
instructions, and the folded `WholeQueryProgram`. Every successful or failed
`readWord segment index word?` event in the resulting trace therefore has
`segment < 23`, independently of store contents or any complete-result
equality. Derive safe-footprint containment and the safe-to-dynamic agreement
bridge from that theorem. Then derive the current safe complete-result alias
through the existing ordered-dynamic complete-`TraceResult` equality.

Expose the safe logical equality as a guarded field of
`ReviewerNativeMachineAdequacy`, consume that field literally in
`listIntSuccinctRMQPaperMainTheorem`, and pin the stronger proposition in the
independently written expected type. Retain the old
`...store_parametric_of_footprint` declaration only for compatibility. A
production topology mutation and the M1 replay's body-aware anti-bypass check
both reject reinserting it into the current chain.

Rejected alternatives:

- Keep the circular containment proof because its final proposition happens
  to be true.
- Treat declaration-name inventory or source grep as the mathematical proof
  of segment containment.
- Delete or rename the legacy theorem, breaking compatibility instead of
  isolating it.
- Prove only value or cost equality under safe agreement rather than equality
  of the complete trace result.
- Add a sibling evaluator, new cost literal, raw serialized-payload query, or
  E1 controller semantics to avoid proving the actual execution theorem.

Consequences and evidence:

- The repaired dependency chain is execution/program/source topology -> typed
  `segment < 23` containment -> safe agreement implies ordered dynamic
  agreement -> ordered-dynamic complete-result equality -> current safe alias
  -> guarded list packet -> literal paper theorem -> independent expected-type
  checker.
- The 24-field reviewer certificate, its 24-field independent required-facts
  proposition, the same-execution `<= 210` derivation, physical source map,
  event trace, payload, and half-open leftmost semantics are unchanged.
- Safe logical equality is an additional guarded public conjunct over the same
  query object; dynamic supplied-store agreement remains the primary theorem.
- Focused StoreParam, Classic, and Headline builds check the formal chain. The
  committed replay and topology controls check the dependency architecture;
  neither substitutes for Lean elaboration.

Publication-facing significance:

A reviewer can now verify why every read touched by the supplied execution is
inside the declared safe layout without assuming the very store-equality
corollary being justified. S1 bit-addressed payload querying, E1 fully charged
control, preprocessing, and conventional word-RAM complexity remain separate
obligations.
## DD-20260721-001: keep the general axiom inventory on the live 210 theorem

Status: Accepted under owner authorization for the CI forward port.

Date: 2026-07-21

Context:

The governed frontier's general axiom inventory still printed
`concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_nonSyntheticWeight_sum_le_207`.
That declaration was retired when the live charged-trace cap moved to `210`, so
the aggregate gate's first integrated run failed with an unknown-constant error.
The sibling Word-RAM inventory already named the live `...sum_le_210` theorem.

Decision:

Change only the general inventory anchor from `...sum_le_207` to
`...sum_le_210`. Keep the live theorem, its statement, proof, namespace, and
trust base unchanged. The inventory continues to ask Lean's kernel for the
axioms of the current public cost theorem rather than a compatibility alias.

Rejected alternatives:

- Keep the retired `207` name and tolerate a permanently red trust inventory.
- Delete the line, which would make the gate green by reducing trust coverage.
- Point the inventory at a historical compatibility theorem, which would check
  the wrong public claim.
- Change or reintroduce a Lean theorem merely to satisfy the stale script.

Consequences and evidence:

- `scripts/axiom_check.lean` and `scripts/wordram_axiom_check.lean` now name the
  same live `210` theorem.
- No theorem proposition, proof term, payload, trace, cost, runtime behavior, or
  public claim changes.
- The first integrated aggregate gate exposed the stale anchor after every build
  succeeded; the focused repaired inventory then exited successfully on the
  warmed exact tree.

## DD-20260722-001: align paper-root and physical-layout comments with live checked facts

Status: Accepted and integrated on 2026-07-22 after fresh-blind audit and
independent coordinator reconstruction.

Date: 2026-07-22

Context:

The current Lean declarations already check a uniform whole-query charged-trace
certificate of `<= 210` and a logical reviewer-source universe `0..22`. Two
nearby comments still described the retired `207` cost and `0..20` source
universe. The mismatch was explanatory prose, not a missing theorem or a
different machine construction.

Decision:

Change exactly two comment phrases. `RMQPaper.lean` now calls the live
construction-facing certificate the uniform `<= 210` certificate.
`RMQ/Core/SuccinctFinal/RAM/ReviewerPhysical.lean` now calls the live universe
the logical `0..22` universe. The latter wording deliberately distinguishes
the 23 logical source identifiers from their 22 physical source descriptions,
where logical sources 0 and 19 share one physical description.

The checked theorem names, theorem types, theorem bodies, proof terms, imports,
executable definitions, source registry, payload, trace, cost model, and query
behavior remain unchanged. These corrections do not create a theorem, improve
a cost result, or alter a representation claim.

Rejected alternatives:

- Change a declaration, source bound, or cost literal to make the stale prose
  true. That would reverse the formal source of truth.
- Describe `0..21` from the number of physical descriptions. That would erase
  the live logical source 22 and conflate logical identity with physical
  storage sharing.
- Leave the comments stale because the declarations elaborate. The paper root
  and declaration-adjacent prose are part of the reviewer-facing source
  surface under `CURRENT-LEAN-SOURCE-COMMENT-COVERAGE`.
- Run a broad Lean build as the primary proof of comment neutrality. Exact
  base-blob reversal and declaration-neutral diff inspection give the sharper
  check; a Lean build is conditional on those checks finding a code change.

Consequences and evidence:

- The paper-root wording now agrees literally with
  `concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost_eq` and the
  live `...nonSyntheticWeight_sum_le_210` certificate.
- The physical-layout wording now agrees with the checked `segment < 23`
  source boundary and the explicit source mapping over logical identifiers
  `0..22`.
- Reversing only the two corrected phrases recovers the exact base blobs of
  both Lean files; the other two inspected inventory files remain byte-identical
  to the exact base.

Publication-facing significance:

Reviewers now see the same current cost and logical-source facts in Lean prose
that the kernel checks. This is wording alignment only; S1 serialized-payload
querying, E1 controller charging, A1 preprocessing, and conventional word-RAM
claims remain separate obligations.

## DD-20260722-002: close M1 at the supplied-store reviewer-native theorem boundary

Status: Accepted and integrated.

Date: 2026-07-22

Context:

The M1 chain now contains the 24-field reviewer-native certificate, independent
required-facts projection, direct dynamic supplied-store agreement theorem,
ordered-read complete `TraceResult` equality, safe corollary, guarded list
packet, literal paper-theorem consumption, and independent expected-type
consumer. Its exact candidate and fresh-blind report have both been audited.
The remaining coordinator choice was whether this evidence closes M1 under the
owner-approved scope or should be held open for serialized-payload or fully
charged controller work.

Decision:

Close and integrate M1 at its stated word-addressed supplied-store boundary.
The integrated theorem preserves the same payload, store, execution, trace,
cost `<= 210`, 22-physical-source/logical-`0..22`, width, guard, provenance,
returned-value, and half-open leftmost-RMQ objects throughout the public chain.
Raw serialized-payload querying remains S1, and fully charged controller/runtime
modeling remains E1; neither is silently imported into M1.

Rejected alternatives:

- Keep M1 open until S1. That would contradict the owner-approved roadmap scope
  and conflate supplied-store transfer with serialized decoding.
- Treat E1 as either a prerequisite or a substitute. E1 is a sibling under U3
  and does not prove M1's quantified supplied-store agreement theorem.
- Close from the worker or auditor verdict alone. Coordinator reconstruction of
  the frozen rows, exact production fixture, theorem/object chain, platform
  evidence, and integration ancestry remained mandatory.

Consequences and evidence:

- Exact candidate `977a4df8b5d9e908fe66d012dd242006790ebaf3` and report
  `e7c936d8a070a1db26e87b60c656044ee8a37b56` are integrated on main.
- The coordinator reproduced 91 unique eight-cell rows, 87 byte-identical
  inherited rows, the exact 120-fixture boundary, report-tree strict checks,
  clean retained platform trees, absent recorded PIDs, and conflict-free
  fast-forward ancestry from governance `b07fcc5470349f7cdc261f82ee6d8c320c65923e`.
- No theorem, proof, payload, cost, or runtime implementation was changed by the
  closure commit; it updates the roadmap and current digestion to the audited
  integrated truth.

Publication-facing significance:

The reviewer-native supplied-store adequacy story is now a closed integrated
theorem node with durable audit evidence. Publication prose must continue to
state the charged-event and supplied-store boundaries and must not imply S1,
E1, preprocessing, or conventional word-RAM closure.

## DD-20260724-001: adopt truncated (monus) subtraction in the E1 bounded route contracts

Status: Owner decision recorded 2026-07-24; contract repair pending the B3 R2
and B2 R4-successor freezes. Recorded by C06 (Claude runtime, disclosed
fallback — this entry records the owner's decision and confers no acceptance).

Date: 2026-07-24

Context:

The B3 historical route worker terminated `OBSTRUCTED` at candidate
`bc71cad140956477f4de7e513529ae15d381aa13`: the accepted pinned source
execution reaches `.sub 19 22 23` at source PC 73 (tick 71) with operands
`5`/`19`, requiring the truncated result `0`, while the frozen R1 contract
demanded ordered/no-wrap subtraction. The accepted PREHIST report (blob
`be80468e…`, lines 543-545) authorizes "every required subtraction ordering
or an explicit checked-underflow behavior"; the frozen matrix's
evidence-cell and prompt glosses dropped the second disjunct in
transcription. The finding was derived by C05 (addendum §3.1) and
independently re-derived by C06 (audit report 2026-07-24, re-derivation 1).
PREHIST's own `B3-HIST-04` requirement row demands width closure only.

Decision:

The bounded target's `.sub` is truncated natural subtraction, matching the
accepted source ISA definition (`E1Machine` docstring: "truncated natural
subtraction"). The width clause is restated as: every arithmetic result is
`< 2^w` (for `.sub`, definitionally via `left - right ≤ left`). The repair
applies centrally to all E1 route contracts at their next freeze; no route
contract may impose an ordered/no-wrap side condition absent from the
accepted definition it constrains. Exact contract deltas, including the
governed re-specification of `MUT-HIST-06G` and the recommended seventh
pinned choice `pinnedUnderflowSubPhase = (73, 0)`, are specified in
`docs/internal/E1_ARCH2_CONTRACT_REPAIR_PREP.md`.

Rejected alternatives:

- Explicit compare-and-branch lowering (worker option 2): monus implemented
  expensively; reopens ROM layout, atomicity, and charge accounting for no
  additional semantic content; kept in reserve as a presentational
  refinement since it refines monus.
- Changing the historical source (worker option 3): defeats the historical
  route's purpose of running the unmodified old program on the shared
  object.
- Retaining the ordered clause: refuted by the kernel-checked
  incompatibility theorems and the reproduced tick-71 observation at
  `bc71cad`; would also eventually collide with the current route's
  `decodePacket` truncation (DD-20260719-205).

Consequences and evidence:

- The B3 R1 obstruction disposition stands as a valid stop-condition result;
  its candidate branch remains immutable negative/diagnostic evidence.
- The tick-71 observation was reproduced by C06 on 2026-07-24 via
  `lake env lean` at `bc71cad` (exact seven-field record), and the focused
  obstruction build passed in 1.369s.
- B3 requires a fresh R2 freeze under the repaired contract before any
  route verdict; nothing is accepted by this entry.

## DD-20260723-001: archived prompt contracts are pinned to exact bytes

Date: 2026-07-23. Scope: `.gitattributes` only. Decided by: C05 while committing
the E1 architecture handoff package. No Lean, no claim surface, no acceptance.

**Context.** The E1 architecture dossier cites SHA-256 identities and byte sizes
for two frozen prompt contracts, and states that those hashes were recomputed
from disk. Committing the prompts into the repository put those identities at
risk: the repository has `core.autocrlf=true` and, before this change, no
`.gitattributes`. Both files are entirely CRLF. Git would therefore have stored
them normalized to LF and checked them out as LF on Linux and macOS, so the
recorded hashes would not reproduce anywhere except Windows.

**Decision.** Mark `docs/internal/e1_arch_prompts/**` and the archived dossier
`-text`, so git stores and restores their bytes exactly. The rule was committed
*before* the artifacts themselves, because a `.gitattributes` added afterwards
would not retroactively undo normalization applied at `git add` time.

**Verification.** After commit, both blobs were re-hashed **from the git object
store rather than the working tree** and reproduce the dossier's recorded values
exactly: `EF0112772907E0005BF5B6A978EF7903957CFA0DEF948CF1FABB3F064165D320`
(22,058 bytes) and
`A3EC3C3077FEE9A34D34FBD745D393ED2DF9BAB92DA081CFDB79F5F6091A47CF`
(18,623 bytes).

**Rejected alternative.** Committing the prompts without the attribute and
adjusting the recorded hashes to whatever git produced. That would have made the
identities platform-dependent and silently invalidated every existing citation
of them.

**Generalizable.** Any artifact whose identity is cited by hash must be pinned
`-text` before it is added, or its hash becomes a property of the checkout
platform rather than of the artifact.

## DD-20260725-001: `.claude/skills` wrappers are runtime surfaces, not a second source of truth

Status: Recorded 2026-07-25 by C06 (Claude runtime, disclosed fallback).

Date: 2026-07-25

Context:

Porting the three Claude-runtime skill wrappers to `main` adds files under
`.claude/skills/`. `scripts/design_decision_check.ps1` classifies that path as
code/repository-sensitive rather than workflow-sensitive, because its workflow
roots are `.github/` and `scripts/` and its workflow-code pattern covers
script extensions rather than Markdown. The substantive process rationale,
the empirical evidence for the blocker, and the audit-wrapper rename are
recorded in `WDD-20260725-001`; this entry exists so the repository-sensitive
classification has its required design record.

Decision:

A file under `.claude/skills/` may contain only a runtime pointer: frontmatter
whose `name` equals its directory name, plus prose directing the reader to the
canonical `.agents/skills/<name>/` skill and any runtime-specific adaptation
notes. It may never restate a canonical skill's instructions, acceptance
criteria, or completion gate. `.agents/skills/` remains the single source of
truth, and a wrapper whose referenced canonical path does not exist is a
defect, not a variant.

Rejected alternatives:

- Duplicate the canonical skill text into the wrapper. That creates two
  divergent sources for a governed contract, which is the failure mode the
  wrapper design exists to prevent.
- Add `.claude/` to the checker's workflow roots so this change needs only a
  workflow entry. That edits a governed classifier and its regression
  expectations to make one commit cheaper; it is a reasonable future cleanup
  but must not ride along inside an unrelated repair.
- Leave the wrappers on the coordinator branch. That is what blocked the B3 R2
  launch in the first place.

Consequences and evidence:

- Three wrappers on `main`; each verified to have matching directory and
  frontmatter names and an existing canonical target.
- `scripts/project_skill_preflight_regression.ps1` passes all fourteen cases,
  including `legacy-rmq-audit-name-rejected`, which is why the ported audit
  wrapper is named `rmq-audit-prompt`.
- No mathematical claim, theorem, payload, cost, or runtime implementation is
  affected.

## DD-20260725-002: exempt the archived handoff dossier from whitespace policing

Status: Recorded 2026-07-25 by C06 (Claude runtime, disclosed fallback).

Date: 2026-07-25

Context:

`scripts/reproduce_artifact.sh` runs `git diff --check HEAD^..HEAD` as its
whitespace committed-patch stage. When the E1 architecture handoff package was
merged to the mainline, that stage failed on
`docs/internal/E1_ARCHITECTURE_COORDINATOR_HANDOFF.md`: three header lines end
with the two-space Markdown hard line break, and the file ends with a blank
line. The defect had been latent — on the original handoff branch the run died
earlier at the M1 clean-baseline check (WDD-20260724-002), and on a descendant
tip it is invisible because the stage inspects only `HEAD^..HEAD`. It surfaces
exactly when the merge that introduces the dossier is the tip commit.

Decision:

Add `docs/internal/E1_ARCHITECTURE_COORDINATOR_HANDOFF.md -whitespace` to
`.gitattributes`, alongside the existing `-text` rule. `git diff --check`
honours the `whitespace` attribute, so the archived document is excluded from
whitespace policing while its bytes are preserved exactly. Verified: with the
attribute present, both `git diff --check b98ab1e^..b98ab1e` and
`git diff --check d16adfc..5d80c20` report clean; without it, the former
reports four issues.

Rejected alternatives:

- Strip the trailing whitespace and final blank line. This is the obvious fix
  and it is wrong here. The dossier is archived verbatim precisely so that its
  own provenance sentence — "every named commit and blob was resolved with Git
  while preparing this dossier" — stays true of the committed copy, and the
  handoff index records that it is superseded in place rather than edited.
  Reformatting evidence to satisfy a lint inverts the relationship.
- Broaden the exemption to `docs/internal/e1_arch_prompts/**`. Those files
  currently pass the check, so the exemption would be speculative, and that
  directory now also holds live prompts (the B3 R2 contract) which should stay
  policed.
- Relax the whitespace stage itself. It is a real guard for maintained source;
  the narrow path-scoped attribute is the smaller change.

Consequences and evidence:

- The mainline can carry archived verbatim evidence without a permanently
  red whitespace stage, and the rule is self-documenting at the exact path.
- Any future archived-verbatim document needs the same explicit exemption; the
  general principle is that evidence files are exempted by attribute, never
  normalized in place.
- No Lean source, theorem, matrix, replay, or claim surface is affected.

## DD-20260725-003: type the B3 semantic ROM in B3-owned target vocabulary

Status: Owner decision recorded 2026-07-25. Governed contract repair; binds the
B3 R3 freeze. Recorded by C06 (Claude runtime); this entry records the owner's
decision and confers no acceptance.

Date: 2026-07-25

Context:

The accepted PREHIST report freezes the ambient route domain with
`semanticROM : E1Machine.Program`. The `E1-ARCH2-B3ROUTE-R2` worker raised, and
correctly declined to decide, that this type cannot carry the read semantics the
same accepted input demands elsewhere. Verified independently at the accepted
source port `c19061629ce8cf1e78992a99346170edd84b4971`:

- `abbrev Program := List Instr` (`B3SourcePort/E1Machine.lean:160`);
- `| readMem (dst segment addrReg : Nat)` — the constructor carries a
  **segment** (line 87);
- `execInstr (store : ReadStore) …` evaluates `.readMem` as
  `store.readWord? segment address` and writes `decodeRead word?` (lines
  168-175), i.e. a segmented logical read with option shifting.

`B3-HIST-03-EXPLICIT-PHYSICAL-READ-LOWERING`, inherited from the same PREHIST
report, requires each source logical read to expand into explicit descriptor
count/offset/span, word-length, payload, sentinel, and dead reads of the one
flat B1 image. The frozen construction choices are sharper still: the B3 target
`readMem` "does not reuse historical shifted `decodeRead` for raw cells: the
all-ones dead cell would decode to `2^width`."

So a ROM typed as `E1Machine.Program` forces exactly the evaluator the contract
forbids, and cannot express the flat physical read it requires. The two
inherited requirements are jointly unsatisfiable.

Decision:

**The semantic ROM is typed in the B3-owned target instruction vocabulary, not
`E1Machine.Program`.** The source `E1Machine.Program` remains the
specification-side object that the target must stutter-simulate; it is not the
target's own program type. `B3-HIST-02`'s "one parameter-free semantic ROM"
obligation is unchanged in substance: one width-independent program, decoded
identically at every supported width, with no shape, query, or image-content
parameter.

This is the **third** instance of one pattern: a frozen clause inherited from an
accepted input contradicting another requirement inherited from the same input.
The first was the ordered-subtraction clause versus the accepted monus ISA
(`DD-20260724-001`); the second was the B2 descriptor geometry citing a
route-dead generic declaration
(`FROZEN-CLAUSE-CITES-UNCONSUMED-GENERIC-DECLARATION`). The owner considered
generalizing this into a standing rule and **deliberately deferred**: a rule
will be recorded if a fourth instance appears, rather than generalizing from
three. Until then each instance is adjudicated on its own evidence.

Rejected alternatives:

- Keep `E1Machine.Program` and weaken `B3-HIST-03` to permit segmented logical
  reads through a `ReadStore`. This abandons the whole point of B3: showing the
  old program runs on the *counted physical object*. A segmented store read is
  the uncharged projection the architecture contract exists to forbid.
- Keep both and add a translation layer inside the ROM's evaluator. That hides
  the physical read behind a semantic helper, which
  `INV-INSTRUCTION-ATOMICITY` and the frozen forbidden-shortcut list reject as
  a macro-step.
- Change the accepted source ISA so `readMem` is flat. This alters the
  historical program's semantics, which defeats the historical route exactly as
  worker option 3 would have.

Consequences and evidence:

- The R3 freeze must state this typing explicitly and cite this entry, and must
  not claim `semanticROM : E1Machine.Program` as verbatim inherited.
- The R2 candidate `5973d5d549fc37575820aa6fb4cc648a0a33452e` already typed its
  ROM this way and flagged the conflict instead of asserting authority to
  resolve it. That candidate remains `INCOMPLETE` and unaccepted; this entry
  ratifies the typing choice, not the candidate.
- No accepted blob, theorem, matrix, or public claim changes.

## DD-20260726-001: preserve F03 campaign evidence in-tree as explicitly unvetted artifacts

Status: Coordinator decision recorded 2026-07-26 under the standing autonomous
design-decision authority. Records a provenance choice only; confers no
acceptance on any file it preserves.

Date: 2026-07-26

Context:

The front-loaded `EG-CP-F03` geometry-closure campaign produced 306 working
files -- Lean instruments, adversarial probes, and captured output -- in a
session-scoped temporary directory. Roughly forty theorems compile there with
`[propext, Classical.choice, Quot.sound]` and no `sorryAx`, and the campaign's
entire residual theorem surface is expressed as "port these into the repo".

Decision:

Copy the campaign-window files into `docs/internal/f03_evidence/` and label them
UNVETTED working artifacts in both that directory's `README.md` and the campaign
report.

Rationale:

The failure mode this project has already paid for is a strong claim supported
only by an agent session -- no branch, no commit, no replay. B2SUFF is the
recorded instance, and the F03 campaign's own completeness critic identified the
same shape one level up: forty theorems in a temp directory that vanish with the
session. Preserving them costs 2 MB and makes the residual actionable by a
porting worker; not preserving them would force a re-derivation that has already
cost 4.4 million tokens.

Alternatives rejected:

- Commit nothing and cite the report only. The report's residual surface names
  declarations that would then exist nowhere, which is the exact
  non-durable-evidence pattern the project forbids.
- Curate a vetted subset. The coordinator has not reviewed 306 files
  declaration-by-declaration, and presenting a subset as reviewed would assert a
  vetting that did not happen. Preserving everything under an explicit UNVETTED
  label is the honest option.
- Place them under `RMQ/`. They are not library code, are not built, and would
  pollute the trust surface.

Consequences and evidence:

- Scope is the campaign window only; fifteen pre-campaign scratch files from
  unrelated E1 work were deliberately excluded, so the directory's provenance is
  exactly the campaign.
- These files are not acceptance evidence and no project claim may cite them as
  established. `docs/internal/f03_evidence/README.md` states this, as does
  section 8 of the campaign report.
- No theorem, matrix, contract, accepted blob, or public claim changes.

## DD-20260726-002: T1 is proved as a congruence, not as a probe-provenance argument

Status: Coordinator decision recorded 2026-07-26 under the standing autonomous
design-decision authority. Records the proof strategy actually taken and its
scope. **Confers no acceptance**; the proof is not in `RMQ/` and `EG-CP-F03`
remains OPEN.

Date: 2026-07-26

Context:

T1 -- that the select-close leaf consumes its bitvector only through
`bits.length` and `occurrenceCount bits target` -- was the decisive residual of
the F03 campaign. Two routes were available. The coordinator's scouted route was
a *probe-provenance* argument: show that the long/sparse branch at
`ChargedRankSelectLeafTrace.lean:1176` tests a decoded probe reply rather than
`GenericSelect.superIsLong`, hence the frontier predicate never runs at query
time. The alternative was a plain congruence over the whole body.

Decision:

Take the congruence route. `T1_L1_size_only` is proved by showing that once the
four scalar geometry fields and the two flag-list lengths agree, the two
evaluations coincide step for step.

Rationale:

The congruence is strictly stronger and strictly simpler. It holds **whatever
the branches do**, so it needs no claim about which arm executes, no appeal to
the store's long-flag segments, and -- decisively -- no reference to the
`superIsLong` crossover at n about 13,276. That is what makes T1 threshold-free,
which was the entire reason T1 and not the bounded-regime stopgap was named the
decisive obligation. A probe-provenance proof would have re-imported a regime
argument into a statement whose value is that it has none.

Two structural facts make it cheap: `bits` occurs exactly once in the whole body
of `bpChunkedSelectTraceResultWithStore` (the guard at
`ChargedRankSelectLeafTrace.lean:1168`), and `PayloadWordStore.readProgram` binds
its store as `_store`, unused (`RMQ/Core/SuccinctSpace/WordStoreRAM.lean:26-29`),
so the entry-table reader congruence is `rfl` with no axioms at all.

Alternatives rejected:

- Probe-provenance. True, and independently worth recording, but it proves less
  and drags a regime claim into a threshold-free result.
- The bounded-regime stopgap (`superSpan` bound). Explicitly rejected by the
  campaign report as not discharging the asymptotic claim.

Consequences and evidence:

- The proof is universal in `bits1`, `bits2`, `target`, `store`, `layout`, the
  segment parameters and `idx`; no size threshold, no regime restriction.
- Axioms `[propext, Classical.choice, Quot.sound]`; no `sorryAx`, no
  `native_decide`. Verified non-vacuous by the coordinator: hypotheses are
  satisfiable off the diagonal and the route corollary was instantiated at two
  equal-size shapes with provably different `bpCode`.
- The campaign's open question about `longSuperRelativeEntries` and
  `sparseDirectory.relativeEntries` is **not on T1's path** -- the trace function
  projects only `flagBits.length` and rank geometry. It still governs the
  `EG-CP-F01` K = 1 vs K = 3 header decision.
- No theorem, matrix, contract, accepted blob, or public claim changes.

## DD-20260726-003: EG-CP-F03 is discharged by a capstone theorem, not by an inventory

> **SUPERSEDED IN PART by DD-20260726-004 (2026-07-26).** The "strictly
> stronger" rationale below is **withdrawn**: it is unsound. The A10 fresh-blind
> audit showed the contraposition fails for observationally masked values, and
> the row is **not** discharged by the capstone. Read this entry only as the
> record of what was built; read DD-20260726-004 for the corrected standing.

Status: Coordinator decision recorded 2026-07-26 under the standing autonomous
design-decision authority. Records what was built and the one question left to
the owner. **Confers no row acceptance.**

Date: 2026-07-26

Context:

`EG-CP-F03`'s evidence column asks for an "exhaustive typed inventory for every
current logical-read source and universal consumers, not representative rows".
The campaign produced a source inventory and it was refuted mid-campaign: the
instrument classified 6 of 55 content-dependent constants, was structurally
blind to controller leaf L2, and its syntactic test had a false-clean mode.

Decision:

Discharge the row with `T4_wholeQuery_trace_size_only` and its public-entry
corollary, now in `RMQ/Core/SuccinctFinal/RAM/GeometryClosure.lean`, rather than
by rebuilding the inventory.

Rationale:

The capstone is strictly stronger, by contraposition over the whole executed
surface: if any data-dependent offset, length, branch, divisor or table selector
failed to factor through the allowed inputs, there would exist two equal-size
shapes, a store and endpoints on which the executed program diverged. The
theorem says no such triple exists. An inventory proves the same thing only if
the enumeration is complete AND every per-item argument is valid -- and this
campaign's inventory demonstrably failed both halves.

Alternatives rejected:

- Rebuild the 55-constant inventory. Weaker, and its completeness would rest on
  the same instrument class that already failed once here.
- Claim the row closed without recording the clause mismatch. That is exactly
  the promotion-past-quantifiers failure the project has already paid for.

Consequences and evidence:

- **Left to the owner:** whether a theorem that subsumes the inventory satisfies
  a clause that names the inventory. Recorded, not assumed away.
- The theorems are about the SUPPLIED-STORE surface. The store-free surface is
  genuinely content-dependent (two length-10 lists give 96 versus 79 events), so
  no derived claim may say "the public query" without "at a shared supplied
  store". A control confirms the store-free route does not typecheck against the
  corollary.
- Probe counting is `EG-CP-F08`'s row, not this one, per both row texts.
- No accepted blob, matrix, contract, or public claim changes.

## DD-20260726-004: withdraw the "strictly stronger" rationale; EG-CP-F03 stays open

Status: Coordinator decision recorded 2026-07-26, disposing the A10 fresh-blind
audit. Supersedes in part DD-20260726-003. Records a **retraction**: the
coordinator's own argument was unsound.

Date: 2026-07-26

Context:

DD-20260726-003 argued that `T4_wholeQuery_trace_size_only` discharges
`EG-CP-F03` and is "strictly stronger by contraposition" than the exhaustive
typed inventory the row's evidence column names. The A10 fresh-blind audit
(`docs/internal/audit_reports/2026-07-26_A10_f03_geometry_closure.md`, finding
A10-F03-01) refuted that argument.

Decision:

**The contraposition is withdrawn and `EG-CP-F03` is recorded as OPEN in both
letter and spirit.**

Rationale:

The contraposition assumed that any value failing to factor through the allowed
inputs would be observable in the trace. That is false. A content-dependent
intermediate offset, length, branch, divisor or selector can be dead code, or
can cancel before any emitted event, and remain invisible to every congruence in
the module. So equal traces under all shared stores do **not** entail that each
intermediate calculation factors through permitted inputs.

The correct relation is that the two are incomparable: the capstone is stronger
on observable behaviour, the inventory is stronger on syntactic enumeration.
"Strictly stronger" was wrong in one direction and should not have been written.

Findings sustained in full: A10-F03-01 (no inventory artifact exists),
A10-F03-02 (shipped scope language exceeded the theorem), A10-F03-03 (a shared
whole store is not the frozen prior-probe dependency model), A10-F03-04 (header
words are neither typed nor separately accounted).

One correction to the audit, which narrows but does not overturn A10-F03-03: the
report states that the public theorems "neither export a sequential prior-reply
invariant". True of the module's own theorems, but
`RMQ.SuccinctClassic.queryTraceResultWithStore_eq_of_orderedReadFootprint`
(`RMQ/Core/SuccinctRMQClassic.lean:1298`) predates the delta at `d09bed7` and is
exported as the headline
`RMQ.Headlines.listIntSuccinctRMQQueryTraceResultWithStoreEqOfOrderedReadFootprint`.
The auditor found the private predicate at `SuccinctFinalStoreParam.lean:202-209`
and not this one. The composition was genuinely absent from the delta; it is now
`queryTraceResultWithStore_length_and_footprint`, with an in-tree anti-vacuity
witness showing the footprint hypothesis admits stores that differ at every
unprobed address.

Consequences and evidence:

- The module docstring no longer claims to discharge the row and no longer
  describes its hypothesis as "prior probe replies"; it carries an explicit
  "What this does not establish" section naming all four audit findings.
- `EG-CP-F03` may not be cited as closed. Closing it requires either the
  exhaustive typed inventory with universal consumers, or an explicit owner
  amendment of the row followed by a fresh audit against the amended
  quantifiers -- the auditor's own recommended order, which the coordinator
  adopts.
- No theorem was retracted. The Lean results are sound, non-vacuous, on the real
  five-instruction route, and cover all three leaves and both L2 arms; the audit
  found no P0 and no trust failure.
- No accepted blob, matrix, contract, or public claim changes.

## DD-20260726-005: amend EG-CP-F03's evidence clause; relocate enumeration to F06

Status: **Owner decision** taken 2026-07-26, recorded by C06. Amends a frozen
Stage F row. Confers no acceptance: the amended row must be audited fresh
against the amended quantifiers before F03 may be recorded closed.

Date: 2026-07-26

Context:

The A10 fresh-blind audit found `EG-CP-F03` not closed, principally because its
minimum-evidence clause names an exhaustive typed inventory of every logical-read
source with universal consumers, and no such artifact exists (A10-F03-01). The
coordinator's contraposition argument for substituting a capstone theorem was
refuted and withdrawn (DD-20260726-004). The auditor's recommendation was that if
a theorem is to replace the artifact, the frozen row must be amended explicitly
first and then audited against the new quantifiers. The owner directed that
course.

Decision:

Two amendment rows are added to the Stage F matrix, preserving the original row
text verbatim:

1. **Evidence.** F03's minimum evidence becomes a universal checked congruence
   over the whole executed controller -- equal `n`, all endpoints, any two
   stores agreeing on the ordered read footprint, identical trace and value --
   plus named anti-vacuity witnesses.
2. **Header words.** F03 may be discharged with the store as an undifferentiated
   read oracle, conditional on `EG-CP-F01`/`F02` later showing the frozen header
   fields are exactly the non-probe metadata consumed, at which point F03 is
   re-checked.

Rationale:

The inventory served two distinct purposes. (a) Model faithfulness: nothing
observable depends on input content beyond `n`. (b) Syntactic eliminability: no
content-dependent computation remains in the controller's text.

The congruence establishes (a) directly, universally, and with no size threshold
-- and is better evidence for (a) than an enumeration, because an enumeration's
completeness must itself be argued and this project's attempt at one failed on
exactly that point (39 invisible constants, a false-clean syntactic test).

It does not establish (b), and the amendment does not pretend otherwise. But (b)
is **already owned by `EG-CP-F06`**, whose requirement is "Remove semantic shape
and every sibling/oracle input" and whose minimum evidence already reads
"Closed signature, expected-type dependency consumer, and cross-shape transcript
determinism for equal allowed inputs/probe replies". The inventory was doing
F06's work inside F03. Relocation is therefore a correction of row boundaries,
not a weakening of the gate: nothing is deleted, and F06 may not be closed by
citing this amendment.

Conflict of interest, stated plainly: this amendment is proposed by the party
whose work an audit found short, and it makes that work sufficient for the
amended row. That is precisely what the mandated fresh audit against the amended
quantifiers exists to check. The amendment is not self-executing.

Alternatives rejected:

- Build the inventory. Defensible, and it remains available. Rejected as the
  primary route because it would re-attempt, under time pressure, the exact
  artifact class that already failed here, to establish a property the
  congruence already establishes better.
- Leave the row unamended and record F03 as permanently open. Rejected: it would
  leave a gate row whose evidence clause asks for an artifact that is neither
  necessary for the model nor sufficient without a completeness argument.
- Amend the requirement text as well. Rejected. The requirement is correct as
  written; only the evidence clause was mis-specified.

Consequences and evidence:

- `EG-CP-F03` remains OPEN until a fresh audit against the amended row.
- `EG-CP-F04`/`F06` inherit the syntactic-elimination obligation explicitly and
  may not cite this amendment as progress on it.
- `EG-CP-F01`/`F02` inherit the typed-header obligation and the binding of the
  supplied store to `memory xs`.
- No theorem, matrix acceptance, accepted blob, or public claim changes.

## DD-20260726-006: land the source half of the F03 inventory; reject the geometry half

Status: Coordinator decision recorded 2026-07-26. Records what the inventory
campaign produced and what was refused. Confers no row acceptance.

Date: 2026-07-26

Context:

The owner directed an attempt at the exhaustive typed inventory the original
`EG-CP-F03` clause names, in preference to relying on the amendment. Four lanes
produced deliverables; two were verified and two were found defective by
independent verification lanes.

Decision:

Land `RMQ/Core/SuccinctFinal/RAM/SourceInventory.lean` -- the logical-read-source
half -- with its limitations stated in the module. Reject the geometry census,
the consumer-map selector table, and the F06 work-list.

Rationale:

The source half succeeds and the geometry half fails for a structural reason,
not a competence one, and the distinction should govern future attempts:

**Exhaustiveness is checkable when the universe is a closed inductive.**
`ReviewerSource` has 22 nullary constructors; rows are joined by case analysis on
it; adding a constructor without extending the table makes the module fail to
elaborate. The elaborator enforces completeness.

**Exhaustiveness is not checkable when the universe is "every Nat-valued
expression in a 917-constant closure."** There is nothing to case on, so the
census is a curated list, and its completeness must be argued separately. Three
independent well-resourced attempts have now shipped a false exhaustiveness
claim on that half: the original campaign's 6-row table (refuted by A10), this
campaign's geometry census (refuted: "false in both directions, with
machine-checked refutations"), and its consumer map (a docstring claiming an
"exhaustive 23-row selector table" over a statement with 13 conjuncts).

Rejected artifacts and why:

- `GeometryCensus.lean` -- sound Lean, false central claim. Landing a module whose
  docstring asserts exhaustiveness it does not have is the exact defect the A10
  audit sustained against this coordinator.
- consumer-map selector table -- 13 conjuncts labelled as 23 rows.
- F06 work-list -- its two headline findings are refuted by content already
  committed at the branch tip it was told to read; it declares a missing lemma
  that exists in-tree as `offsets_congr`.

Consequences and evidence:

- Verified independently by the coordinator in a private build (259 oleans,
  `lake build RMQ` exit 0): an expected type written from the row's clause rather
  than from the module is inhabited by `storeParametricRead_hasListedSource`; the
  source universe is confirmed closed at 22 constructors by
  `cases source <;> decide`. Evidence:
  `docs/internal/f03_evidence/c06_sourceinventory_check.lean`.
- Coverage is universal over every shape, every supplied store and every endpoint
  pair, with no validity side condition.
- **Not established**: segment-to-WORDS payload identity, so the `{0, 19}` alias
  is an equality of labels rather than of returned words. Stated in the module.
- This bears on the amendment (DD-20260726-005) as evidence rather than argument:
  the inventory-as-artifact keeps failing at completeness on exactly the half the
  amendment relocates, while the congruence has no completeness step to fail.
  A11 should weigh it.
- No accepted blob, matrix acceptance, contract, or public claim changes.

## DD-20260802-001: factor packed offsets through Nat-only mirrors, not a census

Status: Worker decision recorded 2026-08-03 on branch
`codex/eg-cp-final-falsification-gate-r1`. Governs how `EG-CP` rows `FG-02` and
`FG-03` are evidenced.

Date: 2026-08-03

Context:

`FG-02` requires that every live physical source offset be "a checked function
only of `n`, `longCount`, typed source/index arguments, and prior packed
replies". The obvious reading is an inventory: enumerate the offsets, show each
one's inputs. That reading has failed on this exact surface three times
(`DD-20260726-006`), always the same way -- the enumeration is a curated list and
its completeness becomes a separate argument that turns out to be false.

Two shortcuts are available and both are forbidden. Synthesizing a canonical
shape from `n` inside the offset function is registry mutation
`M04-CANONICAL-SHAPE-BY-N`. Proving only a congruence -- equal size and equal
long count imply equal offsets -- would establish that the offsets are
*determined* by `(n, longCount)` without producing anything a controller could
evaluate, and the controller has to compute addresses, not merely be promised
they exist.

Decision:

For each shape-indexed quantity entering an offset, define a mirror whose type
mentions only `Nat` and the closed source/component inductives, and prove the
mirror equal to the real quantity. The factorization claim is then carried by
the mirror's *signature*: a definition of type `Nat -> Nat -> Source -> Nat`
cannot consult shape content, so the elaborator enforces what prose previously
asserted.

Coverage is obtained the same way. `ConcreteBPNativeSuccinctRMQFlatPayloadSource`
and `ConcreteBPNativeSuccinctRMQFlatPayloadComponent` are closed inductives, so
the equalities are proved by `cases` and a new constructor breaks elaboration.

The header descriptor is `longCount shape`, the number of long super slots, and
`K = 1` is proposed on the strength of
`GenericSelect.longSuperRelativeTable_payload_length`, which already states that
the long relative table's payload length is that count times two size-only
factors.

Rationale:

`WDD-20260726-010` recorded that the mirror technique itself was sound and only
the exhaustiveness claim layered on it was false. The difference here is that no
such claim is layered on: the universe is a closed inductive rather than "every
`Nat`-valued expression in a 917-constant closure", so completeness is a
typechecking property rather than a curated list. This is the `SourceInventory`
pattern, which is the one attempt on this surface that held up.

Choosing the mirror over the congruence also keeps the evidence honest about
what is still missing. A mirror that cannot be defined is a visible failure at
the point of definition; a congruence that cannot be proved looks the same as a
congruence nobody tried to prove.

Consequences:

- `RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/SourceFactorization.lean` is
  imported by `RMQ.lean`, so it is inside `lake build RMQ` and inside the prose
  hygiene scan. The `EG-CP-F01` campaign's residual R1 recorded definitions left
  outside the build as a defect; this avoids repeating it.
- `closeComponent_flatOffset` proves the close component's base is
  `2 * shape.size + packedAccessOverhead shape.size`. That discharges `FG-03`'s
  second clause: every content-dependent length before the close component,
  including both relative tables, is absorbed by the access padding.
- The cancellation is not arithmetic luck. Truncated `Nat` subtraction makes
  `a + (B - a) = B` false without `a <= B`, and that hypothesis is a field of
  `BPCloseAccessDirectory`, so the layout cannot be instantiated without it.
- No theorem here concerns a controller, a cell, or a probe. Offsets are bit
  positions in the existing flat payload.

Evidence added under `DD-20260802-001` (running list; no decision changes here):

- `closeComponent_flatOffset` -- the close component base is
  `2 * shape.size + packedAccessOverhead shape.size`, discharging `FG-03`'s
  second clause.
- `superSlotCount_eq_packed`, `superFieldWidth_eq_packed`,
  `longFlagBits_length_eq_packed`, `superTable_column_length` -- the select
  super geometry mirrors, resting on the BP code having `shape.size` closing
  parentheses and length `2 * shape.size`.
- `longSuperRelativeTable_length_eq` -- the long relative table's payload length
  is `longCount shape` times two size-only factors. This is the exact statement
  that makes `K = 1` the proposed header rather than `K = 0`: it is the only
  length reachable from a select offset that the input size does not fix.

Recorded separately because it bears on the predetermined `K = 0` flip: the
interior/close side was already proved size-only by `offsets_congr`
(`GeometryClosure.lean:718`) and needs no descriptor at all. The header exists
solely for the select side's long relative table.

### Correction to the `DD-20260802-001` evidence note (2026-08-03)

The running evidence list above overstated two things when it was written. Both
sentences stand as written for the record; neither is now relied on.

**Overclaim 1 -- "the only content-dependent length".** The note said
`longSuperRelativeTable_length_eq` identifies "the only length reachable from a
select offset that the input size does not fix". At the time only the select
super geometry had been mirrored, so that was a projection from a partial map,
not a proved conclusion.

The exact proved conclusion is narrower and conditional:

> `longCount` is the candidate's only content-dependent *prefix* length needed to
> locate later live select sources, conditional on
> `selectPayload_eq_prefix_append_sparseRelative`.

Terminality is what makes the sparse count irrelevant to addressing, and
terminality is a separate theorem, not a corollary of the long-table length. The
scope of "later live select sources" is also doing real work: it is a claim about
prefixes that positions depend on, not a claim that no other length in the
structure varies with content. The sparse relative table's own length does vary
with content; it simply sits after everything that is addressed.

**Overclaim 2 -- congruence read as a mirror.** The note said the interior/close
side "was already proved size-only by `offsets_congr` and needs no descriptor at
all". `offsets_congr` (`GeometryClosure.lean:718`) is a *congruence*: for two
shapes of equal size it proves the offsets are equal. It is also stated over
`canonicalRelativeRmmInteriorComponentOffsets` -- the reviewer interior component
at machine-word granularity -- not over the flat-payload bit offsets this module
addresses.

A congruence and an executable size-only mirror are different deliverables, and
only the mirror is usable here. A congruence says the offsets are *determined* by
the size; a controller cannot evaluate a determination. That distinction is the
reason `DD-20260802-001` chose mirrors in the first place, so reading a
congruence as evidence of a mirror inverted this branch's own decision.

Consequently no claim is made here about the `K = 0` flip. Showing the close side
needs no descriptor would require close-side mirrors over the flat layout, which
do not yet exist.

Further evidence under `DD-20260802-001` (no decision changes):

- `packedRankWordSize`, `packedRankBlockWidth`, `packedRankSuperOverhead`,
  `packedRankBlockOverhead`, `packedRankAuxLength` -- the rank prefix is now a
  `Nat`-only mirror rather than a shape-taking function.
- `selectPayload_eq_prefix_append_sparseRelative` and
  `selectSourceComponentOffset_le_prefix` -- sparse terminality and its
  addressing consequence.
- `PackedSummaryActive`, `PackedInteriorReady`, `PackedSourceCounted` with
  `summaryActive_iff_packed`, `interiorReady_iff_packed` and
  `sourceCounted_iff_packed` -- a decidable size-only counting guard that agrees
  with `concreteBPNativeSuccinctRMQFlatPayloadSourceCountedInFlat` on every
  constructor.

The guard matters beyond bookkeeping. `concreteBPNativeSuccinctRMQFlatPayloadSourceComponentOffset`
computes the two close-interior offsets unconditionally, while those sources are
counted only when the interior is ready; in the not-ready regime the offsets
exceed the component. Today that is discharged only by `CountedInFlat` appearing
as a hypothesis on the slice theorem. A packed controller has no such hypothesis
available at run time, so it must consult `PackedInteriorReady` before issuing
those two reads. `interiorReady_iff_packed` is what makes that possible without a
header field: readiness is decidable from `n`.

Factorization leaf closed under `DD-20260802-001` (2026-08-03):

`packedSourceComponentOffset : Nat -> Nat -> ConcreteBPNativeSuccinctRMQFlatPayloadSource -> Nat`
is the address-factorization surface, and `packedSourceComponentOffset_eq` proves
it agrees with the canonical shape-indexed offset at every shape and every one of
the twenty-nine source constructors. The proof is `cases source`, so a new
constructor fails to elaborate until both sides supply its arm; the alias, the
three retired finite-small slots, and the zero arms are each present rather than
folded into a default.

Supporting mirrors, all `Nat`-only: `packedSuperSlots`, `packedSuperWidth`,
`packedSuperColumn`, `packedSuperTableLength`, `packedLongFlagWordSize`,
`packedLongFlagSuperOverhead`, `packedLongFlagBlockOverhead`,
`packedLongFlagAuxLength`, `packedLocalSlots`, `packedLocalWidth`,
`packedLocalColumn`, `packedLocalTableLength`, `packedSparseSlots`,
`packedSparseWordSize`, `packedSparseSuperOverhead`, `packedSparseBlockOverhead`,
`packedSparseAuxLength`, `packedRankWordSize`, `packedRankBlockWidth`,
`packedRankSuperOverhead`, `packedRankBlockOverhead`, `packedRankSuperColumn`,
`packedRankBlockColumn`, `packedRankAuxLength`, `packedSummaryBaselineLength`,
`packedSummaryBlockColumnLength`, `packedSummaryLength`,
`packedInteriorLocalLength`, `packedLongBlockBits`.

`RMQ/Validation/EGCPFinalFalsification.lean` states each dependency's expected
type independently and discharges it with the library result, so weakening a
theorem breaks that file instead of being absorbed by it.

What this does not settle. The leaf is a statement about bit offsets in the
existing flat payload. It says nothing about spans, cell crossings, or reachability,
and nothing consumes it: `FG-02` asks about offsets "used by the packed execution",
and no packed execution exists. Both `FG-02` and `FG-03` therefore stay Open with
that dependency recorded, rather than being marked closed on the strength of the
leaf alone.

`FG-04` header leaf under `DD-20260802-001` (2026-08-03):

`RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/Header.lean` fixes
`packedPayloadLength n = 2 * n + concreteBPNativeSuccinctRMQOverhead
genericSparseExceptionBPCloseAccessOverhead n` and
`packedCellWidth n = SuccinctRank.machineWordBits (packedPayloadLength n + 2)`.

The commissioned width expression is adopted unchanged. The `+ 2` is what makes
both the largest payload bit index and the one-past-the-end address representable
at the same width, which is the property the address bound will need; no checked
equivalence-required correction was necessary.

`longCount_lt_two_pow_width` is unconditional. It goes through
`longCount <= packedSuperSlots n <= n <= packedPayloadLength n`, the middle step
being `GenericSelect.selectCeilDiv_le_self_of_pos` with the `n = 0` case handled
separately because that lemma needs a positive argument. Because the fit is
unconditional, `packedHeaderBits_decode` is too: it discharges the `_of_lt` side
condition of `bitsToNatLE_natToBitsLE_of_lt` from it rather than assuming a
threshold.

Also proves `shapeOfSize_self` and `mem_shapesOfSize_size`, since the canonical
payload-length theorem is keyed on membership in `shapesOfSize n` rather than on
`shape.size`, and every packed statement is keyed on the latter.

What this does not settle: no memory exists, so "the header occupies cell zero" is
not stated. Nothing here shows a controller ever reads the header. `FG-04` stays
Open on the first of those.

`FG-05` memory definitions under `DD-20260802-001` (2026-08-03):

`RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/Memory.lean` defines
`packedSerializedBits = packedHeaderBits ++ payload`, `packedCellCount n = 1 +
selectCeilDiv (P n) (w n)`, `packedAllocatedBits n = packedCellCount n * w n`,
`packedPaddedBits`, and `packedMemory`.

The chunker is a `List.range` map rather than the repository's existing fuel-based
`SuccinctSpace.chunkPayloadWords`. That chunker leaves a short final word, and
this representation must allocate whole cells; the difference is exactly the
padding `FG-06` has to charge for. Reusing the existing chunker would have made
the allocation look smaller than it is, which is the specific error
`FG-06` names ("Do not count only meaningful bits"), so the divergence is
deliberate and the padding is a named object rather than an implicit remainder.

Proved so far: `packedSerializedBits_length`, `packedSerialized_le_allocated` (via
`selectCeilDiv_mul_ge_of_pos`), `packedPaddedBits_length`, `packedMemory_length`,
`packedMemory_cell_length` (every allocated cell is exactly one full width, none
short), and `packedMemory_cell_zero` (the header is cell zero in full, so the
payload starts at cell one uniformly and no header field straddles a boundary).

Still open in this row: the join round trip, the slice/unpack behaviour for a span
crossing a cell boundary, and the theorem that all execution reads target this one
object. The last of those needs a controller and cannot be stated yet.

`FG-05` round trip (2026-08-04): `packedMemory_flatten` proves that concatenating
the allocated cells recovers the padded bit string exactly, via a general
`chunk_flatten` lemma for any width and any bit string whose length is an exact
multiple of it. `packedMemory_flatten_take` recovers the serialized prefix, so the
header and the whole canonical payload are readable from the cells alone.

The general lemma is stated over an arbitrary width rather than specialised to
`packedCellWidth`, so it also covers the degenerate widths at small sizes and does
not quietly assume a positive or byte-aligned cell.

`FG-06` allocated space under `DD-20260802-001` (2026-08-04):

`RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/Space.lean` proves
`packedAllocatedBits_le : packedAllocatedBits n <= 2 * n + packedRho n` with
`packedRho n = concreteBPNativeSuccinctRMQOverhead
genericSparseExceptionBPCloseAccessOverhead n + 2 * packedCellWidth n`, and
`packedRho_littleO`.

The `2 * packedCellWidth` term is the honest cost of whole-cell allocation: one
full cell for the header, and up to one more for the ceiling remainder of the
final cell. It is logarithmic in `n`, hence `o(n)`, but it is a real allocation
and is charged. Dropping it would have made the bound a statement about
meaningful bits, which is the specific substitution `FG-06` forbids.

Proving it `o(n)` needed a lemma the repository did not have. Every existing
little-o fact is about a function of `n`; the cell width is `machineWordBits` of
the *payload length*, which is linear in `n` rather than equal to it, so
`eventually_scale_log2_succ_le_self` does not apply directly.
`littleOLinear_machineWordBits_comp` supplies the missing step: if `f` is
eventually bounded by `K * n + C`, then `machineWordBits (f n)` is little-o
linear. The proof routes through `f n <= (K + C + 1) * n < 2 ^ (log2 n + K + C + 1)`,
using `nat_succ_le_two_pow` for `K + C + 1 <= 2 ^ (K + C)`.

The eventual linear bound on the payload length comes from
`genericSparseExceptionBPCloseAccessOverhead_le_linear` (global) together with
`compactBPCloseOverhead_littleO` at scale one (eventual). Stating the hypothesis
as eventual rather than global is what lets the second be used at all; no global
linear bound on the close overhead exists in the tree.

What this does not settle: the bound is proved over `packedMemory`, and nothing
yet shows that object is what an execution probes. `INV-STORE-IDENTITY` stays
open, and with it the row.

Shape-free component bases under `DD-20260802-001` (2026-08-04):

`packedComponentFlatOffset : Nat -> ConcreteBPNativeSuccinctRMQFlatPayloadComponent -> Nat`
and `packedComponentFlatOffset_eq` complete the other half of the addressing
story, and `packedSourceFlatOffset_eq` composes the two:

  concreteBPNativeSuccinctRMQFlatPayloadSourceFlatOffset shape source
    = packedSourceFlatOffset shape.size (longCount shape) source

Worth recording: the component bases need **no** long count. The four components
are separated by the BP code and the access padding, both size-only, so the long
count is required only for positions *within* the select component. That is a
sharper statement than "K = 1 suffices" and is what makes the header's role easy
to describe: it moves nothing except the local, sparse and close-adjacent bases
inside one component.

`FG-05` cell addressing (2026-08-04): `packedCellAt` names the `i`-th allocated
cell as a total function, `packedMemory_getElem?` ties it to the memory list at
every in-range index, and `packedCellPair` proves that two consecutive cells are
exactly the double-width window at the first one's base.

`packedCellPair` is the step the physical lowering needs: it is what will let a
logical word of at most one cell width be read from at most two probes. The span
theorem itself is not yet proved and is recorded as remaining.

`FG-05` cell crossing (2026-08-04): `packedSpan_from_two_cells` proves that any
span of at most one cell width, starting at any bit position, equals a slice of
the two consecutive cells containing it. It covers the aligned and
wholly-inside-one-cell cases too, because there the second cell simply
contributes nothing; nothing assumes a crossing actually occurs.

This is the bound the probe cap will rest on: two physical probes per logical
word, for every logical word no wider than a cell. Whether every executed logical
word satisfies that width hypothesis is a separate obligation and is not claimed
here.

`FG-07`/`FG-08` address arithmetic (2026-08-04):
`RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/Address.lean` supplies
`packedBitAddress`, `packedProbeCells` and `packedProbeOffset`, all `Nat`-only,
and proves `packedPayloadSlice` (the canonical payload sits exactly one header
cell into the packed memory, so the shift in the address is justified rather than
assumed) and `packedRead_from_two_cells`, which composes
`packedSourceFlatOffset_eq` with `packedSpan_from_two_cells`: any fixed-width
slice of the canonical payload, of width at most one cell, is recoverable from two
consecutive packed cells whose addresses are computed from the input size, the
decoded long count, the typed source, the index and the width.

This is the step that turns "which source and index do I want" into "which two
cells do I probe". It is not a controller: nothing here executes, and the range
and decoding obligations are untouched.

## DD-20260804-001: issue a conditional one-or-two-cell probe plan, and fetch through a failing accessor

Status: Worker decision recorded 2026-08-04 on branch
`codex/eg-cp-final-falsification-gate-r1`. Governs how `EG-CP` rows `FG-05`,
`FG-08` and `FG-09` compute and justify physical cell addresses. Supersedes the
`FG-07`/`FG-08` address-arithmetic paragraph appended to `DD-20260802-001` on
2026-08-04, which described `packedProbeCells`, `packedProbeOffset` and
`packedRead_from_two_cells`; those three declarations no longer exist.

Date: 2026-08-04

Context:

The first draft of the packed addressing layer computed, for a read starting at
bit `b`, the unconditional cell pair `(b / w, b / w + 1)`, and recovered the
requested span from the concatenation of those two cells. The recovery theorem
was true, but for the wrong reason at the end of the memory. `packedCellAt` is a
total function built from `List.drop` and `List.take`, so at any index at or past
`packedCellCount` it returns the empty list. A read wholly contained in the final
allocated cell therefore "succeeded" while naming an address that does not exist,
and the concatenation `cell ++ []` silently absorbed the difference.

That is precisely the shape of claim a cell-probe result must not make. The
content of a cell-probe bound is that the algorithm touches `C` real cells of a
real memory; a bound that counts an address the memory does not have is counting
something else.

Decision:

1. `packedProbePlan n bit width` is executable and conditional. It issues no
   probe for a zero-width request, one probe when
   `bit % w + width <= w`, and two probes otherwise. The charged count
   `packedProbeCount` is the issued plan's `length`, not a separately declared
   numeral.
2. Probes are issued through `packedProbeCell`, which is `List.getElem?` and
   therefore returns `none` outside the allocation, and a plan is issued through
   `packedFetch`, which returns `some` only when every address in the plan
   resolved. Nothing in the probe layer consults the total `packedCellAt`
   accessor to obtain a reply.
3. `packedProbePlan_lt_cellCount` proves that every issued address is below
   `packedCellCount n` from the single hypothesis
   `bit + width <= packedAllocatedBits n`, and `packedFetch_plan` turns that into
   a successful fetch. `packedProbePlan_decode` then proves the fetched cells
   decode to exactly the requested window, and `packedSourceRead_decode` states
   the same conclusion at the canonical payload slice of a typed source.

Rationale:

The three-way split is stronger than the two-way one the prompt's wording
suggests, not weaker: a zero-width request has an empty requested range, and
issuing one probe for it would be an address the allocation need not contain when
the request sits exactly at the end of the memory. Making the empty case explicit
removes the only hypothesis (`bit < packedAllocatedBits n`) that would otherwise
have to be carried alongside the range-fits hypothesis, so the allocation theorem
now has one premise instead of two.

Fetching through `List.getElem?` rather than a total accessor is what makes the
allocation claim load-bearing. With a total accessor the decoding theorem holds
whether or not the address exists, so no mutation of the address arithmetic can
be detected by it. With the failing accessor, an out-of-range address makes
`packedFetch` return `none` and the decoding equation becomes unprovable.

Consequences and evidence:

- `packedMemory_getElem?_cellCount : (packedMemory shape)[packedCellCount
  shape.size]? = none` records that the address the old plan issued at the end of
  the memory is genuinely absent, so the repair is not cosmetic.
- `packedProbe_final_cell` is the boundary case that separates the two designs: a
  positive-width read contained in the last allocated cell issues exactly
  `[packedCellCount - 1]` and fetches successfully. Under the old plan the second
  issued address would have been `packedCellCount`, and the fetch would have
  returned `none`.
- `packedProbePlan_of_offset` and `packedProbePlan_of_crossing` show both
  branches are reachable, so the conditional is not constant in disguise.
  `packedCellWidth_ge_two` is needed for the second: a one-bit cell could not be
  straddled and the crossing instances would be vacuous.
- `packedProbe_covers_range` states coverage in the form that survives the
  zero-width case: after skipping the in-cell offset, at least `width` bits
  remain in the fetched window.
- `packedProbeCount_le_two` is an upper bound on the probes of one logical read.
  It is not a whole-run cap: no run exists yet, and `FG-09` requires the cap to
  be derived from an actual execution.

## DD-20260804-002: state the raw payload identity separately from its length

Status: Worker decision recorded 2026-08-04 on branch
`codex/eg-cp-final-falsification-gate-r1`. Governs how `EG-CP` row `FG-01` is
evidenced.

Date: 2026-08-04

Context:

Until this commit the packed modules referred to the stored bits only through
`(concreteBPNativeSuccinctRMQFlatPayloadLayout shape).payload` and through the
length theorem `packedPayloadLength_eq`. A length agreement is exactly the kind
of evidence `INV-STORE-IDENTITY` rejects: a separately defined payload of the
same length satisfies it, and registry mutation `M11-SIBLING-PAYLOAD` is built to
exploit that gap.

Decision:

`RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/Payload.lean` names the stored bits
`packedPayloadBits` and proves
`packedPayloadBits shape = concreteBPNativeSuccinctRMQPayload
builtGenericSparseExceptionSelectBPCloseAccessFamily shape` by `rfl`, with a
list-facing companion `packedPayloadBitsOfList_eq_canonical`. `packedSerializedBits`
is redefined to append that object, and `packedSerializedBits_drop_header` proves
that dropping the one header cell recovers it exactly.

Rationale:

`rfl` is the strongest available form of this row's evidence: the right-hand side
is the existing canonical definition applied to the existing access family, so
there is no second object to keep in sync and no equality that could be proved
about a copy. Stating it separately from the length keeps the two obligations
distinguishable in the matrix; folding it into `packedPayloadLength_eq` would
make a sibling payload look closed.

Consequences and evidence:

- `packedSerializedBits_drop_header` is the "no hidden table" clause in the form
  a reader can check: everything after the header cell is the canonical payload,
  so an extra table would have to be inside that object and would be counted by
  the space row.
- `packedPayloadBits_eq_bpCode_append_aux` expands one level, recording that the
  stored string is the BP code followed by the auxiliary payload and nothing
  else.
- The identity is now consumed rather than merely stated: `packedSerializedBits`,
  hence `packedPaddedBits`, `packedMemory` and every probe theorem, take their
  bits from this object.

## DD-20260804-003: type the logical read address without a shape, and leave the width mirror open

Status: Worker decision recorded 2026-08-04 on branch
`codex/eg-cp-final-falsification-gate-r1`. Governs how `EG-CP` row `FG-08` will
present a per-read lowering, and records what is deliberately not claimed.

Date: 2026-08-04

Context:

A logical read of the flat payload store is the pair `(segment, index)`. Turning
it into physical probes needs three things: the typed source the segment names,
the source's bit offset, and the source's word width. The first two are already
shape-free -- `concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?` has type
`Nat -> Option Source`, and `packedSourceFlatOffset` has type
`Nat -> Nat -> Source -> Nat` with `packedSourceFlatOffset_eq` proving agreement.
The third has no mirror yet.

Decision:

Record the address side now, with the width as an explicit argument.
`packedSegmentSource?` names the segment map at the packed layer,
`packedLogicalProbePlan` composes it with the conditional probe plan, and
`packedLogicalRead_decode` proves that the issued cells decode to the canonical
payload slice of the source that segment names. The width is not synthesized,
guessed, or defaulted; a caller must supply it.

Do not define a `packedSourceWidth` mirror before its agreement theorem is
proved. A mirror without its agreement theorem is a placeholder that would make
the lowering look closed while the only load-bearing step was missing.

Rationale:

Partial factorization is worth recording only when the boundary is explicit. The
alternative -- waiting until the width mirror exists before naming the logical
plan at all -- would have hidden the fact that two of the three ingredients are
already `Nat`-only, which is the part a successor session does not have to redo.

Consequences and evidence:

- `packedLogicalProbePlan : Nat -> Nat -> Nat -> Nat -> Nat -> List Nat`. Its
  signature carries the claim for the address side: no shape, no list, no proof
  argument, no callback.
- `packedLogicalProbePlan_length_le_two` gives the per-read probe bound including
  the unmapped-segment case, which issues nothing.
- The next leaf is `packedSourceWidth : Nat -> Nat -> Source -> Nat` together
  with the agreement theorem that every word of
  `concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape source` has that
  length. Most of the underlying width mirrors already exist in
  `SourceFactorization.lean` (`packedSuperWidth`, `packedLocalWidth`,
  `packedRankWordSize`, `packedSummaryRelativeWidth`,
  `packedInteriorOffsetWidth`, `packedLongFlagWordSize`,
  `packedSparseWordSize`); what is missing is the per-source selection and the
  per-constructor agreement proof.
- A separate gap is recorded rather than papered over: the flat-payload segment
  universe and the executed global-store segment universe do not agree at
  segments 21 and 22, which `FlatPayload.lean` documents in place. Any whole-run
  lowering must state which universe it lowers, and the packed layer currently
  lowers the flat-payload one.

## DD-20260804-004: separate a source's stride from its read width

Status: Worker decision recorded 2026-08-04 on branch
`codex/eg-cp-final-falsification-gate-r1`. Governs how `EG-CP` row `FG-08`
addresses a chunked bit source.

Date: 2026-08-04

Context:

`packedBitAddress n longCount source index width` computes
`packedCellWidth n + packedSourceFlatOffset n longCount source + index * width`.
Multiplying the index by the *read width* silently assumes that a source's stride
and its read width coincide. For a fixed-width natural-number table they do: the
`FixedWidthNatTable` structure carries `width` as a type index and its
`word_length_of_get?` field forces every stored word to that length.

They do not coincide for a chunked bit source. `SuccinctSpace.chunkPayloadWords`
cuts a bit string into `wordSize`-bit words and leaves the final word short
whenever the length is not a multiple of `wordSize`; `chunkPayloadWords_get?_eq_take_drop`
states exactly that: word `i` is `(payload.drop (i * wordSize)).take wordSize`,
which truncates at the end of the payload. Four of the twenty-nine typed sources
are such chunkings — `bpCode`, `selectLongFlagBits`, `selectSparseFlagBits` and
`finalRankBPCodeAlias`.

Reading the final word of such a source at full width against the packed memory
would not truncate, because in the packed memory the next component follows
immediately. It would return the correct prefix followed by bits of the next
component. That is a wrong decoded word, not a harmless over-read.

Decision:

Add `packedStridedBitAddress n longCount source index stride`, identical in form
but taking the stride rather than the width, with
`packedBitAddress_eq_strided` recording that the uniform-width address is the
special case. Keep `packedBitAddress` for the fixed-width tables.

For the BP code, define `packedBpCodeWordWidth n = machineWordBits (2 * n)` as the
stride and
`packedBpCodeReadWidth n index = min (packedBpCodeWordWidth n) (2 * n - index * packedBpCodeWordWidth n)`
as the exact read width, and prove `packedBpCodeRead_decode`: for every shape and
every BP-code word the flat payload store would return, the probe plan at that
address and width fetches successfully and decodes to exactly that word.

Rationale:

Widening `packedBitAddress` in place would have changed the meaning of an
already-pinned signature. Adding the strided form leaves the existing consumers
intact and makes the distinction visible at the type level, which is where the
defect was invisible before.

Defining the read width as a `min` rather than case-splitting on "last word or
not" keeps it a single arithmetic expression in `(n, index)`, which is what a
controller has to evaluate.

Consequences and evidence:

- `packedBpCodeRead_decode` is the first source lowered completely: address,
  stride and read width are all functions of `n` and the index, and the decoded
  bits are proved equal to the store word. Pinned by
  `packedBpCodeReadDecodesToTheStoreWord`.
- `packedBpCodeWord_index_lt` derives the in-range condition from the existence
  of the word rather than assuming it, so the theorem has no side condition a
  controller would have to discharge from outside its inputs.
- `packedBpCodeWordWidth_le_cellWidth` discharges the width hypothesis of the
  probe plan from `2 * n <= packedPayloadLength n + 2` and monotonicity of
  `machineWordBits`.
- The remaining three chunked bit sources are not done. Their stride mirrors
  exist (`packedLongFlagWordSize`, `packedSparseWordSize`) and their payload
  lengths are size-only (`longFlagBits_length_eq_packed`,
  `sparseFlagBits_length_eq_packed`), so the same construction should apply; that
  has not been checked.
- This finding narrows the next target recorded in `DD-20260804-003`: the
  per-source width mirror is not one function but two, a stride and a read width,
  and only the fixed-width-table sources can share a single expression.

## DD-20260804-005: the long count is a probe reply, not a supplied argument

Status: Worker decision recorded 2026-08-04 on branch
`codex/eg-cp-final-falsification-gate-r1`. Governs how `EG-CP` rows `FG-04` and
`FG-07` treat the header descriptor.

Date: 2026-08-04

Context:

Every packed address function on this branch takes `longCount` as an explicit
`Nat` argument, and every agreement theorem instantiates it at `longCount shape`.
Read literally, that is a definition parameterized by a quantity derived from the
shape. `FG-07` forbids the controller from receiving shape-derived data other
than through `n` and prior replies, so leaving the long count as a supplied
argument would leave the whole address layer outside the controller's reach even
though its type mentions no shape.

Decision:

State where the argument comes from. `packedHeaderProbePlan = [0]` is the
controller's first probe; `packedHeaderFetch` proves it is allocated at every
size and returns the header cell; `packedHeaderProbe_decode` proves that decoding
that cell with the ordinary little-endian codec yields exactly `longCount shape`,
at every size and with no side condition.

Rationale:

This is the smallest statement that converts the long count from data the
controller would have to be given into data it can obtain. It is deliberately
stated over the same `packedFetch` and `packedMemory` as every other probe, so
the header read is charged like any other read rather than treated as
preprocessing; `packedHeaderProbePlan_length = 1` records its cost.

The alternative -- proving only that the header cell decodes, which
`packedHeaderBits_decode` already did -- leaves the gap this entry closes: a
decodable header that nothing fetches is a field, not a reply.

Consequences and evidence:

- Pinned by `packedHeaderProbeCostsOneProbe`,
  `packedHeaderProbeFetchesTheHeaderCell` and `packedLongCountComesFromAProbe`.
- `packedMemory_cell_zero` is the load-bearing step: it states that cell zero is
  the header **in full**, so no part of the descriptor is split across cells and
  the first probe needs no crossing case.
- This does not close `FG-07`. There is still no controller: nothing sequences
  the header probe before the address computation, and no definition consumes the
  reply. What is now available is that such a definition would not need any input
  beyond `n` to obtain the long count.

## DD-20260804-006: the controller obligation is a scalar factorization, not an architecture change

Status: Worker finding recorded 2026-08-04 on branch
`codex/eg-cp-final-falsification-gate-r1`. Governs how `EG-CP` row `FG-07` is
approached. This entry records a checked structural fact, not a closure.

Date: 2026-08-04

Context:

`FG-07` requires an executed controller whose dynamic inputs are exactly `n`, the
query endpoints, the header reply and prior replies. The existing supplied-store
query leaves visibly take shape-derived data:
`concreteBPNativeSelectCloseGlobalWordTraceResultWithStore` is built from
`GenericSelect.sparseExceptionSelectData shape.bpCode false`. Read at face value
that looks like an architecture problem: a leaf handed the shape's own tables
might be computing its answers from them, in which case the store would be
decoration and no amount of address factorization would produce a controller.

Two readings were possible and they lead to very different campaigns. Either the
shape-derived record supplies the *replies*, in which case `FG-07` needs a
different execution architecture; or it supplies only the *geometry* -- strides,
field widths, slot counts -- in which case `FG-07` needs the same kind of
`Nat`-only mirror the offsets already have, and nothing else.

Decision:

Settle it by proof rather than by reading the source, and record the result where
the next session will find it.

`SuccinctSpace.PayloadWordStore.readProgram` ignores its store argument: its
binder is `_store` and its body is `WordRAM.Program.readWord 0 i`. Therefore:

- `packedTableReadProgram_content_free` -- two `FixedWidthNatTable`s with
  unrelated entry lists and unrelated widths issue the same read program at the
  same index;
- `packedTableReadProgram_eq_readWord` -- that program is
  `mapOptWordNat (readWord 0 index)`;
- `packedSelectEntryRead_content_free` -- given the same segment layout, the same
  supplied store and the same index, two select entry tables with unrelated
  entries and unrelated field widths produce the **same trace result**: the same
  reads, in the same order, with the same replies, and the same decoded entry.

All three are `rfl`.

Rationale:

The third theorem is the decisive one. It quantifies over two tables that share
no parameter, so it cannot be satisfied by a leaf that consults its table for a
reply. A congruence over shapes of equal size would have been weaker and would
have invited the objection recorded in `DD-20260802-001`: a congruence says the
result is determined, not that a controller can compute it. This statement is
stronger in the direction that matters -- the table is not consulted at all.

The prompt for this campaign instructed that the unconditional-two-probe defect
be treated as a repairable lowering obligation rather than an architecture
obstruction. This finding is the independent evidence for the same conclusion one
level up, and it is what a future obstruction claim would have to overturn.

Consequences and evidence:

- Pinned by `packedTableReadIsAnIndexNotALookup` and
  `packedSelectEntryReadIsDeterminedByTheStore`.
- The remaining shape-dependence of `bpChunkedSelectTraceResultWithStore` is a
  fixed list of scalars from the same record: `superStride`, `localStride`,
  `localSlotsPerSuper`, `wordSize`, `queryOccurrence`, and
  `occurrenceCount bits target`, plus `SuccinctClose.bpFringeChunkBits
  shape.bpCode.length` supplied beside it. Each needs a `Nat`-only mirror and an
  agreement theorem, exactly as the offsets did.
- This does **not** close `FG-07`, and it is not evidence about the close/LCA
  side, which has its own leaves. It bounds the shape of the remaining work: a
  scalar factorization over a fixed list, with elaborator-enforced coverage
  available because the record's fields are fixed.

## DD-20260804-007: mirror the select leaf's geometry scalars and its validity guard

Status: Worker decision recorded 2026-08-04 on branch
`codex/eg-cp-final-falsification-gate-r1`. Continues `DD-20260804-006` and feeds
`EG-CP` row `FG-07`.

Date: 2026-08-04

Context:

`DD-20260804-006` bounded the select-side controller work to a `Nat`-only mirror
for a fixed list of scalars. This entry does that list, except one item.

`GenericSelect.sparseExceptionSelectData bits target` sets

```
wordSize           := wordBits bits.length
superStride        := superStride bits.length
localStride        := localStride bits.length
localSlotsPerSuper := localSlotsPerSuper bits.length
```

Each is a function of `bits.length` alone, and for the close-select instance
`bits = shape.bpCode`, whose length is `2 * shape.size`
(`CartesianShape.bpCode_length`). The leaf's validity dispatch is
`idx < occurrenceCount bits target`, and for `target = false` that count is the
number of closing parentheses, which is the input size.

Decision:

Add `packedSelectWordSize`, `packedSelectSuperStride`, `packedSelectLocalStride`
and `packedSelectLocalSlotsPerSuper`, each of type `Nat -> Nat` and each defined
at `2 * n`, with an agreement theorem against the corresponding record field. Add
`packedSelectOccurrenceCount_eq_size : occurrenceCount shape.bpCode false =
shape.size`.

Rationale:

The mirrors are defined at `2 * n` rather than at `shape.bpCode.length` on
purpose. Defining them at the code length would have produced theorems that are
true and useless: a controller cannot evaluate `shape.bpCode.length` without the
shape. Taking `bpCode_length` at the definition site rather than at the use site
is what turns the fact into an executable expression.

The validity guard is worth stating separately because it is the only place the
leaf branches on a quantity that is not a probe reply. Had it been anything other
than a function of `n`, the `K = 1` header would have needed a second field --
which is precisely the kind of finding that would have forced an architecture
decision. It does not.

Consequences and evidence:

- Pinned by `packedSelectWordSizeIsSizeOnly`,
  `packedSelectSuperStrideIsSizeOnly`, `packedSelectLocalStrideIsSizeOnly`,
  `packedSelectLocalSlotsPerSuperIsSizeOnly` and
  `packedSelectValidityGuardIsTheInputSize`, with the four signatures pinned as
  `Nat -> Nat`.
- `queryOccurrence` is **not** mirrored and is not claimed. It is the one
  remaining select-side scalar named in `DD-20260804-006`.
- The close/LCA leaves are untouched. They have their own records and their own
  scalars, and nothing here is evidence about them.
- This does not close `FG-07`. No controller definition exists.

### Addendum to `DD-20260804-007` (2026-08-04): the scalar list is complete

`GenericSelect.SparseExceptionSelectData.queryOccurrence` binds its record as
`_data` and therefore ignores it. `packedSelectQueryOccurrence_content_free`
records that as a checked theorem over two records sharing no parameter:
different bit strings, different targets, different overheads, same occurrence at
the same index.

That closes the select-side scalar list opened by `DD-20260804-006`. Its five
items are now: `wordSize`, `superStride`, `localStride` and `localSlotsPerSuper`
mirrored at `2 * n` with agreement theorems; `occurrenceCount` proved equal to
`n`; and `queryOccurrence` proved content-free. Nothing on the select side is
left needing the shape except through `n`.

Pinned by `packedSelectQueryOccurrenceIsTheIndexAlone`.

This still does not close `FG-07`. No controller definition exists, the close and
LCA leaves have not been examined, and `SuccinctClose.bpFringeChunkBits
shape.bpCode.length` is supplied beside the select data rather than inside it.

### Second addendum to `DD-20260804-007` (2026-08-04): two more read helpers are content-free

`bpChunkedSelectTraceResultWithStore` reaches the supplied store through four
helpers. Three are now covered:

- the four-field entry-table read (`packedSelectEntryRead_content_free`,
  `DD-20260804-006`);
- the dense two-word select read
  (`packedDenseTwoWordSelectRead_content_free`): two bit stores over **unrelated
  bit strings**, sharing only the word size, give the same trace result. The word
  size is a type index rather than stored data, so the helper consults its
  argument for a scalar and reads everything else from the supplied store;
- the relative-offset read, whose declared type is
  `WordRAM.ReadStore -> Nat -> Nat -> Nat -> WordRAM.TraceResult (Option Nat)`.
  It takes no record at all, so nothing shape-derived can reach it. Pinned by
  `packedRelativeOffsetReadSignature`.

The fourth, the two-level rank read
(`SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.bpChunkedRankTraceResultWithStore`),
consumes derived indices of its own record (`data.superIndex pos` and its
neighbours) and is **not** covered. Those indices are computed from the record's
block and super sizes, so the expected shape of the remaining work is another
scalar mirror, but that is a prediction and not a result.

Pinned by `packedDenseTwoWordSelectReadIsDeterminedByTheStore` and
`packedRelativeOffsetReadSignaturePin`.

### Third addendum to `DD-20260804-007` (2026-08-04): the fourth read helper is scalar-determined

`SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.bpChunkedRankTraceResultWithStore`
mentions its record only through `superIndex`, `wordIndex` and `wordOffset`, and
those unfold to `queryPos pos`, `wordSize` and `blocksPerSuper`.

`packedRankRead_scalar_determined` proves that two rank records over unrelated
bit strings, with unrelated overheads and unrelated query costs, produce the same
trace result whenever those three agree. Unlike the other three helpers this one
is not content-free — it genuinely consults its record — but it consults it only
for scalars, which is the property that matters.

All four helpers `bpChunkedSelectTraceResultWithStore` uses to reach the store
are now accounted for:

| Helper | Result |
| --- | --- |
| four-field entry-table read | content-free |
| dense two-word select read | content-free at a fixed word size |
| relative-offset read | takes no record at all |
| two-level rank read | determined by `queryPos pos`, `wordSize`, `blocksPerSuper` |

What remains before the select leaf itself can be stated scalar-determined is the
sparse-directory helper `SparseExceptionDirectory.bpChunkedReadTraceResultWithStore`,
which has not been examined, and then an assembly theorem carrying one hypothesis
per scalar. Neither is claimed.

Pinned by `packedRankReadIsDeterminedByThreeScalars`.

## DD-20260804-008: build the controller through a Nat-only geometry record, not a congruence between dependent records

Status: Worker decision recorded 2026-08-04 on branch
`codex/eg-cp-final-falsification-gate-r1`. Directs how the `FG-07` controller
should be constructed, based on an obstacle found while trying to assemble the
select leaf from its helper results.

Date: 2026-08-04

Context:

All five helpers that `bpChunkedSelectTraceResultWithStore` uses to reach the
supplied store are now accounted for:

| Helper | Result |
| --- | --- |
| four-field entry-table read | content-free |
| dense two-word select read | content-free at a fixed word size |
| relative-offset read | takes no record at all |
| two-level rank read | determined by `queryPos pos`, `wordSize`, `blocksPerSuper` |
| sparse-directory read | determined by those three plus `localStride` |

The obvious next step is an assembly theorem: two `SparseExceptionSelectData`
records agreeing on the scalar list produce the same leaf result. That step does
not go through cleanly, and the reason is worth recording rather than
rediscovering.

`data.bitWords` has type `BoundedPayloadWordStore bits data.wordSize`. Its word
size is a **type index** carrying the record's own field. The content-free
theorem for the dense two-word read requires both bit stores at the *same* index.
Given only a propositional `dataLeft.wordSize = dataRight.wordSize` between two
distinct records, closing that gap requires transporting a dependent type along
an equation between two projections, neither of which is a local variable, so
neither `subst` nor a plain `rw` applies. The same pattern recurs wherever a
geometry scalar appears as a type index rather than as a value.

Decision:

Do not pursue the congruence-between-records route for the controller. Build the
controller as a definition over a `Nat`-only geometry record -- the mirrors
already proved size-only (`packedSelectWordSize`, `packedSelectSuperStride`,
`packedSelectLocalStride`, `packedSelectLocalSlotsPerSuper`) plus the decoded
`longCount` -- and relate it to the existing leaf by instantiating the leaf at
the canonical shape, not by comparing two arbitrary records.

Rationale:

A congruence between two dependently-indexed records fights the elaborator at
every scalar that appears as an index, and it would not produce an executable
definition even if it succeeded -- which is the same objection `DD-20260802-001`
raised against congruences generally. The `Nat`-only record has neither problem:
its fields are values, so no transport arises, and it is something a controller
can hold.

The helper results are not wasted by this decision. They are what makes the
`Nat`-only record adequate: they show the leaf reads the supplied store and
consults its record only for the scalars the record would carry.

Consequences and evidence:

- The five helper theorems stand as recorded, pinned by
  `packedSelectEntryReadIsDeterminedByTheStore`,
  `packedDenseTwoWordSelectReadIsDeterminedByTheStore`,
  `packedRelativeOffsetReadSignaturePin`,
  `packedRankReadIsDeterminedByThreeScalars` and
  `packedSparseDirectoryReadIsDeterminedByFourScalars`.
- The rank-side scalars `queryPos`, `wordSize` and `blocksPerSuper` of
  `longFlagRankData` and of `sparseDirectory.rankData` are **not** yet mirrored
  as size-only functions. They are the next mirrors the `Nat`-only record needs.
- No controller definition exists and `FG-07` remains Open. This entry chooses a
  construction route; it does not walk it.

### Addendum to `DD-20260804-008` (2026-08-04): the rank query position reduces to a bit length

`SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.queryPos` binds its record as
`_data`; its body is `Nat.min pos bits.length`.
`packedRankQueryPos bitLength pos = Nat.min pos bitLength` mirrors it, with
`packedRankQueryPos_eq` proved by `rfl` and
`packedRankQueryPos_length_determined` giving the congruence over unrelated
records from equal bit lengths alone.

That reduces one of the rank read's three scalars to a length, and this
development already has size-only mirrors for the lengths of both rank records
the select leaf uses: `longFlagBits_length_eq_packed` for `longFlagRankData` and
`sparseFlagBits_length_eq_packed` for `sparseDirectory.rankData`.

Remaining for the `Nat`-only geometry record on the select side:
`blocksPerSuper` for both rank records. Their `wordSize` mirrors already exist
(`longFlagRankWordSize_eq_packed`, `sparseFlagRankWordSize_eq_packed`).

Pinned by `packedRankQueryPosIsTheBitLengthAlone` and
`packedRankQueryPosSignature`.

### Second addendum to `DD-20260804-008` (2026-08-04): the select-side scalar list is discharged

Both rank records the select leaf uses group one block per super block.
`GenericSelect.longFlagRankBlocksPerSuper` and
`GenericSelect.sparseExceptionEffectiveFlagRankBlocksPerSuper` each bind both
arguments as `_bits`/`_target` and return `1`, so
`packedLongFlagBlocksPerSuper_eq` and `packedSparseFlagBlocksPerSuper_eq` are
`rfl`. A literal cannot carry shape content, so neither needs a mirror.

That discharges the whole select-side list. Every scalar
`bpChunkedSelectTraceResultWithStore` consumes is now one of:

| Scalar | Status |
| --- | --- |
| `wordSize`, `superStride`, `localStride`, `localSlotsPerSuper` | size-only mirrors at `2 * n`, with agreement theorems |
| `occurrenceCount bits target` | proved equal to `shape.size` |
| `queryOccurrence` | content-free |
| rank `queryPos` | `Nat.min pos bits.length`, both lengths already mirrored size-only |
| rank `wordSize` | mirrors already existed (`longFlagRankWordSize_eq_packed`, `sparseFlagRankWordSize_eq_packed`) |
| rank `blocksPerSuper` (both records) | literal `1` |
| `sparseDirectory.localStride` | `localStride bits.length`, the same expression as the mirrored select local stride |

and all five read helpers are content-free or scalar-determined.

`SuccinctClose.bpFringeChunkBits shape.bpCode.length` is supplied beside the
select data rather than inside it and is still unmirrored; it is a length of the
BP code, so the mirror is immediate, but it has not been written.

Pinned by `packedLongFlagBlocksPerSuperIsOne` and
`packedSparseFlagBlocksPerSuperIsOne`.

This does not close `FG-07`: no controller definition exists. What it means is
that the `Nat`-only geometry record chosen in `DD-20260804-008` has no missing
field on the select side.

### Third addendum to `DD-20260804-008` (2026-08-04): the fringe chunk width

`packedFringeChunkBits n = SuccinctClose.bpFringeChunkBits (2 * n)`, with
`packedFringeChunkBits_eq` proving agreement at `shape.bpCode.length`. This is
the one scalar the select leaf receives beside its data record -- the layout
calls it `c` -- and it is a width of the BP code, so the mirror is immediate.

With it, **nothing the select leaf consumes still needs the shape**. Every input
is the supplied store, a query index, a literal, or a size-only function of `n`.

Pinned by `packedFringeChunkBitsIsSizeOnly` and
`packedFringeChunkBitsSignature`.

`FG-07` is still Open: no controller definition exists, and the close/LCA leaf
tower has not been examined.

## DD-20260804-009: build controller components by inlining, and prove them equal by `rfl`

Status: Worker decision recorded 2026-08-04 on branch
`codex/eg-cp-final-falsification-gate-r1`. Supplies the construction technique
for `EG-CP` row `FG-07`, and lands the first component.

Date: 2026-08-04

Context:

`DD-20260804-006` through `DD-20260804-008` established that the select leaf
reads the supplied store and consults its shape-derived record only for scalars,
and that every one of those scalars is a literal or a size-only function of `n`.
That is an analysis. It does not by itself produce a definition a controller can
call: the existing leaf still takes the record as an argument, and `FG-07`
forbids handing one to the controller.

Two construction routes were available. Constructing a canonical dummy record
from `n` and passing it would be registry mutation `M04-CANONICAL-SHAPE-BY-N`
in spirit and would also require inhabiting several dependent structures.
Rewriting the leaf into a `Nat`-only definition and proving the two equal
propositionally would work but leaves an ordinary theorem obligation at every
layer.

Decision:

Inline. Where a helper's use of its record reduces to a term the record does not
influence -- as `PayloadWordStore.readProgram` does, binding its store as
`_store` -- write the record-free definition with that term substituted directly,
and prove the equality by `rfl`.

`packedSelectEntryRead layout store index` is the first component built this way.
It takes a segment layout, a supplied store and an index, and nothing else.
`packedSelectEntryRead_eq` proves

```
table.readTraceResultRelabeledWithStore layout store index =
  packedSelectEntryRead layout store index
```

for **every** table, over any entries and any field width, by `rfl`.

Rationale:

`rfl` is the strongest available form of this obligation and the cheapest. The
two sides are the same term, so no rewriting is needed at the call site and no
transport arises -- which is exactly the failure mode `DD-20260804-008` recorded
for the congruence route. It also means the record-free definition cannot drift
from the leaf: if the leaf changes, the `rfl` breaks.

The technique generalizes only where the record's influence is definitionally
absent. Where a helper genuinely consults scalars -- the two-level rank read
does -- the record-free version must take those scalars as arguments, and the
equation becomes conditional on the corresponding mirrors. That is expected and
is how the geometry record of `DD-20260804-008` earns its fields.

Consequences and evidence:

- Pinned by `packedSelectEntryReadSignature` (the type carries the claim: no
  table, no shape, no list, no proof argument) and
  `packedSelectEntryReadIsTheLeafRead`.
- This is the **first component of the `FG-07` controller to exist**. Previous
  entries recorded what a controller could be built from; this one is something a
  controller can call.
- `FG-07` remains Open. One component is not a controller: there is no fixed
  top-level definition, no header-then-address sequencing, no `receipt`, and the
  close/LCA leaf tower is unexamined.

### Addendum to `DD-20260804-009` (2026-08-04): the scalar-taking case behaves as predicted

`packedRankRead` is the second controller component. Unlike
`packedSelectEntryRead` it takes scalars -- the bit length, the word size and the
blocks per super block -- because the two-level rank read genuinely consults its
record for those three projections. `DD-20260804-009` predicted that shape, and
it holds:

```
packedRankRead_eq (data) (store) (segments...) (target) (pos) :
  data.bpChunkedRankTraceResultWithStore store superSegment blockSegment
      wordSegment chunkSegment chunkBits target pos =
    packedRankRead superSegment blockSegment wordSegment chunkSegment
      chunkBits target store bits.length data.wordSize data.blocksPerSuper pos
```

by `rfl`, over records with any bit string, any overheads and any query cost.

The three scalars are exactly the ones already discharged: `bits.length` is
mirrored size-only for both rank records the select leaf uses, `wordSize` has
existing mirrors, and `blocksPerSuper` is the literal `1`. So the arguments a
controller would have to supply are all available to it from `n`.

Pinned by `packedRankReadSignature` and `packedRankReadIsTheLeafRankRead`.

Two of the five select helpers are now record-free definitions rather than
theorems about records. `FG-07` remains Open.

### Second addendum to `DD-20260804-009` (2026-08-04): the third component composes the first two

`packedSparseDirectoryRead` is the record-free sparse-directory read. It is built
from `packedRankRead` and the already record-free relative-offset read, plus one
further scalar, the local stride, and
`packedSparseDirectoryRead_eq` proves it equal to
`SparseExceptionDirectory.bpChunkedReadTraceResultWithStore` by `rfl`.

That the composition also closes by `rfl` is the point: the inlining technique
composes, so a record-free definition built from record-free parts does not
accumulate rewriting obligations.

Three of the five select helpers are now record-free definitions. The
relative-offset read never took a record. The one still stated only as a theorem
is the dense two-word select read, which is content-free at a fixed word size;
turning it into a definition means transcribing its body with `wordSize` as an
argument.

Pinned by `packedSparseDirectoryReadSignature` and
`packedSparseDirectoryReadIsTheLeafDirectoryRead`.

`FG-07` remains Open: there is still no top-level controller.

## DD-20260804-010: the close-select leaf is record-free

Status: Worker result recorded 2026-08-04 on branch
`codex/eg-cp-final-falsification-gate-r1`. Completes the select-side
construction begun in `DD-20260804-009`. Feeds `EG-CP` row `FG-07`.

Date: 2026-08-04

Context:

`DD-20260804-009` established the inlining technique and landed
`packedSelectEntryRead`. Its addenda landed `packedRankRead` and
`packedSparseDirectoryRead`, and showed that the technique composes: a
record-free definition built from record-free parts closes by `rfl` with no
accumulated rewriting.

Decision and result:

Apply it to the leaf itself. `packedDenseTwoWordSelectRead` completes the four
helpers -- its body never mentions its bit store, only the word size that reaches
it as a type index, so taking the word size as an ordinary argument removes the
record without changing the term. `packedSelectCloseRead` is then the whole leaf:

```
packedSelectCloseRead
  (layout : SparseExceptionSelectTraceSegmentLayout)
  (chunkSegment selectTableSegment : Nat) (store : WordRAM.ReadStore)
  (chunkBits : Nat) (target : Bool)
  (occurrenceCount superStride wordSize localSlotsPerSuper localStride : Nat)
  (longFlagBitLength longFlagWordSize longFlagBlocksPerSuper : Nat)
  (sparseBitLength sparseWordSize sparseBlocksPerSuper sparseLocalStride : Nat)
  (idx : Nat) : WordRAM.TraceResult (Option Nat)
```

with `packedSelectCloseRead_eq` proving

```
data.bpChunkedSelectTraceResultWithStore layout chunkSegment selectTableSegment
    store chunkBits idx =
  packedSelectCloseRead layout chunkSegment selectTableSegment store chunkBits
    target (occurrenceCount bits target) data.superStride data.wordSize ... idx
```

by `rfl`, for every `SparseExceptionSelectData`.

`queryOccurrence` binds its record as `_data` and returns `idx`, so it inlines to
`idx`.

Rationale:

The signature is the claim. `FG-07` forbids the controller from accepting a
`CartesianShape`, a source program, a list or a proof callback; this definition's
type contains none of them, and the elaborator enforces that. The `rfl` means the
record-free leaf cannot drift from the real one.

Consequences and evidence:

- Every scalar the equation supplies has already been discharged for the
  close-select instance: `occurrenceCount bits target = shape.size`;
  `superStride`, `wordSize`, `localSlotsPerSuper`, `localStride` have size-only
  mirrors at `2 * n`; both `blocksPerSuper` are the literal `1`; both bit lengths
  are mirrored size-only; the sparse local stride is the same `localStride`
  expression. **A controller holding only `n` can supply every argument.**
- Pinned by `packedSelectCloseReadSignature`, `packedSelectCloseReadIsTheLeaf`,
  `packedDenseTwoWordSelectReadSignature`.
- `FG-07` is **not** closed. This is one component of the query, not the query:
  the whole-query program also has `lcaClose`, `rankCloseIfSome` and
  `outputPredIfSome` instructions whose leaves live in the close/LCA tower, which
  has not been examined. There is still no top-level controller definition, no
  header-probe-then-address sequencing, and no `receipt`.

### Addendum to `DD-20260804-010` (2026-08-04): the close-side rank leaf reuses the same component

`concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore` is
`bpChunkedRankTraceResultWithStore` on `builtRelativeSplitBPCloseRankData shape`
at a different segment base. So the record-free version is `packedRankRead`
again: `packedRankCloseRead` is a thin renaming of it, and
`packedRankCloseRead_eq` is `rfl`.

That is worth recording because it means the close side does not automatically
need new machinery. Of the whole-query program's four instructions,
`selectClose` and `rankCloseIfSome` now both reach the store through record-free
definitions, and `outputPredIfSome` touches no store at all. Only `lcaClose`
remains unexamined.

The two scalars this leaf needs -- `wordSize` and `blocksPerSuper` of
`builtRelativeSplitBPCloseRankData` -- are **not** yet mirrored size-only.
`packedRankWordSize` exists in `SourceFactorization.lean` with
`rankWordSize_eq_packed`, so the first is available; the second is not, and no
claim is made about it here. The chunk width and the bit length are the BP code
width and length, both already mirrored.

This required importing `RMQ.Core.SuccinctFinalStoreParam` into
`ReadProgram.lean`. There is no cycle: the store-parameter module does not import
the packed cell-probe modules.

Pinned by `packedRankCloseReadSignature` and
`packedRankCloseReadIsTheCloseRankLeaf`.

## DD-20260804-011: the close/LCA leaf is where the shape genuinely enters

Status: Worker finding recorded 2026-08-04 on branch
`codex/eg-cp-final-falsification-gate-r1`. Locates the residual `FG-07` work
after the select side and the close rank side were made record-free.

Date: 2026-08-04

Context:

Three of the whole-query program's four instructions now reach the store through
record-free definitions or not at all. The fourth, `lcaClose`, is materially
different, and the difference is visible in the type rather than inferred.

`concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore` takes
`CartesianShape` as its **first explicit argument** and passes it straight to
`SuccinctClose.ConcreteCompactBPCloseLCADirectory.lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore`.
The other leaves took a *derived record* -- a select data record, a rank data
record -- and the inlining technique of `DD-20260804-009` removed those records
because the helpers consulted them only for scalars. Here there is no record to
remove: the shape is an argument of the navigator itself.

Decision:

Record the boundary precisely rather than leave it as a guess, and discharge
everything on the near side of it.

- `packedLcaCloseLeafSignature` pins the leaf's type, shape argument included.
  This is deliberately a *negative* record: it names the one surface a controller
  cannot call as it stands.
- `packedLcaCloseRankSeed_eq` discharges the rank seed the leaf supplies to the
  navigator: it is `packedRankCloseRead` at the close rank segment base, by
  `rfl`.

The navigator's other arguments are three fixed segment constants, the store and
the two close endpoints, none of which carry shape content. So the residual is
exactly the navigator's own use of `shape`.

Rationale:

Naming the residue in the type system is worth more than another prose estimate
of remaining work. It also guards against a false completion: any later claim
that `FG-07` is closed must either eliminate this argument or exhibit a
replacement navigator, and `packedLcaCloseLeafSignaturePin` will still be there
stating that the current one takes a shape.

Consequences and evidence:

- Pinned by `packedLcaCloseLeafSignaturePin` and
  `packedLcaCloseRankSeedIsRecordFree`.
- The remaining `FG-07` work on the close side is **deeper** than it was on the
  select side. There, the record was a wrapper over scalars. Here, the navigator
  is the compact close/LCA interior route, and whether its shape use factors
  through `(n, longCount)` plus store replies is an open question this branch has
  not investigated.
- `FG-07` remains Open. Nothing here builds a controller.

### Addendum to `DD-20260804-011` (2026-08-04): the navigator's dispatch is size-only

`lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore` uses its `shape`
argument in exactly two places: the block size that decides same-block versus
cross-block, and the hand-off to the two sub-navigators.

The first is now settled. `canonicalBPRelativeSummaryBlockSizeRaw shape` is
`2 * canonicalBPRelativeSummaryBase shape`, and `packedSummaryBlockSizeRaw n =
2 * packedSummaryBase n = 2 * (n.log2 + 1)` mirrors it, with
`packedSummaryBlockSizeRaw_eq` proved by `rfl`.

So the navigator's top-level branch is decided by `n` and the two close endpoints
alone -- exactly the inputs `FG-07` permits. What remains of the shape's use in
the close/LCA route is the recursive hand-off to
`bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegmentWithStore` and
`bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore`,
neither of which has been examined.

Pinned by `packedCloseDispatchIsSizeOnly` and
`packedSummaryBlockSizeRawSignature`.

`FG-07` remains Open.

### Second addendum to `DD-20260804-011` (2026-08-04): the same-block seed is shape-free

`bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegmentWithStore` binds a
local-BP seed and hands it to the seeded reader. The seed comes from
`ConcreteCompactBPCloseLCADirectory.localBPSeedFromRankCloseTraceResult`, whose
only use of the shape is `localBPWindowBase shape blockSize close` -- and that in
turn uses the shape only through `machineWordBits shape.bpCode.length`, the
BP-code word width already mirrored by `packedBpCodeWordWidth`.

So `packedLocalBPWindowBase n blockSize close` mirrors the base, with
`packedLocalBPWindowBase_eq`, and `packedLocalBPSeed n rankCloseTrace blockSize
close` is the seed with no shape argument, with `packedLocalBPSeed_eq`. The
rank-close reader is supplied by the caller, and `packedRankCloseRead` is already
record-free, so nothing shape-derived reaches it.

Remaining in the same-block branch:
`bpChunkedSameBlockCloseSeededTraceResultAtSegmentWithStore`, which still takes
the shape. Remaining in the cross-block branch:
`bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore`,
untouched.

Pinned by `packedLocalBPSeedIsShapeFree` and
`packedLocalBPWindowBaseSignature`.

`FG-07` remains Open.

### Third addendum to `DD-20260804-011` (2026-08-04): the same-block branch is down to its window reader

`bpChunkedSameBlockCloseSeededTraceResultAtSegmentWithStore` uses its shape in
exactly three places: the fringe chunk width `bpFringeChunkBits
shape.bpCode.length`, the local-BP window base `localBPWindowBase shape blockSize
leftClose`, and the window reader
`localBPWindowBitsTraceResultWithStore shape store blockSize leftClose`.

The first two are already mirrored size-only, so
`packedSameBlockCloseSeededRead` takes the window trace as a supplied argument --
the same pattern the rank seed used -- and `packedSameBlockCloseSeededRead_eq`
discharges the rest.

The same-block branch of the close/LCA route is therefore reduced to one
remaining shape-taking function: the window reader, which is
`WordRAM.TraceResult.map flattenPayloadWords (localBPBlockWordsTraceResultWithStore
shape store blockSize close)`. That reader has not been examined.

The cross-block branch
(`bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore`)
remains untouched.

Pinned by `packedSameBlockCloseSeededReadIsShapeFree`.

`FG-07` remains Open.

### Fourth addendum to `DD-20260804-011` (2026-08-04): the close rank leaf is fully size-only

`builtRelativeSplitBPCloseRankWordSize shape = machineWordBits shape.bpCode.length`
and `builtRelativeSplitBPCloseRankBlocksPerSuper shape` is defined as that same
word size. Both are therefore `packedBpCodeWordWidth n`, discharged by
`packedCloseRankWordSize_eq` and `packedCloseRankBlocksPerSuper_eq`.

With the bit length already `2 * n`, `packedRankCloseRead_size_only` states the
close-side rank leaf entirely in terms of `n`, the supplied store, the segment
base and the position:

```
concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore shape store
    rankSegmentBase pos =
  packedRankCloseRead store rankSegmentBase (packedFringeChunkBits shape.size)
    (2 * shape.size) (packedBpCodeWordWidth shape.size)
    (packedBpCodeWordWidth shape.size) pos
```

That closes the `blocksPerSuper` gap this branch had recorded as outstanding. A
controller holding only `n` can now issue the `rankCloseIfSome` leaf outright,
with no supplied scalars left over.

Pinned by `packedRankCloseReadIsSizeOnly`.

## DD-20260804-012: the same-block close branch is shape-free

Status: Worker result recorded 2026-08-04 on branch
`codex/eg-cp-final-falsification-gate-r1`. Completes one of the two close/LCA
branches. Feeds `EG-CP` row `FG-07`.

Date: 2026-08-04

Context:

`DD-20260804-011` and its addenda reduced the same-block branch step by step: the
navigator's dispatch is `2 * (n.log2 + 1)`; the local-BP seed is shape-free given
the caller's rank reader; the seeded reader is shape-free given its window trace.
One function remained: the window reader.

Decision and result:

`localBPBlockWordsTraceResultWithStore` is four consecutive BP-code word reads
against the supplied store, starting at
`blockStartOf blockSize (blockOfClose blockSize close) / wordSize`, and its only
shape use is that `wordSize = machineWordBits shape.bpCode.length`, the BP-code
word width already mirrored. `packedLocalBPBlockWordsRead` and
`packedLocalBPWindowBitsRead` remove it, with
`packedLocalBPBlockWordsRead_eq` and `packedLocalBPWindowBitsRead_eq`.

Composing seed, window reader and seeded reader gives
`packedSameBlockCloseDecodedRead`, with `packedSameBlockCloseDecodedRead_eq`:

```
bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegmentWithStore
    shape rankCloseTrace fringeSegment store blockSize leftClose rightClose =
  packedSameBlockCloseDecodedRead store rankCloseTrace fringeSegment
    shape.size blockSize leftClose rightClose
```

The rank-close reader stays a supplied argument, as it must -- it is the caller's
choice -- and `packedRankCloseRead_size_only` shows the caller can build it from
`n` with nothing shape-derived left over.

Rationale:

The composition proof needed `simp only` rather than `rw` for the two inner
rewrites, because the seeded reader occurs under the `bind` continuation's binder.
That is a proof-engineering detail, not a weakening: the statement is still an
equation between the real branch and the shape-free one, at every shape.

Consequences and evidence:

- Pinned by `packedSameBlockCloseBranchIsShapeFree`,
  `packedLocalBPWindowBitsReadIsShapeFree`,
  `packedSameBlockCloseDecodedReadSignature`.
- Of the close/LCA route, the same-block branch is now closed. The cross-block
  branch
  (`bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore`)
  is the only part still unexamined.
- `FG-07` remains Open: no top-level controller definition exists.

### Addendum to `DD-20260804-012` (2026-08-04): the endpoint-fringe readers needed no new mirrors

`bpChunkedLeftFringeCandidateSeededTraceResultAtSegmentWithStore` and its right
twin use exactly three shape-derived things -- the fringe chunk width, the
local-BP window base, and the window reader -- and all three were already
discharged. `packedLeftFringeCandidateRead` and `packedRightFringeCandidateRead`
remove the shape with no new scalar mirrors, by `packedLeftFringeCandidateRead_eq`
and `packedRightFringeCandidateRead_eq`.

Both proofs needed `simp only` rather than `rw`, since the window base occurs
under the `bind` continuation's binder.

Pinned by `packedLeftFringeCandidateReadIsShapeFree` and
`packedRightFringeCandidateReadIsShapeFree`.

Of the cross-block branch, the remaining shape-taking callee is the interior
range-min navigator. The two endpoint readers and the seed are done, and the
dispatch scalar was already mirrored.

## DD-20260804-013: T4 is not a shortcut to FG-07, and why

Status: Worker decision recorded 2026-08-04 on branch
`codex/eg-cp-final-falsification-gate-r1`. Records a pre-existing in-tree theorem
found while mapping the close/LCA tower, and the reason it is deliberately not
used to close `FG-07`.

Date: 2026-08-04

Context:

`RMQ/Core/SuccinctFinal/RAM/GeometryClosure.lean:1326` already contains

```
T4_wholeQuery_trace_size_only {a b : CartesianShape} (h : a.size = b.size)
    (store : WordRAM.ReadStore) (l r : Nat) :
  concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore a store l r =
  concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore b store l r
```

The **entire** supplied-store whole-query execution -- value, cost and ordered
trace -- is determined by `(size, store, left, right)`. This branch did not know
that theorem existed when it began the factorization campaign.

The tempting shortcut is immediate: define the controller as
`packedRun n store l r := wholeQueryWithStore (someCanonicalShapeOfSize n) store l r`
and use `T4` to transport it to every shape of that size.

Decision:

**Do not take it.** That definition is exactly registry mutation
`M04-CANONICAL-SHAPE-BY-N` -- "synthesize a canonical shape from `n` inside a
wrapper" -- which the frozen matrix lists as an expected REJECT with failing
surface "structural / same-object". The frozen contract anticipated this shortcut
and forbids it.

The bottom-up factorization (`DD-20260804-009` through `DD-20260804-012`) remains
the route: build record-free and shape-free definitions and prove each equal to
the real leaf by `rfl` or by rewriting with size-only mirrors.

Rationale:

`T4` is a congruence. `DD-20260802-001` already recorded why a congruence is not
executability evidence: it says the result is *determined* by the size, not that
a controller can *compute* it. A controller built on `T4` would still have to
produce a shape to hand the existing evaluator, and producing one from `n` is the
forbidden mutation. The distinction is not pedantic -- it is the difference
between a definition whose type contains no `CartesianShape` and one that
manufactures a shape internally.

Consequences and evidence:

- `T4` is nonetheless valuable as **independent confirmation that no
  architecture obstruction exists** on the executed path: an entire-trace
  size-only congruence cannot hold if some executed read genuinely needed shape
  content beyond the size. It is recorded here as such, not as `FG-07` evidence.
- No consumer in `RMQ/Validation/EGCPFinalFalsification.lean` cites `T4`, by
  design. If a later candidate closes `FG-07` by way of `T4`, that is the
  `M04` mutation and should be rejected.

## DD-20260804-014: the interior layout is size-only

Status: Worker result recorded 2026-08-04 on the same branch. First half of the
interior factorization. Feeds `EG-CP` row `FG-07`.

Date: 2026-08-04

Context:

The interior range-min navigator, the last shape-taking callee in the cross-block
close branch, splits into two independent halves: its **control flow**, driven by
`RelativeRmm.canonicalLayout shape`, and its **component offsets**, which are word
counts of the eight directory tables.

Decision and result:

`RelativeRmm.Layout` has exactly four fields, and all four are summary scalars
this development already mirrors:

| Field | Mirror |
| --- | --- |
| `blockSize` | `packedSummaryBlockSizeRaw n = 2 * (n.log2 + 1)` |
| `blocksPerSuper` | `packedSummaryBase n = n.log2 + 1` |
| `blockCount` | `packedSummaryBlockCountRaw n` |
| `relativeWidth` | `packedSummaryRelativeWidthRaw n` |

so `packedInteriorLayout n` mirrors the record and `packedInteriorLayout_eq` is
`rfl`. Every derived quantity the navigator branches on -- `macroSize`,
`macroSampleCount`, `offsetWidth`, `levelCount`, `globalLevelCount`,
`superSampleCount` -- is a `Layout` method, so all of them follow.

Consequences and evidence:

- Pinned by `packedInteriorLayoutIsSizeOnly` and
  `packedInteriorLayoutSignature`.
- The interior's remaining half is `canonicalRelativeRmmInteriorComponentOffsets`
  (`InteriorDirectory.lean:1614`): eight cumulative word counts plus a dead
  address. Each is `(table.machineStore hword).store.words.size`, and
  `machineStore_words_size_closed` (`GeometryClosure.lean:549`) already gives the
  closed form `entries.length * (chunkPayloadWords wordSize (List.replicate width
  false)).length`. The entry-count lemmas exist; what is missing is the
  assembly.
- `Layout.superWidth` takes a shape argument but returns
  `machineWordBits shape.bpCode.length`, already mirrored -- it is a scalar, not
  a residue.
- `FG-07` remains Open.

### Addendum to `DD-20260804-014` (2026-08-04): converting the interior congruences into mirrors

`GeometryClosure.lean` already proves each interior table's machine-word count is
*determined* by the size: `baselineWords_congr` and its seven siblings, joined by
`componentStoreWords_congr` and `offsets_congr`. Those are congruences, and
`DD-20260802-001` records why a congruence is not executability evidence.

Their proofs are, however, exactly the recipe a mirror needs:
`machineStore_words_size_closed` followed by the table's entry-count lemma, then
`layout_congr` / `bpLen_congr` to move to the other shape. Replacing that last
step with `packedInteriorLayout_eq` and `CartesianShape.bpCode_length` lands on a
`Nat`-only expression instead.

`packedInteriorTableWords entryCount width wordSize` is the closed form, and
`packedBaselineWords` with `packedBaselineWords_eq` is the first of the eight
converted this way. Seven table counts and the cumulative offsets record remain.

This required importing `RMQ.Core.SuccinctFinal.RAM.GeometryClosure` into
`ReadProgram.lean`. No cycle: `GeometryClosure` is a leaf reached only from
`RMQ.lean`, and nothing in it imports the packed cell-probe modules.

## DD-20260804-015: the interior's addresses are size-only, so both its halves are

Status: Worker result recorded 2026-08-04 on branch
`codex/eg-cp-final-falsification-gate-r1`. Completes the interior factorization
begun in `DD-20260804-014`. Feeds `EG-CP` row `FG-07`.

Date: 2026-08-04

Context:

The interior navigator's shape dependence splits into control flow, settled by
`packedInteriorLayout_eq`, and component addresses -- nine offsets, being eight
prefix-summed table word counts plus a dead address.

`GeometryClosure.lean` already proved all nine are *determined* by the size
(`offsets_congr`, `componentStoreWords_congr`, and eight per-table congruences).
Those are congruences.

Decision and result:

Convert each into a mirror by the recipe of the addendum to `DD-20260804-014`:
`machineStore_words_size_closed`, then the table's entry-count lemma, then
`packedInteriorLayout_eq` and `CartesianShape.bpCode_length` in place of
`layout_congr` and `bpLen_congr`.

Eight mirrors landed -- `packedBaselineWords`, `packedMinRelWords`,
`packedMaxRelWords`, `packedArgOffsetWords`, `packedLocalTableWords`,
`packedGlobalTableWords`, `packedLocalLevelWords`, `packedGlobalLevelWords` --
each with an `_eq` theorem. `packedInteriorComponentWords` sums them for the dead
address, and `packedInteriorOffsets` assembles the nine-field record with
`packedInteriorOffsets_eq`.

The widths were read off the table constructions rather than guessed: the three
block tables use `layout.relativeWidth`, the local sparse table
`layout.offsetWidth`, the global sparse table `layout.blockAddressWidth`, and the
two level tables `bpSparseLevelWidth (bpSparseLevelDomain ·)` at `macroSize` and
`macroSampleCount` respectively.

Consequences and evidence:

- Pinned by `packedInteriorOffsetsAreSizeOnly`,
  `packedInteriorComponentWordsAreSizeOnly`, `packedInteriorOffsetsSignature`.
- **Both halves of the interior are now size-only.** Combined with
  `DD-20260804-012` (same-block branch), the addendum making the endpoint-fringe
  readers shape-free, and the mirrored dispatch scalar, every structural unknown
  in the close/LCA tower is discharged.
- What remains on the close side is assembly, not discovery: the interior read
  computations and the cross-block join must be written record-free and proved
  equal, using mirrors that now all exist.
- `FG-07` remains Open: no top-level controller definition exists.

### Addendum to `DD-20260804-015` (2026-08-04): the interior read primitive

`canonicalRelativeRmmMachineReadNatComputation shape table base i` is one call to
`machineReadComputationAt` at the BP-code word width and the offsets' dead
address. Both shape uses are now mirrored, so `packedInteriorReadNat` removes the
shape and `packedInteriorReadNat_eq` proves the equality.

The table argument stays and is harmless: `machineReadComputationAt` binds it as
`_table` and branches only on `entries.length`.
`packedInteriorReadNat_geometry_only` records that by consuming the existing
`GeometryClosure.machineReadComputationAt_geometry_only` -- two tables agreeing on
entry count and width give the same computation, whatever their entries.

This is the primitive the ten interior `FlatStoreComputation` definitions are
built on, so each of those is now a mechanical assembly over mirrors that exist.

## DD-20260804-016: the interior read is five naturals, with no table

Status: Worker result recorded 2026-08-04 on branch
`codex/eg-cp-final-falsification-gate-r1`. Unlocks the ten interior
computations. Feeds `EG-CP` row `FG-07`.

Date: 2026-08-04

Context:

`packedInteriorReadNat` removed the shape from the interior read but kept the
table argument, on the grounds that
`GeometryClosure.machineReadComputationAt_geometry_only` shows the read cannot see
its contents. That is true and sufficient for the read itself, but it does not
help one level up: the ten interior `FlatStoreComputation` definitions obtain
their tables *from the shape*, so a table argument keeps the shape alive in every
one of them.

Decision and result:

Remove the table. `machineReadComputationAt` binds it as `_table`, and its body
mentions only `entries.length` and `width`. Writing those two as ordinary
arguments gives

```
packedInteriorReadNatOf (n entryCount width base i : Nat) :
  FlatStoreComputation (Option Nat)
```

with `packedInteriorReadNatOf_eq` proving that for **every** shape and **every**
fixed-width table, the canonical interior read is this function at that table's
entry count and width.

Rationale:

The alternative was to keep the table and supply a dummy of matching geometry.
That would have worked -- `FixedWidthNatTable.ofEntries` on `List.replicate count
0` is constructible -- but it leaves a fabricated object in the executed
definition for no reason other than to satisfy a type. Removing the argument is
strictly cleaner and removes the question of whether the dummy is doing anything.

Note what this is *not*: it is not the `M04-CANONICAL-SHAPE-BY-N` pattern.
Nothing shape-derived is synthesized here; two projections of an existing
argument are promoted to arguments, and the equation is proved at every table
rather than at a manufactured one.

Consequences and evidence:

- Pinned by `packedInteriorReadIsFiveNaturals` and
  `packedInteriorReadNatOfSignature`.
- The ten interior computations can now be written over `(n, entryCount, width,
  ...)`. Their entry counts and widths are exactly the ones already used by the
  eight word-count mirrors of `DD-20260804-015`, so no new geometry is needed.
- `FG-07` remains Open.

### Addendum to `DD-20260804-016` (2026-08-04): the first two interior computations

With the read at five naturals and the layout and offsets mirrored, each interior
computation is the same expression with mirrors substituted. Two are landed and
they establish both shapes the remaining eight take.

`packedSummaryComputation` is the read-bearing shape: four reads of the summary
table's columns. Its proof is `unfold`, then one `simp only` carrying
`packedInteriorReadNatOf_eq`, the four entry-count lemmas,
`RelativeRmm.Layout.superWidth`, `packedInteriorLayout_eq`,
`packedInteriorOffsets_eq` and `CartesianShape.bpCode_length`, then `rfl`. The
entry counts and widths that appear are exactly those the word-count mirrors of
`DD-20260804-015` already use, so nothing new is introduced.

`packedMinCandidateComputation` is the composing shape: no reads of its own, one
call to a computation already mirrored plus two layout fields. Its proof is two
rewrites.

The remaining eight are one or the other of these.

## DD-20260804-017: the interior computation tower is shape-free

Status: Worker result recorded 2026-08-04 on branch
`codex/eg-cp-final-falsification-gate-r1`. Completes the interior, and with it
every computation in the close/LCA tower. Feeds `EG-CP` row `FG-07`.

Date: 2026-08-04

Context:

`DD-20260804-016` reduced the interior read to five naturals and landed the first
two of the ten interior computations, establishing two templates: a *read-bearing*
one whose proof is `unfold`, one `simp only` over the read equation plus the
relevant entry-count lemmas and the layout/offsets mirrors, then `rfl`; and a
*composing* one whose proof is a couple of rewrites over already-mirrored
computations.

Decision and result:

The remaining eight followed both templates without deviation:

| Computation | Template | Entry count and width |
| --- | --- | --- |
| local span candidate | read-bearing | `macroSampleCount * (levelCount * macroSize)` at `offsetWidth` |
| global span candidate | read-bearing | `globalLevelCount * macroSampleCount` at `blockAddressWidth` |
| local two-span candidate | read-bearing | `bpSparseLevelDomain macroSize` at its level width |
| global two-span candidate | read-bearing | `bpSparseLevelDomain macroSampleCount` at its level width |
| adjacent macro | composing | -- |
| left-middle macro | composing | -- |
| cross macro | composing | -- |
| interior range-min | composing (four-way branch) | -- |

Every entry count and width is one the word-count mirrors of `DD-20260804-015`
already use, so the tower introduced no new geometry.

`packedInteriorRangeMinComputation` is the top: a four-way branch on `count = 0`,
`count <= macroSize - localStart`, and whether the middle-macro and right counts
vanish. Every branch condition is a layout field or arithmetic on the two block
arguments, so the dispatcher itself needs nothing but `n`.

Consequences and evidence:

- Pinned by `packedInteriorRangeMinComputationIsSizeOnly` and
  `packedInteriorRangeMinComputationSignature`.
- **Every computation in the close/LCA tower now has a shape-free mirror.** The
  select side was closed by `DD-20260804-010`, the same-block branch by
  `DD-20260804-012`, the endpoint-fringe readers by its addendum, and the
  interior here.
- What remains on the close side is the store-parameterized wrapper
  (`concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore`),
  the cross-block join, and the `lcaClose` dispatcher -- all pass-throughs over
  mirrors that now exist.
- `FG-07` remains Open: no top-level controller definition exists.

## DD-20260804-018: the whole close/LCA route is shape-free

Status: Worker result recorded 2026-08-04 on branch
`codex/eg-cp-final-falsification-gate-r1`. Discharges the residue `DD-20260804-011`
located. Feeds `EG-CP` row `FG-07`.

Date: 2026-08-04

Context:

`DD-20260804-011` recorded, in the type system, that `lcaClose` was the one
whole-query instruction whose leaf took a `CartesianShape` directly rather than a
derived record, and that the residue was the navigator's own use of the shape.
Its addenda then discharged the dispatch scalar, the seed, the seeded reader and
the window reader; `DD-20260804-012` closed the same-block branch;
`DD-20260804-015` and `-017` closed the interior.

Decision and result:

Three pass-throughs finish the route.

`packedInteriorRangeMinRead` runs the now-shape-free interior computation against
the supplied store's flat view, with `packedInteriorRangeMinRead_eq`.

`packedCrossBlockCloseRead` composes the dispatch block size, the local-BP seed,
both endpoint-fringe readers and the interior read, with
`packedCrossBlockCloseRead_eq`.

`packedLcaCloseRead` is the dispatcher: a block comparison at a size-only block
size, choosing between the two shape-free branches, with `packedLcaCloseRead_eq`.

Consequences and evidence:

- Pinned by `packedLcaCloseRouteIsShapeFree`,
  `packedCrossBlockCloseBranchIsShapeFree`, `packedLcaCloseReadSignature`.
- **All four whole-query instruction leaves are now shape-free**: `selectClose`
  via `packedSelectCloseRead` (`DD-20260804-010`), `rankCloseIfSome` via
  `packedRankCloseRead` and its size-only form, `lcaClose` via
  `packedLcaCloseRead`, and `outputPredIfSome` which touches no store at all.
- The negative record `packedLcaCloseLeafSignature` deliberately remains: it
  still states that the *existing* leaf takes a shape. That is the point -- the
  new definitions are equal to it, they do not replace it, and a reader can see
  both.
- `FG-07` remains Open. Every leaf being shape-free is not a controller: there is
  still no single fixed definition sequencing the header probe, the readiness
  guard and the instruction stream, and no `receipt`.

## DD-20260804-019: the three store-touching instruction leaves are shape-free

Status: Worker result recorded 2026-08-04 on branch
`codex/eg-cp-final-falsification-gate-r1`. First step of the `FG-07` controller
proper.

Date: 2026-08-04

Context:

`WholeQueryInstr` has four constructors. Three touch the store --
`selectClose`, `rankCloseIfSome`, `lcaClose` -- through wrappers that fix the
global segment constants; `outputPredIfSome` touches none. With the select route
and the close/LCA route both mirrored, the wrappers are the last per-instruction
layer.

Decision and result:

`packedSelectCloseLeaf`, `packedRankCloseLeaf` and `packedLcaCloseLeaf` take the
supplied store, the input size and the instruction's own arguments, and nothing
else. Their `_eq` theorems prove each equals the corresponding
`concreteBPNative...WithStore` wrapper at every shape.

`packedLcaCloseLeaf` passes `packedRankCloseLeaf store n` as the rank reader,
which is where the close route's supplied-reader argument is finally discharged:
the caller is now the controller layer, and it builds the reader from `n`.

Seven field bridges were needed. The scalar mirrors are stated about the
standalone geometry functions, while `bpChunkedSelectTraceResultWithStore`
reaches them through record fields
(`selectData.longFlagBits.length`, `selectData.sparseDirectory.rankData.wordSize`
and five more). The record fields are definitionally those functions, so each
bridge is the mirror itself or a `rfl`.

Consequences and evidence:

- The `lcaClose` proof needed `congr 1; funext pos` to descend under the
  rank-reader function argument. That is the only place a function argument had
  to be matched pointwise rather than rewritten.
- `FG-07` remains Open: the leaves are shape-free but nothing sequences them. The
  instruction evaluator, the program evaluator and the whole-query result are the
  remaining layers.

## DD-20260804-020: the packed controller exists

Status: Worker result recorded 2026-08-04 on branch
`codex/eg-cp-final-falsification-gate-r1`. Builds the definition `EG-CP` row
`FG-07` asks for. The row is **not** thereby closed; see the consequences.

Date: 2026-08-04

Context:

Thirty-seven commits of factorization made every leaf of the whole-query program
shape-free. Three layers remained, each a direct substitution once the leaves
were done.

Decision and result:

```
packedInstrStep     (store : WordRAM.ReadStore) (n left right : Nat)
                    (instr : WholeQueryInstr) (state : WholeQueryState) :
                    WordRAM.TraceResult WholeQueryState

packedProgramRun    (store : WordRAM.ReadStore) (n left right : Nat) :
                    WholeQueryProgram -> WholeQueryState ->
                      WordRAM.TraceResult WholeQueryState

packedWholeQueryRun (store : WordRAM.ReadStore) (n left right : Nat) :
                    WordRAM.TraceResult (Option Nat)
```

with `packedWholeQueryRun_eq`:

```
concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore shape store
    left right =
  packedWholeQueryRun store shape.size left right
```

at every shape, every supplied store and every endpoint pair. The equation is
between the `TraceResult`s themselves, so value, modeled cost and ordered trace
all agree.

`packedWholeQueryRun`'s declared type is a supplied store and three naturals.
There is no `CartesianShape`, no `WholeQueryProgram` argument, no `List Int`, no
proof callback and no expected answer. The program it runs is the fixed
`concreteBPNativeSuccinctRMQWholeQueryProgram`, named inside the definition
rather than accepted from a caller.

Rationale:

The program-evaluator step needed `congr 1; funext state'` to descend under the
`bind` continuation, and the instruction step needed a `cases` on each register
guard. Neither is a weakening: the statements are equations at every instruction,
program, state, store and shape.

Consequences and evidence:

- Pinned by `packedWholeQueryRunSignature` -- written independently of the
  definition, so restoring a `shape` parameter, adding a program argument or
  threading a proof callback breaks the ascription -- and by
  `packedControllerIsTheWholeQueryRun` and `packedInstrStepIsShapeFree`.
- **`FG-07` is not closed by this.** The row also requires that the controller
  consume the packed memory's header reply and the `n`-only readiness guard, and
  that its `receipt` be the object the capstone's other conjuncts talk about.
  What exists here is a controller over an abstract `WordRAM.ReadStore`; wiring
  it to `packedMemory` through the physical probe plan is `FG-08`, and that is
  the next obligation.
- The registry mutations `M03-SHAPE-PARAMETER` and `M04-CANONICAL-SHAPE-BY-N`
  now have a concrete target to be run against, which they did not before.

## DD-20260804-021: two word shapes, one slice formula

Status: Worker result recorded 2026-08-04 on branch
`codex/eg-cp-final-falsification-gate-r1`. Fifteen of the twenty-nine flat-payload
sources now have a size-only word geometry. `FG-08` remains open.

Date: 2026-08-04

Context:

The flat payload read store answers a logical read `(segment, index)` with
`(sourceWords shape source)[index]?`, one entry of an `Array (List Bool)`. To
answer the same read by probing `packedMemory`, a controller must know from `n`
and the decoded long count alone how many words that array has and where word
`index` sits. Neither quantity was available: `DD-20260804-003` recorded that the
width was an explicit argument for twenty-eight of the twenty-nine sources.

Decision:

Express both word representations by one function,

```
packedWordSlice (payload : List Bool) (count width i : Nat) : Option (List Bool) :=
  if i < count then some ((payload.drop (i * width)).take width) else none
```

and prove one theorem per source of the form
`(sourceWords shape source)[i]? = packedWordSlice (sourcePayload shape source) c w i`
with `c` and `w` size-only.

Rationale, and why the count is not the naive one:

* **Fixed-width tables.** `packedFixedWidthTable_getElem?` is proved from the
  structure's own fields, with **no** positivity hypothesis on the width. The
  count comes from `read_exact` -- `words[i]?.map bitsToNatLE = entries[i]?`
  forces the two arrays to have the same length -- rather than from the payload
  length, which would need `0 < width`. That matters: the close summary's relative
  width is genuinely `0` when the summary is inactive, and a zero-width table
  still has `entries.length` empty words that `flattenPayloadWords` cannot see.
* **Chunked bit sources.** `List.take` truncates, so the short final chunk needs
  no separate arm; it is the slice that runs out of payload.
* **Sentinel padding.** The three rank-directory bit stores are built by
  `ofChunksWithSentinel`, which appends `payload.length + 1` empty words. Those
  are absorbed by the same formula with a larger count: past the last chunk the
  stride has run off the end, so the slice is empty for exactly the reason the
  sentinel is. `packedChunkCount_mul_le` is the arithmetic that says so.

Consequences and evidence:

- Proved for fifteen sources: the eight dense select columns, the four chunked
  bit sources (`bpCode` bare, `finalRankBPCodeAlias` and the two flag-bit stores
  with sentinels), and the three retired finite-small slots.
- `bpCode` and `finalRankBPCodeAlias` are the same bits at the same stride with
  *different* word arrays -- the alias carries the sentinels. That is why the
  source inventory keeps them apart, and the two theorems differ exactly in the
  count.
- Fourteen sources remain: the four rank-sample columns, the two relative tables,
  the four close summary columns and the two close interior tables. Until all
  twenty-nine are proved there is no packed-backed store, so `FG-08`'s whole-run
  clause is untouched.

## DD-20260804-022: one source's word count is not size-only, and what follows

Status: Worker result recorded 2026-08-04 on branch
`codex/eg-cp-final-falsification-gate-r1`. All twenty-nine flat-payload sources
now have a proved word geometry. Twenty-eight are equations; one is an
implication, for a reason that is a fact about the architecture rather than about
the proof.

Date: 2026-08-04

The finding:

`sparseExceptionRelativeEntries_length` gives the sparse relative table's entry
count as

```
rankPrefix true (sparseExceptionFlagBits bits target) (localSlotCount bits target)
  * localStride bits.length
```

The leading factor is the number of local slots whose span forced a sparse
exception. It is a property of the bit pattern, not of its length. Two shapes of
the same size can differ in it; `longCount` does not record it; no other stored
scalar does either.

`K1` puts exactly one count in the header and the architecture spends it on
`longCount`. So of the twenty-nine sources, **exactly one** has a word count the
controller cannot compute from `n` and the header.

Decision:

Do **not** read this as a `K1` obstruction, and do not add a header field. Use the
size-only bound instead: the exception count is at most the local slot count, so

```
packedSparseRelativeCapacity n = packedLocalSlots n * localStride (2 * n)
```

is a capacity the controller can compute, and
`packedSparseRelativeEntries_le_capacity` proves it is an upper bound
(`Succinct.rankPrefix_le_limit`).

The per-source theorem is then one-directional:

```
packedSelectSparseRelativeWords_of_some :
  (sourceWords shape .selectSparseRelative)[i]? = some word ->
    packedWordSlice (sourcePayload shape .selectSparseRelative)
      (packedSparseRelativeCapacity shape.size) (packedLocalWidth shape.size) i =
      some word
```

Rationale:

Every **successful** logical read still lowers to exactly the right slice, which
is what `FG-08` asks of "every logical read actually used by the query". The gap
is confined to indices between the real count and the capacity, where the packed
read answers and the store would have failed. Discharging that gap is exactly
`FG-09`'s totality clause -- *every attempted probe of an actual run is successful
and in range* -- which the gate already requires. So the residual is scope already
owed, not new scope, and certainly not a second header cell.

Consequences and evidence:

- The other twenty-eight sources are equations, so the asymmetry is visible in
  the theorem shapes rather than hidden in a uniform statement. A later change
  that made a second source content-dependent would have to weaken its equation,
  which is a diff a reviewer can see.
- **This is the honest reason `FG-08` cannot be closed by store equality.** The
  packed-backed store cannot equal `concreteBPNativeSuccinctRMQFlatPayloadReadStore`;
  it can only extend it. The whole-run theorem therefore has to go through
  agreement on the executed footprint, and that is the next obligation.
- If `FG-09`'s totality clause turns out to be false -- if some reachable query
  really does attempt an out-of-range sparse relative read -- then this becomes a
  genuine `K1` obstruction and should be reported as one. That is the first
  concrete obstruction candidate this campaign has produced, and it is recorded
  here so it is not lost.

## DD-20260804-023: the geometry as three functions, and the columns nobody sized

Status: Worker result recorded 2026-08-04 on branch
`codex/eg-cp-final-falsification-gate-r1`.

Date: 2026-08-04

Decision:

Collect the per-source word geometry into three total functions --
`packedSourceStride n source`, `packedSourceWordCount n longCount source` and
`packedSourceBitLength n longCount source` -- and state the twenty-nine
`SourceWords` theorems as one implication over the closed source inductive,
`packedSourceWords_of_some`. Adding a constructor now breaks elaboration until its
geometry is supplied on all three functions and its word theorem exists.

Two arms of the count are deliberately not the number of payload-carrying words:

* the three chunked rank directories append `payload.length + 1` empty sentinel
  words, counted here because the store returns them; and
* `.selectSparseRelative` carries the size-only capacity of `DD-20260804-022`.

`packedSourceBitLength_eq` proves the bit length agrees with the shape-indexed
payload for the twenty-eight sources other than `.selectSparseRelative`, whose
length is the one quantity that is not size-only. The exclusion is a hypothesis on
the theorem, not a missing case.

The columns nobody had sized:

`SourceFactorization` proves a length for every column an *offset* depends on. A
column nothing is addressed after never needed one, so nine were missing: the
fourth column of each dense entry table (`firstOffset`, super and local), the
second polarity of each of the two final rank sample levels, the four long-flag
and sparse-flag rank sample tables, and the interior global table. They are proved
here, each by the same route as its already-mirrored sibling.

Consequences:

- Sizing every source is what a *store* needs and what placing a source did not.
  The asymmetry is why these nine were absent rather than an oversight in the
  earlier factorization.
- The physical read -- turning a word slice into a probe of `packedMemory` -- is
  the next step and is not in this commit.

## DD-20260804-024: every stored word fits one packed cell

Status: Worker result recorded 2026-08-04 on branch
`codex/eg-cp-final-falsification-gate-r1`. `INV-WORD-WIDTH` is proved at the
packed layer for all twenty-nine sources; the row remains open because its
consumer, the physical read, does not exist yet.

Date: 2026-08-04

Context:

`packedProbePlan_decode` is stated for reads of at most one cell, because the plan
issues at most two cells and a wider read would need more. So the per-read
lowering cannot even be stated until every source's stride is known to fit
`packedCellWidth n`. That is `INV-WORD-WIDTH`, and nothing in the pre-existing
development supplied it: the flat payload store has no word-length bound at all,
and the select-side `_le_machine` fields bound widths by
`machineWordBits bits.length`, not by the packed cell width.

Result:

`packedSourceStride_le_cellWidth n source hcounted`, by case analysis over the
closed source inductive. Twenty-six arms reduce to
`machineWordBits X <= machineWordBits (packedPayloadLength n + 2)` with `X` a
count the payload obviously dominates. Three did not:

1. **The final rank block sample width** is `machineWordBits (w * w)` for
   `w = machineWordBits (2 * n)`, and `w * w` is *not* bounded by `2 * n`: at
   `n = 2` it is `9` against `4`. The slack comes from the rank directory the
   payload already carries -- `packedRankAux_le_payload` plus
   `packedRankWordSize_two_le_aux` give `2 * n + 2 * w <= packedPayloadLength n` --
   and the residual is the pure arithmetic fact `k * k <= 2 ^ k + 3`, proved by
   finite check below `5` and induction above it (`packedSq_le_two_pow_add_three`).
2. **The close summary relative width** is not a `machineWordBits` at all. When
   the summary is inactive it is `0`; when active, the *last conjunct of the
   activity predicate itself* is `relativeWidthRaw <= machineWordBits (2 * n)`.
   The guard supplies the bound rather than a separate estimate.
3. **The close interior offset width** is `machineWordBits (base * base)`, and
   `base * base` is the macro size. `PackedInteriorReady n` says exactly that the
   macro size is at most the summary block count, which is at most `n`. **The
   readiness guard `FG-07` requires the controller to consult is what makes this
   source's width admissible.** That is a load-bearing use of the guard, not a
   formality.

Rationale for the hypothesis shape:

The theorem takes `PackedSourceCounted n source` -- the same `n`-only predicate the
controller evaluates -- rather than a bespoke side condition per source. For
twenty-seven sources it is unused; for the two interior sources it is what makes
the statement true; for the three retired finite-small slots it is `False`, so
those arms are discharged by the guard being unsatisfiable, which is the honest
reading of a slot that carries nothing.

Consequences:

- `packedSpine` is introduced to have a shape of every size, so that a size-only
  bound proved through a shape (`packedRankAuxLength_le_accessOverhead`, which
  needs `accessComponents_add_padding`) is available at every `n`.
- If a future change made a stored word wider than a cell, this theorem breaks
  rather than the probe plan silently issuing too few cells.

## DD-20260804-025: the physical read

Status: Worker result recorded 2026-08-04 on branch
`codex/eg-cp-final-falsification-gate-r1`. `FG-08`'s per-read clause is proved for
every source; the row stays open because the whole-run clause is not.

Date: 2026-08-04

Result:

```
packedSourceRead (n longCount : Nat) (memory : List (List Bool))
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource) (index : Nat) :
    Option (List Bool)
```

executable, shape-free, issuing `packedSourceReadPlan` and decoding it, with

```
packedSourceRead_of_some :
  PackedSourceCounted shape.size source ->
    (sourceWords shape source)[index]? = some word ->
      packedSourceRead shape.size (longCount shape) (packedMemory shape) source
        index = some word
```

Two branches, and both are load-bearing:

* **Zero width.** A read whose exact width is zero -- the sentinel words the
  chunked rank directories append -- issues *no probe at all*: the plan is `[]`,
  the fetch is `some []`, and the decode is `[]`. The stored word is empty for
  exactly the reason the width is zero (either the stride is zero or the payload
  has run out), so the two agree without any containment obligation. This is the
  branch that would have been wrong under a plan that always issued a cell.
* **Positive width.** The read is contained in the source payload, hence in the
  canonical payload, hence in the allocated cells. Containment is *derived* from
  the successful read rather than assumed: `List.length` of the flat-slice
  equation gives `min srcLen (payloadLength - offset) = srcLen`, and a positive
  width forces `srcLen > 0`, which is what rules out the degenerate reading in
  which the offset runs past the payload and truncated subtraction hides it.

Rationale for `packedSourceReadWidth_eq_window`:

The read width is computed from the size-only bit length, but the decode has to
produce the window the source payload actually has left. Those agree for the
twenty-eight sources whose bit length is size-only, and for
`.selectSparseRelative` both sides collapse to the full stride, because a
successful read there is at an index below the actual entry count while the
packed side uses the capacity. That is the whole content of the one-directional
asymmetry of `DD-20260804-022`, isolated in one lemma.

Consequences and evidence:

- Pinned by `packedSourceReadSignature`, `packedSourceReadPlanSignature`,
  `packedEveryStoredWordFitsOneCell`, `packedLogicalWordReadIsAtMostTwoProbes`,
  `packedEverySuccessfulReadLowers`, the three geometry signatures, and
  `packedSparseRelativeIsBoundedNotDetermined`.
- **What is still missing for `FG-08`.** There is no theorem relating the ordered
  logical trace of a run to the ordered physical trace with multiplicity, because
  the run's trace has not been mapped through this read yet. That is the next
  obligation, and it is now a mapping problem rather than a geometry problem.
- `conv_rhs` is unavailable in this toolchain; the slice chain is done by a single
  `rw` list instead. Recorded so a later reader does not assume the tactic exists.

## DD-20260804-026: the packed memory as a read store, and what still separates it from the run

Status: Worker result recorded 2026-08-04 on branch
`codex/eg-cp-final-falsification-gate-r1`.

Date: 2026-08-04

Result:

```
packedBackedStore (n longCount : Nat) (memory : List (List Bool)) :
  WordRAM.ReadStore
```

routes a logical `(segment, index)` through the already shape-free
segment-to-source map and answers it with `packedSourceRead`. Two theorems:

* `packedBackedStore_of_some` -- every **successful** read of
  `concreteBPNativeSuccinctRMQFlatPayloadReadStore` is answered identically;
* `packedBackedStore_eq_readWord` -- away from `.selectSparseRelative`, and under
  the readiness guard on segments 24 and 25, the two stores are **equal** at that
  address, failures included.

The `none` direction needed a second aggregate, `packedSourceWords_eq`, which is
the twenty-eight-source equation `packedSourceWords_of_some` could not be. Past
the word count the store has nothing and neither does the packed read.

Why the guard appears here:

The close interior tables exist as objects even when the interior is not ready,
so the *logical* store answers segments 24 and 25 regardless -- but their bits are
then not in the counted payload, and the packed memory cannot answer. This is not
a defect: it is exactly the dispatch `FG-07` requires the controller to perform,
and the pre-existing
`concreteBPNativeSuccinctRMQFlatPayloadReadStore_successful_read_segment_counted`
already carries the same two hypotheses. Discharging them at the run level is a
property of the whole-query program's readiness dispatch, not of the store.

What now separates this from `FG-08`'s whole-run clause, stated exactly:

`concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_store_parametric_of_ordered_read_footprint`
turns store agreement on the executed ordered footprint into equality of the
complete execution -- result, modeled cost, ordered trace and failed reads. So two
obligations remain, and they are the last two:

1. **the readiness dispatch** -- the run never emits a segment-24 or segment-25
   read unless `concreteBPRelativeRmmInteriorReady shape`; and
2. **no out-of-range sparse relative read** -- the run never emits a
   `.selectSparseRelative` read at an index at or beyond the actual exception
   count. This is `FG-09`'s totality clause for one source, and by
   `DD-20260804-022` it is also the discriminator: if it fails, `K1` is
   insufficient and the campaign has an obstruction rather than a candidate.

Both are properties of the *program*, not of the geometry. The geometry work is
finished.

## DD-20260804-027: the executed store stops agreeing with the flat payload at segment 20

Status: Worker result recorded 2026-08-04 on branch
`codex/eg-cp-final-falsification-gate-r1`. This is the most consequential result
on the branch and it is negative, so it is recorded with its evidence and with an
explicit statement of what it is *not*.

Date: 2026-08-04

Context:

`PhysicalRead.lean` lowers every logical read of
`concreteBPNativeSuccinctRMQFlatPayloadReadStore` to a probe of `packedMemory`.
The next step was to feed that store to the whole-query evaluator through
`..._store_parametric_of_ordered_read_footprint`. Before doing so I checked which
store the evaluator actually runs against.

Finding:

`concreteBPNativeSuccinctRMQCanonicalReviewerReadStore_eq_global` (pre-existing)
says the executed store is the *canonical reviewer* store. `ExecutedUniverse.lean`
computes what that store reads, every theorem by `rfl`:

| segment | executed store | flat payload store |
| --- | --- | --- |
| `0` .. `19` | the flat payload's own sources | the same |
| `20` | `canonicalRelativeRmmInteriorComponentStore shape` | close summary baseline |
| `21` | `bpFringeChunkTable ...` | close summary minRel |
| `22` | `bpChunkSelectTable ... false` | close summary maxRel |
| `23` and up | `none` | argOffset, close interior, retired slots |

So the two agree exactly on segments `0` .. `19` and diverge from `20` up.

**The divergence is not a renumbering.** The matrix's `FG-08` clause (c) said the
executed store "numbers segments 21 and 22 differently". It does not: the three
objects the executed store reads at `20`, `21` and `22` are not sources of the
flat payload at all.

* The flat close half is `concreteCompactBPCloseLCADirectory`, whose
  `payload_eq_interior` field makes it the **compact** interior directory --
  summary, local, global, under a readiness guard
  (`concreteBPRelativeRmmInteriorDirectoryPayloadLength`).
* The executed close half is `canonicalRelativeRmmInteriorDirectory` -- summary,
  local, global, **local level, global level**
  (`canonicalRelativeRmmInteriorDirectoryPayloadLength`) -- followed by the two
  chunk tables, neither of which appears anywhere in the flat payload layout.
* `concreteBPNativeSuccinctRMQCanonicalReviewerPayloadLayout`'s own docstring
  says the flat close payload "remains available only through the compatibility
  layout above".

Corroborating evaluation (not a proof, and recorded as such): at the size-three
left spine the flat payload is 21466 bits of which the close component is **0**,
while the canonical close component is 100 bits and the two chunk tables are 40
and 8. `decide` cannot check these in the kernel -- the definitions are
well-founded and reduction sticks -- which is why the committed evidence is the
segment-map `rfl`s rather than the numbers.

Consequences:

- `packedMemory`, which serializes the `FG-01` payload object, can back executed
  segments `0` .. `19` and nothing beyond. Every per-read theorem in
  `PhysicalRead.lean` remains sound; as a *whole-machine* claim the lowering is
  partial, and `INV-GLOBAL-PHYSICAL-MACHINE` names precisely this deficit -- now
  as three named objects rather than an unquantified gap.
- **This is not a `K1` obstruction and is not reported as one.** The header cell
  is not involved and no frozen `K1` quantifier is contradicted. Per the
  commissioning instruction, an obstruction is reported only when a checked
  theorem matches the frozen `K1` quantifiers; this does not.
- What it *is*: a tension between two frozen rows. `FG-01` names one payload
  object; `FG-08` requires the execution to probe the memory built from it. Under
  the current definitions those cannot both be closed unless the close route is
  re-based, and re-basing the packed memory on the canonical reviewer payload
  would contradict `FG-01` as frozen -- which the commissioning prompt forbids.
- The next proof target is therefore no longer "map the run's trace". It is:
  decide whether a bridge exists between the compact and canonical interior
  directories. If one does, the lowering extends and the campaign continues. If a
  checked theorem shows none can, that is a result about the close route, and the
  owner should be told before any further construction work is spent.

## DD-20260804-028: addresses fit the modeled word, not just the host array

Status: Worker result recorded 2026-08-04 on branch
`codex/eg-cp-final-falsification-gate-r1`.

Date: 2026-08-04

`INV-ADDRESS-WIDTH` explicitly rejects a host-array bound:
`packedProbePlan_lt_cellCount` says an issued address indexes an *allocated cell*,
which is not the same as being representable in one modeled machine word. The two
are related by the cell width's own definition -- `packedCellWidth n` is
`machineWordBits (packedPayloadLength n + 2)` -- and the gap closes with one
application of `Nat.log2_lt`:

```
packedCellCount_lt_two_pow_cellWidth :
  packedCellCount n < 2 ^ packedCellWidth n
packedProbeAddress_lt_two_pow_cellWidth :
  bit + width <= packedAllocatedBits n -> addr ∈ packedProbePlan n bit width ->
    addr < 2 ^ packedCellWidth n
```

The `+ 2` in the width is what makes this work at every size: the count is
`1 + ceil(P / w)`, at most `1 + P`, and `P + 2 < 2 ^ machineWordBits (P + 2)`.
Without the `+ 2` the singleton cases would need separate treatment.

Pinned by `packedIssuedAddressesAreMachineRepresentable` and
`packedCellCountIsMachineRepresentable`.

Chosen now because it is independent of `DD-20260804-027`: the executed-universe
gap blocks the whole-run clauses of `FG-08`, `FG-10` and `FG-11`, but not the
width and address invariants, which are properties of the packed representation
alone.

## DD-20260804-029: the replay harness, and why it will not report PASS

Status: Worker result recorded 2026-08-04 on branch
`codex/eg-cp-final-falsification-gate-r1`. `FG-12` stays Open by construction.

Date: 2026-08-04

`scripts/eg_cp_final_falsification_replay.ps1` encodes the sixteen-entry frozen
registry literally and in the commissioned order, and replays a case by applying
one textual mutation to one tracked file, rebuilding the named failing surface,
and requiring the commissioned verdict.

Design points that are obligations rather than taste:

* **Registry integrity is checked before anything runs**: sixteen entries,
  ascending orders `1` .. `16`, unique IDs, every verdict mapped, and exactly two
  `ACCEPT` against fourteen `REJECT`. Omission, duplication or reordering fails
  the run before a single build.
* **Selector nonvacuity**: an explicitly supplied selector that is unknown, empty
  or whitespace exits non-zero; only *omitting* the parameter means full mode.
  `[AllowEmptyString()]` is on the parameter so the empty case reaches the
  harness's own check rather than dying in parameter binding.
* **Byte-exact restoration.** The first working version restored with
  `Set-Content -Encoding utf8`, which on PowerShell 5.1 adds a BOM and rewrites
  CRLF. The restoration hash caught it. The harness now captures
  `[System.IO.File]::ReadAllBytes` and restores with `WriteAllBytes`, so the file
  returned is the file found, not an equivalent one. This is precisely the check
  `INV-MUTATION-REPRODUCIBILITY` asks for, and it failed the first time it was
  run -- which is the argument for having it.
* **Bounded stages.** `Start-Process -PassThru` reported a non-zero exit code for
  a build that succeeds when run directly, so the harness drives
  `System.Diagnostics.Process` itself, drains both pipes asynchronously to avoid
  a full-pipe deadlock turning a semantic failure into a spurious timeout, and
  derives the per-case deadline from a measured clean build (four times the
  measurement, floor 300 s) rather than from a guess.
* **Owned-tree termination** with a descendant self-test that spawns a detached
  grandchild sleeper and requires it dead after the root is killed;
  `taskkill /T /F` on Windows, negated-pid `kill` on Linux.

**Why it will not report PASS on this candidate, and why that is correct.**

Seven of the sixteen commissioned cases have no failing surface yet: `A02`,
`M02`, `M04`, `M06`, `M07`, `M12`, `M13` all name a run, a trace, a controller
over `packedMemory`, or a capstone, and none of those exist. The harness reports
them as `TARGET-ABSENT`, never silently skips them, and exits non-zero in full
mode when any is present. A harness that printed PASS with seven of sixteen cases
unrun would be forging exactly the evidence `FG-12` exists to demand.

The nine runnable cases are `A01`, `M01`, `M03`, `M05`, `M08`, `M09`, `M10`,
`M11`, `M14`. Their mutation targets are chosen in the latest module that carries
the commissioned content, so a rebuild is proportionate to the claim.

## DD-20260804-030: the two named thresholds, located rather than asserted

Status: Worker result recorded 2026-08-04 on branch
`codex/eg-cp-final-falsification-gate-r1`. `FG-14` stays Open.

Date: 2026-08-04

The commissioning prompt recorded two thresholds -- a `5488/5489` long crossover
and a `[1024, 1330]` interior-readiness window -- and `FG-14` asks for
kernel-checked instances with the thresholds *named explicitly from the geometry*.
They appeared nowhere in the source, so they had to be found.

**`decide` cannot check either of them.** `Nat.log2` is defined by well-founded
recursion, so kernel reduction sticks; `#eval` goes through the compiler and
proves nothing. `packedLog2_eq` is the way around: it pins a logarithm from a pair
of power-of-two bounds via `Nat.le_log2` and `Nat.log2_lt`, and the kernel only
has to evaluate `2 ^ k` on literals.

**The long crossover is at `5489`, and it is not a tuning constant.**
`superLongSpan (2n) = superStride * wordBits * ell` is `10976` at `n = 5487`,
`5488` and `5489`, because all three have `wordBits = 14` and `ell = 4`. Meanwhile
`2n` walks past it: `10974`, `10976`, `10978`. So `min (2n) (superLongSpan (2n))`
is `2n` up to and including `5488` and switches sides at `5489`, which is exactly
where the select layer's relative width stops tracking the input size. A sweep of
`[2, 20000]` found this as the *only* transition.

**The readiness window is `[1024, 1330]`, and it moves for one reason.**
`packedSummaryBase n = Nat.log2 n + 1` jumps `10 -> 11` at `n = 1024`. The macro
size is that base squared, so it jumps `100 -> 121`; the raw block count is
`n / base`, so it *falls* `102 -> 93` because the divisor grew. Readiness returns
when the block count catches up, which is exactly `n = 1331` (`1331 / 11 = 121`).
Both endpoints are checked with their neighbours.

What is deliberately not claimed: the `PackedSummaryActive` half of readiness is
not kernel-checked. It does not move across `[1023, 1331]` by evaluation, and the
clause that is checked is the one that does. Saying so is cheaper than a proof
that would add nothing.

## DD-20260804-031: values, not just widths, and the verification ledger filled in

Status: Worker result recorded 2026-08-04 on branch
`codex/eg-cp-final-falsification-gate-r1`.

Date: 2026-08-04

`INV-WORD-WIDTH` is about *values*: stored and returned words must fit one
declared modeled machine word. `DD-20260804-024` proved the stride bound, which is
what the probe plan needs; this closes the clause the row actually states.

```
packedStoredCellValue_lt_two_pow :
  cell ∈ packedMemory shape ->
    SuccinctSpace.bitsToNatLE cell < 2 ^ packedCellWidth shape.size
packedDecodedWordValue_lt_two_pow :
  width <= packedCellWidth n ->
    SuccinctSpace.bitsToNatLE (packedDecodeSpan n bit width cells) <
      2 ^ packedCellWidth n
```

The first goes through `packedMemory_cell_length`, so it is a statement about the
counted memory's own cells rather than about arbitrary bit lists. The second holds
because a decoded span is a `List.take` of the fetched cells and so is never wider
than the request, which is never wider than a cell.

Ledger:

The verification ledger of matrix section 4 had nine rows reading "to be recorded"
or "Pending". They are now filled in from runs at `c472146`: `CHK-02` (validation
root builds), `CHK-03` (the single full replay, `RAN, INCOMPLETE`, exit 7),
`CHK-05` (`headline_axiom_check` clean after `lake build RMQPaper`), `CHK-06`
(hygiene scan clean), `CHK-07` (no native decision shortcut), `CHK-09`
(design-decision check against base `1490c97`, 21 files), `CHK-10` (claim drift,
1498 hits, 0 strict failures), `CHK-12` (the replay derives its deadline from a
measured clean build, so it cannot race Lean startup) and `CHK-13` (focused
selectors run before the full replay was paid for).

`CHK-05` needed `lake build RMQPaper` first; the script imports `RMQPaper` and
`lake build RMQ` does not produce that olean. Recorded so the next runner does not
read the missing-module error as a failure of the check.

The project-skill preflight was re-run at this tip: governance
`f0c7232a8a52b8d61ead5e96d72a8a849bc094b5`, checkout `c472146`, expected /
checkout / working / runtime skill sets all `rmq-audit-prompt, rmq-coordinator,
rmq-proof-sprint`, `required=rmq-proof-sprint`, `required_mode=role-skills`,
**PASS**.

## DD-20260804-032: the universe gap is a disagreement, not a difference of notation

Status: Worker result recorded 2026-08-04 on branch
`codex/eg-cp-final-falsification-gate-r1`.

Date: 2026-08-04

`DD-20260804-027` established by `rfl` that the executed store and the flat
payload store are *defined* by different expressions from segment 20 up. That is
weaker than it sounds: two definitions can agree pointwise, so a bridge was still
formally possible and the honest next step was to look for one or rule it out.

Ruled out:

```
packedStoresDisagree_atSegmentTwentyThree :
  0 < packedSummaryBlockCount shape.size ->
    (flatPayloadReadStore shape).readWord? 23 0 ≠
      (globalReadStore shape).readWord? 23 0

packedStoresNotEqual :
  0 < packedSummaryBlockCount shape.size ->
    flatPayloadReadStore shape ≠ globalReadStore shape
```

At segment 23 the executed store answers `none` -- it is silent from 23 on --
while the flat payload store answers the close summary's argOffset column, which
has a word whenever the summary carries any block at all. So the two stores give
different answers, and no bridge between the universes exists.

The hypothesis `0 < packedSummaryBlockCount shape.size` is the ordinary case, not
a contrivance: it is exactly the condition under which the close summary carries
data. It is satisfied by evaluation across `[1023, 1331]`, where
`PackedSummaryActive` holds. A kernel-checked witness would need the full activity
predicate, whose conjuncts route through `sampledDirectoryOverhead` and
`bpSuperblockSpan`; that is the same `Nat.log2` machinery `Boundaries.lean` uses
and is feasible, but it is not done, so the theorem is stated conditionally rather
than instantiated.

What this does and does not settle:

- It **settles** that `packedMemory`, built over the `FG-01` payload object,
  cannot be made to back the executed run by finding a bridge. `FG-08`'s whole-run
  clause is unreachable from the current pair of frozen rows.
- It **does not** prove a `K1` obstruction, and is not reported as one. `K1` is
  one header cell containing `longCount`; the header cell is not involved in this
  theorem, and no frozen `K1` quantifier is contradicted. The commissioning
  instruction is explicit that an obstruction is reported only when a checked
  theorem matches the frozen `K1` quantifiers, and this does not.
- What it is: a checked incompatibility between `FG-01`'s named payload object and
  `FG-08`'s requirement that the execution probe the memory built from it. Which
  of the two moves is an owner decision, because either resolution edits the
  meaning of a frozen row and the commissioning prompt forbids weakening one.

## DD-20260804-033: the payload I pinned is the public one; the executed one is a third object

Status: Worker result recorded 2026-08-04 on branch
`codex/eg-cp-final-falsification-gate-r1`.

Date: 2026-08-04

Before accepting `DD-20260804-032`'s conclusion I checked an assumption I had not
tested. `FG-01` names the *function* `concreteBPNativeSuccinctRMQPayload`, which
takes an access-family parameter; I had instantiated it at
`builtGenericSparseExceptionSelectBPCloseAccessFamily`. If the accepted semantics
consumed a different instantiation, the whole blocking argument would have been my
mis-instantiation rather than a conflict between frozen rows.

It does consume a different *family*: the public payload is

```
concreteBPCloseNavigationPayload shape =
  concreteBPNativeSuccinctRMQPayload
    builtRelativeSplitSparseExceptionFalseSelectBPCloseAccessFamily.toWeakFamily shape
```

but the two families produce the same payload **value** -- checked at the
size-three left spine, where both are `21466` bits and `decide` reports them
equal. So the object `FG-01` pins is the object the public claim consumes, and the
instantiation was not the error.

(The equality is not stated as a theorem here: the two families are different
terms, `rfl` times out, and proving the directories coincide is a side quest that
does not change any conclusion. The witness check is recorded as a witness check.)

The sharper statement this yields:

There are **three** payload objects, not two.

1. `concreteBPNativeSuccinctRMQPayload <either family> shape` -- the object `FG-01`
   pins, the object the public `Costed` semantics is payload-backed by, and the
   object `packedMemory` serializes. At the size-three spine: `21466` bits, of
   which the close component is `0`, the rest being padding to the size-only
   budgets.
2. `concreteBPNativeSuccinctRMQCanonicalReviewerPayload shape` -- the object the
   word-RAM execution reads, through `concreteBPNativeSuccinctRMQGlobalReadStore`.
   At the same shape: `305` bits, containing the canonical interior directory
   (`100` bits) and the two chunk tables (`40` and `8`).
3. The two are neither equal nor related by a bridge: `packedStoresNotEqual`.

So the split is not between two frozen matrix rows in the abstract. It is between
the object the *space claim* is about and the object the *word-RAM execution*
reads, and the packed cell-probe construction inherits it because `FG-01` sends it
to the first.

What I am **not** claiming: that the project's headline claim conflates the two.
Both layers carry their own space bound -- the `Costed` layer through
`concreteBPNativeSuccinctRMQOverhead` and the reviewer layer through
`concreteBPNativeSuccinctRMQCanonicalReviewerPayload_length_le`. Whether any
public statement composes a bound proved for one with an execution performed on
the other is a question about the headline claim, not about this gate, and it is
outside what I have checked. It is flagged because a reviewer of `M11` at project
scale would want to ask it.

## DD-20260804-034: the header value is load-bearing for addresses

Status: Worker result recorded 2026-08-04 on branch
`codex/eg-cp-final-falsification-gate-r1`. `FG-11` and `INV-VALUE-DEPENDENCY` stay
Open; one clause of each now has real evidence.

Date: 2026-08-04

Both rows insist on the same distinction: an inequality must be at a probe
*address* or the *returned value*, not at an enclosing trace record, because a
record inequality can be satisfied by its log alone. `DD-20260804-032` blocks
anything that quantifies over a run -- but the address side does not.

```
packedLongBlockBits_pos : 0 < packedLongBlockBits n
packedSourceFlatOffset_injective_longCount :
  lc1 ≠ lc2 -> packedSourceFlatOffset n lc1 .selectLocalBaseOccurrence ≠
                 packedSourceFlatOffset n lc2 .selectLocalBaseOccurrence
packedStridedBitAddress_injective_longCount :
  lc1 ≠ lc2 -> packedStridedBitAddress n lc1 .selectLocalBaseOccurrence index stride ≠
                 packedStridedBitAddress n lc2 .selectLocalBaseOccurrence index stride
```

Every source placed after the long relative table is displaced by
`longCount * packedLongBlockBits n`, and that block is never empty because it is
`superStride (2n) * wordBits (2n)` and both factors are positive. So the map from
decoded header count to address is injective: the header reply determines where
later reads go. That is the content `M14-LONG-COUNT-IGNORED` exists to attack, now
carried by a theorem rather than only by a mutation that rejects.

Two limits, stated rather than glossed:

1. The inequality is at the **bit** address. Lifting it to the issued *cell*
   index needs `packedCellWidth n <= packedLongBlockBits n`, so that a one-unit
   change in the count cannot leave the probe inside the same cell. That is not
   proved, and unlike the `k * k <= 2 ^ k + 3` bound it is not obviously true at
   small sizes -- `packedPayloadLength` is dominated by padding there, so
   `packedCellWidth` is larger than the input size would suggest. It is recorded
   as the next smallest target for this row rather than assumed.
2. The row's other half -- the *returned value* -- still needs a run.

## DD-20260804-035: the cell-width bound is false, and was never needed

Status: Worker result recorded 2026-08-04 on branch
`codex/eg-cp-final-falsification-gate-r1`. Corrects the residual recorded in
`DD-20260804-034`.

Date: 2026-08-04

`DD-20260804-034` lifted the header-count value-dependency witness only as far as
the *bit* address, and recorded the next target as
`packedCellWidth n <= packedLongBlockBits n`, described there as "not obviously
true at small sizes".

It is not merely not obvious. **It is false**: at `n = 0` it reads `10 <= 1` and at
`n = 1` it reads `14 <= 8`. It holds from `n = 2` onward, but by evaluation only --
a general proof would need an explicit upper bound on `packedPayloadLength`, which
the development supplies asymptotically through `LittleOLinear` and not in closed
form. Recording a false lemma as the next target would have sent the next session
after something unprovable.

It was also unnecessary. `FG-11` asks for *a* pinned pair of counts whose probe
address differs, not for every pair, so the difference can be **chosen** rather
than estimated:

```
packedStridedBitAddress_step_longCount :
  packedStridedBitAddress n (lc + packedCellWidth n) src index stride =
    packedStridedBitAddress n lc src index stride +
      packedCellWidth n * packedLongBlockBits n

packedProbeCell_moves_with_longCount :
  ... (lc + packedCellWidth n) ... / packedCellWidth n ≠ ... lc ... / packedCellWidth n
```

Separating the two counts by one cell width moves the address by a whole number of
cells, so the issued cell index differs with no inequality between the two
quantities required. `Nat.add_mul_div_left` does the rest.

The lesson worth keeping: the estimate-versus-choose distinction. An existential
obligation does not need a uniform bound, and reaching for one turned a provable
statement into a false lemma.

## DD-20260804-036: I lowered the wrong execution layer

Status: Worker result recorded 2026-08-04 on branch
`codex/eg-cp-final-falsification-gate-r1`. **Corrects the conclusion of
`DD-20260804-027`, `DD-20260804-032` and `DD-20260804-033`.**

Date: 2026-08-04

What I concluded before:

That `FG-08`'s whole-run clause is unreachable, because `packedMemory` serializes
the object `FG-01` names while the executed store reads the canonical reviewer
objects from segment 20 up, and the two stores are provably unequal
(`packedStoresNotEqual`). I reported that as a tension between two frozen rows
requiring an owner decision.

Why that was wrong:

The theorem is correct. The conclusion drawn from it was not, because it assumed
the *word-RAM* `WholeQueryProgram` layer is the execution `FG-08` is about. It is
not the only one, and it is not the one the rest of the gate is about.

`concreteBPNativeSuccinctRMQ_two_n_plus_o_constant_query_profile` -- the project's
public bundle -- composes, for a single access family:

* `overhead_littleO`;
* `(concreteBPNativeSuccinctRMQPayload accessFamily shape).length = 2 * n + overhead n`;
* `(concreteBPNativeSuccinctRMQQueryCosted accessFamily shape left right).cost <= constant`;
* `(concreteBPNativeSuccinctRMQQueryCosted accessFamily shape left (left + len)).erase
   = some (scanWindow shape.representative left len)`.

Space, cost and correctness, all about **one** object: the `Costed` query over
`concreteBPNativeSuccinctRMQPayload accessFamily shape`. That payload is what
`FG-01` pins, what `FG-06` bounds, and what `packedMemory` serializes. Its reads
are `PayloadWordStore.readWordCosted store i`, which is `store.words[i]?` -- the
same shape as the `sourceWords` reads `packedSourceRead_of_some` already lowers.

The word-RAM global-store layer is a *second*, additional development with its own
payload (`canonicalReviewerPayload`) and its own space bound. Nothing in the frozen
rows requires the packed lowering to target it. I targeted it because `FG-07`'s
controller language and the store-parametric machinery pointed that way, and then
read the resulting mismatch as a defect in the frozen matrix rather than as a
consequence of my own choice.

Consequences:

- **The campaign is not blocked on an owner decision.** No frozen row needs
  editing and no close route needs re-basing. `DD-20260804-032`'s theorem stands
  as a true statement about two stores; its *interpretation* as a `FG-01`/`FG-08`
  incompatibility does not.
- **The geometry work is unaffected and still correct.** The twenty-nine source
  word geometries, the width bounds, the probe plan, the address bounds and the
  per-read lowering are all about the flat payload's own sources, which is the
  right object. What must change is which execution they are composed with.
- **The controller must be rebuilt against the `Costed` layer.**
  `packedWholeQueryRun` refactors the word-RAM program and is the wrong target;
  it stays in the tree as a proved theorem about that layer, but it is not the
  `FG-07` controller.
- The next target is therefore concrete and not a decision: express the `Costed`
  query's payload-word reads in terms of the twenty-nine flat sources, then
  compose with `packedSourceRead_of_some`.

Recorded this way, rather than by quietly re-pointing the work, because the
earlier conclusion was reported to the owner as a blocking finding and a request
for a decision. That request is withdrawn.

## DD-20260804-037: retracting DD-20260804-036 -- the public payload is the reviewer payload

Status: Worker result recorded 2026-08-04 on branch
`codex/eg-cp-final-falsification-gate-r1`. **Retracts `DD-20260804-036` and
reinstates the finding of `DD-20260804-027`, `-032` and `-033`, in a sharper
form.**

Date: 2026-08-04

`DD-20260804-036` claimed I had lowered the wrong execution layer, on the grounds
that `concreteBPNativeSuccinctRMQ_two_n_plus_o_constant_query_profile` composes
space, cost and correctness for the `Costed` query over
`concreteBPNativeSuccinctRMQPayload accessFamily shape`. That theorem is real, but
it is a **family-level** profile parameterized over an access family. It is not the
top-level public claim, and I did not check the top-level claim before writing the
retraction.

The top-level claim over `List Int` is `listInt_two_n_plus_o_constant_query_profile`
and its strengthened form
`listInt_flatPayloadStore_noSynthetic_two_n_plus_o_execution_story`. Both are stated
about `buildPayload xs` and `queryCosted xs`, and:

```
def buildPayload (xs : List Int) : List Bool :=
  SuccinctFinal.concreteBPNativeSuccinctRMQCanonicalReviewerPayload (cartesianShape xs)

def queryCosted (xs : List Int) (left right : Nat) : Costed (Option Nat) :=
  (queryTraceResult xs left right).toCosted
```

So the **publicly advertised `2n + o(n)` payload is the canonical reviewer
payload** -- the 305-bit object at the size-three spine -- and the public query is
the word-RAM trace result, not the `Costed` adapter. `FlatPayloadStoreNoSynthetic
ExecutionStory`'s own first conjunct says it outright:
`canonicalReviewerPayload (cartesianShape xs) = buildPayload xs`.

Consequences, stated plainly:

- `DD-20260804-036` was wrong and is retracted. The word-RAM layer *is* the
  execution the accepted semantics is about. My original targeting was right.
- The finding of `DD-20260804-027`/`-032` stands, and is sharper than first
  stated. It is not merely that two frozen rows are in tension. It is that
  **`FG-01`'s own text points at two different objects**: it names the function
  `concreteBPNativeSuccinctRMQPayload`, and it qualifies that name with *consumed
  by the accepted RMQ semantics* -- and the accepted `List Int` semantics consumes
  `concreteBPNativeSuccinctRMQCanonicalReviewerPayload` instead.
- Under the *name* reading -- what I implemented -- `packedMemory` serializes the
  flat payload and `FG-08` is unreachable, by `packedStoresNotEqual`.
- Under the *consumed-by* reading, `packedMemory` would serialize
  `buildPayload xs`, which does contain the interior directory and both chunk
  tables, and the segment 20-22 gap would not arise. `FG-08` would be reachable.

So the owner decision is narrower and better posed than I described two commits
ago: it is not "re-base the close route", it is **which half of `FG-01`'s own
sentence governs**. Both readings are available without editing the row; they
disagree about which object the row names.

Process note, recorded because it matters more than the result: I retracted a
correct finding on the strength of a family-level theorem that I took for the
public claim, and I did it without checking `buildPayload`. One definition would
have settled it. The lesson is not "check more" in general -- it is that when a
finding is about *which object a claim is about*, the only evidence that counts is
the definition of the object the top-level claim names.

## DD-20260804-038: the frozen registry decides FG-01's ambiguity

Status: Decision taken 2026-08-04 on branch
`codex/eg-cp-final-falsification-gate-r1` under the standing decision authority
(pick the most unimpeachable, precedent-matching option). Resolves the question
`DD-20260804-037` left open.

Date: 2026-08-04

`FG-01` names two different objects: the identifier
`concreteBPNativeSuccinctRMQPayload`, and "the object consumed by the accepted RMQ
semantics", which is `concreteBPNativeSuccinctRMQCanonicalReviewerPayload` because
`buildPayload xs` is defined as exactly that. I reported this as an owner
decision. It is not: **the gate's own frozen registry decides it.**

Registry entry 13 is

```
M11-SIBLING-PAYLOAD | prove space for one payload while executing another | REJECT
```

Under the identifier reading, that is precisely what the candidate does. The
packed memory would serialize the flat payload, `FG-06` would bound *that* object,
and the execution would read the reviewer payload -- space proved for one payload,
execution performed on another. A candidate built that way fails `M11` by
construction, and `M11` is a commissioned REJECT. So the identifier reading is not
merely one of two options; it is the option the registry exists to reject.

Decision: `payloadBits` is the object the accepted semantics consumes.
`packedPayloadBits shape` re-targets to
`concreteBPNativeSuccinctRMQCanonicalReviewerPayload shape`, whose `List Int` face
is `buildPayload`.

This is not a weakening of `FG-01`. It satisfies the row's operative qualifier,
uses an existing canonical object at its existing definition site as the row's
evidence clause demands, and makes the row's own anti-vacuity challenge survivable
rather than fatal.

What transfers and what does not:

* **Transfers unchanged.** The generic word-shape lemmas, the probe plan and its
  allocation/coverage/decoding/count theorems, the address-width and word-value
  bounds, the header schema, and the eighteen live access sources -- those are the
  reviewer payload's access half, listed literally in
  `concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources`.
* **Needs redoing.** `FG-06`'s bound moves from
  `concreteBPNativeSuccinctRMQOverhead` to
  `concreteBPNativeSuccinctRMQCanonicalReviewerOverhead`, which already has
  `_littleO` and a `_length_le`, so the shape of the argument is preserved.
* **Is new work.** The close half: the canonical interior directory's five tables
  and the two chunk tables become sources, replacing the compact directory's
  three. Their word geometry is the same kind of obligation already discharged
  twenty-nine times.
* **Is discharged for free.** The segment 20/21/22 gap disappears: those are
  exactly the objects the reviewer payload contains, so
  `INV-GLOBAL-PHYSICAL-MACHINE`'s named deficit closes and `packedStoresNotEqual`
  becomes a true statement about a store the candidate no longer uses.

Recorded before the construction rather than after, so the decision is auditable
independently of whether the construction succeeds.

## DD-20260804-039: the re-target's first obligation, and the obstruction candidate it exposes

Status: Investigation target recorded 2026-08-04 on branch
`codex/eg-cp-final-falsification-gate-r1`. **Not a result.** Recorded so the next
session starts from the right question.

Date: 2026-08-04

`DD-20260804-038` re-targets `packedPayloadBits` at the canonical reviewer
payload. The first thing that must be checked about the new target is whether its
component offsets are still size-only, because `FG-02`/`FG-03`/`FG-07` all depend
on a controller computing addresses from `n` and the decoded header alone.

The reviewer layout is

```
payload = bpCode ++ accessPayload ++ closePayload ++ fringePayload ++ selectChunkPayload
closeBitOffset shape = bpCodePayload.length + accessPayload.length
```

and `accessPayload` is `concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources.flatMap
(sourcePayload shape)`, whose **last** entry is `.selectSparseRelative`.

That source's payload length is
`rankPrefix true (sparseExceptionFlagBits ...) (localSlotCount ...) * localStride * relativeWidth`
-- the sparse exception count, which `DD-20260804-022` established is **not** a
function of `(n, longCount)`. So on its face the close component's offset in the
reviewer payload is content-dependent, and a `K1` controller carrying only
`longCount` could not address the close half.

**If that is right it is a `K1` obstruction of exactly the commissioned shape**:
a checked theorem matching the frozen `K1` quantifiers, showing `K1` needs extra
metadata. It would also explain the earlier `M10-SPARSE-COUNT-DEPENDENCY` framing:
the registry anticipated precisely this dependency.

**It is not yet checked, and the one probe run does not support it.** Left and
right spines of sizes 8, 16 and 32 give equal close offsets (`598`, `1023`,
`1647`) and `longCount = 0` on both, so that probe does not discriminate -- the
sparse exception count is evidently `0` for both spine families at those sizes.
Two possibilities remain open and they have opposite consequences:

1. The sparse exception count is always `0` for Cartesian BP codes, or is itself a
   function of `(n, longCount)`. Then the close offset is size-only after all, the
   re-target proceeds, and `DD-20260804-022`'s one-directional lowering can
   probably be upgraded to an equation.
2. It is genuinely content-dependent. Then `K1` is insufficient for the reviewer
   payload, and the campaign has its obstruction.

The next smallest target is therefore precise: **exhibit two shapes of the same
size whose sparse exception counts differ, or prove the count is determined by
`(n, longCount)`.** The first needs a search over shapes with mixed structure
rather than spines -- spines are extreme and evidently produce no exceptions. The
second would be a theorem about `sparseExceptionFlagBits` on BP codes.

Recorded as an open question with both branches stated, rather than as a finding,
because the branch that says "obstruction" is exactly the one a worker under
pressure to finish would be tempted to claim early.

## DD-20260804-040: the obstruction candidate is not supported; the sparse path looks unreachable

Status: Evidence recorded 2026-08-04 on branch
`codex/eg-cp-final-falsification-gate-r1`. **Evaluation, not proof.** Selects the
branch `DD-20260804-039` left open.

Date: 2026-08-04

`DD-20260804-039` recorded two branches. The measurements are in.

The predicate is

```
localIsSparseException bits target slot =
  (! superIsLong bits target (localSuperSlot bits.length slot)) &&
    decide (wordBits bits.length < shortSuperLocalSpan bits target slot)
```

-- a slot is a sparse exception exactly when its superblock is **not** long yet
its local span still exceeds `wordBits`. Nothing in the definition forces it to
`false`, so the question was empirical.

Measured sparse exception counts, `rankPrefix true (sparseExceptionFlagBits
shape.bpCode false) (localSlotCount shape.bpCode false)`:

* **exhaustively over every shape of every size `0` .. `8`**: the set of distinct
  counts is `[0]` at each size -- not one exception among all Catalan-many shapes;
* **sizes `64`, `256`, `1024`, `4096`, across four shape families** -- left spine,
  right spine, balanced, zigzag -- : `0` in all sixteen cases.

So **branch 2 is not supported**: no witness of a positive sparse count was found,
and therefore no evidence that the close component's offset in the reviewer
payload is content-dependent. The `K1` obstruction candidate of `DD-20260804-039`
is withdrawn as unsupported. It is not refuted -- absence of a witness is not a
proof -- but it should not be pursued as if it were live.

Why this is plausible rather than a sampling accident: a BP code of a shape of
size `n` has exactly `n` target occurrences in `2 * n` bits, so gaps average `2`.
A local slot's span exceeds `wordBits (2 * n)` only in a locally sparse region,
and a region sparse enough to do that is exactly what makes its superblock
**long** -- which the first conjunct then excludes. The sparse-exception path
appears to be designed for parameter regimes this instantiation does not reach.

Consequences, and the next target:

- The `FG-01` re-target of `DD-20260804-038` proceeds. The reviewer layout's close
  offset is size-only if the sparse relative table is empty, which the evidence
  indicates.
- `DD-20260804-022`'s asymmetry -- the one source whose word count is not
  size-only -- probably dissolves rather than needing the capacity bound: if the
  count is always `0`, `packedSelectSparseRelativeWords_of_some` can be
  strengthened from an implication to an equation with count `0`, and the store
  equality of `packedBackedStore_eq_readWord` extends to all twenty-nine sources.
- The next smallest target is therefore a **theorem, not a search**:
  `sparseExceptionRelativeEntries shape.bpCode false = []` for every
  `CartesianShape`, or equivalently
  `localIsSparseException shape.bpCode false slot = false` for every slot. The
  route is the observation above: `wordBits (2n) < shortSuperLocalSpan` should
  imply `superIsLong`, making the conjunction unsatisfiable.

Recorded as evidence with its limits stated, because "we looked and found none"
and "there are none" are different claims and only the first is established.

## DD-20260804-041: why the sparse path is empty -- the mechanism, with its exact threshold

Status: Evidence and mechanism recorded 2026-08-04 on branch
`codex/eg-cp-final-falsification-gate-r1`. Explains `DD-20260804-040`'s
measurements and names the theorem that would settle them.

Date: 2026-08-04

`DD-20260804-040` measured the sparse exception count as `0` everywhere it
looked, and offered a hand-wave about density. The real mechanism is sharper and
is visible in two definitions.

```
shortSuperLocalSpan bits target slot =
  position (shortSuperLocalEndOccurrence ... - 1) + 1 - position (localBaseOccurrence ...)

localIsSparseException bits target slot =
  (! superIsLong ...) && decide (wordBits bits.length < shortSuperLocalSpan bits target slot)
```

The span is measured **between the slot's own occurrences** -- from its base
occurrence's position to its last occurrence's position, plus one. It does not
include the gap before the slot. So a slot covering a *single* occurrence has span
exactly `1`, whatever the surrounding bit pattern, and then the second conjunct is
`wordBits bits.length < 1`, which is unsatisfiable because `wordBits_pos`.

A local slot covers `localStride bits.length` occurrences, and

```
localStride m = max 1 (wordBits m / (ell m * ell m))
```

is `1` whenever `wordBits m < 2 * ell m * ell m`. Measured:

| `n` | `wordBits (2n)` | `ell (2n)` | `localStride (2n)` |
| --- | --- | --- | --- |
| `1` | `2` | `2` | `1` |
| `64` | `8` | `4` | `1` |
| `1024` | `12` | `4` | `1` |
| `65536` | `18` | `5` | `1` |
| `2^32` | `34` | `6` | `1` |

and a sweep of `m = 2 ^ k` finds the **first** `k` with `localStride > 1` at
`k = 97`. So `localStride = 1` for every input size below roughly `2 ^ 96`, and on
that whole range no sparse exception can occur at all -- not because the bit
pattern is nice, but because each local slot holds one occurrence and a one-
occurrence span cannot exceed a word.

This is why every shape of size `0` .. `8`, and four families at `64` .. `4096`,
gave count `0`: the code path is unreachable, not merely unvisited.

The theorem to prove, now with no search left in it:

```
localStride bits.length = 1 -> localIsSparseException bits target slot = false
```

which needs `shortSuperLocalSpan = 1` under a unit stride, then `wordBits_pos`.
Composing it with `localStride (2 * n) = 1` gives
`sparseExceptionRelativeEntries shape.bpCode false = []`, and with it:

- `DD-20260804-022`'s asymmetry dissolves on the whole range: the one source whose
  word count was not size-only has count `0`, so
  `packedSelectSparseRelativeWords_of_some` strengthens to an equation and
  `packedBackedStore_eq_readWord` extends to all twenty-nine sources without the
  `.selectSparseRelative` exclusion;
- `FG-09`'s totality clause loses the discriminator `DD-20260804-022` attached to
  it, because there is no out-of-range sparse read to worry about;
- the `FG-01` re-target of `DD-20260804-038` gets a size-only close offset.

Stated with its limit: above `2 ^ 96` the stride exceeds one and the path becomes
reachable in principle. Every claim above is therefore conditional on
`localStride = 1`, which should appear as a hypothesis rather than be silently
assumed -- the same discipline `DD-20260804-035` arrived at the hard way.

## DD-20260804-042: the re-target's first increment -- the identity, proved

Status: Worker result recorded 2026-08-04 on branch
`codex/eg-cp-final-falsification-gate-r1`. First step of `DD-20260804-038`.

Date: 2026-08-04

`PackedCellProbe/ReviewerPayload.lean` names the object the accepted semantics
consumes and proves `FG-01`'s identity clause against it:

```
packedReviewerPayloadBits shape := concreteBPNativeSuccinctRMQCanonicalReviewerPayload shape

packedReviewerPayloadBits_eq_canonical    : = the canonical object          (rfl)
packedReviewerPayloadBits_eq_buildPayload : = SuccinctClassic.buildPayload xs (rfl)
packedReviewerPayloadBits_length_le       : <= 2 * n + canonicalReviewerOverhead n
packedReviewerOverhead_littleO            : LittleOLinear that overhead
```

Both identities are `rfl` at the existing definition site, in both the
shape-facing and the `List Int`-facing direction. The second is the one that
matters: `buildPayload` is the advertised payload of
`listInt_two_n_plus_o_constant_query_profile` and of the strengthened execution
story, so this is an identity to the object the *public claim* is about, not to a
re-derived copy. That is exactly what `FG-01`'s evidence clause asks and what
`M11-SIBLING-PAYLOAD` exists to check.

`packedReviewerPayload_backs_executedCloseSegments` records the payoff in one
statement: the executed store's segments `20`, `21` and `22` are this payload's
close component and its two chunk tables -- the three objects the flat payload
lacked in `DD-20260804-027`. Re-targeting removes that deficit rather than
relocating it.

The space clause keeps `FG-06`'s shape exactly: a `<= 2 * n + overhead` bound with
a `LittleOLinear` residual, both pre-existing.

What is **not** done, and must not be read into this:

- `packedMemory` still serializes the old object. This module names the new
  target and proves the identity; the header, cell, probe, geometry and store
  layers have not been re-pointed at it.
- The eighteen live access sources transfer, but the close half needs seven new
  word geometries -- five interior tables and two chunk tables -- before the
  per-read lowering applies to the new payload.
- Until `packedMemory` moves, `FG-06`'s bound is still proved over the old object
  and the candidate would still fail `M11`. The re-target is begun, not finished.

## DD-20260804-043 -- the consumed payload's length is `(n, longCount)`, not `n`

`RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerLength.lean`.

The flat payload of `Header.lean` has an input-size-only length because its
layout carries explicit padding fields (`accessPadding`, `closePadding`) that
absorb every input-dependent variation. Measured at `n = 3` it is `21466` bits
against the consumed payload's `305`: the flat object is padding by a factor of
seventy.

The consumed payload has no padding fields. It is

```
bpCode ++ liveAccessPayload ++ interiorDirectory ++ fringeChunkTable ++ selectChunkTable
```

and of its eighteen live access sources `selectLongRelative` carries
`longCount`-many rows. So no input-size-only length function exists for it, and
`FG-04`'s literal `P(n)` cannot be supplied for the new target. This is the
"checked equivalence-required correction" that row's own text anticipates.

The correction is not a concession. `longCount` is precisely the one quantity a
controller cannot recompute from `n`, and precisely the one quantity `K1`'s header
carries. Under the flat payload the header was arguably decorative, because the
layout was size-only without it; under the consumed payload it is load-bearing.
The width stays input-size-only -- it is derived from the advertised space bound
`2 * n + reviewerOverhead n`, not from the exact length -- so cell zero remains
readable before `longCount` is known, and the count follows once it is decoded.

```
packedReviewerPayloadLength (n longCount : Nat) : Nat
packedReviewerPayloadBits_length_eq   : the exact length, under unit stride
packedReviewerPayloadLength_le_bound  : that length <= the advertised bound
packedReviewerCountedAccessSources_eq : drift guard, by rfl
```

Checked against evaluation at sizes `0..7`: the formula reproduces
`[75, 158, 298, 305, 613, 616, 652, 655]`, the measured lengths of the payload
itself.

### The unit-stride hypothesis is not a small-input restriction

`packedSparseExceptionEntries_nil_of_unit_stride` needs
`GenericSelect.localStride (2 * n) = 1`. That function is
`max 1 (wordBits n / (ell n * ell n))`, which first exceeds `1` when
`wordBits n >= 98`, i.e. when `n >= 2 ^ 97`. Evaluated at every size from `0` to
`100000` it is `1`. The hypothesis holds at every size any machine can represent,
so the equation is not confined to toy inputs.

## DD-20260804-044 -- correcting the basis of the re-target, and an `FG-01` defect

`DD-20260804-038` justified the re-target by reading `M11-SIBLING-PAYLOAD` as
forcing "the object the accepted semantics consumes". That reading was an
over-extension: `M11` is an anti-vacuity mutation which the existing `rfl`
identity in `Payload.lean` already defeats. The re-target stands, but on a
different and checkable basis.

The basis is a repository theorem, not a reading of row text:

```
concreteBPNativeSuccinctRMQCanonicalReviewerReadStore_eq_global
  : the reviewer read store IS the executed global read store
```

recorded here as `packedExecutedStore_is_reviewerStore`. Combined with
`packedReviewerPayloadBits_eq_buildPayload` (`rfl`), the payload measured in this
module is the object the accepted semantics executes against.

A naming trap sits directly on this question and should be recorded so the next
reader does not fall into it. `SuccinctRMQClassic.flatPayloadReadStore` is **not**
a store over `concreteBPNativeSuccinctRMQPayload`; it is an `abbrev` for
`concreteBPNativeSuccinctRMQCanonicalReviewerReadStore`. Its "flat" names a
query-independent layout, not the flat payload. It has no consumers anywhere in
the tree.

### The defect

`FG-01-RAW-PAYLOAD-IDENTITY` identifies its object twice, and the two
identifications pick out different objects:

- by name: "the existing canonical `concreteBPNativeSuccinctRMQPayload` object";
- by property: "consumed by the accepted RMQ semantics".

The named object is the flat payload. The object consumed by the accepted
semantics is `concreteBPNativeSuccinctRMQCanonicalReviewerPayload`. These are not
equal: `packedStoresNotEqual` proves the two induced stores differ, and
`packedFlatStore_*Segment` against `packedExecutedStore_*Segment` shows they
differ at executed segments `20`, `21` and `22` specifically.

Both clauses are now discharged separately, against the object each names:

```
packedPayloadBits_eq_canonical         : FG-01's named object      (rfl)
packedReviewerPayloadBits_eq_buildPayload : FG-01's described object (rfl)
```

This is **not** a `K1` architecture obstruction and the campaign does not stop for
it. `K1` -- one header cell carrying `longCount` -- is untouched, and no theorem
here says `K1` needs extra metadata, a new primitive, or another architecture
change. It is a defect in a frozen row: the row describes the codebase
incorrectly.

Amending a frozen row is an owner decision, and the standing instruction forbids
weakening one. So the row is not rewritten. The memory is being built over the
object the accepted semantics consumes, because `FG-08` requires the lowering to
cover "every logical read actually used by the query" and those reads hit
segments the flat payload does not carry; and the divergence is reported rather
than resolved by fiat. `FG-01` stays `Open` pending the owner's ruling on which
clause governs.

## DD-20260804-045 -- the width comes from the advertised bound, not the exact length

`RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerWidth.lean`.

`DD-20260804-043` established that the consumed payload has no input-size-only
length. The cell width may not depend on `longCount`, because cell zero has to be
readable before the header is decoded. So the width is derived from the advertised
size-only bound instead of from the exact length:

```
packedReviewerCellBound n = 2 * n + concreteBPNativeSuccinctRMQCanonicalReviewerOverhead n
packedReviewerCellWidth n = machineWordBits (packedReviewerCellBound n + 2)
```

`packedReviewerPayloadLength_le_bound` is what licenses this: the exact length
never exceeds the bound. The division of labour is then exactly `K1`'s -- width
from `n`, count from the header.

The module is **additive**. `packedCellWidth` and `packedMemory` are untouched, so
the existing stack keeps building while the new one grows beside it. A single
big-bang redefinition would have broken every downstream module at once with no
way to tell a real failure from a mechanical one.

`packedSourceStride_le_reviewerCellWidth` carries `INV-WORD-WIDTH`'s stride clause
across all twenty-nine arms under the same `PackedSourceCounted` guard. Twenty-eight
arms pass a quantity bounded by `2 * n`, and `2 * n <= packedReviewerCellBound n`
holds by construction.

The twenty-ninth, `finalRankBlockFalse`, has a stride that is `machineWordBits` of
a square. It needed `rankWordSize n ^ 2 <= packedReviewerCellBound n + 2`, which is
**false** if one tries to prove it from `2 * n` alone -- at `n = 2` the square is
`9` against `2 * n + 2 = 6`. It holds because `packedAccessOverhead` is literally
the first summand of the reviewer overhead, so the existing
`packedRankAuxLength_le_accessOverhead` transfers with no new arithmetic. Recorded
because the naive route looks plausible and fails at a size small enough to miss.

Sampled at `n` in `0..8, 16, 64, 256, 1024, 4096`, this width agrees with
`packedCellWidth` at every point (`10, 14, 14, 15, 17, ..., 26`) even though the
two bounds differ -- the reviewer bound is slightly *smaller* than the flat payload
length, so the agreement is a property of the logarithm, not an ordering. No
theorem claims they are equal, and none should: the coincidence is not needed.

## DD-20260804-046 -- the packed memory over the consumed payload

`RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerMemory.lean`.

Step three of the re-target: header, serialized bits, cell count, allocation and
cell array over `packedReviewerPayloadBits`.

```
packedReviewerHeaderBits          : longCount at the size-only width
packedReviewerHeaderBits_decode   : reading it back recovers longCount
packedReviewerCellCount (n longCount)
packedReviewerAllocatedBits (n longCount)
packedReviewerMemory              : the cell array
packedReviewerMemory_cell_length  : every cell exactly one full width
packedReviewerMemory_header_cell  : the header occupies cell zero exactly
```

The signature split is the point. `packedReviewerCellWidth` takes `n`;
`packedReviewerCellCount` takes `n` **and** `longCount`. So cell zero is
addressable before anything is decoded, and the count is available immediately
after. `longCount_lt_two_pow_reviewerWidth` gives the all-size count fit with no
side condition, exactly as the flat header had it.

This is where `K1` stops being decorative. Under the flat payload the cell count
was already input-size-only, so a controller could have computed it from `n` and
ignored the header entirely -- which is what made `FG-11`'s liveness clause awkward
to satisfy honestly. Over the consumed payload the count is not computable from
`n`, so the header is on the critical path of addressing.

`packedReviewerMemory_header_cell` needs no unit-stride hypothesis: it is about
cell zero, which is prefix-determined and independent of the payload's length. The
first attempt carried `hstride` and the linter flagged it as unused; the
hypothesis was dropped rather than left in place, since a spurious hypothesis on a
memory theorem would misrepresent what the memory needs.

Still additive: `packedMemory` is untouched.

## DD-20260804-047 -- round trip and cell crossing over the consumed payload

`RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerCrossing.lean`.

```
packedReviewerMemory_flatten           : the cells concatenate to the padded bits
packedReviewerMemory_flatten_take      : the serialized bits are a prefix
packedReviewerMemory_recovers_payload  : every payload bit is inside the cells
packedReviewerCellAt / _getElem? / _CellPair
packedReviewerSpan_from_two_cells      : any span <= one width spans two cells
```

`packedReviewerMemory_recovers_payload` is the clause worth naming separately.
The round trip alone says the cells reconstitute *something*; this says the thing
they reconstitute, after dropping the header cell, is the consumed payload itself.
That is what makes "the memory contains no second table beside it" checkable at
the new target rather than asserted.

`Memory.lean`'s `chunk_flatten` is `private`, so it is copied here as
`packedReviewerChunkFlatten`. It is a general list fact about chunking a string of
exactly `k * w` bits, with no payload content, so the duplication carries no risk
of the two copies meaning different things. Widening the original's visibility
would have been the alternative; copying keeps the flat module untouched, which is
the property that has kept this re-target reversible.

The unit-stride hypothesis appears exactly where the actual bit length is
involved, and nowhere else: the crossing algebra
(`packedReviewerCellAt`, `_CellPair`, `_Span_from_two_cells`) is hypothesis-free,
because it is arithmetic about `drop`/`take` at a positive width and does not care
how long the string is.

## DD-20260804-048 -- allocated space over the consumed payload

`RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerSpace.lean`.

```
packedReviewerRho                          : reviewerOverhead n + 2 * width n
packedReviewerAllocatedBits_le             : the arithmetic core
packedReviewerMemory_length_mul_width_le   : FG-06's form, on the memory object
packedReviewerCellWidth_littleO
packedReviewerRho_littleO
```

`FG-06` insists the bound be stated on allocated cells times width rather than on
the serialized length, so that padding is charged rather than dropped.
`packedReviewerMemory_length_mul_width_le` is in exactly that form.

The `longCount` dependence costs one hypothesis and no generality. The arithmetic
core carries "the payload length is within its advertised bound"; at a shape that
is discharged by `packedReviewerPayloadLength_le_bound` under unit stride. The
residual `packedReviewerRho` is a function of `n` alone, which is what the row
requires -- a `longCount`-dependent residual would not have been a space bound at
all.

`packedReviewerCellWidth_littleO` goes through the existing
`littleOLinear_machineWordBits_comp` with an eventual-linear bound of `3 * n + 2`,
obtained by instantiating `packedReviewerOverhead_littleO` at `1`. The flat
module's corresponding constant is `19909 * n + 563`, because it must dominate the
flat payload's own length; the consumed payload needs only its overhead, which is
`o(n)` outright.

This completes the space half of the re-target. The execution half -- geometries,
lowering, controller, correctness -- is untouched.

## DD-20260804-049 -- the close half is ten components, and two of them are free

`RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerCloseGeometry.lean`.

Section 8b estimated the close half at "seven new word geometries -- five interior
tables and two chunk tables". The count is wrong in both directions and the
correction matters for planning.

**Two are free.** `bpFringeChunkTable` and `bpChunkSelectTable` are
`FixedWidthNatTable`s, so `packedFixedWidthTable_getElem?` -- the generic lemma
already carrying the eighteen live access sources -- applies unchanged. Segments
`21` and `22` are one-line proofs.

**The interior is eight components, not five.** The directory's payload is five
concatenated tables, but the *component store* the executed segment `20` actually
reads is assembled from **eight** machine stores: the summary contributes four
columns separately (baseline, minRel, maxRel, argOffset), then local, global,
local-level, global-level.

### Why segment 20 is not one uniform grid

Two independent reasons, and the second was not visible from the type.

1. The component store is nested `BoundedPayloadWordStore.append`. Words are laid
   end to end at *word* granularity while payloads concatenate at *bit*
   granularity, so a component whose payload does not fill its final word leaves a
   ragged edge and the next component's first word does not start at a multiple of
   the machine width.

2. `FixedWidthNatTable.machineStore`'s words are
   `table.store.words.toList.flatMap (chunkPayloadWords wordSize)` -- each logical
   entry is chunked **separately**. So even within a single component the grid is
   uniform only when the entry width fits inside, or divides, the machine word.
   Chunking the component's payload as a whole gives different words.

The second point is the one to carry forward. The obvious approach -- treat each
interior component as `packedWordSlice` of its own payload at the machine width --
is **wrong in general**, and would produce a theorem that happens to hold at the
sizes one is likely to sample while being false in general. It is recorded here
rather than discovered later against a failing proof.

What this module establishes for segment `20` is the pair of facts the piecewise
geometry will be stated against: the eight-way word split, and that the store
flattens to exactly the directory payload. The bits are all present and in order;
only the word boundaries are non-uniform.

## DD-20260804-050 -- the exact condition making a machine store a uniform grid

`RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerMachineWords.lean`.

`DD-20260804-049` recorded that `FixedWidthNatTable.machineStore` chunks each
logical entry separately. This gives the exact condition under which its words are
nevertheless the table's own uniform grid:

```
packedChunkPayloadWords_singleton        : a payload fitting one word chunks to [it]
packedMachineStoreWords_eq_of_width_le   : 0 < width <= wordSize => same word list
packedMachineStoreWords_getElem?         : hence packedWordSlice, at the table width
```

Both bounds matter and for different reasons. `width <= wordSize` is what makes the
chunk a singleton; `0 < width` is what stops a zero-width column from chunking to
the **empty** list, which would shift every subsequent word index rather than
merely widening a word. A zero-width column is not hypothetical here -- the flat
close summary is inactive at small sizes and has width `0`, which is why
`SourceWords.lean` takes its counts from `read_exact` rather than from payload
length.

The condition is `n`-only: both widths are functions of the input size. So it
belongs beside `PackedSourceCounted` and `PackedInteriorReady` as a guard the
controller can consult, not as a fact about a particular shape. Each of the eight
interior components will discharge it separately.

Stating it as a hypothesis rather than proving the unconditional version is the
point. The unconditional statement is false, and it is false only outside the
regime one naturally samples, so a proof attempt that assumed it would most likely
have succeeded on every example tried and been wrong.

## DD-20260804-051 -- measurement kills the width hypothesis for three columns

`RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerEntryChunks.lean`.

`DD-20260804-050` proved that a machine store is the table's own uniform grid when
`0 < width <= wordSize`, and left each of the eight interior components to
discharge that condition. Measuring the widths first, before attempting the
discharge, was the right order: **three of them cannot.**

On the right spine, each interior column's entry width against
`machineWordBits (2 * n)`:

```
n      0  1  2  4   8  16  64  128  256  512  1024
W      1  2  3  4   5   6   8    9   10   11    12
super  1  2  3  4   5   6   8    9   10   11    12   -- equals W
offset 1  1  3  4   5   5   6    7    7    7     7   -- below W
addr   1  1  1  1   2   2   4    5    5    6     7   -- below W
rel    5  5  7  7   9   9   9   11   11   11    11   -- ABOVE W below ~512
```

`minRel`, `maxRel` and `argOffset` all carry `relativeWidth` entries, which exceed
one machine word at every size below roughly `512`. Their machine stores really do
split each entry, and the `width <= wordSize` route cannot reach them at any size
a test would sample.

This is the second time in two decisions that the sampled regime is where the
convenient statement fails rather than where it holds. Measuring first cost one
evaluation and saved an unprovable goal.

`packedMachineStoreWords_getElem?_general` drops the hypothesis entirely: machine
word `i` is chunk `i % c` of logical entry `i / c`, with `c` the machine words per
entry. `packedMachineStoreWords_getElem?` is the `c = 1` case, kept because five
of the eight components do satisfy it and the one-level statement is cheaper to
consume.

The supporting general lemma is worth naming: `packedFlatMapUniform_getElem?`
indexes any `flatMap` whose blocks share a length, by `i / c` and `i % c`. Nothing
about payloads enters it.

The two-level index is the honest shape of this store. Entries are chunked
individually, so the word grid is a grid of grids, and any single-level
`packedWordSlice` claim over a component's payload is false in exactly the regime
measured above.

## DD-20260804-052 -- machine word to payload bit range, and why it returns `some`

`RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerEntryAddress.lean`.

`DD-20260804-051` indexed an entry-chunked machine store two-level, in terms of
*words*. The packed physical read needs *bits*. This composes that index with
`packedFixedWidthTable_getElem?` and collapses the result to one `drop`/`take`:

```
packedEntryChunkBitOffset width wordSize i = (i % c) * wordSize + (i / c) * width
packedEntryChunkReadWidth  width wordSize i = min (width - (i % c) * wordSize) wordSize
packedMachineStoreWords_payload            : the word is that bit range
```

The offset is the entry's base plus the chunk's offset inside it. The width is a
full machine word except in an entry's final chunk, where the entry runs out
first -- exactly the case the three over-wide interior columns exercise at every
size below roughly `512`, so the `min` is load-bearing rather than defensive.

### The `some` is deliberate

The statement takes `i / c < entries.length` as a hypothesis and concludes
`... = some ...`, rather than being total with a `none` branch off the end.

`FG-09` requires that every attempted probe be *shown* in range, and the frozen
instruction for this campaign says in as many words: do not rely on total
out-of-range lookup returning an empty slice. A total formulation here would have
type-checked, read more cleanly, and quietly relocated the range obligation into
an `Option` that no later theorem was forced to discharge. Keeping the hypothesis
explicit means each of the eight interior components has to produce its own index
bound, which is the work `FG-09` is actually asking for.

This is the same discipline that `SourceWords.lean` applied when it took source
counts from `read_exact` rather than from payload length.

## DD-20260804-053 -- the interior widths are positive, three by computation and one by validity

`RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerInteriorWidths.lean`.

`packedMachineStoreWords_payload` needs three inputs per interior component: a
positive machine word size, a positive entry width, and an in-range index. The
first two are shared across all eight; this module supplies them.

```
superWidth        = machineWordBits shape.bpCode.length   -- machineWordBits_pos
offsetWidth       = machineWordBits layout.macroSize      -- machineWordBits_pos
blockAddressWidth = machineWordBits layout.blockCount     -- machineWordBits_pos
relativeWidth                                             -- Valid.relativeWidth_pos
```

Three are `machineWordBits` of something, hence positive at every argument
including zero. The fourth is not, and its positivity is a **field of the layout's
validity record** rather than a computation: `relativeWidth` must be wide enough to
hold a superblock span, and `Valid` carries that as a hypothesis discharged once in
`canonicalLayout_valid`.

That asymmetry is worth recording. `relativeWidth` is the same width the three
over-wide columns of `DD-20260804-051` carry, so the two facts this development
needs about it -- that it is positive, and that it exceeds a machine word below
`n ~ 512` -- come from entirely different places. A reader who found the second and
assumed the first was equally computational would look in the wrong file.

`packedInteriorComponentWord` specialises the address theorem to the interior's
machine word size, so a component supplies only its width positivity and its index
bound.

The index bound is deliberately still outstanding for all eight. That is the
`FG-09` obligation which `DD-20260804-052` refused to absorb into an `Option`, and
absorbing it here instead would have defeated the point of refusing it there.

## DD-20260804-054 -- the index bound, discharged from what a lowering has

`RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerInteriorCount.lean`.

`DD-20260804-052` kept `FG-09`'s in-range obligation explicit instead of absorbing
it into an `Option`; `DD-20260804-053` left it outstanding for all eight interior
components. This discharges it from the hypothesis a lowering actually carries.

```
packedMachineStoreWords_size            wordCount = entries.length * chunksPerEntry
packedEntryIndex_lt_of_lt               i < count * c  ->  i / c < count
packedInteriorComponentWord_of_lt       the address theorem, from i < wordCount
packedInteriorComponentWord_of_lt_size  the same, against the stored word count
```

A component occupies exactly one machine word per entry per chunk, so an index
below the word count names an entry that exists and the `i / c < entries.length`
side condition follows by division rather than by assumption. The obligation is
met, not moved.

`packedMachineStoreWords_size` needs **no** width positivity. The first draft
carried one; the linter flagged it unused and it was removed rather than left. The
count is `entries.length * chunksPerEntry` unconditionally -- at width zero every
entry chunks to the empty list and `chunksPerEntry` is zero, so both sides vanish.

That is the third spurious hypothesis this campaign has removed on the same
principle, after `hstride` on `packedReviewerMemory_header_cell` and the
never-needed `packedCellWidth n <= packedLongBlockBits n` of `DD-20260804-035`. A
hypothesis a theorem does not need misstates what it depends on, and in a gate
whose whole purpose is checking dependence, that is not cosmetic.

## DD-20260804-055 -- the component split is left-associated, and two failed attempts

`RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerConcatIndex.lean`.

Locating one of the eight interior components inside
`canonicalRelativeRmmInteriorComponentStore` needs three list facts, which land
here:

```
packedConcatIndex_left       an index inside the left operand reads it
packedConcatIndex_right      an index offset by the whole left operand reads the right
packedConcatIndex_lt_append  widening a prefix preserves an in-range index
```

### Two failed attempts, both recorded

The first attempt stated the baseline and minRel accessors directly and did not
unify. Two distinct reasons, found in sequence:

1. `packedReviewerInteriorComponentWords_split` carries `let` binders (`hword`,
   `summary`) in its *statement*, which block the unifier. `dsimp only` removes
   them.
2. Once removed, the real obstacle appeared: `++` is **left**-associative, so
   `A ++ B ++ ... ++ H` is `(((((((A ++ B) ++ C) ++ D) ++ E) ++ F) ++ G) ++ H)`.
   A single `packedConcatIndex_left` does not reach `A`; the outermost operands are
   the first seven components and `H`.

So reading component `k` needs `7 - k` peels with `packedConcatIndex_left`, each
justified by `packedConcatIndex_lt_append` widening the bound up through the
prefixes, then `k` uses of `packedConcatIndex_right`. The offsets in
`canonicalRelativeRmmInteriorComponentOffsets` are exactly those prefix lengths,
so the arithmetic matches by construction rather than by coincidence.

The half-written accessors were **not** committed. Landing a module with two
theorems that do not elaborate, or papering over them with a `simp` that might
close them by accident, would have put an unchecked claim into a gate whose whole
subject is checked claims. The tools are committed; the result is not, and the
report says so.

## DD-20260804-056 -- the first interior component is located

`RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerComponentAccess.lean`.

`DD-20260804-055` diagnosed the left-associated split and predicted `7 - k` peels
per component. Carried out for the leftmost component, the prediction holds
exactly:

```
packedConcatIndex_first_of_eight  the seven-peel chain, generic over eight lists
packedInteriorBaselineAccess      the baseline column IS the store's first words
```

Each peel's bound is the previous one widened by `packedConcatIndex_lt_append`, so
the chain is six `have`s and one seven-step `rw`. No search, no `simp`, nothing
that could close a goal by accident.

Combined with `packedInteriorComponentWord_of_lt_size` this is the first interior
component lowered end to end -- component-store index to payload bit range -- and
the first time segment `20` reaches a computable address.

Recording the shape before attempting it (`DD-055`) rather than after is what made
this a fifteen-line proof instead of a search. The two failed attempts recorded
there cost one elaboration each and bought the correct structure.

## DD-20260804-057 -- the second component confirms the pattern generalises

`ReviewerComponentAccess.lean`, extended.

```
packedConcatIndex_second_of_eight  six peels, then one offset skip
packedInteriorMinRelAccess         the minRel column, after the baseline column
```

`DD-20260804-055` predicted component `k` needs `7 - k` peels followed by the
skip. Component `0` used seven peels and no skip; component `1` uses six peels and
one skip. The prediction is now confirmed at both ends of its range rather than
extrapolated from one instance.

The six remaining components are the same shape with the counts shifted, and the
offsets they skip by are the prefix lengths `canonicalRelativeRmmInteriorComponentOffsets`
already records. Nothing further has to be discovered for them; only written.

`packedInteriorMinRelAccess` states its offset as the baseline column's own word
count rather than as `(canonicalRelativeRmmInteriorComponentOffsets shape).minRel`.
The two are equal by construction, but proving that equality is a separate step,
and stating the theorem in terms of the object it actually peels keeps it free of
an unproved bridge.

## DD-20260804-058 -- the third component, and the first compound offset

`ReviewerComponentAccess.lean`, extended again.

```
packedConcatIndex_third_of_eight  five peels, then a skip by two blocks together
packedInteriorMaxRelAccess        the maxRel column
```

Three of eight located. The pattern of `DD-20260804-055` now holds at three
distinct positions: its start (seven peels, no skip), its second step (six peels,
simple skip), and its first **compound** skip, where the offset is
`(baseline ++ minRel).length` rather than a single block's length.

The compound case is the one worth having done explicitly. Its bound needs
`List.length_append` supplied as a `have` rather than a rewrite -- a first attempt
passed explicit arguments to it and failed, because in this toolchain
`List.length_append` takes its lists implicitly. Small, but it is the kind of thing
that costs an elaboration cycle each time it is rediscovered.

Five components remain, all of the same shape with counts shifted and offsets
lengthening. No new structure is expected; if one appears, that itself is the
finding.

## DD-20260804-059 -- the summary half of the interior is fully located

`ReviewerComponentAccess.lean`, extended.

```
packedConcatIndex_fourth_of_eight  four peels, then the skip
packedInteriorArgOffsetAccess      the argOffset column
```

Four of eight located, which is the whole **summary** half: baseline, minRel,
maxRel, argOffset. The four remaining are the interior tables proper --
`interiorLocal`, `interiorGlobal`, `localLevel`, `globalLevel` -- and they are the
same shape with counts `3, 2, 1, 0` peels.

Nothing new was needed for this one. The template of `DD-20260804-058` applied
unchanged, including the `List.length_append`-as-`have` form. That is the intended
outcome of having written the template down, and it is worth noting that the
pattern has now survived four instantiations without amendment.

## DD-20260804-060 -- the peel chain is complete for all eight positions

`ReviewerComponentAccess.lean`, extended.

```
packedConcatIndex_fifth_of_eight    three peels, then the skip
packedConcatIndex_sixth_of_eight    two peels
packedConcatIndex_seventh_of_eight  one peel
packedConcatIndex_eighth_of_eight   none, and no hypothesis at all
```

`DD-20260804-055`'s `7 - k` prediction now holds across the entire range, from
seven peels at `k = 0` to zero at `k = 7`, with no amendment at any point.

The eighth is worth a line. The last block is the outer right operand of the
left-associated term, so `packedConcatIndex_right` applies **directly**, and it
needs no `j < h.length` hypothesis -- out of range, both sides are `none`. Every
other position needs its bound, because the peels do. That asymmetry is a property
of the association, not an oversight, and stating the eighth with a spurious
hypothesis to match its siblings would have been the wrong kind of uniformity.

Four accessors remain -- `interiorLocal`, `interiorGlobal`, `localLevel`,
`globalLevel` -- each now a one-line application of its matching chain, exactly as
the summary four already are.

## DD-20260804-061 -- all eight interior components are located

`ReviewerComponentAccess.lean`, completed.

```
packedInteriorLocalAccess        component 4, interior local offset table
packedInteriorGlobalAccess       component 5, interior global block table
packedInteriorLocalLevelAccess   component 6, local level table
packedInteriorGlobalLevelAccess  component 7, global level table, no bound needed
```

Eight of eight. Each is a one-line application of its matching peel chain, which
is what `DD-20260804-060` was for.

The four component word lists are named as `abbrev`s
(`packedInteriorBaselineWords` and siblings) so the offsets stay readable at
seven-fold appends. That cost one round: `abbrev` is reducible, so `exact`
unifies through it, but `rw` matches syntactically and does not. The store's own
abbreviation has to be `unfold`ed before the split rewrite. Recorded because the
same shape will recur wherever an abbreviation meets a rewrite.

Combined with `packedInteriorComponentWord_of_lt_size`, every interior component
now has a chain from component-store word index to a bit range of its own table's
payload.

What is still missing before segment `20` reaches a **cell**:

* the bridge from these peel offsets to
  `canonicalRelativeRmmInteriorComponentOffsets`. They are equal by construction
  -- the offsets record is defined as exactly these prefix sizes -- but equal by
  construction is not proved, and this gate does not accept it as such;
* placing each component's payload inside the consumed payload, which is where the
  interior directory sits at a known offset after `bpCode` and the live access
  half.

## DD-20260804-062 -- "equal by construction" is now proved

`ReviewerComponentAccess.lean`, completed.

`DD-20260804-061` flagged the bridge from the peel offsets to
`canonicalRelativeRmmInteriorComponentOffsets` as outstanding, noting the two are
equal by construction but that this gate does not accept construction as proof.
All eight fields are now proved:

```
packedInteriorOffsets_baseline      = 0, by rfl
packedInteriorOffsets_minRel
packedInteriorOffsets_maxRel
packedInteriorOffsets_argOffset
packedInteriorOffsets_localOffset
packedInteriorOffsets_globalBlock
packedInteriorOffsets_localLevel
packedInteriorOffsets_globalLevel
```

Each says the record's field equals the length of the corresponding prefix
append. `baseline` is `rfl`; the rest are `unfold` then `simp` then `omega`.

### The one thing that was not automatic

The record's later fields are written in terms of the *machine store aliases* --
`canonicalRelativeRmmLocalMachineStore` and siblings -- while the peel offsets are
in terms of `(canonicalRelativeRmmInteriorLocalTable shape).table.machineStore`.
`omega` treats those as distinct atoms and reports a counterexample rather than an
unfolding failure, which reads as a false goal until one looks at the atom list it
prints. Adding the aliases to the `unfold` list closes it.

Worth recording because the failure presents as arithmetic and is actually
naming: two spellings of one object, in a file where the whole exercise is
checking that objects are what they are claimed to be. The atom list in `omega`'s
output is the diagnostic.

Segment `20` now has a complete chain: component-store word index, through the
located component and its offset, to a bit range of that component's own payload.
What remains is placing the interior directory's payload inside the consumed
payload.

## DD-20260804-063 -- the close half's position inside the consumed payload

`ReviewerComponentAccess.lean`, extended.

```
packedReviewerPayload_drop_closeOffset
```

Dropping `concreteBPNativeSuccinctRMQCanonicalReviewerCloseBitOffset` bits from the
consumed payload leaves exactly the interior directory followed by the two chunk
tables. Everything before it is `bpCode` and the live access payload, and nothing
else.

The proof needed one re-association. The layout is written
`bpCode ++ access ++ close ++ fringe ++ select`, which is left-associated, so its
top-level split is *after* `fringe` rather than after `access`. `List.drop_left`
needs the split at the drop point, so the term is first rewritten to
`(bpCode ++ access) ++ (close ++ fringe ++ select)` by `simp [List.append_assoc]`
inside a `show`.

This is the third time in this campaign that left-association of `++` has dictated
the proof shape, after `DD-20260804-055` and `DD-20260804-060`. It is worth
treating as a standing feature of this development rather than a recurring
surprise: whenever a statement names an interior split point of a multi-way
append, the term has to be re-associated at that point first.

Segment `20`'s chain is now: component-store word index, to located component, to
that component's offset, to a bit range of its own payload, to a bit range of the
interior directory, to a position inside the consumed payload. What remains is
composing those into a single address function and running it through
`packedReviewerMemory`.

## DD-20260804-064 -- word offsets and bit offsets are separate obligations

`ReviewerComponentAccess.lean`, extended.

```
packedInteriorDirectoryPayload_split
```

The interior directory's **payload** splits eight ways, matching the eight-way
split of its **words**.

These are genuinely different facts and it is worth saying why, because the
temptation is to treat one as the other. A component's word offset is the number
of machine words before it; its bit offset is the number of payload bits before
it. The two agree only when every preceding entry exactly fills its machine
words -- and `DD-20260804-051` measured three interior columns whose entries do
**not**, at every size below roughly `512`. So a bit address derived from a word
offset would be wrong precisely where the structure is most exercised.

Having both splits proved separately is what keeps the eventual address function
from silently conflating them.

The proof needed `canonicalRelativeRmmInteriorDirectory` itself in the `simp` set;
without it the structure projection does not reduce and `simp` closes nothing while
reporting the payload lemmas as unused. The unused-argument hint was the signal
that the goal had not been unfolded at all, rather than that the lemmas were
wrong.

Segment `20`'s remaining work is now composition only: word split, offsets bridge,
bit-level payload split, and close-half position are each proved, and no further
structural fact about the interior is expected.

## DD-20260804-065 -- the prefix slice, and the last structural fact segment 20 needs

`ReviewerComponentAccess.lean`, completed.

```
packedPrefixSlice : off + len <= xs.length -> ((xs ++ ys).drop off).take len
                                            = (xs.drop off).take len
```

A slice wholly inside a prefix does not see the suffix. This is what lets a
component's own payload slice be read off the concatenation it sits in, and it is
the last structural fact segment `20` requires.

The hypothesis is `off + len <= xs.length`, not `off < xs.length`. The stronger
form is what is actually needed and what the callers can supply: a slice that
*starts* inside the prefix but runs past its end would pick up suffix bits, and
this development has at least one source where that is a live possibility rather
than a pedantic one -- the entry chunks of `DD-20260804-051`, whose final chunk is
short precisely because the entry ends.

### Segment 20's structural work is complete

Word split, offsets bridge, bit-level payload split, close-half position, prefix
slice. All proved. No further structural fact about the interior is expected.

What remains for segment `20` is composition, and it is worth noting in advance
that it will need the same re-association as `DD-20260804-063`: the close half is
`directory ++ fringe ++ select`, left-associated, so a statement naming the
directory as the prefix must re-associate to `directory ++ (fringe ++ select)`
first. That is now the fourth appearance of this shape.

## DD-20260804-066 -- segment 20 is composed

`ReviewerComponentAccess.lean`, completed.

```
packedReviewerPayload_interiorSlice
```

Any bit range wholly inside the interior directory is the same range of the
**consumed payload**, shifted by the close bit offset. With the eight component
accessors, the offsets bridge, the bit-level payload split and the prefix slice,
segment `20` now reaches the consumed payload as a computable bit range.

The re-association predicted in `DD-20260804-065` was needed, exactly as written.
One thing was not predicted: `List.drop_drop` folds as `(l.drop a).drop b =
l.drop (b + a)`, so rewriting `drop (closeOffset + off)` backwards yields the
drops in the order that is already wanted, and the `Nat.add_comm` added in
anticipation produced the *reversed* nesting. Removing it closed the goal.

Recorded because the natural instinct -- normalise the sum first -- is wrong here,
and the error it produces is a failed rewrite deep in the chain rather than at the
`add_comm`, so it does not point at its own cause.

### What segment 20 now has

Component-store word index, through the located component and its proved offset, to
a bit range of that component's payload, to a bit range of the interior directory,
to a bit range of the consumed payload. Every link checked.

What remains for the close half is the physical read over
`packedReviewerMemory`, which is what turns a bit range into cells, and which is
shared with the eighteen live access sources rather than specific to segment `20`.

## DD-20260804-067 -- the conditional probe, re-targeted at the consumed payload

`Probe.lean` builds the one-or-two-cell plan over `packedMemory`. The re-target
needs the same plan over `packedReviewerMemory`. This decision records what was
rebuilt, what was reused, and why the split falls where it does.

### Reused verbatim

`packedProbeCell` and `packedFetch` both take the memory as an argument and
mention no width or count. They are used unchanged. Duplicating them would have
created two definitions of "issue a plan" that could drift apart, and the whole
point of the failure they encode -- an unallocated address yields `none`, not an
empty slice -- is that there is exactly one of them.

### Rebuilt

Everything naming a cell width or a cell count. Two independent reasons:

* `packedReviewerCellWidth n` differs from `packedCellWidth n`, so `bit / w` and
  `bit % w` name different cells. No amount of generalisation makes one plan serve
  both; they are different addresses of different memories.
* `packedReviewerCellCount n longCount` takes the decoded long count, where
  `packedCellCount n` does not. Every allocation statement therefore carries
  `longCount` explicitly.

The second is the `K1` argument made load-bearing rather than decorative. Under the
flat payload the cell count is size-only, so a controller could have computed it
from `n` and the header carried nothing it needed. Over the consumed payload it
cannot: `packedReviewerProbePlan_lt_cellCount` cannot even be stated without a
`longCount`, so no address past cell zero can be shown allocated until cell zero
has been probed and decoded. `packedReviewerHeaderProbe_decode` is where that value
comes from, and it is charged as one probe like any other.

### Which theorems need the unit-stride hypothesis, and which do not

Only `packedReviewerProbeWindow_length`, which is about the *length* of the reply
window and so inherits `packedReviewerPaddedBits_length`.

The plan, the three count cases, the cap, the coverage bound, both reachability
directions, the allocation of every issued address, the fetch, the boundary case and
the decode all do without it. They are algebra on the padded bit string, not facts
about how long it is. Carrying `hstride` on them would have misstated what they
depend on, in the same way the three hypotheses removed under `DD-20260804-035`,
`-050` and `-057` did.

### The boundary case

`packedReviewerProbe_final_cell` is the reviewer counterpart of
`packedProbe_final_cell`: a positive-width read contained in the last allocated cell
issues exactly one probe and fetches successfully. Its companion
`packedReviewerMemory_getElem?_cellCount` shows the address an unconditional second
probe would have issued is absent, so the same read would have returned `none`.
Both are restated over the new memory rather than inherited, because the absent
address is a different number.

## DD-20260804-068 -- the per-source address surface over the consumed payload

The flat layout offsets sources componentwise. The reviewer layout does not: its
access half is one `flatMap` over one list, so a source's offset is the summed bit
length of everything before it in that list. `packedReviewerAccessOffset` is defined
as exactly that, over `takeWhile (fun x => x != source)` of the canonical list, so
the offset and the payload it measures read the same list and cannot drift apart.

### Why the prefix sum is size-only with no unit-stride hypothesis

`selectSparseRelative` is the only live access source whose bit length is not a
function of `(n, longCount)`, and in the canonical list it is **last**. Every proper
prefix is therefore made of counted sources, and the offsets need no `hstride` --
unlike `packedReviewerPayloadLength`, which needs one precisely because the sparse
table is inside the total.

That ordering was not something this branch arranged, so
`packedReviewerAccessPrefix_counted` pins it by evaluation. Moving the sparse
relative table earlier breaks the `decide`.

### Three things that were wrong on the first attempt

**Membership is load-bearing.** The prefix-counted lemma was first stated with only
`source != selectSparseRelative`. `decide` reported the proposition **false** for
eleven of the twenty-nine constructors -- every source that is not in the reviewer
list at all. For those, `takeWhile` never fires and consumes the whole list, sparse
relative table included. The fix is a real hypothesis, `hmem`, not a workaround: the
offset of a source that is not in the list is meaningless.

**Containment does not follow from the slice equation.** The first proof of
`packedReviewerAccessOffset_fits` tried to get `offset + len <= total` by taking
lengths of `packedReviewerAccessPayload_slice`. That fails, and it fails for a real
reason rather than a tactic reason: taking lengths gives `min len (total - offset) =
len`, which for `len = 0` holds at **every** offset, including offsets past the end.
A source with an empty payload satisfies the slice equation anywhere. The fit has to
come from the split itself, and now does, through `packedFlatMapPrefixFits`.

**`List.drop_drop` orientation, corrected.** Section `8h` of the result report
recorded this lemma as folding `(l.drop a).drop b = l.drop (b + a)` -- outer summand
first. That is wrong. The actual signature in this toolchain is

```
List.drop_drop : List.drop i (List.drop j l) = List.drop (j + i) l
```

so the **inner** drop's amount comes first in the sum, and `rw [<- List.drop_drop]`
turns `l.drop (X + Y)` into `(l.drop X).drop Y`. The earlier note reached the right
action -- delete the anticipatory `Nat.add_comm` -- from an inverted reading, and
that inverted reading is what put an `add_comm` back into this module and broke the
rewrite chain again. The signature above is now quoted rather than paraphrased.

### The instance question in the split lemma

`packedSplitAtFirst` is stated at the concrete source type rather than generically.
A generic version needs `DecidableEq` for the `by_cases` and `BEq` plus `LawfulBEq`
for the `!=` in the predicate, and nothing forces the `BEq` instance in scope to be
the one `!=` elaborates to at the use site. Specialising removes the question.

## DD-20260804-069 -- the physical read over the consumed payload

The three pieces the re-target needed are now joined: the address surface
(`DD-20260804-068`), the width bound `packedSourceStride_le_reviewerCellWidth`, and
the conditional probe plan (`DD-20260804-067`). `packedReviewerSourceRead` issues a
plan, fetches, and decodes; `packedReviewerSourceRead_of_some` proves the decoded
span is the word the source's word array returns.

### What is deliberately not rebuilt

The per-source word geometry -- `packedSourceStride`, `packedSourceWordCount`,
`packedSourceReadWidth` -- is reused unchanged. Those measure a source's own
payload, not the layout it is embedded in, so they are the same numbers over either
memory. Rebuilding them would have created a second set of widths that could drift
from the first while both remained provable.

Only the *address* is new, and only because the offset is. That is the whole content
of the re-target at this layer.

### Direction, and why it is still an implication

`packedReviewerSourceRead_of_some` is an implication rather than an equation, for
the same reason as its flat counterpart (`DD-20260804-022`): between the sparse
relative table's actual entry count and its size-only capacity the packed read
answers where the store would have failed. Every **successful** logical read lowers
exactly. Restating it as an equation would require the size-only capacity to be
attained, which is not proved and is not needed.

### Scope, stated so it is not mistaken for more

Seventeen counted live access sources. The close half's segments are **not** read
here: they are not in the access list, so they have no `packedReviewerAccessOffset`
at all, and they are reached through `packedReviewerPayload_interiorSlice` instead.
Their read, and therefore any store presenting the reviewer memory to the evaluator,
remains open.

## DD-20260804-070 -- the close half's chunk tables, bounded and read

Segments `21` and `22` are the two close segments that are uniform word grids. They
now have shape-free offsets into the consumed payload, width bounds, and lowerings.

### The width bound is a comparison of bounds, not of widths

`packedReviewerCellWidth n` is `machineWordBits (packedReviewerCellBound n + 2)` -- a
logarithm. So "the entry is narrower than the payload" proves nothing; what is
needed is that the entry's *bound* is no larger than the cell bound.

For the select chunk table this is easy: the entry bound is `c + 1`, and the table's
own overhead `2 ^ c * (c + 1) * W` -- which sits inside the reviewer overhead, hence
inside the cell bound -- already exceeds it.

For the fringe chunk table it is not. The entry bound `(2c+1)(2c+2)(c+1)` is cubic in
`c`, while the naive lower bound on the table overhead, `2 ^ c * (c+1) ^ 2`, only
overtakes it from `c = 5`. Writing out the small cases would need `Nat.log2`
evaluated at numerals, which this toolchain does not reduce willingly.

The gap is closed by the width factor instead. `W >= 4`, because `W <= 3` would give
`entryBound < 2 ^ 3 = 8` through `bpFringeChunkEntryBound_lt_two_pow_width`, while
`entryBound >= 24` whenever `c >= 1` -- and `bpFringeChunkBits_pos` says `c >= 1`
always. Then `entryBound <= 4 (c+1) ^ 3 <= 4 * rowCount <= W * rowCount = overhead`.
No logarithm is ever evaluated.

### Why these two reads are simpler than the live access sources

Both tables satisfy `payload.length = entries.length * width` exactly, so an in-range
read is a full-width window. There is no partial final word and no counterpart of the
sparse relative table's capacity gap, so the read width is the entry width itself
rather than a `min`.

### The type index that cannot be rewritten

`FixedWidthNatTable` takes the entry width as a **type index**, so
`bpFringeChunkTable c : FixedWidthNatTable (bpFringeChunkEntries c)
(bpFringeChunkEntryWidth c)`. Rewriting the width inside any term containing the
table makes the rewrite motive ill-typed, and `rw ... at` reports exactly that.

Rewriting `shape.bpCode.length` inside the table is fine, because the whole term
changes together and the projection `.payload` lands in `List Bool` either way. It is
rewriting the width *alone* that fails.

The proofs are therefore arranged so the size-only width appears only in the goal,
where no table occurs, and the word equation comes from `Option.some.inj` applied to
a transitivity rather than from rewriting a hypothesis.

### Scope

Segment `20` is untouched. The interior component store is not a uniform grid at all,
so it has neither a single entry width to bound nor a single word count to guard, and
its read remains open.

## DD-20260805-071 -- keep K1 and make the reviewer machine all-size by charged discovery

The all-size controller uses the payload the public semantics actually consumes,
`concreteBPNativeSuccinctRMQCanonicalReviewerPayload shape`.  It keeps the existing
one-cell `longCount` header and does **not** add a `sparseCount` header cell.  Instead,
after reading cell zero, it obtains the exact sparse-relative row count through three
fixed logical reads of the sparse flag rank-super word, rank-block word, and final
flag word.  Those source addresses precede the sparse-relative table, depend only on
`n` and the decoded `longCount`, and each lowers to at most two charged physical
cells.  The replies determine `sparseCount` by the same rank decomposition as the
canonical table.

This is the K1 branch of the all-size fork.  K2 was authorized only after a checked
K1 obstruction.  No such obstruction exists: the three permitted prior replies give
the missing count with a fixed six-cell upper bound.  Adding a second header anyway
would therefore spend a counted cell and change the format without satisfying its
authorization condition.

### Closed controller geometry, list-backed proof geometry

The canonical reviewer layout remains list-backed on the proof and construction
side, where that representation prevents the serialized payload from drifting from
its source order.  The executable controller does not traverse that list.  Its
address surface uses a closed match over the eighteen live source tags, followed by
closed arithmetic for the ragged interior directory and the two chunk tables.

The exact access length is expressed as the fixed prefix before
`selectSparseRelative` plus

```
sparseCount * packedLocalWidth n
```

and the total payload length adds the BP prefix and all three close components.
Proof-only drift theorems equate every closed offset, plan, decoder, and total length
to the canonical list-derived geometry.  This split is deliberate: a source list is
good evidence for layout identity but is uncounted dynamic metadata if an executable
request path walks it.

### One first-order machine and one trace

`packedReviewerController` is a proof-free request/reply machine.  Its state carries
only public size/endpoints, decoded header values, fixed control tags/counters, and
prior physical replies.  Memory appears only in `packedReviewerRunAgainstMemory`,
whose driver obtains a reply by indexing the supplied cell array at the emitted
address and feeds that exact reply to `packedReviewerConsumeReply`.

Executed segment `20` is not flattened into a fictitious uniform word grid.  Its
lowering classifies the logical word into one of the eight canonical components and
retains that component's entry count, entry width, per-entry chunk number, partial
final width, and bit prefix.  Segments `21` and `22` retain their separate uniform
chunk geometries.  Zero-cell logical attempts advance the logical protocol without
adding decorative physical events.

The residual logical-step counter in the controller is operational state: it is the
remaining fuel of the accepted fixed 210-step logical request/reply driver, consumed
one logical attempt at a time.  It is not a stored physical cost claim.  The physical
cap is proved only after the run and trace decomposition exist.  Its arithmetic is

```
1 header cell + at most 2 * 3 prelude cells + at most 2 * 210 whole-run cells = 427.
```

The capstone is required to use the identical run object for terminal value,
reviewer-memory backing, ordered physical/logical grouping, allocation, address and
reply width, and the literal trace cap.  Shape and the global logical store appear
only in the proof-side refinement of that run to `packedWholeQueryRun` and the
guarded public `queryTraceResult` semantics.

### Rejected alternatives

* The former `localStride = 1` chain and its informal `2^97` discussion were
  rejected: neither is an all-size theorem, and neither is needed by the charged
  prelude.
* A finite astronomical cutoff was rejected as a restatement of the same gap.
* An unconditional K2 `sparseCount` header was rejected because K1 is constructible
  and no quantifier-matched obstruction was proved.
* Walking `concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources` inside a
  clean-signature wrapper was rejected as hidden controller metadata.  The closed
  arithmetic surface replaces that traversal.
* The older flat sibling payload, internal padding, and a sibling logical store were
  rejected because the space, memory, execution, and public semantics must compose
  through one object.
* A semantic answer decorated with reads, a theorem-only trace, and a stored cap
  were rejected because none would make the terminal value depend on the actual
  charged replies.

### Consequences and evidence surface

The construction pays a small fixed prelude and accepts the conservative literal
cap `427`; it gains an oracle-free all-size route with no content count supplied out
of band.  The main evidence surfaces are `ReviewerSparsePrelude.lean`,
`ReviewerClosedGeometry.lean`, `ReviewerInteriorRead.lean`,
`ReviewerLogicalLowering.lean`, `ReviewerController.lean`,
`ReviewerLogicalSimulation.lean`, and `ReviewerControllerProof.lean`.  Independent
validation must pin their concrete signatures and the same-run public certificate;
source-level cleanliness alone is not acceptance.

The hardest skeptical-reviewer question is whether the apparently closed controller
still reaches a shape-specialized list or semantic store through a helper.  The
answer must remain a transitive call-graph fact, backed by the closed definitions and
their proof-only drift boundary, not merely by the public function types.

## DD-20260805-072 -- normalize completed child protocols before exposing a wrapper

The logical reviewer controller is built by embedding smaller request/reply machines
inside select, interior, LCA, and whole-query states.  A child constructor is allowed
to return an already-terminal state without issuing a request.  A parent that wraps
such a child blindly has `result = none` and `nextRequest = none`, which is a
deadlock: the driver cannot consume a reply that would advance it.

This was not hypothetical.  Four dense-select continuations could start a rank or
word-select child on an empty/zero-chunk word.  The child was `.done`, while the
wrapper remained `denseBeforeRank`, `denseUptoRank`, `denseFirstSelect`, or
`denseSecondSelect`.  The fix is at each select smart constructor: inspect the child
result immediately, advance or map the value when it is present, and construct a
wrapper only when the child has a next request.

Interior range-min has a deeper version because zero-read table decodes can cascade
through defunctionalized continuations.  `packedReviewerInteriorStartRaw` preserves
the branch construction, and `packedReviewerInteriorNormalize` repeatedly consumes
already-completed child results through `packedReviewerInteriorFinishNat` before a
public state is exposed.  Public start and every completed-child consume transition
cross this normalization boundary.  Its fuel is
`packedReviewerInteriorRemaining state + 1`, the existing structural continuation
measure; normalization performs no read and does not contribute a physical probe.

The whole-query protocol can also wrap an immediately done out-of-range select, but
that state is unreachable from the actual physical machine: `packedReviewerController`
checks `left < right` and `right <= n` before entering header, prelude, or whole-query
execution.  Invalid, empty, reversed, and out-of-range inputs instead return the
exact terminal `.done none` run with an empty trace.  The validation surface pins
both sides of this guard.  On valid inputs, the two selected indices are formally
inside `n`, so both whole-query select starts are request-producing.

### Why the protocol, not the proof, changed

The atomic child simulations are quantified over arbitrary supplied logical stores.
It would have been unsound to dismiss an empty reply as impossible while proving
those transition lemmas, and it would have hidden the protocol defect to add a
store-content premise there.
Similarly, increasing the outer fuel cannot repair a state with neither a result nor
a request.  Normalization is the semantic operation the composition was missing.

### Consequences

Logical budgets continue to count actual read attempts only.  Synchronous child
completion consumes structural normalization fuel but creates no logical or physical
event, so trace multiplicity, the 210 logical bound, and the derived 427 physical
bound keep their intended meaning.  Future embedded protocol starts must follow the
same smart-constructor rule, and proof reviews should explicitly check the invariant:
every reachable nonterminal wrapper exposes a next request.

## DD-20260805-073 -- place fixed-budget correctness at the canonical reviewer-store boundary

The physical driver is deliberately total over any list of cells: it receives only
that memory, emits requests, consumes the returned optional cells, and records at
most its structural fuel.  That fact does not make an arbitrary forged memory a
semantic RMQ representation, nor does it imply that every forged reply sequence
reaches the terminal state within the canonical 210 logical-read budget.

The distinction matters in the interior route.  General canonical-layout field
widths have checked bounds as large as seven physical words.  The tight 33-read
interior theorem instead has canonical reachability premises: a positive-size,
bounded block range produced by the actual close/LCA route.  An arbitrary logical
store may forge select replies whose close positions violate that geometry and can
therefore drive a longer interior execution.  A theorem claiming the same fixed
210-step semantic simulation for every `WordRAM.ReadStore` would be stronger than
the accepted cost theorem and is not the interface the physical construction uses.

### Decision

State ordered whole-run correctness and occurrence preservation against
`concreteBPNativeSuccinctRMQGlobalReadStore shape`.  The composition chain is:

```
packedReviewerMemory shape
  -> exact physical replies
  -> packedReviewerLogicalRead_eq_globalReadStore
  -> canonical-store 210-step ordered simulation
  -> packedWholeQueryRun
  -> guarded public queryTraceResult
```

Keep the generic arbitrary-memory theorem only where it is true: the physical
driver's trace length is at most 427 because fuel bounds recorded requests.  Its
terminal adequacy, allocation, successful replies, ordered grouping, and reference
correctness are proved for the canonical reviewer memory on the identical public
run object.  Atomic child simulations may remain store-parametric when their local
budgets are genuinely independent of reply content.

### Rejected alternatives

* Claiming arbitrary-store 210-step termination was rejected because forged select
  replies need not satisfy the bounded interior geometry.
* Adding semantic range checks or an answer oracle to the executable controller was
  rejected: the reviewer memory already supplies the canonical replies, and such a
  check would change the accepted logical protocol rather than prove it.
* Treating the arbitrary-memory 427 fuel cap as a success theorem was rejected.  It
  bounds trace length even when fuel is exhausted; success is a separate canonical
  certificate field.
* Weakening the physical driver to accept a `WordRAM.ReadStore` was rejected because
  it would violate reviewer-memory-only execution and make the proof target choose
  the answer source.

### Consequences and evidence

Validation must pin the shape/canonical-store signature of the 210-step simulation,
the arbitrary-memory signature of the structural 427 cap, and the canonical public
certificate's terminal, allocation, read-backing, reply-success, and result fields.
This is a proof-boundary correction, not an executable shortcut: the controller,
memory lookup, request order, trace, and returned value are unchanged.

## DD-20260805-074 -- close request operands at the reachable-state boundary

The physical controller proof has two logically independent layers.  The first
constructs the request/reply run and proves its exact lowering, canonical terminal
result, ordered physical grouping, memory backing, allocation, address capacity,
reply width, and derived probe cap.  The second proves that every scalar and control
value retained at every canonical prefix is a modeled machine value.  A logical
request's instruction arguments, read-site payload, segment, and index belong to
that second prefix invariant: they are produced by the current nested protocol
state, not by the later physical expansion alone.

### Decision

Keep execution and semantic refinement in `ReviewerControllerProof.lean`.  Put the
constructor-exhaustive logical request-operand theorem, its expected-physical-trace
lift, the grouped-run operand theorem, and the final public run certificate in
`ReviewerControllerStateProof.lean`, which imports the base proof and owns the
canonical reachable-state invariant.  The downstream module recreates the stable
public names and exact signatures; validation therefore sees no weakened API.

The composition is:

```
ReviewerControllerProof
  -> actual run / grouping / allocation / backing / correctness / cap
  -> ReviewerControllerStateProof canonical-prefix invariant
  -> logical request operands
  -> occurrence-preserving physical request operands
  -> exact public run + reachable-state certificates
```

### Rejected alternatives

* Duplicating Select, Interior, LCA, and Whole transition invariants in both modules
  was rejected.  It would create two proof paths for the same derived indices and
  make future protocol changes easy to synchronize incorrectly.
* Making the base module import the state proof was rejected because the state proof
  already consumes the base run and grouping theorems; that would create a module
  cycle rather than a proof.
* Dropping operand fields from the public certificate was rejected because it would
  reopen `INV-ADDRESS-WIDTH` and let a correct physical address theorem coexist with
  unbounded dormant or producing instruction operands.
* Treating constructor tags as unencoded host-language metadata was rejected.  The
  state proof separately enumerates all nested protocol and continuation tags and
  proves that their fixed codes fit the same all-size word width.

### Consequences and evidence

`ReviewerControllerProof.lean` can compile without a forward reference to a theorem
whose natural proof depends on canonical prefix reachability.  The downstream proof
must still reconstruct the exact old certificate fields and prove the request
theorem constructor-by-constructor; moving the declaration is not acceptance by
itself.  `EGCPFinalFalsification.lean` imports both modules and independently
restates every certificate field, so a missing operand theorem, weakened grouping,
or uninhabited state predicate remains a compilation failure.  Replay case
`M12-PUBLIC-TYPE-WEAKENING` follows the declaration to its new owning file.

## DD-20260805-075 -- accurate fuel wording and validation-header inventory

Status: Accepted under the coordinator-commissioned `R2R1-03` repair.

Date: 2026-08-05

Trigger: the coordinator's repair commission identified two inaccurate Lean
comments on the candidate: the simulation docstring described a "fixed
210-read" controller, and the validation root's header still claimed the
controller, whole-run lowering, same-run correctness, and committed replay
"do not yet exist" although the same file pins all of them.

Decision: correct both comments without touching any theorem, definition, or
proof. The simulation docstring now says "210-fuel ... at most 210 logical
attempts, not an exact read count", matching the derived-cap accounting
(1 header cell + at most 2 * 3 K1 cells + at most 2 * 210 logical attempts
= 427). The validation header now states that the controller, lowering,
correctness, and the locally owned seven-case `R2-ALLSIZE` replay exist and
are pinned below, while full `FG-11` liveness and the complete sixteen-case
`FG-12` replay remain open full-node obligations. `210` is never described as
an exact read count, and the theorem is never described as word-RAM
instruction time or as `S1` bit-addressed serialized-payload querying.

Alternatives rejected: leaving the stale header until the claims
synchronization wave (it is a factual in-file inaccuracy on the audited
surface, not a public-claim wording choice); rewording the cap itself
(the numerals and theorems are unchanged and correct).

Consequences: comment-only Lean changes in
`RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerLogicalSimulation.lean`
and `RMQ/Validation/EGCPFinalFalsification.lean`; theorem bodies and types
are unchanged; the strict design-decision classifier requires this ledger
entry because those paths are Lean paths.

## DD-20260806-076 -- the Stage-F capstone is a projection bundle, and header liveness is a universal second-address theorem

The Stage-F residual campaign needed two new theorem surfaces: one combined
capstone over the accepted reviewer-machine objects, and the `FG-11` header
liveness witness. Both live in
`RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerCapstone.lean`.

### Decision

`PackedReviewerStageFCapstone xs left right` is a structure whose fourteen
frozen conjuncts (matrix section 10.5, as corrected by the audited repair
`R2`) are each stated over the literal
`SuccinctClassic.cartesianShape xs`, `packedReviewerMemory shape`, and
`packedReviewerRunAgainstMemory (packedReviewerMemory shape) shape.size left
right`, and whose producer `packedReviewerStageFCapstone_holds` is pure
projection: every field is discharged from
`packedReviewerRunAgainstMemory_public_certificate`, the payload/memory/space
equations, `packedReviewerRunAgainstMemory_eq_of_agree`, or -- for the
`controller_input_boundary` field -- two `rfl`s: the eta-form exact-type pin
`@packedReviewerController = fun (n left right : Nat) =>
packedReviewerController n left right`, which elaborates only at the exact
public entry type `Nat -> Nat -> Nat -> PackedReviewerControllerState`, and
the zeta-form run factorization exhibiting that memory is supplied only to
the physical driver interface. A compile-negative probe on this branch
confirmed the anti-vacuity direction: adding the `M03`-style optional shape
parameter to `packedReviewerController` makes this field ill-typed and
`ReviewerCapstone.lean` is the first failing module of the chain. The
former length/arity and store-agreement facts are retained under the
accurate names `closed_length_and_memory_arity` and
`store_agreement_determinism`; they are conjuncts, not an input boundary. No new execution
story is introduced; the capstone's value is that deleting or weakening any
accepted theorem breaks one named conjunct, and the validation root restates
every conjunct independently.

Header liveness is proved universally rather than at a sampled size:
`packedReviewerHeaderCellAddressLiveness` shows, for every shape and valid
endpoint pair, that replacing only memory cell `0` by the same-width encoding
of `longCount + w(n)` changes the run's second attempted physical address.
The proof route is two-step symbolic execution of the driver on both
memories, plus the linearity of the closed first-order access prefix
(`packedReviewerSparseRankSuperPrefixLength`) in the decoded count: the only
count-dependent prefix term is the long relative table, contributing
`longCount * superStride (2n) * packedSuperWidth n` bits, so a one-cell-width
count shift moves the first `.rankSuper` probe by at least one whole cell.
Supporting facts: the prelude's terminal-sample index is inside the
sparse-rank directory by the successor inequality (`packedSparseRankSlots n`
is literally `index + 1`), the terminal sample is read at the full word size,
and `longCount + w(n)` still fits one cell
(`packedReviewerLongCount_add_width_lt_two_pow`, via
`log2 (bound + 2) + 1 + n <= bound + 2`).

`FG-14` boundary instances are all instantiations of the one universal
capstone: empty, singleton, both size-two lists (with a distinctness proof by
answer divergence, since kernel `decide` cannot reduce `cartesianShape`),
crossover `5487/5488/5489`, the readiness window's six sizes, invalid-query
cases, and the duplicate-minimum fixture `[7, 3, 3]` whose expected `some 1`
comes from `scanWindow`/`queryCosted_exact`/`queryCosted_leftmost`, never
from the implementation output.

### Rejected alternatives

* Restating capstone conjuncts as new proofs rather than projections was
  rejected: a second proof route would let a library weakening survive behind
  the capstone's own copy.
* A sampled header-liveness instance (the frozen row's minimum) was rejected
  in favour of the universal theorem: the geometry is linear in the decoded
  count at every size, so proving one size would spend almost the same work
  for strictly weaker evidence.
* Deriving the second-address fact from the grouping theorem was rejected:
  the mutated memory is no shape's canonical memory, so the grouping does not
  apply to it; direct two-step driver execution covers both runs uniformly.
* A `decide`-based size-two shape distinctness was rejected because
  `cartesianShape` is not kernel-reducible; the answer-divergence proof uses
  only public theorems.

### Consequences and evidence

`ReviewerCapstone.lean` elaborates in under four seconds, which keeps every
replay rebuild chain that includes it far inside the harness deadline. The
validation root gains independently written consumers for the capstone and
the liveness theorems. The decisive-cell and unread-cell fixture theorems
land in the same module and are recorded separately.
