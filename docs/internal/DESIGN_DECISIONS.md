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
DD-20260709-010. Foundational decisions such as the Mathlib-free trust boundary,
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

The next final-route architecture must define total positive geometric
parameters for every input and keep compact-table readiness or payload
availability as a separate predicate. Inactivity must not zero block size,
block count, superblock count, relative width, or other routing geometry.

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
- `RMQ/Core/SuccinctClose/RelativeRmmMacro/LocalBPDecoder.lean`

Follow-up:

Join the total-parameter, dependency-closure, and naming scouts before assigning
the implementing worker.

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
- Provide one semantic directory interface with counted small/packed and
  ready/compact implementations.

Rationale:

A uniform abstraction makes the exactness and cost proof follow the mathematical
decomposition rather than threshold compatibility. Counted representations
preserve the existing space and execution-story truth.

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
