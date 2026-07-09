# Audit-Driven Development Provenance

This note explains how the RMQ/VerifiedDS repository used AI-assisted,
audit-driven development (ADD). It is public provenance, not a proof object.
The proof artifact is the Lean source, its import roots, and the checked
theorem surface. The axiom scans and reproduction scripts are reviewer and
reproducibility checks around that artifact.

The short version: ADD helped choose targets, find weaknesses, and keep prose
honest. It is not part of the trust base. AI-generated code, worker reports,
chat summaries, and this document do not make a theorem true.

## What ADD Means Here

Audit-driven development is a coordinator-mediated proof-engineering workflow:

1. The project owner and a high-context coordinator choose a theorem-shaped
   target.
2. The coordinator checks whether the work is parallelizable: what is the join
   theorem, what leaves are independent, and what remains lead-thread work.
3. Specialist workers attack scoped proof or construction targets and report
   proof digestion: conceptual change, plain-English meaning, live
   assumptions, and the skeptical next question.
4. The coordinator audits worker outputs against the target, theorem map, docs,
   and verification gates.
5. External audits from model-diverse or low-context reviewers are solicited
   periodically.
6. The coordinator audits those audits against source, theorem statements,
   build results, current docs, and project intent.
7. Accepted objections become new theorem-shaped prompts or documentation
   repairs. Rejected or stale objections are recorded as such.
8. Work is promoted only after theorem-surface review, hygiene checks, artifact
   reproduction or focused gates, and public proof digestion.

This is workflow discipline. It can reduce the chance of overclaiming and find
gaps sooner, but it does not replace Lean's kernel, the checked import graph, or
human/auditor synthesis.

## Coordinator Roles

The word "coordinator" was used loosely in chat titles. In ADD terminology this
project had two true global coordinators: the original high-context RMQ
coordinator and the later high-context RMQ coordinator. They were responsible
for global direction, theorem-shaped prompts, branch/worktree hygiene,
delegation, audit-of-audits synthesis, and deciding what could enter the public
theorem surface.

Other long-lived "coordinator" chats were specialist workers. The proof
digestion coordinator, rank/select coordinator, union-find coordinator, and
similar roles maintained focused spokes or exposition layers. They could be
persistent and valuable without owning global project direction.

## Transcript Evidence Policy

The local transcript exports are provenance evidence for how the work was
produced. They are not committed here as public proof artifacts, and no theorem
depends on them. They are useful as case studies for process failures and
repairs: premature stopping, Goodhart-style checklist satisfaction, audit
synthesis, and final integration pressure.

If transcript material is ever published, it should be sanitized and curated as
process evidence. The public proof artifact remains the Lean source plus the
documented theorem, trust, and reproduction surfaces.

## Trust Base And Non-Trust Base

Proof trust rests on:

- Lean kernel checking of the source imported through roots such as
  `VerifiedDS.lean`, `RMQ/Headlines.lean`, and the relevant `RMQ/Core/...`
  modules;
- the pinned Lean/Std environment and Mathlib-free dependency footprint.

Reviewer confidence and reproducibility are supported by:

- axiom and hygiene checks that reject custom axioms, placeholders, unsafe
  hooks, and other known escape hatches;
- theorem-surface review through `RMQ.Headlines`;
- artifact reproduction scripts and CI gates; and
- human/auditor review of whether the public prose matches the theorem surface.

Trust does not rest on:

- AI agent correctness;
- generated prose;
- chat transcripts;
- the ADD process itself;
- CI alone; or
- claims about compiled Lean execution speed, machine code, or hardware.

## Case Study A: Premature Stopping

Early workers could make real progress and still stop short of the intended
target: adding wrappers, helper lemmas, obstruction notes, or honest caveats
while the named theorem was still open. The process response was to require
invalid endpoints and precise stop conditions.

The norm became: honesty is an invariant, not an endpoint. A worker may report a
checkpoint, but the proof sprint is not complete unless the original theorem
target is closed or a precise formal obstruction shows that the target is
impossible or mis-specified.

## Case Study B: Manifest Theorem Versus Counted Backing

One flat-payload worker produced a real theorem connecting a manifest to
read-store agreement. That theorem was useful, but later audit synthesis found
that it was weaker than the research objection. The intended claim was not only
"there exists a manifest"; it was that actual successful read events in the
final trace are backed by counted payload positions.

The repair sharpened the statement into component-slice and flat-slice
containment, plus successful-read counted-payload backing. The relevant checked
anchors include:

- `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQFlatPayloadSource_component_slice`;
- `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQFlatPayloadReadStore_successful_counted_reads_backed_by_counted_payload`;
- `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_successful_read_events_backed_by_counted_flat_payload`;
- `RMQ.Headlines.succinctRMQFlatPayloadStoreNoSyntheticExecutionStory`;
- `RMQ.Headlines.succinctRMQFinalTraceModelAdequacy`; and
- `RMQ.Headlines.succinctRMQFinalFullModelSoundness`.

The lesson is not that the earlier theorem was fake. It was a real theorem that
satisfied a literal prompt while leaving the intended claim architecture too
weak. ADD treats that as a theorem-targeting failure, not as a reason to distrust
all worker output.

## Case Study C: Structural Readiness Repair

The compact close/LCA path once had public prose that made the clean replay
sound gated by `2^128 <= shape.size`. Later audit and source review corrected
the story: the readiness threshold is the structural theorem
`RMQ.SuccinctClose.concreteBPRelativeRmmInteriorReady_of_size_ge_readyThreshold`,
with
`RMQ.SuccinctClose.concreteBPRelativeRmmInteriorReadyThreshold = 2^15`.
The older `2^128` facts survive only as compatibility/large-regime corollaries.

The route through the all-size structural close/LCA layer is anchored by
`RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory.concreteBPRelativeRmmInteriorAllSizeStructuralRoute_total`.
The later public cost-regime split theorem consumes that readiness fact: the
all-size route-split surface now has the clean fixed corollary `4144`, while
the Ready-threshold theorem states
`RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQFastRegimeQueryCost = 118` once
the `2^15` readiness condition is available. The old `196727` aggregate remains
checked only as a legacy compatibility theorem.

## Case Study D: Proof Digestion

Proof digestion is not a synonym for cleanup prose. In this project it is a
third stage after proof production and proof verification: extract the main
ideas, reorganize checked details into teachable structure, expose assumptions
and pain points, and make the result interrogable by mathematicians and computer
scientists who do not know the local code.

The proof-digestion specialist used an adversarial classroom loop: non-Lean
mathematician, data-structures reader, Lean/library-maintainer skeptic,
cost-model skeptic, AI/provenance skeptic, and grad-student explainer. Remaining
objections were either fixed in prose or listed as live frontiers.

## Case Study E: Final Integration

Worker branches were not accepted merely because they built. Local wins had to
be consumed into the public theorem surface, docs, theorem map, and artifact
gates. The final flat-payload/no-synthetic execution story illustrates this:
component repairs were not publication-ready until they fed the headline
surfaces, including:

- `RMQ.Headlines.listIntSuccinctRMQPaperMainTheorem`;
- `RMQ.Headlines.succinctRMQFinalTraceModelAdequacy`;
- `RMQ.Headlines.succinctRMQFinalFullModelSoundness`;
- `RMQ.Headlines.succinctRMQFinalFullModelSoundnessExactOfFootprintGlobal`; and
- `RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultWithStoreSuccessfulReadsBackedByCountedFlatPayloadOfFootprintGlobal`.

## What ADD Claims

ADD claims that the project used a high-recall, adversarial workflow for finding
claim-path weaknesses and turning accepted objections into theorem-shaped work.
It also claims that the public documentation records the resulting caveats more
plainly than a build log would.

ADD does not claim that the agents were correct, that every audit finding was
right, or that the workflow itself proves anything. External audits are useful
because they are diverse and sometimes hostile; they are also fallible. The
audit-of-audits step is where a critique becomes either a theorem target, a docs
repair, or a rejected/stale finding.

## What Remains Open

The remaining public proof frontiers are theorem-shaped:

1. Stronger uniform word-width/asymptotic side conditions for the
   WordRAM/register-program and rank/select trace surfaces.
2. Concrete family instantiation and flattening work where compressed/FID
   component stores should match the RMQ-style flat-payload backing discipline.
3. Union-find Tarjan amortization: the current scaffold records rank-slack,
   bucket, phase-count, and level-index potential checkpoints, but still hides
   residual/large-credit structure rather than proving the inverse-Ackermann
   theorem.
