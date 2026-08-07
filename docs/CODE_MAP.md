# Code Map

This map is for readers who want to understand the repository as a formalized
artifact without first reading the whole Lean tree. It is an orientation guide,
not a new claim surface: theorem truth lives in Lean declarations checked by
the Lean kernel under the pinned toolchain. The curated scripts are
reproducibility and reviewer checks around that kernel-checked surface.

## First Files To Open

Start with these files in this order:

1. `README.md` for the public story and current headline theorem aliases.
2. `artifact/CLAIMS.md` for claim-to-theorem-to-command traceability.
3. `RMQPaper.lean` for the narrow RMQ paper import root.
4. `RMQ/Headlines/RMQ.lean` for RMQ-only aliases over the construction-heavy
   theorem names.
5. `RMQ/Headlines.lean` for the aggregate alias barrel, including spokes.
6. `RMQ.lean` for the broad RMQ import root.
7. `docs/WHAT_IS_PROVED.md` and `docs/TRUST_AUDIT_PACKET.md` for scope,
   non-claims, and reviewer-facing trust-base details.

## Public Roots

- `RMQPaper.lean` is the reviewer-clean RMQ paper import root. It imports
  `RMQ.Headlines.RMQ` and avoids standalone rank/select public capstones,
  standalone BP-navigation public capstones, union-find, archive roots,
  proposal/legacy/compat barrels, obstruction modules, and old implementation
  roots.
- `RMQ.lean` is the flagship import root for the active RMQ stack: reference
  semantics, RMQ/LCA reductions, concrete implementations, succinct RMQ,
  lower bounds, model layers, and headline aliases.
- `RMQ/Headlines/RMQ.lean` is the RMQ-only citable alias layer used by the
  paper root. `RMQ/Headlines.lean` re-exports it and adds standalone
  rank/select and BP-navigation aliases for the full repository.
- `RMQExamples.lean` and `RMQExamples/` are small downstream-facing import and
  example checks. They are useful smoke tests for public roots.
- `RMQHub.lean` exposes reusable model infrastructure without importing the RMQ
  backend stack.
- `RMQRankSelect.lean`, `RMQBPNavigation.lean`, and `RMQUnionFind.lean` are the
  current family roots for the rank/select, balanced-parentheses navigation,
  and union-find spokes.
- `VerifiedDS.lean` and `VerifiedDS/` are thin facade roots over those public
  roots. The canonical theorem names still live under `RMQ`, `RMQ.Headlines`,
  `RMQ.RankSelect`, `RMQ.BPNavigation`, and `RMQ.UnionFind`.
- `RMQArchive.lean` is an optional archive root. It keeps retired or historical
  surfaces checked without making `import RMQ` depend on them.

## Final Succinct RMQ Spine

The public succinct RMQ result is intentionally split across a construction
spine and a model-adequacy spine.

- `RMQ/Core/SuccinctFinal.lean` builds the BP-native succinct RMQ construction:
  payload accounting, exactness, modeled cost, and the main
  `builtGenericSparseExceptionBPNativeSuccinctRMQFamily_*` theorem family.
- `RMQ/Core/SuccinctFinalRAM.lean` is the compatibility root and
  implementation-heavy bridge from the final costed query to interpreted and
  traced `WordRAM` executions. It now keeps the whole-query interpreter,
  traced execution-story packets, bounded trace events, no-synthetic execution
  story, and fast-regime cost theorem while importing the focused RAM split
  modules below.
- `RMQ/Core/SuccinctFinal/RAM/Segments.lean` contains the concrete final RAM
  segment numbering and canonical global `WordRAM.ReadStore`.
- `RMQ/Core/SuccinctFinal/RAM/FlatPayload.lean` contains the query-independent
  flat payload layout, segment/source/backing manifest, flat read store, and
  successful-read backing predicates used by the final execution story.
- `RMQ/Core/SuccinctFinalStoreParam.lean` is the supplied-store replay layer.
  It proves that leaves and the whole final query can be evaluated against an
  explicit `WordRAM.ReadStore`, with read events reporting that store and with
  footprint/store-parametricity theorems.
- `RMQ/Core/SuccinctFinalModelAdequacy.lean` packages existing final-query
  theorem surfaces into reviewer-facing records such as
  `ConcreteBPNativeSuccinctRMQFinalTraceModelAdequacy`,
  `ConcreteBPNativeSuccinctRMQFinalSuppliedStoreAdequacy`, and
  `ConcreteBPNativeSuccinctRMQFinalFullModelSoundness`.
- `RMQ/Core/SuccinctFinalSemanticProvenanceAdequacy.lean` defines the proof-only,
  non-parameterized W19 reviewer-manifest semantic packet. It imports the
  auditable small/long/sparse reachability witnesses and collects counted-source
  and shared-BP reachability, the checked positive-to-mutation bridge, and
  fresh-source rejection without pretending they concern a current query.
- `RMQ/Core/SuccinctRMQClassic.lean` is the ordinary `List Int` front door. It
  specializes the BP-native construction to a reader-facing RMQ input list,
  half-open queries, and leftmost ties.
- `RMQ/Core/SuccinctRMQClassicProvenance.lean` is the proof-only import seam for
  the global packet. It intentionally defines no `xs`/`left`/`right`/
  `ValidRange` wrapper for global liveness. The split keeps symbolic witness
  modules out of the native validator/cost-harness link closure without
  changing their genuine `SuccinctRMQClassic` execution path.
- `RMQ/Headlines/RMQ.lean` exposes the RMQ-only short public names, including
  `succinctRMQListIntTwoNPlusOConstantQuery`,
  `listIntSuccinctRMQFlatPayloadStoreNoSyntheticExecutionStory`,
  `listIntSuccinctRMQPaperMainTheorem`,
  `succinctRMQReviewerMachineWellFormed`,
  `succinctRMQReviewerMachineRequiredFacts`,
  `listIntSuccinctRMQReviewerNativeMachineAdequacy`,
  `succinctRMQCanonicalReviewerPayloadGlobalWordTraceTwoSidedProfile`,
  `succinctRMQFlatPayloadStoreNoSyntheticExecutionStory`, and
  `succinctRMQFinalFullModelSoundness`. `RMQ/Headlines/RMQCompatibility.lean`
  contains explicitly labeled historical query profiles. `RMQ/Headlines.lean`
  re-exports both modules and adds spoke aliases; `RMQPaper` imports only the
  canonical RMQ module.

The model-adequacy theorem spine to look for is:

- `concreteBPNativeSuccinctRMQWholeQueryGlobalWordTrace_execution_story`
- `concreteBPNativeSuccinctRMQWholeQueryGlobalWordTrace_bounded_execution_story`
- `concreteBPNativeSuccinctRMQWholeQueryGlobalWordTrace_noSynthetic_execution_story`
- `concreteBPNativeSuccinctRMQWholeQueryFlatPayloadStore_noSynthetic_execution_story`
- `concreteBPNativeSuccinctRMQFinalTraceModelAdequacy`
- `concreteBPNativeSuccinctRMQReviewerMachineWellFormed`
- `ConcreteBPNativeSuccinctRMQReviewerMachineWellFormed.requiredFacts`
- `concreteBPNativeSuccinctRMQReviewerMachineRequiredFacts`
- `SuccinctClassic.listIntSuccinctRMQReviewerNativeMachineAdequacy`
- `concreteBPNativeSuccinctRMQFinalSuppliedStoreAdequacy`
- `concreteBPNativeSuccinctRMQFinalFullModelSoundness`

These are model-scoped Lean statements. They do not claim anything about the
compiled runtime behavior of Lean programs.

## Proof-Core Clusters

The files below are dense by design: they carry construction details, model
bridges, and store/accounting lemmas that public aliases summarize.

- `RMQ/Core/GenericSelect/` is the split generic select implementation used by
  the close-select path. `GenericSelect/RAM.lean` and
  `GenericSelect/RAMStoreParam.lean` are the `WordRAM` and supplied-store
  bridges.
- `RMQ/Core/SuccinctSelect/` contains the select/rank construction and the
  close-select components consumed by the final RMQ construction.
- `RMQ/Core/SuccinctClose/` contains compact close/LCA, endpoint fringe,
  interior-candidate, and relative-rmM macro components. The store-parametric
  close/LCA bridge is in
  `SuccinctClose/RelativeRmmMacro/ConcreteDirectoryRAMStoreParam.lean`.
- `RMQ/Core/WordRAM.lean`, `RMQ/Core/WordRAM/Register.lean`, and
  `RMQ/Core/WordRAM/ReadStoreEval.lean` define the trace and read-store model
  used by the execution-story theorems.
- `RMQ/Core/SuccinctSpace/` contains the older succinct-space model layers and
  BP/rank-select/RAM bridge infrastructure still consumed by the active proof.
- `RMQ/Core/RankSelectPublic*.lean` and `RMQ/Core/RankSelectCompressed*/`
  support the standalone rank/select public family.
- `RMQ/Core/UnionFind*.lean` is the union-find spoke, with forest refinement
  and amortized-analysis checkpoints separate from the RMQ theorem spine.

## Compatibility And Archive

Several files are intentionally compatibility shims rather than new proof
frontiers:

- `RMQ/Core/SuccinctCloseProposal.lean`
- `RMQ/Core/GenericSelectBPCompat.lean`
- `RMQ/Core/GenericSelect/SuccinctSelectLegacyNames.lean`

They are retained so older downstream imports and names remain checked. New
in-repository code should import the canonical split modules instead.

Deleted on 2026-08-07 in `def5cb3` after a reverse-dependency census found them
unreachable from every `lean_lib` root and every `lean_exe`: the eight
`SuccinctRankProposal`, `SuccinctSelectProposal`, `GenericSelectBuilder`,
`GenericSelectParams`, `GenericSelectPrimitives`, `GenericSelectLegacy`,
`GenericSelect/LegacyNames` and `GenericSelect/PrimitiveLegacyNames` modules.
They are listed here only so that a reader of an older revision of this file
knows what became of them; the paths no longer exist.

`scripts/shim_lint.ps1` is the guardrail for this boundary. It scans live roots,
docs, examples, and scripts to prevent stale proposal shims and old flat
GenericSelect compatibility imports from re-entering active imports.

The paper root has its own measured closure in `docs/RMQ_IMPORT_CLOSURE.md`.
In the current worktree, `RMQPaper` imports 126 workspace Lean files and 105607
Lean LOC, with no modules matching archive/proposal/legacy/compat/obstruction
or standalone public-spoke patterns. The larger whole-workspace source count
belongs to the checked data-structure testbed, not the minimal paper root.

The optional archive root is `RMQArchive.lean`, which imports `RMQ.Archive`.
Archive files are checked historical/retired surfaces, not the recommended
starting point for the current proof spine.

## Examples And Validation

- `RMQExamples.lean` and `RMQExamples/` are checked examples for external
  import surfaces.
- `RMQ/Validation/SuccinctClassic.lean` contains executable validation for the
  classic public succinct RMQ API.
- `RMQ/Validation/SuccinctClassicCostHarness.lean` contains a reviewer-facing
  executable report for deterministic `SuccinctClassic.buildPayload` and
  `SuccinctClassic.queryCosted` runs, including modeled trace/event costs.

Validation and examples are helpful for readers and reviewers, but validation
is explicitly not part of the proof trust base. The proof trust base is the
Lean kernel checking theorem declarations under the pinned toolchain. The
repository's hygiene scans and axiom scripts are reproducibility and reviewer
checks; they are not additional trusted proof machinery.
