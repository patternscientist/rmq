# LB-1 fresh-blind exact-commit audit prompt draft

Readiness: DRAFT_NOT_READY.
Target commit: `<LB1_EXACT_CANDIDATE_SHA_PENDING_FREEZE>`.
Do not launch this draft or substitute the current HEAD implicitly.

## Coordinator launch metadata (outside the pasted auditor prompt)

The coordinator-side authoring preflight passed at governance
`0e6a00f654abc64f8b68988fa9675b9a839dca2f`, checkout
`0bbbe8ca4a937bc9782b2f7c5cc5419faa1a75a2`, requiring
`rmq-audit-prompt` with the actual runtime catalog
`rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint`. The canonical skill,
`docs/internal/templates/AUDIT_PROMPT.md`, `docs/internal/AUDIT_PROTOCOL.md`,
and `docs/internal/CLAIM_DRIFT_POLICY.md` were read. This authoring check is
not the future auditor's no-role preflight.

The draft is for a new low-history session in fresh blind delta mode. Supply
only the auditor prompt below, the exact allowed source packet, and neutral
command evidence. Do not fork the implementation/review conversation into the
auditor. Model selection and launch mechanics remain coordinator metadata.

Before marking a launch prompt ready:

1. Replace every occurrence of
   `<LB1_EXACT_CANDIDATE_SHA_PENDING_FREEZE>` with the one full 40-character
   candidate commit. Verify that it exists, contains the complete requested
   source/registry/public delta, descends from the exact governance and
   contract-freeze commits, and is the intended source target. Do not infer
   source readiness from a commit message or from this draft.
2. Record the exact base-to-target path/stat manifest without worker commit
   narratives. Verify the v3 registry still has 63 proof/control cases and six
   runtime cases, with literal expected verdicts/surfaces. A changed registry
   requires deliberate prompt/evidence reconciliation, not silently changing
   the frozen requirement count or accepting a subset.
3. Establish the future auditor's actual nonempty runtime RMQ catalog and run
   launch preflight for intentional no-role audit mode. Do not inject or name
   a proof/coordinator/prompt-authoring role as the auditor's required skill.
   The source target and governance checkout remain separate identities.
4. Provide a neutral exact-target evidence manifest as runs finish: command,
   source/artifact hashes, target commit, phase, environment/toolchain, owned
   deadline, duration, exit/stdout/stderr, registry expected/executed IDs, and
   restoration results. Do not insert prior findings or verdict narratives.
   Missing execution evidence may remain pending at a source-only launch;
   the auditor must then keep those rows open and withhold a final positive
   audit verdict until it is delivered and assessed.
5. Confirm ignored staging path `.lake/lb1-final-audit/REPORT.md`, the active
   replay owner, and the separate exclusive-grant rule for all Lean/Lake work.
   The auditor gets no implied permission to run the coordinator's campaign
   or aggregate gate. Verify `.lake/lb1-final-audit/` is actually ignored.
6. Run the coordinator's prompt launch preflight after substitution. Only
   then change readiness to READY_TO_SEND. This draft has no target-commit
   preflight or acceptance verdict.

The stock packet generator was inspected but not run: its HEAD-oriented,
whole-log and whole-process-document capture is inappropriate for this exact
target and blind allowlist. Assemble the packet from immutable blobs and
neutral records instead. This draft alone does not claim a generated packet.

The explicit task write-scope override places the durable audit report in the
LB-1 area, rather than the general `docs/internal/audit_reports/` convention
in the template/protocol. The auditor writes only the ignored staged report
while replay requires a clean tracked tree. After replay restores and exits,
the coordinator copies that report to
`docs/internal/extensions/lb1/FINAL_AUDIT.md` and performs report-sensitive
checks on the resulting durable tree. This path/process override changes no
semantic requirement or audit independence obligation.

---

## Auditor prompt begins

Auditor handle: LB1-BLIND.
Requested title: `(LB1-BLIND) Audit packed-allocation lower-bound composition`.
Mode: FRESH BLIND DELTA.
Permission: report-only; source, compiled artifacts, Git state and other
workers' files are read-only.

Audit the exact LB-1 target against its complete frozen contract. Attempt to
falsify both the literal propositions and the intended same-allocation model.
Produce an independent ID-by-ID reconstruction and findings grounded in exact
source or actual command evidence. A declaration inventory, previous green
build, or valuable partial result cannot substitute for this audit.

### Identity, scope and resource ownership

- Source base and workflow governance:
  `0e6a00f654abc64f8b68988fa9675b9a839dca2f`.
- Exact source target: `<LB1_EXACT_CANDIDATE_SHA_PENDING_FREEZE>`.
- Frozen-contract checkpoint:
  `0bbbe8ca4a937bc9782b2f7c5cc5419faa1a75a2`.
- Branch: `codex/lb-1-variable-payload`.
- Governed checkout: `C:/Users/poin/.codex/worktrees/2270/RMQ`.
- Active extension: LB-1, match the information lower bound to the actual PQ1
  packed allocation. The intent is an additive observed-length encoding and
  same-object lower/upper/machine comparison. The original roadmap's matching
  lower/upper and explicit machine-model aims supply context; the assigned
  extension contract below defines this audit's full endpoint.
- Only auditor report path:
  `C:/Users/poin/.codex/worktrees/2270/RMQ/.lake/lb1-final-audit/REPORT.md`.
  Coordinator's later durable destination:
  `docs/internal/extensions/lb1/FINAL_AUDIT.md`.

You are not alone in this worktree. A coordinator-owned replay can temporarily
change working source and oleans. Read target source using `git show
<LB1_EXACT_CANDIDATE_SHA_PENDING_FREEZE>:<path>`, not ordinary working-file
reads. Use the exact base and target for diffs; do not substitute branch tips,
HEAD, mutable source hashes, or live oleans for the audited commit. The fixed
governance checkout is used for tooling/preflight and is conceptually distinct
from the source target being reviewed, even when both refs are ancestors of
the same checkout. Never check out, reset, clean, stash, stage or commit here.

You may inspect immutable source while replay runs. Do not run Lean, Lake,
runtime validation, semantic probes, a mutating lane replay, or a competing
build until the coordinator explicitly grants a separate exclusive slot and
names the permitted commands/cache. Permission to read evidence is not that
grant. The coordinator owns the full replay and aggregate/host gate. Do not
run `lake build`, `scripts/gate.ps1`, or any fallback aggregate. A requested
additional counterfactual that requires source edits must be specified to the
coordinator as exact P/Q predicates and a bounded test; do not make the edit
yourself. Scratch/process outputs, if later authorized, stay under the named
ignored audit scratch directory. During the campaign, make no tracked writes.

Stage findings in the one ignored report. Use status `INCOMPLETE` while
required execution evidence or permissions remain pending. Continue useful
source inspection meanwhile; do not label an unexecuted check passed, or call
the whole audit complete because its source phase finished. After replay
finishes and restoration is verified, the coordinator copies the report to
the durable LB-1 path and runs the report-sensitive final-tree checks. That
copy does not change your audited source target or transfer acceptance
authority to you.

### Independence and required no-role preflight

Do not read worker `REPORT.md`, `COUNT_PROOF_NOTES.md`, `EVIDENCE_PLAN.md`,
`CONTRACT_REVIEW.md`, `REPLAY_REVIEW.md`, `SOURCE_RISK_REVIEW.md`, other worker
completion narratives, prior audit reports/verdicts, chat transcripts, or
commit/tag annotations containing them. Do not follow links to those records
from allowed files. Do not recursively read the LB-1 directory as a packet.
Public documentation addenda are claims to audit, not prior verdict evidence;
read only their scoped LB-1 changed material and the source context needed to
interpret it. If accidental verdict contamination occurs, stop and report the
contamination so the coordinator can choose a fresh audit session.

Read `AGENTS.md`, `docs/internal/AUDIT_PROTOCOL.md`, and the claim policy from
the declared governing/target refs as appropriate. For this intentional
audit-worker role, applicable required project skills are **NONE**. Inventory
the RMQ skills actually exposed in your own runtime catalog; report that
nonempty list. Run the canonical preflight from the governed checkout with:

```powershell
& scripts/project_skill_preflight.ps1 `
  -GovernanceRef 0e6a00f654abc64f8b68988fa9675b9a839dca2f `
  -AllowNoRequiredSkills `
  -RuntimeProjectSkills '<your actual nonempty runtime RMQ catalog>'
```

Replace the descriptive runtime argument from your actual catalog, not from
an expected list. Omit `-RequiredSkills` entirely. Do not nominate
`rmq-audit-prompt`, `rmq-proof-sprint`, or `rmq-coordinator` merely to make this
audit's preflight pass: those are different roles. Having such skills exposed
does not make one an applicable audit role. This explicit no-role mode still
requires the complete canonical checkout, governance ancestry, and actual
nonempty runtime catalog. On a preflight mismatch, stop before substantive
audit work and report cwd, checkout HEAD, governance, expected/actual catalog,
and missing/stale names. Do not continue best-effort or borrow another role.

### Exact source packet and allowed context

Read these frozen contract sources, including every requirement in full:

- `docs/internal/extensions/lb1/FROZEN_REQUIREMENTS.md`;
- `docs/internal/extensions/lb1/FROZEN_INVARIANTS.md`;
- `docs/internal/extensions/lb1/ACCEPTANCE_MATRIX.md`;
- `docs/internal/extensions/lb1/CONTRACT.md`.

Use the contract checkpoint to validate frozen row identity, then the exact
candidate for its source and append-only evidence indices. Enumerate all 29
actual frozen IDs verbatim. Evidence may reside in permitted append-only
ledgers or neutral command artifacts. An unchanged `Open` acceptance cell or
evidence's physical placement is not itself a finding. A row closes only if
its exact proposition, consumer, identity, domain and applicable anti-vacuity
evidence do. Do not read withheld narrative ledgers; request their underlying
neutral checked artifact if an allowed index points there.

Primary Lean delta:

- `RMQ/Core/EncodingVariableLowerBound.lean`;
- `RMQ/Core/WordRAM/Packed/AllocationLowerBound.lean`;
- `RMQ/Validation/VariablePayloadLowerBound.lean`.

Lane controls/tooling:

- `scripts/variable_payload_generic_consumer.lean`;
- `scripts/variable_payload_inventory.lean`;
- `scripts/variable_payload_axioms.lean`;
- `scripts/variable_payload_contract_check.ps1`;
- `scripts/variable_payload_build.ps1`;
- `scripts/variable_payload_replay.ps1`;
- `docs/internal/extensions/lb1/REPLAY_REGISTRY.json`;
- actual dependencies of the process runner in `scripts/owned_process_tree.ps1`.

Relevant predecessor source is in `EncodingLowerBound.lean`, Cartesian shape
and lower-bound modules, and `RMQ/Core/WordRAM/Packed/` allocation, primitive,
guard, query-source, query-correctness, query-safety, query-observation and
capstone modules. Follow actual imports and declarations when needed; this
is a delta audit with transitive model applicability, not an instruction to
reaudit unrelated repository history.

Audit changed LB-1 public addenda in `docs/FAMILY_SUMMARY.md` and
`docs/DIGESTION_LOG.md`, and any README change present in the exact diff.
Check the exact diff for all affected public/trust surfaces; do not presume
this hand list excuses an unexamined changed claim. `RMQPaper.lean` and
headline identities are non-migration boundaries to verify. Existing
`docs/WHAT_IS_PROVED.md`, `docs/PAPER_MODEL_ADEQUACY.md`,
`docs/RMQ_IMPORT_CLOSURE.md` and claim-policy data supply model/trust context
only as needed. Claim-policy allowances are auditable source, not authority
that makes a green scan semantically decisive.

Design intent is recorded in DD-20260912-LB1-001 and DD-20260912-LB1-002,
and process ownership in WDD-20260912-LB1-001 and WDD-20260912-LB1-002.
The coordinator may supply only neutral design-choice excerpts from those
entries; omit review narratives, earlier failures/verdicts and assertions of
prior verification. Do not read those entries wholesale when they mix design
with such history. The frozen CONTRACT and actual source remain primary.

### Required semantic reconstruction

Inspect literal theorem types and independently expand the data path. Name
each relevant object and every live guard/quantifier, with exact source
locations at the target. Declaration names alone do not establish any row.

1. Reconstruct `ExactRMQBoundedEncoding n B`'s four fields, the complete
   length-0-through-B universe and exact `2^(B+1)-1` cardinality, finite-shape
   representative injection from valid half-open leftmost answers, and the
   coefficient-correct doubled lower conclusion at `2*(B+1)`. Check n=0 and
   n=1 and input-domain witnesses. Reject fixed/variable-length substitution,
   hidden prefix-free assumptions, supplied injectivity, missing observed
   length, or vacuous query domains.
2. Expand serializer/deserializer definitions on arbitrary finite bounded word
   lists at positive width. Check exact length and inverse/injection, empty
   bits, zero words of different multiplicities, final padding, and width-zero
   exclusion. Establish that `allocationBits xs` serializes every actual
   `buildMemory xs` cell at one n-only width. It must not serialize a sibling
   representative encoding, erase metadata, pad inputs to B, or assume fixed
   allocation length across all size-n shapes.
3. Expand the actual decoder to its executable arguments and captured data.
   Trace reconstructed numeric words into `queryNat`, the fixed program,
   initial registers, primitive loads and halted result. Check there is no
   captured xs, supplied shape/answer, uncounted input-dependent advice, or
   proof-carried routing oracle. A function signature alone cannot inspect
   closure contents: separately check the one fixed decoder's universal
   size-n exactness and the canonical body's actual dependency graph. Test
   permitted n-only advice and rejected input/shape advice using the same
   accepted exactness predicate and quantifiers.
4. Reconstruct same-shape sharing and injectivity on `shapesOfSize n`.
   Value-list injectivity is not an assigned claim. Equal bitstrings must
   yield equal valid-window answers for the relevant representatives. Do not
   infer it from a field that merely assumes injection.
5. Expand `UniformAllocationBudget n B` and both arbitrary-B and canonical
   encoding instances. Prove the lower bound quantifies over one budget valid
   for every size-n input. Trace its generic theorem application through the
   actual allocation object. Relate the actual per-input upper capacity and
   `LittleOLinear allocationRho` to that same allocation. Reject an individual
   input lower claim, canonical-budget substitution for arbitrary B, or a
   separately true numerical inequality about a different encoding.
6. Inspect `PackedAllocationOptimality`,
   `ReconstructedPackedQueryCapstone`, their producers, `publicContract`,
   `composedConsumer`, and `canonicalEncodingConsumer`. Reconstruct all
   16 optimality and 33 recovered-machine expected field propositions, not
   just record membership. All 49 `checkO01..checkO16` and
   `checkM01..checkM33` consumers must independently require literal types and
   the intended public producer. Include definition pins and generic typed
   consumers. A public proposition changed to True or a sibling field must
   not remain sufficient merely because an initializer or axiom print exists.
7. Expand exact memory recovery and full run identity at arbitrary fuel.
   Check every machine claim applies to the deserialized-memory consumer:
   capacity, code/scratch, words, addresses/sentinel, all instruction operands,
   initial/final/prefix states, actual result, halt, invalid guard, categories,
   positional reads, ordered refinement, supplied-memory agreement, no failed
   valid loads, and width scaling. Preserve all representable-endpoint guards
   of the raw machine. The total Nat wrapper's invalid-query behavior does
   not remove those premises. Compare guards for every conjoined execution.
8. Trace returned values and routing backwards to actual charged reads, not
   merely to a changed log. Inspect `execute`, run transitions and result
   projections. Distinguish event membership from occurrence position,
   multiplicity, producing instruction, prefix pre-state, local occurrence
   and invocation arguments. Require the counted pre-execution store and
   complete-run supplied-memory agreement. Check every physical segment and
   dead/sentinel address under the one query-independent n-linked word width.
   Identify any synthetic/decorative or oracle-dependent evidence.
9. Keep bit payload, proof fields, primitive model transitions, mathematical
   bit conversion, preprocessing, outer argument/result conversion, code,
   scratch and Lean runtime measurements separate. LB-1 adds no charged
   serialization/deserialization time theorem. Inspect whether its scalar
   primitive model is stated honestly. An at-most cost theorem does not prove
   attainment/tightness or rule out a smaller upper bound.

### Frozen rows (exact IDs; verbatim text in the required source blobs)

REQ-LB-COUNT; REQ-LB-PQ1; REQ-LB-MODEL; REQ-LB-CONSUMER;
CHK-LB-CONTROLS; REPLAY-EXACT-REGISTRY; REPLAY-SELECTOR-NONVACUITY;
REPLAY-SUBPROCESS-DEADLINE; INV-STORE-IDENTITY; INV-VALUE-DEPENDENCY;
INV-SEMANTIC-NONVACUITY; INV-TRACE-EXECUTION; INV-STORE-AGREEMENT;
INV-READ-BACKING; INV-WORD-WIDTH; INV-ADDRESS-WIDTH;
INV-INSTRUCTION-ATOMICITY; INV-PROGRAM-ACCOUNTING;
INV-ORACLE-INDEPENDENCE; INV-VALIDATION-REACH; INV-ALL-SIZE;
INV-PROOF-SEPARATION; INV-NO-SYNTHETIC; INV-CATEGORY-SEPARATION;
INV-PUBLIC-COMPOSITION; INV-CERTIFICATE-ANTI-BYPASS;
INV-MUTATION-REPRODUCIBILITY; INV-GLOBAL-PHYSICAL-MACHINE;
INV-WIDTH-SCALING.

The list is 5 assigned theorem/control rows, 3 replay rows, and 21 inherited
invariants. Copy each row's exact requirement from the frozen source into
your reconstructed map. A count-only summary is insufficient. No row can be
removed, narrowed, renamed or declared optional by worker prose. For every
claimed residual/out-of-scope item, map it independently to the frozen rows.

### Adversarial replay and evidence audit

Inspect the version-3 JSON registry and independent literal runner registry.
Require exactly 63 proof/control IDs and six runtime IDs, each unique and
nonempty, with exact expected verdict and failing/accepting surface. Verify
the final executed list equals that ordered expected list; historical
registries or focused runs are not the full current campaign. Inspect every
mutation's concrete source transformation, declaration-span calculation,
artifact replacement and restore path. Resource exhaustion, import failures,
timeouts or diagnostics outside the required declaration are not semantic
rejections.

For all 49 mandatory field weakenings, require modified producer compilation
to pass with its replacement olean, followed by failure inside its own exact
typed consumer. Separately audit explicit memory/read-field deletion, sibling
memory/run/budget substitution and empty-only exactness. For each, quote the
accepted predicate P and mutated predicate Q, including guards, objects and
quantifiers; require predicate identity or a checked P -> Q relation when a
negative control is claimed to test a positive condition. Do not count a
change to prose, a diagnostic label, or an unrelated declaration as that test.

Audit public-proposition and generic-lower-proposition attacks against their
typed consumers, generic exactness deletion, null and wrong decoders, and
lost serializer length against their actual named failure surfaces. In
particular distinguish producer-rejection controls from the 49
producer-pass/consumer-fail obligations. Require both unchanged baseline
acceptance and the altered proof-only wrapper's expected acceptance: its
modified producer, unchanged exact field inventory and full typed consumer
must all pass. This proves the checker permits deliberately non-load-bearing
packet changes while rejecting required public dependency changes.

Use the existing registry attacks as actual counterfactual evidence. For any
remaining applicable inherited semantic-liveness/ownership obligation, test
whether dead sources, missing operational sources, a tautological predicate,
or a consumer label without an evaluator edge could survive. Identify the
exact checked theorem/control that rejects each applicable construction.
Where not applicable to this additive adapter, give a model-specific reason
grounded in the unchanged operational construction; do not use a blanket
waiver. Distinguish component may-read, successful read, top-level valid-query
reachability and actual emitted occurrences.

Audit runtime validation's actual reach to `allocationBits`, deserialization
and `allocationDecoder`. Fixtures must be constructed after startup/selection;
expected values must come from an independent specification or connected
theorem rather than the implementation being tested. The exact six cases are
R01-EMPTY, R02-SINGLETON, R03-LEFTMOST, R04-ZERO-LENGTH, R05-ZERO-WORDS,
and R06-SAME-SHAPE. Check omitted, valid, empty, whitespace, malformed and
unknown selectors and environment/CLI conflict behavior. A selected run must
execute its exact nonempty expected set. Startup/list and one known selector
must precede the full campaign; a --list pass is not query execution evidence.

Audit bounded subprocess ownership, deadlines, actual exit/stdout/stderr,
resource-failure classification, and absence of surviving owned children.
Verify finally restoration of every mutated source and overwritten olean by
exact bytes, plus worktree/index/untracked checks after cases and at exit.
The auditor's ignored report must not compromise that discipline. Windows
owned-job evidence does not establish POSIX process behavior. A condition not
created or observed on the host remains uncovered/inconclusive.

Audit the frozen-row checker against the exact contract-checkpoint Git blob:
strict UTF-8 decoding, complete row delimiters, all 29 literal IDs, rejection
of missing/duplicate IDs, exact row bytes without whitespace/Unicode
normalization, and recognizable-mojibake rejection. Verify unchanged acceptance
and whitespace/missing/duplicate/Unicode/invalid-UTF8 controls use that same
checker. A row count or successful locale round trip is insufficient.

### Checks and phase-qualified evidence

Use immutable Git operations for source identity: exact commit resolution,
ancestry from base/governance/contract checkpoint, path/stat diff for
base..target, `git diff --check base..target`, and exact-blob reads. During
active replay, live `git status` is only a phase observation; temporary runner
mutations are not corruption of the immutable target. Do not read full
commit-message history or annotations to obtain identity.

The following checks are required evidence surfaces. The coordinator supplies
neutral raw outcomes tied to the exact source target, or explicitly grants a
separate owned slot for a named narrow rerun. Do not start them under the
initial report-only/source-phase permission:

- Pinned Lean 4.22.0/toolchain and dependency startup; narrow explicit import
  checks for the three changed modules and the generic typed consumer, using
  `scripts/variable_payload_build.ps1` where appropriate. No full-build fallback.
- `scripts/variable_payload_inventory.lean`: actual metadata for literal
  4/16/33 ordered parent-free structures and all its positive/negative name,
  default, indentation, ordering, absence and parent controls.
- `scripts/variable_payload_axioms.lean`: all 20 explicit dependency outputs,
  including bounded cardinality, shape injection/count/lower, serializer
  inverse/injection, recovered memory/exactness, arbitrary/canonical allocation
  count/lower/upper, run identity, both capstones, and public/composed consumers.
  Reconstruct the trust base, not just the output count. Compare to Lean/Std
  plus omega expectations; no Mathlib or unapproved trust shortcut is licensed.
- `scripts/variable_payload_contract_check.ps1` and its exact frozen-row
  evidence, before expensive final verification.
- `scripts/variable_payload_replay.ps1 -RegistryOnly`,
  `-SelectorBoundaryOnly`, `-DiagnosticOnly`, `-DeadlineOnly` and
  `-RuntimeOnly`, plus the full unselected v3 registry. Inspect actual mode
  behavior: do not infer that one focused mode ran another. Full semantic
  replay and restoration remain coordinator-owned.
- Trust scans over exact target source: prohibited proof/implementation
  escape tokens and Mathlib imports; also `native_decide` and
  `Lean.ofReduceBool`. Explain every relevant hit by declaration and trust
  reach. `#print axioms` does not replace public dependency mutations.
- Exact delta whitespace; strict claim drift including public addenda;
  applicable strict design-decision check with exact base and target. Broad
  aggregate certification remains the coordinator's host-slot duty.

Reconcile neutral supplied evidence with the exact target's source/artifact
hashes, commands and phases. Cache reuse must be justified by the keyed
dependencies rather than a nearby filename or green predecessor build. A
replay run made while the source/registry differed does not automatically
certify this target. A fresh source audit is possible before final execution
evidence arrives, but a final positive audit verdict is not.

After the report text is complete, the report-containing durable tree must
receive strict claim drift with process records, applicable strict design
checking, and whitespace checks. The coordinator performs them after copying
the ignored report; record the resulting evidence before calling that durable
report certified. A pre-report pass does not certify the report artifact.
Paraphrase prohibited current-claim examples or use existing justified narrow
quotation contexts; do not alter claim-policy allowances.

### Boundaries and rejection criteria

This audit does not assign a new query algorithm, native/compiler backend,
preprocessing-time proof, cell-probe tradeoff, paper rewrite, alias migration,
new asymptotic theorem beyond the frozen contract, branch integration, push,
cleanup, or aggregate execution to you. These resource and non-goal boundaries
do not waive any of the 29 frozen source, semantic, runtime, trust or
reproducibility requirements. Assess inherited machine invariants on this
exact recovered-memory consumer, including the relevant predecessor semantics.

Block a positive verdict for missing/false mandatory propositions, wrong
object/quantifier/guard composition, hidden advice/storage/oracles, synthetic
execution claims, uncontrolled trust changes, required controls with wrong
failure surfaces, missing current-registry cases, absent restoration evidence,
or unprovided required execution outcomes. Explain whether an issue is a
source defect, a demonstrated check failure, or a pending evidence condition.
Do not turn an upper bound into tightness, a subset into an exhaustive run,
a model theorem into host performance, or missing permission into a pass.

### Report required

Write the single ignored REPORT.md with findings first, P0 through P3, citing
exact target file/line, declaration/type and command evidence. Include:

1. Audit identity, mode, base/target/governance, actual runtime no-role
   preflight, allowed scope, source snapshots and independence statement.
2. Phase-qualified verdict: `INCOMPLETE` while required evidence is pending;
   after all evidence is available, use the protocol's merge-ready,
   merge-ready with follow-up, blocked, or needs-another-worker-pass vocabulary.
   You do not record coordinator `ACCEPTED` or integrate anything.
3. P0/P1/P2/P3 findings with exact P/Q predicates, guards, identity/data paths,
   observed behavior and the smallest repair or additional evidence needed.
4. All 29 frozen IDs verbatim, each with the exact requirement, proposition,
   consumer, same-object chain, anti-vacuity evidence and independent
   disposition. Do not replace this by a count or a worker's chosen endpoint.
5. Evidence tiers for positive claims: kernel theorem; explicit model/store/
   trace theorem; executable validation; reproducible artifact; process record.
   Cite source and command evidence for each substantive positive assertion.
6. Your stale/rejected objections, with source reasons. No previous auditor's
   verdict is available or needed to construct this section.
7. Commands run, supplied outcomes independently audited, commands skipped and
   why, platform/resource limits, exact 63+6 expected/executed coverage,
   byte restoration, and remaining evidence gaps.
8. Letter-and-spirit roadmap alignment, short proof digestion (conceptual
   change, plain-English meaning, live assumptions and the next skeptical
   question), and the best next concrete target. Do not reclassify a required
   gap as optional hardening based on worker prose.
9. Ignored staging path, planned durable LB-1 path, and report-sensitive
   final-tree check status. Do not claim that the future copy or its checks
   have already happened.

Return the staged report path and concise findings/readiness summary to the
coordinator. Preserve source/read-only boundaries throughout.

## Auditor prompt ends
