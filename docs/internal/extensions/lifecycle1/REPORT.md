Status: CANDIDATE_COMPLETE
I found no assigned or inherited acceptance criterion unmet; coordinator acceptance is still required.

# LIFE-1 continuous packed lifecycle candidate

## Identity and delivery

- Worker/task: LIFE-1, `(LIFE-1) Implement continuous succinct construction and queries`; task `01a0c12b-15fd-7cf1-898e-635805e1e0c7`.
- Worktree: `C:/Users/poin/.codex/worktrees/8941/RMQ`.
- Branch: `codex/life-1-continuous-packed-lifecycle`.
- Exact base: `bf31f983205175481fcb659caa4dfb70ef43e361`.
- Governance: `7b227c49ef2ec044b702126cc41c9add847eed01`; the required `rmq-proof-sprint` skill and the actual three-skill runtime catalog passed preflight before implementation.
- Implementation/source commit: 299ec6527ca2fbcf73cfc34e9de75f4a1f34140c.
- Delivery identity: this report is committed in a subsequent evidence-only closing commit. That commit's exact hash, this report's SHA-256 and byte length, and the post-commit check receipt are supplied in the submission message and `.lake/lifecycle-final/delivery.json`. This avoids claiming that a report can contain the hash of its own enclosing commit. The closing commit changes documentation/evidence only; source identity remains the implementation commit and `SOURCE_MANIFEST.json`.

This is a local unpublished candidate. The independent native consuming boundary, complete repository aggregate, fresh blind audit of the exact submitted commit, and coordinator acceptance remain the explicitly separate campaign consumers. No assigned local implementation row is delegated to them. There was no push, published integration, branch retirement, toolchain change, or predecessor policy change.

## Result and exact public interface

The new machine executes the existing builder body, derives its output pointer and metadata from actual scalar operations, copies the constructed cells forward into the retained arena, releases the old suffix and comparison resources, and enters the compact query through charged initialization. The complete run starts at the builder PC and ends with the first query answer. Later requests consume only the retained owner and two represented endpoint words through four charged boundary events.

In namespace `RMQ.SuccinctFinal.PackedLifecycle`, the public theorem is:

```lean
continuousConstructionQuery_holds
    (model : InputModel) (xs : List Int) (left right : Nat)
    (domain : InputDomain model xs)
    (hl : left < 2 ^ wordWidth xs.length)
    (hr : right < 2 ^ wordWidth xs.length) :
    ContinuousConstructionQuery model xs left right
```

The word form uses the existing `PackedConstruction.InputFits (wordWidth xs.length) xs`; the comparison form quantifies arbitrary `List Int` with only represented endpoint premises. No expected answer, ready owner, canonical memory, or capstone witness is an input premise. Valid half-open ranges halt with `scanWindow xs left (right-left)+1` and its `LeftmostArgMin` proof; invalid represented ranges halt with packet zero. The additive headline is `RMQ.Headlines.succinctRMQContinuousLifecycle`.

The seven public fields concern the same `Continuous.continuousRun`, `Layout.program`, `wordWidth`, constructed store and owner:

1. `construction`: an actual `BuildStage` producer and body trace, completed scalar finalization, linear work, exact concatenation with service, and an indexed complete compact-query suffix after actual setup.
2. `retained`: canonical final memory and zero key resources, the reference answer packet, and the construction-plus-service bound.
3. `safety`: every actual prefix satisfies the numeric, extent, finite-bank and key-resource profile, and every actual instruction transition satisfies its strong safety predicate.
4. `physical`: one code/register/control/arena translation supplies every actual prefix image, positional read backing and widths, and the actual fetched opcode/operand words from counted code. Failed logical accesses are guarded before a physical fetch; generic failed-load lemmas preserve that distinction.
5. `executable`: the finite owner and optional observed run refine the same abstract run, readiness and literal empty key arrays are derived, and capacity counts the actual owner's memory and register lengths plus actual encoded code and controls.
6. `reusable`: any ready halted owner accepts represented subsequent endpoints, restores readiness, returns the reference packet, preserves its exact memory array, and has full boundary/service trace, safety, cost and capacity facts.
7. `uniform`: the same retained remainder is little-o, the same query-independent word width is logarithmic, and every encoded field of the actual fixed program fits it.

`lifecycle_store_determinism` assumes initial non-memory state agreement and guarded dynamic reply agreement at matched actual steps. It concludes run agreement, final status, ordered numeric reads and each category count. Its underlying agreement also constrains registers and key observations. `load_occurrence_value_dependency` constrains the destination register when successful replies differ; trace inequality alone is not its conclusion. Independent C13/C14 clients pin both the public proposition and the numeric extent guard.

`Provenance.continuous_production` consumes the public contract and produces the same builder witness with `ProductionReceipts`: actual output reservation and register frame through the charged transfer, four indexed descriptor reads, every indexed copy load/store pair with its loaded-value dependency, and every indexed tail release. The independent provenance client expands the occurrence predicate into the actual prefix and step equation. [PROOF_INVENTORY.md](PROOF_INVENTORY.md) records hypotheses, conclusions, object chains and source anchors for E01-E14; the exact checked type and axiom output is hashed in the final receipt manifest.

## Concrete layout, work and storage

There is one input-independent program per input model. The service entry is 212964, builder body starts at 221239, descriptor at 223345, finalizer at 223356, and retirement at 223370. The word program has 223371 instructions; comparison has 223379. The encoded program has at most 1116895 words. All encoded fields, including dormant operands, are width checked.

For `n=xs.length`, `M=(buildMemory xs).length`, and the actual producer's `B=regs 3`:

| Quantity | Checked bound or equality |
| --- | --- |
| Scalar finalizer work | `7*M + 4*B + 5` transitions |
| Comparison retirement | `4*n + 5` transitions; zero for word input |
| Builder through final jump | At most `1100000000*(n+1)` transitions |
| First service | At most 160253 transitions, including four preparation operations and 8271 setup operations |
| Each later query | At most 160257 transitions, including the four boundary events |
| Every numeric arena prefix | At most `5000000*(n+1)` words |
| Separate comparison peak | At most `n` key cells and two key registers; both become zero before service |
| Retained numeric capacity | `(M + encodedProgram.length + 8273 + 8)*W <= 2*n + retainedRho n` |
| Remainder | `SuccinctSpace.LittleOLinear retainedRho` |
| Same word width | `log2(n+2)+1 <= W <= 192*(log2(n+2)+1)` |

The C10 direct consumer pins all bank, control, code, setup and query constants, the 160253 service budget, and the entire linear construction-budget function. Bounds are upper bounds; no tightness or practical speed claim is made.

The semantic implementation never materializes `buildMemory xs` as its execution input. That value appears in the specification and proofs of equality with the emitted cells. `Owner` retains arrays and scalar control, with no input list, future-request tape, proof packet or trace history. `runArray` observations and the validator's counters are separate; their final-owner projection is proved. Logical array lengths and physical model addresses do not establish native allocator capacity, consuming ownership or external alias freedom.

## Operational and dependency controls

[CONTROL_PREDICATES.md](CONTROL_PREDICATES.md) gives all P/Q predicates, objects, guards and quantifiers. Direct Lean controls challenge the same operational predicates for output source, initialization, stale tail, absent copy reply, omitted release, backward overlap, key retirement, finalizer/program entry and dormant field width. The tenth control starts with an actual completed query owner and skips the clear of a witnessed nonzero register 400. The positive setup satisfies the exact compact-entry ABI; the mutation fails its checked register projection. It does not claim an incorrect numerical answer from that mutation.

The production dependency runner compiles mutated copies of the actual Capstone or Provenance source and then elaborates the unchanged independent expected-type client. A failed producer never counts as an intended consumer rejection. The registry has 26 ordered cases: 23 expected rejections and three expected acceptances, with exact edits and diagnostic surfaces. It challenges all seven public groups, field removal, sibling/alias substitution, public propositions, cost/code-fetch/prefix-resource/owner-bank subclauses, store determinism and all four global provenance groups. Positive controls preserve the proposition while changing irrelevant implementation packaging. [DEPENDENCY_VERIFICATION.md](DEPENDENCY_VERIFICATION.md) records the observed final verdict for every case.

The diagnostic classifier accepts only the exact expected JSON diagnostic multiset at the named independent-client declarations. Non-JSON output, stderr, mixed/unrelated errors, wrong severity/class/count/surface, timeouts, producer failures and cleanup failures reject. The original trailing `error:`, `uncaught exception:` and `PANIC:` counterexamples were found by an independent read-only review and covered by explicit classifier controls before final replay. Missing/unknown/duplicate/reordered registry entries and omitted-versus-explicit-empty selectors are checked at their relevant boundaries. Original source and shared artifact identities remain unchanged; private producer artifacts are restored between cases.

## Executable reach and model assumptions

The new `rmq_lifecycle_validate` executable invokes actual `Executable.initialOwner`, `runOwner (Layout.program model).toArray` and `queryOwner`. Its expected answer comes from an independent strict-improvement scan with half-open intervals and leftmost ties. Its counters observe actual `stepArray`; `counted_owner` proves their final owner equals production `runOwner` for all inputs and fuel, and `category_index_exact` pins category classification.

All 16 exact fixtures passed, covering both input models, empty and singleton inputs, ties, invalid and repeated requests, actual dirty second-query state, and sizes 24 and 83. The comparison geometry fixtures use multiples of `2^(wordWidth n+5)` and explicitly witness a key outside the word-input interval. They check literal empty key arrays, numeric extent/register counts, actual reserve/release balance, category totals, exact final owner, unchanged reusable memory and charged request entry. [NATIVE_VERIFICATION.md](NATIVE_VERIFICATION.md) contains every fixture, exact command, timing and receipt.

The modeled primitives are scalar arithmetic/bit operations, load/store, scalar reservation of an absent cell (initialized later by charged stores), branch/jump/halt, one-tail-cell releases, and named scalar external admission/control transitions. Arbitrary Int comparison input uses a separately counted oracle/key channel; it is not bounded-word input storage. The retained `2*n+o(n)` statement is about the complete numeric model allocation. It is separate from peak work space, arbitrary-Int resources, proof terms, optional observations, native runtime and physical heap capacity.

## Verification and identities

| Final check | Observed result / duration | Limit and coverage |
| --- | --- | --- |
| `lake build` | PASS, exit 0, 5.732 s | 7200 s; required default integration, warm matching cache |
| `lake build RMQ.Core.WordRAM.Lifecycle.Capstone RMQ.Validation.LifecycleContract rmq_lifecycle_validate RMQ.Headlines.Lifecycle RMQ.Core.WordRAM.Lifecycle.Provenance` | PASS, exit 0, 57.584 s | 7200 s; required named targets plus additive headline/provenance |
| `lake env lean scripts/lifecycle_inventory.lean` | PASS, exit 0, 135.302 s | 300 s; exact types and 41 axiom inventories |
| New validator startup / focused / full16 | PASS, exits 0, 2.508 / 2.669 / 81.505 s | 30 s startup/registry/selector and 1800 s focused/full; 1 MiB output; nine processes |
| New dependency full26 | PASS, 23 expected client exits 1 and three expected accepts; all producer exits 0 | 120 s each; 52 compiler processes totaling 430.055 s, maximum 17.258 s |
| Dependency startup / focused D01 and D13 / classifier, registry, selector and owned-timeout controls | PASS at exact recorded surfaces | Detailed commands, durations, 6 s intentional cleanup test and receipt hashes in DEPENDENCY_VERIFICATION.md |
| Required trust and native-decision scans | Zero matches; both exit 1, 1.395 / 3.097 s | 180 s; `rg` exit 1 is the expected empty result |
| Frozen-row and complete evidence check | PASS, 43 exact IDs, eight frozen columns, no changed frozen rows | 180 s; final output and matrix identity in receipt manifest |
| Strict claim drift and explicit final-report scan | PASS, no strict failures | 7200 s full scan; 180 s report scan uses `-IncludeProcessRecords -Path docs/internal/extensions/lifecycle1/REPORT.md` because default report exclusions are not report coverage |
| Strict design, working/staged and committed-range whitespace, exact source/scope/clean state | PASS as bound by final and closing delivery receipts | 180 s per check; exact base and each commit parent, never an implicit empty range |

The per-commit check for implementation `299ec6527ca2fbcf73cfc34e9de75f4a1f34140c` passed in 3.854 seconds. Static check durations, exact argument arrays and actual exits are in FINAL_RECEIPTS.json and the final delivery receipt. Post-closing-commit durations and clean-state verification are in the final delivery receipt; this file does not claim to embed its own enclosing commit. Full final sources have no changes after the successful semantic suites; later edits are evidence-only.

The final-required default and explicitly named builds are distinct frozen-contract checks. The exact type/axiom inventory reports only subsets of `propext`, `Classical.choice`, and `Quot.sound`; the constant pins use no axioms. Both repository trust-hygiene scans have zero matches. Full outputs are retained at the absolute local paths in `FINAL_RECEIPTS.json`, with SHA-256, lengths, commands, start/end times, duration, exit status, deadline, output limit and process ownership. The source manifest records workspace SHA-256 separately from Git blob identities; it does not silently normalize historical row bytes.

Windows is the executed host. All final bounded child receipts report kill-on-close job ownership, no timeout/output-limit breach and no cleanup survivors. The dependency self-test deliberately times out an owned descendant tree and verifies cleanup. No Ubuntu/native-capacity claim is inferred from Windows execution. Warm artifacts were copied as separate files from the matching source described in [CACHE_PROVENANCE.json](CACHE_PROVENANCE.json); successful final checks are warm build evidence, not independent cold reproduction.

Two earlier broad claim scans supplied no verdict: the 180-second attempt took 181.412 seconds and the 900-second attempt took 900.910 seconds. Their owned jobs terminated IDs 28404/29952/22720 and 29836/29852/24744 respectively; both sets were verified absent. They remain NOT_CERTIFIED as `claim-budget180` and `claim-budget900`. Read-only source inspection identified the last emitted item as term 29 of 35 and later buffered multiline PCRE2 scans that match metadata before applying their narrower reporting filter.

The generated FINAL_RECEIPTS.json initially formed one 1,691-line paragraph. Inserting 270 LF bytes after object records reduces its maximum paragraph to 44 lines while preserving parsed JSON equality, every nonblank line, and every recorded path/hash/byte field. A temporary-copy production strict scan passed in 4.734 seconds; this supports the serialization fix without proving it caused the full-tree delay. The formatted receipt is SHA-256 `1fa9716b1a8d7279ba8bd3ea6a5f2eb7fc546097d78194dbabb94817324389cb`. Only the subsequent completed full-tree scan certifies this check. Scope, policy, matchers and all frozen contract bytes are unchanged; diagnostic and layout receipts are bound by the final delivery record.

The first full scan with that formatting also timed out after 901.547 seconds; its owned IDs 29232/29936/30576 were verified absent, and `claim-budget900-formatted` remains NOT_CERTIFIED. Read-only inspection then identified five inherited, baseline-identical native1 receipts with 40,000–66,000-line nonempty paragraphs. Exact production term-34 measurements on temporary 4,000/8,000/16,000-line prefixes took 1.964/12.384/45.017 seconds, all expected no-match exits with clean owned completion. Weighted estimates suggest about 896 seconds for one representative complete receipt and 5,724 seconds of sequential no-trigger work; concurrent scheduling and extrapolation remain uncertain. These measurements justify a 7200-second owned deadline for the unchanged full scan. No inherited receipt, scanner, policy or reporting scope is changed. The timing samples establish scheduling evidence only, with their exact commands, source identities and complete outputs bound by delivery.json.

The interrupted first native build supplied no certification. A second cold/native continuation passed; the later comparison-fixture correction changed a real edge assertion and justified the corrected final replay. The pre-correction runtime is development evidence only. Early dependency development failures were not accepted as case verdicts; the final registry and classifier are replayed together. Source changes consumed by a check invalidate that check; subsequent evidence-only edits require fresh claim/design/row/whitespace checks but do not invalidate unchanged Lean/native source results.

Byte-pinned contract reproduction requires an LF-preserving checkout, for example `git -c core.autocrlf=false worktree add --detach <fresh-path> <exact-candidate-commit>`. This applies to both matrix files and CONTRACT_REQUIREMENTS.json. The current local core.autocrlf setting is true, but these created workspace files and their committed blobs are checked separately; later checkout/reset must preserve their LF bytes. A default CRLF checkout is expected to fail the byte-integrity check. The checker does not silently normalize frozen evidence, and no repository attributes or user configuration were changed.

The frozen source prompt is SHA-256 `f82a24460dfa06602fc52e2c78b0fa8402fbb84a0d203b4abb95040fa56b0c18`. The 43-row/eight-column frozen matrix is SHA-256 `8b08e2d7c7f284634d88bfa4262ee447f79a401c78b27dc346ea34d76ccba4a7`, 43437 bytes. Final integrity checks preserve every full row and the frozen prefix, with no changed IDs. [ACCEPTANCE_MATRIX.md](ACCEPTANCE_MATRIX.md) retains the original Open rows as history and appends current dispositions. [ACCEPTANCE_EVIDENCE.md](ACCEPTANCE_EVIDENCE.md) contains all 43 exact IDs, their propositions, object chains and control receipts. Their current local disposition is candidate-closed; only coordinator acceptance can change the campaign disposition.

The complete candidate delta contains the following 65 paths (relative to the absolute worktree above):

```text
docs/DIGESTION_LOG.md
docs/digests/LIFECYCLE_PROOF_GUIDE.md
docs/FAMILY_SUMMARY.md
docs/internal/DESIGN_DECISIONS.md
docs/internal/extensions/lifecycle1/ACCEPTANCE_EVIDENCE.md
docs/internal/extensions/lifecycle1/ACCEPTANCE_MATRIX.frozen.md
docs/internal/extensions/lifecycle1/ACCEPTANCE_MATRIX.md
docs/internal/extensions/lifecycle1/CACHE_PROVENANCE.json
docs/internal/extensions/lifecycle1/contract_integrity.json
docs/internal/extensions/lifecycle1/CONTRACT_REQUIREMENTS.json
docs/internal/extensions/lifecycle1/CONTROL_PREDICATES.md
docs/internal/extensions/lifecycle1/DEPENDENCY_VERIFICATION.md
docs/internal/extensions/lifecycle1/FINAL_RECEIPTS.json
docs/internal/extensions/lifecycle1/NATIVE_VERIFICATION.md
docs/internal/extensions/lifecycle1/PROOF_INVENTORY.md
docs/internal/extensions/lifecycle1/REPORT.md
docs/internal/extensions/lifecycle1/RUNNER_REVIEW.md
docs/internal/extensions/lifecycle1/SOURCE_MANIFEST.json
docs/internal/extensions/lifecycle1/START.json
docs/internal/extensions/lifecycle1/VERIFICATION_PLAN.md
docs/internal/WORKFLOW_DESIGN_DECISIONS.md
lakefile.toml
RMQ/Core/WordRAM/Lifecycle/Accounting.lean
RMQ/Core/WordRAM/Lifecycle/Agreement.lean
RMQ/Core/WordRAM/Lifecycle/ArrayRun.lean
RMQ/Core/WordRAM/Lifecycle/BoundarySafety.lean
RMQ/Core/WordRAM/Lifecycle/Builder.lean
RMQ/Core/WordRAM/Lifecycle/BuilderProvenance.lean
RMQ/Core/WordRAM/Lifecycle/Calculus.lean
RMQ/Core/WordRAM/Lifecycle/Capstone.lean
RMQ/Core/WordRAM/Lifecycle/CodeFetch.lean
RMQ/Core/WordRAM/Lifecycle/Construction.lean
RMQ/Core/WordRAM/Lifecycle/Continuous.lean
RMQ/Core/WordRAM/Lifecycle/Controls.lean
RMQ/Core/WordRAM/Lifecycle/Descriptor.lean
RMQ/Core/WordRAM/Lifecycle/Executable.lean
RMQ/Core/WordRAM/Lifecycle/Finalization.lean
RMQ/Core/WordRAM/Lifecycle/Finalizer.lean
RMQ/Core/WordRAM/Lifecycle/Input.lean
RMQ/Core/WordRAM/Lifecycle/Machine.lean
RMQ/Core/WordRAM/Lifecycle/Ownership.lean
RMQ/Core/WordRAM/Lifecycle/Physical.lean
RMQ/Core/WordRAM/Lifecycle/Profile.lean
RMQ/Core/WordRAM/Lifecycle/Program.lean
RMQ/Core/WordRAM/Lifecycle/Provenance.lean
RMQ/Core/WordRAM/Lifecycle/QueryBridge.lean
RMQ/Core/WordRAM/Lifecycle/QueryEntry.lean
RMQ/Core/WordRAM/Lifecycle/QuerySafetyBridge.lean
RMQ/Core/WordRAM/Lifecycle/Resources.lean
RMQ/Core/WordRAM/Lifecycle/Retained.lean
RMQ/Core/WordRAM/Lifecycle/Retirement.lean
RMQ/Core/WordRAM/Lifecycle/Reusable.lean
RMQ/Core/WordRAM/Lifecycle/Safety.lean
RMQ/Core/WordRAM/Lifecycle/Service.lean
RMQ/Core/WordRAM/Lifecycle/ServiceSafety.lean
RMQ/Headlines/Lifecycle.lean
RMQ/Validation/LifecycleContract.lean
RMQ/Validation/PackedLifecycle.lean
scripts/lifecycle_contract_integrity.ps1
scripts/lifecycle_dependency_cases.json
scripts/lifecycle_dependency_README.md
scripts/lifecycle_dependency_replay.ps1
scripts/lifecycle_inventory.lean
scripts/lifecycle_provenance_contract.lean
scripts/lifecycle_validator.ps1
```

## Proof digestion and next consumers

Conceptually, the new result closes the operational gap between building a succinct allocation and querying it. The builder's real reservation result becomes the finalizer's source pointer; scalar copy and tail revocation establish the exact retained store. The query begins by executed control flow and real register initialization. The array owner computes the same execution and can be reused without retaining the input keys or manufacturing a fresh ready state.

For a worked example, follow the source pointer, descriptor reads, copy and release indices in [LIFECYCLE_PROOF_GUIDE.md](../../../digests/LIFECYCLE_PROOF_GUIDE.md). The empty word fixture actually executes 13601 transitions and retains 175 numeric arena words after 132 scalar numeric releases. The 83-element word/comparison fixtures execute 214277/214282 initial transitions and retain 211 words; their next three requests total 81031 transitions. These are measured fixtures alongside uniform checked bounds, not evidence of asymptotic tightness.

Live assumptions are the two declared input domains, represented endpoints, the existing Lean/Std primitive semantics and comparison oracle cost convention, the declared RAM word operations, and the proved model's accounting boundary. A skeptical reader can reconstruct the actual reservation/copy/read occurrences, every retained object in the seven fields, and each expected-type consumer without trusting this report. The next campaign questions concern a consuming native adapter's concrete backing capacity/alias discipline, aggregate portability, and independent exact-candidate acceptance; they are the explicitly assigned subsequent consumers, not missing local propositions.

DD-20260920-LIFE-001 records the machine/layout/accounting choice. WDD-20260920-LIFE-001 and -002 record complete-row freezing, cache/command provenance, independent expected types, isolated mutations, exact diagnostic parsing and new executable reach. The evidence-only closing commit records its own rationale in the workflow ledger. No unrelated reference semantics or predecessor public surface was rewritten.

An optional Claude source-review transfer was rejected by automatic approval review on source-export authorization grounds. The transfer was stopped without retry or workaround; local proof and verification work continued. That helper was not used as independent acceptance evidence.

Automatic approval review also rejected an attempted status message to the coordinator task because it could not establish authorization for that destination. No message was sent. Explicit confirmation was requested in this task while local verification continued; delivery of the local candidate does not assert that this separately blocked message succeeded.
