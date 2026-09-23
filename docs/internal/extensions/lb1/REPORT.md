Status: BLOCKED
Required coordinator-owned full build and aggregate certification results have not been received. The local proof, validation and evidence work reported below is a handoff checkpoint; coordinator acceptance remains required.

# LB-1: observed-length lower bound on the actual packed allocation

Handle: LB-1. Requested task title: (LB-1) Match lower bound to packed allocation.
Branch: codex/lb-1-variable-payload.
Worktree: C:/Users/poin/.codex/worktrees/2270/RMQ.
Base and workflow governance: 0e6a00f654abc64f8b68988fa9675b9a839dca2f.
Frozen contract checkpoint: 0bbbe8ca4a937bc9782b2f7c5cc5419faa1a75a2.
Implementation and independent-audit target: 5033ce54da233fc7a3df319d50ab09a2ebee523a.
Delivery commit: the commit containing this report; its exact identity is supplied with the report digest in the task handoff. Source-equivalence evidence below identifies the exact audited implementation separately.

## Result and remaining requirement

The implementation connects a variable-length bitstring counting theorem to
every serialized cell of PQ1's actual buildMemory, then reconstructs that same
memory for the decoder and all transported machine claims. The independent
consumer composes the counting theorem, decoder and allocation on identical
objects. The extension preserves half-open ranges and leftmost ties.

All required local semantic cases, five focused mode entry points, three additional selector branches, the final twenty-name trust inventory and exact-source policy checks passed. Independent saved-evidence reconciliation found all 63 ordered cases and 134 stages consistent. The required coordinator-owned broad results remain outstanding.

The user selected: "Coordinator will run the checks and provide results" for
the full build and aggregate gate. Neither command was run by this task, and
their success is not inferred from narrow checks. The aggregate builds the new
validation executable, but does not run the LB-1 mutation registry or its
lane-specific inventory and axiom checks. Those have separate coverage.
No coordinator acceptance, integration, push or branch/worktree cleanup is
claimed or performed. The task-title tool was unavailable; the requested title
is recorded here.

## Exact proof and object composition

For an `ExactRMQBoundedEncoding n B`, the decoder is fixed across all ordinary
size-n `List Int` inputs, payload length is at most B, and exactness covers
every contained positive-length half-open window. The checked conclusions are:

```lean
(boundedBitStrings B).Nodup
(boundedBitStrings B).length = 2 ^ (B + 1) - 1
bits ∈ boundedBitStrings B ↔ bits.length ≤ B
Cartesian.shapeCount n ≤ 2 ^ (B + 1) - 1
EncodingLowerBound.doubledLogSlackLower n ≤ 2 * (B + 1)
```

Equal codes imply equal RMQ behavior and equal Cartesian shapes; canonical
shape representatives give the finite injective domain. The required generic
named theorem is `RMQ.ExactRMQBoundedEncoding.doubledLogSlackLower_le`.

The packed instance uses these exact identities:

```lean
allocationBits xs = serializeWords (wordWidth xs.length) (buildMemory xs)
(allocationBits xs).length = (buildMemory xs).length * wordWidth xs.length
reconstructedMemory xs = buildMemory xs
allocationDecoder n bits left right =
  queryNat (deserializeWords (wordWidth n) bits) n left right
```

The complete serializer left inverse applies to every finite word list with
entries below `2 ^ width` when `0 < width`. Length is preserved through the
bitstring itself, including zero-valued words; empty and padded lists are not
identified. Size-n Cartesian shapes inject into the allocation encoding.
Different value lists with the same shape intentionally share memory and bits.

The decoder's exact conclusion for every xs,left,right is:

```lean
allocationDecoder xs.length (allocationBits xs) left right =
  if ValidRange xs left right then
    some (scanWindow xs left (right - left)) else none
```

`UniformAllocationBudget n B` quantifies over every xs of length n and bounds
the actual `buildMemory` allocation in bits by B. The generic instance
`allocationEncoding n B budget` has exactly `encode := allocationBits` and
`query := allocationDecoder n`. Consequently its arbitrary uniform budget
satisfies the same finite count and doubled lower bound. The canonical budget
is `2 * n + allocationRho n`; the actual per-input serialized length has this
upper bound, and `LittleOLinear allocationRho` is checked. The lower bound is
on a uniform worst-case budget, not every individual input's allocation.

`reconstructedRun_eq` equates the whole primitive run for every fuel with the
run on `buildMemory`, preserving program, initial state and endpoints.
`ReconstructedPackedQueryCapstone` transports all 33 machine fields using that
whole-store equality. `PackedAllocationOptimality` has 16 fields and the named
producer `RMQ.SuccinctFinal.PackedWordRAM.packedAllocationOptimality_holds`.
The independent `RMQ.Validation.VariablePayloadLowerBound.composedConsumer`
and canonical encoding consumer join these statements; all 49 field projections
have literal expected types. Definition pins fix the decoder, budget, program,
memory, validity and safety predicates separately.

## Live assumptions and model limits

Public n and observed bitstring length are external conventions. The canonical
decoder requires no input/shape-dependent advice; fixed size-only advice is
permitted by the generic model. Payload counts every allocated cell, including
metadata and padding. Fixed instruction encoding and finite scratch are counted
separately in the complete-capacity theorem. Proof fields do not supply answers.

The transported model has one n-only word width between `log2(n+2)+1` and
`192*(log2(n+2)+1)`, the fixed primitive program, budget 837572, 8271 registers
and 8274 scratch words. Raw machine safety retains endpoint-representability
guards; the natural-number wrapper's total contract does not remove them.
Arithmetic primitives include multiplication, division, modulus and shifts.
Mathematical bit conversion and the outer natural-number wrapper carry no
charged query-time claim. Model steps are not measured Lean execution time.

## Verification and independent audit

| Check | Exact local outcome and durable evidence |
| --- | --- |
| Fresh baseline compilation and metadata | Generic and packed producers, actual 4/16/33 inventory, all 49 literal validation consumers, separate generic consumer: all exit0 before baseline artifacts were saved; evidence/replay-v3-5033/baseline-*.json. |
| Full version 3 replay | All63 ordered cases,61 expected REJECT and 2 expected ACCEPT; all 6 runtime cases;134 raw stages; source/artifact restoration and clean state. evidence/replay-v3-5033/summary.json. Final terminal exit0 at 2026-09-12 11:08:36 UTC. |
| Independent saved-evidence reconciliation | Exact stage order, own-declaration semantic diagnostics including S03 P/Q, no resource/import substitute, six runtime IDs, raw/summary equality,677 current source/configuration files: EVIDENCE_CONSISTENT. Twelve raw byte matches and 665 CRLF/LF-only differences are distinguished. evidence/final-verification/final-replay-verification.json. |
| Five focused entry points | RegistryOnly 5.992s, SelectorBoundaryOnly 42.78s, DiagnosticOnly 6.803s, DeadlineOnly 36.294s, RuntimeOnly 375.182s: all exit0. Expected/executed modes identical; source unchanged and clean. Nested child records retained in evidence/focused-modes-5033. |
| Owned timeout | Windows child3892 was created, the 30-second owned timeout terminated it, and the no-survivor check passed. Deterministic ownership-plan controls also passed. Physical POSIX execution is UNOBSERVED on this host. |
| Additional selector branches | Replay CLI/environment conflict7.14s; runtime conflict42.904s; malformed runtime ID inside a valid case: channel36.94s. Each rejects at the intended branch before any case-pass marker. evidence/selector-extra-5033/summary.json. |
| Trust inventory and source scans | All20 ordered declarations: only propext, Classical.choice and Quot.sound. Both required full RMQ source scans have no hits. Source unchanged/clean; evidence/trust-5033/summary.json and axiom-inventory.json. |
| Frozen acceptance rows | Exact5033 checker:29 unchanged whole rows and 7 corruption controls pass; evidence/final-verification/final-frozen-rows.json (after final prose edits), with the earlier exact-source receipt also retained. |
| Exact-source public/process policy | Strict claim scan including process records:2026 hits,0 strict failures. Strict design check with exact governance base:185 changed files, no failure. evidence/final-verification/source-5033-policy.json and its raw logs. |
| Report-containing tree | Results are recorded in evidence/report-checks.json after the actual report and appendices exist; committed-range and source-equivalence checks are separately reported in the task handoff. |
| Coordinator broad certification | Full lake build and aggregate gate NOT RUN here; user assigned execution/result delivery to the coordinator. |

Every required acceptance ID remains verbatim in ACCEPTANCE_MATRIX.md.
EVIDENCE_PLAN.md expands the exact propositions and same-object consumer chains;
FINAL_DISPOSITION.md maps all 29 IDs to the final evidence without editing those
frozen rows. The frozen-row checker also runs seven corruption controls.

FINAL_AUDIT.md contains the independent LB1-BLIND3 report on exact 5033. Its source review found no proof/model defect and its local evidence review reconciled the full campaign and supplements. Its INCOMPLETE verdict preserves the missing coordinator broad certification and the then-future report-containing-tree checks. The lead performs those report-sensitive checks after saving the returned audit text; the source target remains5033. The final handoff reports the exact audit and worker-report byte digests.

## Repair history and evidence fidelity

The original implementation d6dabbec10648f368df9ddcd32102f84deffb281 passed
60 of 63 replay cases before S03-SIBLING-BUDGET hit a recursion limit during
consumer type comparison. That resource result was rejected as inconclusive;
H01 and A02 did not run. Its 129 raw stage records are retained under
evidence/replay-v3-d6dabb-inconclusive, and AUDIT_D6_INCONCLUSIVE.md links to the losslessly archived original, preserving
the original exact-target audit unchanged.

The sole implementation repair in 5033ce54 changes checkO09's proof body to
`by with_reducible exact packedAllocationOptimality_holds.uniformBudgetCount`.
The literal arbitrary-B proposition and canonical-budget mutation stay the
same. The actual registered S03 focused replay then produced the required
explicit type mismatch and passed restoration, before the new full campaign.
This was an elaboration repair, with no theorem-type or model change.

The runner compares original/restored source and olean bytes in nested finally
blocks and checks clean worktree/index/untracked state after every case and at
exit. Original olean hashes were not separately persisted at launch; artifact
restoration is evidence from those executed comparisons and the recorded
summary, not an invented independent before/after hash pair. The evidence
verifier separately checks current source identities, exact stage order and
diagnostic surfaces. Raw stage outputs, failures and source identities are
preserved; no resource failure is counted as a semantic rejection.

The separate read-only evidence verifier initially failed before examining
records because an asynchronous Git stream helper emitted a boxed task result
alongside its byte object. Suppressing that incidental output exposed a Windows
configuration portability issue with NUL; the final verifier uses the already
working empty global-ignore override. Both failed receipts and the intermediate
pass remain in final-verification. The repaired verifier reconciles all 134
stages and 677 source/configuration files. These were checker repairs; the
successful semantic campaign and source files were unchanged.
One fresh audit attempt stopped after an agent-status tool exposed a withheld
worker completion narrative. Its attempt did not contribute a substantive
verdict. The replacement used a new detached checkout and fresh context,
excluded that tool and withheld all prior narratives. Auditors made no file
edits or Lean executions; returned report text was saved verbatim by the lead.

## Proof digestion and decisions

Conceptually, observing payload length allows exactly `2^(B+1)-1` possible
codes through B bits. RMQ still distinguishes every Cartesian shape. The new
adapter makes this information bound apply to the words the existing machine
actually stores, while whole-list recovery keeps its query facts on those
same words. This now provides one checked lower/upper/allocation composition.

A skeptical graduate student should trace the arbitrary uniform budget into
the actual encoding, inspect whether the decoder receives hidden shape advice,
and compare every transported execution with the counted memory. The literal
consumers, definition pins and recorded counterfactuals address these questions
on the frozen domain. They do not claim a lower bound for each individual input
or a machine-time bound for mathematical deserialization.

DD-20260912-LB1-001/002 record the counting and actual-allocation decisions.
WDD-20260912-LB1-001/002/003 record validation/evidence and the S03 repair choices.
WDD-20260912-LB1-005 records lossless scan-log archival after path-sensitive diagnostics were reclassified when copied as plaintext. Current reports and all current claims remain directly scanned; the archived historical audit is checked after decoding by the same strict scanner. No policy or allowlist changed. WDD-20260912-LB1-004 records the fresh-audit transport and shared-narrative contamination boundary; a replacement audit, rather than a disclaimer on the stopped session, preserves the frozen independence requirement.
The repaired proof changes no mathematical abstraction or representation;
no additional mathematical design decision was needed. FAMILY_SUMMARY.md and
DIGESTION_LOG.md contain append-only candidate updates. README and public alias
migration are outside this additive branch's authorized scope.

## Delivery identity and next action

All theorem/construction/validation modules under RMQ, scripts, lakefile.toml, lean-toolchain, .agents and AGENTS.md remain unchanged from the exact audited implementation 5033ce54da233fc7a3df319d50ab09a2ebee523a. The delivery adds durable copies of the exact executed evidence/probe/verifier bytes and report/public-process appendices. Those evidence and prose additions require their own report-sensitive checks; they do not invalidate unchanged Lean elaboration or the completed semantic campaign. The audited implementation remains an ancestor of the delivery commit.

Only local commits are made. The coordinator should run the required full
build and aggregate gate on the delivered unchanged content, provide exact
commands/results, reconcile the independent report, and record acceptance or
repair dispositions. The status remains blocked pending those external results.
