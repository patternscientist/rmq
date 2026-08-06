Status: CANDIDATE_COMPLETE
I found no assigned or inherited acceptance criterion unmet; coordinator acceptance is still required.

# EG-CP all-size reviewer-machine rung -- worker result

This report covers local rung `EG-CP-ALLSIZE-R1` on branch
`codex/eg-cp-allsize-reviewer-machine-r1`. It supersedes the stalled worker's
INCOMPLETE checkpoint that previously occupied this file. Nothing below records
coordinator acceptance, integration, merge readiness, publication, or closure
of the full EG-CP node; those remain explicitly open in section 11.

## 1. Exact identity and provenance

| Item | Value |
| --- | --- |
| Local rung | `EG-CP-ALLSIZE-R1` |
| Branch | `codex/eg-cp-allsize-reviewer-machine-r1` |
| Worktree | `C:\Users\poin\Documents\RMQ\.claude\worktrees\allsize-reviewer-memory-controller-aac506` |
| Exact branch base | `6bf28dee32c96da4705b139959fd35e4a782bac4` |
| Base tree | `4d173458db3e1ad33186a2f843ee7dd5cbd87d97` |
| Base parent | `d0237a3fa9d01f4ed06fe25d58a2a79981db4809` |
| Frozen-matrix ancestor | `0a18548539035f69f68c1b44031fba64df8297f3` |
| Frozen R2 matrix commit (first commit of this rung) | `c0cd3873bcd2b11abb33f9f67986d309069f82bb` |
| Workflow-governance ref | `f0c7232a8a52b8d61ead5e96d72a8a849bc094b5` |
| Proof-bearing HEAD | `5bca709ad64fb4d8971db76c75da2baa24b5b214` |
| Proof-bearing tree | `cc75bcb8b334d2de39007a4213affa0a38deafd7` |
| Commits since base at the proof-bearing HEAD | 37 |
| Changed tracked paths since base at the proof-bearing HEAD | 31 |

The commit that introduces this corrected report is documentation-only, with
the proof-bearing HEAD `5bca709ad64f` as its frozen parent. Every Lean module,
the replay harness, and the acceptance matrix are byte-identical between the
proof-bearing HEAD and this report commit; a report cannot soundly embed its
own hash, so the report commit's identity is recorded in the accompanying
worker terminal response and by Git itself.

Work began as a byte-faithful recovery of the stalled predecessor worker's
uncommitted construction (28,780 lines, checksummed patch and archive retained
in session evidence), committed matrix-freeze-first at
`c0cd3873bcd2b11abb33f9f67986d309069f82bb` per the freeze-before-edits
discipline. Project-skill preflight passed before substantive work at exact
base `6bf28dee`, with `rmq-proof-sprint` required and runtime catalog
`rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint`.

### Predecessor provenance retained

The 1,907-line predecessor report described the older branch
`codex/eg-cp-final-falsification-gate-r1`, originally based at
`1490c97b399d136bad4e18953441da433d130d4d` and later continued from
`6078a29c318b0bd167b87b05629f576c53266fea`. That predecessor established the
reviewer payload, memory, space accounting, conditional probes, access-half
lowering, and close segments 21 and 22, while leaving segment 20 and the
physical whole-query machine open. Those checked leaves remain provenance for
this rung. The controlling requirements for this rung are the append-only
`R2-*` rows in section 7 of `docs/internal/EG_CP_FINAL_FALSIFICATION_MATRIX.md`;
the original `FG-*` rows remain the frozen historical record and are
byte-identical to the exact base.

## 2. The construction in one paragraph

The branch keeps a one-cell K1 header containing `longCount`. It obtains the
only other content-dependent layout count, `sparseCount`, by three fixed
charged logical reads whose addresses depend only on `n` and the decoded
`longCount`. The resulting all-size closed geometry addresses the exact
canonical reviewer payload, including the eight ragged segment-20 component
stores. A proof-free first-order controller then performs header, K1 prelude,
and whole-query request/reply steps against one external reviewer-memory
array. The proof side relates those exact replies to the canonical global
logical store, preserves logical occurrence and physical probe multiplicity,
and returns the guarded public `queryTraceResult` on the identical run. The
physical cap is derived from the trace decomposition as

```
1 header cell + at most 2 * 3 K1 cells + at most 2 * 210 logical attempts = 427.
```

Here `210` is fuel for the logical driver -- 210 logical reads versus the
derived `427` physical probe cap -- not a claim that every query performs
exactly 210 logical reads. Zero-cell logical attempts advance the protocol
without decorative physical events.

## 3. Same-object composition chain

The exact canonical payload/memory/controller/run/reference composition, now
checked end to end:

```
SuccinctClassic.buildPayload xs
  = packedReviewerPayloadBits (SuccinctClassic.cartesianShape xs)
  -> packedReviewerSerializedBits
  -> packedReviewerPaddedBits
  -> packedReviewerMemory
  -> packedReviewerRunAgainstMemory
  -> ordered header / K1 / lowered-whole physical trace
  -> packedReviewerLogicalRead_eq_globalReadStore
  -> packedReviewerDriveLogical_210_simulates_packedWholeQueryRun
  -> packedWholeQueryRun
  -> SuccinctClassic.queryTraceResult xs left right
```

The older `concreteBPNativeSuccinctRMQPayload` is a flat sibling and is not
part of this chain. Proof-only global-store and shape values occur at the
refinement boundary; neither is a controller field or an alternative reply
source for the physical driver. The principal checked names pinning the chain:

- payload identity: `packedReviewerPayloadBits_eq_canonical`,
  `packedReviewerPayloadBits_eq_buildPayload`;
- serialization and backing: `packedReviewerSerializedBits_drop_header`,
  `packedReviewerMemory_length`, `packedReviewerMemory_header_cell`,
  `packedReviewerMemory_length_mul_width_le`;
- memory-only execution: `packedReviewerRunAgainstMemory_memory_only`;
- physical/logical store agreement:
  `packedReviewerLogicalRead_eq_globalReadStore`;
- ordered simulation and lowering: the drive-logical simulation and
  occurrence theorems and the actual-run lowering consumed at
  `RMQ/Validation/EGCPFinalFalsification.lean` lines ~2328-2437;
- public outcome and certificate:
  `packedReviewerRunAgainstMemory_public_outcome`,
  `packedReviewerRunAgainstMemory_public_certificate` (the inhabited
  26-field `PackedReviewerPublicRunCertificate`);
- the four rung-supplied operand/width closures:
  `packedReviewerDriveLogical_210_request_operands_fit`,
  `PackedReviewerRunGrouping.request_operands_fit`,
  `packedReviewerCanonicalReachable_state_machine_fits` with
  `packedReviewerReachableStateCertificate_of_reachable`, and the all-size
  `packedReviewerInteriorDeadAddress_lt_two_pow`.

The frozen validation root elaborates against all of these; every consumer in
it is an exact-type pin, not a summary.

## 4. Frozen local-rung rows `R2-01` through `R2-10`

Row-by-row closure evidence is recorded in the amended acceptance matrix
(`docs/internal/EG_CP_FINAL_FALSIFICATION_MATRIX.md`, section 7, evidence
columns filled at the proof-bearing HEAD). Summary:

| Row | Disposition |
| --- | --- |
| `R2-01-CONSUMED-PAYLOAD-IDENTITY` | Closed on this rung: identity chain of section 3; replay case `M11-SIBLING-PAYLOAD` REJECTs the flat-sibling substitution. |
| `R2-02-ALL-SIZE-SPARSE-RESOLUTION` | Closed on this rung: K1 survived -- the three-read charged prelude recovers `sparseCount` with no stride, cutoff, sampled-size, or readiness premise anywhere in the capstone chain. K2 was never activated. |
| `R2-03-EXACT-LENGTH-AND-HEADER` | Closed on this rung: exact payload/serialized/padded/cell-count/allocation equations over the actual reviewer object (validation consumers at lines ~1868-1961). |
| `R2-04-SEGMENT20-RAGGED-LOWERING` | Closed on this rung: eight-component coordinates, word order, canonical word, physical decode, and exact segment-20 equality (validation consumers at lines ~2017-2160). |
| `R2-05-PHYSICAL-REQUEST-REPLY-CONTROLLER` | Closed on this rung: proof-free first-order controller pinned by exact-signature consumers; `M03-SHAPE-PARAMETER` REJECTs a semantic shape input. |
| `R2-06-REVIEWER-MEMORY-ONLY` | Closed on this rung: driver-memory-only replies and dynamic-store agreement; `M05-SIBLING-STORE` and `M06-ANSWER-ORACLE` REJECT. |
| `R2-07-ORDERED-WHOLE-RUN-LOWERING` | Closed on this rung: occurrence-indexed logical/physical simulation and actual-run lowering; `M07-DISCONNECTED-TRACE` REJECTs. |
| `R2-08-TOTALITY-ADDRESS-CAP` | Closed on this rung: literal 427 derived from the run trace, allocation, and address width; `M08-FORGED-PROBE-CAP` REJECTs a stored cap. |
| `R2-09-SAME-RUN-REFERENCE-CORRECTNESS` | Closed on this rung: the identical run object returns the guarded independent reference result with grouping in the same conjunction. |
| `R2-10-TYPED-ANTI-BYPASS` | Closed on this rung: the entire frozen validation module elaborates, and the owned `R2-ALLSIZE` replay stage replays all seven commissioned mutations to commissioned REJECT with SHA-verified restoration. |

Every closure reads "closed on this rung"; none records acceptance.

## 5. K1 digestion: K1 survived, K2 unused

The old near-all-size route relied on `localStride = 1` and an informal
astronomical cutoff. The final route treats `sparseCount` as data discovered
by the machine: the one header word carries only `longCount`; three prior
logical reads retrieve the terminal sparse-flag rank super sample, block
sample, and flag word; their decoded values combine with the size-only local
stride to recover the exact sparse-relative row count. The requests and their
addresses are fixed before `sparseCount` is known, their plans are
sparse-count-independent with at most two cells each, and the decoded count
feeds every later sparse-dependent length and address of the same run. K2 was
authorized only after a kernel-checked K1 obstruction; the charged three-read
construction removed the need for any obstruction, so no second header cell
was added and no format drift occurred. No `localStride = 1`, `n < 2^97`,
sampled-size, readiness, or compatibility premise survives in the final
chain (confirmed by the final hygiene scans and the all-size binders of every
capstone consumer).

## 6. What closed the machine after the recovery

Beyond the recovered construction, the completing work landed in
`ReviewerControllerStateProof.lean` and companions:

- the thirteen-arm select tower invariant with per-arm consume closers, the
  exact long- and sparse-flag rank value characterizations over the canonical
  store, relative-directory content bounds, and a done envelope tightened to
  `close <= 2n + 1` (forced: the interior range obligation fails at any
  looser bound);
- the eleven-arm close/LCA tower with seed/window/fringe/interior phases,
  the 34-chunk candidate-argument envelope and its globalization, and a
  `<= 129` structural budget;
- the five-arm whole coupling handing decoded closes into the LCA start and
  the LCA answer (with its carried `+1` slack) into the final rank,
  discharging the public 210-fuel logical operand theorem in the exact
  validation binder shape;
- the coupled physical controller chain: header decode enters the prelude
  normalization, parked probes advance exact plan prefixes, completed whole
  probes regenerate the operational witness field-wise, and reachability
  yields the state-machine envelope and the reachable-state certificate;
- the physical operand closure over the expected trace, its grouped
  transport, and the inhabited 26-field public certificate;
- the dead-address width generalized to every size through the realizing
  shape.

## 7. Inherited invariant status for this rung

All fifteen applicable inherited invariants are closed on this rung with
evidence recorded row-by-row in matrix section 7.3 (address width, all-size,
global physical machine, no-synthetic, oracle independence, program
accounting, proof separation, read backing, store agreement, store identity,
trace execution, validation reach, width scaling, word width, value
dependency). Every closure names its validation consumers and, where
commissioned, its replay REJECT case. None records acceptance.

## 8. Design and workflow decisions

The branch records the recovered worker's four proof/model decisions and one
process decision (`DD-20260805-071` through `DD-20260805-074`,
`WDD-20260805-001`) as described in their ledger entries: K1 discovery via
charged replies, child-protocol normalization before wrapping, fixed-budget
correctness at the canonical reviewer-store boundary, the
Proof/StateProof module split, and the owned seven-case `R2-ALLSIZE` replay
view over the frozen sixteen-case registry. One additional workflow repair
landed during completion: the never-yet-executed replay stage selector
crashed the Windows PowerShell 5.1 dynamic binder (`@(...)` over a generic
list) and was replaced by plain array accumulation, replaying identically
(commit `a4d18d7` on this branch); the frozen registry, selectors, deadlines,
restoration hashes, and clean-state controls were not altered. The `R2R1`
repair rung subsequently added `WDD-20260805-002` (semantic replay mutants
with mechanical activation checks; each expected failure surface names the
honest guarding module) and `DD-20260805-075` (210-fuel wording and
validation-header inventory repair; comment-only Lean changes).

## 9. Verification ledger

### Worker-side runs on this branch (development and final tree)

| Check | Outcome |
| --- | --- |
| Project-skill preflight at `6bf28dee` | PASS before edits. |
| Focused module elaborations | PASS per commit throughout (state-proof builds 39-52 s each; every implementation commit was preceded by a green focused build). |
| Direct `lake build RMQ.Validation.EGCPFinalFalsification` | PASS on the frozen proof tree (1 m 54 s cold). |
| `lake build RMQ` | PASS on the frozen proof tree (3 m 38 s). |
| `scripts/design_decision_check.ps1 -Strict -Base 6bf28dee...` | PASS (31 changed files: 25 code, 3 workflow, 3 neutral). |
| Strict claim-drift scan | PASS (1,511 hits, 0 strict failures). |
| Forbidden-token scan (`sorry`/`admit`/`axiom`/`unsafe`/`opaque`/`implemented_by`/`partial`/`extern`/`noncomputable`/Mathlib) | Zero matches over `RMQ` and `lakefile.toml`. |
| `native_decide` / `Lean.ofReduceBool` scan | Zero matches over `RMQ`. |
| Frozen original-row byte comparison against `6bf28dee` | PASS: matrix diff is append-only (102 insertions inside the amendment markers, 0 deletions), mojibake-free. |
| Committed-range and working-tree `git diff --check` | PASS. |
| Clean index and untracked state | PASS at the proof-bearing HEAD. |
| `R2-ALLSIZE` replay stage | **SUPERSEDED -- do not rely on this row.** PASS: bounded startup with measured deadline, positive selector case, then all seven commissioned mutations REJECT with SHA-verified restoration and terminal clean tree. *(Coordinator annotation, 2026-08-05, audit finding P3-3: this row records the **pre-repair** run, whose `M05`/`M06`/`M07`/`M11` bodies were later found to be arity-only mutations, so those four REJECTs certified signature sensitivity rather than the frozen semantic requirements. The defect and its repair are recorded in the `R2R1` receipts later in this section, in matrix section 8, and in `WDD-20260805-002`. The authoritative evidence is the post-repair stage run on `368b828` and the independent rerun in the fresh-blind audit report.)* |

### Independent coordinator reruns on the exact proof tree

The coordinator independently obtained, on the exact proof-bearing tree
`cc75bcb8b334d2de39007a4213affa0a38deafd7`:

- project-skill preflight PASS;
- `lake build RMQ.Validation.EGCPFinalFalsification` PASS;
- `lake build RMQ` PASS;
- strict design-decision check PASS;
- strict claim drift PASS (1,511 hits, zero failures);
- forbidden/native scans with zero matches;
- diff and cleanliness checks PASS;
- `R2-ALLSIZE` replay PASS in 982 seconds: seven commissioned REJECTs,
  descendant-termination self-test PASS, SHA restoration PASS, terminal
  clean state.

Those reruns are the coordinator's own verification evidence, distinct from
the worker-side runs above. Because that earlier correction was
documentation-only on top of the frozen proof parent, the Lean builds and the
replay stage were not repeated for that report commit; its post-commit checks
were the documentation-appropriate subset: strict claim drift, strict
design-decision check against the exact base, committed-range
`git diff --check`, UTF-8 inspection, and final cleanliness.

### `R2R1` repair receipts on the frozen proof-bearing repair parent

A coordinator-commissioned repair rung (`EG-CP-ALLSIZE-R2R1`) subsequently
landed as the frozen proof-bearing commit
`368b828e0711dfd10a04ca90eb19c7b0d6ccfd13` (tree
`730a8746240bdf6f705d67f9283f6d9db8f25123`), whose parent is the prior
report commit `7abc2f5c52c7ef20faac5e4bfe23972593f60271`. The present
document revision is a report-only child of that frozen repair commit and
does not embed its own hash. The repair changed exactly seven paths:
`scripts/eg_cp_final_falsification_replay.ps1`, `scripts/axiom_check.lean`,
`RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerLogicalSimulation.lean`,
`RMQ/Validation/EGCPFinalFalsification.lean`,
`docs/internal/DESIGN_DECISIONS.md`,
`docs/internal/WORKFLOW_DESIGN_DECISIONS.md`, and
`docs/internal/EG_CP_FINAL_FALSIFICATION_MATRIX.md` (append-only repair
addendum, section 8, inside delimited markers; every frozen row
byte-identical).

Defect repaired: the original working-tree mutation bodies for four
registry entries edited an unused optional surface rather than enacting the
frozen mutation description, so their earlier REJECT verdicts, while
commissioned, did not exercise the semantic defense. The frozen registry
itself (IDs, order, mutation descriptions, expected verdicts, selectors,
deadline contracts, restoration contracts, and process-tree controls) was
not changed; only the enacted mutation bodies and the runner's mechanical
activation check are new. `M03` remains a signature-level mutation by
design; `M08` and `M12` were already semantic and are preserved. The runner
now verifies, before each build, that every declared activation needle is
present in the mutated body actually written to disk, failing the stage
with a distinct `ACTIVATION-MISSING` outcome otherwise.

| Entry | Repaired enacted behavior | Failing surface (honest guarding module) |
| --- | --- | --- |
| `M05-SIBLING-STORE` | `packedReviewerRunAgainstMemory` drives a sibling logical store `memory ++ [[]]` instead of the counted memory. | `PackedCellProbe/ReviewerController.lean`, surface `store identity`. |
| `M06-ANSWER-ORACLE` | the normalize-whole done arm discards the consumed value and returns a semantic answer oracle `some n`. | `PackedCellProbe/ReviewerControllerProof.lean`, surface `oracle independence`. |
| `M07-DISCONNECTED-TRACE` | the expected physical trace is replaced by a disconnected forged empty trace in the then-branch. | `PackedCellProbe/ReviewerControllerProof.lean`, surface `trace execution`. |
| `M11-SIBLING-PAYLOAD` | `packedReviewerSerializedBits` serializes a sibling execution payload `packedReviewerPayloadBits shape ++ [false]`. | `PackedCellProbe/ReviewerMemory.lean`, surface `public / same-object composition`. |

Public axiom inventory (`lake env lean scripts/axiom_check.lean`, exit 0,
on the frozen repair tree): `packedReviewerPayloadBits_eq_buildPayload`,
`packedReviewerMemory_length_mul_width_le`, `packedReviewerRho_littleO`,
`packedReviewerRunAgainstMemory_public_outcome`, and
`packedReviewerRunAgainstMemory_public_certificate` each depend on exactly
`[propext, Classical.choice, Quot.sound]`;
`packedReviewerRunAgainstMemory_trace_length_le_427` depends on
`[propext, Quot.sound]`. No `sorryAx`, no `Lean.ofReduceBool`, no
`Lean.trustCompiler` appears in any receipt.

Verification battery on the frozen repair commit (heavy commands under the
global heavy-verification mutex):

| Check | Outcome |
| --- | --- |
| `lake build RMQ.Validation.EGCPFinalFalsification` | PASS (exit 0, warm). |
| `lake build RMQ` | PASS (exit 0, warm; both builds plus axiom check 3 m 34 s total). |
| `lake env lean scripts/axiom_check.lean` | PASS (exit 0; receipts above). |
| `R2-ALLSIZE` replay, single run, no `-SkipSelfTest` | PASS (exit 0, 8 m 20 s): registry integrity OK (16 ordered entries), descendant-termination self-test PASS, all four repaired activation checks passed (2 needles each), all seven commissioned REJECTs (`M03`, `M05`, `M06`, `M07`, `M08`, `M11`, `M12`) at their commissioned surfaces, SHA256-verified restoration per case, terminal `git status --porcelain` empty. |
| Strict claim drift | PASS (1,511 hits, 0 strict failures). |
| Strict design-decision check vs `6bf28dee` | PASS (32 changed files: 26 code, 4 workflow, 3 neutral). |
| Forbidden-token/Mathlib scan | PASS (zero matches over `RMQ`, `lakefile.toml`). |
| `native_decide`/`ofReduceBool` scan | PASS (zero matches over `RMQ`). |
| Committed-range and working-tree `git diff --check` | PASS (clean). |
| Final `git status --porcelain` | PASS (empty). |

Because the present revision is report-only on top of the frozen repair
commit, the Lean builds and the replay stage are not repeated for it; its
post-commit checks are the documentation-appropriate subset: strict claim
drift, strict design-decision check against the exact base, committed-range
`git diff --check`, UTF-8 inspection, and final cleanliness.

## 10. Validation and anti-bypass status

The frozen validation root `RMQ/Validation/EGCPFinalFalsification.lean`
elaborates end to end. It pins the raw controller/driver signatures, the
canonical control-tag widths, reviewer-memory-only replies and dynamic-store
agreement, ordered logical and physical occurrence expansion, the structural
and grouped 427 caps, allocation/address/reply/result widths, the public
outcome, the exact 26-field public certificate, the independent
required-facts restatement, and the identical-object public consumer. The
three previously missing public names are inhabited:
`packedReviewerDriveLogical_210_request_operands_fit`,
`PackedReviewerRunGrouping.request_operands_fit`, and
`packedReviewerRunAgainstMemory_public_certificate`. The owned `R2-ALLSIZE`
replay stage executed with all seven commissioned REJECT verdicts
(`M03`, `M05`, `M06`, `M07`, `M08`, `M11`, `M12`), SHA-verified restoration,
and a terminal clean tree, in both the worker-side run and the independent
coordinator rerun. Under the `R2R1` repair the four formerly inert mutation
bodies (`M05`, `M06`, `M07`, `M11`) were repaired to semantic mutations
with mechanical activation checks, and the stage was re-executed once on
the frozen repair parent with identical commissioned verdicts (receipts in
section 9).

## 11. Explicit deferrals and full-node boundary

| Item | Disposition |
| --- | --- |
| `FG-11` liveness mutation campaign | Deferred. Blocking for the full node, not this local rung. |
| Remainder of `FG-12` (full sixteen-case registry completion) | Deferred beyond the owned seven-case `R2-ALLSIZE` stage. The exact registry, selector, deadline, descendant-termination, restoration, and clean-state contracts are preserved. Blocking for the full node. |
| Full `FG-14` boundary campaign | Deferred beyond the boundary facts consumed by `R2-08`/`R2-09`. Blocking for the full node. |
| `FG-15` final architecture publication record | Deferred. This worker report is local-rung evidence, not the publication/acceptance record. |
| Coordinator reconstruction and acceptance | Required; not performed or claimed by this worker. |
| Fresh-blind exact-commit audit | Required; not performed or claimed by this worker. |
| Full EG-CP node | Remains open until all `FG-01` through `FG-15` rows, inherited invariants, replay requirements, final checks, coordinator reconstruction, and fresh-blind audit close. |

The deferrals limit this rung's scope; they do not change the frozen
requirements or make deferred work optional for the full node.

## 12. Proof digestion

**Conceptual change.** The predecessor route relied on `localStride = 1`
and an informal astronomical cutoff. This rung replaces that route with a
machine that discovers the content-dependent directory length by charged
reads of its own representation: the one header word carries only
`longCount`, and three fixed-address charged reads recover `sparseCount`
before any sparse-dependent address is formed. Conceptually, the space
theorem and the query machine now consume the same serialized object, and
the query cost is accounted on the same physical trace that the
correctness theorem constrains.

**Plain-English meaning.** The succinct reviewer representation answers
every range-minimum query using one real packed memory, at every input
size, with no oracle: the machine reads the representation itself to learn
its own layout, then follows a fixed request/reply program whose physical
events match one-for-one with the established logical query, all inside
one modeled word width. At most 427 physical probes ever occur (1 header
cell, at most 2 x 3 discovery cells, and at most 2 x 210 logical attempts,
where 210 is driver fuel -- an upper bound on logical attempts, not an
exact read count and not a Word-RAM time bound). The hard completed part
was not the high-level RMQ result but demonstrating that every live
intermediate scalar and every request operand fits the same modeled word
while preserving the exact physical prefix that produced it -- discharged
by the select, LCA, and whole canonical towers and the coupled physical
controller chain of section 6.

**Live assumptions.** The claim lives in the packed counted cell-probe
model: cost is the number of charged physical probes of the declared word
width, not wall-clock or Word-RAM instruction time; the reference
semantics is the guarded public `queryTraceResult`; the kernel checks
everything down to `propext`, `Classical.choice`, and `Quot.sound` (the
427 probe-cap theorem needs only `propext` and `Quot.sound`). Raw
bit-addressed serialized-payload querying (`S1`) is deferred and not
claimed here. Coordinator acceptance of this rung is still required.

**Strongest skeptical question.** "Your 427-probe cap constrains a trace
object your own definitions produce -- what forces the machine to actually
consult the counted memory rather than smuggling the answer or decorating
a disconnected log?" The defense is threefold and now mechanically
exercised: the terminal result and every decisive branch trace back to
consumed physical replies through the coupled controller invariant
(`egcpAllSizeMissingReplyFails`, `egcpAllSizeSameRunPublicOutcome`); the
trace accumulates only through driver steps against the one counted memory
(`egcpAllSizeDriverMemoryOnly`,
`egcpAllSizeEveryLogicalReadFromReviewerMemory`); and the repaired
semantic replay REJECTs the exact three smuggling routes -- an answer
oracle (`M06`), a disconnected forged trace (`M07`), and sibling
store/payload substitution (`M05`, `M11`) -- with mechanical activation
checks proving each mutation was really enacted before the build refuted
it.

<!-- STAGEF-FINAL-RECORD-EG-CP-STAGEF-CLOSE-R2-BEGIN -->

---

# Stage-F final falsification record (`EG-CP-STAGEF-CLOSE-R2`)

Append-only worker record for the repaired Stage-F residual candidate; the
frozen contract is matrix section 10 as reconstructed with the two
authorized repair amendments. Nothing here records coordinator acceptance,
`FEASIBILITY_PASS`, Stage A, publication, or public-claim synchronization.
The rejected candidate `cefc4efa255d0456c94d217a9819c6dbf0325cff` is source
evidence only.

## 1. Exact identity

| Object | Exact value |
| --- | --- |
| Worker branch | `codex/eg-cp-stagef-close-r2` |
| Absolute worktree | `C:\Users\poin\Documents\RMQ\.claude\worktrees\eg-cp-stagef-close-r2` |
| Exact base | `0f386723f56deae5eb39418e535f56e7a2b347dd` (tree `ec0ab9c96f598ddc81a0e30424410461296abe71`) |
| Governance ref | `f0c7232a8a52b8d61ead5e96d72a8a849bc094b5` (verified ancestor; preflight PASS at start, resume, and finish) |
| Rejected source candidate (evidence only) | `cefc4efa255d0456c94d217a9819c6dbf0325cff` (tree `efc76707c373dff3e2dccfa7a96d1180a2df7e64`) |
| Commit A (contract + round log + `WDD-…-001`) | `8d22684` |
| Commit B (capstone with `R2` field + header liveness + enactments + `DD-…-076`/`WDD-…-002`) | `c1eada6` |
| Commit C (fixture + `R1` connection + consumers + `DD-…-077`/`WDD-…-003`) | `37764ad` |
| Commit D (deadline calibration final form + `WDD-…-004`) | `f105971` |
| Certification frozen proof/script tree (full mode ran here) | `f105971` |
| Commit E (this record + ledger cells + worklog + `WDD-…-005`) | the final documentation commit |

## 2. The two audited semantic repairs, `P`/`Q` side by side

### `R1` — decisive provenance and transition (`SF-FG11-DECISIVE`)

**Accepted `P` (the repaired conclusion, existential over the pinned
fixture, all conjuncts on the identical canonical objects):**
`packedReviewerDecisiveCellConnection` concludes, in the theorem type
itself: trace position `11` and its event; `event.request.origin =
.wholeQuery request` with `request.invocation.instruction = .leftSelect`,
`request.invocation.argument = 0`, `request.invocation.argument2 = 0`,
`request.site = .entryFirstOffset`, `request.segment = 8`,
`request.index = 0`; `event.request.address = 8`; `event.reply = some
replyCell` and `event.reply = memory[event.request.address]?`;
`preState = packedReviewerDriveStateAt memory (controller n 0 3) 11` (the
checked prefix fold, proved equal to the driver's own state by
`packedReviewerDriveAux_decompose`); `packedReviewerNextRequest preState =
some event.request`; `packedReviewerConsumeReply preState event.reply =
postState`; `(driveAux memory (measure - 12) postState).terminal = some
(some 1)` and `.state = .done (some 1)`; the run's own terminal/state; and
the guarded leftmost reference `some 1`.

**Challenged `Q` (both challenge directions):** (i) erasing the
instruction/site/segment/index conclusion, and (ii) removing the
transition/continuation link — jointly enacted by replacing the producer
with the rejected origin-erasing proposition. **Failing consumer, probed
on this branch:** `egcpStageFDecisiveCellConnection` in
`RMQ/Validation/EGCPFinalFalsification.lean` fails (type mismatch at its
`exact` producer application, observed at line 3236) with byte-exact
SHA-verified restoration. The prefix-fold decomposition is not an
equivalent substitute but the driver's own fold; `packedReviewerDriveStep`
performs exactly the driver's transition, so the pre-state, transition,
and continuation are pinned by construction.

**Preserved:** `packedReviewerDecisiveCellLiveness` at the returned-answer
projection (`some (some 1)` vs `some (some 2)`, unequal) and the identical
canonical/mutated objects consumed by `SF-M06-BRIDGE`
(`packedReviewerNoMetadataCompletion`) are byte-for-byte the audited-good
material.

### `R2` — the capstone input boundary (`FG-13` / `EG-CP-F13`)

**Accepted `P`:** capstone field `controller_input_boundary` (universal
over `xs`, `left`, `right`, over the same let-bound objects as every other
field): `@packedReviewerController = fun (n left right : Nat) =>
packedReviewerController n left right` — an equation that elaborates only
at the exact public entry type `Nat -> Nat -> Nat ->
PackedReviewerControllerState` — together with
`packedReviewerRunAgainstMemory (packedReviewerMemory shape) shape.size
left right = packedReviewerDriveAgainstMemoryAux (packedReviewerMemory
shape) (packedReviewerControllerMeasure (packedReviewerController
shape.size left right)) (packedReviewerController shape.size left right)`,
exhibiting that the controller receives only `(n, left, right)` while
memory is supplied only to the physical driver interface. The former facts
are retained as separate accurately-named conjuncts
`closed_length_and_memory_arity` and `store_agreement_determinism`; they
are not called an input boundary.

**Challenged `Q` (both challenge directions):** (i) an added
`M03`-style controller shape parameter — probed on this branch: the field
is ill-typed and `ReviewerCapstone.lean` (line 114, type mismatch) is the
first failing module; replay case `M03` REJECTs there as commissioned;
(ii) the field reduced back to the old length/store conjunction — probed
on this branch: the literal expected-type consumer
`EGCPStageFCapstoneFacts` / `egcpStageFCapstoneFactsExact` in
`RMQ/Validation/EGCPFinalFalsification.lean` fails (type mismatch at line
2989), with byte-exact SHA-verified restoration in both probes.

## 3. Row-by-row evidence for matrix section 10

The audited-good rows carry over with their evidence unchanged in
substance; the two repaired rows carry the strengthened evidence above.

- `SF-FG11-HEADER`: `packedReviewerHeaderCellAddressLiveness` (universal
  second-address movement under a header-cell replacement, address
  projection), exact-form corollary `_proj`, opening pin
  `packedReviewerRunOpensWithHeader`; consumers
  `egcpStageFHeaderAddressLiveness`, `egcpStageFRunOpensWithHeader`;
  replay `M01`/`M14` REJECT at `PackedCellProbe/ReviewerControllerProof.lean`.
- `SF-FG11-DECISIVE`: section 2 (`R1`) above; consumers
  `egcpStageFDecisiveCellLiveness`, `egcpStageFDecisiveCellConnection`.
- `SF-FG11-UNREAD`: `packedReviewerUnreadCellAccept` (allocated `4 < 22`;
  no trace event addresses cell `4`; complete run-record equality for
  EVERY replacement via the ordered agreement route) + pinned instance;
  consumers `egcpStageFUnreadCellAccept`, `egcpStageFUnreadCellAcceptPinned`;
  replay `A02` ACCEPTs on the frozen replacement-value patch.
- `SF-M06-BRIDGE`: `packedReviewerNoMetadataCompletion` — no completion
  function of `(n, left, right)` alone (covering the enacted `some n` and
  the reference-semantics oracle of the pinned query) can produce both
  fixture terminals; guards and quantifiers identical to the decisive
  pair; consumer `egcpStageFNoMetadataCompletion`; the joint `M06`/`M07`
  REJECTs stand.
- `FG-13` capstone: `PackedReviewerStageFCapstone`, fourteen conjuncts on
  identical objects (payload identity; header ++ payload; exact final
  padding; one cell width; `2n + rho` and `LittleOLinear rho`; memory-only
  backing; allocation/success; ordered grouping; derived `427`; guarded
  reference result; `controller_input_boundary`;
  `closed_length_and_memory_arity`; `store_agreement_determinism`);
  producer by projection plus two `rfl`s; consumers
  `egcpStageFCapstoneSignature`, `EGCPStageFCapstoneFacts`,
  `egcpStageFCapstoneFactsExact`. Trust: hygiene/native scans zero
  matches; all six curated Stage-F axiom entries on
  `[propext, Classical.choice, Quot.sound]`.
- `FG-14`: every boundary instance instantiates the one universal capstone
  (empty; singleton; both size-two lists with answer-divergence
  distinctness; crossover `5487/5488/5489`; readiness six with the
  `Boundaries.lean` neighbour facts; invalid queries with the exact
  `.done none` empty-trace run; duplicate-minimum `[7,3,3]`/`(0,3)`
  leftmost `some 1` through `scanWindow`/`queryCosted_exact`/
  `queryCosted_leftmost`); uniformity pins + `M04`/`M11` REJECTs close
  no-second-representation.
- `FG-12` and the three `REPLAY-*` contracts: section 4.
- `FG-15`: this record, the filled section 10.8 cells, the worklog entry,
  and the commit-A round-log records.
- Inherited invariants (`INV-VALUE-DEPENDENCY`, `INV-SEMANTIC-NONVACUITY`,
  `INV-STORE-AGREEMENT`, `INV-READ-BACKING`, `INV-PUBLIC-COMPOSITION`,
  `INV-MUTATION-REPRODUCIBILITY`, `INV-CATEGORY-SEPARATION`) close at the
  same objects through the rows above; `FROZEN-ACCEPTANCE-ROW-BYTE-INTEGRITY`
  in section 6.

## 4. Full-registry outcome per ID and OS

Full mode ran exactly once on the frozen proof/script tree `f105971`
(Windows 11, Windows PowerShell 5.1): **`FULL MODE PASS`, exit 0,
1430.4 s**; calibration clean build 2 s, mutated-chain probe 228 s,
per-case deadline 912 s; registry integrity 16 ordered entries, 2 ACCEPT /
14 REJECT; descendant self-test PASS; activation checks passed on every
semantic mutant; every mutation restored with a verified SHA256; terminal
tree clean.

| # | ID | Outcome | Surface reached |
| --- | --- | --- | --- |
| 1 | `A01-PRODUCTION-EXPECTED-ACCEPT` | ACCEPT | (unchanged candidate builds) |
| 2 | `A02-UNREAD-CELL-EXPECTED-ACCEPT` | ACCEPT | (frozen replacement-value patch; pinned theorems elaborate) |
| 3 | `M01-WRONG-LONG-COUNT` | REJECT | `PackedCellProbe/ReviewerControllerProof.lean` |
| 4 | `M02-HOST-LONG-COUNT-MIRROR` | REJECT | `PackedCellProbe/ReviewerController.lean` |
| 5 | `M03-SHAPE-PARAMETER` | REJECT | `PackedCellProbe/ReviewerCapstone.lean` (the exact-type input boundary) |
| 6 | `M04-CANONICAL-SHAPE-BY-N` | REJECT | `PackedCellProbe/ReviewerController.lean` |
| 7 | `M05-SIBLING-STORE` | REJECT | `PackedCellProbe/ReviewerController.lean` |
| 8 | `M06-ANSWER-ORACLE` | REJECT | `PackedCellProbe/ReviewerControllerProof.lean` |
| 9 | `M07-DISCONNECTED-TRACE` | REJECT | `PackedCellProbe/ReviewerControllerProof.lean` |
| 10 | `M08-FORGED-PROBE-CAP` | REJECT | `PackedCellProbe/ReviewerCapstone.lean` (the derived-measure consumer) |
| 11 | `M09-WRONG-CELL-CROSSING` | REJECT | `PackedCellProbe/Probe.lean` |
| 12 | `M10-SPARSE-COUNT-DEPENDENCY` | REJECT | `PackedCellProbe/SourceGeometry.lean` |
| 13 | `M11-SIBLING-PAYLOAD` | REJECT | `PackedCellProbe/ReviewerMemory.lean` |
| 14 | `M12-PUBLIC-TYPE-WEAKENING` | REJECT | `PackedCellProbe/ReviewerCapstone.lean` (the certificate-projecting producer) |
| 15 | `M13-HIDDEN-UNCOUNTED-TABLE` | REJECT | `PackedCellProbe/ReviewerController.lean` |
| 16 | `M14-LONG-COUNT-IGNORED` | REJECT | `PackedCellProbe/ReviewerControllerProof.lean` |

OS termination receipts on the identical frozen tree: Windows
`-SelfTestOnly` PASS (6.4 s) and the full-mode run's own self-test PASS;
WSL `Ubuntu-24.04` under `pwsh 7.6.4` `-SelfTestOnly` PASS (51.3 s) —
registry integrity plus owned root-and-descendant termination verified by
pid on both gate OSes, locally, with no push and no new authority.
Development-loop receipt on the same tree: exact selector
`A01-PRODUCTION-EXPECTED-ACCEPT` ACCEPT (469 s wall including the 244 s
calibration probe, 976 s deadline).

## 5. `EG-CP-F12`: the residual estimate (`R3`)

**Numeric estimate: 0 (zero) focused proof-days of local Stage-F theorem
work remain after this repair** -- within the ten-focused-proof-day ceiling
the `FEASIBILITY_PASS` rule requires, with margin.

**Closed consumer inventory (local Stage-F proof work -- every item exists
on committed bytes of this candidate, with its consumer; classification: no
remaining theorem work):**

| Theorem / definition | Independent consumer | Class |
| --- | --- | --- |
| `PackedReviewerStageFCapstone` (14 conjuncts) + `packedReviewerStageFCapstone_holds` | `EGCPStageFCapstoneFacts` / `egcpStageFCapstoneFactsExact`, `egcpStageFCapstoneSignature` | closed, no remaining work |
| `packedReviewerHeaderCellAddressLiveness` + `_proj` + `packedReviewerRunOpensWithHeader` | `egcpStageFHeaderAddressLiveness`, `egcpStageFRunOpensWithHeader` | closed, no remaining work |
| `packedReviewerDecisiveCellLiveness` | `egcpStageFDecisiveCellLiveness` | closed, no remaining work |
| `packedReviewerDriveStep` / `packedReviewerDriveStateAt` / `packedReviewerDriveStateAt_shift` / `packedReviewerDriveAux_succ_of_request` / `packedReviewerDriveStep_of_request` / `packedReviewerDriveAux_decompose` | consumed by the strengthened connection theorem | closed, no remaining work |
| `packedReviewerDecisiveCellConnection` (`R1`-strengthened) | `egcpStageFDecisiveCellConnection` (full literal expected type) | closed, no remaining work |
| `packedReviewerUnreadCellAccept` + `packedReviewerUnreadCellAcceptPinned` + `egcpStageFUnreadReplacementCell` | `egcpStageFUnreadCellAccept`, `egcpStageFUnreadCellAcceptPinned`, replay `A02` | closed, no remaining work |
| `packedReviewerNoMetadataCompletion` (`M06` bridge) | `egcpStageFNoMetadataCompletion` | closed, no remaining work |
| `FG-14` instances (empty/singleton/size-two pair/crossover triple/readiness six/invalid queries/duplicate-minimum) + uniformity pins + `Boundaries.lean` neighbour facts | the `egcpStageF*` instance consumers, `egcpStageFNoSecondRepresentation`, `egcpStageFReadinessNeighbors` | closed, no remaining work |
| Fixture evaluation pins (memory literal, 68-address trace, terminal, mutant terminal, event 11) | consumed by the liveness/connection theorems and replay `A02` | closed, no remaining work |
| Sixteen-entry replay registry, all targets enacted | full-mode certification run; per-case receipts | closed, no remaining work |
| Six curated Stage-F axiom entries | `scripts/axiom_check.lean` | closed, no remaining work |

**Non-proof consumers, named separately (not proof-days, not conflated):**

| Item | Class |
| --- | --- |
| Coordinator reconstruction of this exact candidate | coordinator evidence review |
| Fresh-blind exact-commit audit | fresh audit |
| `FEASIBILITY_PASS` decision; Stage-A `A01`..`A13` matrix freeze and campaign | downstream Stage-A (post-`FEASIBILITY_PASS`; its own proof cost is Stage-A scoped, not Stage-F residual) |
| Public-claim synchronization / headline selection | downstream public-sync |
| `S1` bit-addressed probe semantics/accounting; `V1` | downstream S1/V1 |

**Assumptions behind the estimate:** (a) the frozen section-10 contract,
as corrected by the two authorized repair amendments, is the complete
Stage-F obligation set (the roadmap's exact next sequencing names no
other); (b) the coordinator accepts those two corrections as binding; (c)
no audit finding reopens a closed row -- a reopened row would be priced as
its own repair, not absorbed silently.

**Unknown dynamic inputs: none.** The controller receives exactly
`(n, left, right)` (the exact-type `controller_input_boundary` pin), memory
is supplied only to the physical driver interface (the run factorization
conjunct), and the two decoded counts (`longCount`, `sparseCount`) are
obtained by charged reads of the counted memory (the K1 chain of the
accepted rung). `EG-CP-F12-RESIDUAL-ESTIMATE` is therefore closed: the
inventory is closed and no dynamic input is unaccounted.

## 6. Inherited-row byte integrity and lifecycle accuracy (`R4`)

**Frozen rows:** strict UTF-8 section-scoped comparison from the exact base
to the final candidate: **148 base rows byte-exact, 0 missing, 0
duplicated, 0 changed; 34 added rows, every one inside the section-10
amendment**; no BOM, no mojibake. Section-10 differences relative to the
rejected candidate are exactly the two authorized contract corrections
plus evidence/status/outcome fields.

**Changed paths (computed from Git, not copied):** `git diff --name-only
0f38672..HEAD` on the final candidate lists exactly twelve paths — the ten
of commits A-D (`docs/internal/AUDIT_AND_A_DESIGN.md`,
`docs/internal/EG_CP_FINAL_FALSIFICATION_MATRIX.md`,
`docs/internal/WORKFLOW_DESIGN_DECISIONS.md`,
`RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/Boundaries.lean`,
`RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerCapstone.lean`,
`scripts/eg_cp_final_falsification_replay.ps1`,
`docs/internal/DESIGN_DECISIONS.md`, `RMQ.lean`,
`RMQ/Validation/EGCPFinalFalsification.lean`, `scripts/axiom_check.lean`)
plus this commit's `docs/internal/EG_CP_FINAL_FALSIFICATION_RESULT.md` and
`docs/internal/R2_ALLSIZE_WORKLOG.md`. The exact command receipt and the
strict checker's own category counts for the final range are reproduced in
the worker terminal report; the counts there sum to the total under that
checker.

**Per-commit workflow-ledger discipline (re-checked on the final tree in a
detached temporary worktree against each exact parent):**

| Commit | Parent | Workflow-sensitive paths | Same-commit WDD | Strict check |
| --- | --- | --- | --- | --- |
| `8d22684` | `0f38672` | matrix, round log | `WDD-20260806-001` | PASS |
| `c1eada6` | `8d22684` | replay runner | `WDD-20260806-002` | PASS |
| `37764ad` | `c1eada6` | replay runner, axiom script | `WDD-20260806-003` | PASS |
| `f105971` | `37764ad` | replay runner | `WDD-20260806-004` | PASS |
| commit E | `f105971` | matrix (10.8 outcome cells) | `WDD-20260806-005` | run immediately after the commit; receipt in the worker terminal report |

No entry landed late on this branch; the rejected branch's two one-commit
lags are repaired by construction, not excused.

## 7. Verification command ledger (observed on this worktree)

| Command | Outcome |
| --- | --- |
| `project_skill_preflight.ps1` (governance `f0c7232a…`, checkout `0f38672…`) | PASS at start, at the interruption resume, and on the frozen tree. |
| Windows `-SelfTestOnly` | PASS, 6.4 s. |
| WSL Ubuntu `pwsh -SelfTestOnly` (same script bytes) | PASS, 51.3 s. |
| Exact selector `-Case A01-PRODUCTION-EXPECTED-ACCEPT` | ACCEPT, exit 0, 469 s. |
| Full replay (exactly once, frozen tree) | `FULL MODE PASS`, exit 0, 1430.4 s (section 4). |
| `lake build RMQ.Validation.EGCPFinalFalsification` | PASS exit 0, 81.9 s (post-replay chain rebuild). |
| `lake build RMQ` | PASS exit 0, 16 s (warm tree). |
| `lake env lean scripts/axiom_check.lean` | PASS exit 0, 257.2 s: `lake env lean scripts/axiom_check.lean`; the six curated Stage-F entries (`packedReviewerStageFCapstone_holds`, `packedReviewerHeaderCellAddressLiveness`, `packedReviewerDecisiveCellLiveness`, `packedReviewerDecisiveCellConnection`, `packedReviewerUnreadCellAccept`, `packedReviewerNoMetadataCompletion`) each depend on exactly `[propext, Classical.choice, Quot.sound]`; zero `sorryAx`, `ofReduceBool`, or `trustCompiler` occurrences anywhere in the printed inventory. |
| Forbidden/native/Mathlib scans | zero matches for the forbidden-token scan over `RMQ` and `lakefile.toml` and for the native-shortcut scan over `RMQ`. |
| `claim_drift_scan.ps1 -Strict` | rerun on the tree containing this record immediately before the final commit; receipt in the worker terminal report. |
| `design_decision_check.ps1 -Strict -Base 0f38672…` (final branch) | run on the final candidate; receipt in the worker terminal report. |
| Per-commit strict checks at each exact parent | PASS at commit time and in the detached re-check (section 6). |
| Strict UTF-8 frozen-row comparison | PASS (section 6). |
| `git diff --check` (committed range and working tree); final cleanliness | receipts in the worker terminal report. |
| `M03` shape-parameter probe; `R1` weaken-producer probe; `R2` field-reduction probe | all three REJECT at their named consumers with SHA-verified restoration (section 2). |
| Aggregate `scripts/gate.ps1` | skipped: every changed surface and acceptance row is owned by the named checks above; a duplicate aggregate run on the unchanged tree adds no unique coverage. |

## 8. Still-open downstream nodes

| Item | Status |
| --- | --- |
| Coordinator audit (reconstruction) of this exact candidate | REQUESTED; not performed or claimed here. |
| Fresh-blind exact-commit audit | REQUESTED; required before any disposition. |
| `FEASIBILITY_PASS` | NOT RECORDED; coordinator decision. |
| Stage A `A01`..`A13` and its matrix freeze | NOT STARTED; gated on `FEASIBILITY_PASS`. |
| Public-claim synchronization, headline promotion | OPEN, untouched. |
| `S1`, `V1` | OPEN, not claimed. |
| Full EG-CP node closure | OPEN; requires all of the above. |

## 9. Four-part proof digestion

**Conceptual change.** The rejected candidate proved the right facts but
let two of its most important propositions say less than their proofs
knew: the decisive-occurrence theorem constructed the producing invocation
and transition internally and then erased them from its conclusion, and
the capstone called a bundle of length/store facts a "dynamic-input
boundary" when nothing in it pinned what the controller may receive. The
repair makes the theorems SAY what the machine DOES: the decisive probe's
provenance now survives as conclusion conjuncts anchored by a checked
driver prefix decomposition, and the capstone now carries an exact-type
equation that cannot elaborate if the controller grows any parameter
beyond `(n, left, right)`.

**Plain English.** We can now point at probe number 12 of the canonical
run and say, in the theorem's own statement: this is the `leftSelect`
instruction reading the select layer's first-offset entry; here is the
controller state that asked for it, computed by replaying the driver's own
first eleven steps; here is the reply it got from cell 8; and here is the
checked path from consuming that reply to the machine answering "index 1".
And the machine's front door provably accepts three numbers and nothing
else — memory only ever enters through the driver.

**Live assumptions.** The Lean kernel and pinned toolchain (v4.22.0) with
the standard axioms; the cell-probe model boundary (`427` is the derived
physical cap, `210` is logical-attempt fuel, never an exact read count; no
Word-RAM instruction-time or preprocessing claim); the replay harness's
OS-level evidence certifies its cases, not statements beyond them; the
frozen section-10 contract as corrected is the Stage-F obligation set.

**Strongest skeptical question.** "Your pre-state is a fold you defined
yourself — how do I know `packedReviewerDriveStateAt` at position 11 is
the driver's actual state and not a convenient stand-in?" Answer recorded:
`packedReviewerDriveAux_decompose` proves, for every memory, fuel, state,
and position, that the fold is live, computes exactly the emitted request
of the recorded event, and that restarting the driver at the fold with the
remaining fuel reproduces the whole run's terminal, state, and trace
suffix — so the fold and the driver cannot disagree anywhere a trace
event exists, and the continuation conjuncts consume the fold at the very
fuel arithmetic the driver uses. The residual question — value liveness at
sizes beyond the pinned fixture — remains a strictly-stronger-than-frozen
item listed for the coordinator, exactly as before.

<!-- STAGEF-FINAL-RECORD-EG-CP-STAGEF-CLOSE-R2-END -->
