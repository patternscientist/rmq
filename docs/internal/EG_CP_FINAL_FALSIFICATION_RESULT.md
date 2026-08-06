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
