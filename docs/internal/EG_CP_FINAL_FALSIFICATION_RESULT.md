# EG-CP all-size reviewer-machine rung -- worker result

> **Authoritative status: INCOMPLETE.**
>
> This report covers local rung `EG-CP-ALLSIZE-R1`. Source construction and proof
> work are still in progress. `ReviewerControllerProof.lean` has not yet reached a
> green focused elaboration, `ReviewerControllerStateProof.lean` still lacks its
> reachable-state and certificate closure, the validation root therefore does not
> elaborate, and no final-tree certification has run. Nothing below records
> coordinator acceptance, integration, publication, or closure of the full EG-CP
> node.

## 1. Exact identity and provenance

| Item | Value |
| --- | --- |
| Local rung | `EG-CP-ALLSIZE-R1` |
| Branch | `codex/eg-cp-allsize-reviewer-machine-r1` |
| Worktree | `C:\Users\poin\.codex\worktrees\e886\RMQ` |
| Exact branch base | `6bf28dee32c96da4705b139959fd35e4a782bac4` |
| Base tree | `4d173458db3e1ad33186a2f843ee7dd5cbd87d97` |
| Base parent | `d0237a3fa9d01f4ed06fe25d58a2a79981db4809` |
| Frozen-matrix ancestor | `0a18548539035f69f68c1b44031fba64df8297f3` |
| Workflow-governance ref | `f0c7232a8a52b8d61ead5e96d72a8a849bc094b5` |
| Final HEAD | `<FINAL_HEAD>` |
| Final tree | `<FINAL_TREE>` |
| Final parent or parents | `<FINAL_PARENT_OR_PARENTS>` |
| Final commit count since base | `<FINAL_COMMIT_COUNT_SINCE_BASE>` |

Project-skill preflight passed before substantive work at exact base `6bf28dee`,
with `rmq-proof-sprint` required and the actual runtime catalog
`rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint`. That is a startup precondition,
not evidence that any theorem or final gate below is green.

### Predecessor provenance retained

The 1,907-line predecessor report described the older branch
`codex/eg-cp-final-falsification-gate-r1`, originally based at
`1490c97b399d136bad4e18953441da433d130d4d` and later continued from
`6078a29c318b0bd167b87b05629f576c53266fea`. Its last independently summarized
close-half state was commit `6db4c6a03af8f5432c907a5ca967d07b30964f82`,
tree `2eb27ffcc2eeb9132c5bd06b88539db6231c7863`, with 105 commits from
`6078a29`. The current base `6bf28dee` is 107 commits after `6078a29` and retains
the frozen ancestor `0a18548`.

That predecessor established the reviewer payload, memory, space accounting,
conditional probes, access-half lowering, and close segments 21 and 22, while
leaving segment 20 and the physical whole-query machine open. Those checked
leaves remain provenance for this rung. Its historical row statuses, clean-tree
claims, builds, and replay verdicts are not current-tree certification.

The controlling requirements for this rung are the append-only `R2-*` rows in
section 7 of `docs/internal/EG_CP_FINAL_FALSIFICATION_MATRIX.md`. The original
`FG-*` rows remain the frozen historical record and are not silently reinterpreted
here.

## 2. Current construction in one paragraph

The branch keeps a one-cell K1 header containing `longCount`. It obtains the only
other content-dependent layout count, `sparseCount`, by three fixed charged logical
reads whose addresses depend only on `n` and the decoded `longCount`. The resulting
all-size closed geometry addresses the exact canonical reviewer payload, including
the eight ragged segment-20 component stores. A proof-free first-order controller
then performs header, K1 prelude, and whole-query request/reply steps against one
external reviewer-memory array. The proof side relates those exact replies to the
canonical global logical store, preserves logical occurrence and physical probe
multiplicity, and targets the guarded public `queryTraceResult`. The intended
physical cap is derived from the trace decomposition as

```
1 header cell + at most 2 * 3 K1 cells + at most 2 * 210 logical attempts = 427.
```

Here `210` is fuel for the logical driver, not a claim that every query performs
exactly 210 logical reads. Zero-cell logical attempts advance the protocol without
decorative physical events.

## 3. Same-object composition chain

The required object chain is:

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

The older `concreteBPNativeSuccinctRMQPayload` is a flat sibling and is not part of
this chain. Proof-only global-store and shape values occur at the refinement
boundary; neither is a controller field or an alternative reply source for the
physical driver.

The principal checked source names intended to pin the chain are:

- payload identity: `packedReviewerPayloadBits_eq_canonical` and
  `packedReviewerPayloadBits_eq_buildPayload`;
- serialization and backing: `packedReviewerSerializedBits_drop_header`,
  `packedReviewerMemory_recovers_payload`, and `packedReviewerMemory_getElem?`;
- memory-only execution: `packedReviewerRunAgainstMemory_memory_only`;
- physical/logical store agreement: `packedReviewerLogicalRead_eq_globalReadStore`;
- ordered logical simulation:
  `packedReviewerDriveLogical_210_simulates_packedWholeQueryRun` and
  `packedReviewerDriveLogical_210_occurrence_erases`;
- actual-run lowering and public outcome:
  `packedReviewerRunAgainstMemory_eq_lowered`,
  `packedReviewerRunAgainstMemory_public_outcome`, and
  `packedReviewerPublicResult_lt_two_pow`.

These are source-evidence names on the current dirty tree. Until their owning
modules elaborate together and the independent consumers pass, this report does
not treat the chain as certified.

## 4. Frozen local-rung rows `R2-01` through `R2-10`

| Row | Exact current composition/evidence surface | Current status and residual |
| --- | --- | --- |
| `R2-01-CONSUMED-PAYLOAD-IDENTITY` | `buildPayload` -> `packedReviewerPayloadBits_eq_buildPayload` -> serialized/padded reviewer bits -> `packedReviewerMemory` -> identical physical run; logical replies cross to the global store only through `packedReviewerLogicalRead_eq_globalReadStore`. | Candidate source chain present. Still **INCOMPLETE** because the controller proof, final public certificate, validation consumer, sibling-payload mutation, and final checks are not green. |
| `R2-02-ALL-SIZE-SPARSE-RESOLUTION` | K1 branch: `packedReviewerSparseCountFromReplies`; `packedReviewerSparsePrelude_sourceReplies_exact`; fixed requests `rankSuper`, `rankBlock`, `flagWord`; per-request plans of length at most two; aggregate prelude length at most six; decoded result equals `packedReviewerSparseCount shape`; exact addresses feed the all-size layout. | Candidate K1 construction present with no stride or finite-cutoff premise in the final route. Still **INCOMPLETE** pending focused elaboration, consuming controller certificate, validation, and final scans. No K1 obstruction was used and K2 was not activated. |
| `R2-03-EXACT-LENGTH-AND-HEADER` | `packedReviewerPayloadBits_length_eq` -> `packedReviewerSerializedBits_length` -> final-cell-only padding -> `packedReviewerMemory_length`; one header cell via `packedReviewerMemory_header_cell`; allocated space via `packedReviewerMemory_length_mul_width_le`. | Exact source equations are present on the reviewer object. Still **INCOMPLETE** until the same-run certificate and independent validation elaborate and final checks confirm no sibling substitution or internal padding. |
| `R2-04-SEGMENT20-RAGGED-LOWERING` | Closed eight-component classification -> `packedReviewerInteriorLocation_coordinates` -> per-entry chunk offset and short final width -> `packedReviewerInteriorStoreAccess` -> physical slice -> `packedReviewerInteriorLocationDecode` -> `packedReviewerInteriorRead_of_classify` -> `packedReviewerInteriorRead_eq_segment20`; aggregate logical plan/decode theorems preserve segment 20. | Candidate exact lowering is present for all eight components, including failed/dead classification. Still **INCOMPLETE** pending compilation, whole-run consumption, exact-type validation, and mutation evidence. |
| `R2-05-PHYSICAL-REQUEST-REPLY-CONTROLLER` | Proof-free `PackedReviewerControllerState`, `PackedReviewerPhysicalRequest`, `packedReviewerController`, `packedReviewerNextRequest`, `packedReviewerConsumeReply`, and `packedReviewerRunAgainstMemory`. Controller state contains public scalars, fixed control, and prior replies; only the driver takes memory. | Concrete source architecture present. Still **INCOMPLETE** because `ReviewerControllerProof.lean` is not green and the constructor-exhaustive reachable-state certificate is unfinished. |
| `R2-06-REVIEWER-MEMORY-ONLY` | Driver event reply is literal `memory[event.request.address]?`; canonical run supplies `packedReviewerMemory shape`; `packedReviewerRunAgainstMemory_memory_only` and `packedReviewerRunAgainstMemory_eq_of_agree` keep execution separate from proof-side logical-store simulation. | Candidate positional backing and dynamic-store agreement present. Still **INCOMPLETE** pending focused elaboration, grouped request certificate, validation, and final trust checks. |
| `R2-07-ORDERED-WHOLE-RUN-LOWERING` | Logical events retain invocation, site, segment, index, and reply. Physical events retain origin, address, ordinal, cell count, and reply. `packedReviewerPhysicalEvents_get?_eq`, lowered-whole simulation, actual-run lowering, `PackedReviewerRunGrouping.trace_eq`, and `.get?_eq` preserve order and multiplicity. | Candidate occurrence-sensitive chain present. Still **INCOMPLETE** because the logical-operand theorem and grouped physical-operand lift remain absent in StateProof, and no validation build has passed. |
| `R2-08-TOTALITY-ADDRESS-CAP` | Structural arbitrary-memory trace bound `packedReviewerRunAgainstMemory_trace_length_le_427`; canonical grouping allocation/address theorems; reply width/value theorems; dead address bound; invalid endpoints return empty trace. State inventories target scalar count `512`, word buffer `212`, wide buffer count `1`, and continuation depth `3`. | Base run/cap/address source facts are present. Still **INCOMPLETE**: canonical reachable `state_machine_fits`, request-operand bounds, reachable certificate, validation, and final checks remain open. The 427 bound is not a success theorem for forged memory. |
| `R2-09-SAME-RUN-REFERENCE-CORRECTNESS` | `packedReviewerRunAgainstMemory_public_outcome` targets the guarded public value for valid and invalid endpoint cases on the identical run; grouping, backing, allocation, reply width, cap, and result width are intended fields of `PackedReviewerPublicRunCertificate`. | Public outcome source theorem and certificate type are present. Still **INCOMPLETE** because the 26-field public certificate has no inhabitant and the downstream request-width fields are missing. |
| `R2-10-TYPED-ANTI-BYPASS` | `RMQ/Validation/EGCPFinalFalsification.lean` imports both controller proof modules and independently restates controller, driver, trace, width, cap, outcome, and public-certificate types. The replay source defines the owned `R2-ALLSIZE` stage without replacing the frozen registry. | Validation draft is intentionally load-bearing but currently does not elaborate: it names absent logical-request, grouped-physical-request, and public-certificate theorems. No current mutation stage or final validation result is claimed green. |

No `R2-*` row is recorded closed by this report.

## 5. K1 digestion

### What changed conceptually

The old near-all-size route relied on `localStride = 1` and an informal astronomical
cutoff. The current route instead treats `sparseCount` as data discovered by the
machine. The one header word still carries only `longCount`. Three prior logical
reads retrieve the terminal sparse-flag rank super sample, block sample, and flag
word. `packedReviewerSparseCountFromReplies` combines their decoded values with the
size-only local stride to recover the exact sparse-relative row count.

### Why this is genuinely K1

The requests and their addresses are fixed before `sparseCount` is known. They use
only `n`, decoded `longCount`, typed request tags, and the fixed endpoint index.
Their plans are sparse-count-independent and contain at most two cells each. The
three replies are actual charged data; `sparseCount` is not a proof field, callback,
shape lookup, or uncharged literal. Once decoded, it determines exact reviewer
length, close offsets, segment plans, and allocation for the same run.

K2 was authorized only after a quantifier-matched K1 obstruction. The charged
three-read construction removes the need for such an obstruction, so adding a
second header cell would be unauthorized format drift.

### Live assumptions and reviewer questions

The intended final chain has no `localStride = 1`, `n < 2^97`, sampled-size,
readiness, or compatibility premise. This must still be confirmed by the final
source scan and exact-type consumers. A skeptical reviewer should ask:

1. Are all three K1 plans derived without consulting `sparseCount` or a source list?
2. Does each decoded reply come from the same reviewer memory that the space theorem
   counts?
3. Does the recovered count feed every later sparse-dependent length and address,
   including dead and zero-cell attempts?
4. Is the six-cell prelude bound derived from the actual plans, rather than stored
   in controller state?

## 6. StateProof closure and the present blocker

`ReviewerControllerStateProof.lean` owns the proof-side fixed-state envelope and the
final request/certificate wrappers, following `DD-20260805-074`. It currently
contains:

- explicit codes for every nested protocol and continuation constructor, with
  `packedReviewerControllerNestedTagCodes_fits`;
- structural inventory bounds
  `packedReviewerControllerStateNatFields_length_le_of_depth`,
  `packedReviewerControllerStateWordFields_length_le_of_control`, and
  `packedReviewerControllerStateWideFields_length_le_one`;
- word-buffer, wide-buffer, control-counter, and continuation-shape preservation
  through Rank, WordSelect, Fringe, BPWindow, Interior, Select, LCA, and Whole;
- canonical logical reachability facts for Whole storage, shape safety, and depth;
- the types `PackedReviewerReachableStateCertificate`,
  `PackedReviewerReachableStateRequiredFacts`, and
  `PackedReviewerPublicRunCertificate`.

Five theorem clusters remain:

1. `packedReviewerCanonicalReachable_state_machine_fits` for every actual canonical
   physical prefix;
2. `packedReviewerReachableStateCertificate_of_reachable` and an inhabited canonical
   start certificate;
3. `packedReviewerDriveLogical_210_request_operands_fit`;
4. `PackedReviewerRunGrouping.request_operands_fit`;
5. `packedReviewerRunAgainstMemory_public_certificate`.

The first real proof gap is semantic scalar width. Existing storage invariants
deliberately bound stored reply words, wide buffers, counters, and continuation
shape, but do not bound every semantic natural retained in Select/LCA/Whole states.
Those fields include decoded entry values, rank bases and accumulators, candidate
values and indices, and interior continuation parameters. A theorem derived from
`PackedReviewerCanonicalLogicalReachable` alone would be too strong: its start
constructor permits arbitrary endpoints, while the start state stores them. The
correct proof must carry valid-endpoint bounds and a richer canonical-phase invariant
through `packedReviewerNormalizePrelude` and `packedReviewerNormalizeWhole`, including
canonical counts and exact partial-plan reply identity.

This scalar obligation is required by the frozen reachable-state certificate as
currently written, but it is not needed to prove logical/physical run facts. The
shorter independent route for request operands is an aggregate
`PackedReviewerRequestsFitFrom` theorem for the valid 210-fuel Whole start, composed
from the existing Entry, Rank, WordSelect, Fringe, BPWindow, and InteriorNat request
leaves, followed by
`packedReviewerDriveLogical_trace_request_operands_fit_of_fitFrom`. No public
Select/LCA/Whole aggregate or public splice lemma exists yet.

After logical operands, physical operands can be lifted blockwise with
`packedReviewerPhysicalEvents_request_operands_fit`, the header plan, K1 plan-length
and address bounds, and `packedReviewerLogicalPlan_address_lt_two_pow` plus
`packedReviewerLogicalPlan_length_le_two`, then transported through grouping.

## 7. Inherited invariant status for this rung

| Invariant | Current evidence surface | Residual |
| --- | --- | --- |
| `INV-STORE-IDENTITY` | Exact reviewer payload -> serialization -> memory -> run chain in section 3. | Independent consumer and sibling substitution still unverified. |
| `INV-READ-BACKING` | Driver replies are literal indexed cells; canonical grouping supplies allocated requests and successful replies. | Focused proof and final validation are not green. |
| `INV-STORE-AGREEMENT` | `packedReviewerRunAgainstMemory_eq_of_agree` determines the whole run from ordered replies. | Final exact-type consumer and unread-cell control remain outside current evidence. |
| `INV-TRACE-EXECUTION` | Physical trace is accumulated only by driver steps; expected trace is equated to the actual run by `PackedReviewerRunGrouping`. | Grouped request-operand wrapper and validation remain open. |
| `INV-GLOBAL-PHYSICAL-MACHINE` | One reviewer memory lowers legacy segments, ragged segment 20, and chunk segments 21/22, including failed/dead attempts. | Whole transitive build and validation are pending. |
| `INV-ADDRESS-WIDTH` | Physical allocation/address theorems, dead address theorem, finite control codes, and state inventory types exist. | Canonical semantic scalars and logical/physical request-operand theorems are the principal open part. |
| `INV-WORD-WIDTH` / `INV-WIDTH-SCALING` | One `packedReviewerCellWidth n` bounds memory cells, successful logical decodes, physical replies, counts, and addresses; logarithmic width theorem is present. | Complete reachable-state scalar closure and final trust checks are pending. |
| `INV-ALL-SIZE` | K1 prelude and all reviewer geometry are written without the old stride/cutoff premise. Invalid endpoint handling is total. | Final scan, elaboration, and boundary consumers have not certified the claim. |
| `INV-PROGRAM-ACCOUNTING` / `INV-PROOF-SEPARATION` | Executable controller types are proof-free and do not contain shape, semantic store, source/program list, expected answer, or proof callback. | Transitive typed validation and mutation evidence remain pending. |
| `INV-NO-SYNTHETIC` / `INV-VALUE-DEPENDENCY` | Result is produced after consuming actual replies; logical/physical occurrence and public outcome chains exist in source. | Reachable-state/request closure, decisive-reply anti-bypass, and final certificate are open. |
| `INV-ORACLE-INDEPENDENCE` | Correctness targets established guarded `queryTraceResult` semantics, not an expected value generated by the implementation. | Validation and any required boundary fixtures have not run. |
| `INV-VALIDATION-REACH` | Validation imports both new proof modules and names the final exact types. | It currently fails by construction because required StateProof theorem inhabitants are absent. |

All inherited invariants remain subject to final elaboration and independent
reconstruction; this table is a source-evidence inventory, not an acceptance table.

## 8. Design and workflow decisions

The current branch records four proof/model decisions and one process decision:

- `DD-20260805-071`: keep K1 and discover `sparseCount` through three charged prior
  replies; reject cutoff reasoning and unauthorized K2.
- `DD-20260805-072`: normalize already-completed child protocols before exposing a
  wrapper, so every reachable nonterminal state has a request and zero-read cascades
  do not create synthetic events.
- `DD-20260805-073`: state fixed-budget correctness at the canonical reviewer-store
  boundary; retain arbitrary-memory total trace bounds without claiming arbitrary
  forged memory is a correct RMQ representation.
- `DD-20260805-074`: keep execution/grouping/correctness in
  `ReviewerControllerProof.lean` and put canonical-prefix state and final operand
  certificates in downstream `ReviewerControllerStateProof.lean`.
- `WDD-20260805-001`: preserve the frozen sixteen-case registry and expose one
  `R2-ALLSIZE` view over seven newly owned reject cases, sharing one baseline build,
  one descendant-termination self-test, restoration hashes, and terminal clean-tree
  check. Source-static wiring exists; execution is pending.

These decisions document architecture and rejected alternatives. They do not replace
the checked theorem types, mutation verdicts, or final command ledger.

## 9. Verification ledger

### Current all-size rung

| Check | Current outcome | Runtime/deadline evidence |
| --- | --- | --- |
| Project-skill preflight at `6bf28dee` | **PASS before edits** | Seconds; 120 s deadline. Governance only. |
| Focused elaboration of `ReviewerControllerProof.lean` | **IN PROGRESS / not green** | Multiple development iterations; authoritative successful runtime not recorded. Current source still has local proof-normalization failures. |
| Focused elaboration of `ReviewerControllerStateProof.lean` | **Pending** | Blocked first by its imported base proof and then by the five clusters in section 6; 300 s planned deadline. |
| Direct validation elaboration | **Pending** | Missing StateProof theorem names are referenced intentionally; 600 s planned deadline. |
| `lake build RMQ` on frozen final tree | **Pending** | Prior broad builds are multi-minute; 1800 s planned deadline; run once on unchanged final tree. |
| Strict design-decision check from `6bf28dee` | **Pending** | 300 s deadline. |
| Strict claim-drift scan | **Pending** | 300 s deadline. |
| Trust/hygiene scan over `RMQ` and `lakefile.toml` | **Pending** | 120 s deadline. |
| `native_decide` / `Lean.ofReduceBool` scan | **Pending** | 120 s deadline. |
| Frozen original-row byte comparison against `6bf28dee` | **Pending** | 120 s deadline. |
| Committed-range and working-tree `git diff --check` | **Pending** | 120 s deadline. |
| Clean index and untracked-state check | **Pending** | Final committed tree only. |
| `R2-ALLSIZE` replay stage | **Pending** | Must follow green production and validation builds; no verdict or duration recorded. |
| Full sixteen-case replay | **Deferred for this rung** | It must remain fail-closed while deferred targets are absent. |
| Aggregate gate | **Pending decision** | Run at most once only if mandatory commands do not already cover the final changed surface. |

No Lean or Lake command was run merely to rewrite this report.

### Historical timing context, not current certification

On predecessor clean trees, the old report recorded 2--4 s direct module checks,
4--13 s incremental probe builds, an approximately 8 s incremental validation
build, 1.6--3.9 s fully warm/cached broad builds, an approximately one-minute claim
scan, and a 683 s cold `lake build RMQ` baseline at `6078a29`. It also recorded a
full predecessor replay with 16 cases considered, 9 commissioned verdicts, 7
`TARGET-ABSENT` cases, clean restoration, and exit 7. These numbers guide deadlines
only. They certify neither the current dirty tree nor the all-size controller.

## 10. Validation and anti-bypass status

The validation root currently pins, among other things:

- raw controller, next-request, consume-reply, and external-driver signatures;
- canonical logical and physical control tag widths;
- reviewer-memory-only replies and dynamic-store agreement;
- ordered logical occurrence and physical occurrence expansion;
- structural 427 cap and grouped actual-run cap;
- allocation, address, reply, and result widths;
- public outcome and the exact 26-field public certificate type.

The following intended public names are deliberately missing until StateProof closes:

- `packedReviewerDriveLogical_210_request_operands_fit`;
- `PackedReviewerRunGrouping.request_operands_fit`;
- `packedReviewerRunAgainstMemory_public_certificate`.

The reachable-state proof also still needs its canonical fits theorem and inhabited
certificate constructor/start. Therefore the validation draft is useful as a
load-bearing specification, but it is not presently a passing validation artifact.

The mutation script has a source-static `R2-ALLSIZE` stage for the seven locally
owned reject cases `M03`, `M05`, `M06`, `M07`, `M08`, `M11`, and `M12`. No current
stage verdict is recorded. Full registry semantics, selector nonvacuity, deadlines,
process-tree termination, byte restoration, and clean-tree requirements remain
unchanged.

## 11. Explicit deferrals and full-node boundary

| Item | Disposition |
| --- | --- |
| `FG-11` liveness mutation campaign | Deferred except for any unavoidable local theorem dependency. Blocking for the full node, not this local rung. |
| Full `FG-12` registry completion | Deferred. The exact registry, selector, deadline, descendant-termination, restoration, and clean-state contracts must be preserved. Blocking for the full node. |
| `FG-13` trust and same-object closure | Local same-object and trust checks are still required before this rung can finish; complete full-node closure additionally depends on the final capstone, exact replay, and independent audit. |
| Full `FG-14` boundary campaign | Deferred beyond boundary facts required directly by `R2-08` and `R2-09`. Blocking for the full node. |
| `FG-15` final architecture publication record | Deferred. This worker report and current decisions are local-rung evidence, not the full publication/acceptance record. |
| Fresh-blind exact-commit audit | Required only after a frozen candidate exists. Not performed or claimed. |
| Coordinator reconstruction and acceptance | Required after worker evidence is complete. Not performed or claimed. |
| Full EG-CP node | Remains open until all `FG-01` through `FG-15` rows, inherited invariants, replay requirements, final checks, coordinator reconstruction, and fresh-blind audit close. |

The deferrals limit this rung's scope; they do not change the frozen requirements or
make deferred work optional for the full node.

## 12. Remaining work and handoff

The shortest honest completion order is:

1. Make the current `ReviewerControllerProof.lean` elaborate without weakening its
   request, lowering, grouping, backing, correctness, or cap types.
2. Close the valid-endpoint semantic scalar and canonical physical-phase invariants
   in `ReviewerControllerStateProof.lean`.
3. Construct the reachable-state theorem, certificate constructor, and start
   inhabitant.
4. Prove the aggregate 210-fuel logical request-operand theorem, lift it through the
   exact physical grouping, and inhabit the public certificate.
5. Elaborate the independent validation root and repair only genuine type or proof
   defects, not the frozen expected propositions.
6. Run proportionate focused checks, then the single final broad build and the
   final-required static/decision/diff/clean-tree checks on one unchanged tree.
7. Run the owned replay stage only after its production and validation targets are
   green; record exact verdicts, surfaces, restoration, tree identity, and duration.
8. Fill the four final identity placeholders in section 1 and record every final
   command against that exact tree.

### Plain-English proof digestion

The new machine is intended to show that the succinct reviewer representation can
answer every query using one real packed memory, even though one directory length is
content-dependent. It learns that length by reading the representation itself,
then follows a fixed request/reply program whose events can be matched one-for-one
with the established logical query. The difficult remaining proof is not the
high-level RMQ result; it is demonstrating that every live intermediate scalar and
every request operand fits the same modeled word while preserving the exact physical
prefix that produced it.

### Questions a skeptical graduate student should ask next

1. Does the semantic scalar inventory describe genuinely encoded machine state, or
   has it become stronger than the operational claim needs?
2. Can the valid-endpoint hypothesis and canonical reply-prefix relation be carried
   through normalization without silently replacing reviewer-memory replies by a
   semantic store?
3. Do equal repeated logical reads remain distinguishable after physical expansion?
4. Does every segment-20 dead/short-final case keep its component identity and issue
   exactly the plan recorded by the run?
5. Does mutating a decisive reply change a route or terminal result, rather than
   only a decorative trace field?
6. Do the final certificate, space theorem, and public correctness theorem all name
   the identical payload, memory, endpoints, run, and trace?

Until those questions are answered by checked propositions and the pending ledger is
green on one frozen tree, the authoritative status remains **INCOMPLETE**.
