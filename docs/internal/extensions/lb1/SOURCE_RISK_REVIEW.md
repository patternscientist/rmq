# LB-1 development source risk review

Status: INCOMPLETE. Phase: independent development source review. Adapter and
validation elaboration, semantic replay, final trust checks, and the mandatory
blind exact-commit audit remain open. This report records no overall task
completion or coordinator acceptance.

Reviewed on 2026-09-12, approximately 08:12-08:18 UTC, in
`C:/Users/poin/.codex/worktrees/2270/RMQ`, branch
`codex/lb-1-variable-payload`. Governance/base:
`0e6a00f654abc64f8b68988fa9675b9a839dca2f`. Frozen requirements:
`0bbbe8ca4a937bc9782b2f7c5cc5419faa1a75a2` and the 29 unchanged rows of
`ACCEPTANCE_MATRIX.md`. The dedicated frozen-row evidence is in
`FROZEN_ROW_EVIDENCE.md`; this review does not replace that byte check.

The role used the previously passed canonical `rmq-proof-sprint` preflight,
its completion gate, and `docs/internal/AUDIT_PROTOCOL.md`. The runtime RMQ
catalog contained `rmq-audit-prompt`, `rmq-coordinator`, and
`rmq-proof-sprint`. This is a bounded child review alongside useful parent and
adapter work; no further parallel leaf was needed. Only this report was edited.
No Lean/Lake process was started, respecting the other worker's build slot.

## Result and concrete replay repairs

No semantic-composition or quantifier defect was identified in the inspected
adapter and validation drafts. The actual serialized words, recovered memory,
bounded encoding, upper capacity, and transported machine propositions have an
explicit same-object chain. That source assessment is not an elaboration or
mutation verdict. Two replay design issues were identified during development:

1. **Expected acceptance needed an altered packet.** A01 compiles the unchanged
   consumer. Alone, it cannot distinguish rejection of a required public
   dependency from blanket rejection of any producer edit. The minimally
   invasive repair is A02-PROOF-ONLY-WRAPPER: temporarily append a private Prop
   wrapper containing the unchanged `PackedAllocationOptimality` and an unused
   `True` note, and construct it using `packedAllocationOptimality_holds`.
   Require the modified producer to compile with its replacement olean, then
   require the exact three-structure inventory and full typed consumer to pass.
   Keep all public structure inventories unchanged. Parent confirmed this
   implementation; the v3 script was inspected and contains all three required
   passes and the common exact restoration path. **Source repair implemented;
   semantic expected-accept execution remains open.**

2. **D03 originally pinned an unreliable later diagnostic.** Its mutation
   replaces `serializeWords` with `[]`. The first false proposition is
   `serializeWords_length` at AllocationLowerBound.lean:32. The later
   `deserializeWords_serializeWords` proof rewrites with that declaration at
   line 46; an error placeholder from the failed earlier theorem can change
   whether the later declaration reports an error. A diagnostic in the earlier
   declaration must not be accepted as a diagnostic in the later one. The
   precise repair is to retain D03-ZERO-SERIALIZER but change its expected
   surface, in both independently literal registries, to
   `serializeWords_length`. This tests the unchanged equation
   `(serializeWords width words).length = words.length * width` directly.
   Parent selected that repair before the development v3 registry is frozen;
   a final source reread confirmed `serializeWords_length` in both literal
   registries. D03 then
   establishes rejection of lost observed length, not an independent
   round-trip rejection. O01/O02 and R05 separately exercise inverse,
   injectivity, and zero-word multiplicity. **Pre-freeze diagnostic correction;
   no semantic D03 result is claimed.**

Registry v1/56 and v2/62 are historical evidence phases. The inspected v3 adds
A02 for 63 proof/control cases plus six runtime cases. Old discovery or
subprocess-selector results do not constitute a v3 semantic campaign. No
requirement, public proposition, or frozen matrix row needs weakening for
either repair.

## Generic model and same-object construction

The generic module's checked source SHA-256 is
`688E98C5FBCC12D17CB475FD4B381B707EC224805C9A3C1C0B1858B3270B1FFA`.
It matches the source associated with the supplied 15-module check in
`COUNT_PROOF_NOTES.md` and
`evidence/build-20260912T071953550.jsonl` (exit 0; new leaf 18.991 seconds;
600-second deadline). This review trusts that supplied generic evidence and
does not rerun it. Adapter and validation declarations below are drafts for
purposes of this review, even if another worker later obtains checked evidence.

`ExactRMQBoundedEncoding n B` contains exactly `encode`, `query`, `length_le`,
and `query_exact`. The last two quantify over every ordinary `List Int` of
length n, and every left,len with `0 < len` and `left + len <= n`. The decoder
is one fixed function of payload and endpoints. `boundedBitStrings B` includes
the empty string and all lengths through B, with no prefix-free convention;
its public theorem gives Nodup, cardinality `2^(B+1)-1`, and membership exactly
when length is at most B. Equal codes imply equal valid-window answers, hence
equal Cartesian shapes. Canonical representatives inject `shapesOfSize n`
into that very universe. The doubled lower conclusion is
`doubledLogSlackLower n <= 2*(B+1)`. Applying the existing cubic-square
arithmetic bridge at B+1 does not construct a fixed-length encoding.

The adapter chain is explicit in AllocationLowerBound.lean:23-209:

1. `serializeWords width words` concatenates each full width-bit cell.
   `deserializeWords` obtains the number of cells from `bits.length / width`
   and reconstructs each width-bit slice. Its left inverse quantifies over
   every finite bounded word list at every positive width. The resulting
   injection therefore covers arbitrary finite list lengths, including
   different counts of zero words. Width zero is explicitly excluded from the
   inverse and has a deliberate collision control.
2. `allocationBits xs` is literally the serialization of `buildMemory xs` at
   `wordWidth xs.length`. Its exact length is the actual allocation's cell
   count times that width. Allocation.lean:154-158 defines the underlying
   allocation from `shapeMemory`, including its metadata and repacked cells;
   the serializer does not discard metadata, the final cell, or padding.
3. `wordWidth n = 32 + 8 * packedReviewerCellWidth n` is positive and depends
   only on n. `buildMemory_words_fit` supplies the word premise, giving
   `reconstructedMemory xs = buildMemory xs` for every xs.
4. `allocationDecoder n bits left right` is literally
   `queryNat (deserializeWords (wordWidth n) bits) n left right`. No xs, shape,
   answer, certificate, or proof is an executable argument. Exactness rewrites
   the recovered memory to `buildMemory xs` and applies `queryNat_exact`.
   It gives the total valid-range/none equation and the leftmost answer on
   that same input. No assertion about malformed arbitrary bitstrings is
   needed: exactness is required on the encoder image.
5. Equal Cartesian shapes imply equal actual memory; their equal sizes also
   give equal serialization widths. Conversely, equal serialized encodings
   of representatives of two size-n shapes imply equal valid RMQ behavior,
   then equal shapes. There is no false injection on all value lists: the
   distinct-valued fixtures `[0,1]` and `[9,10]` intentionally share memory.
6. `UniformAllocationBudget n B` is
   `forall xs, xs.length=n -> (buildMemory xs).length * wordWidth n <= B`.
   `allocationEncoding n B budget` has encode=allocationBits and
   query=allocationDecoder n. The uniform lower bound consumes that instance.
   `canonicalAllocationBudget n` constructs it at `2*n+allocationRho n` from
   the actual memory upper theorem. The public upper bound concerns each
   `allocationBits xs`; the lower bound concerns any budget valid for all
   size-n inputs. It never asserts a near-2n lower bound for every input.

An arbitrary function type cannot inspect closure contents. The relevant
anti-advice protection is the fixed decoder plus universal exactness across
all size-n inputs, and the canonical decoder's inspected executable body.
`ofSizeAdvice` fixes advice n once. The generic consumer's `inputAdviceRejected`
and `shapeAdviceRejected` instantiate the same full size-two exactness
predicate with an empty payload and a fixed advice oracle; `[0,1]` versus
`[1,0]` refutes it. They do not purport to prove that all closures are
syntactically free of captured constants. The size-one n-only advice positive
control is legitimate. Small-size anti-vacuity uses exactness/count controls,
not the coarse doubled logarithmic inequality, which can be zero there.

## Exact recovered-memory machine consumer

`reconstructedRun_eq` equates the complete runs at every fuel, using the same
program and `initialState xs.length left right`. The 33-field
`ReconstructedPackedQueryCapstone` block was compared against the existing
`FullyChargedPackedQueryCapstone` block: after only substituting `buildMemory`
with `reconstructedMemory` and reconciling CRLF/LF for this source comparison,
the blocks are literally equal. Both marker matches were nonempty. This
source comparison is separate from, and does not relax, frozen-row byte
integrity. Each memory-dependent initializer rewrites by exact recovery and
uses the corresponding existing field; independent fields use that same
capstone's direct projection.

The mathematical decoder is not assigned the primitive program's time bound.
QuerySource.lean:67 checks `encodeInputs`, executes the unchanged fixed
`queryProgram`, and decodes its halted result packet. Guard.lean:18-22 initializes
only left,right,n. Primitive.lean:133 loads an actual memory reply into the
destination register; its recursive `run` derives the transitions and final
state, and `Run.result` reads the halted state. `scanWindow` appears in the
proved result and independent fixture expectations, not as a precomputed
answer supplied to that execution.

`positionalReadBacking` retains the occurrence index, prefix pre-state, fetched
instruction, actual `execute`, and exact memory reply. `suppliedMemoryAgreement`
equates entire runs after agreement at the original run's receipt addresses;
it is stronger than just equal receipt logs. The ordered reference-read
formula is a refinement conclusion about the actual run, not synthetic
evidence generated by a new post-hoc execution.

Raw-machine result, halt, state/transition safety, and read-width fields retain
the original premises `left,right < 2^wordWidth xs.length`. Valid ranges imply
those premises through `validInputs`. The total Nat wrapper does not extend
raw-machine safety to arbitrary unrepresentable invalid endpoints. The width
also bounds allocation addresses through the end sentinel, all instruction
fields, and reachable words/results. Complete capacity separately includes
literal encoded program words and the finite register/scratch bank.

Validation.lean has 16 independently literal checkO types and 33 checkM types,
each directly projecting `packedAllocationOptimality_holds`. `composedConsumer`
expands the uniform allocation premise and valid-range guard. Definition pins
expand encode/decode/recovered memory, the generic fields, and the model
predicates, so a renamed proposition or a sibling object does not suffice.
`canonicalEncodingConsumer` explicitly applies the generic lower consumer to
the actual canonical allocation encoding. The inventory uses literal expected
4/16/33 field arrays and actual Lean structure metadata, including absence,
parent, order, default, escaped, Unicode, and missing-field controls; compiling
that inventory is still separate evidence.

## Runtime and replay source reach

Validation runtime fixtures contain six small tags, not eagerly computed
allocations or program runs. `--list` checks and lists their exact registry
without calling `runCase`. The selected case then constructs `allocationBits`,
deserializes its actual memory, and invokes `allocationDecoder`. Expected
answers are independent literals (including singleton and leftmost zero),
with reference `scanWindow` checks where informative. Empty inputs, invalid
endpoints, width-zero exclusion, zero-word multiplicity, mixed bounded words,
and distinct values sharing a shape have explicit controls.

No selector means all six cases; one known ID means exactly one. Empty,
whitespace, malformed, unknown, and duplicate selectors fail. The environment
`case:` channel preserves an explicitly empty native argument and conflicts
with CLI selection rather than silently dropping it. Registry equality,
nonemptiness, unique IDs, selected IDs, and executed/expected counts are
checked. The replay script independently pins both its proof registry and the
runtime IDs, and runs runtime startup/list plus a known R04 case before a full
campaign. Selector and process evidence from earlier development is not
reported as execution of this current source.

For all 49 O/M weakenings, replay edits the real producer field and initializer,
requires the producer to compile into the replacement olean, and then requires
a diagnostic inside the corresponding independently typed consumer. Deletions,
reflexive-memory/run substitutions, replacing arbitrary B with the canonical
budget, and restricting exactness to empty inputs address distinct bypasses.
The generic lower proposition has a separate typed consumer. Deleting generic
exactness is a producer rejection at `sameRMQBehavior_of_encode_eq`; null and
wrong canonical decoders target `allocationDecoder_exact`. These are distinct
expected failure disciplines and must remain distinct in final results.

The half-open declaration-span correction excludes errors in the next
declaration. Owned subprocess wrappers bound Lean, runtime, and Git operations,
retain result/output evidence, and classify timeout/resource failures as
inconclusive. Every source and overwritten olean is restored from exact byte
backups in `finally`; byte comparison and clean worktree/index/untracked checks
run per case and at exit. POSIX ownership remains uncovered on this Windows
host. This report did not run a replay case or issue a new process-ownership
verdict.

## Disposition of every frozen row

The following are source-route dispositions, not acceptance statuses. Every
row remains subject to the outstanding checks above; none is removed or
narrowed.

| Frozen ID | Source-grounded disposition and remaining evidence |
| --- | --- |
| REQ-LB-COUNT | Checked supplied generic source gives the actual bounded universe, shape injection, exact finite count, and doubled B+1 conclusion. Final dependency/trust inventory remains. |
| REQ-LB-PQ1 | Exact allocation serialization, finite-list inverse, size-only width/decoder and finite-shape injection are explicit drafts; adapter and O01-O08 elaboration remains. |
| REQ-LB-MODEL | UniformAllocationBudget and canonical allocation instance preserve worst-case quantifiers; O09-O14 pin lower/upper/residual. Checked join remains. |
| REQ-LB-CONSUMER | publicContract, literal checkO/checkM, composedConsumer, and canonicalEncodingConsumer compose the actual object; consumer elaboration and public mutation evidence remain. |
| CHK-LB-CONTROLS | Required generic, boundary, advice, and zero-word controls exist; A02 supplies mutated expected acceptance. D03 now pins the precise first-failure surface described above; semantic outcomes remain. |
| REPLAY-EXACT-REGISTRY | Independent literal v3/63 proof list and six runtime IDs reject omissions; final frozen-registry executed/expected evidence remains. |
| REPLAY-SELECTOR-NONVACUITY | Explicit omitted/single/empty/whitespace/malformed/unknown behavior and nonempty selections exist in both paths; current-source runtime boundaries remain. |
| REPLAY-SUBPROCESS-DEADLINE | Owned bounded helpers and exact finally restoration are used; current campaign evidence remains, and POSIX ownership is uncovered. |
| INV-STORE-IDENTITY | O03/O04/O15 equate counted words, recovered whole memory, and every fuel-prefix run; sibling/deletion cases target those equations. |
| INV-VALUE-DEPENDENCY | Decoder runs the primitive program on recovered numeric words; execute.load writes actual replies and result comes from halted state. Null/wrong exactness rejection remains. |
| INV-SEMANTIC-NONVACUITY | Ordinary List Int inputs, replicate witnesses, total all-size decoder and independent literal model pins exclude True/domain substitution; H01 tests empty-only exactness. |
| INV-TRACE-EXECUTION | M27 records actual indexed producing transition and pre-state; M28 is a same-run ordered refinement. Transport elaboration remains. |
| INV-STORE-AGREEMENT | M30 equates entire supplied-memory/canonical runs under agreement at actual receipt addresses, including result/cost/trace. |
| INV-READ-BACKING | M27 retains exact indexed memory reply; M26 adds width and M32 excludes valid-run failed loads. Field deletion/weakening outcomes remain. |
| INV-WORD-WIDTH | M03/M06/M23-M26 retain one declared width and original endpoint premises for stored/reachable/returned words. |
| INV-ADDRESS-WIDTH | M07 includes end sentinel; M08 covers every encoded instruction; M24-M26 retain executed address/operand safety. |
| INV-INSTRUCTION-ATOMICITY | The accepted primitive evaluator/program is unchanged; serialization, deserialization, and Nat wrapper receive no primitive step claim. |
| INV-PROGRAM-ACCOUNTING | M05/M11-M14 count literal code and finite scratch separately; shape-dependent metadata remains inside recovered counted memory. |
| INV-ORACLE-INDEPENDENCE | Actual decoder output is compared with independent literal/reference expectations; it is never its own expected answer. Runtime execution remains. |
| INV-VALIDATION-REACH | Runtime imports and invokes the new allocationBits/deserializer/allocationDecoder path after selection; current-source runtime execution remains. |
| INV-ALL-SIZE | Recovery/decoder/canonical encoding quantify every xs/n without readiness dispatch; valid, empty, singleton, and invalid endpoint cases are retained. |
| INV-PROOF-SEPARATION | Decoder inputs contain no proof certificate, shape, or input list; proof records express conclusions and do not carry executable answers. |
| INV-NO-SYNTHETIC | No new trace-producing execution is introduced; complete run identity transports the existing execution-derived receipts and state. |
| INV-CATEGORY-SEPARATION | O03 counts bits; M05 counts code/scratch; M21/M22 count primitive transitions/categories. Lean duration is separate evidence. |
| INV-PUBLIC-COMPOSITION | One optimality record joins exact recovery, generic allocation instance, upper/lower and the full recovered-memory machine record; literal consumers pin the join. |
| INV-CERTIFICATE-ANTI-BYPASS | Literal 16+33 consumer projections and exact metadata inventory exist; 49 producer-pass/consumer-fail cases plus deletions/siblings remain to execute. |
| INV-MUTATION-REPRODUCIBILITY | Versioned literal registry, bounded stages, exact surfaces, A02 altered acceptance, and byte/clean restoration are source-visible; committed full campaign remains. |
| INV-GLOBAL-PHYSICAL-MACHINE | Complete memory equality transports every program segment, actual load, sentinel and code field to one pre-execution store. No suffix-only embedding is substituted. |
| INV-WIDTH-SCALING | M03 links the same n-only width to logarithmic size bounds; capacity, stored words, sentinels, instruction fields and primitive safety all use it. |

## Snapshot and review limits

At 08:12:53 UTC the inspected source snapshots had SHA-256:

| File | SHA-256 |
| --- | --- |
| RMQ/Core/EncodingVariableLowerBound.lean | 688E98C5FBCC12D17CB475FD4B381B707EC224805C9A3C1C0B1858B3270B1FFA |
| RMQ/Core/WordRAM/Packed/AllocationLowerBound.lean | 3F50B46472C8AEDF0D27E3375660ECED6D7D1B1AB7770CAB7342863E39ACFF0E |
| RMQ/Validation/VariablePayloadLowerBound.lean | 0C2C86D986312DB6A4012BE2C0E5CE69625A5729042553E842D68313C8594D7E |
| scripts/variable_payload_replay.ps1 | 81EFB932B42B8A0CE400DB950C687550652AB77207F069469F199A431D73AE4C |
| docs/internal/extensions/lb1/REPLAY_REGISTRY.json | 9CFAF815C73490F84BE978D3F699880D9129EFC62196D2C124826A6D102631F9 |
| docs/internal/extensions/lb1/EVIDENCE_PLAN.md | F64311FF9EA914A2FEF2D5F85188B7775DB4C712073F9FFA0E86503C765FF313 |

The replay hashes precede the selected D03 diagnostic correction. Other workers
are editing this shared development tree. These hashes scope the source
observations and do not identify a frozen final candidate. The final audit must
use its own exact commit and replay evidence. Existing PQ1 capstone source was
read to check applicability; this phase is not a fresh proof of its entire
transitive closure. Broad builds were skipped because this is a read-only
development review and another worker owns the build slot. No design decision
was introduced by this report; replay recommendations refine evidence for the
unchanged frozen contract and are parent-owned.

Report checks: targeted strict claim-drift scan passed with zero hits/failures;
strict design-decision check at the exact original base passed on the current
shared tree (34 changed files); report whitespace check passed. The report's
29 disposition IDs exactly match the frozen matrix's ordered IDs. These are
document/process checks and do not elaborate the adapter or validate a replay.

## Proof digestion

Conceptually, observing bit-list length permits a finite universe containing
all lengths through B. The canonical packed allocation inhabits that universe
through a lossless serialization of every allocated word. In plain English,
the same recovered memory both answers the queries and accounts for the upper
and worst-case lower comparison. Live assumptions are the uniform size-n
budget, valid half-open leftmost exactness, positive bounded word width, and
the existing explicitly guarded primitive model. The next skeptical question
is whether the kernel-checked adapter and literal consumers, followed by the
exact frozen mutation campaign, actually validate every advertised dependency.
That evidence remains open here.

## Development addendum: checked inventory syntax repair

At 2026-09-12 08:48:47 UTC, a separately authorized narrow build corrected the
inventory control declaration from `structure WithParent extends Unchanged :
Prop where` to Lean 4.22 syntax `structure WithParent : Prop extends Unchanged
where`. The initial failure is preserved in `evidence/development-checks.json`:
exit 1 after 29.686 seconds, a syntax diagnostic followed by absent parent
metadata. That failed attempt did not establish parent rejection. No public
producer, expected inventory array, control predicate, or category boundary
changed in the repair.

The exact repaired `scripts/variable_payload_inventory.lean` was run with
Lean 4.22.0, `-j1`, the task-local `.lake/build/lib/lean` import cache, and the
existing owned-process wrapper. It passed with exit 0 in 13.230 seconds under
a 600-second deadline, using kill-on-close job ownership; stderr was empty,
with no timeout or output truncation. The process finished and the exclusive
Lean slot was explicitly released to the parent before further documentation
work. No axiom or runtime/replay check was run in this repair.

Actual metadata matched all literal ordered inventories: encoding 4,
optimality 16, and reconstructed machine 33 fields, all parent-free. The
unchanged and correctly ordered controls were accepted. Eleven negative
checks rejected defaulted, extra-indented, underscore, apostrophe, Unicode,
escaped, replacement/missing-field, absent-structure, missing expected field,
reversed order, and parent-structure cases through the same `hasInventory`
predicate. The parent control additionally checked that actual metadata had
exactly `toUnchanged, added` and a nonempty parent record before testing its
rejection. Thus absence or a wrong field list could not masquerade as passing
the parent-category check.

Separate reproducible result evidence is
`evidence/inventory-repaired-20260912T084829575.json` (2,973 bytes; SHA-256
`7829D223AFEA1A1933B3009EF1E41585E2E581A2B8ED8BE9E732A263E01FD533`).
It records the binary version, source/imported-olean hashes, exact result,
deadline, ownership, and successful post-run unchanged-input checks. The
repaired inventory is 5,522 bytes, SHA-256
`1E4A84883CE5695C3392B5DB38B02335D0853B4FAFF772040D351FDB15E30721`.
The original development evidence retained SHA-256
`B7AD3379491473351D00E8790C616DD8F2A95CA105F7AE89EC8FD827E132E433`.
This addendum supplies checked inventory evidence only. The earlier source
review remains scoped to its snapshots; the full semantic campaign, trust
inventory, and final independent audit are still open.
