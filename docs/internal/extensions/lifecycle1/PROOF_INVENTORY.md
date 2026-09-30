# LIFE-1 proposition and object inventory

This source inventory accompanies the immutable
[43-row contract](ACCEPTANCE_MATRIX.frozen.md). It does not change those rows,
declare acceptance, or replace final-tree type, executable, mutation or gate
receipts. The [worked guide](../../../digests/LIFECYCLE_PROOF_GUIDE.md) explains
the route. Source locations below identify declarations; proposition summaries
include the live guards rather than treating declaration names as evidence.

Base: `bf31f983205175481fcb659caa4dfb70ef43e361`. Governance:
`7b227c49ef2ec044b702126cc41c9add847eed01`. Frozen matrix SHA-256:
`8b08e2d7c7f284634d88bfa4262ee447f79a401c78b27dc346ea34d76ccba4a7`.

## Common quantified objects

All lifecycle names below are under
`RMQ.SuccinctFinal.PackedLifecycle`; `C` abbreviates `PackedConstruction` and
`PW` abbreviates `PackedWordRAM`. Let:

```text
n       = xs.length
W       = PW.wordWidth n
cells   = PW.buildMemory xs
M       = cells.length
p       = Layout.program model
initial = initialState model xs left right Layout.builderBase
actual  = Continuous.continuousRun model xs left right
```

The public input guards are `InputDomain model xs`, `left < 2^W`, and
`right < 2^W`. `InputDomain .word xs` is the existing `C.InputFits W xs`;
`InputDomain .comparison xs` is `True`. This `True` is the deliberate absence
of a numeric encoding restriction on comparison keys, not a vacuous execution
or readiness predicate. Input materialization and out-of-word endpoint
admission are explicit boundaries.

`RunsTo p s t ts` means exactly `run p ts.length s = <t,ts>`.
`Retained.Canonical xs s` expands to canonical whole memory and extent, default
key functions, zero owned key extents, zero numeric tail at 8273, and `s.Fits W`.
It contains no expected answer or execution certificate.

## Operational propositions

### E01: machine, scalar boundary, and old semantics

[Machine.execute](../../../../RMQ/Core/WordRAM/Lifecycle/Machine.lean#L28)
delegates `.old primitive` exactly to `C.execPrim`. Each successful new release
changes one tail cell/register and decrements its corresponding extent. Zero
extent faults and does not decrement. `executeBoundary` changes only register
300, register 301, PC, or status, according to its constructor.
[Calculus.old_step](../../../../RMQ/Core/WordRAM/Lifecycle/Calculus.lean#L127)
and the old-run lemmas preserve complete states and ordered transitions.

`requestProtocol_exact entry left right answer s (s.status = halted answer)`
identifies the final state with the two scalar register writes, fixed entry PC
and running status, and proves exactly four steps/categories:
`[requestAdmission,requestAdmission,controlEntry,controlEntry]`.
`requestProtocol_safe` additionally requires represented values/entry, entry
inside the program, bank size greater than 301, initial Fits/Closed, and zero
register tail. It proves boundary-or-instruction `ActionSafe` and represented,
closed pre/post states for every actual event.

### E02: fixed programs and accounted fields

[Program](../../../../RMQ/Core/WordRAM/Lifecycle/Program.lean#L22) fixes builder,
descriptor, finalizer and retirement bases at `221239`, `223345`, `223356`, and
`223370`; service entry is `212964`. `program` takes only `InputModel`.
`source_size = 2106`, `oldPrefix_length = finalizerBase`, and
`program.length = jumpBase model + 1`, with jump bases `223370`/`223378`.
`old_builder_host`, `descriptor_host`, `finalizer_host`, `retirement_host` and
`jump_fetch` identify the actual fragments in that one program.

[Accounting.all_encoded_fields_fit](../../../../RMQ/Core/WordRAM/Lifecycle/Accounting.lean#L60)
quantifies every word of the flattened actual instruction encoding and proves
it below `2^W`, including dormant code. `encodedProgram_length_le` bounds that
same list by `1116895` words. Numeric register/control accounting is
`8273+8`; descriptor and request registers are already in this bank.

### E03: live builder and reservation provenance

[Builder.hosted_body](../../../../RMQ/Core/WordRAM/Lifecycle/Builder.lean#L148)
is generic in old program, nonzero base and supplied state. Its guards include
`32 <= W`, the old leaf `KeySpec`, leaf registers below 400, running entry at
the hosted base, zero initial numeric registers, positive extent, stored header
`n`, input predicate local to the initial extent, the existing polynomial and
arena capacity bounds, adequate width, hosted compiled BODY, continuation inside
the program, program/initial-state Fits, and numeric clean tail.

It derives `exists abstract producer ts, HostedBody ...`, whose fields include:

```text
producer = { abstract with pc := base + source.size }
C.RunsTo oldProgram initialCore producer ts
producer.status = running
producer.extent = producer.regs 3 + M
forall i < M, producer.memory (producer.regs 3+i) = some (cells.getD i 0)
forall a < initialCore.extent, producer.memory a = initialCore.memory a
forall r >= 400, producer.regs r = initialCore.regs r
```

Its `reservation` field is the production
[ReservationReceipt](../../../../RMQ/Core/WordRAM/Lifecycle/BuilderProvenance.lean#L192):
`ts = before ++ [actual reserve 3 transition] ++ after`, with actual prefix and
suffix `RunsTo`, a running producing pre-state/fetch, and no suffix writer of
register 3. `ReservationReceipt.occurrence` proves an indexed occurrence,
`(run oldProgram index initialCore).final = pre`, `producer.regs 3 = pre.extent`,
and that equality through every following suffix prefix.

[Construction.build_stage](../../../../RMQ/Core/WordRAM/Lifecycle/Construction.lean#L267)
discharges these guards from the three common input guards and derives one
`BuildStage`. Its execution is the actual `RunsTo p initial producedState
producedTrace`, where `producedTrace` maps the old transitions with the actual
initial bank extents. It proves Closed/Fits, numeric tail zero at 400, the exact
next `Descriptor.Entry`, and body work `<= 1000000000*(n+1)`.

### E04: descriptor and request dependency

[Descriptor.Entry](../../../../RMQ/Core/WordRAM/Lifecycle/Descriptor.lean#L36)
requires running PC at its base, register 3 equal to `B`, actual present metadata
`memory B = some n`, `memory (B+7) = some M`, and two present in-extent request
cells at the model's request base. `Construction.body_descriptor` derives this
entry from produced metadata and the builder's input frame.

`transfer` derives eleven actual steps, running PC `base+11`, registers
`0=B`, `2=M`, `302=n`, `300=left`, `301=right`, and exact memory/key/extent
frames. `transfer_safe` adds only width, initial Fits and whole-program length
bounds. `transfer_prefix_frame` covers every fuel through 11.

`output_transfer_at` supplies occurrence 0 with the exact `move 0 3` action and
pre-state; `OutputReceipt` constrains the destination projection itself.
`output_wrong_source` assumes a different source value and proves destination
inequality. Opcode/source identity remains required even if two sources have
equal values. `read_occurrences` supplies actual occurrences 1, 4, 8, 10 with
`ReadReceipt` for metadata `n`, metadata `M`, left and right respectively.
`ReadReceipt` includes opcode, address-register value, present pre-state cell,
actual `execute` after-state and resulting destination value.

### E05: overlapping numeric copy and exact release count

[Finalizer.Entry](../../../../RMQ/Core/WordRAM/Lifecycle/Finalizer.lean#L82)
requires running PC at the hosted base, extent `B+M`, registers 0 and 2 equal
to `B` and `M`, each source cell initialized, and absent numeric tail.
Under that entry and `Hosted`, `finalizer` proves `FinalOutput`, running exit
at `base+14`, and exact steps `7*M+4*B+5`.
`finalizer_memory cells` additionally assumes only the produced source lookup
for `i<M`, and concludes:

```text
final.memory = fun a => cells[a]?
final.extent = cells.length
final.status = running
final.pc = base + 14
```

`ordered_copy`: for every `i<M`, actual load/store occurrences are `4+7*i`
and `5+7*i`, satisfy the same `CopyReceipt original B i`, and have the actual
prefix pre-states and successful `step` equations. `ordered_release`: for
every `k<B`, occurrence `5+7*M+4*k` has `ReleaseReceipt (M+(B-k)-1)` and its
actual producing prefix. `finalizer_category_counts` counts exactly `M` reads,
`M` writes and `B` numeric releases; `finalizer_frame` covers all prefixes.
`Finalization.descriptor_to_finalizer` derives this entry on the actual
descriptor exit, and `copy_stage` specializes the whole-memory conclusion to
the same `cells`.

### E06: separate key retirement and READY

[Retirement.Entry](../../../../RMQ/Core/WordRAM/Lifecycle/Retirement.lean#L33)
requires running PC at the fragment base, key extents `n` and `2`, register
302 equal to `n`, and Closed. `comparison_retired` derives actual steps
`4*n+5`, running PC `base+8`, both extents zero, both key functions default,
and unchanged numeric memory/extent and registers outside 6/7.
`key_release_at` locates release `k<n` at `3+4*k` and cell `n-k-1`;
`key_register_release_at` locates releases `j<2` at `4*n+3+j`.
`word_retired` is the actual zero-step identity on already empty banks.

[Finalization.completed](../../../../RMQ/Core/WordRAM/Lifecycle/Finalization.lean#L215)
consumes `BuildStage`, not an assumed finalizer result, and proves actual
`RunsTo` through descriptor/copy/retirement/jump, `Retained.Canonical xs`
at its `finalState`, `Service.Inputs` on that same projected state, exact
continuation cost, and transition safety. `full_execution` prepends the actual
builder trace. `exact_cost` is:

```text
fullTrace.length = builderTrace.length + 11 + (7*M+4*B+5)
                   + retirementCost model n + 1
```

`linear_cost` bounds this completed trace by `1100000000*(n+1)`.

### E07: first service and complete compact suffix

[Service.Inputs](../../../../RMQ/Core/WordRAM/Lifecycle/Service.lean#L44)
requires running PC at entry, request registers 300/301, and zero numeric tail
at 8273. The service loads `n` from the retained header, copies the request to
registers 0/1, clears registers 3 through 8272, then jumps to PC 0. This restores
the exact accepted compact initial registers, including dirty incoming banks.

[Continuous.exact_run](../../../../RMQ/Core/WordRAM/Lifecycle/Continuous.lean#L48)
under the derived `BuildStage` identifies `actual` with the actual service final
state and `Finalization.fullTrace ++ serviceRun.transitions`. Completion and
stopped-run extension justify the fixed lifecycle budget. `query_suffix`
further factors the service into an actual preparation/clear trace of length
`4+8271` and `compactQueryRun cells n left right`.transitions mapped by the
complete-state `liftTransition cells`. `halts` gives the reference packet;
`cost` gives exact completed lengths and bound
`1100000000*(n+1)+160253`.

The [QueryBridge](../../../../RMQ/Core/WordRAM/Lifecycle/QueryBridge.lean#L75)
and [QuerySafetyBridge](../../../../RMQ/Core/WordRAM/Lifecycle/QuerySafetyBridge.lean)
lift complete transitions and attempted receipts, including absent replies and
repetitions. Canonical execution subsequently proves successful reads; this
does not erase failure behavior from the generic adapter.

### E08: reusable admission, observations and result

[Reusable.query_correct](../../../../RMQ/Core/WordRAM/Lifecycle/Reusable.lean#L114)
takes exactly `Canonical xs s`, `s.status = halted answer`, and represented
endpoints. It derives Canonical final state, exact halted reference packet,
unchanged whole numeric memory/extent, exact steps
`4+4+8271+compactQueryRun.steps`, and `steps <= 160257`.
`query_action_safe` proves the boundary/instruction union at every event;
`query_transition_canonical`/`query_transition_fits` cover both states of every
event. `query_resources` also frames key functions/extents and numeric tail.

`query_reads` is exactly
`(0,some n) :: compactQueryRun.reads.map (address,reply)`.
`query_ordered_reads` expands the compact part to metadata reads 0 through 173
followed by the accepted logical trace when `ValidRange`, and `[]` otherwise.
`query_read_occurrence` proves any read at index `k` is the actual service
occurrence `k-4`, with `4<=k`, actual prefix pre-state/step, canonical backing,
represented address, and present represented reply.

`query_valid` adds `left<right ∧ right<=n` and concludes
halted packet `scanWindow xs left (right-left)+1` and the full
`LeftmostArgMin` specification. `query_invalid` adds its negation and concludes
halted zero with exactly `[(0,some n)]` reads. `query_leftmost` turns any observed
positive packet `index+1` into `LeftmostArgMin xs left right index`.

### E09: width, peak and same-owner retained capacity

[Resources.run_key_extents](../../../../RMQ/Core/WordRAM/Lifecycle/Resources.lean#L60)
has no safety premises: every run final state and every transition before/after
has both key extents bounded by the corresponding initial extent.
`run_numeric_closed` needs only initial numeric `CleanTail` and preserves it
at those same states. `Reusable.construction_key_peak` specializes to the actual
program/input at every fuel: comparison bounds are `n,2`, word bounds `0,0`.

`Finalization.full_prefix_peak` bounds every prefix through the construction
trace by `5000000*(n+1)` numeric cells. `Continuous.prefix_resources` extends
that bound and finite numeric support through the first service. The
[Profile](../../../../RMQ/Core/WordRAM/Lifecycle/Profile.lean) conjunction combines
those facts with Fits, clean tail and separate key bounds on the same prefix;
its development compile is recorded by `profile01`; final-source checks remain
separate.

[Accounting.retained_capacity](../../../../RMQ/Core/WordRAM/Lifecycle/Accounting.lean#L70)
proves `(M + encodedProgram.length + 8273 + 8)*W <= 2*n+retainedRho n`.
`retainedRho_littleO` is for the same fixed rho. `Ownership.Ready.capacity_bound`
rewrites the executed owner's actual memory/register sizes to those terms.
The word profile is the existing query-independent `PW.wordWidth n`; the
builder's bounds, program operands, every state and physical addresses must all
be consumed at this same width. A large constant width witness is not used.

### E10: evolving physical backing

[Physical](../../../../RMQ/Core/WordRAM/Lifecycle/Physical.lean#L20) fixes code,
register, control and arena offsets for `p`. `view model s` includes the current
arena lookup; `checkedAddress` rejects a logical address outside its extent.
The scalar store/reserve/release and boundary image lemmas describe those actual
updates. `physicalReads_exact` preserves the whole ordered logical receipt
projection; `image_occurrence` preserves each transition index and its two
physical views. `runArray_image` connects this image to finite-container runs
under the operational destination bounds.

`Continuous.physical_read` ties an actual continuous read occurrence to its
actual prefix state and indexed image and derives physical/logical address and
reply width. `physical_prefix` bounds each evolving physical extent and stored
word. `Physical.canonical_capacity` identifies the initialized retained numeric
word list with the same view and proves its complete capacity bound. Comparison
Int values remain a separate resource (`oracle_values_irrelevant`). This is the
contract's evolving-arena interpretation, not a native allocator theorem.

### E11: supplied-store agreement and loaded-value dependency

[Agreement.State.Agree](../../../../RMQ/Core/WordRAM/Lifecycle/Agreement.lean#L16)
equates numeric registers, numeric extent, key registers, PC/status and both
key extents; memory/key lookup functions may differ. `Instruction.ReadAgree`
requires equality of an executed numeric load reply only under its actual
in-extent guard, and equality of an executed `loadKey` reply unconditionally.
`DynamicReadsAgree p fuel s t` recursively applies this condition at the two
actual producing prefixes. It accepts absent replies and repeated attempts.

`run_agree_of_dynamic_reads p fuel s t` assumes initial `State.Agree` and this
dynamic relation, and derives positional `Run.Agree`. Its projections give
equal final numeric registers/status/result, actions, categories/counts, steps,
ordered numeric/key reads and writes. Unread backing cells need not become
equal. `Run.Agree.occurrence` pairs the same occurrence index. The default
branches of `DynamicReadsAgree` are sufficient only together with initial
agreement: matching next fetch/stop behavior is derived inductively.

`load_occurrence_value_dependency` assumes two actual occurrences at the same
index with the same load opcode and evaluated address, both guarded successful
source cells, and distinct replies. It concludes distinct destination register
values, not just distinct records. `absent_source_rejects_read_agreement`
negates the same positive reply relation when a present in-extent source is
replaced by `none`. `requestProtocol_agree` transports full agreement through
the same charged boundary events.

### E12: arrays, production ownership and reuse

[ArrayRun.executeArray_toState](../../../../RMQ/Core/WordRAM/Lifecycle/ArrayRun.lean#L147)
and `executeBoundaryArray_toState` refine the actual scalar implementations
under finite destination bounds. `runArray_toState`/`runOwner_toState` preserve
the corresponding whole execution; `ArrayRun.observations_toRun` and occurrence
lemmas preserve cost categories and ordered reads/writes. `Owner` is the
existing finite `C.ExecState`; `runOwner` returns no observation history.

[Executable.initial_owner_refinement](../../../../RMQ/Core/WordRAM/Lifecycle/Executable.lean#L639)
and `initial_array_refinement` derive every required destination bound from
the common input guards, for every fuel. Their conclusions identify the actual
finite final state/full run with `run p fuel initial`, and numeric bank size
8273. The key destination argument is phase-specific: builder comparison loads
use only registers 0/1; subsequent phases are key-load free.

[Ownership.refinement](../../../../RMQ/Core/WordRAM/Lifecycle/Ownership.lean#L43)
specializes to `Continuous.lifecycleBudget n`, identifying both production owner
and optional observations with `actual`. `Ownership.Ready.empty_keys` derives
literal `#[]` key arrays from zero extents. `Ownership.Ready.query`, under Ready,
halted status and represented endpoints, derives Ready/packet on
`Executable.queryOwner`, equality of its actual numeric array with the incoming
owner, exact `queryArray.toRun = Reusable.queryRun`, and bound 160257.

### E13: public contract and exact object arguments

[Capstone.continuousConstructionQuery_holds](../../../../RMQ/Core/WordRAM/Lifecycle/Capstone.lean#L123)
has the type:

```lean
(model : InputModel) (xs : List Int) (left right : Nat)
(domain : InputDomain model xs)
(hl : left < 2 ^ wordWidth xs.length)
(hr : right < 2 ^ wordWidth xs.length) :
  ContinuousConstructionQuery model xs left right
```

The seven fields of the resulting Prop record are:

| Field | Guarded proposition on the named objects |
| --- | --- |
| `construction` | One existential `abstract,producer,body` with the derived `BuildStage`, linear `fullTrace` length, canonical/entered `Finalization.finalState`, exact `continuousRun` equality, and the full compact suffix plus exact step equation. |
| `retained` | Canonical `actual.final`, its exact halted reference packet, and actual completed steps bounded by `constructionBudget n+160253`. |
| `safety` | `Continuous.PrefixProfile` for every fuel through `actual.steps`, and instruction safety for every actual transition. |
| `physical` | Exact whole ordered physical-read projection; physical extent and value widths at every prefix; indexed read backing/pre-state; and each actual instruction's encoded words fetched from the same counted code range. |
| `executable` | `Ownership.owner.toState = actual.final`, `Ownership.observations.toRun = actual`, Ready and literal empty key arrays, and capacity of that same executed owner. |
| `reusable` | For every Ready owner, halted packet and represented next endpoints: Ready/packet, equality of the actual memory array, exact `queryArray` refinement, query cost/read list, every event ActionSafe with canonical before/after, and capacity of that same next owner. |
| `uniform` | `LittleOLinear retainedRho`, `log2(n+2)+1 <= W <= 192*(log2(n+2)+1)`, and every field of `encodedProgram model` below `2^W`. |

`wordInputContinuousConstructionQuery` specializes only the input encoding
predicate; `comparisonInputContinuousConstructionQuery` has no Int-magnitude
guard. `ContinuousConstructionQuery.valid` derives the scan-window packet and
leftmost contract under `ValidRange`; `.invalid` derives packet zero under the
complement. The separate public `lifecycle_store_determinism` specializes E11 to
the actual fixed program, retaining initial state agreement and paired dynamic
reply agreement as its only operational hypotheses.

`Physical.run_fetched_words` in
[CodeFetch](../../../../RMQ/Core/WordRAM/Lifecycle/CodeFetch.lean#L45) quantifies
the actual instruction occurrence and every field index. It proves that the
program's prefix-encoding length plus that field lies below the counted code
length and that the physical code lookup returns the same field word. This
connects code accounting to fetch; a dormant-field width theorem alone would
not supply that identity.

### E14: whole-run producing positions

[Provenance](../../../../RMQ/Core/WordRAM/Lifecycle/Provenance.lean#L201) makes the
component-to-continuous index arithmetic explicit. Its public companion theorem
is `continuous_production contract`, with no additional input, answer
or finalizer premise. The conclusion keeps one existential
`abstract,producer,body` shared by `BuildStage` and `ProductionReceipts`.
`Occurrence ... k t` expands to the actual `continuousRun.transitions[k]?`,
the complete prefix pre-state, and `step p t.before = some t`.

The four receipt groups constrain:

* `output`: an actual `reserve 3` at index below `body.length`, the old extent
  equaling `producer.regs 3`, a register-3 frame at every whole-run prefix from
  the reservation through the builder exit, and the actual `move 0 3` at
  `body.length` whose destination equals that reserved extent.
* `metadata`: actual `ReadReceipt` at global offsets
  `body.length + {1,4,8,10}` for `n`, `M`, left and right.
* `copy`: actual load/store at `body.length+11+(4+7*i)` and
  `body.length+11+(5+7*i)` for every `i<M`, with the unchanged production
  `CopyReceipt producer.memory B i`, the canonical loaded value and canonical
  stored cell.
* `releases`: actual `ReleaseReceipt (M+(B-k)-1)` at
  `body.length+11+(5+7*M+4*k)` for each `k<B`.

The independent
[provenance consumer](../../../../scripts/lifecycle_provenance_contract.lean)
spells out the occurrence and scalar receipt predicates rather than aliasing
the mutable producer definitions. `checkP01` projects all four groups from
`continuous_production` on the same witness. `provenance01` compiled the source
in 5.772 seconds; `provenance_inventory01` printed the exact types and standard
axioms in 13.203 seconds; `lifecycleprovenancecontract01` compiled the independent
client in 3.852 seconds without diagnostics. Provenance source SHA-256 is
`454ecb3a9615977aa2d5d52015771a187fada6e6f5ce1f90d5a125cd873d273e`.
The final registered shadow replay passed all26 cases, including P01-P05
expected rejections and P06 expected acceptance; its actual summary and restored
source/artifact identities are recorded in DEPENDENCY_VERIFICATION.md.

## Same-object composition and final integration evidence

The source chain to be consumed by the public theorem is:

```text
InputDomain + represented request
  -> Construction.build_stage (one producer and old trace)
  -> Finalization.full_execution (one producedState/fullTrace)
  -> Continuous.exact_run (the defined continuousRun, not a sibling run)
  -> canonical result + prefix resources + exact compact suffix
  -> Executable initial refinements at that same fixed budget
  -> Ownership.refinement/Ready and actual retained capacity
  -> Ownership.Ready.query / Reusable queryRun for every next represented request
```

The capstone source above consumes this chain, and development receipt
`capstone04` records a successful compile (3.331 seconds).
[LifecycleContract](../../../../RMQ/Validation/LifecycleContract.lean) compiled
under `lifecyclecontract04` (12.421 seconds). Its C01-C07 clients independently
expand the seven fields, including canonical memory, readiness and prefix
resource predicates; C08/C09 pin both public input forms; C10 pins constants;
C11/C12 pin valid/invalid packets; C13/C14 pin supplied-store determinism and
its actual-step numeric/key reply guard. The direct global-provenance consumer
is recorded in E14. Final B/T/N/D receipts now bind this chain: default/named
builds passed in5.732/57.584s, the exact type/axiom inventory in135.302s,
the corrected16-case native replay in81.505s, and the full26-case dependency
summary reports passed=true with all expected verdicts and restoration checks.
A compiled client alone is not credited as an observed mutation rejection.
ACCEPTANCE_EVIDENCE.md maps all43 IDs to these actual final consumers and the
mandatory S source/static/delivery identity invariant.

## Frozen-row cross-reference

The IDs below reference the verbatim frozen requirements; these are evidence
routes, not replacement frozen row statuses. Current candidate-local
dispositions and final evidence families are in ACCEPTANCE_EVIDENCE.md.

| ID | Proposition route and exact required consumer |
| --- | --- |
| L1-01 | E01: conservative complete-state old embedding, scalar releases/zero faults, four charged boundary events; consume in the actual lifecycle/query run. |
| L1-02 | E02: `program model` has no data arguments; actual fragment hosts and encoded-field inventory; same program in E07/E12. |
| L1-03 | E03 then E06/E07: live nonzero BODY `RunsTo`, full producer identity and exact trace concatenation. |
| L1-04 | E03 reservation occurrence -> E04 occurrence 0 and metadata/request reads -> E05/E07 actual ABI; E14 lifts the same producer/operands to global indices. |
| L1-05 | E05: initialized produced source, exact whole-memory/extent/tail, positional copy and exactly B releases; E06 composes and E14 pins global indices. |
| L1-06 | E06 -> E12: actual scalar key retirement, zero extents, literal empty owner arrays, no trace field in `Owner`; native aliases/capacity are separate. |
| L1-07 | E04 n/request production -> E06 jump -> E07 prepare/8270 clears/jump; incoming support derived, not assumed at the public input. |
| L1-08 | E07 exact `actual` and full compact transition suffix; E10 backing; valid and invalid projections must use that same run. |
| L1-09 | E08 and E12: arbitrary dirty finite bank, four boundary events, same owner array, restored Ready, constant 160257. |
| L1-10 | E03 discharges execution from the common all-size domain; E08 guards valid/invalid represented requests coherently. |
| L1-11 | E02 fields + E03/E07 state Fits + E09 profile + E10 physical addresses; final consumer must use the same logarithmic `W`. |
| L1-12 | E06 completed exact cost and linear bound; E07/E08 completed service/reuse counts, separate key categories. |
| L1-13 | E09 every-prefix numeric/separate-key bounds and same-owner retained rho; E10 numeric physical view and E12 actual sizes. |
| L1-14 | E11 paired actual producing-prefix agreement and projection-specific load dependence; E04 source projection. |
| L1-15 | E12 derived destination refinement and history-free owner; N executes the new layer with independent expectations and actual program-clear mutation, while D05/D17 reject lost public refinement/bank facts. |
| L1-16 | E13 projects E01-E12 on `actual`/`owner`; independently expanded C01-C14 and E14 checkP01 clients compile; final-source mutation receipts remain separate. |
| L1-17 | Nine kernel controls plus both actual second-query ABI negatives passed; N witnesses dirty register400 and the exact checked P-to-Q bridge. |
| L1-18 | Final D contains all26 expected-type dependency cases plus observed selector/diagnostic/owned-cleanup/restoration controls and3 expected accepts; final source identities are recorded. |
| L1-19 | The worked guide, this typed dependency route, generic scalar helpers, and reuse of original builder/compact query; no second machine is introduced. |
| L1-20 | Final commit, exact types/axioms, new validator and controls, default/named builds, design/claim/whitespace/contract checks remain governed by VERIFICATION_PLAN.md. |
| INV-STORE-IDENTITY | E05 canonical whole memory -> E07 same `cells` suffix -> E12 exact owner projection -> E09/E10 count that owner/view. |
| INV-VALUE-DEPENDENCY | E03 exact reserve source/frame, E04 actual transfer/load projection, E05 loaded-to-stored value chain, E11 distinct replies force distinct destination values. |
| INV-SEMANTIC-NONVACUITY | E03 derives the producer; E05/E06 derive finalizer/retirement outputs; E12 derives empty arrays from actual execution. |
| INV-TRACE-EXECUTION | `RunsTo`, E07 exact run, E08 actual append, E11 positional pairing and E12 whole-run equality. |
| INV-STORE-AGREEMENT | E11 initial `State.Agree` plus guarded `DynamicReadsAgree` implies full operational projections; no final-answer premise. |
| INV-READ-BACKING | E04/E05 occurrence receipts; E08 `query_read_occurrence`; E10 actual prefix and physical image at the same index. |
| INV-WORD-WIDTH | E03/E07 Fits, E08 represented before/after/result, E10 lookup/value bounds at `W`. |
| INV-ADDRESS-WIDTH | E02 every encoded field, E09 prefix Fits/peak, E10 checked logical/physical addresses including rejected attempts. |
| INV-INSTRUCTION-ATOMICITY | E01 constructor implementation; E05 copy/release and E07 clearing are loops of scalar transitions, not new macro primitives. |
| INV-PROGRAM-ACCOUNTING | E02 input-independent code and flattened encoding; E04 runtime descriptors and E09 8273+8 state words. |
| INV-ORACLE-INDEPENDENCE | Valid packet connects to `scanWindow`/`LeftmostArgMin`; N uses its own strict-improvement reference scan and passes all16 cases. |
| INV-VALIDATION-REACH | N invokes actual initialOwner/runOwner/queryOwner and rejects one changed real service-clear instruction on the same produced owner; D05/D17 bind public executable refinement. |
| INV-ALL-SIZE | E03 quantified `List Int`/InputDomain and endpoint guards; no size/readiness dispatch; invalid compact behavior plus service header remain coherent. |
| INV-PROOF-SEPARATION | State/Owner/Instruction contain data and scalar control only; derived Prop records do not supply an executable answer. T reports only standard axioms and both final hygiene scans are empty. |
| INV-NO-SYNTHETIC | Actual old/body/fragment/service transitions compose by `RunsTo`; E07/E12 equalities rule out detached replay as the implementation. |
| INV-CATEGORY-SEPARATION | E01 release/boundary categories, E06/E08 actual counts, E09 separate peak/retained numeric/key resources; no native runtime claim. |
| INV-PUBLIC-COMPOSITION | E13 consumes E03 -> E06 -> E07 -> E12 -> same E09/E10 capacity; independent consumer must preserve all object arguments and guards. |
| INV-CERTIFICATE-ANTI-BYPASS | Independent C01-C14/checkP01 types project every public group; D observes23 expected rejects and3 expected accepts on exact producer/client objects. |
| INV-MUTATION-REPRODUCIBILITY | Immutable scalar fixtures, N's in-memory clear challenge and D's exact versioned26-case registry have final replay, diagnostic and restoration receipts. |
| INV-GLOBAL-PHYSICAL-MACHINE | E10 common fixed offsets plus evolving arena state at every segment/occurrence, scalar update images and array refinement. |
| INV-WIDTH-SCALING | Existing logarithmic `PW.wordWidth n` consumed by E02/E03/E07/E09/E10, not an independently chosen per-instance width. |
| CHK-FINAL | Final-source checks/identities/platform outcomes from VERIFICATION_PLAN.md, not reuse of earlier development receipts as certification. |
| CHK-SCOPE | Only assigned source/docs; exact base, unchanged 43 frozen rows, permitted paths and clean committed state checked by coordinator. |

## Positive and negative predicates

The full objects, guards and replay method are maintained in
[CONTROL_PREDICATES.md](CONTROL_PREDICATES.md). In each compiled scalar case
below, `P = R positiveObject` and the challenged `Q = R mutatedObject` use the
same production relation `R`; the negative theorem proves `not Q`. These are
concrete control witnesses, not universally quantified sensitivity claims.

| Control | Exact R and challenged projection |
| --- | --- |
| OUTPUT-SOURCE | `Descriptor.OutputReceipt`: actual `move 0 3` versus `move 0 4`; distinct supplied values also force destination inequality. |
| SKIPPED-INITIALIZATION | `Finalizer.Initialized memory 1 2`: reserve/constant/store versus skipped store; address 2 remains absent. |
| STALE-TAIL | Same `Finalizer.Entry 0 1 2` and `FinalOutput original 1 2`; extra initial cell violates the entry, and the challenged output retains extent 3. No rejection under valid entry is asserted. |
| ABSENT-SOURCE | Same `copiedAt` definition wrapping production `CopyReceipt` with actual indexed occurrences; failed second load leaves no following store occurrence. |
| OMITTED-RELEASE | Same `FinalOutput original 1 2`: both copied words agree, but extent remains 3 when release becomes a constant write. |
| BACKWARD-COPY | Same `FinalOutput`: extent/release count are right, but overlap destroys the next source and destination 0 becomes 22 instead of 11. |
| KEY-RETENTION | `Retired s := keyExtent=0 and keyRegExtent=0`; default-valued arrays of length one reject despite all lookups being none/zero. |
| WRONG-ENTRY | Same full Entry/FinalOutput predicates; PC 1 skips counter initialization and retains the old suffix. |
| FIELD-OVERFLOW | Same `forall i in program, i.Fits 8`; dormant immediate/register/target value 256 rejects while 255 accepts. Both halt before the dormant instruction. |
| SECOND-QUERY-DIRTY-BANK | `RMQ.Validation.PackedLifecycle.dirtyControl` starts both service entries from the same real first-query owner and replaces one witnessed dirty register's clear by a self move. The same `entryRegisterClean owner r` accepts the positive and rejects the challenge; `dirty_register_rejects_entry` proves rejection of the exact compact ABI. N:L11-W-DIRTY/L12-C-DIRTY both passed with actual register400. |

For arbitrary supplied stores, E11 uses an explicitly different kind of
comparison: positive `ReadAgree` at an actual guarded load versus the same
relation after removing its source. For value sensitivity, both reads must
succeed at matching actual occurrences and the replies must differ. Neither
result proves that every payload mutation changes every RMQ answer.

The dirty-bank bridge in
[Controls](../../../../RMQ/Core/WordRAM/Lifecycle/Controls.lean#L280) spells out
`P := Retained.projectQueryState owner.toState = PW.initialState n left right`
and `Q := entryRegisterClean owner r = true`. Under `3 <= r`,
`query_entry_implies_clean` proves `P -> Q`; `dirty_register_rejects_entry`
uses the observed false Boolean to prove `not P`. Thus its negative is not
merely rejection of a stronger unrelated predicate. The runtime witness chooses
an actually nonzero register at or above 400 after the first query and checks
both entries on the same admitted owner, same memory and bank size. This
challenges initialization, not an unsupported claim that changing this register
must change the eventual answer.

## Final executable and dependency reconciliation

[PackedLifecycle](../../../../RMQ/Validation/PackedLifecycle.lean) compiles the
new finite runner, independent strict-comparison reference scan, history-free
validation counters and sixteen exact word/comparison fixtures. Its source
checks empty, singleton, repeats, tied minima, represented invalid requests,
dirty second-entry cases, and geometry inputs of lengths 24/83; comparison
geometry uses2^(wordWidth n+5) scaling and explicitly witnesses keys outside
the signed word-input domain. `counted_owner` proves its counter fold has the
same final owner as `runOwner`. Historical label lifecycle-validator-05 checked
an earlier source. Final lifecycle-validator-06 compiled in13.122s and native03
built in12.593s; corrected final all16 execution passed in81.505s, including
both actual dirty-bank controls. The [validator runner](../../../../scripts/lifecycle_validator.ps1)
recorded9 clean owned process receipts for registry/startup/focused selection,
five selector negatives and full replay, with exact output classification and
unchanged source/binary hashes. NATIVE_VERIFICATION.md records the full command
history and .lake/lifecycle-validator/da0d7bf710d148dfa5e439022fca3ede receipts.

The frozen
[dependency registry](../../../../scripts/lifecycle_dependency_cases.json)
currently contains D01-D20 and P01-P06: 23 expected rejections and three
expected acceptances. It challenges all seven public groups, field removal,
sibling physical evidence, mutable public/alias types, retained cost, code
fetch, prefix resources, Ready bank size, store determinism, the four global
provenance groups, and the public provenance theorem itself. Comment/identity
cases are expected acceptances. The
[replay runner](../../../../scripts/lifecycle_dependency_replay.ps1) is the
production verdict path. Actual final summary
.lake/lifecycle-dependency/20260921T021035666-83fc2827/summary.json reports
passed=true,26 selected/cases, all23 rejection and3 acceptance exits matching,
every original/private restoration=true and shadowRemoved=true. Its SHA-256 is
17d5798eb4a91699c2b938fa9f82e393652c43de9a28654976649c8c5ae29ed7.
DEPENDENCY_VERIFICATION.md preserves final focused-selector, mixed/fatal JSON
diagnostic, timeout/descendant cleanup and private-artifact binding controls,
as well as rejected development attempts. Expected registry entries alone are
never credited as observed verdicts.

Final default/named builds and exact type/axiom inventory are B/T in
ACCEPTANCE_EVIDENCE.md; the inventory took135.302s and reported only subsets of
propext/Classical.choice/Quot.sound, with no axioms for constant pins. Both
required trust-hygiene scans have zero matches. SOURCE_MANIFEST.json,
FINAL_RECEIPTS.json and REPORT.md bind source and static evidence. S is the
mandatory delivery invariant: actual post-closing-commit outcomes are in
external delivery.json/submission, avoiding self-referential report hashes.
This is candidate-local worker reconciliation, not coordinator acceptance.

## Verification provenance and maintenance

Known development receipts for this leaf chain include
`construction02`, `finalization04`, `resources02`, `reusable_ext04` and
`reusable_inventory01` under `.lake/lifecycle-dev`. They establish the source
versions compiled by those commands, not the final campaign tree. The reusable
inventory reported only `propext`, `Classical.choice`, and `Quot.sound` (numeric
clean-tail preservation uses a subset). The controls document pins its own
source hash and replay receipt. Root owns the final capstone/consumer inventory,
validator, mutation and certification ledger.

When a source declaration moves, update its location and inspect its exact type
before changing this prose. When a proposition, guard or object changes, update
the corresponding consumer and replay controls; a declaration rename alone
does not preserve the evidence chain. No new design choice is made by this
inventory: it documents the existing machine, layout, predicates and owners.
