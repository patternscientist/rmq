# Lifecycle proof guide

This guide follows the executed objects in `RMQ/Core/WordRAM/Lifecycle`. The
[proof inventory](../internal/extensions/lifecycle1/PROOF_INVENTORY.md) records
the precise guards, propositions and frozen acceptance-row dependencies. It is
an implementation guide, not an acceptance or final-verification record.

## The objects to keep together

For input `xs`, write `n = xs.length`, `W = PackedWordRAM.wordWidth n`, and
`cells = PackedWordRAM.buildMemory xs`. `InputModel.word` requires the existing
signed `InputFits W xs`; `InputModel.comparison` admits every `List Int` and
accounts for the Int key banks separately. Both routes require
`left < 2^W` and `right < 2^W`. Input materialization is the declared initial
boundary; construction and query instructions do not construct their expected
answers from `xs`.

The program is `Layout.program model`. Its definition has no `xs`, `n`, shape,
or endpoint argument. The initial state is
`initialState model xs left right Layout.builderBase`. Its numeric memory owns
the input representation followed by two request words. Initial numeric extent
is `n+3` for word input and `3` for comparison input. Comparison input owns `n`
key cells and two key registers; word input owns neither bank.

The actual physical numeric view places the fixed encoded code, 8273 numeric
registers, eight control words, and the current arena in consecutive disjoint
ranges. The arena evolves through stores, reservations and tail releases. An
uninitialized reserved cell remains `none` in this view. Int comparison values
are not silently recoded as bounded numeric words.

## A worked route

Consider `xs = [4,1,1,7]` with request `[0,3)`. The independent half-open,
leftmost specification selects index `1`, so the machine's successful packet is
`2`. This is an explanatory instance of the quantified contract, not a recorded
execution measurement. Keep `M = cells.length` symbolic and obtain `B` from the
execution rather than guessing either value.

| Phase | Actual location and effect | Proof route |
| --- | --- | --- |
| Builder BODY | Starts running at PC `221239`; exits running at `223345`. It allocates the produced canonical cells at `[B,B+M)` and leaves `B` in register 3. | [Builder.HostedBody](../../RMQ/Core/WordRAM/Lifecycle/Builder.lean#L123), [Construction.build_stage](../../RMQ/Core/WordRAM/Lifecycle/Construction.lean#L267). |
| Descriptor | Eleven charged instructions start at `223345`. Occurrence 0 moves register 3 to register 0. Reads at occurrences 1 and 4 load `n` from `B` and `M` from `B+7`; occurrences 8 and 10 load the saved request into registers 300 and 301. | [Descriptor.transfer](../../RMQ/Core/WordRAM/Lifecycle/Descriptor.lean#L53), [read_occurrences](../../RMQ/Core/WordRAM/Lifecycle/Descriptor.lean#L271). |
| Numeric finalizer | Starts at `223356`. Copies forward from `[B,B+M)` to `[0,M)`, then executes exactly `B` single-cell releases. | [Finalizer.finalizer_memory](../../RMQ/Core/WordRAM/Lifecycle/Finalizer.lean#L534), [ordered_copy](../../RMQ/Core/WordRAM/Lifecycle/Finalizer.lean#L570), [ordered_release](../../RMQ/Core/WordRAM/Lifecycle/Finalizer.lean#L615). |
| Key retirement | At `223370`, comparison input executes `n` key releases followed by two key-register releases. Word input has an empty retirement fragment. | [Retirement.comparison_retired](../../RMQ/Core/WordRAM/Lifecycle/Retirement.lean#L394), [Finalization.retire_copied](../../RMQ/Core/WordRAM/Lifecycle/Finalization.lean#L154). |
| First query entry | A real jump enters PC `212964`. Four service instructions load the retained header and copy the request, then 8270 scalar clears and one jump establish the compact-query ABI at PC 0. | [Service.prepare](../../RMQ/Core/WordRAM/Lifecycle/Service.lean#L24), [QueryEntry.setup_exec](../../RMQ/Core/WordRAM/Lifecycle/QueryEntry.lean#L181). |
| Compact query | The accepted compact transition list is lifted on exactly `cells`. The final packet is obtained by those instructions. | [Continuous.query_suffix](../../RMQ/Core/WordRAM/Lifecycle/Continuous.lean#L161), [QuerySafetyBridge](../../RMQ/Core/WordRAM/Lifecycle/QuerySafetyBridge.lean). |

The reservation provenance is stronger than a numerical equality: it supplies
an indexed actual `reserve 3` occurrence, its pre-state extent, and a register-3
frame through the entire following builder suffix. The descriptor's source is
the operand `3` of its actual `move 0 3`, even if some other register happens to
contain the same number.

[Provenance.continuous_production](../../RMQ/Core/WordRAM/Lifecycle/Provenance.lean#L201)
lifts these receipts into the actual continuous trace using one shared producer
witness. If the builder trace has length `T`, transfer is at `T`, descriptor
reads at `T+1`, `T+4`, `T+8`, `T+10`, copy load/store at
`T+11+4+7*i` and `T+11+5+7*i`, and release `k` at
`T+11+5+7*M+4*k`. Each occurrence includes its complete actual prefix pre-state
and step equation, so equal repeated events remain distinct occurrences.

Forward order matters when source and destination overlap. At copy iteration
`i`, the load precedes the store and the copy invariant preserves every future
source cell. The whole-memory theorem includes absence at every address
`a >= M`; matching only the first `M` values would not establish retirement.

## Composition and repeated queries

`Construction.build_stage` derives a live producer and its complete state from
the input contract. `Finalization.full_execution` composes its actual ordered
trace with descriptor, copy, key retirement and jump. `Continuous.exact_run`
then identifies the fixed-fuel `continuousRun` with that trace followed by the
actual service trace. Extra fuel is justified only after the composed execution
is proved halted. No phase replaces the machine state by a separately prepared
equal-memory state.

At the retained boundary, `Retained.Canonical xs s` means the whole numeric
memory is canonical lookup, extent is exactly `M`, both key functions are
default, both key extents are zero, registers at or above 8273 are zero, and the
state fits `W`. Registers below 8273 may be dirty. The service clears the full
finite query bank, so a second request such as `[2,4)` does not rely on the
builder's smaller 400-register frame.

`Reusable.queryRun` first executes four explicit boundary events on a halted
state: write left, write right, set the fixed service PC, activate. It appends
the actual service transitions. The boundary contributes four charged events
and no numeric reads. Every service performs its header read, including invalid
requests. Consequently an invalid represented request has packet zero and read
list `[(0,some n)]`; the compact guarded suffix alone has an empty read list.
For valid requests, the additional header read precedes the compact metadata
and logical-read sequence, including repeated addresses.

## What is counted

| Quantity | Fixed theorem bound or exact expression |
| --- | --- |
| Finalizer transitions | `7*M + 4*B + 5`. |
| Comparison retirement transitions | `4*n + 5`; word retirement is zero. |
| Builder through final jump | At most `1100000000*(n+1)`, derived from a completed concatenated trace. |
| Service | `4 + 8271 + compactQueryRun.steps <= 160253`. |
| Reusable query including admission | `4 + 4 + 8271 + compactQueryRun.steps <= 160257`. |
| Peak numeric arena | At most `5000000*(n+1)` words at every actual prefix. |
| Separate comparison peak | At most `n` key cells and two key registers; both become zero before service. |
| Retained numeric capacity | `(M + encodedProgram.length + 8273 + 8)*W <= 2*n + retainedRho n`, with checked `LittleOLinear retainedRho`. |

These are model transitions and logical ownership/capacity bounds. They do not
measure native runtime, native allocation capacity, or external aliases.
`Physical.wordView` is an observation of the counted state, not an uncharged
machine operation used to produce the answer.

## Following the executable owner

`Executable.initialOwner` materializes the finite input arrays and requests.
`runOwner` computes only the final owner. `runArray` additionally returns
validation observations; the observations are not owner fields.
`Executable.initial_owner_refinement` and `initial_array_refinement` prove
equality with the same abstract execution for every fuel, deriving all finite
destination bounds from the actual phases. `Ownership.refinement` specializes
them to the continuous budget. `Ownership.Ready.empty_keys` concludes literal
empty key arrays, and `Ownership.Ready.query` preserves the actual numeric array
while restoring readiness after another charged query.

For maintenance, start with the smallest affected scalar theorem, then its
handoff and exact consumer. Keep occurrence indices when changing copy, release,
descriptor or read claims. Preserve all request guards across result, trace,
cost and capacity conjuncts. The [inventory](../internal/extensions/lifecycle1/PROOF_INVENTORY.md)
and [control predicates](../internal/extensions/lifecycle1/CONTROL_PREDICATES.md)
identify the concrete counterfactual each dependency must reject.
