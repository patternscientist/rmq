# LB-1 packed allocation proof notes

Status: complete adapter implemented and target-checked. Independent validation,
mutation replay, integration checks and coordinator acceptance remain parent-owned
obligations. This note is scoped producer evidence, not an LB-1 acceptance report.

Owner: packed adapter subagent for LB-1. Owned files:
`RMQ/Core/WordRAM/Packed/AllocationLowerBound.lean` and this note. No shared
Packed source, generic encoding interface, validation source, ledger or public
root was edited by this owner. Parent owns integration, validation, replay and
the full durable report. No commits have been performed by this owner.

Base and governing workflow: `0e6a00f654abc64f8b68988fa9675b9a839dca2f`.
Worktree: `C:/Users/poin/.codex/worktrees/2270/RMQ`.
Branch assigned by parent: `codex/lb-1-variable-payload`.

## Preflight and contract

The initial read-only inventory verified clean HEAD equal to the exact base.
`scripts/project_skill_preflight.ps1` passed against that governance ref with
required role `rmq-proof-sprint` and actual runtime project catalog
`rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint`. The canonical skill, AGENTS,
completion gate, relevant roadmap/PQ1 decisions and audit protocol were read.
The parent subsequently authorized implementation after its independent route
review. The generic interface remains exactly the one frozen in `CONTRACT.md`.

## Definitions and object composition

All definitions below are in `RMQ.SuccinctFinal.PackedWordRAM`.

```lean
serializeWords width words =
  (words.map (SuccinctSpace.natToBitsLE width)).flatten
deserializeWords width bits =
  (List.range (bits.length / width)).map fun i =>
    SuccinctSpace.bitsToNatLE ((bits.drop (i * width)).take width)
allocationBits xs = serializeWords (wordWidth xs.length) (buildMemory xs)
allocationDecoder n bits left right =
  queryNat (deserializeWords (wordWidth n) bits) n left right
reconstructedMemory xs =
  deserializeWords (wordWidth xs.length) (allocationBits xs)
UniformAllocationBudget n B =
  forall xs : List Int, xs.length = n ->
    (buildMemory xs).length * wordWidth n <= B
```

The mathematical decoder has no original-list, shape, proof, or input-specific
advice argument. Public size is its sole captured parameter; endpoints and the
observed bit list are its varying arguments. The bit-list length determines
the number of reconstructed words. Nothing pads the output to budget B.

`serializeWords_length` proves exactly `words.length * width` for all lists.
`deserializeWords_serializeWords` proves the full list equality under positive
width and `forall word in words, word < 2^width`. Its proof uses
`uniform_flatten_slice` and `bitsToNatLE_natToBitsLE_of_lt`, not an existential
decoder or a proof-carried lookup table. `serializeWords_injective` applies
that left inverse to both arbitrary bounded lists. Width zero is excluded only
from the inverse and injectivity, because all zero-word lists collapse there.
PQ1's `wordWidth_pos n` supplies the guard at every n including zero.

Canonical composition is:

1. `buildMemory xs` is the actual PQ1 word list, constructed as
   `shapeMemory (Cartesian.shape xs)`.
2. `buildMemory_words_fit xs` supplies its per-word bounds.
3. `reconstructedMemory_eq_buildMemory xs` is full `List Nat` equality.
4. `allocationDecoder_exact` rewrites by that equality and consumes
   `queryNat_exact`, giving `if ValidRange xs left right then some (scanWindow
   xs left (right-left)) else none` for all ordinary lists and endpoints.
5. `allocationEncoding n B budget` puts this exact decoder and `allocationBits`
   into the frozen `ExactRMQBoundedEncoding n B` interface. The only budget
   premise is uniform over every size-n ordinary list.
6. The generic `shapeCount_le` and `doubledLogSlackLower_le` are applied to that
   instance, yielding `shapeCount n <= 2^(B+1)-1` and
   `doubledLogSlackLower n <= 2*(B+1)`.
7. `canonicalAllocationBudget n`, from `buildMemory_capacity_le`, chooses
   `B = 2*n + allocationRho n`. `allocationRho_littleO` supplies the asymptotic
   residual. No individual allocation is claimed to satisfy the lower bound.

`shape_eq_of_allocationBits_eq` derives equal `SameRMQBehavior` from a common
payload decoder and equal lengths, then invokes
`Cartesian.shape_eq_of_sameRMQBehavior`. `allocationBits_shape_injective`
specializes to every shape in `shapesOfSize n` and its representative.
`allocationBits_representative` explicitly identifies that representative's
bits with `serializeWords (wordWidth shape.size) (shapeMemory shape)`.
Conversely, `buildMemory_eq_of_shape_eq` and `allocationBits_eq_of_shape_eq`
prove that same-shape inputs intentionally share words and serialized bits.

## Primitive transport and category boundaries

`ReconstructedPackedQueryCapstone` retains all 33 baseline PQ1 field types,
with every occurrence of `buildMemory xs` replaced by `reconstructedMemory xs`.
Each of the 22 memory-bearing initializers explicitly transports its matching
baseline field using `reconstructedMemory_eq_buildMemory`. The 11 fields with
unchanged, memory-independent types directly project the same baseline field.
The source marks the frozen field region
with `LB1-MACHINE-FIELDS-BEGIN/END` for the parent's independent consumer.

The transport preserves the actual whole primitive run, every fuel prefix,
word and address widths (including failed-address conventions), exact literal
instruction encoding, finite scratch accounting, positional read occurrences,
ordered logical refinement and supplied-memory agreement. Raw safety fields
retain both endpoint representability hypotheses. `reconstructedRun_eq` also
states equality of every fuel-prefix run on the two full word lists.

The serializer/deserializer are mathematical functions with no charged cost
assertion. `queryNat` retains its existing outer mathematical input check.
The word-RAM query bound concerns the primitive run on the reconstructed word
list. No deserialization scan is counted as one machine instruction. Fixed
program and scratch are included only in the separate complete-capacity
fields. Public n remains external. These conventions match PQ1.

`PackedAllocationOptimality` exposes 16 main fields and includes the entire
transported machine capstone as its `machine` field. The exact main signatures
are marked by `LB1-OPTIMALITY-FIELDS-BEGIN/END`. Both records also have corresponding
`INITIALIZERS-BEGIN/END` markers. The parent has written independent expected-type
consumers of all 49 fields and owns the executable/mutation registry. No field name,
type or count changed during the compilation loop.

## Verification state and digestion

The parent granted exclusive one-process build ownership. Both owned executions
used `pwsh -NoProfile -File scripts/variable_payload_build.ps1 -Module
RMQ.Core.WordRAM.Packed.AllocationLowerBound -DeadlineSeconds 1800`, the direct
Lean 4.22.0 toolchain on Windows, one `-j1` child per module, a kill-on-close owned
job and task-local dependency keys. The 1800-second deadline applied per module.

The initial cold-closure build began at 2026-09-12 07:24:55 UTC. It passed with
closure size 251, 250 rebuilt modules and no proof errors or timeouts. The adapter
itself was checked at 08:40:49 UTC in 7.658 seconds. Its only diagnostics were
unused `xs` and `ys` initializer variables on line 449. That proof term was made
explicit as `sameShapeMemory xs ys := @buildMemory_eq_of_shape_eq xs ys`; no theorem
proposition changed. Exact first-check evidence, including those two warnings and
139 pre-existing dependency warnings across eight modules, is retained in
`evidence/build-20260912T072455472.jsonl`.

The subsequent warm check passed with closure size 251 and only the changed
adapter rebuilt. It began checking the adapter at 08:41:52 UTC, took 9.714 seconds,
and emitted no warnings or errors. Its record is
`evidence/build-20260912T084142579.jsonl`. The checked adapter is 26,282 bytes with
SHA-256 `FB78AD4A5C23709E0EAB724D02F5DEB46E23A535D5AC63CC6E2B4DE54192972D`.
Both owned executions exited zero, and the build slot was explicitly released
to the parent for independent validation. No other Lean process was launched by
this owner during or after the slot.

A scoped scan of the new Lean source found no `sorry`, `admit`, `axiom`, `unsafe`,
`opaque`, `implemented_by`, `partial`, `extern`, `noncomputable`, Mathlib import,
`native_decide` or `Lean.ofReduceBool`. No-index `git diff --check` against the two
new owned files reported no whitespace errors; Git emitted its LF-to-CRLF working
copy notices, and exit one reflected the files' additions. The unchanged default
public roots do not import this module. Parent owns the final trust inventory,
full registry, broad checks, decision/public ledgers and exact-commit audit.

Conceptually, the lower-bound encoder now stores precisely the bits occupied
by PQ1's actual allocation. A reviewer can trace every decoded query back to
the recovered, counted numeric list. The generic information theorem measures
worst-case budget across shapes, while PQ1 supplies a uniform upper budget.
Live assumptions are the positive size-fixed width, bounded numeric words,
observed length, fixed per-size decoding, and PQ1's accepted explicit word-RAM
instruction model. The named downstream consumer is
`packedAllocationOptimality_holds`, then the parent's independent validation
capstone. A skeptical graduate student's next check is whether the typed
consumer truly pins the generic lower-bound dependency, exact decoder and
reconstructed execution together; the parent-owned mutations must answer it.
