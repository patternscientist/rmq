# Verified Range-Minimum Query

[![CI](https://github.com/patternscientist/rmq/actions/workflows/ci.yml/badge.svg)](https://github.com/patternscientist/rmq/actions/workflows/ci.yml)

Range-minimum query (RMQ) asks for the leftmost position of the smallest value
in a subarray. The classical surprise is that the values can be discarded: the
Cartesian shape alone determines every answer. This repository machine-checks
that story in Lean 4 -- correctness, payload-bit accounting, modeled query cost,
and a matching information-theoretic lower bound -- with explicit Lean definitions for the
mathematical models and separate statements of runtime assumptions.

**Start here:** [`docs/V1_GUIDE.md`](docs/V1_GUIDE.md) gives a worked half-open
leftmost-tie example, a model-and-cost comparison table, a source-to-consumer
tour, and the smoke versus full reproduction commands.

This tree is the **V1 release candidate `1.0.0-rc.1`**: a research artifact
prepared for review; it has not been published as a release. It is
Mathlib-free -- Lean 4 with `Std` plus `omega`, pinned by `lean-toolchain` to
`leanprover/lean4:v4.22.0` -- with no `sorry`, custom `axiom`, `unsafe`,
`partial`, or `noncomputable` definitions in the checked source.

## The Reference Contract

Value-level RMQ queries share one contract
([`RMQ/Core/Spec.lean`](RMQ/Core/Spec.lean)): inputs are ordinary
`xs : List Int`, a valid query is a nonempty half-open window `[left, right)`
inside the list, and the answer is the *leftmost* index attaining the minimum.
`RMQ.LeftmostArgMin` states it, `RMQ.leftmostArgMin_unique` proves the witness
unique, and invalid or empty windows return `none`.

## Headline Results

| Result | Public alias, available from `import RMQPaper` |
| --- | --- |
| Succinct upper bound: `SuccinctClassic.buildPayload` has length at most `2*n + overhead n` with `overhead` proved `o(n)`; valid windows return the exact leftmost minimum, invalid or empty windows return `none`, and modeled query cost is bounded by a fixed constant. | `RMQ.Headlines.succinctRMQListIntTwoNPlusOConstantQuery` |
| Payload lower bound: every fixed-length, payload-only exact RMQ encoding needs `2n - 1.5 log n - O(1)` bits, stated in doubled integer form over Cartesian-shape counting. | `RMQ.Headlines.exactRMQLowerBoundDoubledCatalanSlack` |
| Validity boundary: one guard rejects empty, reversed and out-of-bounds windows, with specialized aliases exported beside it. | `RMQ.Headlines.listIntSuccinctRMQQueryCostedInvalid` |

**Primitive-machine query (accepted).** Preprocessing builds one numeric memory
per input, `PackedWordRAM.buildMemory xs`. The closed loop-free program of
837,572 primitive instructions is fixed for every list and every size. Running
that program on that memory answers every representable endpoint pair: valid
windows return the leftmost minimum, representable invalid windows return the
rejection packet `0` with no memory reads, the run halts within at most 837,572 steps -- which is
simply the program length, with no tightness claimed -- every stored word,
operand and prefix state stays inside one logarithmic word width, and the
memory, literal program encoding, 8,271-register bank and three control words
fit in `2n + o(n)` bits of allocated word capacity.
Each executed instruction costs one step; unit-cost multiplication, division,
remainder, variable shifts and bitwise word operations are model assumptions,
and every executed operation is proved free of overflow, underflow, zero
division and oversized shifts. Alias
`RMQ.Headlines.succinctRMQFullyChargedPackedQuery`; status **ACCEPTED**, with
the [coordinator record](docs/internal/packed_query/PQ1_COORDINATOR_ACCEPTANCE.md)
and the [machine review packet](docs/WORD_RAM_REVIEW_PACKET.md). The fixed
code/register term can dominate moderate inputs; its lower-order bound is
asymptotic, not a practical memory recommendation.

**Continuous lifecycle (merged; coordinator acceptance still open).** A
separate fixed program per input model joins the builder body, metadata and
request transfer, retirement and a first query into one continuous run, then
serves further requests from the retained owner. Construction through query
entry takes at most `1100000000 * (n + 1)` primitive transitions and owns at
most `5000000 * (n + 1)` numeric arena cells at every prefix; arbitrary-Int
comparison input has separately counted key cells and registers; the first service
takes at most 160253 further transitions and each later request at most 160257;
retained numeric capacity is at most `2*n + retainedRho n` bits with `retainedRho`
proved `o(n)`, which is a different quantity from the peak construction
workspace. Alias `RMQ.Headlines.succinctRMQContinuousLifecycle`, reachable from
`import RMQ` but deliberately not from `RMQPaper`. The source, its independent
frozen client propositions and its integration audits are in place; acceptance
remains open pending the V1 evidence reconciliation, so this is not presented
as an accepted result beside the packed query above.

Also checked, outside the paper root: RMQ/LCA reductions over rose trees, Euler
tours, Cartesian trees and balanced parentheses; a standalone rank/select spoke
(`RMQ.Headlines.rankSelectNPlusOConstantQuery`); a BP close-navigation spoke
(`RMQ.Headlines.concreteBPCloseNavigationProfile`); and a union-find spoke that
is still short of the Tarjan bound.

## Model Scope

Cost statements are model-relative, and the models differ. The current
charged-trace cap is `210` on the canonical reviewer query: modeled cost is
the emitted trace length, and
`RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultReadWordOnly` proves
every emitted event is a payload-word read, failed reads included. Controller
dispatch, decoding, arithmetic, branching, local scanning and the validity
guard are outside this event vocabulary. The packed cell-probe bound of `427` counts attempted aligned
`w(n)`-bit probes and treats computation between probes as free. The accepted
primitive-machine theorem above instead charges every executed instruction of
its own register machine. Three executions, three charge policies; none of them
is a wall-clock or compiled-code statement.

Space statements exclude proof-only fields and certificates. The reference
payload counts its bit list; complete packed capacity counts every allocated
word at its full width, including padding, plus encoded code and registers.

**Preprocessing.** The query theorems above bound queries only: none of them
bounds the work or space needed to build the payload. The lifecycle theorem is
the one surface that does bound construction, inside its own model and with the
constants quoted above, and input materialization precedes its modeled run.
The repository also proves image-codec and byte-limb refinements. General
compiler correctness, FFI discipline and native allocator realization remain
assumptions; modeled capacity does not bound native copying time or RSS.

## Build And Verify

Install the toolchain named in `lean-toolchain`, then check the paper root and
the worked clients:

```powershell
lake build RMQPaper RMQExamples.V1Clients
```

The [V1 guide](docs/V1_GUIDE.md#reproduction) separates this smoke build from
the complete repository gate, lifecycle checks and native supplement. Full
reproduction needs a clean Git checkout with the historical objects used by
mutation controls. The source bundle includes the pinned toolchain name,
manuscript and a per-file hash manifest; it is not a precompiled library.
