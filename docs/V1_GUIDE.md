# RMQ V1 guide

Start here for the `1.0.0-rc.1` research artifact. The
[claims packet](../artifact/CLAIMS.md) is the claim-to-theorem map;
[FAMILY_SUMMARY](FAMILY_SUMMARY.md) holds the full inventory and
[CODE_MAP](CODE_MAP.md) explains the module structure.

## Contract and checked examples

An RMQ query on `xs : List Int` asks for the leftmost minimum index in the
nonempty half-open range `[left, right)`, with `right <= xs.length`.
[Spec.lean](../RMQ/Core/Spec.lean) defines `ValidRange` and `LeftmostArgMin` and
proves uniqueness. Value-level queries reject invalid ranges with `none`.

For `[4, 1, 1, 3]`, `[0, 4)` returns `some 1`: the two minima tie and index 1
comes first. `[2, 2)`, `[3, 1)` and `[0, 5)` are respectively empty, reversed
and out of bounds. All three return `none`. These are checked in
[V1Clients.lean](../RMQExamples/V1Clients.lean), which imports only
`RMQ.Headlines.RMQ`. `scanWindow` takes a length, so `scanWindow xs left len`
specifies the range `[left, left + len)`.

The [client guide](V1_CLIENTS.md) maps practical goals to existing named APIs:
packed-query halting and correctness, leftmost answers, eventual complete
capacity at most `3*n` bits, classic payload and trace-cost bounds, and reuse of the
supplied-store agreement theorem. Finite examples complement those universal
clients; they do not establish the asymptotic theorems.

## Models and accounting

| Bound | Counted execution or object | Boundary |
| --- | --- | --- |
| `210` | Canonical reviewer query's charged trace | Emitted trace length; every event is an attempted payload-word read, failures included. Controller arithmetic, branching and decoding are outside the event vocabulary. |
| `427` | Packed cell-probe controller | Attempted aligned probes; computation between probes is free. |
| `837,572` | Fixed loop-free primitive query program on per-input `buildMemory xs`; theorem `RMQ.Headlines.succinctRMQFullyChargedPackedQuery` | Every executed instruction costs one step; the upper budget is program length, not an attained maximum. |
| `151978` steps; `212964` instructions; `722339` encoded words | Compact query hosted by the lifecycle service | A dynamic upper bound and two distinct static code sizes. |
| `1100000000*(n+1)` transitions; `5000000*(n+1)` cells | Lifecycle construction through query entry | Primitive transitions and peak numeric arena cells; comparison-key storage is counted separately. |
| `160253` first service; `160257` later request | Lifecycle service on the retained owner | Header read and full bank initialization; later requests add four admission/control events. |
| `2*n + overhead n` bits | Logical reference payload | Its bit list; proof fields and certificates are excluded. |
| `2n + o(n)` bits | Complete packed numeric capacity | Full-width allocated memory, encoded code, registers and control words, including padding. |
| `2*n + retainedRho n` bits | Lifecycle retained numeric owner | Memory, code and finite banks after construction; not peak workspace. |
| `2n - 1.5 log n - O(1)` bits | Fixed-length payload-only exact RMQ encoding | Information-theoretic bound; no fast-decoder premise. |

The word model assumes unit-cost multiplication, division, remainder, variable
shifts and bitwise operations on logarithmic-width words. The primitive-query
proof establishes operation safety, rather than silently wrapping mathematical
naturals. The outer check for endpoints outside the word domain is uncharged.
The fixed code/register cost becomes lower order only asymptotically; it can
dominate storage on moderate inputs. None of these figures measures elapsed time.

Lifecycle comparison input permits arbitrary integers with separate key banks;
word input requires the signed input-fit predicate. Input materialization
precedes the modeled run. An invalid represented lifecycle request still reads
the retained header, unlike the compact guarded query suffix's empty read trace.

## Source tour

- Reference: [Spec](../RMQ/Core/Spec.lean), [Window](../RMQ/Core/Window.lean).
- Existing backend substitution: [Backend](../RMQ/Core/Backend.lean), consumed by
  [Equivalence](../RMQ/Impl/Equivalence.lean).
- Succinct construction: [SuccinctFinal](../RMQ/Core/SuccinctFinal.lean);
  ordinary-list interface: [SuccinctRMQClassic](../RMQ/Core/SuccinctRMQClassic.lean).
- Store refinement: [SuccinctFinalStoreParam](../RMQ/Core/SuccinctFinalStoreParam.lean).
- Lower bound: [EncodingLowerBound](../RMQ/Core/EncodingLowerBound.lean).
- Primitive semantics and contract: [Primitive](../RMQ/Core/WordRAM/Packed/Primitive.lean),
  [Capstone](../RMQ/Core/WordRAM/Packed/Capstone.lean).
- Construction and reusable owner: [lifecycle capstone](../RMQ/Core/WordRAM/Lifecycle/Capstone.lean),
  [independent client](../RMQ/Validation/LifecycleContract.lean),
  [worked proof guide](digests/LIFECYCLE_PROOF_GUIDE.md).

The narrow `RMQPaper` root contains query theorems. The lifecycle headline is an
additive import through `RMQ.Headlines.Lifecycle` and the broad `RMQ` root.
The [manuscript source note](../paper/V1_SOURCE_RELATION.md) explains its older
query-theorem pin and the candidate's relationship to it.

## Reproduction

With the toolchain pinned by `lean-toolchain`, run this smoke check from the
repository root, or from an unpacked source bundle:

```powershell
lake build RMQPaper RMQExamples.V1Clients
rg -n "\b(sorry|admit|axiom|unsafe|opaque|implemented_by|partial|extern|noncomputable)\b|import Mathlib" RMQ RMQExamples RMQPaper.lean lakefile.toml
```

The scan should find no matches (ripgrep exits 1 for no matches). A successful
build alone does not establish this source-hygiene claim. The headline axiom
inventory imports the broad `RMQ` root and belongs to the full path below.

For the additive lifecycle client and trust inventory:

```powershell
lake build RMQ.Headlines.Lifecycle RMQ.Validation.LifecycleContract RMQ.Core.WordRAM.Lifecycle.Controls RMQ.Core.WordRAM.Lifecycle.Provenance
lake env lean scripts/lifecycle_inventory.lean
lake env lean scripts/lifecycle_provenance_contract.lean
```

Full reproduction requires a clean Git checkout with the historical objects
used by mutation controls, plus Bash, PowerShell (`pwsh`) and ripgrep:

```bash
bash scripts/reproduce_artifact.sh
```

This includes `scripts/gate.ps1`, public roots, validators, trust inventories
and the committed mutation campaigns. A skipped gate is incomplete verification.
The script emits per-section `TIMING:` lines; measured durations describe the
verification host, not algorithmic performance. See
[ARTIFACT_REPRODUCIBILITY](ARTIFACT_REPRODUCIBILITY.md) for the detailed path.

The native supplement has separate [build and ownership instructions](../native/packed-rmq/README.md).
Formal image codecs, encoded-code backing and byte-limb refinements are proved;
general compiler correctness, C/Rust FFI discipline and allocator realization
remain assumptions. Logical retained capacity does not bound native RSS or
copying time. Lifecycle evidence status and current follow-ups are recorded in
the claims packet; merging alone is not acceptance.
