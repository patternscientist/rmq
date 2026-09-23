# LB-1 contract and source feasibility

Status: contract frozen; implementation and independent route review pending.

Handle/title: LB-1 / (LB-1) Match lower bound to packed allocation.
Branch: codex/lb-1-variable-payload.
Worktree: C:/Users/poin/.codex/worktrees/2270/RMQ.
Base and governance: 0e6a00f654abc64f8b68988fa9675b9a839dca2f.

## Generic interface, pinned before proof implementation

```lean
structure RMQ.ExactRMQBoundedEncoding (n B : Nat) where
  encode : List Int -> List Bool
  query : List Bool -> Nat -> Nat -> Option Nat
  length_le : forall xs, xs.length = n -> (encode xs).length <= B
  query_exact : forall xs, xs.length = n ->
    forall left len, 0 < len -> left + len <= n ->
      query (encode xs) left (left + len) = some (RMQ.scanWindow xs left len)
```

The decoder is fixed across every size-n input. Its only varying arguments are
the payload and endpoints; n and n-only fixed advice may be captured once. There
is no supplied shape, original input, answer, or proof argument on its executable
path. The bound concerns all inputs of length n, not every input separately.

Required derived types in namespace RMQ.ExactRMQBoundedEncoding:

```lean
shapeCount_le (E : ExactRMQBoundedEncoding n B) :
  Cartesian.shapeCount n <= 2^(B+1)-1
doubledLogSlackLower_le (E : ExactRMQBoundedEncoding n B) :
  EncodingLowerBound.doubledLogSlackLower n <= 2*(B+1)
```

The canonical representative map is `fun s => E.encode s.representative`.
Its injectivity on `Cartesian.shapesOfSize n` is derived from equal answers on
all valid half-open windows, via `Cartesian.shape_eq_of_sameRMQBehavior`, not
assumed as a record field. `boundedBitStrings B` enumerates all lengths 0..B;
its length is exactly `2^(B+1)-1`. Source `shapesOfSize_nodup` and
`LowerBound.length_le_of_nodup_injective_into` give the cardinal inequality.
`EncodingLowerBound.shapeCount_cubic_square_lower` and
`LowerBound.two_mul_bits_lower_of_cubic_square_bound` at bits=B+1 give the
coefficient-correct doubled lower bound, without any fixed-length coercion.

## Canonical adapter and join

`serializeWords width words := (words.map (SuccinctSpace.natToBitsLE width)).flatten`.
Its length is exactly `words.length * width`. For width>0, reconstruct each
word from the width-bit slice indexed by `List.range (bits.length / width)`.
`uniform_flatten_slice` and `bitsToNatLE_natToBitsLE_of_lt` prove the left
inverse on every finite list with entries below `2^width`. Consequently zero
words of different counts remain distinct by bitstring length; no padding to a
uniform B is introduced.

The actual payload is `serializeWords (wordWidth xs.length) (buildMemory xs)`.
The decoder accepts n, bits and endpoints, reconstructs numeric words at
`wordWidth n`, and calls existing `queryNat memory n left right`.
The round trip identifies that memory with `buildMemory xs` exactly.
`queryNat_exact`, `buildMemory_words_fit`, `buildMemory_capacity_le` and
`allocationRho_littleO` supply the canonical bounded instance at `2*n+allocationRho n`.
An arbitrary uniform budget B on actual allocation yields another instance,
therefore `doubledLogSlackLower n <= 2*(B+1)`.

`packedAllocationOptimality_holds` must consume that instance, its actual-memory
round trip, shape injectivity, exact decoding and two-sided budget statement.
A separately typed consumer pins every advertised mandatory field. PQ1's
existing machine capstone is consumed at that identical reconstructed memory;
its physical store, word width, instruction and scratch facts are not inferred
from mere serialization. Mathematical bit serialization/deserialization gains
no charged machine-time claim. Fixed query code and finite scratch retain PQ1's
separate complete-capacity theorem; external n/advice is explicitly fixed per n.

## Scope, phase order and controls

The entire assigned extension remains the endpoint. Read-only source inventories
run in parallel with this contract freeze. Independent contract/route review
precedes adapter implementation; generic counting implementation may proceed
after this exact signature is frozen. The PRE-specific mandatory builder gate
does not assign a PRE builder to LB-1. No route choice depends on evidence that
has not yet been produced.

The existing fixed-length encoding and public RMQPaper/Headlines identities are
unchanged. No native format, cell-probe tradeoff, per-input near-2n claim, query
algorithm change, paper rewrite, integration, push, branch deletion or cleanup
is assigned. Only the coordinator records acceptance.

Required controls target these same exact propositions: empty and singleton
domains; equal-key leftmost answers; empty string versus zero words; null and
wrong decoder; deleted or weakened exactness/public fields; n-only advice
accepted uniformly; input/shape-dependent advice excluded by the exact decoder
type. Registry and selector checks cover omissions and empty selection. Mutated
source bytes restore in finally and are hash-checked. A control not executed on
this host is uncovered, never passed.

## Verification coverage plan

Development checks build only owned modules and direct consumers, one job and
one owned process per tree, using the task-local cache. Command evidence records
platform, exact tree, covered rows, deadline, duration, exit, output and ownership.
A targeted toolchain/dependency startup check precedes proof builds. Startup and
one known selector precede the full registry. No unchanged timeout is retried.

Final required: explicit owned module/consumer imports, lane full registry,
axiom inventory, trust scans, diff checks for working tree and base..HEAD, strict
design check with exact base. Public family/digestion appendices require strict
claim drift. `lake build` and aggregate certification await a coordinator host
slot on frozen content; this task will request that slot without running a
competing full build. Existing compatibility tests are conditional on behavior
changes. POSIX process ownership is uncovered unless separately executed.

Real stop conditions: full candidate closure; a matching formal obstruction;
required unavailable external state; explicit user/coordinator redirect. A
partial proof, successful build or difficulty is only a checkpoint.

## Route-review clarification (requirements unchanged)

The generic function type alone cannot prohibit a programmer from closing over
an arbitrary constant. Its semantic safeguard is one decoder fixed across all
size-n inputs and exact on every valid window. The canonical adapter is visibly
`allocationDecoder n bits left right`, with no captured input or shape. The
advice controls negate uniform size-two exactness of a fixed input/shape-based
answer oracle with an empty payload, using the same quantifiers as query_exact.
They do not claim that a function signature can inspect closure contents.
