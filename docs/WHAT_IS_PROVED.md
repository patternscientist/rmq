# What Is Proved

This document is the short scope map for external readers. It separates the
mathematical statements, modeled complexity claims, payload accounting, and
non-claims about executable Lean runtime.

## Headline Surfaces

The short public theorem aliases live in `RMQ/Headlines.lean`.

| Alias | Meaning |
| --- | --- |
| `RMQ.Headlines.exactRMQLowerBoundDoubledCatalanSlack` | Tight fixed-length RMQ payload lower bound with doubled Catalan slack. |
| `RMQ.Headlines.rankSelectNPlusOConstantQuery` | Standalone plain-bitvector Jacobson/Clark rank/select family with `n + o(n)` payload and constant modeled query cost. |
| `RMQ.Headlines.rankSelectWordBoundedNPlusOConstantQuery` | The same public rank/select family, strengthened with machine-word-bounded concrete payload reads. |
| `RMQ.Headlines.succinctRMQTwoNPlusOConstantQuery` | BP-native succinct RMQ capstone with exact queries, `2*n + o(n)` payload bits, constant modeled query cost, and the matching lower-bound side. |

The original theorem names remain construction-heavy so that their dependencies
and modeling choices are explicit. `RMQ.Headlines` only gives stable public
aliases.

## RMQ Correctness

The reference contract is a half-open, leftmost range-minimum query over
`List Int`. The project proves exactness for several RMQ backends, including:

- linear scan;
- sparse table;
- hybrid block RMQ;
- recursive hybrid RMQ;
- microtable/Cartesian-shape local queries;
- Fischer-Heun-style value-level structures; and
- the final succinct Cartesian-shape RMQ profile.

Correctness means the returned index is in range, its value is present in the
query window, it is no larger than every value in the window, and it is the
leftmost index satisfying that minimum property.

## RMQ And LCA

The project proves RMQ/LCA reductions over proof-friendly rose trees,
Euler-tour depth traces, Cartesian trees, and balanced-parentheses
representations. The plus-minus-one depth invariant of Euler tours is
formalized and used to connect LCA-style navigation to RMQ.

## Lower Bounds

The lower-bound layer proves information-theoretic statements for exact RMQ
state encodings from Cartesian-shape counting. The strongest public form is a
doubled integer statement equivalent to the coefficient-correct
`2n - 1.5 log n - O(1)` Catalan slack, avoiding rational arithmetic in the
public Lean statement.

These lower bounds are mathematical payload-capacity statements: any exact
decoder for all shapes of a size must have enough bitstrings to distinguish the
relevant Cartesian shapes.

## Succinct Upper Bound

The succinct capstone proves a modeled upper-bound profile for Cartesian-shape
RMQ:

- the base payload is the balanced-parentheses shape code of length `2*n`;
- auxiliary rank/select and BP close-navigation payload is `o(n)`;
- query exactness is proved against the same leftmost RMQ contract; and
- the modeled query cost is bounded by a fixed constant.

The theorem is payload-accounted: auxiliary bits are counted separately from
proof-only fields and certificates. The final path routes through payload-live
rank/select and close-navigation components rather than retired raw wrappers
that charged aggregate reference computations as one step.

## Standalone Rank/Select

`RMQRankSelect` exposes a reusable plain-bitvector rank/select spoke:

- stored-bit access;
- exact rank;
- exact select;
- counted payload length `n + overhead n`; and
- `LittleOLinear overhead` plus constant modeled query cost.

The public theorem is
`RMQ.RankSelect.jacobsonClarkNPlusOConstantQuery`.

The strengthened public profile
`RMQ.RankSelect.jacobsonClarkWordBoundedNPlusOConstantQuery` also exposes the
construction-level word discipline: concrete rank payload words erase to the
stored bitvector, and concrete rank/select payload-word reads are bounded by the
repository's machine-word-size function.

The compressed/FID target surface is also formalized:
`RMQ.RankSelect.fixedWeightBitstringsLength` counts fixed-weight bitvector
universes by a local binomial recurrence, and
`RMQ.RankSelect.fixedWeightCodecRoundTrip` /
`RMQ.RankSelect.fixedWeightDecodeEqSomeIff` prove the canonical finite-universe
rank/unrank facts. The total code
`RMQ.RankSelect.fixedWeightCode` is also proved to fit below
`2 ^ fixedWeightPayloadBudget bits`, and
`RMQ.RankSelect.fixedWeightPackedPayloadProfile` proves that the canonical code
is stored in exactly `fixedWeightPayloadBudget bits`, reads back through
`bitsToNatLE`, and decodes to the original bitvector.
`RMQ.RankSelect.fixedWeightPackedReadbackDirectoryProfile` is the first
charged non-oracular query consumer: it stores exactly that packed payload,
charges access/rank/select the full packed-payload readback cost, decodes, and
answers against the decoded reference bitvector. The bounded-word refinement
`RMQ.RankSelect.fixedWeightPackedReadbackDataOfChunksProfile` stores the same
payload in a `BoundedPayloadWordStore`, charges one modeled read per stored
word, and proves word-size-bounded readback. In addition,
`RMQ.RankSelect.compressedFixedWeightConstantQueryProfile` states the reusable
profile with payload
`log2 (binomialCount n m) + 1 + o(n)` and constant modeled
access/rank/select, while
`RMQ.RankSelect.fixedWeightCompressedAuxiliaryToCompressedFamilyProfile` is the
public adapter theorem for any future auxiliary family that supplies `o(n)`
overhead and constant bounded reads. This is not yet the full FID construction:
the remaining work is a concrete global auxiliary layer that avoids the
full-payload readback cost while still consuming charged payload rather than
proof-only decoded bits.
The pointwise `RMQ.RankSelect.fixedWeightDependentAuxiliaryDataProfile`
extends that surface to dependent auxiliary reads: the second read schedule may
depend on the charged packed-code read values, which is the shape needed by
RRR-style local block kernels.
The local `RMQ.RankSelect.fixedWeightTableRAMBlockDependentReadProfile`
checkpoint proves the block-level non-oracular spine: a charged packed-code
read, a decoded-word table read at that erased code, direct decoded access, and
fixed RAM rank/select primitives with constant modeled cost.
`RMQ.RankSelect.fixedWeightTableRAMBlockDependentAuxiliaryDataProfile`
packages the same local kernel through the generic dependent-read scaffold.
`RMQ.RankSelect.fixedWeightTableRAMBlockDependentAuxiliaryFullProfile` combines
that scaffold profile with the stronger local dependent-read facts and a bridge
showing the scaffold-backed directory agrees with the direct local block
directory on payload, costs, and erased answers.
`RMQ.RankSelect.fixedWeightComputedRRRBlockKernelProfile` is the stricter
packed-code-only local RRR checkpoint: it stores only the fixed-weight code
payload, spends an explicit computed-decoder budget, and then uses direct
access plus fixed RAM rank/select primitives.
`RMQ.RankSelect.fixedWeightComputedRRRBlockDependentAuxiliaryDataProfile`
packages that same kernel through the generic dependent-read scaffold with
zero auxiliary payload. This removes the local dense decoded-table payload, but
the decoder is still charged explicitly rather than proved globally O(1).
`RMQ.RankSelect.fixedWeightComputedRRRBlockBoundedCompressedDirectoryProfile`
is the local bounded-regime theorem: under the premise
`fixedWeightComputedRRRQueryCost bits <= queryCost`, the packed-code-only
kernel is a zero-auxiliary compressed/FID directory whose access/rank/select
costs are all bounded by `queryCost`.
`RMQ.RankSelect.fixedWeightComputedRRRBlockDependentAuxiliaryBridgeProfile`
and
`RMQ.RankSelect.fixedWeightComputedRRRBlockDependentAuxiliaryFullProfile`
show that the same local kernel is faithfully exposed through the generic
dependent-auxiliary scaffold: same payload, same query costs, and same erased
answers as the direct computed-RRR directory.
`RMQ.RankSelect.fixedWeightComputedRRRClassLengthBlockKernelProfile` proves the
local class/length-read RRR checkpoint: two charged fixed-width metadata words
recover the block length and class, a charged packed-code word supplies the
fixed-weight code, and access/rank/select are exact through direct decoded
access plus the RAM word primitives.
`RMQ.RankSelect.fixedWeightComputedRRRClassLengthBlockDependentAuxiliaryDataProfile`
packages that same local kernel through the dependent-read scaffold.
`RMQ.RankSelect.fixedWeightAmbientComputedRRRBlockCompositionProfile` consumes
that local adapter in the ambient block-composition layer: routed queries read
the charged block-code word, charge route/class metadata reads, invoke the
computed local RRR dependent-auxiliary evaluator, and satisfy the ambient
directory profile under an explicit route-plus-local query-cost discipline.
`RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteTableReadProfile`,
`RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteTableProfile`, and
`RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteTableFamilyProfile` add the
counted route/class metadata table envelope: a concrete auxiliary payload and
bounded word store, charged metadata reads whose erased values are the store
reads at each route schedule, an `o(n)` family overhead, and ambient query-cost
bounds.  `RMQ.RankSelect.fixedWeightAmbientComputedRRRDecodedMetadataReadProfile`
is the stricter decoded-metadata checkpoint: fixed decoders mapped over the
charged route-store reads recover the route fields consumed by the ambient
computed-RRR evaluator.  The decoded route-table profiles
`RMQ.RankSelect.fixedWeightAmbientComputedRRRDecodedRouteTableProfile` and
`RMQ.RankSelect.fixedWeightAmbientComputedRRRDecodedRouteTableFamilyProfile`
package this with the same counted route-payload envelope.
`RMQ.RankSelect.fixedWeightAmbientComputedRRRPackedAccessMetadataReadValuesEq`,
`RMQ.RankSelect.fixedWeightAmbientComputedRRRPackedRankMetadataReadValuesEq`,
and
`RMQ.RankSelect.fixedWeightAmbientComputedRRRPackedSelectMetadataReadValuesEq`
strengthen the route metadata checkpoint by showing that the charged route
reads return fixed-width `natToBitsLE` words for the route fields.
`RMQ.RankSelect.fixedWeightAmbientComputedRRRPackedRouteTableProfile` and
`RMQ.RankSelect.fixedWeightAmbientComputedRRRPackedRouteTableFamilyProfile`
carry that packed readback discipline through the same counted route-payload
envelope.
`RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteFieldTablesPackedProfile`
derives the same packed profile from a canonical fixed-width route-field table,
and
`RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteFieldTableLayoutPackedProfile`
does so from eight concatenated canonical fixed-width field tables.
`RMQ.RankSelect.fixedWeightAmbientComputedRRRClassLengthTableProfile` adds the
analogous concrete per-block length/class table: two fixed-width table
segments, a counted payload length
`RMQ.RankSelect.fixedWeightBlockClassLengthTablePayloadLength`, charged
readback for length/class words at a block index, and a local dependent-RRR
bridge for each addressed block.
`RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeProfile`
pairs the eight-table route layout with that class/length table, concatenates
both into one charged auxiliary store, and feeds the class/length read prefix
to the ambient class/length RRR evaluator through
`RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteClassLengthEnvelopeToClassLengthAmbientBlockCompositionData`.
`RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteFieldTableLayoutToRouteClassLengthTableEnvelopeProfile`
builds that envelope from an eight-table route layout under block-size and
local-cost side conditions.
`RMQ.RankSelect.fixedWeightRouteFieldTableLayoutPayloadLength`,
`RMQ.RankSelect.fixedWeightRouteFieldTableLayoutBoundedStoreWordsToList`, and
`RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteFieldTableLayoutOfCanonicalFixedWidthTables`
make the route layout store itself canonical rather than assuming the layout
word equation.
`RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamilyProfile`
adds the family-level combined route plus class/length `o(n)` accounting under
a supplied class/length-overhead budget, and
`RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeWordBoundedCompressedProfileOfPrimaryBudget`
carries that combined auxiliary budget into the conditional compressed/FID
primary-budget bridge.
`RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteFieldTableLayoutFamilyToRouteClassLengthTableEnvelopeFamilyProfile`
promotes an eight-table layout family to that combined envelope family, while
`RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteFieldTableLayoutFamilyToRouteClassLengthTableEnvelopeWordBoundedCompressedProfileOfPrimaryBudget`
pushes the promoted family through the conditional compressed/FID bridge.
`RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteFieldTableLayoutFixedBlockSizeRouteClassLengthTableEnvelopeFamilyProfile`
specializes that promotion to a uniform `blockSize`/`fieldWidth` family and
the class/length block-size query-cost budget.
`RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteFieldTableLayoutFixedBlockSizeWordBoundedCompressedProfileOfBlockBounds`
is the global compressed/FID budget bridge for that specialization: from a
block-count bound, a field-width bound, and a primary block-code budget, it
feeds `RMQ.RankSelect.fixedWeightBlockClassLengthTableOverheadLeBudget` and
returns the word-bounded compressed profile for the promoted route/class-length
envelope. `RMQ.RankSelect.fixedWeightChunkBlocksLengthLe` supplies the
concrete fixed-size chunk block-count bound
`blocks.length <= bits.length / blockSize + 1`, and
`RMQ.RankSelect.fixedWeightBlockClassLengthTableOverheadLeChunkBudget` feeds
that chunk bound into the class/length metadata budget. The route-total
sentinel variant
`RMQ.RankSelect.fixedWeightChunkBlocksWithSentinelLengthLe` proves the
`bits.length / blockSize + 2` bound after appending one empty fallback block,
and `RMQ.RankSelect.fixedWeightChunkBlocksWithSentinelGetSentinel` identifies
that fallback block for invalid-query routing.
`RMQ.RankSelect.fixedWeightChunkAccessRouteWithSentinel` closes the access
route-exactness leg for sentinel chunks: in-range accesses route to the
computed chunk, invalid accesses route to the sentinel, and
`RMQ.RankSelect.fixedWeightChunkBlocksGetAccessExact` proves the local
chunk-offset bit equation.
`RMQ.RankSelect.fixedWeightAmbientComputedRRRBlockSizeRouteTableFamilyProfile`
adds the ambient block-size route-table refinement: the local computed-RRR cost
premise is derived from a uniform block-length cap rather than assumed
per-block. The remaining global constructor task is to instantiate a concrete
charged route-directory family over the chunk blocks that proves the primary
block-code budget and derives the rank/select semantic route exactness fields
from charged routing tables.
The ambient/global fixed-weight block predecessor is also formalized:
`RMQ.RankSelect.fixedWeightAmbientBlockCompositionFamilyWordBoundedProfile`
proves an `o(n)` counted auxiliary envelope for block-composed fixed-weight
codes, with code and auxiliary payload words bounded by the ambient
`Nat.log2 bits.length + 1` word size. The bridge
`RMQ.RankSelect.fixedWeightAmbientBlockCompositionCompressedProfileOfPrimaryBudget`
isolates the remaining compressed/FID primary-budget theorem: the sum of
per-block fixed-weight code budgets must be bounded by the global
fixed-weight payload budget plus an `o(n)` slack.
`RMQ.RankSelect.fixedWeightAmbientBlockCompositionWordBoundedCompressedProfileOfPrimaryBudget`
is the strengthened version carrying the directory profile and ambient
machine-word bounds into that conditional compressed/FID shape.
The same conditional compressed/FID shape is exposed directly for the
ambient computed-RRR route layers by
`RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteTableWordBoundedCompressedProfileOfPrimaryBudget`
and
`RMQ.RankSelect.fixedWeightAmbientComputedRRRBlockSizeRouteTableWordBoundedCompressedProfileOfPrimaryBudget`
and
`RMQ.RankSelect.fixedWeightAmbientComputedRRRDecodedRouteTableWordBoundedCompressedProfileOfPrimaryBudget`;
the packed fixed-width route-word bridge is
`RMQ.RankSelect.fixedWeightAmbientComputedRRRPackedRouteTableWordBoundedCompressedProfileOfPrimaryBudget`.
The field-table constructor bridges are
`RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteFieldTablesWordBoundedCompressedProfileOfPrimaryBudget`
and
`RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteFieldTableLayoutWordBoundedCompressedProfileOfPrimaryBudget`.
These remain conditional on the primary block-code budget theorem.

## Balanced-Parentheses Navigation

`RMQBPNavigation` exposes the compact BP close/LCA layer used by the succinct
RMQ capstone. The public concrete profile is
`RMQ.BPNavigation.compactCloseDirectoryProfile`.

The public bridge theorem
`RMQ.BPNavigation.shapeAccessCloseRankProfile` proves the basic charged BP
tree-navigation legs: false-select maps an inorder node index to its closing
parenthesis, and false-rank at `close + 1` recovers the inorder index when the
close position is exact. The compact close profile proves `o(n)` auxiliary
close-navigation payload, constant modeled query cost, exact answer-close
semantics for Cartesian-shape RMQ queries supplied with exact endpoint close
positions, and machine-word-bounded payload reads. This is not yet a full
balanced-parentheses tree-navigation library; it is the RMQ-facing close/LCA
navigation spoke plus the first reusable close/rank bridge.

## Union-Find Scaffold

`RMQUnionFind` exposes the first non-succinct spoke. It proves a finite
partition-state specification, exact costed reference `find` and `union`
operations, and a reusable potential-method backend interface:
`RMQ.UnionFind.referenceBackend_profile` and
`RMQ.UnionFind.referenceAmortizedBackend_profile`.

This is infrastructure for the next structure, not the final theorem: the repo
does not yet contain a parent-pointer forest implementation, path compression,
union-by-rank, or the inverse-Ackermann amortized analysis.

## Cost Model

The complexity claims are not claims about Lean's native execution time.

They are theorems inside a simple model:

- `Costed` functions return a value and a natural-number cost.
- `RAM.Exec` traces small primitive operations and converts traces to
  `Costed`.
- Indexed table reads and bounded word primitives are charged as unit-cost
  operations under the documented RAM/indexed-access model.

This is the standard model used to state succinct-data-structure results, but
it is deliberately named so the theorem surface does not confuse model cost
with Lean's executable runtime.

## Non-Claims

The repository does not claim:

- that Lean `List` lookup is constant time;
- that every proof-support structure is executable production code;
- that the final theorem is a new data-structure bound;
- that the project is already a stable CSLib-style library API; or
- that the Mathlib-free policy is a permanent categorical ban.

The new contribution is the machine-checked connection of correctness,
reductions, lower bounds, payload accounting, and modeled succinct upper-bound
profiles for this RMQ family.
