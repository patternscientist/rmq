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
| `RMQ.Headlines.rankSelectCompressedFIDFixedWeightFamilyProfile` | Fixed-weight compressed/FID rank/select family: fixed-weight primary payload plus `o(n)` auxiliary payload, exact access/rank/select, and one constant modeled query bound. |
| `RMQ.Headlines.rankSelectCompressedFIDFixedWeightInterpretedFamilyProfile` | Interpreter-backed replay of that compressed/FID rank/select family: same payload/profile shape, with access/rank/select reads routed through first-order `WordRAM` bridges. |
| `RMQ.Headlines.rankSelectCompressedFIDFixedWeightGlobalPayloadStoreFusedProfile` | Fused fixed-weight compressed/FID rank/select capstone: compressed payload plus `o(n)`, exact constant-query access/rank/select, interpreted replay, one target-independent global payload store, and bounded trace-local event widths. |
| `RMQ.Headlines.rankSelectCompressedFIDFixedWeightGlobalPayloadStoreExecutionStory` | Target-independent global-store execution story for compressed/FID rank/select: for fixed `bits`, shared access plus rank false/true and select false/true traces all read from one concrete payload store. |
| `RMQ.Headlines.rankSelectCompressedFIDFixedWeightGlobalPayloadStoreBoundedExecutionStory` | Bounded target-independent global-store execution story for compressed/FID rank/select: the combined traces also have finite trace-local widths bounding every payload-read address and word-primitive natural operand/result. |
| `RMQ.Headlines.rankSelectCompressedFIDFixedWeightTargetGlobalPayloadStoreExecutionStory` | Lower-level target-indexed global-store execution packet for one fixed rank/select target. |
| `RMQ.Headlines.rankSelectCompressedFIDFixedWeightTargetGlobalPayloadStoreBoundedExecutionStory` | Lower-level bounded target-indexed global-store packet for one fixed rank/select target. |
| `RMQ.Headlines.succinctRMQListIntTwoNPlusOConstantQuery` | Classic list-facing succinct RMQ theorem: for every ordinary `xs : List Int`, the built payload has length `2*n + o(n)` and valid half-open queries return the exact leftmost RMQ answer within constant modeled query cost. |
| `RMQ.Headlines.listIntSuccinctRMQFlatPayloadStoreNoSyntheticExecutionStory` | List-facing flat-payload no-synthetic execution story: for ordinary `xs : List Int`, the final query keeps the classic half-open leftmost RMQ contract and constant modeled query bound while its WordRAM trace reads from one query-independent flat payload layout with backed reads, bounded event data, and no synthetic cost-only markers. |
| `RMQ.Headlines.succinctRMQTwoNPlusOConstantQuery` | BP-native succinct RMQ capstone with exact queries, `2*n + o(n)` payload bits, constant modeled query cost, paired with the separately proved encoding-quantified lower bound. |
| `RMQ.Headlines.succinctRMQTwoNPlusOConstantQueryInterpreted` | Whole-query-interpreted variant of the final BP-native succinct RMQ capstone: same theorem shape, with the final query control represented by a closed first-order program whose leaves are interpreted close-select, compact close/LCA, and register-backed answer-rank operations. |
| `RMQ.Headlines.succinctRMQTwoNPlusOConstantQueryLeafTrace` | Leaf-trace-preserving variant of the same capstone: the closed controller now evaluates to an explicit domain-leaf trace before projection back to `Costed`; the leaves are still interpreted component queries, not one unified store trace. |
| `RMQ.Headlines.succinctRMQTwoNPlusOConstantQueryWordTrace` | Unified-`WordRAM.TraceEvent` variant of the same capstone: the final query emits one trace stream; close-select, answer-rank, compact-close rank-seed reads, the finite-small same-block close fallback, and the all-size relative-rmM interior query are structural payload/register traces. |
| `RMQ.Headlines.succinctRMQTwoNPlusOConstantQueryWordTraceLargeRegime` | Large-regime WordRAM variant: the same two-sided theorem shape with an explicit size premise that lets the compact close/LCA query replay local/fringe/interior close navigation structurally instead of using the all-size fallback. |
| `RMQ.Headlines.succinctRMQGlobalPayloadStoreExecutionStory` | All-size final-query execution story: the public costed query refines one globally segmented `WordRAM.TraceEvent` stream, every event is a payload read or bounded word primitive, and every read agrees with one concrete payload store. |
| `RMQ.Headlines.succinctRMQGlobalPayloadStoreExtensionalExecutionStory` | Store-extensional all-size execution story: any read store agreeing with the concrete global store on emitted payload-read events validates the same final-query trace. |
| `RMQ.Headlines.succinctRMQGlobalPayloadStoreBoundedExecutionStory` | Bounded all-size execution story: the global trace also has a finite trace-local bit width bounding every payload-read address and every natural operand/result exposed by word primitives. |
| `RMQ.Headlines.succinctRMQGlobalPayloadStoreAllSizeStructuralExecutionStory` | All-size structural execution story for the same global trace after the zero-block same-block and cross-block interior close-navigation `TraceResult.ofCosted` leaves have been replaced by payload-backed structural traces. |
| `RMQ.Headlines.succinctRMQGlobalPayloadStoreNoSyntheticExecutionStory` | Strongest all-size global execution story: the same store-backed and bounded trace plus a proof that no event is the dedicated synthetic cost-only marker. |
| `RMQ.Headlines.succinctRMQFlatPayloadStoreNoSyntheticExecutionStory` | Flat-payload no-synthetic execution story: the final trace reads from one query-independent flat payload layout, successful reads have component/offset backing evidence, addresses and word-primitive operands are bounded, and no synthetic cost-only event occurs. |
| `RMQ.Headlines.succinctRMQLargeRegimeGlobalPayloadStoreExecutionStory` | Large-regime companion to the all-size execution story: under `2^128 <= shape.size`, the compact close/LCA leg uses the positive-block structural replay rather than the all-size fallback. |
| `RMQ.Headlines.succinctRMQLargeRegimeGlobalPayloadStoreBoundedExecutionStory` | Bounded large-regime companion to the global-store execution story. |
| `RMQ.Headlines.bpCloseNavigationInterpretedTwoNPlusOConstantQuery` | Conditional component-level interpreter-backed BP close-navigation profile, parameterized by a supplied word-bounded sampled encoded close-navigation family. |

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

The succinct capstone now has both a construction-facing Cartesian-shape theorem
and a reader-facing ordinary-list theorem.  The list-facing surface is
`RMQ.Headlines.succinctRMQListIntTwoNPlusOConstantQuery`: for every
`xs : List Int`, it builds a counted payload of length
`2 * xs.length + overhead xs.length`, proves `overhead = o(n)`, and answers
valid half-open queries with the exact leftmost RMQ index of `xs` under a fixed
modeled query-cost bound.  The strengthened list-facing execution surface
`RMQ.Headlines.listIntSuccinctRMQFlatPayloadStoreNoSyntheticExecutionStory`
keeps those clauses and additionally consumes the final flat-payload
no-synthetic WordRAM story for the Cartesian shape of `xs`.  The construction-facing theorem proves the same
profile over Cartesian-shape representatives:

- the base payload is the balanced-parentheses shape code of length `2*n`;
- auxiliary rank/select and BP close-navigation payload is `o(n)`;
- query exactness is proved against the same leftmost RMQ contract; and
- the modeled query cost is bounded by a fixed constant.

The theorem is payload-accounted: auxiliary bits are counted separately from
proof-only fields and certificates. The final path routes through payload-live
rank/select and close-navigation components rather than retired raw wrappers
that charged aggregate reference computations as one step.

The global-store execution story now has a flat-payload no-synthetic backing
theorem, `RMQ.Headlines.succinctRMQFlatPayloadStoreNoSyntheticExecutionStory`.
It exposes the
concrete flat payload layout
`SuccinctFinal.concreteBPNativeSuccinctRMQFlatPayloadLayout`, whose payload is
the counted `concreteBPNativeSuccinctRMQPayload` plus the finite-small
same-block structural table needed by the all-size no-synthetic replay, split
as BP code, final rank/access payload, generic sparse-exception select payload,
padding, compact close/LCA payload, and finite-small structural payload. The
theorem ties the final query trace to this flat store, proves successful reads
carry explicit source/component offsets, and packages the bounded/no-synthetic
execution story in the same statement. The BP-code alias maps back to the
existing BP-code component; it is not a second counted copy.

The strongest interpreter-backed query surface is now
`RMQ.Headlines.succinctRMQTwoNPlusOConstantQueryWordTrace`, an additive variant
of the final BP-native succinct RMQ capstone. It keeps the same two-sided
lower/upper theorem shape as
`RMQ.Headlines.succinctRMQTwoNPlusOConstantQuery`, while routing the final query
control through a closed instruction list over optional/natural registers and
preserving one `WordRAM.TraceEvent` stream. The answer-rank leaf is a concrete
register-program trace: once the dynamic `answerClose + 1` position is supplied
in a register, the super-sample, block-sample, and bit-word addresses are
computed inside first-order syntax. The WordRAM/register layer now also exposes
bounded-address and no-overflow predicates: arithmetic is mathematical `Nat`,
and machine-word address safety is an explicit proof obligation rather than a
silent wraparound policy. The sparse-exception close-select leg is
structural too, and the compact close/LCA leg now exposes its rank-seed reads
structurally. The all-size compact close/LCA leg now also replaces the former
`TraceResult.ofCosted` boundaries with payload-backed traces:
`SuccinctClose.ConcreteCompactBPCloseLCADirectory.lcaCloseTraceResultWithRankSeedAllSizeStructural`
and
`SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTrace_noSynthetic_execution_story`
are the concrete theorem anchors. `TraceResult.ofCosted` now emits a dedicated
`TraceEvent.syntheticCostOnlyPrimitive` constructor, separate from real
`wordRank`/`wordSelect` primitives, and the no-synthetic final theorem proves
that constructor is absent from the all-size global query trace.
The component-level
`RMQ.Headlines.bpCloseNavigationInterpretedTwoNPlusOConstantQuery` remains
available as the reusable BP close-navigation profile, but it is conditional:
the theorem consumes a supplied word-bounded sampled encoded close-navigation
family rather than constructing that family in the public BP-navigation spoke.

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

The fixed-weight compressed/FID capstone is now exposed as the family theorem
`RMQ.RankSelect.compressedFIDFixedWeightFamilyProfile`, with headline alias
`RMQ.Headlines.rankSelectCompressedFIDFixedWeightFamilyProfile`. For every
`bits : List Bool`, the family counts the enumerative fixed-weight primary
payload plus `o(n)` auxiliary payload and proves exact access, rank, and select
under one uniform modeled constant query bound. The pointwise theorem
`RMQ.RankSelect.compressedFIDFixedWeightConstantQueryProfile` remains available
for the individual directory. This is still a model-level theorem, not a claim
about Lean's runtime representation.

The additive interpreted replay theorem
`RMQ.RankSelect.compressedFIDFixedWeightInterpretedFamilyProfile`, with
headline alias
`RMQ.Headlines.rankSelectCompressedFIDFixedWeightInterpretedFamilyProfile`,
keeps the same compressed payload and constant-query theorem shape but routes
the access, rank, and select reads through the repository's first-order
`WordRAM` bridge layer. This sharpens the non-oracle story for the standalone
rank/select spoke; it is still a word-RAM model theorem, not a Lean runtime
claim or a single closed machine-code program.

The trace-level surface now includes
`RMQ.RankSelect.compressedFIDFixedWeightAccessTraceResult_execution_story`,
`RMQ.RankSelect.compressedFIDFixedWeightRankTraceResult_execution_story`, and
`RMQ.RankSelect.compressedFIDFixedWeightSelectTraceResult_execution_story`.
These prove that each query trace projects to the interpreted query, refines
the costed query, contains only payload-read or word-primitive events, and
matches a concrete segmented read store.  The combined theorem
`RMQ.RankSelect.compressedFIDFixedWeightGlobalPayloadStore_execution_story`
relabels shared access plus rank false/true and select false/true packets into
one target-independent global store for each fixed `bits`.  The bounded
companion
`RMQ.RankSelect.compressedFIDFixedWeightGlobalPayloadStore_bounded_execution_story`
adds the RMQ-style finite trace-local bit-width theorem for payload-read
addresses and word-local primitive operands/results.  The earlier
target-indexed store theorem remains available as a lower-level packet, while
the remaining width story is trace-local rather than a uniform asymptotic
machine-word theorem.

The compact public citation for this whole compressed/FID stack is now
`RMQ.RankSelect.compressedFIDFixedWeightGlobalPayloadStoreFusedProfile`, with
headline alias
`RMQ.Headlines.rankSelectCompressedFIDFixedWeightGlobalPayloadStoreFusedProfile`.
It conjoins the family payload/cost/exactness theorem, the interpreted replay
theorem, the target-independent global payload-store theorem, and the bounded
trace-local event-width theorem in one public surface.

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
public adapter theorem for any auxiliary family that supplies `o(n)` overhead
and constant bounded reads. This scaffold is now consumed by the concrete
sub-log/Packed-Clark family theorem
`RMQ.RankSelect.compressedFIDFixedWeightFamilyProfile`; the interpreted replay
surface `RMQ.RankSelect.compressedFIDFixedWeightInterpretedFamilyProfile` now
routes those concrete access/rank/select reads through the first-order
Word-RAM bridge layer.
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
The sentinel chunk route-exactness layer now covers rank and select as well:
`RMQ.RankSelect.fixedWeightChunkBlocksGetRankPrefixAddExact` proves the
additive rank-prefix equation for the routed chunk, and
`RMQ.RankSelect.fixedWeightChunkRankRouteWithSentinel` packages the total rank
route.  `RMQ.RankSelect.fixedWeightChunkBlocksGetSelectExactOfGlobalSelect`
localizes a successful global select to the selected chunk, and
`RMQ.RankSelect.fixedWeightChunkSelectRouteWithSentinel` packages the total
select route, sending missing selects to the empty sentinel.
The log-sized chunk-count budget is also formalized:
`RMQ.RankSelect.fixedWeightLogChunkBlockCountBoundLittleO` and
`RMQ.RankSelect.fixedWeightLogChunkBlockCountBoundWithSentinelLittleO` prove
the `o(n)` block-count side for `n / (log n + 1) + O(1)` chunks, with matching
length bounds from `RMQ.RankSelect.fixedWeightLogChunkBlocksLengthLe` and
`RMQ.RankSelect.fixedWeightLogChunkBlocksWithSentinelLengthLe`. The narrow
class/length side is now proved too:
`RMQ.RankSelect.fixedWeightLogChunkClassLengthOverheadLittleO` is an `o(n)`
budget, and
`RMQ.RankSelect.fixedWeightLogChunkBlockClassLengthTableOverheadLe` places the
sentinel log-chunk class/length table under it. Conversely,
`RMQ.RankSelect.fixedWeightLogChunkRouteWidthClassLengthOverheadNotLittleO`
formalizes that route-width-padded class/length fields are not a compressed
auxiliary budget.
`RMQ.RankSelect.fixedWeightAmbientComputedRRRBlockSizeRouteTableFamilyProfile`
adds the ambient block-size route-table refinement: the local computed-RRR cost
premise is derived from a uniform block-length cap rather than assumed
per-block. The later sub-log/Packed-Clark route construction closes the public
compressed/FID family surface; these ambient route-table theorems remain as
reusable lower-level components and historical design boundaries.
The ambient/global fixed-weight block predecessor is also formalized:
`RMQ.RankSelect.fixedWeightAmbientBlockCompositionFamilyWordBoundedProfile`
proves an `o(n)` counted auxiliary envelope for block-composed fixed-weight
codes, with code and auxiliary payload words bounded by the ambient
`Nat.log2 bits.length + 1` word size. The bridge
`RMQ.RankSelect.fixedWeightAmbientBlockCompositionCompressedProfileOfPrimaryBudget`
isolates the generic compressed/FID primary-budget theorem: the sum of
per-block fixed-weight code budgets must be bounded by the global
fixed-weight payload budget plus an `o(n)` slack.
For sentinel log chunks, that budget is now proved:
`RMQ.RankSelect.fixedWeightBlockPayloadBudgetLePayloadBudgetFlattenAddBlocks`
gives the generic fixed-weight product/counting bridge from per-block code
budgets to the global fixed-weight payload budget plus one slack bit per
block, and
`RMQ.RankSelect.fixedWeightLogChunkBlockPayloadBudgetLePayloadBudgetAddBound`
specializes it to the `o(n)` sentinel log-chunk block-count overhead.
The older conservative primary theorem is
`RMQ.RankSelect.fixedWeightLogChunkBlockPayloadBudgetLeLengthAddBound`: for
sentinel log chunks, the per-block primary codes are bounded by raw `n` plus an
`o(n)` block-count term.
`RMQ.RankSelect.fixedWeightAmbientBlockCompositionWordBoundedCompressedProfileOfPrimaryBudget`
is the strengthened version carrying the directory profile and ambient
machine-word bounds into that conditional compressed/FID shape.
`RMQ.RankSelect.fixedWeightAmbientBlockCompositionWordBoundedCompressedProfileOfLogChunkBlocks`
consumes the sentinel log-chunk primary budget and removes the explicit
`primaryOverhead`/`hprimary` premise.
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
For route/class-length envelope families whose blocks are sentinel log chunks,
`RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeWordBoundedCompressedProfileOfLogChunkBlocks`
removes the primary-budget premise. The specialized public theorem
`RMQ.RankSelect.fixedWeightAmbientComputedRRRLogChunkRouteClassLengthTableEnvelopeWordBoundedCompressedProfile`
also fixes the block decomposition and class/length metadata overhead in the
theorem statement itself. The obstruction theorem
`RMQ.RankSelect.noFixedWeightAmbientComputedRRRLogChunkRouteClassLengthTableEnvelopeFamily`
proves this exact specialized computed-RRR envelope cannot be inhabited with a
fixed modeled local query cost. The replacement envelope is now
`RMQ.RankSelect.FixedWeightAmbientTableRAMRouteDirectoryFamily`, with public
profile
`RMQ.RankSelect.fixedWeightAmbientTableRAMRouteDirectoryFamilyWordBoundedCompressedProfileOfPrimaryBudget`.
It charges route/class metadata reads and a shared decoded-word table read
before fixed RAM word primitives. The log-chunk specialization
`RMQ.RankSelect.fixedWeightAmbientTableRAMLogChunkRouteDirectoryFamilyWordBoundedCompressedProfile`
now consumes the primary block-code budget in the theorem statement, and
`RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteFieldTableLayoutFamilyToTableRAMRouteDirectoryFamily`
feeds the existing fixed-width route tables into the table/RAM envelope. Two
tempting completions are ruled out: the dense log-chunk decoder is not an
`o(n)` counted payload
(`RMQ.RankSelect.noFixedWeightLogChunkDenseDecoderLittleO`), and route-width
class/length metadata is not `o(n)`. More directly,
`RMQ.RankSelect.noFixedWeightAmbientTableRAMLogChunkRouteDirectoryFamilyRouteWidthClassLength`
rules out the old single-width log-chunk table/RAM family when class/length
fields use route width. The replacement split-width surface is now proved:
`RMQ.RankSelect.fixedWeightAmbientTableRAMLogChunkSplitWidthRouteDirectoryFamilyWordBoundedCompressedProfile`
consumes the log-chunk primary budget while separating route width from
class/length width, and
`RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteFieldTableLayoutFamilyToSplitWidthTableRAMRouteDirectoryFamily`
feeds the existing route tables into that split-width envelope. The subsequent
sub-log/Packed-Clark modules close the concrete public compressed/FID family,
and the follow-up interpreted replay of the charged reads is now landed as
`RMQ.RankSelect.compressedFIDFixedWeightInterpretedFamilyProfile`.

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
operations, a reusable potential-method backend interface, and a concrete
parent-pointer forest layer:
`RMQ.UnionFind.referenceBackend_profile`,
`RMQ.UnionFind.referenceAmortizedBackend_profile`, and
`RMQ.UnionFind.Forest.parentForestRefinement_profile`.

The forest spoke now includes executable root search, union-by-rank refinement
checkpoints, root-mass and rank-power invariants, full path-compression find
refinement, logarithmic-rank and rank-bucket amortized checkpoints, and a
rank-slack compression-drop kernel. The current frontier profiles are
`RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressionRankBucketAmortizedBackend_profile`,
`RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressionRankSlackCheckpoint_profile`,
`RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressionRankSlackAmortizedBackend_profile`,
and
`RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressionRankSlackSizeUnionAmortizedBackend_profile`.
Successful full-compression find is paid by rank-slack potential drop up to
constant credit, while the cleaned union checkpoint still uses the coarse
credit `rankBucketPotential backend + 1`. It is still not the final Tarjan
theorem: the repo does not yet prove the inverse-Ackermann amortized bound, a
small uniform union credit under this potential, or a mutable-array
implementation refinement.

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
