# PRE-1 source and feasibility inventory

Read-only review at `0e6a00f654abc64f8b68988fa9675b9a839dca2f`; this inventory
is evidence for choosing the contract, not a complexity theorem. Independent
leaves reviewed the historical contract and the canonical pipeline while the
lead authored the contract. No builder construction was performed.

## Exact output

Packed/Allocation.lean:154-158 defines
`buildMemory xs = shapeMemory (SuccinctClassic.cartesianShape xs)` and
`shapeMemory shape = repackWords (metadata shape) (wordWidth shape.size)
(packedReviewerMemory shape)`. Packed/DensePacking.lean:163 defines
`repackWords headers width old = headers ++ denseWords width old.flatten`.
The old memory header and old zero padding are therefore retained before the
new dense-word padding. Removing either changes the required ordered output.

Allocation.lean:47,119-150 fixes 174 metadata words: 42 scalars, 23 descriptors
of four words, eight descriptors of five words. Its scalar fields include
length, both widths, old extent, long/sparse counts, physical extent, directory
geometry and component offsets. Shape-dependent metadata is stored data.

The outer five payload components, in FlatPayload.lean:1864-1883, are BP code,
access payload, close/interior directory, fringe microtable and false-select
microtable. The access payload has 18 sources at FlatPayload.lean:1831-1842.
These five components must not be confused with the interior **five wrappers**:
InteriorDirectory/Base.lean:1376-1457 has the summary wrapper (four tables),
local sparse wrapper, global sparse wrapper, local level/span wrapper, and
global level/span wrapper. Its component store at line 1551 orders the eight
encoded tables as baseline, minimum relative excess, maximum relative excess,
argmin offset, local sparse offset, global sparse block, local level/span,
global level/span. Allocation.interiorComponents:77-79 repeats this order.

## Construction obligations and feasibility

| Reference source | Actual operation | Required efficient replacement and equality invariant |
| --- | --- | --- |
| Shape.lean:662,893 | Each insertion descends and rebuilds the right spine | Maintain a monotone stack; each node pushes/pops at most once. Pop on strict improvement only, preserving equal-key leftmost ties. Tail recursion of the old builder is not an amortized bound. |
| Shape.lean:47 | BP is opening, left subtree, closing, right subtree; repeated append | Cursor/stack traversal emits that exact order with 2n bits and charged constant work per node/bit. |
| SuccinctRank.lean:46,89,97 | Fresh rankPrefix calls for each sampled prefix | Running count and saved super-boundary count produce exactly the same samples, including terminal/sentinel entries. |
| GenericSelect/Slots.lean:62 and Entries.lean:21 | Repeated semantic select/position scans and span computations | One occurrence-position pass, strict threshold comparisons, canonical inactive zero fields, stable exception compaction. |
| LocalSparseOffset.lean:19; LocalGlobalSparse.lean:204; SparseArgMin.lean:100 | Each valid cell scans its range | Memoize adjacent-half minima with leftmost ties, exact invalid-cell zeros and local macro/level/start versus global level/start order. |
| SparseTableMemoCost.lean:57-86 | Semantic recurrence and modeled tickValue | Reuse equality ideas only; these ticks do not establish reflected construction work. |
| ChargedFringeChunks.lean:42,363 | c=log2(m)/8+1, table size 2^c*(c+1)^2 | Generate and charge microtable entries, with explicit all-size work constants. |
| ChargedWordChunks.lean:461,491,530 | Select microtable entries/wrapper | Generate the exact table as counted data, never as a free instruction literal or semantic macro. |
| ReviewerMemory.lean:54,96-147; DensePacking.lean:163 | Old header/padding followed by dense repacking | Stream the identical old word bits into the new width, preserving both padding layers and metadata order. |

These are feasible local proof/construction obligations, not a proof of their
joint linear bound. No formal obstruction to the assigned target was found.
The full matrix remains open until that target is proved.

## Width and query consumer

Allocation.lean:23 has `wordWidth n = 32 + 8 * packedReviewerCellWidth n`.
The floor is intentional even at n=0. ReviewerWidth.lean:59-63 derives the
older width from the payload bound. QueryStatic.lean:65-107 pins the fixed
program budget to 837572, register count 8271, scratch 8274, and proves its
fields fit every n using the 2^32 floor. No strict all-size code/payload
information gap follows from these facts.

Packed/Primitive.lean imports Std only; it has nine constructors and no store
or allocation. The arithmetic and comparison operation sets are explicit. Its
execute/step/run and safety interfaces are the conservative-extension boundary.

Packed/Capstone.lean:173 supplies fullyChargedPackedQueryCapstone_holds. Its
record binds retained capacity, word/address bounds, exact half-open answers,
leftmost ties, query run and positional reads to the same buildMemory xs.
Representable invalid endpoints return packet zero without reads. PRE must
transport these statements using exact emitted-cell equality, not matching
length or an intermediate sibling allocation. The existing theorem makes no
preprocessing or Lean-runtime claim.

## Historical contract sources

RMQ_PROGRAM_PLAN.md:228-322 defines C1-C4 and the prior-audit boundary.
Its lines 297-300 explicitly add an aggregate gate; there is no baseline PRE
contract checker. The 15-case author completeness table is process evidence,
not a replacement for a fresh blind audit. The historical JSON contains 25
comparison rows, 15 distinct FK IDs, with no FK-10.

SHA-256 at the governed base:

- wf3_attack.json: F26087549E6AB0B5A8A43423474F42509CCA2720DE93ED761840DD02660B44E6
- RMQ_PROGRAM_PLAN.md: E66111A9545DA6C8E9F472BBAFCF81C3752AD734961853C9612EF8F07B113B86
