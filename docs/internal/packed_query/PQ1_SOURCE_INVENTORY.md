# PQ1 source inventory and disposition

Exact source/governance: `4639223bc8130b0ef752270b5cbdd74325abcd60`.
Two read-only subagents inspected source, passed role preflight with the actual
three-skill runtime catalog, and confirmed their inspected paths still matched
RC6. Neither changed files nor ran Lean/Lake. Their inventory evidence is
incorporated here; no source acceptance or roadmap closure follows from it.

## PQ1-SM: allocation and width

Selected route: prepend a fixed number H of numeric metadata words to dense
repacking of `(PackedCellProbe.packedReviewerMemory shape).flatten` at W(n).
This retains and counts the old header and padding. The generic inequality is
`new.length*W <= old.length*oldWidth+(H+1)*W`; the extra one is new final padding.
Program and scratch P,R words can be absorbed by replacing H+1 with H+1+P+R.

Verified source anchors under
`RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/`:

* `ReviewerPayload.lean:47`: packed reviewer payload for the List-built shape
  equals `SuccinctClassic.buildPayload xs`.
* `ReviewerLength.lean:161,195`: exact payload length in n/long/sparse counts
  and unconditional bound by `2*n+reviewerOverhead n`.
* `ReviewerMemory.lean:151,158`: exact old cell count and every old cell has
  length `packedReviewerCellWidth shape.size`.
* `ReviewerCrossing.lean:68,116`: old-memory flatten identity and one-word span
  reconstruction from two consecutive old cells. The generic induction at
  line 43 is private, so arbitrary-width public packing is a new prerequisite.
* `ReviewerSpace.lean:64,89,96`: complete old allocated capacity bound,
  `LittleOLinear packedReviewerCellWidth`, `LittleOLinear packedReviewerRho`.
* `ReviewerControllerProof.lean:594`: for every shape and logical request,
  `packedReviewerLogicalRead shape.size (longCount shape)
  (packedReviewerSparseCount shape) (packedReviewerMemory shape) request`
  equals the canonical global store's read at request.segment/request.index.
  This includes absent requests and segment 20.
* `ReviewerControllerProof.lean:2778,2791,2806`: capacity bound
  `packedReviewerCellBound n+2 <= 400000*(n+1)`; old width at most
  `20*(Nat.log2(n+2)+1)`; sparse count fits the old width.

Proposed metadata bank: 174 words, comprising 42 scalar values, 23 regular
descriptor slots of four fields, eight interior descriptors of five fields.
Regular fields: old absolute bit base, payload bit length, logical stride,
logical word count. Preserve the last field even when a logical sentinel has
zero length. Interior fields: segment word base, component word count, old
absolute bit base, entry width, chunks per entry. The eight components are
baseline/minRel/maxRel/argOffset/localOffset/globalBlock/localLevel/globalLevel.
This schema must be proven complete against the final program before freezing
its concrete builder; 174 is currently the source-derived proposal.

Next bridge: an old-cell loader receives only H,W,oldWidth,oldCount,memory,index.
It guards the index and reads bit span `H*W+index*oldWidth` of length oldWidth.
For canonical repacking prove the numeric reply equals
`old[index]?.map bitsToNatLE`. Then lift old packed fetch by ordered-list
induction, preserving repetition. A two-old-cell logical plan needs at most
four new payload reads. Primitive instruction proof remains separate.

## PQ1-SC: control and constant loop bounds

The public whole protocol at `ReviewerWholeProtocol.lean:31,36,73,102`
starts from n,left,right, exposes a next logical request, consumes a logical
reply, and exposes an optional terminal result. Its five states are leftSelect,
rightSelect,lcaClose,finalRank,done. It selects left and right-1, obtains their
LCA close, then ranks answerClose+1 and subtracts one.

`ReviewerLogicalSimulation.lean:6104` proves, for every shape and valid range,
that the actual 210-fuel logical drive has terminal `some reference.value`,
state `.done reference.value`, and ordered erased trace equal to
`packedWholeQueryRun store shape.size left right`. Its index-preserving theorem
at 6129 and occurrence erasure at 6146 support positional consumers. Component
public joins at 5645 and 5674 cover select in 35 logical steps and LCA in 129.
These numbers count logical requests, not primitive instructions.

| Restricted-source computation | Bound / exact source |
| --- | --- |
| Sparse-count prelude | Growing `SPARSESLOTS % SPARSEW`; replaced by counted metadata. |
| Rank chunk fold and word-select search | At most 8; `ChargedWordChunks.lean:153`, `bpWordChunkCount_le_eight`. |
| Select dispatch | Fixed branches; long segment12/sparse segment16 are actual exception reads. |
| BP window load and ragged chunk extraction | Four logical attempts and four value/length pieces. |
| Fringe fold | At most 33 chunks per fringe; two fringes on different-block path. |
| Interior entry | At most 8 logical chunks from all-size widths, not an assumed one-word entry. |
| Interior range | At most three local/global two-span calls; no loop over macros. |
| Physical logical plan | At most two old cells per request. |
| Whole protocol | 210 logical transitions; each still needs charged computation. |
| Calls | Acyclic subroutines with explicit moves and transfer/return PCs. |

The interior bound follows from directory Base.lean:3830/3850/3874 and
SparseLevelWidth.lean:96/113 under
`RMQ/Core/SuccinctClose/EndpointFringe/InteriorCandidate/InteriorDirectory/`:
relative/offset/block/local-level/global-level widths are at most 7 BP words.
`canonicalRelativeRmmMachineReadNatCosted_cost_le_eight` at SparseLevelWidth:367
converts these into at most eight chunks. One-word macro-crossing refinements
exist but are unnecessary for a generous instruction bound.

Semantic edges to retain: rank count at effective length zero is one because
Nat subtraction precedes division; missing BP words contribute zero *length*;
short BP words retain actual length; missing select-table reply defaults to
offset zero in the logical semantics; missing physical load faults after its
receipt; dead interior logical requests may have empty physical plans; candidate
merge uses strict improvement so ties remain leftmost. Current interior uses
local/global level-table reads, not runtime log2.

The new ragged numeric extractor must prove equality to
`bitsToNatLE (((w0++w1++w2++w3).drop(j*c)).take c)` for arbitrary four lengths.
Existing `E1FringeBridge` fixed-stride theorem requires three full words and
cannot close this leaf. Reuse its append numeric lemma and `E1RankBridge`'s
drop/division and take/modulo facts instead.

## Lifecycle disposition

Both scout prompts passed structural preflight and lead semantic review.
Reports are incorporated as inventory; no temporary worktrees were created.
Their source findings supply concrete consumers in the model/proof DAG.
PQ1-C separately owns generic primitive execution calculus. Lead owns
Primitive.lean, DensePacking.lean, the allocation/compiler joins and shared
ledger updates. All work remains on the user-authorized feature branch.
