# Different-block LCA arithmetic specification

Exact source baseline: RC6 `4639223bc8130b0ef752270b5cbdd74325abcd60`, at `C:/Users/poin/Documents/RMQ/audit-rc6-20260910`. Coordinates below are relative to that tree. This leaf wrote only this note and `lca_interior_program.py`; it did not edit the candidate or run Lean, Lake, or the Python query. The Python file is restricted DSL input for the lead's compiler, not a host-language implementation to use as an answer oracle.

## Chosen reference and interface

The reference is the literal size-only `packedLcaCloseLeaf`, with the different-block branch `packedCrossBlockCloseRead` at `RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReadProgram.lean:1873-1900`, as defunctionalized by `ReviewerLcaProtocol.lean`. In the pseudocode below, `read(segment,index)` returns the little-endian integer payload plus one; zero means absent. `word_len(segment,index)` gives that logical reply's actual bit length. The lead's actual-memory physical lowering must implement both. The supplied `rank_close(pos)` is the literal close-rank logical route and returns an untagged natural.

`lca(left_close,right_close)` returns zero for `none`, and `answerClose+1` otherwise. It does not perform the outer RMQ interval validation or the two initial select-close calls. The caller owns those. Same-block support is included in the DSL because it shares the same fringe implementation.

All subtraction in this DSL means **Lean natural subtraction**, saturated at zero. Ordinary Python subtraction is not an interpreter for it. No signed-excess encoding is necessary: the reference uses natural excess values with offset-encoded table fields and explicit subtraction. In particular `seed = base - 2*rankFalse` (`SuccinctClose/RelativeRmmMacro/LocalBPDecoder.lean:484-486`), and a summary score is `baseline + minRel - B*S` (`EndpointFringe/PrefixRange/RelativeSummaryCandidate.lean:15-22`). Do not replace these by signed subtraction on malformed inputs.

Candidates are represented by three separate globals `CAND_OK`, `CAND_SCORE`, `CAND_POS`, not one quadratic-size packed integer. A candidate's position is a BP prefix position; converting it to a close applies `position - 1`. Thus the tagged final result is **`(position - 1) + 1`**, retaining saturation even when the position is zero. The source conversion and tie rule are `EndpointFringe/InteriorCandidate/Candidate.lean:15-29`: take the right candidate only for a strictly smaller score, preserving the left candidate on ties.

## Size-only geometry globals

Let `lg(x) = Nat.log2 x`, including `lg(0)=0`, and `ceilDiv(a,b) = a//b + (1 if a%b != 0 else 0)` for positive `b`.

| DSL global | Formula | Source |
|---|---|---|
| `S` | `lg(N)+1` | `PackedCellProbe/SourceFactorization.lean:386` |
| `B` | `2*S` | `ReadProgram.lean:800` |
| `BPW` | `lg(2*N)+1` | `PackedCellProbe/Probe.lean:683`, `packedBpCodeWordWidth` |
| `C` | `lg(2*N)//8+1` | `ReadProgram.lean:869`; `ChargedFringeChunks.lean:42` |
| `NB` | `N//S` | `SourceFactorization.lean:389` |
| `NS` | `NB//S+1` | `RelativeSummary.lean:1285` |
| `M` | `S*S` | `RelativeSummary.lean:1292` |
| `MC` | `NB//M+1` | `RelativeSummary.lean:1295` |
| `OW`, `LC` | `lg(M)+1`, and `LC=OW` | `RelativeSummary.lean:1298-1302` |
| `GC` | `lg(MC)+1` | `RelativeSummary.lean:1304` |
| `BAW` | `lg(NB)+1` | `RelativeSummary.lean:1307` |
| `RW` | `2*(lg(S)+1)+3` | `SourceFactorization.lean:396` |
| `LD`, `GD` | `M+2`, `MC+2` | `PrefixRange/SparseLevelTable.lean:41` |
| `LW` | `lg(LD*(lg(LD)+1))+1` | `SparseLevelTable.lean:150` |
| `GW` | `lg(GD*(lg(GD)+1))+1` | same |

`ReadProgram.lean:1062-1066` assembles the layout from `B,S,NB,RW`. For segment 20, eight tables have the following entry counts and fixed entry widths, in this exact order (`ReviewerInteriorRead.lean:41-62`):

| Table | Entry count | Entry width | DSL base |
|---|---:|---:|---|
| baseline | `NS` | `BPW` | `OFF_BASELINE` |
| relative minimum | `NB` | `RW` | `OFF_MIN` |
| relative maximum | `NB` | `RW` | `OFF_MAX` |
| argmin offset | `NB` | `RW` | `OFF_ARG` |
| local sparse offset | `MC*(LC*M)` | `OW` | `OFF_LOCAL` |
| global sparse block | `GC*MC` | `BAW` | `OFF_GLOBAL` |
| local level/span | `LD` | `LW` | `OFF_LOCAL_LEVEL` |
| global level/span | `GD` | `GW` | `OFF_GLOBAL_LEVEL` |

Each table's logical word count is `entryCount * ceilDiv(entryWidth,BPW)`. `OFF_BASELINE=0`; each following base is the prefix sum of these word counts; `OFF_DEAD` is their total. This is the literal offset construction at `ReadProgram.lean:1255-1275`, with its closed chunk-count counterpart at `ReviewerInteriorRead.lean:87-94`.

These globals contain only input-size geometry. If the experiment supplies them before the charged query, its measurements exclude that setup. They must be computed/charged or explicitly admitted as preprocessing/nonuniform constants before asserting a full uniform word-RAM query theorem.

## Outer different-block path: exact read order

For close endpoints `L,R`, let `lb=L//B`, `rb=R//B`, and

```text
base(close) = (((close//B)*B)//BPW)*BPW
```

This is `packedLocalBPWindowBase` (`ReadProgram.lean:828-831`). The different-block sequence is:

1. `rank_close(base(L))`; set `leftSeed=base(L)-2*rankFalse`.
2. Read exactly four logical BP words: segment 0 at `((lb*B)//BPW)+0,+1,+2,+3`.
3. Left fringe with `start=L+1`, `span=lb*B+B-L`, `relLo=start-base(L)`, `relHi=start+span-1-base(L)`.
4. If `lb+1 < rb`, interior query `(startBlock=lb+1,count=rb-lb-1)`; otherwise middle candidate is absent and no interior read is issued.
5. `rank_close(base(R))`; set `rightSeed=base(R)-2*rankFalse`.
6. Read exactly four logical segment-0 words starting at `(rb*B)//BPW`.
7. Right fringe with `start=rb*B`, `span=R-start+2`, and the same relative-coordinate formulas using `base(R)`.
8. Merge left then middle then right with the strict-score keep-left rule, and convert prefix position to close position.

The construction and progression are `ReviewerLcaProtocol.lean:65-79,133-210,237-293`. Same-block uses one seed/window/fringe with `start=L+1`, `span=R-L+1` (`:104-131`).

The four logical BP attempts are unconditional, including absent tail words. `ReviewerLogicalProtocol.lean:494-519` appends `reply.getD []`, so missing replies have **zero** concatenation length; they are not padded with a full zero word. A short final successful word uses its actual length. The DSL preserves this by storing four separate word/length register pairs `LCA_WIN0..3`/`LCA_LEN0..3`; it does not concatenate all four into a register requiring four times the BP-word width.

`window_chunk(j)` implements the low-endian integer of `(window.drop(j*C)).take(C)` (`ChargedFringeChunks.lean:489-490`). It walks those four registers, extracts their overlap with the requested slice, and assembles at most `C` bits. This is a fixed four-iteration arithmetic loop over returned data, with no additional memory reads.

## Fringe arithmetic

For `j=0 .. min(relHi//C+1,33)-1`, with `u=j*C`:

```text
a = min(C, max(relLo,u)-u) = min(C, relLo-u)    [Nat subtraction]
b = min(relHi+1,(j+1)*C)-u
v = window_chunk(j)
slot = (v*(C+1)+a)*(C+1)+b
tag = read(21,slot)
entry = tag-1                                [absent -> 0]

candidate exists for this j iff a < b:
  score = acc + ((entry//(C+1)) % (2*C+2)) - C
  position = j*C + entry%(C+1)
  merge into best using strict score comparison; ties retain older best

acc = acc + entry//((C+1)*(2*C+2)) - C
```

Initialize `acc=seed`, `best=none`. Compute the candidate with the **old** accumulator before updating `acc`. At the end, a present best becomes `(best.score,base+best.position)`; if no best exists, return the present fallback `(seed,start)`.

Sources: `ReviewerLogicalProtocol.lean:428-468`; `ChargedFringeChunks.lean:245-248` (mixed-radix entry), `:360-364` (slot/table count), `:900-905` (start/end offsets), `:1493-1502` (reply-driven step), and `:1617-1620` (fallback/global transport). Do not recompute delta, minimum, or argmin from the BP bits: all three are decoded from the actual segment-21 reply.

## Segment-20 decoded natural read

`interior_read(entryCount,width,base,index)` returns a tagged natural:

* Set `chunks=ceilDiv(width,BPW)`.
* If `index < entryCount`, attempt segment-20 reads at `base+index*chunks+j` for every `j=0..chunks-1`, in order. Decode the concatenation of the actual successful word lengths in little-endian order. Return absent if **any** attempted reply was absent; still issue the remaining reads. For `chunks=0`, the empty decode is present zero, hence tag 1.
* Otherwise, attempt exactly one logical read at `OFF_DEAD` and decode that singleton reply. On the accepted physical route the dead address classifies absent and generates no physical read, but it remains one attempted logical read in the supplied-store reference.

Sources: `ReviewerLogicalProtocol.lean:544-587`; `SuccinctSpace/MachineChunkedTable.lean:12-13,215-217`. Do not implement a missing chunk as zero and then return a present entry.

## Interior control and candidate arithmetic

`minCandidate(block)` reads **all four** of the following, in this order:

```text
b  = interior_read(NS,BPW,OFF_BASELINE,block//S)
mn = interior_read(NB,RW,OFF_MIN,block)
mx = interior_read(NB,RW,OFF_MAX,block)
arg= interior_read(NB,RW,OFF_ARG,block)
```

If any is absent, the candidate is absent. Otherwise decode their tags and return `(b+mn-B*S, block*B+arg)`. The `mx` value is not used in that pair, but its presence and actual read remain required. Removing it changes the reference trace and failure behavior. Source: `ReviewerInteriorProtocol.lean:99-107,213-243`; `ReadProgram.lean:1403-1425`.

```text
localSpan(macro,localStart,level):
  slot = macro*(LC*M) + level*M + localStart
  offset = interior_read(MC*(LC*M),OW,OFF_LOCAL,slot)
  if absent: none
  else: minCandidate(macro*M + offset)

globalSpan(macroStart,level):
  slot = level*MC + macroStart
  block = interior_read(GC*MC,BAW,OFF_GLOBAL,slot)
  if absent: none
  else: minCandidate(block)

localTwo(macro,localStart,count):
  encoded = interior_read(LD,LW,OFF_LOCAL_LEVEL,count)
  if absent: none
  else:
    level = encoded//LD; span=encoded%LD
    a = localSpan(macro,localStart,level)
    b = localSpan(macro,localStart+count-span,level)
    merge(a,b)

globalTwo(macroStart,count):
  encoded = interior_read(GD,GW,OFF_GLOBAL_LEVEL,count)
  if absent: none
  else:
    level = encoded//GD; span=encoded%GD
    a = globalSpan(macroStart,level)
    b = globalSpan(macroStart+count-span,level)
    merge(a,b)
```

All displayed variables after successful `interior_read` calls in this pseudocode are **decoded payload values**, not tags. The Python DSL subtracts one explicitly. Sparse-level payloads encode `span + domain*level` (`SparseLevelTable.lean:55-56`); consume those returned fields rather than computing a new `log2(count)` or `2^level`. Local/global slot formulas are at `PrefixRange/LocalSparseOffset.lean:15-17` and `InteriorCandidate/LocalGlobalSparse.lean:200-202`; continuations are at `ReviewerInteriorProtocol.lean:109-162,169-187,244-273`.

Even if both sparse spans have identical starts, **read both** and both corresponding summaries. The source performs both calls; deduplication would fail an ordered trace comparison.

For the top-level interior query `(startBlock,count)`:

```text
if count==0: none
macroStart = startBlock//M
localStart = startBlock%M
firstCount = M-localStart
if count<=firstCount:
  localTwo(macroStart,localStart,count)
else:
  rest=count-firstCount; middleCount=rest//M; rightCount=rest%M
  left=localTwo(macroStart,localStart,firstCount)
  if middleCount==0:
    right=localTwo(macroStart+1,0,rightCount)
    merge(left,right)
  else:
    middle=globalTwo(macroStart+1,middleCount)
    if rightCount==0:
      merge(left,middle)
    else:
      right=localTwo(macroStart+1+middleCount,0,rightCount)
      merge(merge(left,middle),right)
```

This follows `ReviewerInteriorProtocol.lean:275-305` and `ReadProgram.lean:1701-1746`. The scalar DSL performs the pure left/middle merge before reading the right subcandidate; the reference's final merge expression has the same left-associated value and the same ordered reads. This timing of pure register work is not an exact translation of every Lean evaluator reduction, and no such reduction count is claimed.

## Physical lowering: ragged geometry is load-bearing

Segment 20 is a concatenation of *logical machine chunks of entries*, but its packed bit payload has no per-entry or per-word padding. Thus the physical address is **not** a common base plus `logicalIndex*BPW`.

Classify the segment-20 index using the eight `OFF_*` ranges; reject `index >= OFF_DEAD`. For the selected table with entry width `t`, entry count `k`, logical word prefix `wp`, and **bit prefix** `bp=sum(previous entryCount*entryWidth)`:

```text
q = ceilDiv(t,BPW)
j = logicalIndex-wp
entry = j//q
chunk = j%q
bitOffset = entry*t + chunk*BPW
readWidth = min(BPW, t-chunk*BPW)
addressBits = physicalCellWidth
            + (2*N + closedAccessLength(N,longCount,sparseCount))
            + bp + bitOffset
```

The range classifier ensures `q>0` for a selected table. These are `ReviewerInteriorRead.lean:97-158,186-206` and `ReviewerEntryAddress.lean:45-54`, with the absolute address at `ReviewerClosedGeometry.lean:262-272`. `packedReviewerSegment20_eq_interiorRead` at `ReviewerInteriorRead.lean:1323-1328` connects this read to the actual global store.

For segment 21:

```text
fringeBase = 2*N + closedAccessLength(...) + interiorRawPayloadOverhead(N)
addressBits = physicalCellWidth + fringeBase + slot*fringeEntryWidth(N)
readWidth = fringeEntryWidth(N)
```

This is `ReviewerClosedGeometry.lean:291-307`. Guard the slot against `packedReviewerFringeCount N`; invalid slots have an empty physical plan and absent logical reply (`ReviewerLogicalLowering.lean:216-269`). Decode from one cell if `addressBits % physicalCellWidth + readWidth <= physicalCellWidth`, otherwise from the ordered pair of adjacent cells. `readWidth=0` issues no cells. Physical allocation guards and missing-cell behavior belong to the lead's physical `read` implementation, not a table reconstructed from source input values.

## Complexity and coverage cautions

The existing close/LCA measure is at most 129 logical reads on the cross-block route (`ReviewerLcaProtocol.lean:303-324`): two rank seeds, two windows/fringes, and up to 33 interior logical reads. This is **not** an instruction count. The DSL charges its scalar register operations, loops, dispatch, tag decoding, and physical lowering under the lead's new experiment semantics.

The interior's `<=33` statement is for canonically reachable invocations; `ReviewerInteriorProtocol.lean:352-355` explicitly excludes arbitrary forged state parameters. The DSL preserves the generalized chunk-read loops; a malformed query or size outside that reachable path is not evidence against the canonical structural bound.

Small whole-query fixtures may reach nonempty interior lookups while still exercising only `localTwo`. Size-only arithmetic gives the following necessary availability thresholds for later macro branches: `NB>=M+1` first occurs at `N=1010` (`S=10,M=100,NB=101`); `NB>=2*M` first occurs at `N=3456`; `NB>=2*M+1` first occurs at `N=3468` (both `S=12,M=144`). These were computed from the displayed geometry alone, not measured source queries. They do not guarantee a selected shape/query reaches the branch. Running large canonical builders merely to reach these branches may be costly; report actual branch coverage instead of implying all four cases were tested.

No result of the DSL/compiler is reported by this leaf. The lead must record compilation, actual reply/trace/output comparisons, numeric maxima, and any unexecuted branches. The remaining claim boundary is a semantic/compiler-refinement proof and all-size bounded-word analysis, including geometry setup and tagged intermediate values; finite matching runs do not complete that theorem.
