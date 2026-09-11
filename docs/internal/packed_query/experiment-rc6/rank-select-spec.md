# RC6 rank/select arithmetic and physical geometry

Source assessed: `audit-rc6-20260910`, commit `4639223bc8130b0ef752270b5cbdd74325abcd60`. This is a source-derived implementation specification for the external experiment, not a new Lean refinement theorem. Candidate files were read only. The companion `rank_select_program.py` is restricted Python syntax intended for the lead's AST compiler; its query functions must never run as host-language semantic callbacks.

All source paths below are relative to that candidate. `PCP/` abbreviates `RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/`; `RMM/` abbreviates `RMQ/Core/SuccinctClose/RelativeRmmMacro/`.

## Arithmetic contract and compiler entry points

All values are naturals. Every subtraction saturates at zero. Division is floor division. All divisors below are positive, including at `N=0`. Use Lean's `log2(0)=0`. Words are little-endian integers paired with their geometry-derived actual bit length; zero high bits do not disclose the length.

The companion supplies `rank_close(pos)`, `rank_long(pos)`, `rank_sparse(pos)`, `select_close(index)`, `rank_word(word,word_len,limit,target)`, and `select_word_false(word,word_len,occurrence)`. Select returns option-tagged indices: `0=none`, `position+1=some position`. Rank returns the untagged count. The helper functions contain only arithmetic, comparisons, conditionals, while loops, and statically inlineable calls.

Required external calls:

- `read(segment,index)`: execute this logical request through the physical mapper below. Return `0` for an absent logical word; otherwise return its decoded integer plus one. This function must itself lower to charged instructions and physical loads. It cannot consult the input list, Cartesian shape, a logical-store oracle, expected answers, or a precomputed query trace.
- `read_len(segment,index)`: return the requested logical bit width from the same geometry. It performs no memory load. In this file it is called only after a present logical word. A present empty sentinel has tag `1` and length `0`.

An absent physical cell is a different event: the packed controller fails immediately, after counting the attempted probe. Do not treat it as an ordinary logical `none` and continue. The finite canonical-memory experiment may avoid this case, but must state that limit. See `PCP/ReviewerLogicalLowering.lean:216` (logical plan) and `:251` (logical presence guard).

## Size-only constants

Define `mb(x)=log2(x)+1` and `ceil(a,b)=(a+b-1)//b` for positive `b`.

| Compiler name | Formula | Source |
|---|---|---|
| `N` | public input length | endpoint contract |
| `BPW` | `mb(2*N)` | `PCP/ReadProgram.lean:120`; `PCP/Probe.lean:683` |
| `C` | `log2(2*N)//8+1` | `PCP/ReadProgram.lean:869`; `RMM/ChargedFringeChunks.lean:42` |
| `ELL` | `mb(BPW)` | `RMQ/Core/GenericSelect/Params.lean:22` |
| `SS` | `BPW*BPW` | `Params.lean:25` |
| `LS` | `max(1,BPW//(ELL*ELL))` | `Params.lean:28` |
| `LPS` | `ceil(SS,LS)` | `GenericSelect/Arithmetic.lean:213`; `Slots.lean:30` |
| `SUPERSLOTS` | `ceil(N,SS)` | `PCP/SourceFactorization.lean:245` |
| `LOCALSLOTS` | `SUPERSLOTS*LPS` | `SourceFactorization.lean:575` |
| `SPARSESLOTS` | `min(LOCALSLOTS,N)` | `SourceFactorization.lean:599` |
| `LONGW` | `mb(SUPERSLOTS)` | `SourceFactorization.lean:522` |
| `SPARSEW` | `mb(SPARSESLOTS)` | `SourceFactorization.lean:613` |
| `LOCALWIDTH` | `mb(min(2*N,SS*BPW*ELL))` | `SourceFactorization.lean:586`; `Params.lean:31` |
| `RANKBLOCKWIDTH` | `mb(BPW*BPW)` | `SourceFactorization.lean:144` |
| `W` | `mb(2*N+canonicalReviewerOverhead(N)+2)` | `PCP/ReviewerWidth.lean:59` |

The exact Lean name in the last row is `concreteBPNativeSuccinctRMQCanonicalReviewerOverhead`. `W` is the physical cell width; it is not `BPW`. Supplying the exact candidate's size-only overhead/width as a compiler parameter is permitted by this experiment. Computing it by a uniform query program would itself require a cost/refinement account.

Only `LONG` and `SPARSE` are content-dependent geometry scalars. They must be decoded during the charged header/prelude execution, not supplied from the fixture's expected metadata.

## Rank: three directory reads followed by the real chunk-table fold

`PCP/ReviewerLogicalProtocol.lean:168-325` gives the three rank specializations:

| Rank | bit length | word size | blocks per super | super/block/word segments | target |
|---|---:|---:|---:|---|---|
| close | `2*N` | `BPW` | `BPW` | 17 / 18 / 19 | false |
| long | `SUPERSLOTS` | `LONGW` | 1 | 9 / 10 / 11 | true |
| sparse | `SPARSESLOTS` | `SPARSEW` | 1 | 13 / 14 / 15 | true |

Clamp `q=min(pos,bitLength)`; let `i=q//wordSize`. Read the super at `i//blocksPerSuper`, block at `i`, and word at `i`, in that order. Perform all three reads before testing their options. If any is absent, return zero. Otherwise return the two decoded samples plus `rank_word(word,actualWordLength,q-i*wordSize,target)`.

For that fold:

```text
e = min(limit, actualWordLength)
count = min(((e-1) // C)+1, 8)       # Nat subtraction
acc = 0
for j = 0 .. count-1:
    t = min(C, e-j*C)
    v = (word >> (j*C)) & ((1<<C)-1)
    slot = (v*(C+1)+t)*(C+1)+t
    packedEntry = default0(decode(read(21,slot)))
    z = ((packedEntry//(C+1)) % (2*C+2) + t - C)//2
    acc += z if target=true else t-z
return acc
```

These are actual table requests, not replacement host popcounts. The slot and decode formulas are `RMM/ChargedFringeChunks.lean:360`, `:489`, and `RMM/ChargedWordChunks.lean:106`, `:138`, `:142`, `:150`, `:255`.

**Zero-length edge:** `count=1` when `e=0`; the source's `(e-1)` is saturating. Do not replace this with ordinary ceiling division that visits zero chunks. This matters at word boundaries and empty sentinel words. The code preserves it.

## Select: entry dispatch, then long/sparse or dense two-word resolution

`PCP/ReviewerSelectProtocol.lean:70-310` and `RMQ/Core/GenericSelect/RelativeSplit.lean:13-65` determine the algorithm. Indices are zero-based occurrences of false (closing) bits. If `index>=N`, return none without reads.

Read super fields at `superSlot=index//SS` from segments 1,2,3,4 in order. They are `baseOccurrence,baseWordIndex,rankBefore,firstOffset`. All four are read before checking absence. Any missing field means none. A mark is exactly `rankBefore!=0`.

If the super entry is marked:

```text
exceptionRank = rank_long(superSlot)
slot = exceptionRank*SS + (index-super.baseOccurrence)
offset = read(12,slot)
return map (super.baseWordIndex*BPW + super.firstOffset + offset)
```

Otherwise read the four local fields from segments 5,6,7,8 at:

```text
localSlot = superSlot*LPS + (index-super.baseOccurrence)//LS
baseOccurrence = super.baseOccurrence + local.baseOccurrence
basePosition = (super.baseWordIndex+local.baseWordIndex)*BPW + local.firstOffset
```

The local first offset belongs to the combined base word; do not add the super first offset again. If local is marked, read segment16 at
`rank_sparse(localSlot)*LS + (index-baseOccurrence)` and map the returned offset to `basePosition+offset`.

For an unmarked local entry:

1. Read segment0 at `baseWord=basePosition//BPW`; absence means none.
2. Run two actual false-target chunk rank folds on that reply: `beforeFirst` below `basePosition-baseWord*BPW`, then `uptoFirst` below its actual length.
3. Let `k=index-baseOccurrence` and `available=uptoFirst-beforeFirst`.
4. If `k<available`, word-select occurrence `beforeFirst+k` in the first word and add `baseWord*BPW`.
5. Otherwise read segment0 at `baseWord+1`, word-select occurrence `k-available` there, and add `(baseWord+1)*BPW`. Missing second word means none.

Word-select (`PCP/ReviewerLogicalProtocol.lean:334-405`) uses the same capped chunk count and first reads segment21's `(v,t,t)` row for each visited chunk. Decode its false count. If the remaining occurrence lies in that chunk, read segment22 at `v*(C+1)+occurrence`, then return `j*C+default0(decodedReply)`. Otherwise subtract the count and advance. Exhaustion means none. **A missing select-table reply defaults to offset0 and returns some**, matching the source; do not strengthen malformed-memory behavior accidentally. The sole segment22 table on this route is for false bits.

## Physical map for segments 0..19, 21, 22

For each segment let `stride`, `rows`, and `bits` be as follows. Define `chunkCount(m,w)=ceil(m,w)` (ordinary zero-preserving ceiling), `LR=SUPERSLOTS//LONGW+1`, `SR=SPARSESLOTS//SPARSEW+1`, `RS=2*N//BPW//BPW+1`, `RB=2*N//BPW+1`.

| Segments | stride | logical rows | stored bits |
|---|---:|---:|---:|
| 0 | BPW | chunkCount(2*N,BPW) | 2*N |
| 1..4 | BPW | SUPERSLOTS | SUPERSLOTS*BPW each |
| 5..8 | LOCALWIDTH | LOCALSLOTS | LOCALSLOTS*LOCALWIDTH each |
| 9,10 | LONGW | LR | LR*LONGW each |
| 11 | LONGW | chunkCount(SUPERSLOTS,LONGW)+SUPERSLOTS+1 | SUPERSLOTS |
| 12 | BPW | LONG*SS | LONG*SS*BPW |
| 13,14 | SPARSEW | SR | SR*SPARSEW each |
| 15 | SPARSEW | chunkCount(SPARSESLOTS,SPARSEW)+SPARSESLOTS+1 | SPARSESLOTS |
| 16 | LOCALWIDTH | SPARSE | SPARSE*LOCALWIDTH |
| 17 | BPW | RS | RS*BPW |
| 18 | RANKBLOCKWIDTH | RB | RB*RANKBLOCKWIDTH |
| 19 | BPW | chunkCount(2*N,BPW)+2*N+1 | aliases segment0 |
| 21 | FW | FC | FC*FW |
| 22 | SW | SC | SC*SW |

Here `FC=(1<<C)*(C+1)*(C+1)`, `FW=mb((2*C+1)*(2*C+2)*(C+1))`, `SC=(1<<C)*(C+1)`, `SW=mb(C+1)`. Source: `PCP/SourceGeometry.lean:29-130`, `SourceWords.lean:586-599`, `:759`; reviewer overrides the sparse-relative capacity with the actual `SPARSE` row count at `ReviewerPhysicalRead.lean:85-99`. Shared table geometry is `ReviewerCloseRead.lean:200-213`.

Storage order of the eighteen access components is:
`17,18,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16`.
Each access component starts after the BP prefix of `2*N` bits and the stored-bit sum of preceding access components. Segments0 and19 both start at payload bit0; segment19's empty sentinels are logical objects with no separately stored bits.

Let `ACCESS=sum(access stored bits)` and `INTERIORBITS` be the n-only raw directory bit count below. Payload-relative bases are:

```text
base(0)=base(19)=0
base(access segment)=2*N + its preceding access bit sum
base(20)=2*N+ACCESS
base(21)=base(20)+INTERIORBITS
base(22)=base(21)+FC*FW
```

For non-interior logical read `(s,i)`, first reject `i>=rows(s)` as logical none with **zero physical probes**. Otherwise `len=min(stride,bits-i*stride)`; this can be zero for present sentinels. Compute absolute bit address `a=W+base(s)+i*stride(s)`; the extra `W` is the header cell.

- `len=0`: return present empty bits (tag1), no physical probe.
- Otherwise `cell=a//W`, `off=a%W`. Probe `cell`, then probe `cell+1` iff `off+len>W`.
- Decode the requested little-endian span from those returned cells only. For one cell use `(lo>>off)&((1<<len)-1)`. For two, combine the low fragment with the needed low bits of the second cell; mask before shifting to avoid a needless `2*W`-bit intermediate.
- Return decoded value+1. Every attempted physical probe is counted, including failure. Do not cache or merge repeated loads if exact trace equality is the target.

These are `PCP/ReviewerClosedGeometry.lean:49`, `:173`, `:182`, `:245-314`, `ReviewerProbe.lean:108`, `:406`, and `ReviewerLogicalLowering.lean:216-287`.

**Affine dependence:** every base is `a(N)+b(N)*LONG+d(N)*SPARSE`. Segment12 contributes `LONG*SS*BPW`; segment16 contributes `SPARSE*LOCALWIDTH`; all remaining bits and widths are n-only. Consequently this mapping needs a fixed branch tree and scalar arithmetic; no source-list scan is needed at query time. `ReviewerClosedGeometry.lean:197` equates this closed map to the old prefix-sum map.

## Segment20 geometry and raw interior length

This supplies the physical mapper for the close side while its logical navigation is handled by the other leaf. Set:

```text
B=mb(N); blocks=N//B; superCount=blocks//B+1
RW=2*mb(B)+3; M=B*B; macroCount=blocks//M+1
OW=mb(M); GL=mb(macroCount); BW=mb(blocks)
LD=M+2; GD=macroCount+2
levelWidth(d)=mb(d*mb(d))
```

The eight components occur in this order, with entry count and entry bit width:

| component | entry count | entry width |
|---|---:|---:|
| baseline | superCount | BPW |
| minRel | blocks | RW |
| maxRel | blocks | RW |
| argOffset | blocks | RW |
| localOffset | macroCount*OW*M | OW |
| globalBlock | GL*macroCount | BW |
| localLevel | LD | levelWidth(LD) |
| globalLevel | GD | levelWidth(GD) |

For each component `c`, let `Kc=ceil(entryWidth(c),BPW)`, `words(c)=entryCount(c)*Kc`, and `bits(c)=entryCount(c)*entryWidth(c)`. Logical component bases are prefix sums of **words**; physical component bases are prefix sums of **bits**. Do not multiply the logical index by BPW across ragged entry boundaries.

Classify segment20's index into those eight word intervals; an index at/beyond the total word count is none with no physical load. In a component with local word index `j`:

```text
entry = j//Kc; chunk = j%Kc
len = min(BPW,entryWidth(c)-chunk*BPW)
a = W + base(20) + precedingComponentBits
      + entry*entryWidth(c) + chunk*BPW
```

Then execute the same one/two-cell decode. `INTERIORBITS=sum(bits(c))`.
Sources: `PCP/ReviewerInteriorRead.lean:41-70`, `:111`, `:146`, `:186`; `ReadProgram.lean:1231`, `:1255`; `RMQ/Core/SuccinctClose/RelativeSummary.lean:1285-1308`; `EndpointFringe/PrefixRange/SparseLevelTable.lean:41`, `:150`; `EndpointFringe/InteriorCandidate/InteriorDirectory/ValueDependency.lean:470-487`. Every number in this component classifier is n-only, so the eight-case classifier may compile to a fixed branch tree.

## Prelude popcount: the remaining instruction-bound issue

After probing header cell0 to obtain `LONG`, the sparse prelude reads the source words for segments13,14,15, in that order, all at `i=SPARSESLOTS//SPARSEW`. Their physical addresses depend on `N,LONG` only. Let `t=SPARSESLOTS%SPARSEW`; its decoder is:

```text
SPARSE = (decode(superReply)+decode(blockReply)
          + popcount_true(flagReply below min(t,flagReplyLength))) * LS
```

This is literal `packedReviewerSparseCountFromReplies`, `PCP/ReviewerSparsePrelude.lean:197-215`. A direct shift-and-test loop over those `t` bits is executable and oracle-free, but has up to `SPARSEW-1=O(log N)` iterations. A fixed physical width used in a finite experiment caps it only for that width; it does not establish an all-size constant instruction count. The precise static condition needed to bound this particular loop by a universal literal is a universal bound on this remainder, or a replacement with a proved uniformly bounded routine. No such remainder bound or replacement was reconstructed here.

The existing E1 true-rank loop is useful **after** the prelude: `RMQ/Core/WordRAM/E1RankTrueBlock.lean:47-70` has 23 instructions per chunk (24 including its back-edge), and `:460` proves the chunk-fold simulation. But it contains a table read at `:59`; it is not a table-free population-count implementation. The false loop `E1RankBlock.lean:148-175` analogously has 24 body instructions. Their literal eight-chunk cap depends on the shared fringe table already being addressable.

Using segment21's existing table to bootstrap the prelude is circular under this memory layout: `base(21)` includes `SPARSE*LOCALWIDTH`, and `SPARSE` is what the prelude is computing. The two sampled rank entries supply counts at a word boundary, leaving exactly the residual prefix in the final flag word; they do not simply supply a terminal full-prefix sample.

This is an identified obstruction to a shortcut proof, not a lower bound on all possible arithmetic programs. A new proved arithmetic population-count routine, a different bootstrap table placement, or additional explicitly accounted metadata could change the situation. Each would be an additional refinement or representation decision. Treating population count as one instruction strengthens the ISA; the existing `E1Machine.Instr` list at `E1Machine.lean:77-103` contains no such primitive.

## Limits and proof digestion

The source reconstruction shows how both rank and select can be implemented using only endpoints, n-only constants, and returned memory words. No query-time shape, input-list lookup, list-valued semantic register, or answer oracle is needed. The read structure is preserved even in awkward empty and missing-logical-word cases. The companion is an implementation candidate, not kernel-checked correspondence evidence; the lead's compiler/VM fixture comparisons provide separate finite evidence.

For an all-size theorem the live obligations are: correctness of compilation and physical reads; correspondence of each decoded word length to its geometry; termination and a numerical instruction measure; bounds on every register/intermediate and program-counter constant; and the prelude's width-dependent population count. Numeric reply tagging requires at least W+1 register bits even when memory cells have only W bits, because an all-one W-bit cell decodes to tag `2^W`. That alone does not bound every address/intermediate. Fixed-width test success must not be promoted to an arbitrary-size overflow theorem.

The skeptical next question is precise: can a whole-machine simulation preserve the candidate's actual attempted physical trace while accounting for every arithmetic instruction, and what bound does that machine really satisfy as N grows? This leaf supplies source and geometry for that test; it does not claim a uniform word-RAM time theorem.

