# BV-1 contract and approved route

Phase: implementation; status INCOMPLETE. The complete target remains
`RMQ.PackedBitvector.fullyChargedBitvectorCapstone_holds`. No row of the frozen
matrix is closed by this document. Source facts are at baseline
`0e6a00f654abc64f8b68988fa9675b9a839dca2f`; new code is an unverified experiment
until its command results are recorded. The coordinator approved this route at
evidence commit 645a0502b9da9ad6444edbe44759e1c2c5661f25; the route review is
discharged. Its preserved disposition is COORDINATOR_ROUTE_DISPOSITION.md.

## Operation conventions and quantifiers

For every `bits : List Bool`, `target : Bool` and `argument : Nat`:

- Access at `i` returns `bits[i]?`; zero-based, absent when `n <= i`.
- Rank at prefix `p` counts target bits in `[0,p)`. The machine/API guard
  rejects `p > n`; the independent semantic rank saturates there, so the
  public result is `if p <= n then some (Succinct.rankPrefix target bits p)
  else none`. Prefix zero and prefix n are valid, also for n=0.
- Select at `k` returns `Succinct.select target bits k`. Occurrences and
  returned positions are zero-based; k=0 is the first occurrence and
  `occurrenceCount bits target <= k` returns none.

Natural API wrappers guard unbounded inputs before encoding. Physical-run
statements cover all representable machine arguments, including representable
invalid ones. Every valid argument fits; no readiness assumption is permitted.
Option-natural packets use zero for absence and value+1 for presence. Access
uses an explicit Boolean-result encoding. Each capstone field quantifies the
same guarded or representable domain as its actual execution object.

## Proposed representation and source

The experiment stores the raw bitvector once, select-directory components for
false and true, and shared rank/select chunk tables. A prefix contains charged
numeric geometry and two banks of regular segment descriptors. It serializes
the body densely using the existing `PackedWordRAM.denseWords`, with one
physical width. The first select experiment uses 23 scalar words and two banks
of 23 four-word descriptors, for 207 header words. Access/rank components are
still to be added to the final allocation; 207 is not a final capstone constant.

Select source is the existing `PackedWordRAM.selectCloseBlock physicalReader`.
No copy or edit of that source is made. The custom reader loads its descriptors,
uses `regularLocateBlock 8200` and `spanBlock 8256`, and returns the existing
numeric packet/length convention at registers 8194/8195. It uses the current
`Structured.Block.compileAt` and the actual primitive `run` (through the proved
`runArray_toArray` equality in executable checks).

The input target is encoded in register 3; occurrence is in register 512.
Charged metadata supplies the chosen occurrence count to register 16, while
length-based geometry is kept independent in registers 24..34. Input-dependent
counts, addresses, strides, exceptional lengths and tables are memory data,
never specialized program constants. Source and compiled code are fixed.

Only segment 0 data replies are normalized: `normalize b xs = xs.map
(fun x => x != b)`. For target=false this is identity; for true it complements
within the actual logical word length. For a present raw word of value v and
length len, the true-target packet is `2^len - v`; absence remains packet zero.
Long/sparse flag words (segments 11/15) remain unchanged because the shared
controller ranks true flags. Shared table 22 selects false normalized bits.
Directory metadata/offsets still belong to the original target.

The initial width candidate is `W n = 32 + 16 * machineWordBits n`.
The chunk width is `c n = bpFringeChunkBits (2*n)`, allowing direct reuse of
existing LittleOLinear table envelopes. The floor handles code/scratch even at
n=0. No safety or width theorem for the experiment is asserted yet.

## Exact reader bridge signature to implement

The following definitions now elaborate in ReaderInterface.lean; they are
propositions awaiting proofs, not established correctness theorems. Their
specification objects are proof-side parameters; `reader : Block` has no
semantic-store callback. GenericReaderMetadata fixes register3 to target.toNat
and register22 to the declared width. The larger controller metadata obligation
is separate. genericReaderReceipts includes descriptor loads before span loads.

```lean
def GenericReaderCorrect (bits : List Bool) (target : Bool)
    (mem : Memory) (reader : Block) : Prop :=
  forall regs, GenericReaderMetadata bits target regs ->
    let actual := reader.eval mem (Data.mk regs .running)
    let expected := genericLogicalWord bits target (regs 8192) (regs 8193)
    actual.final.status = .running /\
    actual.final.regs 8194 = readerPacket expected /\
    actual.final.regs 8195 = readerLength expected /\
    actual.reads = genericReaderReceipts bits target mem
      (regs 8192) (regs 8193) /\
    GenericReaderFrame regs actual.final.regs

def CanonicalGenericReaderCorrect : Prop :=
  forall (bits : List Bool) (target : Bool),
    GenericReaderCorrect bits target (Experiment.memory bits) Experiment.physicalReader
```

Final bridge proofs must cover missing/empty logical words separately. For
absent logical spans there are descriptor reads but no payload load; a present
zero-length word returns packet1, also with no payload load. Out-of-allocation
primitive loads retain failed receipts and fault. Successful canonical
operations must prove they never fault. For arbitrary supplied memory,
`run_eq_of_agree` supplies same-run result/cost/ordered-trace agreement from
agreement at attempted addresses, including missing replies.

The independent route review identified two specific boundaries. The expected
receipt specification uses canonical descriptors and is not an arbitrary-memory
fault specification: empty memory faults on the first descriptor read, whereas
the expected prefix lists four. Only the canonical memory is quantified in
CanonicalGenericReaderCorrect. Fault controls and supplied-memory agreement
must describe actual executions directly.

Also, a descriptor using first-word length is not valid for an arbitrary bounded
array: `[[], [true]]` loses its second word. Prove regularity for each canonical
chunk/sentinel/fixed-width builder, including a short first word and all empty
sentinels. Mere word-length bounds plus erasure are insufficient. This is a
proof obligation of the chosen layout, not a target impossibility.

An exact physical-reader safety theorem must use the same allocation, layout,
width and target. It derives strict span length `< W`, position/address bounds,
all scalar intermediate bounds and all-prefix safety, and does not assume the
eventual capstone's safety proposition.

## Space proof plan with exact identity obligations

`jacobsonClarkRankSelectOverhead n` is rank overhead plus two canonical
select overheads; its LittleOLinear theorem already exists. It is an abstract
profile, so it supplies component space bounds only.

For each target-specific directory d, selected physical segments 1..16 omit
the false sample tables for long/sparse flag rank. Their bit concatenation is
not definitionally d.payload. Prove:

```text
selectedSegmentBits.length + longSuperFalse.payload.length
  + longBlockFalse.payload.length + sparseSuperFalse.payload.length
  + sparseBlockFalse.payload.length = d.payload.length
```

Use each table's `store.payload_eq_words_join`, the flag stores' erasure to
their flag lists, and `d.payload_length_le_canonical`. Establish each target's
bound separately. No second copy of the raw n-bit input is permitted. A
length-equivalent reordered payload is adequate for the bound only after each
descriptor's exact subrange is proved to recover its source words.

The final body additionally counts rank directories and the common chunk rank
and false-select tables. Use `bpFringeTableOverhead` and
`bpChunkSelectTableOverhead` at the selected c. Dense-packing capacity adds at
most one W-bit cell; metadata and every literal encoded program word plus the
finite retained scratch bank add a constant times W. The final rho is a sum
of these checked LittleOLinear functions, with the leading n coefficient
preserved. Program words and scratch for all three supported operations count
together; operation-specific capacities on sibling allocations do not compose.

## Source and proof joins

The generic `packedSelectCloseRead` already takes target, occurrence count and
all geometry as data. Its equality to
`SparseExceptionSelectData.bpChunkedSelectTraceResultWithStore` is definitional.
`bpChunkedSelectCosted_erase` gives independent select semantics under positive
c and three word-size bounds <= 8*c. The new proofs must transport this generic
algorithm through normalization and the actual primitive reader. Shape-indexed
`SelectProof`/`ReaderCorrect` theorems are not applicable as final premises.

Independent leaves: semantic normalization (worker-owned); generic component
serialization/space; reader/frame/metadata reconstruction; generic controller
source refinement and safety. Lead owns representation/source identity,
capstone, exact-type consumers, validation, replay, ledgers and integration of
leaf proofs. At most one Lean/Lake command runs in this tree.

## Feasibility evidence and route review

Before making this route final, run full physical select on empty, singleton,
size-two, equal/alternating/mixed inputs, both target bits and invalid
occurrences. Preserve actual receipt crossings, not just expected semantics.
Parameterized well-formed directory fixtures must cover long and sparse
exceptions. Canonical-global rare cases not reached by finite fixtures remain
universal-proof obligations.

The route review consumes that execution evidence, the exact reader signature,
component erasure facts and width/safety obligations above. It may request
repairs; it does not authorize weakening any frozen row. The PRE-specific
builder contract gate is owned by PRE's separate task; this lane implements no
PRE builder. No full aggregate slot has been requested or used at this phase.
