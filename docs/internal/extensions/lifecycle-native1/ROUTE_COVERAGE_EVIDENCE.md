# LIFE-NATIVE-1 finite route-label evidence

This bounded N1-17 review interprets the actual completed 13-fixture run; it
does not certify the whole native campaign. Governance preflight passed at
`7b227c49ef2ec044b702126cc41c9add847eed01`, with `rmq-proof-sprint`, on checkout
`3dbdebedcc6ba6b2a864df0d46dcc09ccaaa7536` plus the current implementation.
This documentation leaf edits only the three assigned native evidence documents.
No compiler or native process was run. Verification consists of source tracing, receipt arithmetic, ordered-read
checks, source hashes and whitespace checks. Broad builds belong to the lead.

The frozen requirement says: "actual same-block, different-block/fringe/interior/crossing-cell
query paths when reachable" and "Record actual route coverage or a precise
absence, not guessed labels." This document supplies the finite route part;
input-domain coverage and independent expected answers remain in the registry
and its separate review.

## Producing evidence and exact counters

Receipt directory:
`.lake/lifecycle-native1/replay/20260927T064849543-b1d28b93/`.
`RESULT.json` reports success for 13 fixtures and 26 observed/unobserved
processes. The current secondary review at
`.lake/lifecycle-native1/native-refresh-review/secondary-20260927/FIXTURE_REVIEW.json`
records 71 requests per mode and 142 actual requests, checks each frozen packet
against an independent leftmost minimum computation, and redoes the ordered-read
and interior-occurrence arithmetic below. Its SHA-256 is
`bbeb482b4a3b12a11f07c294de4158754ef172ad972554826393728272dac1c7`.

Every non-pointer field of all 26 current reports equals the corresponding
historical report at `replay/20260927T045754455-9f927669`. Python preserves all
integers exactly. Only the two program and four owner-bank address fields are
normalized: each program root is nonzero and distinct; each concurrently live
set of four owner banks is nonzero, distinct and disjoint from the programs.
Raw addresses remain in the pinned reports. Reuse after a prior generation is
freed is not a live alias and is not treated as an invariant across processes.
The current DLL source/artifact chain is `build-20260927T063830290` through
client producer `build-20260927T064222779`, detailed in
`COMPILED_ROUTE_EVIDENCE.md` and `NATIVE_EXECUTION_EVIDENCE.md`. The source
producing the DLL is bound by these receipts, not by checkout HEAD alone.

The checked observed reports all give signature counts 1, 1, 1, 1, 110, 193
for IDs 7 through 12. The first two pairs count the same instruction with
opposite prestate predicates. The native client checks uniqueness for 7–10,
but only nonzero occurrence for 11–12
(`native/packed-rmq/tests/lifecycle_owner.c:356–366`). Neither of the latter
signatures is unique.

| Fixtures | Same close block (7) | Different close blocks (8) | Nonempty middle (9) | Empty middle (10) | Segment-20 selection (11) | Second physical load (12) |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| LN1-W-EMPTY / LN1-C-EMPTY, each | 0 | 0 | 0 | 0 | 0 | 0 |
| LN1-W-SINGLE / LN1-C-SINGLE, each | 3 | 0 | 0 | 0 | 0 | 0 |
| LN1-W-TWO / LN1-C-TWO, each | 3 | 0 | 0 | 0 | 0 | 3 |
| LN1-W-TIES / LN1-C-TIES, each | 1 | 3 | 0 | 3 | 0 | 0 |
| LN1-W-N24 / LN1-C-N24, each | 1 | 6 | 5 | 1 | 90 | 11 |
| LN1-W-N83 / LN1-C-N83, each | 1 | 6 | 5 | 1 | 90 | 9 |
| LN1-C-WIDE-PAD | 2 | 2 | 0 | 2 | 0 | 0 |
| Total | 20 | 32 | 20 | 12 | 360 | 46 |

The observations are per request; summing them once produces this table.
Request 0 includes construction and the first query. Later requests contain
only their service/query segment. These are dynamic occurrence counts, not
numbers of distinct PCs, payload cells, fixtures or all reachable routes.

## Source-to-label connection

Paths in this section are relative to `RMQ/Core/WordRAM/` unless specified.
The actual service prefix uses `compactQueryProgram`
(`Lifecycle/Service.lean:24–27`), built from the packed `querySource`
(`Optimization/Query.lean:16–19`). `Optimization/Compact.lean:41–58` preserves
action instructions and compiles source branches and repetitions. The packed
query composes select-close operations, LCA and final rank
(`Packed/QuerySource.lean:24–56`). Thus the operands below are close-position
and packed-reader registers, not the user's input-array indices directly.

**Same/different close blocks, and fringes.** The unique
`.comparison .eq 1215 1203 1204` comes from
`Packed/FringeSource.lean:172–175`: register 1203 is close1200 / register33,
and 1204 is close1201 / register33. Register33 is metadata field17, the
packed interior block size (`Packed/Allocation.lean:105–117`;
`Packed/ReadInterface.lean:21–22`). The observation predicates additionally
require PC < 212964 and equality/inequality of those two prestate registers
(`Native/Lifecycle/Observations.lean:122–125,133–145`).

The source immediately selects `lcaSameBlock` for equality and the cross
program for inequality (`FringeSource.lean:181–187`). The same-block arm runs
`fringeBlock` at 130–134. The cross arm runs the left fringe, middle and right
fringe in sequence (136–170). Therefore, on these completed successful
canonical query routes, the decisions substantiate same-close-block fringe
execution and different-close-block execution with both fringe arms. They do
not count individual fringe-table reads or identify a particular logical
fringe request in the exported read list.

For reference, `Packed/LCAProof.lean:89–94` proves the initializer's actual
final registers equal the two divisions and its comparison result is their
equality test. At 649–658, `lcaCloseProgram_source`, under `ReaderCorrect`,
`ReaderWrites`, `InteriorCandidateCorrect`, the interior write frame and
`MetadataMatches`, concludes for the same evaluation:

```lean
actual.final.status = .running ∧
actual.final.regs 1202 = optionNatPacket expected.value ∧
actual.reads = logicalTraceReads shape memory expected.trace ∧
ReadOnlyTrace expected.trace
```

**Nonempty/empty middle.** The unique `.comparison .lt 1215 896 1204`
follows `896 := 1203 + 1` (`FringeSource.lean:144–146`). Its branch skips the
interior candidate for false and calls it with count `1204 - 1203 - 1` for
true (148–154). `LCAProof.lean:304–308` proves the comparison result is
`if regs 1203 + 1 < regs 1204 then 1 else 0`; the source theorem at 378–385
joins the same middle computation's candidate and ordered reads to its
reference trace. The native predicates use the actual prestate inequality
(`Observations.lean:126–129,147–159`). These labels mean a nonempty/empty
interval of complete BP blocks between the two close blocks. They do not
mean that the entire input query is nonempty/empty.

Both models' size-24 requests 1, 2, 3 give useful concrete witnesses:
`[0,3)` has counters 7–12 `[1,0,0,0,0,0]`; `[0,5)` has
`[0,1,0,1,0,1]`; `[0,10)` has `[0,1,1,0,18,2]`. All independently expected
packets are 1. Size-83 requests 1, 2, 3 similarly use `[0,3)`, `[0,7)`,
`[0,14)` with counter vectors `[1,0,0,0,0,0]`, `[0,1,0,1,0,0]`,
`[0,1,1,0,18,1]`.

**Counter 11 is not a physical-read counter.** Its entire predicate is
PC < 212964 and `.constant 8192 20`
(`Observations.lean:130–131,161–164`). This sets the reader's segment selector
in `interiorReadAddress` (`Packed/InteriorSource.lean:33–37`), followed by a
reader invocation at 47–49. The same constant also occurs in the explicit
out-of-range arm at 62–64. `Packed/Locate.lean:474–481` dispatches segment20
to the interior components. But `Packed/PhysicalRead.lean:34–36` can return
from a missing span without a load; a zero-length span also performs none.
`ReadInterface.lean:38–52` states this distinction explicitly. Accordingly,
360 means executed segment20 selections, not 360 successful payload loads,
360 distinct interior entries, or even 360 nonempty logical spans.

**Crossing-cell loads.** `Packed/PhysicalRead.lean:19–36` invokes
`spanBlock 8256` with width in8256, shifted bit position in8257 and length
in8258. At that base, the crossing arm's `.load (base + 10) (base + 5)` is
exactly `.load 8266 8261` (`Packed/SpanAssembly.lean:31–54`, especially45).
The arm is reached only after the first successful load and the comparison
`position % width + len ≤ width` is false. It increments the first cell
address and loads the next physical cell. The 193 static occurrences are
copies of this reader operation in the fixed query, not 193 distinct kinds
of crossing. The source theorem `spanBlock_source` at 72–78 gives both
`SpanOutcome base (decodeSpanNat width position len memory) actual.final`
and `actual.reads = spanAttemptReceipts width position len memory`; that
receipt definition at 18–27 preserves the first and second attempts in order.

Counter12 alone says that instruction was attempted; successful completion
and successful read receipts are needed to say it completed. They hold here.
Thus 46 is supported as second-cell load occurrences on actual crossing
routes. It is not a count of distinct cell pairs, and it does not identify
which segment crossed. Arbitrarily picking adjacent addresses from `readsLE`
would not supply that missing segment attribution. These receipts do not
export PC/segment/index annotations for each read.

## Direct interior payload occurrences

This review independently decoded all 10,480 read/reply pairs from requests
after request0 across the 13 observed reports. Every reply was present and
equal to the corresponding `memoryLE` cell. Of these pairs, 3,288 have an
address at least174. The native client already enforces this same backing
predicate at `lifecycle_owner.c:428–434`. The first construction/query
segment cannot generally be checked against final memory this way because
its memory changes during construction; it is not included in these totals.

More specifically, each interior descriptor has five fields
`[wordPrefix, wordCount, bitBase, entryWidth, chunksPerEntry]`
(`Packed/Allocation.lean:78–89`). The descriptors occupy memory134..173,
after42 scalar and92 regular-descriptor cells (123–128). Their actual
contiguous bit intervals are disjoint from every nonempty regular-segment
interval in these two fixtures. Full physical cells strictly contained in
their union therefore hold interior payload throughout; this does not rely
on the marker count. The physical reader's174-word shift is at
`PhysicalRead.lean:19–24`.

| Both word and comparison report | Request index / endpoints | Interior bit interval before header shift | Word width | Whole cells inside interval | Actual zero-based read-list occurrences |
| --- | --- | --- | ---: | --- | --- |
| LN1-*-N24-observed1.json | 3 / `[0,10)` | `[1100,2067)` | 184 | 180..184 | 234 and235 read184; 236 reads180 |
| LN1-*-N83-observed1.json | 3 / `[0,14)` | `[4779,7328)` | 200 | 198..209 | 247 and248 read208; 249 reads199; 251 reads198 |

The size-24 read184 reply is the little-endian magnitude
`04047474e8e8e8e86465656565656565f1f1f1f1f1f1f1`; read180 is
`c8902143468d1a356a0030a000000862`. Both repeated read184 occurrences are
retained, with their separate positions. Size83 read208 is
`000000000000001020408d1a6ad4a851132a54a850a142850a`.
These are actual interior physical payload reads in the successful queries.
This interval argument does not reconstruct the logical index or establish
that every marker corresponds to one physical read.

The checked observation bridges preserve these distinctions:
`Observations.run_route` (383–385), `buildFirst_route` (519–521) and
`query_route` (602–604) identify route counters with
`transitions.countP (routeMarked mark)` for the same execution.
`run_reads` (378–381), `buildFirst_reads` (513–517), and `query_reads`
(597–600) identify the ordered read list. `read_occurrence_output`
(414–422) preserves the split at a producing transition and its prestate.
Their conclusions do not add a semantic segment label to the native JSON.

## Reproduce the receipt arithmetic without executing the native program

Run the following Python from the repository root. It only reads existing
evidence, sums the source-defined counter IDs, checks later-query backing,
and verifies the interior intervals and named occurrence positions.

```python
import json
from pathlib import Path
b = Path('.lake/lifecycle-native1/replay/20260927T064849543-b1d28b93')
reg = json.loads(Path('scripts/lifecycle_native_cases.json').read_bytes())
dec = lambda s: int.from_bytes(bytes.fromhex(s), 'little')
totals, later, payload = [0] * 13, 0, 0
for name in reg['orderedIds']:
    doc = json.loads((b / (name + '-observed1.json')).read_bytes())
    assert {k: dec(v) for k, v in doc['signatureCountsLE'].items()} == {
        '7': 1, '8': 1, '9': 1, '10': 1, '11': 110, '12': 193}
    for r in doc['requests']:
        totals = [a + dec(v) for a, v in zip(totals, r['observations']['routesLE'])]
        if r['index'] == 0:
            continue
        m = list(map(dec, r['memoryLE']))
        for z in r['observations']['readsLE']:
            a = dec(z['address'])
            assert z['reply'] is not None and a < len(m) and dec(z['reply']) == m[a]
            later += 1
            payload += a >= 174
    if name.endswith(('N24', 'N83')):
        r = doc['requests'][3]
        m = list(map(dec, r['memoryLE']))
        ds = [m[134 + 5*t:139 + 5*t] for t in range(8)]
        assert all(d[1] % d[4] == 0 for d in ds)
        spans = [(d[2], d[2] + (d[1] // d[4]) * d[3]) for d in ds]
        assert all(spans[i][1] == spans[i+1][0] for i in range(7))
        start, end = spans[0][0], spans[-1][1]
        for seg in range(23):
            d = m[42 + 4*seg:46 + 4*seg]
            assert d[1] == 0 or d[0] + d[1] <= start or end <= d[0]
        cells = range(174 + (start + m[6] - 1) // m[6], 174 + end // m[6])
        expected = ([(234,184), (235,184), (236,180)] if name.endswith('N24')
                    else [(247,208), (248,208), (249,199), (251,198)])
        for index, address in expected:
            assert address in cells
            assert dec(r['observations']['readsLE'][index]['address']) == address
assert totals == [637553,284,587241,493168,143,118513,507,20,32,20,12,360,46]
assert (later, payload) == (10480, 3288)
print('PASS: route totals, signatures, ordered backing and interior occurrences')
```

## Limits and disposition

The recorded finite routes cover both same/different close blocks, both
fringes on cross routes, nonempty and empty middle decisions, actual interior
physical payload reads, and successful crossing-cell loads in both models.
There is no claim that every interior subroutine arm or every logical segment
crossed. The tested size24/83 layouts have fewer blocks than their macro size;
this evidence is not coverage of a multi-macro interior route.

For more specific labels such as "this crossing belongs to segment20/indexK"
or a claimed one-to-one marker/read relationship, the missing evidence is an
occurrence-preserving connection from the actual reader invocation and its
prestate segment/index/span to the indexed native read pair. The current
aggregate counters and unannotated read list do not provide it. No such finer
label is used here. Compiler/FFI/runtime correctness and the build-to-DLL
binding remain operational assumptions, separate from kernel facts.

Proof digestion: the useful labels are established by the source's tested
branch conditions and successful execution. Interior loads additionally have
direct allocation-and-reply evidence. Counter11 must retain its narrower
meaning. A skeptical reader can reproduce the finite receipt checks above;
the next stronger question would require per-invocation read attribution.
No new design or process decision was made.

## SHA-256 identities

Paths under the receipt directory use the prefix `receipt/` below. These are
raw-byte hashes, not claims that the uncommitted implementation equals HEAD.

| Path | SHA-256 |
| --- | --- |
| `receipt/RESULT.json` | `02060b1e4615bcb812bafff8794341271257eb447625dcfdcd62b7a319b36493` |
| `.lake/lifecycle-native1/native-refresh-review/secondary-20260927/FIXTURE_REVIEW.json` | `bbeb482b4a3b12a11f07c294de4158754ef172ad972554826393728272dac1c7` |
| `receipt/LN1-W-N24-observed1.json` | `a8d8cf2b9621148b2f11741dc62c0a097515f6af9013f5c35d7b8678f0265944` |
| `receipt/LN1-C-N24-observed1.json` | `e49d9b7a4879b83b551dae51431e0cf2b6710b35177dd5acdbdacfdc1d6e04b7` |
| `receipt/LN1-W-N83-observed1.json` | `91246a53ce96ca953b5de190c387a1a09bea38a256e33045f813ef900a333ac8` |
| `receipt/LN1-C-N83-observed1.json` | `63a7aa6de731c9b6f5c43ec57898d7cd11e9ff54a09eaed456af535f19fedcc2` |
| `scripts/lifecycle_native_cases.json` | `9dc72366b51592f18dc50e52d2b799c736dc047e6166538a0a880192062985fd` |
| `native/packed-rmq/tests/lifecycle_owner.c` | `0cd522806030bddb51be7f55b4b8c006612c59a3d168815accfa34b9ad635ded` |
| `RMQ/Core/WordRAM/Native/Lifecycle/Observations.lean` | `1216fe255e14175f2ee67b2c77c28cdb0509606c3be4b0063fd22d39867dbb96` |
| `.lake/build/ir/RMQ/Core/WordRAM/Native/Lifecycle/Observations.c` | `c62c6056c651ff833df6acda2c156724579d98c4fbe3c577aa7f39d9f54a63ec` |
| `RMQ/Core/WordRAM/Packed/FringeSource.lean` | `bc779a746a938c7b10fdb4b93c84003e9ca91d27fb3a3813abdf5944920b96c2` |
| `RMQ/Core/WordRAM/Packed/LCAProof.lean` | `281f6c63fda95699292eb9eed87dcf362d3ec549d99cbcb5a0a0cffe0cfff058` |
| `RMQ/Core/WordRAM/Packed/InteriorSource.lean` | `656c25cffd3d7bec326ca03c9e068250b9287402aaf6091e71e5a234c0879949` |
| `RMQ/Core/WordRAM/Packed/SpanAssembly.lean` | `ea0b7ca706c9750a6e0cdf6220f5f8b411a54cec33cfaddded4f010020239106` |
| `RMQ/Core/WordRAM/Packed/PhysicalRead.lean` | `49c9ce18f81b0b7a00e96c0e32f12121ee27401412146752db845ce22581558f` |
| `RMQ/Core/WordRAM/Packed/ReadInterface.lean` | `75509f98331eb79e87809851b1bfb340bc3157e4482405f9f47d1d49a7c1ea87` |
| `RMQ/Core/WordRAM/Packed/Allocation.lean` | `7fdc39400ff3ab877becd63d2e367e24ace0c71f373c7f54017039ee578e7d49` |
| `RMQ/Core/WordRAM/Packed/QuerySource.lean` | `dfcb57325902a1eebafabcf24fc5437aed88a2ea32df416b5cb2bbce98f51415` |
| `RMQ/Core/WordRAM/Optimization/Compact.lean` | `7bde1173b5661a8c68acfd13f5e9911d176cf8e55f7fbd635e8a5e5819c8de17` |
| `RMQ/Core/WordRAM/Optimization/Query.lean` | `1fe89cf2b3f2833c330c91db9c93ea35b6c37a3f98bc85a4b241d6aa63c36c05` |
| `RMQ/Core/WordRAM/Lifecycle/Service.lean` | `f4157493517f232a6a83bb52c87b751f6a0c2c1f9ca9c98fb6cae036542a34e0` |
