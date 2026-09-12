# BV-1 allocation and reader proof development

Status: INCOMPLETE. The full capstone and every frozen acceptance row remain
open. These development results are components awaiting the same-allocation
machine, safety, capacity and public-consumer joins.

## Exact component interfaces

`MemoryLayout.memory_descriptor_field` identifies an actual lookup in
`Experiment.memory bits` at
`23 + target.toNat * 92 + segment * 4 + field` with the selected descriptor
field, for every segment below 23 and field below 4. Descriptors have four
words, each bank has 23 descriptors, and the header has exactly 207 words.
`allDescriptors_getElem!` identifies a component's base with
`207 * width bits.length + componentOffset (allSegments bits) component`.
The offset is the bit length of the preceding actual arrays, not a semantic
address supplied to the source.

`WordBounds.allSegments_word_length_lt` quantifies every word in every retained
array and proves its length strictly below `Experiment.width bits.length`.
`allSegments_firstLength_lt` handles the empty first-word case explicitly.
`SegmentMap.genericLogicalWord_selected` proves, for every segment and index,
that the selected actual array is the logical source, with normalization only
at segment zero. Reserved and outside segments produce absence.

`DescriptorReader.physicalReader_regular_words` quantifies arbitrary numerical
memory, registers, target, word array and base. Its premises are the actual
four successful descriptor lookups, the proved `RegularWords` property, and
the shared `decodeSpanNat` equality for a present index. It concludes the
actual `Experiment.physicalReader.eval` status, normalized packet, logical
length, exact descriptor-prefix-plus-span-attempt receipts, and frame.
The absent-index branch is included. Source safety remains a separate theorem.

These facts join as actual allocation -> installed descriptor -> selected
regular array -> shared dense decoder -> numeric source theorem -> actual
reader evaluation. `ReaderGeometry` and `ReaderProof` are still being checked;
their presence in source is not yet proof evidence.

## Development commands and repairs

All commands use `run_command.ps1`, the pinned direct Lean 4.22 toolchain, one
shared build slot, an owned subprocess and a recorded deadline. Exact commands,
source hashes, output, stderr, exits and duration are in `commands/*.json`.

- `memory-layout-6`: exit 1, 27.857 seconds, 180-second deadline. Two ordinary
  optional lookup/default conversion goals remained in bank selection.
- `memory-layout-7`: exit 1, 71.787 seconds, 180-second deadline. MemoryLayout
  and Allocation built. The dependent first checks identified list membership
  notation, optional lookup rewrite order, Boolean normalization rewrite order,
  and use of Lean's reserved `prefix` token as a binder. No timeout or model
  obstruction occurred.
- `reader-support-8`: exit 0, 25.302 seconds, 180-second deadline. WordBounds,
  SegmentMap, DescriptorReader and Source built, with no local warnings.
  NumericReader's existing standard axiom inventory was replayed by Lake.

The repair check covers changed dependent modules; it is not an aggregate
certification or a repeated full gate. No full build or aggregate slot has
been requested at this development stage.

## Complete allocation and operations

The checked `Allocation` definitions retain the original 35 component arrays
and append four Jacobson rank sample arrays. Each of the two banks has 23
descriptors. Logical 17/18 select the target's super/block sample tables;
logical 19 describes the actual Jacobson sentinel word array over the same raw
bit position as logical zero. Logical 20 remains absent. Thus the raw bit
payload is stored once; the sentinel word count is independent of bit length.
The final header still has 207 words; its newly used scalar slots contain rank
word size and blocks per superblock.

The checked `Source` definitions contain three fixed operation programs, all
using `Allocation.memory`, the existing `Experiment.setup` loads, the unchanged
physical reader and the existing rank/select controllers. Access reads the
sentinel raw view and extracts the requested bit. Rank rejects end positions
greater than length and adds the present-packet tag after the shared rank
controller. Select uses the existing target setup. The API guards
unrepresentable natural arguments; explicit primitive runs remain defined
separately. These definitions have no correctness or safety claim yet.

## Proof digestion

The completed support work separates three issues: what bytes were retained,
which logical word a descriptor denotes, and what the numeric reader actually
does with the replies. The reader now has a reusable proved refinement from
actual successful descriptor/span replies, including empty and absent words.
Canonical span recovery must discharge those premises; the full controller
must then consume this same memory and reader. A skeptical reader should next
ask whether the final rank alias really shares the raw bit range, whether all
nominal sentinel positions fit the declared word width, and whether the final
space sum includes all three programs and the union of their scratch banks.
Those remain explicit full-target obligations.

## Complete-allocation refinement checked in the continuation

The preceding digestion describes the earlier support checkpoint. The later
checked object chain is now:

`Allocation.allSegments bits` (39 components) →
`Allocation.logicalWords bits target segment` →
`Allocation.bankDescriptor_active` → `decode_serialized_view` →
`Allocation.decode_logicalWords` → `physicalReader_regular_words` →
`Allocation.physicalReader_correct` → `Allocation.readerSimulation`.

`CompleteLayout` proves regularity and strict physical word-width bounds for
all 39 actual components. For `activeSegment segment := segment < 23 ∧
segment ≠ 20`, it proves the exact descriptor

```lean
bankDescriptor bits target segment =
  Experiment.descriptor
    (207 * Experiment.width bits.length +
      Experiment.componentOffset (allSegments bits) (physicalComponent target segment))
    (logicalWords bits target segment)
```

and the equality of that view's erased payload to the selected physical
component. Segment 19 uses `jacobsonRankData bits` with its actual empty
sentinels, while its erased payload is the single component zero. Empty spans
perform no payload read even if their nominal position is beyond the body;
the separate numerical geometry target must still bound that position.

`CompleteReader.physicalReader_correct` quantifies over every `List Bool`,
both targets and arbitrary request registers. Its only metadata premises are
`regs 3 = target.toNat` and `regs 22 = Experiment.width bits.length`. On the
unchanged physical reader and **Allocation.memory bits**, it proves running
status, exact logical packet and length, exact ordered actual descriptor/span
receipts, and the reader frame. Segment 20 is absent; requests at segment≥23
produce no reads. The proof derives the successful four-word descriptor
prefix from this same memory and handles out-of-range word indices separately.

The checked `Space.complete_capacity` has literal encoded instruction-list
lengths for all three programs in its proposition:

```lean
((Allocation.memory bits).length +
  ((program .access).map Instruction.encoding).flatten.length +
  ((program .rank).map Instruction.encoding).flatten.length +
  ((program .select).map Instruction.encoding).flatten.length +
  (registerCount + 3)) * Experiment.width bits.length ≤
    bits.length + completeRho bits.length
```

`completeRho_littleO` proves `LittleOLinear completeRho`; `registerCount=8271`.
The proof uses abstract natural arithmetic before substitution. An earlier
version introduced intermediate aliases on only one side of a definitional
equality; Lean then expanded a fixed program during conversion and hit its
recursion limit. Keeping the same literal code-count expressions in
`completeRho` and the theorem resolved that issue without increasing proof
resource limits or changing the counted allocation.

`Metadata` proves that the actual charged setup output has every scalar used
by the shared select reference and the Jacobson rank geometry. Its
`loadedModel_reader` consumes the complete physical reader, and
`selectReference_value` connects those exact loaded fields and the same
read store to `Succinct.select target bits argument`.

Recorded checks after `reader-support-8`:

- `reader-geometry-9`: exit1,72.006s/300s. Initial AllocationLayout passed;
  dependent span and final space arithmetic normalization errors remained.
- `reader-space-10`: exit1,33.182s/180s. Width, CompleteReadStore and
  ReaderGeometry passed; a dependent array rewrite and the final capacity
  conversion remained.
- `complete-layout-11`: exit1,112.42s/180s. Expanded AllocationLayout,
  CompleteReadStore, CompleteLayout and ReaderProof passed. Space alone failed
  in conversion of the fixed code count.
- `complete-reader-12`: exit1,15.44s/180s. The fixed code-count conversion and
  one map-versus-match packet conversion remained.
- `complete-reader-limits-13`: exit1,21.14s/180s. Space, CompleteReader,
  CanonicalLimits and Metadata passed. CanonicalStoreBounds had four ordinary
  no-progress simplification errors. Its claims are pending until a successful
  later check. CanonicalLimits had one unused simp hint, removed afterward.

Every JSON command record pins its own exact source hashes, dirty tree, exit,
deadline, elapsed time, standard output and error. These are development
checks, not a whole-target acceptance or aggregate certification. The frozen
matrix remains byte-identical (SHA256
`80BD59A314FD33D37076802954444DA24F65C87A2A91DE23BC668B6AF9CCEB24`).

The newly checked work means that numeric loads from one counted body recover
the intended logical words for arbitrary input bitvectors. It does not yet
close the full operation/API, all-prefix numerical safety or public capstone.
The next skeptical questions concern the actual charged setup/controller
composition, representable natural input handling, all nominal descriptor
positions fitting the one width, and replayable public consumers.

## Subsequent allocation and compiled-answer checks

The pending `CanonicalStoreBounds` claims above passed in
`operation-joins-15`; the earlier stage14 diagnostic identified the missing
`genericReadStore` unfolding in two logical directory bounds. The canonical
directory packet is at most `2^(2*M+3)`, the shared table packet at most
`2^(M+8)`, and every raw or flag word requested by the generic controller has
length at most `M = machineWordBits n`. `CanonicalLimits` supplies the one
width `W = 32+16*M`, envelope `E = 2^(9+2*M)`, and the required square/cube
arithmetic bounds. See the independently checked canonical-memory and safety
leaf reports for the actual numeric memory, descriptor and whole-execution
composition; those leaves are no longer pending.

`SelectExecution` and `AccessExecution` passed in `operation-joins-20`.
`RankExecution` passed in `operation-joins-29`. Their quantified propositions
have no size, readiness or argument-fit hypotheses: for every input list and
natural argument, the actual `execute` on `Allocation.memory bits` returns
the encoded independent List answer, halts with that packet, places it in
the API's output register, emits the exact ordered setup/controller receipts,
and takes at most `source.size+1` transitions. Access uses register705 and
`((bits[i]?).map (fun b => b.toNat+1)).getD 0`; rank uses register360 and
`if p <= bits.length then rankPrefix target bits p + 1 else 0`; select uses
register513 and `optionNatPacket (Succinct.select target bits k)`. The rank
and select statements quantify both Boolean targets.

The composition chain is explicit: `ChargedSetup.setup_source` and, for
select, `ChargedSetup.targetSetup_source` determine the loaded register state
and actual setup receipts; `loadedModel_reader` connects each generic
controller request to the same numerical memory; the corresponding generic
source theorem supplies the actual controller evaluation; the independent
read-store refinement identifies the List answer; and the shared Structured
compiler theorem yields the actual Packed `run`, halt, register and receipts.
No trace is synthesized or replayed after computing an answer.

Several development checks exposed elaboration problems rather than missing
semantic premises. Stages14/18/19 timed out in Lean's default deterministic
heartbeat budget while converting a concrete select-run projection. Stage20
fixed this with `execute_source_result`, keeping the operation and the output
register abstract during the compiler/state conversion and only then
specializing them. No resource-limit increase is part of the fix. Stages21–24
fixed the rank reader namespace, a parenthesis, metadata register preservation,
the Bool-to-Nat bridge, and the order in which the core evaluation is abstracted.
Stage25 again exposed eager concrete evaluation; stages26–29 made the source
sequence and closed register tests simplify explicitly while retaining an
abstract core, and aligned the prepared length register before applying its
evaluation equation. All failed records remain in the command ledger.

`Observations` passed in stage18: program lengths and source budgets are
132/1450/10030 for access/rank/select; actual category counts partition actual
steps, and each category is at most the corresponding fixed bound. Stage17
was a launcher-path typo and ran no Lean check. The later stage29 API
corollaries still required the same abstract-operation conversion technique;
their final result and the public certificate are recorded separately after
successful checks. No helper or development checkpoint closes the frozen
30-row acceptance matrix.

These results mean that the fixed programs obtain their answers through the
charged numeric reader on the counted allocation for arbitrary lists. The
remaining questions at this checkpoint concern the public API/certificate
consumer, valid exceptional-route fixtures, executable registries and mutation
replay, rather than a correctness or geometry hypothesis left on the machine.

`operation-joins-30` passed `InterfaceProof` in6.86s/180s with no local
warnings. `queryPacket_of_result` performs the guarded-register conversion
while the operation/output register remain abstract; concrete API corollaries
then use the actual execution theorem and a pure packet-decoding equality.
The unbounded-Nat branch uses the proved `bits.length < 2^W` bound to show that
an unrepresentable argument is invalid in the independent List specification.
The exact public equalities are:

```
access bits i = bits[i]?
rank bits target p =
  if p <= bits.length then some (Succinct.rankPrefix target bits p) else none
select bits target k = Succinct.select target bits k
```

The same module proves `execution_eq_of_agree`: for arbitrary supplied memory,
agreement with the counted allocation at every receipt address attempted by
the canonical execution implies equality of the complete actual `run` on
the same program, budget and initial state. Equality includes the result,
final registers, transitions, receipts and all category counts; absent replies
are included in the agreement premise. This is the existing Packed
`run_eq_of_agree` theorem instantiated at the complete construction.
