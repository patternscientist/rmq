# BV-1 numeric reader leaf — frozen contract

Owner: numeric_reader. Base checkpoint: 645a0502b9da9ad6444edbe44759e1c2c5661f25.
Governance: 0e6a00f654abc64f8b68988fa9675b9a839dca2f. Canonical proof-sprint
preflight passed with the actual three-skill RMQ runtime catalog. Write scope is
NumericReader.lean and this record; root owns the canonical instantiation.

The assigned target is a shape-free numeric physicalReader source theorem in
terms of actual descriptor replies and decodeSpanNat, with exact ordered reads,
packet, length and register frame on the same evaluation. It consumes the actual
Experiment.descriptorLoads, regularLocateBlock, spanBlock and finishPacket.
It does not independently close the full BV-1 capstone or its safety/space rows.

Frozen theorem interface before source edits (names are in RMQ.PackedBitvector):

```lean
def numericDescriptorAddress (regs : Registers) : Nat :=
  23 + regs 3 * 92 + regs 8192 * 4
def numericDescriptorReceipts (memory : Memory) (regs : Registers) : List Receipt :=
  (List.range 4).map fun i =>
    ⟨numericDescriptorAddress regs + i, memory[numericDescriptorAddress regs + i]?⟩

theorem physicalReader_outside (memory : Memory) (regs : Registers)
  (outside : 23 ≤ regs 8192) :
  let actual := Experiment.physicalReader.eval memory ⟨regs, .running⟩
  actual.final.status = .running ∧ actual.final.regs 8194 = 0 ∧
  actual.final.regs 8195 = 0 ∧ actual.reads = [] ∧
  GenericReaderFrame regs actual.final.regs

theorem physicalReader_absent (memory : Memory) (regs : Registers)
  (bitBase bitLength stride count : Nat) (segment : regs 8192 < 23)
  (hbase : memory[numericDescriptorAddress regs]? = some bitBase)
  (hlen : memory[numericDescriptorAddress regs + 1]? = some bitLength)
  (hstride : memory[numericDescriptorAddress regs + 2]? = some stride)
  (hcount : memory[numericDescriptorAddress regs + 3]? = some count)
  (absent : count ≤ regs 8193) :
  let actual := Experiment.physicalReader.eval memory ⟨regs, .running⟩
  actual.final.status = .running ∧ actual.final.regs 8194 = 0 ∧
  actual.final.regs 8195 = 0 ∧
  actual.reads = numericDescriptorReceipts memory regs ∧
  GenericReaderFrame regs actual.final.regs

theorem physicalReader_present (memory : Memory) (regs : Registers)
  (bitBase bitLength stride count value : Nat) (segment : regs 8192 < 23)
  (hbase : memory[numericDescriptorAddress regs]? = some bitBase)
  (hlen : memory[numericDescriptorAddress regs + 1]? = some bitLength)
  (hstride : memory[numericDescriptorAddress regs + 2]? = some stride)
  (hcount : memory[numericDescriptorAddress regs + 3]? = some count)
  (present : regs 8193 < count)
  (decoded : decodeSpanNat (regs 22) (bitBase + regs 8193 * stride)
    (min stride (bitLength - regs 8193 * stride)) memory = some value) :
  let len := min stride (bitLength - regs 8193 * stride)
  let actual := Experiment.physicalReader.eval memory ⟨regs, .running⟩
  actual.final.status = .running ∧
  actual.final.regs 8194 =
    (if regs 8192 = 0 ∧ regs 3 ≠ 0 then 2 ^ len - value else value + 1) ∧
  actual.final.regs 8195 = len ∧
  actual.reads = numericDescriptorReceipts memory regs ++
    spanAttemptReceipts (regs 22) (bitBase + regs 8193 * stride) len memory ∧
  GenericReaderFrame regs actual.final.regs
```

No positive length, shape, canonical-memory, Boolean-valued target register or
arithmetic-width premise is introduced. The root's canonical word decoding
consumer must discharge the exact four lookups and decoded premise; bounded
machine arithmetic and all-prefix safety remain separate obligations. The
source theorem admits zero-length present sentinels and uses the decoder's
actual early-stop receipt sequence. Failed descriptor replies are outside the
successful-descriptor theorem, not silently replaced by a canonical transcript.

Acceptance mapping: REQ-BV-REUSE and the source leaves of REQ-BV-RUN,
INV-TRACE-EXECUTION, INV-STORE-IDENTITY, INV-READ-BACKING and INV-VALUE-DEPENDENCY.
The whole-client matrix remains frozen and is consumed by the root. The
non-synthetic challenge is to change a successful descriptor or payload reply:
the assumptions and resulting numeric packet/read addresses must change with
that exact supplied memory. Empty memory cannot satisfy the four successful
lookup premises. Packet normalization reads segment/target and the actual
decoded value; no logical word or proof answer is an executable input.

Verification plan: one-job bounded narrow module check after the root grants
the shared build slot, then exact-type consumers and relevant axiom inventory.
Use unique numeric-reader-* command records through run_command.ps1. Closest
warm module checks were 8–19 seconds; initial deadline 180 seconds. This leaf
does not run a full aggregate gate; root coordinates the final candidate gate.
Read-only static hygiene and diff checks do not consume the Lean build slot.

## Evidence (append-only)

Implementation and checked results pending.

2026-09-12 development evidence (Windows, exact checkpoint HEAD above, owned
source dirty):

| Stage | Command | Deadline | Duration | Outcome |
| --- | --- | --- | --- | --- |
| numeric-reader-compile-v1 | pinned Lake `env lean RMQ/Core/WordRAM/Bitvector/NumericReader.lean` | 180 s | 10.558 s | Exit 1: symbolic address association, projection reduction and prepared-register rewrite issues. |
| numeric-reader-compile-v2 | same narrow file after source repair | 180 s | 9.693 s | Exit 1: two remaining composition goals; repeated unit-address increments and final body simplification. |

Each exact launch/tree/hash/exit/stdout/stderr/ownership record is retained at
`commands/<stage>.json`. Neither command timed out, neither left a child alive,
and neither is marked as a passing semantic check. The imports were already
built in this task's local `.lake`; no shared or peer artifact was copied.
The root granted the build slot explicitly and received its release after v2.
The subsequent repair uses the same actual source and strengthens no premise.

The source inventory has fixed sizes 35 (descriptor loading), 9 (packet
finishing), and 77 (whole reader). Its write inventory is [8194,8271), so the
request pair, target input and physical width remain unchanged. These facts
concern source syntax and its frame, not all-prefix bounded-word safety.
Final evidence remains pending the next root-granted narrow check.

Proof digestion: the four descriptor replies become the locator's numeric
base, payload length, stride and count. The unchanged locator distinguishes
absence from a present empty word. On presence, the unchanged span decoder
consumes the same numeric memory, and its actual decoded value feeds the
packet arithmetic. Only segment zero with nonzero target is complemented.
The reader does not receive a logical store or a proof-supplied answer.

Live assumptions of the successful-descriptor leaf are exactly the four
lookups into the supplied memory, the segment/index guards and the shared
decoder's successful result. A separate first-failed-descriptor statement
retains the early fault and single attempted occurrence. A separate empty
sentinel consumer specializes the full present theorem to length zero and
therefore needs no payload address bound for an unexecuted read.

Named downstream consumer: the root's CanonicalGenericReaderCorrect proof,
using MemoryLayout's exact descriptor/slice identities and RegularLayout's
canonical chunk/sentinel regularity. A skeptical graduate student should ask
how every canonical logical word satisfies those hypotheses and how the
mathematical scalar computation is made safe at every primitive prefix; those
are explicit root-owned joins, not conclusions of this numeric leaf.

No new route decision was made here. Root's appended DD-20260912-BV1-002 records
the selected source/layout route. The proof-side register snapshots and
compositional evaluator lemmas do not add a second reader, decoder or compiler.
No separate process decision or broad certification run is introduced.

### Final numeric leaf evidence

The frozen `physicalReader_outside`, `physicalReader_absent` and
`physicalReader_present` signatures above now elaborate unchanged. In addition,
`physicalReader_first_descriptor_missing` proves an actual fault with exactly
one failed descriptor attempt, and `physicalReader_present_empty` consumes the
full present theorem to prove packet 1, length 0 and descriptor-only receipts
for any present zero-length span, regardless of the target register.

| Stage | Command | Deadline | Duration | Outcome |
| --- | --- | --- | --- | --- |
| numeric-reader-build-v3 | pinned Lake `build RMQ.Core.WordRAM.Bitvector.NumericReader` | 180 s | 10.813 s | Exit 0; all source branches, exact-type consumer and nine axiom inventories pass; six unused proof hints reported. |
| numeric-reader-build-final | same narrow module after removing those unused hints | 180 s | 13.729 s | Exit 0; no warnings, all nine axiom inventories pass; importable local module produced. |

Final source SHA-256:
`7E2CC443F2DE7351112460B7C2B0699C2879B51E760DEC3261B055790133897D`.
The local NumericReader.olean is 982,920 bytes, produced by this task's pinned
Lean 4.22 build. The actual source declaration `physicalReader_present` is
consumed by an independently written exact expected-type example in the same
file. No named-only check is substituted for that consumer. No mutation
campaign is claimed by this leaf; the root owns the composed capstone attacks.

`finishPacket_source` depends on `propext`. The eight other printed declarations
(`descriptorLoads_source`, `physicalReader_writes`, `physicalReader_frame`,
`physicalReader_outside`, `physicalReader_absent`, `physicalReader_present`,
`physicalReader_first_descriptor_missing`, `physicalReader_present_empty`)
depend only on the standard `propext`, `Classical.choice`, and `Quot.sound`.
There is no extra axiom or incomplete-proof axiom. Every command above was an
owned one-job process, completed within its deadline with empty stderr and no
surviving child. The root was notified and the build slot released immediately
after the final check. The canonical reader and whole BV-1 capstone remain
root-owned consumers, so this leaf does not close the full frozen matrix.
