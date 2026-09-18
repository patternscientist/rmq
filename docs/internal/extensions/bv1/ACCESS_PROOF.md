# BV-1 actual access query — frozen leaf contract

Owner: numeric_reader. Same governed checkpoint/worktree as NUMERIC_READER.md
and CHARGED_SETUP.md; canonical proof-sprint preflight passed on this task.
Scope: new AccessProof.lean, this record and an independent exact-type
consumer. Root owns Source, final allocation/reader/metadata and compiled/API
joins. No executable source or shared Packed module is changed. The root and
two other workers own independent downstream leaves, so this sequential access
proof is prepared locally while their builds run. No Lean before slot grant.

## Verbatim assignment and frozen expectations

AP-EXEC: "actual Source.accessQuery (same Allocation.memory) exact Bool
packet 0 if index>=n else 1/2 original bits[index], exact reads from its one
actual segment19 request".

AP-SAFE: "source safety from canonical MemoryWordsFit/NumericReaderGeometry-
derived ReaderSafe plus entry fit and metadata equalities n/reg18, M/reg19,
W/reg22,target reg3=false.toNat."

AP-BITS: "Access has no normalization of segment19 and derives bit via
packet−1, shift(index mod M),mod2."

AP-CLOSE: "Freeze full target before edits; no alternate helper endpoint."

AP-SCOPE: "Root will handle metadata/setup and final API/compiled joins,
select/rank wrappers. Keep ownership Source unchanged unless actual obstruction
requires coordinated fix."

All frozen declarations are in RMQ.PackedBitvector.AccessProof. They use
SuccinctRank.machineWordBits and the existing shared Structured evaluator,
with no source copy or precomputed executable answer.

```lean
def AccessMetadata (bits : List Bool) (regs : Registers) : Prop :=
  regs 3 = 0 ∧ regs 18 = bits.length ∧
  regs 19 = machineWordBits bits.length ∧
  regs 22 = Experiment.width bits.length

def accessPacket (bits : List Bool) (index : Nat) : Nat :=
  ((bits[index]?).map fun bit => bit.toNat + 1).getD 0

def accessReceipts (bits : List Bool) (index : Nat) : List Receipt :=
  if index < bits.length then
    Allocation.readerReceipts bits false 19 (index / machineWordBits bits.length)
  else []

theorem accessQuery_source (bits : List Bool) (regs : Registers)
  (hm : AccessMetadata bits regs) :
  let actual := accessQuery.eval (Allocation.memory bits) ⟨regs, .running⟩
  actual.final.status = .running ∧
  actual.final.regs 705 = accessPacket bits (regs 704) ∧
  actual.reads = accessReceipts bits (regs 704) ∧
  (∀ r, r < 705 ∨ (710 ≤ r ∧ r < 8192) ∨ 8271 ≤ r →
    actual.final.regs r = regs r)

theorem accessQuery_safe (bits : List Bool) (regs : Registers)
  (hm : AccessMetadata bits regs)
  (fit : (⟨regs, .running⟩ : Data).Fits (Experiment.width bits.length))
  (readerSafe : Controller.ReaderSafe
    (Allocation.controllerModel bits false regs) (Experiment.width bits.length)
    (Allocation.memory bits) Experiment.physicalReader) :
  accessQuery.Safe (Allocation.memory bits) (Experiment.width bits.length)
    ⟨regs, .running⟩
```

ReaderSafe is the existing universal safety interface, instantiated with the
actual original metadata register function. The root supplies it from the
canonical memory-word and numeric-reader geometry bounds. This leaf does not
silently replace that obligation with a final-fit proposition. The entry width
is the same query-independent Experiment.width used by the reader. Its
constant-capacity and raw-width inequalities are derived from the existing
width definition/theorems, not additional all-size hypotheses.

| ID | Exact evidence / consumer chain | Anti-vacuity boundary | Status |
| --- | --- | --- | --- |
| AP-EXEC | The full frozen source conjunction on actual accessQuery.eval over Allocation.memory, consumed externally with the safety conclusion. | Empty bits and index equal to length return packet 0 with no reads; a valid last bit executes the same segment-19 reader even in a ragged final raw word. | FROZEN |
| AP-BITS | Actual logical raw word lookup → packet − 1 → shifted modulo-two bit → original bits[index]. | False and true yield distinct 1/2 packet projections; segment 19 is never complemented. | FROZEN |
| AP-SAFE | Frozen Block.Safe conclusion consumes existing ReaderSafe at the actual prepared reader state, preserving low metadata. | Division uses positive raw width, subtraction is non-underflowing, remainder used as shift is strictly below machine width, final increment stays below capacity. | FROZEN |
| AP-CLOSE | Narrow target and independent full expected-type consumer; exact axioms/hygiene/evidence/digestion. | No helper-only completion and no reference value injected into execution. | FROZEN |
| AP-SCOPE | Same existing source and allocation, with final metadata/setup/compiler/API consumers owned by root. | No shape, readiness or storage-layout rewrite narrows all-size access correctness. | FROZEN |

Relevant inherited contributions: INV-STORE-IDENTITY,
INV-VALUE-DEPENDENCY, INV-TRACE-EXECUTION, INV-READ-BACKING,
INV-WORD-WIDTH, INV-ADDRESS-WIDTH, INV-ALL-SIZE, INV-PROOF-SEPARATION,
INV-NO-SYNTHETIC and INV-PUBLIC-COMPOSITION. The full inherited matrix remains
untouched; its broader rows are root-owned. Static fields, PC/transition bounds,
API word-domain guards and preprocessing claims are separate root obligations.

Verification: warm exact AccessProof target under an owned 180-second deadline
once granted; direct expected-type consumer; axiom inventory; trust and direct
whitespace/conflict scans; git diff --check. Diagnose ordinary local failures
narrowly. No aggregate build/gate in this leaf.

## Evidence and digestion

Pending implementation. No AccessProof build has run.

### Checked result and verification

Both frozen endpoints close unchanged. `accessQuery_source` has only the four
metadata equalities as hypotheses and covers every bitvector/index. It fixes
the actual final status, packet, ordered receipts and frame. `accessQuery_safe`
consumes exactly the frozen entry fit and existing ReaderSafe interface. The
external `access_expected_type.lean` expands the packet and receipt definitions
in its independently written `actual_access_required` type and conjoins all
four semantic/frame observations with safety of the same actual source.

| Stage | Exact target / purpose | Deadline | Duration | Outcome |
| --- | --- | --- | --- | --- |
| access-proof-build-v1 | pinned Lake `build RMQ.Core.WordRAM.Bitvector.AccessProof` | 180 s | 11.407 s | Exit 1: local Array/List rewrite direction, shift notation, and reserved local identifier. |
| access-proof-build-v2 | Same target after initial local repairs. | 180 s | 44.733 s | Exit 1: shift function/notation mismatch and elaboration heartbeat limit while converting safety at an expanded actual reader state. |
| access-proof-build-v3 | Same target with explicit conversion arguments. | 180 s | 49.843 s | Exit 1: same heartbeat obstruction remained; no process timeout. |
| access-proof-build-v4 | Same target after a literal Nat.shiftRight bridge and state abstraction before conversion. | 180 s | 14.653 s | Exit 1: semantics and local tail safety passed; two remaining final width-alias normalization goals. |
| access-proof-build-v5 | Same target with explicit final ScalarChecks width. | 180 s | 9.524 s | Exit 0; unused simp hints remained. |
| access-proof-build-final | Same target after removing unused hints. | 180 s | 14.831 s | Exit 0; zero AccessProof warnings. |
| access-proof-consumer-final | pinned Lake `env lean docs/internal/extensions/bv1/access_expected_type.lean` | 90 s | 8.209 s | Exit 0; external full expected-type consumer, zero warnings. |

Complete command/tree/source-hash/output/ownership records are retained under
`commands/<stage>.json`. All stages used explicit Lean 4.22.0 and one Lean
thread. No process deadline or output cap was exceeded. Final stages have
empty stderr and terminated-child lists; the build slot was released after
the final consumer, with no surviving owned process. The two deterministic
elaboration limits were repaired structurally without increasing Lean's
heartbeat limit. The final AccessProof artifact is 923,432 bytes.

Final source SHA256:
`0077FE19D2E693D7F02936FDB4A9592D68B9E67AC1FB9A1E905D361F1DB30DE2`.
Final external consumer SHA256:
`AF77F97FEF74247BFC45061D2078EF8D4709D22EF5A77C00F7F11A9BB018FB54`.
No source change followed the final module check. Both exported endpoint
inventories and external `actual_access_required` use exactly
`[propext, Classical.choice, Quot.sound]`. Own prohibited-token, extra trust,
trailing-whitespace and conflict scans are empty. `git diff --check` passes
with only existing LF/CRLF advisories. The full frozen matrix remains unchanged
at SHA256 `80BD59A314FD33D37076802954444DA24F65C87A2A91DE23BC668B6AF9CCEB24`.

### Requirement reconstruction

AP-EXEC/AP-BITS: `raw_access_word` connects the actual complete read store's
segment 19 to `jacobsonRankData bits`' actual raw array, through
`jacobson_raw_words_eq`. A valid index's quotient selects a present original
chunk before the appended empty sentinels; the exact chunk-slice theorem and
division/remainder identity identify its local indexed bit with bits[index].
`extract_bit` proves shifting its little-endian numeric decode and reducing
modulo two returns that bit's Bool.toNat. It uses induction on the actual word
and position, with false/true base cases.

The main source proof calls `Allocation.physicalReader_correct` at the actual
four-write prepared register state. The exact segment-19 logical reply becomes
the reader's packet, length and exact Allocation.readerReceipts. Its frame
preserves the original argument and raw width. Simplifying the existing
accessQuery tail then performs packet-minus-one, remainder, shift, modulo two
and increment, yielding the frozen accessPacket. No normalized segment-zero
word, sibling payload, precomputed answer, synthetic trace or replacement
reader occurs in this chain. The frame theorem is derived independently from
accessQuery's actual write syntax and physicalReader_writes.

AP-SAFE: constants and guards fit using the canonical width floor; the quotient
is bounded by the original fitting index. Four actual prefix writes preserve
all controller metadata registers below 190. ReaderSafe is instantiated at
that same actual prepared state. Source evaluation fit and the actual reader's
running/frame facts supply the tail state. The tail checks packet subtraction
under the nonzero guard, positive raw-width division/modulo, remainder below
raw width below physical width, decreasing shift, modulo-two bound and the
final increment. The outer ScalarChecks composition is converted to
accessQuery.Safe with the original entry fit.

The universal checked branches cover empty input and every index at or above
length: packet 0 and no reads. Every valid index selects its actual raw chunk,
including a final ragged word; false/true extraction gives packets 1/2.
The exact projection equality rejects a value-inert access implementation even
if its receipts changed. These are branches of a checked proof and exact-type
consumer, not a claimed executable mutation campaign.

### Proof digestion and disposition

Access now means what its instructions say: load the one relevant packed raw
word from the counted allocation, then extract the original bit by arithmetic.
The theorem covers all indices, and its receipts come from that same reader
invocation. Source safety also closes under the existing canonical-reader
safety interface and explicit initial fit.

Live assumptions: the four already-loaded metadata equalities; entry register
fit and ReaderSafe for source safety. Root must derive ReaderSafe from the
actual allocation's word/descriptor bounds and connect charged setup to those
metadata equalities. Static instruction fields, compiled PC bounds, primitive
run observations, API domain guards and final public composition remain root
obligations. A skeptical graduate student should follow these assumptions into
the whole-source/compiled join and verify that packet, receipts and every
prefix refer to this same Allocation.memory and unchanged accessQuery.

AP-EXEC, AP-SAFE, AP-BITS and AP-CLOSE have the checked leaf evidence above;
AP-SCOPE was preserved. Status is `CANDIDATE_COMPLETE`, pending coordinator
reconstruction. This is no full-client acceptance or broad-gate claim. No
source/representation design choice changed, no shared source was edited, and
no commit/push was performed. Root owns integration ledgers and final audit.
