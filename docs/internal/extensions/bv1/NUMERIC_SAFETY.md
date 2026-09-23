# BV-1 numeric reader safety — frozen contract

Owner: numeric_reader. Root authorized this next leaf after the numeric source
proof passed. Existing checkpoint/governance, branch and full acceptance matrix
are unchanged. Scope: NumericSafety.lean and this record. No shared Packed
source, NumericReader source or executable bitvector reader is changed.

The concrete target is safety of the actual Experiment.physicalReader for
arbitrary numeric memory and input registers satisfying explicit numerical
bounds. The root separately proves those bounds from canonical allocation and
controller invariants. This leaf must handle actual missing descriptor/payload
replies by early faults; no successful-read assumption is introduced globally.

Frozen interface before implementation:

```lean
def NumericReaderGeometry (memory : Memory) (width : Nat) (regs : Registers) : Prop :=
  (regs 8192 < 23 → numericDescriptorAddress regs + 3 < 2 ^ width) ∧
  ∀ (bitBase bitLength stride count : Nat),
    memory[numericDescriptorAddress regs]? = some bitBase →
    memory[numericDescriptorAddress regs + 1]? = some bitLength →
    memory[numericDescriptorAddress regs + 2]? = some stride →
    memory[numericDescriptorAddress regs + 3]? = some count →
    regs 8193 < count →
    bitBase + regs 8193 * stride < 2 ^ width ∧ stride < width

theorem physicalReader_safe (memory : Memory) (width : Nat) (regs : Registers)
    (hw : 8 ≤ width) (memoryFit : MemoryWordsFit memory width)
    (fit : (⟨regs, .running⟩ : Data).Fits width)
    (hwidth : regs 22 = width)
    (geometry : NumericReaderGeometry memory width regs) :
    Experiment.physicalReader.Safe memory width ⟨regs, .running⟩
```

An independently written `example` will pin this exact expected type while
consuming `physicalReader_safe`. This is a `Block.Safe` theorem; root consumes
it with the actual shared Structured compiler, static fields/code bounds and
its source correctness theorem to obtain one run with value, exact receipts,
instruction bounds and all-prefix safety. A theorem merely asserting final
register fit would not close this leaf.

Acceptance mapping: the source-safety leaves of REQ-BV-RUN, REQ-BV-REUSE,
INV-WORD-WIDTH, INV-ADDRESS-WIDTH, INV-INSTRUCTION-ATOMICITY and
INV-WIDTH-SCALING. Source syntax is unchanged, so its frame and fixed 77-size
result are consumed from NumericReader. Remaining full-client rows stay with
the root. The frozen whole-client matrix is not edited.

Live geometry is stated only when the segment is entered or all four
descriptor loads actually succeed. The position bound implies the locator's
intermediate index-times-stride bound. It applies even to an empty sentinel:
the locator computes this number although the span decoder performs no payload
read. The stride bound implies decoded length below width. MemoryWordsFit
bounds replies without assuming their presence or inferring addressability
from memory length. All initial registers fit; API guards for unbounded Nat
arguments remain a separate root-owned boundary.

Consumer plan: reuse ScalarSafety.regularLocateBlock_safe and
LoadSafety.spanBlock_safe for the existing blocks. The finish arithmetic must
bound the unconditionally executed `value + 1`, then its optional complement
shift and non-underflow subtraction. ReaderSafety.decodeSpanNat_value_lt is a
shape-free theorem even though its containing file also has shape-specific
results; none of those premises may enter this theorem.

Verification plan: prepare source offline; do not run Lean until root grants
the one-job build slot. Required imports' safety artifacts are currently cold,
so warm the exact required targets under a separately recorded realistic
deadline before the narrow NumericSafety loop. Use unique numeric-safety-*
stages through the existing owned bounded-process helper, then exact-type
consumer and axiom inventory. No full aggregate gate is run by this leaf.
Trust/diff checks remain proportionate; root performs final committed-range
and design/public checks on the integrated candidate.

## Evidence (append-only)

Implementation and checked results pending. Static source review established
the exact safety entry points and the empty-sentinel arithmetic distinction.

### Root-approved interface amendment

The root approved weakening the descriptor-quadruple premise to apply only
when `regs 8192 < 23`, matching the reader's actually entered branch. The
original frozen interface above is preserved as history. Its unguarded second
clause would unnecessarily constrain unused memory addresses for segment
requests outside the reader's range. The updated predicate is exactly:

```lean
def NumericReaderGeometry (memory : Memory) (width : Nat) (regs : Registers) : Prop :=
  (regs 8192 < 23 → numericDescriptorAddress regs + 3 < 2 ^ width) ∧
  (regs 8192 < 23 → ∀ (bitBase bitLength stride count : Nat),
    memory[numericDescriptorAddress regs]? = some bitBase →
    memory[numericDescriptorAddress regs + 1]? = some bitLength →
    memory[numericDescriptorAddress regs + 2]? = some stride →
    memory[numericDescriptorAddress regs + 3]? = some count →
    regs 8193 < count →
    bitBase + regs 8193 * stride < 2 ^ width ∧ stride < width)
```

The theorem and exact expected-type consumer retain their frozen hypotheses
and conclusion, consuming this amended predicate. This is a stronger safety
result because it requires fewer geometric assumptions. All actual descriptor
attempts and every computed sentinel position retain their original bounds.
No full-client requirement or inherited matrix row was changed.

### Dependency scheduling evidence

Before requesting the safety build slot, a source-import traversal found 218
RMQ modules in ReaderSafety's dependency closure; 211 already had this task's
local `.olean` artifacts. Seven were missing, totaling 230,984 source bytes:
Guard (5,782), Locate (61,614), PhysicalRead (15,311), Safety (43,628),
ScalarSafety (11,712), LoadSafety (42,584), ReaderSafety (50,353). Safety feeds
ScalarSafety/LoadSafety; Locate feeds PhysicalRead; those plus Guard feed the
ReaderSafety target. Their other imports were already warm.

The planned dependency deadline was reduced from a preliminary 1,800 seconds
based on the previously fully cold tree to 900 seconds for this exact seven-
module remainder. The parent separately reported a 175-second successful
prerequisite warmup following the older 900-second Rank timeout. NumericSafety
itself will use a 180-second warm check. No safety process has yet run; this is
scheduling evidence, not a pass. The root owns the build-slot queue.

Immediately before the granted prerequisite slot, the controller had also
built Locate and PhysicalRead. The remaining set was five modules totaling
154,059 source bytes: Guard, Safety, ScalarSafety, LoadSafety, ReaderSafety.
The actual deadline was therefore reduced to 600 seconds for the exact
ReaderSafety target. All other 213 project imports were warm.

| Stage | Exact command | Deadline | Duration | Outcome |
| --- | --- | --- | --- | --- |
| numeric-safety-prerequisite-v1 | pinned Lake `build RMQ.Core.WordRAM.Packed.ReaderSafety` | 600 s | 111.835 s | Exit 0; all five missing artifacts built. No timeout, no stderr or surviving child. |

The complete launch/tree/hash/output/ownership result is retained at
`commands/numeric-safety-prerequisite-v1.json`. Lake replayed existing baseline
unused-simp warnings from the unchanged import closure; no shared source was
edited. This is prerequisite verification only. The root requested a release
before the new NumericSafety module's first check, and received that release
immediately. NumericSafety is now warm and awaiting its next granted slot.

### Final implementation and verification

The amended full target now closes on the actual `Experiment.physicalReader`.
Its public proposition and independently written expected-type `example` are
exactly the theorem signature frozen above. The implementation adds no
executable reader and changes no shared Packed module. The final source SHA256
is `621FC88A3FD86C8188A3074608CB254FA1D507CC4482F21C9EA13F8888A02C92`.
The v3 checked source was
`D6DD907D757F9047855C31F0DFBAEDFDB201F7402CE74A3A9EE2A5887AB5F943`;
the only subsequent source change removed four trailing spaces left by the
unused-hint cleanup. No Lean tokens changed. The root's direct-consumer build
will refresh the artifact on the final whitespace-clean source.

| Stage | Exact command | Deadline | Duration | Outcome |
| --- | --- | --- | --- | --- |
| numeric-safety-build-v1 | pinned Lake `build RMQ.Core.WordRAM.Bitvector.NumericSafety` | 180 s | 18.359 s | Exit 1; stopped-state simplification, descriptor-success witness equalities, and final folded-sequence rewrite required local repairs. |
| numeric-safety-build-v2 | same exact narrow target | 180 s | 20.954 s | Exit 1; all safety composition elaborated; the fourth successful-reply witness required reflexivity after the lookup case split. |
| numeric-safety-build-v3 | same exact narrow target | 180 s | 30.439 s | Exit 0; complete theorem and expected-type consumer checked; zero NumericSafety warnings. |

The final pass used Lean 4.22.0, one Lean thread and the owned bounded-process
helper, as recorded with complete commands, source hashes and output in
`commands/numeric-safety-build-v3.json`. It did not time out or exceed its output
limit; stderr and terminated-child lists were empty. The emitted local
NumericSafety artifact is 2,281,184 bytes. Existing baseline warnings were
replayed from unchanged imports. The build slot was released to the root
immediately after the pass; no further Lean process was launched by this leaf.

All three printed inventories are exactly
`[propext, Classical.choice, Quot.sound]`:
`descriptorLoads_safe`, `finishPacket_safe`, `physicalReader_safe`.
The exact-type consumer calls `physicalReader_safe` with all frozen arguments
and has the conclusion
`Experiment.physicalReader.Safe memory width ⟨regs, .running⟩`.
The prohibited-token and additional proof-trust scans over NumericSafety are
empty. `git diff --check` passes; only existing LF/CRLF advisory warnings were
reported. The untracked owned source is also checked directly for trailing
whitespace and conflict markers before handoff. NumericReader remains
unchanged at SHA256
`7E2CC443F2DE7351112460B7C2B0699C2879B51E760DEC3261B055790133897D`.
The complete frozen acceptance matrix remains unchanged at SHA256
`80BD59A314FD33D37076802954444DA24F65C87A2A91DE23BC668B6AF9CCEB24`.

### Requirement evidence and composition

The source-safety contribution to REQ-BV-RUN, REQ-BV-REUSE,
INV-WORD-WIDTH, INV-ADDRESS-WIDTH, INV-INSTRUCTION-ATOMICITY and
INV-WIDTH-SCALING is the exact `Block.Safe` proposition above, with arbitrary
actual memory, all entry registers fitting the same width, register 22 equal
to that width, width at least 8, `MemoryWordsFit`, and the approved guarded
geometry predicate. No global successful-read or CartesianShape assumption
occurs. The full inherited rows remain root-owned integration obligations.

The object-composition chain is:

1. The actual descriptor prefix either stops on one of its four actual loads
   or reaches `regularLocateBlock 8200`. Successful replies are recovered
   from this same evaluation. `regularLocateBlock_safe` receives the actual
   index, base and stride bounds; the position bound also bounds the
   intermediate index-times-stride product.
2. `descriptorLoads_source` identifies that same evaluation's presence flag,
   position and length. Its write-frame theorem preserves the word-width
   register. For a present record, the actual three register moves feed the
   same position and length to the existing `spanBlock 8256`.
3. `spanBlock_safe` covers its actual loads including missing replies. When
   decoding succeeds, `decodeSpanNat_value_lt` bounds the actual value by
   `2 ^ len`; `finishPacket_safe` bounds the unconditional increment, optional
   shift and non-underflow subtraction in `Experiment.finishPacket`.
4. Structural `ScalarChecks`/`Block.Safe` composition closes the actual
   outer `Experiment.physicalReader` and every stopped branch. These proof
   decompositions are not alternate executable programs.
5. The root supplies canonical allocation/controller hypotheses to this
   theorem, then passes its source-safety conclusion to the existing
   `Block.compile_safe_correct` or `Block.compile_with_halt_safe`. Those
   consumers preserve the same source final data and ordered receipts and
   prove every actual instruction safe plus every bounded execution prefix
   fitting. Static `FieldsFit`, hosted code/end-PC bounds, entry state fit,
   and optional halt operand fit remain required compiler premises.

Boundary challenges are discharged within the checked theorem: segment 23 or
larger takes the inactive branch without either geometry clause; each missing
descriptor reply stops safely; an absent index skips the span; missing first
or second payload replies stop safely through the shared span theorem; a
present zero-length span still requires its computed locator position to fit,
while decoding performs no payload read; nonzero target on segment zero takes
the complement branch only after the unconditional increment was shown safe.
These are case branches of the actual generic proof, not claimed executable
mutation tests.

### Proof digestion and disposition

Conceptually, numeric exactness and numeric safety are now separate checked
interfaces for one unchanged reader. Exactness says which packet and ordered
attempted reads the reader produces. Safety says its arithmetic, shifts and
actual load addresses respect a declared word width under explicit numeric
bounds, including runs that fault because supplied memory is missing data.

The remaining live assumptions are entry-register fit, stored-word fit,
width-register equality, width at least 8, active descriptor-address capacity,
and bounded computed positions/strides for successful present descriptors.
The source theorem alone does not assert that encoded register identifiers
fit at width 8: the root must additionally establish static instruction fields
and code bounds at its chosen width before applying the shared compiler.
Canonical allocation coverage and the full rank/select controller invariant
also remain root-owned. A skeptical graduate student should next ask how
those hypotheses follow from the exact counted allocation and each controller
request, and verify that the compiler consumes this same source-safety theorem
alongside the same execution's semantic/receipt theorem.

Leaf status: `CANDIDATE_COMPLETE`, pending coordinator reconstruction. No
full-client closure, acceptance, new design decision, commit, push or aggregate
gate is asserted here. Broad verification is reserved for the root's composed
candidate; this leaf used its narrow changed module and an exact-type direct
consumer. Root owns integration design/public ledgers and final audit.
