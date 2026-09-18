# BV-1 regular logical-word layouts

Status: INCOMPLETE (BV-1 composition phase). The full assigned canonical
regular-layout leaf is proved and checked. Whole-machine and full-capstone
acceptance remain OPEN in the main BV-1 matrix.

Checkpoint: `645a0502b9da9ad6444edbe44759e1c2c5661f25`.
Governance: `0e6a00f654abc64f8b68988fa9675b9a839dca2f`.
Branch/worktree: `codex/bv-1-fully-charged-rank-select`,
`C:\Users\poin\.codex\worktrees\c974\RMQ`.
Proof-sprint preflight passed at the checkpoint against the exact governance
with actual runtime catalog rmq-audit-prompt, rmq-coordinator, rmq-proof-sprint
and required rmq-proof-sprint. Canonical skill/completion gate and the full
frozen BV-1 matrix govern this independent leaf. The lead approved the exact
interface below before proof edits. Ownership is only RegularLayout.lean and
this evidence file. Earlier leaf files, shared Packed, SelectExperiment and
ReaderInterface are frozen/outside this write scope. No separate commits.

## Frozen signatures and acceptance

```lean
def firstLength (words : Array (List Bool)) : Nat :=
  (words[0]?.getD []).length

def RegularWords (words : Array (List Bool)) : Prop :=
  ∀ i (hi : i < words.size),
    words[i] = ((Experiment.segmentBits words).drop
      (i * firstLength words)).take (firstLength words)

theorem RegularWords.getElem?_eq {words : Array (List Bool)}
    (h : RegularWords words) (i : Nat) :
  words[i]? = if i < words.size then
    some (((Experiment.segmentBits words).drop
      (i * firstLength words)).take (firstLength words)) else none

theorem RegularWords.length_eq {words : Array (List Bool)}
    (h : RegularWords words) (i : Nat) (hi : i < words.size) :
  words[i].length = min (firstLength words)
    ((Experiment.segmentBits words).length - i * firstLength words)
```

The final canonical theorem must quantify every input bits and every array in
exactly this expression from Experiment.memory (no helper-only endpoint):

```lean
let df := GenericSelect.sparseExceptionSelectData bits false
let dt := GenericSelect.sparseExceptionSelectData bits true
let c := SuccinctClose.bpFringeChunkBits (2 * bits.length)
∀ words ∈ [df.bitWords.store.words] ++
    Experiment.directorySegments df ++ Experiment.directorySegments dt ++
    [(SuccinctClose.bpFringeChunkTable c).store.words,
     (SuccinctClose.bpChunkSelectTable c false).store.words],
  RegularWords words
```

| ID | Exact frozen requirement | Scope | Evidence needed | Consumer/identity chain | Adversarial boundary | Evidence/status |
| --- | --- | --- | --- | --- | --- | --- |
| `LEAF-REGULAR-ALL` | canonical regular layout and exact flattened-slice recovery for EVERY actual array in Experiment.memory (raw bitWords, all16 selected components for both targets, two shared tables), including short-first words and trailing empty sentinels. | Full assigned leaf | Exact canonical membership theorem above; no extra regularity assumptions. | Actual canonical builders -> their actual arrays -> RegularWords -> guarded slice and exact length -> lead's descriptor/span reader. | Empty payload; short first chunk; partial final chunk; arbitrary trailing empty count; fixed-width zero-bit rows. | CLOSED for the leaf by `canonical_allSegments_regular`; same-array min-length direct consumer passed. |
| `LEAF-REGULAR-PREDICATE` | Pin a generic RegularWords predicate sufficient for descriptor: for every i<words.size, words[i] = (segmentBits words).drop(i * firstLength) \|>.take(firstLength), with actual length=min firstLength (total-i*firstLength), and prove canonical arrays satisfy it; allow nonzero count empty arrays. | Generic descriptor contract | Frozen predicate and typed recovery/length theorems above. | firstLength is exactly the descriptor's first-word length; count remains words.size, independent of payload length. | `#[[], [true]]` fails the SAME RegularWords predicate by retained kernel proof. | CLOSED: exact frozen types, count guard and min-length corollary all elaborated. |
| `INV-ALL-SIZE` | exactness covers all assigned sizes and edge cases without hidden readiness or compatibility dispatch; | This layout consumer | All bits/arrays/valid indices, plus exact absent-index guard. | Canonical all-segment theorem instantiates every component; proof-side geometry only. | Nonzero count with zero total length remains present; no positivity premise is added to RegularWords. | CLOSED for this layout leaf; canonical theorem has no readiness or array-regularity premise. |
| `LEAF-REGULAR-CHECK` | Build ONLY when I explicitly grant the shared build slot; write/read in parallel now, message when ready to check. | Verification | Bounded serial narrow builds and independently written exact-type consumers, plus trust inventory. | Final owned source and same canonical array expression. | No unchecked source signature closes the target. | CLOSED: explicit lead slot, unique serial stage names, final build and typed/trust import passed; slot released. |

Full BV-1 space, global physical store, charged execution, width/address,
instruction, replay and public-composition rows remain applicable in the main
matrix. This leaf establishes descriptor geometry; it does not certify those
composed obligations on its own.

## Source-grounded plan

All retained arrays belong to three inspected classes:

- The raw bitvector uses BoundedPayloadWordStore.ofChunks.
- Each of the two target directories contains fourteen FixedWidthNatTable
  arrays and two flag arrays built by ofChunksWithSentinel.
- The shared fringe/rank and false-select chunk tables are FixedWidthNatTable
  arrays. Their declared fixed-width row contract suffices independently of
  their entry values.

The generic proof normalizes a configured chunk width w to
`min w payload.length`, which is exactly the first logical word's length.
When the first word is short, all later canonical words are empty sentinels;
the min-width slice agrees with the configured-width slice for every index.
Count remains explicit even when stride and total length are zero.

The flag builder chains were inspected independently by select_inventory:
longFlagRankData and sparseExceptionEffectiveFlagRankData both use
canonicalTwoLevelRankDataOfChunksExactLocalBlock, then
canonicalTwoLevelRankDataOfBridgeLocalBlock, then
canonicalRankWordBridgeOfChunksWithSentinel. Their actual bitWords arrays are
therefore ofChunksWithSentinel over the actual long/sparse flag lists.

The lead owns MemoryLayout wrappers, component offsets, descriptor execution,
span decoding and final integration. This leaf exposes
canonical_allSegments_regular over the explicit allocation expression to avoid
an independently defined or accidentally mismatched allSegments wrapper.

## Verification plan

Development after an explicit slot: owned run_command.ps1 with unique
regular-layout stage names, directly pinned Lake v4.22.0, one Lean job and a
bounded deadline; repair only after diagnosing the smallest failure. Then
typed imports for guarded recovery, exact length, the full canonical expression
and the malformed-array rejection; explicit axiom inventory. Prior warm leaf
builds took 8-27 seconds; deadline will follow the lead's slot assignment.
No broad gate or separately owned commit belongs to this leaf.

## Checked interfaces and actual component coverage

All frozen signatures above elaborated as written in `RMQ.PackedBitvector`.
The lead approved the following additional consumer before its proof was added:

```lean
theorem RegularWords.min_slice_eq {words : Array (List Bool)}
    (h : RegularWords words) (i : Nat) (hi : i < words.size) :
  words[i] = ((Experiment.segmentBits words).drop
    (i * firstLength words)).take
      (min (firstLength words)
        ((Experiment.segmentBits words).length - i * firstLength words))
```

This is recovery at the exact span length computed by `regularSpan`. Combined
with `RegularWords.length_eq`, the numeric min is the actual returned logical
word length, including zero-length sentinels. A separate typed import composed
`canonical_allSegments_regular bits words hmem` with `.min_slice_eq i hi` for
arbitrary bits, a member of the complete allocation expression, and every valid
word index. There is no detached sibling array in that consumer.

The complete array inventory is 35 arrays:

| Source | Count | Checked producer |
| --- | --- | --- |
| Raw data array from the false-target canonical directory | 1 | `canonical_bitWords_regular`, using the actual `BoundedPayloadWordStore.ofChunks` field. |
| Fixed-width table arrays across both selected directories | 28 | `regularWords_fixedWidthTable`, using each actual table's universal `word_length_of_get?` contract. |
| Long-superblock and sparse-local flag arrays, both targets | 4 | `canonical_directorySegments_regular`, reducing the actual builder chains to `ofChunksWithSentinel`. |
| Shared fringe/rank and false-select chunk tables | 2 | `regularWords_fixedWidthTable` on the exact two tables and chunk parameter in the memory expression. |

`directorySegments_regular d hlong hsparse` first discharges all sixteen
components of an arbitrary directory when its two flag arrays are regular.
Its canonical consumer derives both premises from the actual flag builders;
they are not premises of `canonical_directorySegments_regular` or
`canonical_allSegments_regular`. The final theorem has only `bits : List Bool`
as an explicit input and retains the full explicit allocation expression from
the frozen interface. The lead can bridge its own MemoryLayout wrapper by
definitional equality.

## Proof construction and boundary behavior

`regularWords_of_slices words payload width herase hslices` proves the generic
first-word-stride property from exact original-width slices. If a valid index
exists, index zero exists, and its slice has length
`min width payload.length`. For every i, the slice with configured width equals
the slice with that smaller first length. If the first word is short, all
positive-index slices are empty under either width. If width fits the payload,
the two widths coincide.

`regularWords_of_uniform` consumes the existing
`PackedWordRAM.uniform_flatten_slice` over each table's actual word list. Its
width argument can be zero. `regularWords_fixedWidthTable` derives the uniform
premise from every stored word's fixed-width table contract; it does not assume
that only one particular table builder is regular.

`regularWords_chunks_with_empty_tail payload hw sentinels` covers every positive
configured width and every number of trailing empty words. Before the end of
the chunk list, the proof consumes the existing exact chunk-slice theorem.
After that end, a hypothetical in-payload offset would imply a present chunk,
contradicting the index bound. Thus both the stored sentinel and its payload
slice are empty. The full flattened payload is proved from existing chunk
erasure plus empty-tail erasure. `ofChunks` specializes sentinels to zero;
`ofChunksWithSentinel` specializes it to `payload.length + 1`.

No offset-before-total premise is added for sentinel indices: count can exceed
the number of nonempty chunks. Such an index remains present with length zero.
The separate global reader and safety proofs must handle its numeric position
under their own word/address-width bounds; this leaf does not suppress that
obligation.

The retained negative theorem is exactly:

```lean
irregular_empty_head_rejected : ¬ RegularWords #[[], [true]]
```

It applies the same universally quantified predicate at valid index one. The
first-word stride is zero, so the required slice is empty, while that actual
word is `[true]`. This rejection is kernel-checked in the source and direct
import. Positive source/import controls cover three present empty words,
short-first chunks with sentinel tails, an empty payload with sentinel count
one, and a two-bit configured chunk width with a partial final chunk. They
exercise the actual generic constructor theorems; universal proofs cover all
other sizes. No runtime machine-validation claim is made for these proof checks.

## Exact command evidence

Every Lean command ran after the lead explicitly released its MemoryLayout
development slot and granted this leaf the build tree. All used
`docs/internal/extensions/bv1/run_command.ps1`, unique stage names, the direct
pinned `C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0/bin/lake.exe`,
one Lean job, local `.lake/build` outputs and a 180-second deadline. Platform was
Windows and HEAD was the checkpoint above; source was the task's uncommitted
RegularLayout.lean. The runner JSON records the full concurrent dirty-tree
inventory. No shared mutable cache or parallel Lean process was introduced.

| Stage | Arguments | Duration | Exit/result | Durable output |
| --- | --- | --- | --- | --- |
| `regular-layout-1` | `build RMQ.Core.WordRAM.Bitvector.RegularLayout` | 4.786 s | 1; ordinary elaboration errors: implicit take-length argument, empty-take reduction, unavailable `by_contra`, list-membership association, and warning cleanup. | `commands/regular-layout-1.json` |
| `regular-layout-2` | Same module target after source repairs | 4.132 s | 1; one explicit List/Array optional-access coercion remained. All other proof targets elaborated. | `commands/regular-layout-2.json` |
| `regular-layout-3` | Same module target after adding `List.getElem?_toArray` rewrite | 5.178 s | 0; complete clean build without Lean warnings. | `commands/regular-layout-3.json` |
| `regular-layout-axioms` | `env lean <temporary-directory>/bv1-regular-layout-exact-types.lean` | 6.514 s | 0; eight independently typed consumers/controls and fourteen axiom reports passed. | `commands/regular-layout-axioms.json` |
| `regular-layout-axiom-source` | `env lean <temporary-directory>/bv1-regular-layout-axiom-source.lean` | 6.090 s | 0; six targeted dependency axiom reports located the inherited Classical.choice dependency. | `commands/regular-layout-axiom-source.json` |

The two failed builds were repaired before rerunning; no unchanged command was
retried after failure. Every result reported `TimedOut=false`,
`OutputLimitExceeded=false`, `TerminatedIds=[]`, ownership
`kill-on-close-job`. Failed-build stderr was preserved as `error: build failed`.
All successful commands had empty subprocess stderr. Existing Git global-ignore
access warnings appeared in the wrapper and did not change the compiler exits.
The source was frozen after regular-layout-3; later imports added no source edit.

The final import's exact checks were: general guarded optional lookup, exact
length, min-length slice, the full canonical membership theorem, the composed
canonical min-length slice, exact malformed-array rejection, partial-final
ofChunks instantiation and empty-payload sentinel instantiation. The axiom
inventory was:

- `[propext]`: `RegularWords.length_eq`, `RegularWords.min_slice_eq`,
  `irregular_empty_head_rejected`.
- `[propext, Quot.sound]`: `RegularWords.getElem?_eq`,
  `regularWords_of_slices`, `regularWords_of_uniform`,
  `regularWords_fixedWidthTable`, `directorySegments_regular`.
- `[propext, Classical.choice, Quot.sound]`:
  `regularWords_chunks_with_empty_tail`, `regularWords_ofChunks`,
  `regularWords_ofChunksWithSentinel`, `canonical_bitWords_regular`,
  `canonical_directorySegments_regular`, `canonical_allSegments_regular`.

The additional diagnostic confirmed that Classical.choice is already a
dependency of the existing `SuccinctSpace.chunkPayloadWords_get?_some_of_mul_lt`
and `flattenPayloadWords_chunkPayloadWords`. The existing chunk slice and
List optional-access/membership lemmas inspected by that diagnostic depend
only on propext. This module introduces no new axiom declaration and no
noncomputable executable function.

Both full working-tree trust scans returned no matches (normal rg no-match
exit 1). `git diff --check` passed with only the existing LF/CRLF notices for
the lead's concurrently edited ledgers, contract and report. Broad gates,
strict design checks, committed-range checks and exact-commit acceptance remain
the lead's responsibility; this leaf does not claim them.

Final source: RegularLayout.lean, 10776 bytes, SHA-256
`172ED0F83F0D8E63136F7A3063F8EDC009F71D57C4BF8B1D311067F1AC53638C`.

## Proof digestion and next consumer

Conceptually, the descriptor's stride is now justified from the actual retained
word arrays. A short first word is harmless because its later canonical words
are empty; trailing sentinels remain present even when their slice length is
zero. Uniform fixed-width tables satisfy the same interface, including
zero-width rows. All 35 arrays in the actual allocation expression are covered
at every input size.

In plain English, taking a logical word's descriptor slice recovers exactly the
word that the canonical store says is at that index. The proof retains both
its contents and its true length. Live assumptions for generic helpers are
explicit store erasure/slice or table-width contracts and positive configured
chunk width. The final canonical theorem discharges those assumptions from the
existing builders and has no readiness or regularity premise.

The named downstream consumer is the lead's descriptor/span physical reader,
ultimately the same-store capstone
`RMQ.PackedBitvector.fullyChargedBitvectorCapstone_holds`. A skeptical reader
should next check that descriptor offsets point to these exact slices in the
counted numeric allocation and that actual loads/decoding recover them safely.
Those execution and global-memory links belong to the lead's continuing
work, not to an assumed fact inside RegularWords. Shared ledger/digestion
entries and commits remain lead-owned. The worker released the build slot and
stays available for the next explicitly assigned independent leaf.
