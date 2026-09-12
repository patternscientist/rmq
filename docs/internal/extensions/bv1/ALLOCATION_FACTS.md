# BV-1 select-directory allocation facts

Status: INCOMPLETE (BV-1 composition phase). The assigned independent
serialization-counting leaf is proved and checked. The full BV-1 rows remain
OPEN in ACCEPTANCE_MATRIX.md.

Base/governance and current HEAD:
`0e6a00f654abc64f8b68988fa9675b9a839dca2f`.
Branch: `codex/bv-1-fully-charged-rank-select`.
Worktree: `C:\Users\poin\.codex\worktrees\c974\RMQ`.
Ownership: only `RMQ/Core/WordRAM/Bitvector/AllocationFacts.lean` and this file.
No commits, shared ledgers or earlier frozen normalization files are owned by
this assignment. The same governed proof-sprint preflight passed earlier in
this task, and HEAD/governance are unchanged. The frozen matrix and current
CONTRACT.md were read before source edits.

## Frozen local acceptance matrix

The following local row preserves the lead's exact requested mathematical
target. It supports REQ-BV-ALLOC without replacing any full-capstone row.

| ID | Exact frozen requirement | Scope | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge attempted and outcome | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `LEAF-DIRECTORY-COUNT` | Prove for arbitrary SparseExceptionSelectData d (all target bits and all component parameters), `(Experiment.directorySegments d).flatMap Experiment.segmentBits` length ≤ d.payload.length, ideally exact equality after adding omitted false rank sample table lengths. Then derive bound ≤ canonicalSparseExceptionSelectOverhead bits.length via d.payload_length_le_canonical. | Independent counting leaf | Universal equality between the selected-segment bit length plus four omitted false-table lengths and `d.payload.length`; inequalities to that payload and the canonical overhead. | Actual experiment `directorySegments d` -> `segmentBits` -> each actual `PayloadWordStore` erasure -> the same `d.payload` -> `d.payload_length_le_canonical`. | Duplicating a positive-length selected segment violates the retained kernel exact-reconciliation theorem; no equality of reordered bytes is claimed. | Final module build and independently written typed projections passed for the exact propositions below. | CLOSED for this counting leaf; final allocation composition remains OPEN. |
| `INV-ALL-SIZE` | exactness covers all assigned sizes and edge cases without hidden readiness or compatibility dispatch; | Counting leaf | Quantify all bits, target, both overhead parameters and every inhabitant d; no shape or canonical-builder premise. | Same selected arrays for arbitrary valid directory objects. | Empty payloads and zero-length component tables remain in the universal domain. | Theorems have all displayed implicit data parameters and only d as their argument. A typed application to `sparseExceptionSelectData bits target` passed for arbitrary bits/target. | CLOSED for this counting leaf. |
| `LEAF-CHECK` | No Lean commands until explicit slot: lead select startup/runs underway. Write source and ask me to check; can continue proofs from source meanwhile. | Verification | Lead-authorized serial narrow build and exact-type/axiom check. | AllocationFacts module. | Source text alone cannot certify the counting claim. | Lead explicitly granted the slot after registry-v1 completed. Build repair and exact-type import ran serially; slot released after all Lean checks. | CLOSED. |

The full machine, trace, read-backing, word/address-width, instruction, replay
and capstone invariants stay applicable and OPEN in the parent matrix. This
leaf proves list serialization identities and bit lengths only. It defines
no machine execution and cannot certify whole-store identity or total retained
capacity by itself.

## Source facts and proof plan

`Experiment.directorySegments d` is exactly the 16 retained array components
for select segments 1 through 16. It includes both flag bitvectors, their true
super/block rank samples, both four-field entry tables, and both exceptional
relative-offset tables. The omitted components are the false super/block rank
sample tables for the long-superblock and sparse-local flag vectors.

`PayloadWordStore.payload_eq_words_join` relates each actual stored word array
to its payload through `flattenPayloadWords`. A checked list-flatten identity
connects that representation to the experiment's `Array.toList.flatten`.
`SparseExceptionSelectData.payload` concatenates the same counted components in
a different order and includes the four omitted false tables. Its existing
`payload_length_le_canonical` theorem applies to every `d` in this assignment.

The proof exposes component lengths before using arithmetic rearrangement.
It makes no bit equality claim between differently ordered payloads. The
downstream physical allocation proof still needs exact descriptors/subranges,
one copy of the raw data, both target directories, shared tables, alignment,
numeric headers, code and scratch accounting.

## Verification plan

- Source-only preparation while the lead owns the Lean build slot.
- After explicit authorization: build the owned module with the pinned direct
  Lake binary, bounded ownership and one Lean job; check exact projected types
  and axiom inventory. Closest comparable warm leaf builds took 10-19 seconds;
  a 120-second deadline gives host scheduling margin.
- Scoped hygiene and whitespace checks; broad gate/commit/audit obligations
  remain with the lead because this is a pure counting leaf.
- Final evidence must record the exact source identity, command artifacts,
  result, duration, deadline and trust inventory before claiming the leaf proved.

## Checked theorem types and composition

All declarations below are in `RMQ.PackedBitvector`; the source opens
`RMQ.GenericSelect`, `RMQ.SuccinctSpace` and the actual `Experiment` namespace.
`bits`, `target`, `rs`, and `rb` are arbitrary in every single-directory result.

```lean
segmentBits_payload {payload : List Bool} (store : PayloadWordStore payload) :
  Experiment.segmentBits store.words = payload

directorySegments_length_add_omitted
    {bits : List Bool} {target : Bool} {rs rb : Nat}
    (d : SparseExceptionSelectData bits target rs rb) :
  ((Experiment.directorySegments d).flatMap Experiment.segmentBits).length +
    d.longFlagRankData.superTables.falseTable.payload.length +
    d.longFlagRankData.blockTables.falseTable.payload.length +
    d.sparseDirectory.rankData.superTables.falseTable.payload.length +
    d.sparseDirectory.rankData.blockTables.falseTable.payload.length =
    d.payload.length

directorySegments_length_le_payload
    {bits : List Bool} {target : Bool} {rs rb : Nat}
    (d : SparseExceptionSelectData bits target rs rb) :
  ((Experiment.directorySegments d).flatMap Experiment.segmentBits).length ≤
    d.payload.length

directorySegments_length_le_canonical
    {bits : List Bool} {target : Bool} {rs rb : Nat}
    (d : SparseExceptionSelectData bits target rs rb) :
  ((Experiment.directorySegments d).flatMap Experiment.segmentBits).length ≤
    canonicalSparseExceptionSelectOverhead bits.length

directorySegments_both_length_le
    {bits : List Bool} {rfs rfb rts rtb : Nat}
    (df : SparseExceptionSelectData bits false rfs rfb)
    (dt : SparseExceptionSelectData bits true rts rtb) :
  ((Experiment.directorySegments df ++ Experiment.directorySegments dt).flatMap
    Experiment.segmentBits).length ≤
      canonicalSparseExceptionSelectOverhead bits.length +
        canonicalSparseExceptionSelectOverhead bits.length
```

`directorySegments_bits_eq` first proves the exact selected bit list in the
actual descriptor order: four super fields, four local fields, long true
super/block samples, long flag bits, long relative offsets, sparse true
super/block samples, sparse flag bits, and sparse relative offsets. Each
component equality consumes its actual `.store.payload_eq_words_join` through
`segmentBits_payload`. There is no sibling array or size-only replacement in
this first equality.

The exact length theorem expands `SparseExceptionSelectData.payload`,
`SparseExceptionDirectory.payload`, the rank `auxPayload`/super/block payload
definitions, and `FixedWidthRankSampleTables.payload`. Only then does `omega`
rearrange the resulting natural-number sum. Nonnegativity drops the four
omitted lengths. `Nat.le_trans` composes this with the existing
`d.payload_length_le_canonical` theorem at the same d.

Live assumptions are precise: d is an inhabitant of the existing
`SparseExceptionSelectData bits target rs rb` structure. It carries validated
word-store erasures and a canonical payload-envelope proof. The length
reconciliation needs the stores' erasures and component definitions; the
canonical inequality additionally consumes d's existing envelope theorem.
The leaf does not prove an envelope for unconstrained arbitrary arrays.
No shape, canonical-builder identity, positive payload length, threshold,
readiness, or additional correctness premise is added.

`directoryAllocationFacts d` is a typed conjunction of the exact omitted-table
equality, the bound by `d.payload.length`, and the canonical bound, all at the
same selected arrays. A separate temporary import projected each field into an
independently written expected type. The same check instantiated the canonical
bound with `sparseExceptionSelectData bits target` for arbitrary bits/target,
and checked the two-target bound with four independent overhead parameters.

## Independent review and anti-vacuity

The read-only `/root/select_inventory` review confirmed that all sixteen
components and all four omissions match the existing directory definitions.
Flag arrays erase to their flag lists, while rank auxPayload excludes those
flag lists, so the sum has no duplicate flag-vector charge. The review also
requested changing a comment from "bytes" to "bits"; that repair is in the
final checked source. This local source review is separate from the mandatory
whole-candidate exact-commit audit.

Let P(d) be the exact equality in `directorySegments_length_add_omitted`.
The retained `directorySegments_positive_extra_breaks_exact_count` theorem
universally quantifies the same d, an extra bit list, and a premise
`0 < extra.length`. It refutes the same equality after appending extra to the
selected serialization, while retaining exactly the same four omission terms
and the same `d.payload.length`. Choosing a positive selected component as
extra gives the requested duplication attack. This theorem targets the exact
count identity; it does not assert that every positive addition exceeds the
looser canonical upper bound. No temporary mutation campaign is used as
acceptance evidence.

## Command ledger and trust

All commands ran on Windows with HEAD
`0e6a00f654abc64f8b68988fa9675b9a839dca2f` and the task's uncommitted branch.
The approved runner was `docs/internal/extensions/bv1/run_command.ps1`, with
the directly installed pinned binary
`C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0/bin/lake.exe`,
`LEAN_NUM_THREADS=1`, and task-local `.lake/build` outputs. The lead explicitly
chose 180-second deadlines for this slot. The direct toolchain avoids the
previously reported elan-shim network attempt. No shared mutable cache was used.

| Stage | Arguments | Duration | Outcome | Durable output |
| --- | --- | --- | --- | --- |
| Development `allocation-facts` | `build RMQ.Core.WordRAM.Bitvector.AllocationFacts` | 26.827 s | Exit 1: `.trans` field notation is unavailable on Nat inequalities in this Mathlib-free environment. Exact serialization/count proofs elaborated; no timeout. | `commands/allocation-facts.json` |
| Final `allocation-facts-repair-1` | `build RMQ.Core.WordRAM.Bitvector.AllocationFacts` | 8.193 s | Exit 0, clean build without Lean warnings. Material repair: use explicit `Nat.le_trans`; comment terminology corrected simultaneously. | `commands/allocation-facts-repair-1.json` |
| Typed/trust `allocation-facts-axioms` | `env lean <temporary-directory>/bv1-allocation-facts-exact-types.lean` | 9.943 s | Exit 0; five exact-type consumers passed and eight axiom inventories printed; no warnings or stderr. | `commands/allocation-facts-axioms.json` |

All three runs recorded `TimedOut=false`, `OutputLimitExceeded=false`,
`TerminatedIds=[]`, and ownership `kill-on-close-job`. The initial expected
failure preserved stderr `error: build failed`. Both successful runs had empty
stderr. The wrapper also emitted the existing Git global-ignore access warning;
it did not alter the compiler outcomes. No unchanged failed command was rerun:
the source repair preceded the successful rebuild.

Axiom inventories:

- `segmentBits_payload`, `directorySegments_bits_eq`: `[propext]`.
- `directorySegments_length_add_omitted`,
  `directorySegments_length_le_payload`,
  `directorySegments_length_le_canonical`,
  `directorySegments_both_length_le`,
  `directorySegments_positive_extra_breaks_exact_count`, and
  `directoryAllocationFacts`: `[propext, Quot.sound]`.

Both full working-tree trust scans required by AGENTS returned no matches
(normal `rg` no-match exit 1). `git diff --check` passed with only the existing
LF/CRLF notice for the lead's `lakefile.toml` edit. This worker did not edit that
file. Broad gates, strict design checks, committed-range verification and the
independent full audit remain with the lead; they are not duplicated for this
pure serialization-counting leaf.

Final source: `AllocationFacts.lean`, 5997 bytes, SHA-256
`F189969208B13333219EE460DB8581D43BABB88F18480C68A37F47C070801623`.

## Proof digestion and handoff

Conceptually, physical select uses the true-rank samples of its two exception
flag directories. The existing logical payload also accounts for their false
samples. The new theorem accounts for this exact difference and proves that
the actual selected arrays stay within the old envelope for either Boolean.
The combined theorem adds both Boolean directory charges explicitly.

In plain English, selecting only the components used by the physical controller
does not cost more bits than the already-bounded generic directories. The proof
works for every valid generic directory instance and keeps all long/sparse
exceptional payload components. The named downstream consumer is the lead's
same-allocation capacity theorem and ultimately
`RMQ.PackedBitvector.fullyChargedBitvectorCapstone_holds`.

The next skeptical question is whether descriptors recover these exact retained
components from one numerical memory and whether raw data, rank data, shared
tables, headers, alignment, code and scratch complete the same capacity sum.
Those full-BV-1 obligations remain OPEN. The lead owns their composition,
shared design/digestion entries, commits and independent acceptance. No shared
file or previously frozen normalization artifact was changed by this leaf.
