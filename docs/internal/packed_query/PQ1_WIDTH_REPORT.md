Status: CANDIDATE_COMPLETE
I found no assigned or inherited acceptance criterion unmet; coordinator acceptance is still required.

This declaration concerns the bounded PQ1-W allocation-width leaf. It does not
declare completion of the whole-query roadmap node or its execution/register/
instruction-width obligations.

## Identity and scope

- Handle: PQ1-W.
- Worktree: `C:/Users/poin/.codex/worktrees/a84a/RMQ`.
- Branch: `codex/fully-charged-packed-query-v1`.
- Assigned base: `13d188582d3994a04f893ca0e21970c40c14b8cd`.
- Governance: `4639223bc8130b0ef752270b5cbdd74325abcd60`.
- Shared HEAD at final source check: `9e2720b991e203d22a2787abf66dbfb9888088fb`.
- Canonical skill preflight: PASS; actual runtime catalog was
  `rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint`; required role was
  `rmq-proof-sprint`.
- Owned changes: `RMQ/Core/WordRAM/Packed/Width.lean`, this report, and
  `PQ1_WIDTH_MATRIX.md`. No staging, commits, branch switch or other source edits.
- Width source SHA256:
  `03785ecfed5e168e2e5ad6bb511de2d8132bc8d72770d6a91835ebf1270e83d5`.

The builder, 174-word schema, width formula and allocation residual are imported
unchanged from Allocation.lean. The read-only source scout supplied exact source
anchors and the sentinel-count proof idea; this worker wrote and checked the
complete width proofs.

## Exact checked surfaces

All declarations below are in `RMQ.SuccinctFinal.PackedWordRAM`.

```lean
metadata_words_fit (shape : CartesianShape) :
  ∀ word ∈ metadata shape, word < 2 ^ wordWidth shape.size

buildMemory_words_fit (xs : List Int) :
  ∀ word ∈ buildMemory xs, word < 2 ^ wordWidth xs.length

buildMemory_length_fit (xs : List Int) :
  (buildMemory xs).length < 2 ^ wordWidth xs.length

buildMemory_address_fit (xs : List Int) (address : Nat)
  (haddress : address ≤ (buildMemory xs).length) :
  address < 2 ^ wordWidth xs.length

validEndpoints_fit (xs : List Int) (left right : Nat)
  (hvalid : left < right ∧ right ≤ xs.length) :
  left < 2 ^ wordWidth xs.length ∧ right < 2 ^ wordWidth xs.length
```

`allocation_width_requiredFacts` independently pins the same construction and
all object arguments, consuming those declarations with the existing space and
logarithmic-width theorems:

```lean
allocation_width_requiredFacts (xs : List Int) :
  (∀ word ∈ buildMemory xs, word < 2 ^ wordWidth xs.length) ∧
  (∀ address ≤ (buildMemory xs).length, address < 2 ^ wordWidth xs.length) ∧
  ((buildMemory xs).length * wordWidth xs.length ≤
    2 * xs.length + allocationRho xs.length) ∧
  (wordWidth xs.length ≤ 192 * (Nat.log2 (xs.length + 2) + 1)) ∧
  (∀ left right, left < right ∧ right ≤ xs.length →
    left < 2 ^ wordWidth xs.length ∧ right < 2 ^ wordWidth xs.length)
```

The shape-level intermediary `shapeMemory_length_eq` identifies the length with
the exact new-count metadata field. Consequently the first missing address is
bounded by a counted field of this allocation, rather than by an unrelated
abstract capacity certificate.

## Complete metadata coverage

`metadata_words_le_envelope` proves every actual metadata word is at most
`64 * (2 ^ packedReviewerCellWidth n) ^ 2`. The strict power bound is
`2^(6+2*oldWidth) < 2^(32+8*oldWidth)`, proved for every n.

- All 42 scalar entries are discharged by `scalarGeometry_le_envelope`:
  n, old width/count/bits, both shape-dependent counts, new width/count,
  select geometry, flag geometries, BP/fringe geometry, every interior layout
  scalar, both level domains and widths, all eight offsets and the dead offset.
- All 23 regular descriptors are discharged by
  `regularDescriptor_le_envelope`: segments 0–19 use the exact source map,
  segment 20 retains its four zeros, and segments 21–22 use the complete fringe
  and select table extents. Each four-field descriptor covers its old bit base,
  bit length, stride and logical count. Logical sentinel words are preserved:
  the count bound is `count ≤ 2*bitLength+2`, not the false `count ≤ bitLength`.
- All eight five-field interior descriptors are discharged by
  `interiorDescriptor_le_envelope`: component word prefix/count, absolute bit
  prefix, entry width and chunks per entry. Canonical directory decomposition
  bounds the bit prefix even for empty tables; component span bounds include
  the dead address. The public all-size relative/offset/block/level-width bounds
  are joined by `interiorEntryWidth_le_seven`.
- `repackWords_word_lt` then covers all body cells under the same width and
  header list; `packedReviewerCartesianShape_size` transports the shape theorem
  to ordinary List Int without changing objects.

## Verification and limits

The development checks were narrow direct Lean invocations using the private
`.lake/build/lib/lean` dependency cache and Lean 4.22.0. The first pass exposed
three definitional-normalization mismatches and one trivial reflexive goal;
the second pass exposed a simp/no-progress and dependent-match normalization
issue. Each retry followed source repairs. The third pass exited 0, including
the exact consumer above and typed cases for an empty allocation, arbitrary
singleton value, singleton [0,1) endpoints, and an arbitrary canonical shape
with symbolic positive long and sparse counts. No theorem assumes those counts
are zero; the symbolic consumer does not assert existence of such a shape.

Owned-source trust/hygiene scan found no forbidden proof/runtime shortcuts.
`git diff --check` passed on the shared tracked tree; the lead must run the
required committed-range check after integration because this owned source
was untracked during worker verification. Final emitted-artifact check and
owned whitespace evidence are recorded in the matrix command ledger.

No mutation campaign is claimed. In-module examples are direct typed consumers,
not empirical evidence for universal width. No broad Lake or aggregate gate was
run: this leaf adds one proof module, and the lead owns final integration,
strict design, public correspondence, and aggregate certification.

Invalid representable endpoint rejection remains an obligation of the primitive
program guard. The mathematical Nat API and unbounded-input parsing remain
separate. This leaf does not establish widths of arithmetic results, dormant
instructions, scratch registers, returned machine values or executed addresses
outside the allocated-plus-first-missing domain.

## Proof digestion and proposed design entry

The conceptual change is to prove numeric fit for every field actually
serialized by the builder. The payload-space bound alone could not establish
that its Nat-valued metadata were machine words. A conservative old-capacity
square supplies a common bound while leaving the physical width and dense
packing construction unchanged.

In plain English, the allocation now really can be stored in its declared word
format at every input size, and an endpoint of any valid RMQ interval can be
represented in that same format. A caller still needs a proved program that
computes its answer using only these words.

Live assumptions are the existing Mathlib-free Lean/Std trust base and the
unchanged canonical builder and width definitions. No readiness, minimum size,
assumed header fit or exceptional-count hypothesis appears in the main proofs.
A skeptical graduate student should next inspect how the final program bounds
its intermediate arithmetic and dormant code operands; fitting stored metadata
does not itself bound every calculation performed on it.

Proposed companion design-ledger append for the lead: record the common
`64*Q²` metadata envelope with `Q=2^oldWidth`, its strict embedding into
`2^(32+8*oldWidth)`, and its exhaustive consumption by the concrete metadata
schema. State why individual sharp widths were unnecessary, why sentinel
logical counts require `2*bits+2`, and why this does not discharge execution
operand widths. Cite Width.lean and the exact same-allocation typed consumer.
The ledger is lead-owned and was deliberately not edited concurrently.
