# Adversarial Architecture Fixed-Point Audit — Compact Long-Super Exception Locator (2026-06-21)

Design audit (not implementation). Audits the proposed repair of the long-super
branch of `RelativeSplitSparseExceptionFalseSelectCloseData`. **Not a claim of C1
closure.**

## Grounding (verified against current surfaces)

- **Misspec is precise.** `relativeSplitSparseException_long_super_padded_payload_not_littleO`
  proves: if `longSuperRelativeEntries.length ≥ superSlotCount * superStride`
  (the padded grid keyed by `superSlot * superStride + localOccurrence`) and the
  table payload is the overhead, then `¬ LittleOLinear overhead` — because
  `superSlotCount * superStride ≈ #occurrences ≈ n`.
- **The repair pattern already exists on the sparse-local side.** The
  sparse-local exceptions are already compact and o(n)
  (`builtRelativeSplitFalseSelectSparseExceptionRelativeTable`, relative width
  `≤ 4·ell ≤ machineWordBits`, `…_payload_le_overhead`,
  `sparseExceptionRelativeTableOverhead_littleO`).
- **The flag-rank directory already exists** as
  `builtRelativeSplitFalseSelectFlagRankData` (a two-level rank over flag bits,
  with `_profile`).
So the repair is **not new technology** — it mirrors the working sparse-local
machinery onto the long-super fields. That is why no broad redesign is warranted.

The proposed repair: flag bits over actual long-super exception blocks, charged
rank over those flags, dense relative-entry table indexed by
`exceptionRank * stride + localOccurrence`. The rest of this doc tries to break it.

## Break attempts → blockers → patches (to fixed point)

### Category A — hidden LINEAR payload

- **A1 (the central one): "compact" still linear if many supers are long.**
  If `exceptionCount` is only bounded by `#supers = n/superStride`, then
  `exceptionCount * superStride = n` — still linear. The compaction buys nothing
  unless `exceptionCount` is genuinely sublinear.
  *Patch / obligation:* a **proven disjointness count bound**
  `longSuperExceptionCount ≤ bpCode.length / superLongSpan`, derived from
  `Σ(long-super spans) ≤ bpCode.length` (long spans are disjoint) and
  `superLongSpan = superStride * w * ell`. Then
  `exceptionCount * superStride * width ≤ (2n/(superStride·w·ell))·superStride·w
  = 2n/ell = o(n)`. This bound must be a theorem from `shape.bpCode`, **never a
  record field or builder hypothesis.**
- **A2: flag-vector universe linear.** If flags are one bit per *position* or per
  *occurrence*, the flag vector itself is Θ(n).
  *Patch:* flag universe = `superSlotCount` (one flag per super), with
  `superSlotCount ≤ n/superStride` and `superStride ≥ w²` ⇒ flag vector is o(n).
- **A3: flag-rank directory uncounted.** The rank-over-flags needs its own
  directory; if its overhead isn't in the total, the o(n) sum is incomplete.
  *Patch:* include `flagRankOverhead` (already `builtRelativeSplitFalseSelectFlagRankData`)
  as a summand of the total overhead; it is o(n) because it is a rank over an
  o(n)-bit vector.
- **A4: non-uniform stride / variable span.** If the per-exception segment uses
  the *actual span* (large for long supers) rather than the fixed occurrence
  count, the table is large.
  *Patch:* `stride := superStride` (fixed occurrences/super); store one entry per
  occurrence-in-super, `superStride` per long exception; prove
  `localOccurrence < superStride`.
- **A5: vacuous space proof.** `LittleOLinear (fun _ => payload.length)`.
  *Patch:* require `LittleOLinear (overhead : Nat → Nat)` **and**
  `payload.length ≤ overhead shape.size`, where `overhead` is the explicit sum.

### Category B — uncharged search

- **B1: `exceptionRank` by scan.** `exceptionRank = (flags.take superSlot).count`
  is an O(#supers) uncharged search masquerading as O(1).
  *Patch:* `exceptionRank := (flagRankData.rankCosted superSlot)` — charged,
  cost ≤ const, via the flag-rank directory. Forbid `List.count`/`take`/`filter`
  in the query path.
- **B2: flag-bit / super-base by scan.** Deciding "is this super long" or reading
  the super base must be charged O(1) table reads, not recomputed from `bpCode`.
  *Patch:* charged `FixedWidth` reads for the flag bit and the super base.
- **B3: uncharged routing index.** Any `exceptionIndex : Nat → Nat` left as a
  free function can hide predecessor/search.
  *Patch:* the only index arithmetic allowed is `q/superStride`,
  `q - superBase`, and `exceptionRank*superStride + localOccurrence`; everything
  else must be a charged read. `exceptionRank` must be *defined as* the charged
  flag-rank, not an opaque function.

### Category C — answer-as-premise exactness

- **C1: exactness supplied as a field.** A record field
  `long_explicit_exact : … = select false bpCode q` is answer-as-premise.
  *Patch:* derive it via a `…_lookup_exact` theorem from the builder, exactly as
  the sparse side does via `sparseDenseFalseSelectBranchObligations_of_built_entries`.
- **C2: rank≠compaction-index gap.** The query uses `exceptionRank` to index the
  compact table; this is correct **only if** `flagRank(superSlot)` equals the
  position of `superSlot` among long supers in the table's build order.
  *Patch:* `compactLongSuperFlagRank_eq_segmentIndex` — proven from the
  co-construction (table built by `flatMap` over long supers in flag order;
  flag-rank = `rank₁(flags, superSlot)`). This is the linchpin correctness lemma.
- **C3: conditional exactness.** Exactness proved only "when the answer is in the
  segment" (a hypothesis that pre-locates the answer).
  *Patch:* prove **segment coverage**: for every `q` in a long super,
  `exceptionRank*superStride + (q - base)` is in-bounds and stores `select(q)` —
  unconditionally over all close indices.
- **C4: assumed disjointness.** A4/A1's count bound supplied as a hypothesis.
  *Patch:* `longSuperSpanSum_le_bpCode_length` proved from BP/select semantics.

### Category D — non-word-bounded reads

- **D1: packed multi-field entry.** Reviving the 4-fields-in-one-word locator is
  the original obstruction.
  *Patch:* compact long table = `FixedWidthNatTable`, **one field per word**,
  width `≤ machineWordBits bpCode.length`.
- **D2: missing word bounds.** Flag vector words, flag-rank directory words, and
  compact-table words each need a machine-word bound.
  *Patch:* `ReadWordsLengthLeMachine` for each new table, from
  `fieldWidth ≤ machineWordBits`.
- **D3: stored value width.** Storing the absolute select position is width `w`
  (= machineWordBits) — acceptable as one field/word; relative-to-base is
  narrower. Either is fine **if** the width ≤ machineWordBits is proven.

### Fixed point

No further architectural blocker remains short of ordinary Lean proof work,
**provided** the linchpins hold: (i) the disjointness count bound A1/C4, (ii) the
charged flag-rank B1, (iii) the rank=segment-index lemma C2 with unconditional
segment coverage C3, (iv) one-field-per-word D1, (v) a single explicit
`LittleOLinear` sum A5/A3. The sparse-local side already satisfies the analogues,
which is evidence the fixed point is reachable.

## Deliverables

### Must-change interface items
1. **Replace the long-super exactness coordinate** in the record from
   `superSlot * superStride + localOccurrence` to
   `longExceptionRank * superStride + localOccurrence`.
2. **Add (or reuse) a long-super flag-rank field**: a flag bitvector over
   `superSlotCount` + a `FlagRankData` directory (reuse
   `builtRelativeSplitFalseSelectFlagRankData`).
3. **Long-super table = `FixedWidthNatTable`**, one field/word, width
   `≤ machineWordBits`.
4. **Overhead must be an explicit `Nat → Nat` sum** of: super inventory +
   flag vector + flag-rank directory + compact long table + short-local inventory
   + sparse flag/rank/compact + dense split + aux — with `payload.length ≤ sum`.

### Proof obligations
- `longSuperSpanSum_le_bpCode_length` (disjoint long spans).
- `longSuperExceptionCount_le_bpCode_length_div_superLongSpan`.
- `compactLongSuperFlagRank_eq_segmentIndex` (rank = build-order index).
- `compactLongSuperRelativeTable_lookup_exact` (unconditional segment coverage).
- `…_flagRankData.rankCosted` charged + `erase = rank₁ flags superSlot`.
- `ReadWordsLengthLeMachine` for flag vector, flag-rank dir, compact long table.
- `payload_length_le` over the assembled concatenation; `LittleOLinear` of the sum.

### Likely arithmetic lemmas
- `littleOLinear_id_div_logLog_succ` (n/ell is o(n)) — flagged in the
  architecture doc; prove only if consumed here.
- `exceptionCount * superStride * width ≤ 2n/ell` from the count bound +
  `superLongSpan = superStride·w·ell`.
- `LittleOLinear.add` chaining for the explicit sum (exists).
- `localOccurrence < superStride` from `q < (superSlot+1)*superStride` minus base.

### Worker-ready theorem targets (chain)
1. `longSuperSpanSum_le_bpCode_length`
2. `longSuperExceptionCount_le_bpCode_length_div_superLongSpan`
3. `compactLongSuperFlagRank_eq_segmentIndex`
4. `compactLongSuperRelativeTable_lookup_exact`
5. `compactLongSuperRelativeTable_payload_le_overhead` + `…_littleO`
6. `repairedRelativeSplitFalseSelectCloseData_profile` (or the edited record's
   `profile`): `payload.length ≤ overhead shape.size ∧ LittleOLinear overhead ∧
   selectCloseCosted.cost ≤ const ∧ selectCloseCosted.erase = bpCloseOfInorder? ∧
   read_words ≤ machineWordBits` — with the long-super branch now compact.
7. Consume in `…BPCloseAccessDirectory_profile` then the read-backed final join.

### Traps to forbid in prompts
- Any long-super table with `length ≥ superSlotCount * superStride` (the proven
  misspec) or any `superSlot * superStride` index.
- `exceptionRank`/routing via `List.count`/`take`/`filter`/`findIdx` (uncharged).
- Long-super exactness as a record field or conditioned on a premise that locates
  the answer (`hsegment`, `… = select …` supplied).
- Assuming the disjointness/count bound instead of proving it from `bpCode`.
- Packed multi-field entries; any charged read without a machine-word bound.
- `LittleOLinear (fun _ => …)`; any overhead not an explicit `Nat → Nat` with
  `payload.length ≤ overhead n`.
- A flag vector whose universe is positions/occurrences rather than supers.

## Edit old record or new successor?

**Edit the existing `RelativeSplitSparseExceptionFalseSelectCloseData` in place.**
Reasons: (a) AGENTS.md forbids parallel APIs and prefers strengthening existing
modules; (b) the **sparse-local branch of this same record is already compact**,
so the long-super branch is just being brought to parity — a localized field
change (long-super coordinate + flag-rank field + `FixedWidthNatTable`), not a new
abstraction; (c) downstream (`…BPCloseAccessDirectory`, final join) consume the
`profile`, not the long-super coordinate, so they migrate without a parallel type.
Keep `relativeSplitSparseException_long_super_padded_payload_not_littleO` as the
recorded obstruction. Spin a successor record **only if** a downstream consumer
turns out to depend on the padded long-super coordinate in its own type signature
(not expected). The misspec is in the *builder/coordinate*, not in the record's
existence, so the record can host the compact long-super fields.

## Coordinator review — accepted corrections (folded in) + 2 refinements

The coordinator reviewed this audit and added five corrections. **All five are
valid and grounded; accept all.** Verified against the surfaces:

1. **Own flag vector, not the same object.** The existing
   `builtRelativeSplitFalseSelectFlagRankData` is over `…SparseFlagBits` (sparse
   universe). Long-super needs its **own** flag bitvector **over super slots** and
   its own rank directory. Reuse the *construction pattern*, not the object.
2. **Separate rank-overhead accounting per directory.** The record currently
   carries one `(rankSuperOverhead, rankBlockOverhead)` pair. With both
   sparse-local and long-super exception directories present, each needs its own
   rank-overhead term (or a wrapper hiding each). Do not force a shared overhead.
   (Verify which directory the current pair serves; the per-directory-accounting
   principle holds either way.)
3. **Partial last super guard.** `exceptionRank*superStride+localOccurrence` can
   address cells beyond `falseSelectOccurrenceCount` (last super is partial). Add
   a top-level valid-occurrence guard (`q < falseSelectOccurrenceCount` /
   `idx < shape.size` → `none`) **or** an option/sentinel table with a proof that
   padded offsets erase to `none`. Prefer the cheap guard. (Precise boundary case
   under-specified by A4/C3 above.)
4. **Branch/flag consistency.** `superMarked superSlot ↔
   longFlagBits[superSlot]? = some true`; else the query branches on the super
   entry while ranking over a different flag universe.
5. **Don't overstate sparse-local as "done."** The sparse-local compact
   directory/profile exists and is reusable, but the end-to-end C1 builder still
   must consume concrete built tables; "parity" ≠ "sparse-local closed to final
   RMQ." (This audit's "already compact o(n)" is a *component*-level claim.)

Two refinements on top of the corrections:

- **R-a (avoid churning the working sparse path).** "Define a generic
  `CompactExceptionDirectory`" must not become a refactor that destabilizes the
  already-working sparse-local machinery. Preferred: add the long-super compact
  directory *alongside* the existing sparse vectors/`FlagRankData`, mirroring them;
  extract a shared record only if it demonstrably *reduces* proof burden.
  (Consistent with AGENTS.md "keep changes scoped.")
- **R-b (make correction 4 free).** "Is long" is already
  `sparseDenseFalseSelectEntryIsMarked super`, and the long-flag vector is exactly
  "which supers are marked." So **define `longFlagBits := superEntries.map
  isMarked`**; then correction 4 is definitional (a one-line `getElem?`-map lemma)
  rather than a co-construction obligation, removing flag/branch divergence by
  construction.

Also retain (not re-listed in the verdict but in this plan, and must reach worker
prompts): the **machine-word / one-field-per-word** obligations (D1/D2) for every
new flag/rank/compact table, and the single **explicit `LittleOLinear` sum with
`payload.length ≤ overhead n`** (A5/A3).

**Net:** convergence, not conflict. Hardened worker spec = this audit's chain +
corrections 1–5 + refinements R-a/R-b. No broad redesign; localized interface
hardening of the existing record.
