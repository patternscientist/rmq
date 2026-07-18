# Option B: Fully Charged Four-Russians Route (B0 Design)

Status: coordinator-approved direction (user decision 2026-07-17); B1/B2 core
in progress. This document governs the B campaign rungs and the amended E1
target. It is a delegation/design document, not a public claim surface.

## Decision

Replace every unit-cost word-level primitive in the accepted RMQ query route
with charged table lookups over half-word chunks plus ordinary arithmetic, so
that the charged instruction repertoire collapses to memory reads (and, at the
E1 machine level, individually charged arithmetic/comparison/branch/register
steps). This is the Fischer–Heun / four-Russians precedent shape. Rationale:
the project goal is to minimize precedent-free justification a reviewer must
audit; a unit-cost word-min-excess primitive (Option A) is technically
justifiable but bespoke, while o(n)-bit lookup tables are the
pattern-matchable standard. The E1-01R3 obstruction
(`e1R3FamiliarMachineTarget_obstruction`, commit `7fe5b8b`) proved the old
per-position-charged contract unsatisfiable; this design supersedes that
contract rather than repairing it.

Evidence base: architecture scout 2026-07-17 (C05 round log entry in
`AUDIT_AND_A_DESIGN.md`): of the accepted 76 events only 5–9 are
`wordRank`/`wordSelect`; the interior directory (<=30) is already pure
`FixedWidthNatTable` reads; the one event-silent computation is the fringe
min-excess/argmin scan in `LocalBPDecoder.lean`.

## Model statement (end state, public wording)

The machine model is the standard transdichotomous word-RAM: memory words of
`machineWordBits`-many bits (Θ(log n)), unit-cost word reads. Every charged
trace event is a memory read; the trace-level cost of a query is its read
count, bounded by a single literal for all sizes. The E1 machine additionally
charges every controller, decode, arithmetic, comparison, branch, and register
step and proves a separate literal total. Decoding a fetched word into a
register value is part of the read (a read returns a machine integer); no
in-word rank/select/min-excess primitive is assumed.

## B1/B2 core design

### Chunk geometry

- Chunk width: `chunkBits n = Nat.log2 n / 2 + 1` (positive for all n; reuse
  or mirror `SuccinctSpace.subLogBlockSize` at
  `RMQ/Core/SampledLayoutBudget.lean:54` which already carries
  `two_pow_subLogBlockSize_sq_le` and `subLogBlockTableRows_littleO`).
- The accepted local window is 4 machine words (`localBPWindowBits`,
  `take (4 * wordSize)`); at chunk width ~w/2 that is ~8 chunks per window.

### Table content

One `FixedWidthNatTable`-style structure (pattern:
`RMQ/Core/SuccinctSpace/Tables.lean:23,86`, consumed end-to-end by
`InteriorDirectory.lean:1622-1699` including store/erasure/provenance)
indexed by chunk bit-value, with fields per entry:

- `deltaExcess`: total excess change across the chunk
  (`2*popcount - chunkBits`, offset-encoded to stay in `Nat`);
- `minPrefixExcess`: minimum prefix excess within the chunk (offset-encoded);
- `argMinPos`: leftmost position attaining the minimum.

Row count `2^(chunkBits n)`; total bits `O(sqrt(n) * polylog(n)) = o(n)` via
`LittleOLinear` algebra (`RMQ/Core/SuccinctSpace/Asymptotics.lean`); if the
direct product lemma is awkward, use the `/8`-width slack trick proven in
`RankSelectCompressedSubLog.lean:25`.

### Boundary handling (worker's choice, correctness + o(n) required)

Fringe ranges start/end mid-chunk. Acceptable mechanisms:
1. secondary boundary table indexed by `(chunkValue, offset)` — rows
   `2^(chunkBits) * chunkBits`, still o(n); or
2. silent masking arithmetic that reduces a boundary chunk to an equivalent
   full-chunk query (careful: BP excess semantics treat 0 as close; masking
   must not corrupt excess — justify or reject);
3. charging the at-most-two boundary chunks per fringe by a second lookup.

### Charged fringe evaluation

A new costed/trace path computing the exact left/right fringe candidates now
produced by `localBPLeft/RightFringeCandidateSeededCosted`
(`LocalBPDecoder.lean:1071,1087`): the existing 4 window-word reads, then per
chunk one (or two, boundary) charged table reads into the new store region,
combined by a fixed-shape silent fold (constant arithmetic per chunk, no
per-position scan, no unbounded recursion). The seed threading must preserve
`localBPWindowBits_alone_does_not_determine_base_excess`
(`LocalBPDecoder.lean:609`): base excess comes from the directory seed exactly
as today.

Required theorems (names indicative):
- table correctness: entry fields agree with `bpExcessAtBits` /
  `bpPrefixRangeMinExcessBits` / argmin (`LocalBPDecoder.lean:1728-1756`,
  `EndpointFringe/PrefixRange/PrefixArgMin.lean:392`) on the chunk;
- fringe-value equivalence: the charged chunked fringe candidate equals the
  accepted seeded fringe candidate for every valid invocation reachable from
  the accepted route (value-level identity, not just result agreement);
- literal read-count bound for the chunked fringe (all sizes, no guards);
- store extension: new `ReviewerSource` constructor(s) for the table(s),
  erasure extension (`reviewerSources_erases` fold,
  `ReviewerPhysical.lean:725,786`), per-source linear capacity bound feeding
  `PhysicalWords_length_le_capacity` (`ReviewerPhysical.lean:1771`;
  crude `2^(chunkBits)*w <= 4n`-style bounds suffice given
  `reviewerCapacity n = 400000*(n+1)`);
- table bits fold into the space overhead: amended
  `buildPayload`/`overhead` with the public shape
  `buildPayload.length <= 2*n + overhead n`, `overhead = o(n)` preserved
  (`SuccinctRMQClassic.lean:925-941`).

### Explicit non-goals for the B2 core rung

Full provenance regeneration (B4), rank/select leaf recharge (B3), whole-route
constant re-derivation and headline swap (B5), E1 machine construction, and
doc/claim migration. BUT: per the standing anti-scaffolding rule (round log
2026-06-18, "never stop with unwired scaffolding"), the B2 core rung is not
closed until either (a) the chunked fringe is wired into the accepted
whole-query route with the cost chain re-derived, or (b) the equivalence
theorem is consumed by a committed bridging theorem that pins the future
wiring (an exact-value substitution lemma at the accepted route's fringe call
sites), with the wiring rung named as the immediate successor. Prefer (a) if
time permits.

## Constants policy

The current 76 becomes a frozen historical bound alongside 328/4144/118
(pattern: `SuccinctRMQClassic.canonicalTransitionalQueryCost`). The new
route literal is derived, never asserted; expected magnitude 150–250.

## Staging (from C05 feasibility scouts)

B1 tables (1–1.5 rounds) -> B2 fringe recharge (2–3, riskiest, this campaign)
-> B3 rank/select leaves + store consolidation (2–3) -> B4 provenance
regeneration (2–3) -> B5 cost/headline re-derivation + doc migration + alias
consolidation + compatibility pruning (1–1.5) -> E1-R4 standard machine ->
A07 blind audit at the B-complete commit -> V1.

Pivot tripwire: if B2 stalls beyond ~1 week of repair rounds, fall back to
Option A (charged word primitives + explicit model statement), reusing B1
tables as the primitives' realizability justification.
