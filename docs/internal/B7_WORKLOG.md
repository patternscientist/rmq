# B7 Worklog - charged sparse-table level (worker B7-01)

Branch `claude/b7-charged-sparse-level`, worktree
`C:\Users\poin\Documents\RMQ\.worktrees\b7-charged-level`, base `f6564ec`.

## Milestone 0 - mechanism determination (this commit)

Finding re-verified at source at `f6564ec`; all four executed sites and
both underlying definitions confirmed. Full evidence, the rejected
alternatives, and the literal derivation are in DD-20260718-012
(`docs/internal/DESIGN_DECISIONS.md`). Summary:

- CHOSEN: mechanism 3, in a single-source single-read form. One new
  counted table `bpSparseLevelTable` over domain
  `macroSize + macroCount + 1`, cell `i` packing
  `Nat.log2 i * D + bpSparseLogSpan i`, unpacked by constant-divisor
  div/mod. One charged read per two-span call.
- The SPAN (`bpSparseLogSpan = 2 ^ Nat.log2`, `SparseArgMin.lean:598-599`)
  is part of the finding, not a separate issue - `Nat.pow` is a second
  Theta(log n) recursion at the same site. Charging only the level would
  not close the rung. This is why the stored cell is a packed pair.
- REJECTED 1 (already-charged read): the level forms the ADDRESS of the
  first read of the span, so it must be known before any charged read
  occurs; the reads present return a single `Option Nat` each.
- REJECTED 2 (widen an existing entry): one query needs the levels of
  three DIFFERENT runtime values on the cross-macro branch, so no single
  entry suffices; and the offset cell has ~1 spare bit.
- REJECTED 4 (restructure): indexing the sparse cell by span instead of
  level costs `n * macroSize` bits, i.e. Theta(n polylog), destroying o(n).
- NOT EVALUATED, per the user decision: an `msb`/`log2` ISA instruction,
  or weakening a bound to accept Theta(log n) work.

### Derived consequence: the route literal MOVES, 207 -> 210

Derived rather than assumed, from the exactly-tight chain
5 (`spanCandidateCosted_cost_le_five`) -> 10
(`twoSpanCandidateCosted_cost_le_ten`) -> 30
(`bpTwoLevelInteriorCandidateCosted_cost_le_thirty`, attained on the
cross-macro branch). One added read per two-span call gives 11 -> 33, and
`closeLCA = 2*11 + 2*37 + 33 = 129`,
`wholeQuery = 2*35 + 129 + 11 = 210`. B6 left 207 unmoved because its
recharged leaf was not on the maximizing branch; this one is.

### Corroboration

DD-20260718-011 (E1-R4m, tail of `DESIGN_DECISIONS.md`) independently
flagged the same `Nat.log2` / `2 ^ Nat.log2` computation as an open
ISA-level item and explicitly did not decide it. This entry decides the
route side of it.

### Recorded for the uncharged-computation inventory, not relied on here

`summaryCosted` (`RelativeSummary.lean:735-754`) charges four reads;
`bpRelativeSummaryMinCandidate`
(`EndpointFringe/PrefixRange/RelativeSummaryCandidate.lean:15-22`) never
projects the `maxRel` field. One of the four reads is dead at the
min-candidate site. Dropping it would take the span cap 5 -> 4, the
two-span cap 10 -> 8, and the interior cap to 24, so the B7 read would
fit under the existing 30 and the literal would NOT move. This was NOT
adopted: it changes shared summary machinery used by max-candidate
consumers, its blast radius is far outside this rung, and it is an
optimization rather than the charged-level fix. Flagged for coordinator
adjudication.

## Verification ledger

- Baseline `lake build RMQ` at `f6564ec`: launched under the
  `Global\RMQHeavyVerification` mutex; result recorded at the next commit.

## Milestone 0b - corrections of record and the decisive number (commit 2)

The coordinator relayed read-only scout findings that CONTRADICTED this
worker's own subagent survey on the single most important structural
question: which family is executed. Both accounts were checked at source;
the coordinator's is correct and mine was backwards. Full detail in
DD-20260718-013.

- EXECUTED FAMILY: `FlatStoreComputation`, rooted at
  `canonicalRelativeRmmInteriorRangeMinComputation`
  (`InteriorDirectory.lean:2185`). The three class-(a) sites are
  `InteriorDirectory.lean:2117`, `:2131`, and `SparseArgMin.lean:599`.
  The `PayloadLive*` chain I cited in DD-20260718-012 is the refinement
  ladder and dead-ends at `SuccinctFinalRAM.lean:2238`.
  LESSON WORTH KEEPING: the two ladders are near-homonyms, so a
  caller-chain walk started on the wrong one terminates plausibly instead
  of failing visibly. Route claims should be anchored at the flat-store
  root, not at whichever family a name search reaches first.
- NO NEW SEGMENT. `flatStoreExecutionTraceResultAtSegment`
  (`InteriorRAM.lean:175-180`) puts the whole interior execution on one
  component segment, so the new table is a region of the existing interior
  component store. REQ-B7-04 is lighter than frozen.
- THE DECISIVE NUMBER, read from the cap proof rather than inferred: the
  interior cap 30 is GENUINELY TIGHT. In
  `canonicalRelativeRmmInteriorRangeMinCosted_cost_le_thirty_of_size_ge_four_of_bounded`
  (`InteriorDirectory.lean:4451-4510`) the cross-macro branch applies
  `..._cost_le_thirty_of_macro_crossing` directly against the cap with no
  `Nat.le_trans` and zero slack (the other branches carry 12, 10, 10).
  So interior 30 -> 33, closeLCA 126 -> 129, literal 207 -> 210, and this
  is a 3-4 session rung because the moved literal drags the full
  claim-registry and doc migration surface.
- SIZING SUPERSEDED: one generic count-indexed table, instantiated twice,
  reusing `logLogSampledDirectoryOverhead_littleO` (`Asymptotics.lean:243`)
  and `eventually_scale_log2_succ_cube_le_self` (`:516`).

Note on DD-20260718-012: its MECHANISM decision stands unchanged (a new
count-indexed charged table delivering BOTH level and span, one read per
two-span call). Its site citations and its merged-domain sizing are
superseded here; its literal derivation reached the right answer for a
partly wrong reason (it reasoned from the `PayloadLive` caps of 5/10/30
rather than the executed family's) and is now established on the executed
family.

## Verification ledger

- Baseline `lake build RMQ` at `f6564ec` under the
  `Global\RMQHeavyVerification` mutex: launched at session start, fresh
  tree, 243 jobs.

## Milestone 1 - the generic charged table (commit 3)

`RMQ/Core/SuccinctClose/EndpointFringe/PrefixRange/SparseLevelTable.lean`,
new module, imported from `InteriorDirectory.lean:3` so the root build
compiles it. Nothing consumes it yet - this is the parallel half of
parallel-then-swap, matching the B2/B6 precedent.

Contents (all green, no sorry/axiom/native_decide):

- `bpSparseLevelDomain bound = bound + 2`, with
  `two_le_bpSparseLevelDomain` and `bpSparseLevelDomain_covers`
  (`count <= bound -> count < domain`), the coverage feed for both
  instantiations.
- `bpSparseLevelCell domain i = bpSparseLogSpan i + domain * Nat.log2 i`.
- THE TWO PROJECTIONS, which are the value-equivalence core of REQ-B7-02:
  `bpSparseLevelCell_div : cell / domain = Nat.log2 i` and
  `bpSparseLevelCell_mod : cell % domain = bpSparseLogSpan i`, both under
  `2 <= domain` and `i < domain` only. Supporting:
  `bpSparseLogSpan_lt_of_lt` (the `i = 0` case matters -
  `bpSparseLogSpan 0 = 1`, which is why the domain is `bound + 2`),
  `log2_lt_of_lt`, `bpSparseLevelCell_lt : cell < domain * domain`.
- `bpSparseLevelEntries`, `_length`, `_getElem?`, `bpSparseLevelWidth
  domain = Nat.log2 (domain * domain) + 1`,
  `bpSparseLevelEntries_lt_two_pow` (the `ofEntries` obligation).
- `PayloadLiveBPSparseLevelTable domain overhead` wrapping
  `FixedWidthNatTable`, with `payload`, `payload_length`,
  `readCellCosted` (the single charged read), `readCellCosted_cost = 1`,
  `_cost_le_one`, `_erase`, and the two equivalences
  `readCellCosted_erase_div` / `readCellCosted_erase_mod`.
- `bpSparseLevelTableOverhead domain = domain * bpSparseLevelWidth domain`,
  `bpSparseLevelTable_payload_length`, and the construction
  `bpSparseLevelTable bound`.

Deliberately generic in `domain` so it can be instantiated twice per
DD-20260718-013 correction 3, rather than merged over a summed domain.

## RESUME INVENTORY (verified file:line, for the next session)

Remaining work in dependency order. Steps 1-3 are the swap; 4 is the
literal migration; 5-6 close the rung.

STEP 1 - instantiate the table twice, beside the existing tables.
  `canonicalRelativeRmmInteriorLocalTable` (`InteriorDirectory.lean:1418`)
  and `canonicalRelativeRmmInteriorGlobalTable` (`:1432`) are the models.
  Local instance: `bound = (RelativeRmm.canonicalLayout shape).macroSize`.
  Global instance: `bound = (RelativeRmm.canonicalLayout shape).macroSampleCount`
  (NOTE: the global slot function uses `layout.macroSampleCount`, see
  `InteriorDirectory.lean:2105-2107`, not `macroCount`).

STEP 2 - extend the interior component store and offsets.
  `canonicalRelativeRmmInteriorComponentStore` (`InteriorDirectory.lean:1494`)
  is a right-nested `BoundedPayloadWordStore.append` over SIX tables in
  counted directory-payload order (baseline, minRel, maxRel, argOffset,
  local sparse offset, global sparse block). Append the two new tables as
  regions 7 and 8. Then extend
  `CanonicalRelativeRmmInteriorComponentOffsets` (`:1513`, a 7-field
  structure with `deriving Repr, DecidableEq`) with `localLevel` and
  `globalLevel` fields, and `canonicalRelativeRmmInteriorComponentOffsets`
  (`:1523`) with their word offsets; `deadAddress` (last field) must move
  past both. NO new segment and NO new `ReviewerSource`: the whole interior
  execution is mapped onto one component segment by
  `flatStoreExecutionTraceResultAtSegment` (`InteriorRAM.lean:175-180`),
  consumed at `ConcreteDirectoryRAM.lean:1113`.

STEP 3 - amend the two executed sites.
  `canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation`
  (`InteriorDirectory.lean:2112`, `let level := Nat.log2 count` at `:2117`,
  `bpSparseLogSpan` at `:2118`) and
  `canonicalRelativeRmmMachineGlobalTwoSpanCandidateComputation`
  (`:2126`, log2 at `:2131`, span at `:2132`). Replace both `let`s with a
  `FlatStoreComputation.bind` on
  `canonicalRelativeRmmMachineReadNatComputation` (`:1932`, the existing
  read combinator) against the new table at the new offset, then unpack by
  `/ domain` and `% domain` using `bpSparseLevelCell_div` / `_mod`. The
  read must be sequenced BEFORE both span reads, since the level is the
  address argument of the first one
  (`canonicalRelativeRmmMachineLocalSpanCandidateComputation`, `:2079`).

STEP 4 - cost caps and the literal, 207 -> 210.
  Per-two-span cap 10 -> 11:
  `canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted_cost_le_ten_of_macro_crossing`
  (`InteriorDirectory.lean:4310`) and the global twin (`:4334`); the
  underlying span caps at `:4224` / `:4260` are UNCHANGED (the new read is
  per two-span, not per span). Branch caps: within-macro `:4289`
  (18 -> 20), adjacent `:4358` (20 -> 22), left-middle (20 -> 22), all still
  under 30; cross-macro `..._cost_le_thirty_of_macro_crossing` 30 -> 33 -
  THIS is the one with zero slack. Then
  `canonicalRelativeRmmPrincipledInteriorChargedTraceCost` (`:1783`)
  30 -> 33 and the branch dispatcher
  `canonicalRelativeRmmInteriorRangeMinCosted_cost_le_thirty_of_size_ge_four_of_bounded`
  (`:4451`). NOTE the lemma NAMES embed the numerals ("ten", "thirty");
  decide rename-versus-keep against the frozen-identity rule before
  touching them, and check `SuccinctCloseProposal.lean:95`, which consumes
  `bpTwoLevelInteriorCandidateCosted_cost_le_thirty`.
  Then the algebra at `SuccinctFinalRAM.lean:8810-8820`
  (`interiorDirectory := 30` -> 33), `..._CloseCost_eq = 126` -> 129
  (`:8818`), `..._TraceCost_eq = 207` -> 210 (`:8822`), all by `rfl`.
  Freeze 207 as
  `concreteBPNativeSuccinctRMQSilentSparseLevelChargedTraceCost` following
  the 142/76/328 pattern already at `SuccinctFinalRAM.lean:8825-8875`.
  Consumers to migrate: `Headlines/RMQ.lean:70/:497/:529`,
  `Validation/SuccinctClassic.lean:266`,
  `Validation/SuccinctClassicCostHarness.lean:118` (`canonicalBoundIs207`),
  `RMQExamples/Concrete.lean:84`, `scripts/paper_topology_lint.ps1`
  (`SumLe207`), `scripts/headline_axiom_check.lean`. Frozen legacy anchors
  untouched.

STEP 5 - space accounting (REQ-B7-06).
  Two overheads, each dominated separately. Global instance: reuse
  `logLogSampledDirectoryOverhead_littleO` (`Asymptotics.lean:243`) via
  `LittleOLinear.of_le` (`:35`). Local instance: repackage
  `eventually_scale_log2_succ_cube_le_self` (`Asymptotics.lean:516`).
  Do NOT copy `bpFringeTableOverhead_littleO` - its exponential-slack
  threshold step is vacuous for a count-indexed table. Linear-capacity
  feed analogues of `bpFringeChunkRowCount_le_linear` and
  `bpChunkSelectEntryWidth_le_machineWordBits_capacity` are still needed.
  Public statement shape template: `ChargedFringeSpace.lean:37-77`.

STEP 6 - provenance, vocabulary theorem, docs.
  Regenerate the producer-provenance packets with a level-read path and a
  W19 successful-occurrence witness on an execution that actually reads
  the level table; re-prove
  `concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_readWord_only`
  over the amended route; repair the charge-policy section of
  `docs/PAPER_MODEL_ADEQUACY.md` with the representation-artifact versus
  algorithmic-work principle and named bridge lemmas; then the stretch
  inventory (STRETCH-01), whose first known entry is the dead `maxRel`
  read recorded in DD-20260718-012.
