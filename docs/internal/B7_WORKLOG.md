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

## Milestone 2 - the two instantiations (commit 4, RESUME STEP 1 done)

`InteriorDirectory.lean`, added beside the existing local/global tables:

- `canonicalRelativeRmmInteriorLocalLevelTable shape`
  = `bpSparseLevelTable (RelativeRmm.canonicalLayout shape).macroSize`
- `canonicalRelativeRmmInteriorGlobalLevelTable shape`
  = `bpSparseLevelTable (RelativeRmm.canonicalLayout shape).macroSampleCount`
- `canonicalRelativeRmmInteriorLevelTableOverhead` (the sum, for REQ-B7-06)
- payload-length lemmas for both.

CONFIRMED WHILE WRITING THESE: the global bound is `macroSampleCount`, not
`macroCount`. `canonicalRelativeRmmInteriorGlobalTable`
(`InteriorDirectory.lean:1432`) is parameterized by
`layout.macroSampleCount`, and `bpGlobalSparseCellSlot` is applied to
`layout.macroSampleCount` at `:2105-2107`. DD-20260718-012's sizing prose
said `macroCount`; the instantiation uses the correct field.

Nothing consumes the instantiations yet. They are not counted payload
sources at this commit (they are not in the interior component store), so
no dead-counted-source obligation arises; this remains the parallel half
of parallel-then-swap.

Verification at this commit: `lake build RMQ` exit 0 (384.9s, zero
errors). `#print axioms` after the M1 root build, on all ten new names:
`[propext, Quot.sound]` or `[propext]` only - no `Classical.choice`, and
no `Lean.ofReduceBool`, so no `native_decide` leaked in.

## Verification ledger (cumulative)

- `f6564ec` baseline `lake build RMQ`: exit 0, 243 jobs, fresh tree.
- `78d15c3` (M1): `lake build RMQ` exit 0, 417.8s, 244 jobs, 0 errors;
  hygiene rg clean; `git diff --check` clean.
- M2 (this commit): `lake build RMQ` exit 0, 384.9s, 0 errors.
- `#print axioms` on the ten M1 names: clean (see above).

## Verification battery at `af6023d` (M2)

- `lake build RMQ` exit 0 (384.9s, 0 errors).
- `lake build RMQ RMQPaper RMQExamples` exit 0 (55.6s incremental, 0 errors).
- `git diff --check` exit 0; `git diff --check f6564ec..HEAD` exit 0.
- `design_decision_check.ps1 -Strict -Base f6564ec` exit 0 (5 changed files).
- `claim_drift_scan.ps1` exit 0. (The four `[fail]` substrings in the
  output are fixture TEXT quoted inside W15/W21 matrix rows, not
  classifications, matching the B6 ledger.)
- `paper_topology_lint.ps1` PASS, exit 0 (83 broad documentary
  identifiers; 49 paper identifiers resolved) - byte-identical counts to
  the B6 ledger, as expected since the literal has not moved yet.
  NOTE: this lint FAILS with `unknown module prefix 'RMQPaper'` until
  `lake build RMQPaper` has run in the worktree. That is a build-state
  precondition of the lint, not a claim regression; worth knowing because
  it looks alarming.
- `lake env lean scripts/headline_axiom_check.lean` exit 0, no errors, no
  `Lean.ofReduceBool`.
- `#print axioms` on the ten new names (after a root build):
  `[propext, Quot.sound]` or `[propext]` only. No `Classical.choice`, no
  `Lean.ofReduceBool`.
- Hygiene `rg` over the new module: zero hits for
  sorry/admit/native_decide/implemented_by/partial/unsafe/extern/
  noncomputable/`import Mathlib`/axiom.

### PRE-EXISTING, EXTERNALLY OWNED BLOCKER (not caused by this rung)

`lake env lean scripts/wordram_axiom_check.lean` FAILS, exit 1:

    scripts/wordram_axiom_check.lean:197:14: error: unknown constant
    'RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_nonSyntheticWeight_sum_le_76'

Verified pre-existing and NOT attributable to B7: the name occurs nowhere
in `RMQ/`; it is referenced only by `scripts/wordram_axiom_check.lean:197`
and `scripts/axiom_check.lean:975`. The delegation already records
`axiom_check.lean` as broken for two independent reasons and assigned
elsewhere; this is evidently the same defect reaching the second script.
Both files are owned by `claude/a07-blocker-repairs`, so B7 does NOT touch
them. B7's diff touches only its own five files, none in `SuccinctFinal`
and none in `scripts/`. Flagged for the coordinator: the B7 final battery
cannot be completed while this script is red, through no fault of this
rung.

## STATUS AT END OF B7-01's SESSION: INCOMPLETE

Resume steps 1 of 6 complete (M2). Steps 2-6 remain, as written in the
RESUME INVENTORY above, unchanged and still file:line accurate. The next
action is RESUME STEP 2 (extend `canonicalRelativeRmmInteriorComponentStore`
at `InteriorDirectory.lean:1494` and
`CanonicalRelativeRmmInteriorComponentOffsets` at `:1513`/`:1523` with the
two level-table regions). That step was deliberately NOT started: it is
the first structurally risky edit of the rung (a right-nested
`BoundedPayloadWordStore.append` chain plus a `deriving DecidableEq`
structure with a trailing `deadAddress` field that must move past both new
regions), and starting it without budget to finish would have left the
tree red rather than green.

Coordinator ruling received and recorded for the next session: the
207 -> 210 move is AUTHORIZED, to be executed in the established pattern -
freeze 207 as a named historical constant with its `_eq` theorem and
guards exactly as 142/76/328 are, update every Lean consumer, move the
CURRENT topology anchor `SumLe207` in `scripts/paper_topology_lint.ps1`
and `scripts/headline_axiom_check.lean`, leave the frozen legacy anchor
list untouched, and delete no historical constant.

---

# Session 2 (worker B7-02): step 2 executed, then reverted on an atomicity finding. No Lean change committed.

Branch `claude/b7-charged-sparse-level`, base `f6564ec`, session start and
session end both at `398d4e8`. This session committed DOCUMENTATION ONLY.
The Lean working tree was restored to `398d4e8` before commit.

## THE DECISIVE FINDING: steps 2, 3, 4 and part of 5 are ONE commit

This supersedes the six-step plan's implied commit granularity and is the
main reason this session landed no Lean change.

Step 2 (extend the component store) cannot be committed on its own, and
neither can steps 2+3 without 4. The chain, each link verified at source
this session:

1. Putting the two level tables into
   `canonicalRelativeRmmInteriorComponentStore` forces them into the
   COUNTED payload, because `CanonicalRelativeRmmInteriorStoreProfile`'s
   field `component_flattens` (`InteriorDirectory.lean:5456`) asserts
   `flattenPayloadWords (store.words.toList) = <the enumerated payloads>`,
   and `canonicalRelativeRmmInteriorDirectory.payload` (`:4962`) must match
   it. There is no way to add a store region without adding a counted
   payload region. VERIFIED: leaving `canonicalRelativeRmmInteriorDirectory`
   unamended makes `RMQ.Core.SuccinctFinal.RAM.FlatPayload` fail to build
   (decisive line pasted in the ledger below).
2. A counted payload region that no execution reads is a DEAD COUNTED
   SOURCE, which the standing rules forbid at every commit. B7-01's M2 note
   is the same reading from the other side: the instantiations were safe to
   commit at M2 precisely BECAUSE they were "not in the interior component
   store".
3. So the reads must be wired (step 3) in the same commit.
4. Wiring a read adds a charged tick per two-span call, which falsifies
   `..._cost_le_ten_of_macro_crossing` (`:4370`, `:4394`) and every cap
   above it, up to
   `canonicalRelativeRmmInteriorRangeMinCosted_cost_le_thirty_of_size_ge_four_of_bounded`
   (`:4511`). So step 4's cap migration is in the same commit.
5. And the caps feed `canonicalRelativeRmmPrincipledInteriorChargedTraceCost`
   (`:1843`), which feeds the whole-query literal, so the 207 -> 210
   migration is in the same commit too.

Nothing in this chain is avoidable by ordering. The rung's first
committable state is the FULL swap. Plan accordingly: the next session
should expect to hold a red tree for most of its length and should not
interpret that as a defect.

## Step 2 IS WRITTEN AND IT ELABORATES CLEAN

The full store extension was implemented this session and verified to make
`InteriorDirectory.lean` elaborate with zero errors and zero warnings
(`lake env lean` on that file, no output). It was then REVERTED, per the
atomicity finding above, rather than committed red.

The diff was saved outside the repo as a 491-line patch in this session's
Claude scratchpad (`b7-step2-store-extension.patch`). That path is
session-scoped and may be garbage-collected. It is NOT relied on: the
complete edit inventory below is sufficient to redo the work from scratch,
and redoing it is mechanical.

### Edit inventory for step 2, in file order (all in InteriorDirectory.lean)

Line numbers are as at `398d4e8`. NOTE: B7-01's RESUME INVENTORY line
numbers for this file are STALE BY ABOUT 59 LINES (they predate the M2
commit that inserted the two instantiations). The path in that inventory is
also wrong: the file is under `EndpointFringe/InteriorCandidate/`, NOT
`EndpointFringe/PrefixRange/`. Corrected numbers below.

1. `:1548` (before `canonicalRelativeRmmInteriorComponentStore`) - add
   `canonicalRelativeRmmLocalLevelMachineStore` and
   `canonicalRelativeRmmGlobalLevelMachineStore`, mirroring
   `canonicalRelativeRmmLocalMachineStore` (`:1530`) exactly.
2. `:1553` `canonicalRelativeRmmInteriorComponentStore` - the payload type
   becomes `(((((summary4) ++ local) ++ global) ++ localLevel) ++
   globalLevel)` and the body a four-deep left-nested
   `BoundedPayloadWordStore.append`. (The chain is LEFT-nested at the top
   level, not right-nested as B7-01's inventory says; the right-nesting is
   only inside the summary quadruple.)
3. `:1572` `CanonicalRelativeRmmInteriorComponentOffsets` - insert
   `localLevel` and `globalLevel` between `globalBlock` and `deadAddress`.
   `deriving Repr, DecidableEq` needs no change.
4. `:1582` `canonicalRelativeRmmInteriorComponentOffsets` - add
   `globalWords` and `localLevelWords` lets, and the two new offset fields.
5. `:1607` `..._flattens_payload`, `:1621` `..._words_toList`, `:1640`
   `..._words_size_eq` - extend each with the two regions. `:1657`
   `..._words_bounded` needs NO change (it is generic).
   For `_flattens_payload` add `PayloadLiveBPSparseLevelTable.payload` to
   the simp set.
6. `:2090` - add `canonicalRelativeRmmLocalLevelReadComputation_footprint_le_dead`
   and `canonicalRelativeRmmGlobalLevelReadComputation_footprint_le_dead`,
   mirroring `:2076`/`:2090`. TWO new lemmas, not the "seventh" single one
   B7-01's inventory predicted. Simp sets must accumulate: the local-level
   one needs `canonicalRelativeRmmGlobalMachineStore` added; the
   global-level one additionally needs
   `canonicalRelativeRmmLocalLevelMachineStore`. The global-level one must
   NOT list `canonicalRelativeRmmGlobalLevelMachineStore` itself
   (unused-simp-arg linter error).
7. THE FOUR PRE-EXISTING `_refines` PROOFS AT `:2818` (maxRel), `:2872`
   (argOffset), `:2926` (local) AND `:2982` (global) ALL BREAK. This is the
   part B7-01's inventory did not anticipate. Each contains an `hmiddle`
   term that spells out the ENTIRE store word list literally, so each must
   have the two new tails appended to its `post` argument of
   `List.getElem?_append_middle_of_lt`:
   - maxRel: post `(argWords ++ localWords ++ globalWords)` becomes
     `(argWords ++ localWords ++ globalWords ++ localLevelWords ++ globalLevelWords)`
   - argOffset: post `(localWords ++ globalWords)` becomes
     `(localWords ++ globalWords ++ localLevelWords ++ globalLevelWords)`
   - local: post `globalWords` becomes
     `(globalWords ++ localLevelWords ++ globalLevelWords)`
   - global: post was the literal `[]` (it was the last region); becomes
     `(localLevelWords ++ globalLevelWords)`
   Each also needs the two new `let` bindings and the two new names in its
   trailing `simpa` set. Baseline (`:2764`) and minRel (`:2790`) do NOT
   break - their `hmiddle` shape is normalized by simp.
8. `:2982` onward - add `canonicalRelativeRmmLocalLevelReadComputation_refines`
   and `canonicalRelativeRmmGlobalLevelReadComputation_refines`. Again TWO,
   not one. The global-level one is the new last region and takes `[]` as
   its `post`.
9. `:3529` `canonicalRelativeRmmInteriorRange_successful_read_backed` -
   extend the payload decomposition in the STATEMENT with the two payloads.
10. `:5456` `CanonicalRelativeRmmInteriorStoreProfile.component_flattens` -
    extend the field's stated decomposition with the two payloads. The
    sibling fields `successful_read_backed`, `returned_words_bounded`,
    `returned_words_bounded_reviewer` do NOT name the payload and need no
    change.
11. `:1506` `canonicalRelativeRmmInteriorDirectoryPayloadLength` and `:4962`
    `canonicalRelativeRmmInteriorDirectory.payload` - add both tables.
    This is the step that makes them COUNTED, i.e. the step that triggers
    the atomicity finding above.

After 1-11, `lake env lean` on `InteriorDirectory.lean` is clean, and the
root build advances to the space-accounting obstruction below.

## THE NEXT OBSTRUCTION, located and characterised but NOT solved

With step 2 complete the root build fails in exactly two places, both in
`InteriorDirectory.lean`, and both are space accounting (i.e. step 5 work
pulled forward by the atomicity finding):

    InteriorDirectory.lean:5276  canonicalRelativeRmmInteriorDirectory_payload_length_eq_raw
    InteriorDirectory.lean:5303  canonicalRelativeRmmInteriorDirectory_payload_length_eq_legacy_of_compactReady

Both are "unsolved goals": the counted payload now has two summands that
the right-hand sides do not.

The shape of the fix, with the arithmetic checked by hand this session but
NOT yet in Lean:

- `canonicalRelativeRmmInteriorRawPayloadOverhead` (`:5130`) is a closed
  form in `n`. Its local variables already coincide with the two new
  domains: the table domains are `macroSize + 2` and `macroSampleCount + 2`,
  and in the closed form `macroSize = M = w*w` and
  `macroSampleCount = m = b/M + 1` (VERIFIED: `RelativeSummary.lean:1292`
  `macroSize = blocksPerSuper * blocksPerSuper`, `:1295`
  `macroSampleCount = blockCount / macroSize + 1`; and
  `SuccinctRank.machineWordBits n = Nat.log2 n + 1`,
  `SuccinctRank.lean:38-39`). So the two added summands are
  `(M+2) * (Nat.log2 ((M+2)*(M+2)) + 1)` and
  `(m+2) * (Nat.log2 ((m+2)*(m+2)) + 1)`.
- `..._payload_length_eq_raw` then stays an EQUALITY, which is the honest
  outcome and preserves the audit property that the counted payload is
  exactly accounted. Prefer this over weakening it.
- `..._payload_length_eq_legacy_of_compactReady` (`:5299`) genuinely cannot
  stay an equality: the legacy directory has no level tables. The delegation
  authorised weakening it to `<=`. A STRONGER and equally cheap option is
  available and is recommended: restate it as an exact equality to
  `legacy + canonicalRelativeRmmInteriorLevelTableOverhead shape`. Its only
  consumer is `..._littleO` at `:5406`, inside a `calc` that already ends in
  `<=`, so either form threads through. It has NO consumers outside this
  file (verified by ripgrep over `RMQ/`).
- `..._littleO` (`:5388`) currently routes the whole overhead through the
  legacy envelope. With a level term added it must instead use
  `LittleOLinear.add` (`SuccinctSpace/Asymptotics.lean:700`) over the legacy
  part and a new level part. The level part IS littleO: it is
  `~ log^2 n * log log n`, dominated by
  `eventually_scale_log2_succ_cube_le_self` (`Asymptotics.lean:516`) since
  `log log n <= log n`. `LittleOLinear.of_le` is at `:35`,
  `logLogSampledDirectoryOverhead_littleO` at `:243`.
- `..._le_linear` (`:5145`, the `218 * (n + 1)` capacity feed, consumed at
  `SuccinctFinal/RAM/ReviewerPhysical.lean:1880`) must be re-derived with a
  larger constant. CAUTION, checked this session: the existing proof's
  `hmM5 : m * M <= 5 * n` gives `M <= 5*n`, which is FAR too loose to bound
  the level term linearly - it would yield `~ n log n`. The tighter fact
  `M = w*w = (Nat.log2 n + 1)^2` must be used directly. This is the one
  genuinely new piece of arithmetic in the rung's space accounting and it
  should be budgeted as such, not assumed to fall out.

## CORRECTIONS OF RECORD to B7-01's RESUME INVENTORY

All verified at source this session. B7-01's inventory is otherwise sound;
these are the points where acting on it literally would misfire.

1. WRONG PATH. `InteriorDirectory.lean` is under
   `RMQ/Core/SuccinctClose/EndpointFringe/InteriorCandidate/`, not
   `.../PrefixRange/`. (`SparseLevelTable.lean` IS under `PrefixRange/`.)
2. LINE DRIFT. Every `InteriorDirectory.lean` line number in B7-01's
   inventory is low by about 59 lines (the M2 commit inserted the
   instantiations at `:1447-1504`). Notably
   `canonicalRelativeRmmPrincipledInteriorChargedTraceCost` is at `:1843`,
   not `:1783`.
3. WRONG THEOREM NAMES for the literal. The cost-algebra theorems are
   `concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCloseCost_eq`
   (`SuccinctFinalRAM.lean:8818`, `= 126`) and
   `concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost_eq`
   (`:8823`, `= 207`). B7-01 wrote `..._CloseCost_eq`, which does not
   exist. The algebra def is at `:8806`, the structure at `:8787`.
4. A FIFTH PARALLEL FAMILY, previously unlisted anywhere in this worklog or
   in DD-20260718-012/013:
   `RMQ/Core/SuccinctClose/EndpointFringe/InteriorCandidate/WordReads.lean`,
   `localTwoSpanCandidateWordsRead` (`:203`) and
   `globalTwoSpanCandidateWordsRead` (`:260`), each with its own
   `let level := Nat.log2 count`. This is the word-count/budget family; an
   added read almost certainly moves its arithmetic. The complete set of
   `let level := Nat.log2 _` sites in the worktree is now:
   `InteriorDirectory.lean:1769,1783` (Costed), `:2177,:2191` (Computation),
   `InteriorRAM.lean:573,621,819,867`,
   `LocalGlobalSparse.lean:30,101,603,676`,
   `ConcreteDirectoryRAMStoreParam.lean:1405,1995`,
   `WordReads.lean:203,260`.
5. FOUR EXECUTED SITES, NOT TWO. B7-01's step 3 names only the two
   `...Computation` sites. The two `...Costed` sites
   (`InteriorDirectory.lean:1769`, `:1783`) are the cost-model twins that
   the `_refines` chain equates to them, so they must be amended in the
   same commit or `..._refines` (`:3065-3122`) fails.

## MEASURED REPAIR SURFACE for the swap (step 3 + step 4)

Enumerated by name and line this session. 28 theorems and 12 downstream
defs mention the four two-span definitions:

- `InteriorDirectory.lean`, 26 theorems in four bands:
  footprint_le_dead `:2340,2360,2380,2400,2420` + aggregate `:2445`;
  refines `:3065,3079,3093,3107,3122` + `:3137` (`..._eq_current`) and
  `:3356` (`..._refines_logical`);
  cost_le `:3928,3953,3977,4003,4029` + aggregate `:4070`;
  cost_le_..._of_macro_crossing `:4349,4370,4394,4418,4443,4468` +
  aggregate `:4511`.
- Downstream defs: `...AdjacentMacroCandidate{Costed,Computation}`
  (`:1793`/`:2201`), `...LeftMiddleMacroCandidate{Costed,Computation}`
  (`:1806`/`:2214`), `...CrossMacroCandidate{Costed,Computation}`
  (`:1819`/`:2227`), `canonicalRelativeRmmInteriorRangeMin{Costed,Computation}`
  (`:1845`/`:2245`).
- Cross-file, both on the Local Computation def only:
  `SuccinctFinal/RAM/ReviewerReachabilitySmall.lean:2095`
  (`reviewerIncreasingCanonicalInterior_successfulRead`) and
  `SuccinctFinalRAM.lean:5953` (`reviewerCanonicalInterior_mayRead`).
  NOTE: `ReviewerReachabilitySmall.lean` is owned by
  `claude/a07-blocker-repairs` for provenance witnesses. The next B7 worker
  must check with the coordinator before editing it, or confirm a07 has
  landed.

The four per-span cap lemmas that do NOT move (the new read is per two-span,
not per span) are `:4224` (`..._cost_le_nine_of_size_ge_four`), `:4258`
(`..._cost_le_eight_of_size_ge_four`), `:4284` and `:4320`
(`..._cost_le_five_of_macro_crossing`).

## PROVENANCE AND ADEQUACY TARGETS (step 5), located

- `ReviewerProducerReadPath` is `inductive` at `SuccinctFinalRAM.lean:5324`
  with 14 constructors (`:5327-5424`). The mirror for a new constructor is
  the B6-added `lcaSameBlock` (`:5419-5424`) together with its discharge
  site in `lcaCloseGlobalWordTraceResult_producerReadPath` at `:5537`;
  neighbouring discharges at `:5525`, `:5531`, `:5543`.
- The three W19-standard names are STRUCTURE FIELDS, not theorems, in
  `RMQ/Core/SuccinctFinalModelAdequacy.lean`: declarations at `:117`
  (`every_emitted_read_has_listed_region`), `:133`, `:135`; instantiations
  at `:324`, `:329`, `:332`. They are stated about the WHOLE-QUERY trace
  result, not the interior execution.
  `every_emitted_read_has_listed_region` is the one with teeth: it
  quantifies over every emitted `readWord`, so the new level read must land
  in a listed region or its proof
  (`concreteBPNativeSuccinctRMQWholeQueryFlatPhysical_read_has_listed_region`)
  breaks.
- `canonical_segments_complete` (`SuccinctFinalModelAdequacy.lean:113`)
  hard-codes `segment < 23`. CONSISTENT with matrix Amendment 1 point 2:
  no new segment, so this does NOT move. Recorded because the frozen
  REQ-B7-04 text wrongly predicted it would move.

## THE 207 CONSUMER SET IS WIDER THAN B7-01 RECORDED

Enumerated by ripgrep this session. B7-01's list omits the first two groups:

- `RMQ/Core/SuccinctFinalModelAdequacy.lean:67,69,302,303` - includes the
  field `nonSyntheticWeight_sum_le_207`.
- `RMQ/Core/SuccinctFinalRAM.lean:8824,9410,9411,9414,9421,9720,9729,9778,9792,9843`.
  The underlying theorem is
  `concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_nonSyntheticWeight_sum_le_207`
  (`:9411`).
- `RMQ/Core/SuccinctRMQClassic.lean:111` (`queryCost_eq`).
- `RMQ/Headlines/RMQ.lean:27,70,497,498,499,529` (`:498` is the `SumLe207`
  abbrev).
- `RMQ/Validation/SuccinctClassic.lean:266`;
  `RMQ/Validation/SuccinctClassicCostHarness.lean:118,129,131`.
- `RMQExamples/Concrete.lean:84`.
- `scripts/headline_axiom_check.lean:97`; `scripts/paper_topology_lint.ps1:354`.
- Docs (prose, migrate with the doc pass): `README.md:70,76,80,140,334`;
  `docs/PAPER_CLAIM_CORRESPONDENCE.md:7,8,9,54,56`;
  `docs/PAPER_MODEL_ADEQUACY.md:91,175,274,289,293`;
  `docs/WHAT_IS_PROVED.md:34,72,80,84,184,254`;
  `docs/FAMILY_SUMMARY.md:9,43,48,133,446,1041`;
  `artifact/CLAIMS.md:31,65,69,73,110,128`.
  NOTE `README.md`, `docs/FAMILY_SUMMARY.md` and RMQPaper docstrings are
  owned by `claude/a07-blocker-repairs`; coordinate before editing.
- There is no `RMQPaper/` directory; `RMQPaper.lean` at the root has ZERO
  hits for 207.

The historical-constant pattern to mirror for freezing 207 is the 142 block:
`SuccinctFinalRAM.lean:8851-8873` (algebra def + cost def + `_eq` theorem),
its public mirror `RMQ/Core/SuccinctRMQClassic.lean:123-132` (abbrev +
`_eq`), and its guards at `RMQExamples/Concrete.lean:85` and
`RMQ/Validation/SuccinctClassic.lean:267`. The 76 block is
`SuccinctFinalRAM.lean:8827-8848` / Classic `:114-121` / guards
`Concrete.lean:86`, `SuccinctClassic.lean:268`. The 328 block is Classic
`:102`/`:135`, guards `Concrete.lean:88`, `SuccinctClassic.lean:269`, plus
`RMQ/Headlines/RMQCompatibility.lean:73`.

## Verification ledger for this session

- `lake env lean RMQ/.../InteriorCandidate/InteriorDirectory.lean` WITH the
  step-2 edits applied: no output, exit 0 (zero errors, zero warnings).
  Recorded as an ITERATE-AID result only, per the standing warning that
  per-file elaboration writes no olean.
- `lake build RMQ` WITH the step-2 edits applied: exit 1, failing at
  `[213/244] RMQ.Core.SuccinctFinal.RAM.FlatPayload`, decisive line:

      error: RMQ/Core/SuccinctFinal/RAM/FlatPayload.lean:2271:8: type
      mismatch, term
        SuccinctClose.canonicalRelativeRmmInteriorComponentStore_flattens_payload shape

  This is the evidence for atomicity point 1 above. After amending
  `canonicalRelativeRmmInteriorDirectory` the failure moves to the two
  space-accounting theorems named above.
- `lake build RMQ` on the REVERTED tree: recorded at the commit below.
- The externally-owned blocker recorded at `398d4e8`
  (`scripts/wordram_axiom_check.lean` exit 1 on a name that exists nowhere
  in `RMQ/`) was NOT re-run this session and is NOT claimed as re-verified.
  It remains owned by `claude/a07-blocker-repairs`.

## STATUS AT END OF THIS SESSION: INCOMPLETE

Steps 1 of 6 complete (unchanged from B7-01). Step 2 is written, verified
to elaborate, and reverted; it is NOT committed and must be redone or
re-applied from the patch.

NEXT ACTION for the following session, in order:

1. Re-apply step 2 from the edit inventory above (mechanical).
2. Do the space accounting (the two theorems at `:5276`/`:5303`, then
   `..._littleO` at `:5388` and `..._le_linear` at `:5145`). Budget the
   `M = (Nat.log2 n + 1)^2` arithmetic properly; it is the one novel piece.
3. Wire all FOUR sites (`:1769`, `:1783`, `:2177`, `:2191`), then repair the
   26 in-file theorems band by band in the order footprint -> refines ->
   cost_le -> cost_le_of_macro_crossing.
4. Migrate the caps and the literal 207 -> 210 across the consumer set above.
5. Only then commit. Expect the tree to be red throughout 1-4; that is
   forced by the atomicity finding and is not a defect.

Steps 5 (provenance/vocabulary/o(n)) and 6 (docs/matrix) of the original
plan follow unchanged, with the located targets recorded above.

No acceptance-matrix row changed status this session; no row was weakened.

## PRE-SWAP COST-HARNESS BASELINE (recorded for CHK-04 anti-vacuity)

`lake exe rmq_succinct_classic_cost_harness` at `398d4e8`, exit 0, "all
reported windows agree with reference List Int RMQ semantics",
`canonicalBound=207` and `canonicalBoundIs207=true` on every window.

CHK-04 requires that the interior-route windows MOVE after the swap. These
are the pre-swap `modeledTraceCost` values to compare against; the
`crossBlock` rows are the ones that exercise the interior two-span path and
so are the ones that must change:

    tie-boundary n=6      [0,6) crossBlock 76   [1,5) crossBlock 72
                          [2,3) sameBlock  54
    generated-64          [0,64) crossBlock 116  [7,39) crossBlock 126
                          [31,32) sameBlock 62
    zigzag-128            [0,128) crossBlock 92  [17,97) crossBlock 96
                          [64,65) sameBlock 57
    generated-128-alt     [0,128) crossBlock 93  [15,96) crossBlock 95
                          [63,64) sameBlock 57

A swap that leaves every one of these unchanged has not gone live, whatever
the caps say.

# Session 3 (B7-03)

Two durable results this session: the FIFTH-FAMILY reachability question is
CLOSED (negative), and the space accounting - the piece B7-02 flagged as the
one genuinely novel item - is SOLVED in Lean except for its last link.
No Lean change is committed: the atomicity finding still holds, so the tree
cannot go green until the whole swap lands. The WIP patch is refreshed.

## FIRST ACTION discharged: the reverted work is now durable

B7-02's 491-line scratchpad patch was recovered intact and committed as
`docs/internal/B7_STEP2_WIP.patch` (commit `c5a00ae`, docs-only).
`git apply --check` clean before committing.

RECORDED so a later battery is not misread: this file trips
`git diff --check`, because a blank CONTEXT line in a unified diff is a
single space and reads as trailing whitespace. This is structural to any
committed patch and is NOT a source defect. The precedent has the same
property - `git show 7cc792a --check` (the B3_M5_WIP.patch commit) exits 2
with 103 such hits. Stripping them would corrupt the patch.

## SITE COUNT IS FOUR, NOT SIX: the fifth family is UNREACHABLE

The delegation asked for a per-site verdict walked from
`concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult`, not assumed
from the name. Verdicts:

| Site | Verdict |
|---|---|
| Local two-span `...Computation` (`InteriorDirectory.lean`) | REACHABLE |
| Global two-span `...Computation` | REACHABLE |
| The two `...Costed` twins | REACHABLE (spec-side; equated by the `_refines` chain, so they must move in the same commit) |
| `WordReads.lean` `localTwoSpanCandidateWordsRead` | UNREACHABLE |
| `WordReads.lean` `globalTwoSpanCandidateWordsRead` | UNREACHABLE |
| `LocalGlobalSparse.lean`, `ConcreteDirectoryRAMStoreParam.lean` | UNREACHABLE (`Costed` spec layer / legacy store-parametric branch off a different root) |

DECISIVE EVIDENCE for the negative verdict, re-confirmed by hand at source
(not taken on the subagent's word). Both `WordReads` definitions funnel
into `bpTwoLevelInteriorCandidateWordsRead`, which has exactly TWO def-body
consumers in the whole tree:

- `InteriorDirectory.lean:955` - the `payloadWordsRead` field of the LEGACY
  `concreteBPRelativeRmmInteriorDirectory`. The live all-size structural
  route never projects this field; the CANONICAL directory sets
  `payloadWordsRead` from
  `canonicalRelativeRmmInteriorRangePhysicalWordsReadWithStore` instead.
- `InteriorDirectory.lean:1723` - `canonicalRelativeRmmInteriorLogicalWordsRead`,
  whose only consumers anywhere are two THEOREMS
  (`..._length_le_machine`, `..._reconstruct_logical`).

Every other mention is a theorem statement, a proof `simp` set, or the
`SuccinctCloseProposal.lean` name manifest. None is execution.

CONSEQUENCE: charging the four reachable sites CLOSES the rung. There is no
residual Theta(log n) silent computation hiding in the `WordsRead` family,
because that family is an audit projection, not an execution path. B7-02's
worry that this family "almost certainly moves its arithmetic" is
DISCHARGED NEGATIVE - it does not move, because it never runs.

CAVEAT OF RECORD: the subagent that produced the first pass read the tree
while the step-2 patch was being applied underneath it, so ITS LINE NUMBERS
ARE UNRELIABLE and are deliberately not reproduced above. Its structural
claims are unaffected, and the decisive one was re-verified independently.
Trust the names, re-derive the lines.

## SPACE ACCOUNTING: SOLVED IN LEAN, three links of four

This was B7-02's identified novel piece. It is no longer novel; the
arithmetic is written and elaborates. Verified with `lake env lean` on
`InteriorDirectory.lean` with the full patch applied (ITERATE AID ONLY - no
olean is written, so no `#print axioms` claim is made here).

The key move, and the answer to B7-02's trap: B7-02 was RIGHT that
`hmM5 : m * M <= 5 * n` is too loose for the local level term (it gives
only `M <= 5n`, hence `~ n log n`). But the fix is NOT to use
`M = (Nat.log2 n + 1)^2` symbolically. It is to use the TIGHT CUBE BOUND
that already exists in the same proof three lines above:
`hMw : M * w <= 8 * n` (from `machineWordBits_cube_le_eight_mul_self_of_pos`).
The local term is `(M+2) * width`, and
`(M+2) * (16w+9) = 16*(M*w) + 9*M + 32*w + 18`, which the cube bound closes
directly. The global term DOES yield to the loose bound, via
`m * w <= m * (w*w) = m * M <= 5 * n`.

Two new private helpers were added (both elaborate):

    private theorem machineWordBits_add_two_le_four_mul_of_pos
        {x : Nat} (hx : 0 < x) :
        SuccinctRank.machineWordBits (x + 2) <=
          4 * SuccinctRank.machineWordBits x

    private theorem sparseLevelWidth_add_two_le_of_pos
        {x : Nat} (hx : 0 < x) :
        Nat.log2 ((x + 2) * (x + 2)) + 1 <=
          8 * SuccinctRank.machineWordBits x + 1

Status of the four space-accounting links:

1. `..._payload_length_eq_raw` - DONE, and it STAYS AN EXACT EQUALITY (the
   honest outcome B7-02 recommended). `canonicalRelativeRmmInteriorRawPayloadOverhead`
   gained two summands, `localLevelDomain := macroSize + 2` and
   `globalLevelDomain := macroCount + 2`, each contributing
   `domain * (Nat.log2 (domain * domain) + 1)`. The proof needed only the
   two `..._payload_length` rewrites plus `bpSparseLevelTableOverhead`,
   `bpSparseLevelDomain`, `bpSparseLevelWidth` in the simp set.

2. `..._le_linear` - DONE. THE CONSTANT MOVES: 218 -> 527. Derived, not
   asserted: local level term `<= 196n + 18`, global level term
   `<= 113n + 3`, and `218n + 218 + 196n + 18 + 113n + 3 = 527n + 239`
   `<= 527(n+1)`. NOTE FOR THE NEXT WORKER: 527 is a new consumer-visible
   constant; its consumer is `SuccinctFinal/RAM/ReviewerPhysical.lean:1880`
   and that site must be migrated in the same commit.

3. `..._payload_length_eq_legacy_of_compactReady` - DONE, and STRENGTHENED
   rather than weakened. The delegation authorised weakening it to `<=`;
   that authorisation was NOT used. It is now an exact equality:

       (canonicalRelativeRmmInteriorDirectory shape).payload.length =
         (concreteBPRelativeRmmInteriorDirectory shape).payload.length +
           canonicalRelativeRmmInteriorLevelTableOverhead shape

   No row is weakened by this rung's space accounting.

4. `..._littleO` - NOT DONE. THIS IS THE RESUME POINT. With link 3 restated
   the error moves here, exactly as B7-02 predicted:

       InteriorDirectory.lean:5517:6: error: type mismatch, term
         heq
       after simplification has type
         canonicalRelativeRmmInteriorRawPayloadOverhead n =
           (concreteBPRelativeRmmInteriorDirectory shape).payload.length +
             canonicalRelativeRmmInteriorLevelTableOverhead shape : Prop
       but is expected to have type
         canonicalRelativeRmmInteriorRawPayloadOverhead n =
           (concreteBPRelativeRmmInteriorDirectory shape).payload.length : Prop

   The shape of the fix is B7-02's and still stands: split with
   `LittleOLinear.add` (`SuccinctSpace/Asymptotics.lean:700`) over the
   legacy part and a level part. The level part needs a closed form IN `n`
   (the current `canonicalRelativeRmmInteriorLevelTableOverhead` is in
   `shape`), and is `~ log^2 n * log log n`, dominated by
   `eventually_scale_log2_succ_cube_le_self` (`Asymptotics.lean:516`).
   `LittleOLinear.of_le` is at `:35`.

## STATE OF THE TREE AND OF THE PATCH

The source tree is REVERTED and the root build is GREEN. No partial swap is
committed, per the standing rule and B7-02's precedent.

`docs/internal/B7_STEP2_WIP.patch` is REFRESHED to 661 lines. It is no
longer just step 2: it is step 2 PLUS space-accounting links 1-3. Verified
`git apply --check` clean against this commit. Applying it reproduces a tree
whose only remaining `InteriorDirectory.lean` error is the `_littleO`
mismatch quoted above.

## BASELINE OF RECORD for the next session

`lake build RMQ` at `c5a00ae`: exit 0, "Build completed successfully", with
TWELVE pre-existing unused-simp-arg warnings (`SuccinctFinalRAM.lean`
:5804, :5807, :5809, :5811, :5933, :5934; `ReviewerReachabilitySmall.lean`
:463, :1484 twice; `ReviewerReachabilityLong.lean`:519;
`ReviewerReachabilitySparse.lean`:563; `BPNavigationRAM.lean`:2111).
NONE is in `InteriorDirectory.lean`. Recorded so the next worker does not
attribute them to the rung. The refreshed patch adds no new warning.

## STATUS AT END OF THIS SESSION: INCOMPLETE

NEXT ACTION, in order:

1. Apply `docs/internal/B7_STEP2_WIP.patch` (step 2 + space accounting 1-3).
2. Finish `..._littleO` (the only remaining space-accounting link).
3. Migrate the `218 -> 527` capacity constant at
   `SuccinctFinal/RAM/ReviewerPhysical.lean:1880`.
4. Wire the FOUR reachable sites only - the `WordReads` family is settled
   UNREACHABLE and must NOT be touched.
5. Repair the 28 theorems / 12 defs band by band, then the caps, then the
   literal 207 -> 210 across B7-02's widened consumer set.
6. Provenance, adequacy, docs, matrix.

No acceptance-matrix row changed status this session; no row was weakened.
No constant is asserted; the 527 and the 207 -> 210 chain are both to be
derived at the commit that lands them.

# Session 4 (B7-04)

Two durable results: SPACE ACCOUNTING IS COMPLETE (link 4, `..._littleO`,
was B7-03's resume point and is now solved and compiled to a real olean),
and the store extension's blast radius is now known to reach OUTSIDE
`InteriorDirectory.lean` - a breakage no predecessor could have seen.
No Lean change is committed: the atomicity finding still holds. The WIP
patch is refreshed from 661 to 952 lines.

## LINK 4 SOLVED: `canonicalRelativeRmmInteriorRawPayloadOverhead_littleO`

B7-03 left the decisive error verbatim: after `heq` simplification the term
carries `+ canonicalRelativeRmmInteriorLevelTableOverhead shape` while the
goal expects the bare directory payload length. The `LittleOLinear.add`
route was right; what it needed was a closed form in `n` plus a bridge to
the `shape`-indexed overhead.

Four new pieces in `InteriorDirectory.lean`:

1. `canonicalRelativeRmmInteriorLegacyPartOverhead (n : Nat) : Nat` - the
   first three summands (summary, local sparse, global sparse). This is
   exactly the PRE-B7 raw overhead.
2. `canonicalRelativeRmmInteriorLevelPartOverhead (n : Nat) : Nat` - the
   two charged level-table summands as a closed form in `n`.
3. `canonicalRelativeRmmInteriorRawPayloadOverhead_eq_parts` - raw =
   legacy part + level part. Needs `Nat.add_assoc`: the raw def associates
   left, the split associates right.
4. `canonicalRelativeRmmInteriorLevelTableOverhead_eq_levelPart` - THE
   BRIDGE, `levelTableOverhead shape = levelPart shape.size`. Proved by
   the same simp set `..._payload_length_eq_raw` already uses, minus two
   args the linter rejects as unused
   (`Cartesian.CartesianShape.bpCode_length`, `Nat.mul_assoc`). That
   theorem had already done the layout-field-to-closed-form work, so the
   bridge is nearly free once the level part is named.

With the bridge, `..._eq_legacy_of_compactReady` (which B7-03 STRENGTHENED
to an exact equality, and which STAYS strengthened) rewrites into
`legacyPart n + levelPart n = legacyPayload + levelPart n` and the level
term CANCELS by `omega`. So `..._LegacyPartOverhead_littleO` is B7-03's
existing proof verbatim plus the cancellation, and the raw `_littleO` is
`LittleOLinear.add` of the two parts transported across `_eq_parts` by
`LittleOLinear.of_le`.

### The level part's envelope, derived

`levelPartOverhead_le_envelope` (private), for `2 <= n`, with
`base := Nat.log2 n + 1`:

    canonicalRelativeRmmInteriorLevelPartOverhead n <=
      81 * ((Nat.log2 n + 1) * ((Nat.log2 n + 1) * (Nat.log2 n + 1))) +
        (9 * (n / (Nat.log2 n + 1)) + 21)

- LOCAL table, domain `M + 2` with `M = base * base`. Width
  `<= 8 * machineWordBits M + 1` by B7-03's
  `sparseLevelWidth_add_two_le_of_pos`; then
  `machineWordBits (base*base) <= 2 * machineWordBits base + 1`
  (`SuccinctRank.machineWordBits_mul_self_log_bound`) and
  `machineWordBits base <= base` (`machineWordBits_le_self_of_pos`) give
  width `<= 16*base + 9 <= 25*base`. Domain `<= 2*(base*base)`. Product
  `<= 50 * base^3`. CUBIC - needs `eventually_scale_log2_succ_cube_le_self`.
- GLOBAL table, domain `x + 3` with `x = n / base / (base*base)`. Width
  `<= 9*base` using `machineWordBits (x+1) <= machineWordBits n = base`
  via `machineWordBits_mono_le` against `x + 1 <= n`. Product
  `<= 9*(base*x) + 27*base`, and `base * x <= n / base` by
  `Nat.div_div_eq_div_mul` + `Nat.div_mul_le_self`. So the global term is
  `~ n / log^2 n`, NOT cubic - it needs `littleOLinear_id_div_log2_succ`.
  THE TWO TERMS NEED DIFFERENT ENVELOPES AND MUST NOT BE MERGED.

## NEW OBSTRUCTION FOUND AND FIXED, outside `InteriorDirectory.lean`

No predecessor saw this because no predecessor's build ever got PAST
`InteriorDirectory.lean`. With link 4 done the root build advanced and
failed at [213/244]:

    error: RMQ/Core/SuccinctFinal/RAM/ReviewerPhysical.lean:1815:6:
    type mismatch, term ...
    but is expected to have type
      (SuccinctClose.canonicalRelativeRmmInteriorComponentStore
        shape).store.words.toList = ... (six regions) ...

`concreteBPNativeSuccinctRMQReviewerCloseWords_length_le` contains a
`rw [show ... by simpa ...]` that spells the component store's word list
out LITERALLY over six regions - the same defect class as the four
`_refines` proofs B7-02 enumerated, but in a different file and absent
from every inventory to date. Repaired by adding two `let`s
(`localLevel`, `globalLevel`), two
`fixedWidthNatTable_machineWords_length_le_payload_length` facts, the two
new tails on the decomposition, and
`SuccinctClose.PayloadLiveBPSparseLevelTable.payload` to the closing simp
set. `lake env lean` on the file is then clean, no errors, no warnings.

LESSON FOR THE NEXT WORKER: the literal-store-decomposition defect class
is NOT confined to `InteriorDirectory.lean`. Before assuming the repair
surface is the 28 theorems / 12 defs B7-02 measured, grep the whole tree
for proofs that enumerate the component store's regions. B7-02's measured
surface was measured against a build that never reached `SuccinctFinal`.

## 218 -> 527 MIGRATED

`RMQ/Core/SuccinctFinal/RAM/ReviewerPhysical.lean`, three occurrences in
`concreteBPNativeSuccinctRMQReviewerPhysicalWords_length_le` (`hdirLinear`,
`hcloseBound`, `hcanonicalCloseBound`). Headroom is not close:
`concreteBPNativeSuccinctRMQReviewerCapacity n = 400000 * (n + 1)`
(`ReviewerPhysical.lean:1470-1471`), so the extra `309 * (n+1)` is absorbed
without touching the capacity constant or any other consumer.

## CORRECTIONS OF RECORD (tactic-level, cost real time if rediscovered)

1. `set` IS NOT AVAILABLE - it is a Mathlib tactic and this project is
   Mathlib-free. The envelope had to be factored as a standalone
   arithmetic lemma `levelPart_envelope_arith` over plain variables
   `base q x` with three hypotheses, then instantiated by `exact` against
   the zeta-reduced goal. Do not reach for `set`, `ring`, or `nlinarith`.
2. `Nat.log2 2 = 1` DOES NOT REDUCE BY `decide` - `Nat.log2` is
   well-founded recursion and the `Decidable` instance gets stuck with
   "reduction got stuck at the 'Decidable' instance". The working route to
   `1 <= Nat.log2 n` from `2 <= n` is
   `(Nat.le_log2 hne).2 (hpow : 2^1 <= n)`.
   (`ChargedTableRegime.lean:44` has `bpRegime_log2_two` if a numeral is
   ever wanted.)
3. `omega` cannot see through a product of two variables. Every
   `(a) * (b) = c` step is a separate `have` closed by
   `simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, ...]` and
   consumed by `Nat.le_trans`, never handed to `omega` directly.

## STRETCH-01 GROUNDWORK: subagent inventory of the interior leg

Delegated read-only sweep of the flat-store executed family. Recorded as
GROUNDWORK, not as a closed inventory:

- It independently re-derived the four sites (`:2263`/`:2264` local level
  and span, `:2277`/`:2278` global level and span) and confirmed the
  arguments are runtime-derived (`count = rightBlock - leftBlock - 1` at
  `ChargedFringeTrace.lean:943`), not layout constants.
- It found NO additional genuine defect in the interior leg. Everything
  else classified as representation artifact or accepted primitive:
  constant-divisor `/` and `%`; index arithmetic; `bitsToNatLE` word
  decoding; `entries.length` (bridge lemmas at
  `LocalGlobalSparse.lean:838`, `:866`,
  `RelativeSummary.lean:559/566/573/580`).
- USEFUL NEGATIVE: `bpLocalSparseCellOffset`'s `let span := 2 ^ level`
  (`LocalSparseOffset.lean:23`) is on the TABLE-CONSTRUCTION path, not the
  query path - the query uses `...CellSlot`, not `...CellOffset`.
- COMPLETENESS LIMITS, stated so this is not mistaken for a closed
  inventory: it swept ONLY the interior leg. The endpoint-fringe, local BP
  decoder, and rank/select-close legs were inspected only at the call site.
  Leaf expansion was one level. Reachability was textual, not elaborated.
  It could not settle whether
  `concreteBPFiniteSmallInteriorRangeMinTable` /
  `...AllSizeStructuralLegacy` (`ConcreteDirectoryRAM.lean:1100-1209`,
  which dispatches to a `boundedSummaryRangeScanTraceResultAtSegments`, a
  name suggesting a LINEAR SCAN) is dead from the whole-query root.
  THAT LAST ITEM IS THE MOST INTERESTING UNRESOLVED THREAD IN THIS RUNG.

STRETCH-01 remains Open. This is a candidate list for the interior leg
with stated limits, not the auditable complete enumeration the row asks
for.

## DECISIVE FINDING: THE FROZEN HISTORICAL CONSTANTS TRACK THE LIVE INTERIOR CAP

This blocks the 30 -> 33 move under EVERY staging plan, atomic or split,
and it appears in no previous inventory. Found by reading the freeze
pattern before migrating the literal, not by a build failure.

Both frozen historical algebras in `SuccinctFinalRAM.lean` set their
`interiorDirectory` field to the LIVE def, not to a frozen numeral:

    def concreteBPNativeSuccinctRMQSilentFringeChargedTraceCostAlgebra ... where
      selectClose := 13
      rankClose := 4
      endpointFringe := ...canonicalEndpointFringeChargedTraceCost
      interiorDirectory :=
        SuccinctClose.canonicalRelativeRmmPrincipledInteriorChargedTraceCost

    def concreteBPNativeSuccinctRMQSilentWordRankSelectChargedTraceCostAlgebra ... where
      selectClose := 13
      rankClose := 4
      endpointFringe := ...bpChunkedEndpointFringeChargedTraceCost
      interiorDirectory :=
        SuccinctClose.canonicalRelativeRmmPrincipledInteriorChargedTraceCost

With `wholeQuery = 2*selectClose + (2*rankClose + 2*endpointFringe +
interiorDirectory) + rankClose`:

- 76 block:  26 + (8 + 8 + 30) + 4 = 76   -> with 33: 79
- 142 block: 26 + (8 + 74 + 30) + 4 = 142 -> with 33: 145

Both `_eq` theorems are `rfl` and both BREAK. The standing rule is that
frozen legacy anchors stay untouched and no historical constant is
deleted, so `canonicalRelativeRmmPrincipledInteriorChargedTraceCost`
CANNOT simply be edited 30 -> 33 in place.

REQUIRED SHAPE OF THE FIX (the established freeze pattern, applied one
level DOWN - at the component, not just at the whole-query literal):
mint a frozen historical interior component constant pinned at 30, e.g.

    def canonicalRelativeRmmSilentSparseLevelInteriorChargedTraceCost : Nat := 30

re-point BOTH historical algebras at it so history stops tracking the
live route, and only then move the live def to 33. Verify afterwards that
`..._SilentFringeChargedTraceCost_eq = 76` and
`..._SilentWordRankSelectChargedTraceCost_eq = 142` still hold by `rfl`.

`canonicalTransitionalQueryCost = 328` (`SuccinctRMQClassic.lean:135-138`)
does NOT go through this algebra and is unaffected.

## SECOND NEW OBSTRUCTION: `ReviewerReachabilitySmall.lean:2088`

With `ReviewerPhysical.lean` repaired the build advanced to [243/244] and
failed at `RMQ.Core.SuccinctFinal.RAM.ReviewerReachabilitySmall`, a THIRD
instance of the literal-store-decomposition defect class:

    error: RMQ/Core/SuccinctFinal/RAM/ReviewerReachabilitySmall.lean:2088:4:
    type mismatch, term ...

Its `hmiddle` spells the component store out literally and passes
`globalWords` as the `post` argument of
`SuccinctSpace.List.getElem?_append_middle_of_lt`. Repaired exactly as
B7-02 prescribed for the four in-file `_refines` proofs: two new `let`s
(`localLevelWords`, `globalLevelWords`), `post` becomes
`(globalWords ++ localLevelWords ++ globalLevelWords)`, and the two names
added to the trailing `simpa` set. `lake env lean` on the file then shows
ONLY the three pre-existing warnings B7-03's baseline already recorded
(`:463`, `:1484` twice) and no errors.

### CONCURRENCY BOUNDARY CROSSED - COORDINATOR ACTION NEEDED

`RMQ/Core/SuccinctFinal/RAM/ReviewerReachabilitySmall.lean` is owned by
`claude/a07-blocker-repairs` (provenance witnesses). B7-02's worklog
already flagged that a later B7 worker would have to coordinate before
editing it. That moment has arrived, and it arrived as a BUILD BLOCKER
rather than as an optional edit: the store extension cannot compile
without this repair.

HOW THIS WORKER HANDLED IT, deliberately and conservatively: the repair
is carried ONLY in `docs/internal/B7_STEP2_WIP.patch`. It is NOT committed
as source. So B7's committed history still touches none of a07's files and
no merge conflict exists yet; what exists is a RECORDED REQUIREMENT.

The edit is mechanical and semantically inert with respect to a07's
concerns: it does not change the theorem's statement, its provenance
witness, or the segment it exhibits. It only keeps an existing proof
working as the component store grows two regions. The coordinator should
decide whether a07 absorbs it or B7 lands it at swap time.

## STATE OF THE TREE AT THE END OF THIS SESSION

Source tree: HOLDS the full patch (step 2 + space accounting links 1-4 +
the 527 migration + the two new store-decomposition repairs). NOT
committed, per the atomicity rule - the level tables are counted but not
yet read, which would be a dead counted source.

Committed: docs only (`8bfe3a5` and this commit).

The `git apply --check` of the committed patch against a clean tree was
verified CLEAN this session (stash / check / pop, with the restored tree
diffed byte-for-byte modulo git's CRLF round-trip).
## VERIFICATION LEDGER FOR THIS SESSION (B7-04)

All results as observed in this worktree, with the full patch applied to
the source tree unless stated otherwise.

- `lake build RMQ` WITH the full patch applied: EXIT 0, 67.7s incremental,
  "Build completed successfully", 243/244 jobs, ZERO errors and TWELVE
  warnings - byte-identical in count to B7-03's recorded pre-existing
  warning baseline, so the patch adds NO new warning. THIS IS THE FIRST
  COMPLETED ROOT BUILD IN THE RUNG'S HISTORY WITH THE STORE EXTENSION
  APPLIED; sessions 2 and 3 never got past `InteriorDirectory.lean`, which
  is why the two store-decomposition breakages above had never been seen.
- `lake env lean` on `InteriorDirectory.lean`: no output, exit 0 (zero
  errors, zero warnings). Iterate aid only.
- `lake env lean` on `ReviewerPhysical.lean`: no output, exit 0.
- `lake env lean` on `ReviewerReachabilitySmall.lean`: zero errors; only
  the three PRE-EXISTING warnings (`:463`, `:1484` twice) already in
  B7-03's baseline.
- Hygiene `rg` over all four B7-touched files (the three above plus
  `SparseLevelTable.lean`): ZERO hits for
  sorry/admit/native_decide/implemented_by/partial/unsafe/extern/
  noncomputable/`import Mathlib`/axiom.
- `git diff --check` on the working tree: exit 0.
- `git diff --check f6564ec..HEAD`: exit 2, hits ONLY
  `docs/internal/B7_STEP2_WIP.patch`. This is the structural
  committed-patch property B7-03 documented (a blank context line in a
  unified diff is a single space); the `B3_M5_WIP.patch` precedent has the
  identical property. NOT a source defect.
- `git apply --check docs/internal/B7_STEP2_WIP.patch` against a CLEAN
  tree: CLEAN. Verified by stash / check / pop, with the restored files
  diffed against scratchpad backups and found identical modulo git's
  CRLF round-trip.

NOT RUN this session, and NOT claimed: the cost harness (CHK-04), the
headline axiom check, `#print axioms` on the new names,
`design_decision_check.ps1`, `claim_drift_scan.ps1`,
`paper_topology_lint.ps1`, and `lake build RMQ RMQPaper RMQExamples`.
The rung is not at a candidate state, so the final battery was not the
right use of the remaining budget; the next session should run it once
the swap lands. Per the delegation, `scripts/axiom_check.lean` and
`gate.ps1` were NOT run.

KNOWN RED, externally owned, NOT re-verified this session and NOT claimed:
`scripts/wordram_axiom_check.lean`, `scripts/axiom_check.lean`,
`lake exe rmq_succinct_classic_validate`. All belong to
`claude/a07-blocker-repairs`.

## STATUS AT END OF THIS SESSION: INCOMPLETE

No acceptance-matrix row changed status. No row was weakened. No
constant is asserted. The 207 -> 210 chain is NOT started and remains to
be derived at the commit that lands it.

NEXT ACTION, in order:

1. Apply `docs/internal/B7_STEP2_WIP.patch` (989 lines; step 2 + space
   accounting links 1-4 + the 527 migration + three store-decomposition
   repairs). It builds GREEN as-is - but it is NOT committable alone,
   because the level tables are counted and not yet read.
2. Decide the staging question with the coordinator (see the evaluation
   recorded above). If the split is taken, commit A must FIRST mint a
   frozen historical interior constant pinned at 30 and re-point the 76
   and 142 algebras at it, or those two frozen `rfl` identities break.
3. Wire the FOUR reachable sites (`:1823`, `:1837` Costed; `:2263`,
   `:2277` Computation, in the PATCHED file's numbering).
4. Repair the theorem bands, then the caps, then the literal.
5. Provenance, adequacy, docs, matrix, and the final battery including
   CHK-04 against the pre-swap harness baseline recorded in session 2.

# Session 6 (B7-06)

COMMIT A LANDED AND GREEN. The rung is past the frozen-constant blocker
that stalled sessions 2-5. The swap (commit B) is NOT started, deliberately;
see the budget ruling at the end.

Commits this session, oldest first:

- `f6000c3` B7 commit A: cap 30 -> 33, literal 207 -> 210, frozen 207.
- `34a1c9d` cross-branch README line (topology-lint forced), isolated.
- `7707f73` WDD-20260719-001 (design-decision gate).
- `90c1fbf` swap patch refreshed 989 -> 952 lines.

## THE INTERIOR PROOF WAS RESTRUCTURED, NOT WRAPPED

The delegation carried a verified one-branch fix: give the cross-macro
branch of `..._cost_le_thirty_of_size_ge_four_of_bounded` the same
`Nat.le_trans ... (by simp [cap])` wrapper its three siblings have, since
it alone applies its `<= 30` lemma directly with `exact` and so does not
adapt to a widened cap.

That fix is correct and it was not used. A better one was available:

- The tight proof body is kept VERBATIM under
  `canonicalRelativeRmmInteriorRangeMinCosted_cost_le_thirty_literal_of_size_ge_four_of_bounded`,
  concluding at the LITERAL `30`. Because the goal is now a literal, all
  four branches close unchanged - the cross-macro branch's bare `exact`
  included, since its lemma concludes at exactly `30`.
- The cap-facing theorem keeps its NAME and STATEMENT and is re-derived
  from the literal one in three lines by `Nat.le_trans`.

Why this is better than the wrapper: it fixes the zero-slack branch
STRUCTURALLY rather than per-branch (no future cap move can break a branch
again, because no branch mentions the cap); it keeps the tight `<= 30`
content checkable on its own rather than buried inside a `<= 33` statement;
and it leaves both external consumers (`ChargedFringeSubstitution.lean:418`,
`ConcreteDirectoryRAM.lean:2534`) and both axiom-inventory scripts
untouched, since the consumed name did not change.

Side effect handled: with the goal a literal, four
`simp [canonicalRelativeRmmPrincipledInteriorChargedTraceCost]` arguments
inside the literal theorem became UNUSED and the linter said so. They were
removed rather than left, so the warning baseline stays at exactly 12.

## THE SLACK ARTIFACT

Required by the delegation, carried as a checked proposition:

    theorem canonicalRelativeRmmPrincipledInteriorChargedTraceCost_announced_slack_of_size_ge_four_of_bounded
        (shape : Cartesian.CartesianShape) (hsize : 4 <= shape.size)
        (startBlock count : Nat)
        (hbound : startBlock + count <=
          (RelativeRmm.canonicalLayout shape).blockCount) :
        (canonicalRelativeRmmInteriorRangeMinCosted shape startBlock count).cost <=
            30
          /\ 30 < canonicalRelativeRmmPrincipledInteriorChargedTraceCost
          /\ canonicalRelativeRmmPrincipledInteriorChargedTraceCost = 33

The middle conjunct is the point. A theorem merely bounding the route by 30
would be a bound; asserting that the declared cap STRICTLY exceeds what the
route needs is an ANNOUNCEMENT, and it is unprovable the moment the swap
consumes the headroom. Commit B must DELETE it, not weaken it.

## THE HARNESS CONFIRMS THE SLACK - AND LEAVES CHK-04 OPEN

Cost harness at commit A: exit 0, "all reported windows agree",
`canonicalBound=210` / `canonicalBoundIs210=true` everywhere. Every
`modeledTraceCost` is IDENTICAL to the session-2 pre-swap baseline:

    tie-boundary n=6      [0,6) 76   [1,5) 72   [2,3) 54
    generated-64          [0,64) 116 [7,39) 126 [31,32) 62
    zigzag-128            [0,128) 92 [17,97) 96 [64,65) 57
    generated-128-alt     [0,128) 93 [15,96) 95 [63,64) 57

All twelve unchanged. That is exactly right for commit A - it widens a cap
and adds no reads - and it is independent empirical confirmation that the
slack theorem tells the truth about the live route.

It also means CHK-04 IS NOT DISCHARGED and was not claimed. CHK-04 demands
the interior windows MOVE. Only commit B can do that.

The same applies to REQ-B7-05, and this must not be glossed. That row's
anti-vacuity challenge says the literal must move BECAUSE new reads entered
the accounting on the maximizing branch, "not because a cap was loosened".
At commit A it moved because a cap was loosened. REQ-B7-05 therefore stays
OPEN despite the literal already reading 210. Closing it requires
re-deriving 210 over the AMENDED route and exhibiting the branch bound that
consumes the three units.

## 207 FROZEN WITH ITS OWN PINNED COMPONENT

`concreteBPNativeSuccinctRMQSilentSparseLevelChargedTraceCost_eq = 207`
plus a `..._CloseCost_eq = 126` companion, public abbrev
`canonicalSilentSparseLevelQueryCost`, and guards in
`Validation/SuccinctClassic.lean` and `RMQExamples/Concrete.lean` - the
same surface the 142/76/328 constants have.

Its endpoint-fringe field is a NEW pinned constant
(`canonicalSilentSparseLevelHistoricalEndpointFringeChargedTraceCost := 37`)
rather than a reuse of the identically-valued silent-rank/select capture.
Deliberate: under the `228ae8f` discipline each frozen algebra owns its own
components, so no retired route's narrative can be edited by work on
another's. Two constants holding 37 is the intended shape, not duplication
to be collapsed.

Confirmation that `228ae8f` did its job: the frozen `76` and `142` `_eq`
theorems still close by `rfl` across a live interior move, and
`#print axioms` reports both as depending on no axioms.

## THE SWAP PATCH WAS STALE FOR A GOOD REASON

See `90c1fbf`. The patch's third section repairs the same
`ReviewerReachabilitySmall.lean` proof that `0445d1d` already repaired, and
`0445d1d`'s version is store-growth-INVARIANT (`hmiddle` quantified over
`forall post`) where the patch's enumerates the new tail literally. Section
dropped, not merged; patch 989 -> 952 lines; `git apply --check` clean.

FIRST THING TO CHECK AT COMMIT B: whether that generalised proof really
survives the store extension untouched. It is quantified precisely so that
it should, which is why the hunk was dropped - but that is a prediction and
only commit B's first root build settles it. If it fails, repair it in the
GENERALISED style; do not reinstate the deleted hunk.

## VERIFICATION LEDGER (B7-06), all as observed at `90c1fbf`

- `lake build RMQ`: exit 0, 243/244, "Build completed successfully",
  ZERO errors, TWELVE warnings - byte-identical to the recorded baseline,
  none in any file this session touched.
- `lake build RMQ RMQPaper RMQExamples`: exit 0, 267/268, "Build completed
  successfully". `RMQExamples.Concrete` builds, so the new `#guard`s pass.
- `lake env lean scripts/headline_axiom_check.lean`: exit 0.
- `#print axioms` after a root build, on all new/migrated names: the
  arithmetic identities - both live (`= 210`, `= 129`), both new frozen
  (`= 207`, `= 126`), `queryCost_eq`,
  `canonicalSilentSparseLevelQueryCost_eq`, and the UNCHANGED frozen
  `76`/`142` - all report "does not depend on any axioms". The route
  theorems, the slack artifact, the literal interior theorem and
  `listIntSuccinctRMQPaperMainTheorem` report only
  [propext, Classical.choice, Quot.sound]. No name reported
  `unknown constant`.
- Cost harness: exit 0 (values above).
- Hygiene: zero forbidden-token hits across all eight touched Lean files;
  zero `native_decide`/`ofReduceBool` repo-wide.
- `git diff --check` (working tree): exit 0.
- `git diff --check f6564ec..HEAD`: exit 2, hits ONLY
  `docs/internal/B7_STEP2_WIP.patch`. Structural committed-patch property,
  documented since B7-03. NOT a source defect.
- `design_decision_check.ps1 -Strict -Base f6564ec`: exit 1 at first run
  ("strict mode found 1 missing design-log updates", triggered by
  `scripts/paper_topology_lint.ps1`); exit 0 after WDD-20260719-001
  ("DESIGN-CHECK: checked 22 changed files").
- `claim_drift_scan.ps1`: exit 0.
- `paper_topology_lint.ps1`: exit 1 before the README line moved
  ("unknown identifier '...SumLe207'", 1 failure); after `34a1c9d`,
  "PAPER-TOPOLOGY PASS (83 broad documentary identifiers; 49 paper
  identifiers resolved)", exit 0.
- Per the delegation, `scripts/axiom_check.lean` and `gate.ps1` were NOT run.

## OUTSTANDING, OWNED BY `claude/a07-blocker-repairs`, NOT TAKEN

Stale `207` prose numerals that B7's migration makes false but that no gate
catches (both `claim_drift_scan.ps1` and `paper_topology_lint.ps1` exit 0
with them present, since prose numerals are not resolved as identifiers):

- `README.md:70,76,140,334`
- `docs/FAMILY_SUMMARY.md:9,43,48,133,446,1041` - `:9` also carries the
  component formula with `interior30`, which becomes `interior33`.

B7 took ONLY `README.md:80`, and only because the topology gate fails
structurally without it. These must be migrated before the rung is
presented as complete. Coordinator to decide whether a07 absorbs them.

## BUDGET RULING: COMMIT B NOT STARTED, DELIBERATELY

The delegation is explicit that a partial swap must not be committed. On
honest assessment the remaining budget does not cover: apply the patch,
wire the four sites, discharge a repair surface known to be a LOWER bound,
retire the slack artifact, re-tighten the caps, re-derive the literal over
the amended route, extend W19 provenance for a NEW source, and re-run a
battery whose root build alone is 400-700s per iteration. Starting it would
produce exactly the partial swap the rules forbid.

So the session stopped at a clean, green, fully-verified commit A with a
clean-applying refreshed patch - the state the delegation prescribes here.

## RESUME POINT, in order

1. Apply `docs/internal/B7_STEP2_WIP.patch` (952 lines, `git apply --check`
   clean at `90c1fbf`). The FIRST build answers the open
   `ReviewerReachabilitySmall.lean` question above.
2. Wire the four reachable sites (`:1823`, `:1837` Costed; `:2263`, `:2277`
   Computation, in the PATCHED file's numbering).
3. Discharge the repair surface - LOWER bound; `ReviewerPhysical.lean:1815`
   and the two recorded overruns.
4. RETIRE the slack artifact by DELETING
   `canonicalRelativeRmmPrincipledInteriorChargedTraceCost_announced_slack_of_size_ge_four_of_bounded`,
   and re-tighten: the `_literal` theorem's `30` becomes the amended tight
   value, and if that value is 33 the cap-facing theorem's `Nat.le_trans`
   step collapses to `Nat.le_refl` or the two theorems merge again.
5. Re-derive 210 over the AMENDED route and exhibit the maximizing branch
   bound that consumes the three units - this is what closes REQ-B7-05,
   which commit A explicitly did NOT close.
6. Re-establish `..._readWord_only`; extend provenance
   (`ReviewerProducerReadPath`, `SuccinctFinalRAM.lean:5324`, mirroring
   `lcaSameBlock` at `:5419-5424`, discharge at `:5537`; W19 names are
   STRUCTURE FIELDS in `SuccinctFinalModelAdequacy.lean:117/133/135`;
   `canonical_segments_complete` at `:113` hard-codes `< 23` and does NOT
   move).
7. CHK-04 against the session-2 baseline quoted above: the interior windows
   must MOVE. Twelve unchanged values is the failure signal.
8. Finish REQ-B7-08 (the doc section already states the principle and names
   the bridge lemmas, but describes commit A's route; it must be made true
   of the AMENDED route), then the matrix and the full battery.

# Session 7 (B7-07)

Commit B was ATTEMPTED and is NOT landed. Two durable results, one of which
is a DECISIVE OBSTRUCTION that invalidates an arithmetic assumption shared by
DD-20260718-012, the frozen acceptance matrix, and commit A's already-landed
`33` / `210`. No Lean change is committed; the source tree is reverted and
green, and the WIP patch is refreshed 952 -> 1107 lines.

## RESULT 1: the inherited `ReviewerReachabilitySmall` question is SETTLED, POSITIVE

B7-06 dropped the patch section that repaired `ReviewerReachabilitySmall.lean`,
on the ground that `0445d1d` already repairs the same proof in a
store-growth-INVARIANT style (`hmiddle` quantified over `forall post`), and
flagged the prediction as UNVERIFIED pending commit B's first build.

VERIFIED THIS SESSION, POSITIVE. With the 952-line patch applied and nothing
else changed, `lake build RMQ` completed EXIT 0, 244/244, zero errors, and
`RMQ.Core.SuccinctFinal.RAM.ReviewerReachabilitySmall` built at [229/244].

The generalised proof absorbs the two new store regions untouched. The dropped
hunk was correctly dropped and must NOT be reinstated. The concurrency boundary
with `claude/a07-blocker-repairs` recorded by B7-04 is therefore NOT crossed by
this rung after all: B7 needs no edit to that file.

This also re-confirms the rest of the patch against a completed root build:
`FlatPayload` [217/244] and `ReviewerPhysical` [220/244] both green, so the
store extension, the four space-accounting links and the `218 -> 527` capacity
migration are all sound as carried.

## THE FOUR SITES ARE WIRED (carried in the patch, not committed)

All four reachable sites now take the level and the span from ONE charged read
of the new table, unpacked by constant-divisor div/mod:

- `canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted`
- `canonicalRelativeRmmMachineGlobalTwoSpanCandidateCosted`
- `canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation`
- `canonicalRelativeRmmMachineGlobalTwoSpanCandidateComputation`

`Nat.log2` and `bpSparseLogSpan` no longer occur in any of the four bodies.
The `none` arm is `pure none`, NOT a fallback that recomputes `Nat.log2`; that
choice is deliberate and is discussed under "design decision" below.

LINE-NUMBER CORRECTION OF RECORD: the delegation and B7-06's resume point give
the two `Computation` sites as `:2263` and `:2277` in the patched file. They
are at `:2277` and `:2291`; the `Costed` pair at `:1823` / `:1837` is correct.
The sites are unambiguous by name regardless.

## RESULT 2 - THE DECISIVE OBSTRUCTION: the packed cell does not fit in one machine word

THE MECHANISM'S CENTRAL ARITHMETIC CLAIM IS FALSE AS STATED, and this was found
by deriving the new read's cost rather than assuming it.

DD-20260718-012, the frozen matrix, and commit A all rest on "ONE charged read
per two-span call", hence interior `30 -> 33`, `closeLCA 126 -> 129`, literal
`207 -> 210`. In this cost model a read does NOT cost one unit: it costs one
unit PER MACHINE WORD TOUCHED.
`canonicalRelativeRmmMachineReadNatCosted_cost_le_one`
(`InteriorDirectory.lean:3945`) requires

    width <= SuccinctRank.machineWordBits shape.bpCode.length

and the level table does not satisfy it on reachable shapes.

The numbers, with `b = canonicalBPRelativeSummaryBase = Nat.log2 size + 1`,
`macroSize = blocksPerSuper^2 = b^2` (`RelativeSummary.lean:1244-1246`),
`domain = macroSize + 2`, stored width
`bpSparseLevelWidth domain = Nat.log2 (domain * domain) + 1`
(`SparseLevelTable.lean:131`), and machine word
`machineWordBits (bpCode.length) = Nat.log2 (2 * size) + 1`:

    size    b   macroSize  domain  width  machineWord  read cost
    2048    12  144        146     15     13           2
    8192    14  196        198     16     15           2
    16384   15  225        227     16     16           2
    32768   16  256        258     17     17           2
    65536   17  289        291     17     18           1

These are not edge cases. Macro crossing is `macroSize < blockCount`, i.e.
`b^2 < size / b`, i.e. `size > b^3`; at `size = 2048`, `b^3 = 1728 < 2048`, so
the CROSS-MACRO branch - the maximizing branch, the one carrying all three new
reads - is reachable at a size where each level read costs 2.

CONSEQUENCE, and it is not small: the cross-macro branch bound becomes
`30 + 3*2 = 36`, not 33. Interior 36 gives `closeLCA = 2*11 + 2*37 + 36 = 132`
and `wholeQuery = 2*35 + 132 + 11 = 213`, not 210. Commit A has ALREADY frozen
`207`, moved the live literal to `210`, and migrated every consumer plus the
topology anchor (`SumLe207 -> SumLe210`) to a value the amended route cannot
attain. REQ-B7-05's anti-vacuity challenge - the literal must move BECAUSE of
the reads - is exactly what exposes this: derived over the amended route the
value is not the value commit A assumed.

### THE FIX IS AVAILABLE AND IS A WIDTH FIX, NOT A CAP FIX

The cell is over-wide by construction, not by necessity.
`bpSparseLevelCell domain i = bpSparseLogSpan i + domain * Nat.log2 i` is
bounded in `bpSparseLevelCell_lt` (`SparseLevelTable.lean:99`) by
`domain * domain`, which bounds the LEVEL by `domain`. But the level is
`Nat.log2 i` with `i < domain`, so it is bounded by `Nat.log2 domain`, which is
exponentially smaller. The honest bound is

    bpSparseLevelCell domain i < domain * (Nat.log2 domain + 1)

giving
`bpSparseLevelWidth domain = Nat.log2 (domain * (Nat.log2 domain + 1)) + 1`.
Recomputed over the same shapes that fail above, this width is 11, 11, 11, 12,
12 against machine words 13, 15, 16, 17, 18 - it FITS IN ONE WORD with margin at
every one of them, restoring cost 1 per two-span call and with it the `33` /
`210` that commit A already froze.

So commit A's frozen literal is very likely RECOVERABLE and does not need a
second migration. That is the recommended route and it is why this session did
not start a `210 -> 213` re-migration.

### WHAT THE WIDTH FIX COSTS, stated so it is not under-budgeted

1. `bpSparseLevelWidth`, `bpSparseLevelCell_lt` and
   `bpSparseLevelEntries_lt_two_pow` in `SparseLevelTable.lean` all move.
2. A NEW arithmetic lemma is required, and it is the real work:
   `bpSparseLevelWidth (bpSparseLevelDomain macroSize) <= machineWordBits
   shape.bpCode.length` UNDER THE MACRO-CROSSING HYPOTHESIS. This is a
   `log2`-of-`log2` inequality against `size > b^3` and it is the analogue of
   `canonicalRelativeRmmOffsetWidth_le_relativeWidth` /
   `canonicalRelativeRmmRelativeWidth_lt_two_machine_of_size_ge_four` (the
   pattern the existing sparse reads use, `InteriorDirectory.lean:4551-4557`).
3. The four space-accounting links B7-04 completed are stated over the OLD
   width. A narrower width makes every space bound EASIER, but the proofs are
   not automatically re-usable: `sparseLevelWidth_add_two_le_of_pos` and
   `levelPartOverhead_le_envelope` are written against
   `Nat.log2 ((x+2)*(x+2)) + 1` and must be restated.
4. The WITHIN-MACRO branch (`..._cost_le_eighteen_of_size_ge_four`, which
   carries only `4 <= shape.size` and so must hold at tiny shapes where NO
   width fits one word) needs the `cost_le_two`-style route, not `cost_le_one`.
   It has ample headroom - it only has to stay under the interior cap - so this
   is bookkeeping, not a new obstruction.

## MEASURED REPAIR SURFACE OF THE WIRING ITSELF

With the four sites wired and nothing else changed, `lake env lean` on
`InteriorDirectory.lean` reports EXACTLY 13 errors in five groups. Recorded so
the next worker does not re-measure:

- `:2027`, `:2039` - the `Costed`-to-spec `_refines` pair. These need the domain
  hypothesis (`count <= macroSize`, resp.
  `macroSpanCount <= macroSampleCount`); the goal is otherwise stuck on
  `(bpSparseLevelEntries domain)[count]?`. Both are `@[simp]`.
- `:2498`, `:2502`, `:2518`, `:2522` - `whnf` / tactic-execution HEARTBEAT
  TIMEOUTS in the two-span `footprint_le_dead` lemmas, not logical failures.
  The added bind/match deepens the term; these will need restructuring or
  `set_option maxHeartbeats`.
- `:3386`, `:3400` - the `Computation`-to-`Costed` `_refines` pair. IMPORTANT
  AND GOOD NEWS: these need NO hypothesis, because both sides were amended
  identically. Proof repair only (the `simp only` set must step through the new
  outer bind and the match).
- `:4266`, `:4290` - `..._cost_le_eighty` (the generic caps).
- `:4683`, `:4707`, `:4731` - `..._cost_le_eighteen_of_size_ge_four` and the two
  `..._cost_le_ten_of_macro_crossing`.

All five cost errors have the same mechanical shape: the proof must become an
outer `costed_bind_cost_le` over the level read with a
`htail : forall cell?, (match cell? with ...).cost <= K` obligation, the `none`
arm closing by `simp [Costed.pure]`. The template to copy is
`canonicalRelativeRmmMachineLocalSpanCandidateCosted_cost_le_nine_of_size_ge_four`
(`InteriorDirectory.lean:4540-4570`), which already has exactly this shape.

### THE HYPOTHESIS CASCADE IS BOUNDED - measured, not assumed

Adding the domain hypothesis to the two `Costed`-to-spec `_refines` lemmas
propagates to the adjacent / left-middle / cross twins and then to
`canonicalRelativeRmmInteriorRangeMinCosted_refines_logical` (`:3672`). At that
dispatcher the branch guards discharge most of it: `hwithin` gives
`count <= macroSize` directly; `leftCount = macroSize - localStart <= macroSize`
and `rightCount = _ % macroSize < macroSize` are immediate. ONLY
`middleMacroCount = _ / macroSize <= macroSampleCount` needs more, and it
follows from `hbound : startBlock + count <= blockCount` via
`macroSampleCount = blockCount / macroSize + 1`. `hbound` is ALREADY carried by
the route-level theorems (e.g.
`canonicalRelativeRmmInteriorRangeMinCosted_erase_exact`), so the cascade
terminates inside this file rather than escaping to the cross-file consumers.

## DESIGN DECISION RECORDED: the `none` arm is `pure none`, not a recompute

The alternative was `| none => <recompute via Nat.log2>`, which would make
every `_refines` theorem unconditional and erase the entire hypothesis cascade
above - a materially cheaper commit. It was REJECTED: it would leave
`Nat.log2 count` textually present in the executed definitions, so the claim
"no silent Theta(log n) computation remains on the route" would rest on a
reachability argument about a dead branch rather than on the definitions. The
frozen REQ-B7-02 explicitly contemplates the equivalence carrying the route's
own hypotheses (`0 < count`, `count <= macroSize`), so the conditional form is
what the contract asks for. Flagged for coordinator visibility because it is
the single biggest cost driver left in the rung.

## VERIFICATION LEDGER (B7-07)

- `lake build RMQ` with the 952-line patch applied, nothing else: EXIT 0,
  244/244, "Build completed successfully", ZERO errors, warnings only from the
  recorded pre-existing baseline. `ReviewerReachabilitySmall` at [229/244],
  `FlatPayload` at [217/244], `ReviewerPhysical` at [220/244].
- `lake env lean InteriorDirectory.lean` with the four sites wired: EXIT 1,
  exactly 13 errors, enumerated above. ITERATE AID ONLY (no olean written).
- `git apply --check docs/internal/B7_STEP2_WIP.patch` (refreshed, 1107 lines)
  against the reverted tree: CLEAN.
- `lake build RMQ` on the REVERTED tree at this commit: recorded below.
- Source tree reverted to `21544b4`; this commit is DOCS ONLY.
- NOT RUN and NOT claimed this session: the cost harness (CHK-04), the headline
  axiom check, `#print axioms`, `design_decision_check.ps1`,
  `claim_drift_scan.ps1`, `paper_topology_lint.ps1`,
  `lake build RMQ RMQPaper RMQExamples`. The rung is not at a candidate state.
  Per the delegation, `scripts/axiom_check.lean` and `gate.ps1` were NOT run.
- KNOWN RED, externally owned, NOT re-verified and NOT claimed:
  `scripts/wordram_axiom_check.lean`, `scripts/axiom_check.lean`,
  `lake exe rmq_succinct_classic_validate`. Also not taken: the a07-owned stale
  `207` prose numerals in `README.md` and `docs/FAMILY_SUMMARY.md`.

## STATUS AT END OF THIS SESSION: INCOMPLETE

No acceptance-matrix row changed status. No row was weakened. No constant is
asserted. REQ-B7-05 and CHK-04 remain OPEN and are NOT claimed - the harness was
not run because no swap landed, so the twelve interior windows are necessarily
still at commit A's baseline. The slack artifact
`canonicalRelativeRmmPrincipledInteriorChargedTraceCost_announced_slack_of_size_ge_four_of_bounded`
is STILL PRESENT and still true, which is the correct state for a tree where the
swap has not landed.

## RESUME POINT, in order

1. FIRST, settle the width obstruction, because the cap arithmetic depends on it
   and nothing else should be built on the old width. Tighten
   `bpSparseLevelWidth` per "the fix is available" above and re-prove
   `bpSparseLevelCell_lt` / `bpSparseLevelEntries_lt_two_pow`.
2. Restate the two space-accounting envelope helpers over the new width
   (`sparseLevelWidth_add_two_le_of_pos`, `levelPartOverhead_le_envelope`). The
   bounds get easier; the statements still change.
3. Prove the new macro-crossing width lemma (item 2 of "what the width fix
   costs"). This is the one genuinely novel piece of arithmetic remaining in the
   rung and should be budgeted as such.
4. Apply `docs/internal/B7_STEP2_WIP.patch` (1107 lines, includes the four wired
   sites) and clear the 13 measured errors, group by group, using the templates
   and the cascade analysis above.
5. Only then the caps, the re-derived literal (expected to come back to `33` /
   `210`, but DERIVE it - that is the whole point of REQ-B7-05), the deletion of
   the slack artifact, provenance/W19, the vocabulary theorem, the docs, the
   matrix, and the full battery including CHK-04 against the session-2 baseline.

# Session 8 (B7-08)

THE WIDTH OBSTRUCTION IS CLOSED, and closed in the strong form the coordinator
required: not a sampled table of sizes but a checked all-size proposition
carrying the route's own reachability hypothesis. That work is COMMITTED AND
GREEN (`fa5e94d`). The swap (commit B) is still NOT landed; the refreshed patch
carries it.

## THE COORDINATOR RULING, and why it is a policy point

Ruling: tighten `bpSparseLevelWidth` to recover commit A's frozen `210`, rather
than re-migrate `210 -> 213` and freeze `210` as a second historical constant.
Recorded in full as DD-20260719-001. The short form:

A frozen historical constant records a value that GENUINELY DESCRIBED THE
ACCEPTED ROUTE at some point. `76`, `142` and `207` each did. `210` never did -
it exists only inside commit A's staging window and is an artifact of a
deliberately loosened cap. Freezing it would put a fiction in the permanent
record, which is worse than redoing a migration.

COORDINATOR CORRECTION OF RECORD, coordinator-initiated: the phrase "one
charged read per two-span call" was the coordinator's and was WRONG as stated,
because in this cost model a read costs one unit PER MACHINE WORD TOUCHED.
B7-07 was right to compute actual widths against `machineWordBits` rather than
trust the phrasing. This rung has now corrected the coordinator twice.

## THE WIDTH FIX (`SparseLevelTable.lean`)

`bpSparseLevelCell_lt` now concludes at `domain * (Nat.log2 domain + 1)`
instead of `domain * domain`. The stored level is `Nat.log2 i` with
`i < domain`, so it is bounded by `Nat.log2 domain`, not by `domain` -
exponentially smaller. The old bound was slack by construction.

    def bpSparseLevelWidth (domain : Nat) : Nat :=
      Nat.log2 (domain * (Nat.log2 domain + 1)) + 1

## THE ALL-SIZE FIT, with the hypothesis that IS the work

Four theorems, all `[propext, Quot.sound]` only. The two that matter, quoted
exactly:

    theorem bpSparseLevelLocalWidth_le_machine_of_macro_crossing
        {shape : Cartesian.CartesianShape}
        (hmacro : (RelativeRmm.canonicalLayout shape).macroSize <
            (RelativeRmm.canonicalLayout shape).blockCount) :
        bpSparseLevelWidth
            (bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize) <=
          SuccinctRank.machineWordBits shape.bpCode.length

    theorem bpSparseLevelGlobalWidth_le_machine_of_macro_crossing
        {shape : Cartesian.CartesianShape}
        (hmacro : (RelativeRmm.canonicalLayout shape).macroSize <
            (RelativeRmm.canonicalLayout shape).blockCount) :
        bpSparseLevelWidth
            (bpSparseLevelDomain
              (RelativeRmm.canonicalLayout shape).macroSampleCount) <=
          SuccinctRank.machineWordBits shape.bpCode.length

`hmacro` is NOT a size threshold introduced for convenience. It is exactly what
the interior dispatcher already derives before it can reach a cross-macro
two-span call: the branch guard `hcross` plus the route-level `hbound` produce
`hmacro : macroSize < blockCount` in
`canonicalRelativeRmmInteriorRangeMinCosted_cost_le_..._of_size_ge_four_of_bounded`.
The precedent carrying the identical hypothesis is
`canonicalRelativeRmmRelativeWidth_le_machine_of_macroSize_lt_blockCount`, and
the new lemmas are its analogue.

THE HYPOTHESIS IS LOAD-BEARING, exactly as the coordinator predicted. At
`size = 4`: base 3, `macroSize` 9, domain 11, tightened width 6 against a
`machineWordBits` of 4. The fit FAILS there. It is saved by unreachability:
macro crossing needs `9 < blockCount = 1`, which is false.

Derivation, no threshold introduced at any step:
macro crossing gives `base^3 < size`; `size < 2 ^ base` holds by definition of
`base = Nat.log2 size + 1`; together they force `10 <= base` by ELIMINATING
`base <= 9` (at `base = 9`, `base^3 = 729` but `2^9 = 512`). With `10 <= base`
the local domain `base*base + 2` is below `2 ^ base`, so its level is at most
`base`, so the packed product is at most `2 * base^3 < 2 ^ (base+1)`, giving
width `<= base + 1 <= machineWordBits shape.bpCode.length` via the existing
`canonicalRelativeRmmBase_succ_le_machine_of_size_pos`. The global instance runs
the same way through `base * (size / base^3) <= size`.

Branches WITHOUT `hmacro` are covered unconditionally by
`bpSparseLevelLocalWidth_le_seven_machine` and
`bpSparseLevelGlobalWidth_le_seven_machine` (`<= 7 * machineWordBits`), so those
reads charge at the `cost_le_eight` rate. Those branches only have to stay under
the interior cap and have ample headroom. Their proofs are elementary: `base`
bounds `machineWordBits` by monotonicity, and `Nat.lt_two_pow_self` does the
rest - no induction anywhere in this rung's width arithmetic.

## SPACE ACCOUNTING: RE-DERIVED, NOT ASSUMED - and it did need work

The tighter width makes the table SMALLER, so the bounds get easier, but the
four links state the width SYNTACTICALLY: 13 occurrences of
`Nat.log2 ((x+2)*(x+2)) + 1` across the raw-overhead def, the `527` linear feed
and the envelope arithmetic. They do NOT transport for free.

Resolved by a bridge rather than by reproving:

    private theorem bpSparseLevelWidth_le_square_width
        {domain : Nat} (hpos : 0 < domain) :
        bpSparseLevelWidth domain <= Nat.log2 (domain * domain) + 1

so each existing bound is inherited through one `Nat.le_trans`. CONSEQUENCE
WORTH STATING: the `527` capacity constant and both `LittleOLinear` envelopes
are UNCHANGED and remain valid - now loose rather than tight, which is sound for
upper bounds. No row is weakened, and `ReviewerPhysical.lean` needs no second
migration.

One genuine repair was needed: the `n = 0` case of
`..._RawPayloadOverhead_le_linear` closed on `Nat.log2 9` and now needs
`bpSparseLevelWidth 3`, which does not reduce. Routed through the bridge.

## THE 13 ERRORS ARE CONFIRMED UNCHANGED

With the refreshed patch applied, `lake env lean` on `InteriorDirectory.lean`
reports EXACTLY 13 errors - the same five groups B7-07 enumerated, with no new
error introduced by the width work or the space-accounting migration. LINE
NUMBERS IN THE PATCHED FILE HAVE MOVED, because the width block adds 352 lines
at `:4042`. The first eight are unmoved; the five cost errors shift by +352:

    :2027 :2039              Costed-to-spec _refines pair (needs domain hyp)
    :2498 :2502 :2518 :2522  footprint_le_dead heartbeat timeouts
    :3386 :3400              Computation-to-Costed _refines (NO hypothesis)
    :4618 :4642              _cost_le_eighty        (was :4266 :4290)
    :5035 :5059 :5083        _cost_le_eighteen + two _cost_le_ten_of_macro_crossing
                             (was :4683 :4707 :4731)

## CORRECTIONS OF RECORD (tooling; each cost real time)

1. `import RMQ` DOES NOT REACH `InteriorDirectory`. `#print axioms` on any
   `InteriorDirectory` name reports `unknown constant` under `import RMQ` even
   after a successful `lake build RMQ`. Import the module directly:
   `import RMQ.Core.SuccinctClose.EndpointFringe.InteriorCandidate.InteriorDirectory`.
   This is a real trap: the failure looks exactly like "the theorem was not
   built", and the standing instruction says only "after a root build".
2. DO NOT splice Lean source with Windows Python using default encoding.
   Reading a UTF-8 file without `encoding='utf-8'` and rewriting it produced
   mojibake in the middle-dot and disjunction characters, which Lean reported as
   "unknown tactic" - a misleading error a long way from the real cause.
3. `Nat.lt_two_pow` does not exist; the name is `Nat.lt_two_pow_self`.
   `Nat.pos_pow_of_pos` is deprecated in favour of `Nat.pow_pos`, whose argument
   order differs.

## VERIFICATION LEDGER (B7-08), all as observed

- `lake build RMQ` at `fa5e94d` (width fix committed, swap NOT applied):
  EXIT 0, 243/244, "Build completed successfully", ZERO errors, TWELVE
  warnings - byte-identical to the recorded baseline
  (`SuccinctFinalRAM` :5804 :5807 :5809 :5811 :5933 :5934;
  `ReviewerReachabilitySmall` :463 :1484 twice; `ReviewerReachabilityLong`:519;
  `ReviewerReachabilitySparse`:563; `BPNavigationRAM`:2111). NONE in a file
  this session touched.
- `lake build RMQ RMQPaper RMQExamples` at `fa5e94d`: EXIT 0, 266/268,
  "Build completed successfully". `RMQExamples.Concrete` builds, so commit A's
  `#guard`s still pass across the width change.
- `claim_drift_scan.ps1`: exit 0, "scan complete (782 hits, 0 strict failures)".
- `paper_topology_lint.ps1`: exit 0, "PAPER-TOPOLOGY PASS (83 broad documentary
  identifiers; 49 paper identifiers resolved)" - byte-identical counts to the
  commit A ledger, as expected since no literal moved this session.
- `lake env lean scripts/headline_axiom_check.lean`: exit 0, zero errors, zero
  `Lean.ofReduceBool`.
- `rg` for `native_decide` / `ofReduceBool` across `RMQ/` and `RMQExamples/`:
  ZERO hits.
- `git diff --check f6564ec..HEAD`: exit 2, hits ONLY
  `docs/internal/B7_STEP2_WIP.patch`. Structural committed-patch property,
  documented since B7-03 (a blank context line in a unified diff is a single
  space). NOT a source defect; do not "fix" it.
- `#print axioms` after that root build, importing the module directly:
  `bpSparseLevelLocalWidth_le_machine_of_macro_crossing`,
  `bpSparseLevelGlobalWidth_le_machine_of_macro_crossing`,
  `bpSparseLevelLocalWidth_le_seven_machine`,
  `bpSparseLevelGlobalWidth_le_seven_machine`, `bpSparseLevelCell_lt`,
  `bpSparseLevelEntries_lt_two_pow`, `bpSparseLevelTable` - ALL
  `[propext, Quot.sound]`. No `Classical.choice`, no `Lean.ofReduceBool`.
- `lake env lean InteriorDirectory.lean` WITH the refreshed patch applied:
  EXIT 1, exactly 13 errors as enumerated above. ITERATE AID ONLY.
- Hygiene `rg` over both touched Lean files: ZERO hits for
  sorry/admit/native_decide/implemented_by/partial/unsafe/extern/
  noncomputable/`import Mathlib`/axiom/ofReduceBool.
- `git diff --check` on the working tree: exit 0.
- `design_decision_check.ps1 -Strict -Base f6564ec`: exit 0,
  "DESIGN-CHECK: checked 22 changed files".
- `git apply --check docs/internal/B7_STEP2_WIP.patch` (refreshed, 1128 lines)
  against `fa5e94d`: CLEAN.
- NOT RUN and NOT claimed: the cost harness (CHK-04), `headline_axiom_check`.
  The rung is not at a candidate state and no swap landed, so the twelve
  interior windows are necessarily still at commit A's baseline.
- Per the delegation, `scripts/axiom_check.lean` and `gate.ps1` were NOT run.
- KNOWN RED, externally owned, NOT re-verified and NOT claimed:
  `scripts/wordram_axiom_check.lean`, `scripts/axiom_check.lean`,
  `lake exe rmq_succinct_classic_validate`; and the a07-owned stale `207` prose
  numerals in `README.md` and `docs/FAMILY_SUMMARY.md`.

## STATUS AT END OF THIS SESSION: INCOMPLETE

No acceptance-matrix row changed status. No row was weakened. No constant is
asserted. REQ-B7-05 and CHK-04 remain OPEN and are NOT claimed. The slack
artifact
`canonicalRelativeRmmPrincipledInteriorChargedTraceCost_announced_slack_of_size_ge_four_of_bounded`
is STILL PRESENT and still true, which is correct for a tree where the swap has
not landed.

## RESUME POINT, in order

The width obstruction is CLOSED and committed; do not revisit it. Start at 1.

1. Apply `docs/internal/B7_STEP2_WIP.patch` (1128 lines, `git apply --check`
   clean at `fa5e94d`). It carries the store extension, all four
   space-accounting links migrated to the new width, the `527` migration, and
   the four wired sites.
2. Clear the 13 errors group by group, at the line numbers above. Templates and
   the bounded hypothesis cascade are in session 7's entry and still apply;
   `:3386`/`:3400` need NO hypothesis.
3. Charge the level reads: `cost_le_one` under `hmacro` via the two
   `_of_macro_crossing` fit theorems; `cost_le_eight` elsewhere via the two
   unconditional ones. THE FIT LEMMAS ARE ALREADY IN THE TREE at `fa5e94d` -
   they need only to be applied.
4. Re-tighten the caps and DELETE the slack artifact (its `30 < cap` conjunct
   becomes unprovable - that is the signal commit B is real).
5. Re-derive the literal over the AMENDED route and exhibit the maximizing
   branch bound. Expected back at `33` / `210`, but DERIVE it; that is what
   closes REQ-B7-05.
6. Provenance/W19, the vocabulary theorem, REQ-B7-08 docs, the matrix, and the
   full battery including CHK-04 against the session-2 baseline. The interior
   windows MUST move.

# Session 10 (B7-10)

## WHAT I INHERITED, AND HOW IT DIFFERED FROM THE DELEGATION

The delegation described one blocker in `SuccinctFinalRAM.lean` (timeout at
`:5992`/`:5953`, cascade at `:6020`) and a resume point calling for the caps,
the slack deletion and the literal. ALL OF THAT WAS ALREADY DONE in the
uncommitted working tree; session 9 was never logged, so the worklog's session-8
resume point and the coordinator's error report were both stale. Verified rather
than assumed:

- `lake env lean RMQ/Core/SuccinctFinalRAM.lean`: EXIT 0, zero errors, and
  `InteriorDirectory.olean` (01:46:19) was NEWER than its source (01:44:26), so
  it had typechecked against the SWAPPED definitions. The `SuccinctFinalRAM`
  witness had already been rewritten to exhibit the level read, with the
  rationale in a comment at `:5964-5972`.
- The cap constant is `33`, the tight branch theorem is
  `..._cost_le_thirty_three_literal_of_size_ge_four_of_bounded`, and the slack
  artifact is DELETED (tombstone comment at `InteriorDirectory.lean:5541-5555`).
- The live literal is already `210` with `207` frozen; W19 already carries the
  level read through the EXISTING `lcaInterior` constructor.

FIRST ACTION was still the preservation the delegation asked for: the WIP patch
was refreshed from the working tree and committed docs-only at `714fb4a`, with
`git apply --check` verified CLEAN against a scratch worktree at `65c6ab3`.

## THE REAL BLOCKER WAS IN A DIFFERENT FILE

`lake build RMQ RMQPaper RMQExamples` failed with the SAME signature the
coordinator described but in `ReviewerReachabilitySmall.lean`:

    :2096:0    (deterministic) timeout at `whnf`, 200000 heartbeats
    :2699:16   (kernel) unknown constant
               '..._private...reviewerIncreasingCanonicalInterior_successfulRead'

The coordinator's structural diagnosis was CORRECT - it was simply pointing at
the file where the symptom had already been fixed. Cause (1) was genuinely live
here, and this is exactly the case where raising `maxHeartbeats` would have
produced a theorem describing the wrong machine:

    let slot := bpLocalSparseCellSlot layout.macroSize layout.levelCount 0 1
      (Nat.log2 2)                                       -- proof-level log2
    ...
    have hlocalSpan : ... in ((canonicalRelativeRmmMachineLocalSpanCandidate
      Computation shape 0 1 (Nat.log2 2)).run store).reads
    have htwo : ... := by
      unfold ...LocalTwoSpanCandidateComputation
      simp only [bind_run, append]
      exact List.mem_append_left _ hlocalSpan     -- SPAN CLAIMED LEFTMOST

`canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation`
(`InteriorDirectory.lean:2351-2373`) now binds the LEVEL read first and only
then, inside the `match` on the read value, reads the span. So the span read is
no longer in the left summand of the append and `mem_append_left` no longer
places it there.

## THE REPAIR

Rewritten against the amended computation's ACTUAL read sequence. The witness
now exhibits the LEVEL read, which the outer bind performs unconditionally
before matching on the read value and which is therefore genuinely the leftmost
read. Consequences worth recording:

- No `Nat.log2` and no `bpLocalSparseCellSlot` address arithmetic survive at
  proof level. The level slot IS the count the route presents (`2`), so the
  concrete `slot` unfolding that drove elaboration into `whnf` is GONE rather
  than merely made cheaper. That is why no heartbeat increase was needed.
- The in-range obligation is discharged positionally: `2 < domain` from
  `bpSparseLevelEntries_length` and `bpSparseLevelDomain = bound + 2`, with
  `hmacroSize : macroSize = 25`.
- New `reviewerCanonicalComponent_localLevel_get`, the component-store accessor
  for the level region, stated over the six regions that PRECEDE it and
  quantified over everything that follows - the same discipline the local
  accessor documented, which is what keeps it stable as the store grows.

DEAD SOURCES REMOVED IN THE SAME COMMIT. The rewrite took the last caller of
`reviewerCanonicalComponent_local_get` and of `reviewer_log2_twentyFive`; both
are deleted, since "no dead sources at any commit" binds here.

## CHK-04: SIX OF EIGHT INTERIOR WINDOWS MOVED, AND THE TWO THAT DID NOT CANNOT

`lake exe rmq_succinct_classic_cost_harness`, EXIT 0, "all reported windows
agree with reference List Int RMQ semantics", `canonicalBound=210` and
`canonicalBoundIs210=true` on every window. Against the session-2 baseline:

    fixture             window          baseline  now   delta
    tie-boundary n=6    [0,6)   cross      76      76     0
    tie-boundary n=6    [1,5)   cross      72      72     0
    generated-64        [0,64)  cross     116     118    +2
    generated-64        [7,39)  cross     126     128    +2
    zigzag-128          [0,128) cross      92      93    +1
    zigzag-128          [17,97) cross      96      97    +1
    generated-128-alt   [0,128) cross      93      94    +1
    generated-128-alt   [15,96) cross      95      96    +1
    (all four sameBlock rows 54/62/57/57 unchanged, as expected - sameBlock
     does not enter the interior)

THE TWO UNMOVED WINDOWS ARE STRUCTURALLY INCAPABLE OF MOVING, and this was
checked rather than argued. Probed layouts:

    tie n=6  blockSize=6  blockCount=2  macroSize=9  macroSampleCount=1
    gen64    blockSize=14 blockCount=9  macroSize=49 macroSampleCount=1

With `blockCount=2` a crossBlock query's two endpoint blocks have NO block
strictly between them, so the interior range-min is invoked with `count=0` and
takes the `Costed.pure` branch. Probed directly:

    tie n=6  interior startBlock=0 count=0 cost=0
    tie n=6  interior startBlock=0 count=1 cost=18
    tie n=6  interior startBlock=0 count=2 cost=18
    gen64    interior startBlock=0 count=0 cost=0
    gen64    interior startBlock=0 count=1 cost=18

The charged level read lives inside the two-span computation, which `count=0`
never reaches. So the n=6 rows carry zero interior reads before AND after the
swap; they are not evidence of a dead store.

The criterion's stated RATIONALE ("windows identical to baseline would mean the
store grew and nothing reads it") is therefore disproven - the store is read on
every window whose fixture has `blockCount >= 3`. But the criterion's LITERAL
window list includes `76` and `72`, and those did not move. I am NOT closing
CHK-04 on my own authority and I have NOT weakened the row. The coordinator
should decide whether to amend the window list to exclude the `blockCount=2`
fixture, with the probe above as the justification.

## VERIFICATION LEDGER (B7-10), all as observed

- `lake build RMQ RMQPaper RMQExamples` at the candidate state: "Build completed
  successfully", `LAKE_EXIT=0`, twelve warnings (the recorded baseline; none in
  a file this session touched).
- `lake exe rmq_succinct_classic_cost_harness`: `HARNESS_EXIT=0`, table above.
- `lake env lean scripts/headline_axiom_check.lean`: `EXIT=0`, zero
  `Lean.ofReduceBool`, zero `sorryAx`.
- `#print axioms` after a root build, importing the modules DIRECTLY:
  `..._small_successful_closed_valid_occurrence` (the public consumer of the
  rewritten private witness), `..._cost_le_thirty_three_literal_...`,
  `..._cost_le_thirty_of_size_ge_four_of_bounded`,
  `..._readWord_only`, `..._counted_producer_may_path` - all
  `[propext, Classical.choice, Quot.sound]`. And `queryCost_eq`,
  `..._PrincipledAllSizeChargedTraceCost_eq`, `..._CloseCost_eq`,
  `..._SilentSparseLevelChargedTraceCost_eq` report "does not depend on any
  axioms", which is the sharpest available evidence that `210` is COMPUTED and
  not asserted.
- Hygiene `rg` over all seven touched Lean files: ZERO hits for
  sorry/admit/native_decide/implemented_by/partial/unsafe/extern/noncomputable/
  `import Mathlib`/axiom/ofReduceBool. `native_decide`/`ofReduceBool` across
  `RMQ/` and `RMQExamples/`: ZERO.
- `git diff --check` on the working tree: exit 0. `git diff --check
  f6564ec..HEAD`: exit 2, hits ONLY `docs/internal/B7_STEP2_WIP.patch` - the
  documented structural property of a committed unified diff. NOT a defect.
- `design_decision_check.ps1 -Strict -Base f6564ec`: exit 0, "DESIGN-CHECK:
  checked 24 changed files".
- `claim_drift_scan.ps1`: exit 0, "scan complete (721 hits, 0 strict failures)".
- `paper_topology_lint.ps1`: exit 0, "PAPER-TOPOLOGY PASS (83 broad documentary
  identifiers; 49 paper identifiers resolved)".
- KNOWN RED, externally owned, CONFIRMED UNCHANGED and NOT fixed:
  `lake exe rmq_succinct_classic_validate` fails at elaboration with
  "`singletonRepeatedEqualReadPositionsOK` did not evaluate to `true`"
  (`Validation/SuccinctClassic.lean:253`). That is precisely the a07-owned
  fixture the delegation ring-fenced; the failure is in the fixture, not in the
  literal migration in the same file.
- Per the delegation, `scripts/axiom_check.lean`, `scripts/wordram_axiom_check.lean`
  and `gate.ps1` were NOT run.

## NUMERALS MOVED (FOR THE MERGE RECONCILER)

Moved by session 9 and carried in this commit; none moved by session 10:

    canonicalTransitionalQueryCost      328 -> 352
      RMQ/Core/SuccinctRMQClassic.lean:148
      RMQ/Validation/SuccinctClassic.lean:270
      RMQExamples/Concrete.lean:89
      docs/internal/CLAIM_DRIFT_POLICY.json  id canonical-transitional-328 ->
        canonical-transitional-352, pattern \b328\b -> \b352\b
      scripts/paper_topology_lint.ps1  oldRegimePattern gains 352 (328 retained)
    interior cap                         30 -> 33
      InteriorDirectory.lean:1934
    live whole-query literal            207 -> 210 (queryCost), with 207/126
      frozen as named historical constants pinned to LITERAL components
      (SuccinctFinalRAM.lean:8852 = 30, :8874 = 37)

`Validation/SuccinctClassic.lean`'s a07-owned fixture was NOT touched.

## STATUS AT END OF THIS SESSION

The library and both example/paper targets are green, the swap is committed as
real source rather than a patch, and the rung's substantive obligations carry
evidence. CHK-04 is the one row I decline to close on my own authority, for the
reason recorded above. No row was weakened, no constant is asserted, no frozen
identity was renamed or deleted.

# Session 11 (B7-11)

## WHAT I WAS ASKED, AND THE RULING I IMPLEMENTED

Session 10 left exactly one row open: CHK-04. It had probed why the two
`tie-boundary` `n=6` windows did not move and asked the coordinator to rule on
excluding that fixture from the row's window list.

THE COORDINATOR DECLINED TO EXCLUDE IT and ruled instead: ADD a tie-boundary
fixture with `blockCount >= 3`, keep the `blockCount = 2` one. Two reasons,
recorded here because they govern what this session did:

1. Excluding a fixture BECAUSE it did not move, on the strength of an argument,
   is the move anti-vacuity rows exist to prevent. CHK-04's job is to convert
   "the store is read" from an argument into an observation; narrowing the
   observation set to fit the argument inverts that.
2. Independently of bookkeeping, the probe revealed a REAL COVERAGE GAP. The
   tie-boundary group exists to exercise leftmost tie-breaking. If every fixture
   in it has `blockCount = 2`, tie-breaking has never been exercised with the
   interior participating at all.

CHK-04's wording was NOT edited and the `blockCount = 2` fixture was NOT removed.

## THE NEW FIXTURE, AND WHY IT REACHES THE INTERIOR

`tie-boundary-live-interior`, n=24, added to `defaultFixtures` in
`RMQ/Validation/SuccinctClassicCostHarness.lean` immediately after the existing
`tie-boundary`.

The interior invocation condition is not assumed from the fixture size; it is
read off the live route. `canonicalCrossBlockCloseCostedWithRankSeed`
(`RelativeRmmMacro/ConcreteDirectoryRAM.lean:2336-2340`) invokes
`(canonicalRelativeRmmInteriorDirectory shape).rangeMinCosted (leftBlock + 1)
(rightBlock - leftBlock - 1)` ONLY under `leftBlock + 1 < rightBlock`, and takes
`Costed.pure none` otherwise. Probed at the candidate state:

    fixture=tie-boundary-live-interior n=24 base=5 blockSize=10 blockCount=4
      window=[0,24)  leftBlock=0 rightBlock=4 interiorLive=true  count=3 interiorCost=18
      window=[4,20)  leftBlock=1 rightBlock=4 interiorLive=true  count=2 interiorCost=18
      window=[10,20) leftBlock=2 rightBlock=4 interiorLive=true  count=1 interiorCost=18
      window=[11,12) leftBlock=2 rightBlock=2 interiorLive=false count=0 interiorCost=0

So the fixture covers interior `count = 3, 2, 1` AND retains a `count = 0`
sameBlock control inside the same shape.

THE INTERIOR IS LOAD-BEARING, NOT MERELY LIVE. This is the part that closes the
coverage gap rather than just the bookkeeping. The values are
`[9,8,9,7,9, 4,6,4,9,4, 8,4,9,4,6, 8,4,9,4,8, 9,7,9,8]`, so the minimum `4`
occurs ONLY at indices 5, 7, 9, 11, 13, 16, 18. Probed index-to-block map:

    0:4/b0   1:5/b0   2:7/b0   3:8/b0   4:10/b1  5:11/b1  6:14/b1  7:15/b1
    8:18/b1  9:19/b1  10:22/b2 11:23/b2 12:26/b2 13:27/b2 14:30/b3 15:32/b3
    16:33/b3 17:36/b3 18:37/b3 19:40/b4 20:42/b4 21:43/b4 22:46/b4 23:47/b4

Every minimum lies in block 1, 2 or 3 - the interior blocks for `[0,24)` - and
the two fringe blocks (b0 = indices 0-3, values 9,8,9,7; b4 = indices 19-23,
values 8,9,7,9,8) contain NO minimum. The leftmost-tie answer for `[0,24)` is
index 5, at close 11 in block 1, which is an interior block. The answer is
therefore produced by the interior range-min breaking ties ACROSS blocks 1, 2
and 3, not by either fringe decoder. That interaction had no coverage before
this session.

## AN ACCOUNTING CORRECTION: THERE ARE NINE CROSSBLOCK WINDOWS, NOT EIGHT

Recorded so a later reader does not think the table shrank. Session 10's table
listed eight crossBlock windows and four sameBlock windows. The
`tiny-leftmost-ties` fixture was omitted from that accounting ENTIRELY: its
`[0,5)` window is crossBlock and its `[2,4)` window is sameBlock, so the true
pre-existing counts are NINE crossBlock and FIVE sameBlock. The omission was in
the write-up, not in the harness - `tiny-leftmost-ties` has always run. Probed:

    fixture=tiny-leftmost-ties n=5 base=3 blockSize=6 blockCount=1
      window=[0,5) leftBlock=0 rightBlock=1 interiorLive=false count=0

`blockCount = 1`, so its interior is dead for the same structural reason as the
`n=6` fixture, only more so. The table below covers all 21 windows.

## BEFORE/AFTER, MEASURED BOTH SIDES MYSELF

I did NOT carry session 10's baseline forward as my own. A detached scratch
worktree at `714fb4a` (the pre-swap preservation commit; commit A's code, whose
harness numbers session 10 recorded as identical to the session-2 baseline) got
the IDENTICAL new fixture, and both harnesses were run. Both exit 0, both print
"all reported windows agree with reference List Int RMQ semantics", and
`canonicalBound=210` / `canonicalBoundIs210=true` on every window on both sides.

    fixture (blockCount)              window     route      cnt  before after  delta
    tiny-leftmost-ties      n=5  (1)  [0,5)      crossBlock   0     68    68      0
                                      [2,4)      sameBlock    -     57    57      0
                                      [1,1)      invalid      -      0     0      0
                                      [2,1)      invalid      -      0     0      0
                                      [0,6)      invalid      -      0     0      0
    tie-boundary            n=6  (2)  [0,6)      crossBlock   0     76    76      0
                                      [1,5)      crossBlock   0     72    72      0
                                      [2,3)      sameBlock    -     54    54      0
    tie-boundary-live-      n=24 (4)  [0,24)     crossBlock   3    112   114     +2
      interior   (NEW)                [4,20)     crossBlock   2    107   109     +2
                                      [10,20)    crossBlock   1    105   107     +2
                                      [11,12)    sameBlock    0     73    73      0
    generated-64            n=64 (9)  [0,64)     crossBlock   8    116   118     +2
                                      [7,39)     crossBlock   3    126   128     +2
                                      [31,32)    sameBlock    -     62    62      0
    zigzag-128             n=128 (16) [0,128)    crossBlock  14     92    93     +1
                                      [17,97)    crossBlock   9     96    97     +1
                                      [64,65)    sameBlock    -     57    57      0
    generated-128-alt      n=128 (16) [0,128)    crossBlock  14     93    94     +1
                                      [15,96)    crossBlock  10     95    96     +1
                                      [63,64)    sameBlock    -     57    57      0

The nine pre-existing crossBlock and five sameBlock "before" values reproduce
session 10's recorded baseline exactly, so that baseline is corroborated by
independent measurement rather than inherited.

THE RESULT IS SHARPER THAN "SIX OF EIGHT MOVED". The set of windows that moved
is EXACTLY the set whose interior is invoked with `count > 0`:

- All nine windows with `count > 0` moved (three of them the new fixture's).
- All twelve windows with no live interior - three crossBlock with `count = 0`,
  five sameBlock, three invalid, one sameBlock in the new fixture - did not.

There is no window on either side of that partition that behaves against it.
That is a stronger anti-vacuity observation than the row asked for: it is not
merely that some windows moved, it is that movement and interior-liveness
coincide exactly across 21 windows.

THE DELTA SIZE IS SHAPE-DETERMINED, NOT COUNT-DETERMINED. `+2` on the n=24 and
n=64 fixtures at counts 1, 2, 3, 8 alike; `+1` on both n=128 fixtures at counts
9, 10, 14. I OBSERVE this and did not derive it; the natural reading is that the
branch taken through the interior (within-macro versus macro-crossing) differs
by shape and carries a different number of level reads, but I am not asserting
that as a checked fact.

THE STORE GREW ON EVERY FIXTURE. `payloadBits` before -> after: tiny 541->616,
tie n=6 577->652, new n=24 1871->2096, gen64 4635->5103, zigzag 10781->11384,
gen128alt 10781->11384. This is worth pairing with the table: the level table is
added to EVERY shape, including the two whose windows cannot move. That is
exactly the "the store grew and nothing reads it" hazard CHK-04 names, and it is
precisely why a `blockCount >= 3` tie-boundary fixture was needed - on the
tie-boundary group specifically, growth was previously unaccompanied by any
observed read.

## WHAT THE `blockCount = 2` FIXTURE DEMONSTRATES (not a defect)

Recorded per the coordinator's instruction. The `tie-boundary` n=6 fixture, and
`tiny-leftmost-ties` n=5 alongside it, are KEPT and are legitimate coverage.
They demonstrate the ZERO-INTERIOR PATH: a crossBlock query whose endpoint
blocks are adjacent (or identical), where `leftBlock + 1 < rightBlock` is false,
the interior range-min is never entered, and the answer is produced by the two
fringe decoders and their merge alone. Their stability across the swap is the
CORRECT behaviour - a charged read added inside the two-span computation must
not change the cost of a route that never reaches it. If those two windows HAD
moved, that would have been the defect, because it would mean the level read was
being charged on a path that does not perform it.

So the row now rests on both halves of the partition: `count > 0` windows move,
`count = 0` windows do not, and both are observed rather than argued.

## CHK-04 - EVIDENCE COMPLETE

The row's requirement is met on its own terms and without amendment: the harness
run is recorded, the guards are consistent with the DERIVED literal
(`canonicalBound=210`, `canonicalBoundIs210=true` on all 21 windows, both
sides), and interior-route windows MOVED - nine of them, including three in a
tie-boundary fixture. The row's literal window list included `76` and `72`;
those windows are still present, still at `76`/`72`, and the reason is now an
observed structural property of the zero-interior path rather than an excuse.
NOT closed unilaterally; coordinator acceptance required.

## VERIFICATION LEDGER (B7-11), all as observed at `8131716`

- `lake build RMQ RMQPaper RMQExamples`: `Build completed successfully.`,
  `LAKE_EXIT=0`, TWELVE warnings - the recorded baseline, and none in a file
  this session touched (the only touched Lean file is the harness).
- `lake exe rmq_succinct_classic_cost_harness` at the committed HEAD:
  `HARNESS_EXIT=0`, `all reported windows agree with reference List Int RMQ
  semantics`, `canonicalBound=210` / `canonicalBoundIs210=true` on all 21
  windows. The new fixture at HEAD:

      window=[0, 24)  answer=some 5  expected=some 5  agrees=true crossBlock modeledTraceCost=114
      window=[4, 20)  answer=some 5  expected=some 5  agrees=true crossBlock modeledTraceCost=109
      window=[10, 20) answer=some 11 expected=some 11 agrees=true crossBlock modeledTraceCost=107
      window=[11, 12) answer=some 11 expected=some 11 agrees=true sameBlock  modeledTraceCost=73

  `answer=some 5` on `[0,24)` is the leftmost tie at index 5, which lies in
  interior block 1 - the harness output itself witnesses that the interior
  decided the answer.
- Pre-swap comparison run at `714fb4a` in a detached scratch worktree with the
  IDENTICAL fixture: `HARNESS_EXIT=0`, same agreement line, same guards. Full
  21-window table in the session-11 entry above.
- `lake env lean scripts/headline_axiom_check.lean`: `HEADLINE_EXIT=0`, ZERO
  `ofReduceBool`, ZERO `sorryAx` (grep count 0 over the whole output).
- `#print axioms`: NOT APPLICABLE THIS SESSION and not claimed. This session
  added no theorem, no definition in the library, and no constant - the only
  Lean change is a `Fixture` value inside the harness executable
  (`RMQ/Validation/SuccinctClassicCostHarness.lean`), which is not in the
  theorem trust base. Session 10's `#print axioms` results are NOT restated here
  as this session's evidence.
- Hygiene `rg` over the touched Lean file for
  sorry/admit/native_decide/implemented_by/partial/unsafe/extern/noncomputable/
  `import Mathlib`/axiom/ofReduceBool: ZERO hits (rg exit 1).
  `native_decide`/`ofReduceBool` across `RMQ/` and `RMQExamples/`: ZERO hits
  (rg exit 1).
- `git diff --check` on the working tree: exit 0.
  `git diff --check f6564ec..HEAD`: exit 2, hits ONLY
  `docs/internal/B7_STEP2_WIP.patch` - confirmed by reducing the output to its
  distinct file list, which is that one path. Structural property of a committed
  unified diff, documented since B7-03. NOT a defect and NOT "fixed".
- `design_decision_check.ps1 -Strict -Base f6564ec`: exit 0,
  `DESIGN-CHECK: checked 24 changed files`.
- `claim_drift_scan.ps1`: exit 0,
  `CLAIM-DRIFT: scan complete (736 hits, 0 strict failures)`. Hit count moved
  736 from session 10's 721; the delta is documentary text added by this
  session's worklog and matrix entries, and strict failures remain 0.
- `paper_topology_lint.ps1`: exit 0,
  `PAPER-TOPOLOGY PASS (83 broad documentary identifiers; 49 paper identifiers
  resolved)`.
- KNOWN RED, externally owned, CONFIRMED UNCHANGED and NOT fixed:
  `lake exe rmq_succinct_classic_validate` exits 1, failing at COMPILE time:

      error: RMQ/Validation/SuccinctClassic.lean:253:0: expression
        singletonRepeatedEqualReadPositionsOK
      did not evaluate to `true`

  This is the a07-owned fixture the delegation ring-fenced. Note that this
  session edited `RMQ/Validation/SuccinctClassicCostHarness.lean`, a DIFFERENT
  file from `RMQ/Validation/SuccinctClassic.lean`; the two are separate
  `lean_exe` roots, so the harness runs green while the validate target stays
  red for a reason this rung neither caused nor touched.
- Per the delegation, `scripts/axiom_check.lean`,
  `scripts/wordram_axiom_check.lean` and `gate.ps1` were NOT run.

## B7 MATRIX STATE AT THE END OF THIS SESSION

CHK-04 was the sole row session 10 left without complete evidence. It now has
complete evidence on its UNAMENDED wording. Every other row's evidence stands as
recorded in the session 7, 8 and 10 matrix sections; this session did not
disturb any of them, because it changed no library source - only an executable
fixture and two documents.

No row is closed unilaterally. Per this project's standing discipline, worker
sessions record evidence and a disposition; ACCEPTANCE is the coordinator's and
is not claimed here for CHK-04 or for any other row.

Nothing was weakened: no requirement text edited, no fixture removed, no
constant asserted, no frozen identity renamed or deleted, and no dead source
introduced.

# B7-R1 repair session: governed preflight, contract freeze, and scope stop

## Checkout and governance

- Worker: B7-R1.
- Requested title: `(B7-R1) Close the charged sparse-level acceptance contract`.
- Worktree: `C:\Users\poin\.codex\worktrees\dd4a\RMQ`.
- Exact base: `55e2b9ae3704a16129aaecc9c12f487aee5df12e`.
- Branch: `codex/b7-charged-sparse-level-r1`.
- Governance: `bd854edaa65944d5a7fa0fac5667e9572c370bbb`.
- `scripts/project_skill_preflight.ps1` with required
  `rmq-proof-sprint` and runtime skills `rmq-audit-prompt`,
  `rmq-coordinator`, `rmq-proof-sprint`: exit 0 in 8.5s.

The append-only B7-R1 contract and verification ledger were frozen before any
repair implementation and committed as `197a3f7`. No Lean, trust, harness,
hygiene-artifact, public-surface, design-decision, or workflow-decision repair
was made after the freeze, because the current-surface inventory exposed a
closed-write-scope dependency.

## Blocking dependency: five registered current surfaces are out of scope

`docs/internal/CLAIM_DRIFT_POLICY.json` version 18 registers 18 current fact
surfaces through `currentFactSurfacePathRegex`. Five registered files outside
the B7-R1 closed write list contain stale current B7 facts and require edits:

- `docs/PAPER_RELATED_WORK.md:102-107`: current canonical charged-trace bound
  `76`.
- `docs/PUBLICATION_STRATEGY.md:66-71`, `:122-127`, and `:151-155`: current
  canonical `76` story.
- `docs/RELATED_WORK_AND_LIMITATIONS.md:55-64`: current `76` bound and
  component-minimality wording.
- `docs/ROADMAP.md:74-79`: current algebra
  `2*13 + (2*4 + 2*4 + 30) + 4 = 76` and weaker three-constructor event
  vocabulary.
- `docs/internal/RMQ_FINAL_ROADMAP.md:199-217`: current U3 `76` and weaker
  three-constructor vocabulary.

The frozen B7-R1 requirement says every surface registered by the candidate
policy must state the checked current facts, including the exact `210` algebra
and the separate strong public `readWord`-only theorem identity. Removing these
paths from the registry, allowlisting their current prose, or treating a green
scanner as a substitute for correcting the statements would weaken or evade
the contract. The delegation explicitly says to stop on a genuinely new
required path outside the closed transitive write list. Coordinator authority
is therefore required to add these five paths (or to amend the semantic
contract) before implementation may continue.

The inventory also found the inverse registry gap:
`docs/ADD_PROVENANCE.md` is explicitly in B7-R1 write scope but absent from the
current-surface regex. It contains stale `20-source` and global-position
`0`/`12` prose. On an authorized continuation it should join the current
registry, with exact frozen-history treatment for historical material.

## Read-only diagnostics and resume leads

- `powershell -ExecutionPolicy Bypass -File scripts/claim_drift_scan.ps1
  -Strict`: exit 1 in 11.1s with 55 strict failures. Among the failures are
  stale current costs, source counts, positions, weaker vocabulary, and missing
  strong-theorem attributions. This was a development diagnosis, not final-tree
  evidence.
- `lake build
  RMQ.Core.SuccinctClose.EndpointFringe.InteriorCandidate.InteriorDirectory`:
  exit 0 in 353.3s after the fresh worktree lacked module artifacts. The live
  child was inspected while quiet and was advancing through prerequisites; no
  duplicate was launched. This is cache warm-up only, not acceptance evidence.
- A read-only theorem audit found a plausible exact reachable witness for the
  missing tightness proof: the right-spine shape of size `3469`, list query
  `[1704,3469)`, and accepted interior `(startBlock,count)=(143,146)`, which
  dispatches to cross-macro parameters `(0,143,1,1)`. The proposed proof must
  still be kernel checked on the canonical store-backed structural trace before
  it can evidence `cost = 33` and `not (cost <= 30)`.
- A read-only gate audit reproduced 66 committed-range whitespace failures, all
  in `docs/internal/B7_STEP2_WIP.patch`; naïve whitespace stripping corrupts
  the patch. The repair lead is to regenerate the exact
  `65c6ab3..c45e62c` nine-file artifact as a replayable zero-context diff and
  validate it in an exact scratch tree, or truthfully retire it.
- `scripts/wordram_axiom_check.lean:197` names the removed
  `...nonSyntheticWeight_sum_le_76`; the live coverage replacement is
  `...nonSyntheticWeight_sum_le_210`, while the generic principled theorem at
  line 196 remains.
- The current 21-window cost harness has no exact stable-ID registry or focused
  selector. Its empty recursive base returns true, so an eventual filtered
  zero-case selection would pass vacuously unless validation is added.

## Stop disposition

Status is BLOCKED on write-scope authority, not on proof difficulty or a failed
semantic target. The branch remains a clean checkpoint containing only the
pre-implementation contract freeze and this durable stop record. No original
B7 row or B7-R1 row is claimed complete, no coordinator acceptance is claimed,
and no roadmap closure is claimed.

# B7-R2 repair session: governed re-entry and frozen continuation

## Checkout and governance

- Worker: B7-R2.
- Requested title: `(B7-R2) Complete the charged sparse-level repair on the closed surface set`.
- Worktree: `C:\Users\poin\.codex\worktrees\25b6\RMQ`.
- Exact base: `e23875542995ca31404567cba5b128c9271e861a`.
- Branch: `codex/b7-charged-sparse-level-r2`.
- Ordered base parents: B7-R1 checkpoint
  `24a166c5959aa1cac52be6d0aeefb3e2811f056c`, then governance
  `5fc02e5a8960c4cc5bacba4daa58cc8f4bd8a91f`.
- `scripts/project_skill_preflight.ps1` with required `rmq-proof-sprint` and
  runtime RMQ skills `rmq-audit-prompt`, `rmq-coordinator`,
  `rmq-proof-sprint`: exit 0 in 9.9s.

The B7-R1 frozen acceptance wording and IDs were reread in full before any
implementation edit.  The B7-R2 continuation note in the matrix records the
same hard target, the independent tightness and value-dependency challenges,
the unchanged stretch deferral, and the verification/deadline discipline.
The repaired 18-path write scope removes B7-R1's only external blocker.

## Parallelization and ownership

The concrete join target is the exact-cost-33 canonical interior execution.
Three independent read-only inventories ran in parallel: the concrete witness
and consumer chain; the historical-328/trust/current-surface chain; and the
21-window replay registry.  B7-R2 retains sole ownership of all source edits,
shared evidence records, public theorem signatures, verification, and commits.
No worker writes were merged or copied as proof evidence.

## B7-R2 stop: historical-identity repair needs four unauthorized consumers

After the exact-cost source and accepted-consumer checkpoint kernel-checked,
the historical-name dependency inventory found that the frozen
`REQ-B7R1-HISTORICAL-328-IDENTITY` migration cannot be completed inside the
declared path set. The direct required paths are
`RMQ/Core/SuccinctFinalStoreParam.lean`,
`RMQ/Core/SuccinctFinalModelAdequacy.lean`,
`RMQ/Headlines/RMQCompatibility.lean`, and
`RMQ/Validation/SuccinctClassic.lean`. In particular, the compatibility
headline currently gives `Compatibility328` names to the live expression
whose checked value is `352`. Leaving that surface unchanged would be the
forbidden historical-name drift; changing only `SuccinctRMQClassic.lean`
would not close the row.

Per the checkout contract, no unauthorized path was edited. The worktree is
therefore a partial, uncommitted checkpoint and not a candidate. Required
coordinator choice: expand write scope to the four named paths (recommended),
or amend the frozen requirement. No frozen requirement was weakened here.

# B7-R3 governed re-entry and contract freeze

- Handle/title: `B7-R3`, `(B7-R3) Finish the charged sparse-level repair with closed consumers`.
- Branch/worktree: `codex/b7-charged-sparse-level-r3` at
  `C:\\Users\\poin\\Documents\\RMQ\\.worktrees\\b7-charged-sparse-level-r3`.
- Exact base: `14e38031a541bcaa2df8d67976078c76dbae975a`.
- Ordered parents verified before editing: implementation checkpoint
  `16645c60792954b84ad588b56f5b56da720847df`, then governance
  `986e8066f9b93f6576edd20e6d25e363eb029fa1`.
- `scripts/project_skill_preflight.ps1` passed with required
  `rmq-proof-sprint` and runtime RMQ catalog
  `rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint` before substantive work.
- The full completion gate, original B7 matrix, B7-R1/R2 continuations,
  relevant decision records, source definitions, and enumerated direct
  consumers were reread. Checkpoint prose remains untrusted; theorem types and
  consumer composition will be reconstructed on the final tree.

The R3 matrix continuation freezes the unchanged acceptance IDs, exact
same-object `33` versus rejected `<= 30` challenge, independent value
corruption challenge, literal historical `328` versus distinctly named live
`352` split, exact 21-entry replay registry/selector obligations, and final
command ledger. The newly authorized four Lean consumers remove R2's only
scope blocker. No implementation or roadmap acceptance is claimed by this
entry.

# B7-R3 implementation and candidate reconstruction

## Closed-consumer historical/live split

The historical name is literal-pinned again:

```lean
RMQ.SuccinctClassic.canonicalTransitionalQueryCost_eq :
  RMQ.SuccinctClassic.canonicalTransitionalQueryCost = 328
```

The current raw-expression compatibility value is a different object and a
different proposition:

```lean
RMQ.SuccinctClassic.liveCompatibilityQueryCost_eq :
  RMQ.SuccinctClassic.liveCompatibilityQueryCost = 352
```

The source, store-parametric, model-adequacy, classic, headline,
validation, example, WordRAM-inventory, topology, WIP-artifact, and paper
consumers were searched from the five frozen symbols and migrated explicitly.
`Compatibility328` declarations now conclude against the literal historical
`328`; the live raw expression is exposed only through `Compatibility352`
declarations. `scripts/axiom_check.lean` remains byte-for-byte outside the R3
diff and was not run.

## Exact replay registry

`RMQ/Validation/SuccinctClassicCostHarness.lean` now has one typed ordered
`List ReplayCase`. Each entry contains its stable ID, fixture, half-open window,
independently computed List answer, canonical route, pre-repair cost,
post-repair cost, and disposition. A separate literal expected-ID list pins all
21 IDs and their order; structure validation checks exact length, exact ordered
IDs, `Nodup`, and the exact pre-repair vector before executing a query. Default
mode executes the registry itself. `--case` requires one exact match;
`--fixture` rejects zero matches. The harness contains no process-launch API.

## Returned-value dependency gap found and repaired

Reconstructing `INV-VALUE-DEPENDENCY` from source exposed a real missing
theorem: the charged level read was proved to refine the logical computation,
but no same-query store corruption theorem concluded inequality of the returned
interior candidate. The exact-cost witness cannot substitute for that row, so
R3 added the independent theorem
`canonicalRelativeRmmInteriorCost33LocalLevelDrop_changes_returned_candidate`.
Its checked proposition uses the canonical size-3469 shape and the identical
valid interior query `(startBlock,count)=(0,1)` on both sides. It concludes,
side by side:

```lean
(address, canonicalStore address) ∈ canonicalRun.reads ∧
(address, none) ∈ droppedRun.reads ∧
canonicalRun.value =
  some (bpRangeMinExcess shape layout.blockSize 0 1,
        bpRangeArgMinPrefixPos shape layout.blockSize 0 1) ∧
droppedRun.value = none ∧
canonicalRun.value ≠ droppedRun.value
```

`droppedStore` differs from the canonical flat component store only at
`offsets.localLevel + 1`, the one-word physical footprint of local charged
level cell `1` on this witness (`level width = 11`, reviewer word size `= 13`,
chunk count `= 1`). The proof unfolds the real
`canonicalRelativeRmmInteriorRangeMinComputation` dispatcher, records that
exact address in both executions, uses
`canonicalRelativeRmmInteriorRangeMinCostedWithStore_erase_exact` for the
accepted value, and proves that decoding the dropped first word returns
`none`. The theorem was added to `scripts/wordram_axiom_check.lean`; semantic
coverage was extended rather than deleted.

Development evidence on the stabilized Lean source:

- `lake env lean RMQ/Core/SuccinctClose/EndpointFringe/InteriorCandidate/InteriorDirectory.lean`:
  exit 0 in 33.3s;
- `lake build RMQ.Core.SuccinctClose.EndpointFringe.InteriorCandidate.InteriorDirectory`:
  exit 0 in 37.0s, `59/59`;
- `lake env lean scripts/wordram_axiom_check.lean`: exit 0 in 103.6s with
  the new returned-value theorem, exact-cost chain, historical `328`, live
  `352`, current `210`, and public strong read-only names all retained.

No new design decision was needed for this theorem: its store, query object,
and accepted/rejected predicates are dictated verbatim by the frozen
`INV-VALUE-DEPENDENCY` row. DD-20260719-002 records the historical/live split;
DD-20260719-003 records the exact registry. WDD-20260719-008 records the
selector/deadline process policy.

## Replay deadline incident and owned cleanup

The first post-repair four-control shell used a positive 20-minute deadline.
It timed out after 1204.1s while the default traversal was still responsive.
Inspection, before any retry, found the owned tree
`4312 (elan lake) -> 14948 (toolchain lake) -> 4688 (harness)` and three
unrelated `lake build RMQ` jobs that had started later in other worktrees and
were simultaneously running four large Lean children. The harness CPU counter
had advanced to 695.6s and `Responding=True`, so the failure was classified as
external CPU contention, not a semantic verdict or deadlock. Only the owned
PIDs `4688`, `14948`, and `4312` were stopped; the unrelated worktrees were not
touched. Survivor inspection then returned no owned process, and
`git status --short` showed exactly the pre-existing intended R3 paths with no
scratch or generated source artifact. An unchanged retry is forbidden until
the external heavy jobs have exited; the next replay uses the same executable
only after that observable external-state change.

## Proof digestion

1. **Conceptual change.** History and live compatibility are now two stable
   cost objects, the replay fixture set is one executable exact registry, and
   the charged sparse-level word has an explicit returned-value corruption
   witness.
2. **Plain-English meaning.** The old route really cost 328, the current raw
   compatibility expression really costs 352, all current public statements
   say which one they mean, and the level-table read is indispensable data:
   removing the word the evaluator actually asks for changes the answer it
   returns.
3. **Live assumptions.** The reference semantics remain guarded half-open
   leftmost RMQ over `List Int`; cost counts modeled trace events rather than
   Lean runtime; the canonical component store is the counted payload object;
   and the public upper-bound story is `2*n + overhead n` with
   `LittleOLinear overhead` under the existing explicit indexed-access model.
4. **Strongest skeptical graduate-student question.** The new witness proves
   one charged level word is decisive and the exact-cost witness proves the
   current cap is attained, but can the next rung mechanize a complete
   reachability inventory showing that every remaining uncharged operation is
   either a checked representation bridge or a genuinely constant-time RAM
   primitive? That is precisely the still-deferred `STRETCH-01`, not a claim
   made by this rung.
