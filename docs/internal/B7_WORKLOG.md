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
