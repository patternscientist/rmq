# E1 LIVE STATE

**Read this instead of `E1_WORKLOG.md`.** The worklog is a 7,500-line
append-only archive of 24 sessions; reading it whole was costing every session a
large fraction of its budget. Consult it only for a NAMED section.

Maintained by coordinator C05. Every anchor below was grep-verified at the
commit named. If you find one wrong, say so in your report — coordinator
addressing claims have failed inspection nine times this campaign and every
catch has come from a worker.

---

## 1. Where things stand

Campaign branch `claude/b1-b2-charged-fringe-tables`. **Get the head with
`git log --oneline -1`, not from this line.** A file that records its own
branch's HEAD can never name the commit that updates the file, so any hash
written here is stale by construction — it has already been wrong twice.

**ALL FIVE BRANCHES ARE MERGED. There is no unmerged sibling lane left**
(E1-LaneM). The campaign branch now carries, in ONE TREE:

- the **interior leg** — `#1`–`#9` built, the five-branch composition
  (`interiorDispatchBlock_runsTo`), `hInterior` discharged
  (`interiorDispatch_hInterior`) AND consumed
  (`crossBlockArm_withCanonicalInterior_runsTo`);
- the **interior preservation discriminator**, executed — validator phases
  3i and 4h (from `claude/e1-interior-preservation`, DD-20260719-030..034);
- the **close leg** — `hc` discharged, the nine window premises REMOVED,
  the cross-arm terminator, `CloseLegUntouched` (from
  `claude/e1-close-leg-structural`, DD-20260719-070..073);
- the **whole-query glue foundations** — `guard_accept_of_valid`, the
  strengthened guard bridge, the object reconciliations, the route
  case-split, `wholeQueryBranchCats` (from `claude/e1-glue-foundations`,
  DD-20260719-090..092);
- the `design_decision_check` `RMQ/Validation` coverage fix and
  `WDD-20260719-002` (from `claude/dd-check-validation-coverage`).

The merge required ONE semantic repair that no textual tool reported: the
close leg's signature change to `crossBlockArmProgramAt_runsTo` versus the
campaign branch's application of it, in two different files with no
conflict. See the §3 subsection on that signature and DD-20260719-110.

**What is still missing for whole-query is the whole-query PROGRAM
ITSELF** — no definition composes the close legs and the interior into one
runnable query program, and no `wholeQueryProgram` exists in the tree.
Validator phase 5 remains OPEN and states this correctly.

**All eleven rows of `E1_AMENDED_MACHINE_ACCEPTANCE_MATRIX.md` are Open.**

**CORRECTION — an earlier version of this file said "they are whole-query scoped
by deliberate design, so no interior-leg component can close one." THAT WAS
FALSE, and it was mine, not the matrix's.** The matrix's own `Scope` column
reads: `01` Local, `02` Local, `03` Local+roadmap, `04` Local+roadmap, `05`
**Local**, `06` Local, `07` Local+roadmap, `08` Local, `09` Public surface, `10`
Process, `11` Inherited hygiene + process. Nothing says whole-query. Workers
have been annotating rows "Does NOT discharge the row (whole-query scope)" — a
phrase that appears nowhere in the matrix, because I put it in their briefs.

**Read each row's own `Evidence needed` column and judge against THAT.** Under
`COMPLETION_GATE.md` §1 that column is the operative acceptance test: "the exact
proposition or check result that would entail the requirement." Three rows are
at or near closable on evidence that already exists:

- **REQ-E1-01** — every item in its Evidence-needed column and its whole
  anti-vacuity challenge exist in `E1Machine.lean` plus DD-20260718-005. Its only
  residual is the *Named consumer* column, which points at the REQ-E1-07 Prop
  that does not yet exist.
- **REQ-E1-05** — everything exists except the five words "and in the
  validator". One validator phase running `programSkeleton` on the
  empty/reversed/out-of-bounds fixtures closes it, and it is **independent of the
  interior leg**: `programSkeleton_invalid_matches_public_guard`
  (`E1QueryBridge.lean:55`) is universally quantified over `validPath`.
- **REQ-E1-10** — matrix-first ordering verified by git ancestry (`702cfbe` is an
  ancestor of `11b8cf9`); DD coverage present.

Still true and still binding: **do not weaken a row to make it closable**, and
do not edit frozen requirement text — append a NOTE, as M3d-11/-12/-13/-16/-17
did.

## 2. The interior leg's ACTUAL structure

Mapped by reading `InteriorDirectory.lean:2300-2468` (the file is under
`SuccinctClose/EndpointFringe/InteriorCandidate/`). Earlier coordinator ladders
under-counted this — there are **three macro combiners** between the two-span
blocks and the dispatch that were never enumerated.

| # | Route computation | Line | Reads? | Machine side |
|---|---|---|---|---|
| 1 | `...MinCandidateComputation` | 2300 | 4 (via summary group) | **DONE** |
| 2 | `...LocalSpanCandidateComputation` | 2311 | 1, then `some`→#1 / `none`→pure | **DONE** |
| 3 | `...GlobalSpanCandidateComputation` | 2329 | 1, then `some`→#1 / `none`→pure | **DONE** |
| 4 | `...LocalTwoSpanCandidateComputation` | 2351 | 1, then level/span split, two #2 merged | **DONE** |
| 5 | `...GlobalTwoSpanCandidateComputation` | 2376 | 1, then two #3 merged | **DONE** |
| 6 | `...AdjacentMacroCandidateComputation` | 2400 | **none** — two #4, merged | **DONE** |
| 7 | `...LeftMiddleMacroCandidateComputation` | 2413 | **none** — #4 + #5, merged | **DONE** |
| 8 | `...CrossMacroCandidateComputation` | 2426 | **none** — #4 + #5 + #4, TWO two-way merges | **DONE** |
| 9 | `...InteriorRangeMinComputation` | 2444 | **none** — 5-way dispatch | **DONE** |

**THE INTERIOR LEG IS COMPLETE** (E1-LaneB6). All nine rows are built and
`hInterior` is discharged.

**#9's STATE, precisely.** The 4204-instruction program
(`interiorDispatchBlock`, `E1InteriorDispatch.lean:251`), its
28-instruction prologue in four read-free pieces, the five
`dispatchSelector_reaches_arm*` lemmas and the route decomposition
`interiorRangeMin_of_*` were built by E1-LaneB5. **E1-LaneB6 added the
composition** — `interiorDispatchBlock_runsTo`
(`E1InteriorDispatchCompose.lean:816`), one simulation from `Q` to
`Q + 4204` carrying receipt, category log, value and preservation on all
five branches — **and `hInterior`**
(`interiorDispatch_hInterior`, `:1171`), which is not merely
premise-SHAPED but is CONSUMED by `crossBlockArmProgramAt_runsTo` in
`crossBlockArm_withCanonicalInterior_runsTo` (`:1274`). Nothing in
`E1CrossBlockArm.lean` was edited.

~~**What is NOT built is the composition of the five arms into one
`interiorDispatchBlock_runsTo`**, and therefore `hInterior` is not
discharged.~~ **SUPERSEDED (E1-LaneB6)** — both now exist. Left struck
through rather than deleted, per the standing rule.

**NAME CORRECTION (E1-LaneB4), checked by grep across `RMQ/`.** Row 9's
identifier is `canonicalRelativeRmmInteriorRangeMinComputation` — there is
**no `Machine`** in it, unlike rows 1–8.
`canonicalRelativeRmmMachineInteriorRangeMinComputation` does not exist;
16 hits, all the non-`Machine` spelling. The `...` in this table hides the
difference, so anyone expanding row 9's name from the pattern of rows 1–8
will grep for a constant that is not there.

**#8 IS NOT A THIRD PRIMITIVE.** `bpCandidateMerge3?` (`Candidate.lean:24`)
is DEFINITIONALLY `bpCandidateMerge? (bpCandidateMerge? left middle) right`,
so #8 is the two-way merge block run twice and the reassociation is `rfl`.
Checked, not asserted: `merge3_eq_two_merges` (`E1InteriorMerge.lean:593`).
The earlier "merge3" label in this table read as a third block owed. It is
not one. Chaining does need a two-instruction shuttle, which exists
(`mergeShuttle`, `:604`), because the merge writes IN PLACE.

**There are only THREE structural patterns here, instantiated seven times.**
#2/#3 are the same block modulo table and slot. #4/#5 are the same block modulo
which span block they call. #6/#7/#8 are read-free merge combiners over
sub-legs. Building each pattern PARAMETRICALLY and instantiating it is the
difference between one session and three — and parametric statements are also
what makes them kernel-executable (see §4).

**#2 AND #3 ARE DONE** (M3d-25 built the pattern, M3d-27 instantiated it).
The parametric-pattern claim HELD: one `spanBlock`, parametric in a
`TableGeom`, covers both, because the two block-index maps
(`macroIdx * macroSize + value` and `value`) are both `off + value` for a
caller-supplied `off`. The two geometries are `localSpanGeom`
(`E1InteriorSpanBlock.lean:630`) and `globalSpanGeom` (`:642`), and the
route-value links are `spanValue_localSpan_eq_routeValue` (`:773`) and
`spanValue_globalSpan_eq_routeValue` (`:808`), with NO validity, cap or
store hypothesis surviving.

**CITATION CORRECTION, made by the worker who used this file.** The two
bridge lemmas were cited here as `E1InteriorChunkStore.lean:674` and `:904`.
The LINE NUMBERS were right; the FILE was wrong. `geomCell_eq_routeDecode`
(`:674`), `geomCell_eq_routeDecode_of_invalid` (`:717`), the four summary
bridges (`:737`–`:800`) and `geomRouteDecode_eq_readComputation_value`
(`:904`) are all in **`E1InteriorSummaryGroup.lean`**, which is 1185 lines;
`E1InteriorChunkStore.lean` is 619, so the citation was refutable by `wc`
alone. `hexact_local`/`hexact_global` ARE in `E1InteriorChunkStore.lean`
(`:514`/`:537`), which is probably how the two got conflated.

The recipe that worked, for #4/#5 to copy: define every `TableGeom` field
as the ROUTE's own quantity. Then all three hypotheses of
`geomRouteDecode_eq_readComputation_value` are `rfl`, and `hvalid` and
`hentries` become the SAME proposition so one validity split discharges
both. The two missing concrete store clauses were one line each
(`hexact_local_concrete`, `E1InteriorStoreConcrete.lean:232`;
`hexact_global_concrete`, `:252`). DD-20260719-051.

Caps for both are already proved: `chunkCount_{pos,le_eight}_offsetWidth` and
`..._blockAddressWidth` (`E1InteriorChunkCap.lean:138`,`:146`,`:206`,`:212`).
The level-table caps #4/#5 will need are there too (`:155`,`:165`,`:218`,`:232`).

**CORRECTION TO THIS FILE'S OWN §3, made by the worker who used it.**
`candMerge3` is **not** reusable for #8. `bpCandidateMerge3?_some_left_right`
(`E1CandMerge3.lean:139`) takes `left right : Nat × Nat` — BARE PAIRS, not
options — so the block assumes the left and right arms are OCCUPIED, which is
the fringe's situation and not the interior's, where all three sub-legs are
`Option`.

~~Its epilogue also writes `fRes = mAP - 1`, the `bpCandidateClose?` CLOSED
POSITION, whereas #6/#7/#8 need the merged CANDIDATE left in the bank.~~
**SUPERSEDED (M3d-27), and the correction matters because it misstates the
reason.** `candMerge3Close` (`E1CandMerge3.lean:190`) is ADDITIVE: two
separable instructions, and `candMerge3_runsTo` (`:718`) already exports
`bestOfRegs (regs' mAV) (regs' mAP)` holding the merged candidate ALONGSIDE
the `fRes` clause. The candidate IS left in the bank. The real second
obstacle is narrower: the `fRes` (69) write itself, `fRes` being the shared
dispatch output register, which a combiner running mid-leg must not touch.
Left as struck-through rather than deleted, per the standing rule.

**THE TWO-WAY MERGE BLOCK NOW EXISTS** — `E1InteriorMerge.lean`, new this
session. 9 instructions, all four option combinations, read-free, result
written IN PLACE to `mMV`/`mMP` so every interior producer lands in one
pair. #4, #5, #6, #7 and #8 can all call it. DD-20260719-052.

**#4 AND #5 ARE DONE** (M3d-28). One parametric `twoSpanBlock`
(`E1InteriorTwoSpan.lean:186`) covers both, 509 instructions, exit
`Q + 509` on both arms. The parametric-pattern claim held a second time,
though for a slightly different reason than this file gave: #4/#5 differ
not only in "which span block they call" but ALSO in the SLOT MAP — and
both maps are `A + level * M + start` for a caller-supplied `A` and a
program constant `M` (local: `A = macroIdx * (levelCount * macroSize)`,
`M = macroSize`; global: `A = 0`, `M = macroSampleCount`). That is what
makes one block cover both.

**#9's five branches**, read off the source: `count = 0` → `pure none`;
`count ≤ macroSize - localStart` → #4; `middleMacroCount = 0` → #6;
`rightCount = 0` → #7; else → #8.

## 3. Landed machinery you should USE, not rebuild

| Fact | Anchor |
|---|---|
| composed 177-instruction interior leg | `summaryMinCandidate_runsTo` — `E1InteriorMinCandidate.lean:963` |
| its receipt = the route's read log | `summaryMachineTrace_eq_routeReads` — `:1237` |
| min-candidate receipt | `minCandidateMachineTrace_eq_routeReads` — `:1296` |
| summary group, all 8 premises supplied | `canonicalSummaryGroup_runsTo` — `E1InteriorSummaryGroup.lean:555` |
| machine cell = route computation value | `routeDecode_eq_machineReadComputation_value` — `:879` |
| block lengths (177 = 156 + 21) | `summaryGroup_length` `:299`, `minCandidateBlock_length` `E1InteriorMinCandidate.lean:241` |
| read-free 3-way merge — **fringe-shaped, see §2 correction** | `candMerge3` — `E1CandMerge3.lean:198`, `candMerge3_readFree` `:206` |
| merge algebra | `bpCandidateMerge?_some_left` `:132`, `bpCandidateMerge3?_some_left_right` `:139` |
| cross-block arm — **SIGNATURE CHANGED, see below** | `crossBlockArmProgramAt_runsTo` — `E1CrossBlockArm.lean:1181` |
| interior fold preservation clause — **COMPOSED HEADLINE** | `interiorChunkFold_runsTo` `E1InteriorChunkFold.lean:1808`, clause at `:1835` |
| **the #2/#3 span block, both arms** | `spanBlock_runsTo` — `E1InteriorSpanBlock.lean:262` |
| **its `none`-arm discriminator** | `spanNoneArm_discriminates` — `E1InteriorSpanBlock.lean:540` |
| **177-leg preservation, now exported** | `LegUntouched` `E1InteriorMinCandidate.lean:934`, clause at `:1009` |
| **`hexact` at the two span tables** | `hexact_local` `E1InteriorChunkStore.lean:514`, `hexact_global` `:537` |
| **#2/#3's two geometries** | `localSpanGeom` `E1InteriorSpanBlock.lean:630`, `globalSpanGeom` `:642` |
| **#2/#3's route-value links** | `spanValue_localSpan_eq_routeValue` `:773`, `..._globalSpan_...` `:808` |
| their cell bridges, unconditional | `geomCell_localSpan_eq_routeDecode` `:667`, `..._globalSpan_...` `:683` |
| the `cellOpt` forms the value dispatches on | `cellOpt_spanCell_localSpan` `:702`, `..._globalSpan` `:718` |
| the `some` arm's target, route-side | `legValue_eq_minCandidateComputation_value` `:740` |
| span tables' concrete `hexact` | `hexact_local_concrete` `E1InteriorStoreConcrete.lean:232`, `_global_` `:252` |
| **THE TWO-WAY MERGE, all four arms** | `mergeBlock_runsTo` — `E1InteriorMerge.lean:178` (block at `:100`) |
| its charge log, as a route function | `mergeCats` — `E1InteriorMerge.lean:125` |
| its preservation, DECIDED at the four operands | `mergeUntouched_at_crossBlockArm_operands` — `:157` |
| **its paired discriminators** | `mergeTie_discriminates` `:455`, `mergePos_discriminates` `:501` |
| **the category-log boundary, both sides** | `mergeTie_catLogs_differ` `:471`, `mergePos_catLogs_agree` `:519` |
| **#8 is two two-way merges, not a primitive** | `merge3_eq_two_merges` — `E1InteriorMerge.lean:593` |
| the chaining shuttle — **ONE LEVEL DOWN ONLY, see §6** | `mergeShuttle` `:604`, `mergeShuttle_runsTo` `:624` |
| **the #4/#5 two-span block, both arms** | `twoSpanBlock_runsTo` — `E1InteriorTwoSpan.lean:355` (block at `:185`, 509 instrs) |
| **#4 and #5 instantiated** | `twoSpanValue_local_eq_routeValue` `E1InteriorTwoSpan.lean:1085`, `..._global_...` `:1123` |
| **#4/#5's two level geometries** | `localLevelGeom` `E1InteriorTwoSpan.lean:885`, `globalLevelGeom` `:898` |
| their cell bridges, unconditional | `geomCell_localLevel_eq_routeDecode` `:936`, `..._globalLevel_...` `:952` |
| **the level tables' `hexact`** (did NOT exist before M3d-28) | `hexact_localLevel` `E1InteriorChunkStore.lean:580`, `hexact_globalLevel` `:601` |
| their concrete twins | `hexact_localLevel_concrete` `E1InteriorStoreConcrete.lean:280`, `_globalLevel_` `:298` |
| **the two-span block's IMPOSTOR PAIR** | `twoSpanNoneArm_discriminates` `E1InteriorTwoSpan.lean:1251` |
| **the RECEIPT boundary, both sides** | `..._receipt_catches_impostorA` `:1258`, `..._receipt_blind_to_impostorB` `:1266` |
| **the write set is below `136`** | `twoSpanUntouched_of_ge` — `E1InteriorTwoSpan.lean:303` |
| **the two-span block CLOBBERS `qLV`/`qLP`** | `twoSpanUntouched_excludes_mergeStash` — `:331` |
| one two-span leg's four-input setup | `legSetup_runsTo` — `E1InteriorCombine.lean:168` (setup at `:135`) |
| **`#6`/`#7`'s block, BOTH LEGS** | `twoLegBlock_runsTo` — `E1InteriorCombine.lean:434` (block at `:265`, 1044 instrs) |
| **`#6` and `#7` instantiated** | `twoLegValue_adjacentMacro_eq_routeValue` `E1InteriorCombine.lean:801`, `..._leftMiddleMacro_...` `:837` |
| their second-leg source witnesses | `adjacentMacro_src_witnesses` `:886`, `leftMiddleMacro_src_witnesses` `:900` |
| **`#8`'s block, all three legs** | `crossLegBlock_runsTo` — `E1InteriorCombine.lean:1011` (block at `:944`, 1574 instrs) |
| **`#8` instantiated** | `crossLegValue_crossMacro_eq_routeValue` — `E1InteriorCombine.lean:1332` |
| the combiner write-set ladder | `twoLegUntouched_of_ge` (<`144`) `:374`, `twoLegUntouched_of_bank` `:390`, `crossLegUntouched_of_ge` (<`146`) `:997` |
| **the combiner preservation predicates** | `TwoLegUntouched` `:333` (SUPERSEDED form, see §6), `CrossLegUntouched` `:983` |
| four route branch decompositions | `E1RouteDecomposition.lean:41`, `:85`, `:121`, `:148` |
| **#9's program, 4204 instrs** | `interiorDispatchBlock` — `E1InteriorDispatch.lean:251` |
| its four prologue simulations | `rangePreamble_runsTo` `E1InteriorDispatch.lean:578`, `indexDecomp_runsTo` `:706`, `localArmSetup_runsTo` `:898`, and the selector below |
| **the five arm-reachability lemmas** | `dispatchSelector_reaches_arm0` `E1InteriorDispatch.lean:1002`, `_arm4` `:1030`, `_arm6` `:1067`, `_arm7` `:1124`, `_arm8` `:1189` |
| **THE FALL-THROUGH DISCRIMINATOR** | `unterminatedDispatch_falls_through` — `E1InteriorDispatch.lean:1410` |
| its correct twin, and the boundary | `witnessDispatch_runs_none` `:1358`, `unterminatedDispatch_receipts_agree` `:1499`, `..._catLogs_differ` `:1511` |
| **#9's preservation, checked against its OWN writes** | `DispatchUntouched` `E1InteriorDispatch.lean:335`, `dispatchUntouched_of_lt` `:380` |
| **the close leg's clause, as a SEPARATE export** | `dispatchUntouched_of_closeLegUntouched` — `E1InteriorDispatch.lean:427` |
| the route's five branches, machine-free | `interiorRangeMin_of_count_zero` `E1InteriorDispatch.lean:447`, `_of_local` `:455`, `_of_adjacent` `:468`, `_of_leftMiddle` `:486`, `_of_cross` `:507` |
| the caller's guard is subsumed | `interiorRangeMin_guard_subsumed` — `E1InteriorDispatch.lean:544` |
| **`#9`'s FIVE ARMS COMPOSED — the interior leg's top** | `interiorDispatchBlock_runsTo` — `E1InteriorDispatchCompose.lean:816` |
| **`hInterior`, DISCHARGED** | `interiorDispatch_hInterior` — `E1InteriorDispatchCompose.lean:1171` |
| **and CONSUMED, which is what proves it fits** | `crossBlockArm_withCanonicalInterior_runsTo` — `:1274` |
| the close leg's clause, as a SEPARATE export | `interiorDispatch_preserves_closeLeg` — `:1223` |
| `#9`'s receipt and charge log, written FROM THE ROUTE | `dispatchEvents` `:194`, `dispatchCats` `:374`, `dispatchArmCats` `:264` |
| the route's answer, named once | `dispatchRouteValue` — `:381` |
| the block at the canonical geometries | `canonicalInteriorDispatchBlock` `:89`, length `:103` |
| its ten-way hosting peel | `canonicalInteriorDispatchBlock_hosts` — `:396` |
| the branch-independent 19-category prologue | `dispatchPrologue_runsTo` `:701`, `dispatchPrologueCats` `:251` |
| **route block size = sub-block block size, KERNEL-CHECKED** | `canonicalBlockSize_eq_layoutBlockSize` — `:1151` |
| the two span geometries' positivity | `localSpanGeom_pos` `:670`, `globalSpanGeom_pos` `:674` |
| **THE MIS-DISPATCH DISCRIMINATOR** | `missDispatch_runs_armA` `:1431`, `missDispatchImpostor_runs_armB` `:1502` |
| its boundary, all four sides | `..._exit_and_halt_agree` `:1574`, `..._catLogs_agree` `:1581`, `..._receipts_differ` `:1596`, `..._values_differ` `:1604` |
| close/LCA dispatch, both arms | `closeDispatch_runsTo_same` / `_cross` — `E1CloseDispatch.lean:187`/`:224` |
| same-block leg composed | `sameBlockDispatchProgram_runsTo` — `E1CloseCompose.lean:95` |

**Register allocation.** Merge bank `75..84`. Interior fold bank `89..99`.
Summary+min-candidate `105..117`. Span block `118..122` (`pSlot` 118 and
`pOff` 119 are INPUTS the caller writes; `pCell` 120, `pT` 121, `pOne` 122 are
scratch). Two-way merge `123..126` (`qLV` 123 and `qLP` 124 are the INPUT
stashed left candidate; `qT` 125 and `qOne` 126 are scratch).
Two-span block `127..135` (`tA` 127, `tStart` 128, `tN` 129, `tOff` 130 are
INPUTS; `tCell` 131, `tLvl` 132, `tRS` 133, `tT` 134, `tOne` 135 scratch).
Combiner `136..143` (`uMacro` 136, `uLocal` 137, `uMid` 138, `uRight` 139 are
INPUTS; `uT` 140, `uZero` 141 scratch; `uSV` 142, `uSP` 143 the combiner's
OWN stash pair — see §6).
Three-leg combiner `144..145` (`vSV` 144, `vSP` 145, the THIRD stash pair).
Dispatch bank `146..151` (`wOne` 146 the unconditional-branch condition,
`wT` 147 scratch, `wStart` 148, `wCount` 149, `wRem` 150, `wLeft` 151).
**Next free block opens at `152`.**

**`wOne` AT `146` IS LOAD-BEARING, NOT ARBITRARY.** There is no
unconditional jump in the ISA, so every arm's terminator is
`brNZ wOne <join>` — a register set before the arm and read after up to
1574 instructions have run. `crossLegUntouched_of_ge` puts the whole
three-leg write set below `146`, which is exactly what keeps `wOne`
nonzero at the branch. **A dispatch bank opening anywhere below `146`
would let an arm clear its own terminator's condition, turning the branch
into a silent fall-through** — the DD-20260719-059 defect reintroduced
through the register file instead of the layout. DD-20260719-060.

**THE STASH-PAIR LADDER, which determines where the next bank goes.** Each
combiner WRITES the stash pair of the level below it, because that pair is
where its own sub-block leaves its answer: `twoSpanBlock` writes
`qLV`/`qLP`, so `twoLegBlock` needs `uSV`/`uSP`; `twoLegBlock` writes
`uSV`/`uSP`, so `crossLegBlock` needs `vSV`/`vSP`. **`#9` must allocate a
fresh pair at `146`+ if it stashes across a dispatch arm, and must not
reuse `vSV`/`vSP`.** DD-20260719-058.

The three `of_ge` lemmas are the ladder's cheap form —
`twoSpanUntouched_of_ge` (<`136`), `twoLegUntouched_of_ge` (<`144`),
`crossLegUntouched_of_ge` (<`146`). Use the matching one rather than
re-deciding a dozen conjuncts. Note `twoLegUntouched_of_ge` does NOT reach
the INPUT registers `136..139`, which sit below the block's own scratch;
`twoLegUntouched_of_bank` is the form for those.

`twoSpanUntouched_of_ge` (`E1InteriorTwoSpan.lean:303`) proves the two-span
block's whole write set lies below `136`, so a combiner can carry its bank
across a sub-leg without re-deciding ten conjuncts. Use it.

### 3a. PROGRAM GEOMETRY FOR `#9`'s DISPATCH — read this before laying it out

Assembled by E1-LaneB4 at the coordinator's request, because `#9` cannot be
laid out without it and it is expensive to re-derive.

| Block | Length | Entry PC | Exit PC | Terminates? |
|---|---|---|---|---|
| 177-leg `summaryMinCandidate` | 177 | `A` | `A + 177` | **FALLS THROUGH** |
| `spanBlock` (#2/#3) | 222 | `Q` | `Q + 222` | **FALLS THROUGH** |
| `twoSpanBlock` (#4/#5) | 509 | `Q` | `Q + 509` | **FALLS THROUGH** |
| `twoLegBlock` (#6/#7) | 1044 | `Q` | `Q + 1044` | **FALLS THROUGH** |
| `crossLegBlock` (#8) | 1574 | `Q` | `Q + 1574` | **FALLS THROUGH** |
| `mergeBlock` | 9 | `Q` | `Q + 9` | **FALLS THROUGH** |
| `interiorDispatchBlock` (#9) | 4204 | `Q` | `Q + 4204` | **FALLS THROUGH — AND MUST** |

**#9 DOES NOT TERMINATE EITHER, AND THAT IS FORCED, NOT INHERITED**
(E1-LaneB5). `hInterior`'s target state is
`⟨regsI, A + 176 + interior.length, false⟩` — the halted flag is
**`false`** (`E1CrossBlockArm.lean:1181`, re-read this session). So a
`#9` that ended in `halt` could not discharge the premise at all. The
rule "every block here falls through" is, at this one block, not a
convention that could have gone the other way.

**#9's INTERNAL GEOMETRY**, for whoever composes the arms:

| Piece | Offset from `Q` | Length |
|---|---|---|
| `rangePreamble` | `0` | 6 |
| `indexDecomp` | `6` | 9 |
| `localArmSetup` | `15` | 4 |
| `dispatchSelector` | `19` | 9 |
| `#0` arm (`pure none`) | `28` | 2 |
| `#4` arm (`twoSpanBlock` + branch) | `30` | 510 |
| `#6` arm (`twoLegBlock` + branch) | `540` | 1045 |
| `#7` arm (`twoLegBlock` + branch) | `1585` | 1045 |
| `#8` arm (`crossLegBlock`, NO branch) | `2630` | 1574 |
| join | `4204` | — |

**THIS GEOMETRY IS NOW EXECUTED, NOT JUST DESIGNED** (E1-LaneB6).
`interiorDispatchBlock_runsTo` runs every one of these offsets, so the
table is checked by the elaborator rather than by reading. The three
arm-body exits `Q + 30 + 509`, `Q + 540 + 1044`, `Q + 1585 + 1044` and
`Q + 2630 + 1574` land on `Q + 539`, `Q + 1584`, `Q + 2629` and
`Q + 4204`; the first three are the terminators' PCs and the fourth is
the join.

Four arms end with `brNZ wOne (Q + 4204)`; `#8` is physically last and
exits by fall-through. **The coordinator brief's "every one of #9's five
arms needs an explicit branch" is over-stated by exactly one** — the last
arm cannot have one. `dispatchArm8_exit_is_join` states the coincidence
rather than leaving it to arithmetic. DD-20260719-059.

Note `dispatchSelector` takes the BLOCK base `Q`, not its own base: it is
hosted at `Q + 19` and its targets are written in terms of `Q`. A
`HostedAt program (Q + 19) (dispatchSelector Q)` premise is the correct
one and `HostedAt program (Q + 19) (dispatchSelector (Q + 19))` would be
satisfiable and wrong.

**NOT ONE OF THESE BLOCKS TERMINATES. THEY ALL FALL THROUGH.** Every
`runsTo` above ends in the state `⟨regs', <exit>, false⟩` — the third
component is the HALTED FLAG and it is `false` in every one. This is not
an oversight in the blocks: a `halt` instruction does exist in the ISA
(`E1Machine.lean:103`), and none of them uses it, because each is designed
to be composed.

**WHAT THE CALLER MUST PLACE AFTER THEM, and why `#9` is where this
bites.** A dispatch arm that ends at its block's exit PC continues
executing at whatever instruction sits there. So **every one of `#9`'s
five arms must end with an explicit unconditional branch to the dispatch's
join point**, or the arm falls straight into the next arm's code. That is
the cross-block-arm defect the close-leg lane found — an arm whose exit PC
landed exactly on the next block's base — restated as a design rule, and
it is the single most likely way `#9` goes wrong. The `count = 0` arm
(`pure none`) is the dangerous one: it is the shortest, so it is the arm
whose missing branch is cheapest to overlook, and a two-instruction
witness arm is precisely the shape that CANNOT exhibit the defect.

**Every one of these blocks is POSITION-DEPENDENT and takes its own base
as an argument.** `spanBlock`, `twoSpanBlock`, `mergeBlock`, `twoLegBlock`
and `crossLegBlock` all take `Q` and compute their internal branch targets
from it, so **the `Q` passed to the constructor must equal the base it is
hosted at** or the branch targets silently point elsewhere. Nothing in the
type enforces this; `HostedAt program Q (block ... Q)` is where the two are
tied together, and a `runsTo` premise written as
`HostedAt program Q (block ... Q')` with `Q ≠ Q'` would be satisfiable and
wrong. `legSetup` and `mergeShuttle` are the exceptions — no `Q`, position
independent.

**Register state on entry and exit.**

| Block | Caller must pin on entry | Leaves candidate in |
|---|---|---|
| `spanBlock` | `pSlot` 118, `pOff` 119 | `mMV`/`mMP` |
| `twoSpanBlock` | `tA` 127, `tStart` 128, `tN` 129, `tOff` 130 | `mMV`/`mMP` |
| `twoLegBlock` | `uMacro` 136, `uLocal` 137, `uMid` 138, `uRight` 139 | `mMV`/`mMP` |
| `crossLegBlock` | the same four | `mMV`/`mMP` |
| `mergeBlock` | `qLV` 123, `qLP` 124 (left); `mMV` 77, `mMP` 78 (right) | `mMV`/`mMP` |

`twoLegBlock` and `crossLegBlock` additionally need their second leg's
sources tied to values by `hS2`/`hN2` — see §10b and DD-20260719-057.
Their `runsTo` statements say what each block LEAVES ALONE but deliberately
say NOTHING about the final value of a register they write, so `#9` must
not read `uT` or `uZero` out of a finished combiner; recompute instead.

**The interior's output pair is `mMV`/`mMP` (77/78), and every interior
block must land there.** `crossBlockArmProgramAt_runsTo`'s `hInterior` reads
the answer from `bestOfRegs (regsI mMV) (regsI mMP)`, so `spanBlock`, the
177-leg and the merge block all write that pair — the merge block IN PLACE,
which is why chaining needs `mergeShuttle`. Do not introduce a second
output convention for #4–#9.

### `crossBlockArmProgramAt_runsTo` LOST SEVEN PREMISES — do not re-supply them

Landed with the close-leg merge (E1-LaneM). `crossBlockArmProgramAt_runsTo`
(`E1CrossBlockArm.lean:1181`) no longer takes `hc`, and no longer takes the
six `readBits ... .length = machineWordBits` window premises (`hL0`, `hL1`,
`hL2`, `hR0`, `hR1`, `hR2`). `hc` is discharged internally; the six window
premises were REMOVED because they are FALSE across contiguous regions of
reachable close positions — a theorem demanding them is unusable at exactly
the positions the route reaches.

Its argument order is now `shape hHost hInterior regs hClose hRight`. Code
written against the old seven-longer signature will fail with an
application type mismatch in which `hc` lands in `hHost`'s position. **The
fix is to DELETE the arguments, never to re-add the premises.**

`crossBlockArm_withCanonicalInterior_runsTo`
(`E1InteriorDispatchCompose.lean:1274`) has had the same seven binders
removed for the same reason, so it too is now
`shape hHost regs hClose hRight`. Retaining them would have obliged every
caller to prove facts that do not hold. See DD-20260719-110.

## 4. Techniques that are state of the art here

- **The kernel boundary is a property of a STATEMENT'S SHAPE, not of the
  mathematics.** `machineWordBits` → `Nat.log2` is well-founded recursion: the
  compiler evaluates it, the kernel cannot, so `rfl`/`decide` fail on
  shape-level fixtures. Parametrising `wordSize` moves the same equation into
  kernel-reachable territory with the shape-level form as an instance. Reach for
  this before concluding something cannot be witnessed.
- **An inline `match` in a statement elaborates a fresh auxiliary per
  declaration**, so an inversion lemma can be defeq to the goal and still not
  fire. Presents as "unsolved goals" on a goal `simp` visibly should close. Fix
  is to NAME the match, which is definitional, so no statement moves.
- **A whole-goal `simp` can leave two sides that print identically and do not
  close.** Localise into a per-segment bridge lemma.
- **A whnf heartbeat timeout can also mean your SIMP SET names a definition
  that unfolds into the concrete store.** §5's rule — never raise
  `maxHeartbeats` on an execution proof — is right, but the diagnosis is not
  always a stale read order. Putting `geomEvents`/`geomCats`/`geomCell` in a
  simp set forces `canonicalSummaryLayout`'s projections, hence
  `machineWordBits`, and times out. **Fix: convert into geom vocabulary ONCE, by
  defeq, with a typed `have`** — each is one delta step from the stage's own
  spelling, so the ascription is free — then never unfold it again. This is what
  made `spanBlock_runsTo` go through; see the comment at
  `E1InteriorSpanBlock.lean:335`.
- **Elaboration order bites `RunsTo.*` step lemmas.** `RunsTo.move (by simp)
  (by simpa using h.head)` can fail with the state still a metavariable. Bind
  the fetch in its own typed `have`, and pass `(s := ⟨…⟩)` explicitly.
- **Compose on the FOLD uniformly.** The 7-instruction atom
  (`interiorReadNat_route_atom`, `E1InteriorReadBlock.lean:443`) is single-chunk
  and unsound at reachable multi-chunk shapes — chunk counts are shape-dependent
  and are `(1,2,2,2)` at size 8.
- **Spell every new `TableGeom` field as the ROUTE's own quantity.** This is
  not style. It makes `geomRouteDecode_eq_readComputation_value`'s three
  hypotheses `rfl`, makes `hvalid` and `hentries` the SAME proposition (one
  `by_cases` discharges both), and lets the cap apply with no arithmetic
  between. An equivalent-but-differently-spelled geometry leaves all three as
  obligations at every call site. #2/#3's whole instantiation was ~90 lines
  because of this; expect #4/#5's level tables to behave the same way.
- **`0 + value` is NOT definitionally `value`.** `Nat.add` recurses on its
  SECOND argument, so `value + 0` reduces and `0 + value` does not. The
  global span twin needs `Nat.zero_add` substantively where the local twin
  needs nothing. Any block parametric in an additive offset will meet this at
  its zero instantiation.
- **To case-split across a route `bind`, reduce the RHS FIRST.** The
  scrutinee does not occur syntactically inside
  `((FlatStoreComputation.bind c f).run s).value`, so `cases h : …` catches
  only the machine side and the leaves will not close. `simp only
  [FlatStoreComputation.bind, FlatStoreExecution.append, h]` exposes it —
  and use `simp only`, never bare `simp`, which reaches the concrete store
  and times out (see the whnf note above). The `pure` leaf then needs a
  bare `rfl` after it.
- **Align scrutinees SYNTACTICALLY before `cases`, even when defeq.** A
  `@[simp] theorem geomBase : (someGeom shape).base = offsets.field := rfl`
  costs one line and is what lets the machine-side and route-side scrutinees
  be recognised as the same term.
- **`simp` does NOT unfold the register `abbrev`s, and `omega` collects them
  as OPAQUE ATOMS.** Both fail in ways that read as something else:
  `simp [.., RegFile.write, ..]` leaves a goal like `tT = tLvl → v / D = v`,
  and `omega` reports "a possible counterexample may satisfy `a ≥ 136` where
  `a := iIdx`". Two fixes, both cheap: for register-value chains use explicit
  `rw [hEq, RegFile.write_other _ _ (by decide)]` rather than `simp`; for
  numeric-bound lemmas write the NUMERAL (`show r ≠ 85 by omega`), which is
  accepted by defeq. `twoSpanUntouched_of_ge` is the worked example.
- **There is no modulus instruction.** The route's `v % D` becomes
  `divConst`/`mulConst`/`sub` — `v - v / D * D` — and the one bridge is
  `mod_eq_sub_div_mul` (`E1InteriorTwoSpan.lean:143`). `omega` cannot do it
  alone (`D * (v / D)` is a product of two variables); supply
  `Nat.mod_add_div` and `Nat.mul_comm` as hypotheses and omega closes it
  treating both products as atoms.
- **`rw`'s trailing `rfl` will SOLVE an implicit numeric argument as a
  metavariable, and the damage shows up two tactics later.** Supplying a
  sub-block's register premise as `(by rw [RegFile.write_other _ _ (by
  decide)]; exact hta)` when the block's `A`/`start`/`n`/`off` are still
  implicit makes `rw` close the goal by unifying `?A := p tA`. It presents
  as **"no goals to be solved"** at the `exact`, which reads like a
  redundant tactic — and then the block's events are stated at `p tA`
  instead of at the route's own quantity, so the composition's defeq
  check runs away and reports a **whnf heartbeat timeout** at the
  `refine` that assembles the arms. Two errors, neither of them where the
  cause is. Fix: pin the implicits at the call site
  (`(A := ...) (start := ...) (n := ...) (off := ...)`, and
  `(macroStart := ...) (localStart := ...) (mid := ...) (right := ...)
  (start2 := ...) (n2 := ...)` for the combiners). E1-LaneB6 lost one
  build cycle to this on `#4` and pre-empted it on `#6`/`#7`/`#8`.
- **`interval_cases` is Mathlib.** A claim of the form "the two layouts
  agree at every index except one" written as `∀ i, 2 ≤ i → ...` has no
  cheap tactic here; state it with `List.drop` instead
  (`missDispatch.drop 2 = missDispatchImpostor.drop 2`) and the whole
  claim DECIDES.
- **A `by decide` in a fetch position fails with "expected type must not
  contain meta variables".** `RunsTo.brNZ_taken`'s `hfetch` mentions the
  implicit `cond` and `target`, so `decide` has nothing to evaluate. Bind
  each fetch in its own typed `have` (`have f0 : prog[0]? = some (...) :=
  rfl`) and pass it. Same family as §4's elaboration-order note on
  `RunsTo.move`.
- **A `mulConst` by the program constant `0` is how a global leg reuses a
  local leg's instruction shape.** `legSetup` (`E1InteriorCombine.lean:135`)
  sets `tA` and `tOff` by `mulConst` at `(levelCount * macroSize, macroSize)`
  for a local leg and at `(0, 0)` for a global one, so both share ONE
  four-instruction shape and ONE category log. Spelling the global setup with
  `const` instead would make `#6` and `#7` differ in CATEGORY for a
  difference the route does not observe.

## 5. Gotchas that have each cost a session

- `set`, `norm_num`, `by_contra` are **Mathlib** and unavailable here.
- Never raise `maxHeartbeats` on a proof about execution structure. A whnf
  heartbeat timeout there means a **stale read order** encoded in an append
  chain, not a resource shortage. The level read is the unconditional head of
  every two-span chain.
- `lake build <lib>` is binding only for the library — it misses `lean_exe`.
  Per-file `lake env lean` reports clean on commented-out code and writes no
  olean. `#print axioms` through an indirect import reports `unknown constant`
  for real theorems: import the module DIRECTLY.
- A green check is evidence only of what it examined. **A clause that is proved
  but never executed passes every check in the battery** — that is exactly how
  the interior preservation clause sat unexecuted while the fringe's twin ran.

## 6. The defect class that has bitten three times: RIGHT SHAPE, WRONG CONTENT

A category log of the right LENGTH with one slot wrong; a receipt in the right
ORDER with a stale head; a result `some` where the route is `none` with an
IDENTICAL trace. All pass length, read-count and exit-code checks. Only exact
positional, per-constructor comparison catches them.

**A fourth working model, and the sharpest one, is now in the tree**:
`spanNoneArm_discriminates` (`E1InteriorSpanBlock.lean:540`) with its four
companions. It is the third variety exactly — `some` where the route is `none`
— and the fixture establishes, by EXECUTION, that of the four things one can
check about that block, **none but the value rejects the impostor**: receipts
equal (`spanNoneArm_traces_agree`), both empty so read counts equal, both halt
(`spanNoneArm_both_halt`), and preservation holds on both arms
(`armOperands_preserved_impostor`). The one check that does catch it besides
the value is a POSITIONAL category comparison
(`spanNoneArm_catLogs_differ`) — recorded so the boundary is exact rather than
implied. Copy this shape: state the non-entailments, not just the discriminator.

**A FIFTH MODEL, AND IT MOVES THE BOUNDARY THE FOURTH ESTABLISHED.**
`spanNoneArm_discriminates` showed receipt, read count, exit code and
preservation all failing to reject an impostor while a POSITIONAL CATEGORY
comparison caught it. Read alone that invites the conclusion that a category
log is a sufficient backstop. **It is not**, and the merge block proves it
with a deliberate PAIR of impostors on opposite sides of that line:

- `mergeTie_discriminates` (`E1InteriorMerge.lean:455`) — `natLe` for
  `natLt`, wrong only on TIES, which are the generic case when two
  sub-ranges share a minimum excess. Caught by the category log
  (`mergeTie_catLogs_differ`, `:471`), because it branches where the correct
  block falls through.
- `mergePos_discriminates` (`:501`) — `qLV` for `qLP` as the position move's
  source. Takes the SAME PATH, so receipt, read count, exit code,
  preservation AND THE POSITIONAL CATEGORY LOG all agree
  (`mergePos_catLogs_agree`, `:519`, proves the last one). **Only the value
  rejects it.**

The rule: **a category log constrains WHICH INSTRUCTIONS RAN and says
nothing about their OPERANDS.** Any defect preserving the control path is
invisible to it. When you build a block's discriminator, build one impostor
that changes the path and one that does not — the second is the one that
tells you whether your value clause is load-bearing. DD-20260719-052.

**A SIXTH MODEL, AND IT LOCATES THE RECEIPT'S BOUNDARY** (M3d-28). The
two-span block's `none` arm admits TWO impostors — the same defect, a wrong
branch target, at two of the block's own live numerals — and they fall on
OPPOSITE SIDES of the receipt boundary:

- **A**, target `Q + 275` (past only the FIRST span block). The tail it
  falls into CONTAINS A READ, so it emits an event the route never emitted.
  **The receipt catches it** (`twoSpanNoneArm_receipt_catches_impostorA`,
  `E1InteriorTwoSpan.lean:1258`).
- **B**, target `Q + 500` (straight to the merge). `mergeBlock_readFree`
  makes that tail read-free, so receipt and read count are IDENTICAL to the
  correct arm's; it merges a STALE left candidate out of `qLV`/`qLP` and
  returns it where the route returns `none`.
  **The receipt is formally incapable of catching it**
  (`..._receipt_blind_to_impostorB`, `:1266`). Only the category log and the
  value reject it.

The rule this adds: **a receipt constrains WHICH READS HAPPENED, so its power
over a skipped-code defect is exactly whether the skipped code READS.** §6's
first four models all happened to skip read-free code, which made the receipt
look uniformly weak. It is not — it is weak precisely there.

**A SEVENTH MODEL, AND IT IS AT THE PROGRAM-LAYOUT LEVEL RATHER THAN
INSIDE A BLOCK** (E1-LaneB5). `unterminatedDispatch_falls_through`
(`E1InteriorDispatch.lean:1410`) is the first discriminator here whose
impostor is not a wrong operand or a wrong branch target but a MISSING
TERMINATOR — the defect the close-leg lane found live in
`crossBlockArmProgramAt`. On a `count = 0` query the unterminated layout
runs off `#9`'s `pure none` arm into `#4`'s code and halts carrying the
other arm's marker, so `bestOfRegs` reads `some` where the route reads
`none`. Same store, same entry registers, same correct selector, same
correct arm; one instruction's control effect apart.

Two things about it are worth copying:

- **The witness arms end UN-HALTED**, because every real sub-block does.
  A witness arm that halted at its own end is the one shape that cannot
  exhibit this defect, and that is precisely how the close-leg cross arm
  stayed invisible to the whole battery.
- **Its receipt blindness is the FIXTURE's, not the block's**, and is
  labelled as such. No witness arm reads, so both runs emit `[]`. In the
  real layout the fall-through lands on `twoSpanBlock`'s unconditional
  head level read, so by the sixth model's rule the real receipt WOULD
  catch it. A non-entailment recorded without that scope note would
  understate the instrument.

The exit PC and halted flag agree across both layouts, which is the
sharpest of the non-entailments: "ends at the join, halted" is the
property a layout check would most naturally verify, and this defect
preserves it.

**AN EIGHTH MODEL, THE SEVENTH'S SIBLING: RIGHT JOIN, WRONG ARM**
(E1-LaneB6). The seventh model's impostor is a MISSING terminator. This
one's is a PRESENT, correct, terminating branch whose target is a
DIFFERENT ARM'S BASE — the defect the arm composition could have
shipped. `missDispatch_runs_armA` (`E1InteriorDispatchCompose.lean:1411`)
against `missDispatchImpostor_runs_armB` (`:1502`), one instruction
apart (`missDispatch_differ_at_one_index`, `:1422`).

Every arm of `#9` reaches the same join, ends un-halted, and writes
inside `DispatchUntouched`. So **exit PC, halted flag and preservation
are all identical under a mis-dispatch** — the seventh model's
non-entailment reached from the opposite direction. What separates them:

- **the RECEIPT** (`missDispatch_receipts_differ`, `:1596`), at EVERY
  store, because a `readWord` event carries its ADDRESS and the two
  addresses are different numerals whatever the store returns — the
  inequality survives a store answering `none` to both;
- the value (`missDispatch_values_differ`, `:1604`).

This is the sixth model's rule in its FAVOURABLE direction, and it is the
real block's situation: `#4`, `#6`, `#7` and `#8` all begin with an
unconditional level read, so a real mis-dispatch changes the FIRST event
of the receipt. Against `#9`, the receipt is a real instrument, not a
formality.

**Its category-log agreement is the FIXTURE's, not the block's**
(`missDispatch_catLogs_agree`, `:1581`), and is labelled as such. The two
witness arms were given IDENTICAL instruction shapes on purpose, to leave
the receipt as the only non-value discriminator. `#9`'s real arms are
510, 1045, 1045 and 1574 instructions with different logs, so the real
category log would ALSO catch a mis-dispatch. Quoting the fixture's
agreement as the block's would understate the block — the mirror of the
seventh model's receipt-blindness note. Both witness arms end UN-HALTED.
DD-20260719-063.

**AND A PRESERVATION PREDICATE CAUGHT A REAL DESIGN ERROR AT A COMPOSITION
SITE.** The natural combiner for `#6`/`#7` stashes the first sub-leg's
candidate in `qLV`/`qLP` and merges after the second. That is WRONG:
`twoSpanBlock` CONTAINS a `mergeShuttle` and a `mergeBlock`, so it writes
that pair itself and the second sub-leg destroys the stash.
`twoSpanUntouched_excludes_mergeStash` (`E1InteriorTwoSpan.lean:331`) proves
it rather than asserting it. **Every nesting level needs its OWN stash pair**
— the combiner's is `uSV`/`uSP` at `142`/`143`. §3's "the chaining shuttle"
row is true one level DOWN and not sufficient one level UP. The type checker
caught this, not a fixture: `TwoSpanUntouched qLV` is unprovable because it
is false.

**A PRESERVATION PREDICATE CAN ALSO BE TOO STRONG, AND THAT IS THE MIRROR
OF §9's LESSON** (E1-LaneB4). §9 records a `SpanUntouched` that was too
WEAK — it declined to claim `mLP`, which its consumer needed. The
inherited `TwoLegUntouched` was the opposite: it CLAIMED four registers
its own block destroys. `TwoSpanUntouched` omits `tA`/`tStart`/`tN`/`tOff`
(`127`-`130`) deliberately and correctly, because `twoSpanBlock` only
READS them — but `twoLegBlock` WRITES all four, twice, in its two
`legSetup`s. So `TwoLegUntouched 127` closed by `decide` while the block
clobbered `127`, and the preservation clause of `twoLegBlock_runsTo`
stated with it would have been FALSE.

**Nothing catches this while a block is only DEFINED.** A preservation
predicate is not executed until a simulation quantifies over it, and the
`at_crossBlockArm_operands` evaluation passes under BOTH versions because
`70`/`71`/`75`/`76` are not among the registers at issue. Inheriting a
predicate whose block has no `runsTo` means inheriting a conjecture.
**Ask of every preservation predicate not only whether it claims enough,
but whether the block leaves alone everything it claims** — the two
failures look identical from the predicate's own text, and only the
consumer's proof obligation separates them. DD-20260719-056.

Working models to copy: `witness_maxRel_discriminates`
(`E1InteriorMinCandidate.lean:817`), `linkWitness_discriminates_content`
(`E1InteriorSummaryGroup.lean:1090`), and the stale-head receipt fixture, whose
load-bearing part is `receiptWitness_staleHead_value_agrees` — it proves a
**non-entailment**, that a value equation is formally incapable of rejecting the
impostor. For each new block, ask which sub-leg's index differs from its
neighbours' and build the impostor there.

## 7. Still owed beyond the interior program

**THE INTERIOR LEG ITSELF IS NO LONGER ON THIS LIST** (E1-LaneB6). Rows
`#1`-`#9` are built and `hInterior` is discharged and consumed. What
follows is everything else, unchanged except where noted.

- ~~**Interior preservation discriminator**~~ — **DONE and MERGED**
  (E1-LaneM). The clause is now EXECUTED, not merely stated: validator
  phase 3i runs the fold's preservation clause and phase 4h rejects a
  combine-scratch mutation that exit pc, steps, cell and read log all
  MISS (`mutantH_clobberedRegs=[102]`, `mutantH_isPreservationOnly=true`).
  DD-20260719-030..034.
- ~~**The close leg**~~ — **DONE and MERGED** (E1-LaneM), including the
  cross-arm terminator and `CloseLegUntouched`. Note the signature change
  in §3: seven premises were removed from
  `crossBlockArmProgramAt_runsTo`, not weakened around.
- **Closure ladder** — the glue FOUNDATIONS have landed (E1-LaneM):
  `guard_accept_of_valid`, the strengthened guard bridge, the object
  reconciliations, the route case-split via `E1RouteDecomposition`, and
  `wholeQueryBranchCats` are in the tree. **Still owed:** the whole-query
  PROGRAM itself — no definition composes the close legs and the interior
  into one runnable program, which is now the single blocking item for
  whole-query. Then: full LCA leg at canonical-store form; category
  accounting across ALL branches including
  selects-none and lca-none; the public `List Int` corollary; the **DERIVED**
  all-size step literal (from the category algebra and the caps 33/8/8 — derive,
  never assert); the amended-target Prop with its supersession note; the
  validator's whole-query phase; docs and matrix. One consolidated
  program-layout DD lands at the glue.
- **M7 doc claim** is scoped to QUERY TIME, construction-time carved out as
  preprocessing (`bpSparseLevelCell`, `SparseLevelTable.lean:55`). Do not write
  it until the interior leg exists.
- ~~**Prose only, deferred three times as concern-mixing**~~ — **DONE** (M3d-26).
  The `E1InteriorChunkStore.lean` header cited
  `probeShape_unbounded_agreement_fails`, which does not exist anywhere in the
  tree; the theorem is `unbounded_agreement_refuted`, now at `:594`. Folded in
  while editing that file for `hexact_local`/`hexact_global`.

## 8. Known red, externally owned — record, do not fix

`wordram_axiom_check.lean`, `axiom_check.lean`,
`lake exe rmq_succinct_classic_validate` (COMPILE-time failure).
Committed-range `git diff --check` flags whitespace solely in the inherited
`B7_STEP2_WIP.patch`.

---

## 9. Worklog — E1-LaneB, 2026-07-19 (M3d-25, M3d-25b, M3d-26)

Branch `claude/b1-b2-charged-fringe-tables`, base `c4595b7`, HEAD `f3d96e2`.
Three commits: `813fd04`, `e11eeaa`, `f3d96e2`.

**Built.** The #2/#3 parametric span block (`E1InteriorSpanBlock.lean`, new,
registered in `RMQ.lean`): `spanBlock` (222 instructions, exit `Q + 222` on both
arms), `spanBlock_runsTo` with receipt, charge log, value and preservation, and
the `none`-arm discriminator with its four non-entailments. Plus
`hexact_local`/`hexact_global`, and the 177-leg's preservation clause re-exported.

**Owed on this lane, in the order I would take them.** #2/#3's two `TableGeom`s
and route-value link (§2 says exactly how, and the gate is now open); then the
TWO-WAY merge block, which does not exist and which #4–#7 all need; then #4/#5;
then #6/#7/#8; then #9's five-branch dispatch; then `hInterior`.

**On `hInterior` specifically — the shape is known and the arithmetic checks
out, so do not re-derive it.** `crossBlockArmProgramAt_runsTo`
(`E1CrossBlockArm.lean:1181`) needs, at base `A + 176`: a `RunsTo` to
`A + 176 + interior.length`, `bestOfRegs (regsI mMV) (regsI mMP) = interiorValue`,
and preservation of `fClose` (70), `fRight` (71), `mLV` (75), `mLP` (76).
All four survive the 177-leg — `legUntouched_at_crossBlockArm_operands`
(`E1InteriorMinCandidate.lean:945`) EVALUATES that — and all four survive the
whole span block (`spanUntouched_at_crossBlockArm_operands`,
`E1InteriorSpanBlock.lean:232`). So the preservation half of `hInterior` is
already discharged for everything built so far; what is missing is only #9's
program to run.

**Two things I got wrong mid-session, recorded because the same traps are live.**
(1) My first `SpanUntouched` was false at `r = 76`, i.e. it declined to claim
`mLP` — a preservation predicate can be too WEAK and still typecheck, and
nothing catches that but reading it against the consumer's needs. It is marked
SUPERSEDED in the module rather than silently rewritten.
(2) Every line number I wrote into §3 from memory was wrong, and inserting
`LegUntouched` shifted `summaryMinCandidate_runsTo` from `:929` to `:963`,
staling four citations I had not written. Grep your own output; the worklog's
historical `:929` references were left alone as records of what was true then.

---

## 10. Worklog — E1-LaneB2, 2026-07-19 (M3d-27)

Branch `claude/b1-b2-charged-fringe-tables`, base `2ad0206`. Six commits.
DD-IDs claimed: **`051` and `052`**; also WROTE `050`, which my predecessor
claimed in its report and cited twice in `E1InteriorSpanBlock.lean` but
never entered in `DESIGN_DECISIONS.md`. Band `053-069` remains free.

**Built.**
- **#2 and #3 CLOSED.** `localSpanGeom`/`globalSpanGeom`, their caps, the
  two unconditional cell bridges, the `cellOpt` forms, the leg-value link,
  and the two headline route-value theorems. Plus the two missing concrete
  store clauses `hexact_local_concrete`/`hexact_global_concrete`, one line
  each — the four summary twins existed; the two span twins had simply not
  been written.
- **The two-way merge block** (`E1InteriorMerge.lean`, new, registered in
  `RMQ.lean`): 9 instructions, all four option combinations, read-free,
  writing IN PLACE to `mMV`/`mMP`, with `mergeBlock_runsTo`, the paired
  discriminators, and preservation EXECUTED on three arms.
- **`merge3_eq_two_merges` and `mergeShuttle`**, which shrink #8.

**NOT built, and not started:** #4, #5, #6, #7, #8, #9, `hInterior`. The
merge block is the piece #4–#8 were blocked on, but no composition exists:
#4/#5 still need the level read wired as the unconditional head of a
two-span append chain, with two `spanBlock` runs and a `mergeBlock` after.

**Four coordinator/file claims checked; two failed.**
1. `geomCell_eq_routeDecode` and `geomRouteDecode_eq_readComputation_value`
   were cited as `E1InteriorChunkStore.lean:674`/`:904`. **Wrong file** —
   both are in `E1InteriorSummaryGroup.lean`, and `E1InteriorChunkStore.lean`
   is 619 lines, so `wc` refutes it. Line numbers were right. Fixed in §2.
2. `candMerge3`'s epilogue "writes the closed position where the combiners
   need the candidate left in the bank". **False** — the close is additive
   and `candMerge3_runsTo` already exports the merged candidate in
   `mAV`/`mAP`. Struck through in §2 with the real reason (the `fRes` 69
   clobber) recorded. The conclusion it supported — that no two-way merge
   block existed — held, and I built one.
3. `hexact_local`/`hexact_global` at `E1InteriorChunkStore.lean:514`/`:537`
   — **correct**, and they composed in one line each as advertised.
4. `bpCandidateMerge3?` is definitionally two `bpCandidateMerge?`
   applications — **correct**; landed as a checked one-liner rather than
   relied on as a remark.

**What I would take next, in order.** #4 and #5, which are now
same-pattern-twice exactly as #2/#3 were: define the two level-table
`TableGeom`s by the §4 recipe, then compose `levelRead ++ spanBlock ++
stash ++ spanBlock ++ mergeBlock`. The level read is the UNCONDITIONAL
HEAD of the chain — putting it anywhere else encodes a stale read order and
presents as a whnf heartbeat timeout, not as a wrong answer. Then #6/#7/#8,
which are read-free and now need only `mergeBlock` + `mergeShuttle`. Then
#9's five-branch dispatch, then `hInterior`.

**On `hInterior`, carried forward and now stronger.** Its preservation half
is discharged for EVERYTHING built so far: the 177-leg
(`legUntouched_at_crossBlockArm_operands`), the whole span block
(`spanUntouched_at_crossBlockArm_operands`), the merge block
(`mergeUntouched_at_crossBlockArm_operands`) and the shuttle
(`shuttleUntouched_at_crossBlockArm_operands`) each EVALUATE that `70`,
`71`, `75`, `76` survive. What is missing is still only #9's program to run.

**Honest note on the validator.** `lake exe rmq_e1_machine_validate` is
PASS, but phase 5 reports `wholeQueryComparisonAvailable=false` and
`wholeQueryComparison=OPEN (interior leg UNBUILT)`. **It does not exercise
anything I built.** Evidence for these blocks is the in-tree executed
fixtures, not the validator run.

**One process mistake, recorded.** I committed a `#print axioms` scratch
driver (`axcheck_e1laneb2.lean`) into the tree and had to remove it in a
follow-up commit. Keep throwaway drivers in the session scratchpad; `git
add -A` will otherwise take them.

---

## 10b. Worklog — E1-LaneB6, 2026-07-19

Branch `claude/b1-b2-charged-fringe-tables`, base `59e5a93`.
DD-IDs claimed and WRITTEN into `DESIGN_DECISIONS.md`: **`061`, `062`,
`063`**. Band `064-069` remains free.

**This section replaces E1-LaneB5's worklog per the coordinator's
standing instruction. Its still-live findings have been folded into §2,
§3, §3a, §4 and §6 rather than dropped.**

**BUILT: THE ARM COMPOSITION AND `hInterior`. THE INTERIOR LEG IS
COMPLETE.** One new module, `E1InteriorDispatchCompose.lean`, registered
in `RMQ.lean`. `E1CrossBlockArm.lean` was NOT edited.

- `interiorDispatchBlock_runsTo` (`:816`) — `#9`'s five arms composed
  into one simulation from `Q` to `Q + 4204`, carrying receipt, category
  log, value and preservation on every branch, case-split against
  `interiorRangeMin_of_*`.
- `interiorDispatch_hInterior` (`:1171`) — `hInterior`'s body at its
  intended instantiation. FOUR register equalities, not five.
- `crossBlockArm_withCanonicalInterior_runsTo` (`:1274`) — which CONSUMES
  `crossBlockArmProgramAt_runsTo` with it. See the note below on why
  this, and not the previous item, is what discharges the premise.
- `interiorDispatch_preserves_closeLeg` (`:1223`) — the close leg's
  clause as a SEPARATE additional export.
- `dispatchEvents` (`:194`), `dispatchArmCats` (`:264`), `dispatchCats`
  (`:374`), `dispatchRouteValue` (`:381`) — receipt and charge log
  written from the ROUTE's own five-way condition order, before the
  machine side was touched. DD-20260719-061.
- `dispatchPrologue_runsTo` (`:701`) and
  `canonicalInteriorDispatchBlock_hosts` (`:396`).
- `canonicalBlockSize_eq_layoutBlockSize` (`:1151`) — a KERNEL CHECK.
- The mis-dispatch discriminator, §6's eighth model (`:1431`, `:1502`,
  `:1574`, `:1581`, `:1596`, `:1604`). DD-20260719-063.

**WHY THE `hInterior` CLAIM IS TWO THEOREMS AND NOT ONE.** A theorem with
`hInterior`'s SHAPE and a DISCHARGED `hInterior` are different claims,
and only the second is worth anything. `interiorDispatch_hInterior` could
have typechecked while failing to unify with the premise — if
`interior.length` did not reduce to `4204`, or if the route's
`canonicalBPRelativeSummaryBlockSizeRaw shape` and the sub-blocks'
`(RelativeRmm.canonicalLayout shape).blockSize` were not the same term to
the elaborator. `crossBlockArm_withCanonicalInterior_runsTo` applies
`crossBlockArmProgramAt_runsTo` to it and therefore proves both. Anyone
reading only the first theorem is reading a weaker claim than the module
makes. DD-20260719-062.

**Six coordinator/file claims checked. All six held.** This is the first
lane in a while with no correction to report, which is itself worth
recording rather than papering over — the file has been edited by five
workers since the last coordinator pass, and it shows.

1. `hInterior` has exactly FOUR register equalities — **held**, re-read
   at `E1CrossBlockArm.lean:1181` before writing anything against it.
2. `#9` falls through and MUST, because `hInterior`'s target state
   carries `halted = false` — **held**, and now executed: the composition
   ends `⟨regs', Q + 4204, false⟩`.
3. The physically last arm exits by fall-through and cannot have an
   explicit branch — **held**. `#8`'s exit `Q + 2630 + 1574` is the join.
4. `(RelativeRmm.canonicalLayout shape).blockSize` IS
   `canonicalBPRelativeSummaryBlockSizeRaw shape` definitionally — **held
   AND UPGRADED**: it is now `canonicalBlockSize_eq_layoutBlockSize`,
   proved `rfl`, so a future divergence stops the build instead of
   silently breaking every `hInterior` instantiation.
5. Next free register bank is `152` — **held**, and this session
   allocated nothing: the composition reuses `146`-`151` and the
   discriminator fixture reuses `wT`/`wStart`/`mMV`. **`152` is still
   free.**
6. `CloseLegUntouched` is a SEPARATE export and not a fifth conjunct —
   **held**; a fifth conjunct does not typecheck and was not attempted.

**Two traps met, one of them expensive.** Both are now in §4.
(1) `rw`'s trailing `rfl` SOLVED a sub-block's implicit `A`/`start`/`n`/
`off` as metavariables when the register premise was supplied as
`(by rw [...]; exact hta)`. It surfaced as "no goals to be solved" at the
`exact` — which reads like a redundant tactic — plus a whnf heartbeat
timeout at the `refine` 25 lines later. Neither error was at the cause.
Pin the implicits at the call site.
(2) `interval_cases` is Mathlib; `by decide` in a fetch position fails
with "expected type must not contain meta variables".

**Validator, and what it is NOT evidence of.**
`lake exe rmq_e1_machine_validate` is PASS at **8.8 s wall clock**;
phase 3 `dispatchCases=405`/`modeledSteps=2430`, phase 3b
`legCases=90`/`legModeledSteps=30343`, phase 3c
`selectCases=32`/`selectModeledSteps=8273`, phase 3d
`composeCases=40`/`composeModeledSteps=9222`, phase 3e
`mergeCases=36`/`mergeModeledSteps=431`, phase 3f
`armCases=36`/`armModeledSteps=6276`. **It does not exercise one line of
this session's work.** The evidence for the composition is the in-tree
simulation and the discriminator, not this run.

**AND ITS PHASE-5 MESSAGE IS NOW STALE, in a way that will mislead.**
Phase 5 still reports `wholeQueryComparisonAvailable=false` and
`wholeQueryComparison=OPEN (interior leg UNBUILT, ... five-branch
composition and hInterior not written; NOT a pass)`. **The parenthetical
is false at this commit**: both are written. The string lives in
`RMQ/Validation/E1MachineValidate.lean`, which belongs to the unmerged
`claude/e1-interior-preservation` branch and which this lane may not
edit, so it is RECORDED here rather than fixed. Whoever merges that
branch owes the correction, and until then the validator's own phase-5
text should not be quoted as a statement about the interior leg.

**`#print axioms`** on the eleven exported theorems, through a
scratchpad driver importing `E1InteriorDispatchCompose` directly:
`propext, Classical.choice, Quot.sound` on the eight substantive ones,
`propext` alone on `canonicalBlockSize_eq_layoutBlockSize` and
`missDispatch_receipts_differ`, and `missDispatch_differ_at_one_index`
and `missDispatch_catLogs_agree` depend on **no axioms at all**. No
`sorryAx` anywhere.

**What I would take next.** The interior leg is done, so the frontier is
whole-query assembly: the glue via `E1RouteDecomposition`, category
accounting across ALL branches (§11 F's warning about writing the
whole-query category function FROM THE ROUTE applies with full force and
is now the single largest un-instrumented obligation — `catLog` still
appears zero times in the validator), and the DERIVED all-size step
literal. Note §11 B: state that target as an INEQUALITY and `Nat.log2` is
not an obstruction. Two cheap independent items are still unclaimed and
block nothing: `catCount log c = (log.filter (· == c)).length` (§11 D,
absent, short induction) and REQ-E1-05's validator phase (§1).

### What whole-query assembly may now ASSUME (E1-LaneM, five-branch merge)

All five branches are in one tree and the tree is green, so the assembler
no longer has to reason about which lane a fact came from. It may assume,
without rebuilding any of it:

- **The interior leg is complete AND consumed.** `interiorDispatch_hInterior`
  (`E1InteriorDispatchCompose.lean:1171`) is not merely `hInterior`-shaped;
  `crossBlockArm_withCanonicalInterior_runsTo` (`:1274`) APPLIES
  `crossBlockArmProgramAt_runsTo` to it, so the shape is known to UNIFY.
  Assembly consumes the wrapper and does not re-derive `hInterior`.
- **The cross arm needs NO width or window premises.** After the close-leg
  merge, `crossBlockArmProgramAt_runsTo` takes
  `shape hHost hInterior regs hClose hRight` and nothing else. Do not
  attempt to discharge `hc` or any `readBits ... .length` fact for it —
  those premises are gone, and six of them are FALSE at reachable close
  positions. Same for the wrapper. See §3 and DD-20260719-110.
- **The close leg exports its own preservation clause.** `CloseLegUntouched`
  (`r ≤ 7 ∨ r = 28`) survives the interior:
  `interiorDispatch_preserves_closeLeg` (`:1223`) is a SEPARATE export, so
  assembly can carry close-leg register facts across the interior without
  re-proving them.
- **The guard and route case-split are available.** `guard_accept_of_valid`
  (`E1QueryProgram.lean:608`), the strengthened guard bridge, the object
  reconciliations, `E1RouteDecomposition`'s case-split
  (`E1RouteDecomposition.lean:41`) and `wholeQueryBranchCats`
  (`E1WholeQueryCats.lean:98`) all exist. §11 F's warning still binds:
  write the whole-query category function FROM THE ROUTE — LaneG already
  did, and `wholeQueryBranchCats` is indexed by a route-side branch
  classifier for exactly that reason.
- **Preservation is instrumented, not just stated.** Validator phases 3i
  and 4h execute the interior fold's preservation clause and reject a
  mutation invisible to every other discriminator. A whole-query phase can
  follow that pattern rather than inventing one.

**What assembly may NOT assume: that any whole-query program exists.** It
does not. There is no `wholeQueryProgram` in the tree;
`WholeQueryMachineAgrees` (`E1WholeQueryPublic.lean:114`) is the target
predicate, not a program. Validator phase 5 is OPEN, contributes no clause
to the verdict, and runs no comparison — building the program is the
blocking item, and phase 5 must not be flipped to available until there is
something real for it to run.


---

## 11. Findings from the four read-only surveys (2026-07-19)

Only items that change what a worker should DO are here. Cosmetic doc drift was
deliberately left unfixed and is listed at the end.

**A. The operative constant is `210`, not `207`.** AMENDMENT A1 in the matrix
(owner-approved) migrated REQ-E1-06's frozen `<= 207` and the accepted-route
citations. At HEAD `207` is a frozen HISTORICAL constant naming a retired route;
`f6000c3` migrated the live bound to `210`. Algebra:
`2*select35 + (2*rank11 + 2*endpointFringe37 + interior33) + rank11 = 210`,
`closeLCA = 129`. **Never prove anything against `207`.**

**B. `Nat.log2` does NOT block the derived step literal.** Three sessions have
been shaped by treating the kernel boundary as an obstruction here. It is not:
REQ-E1-06 conjunct (c) demands an **inequality** `totalSteps <= <literal>`, not
an equality, and every cap in the algebra is proved symbolically by
`unfold; omega`. The boundary bites only on *equations* whose value passes
through `machineWordBits`. State the target as `≤` and it is reachable today.

**C. THERE ARE TWO DISTINCT `33`s, and the campaign shorthand "caps 33/8/8"
conflates them.**
- fringe-window chunk-read cap — lives INSIDE `endpointFringe = 4 + 33 = 37`
  (`ChargedFringeChunks.lean:1624-1687`)
- whole-interior-directory read cap —
  `canonicalRelativeRmmPrincipledInteriorChargedTraceCost := 33`
  (`InteriorDirectory.lean:1934`)
- (`3 * rankClose = 33` is a third, coincidental)
The two `8`s were already flagged as distinct in an M3d-11 note; **the two 33s
never were**, and they are the more dangerous pair because one sits inside the
other's sibling term in the same algebra. Anyone writing the step literal or
REQ-E1-07's supersession note must distinguish them.

**D. A vocabulary gap with zero bridge lemmas.** Machine-level accounting uses
`catCount log c`; every block-level cap uses `(log.filter (· == c)).length`.
There is **no lemma connecting them anywhere**. REQ-E1-06 needs
`catCount log c = (log.filter (· == c)).length` — a short induction, absent,
buildable today with no interior dependency, and currently invisible to everyone.

**E. REQ-E1-07's supersession note must be precise about WHAT was refuted.**
`E1R3FamiliarMachineTarget` and `e1R3FamiliarMachineTarget_obstruction` are
recoverable as git objects at commit `7fe5b8b` (absent from HEAD sources). The
note must name the **THIRD conjunct** — the familiar-local-iteration lower bound
— and cite `e1R3CanonicalSameBlockInvocation_unbounded` as the refuting witness.
Two further precision points: the old target had **five** step categories, the
amended machine freezes **six** (DD-20260718-005), so the category set is
refrozen rather than inherited; and the old target demanded
`publicModeledCost = accepted.toCosted.cost` as an **equality**, which the
amended Prop should preserve rather than weaken to `≤`.

**F. On the `none` branches the positional category log is the SOLE
discriminator.** Result agreement degenerates to `none = none`, satisfied by any
impostor that also returns `none`; and a machine that ran a leg it should have
skipped is invisible to receipt equality restricted to the legs that DID run.
Category accounting is also the ONE obligation with no discriminator anywhere —
`catLog` appears **zero** times in the 1,901-line validator, while value, receipt
and preservation each have a mutant proven invisible to the other two.
**Corollary for anyone writing a whole-query category function: write it from
the ROUTE, before the machine side exists. A category function written after the
machine is a category function fitted to the machine.**

**G. Sibling-branch state.** `chunkPres*` / `mutantH` (the interior fold's
executed preservation phase) are NOT on this branch — they are on
`claude/e1-interior-preservation`, unmerged. If you grep for them here and find
nothing, that is why. Two further lanes are live on
`claude/e1-close-leg-structural` (the nine width premises, the cross arm's
missing terminator, `hc`, and the composed arms' absent preservation clauses)
and `claude/e1-glue-foundations` (guard-accept, the category strengthening, the
rank/LCA object reconciliations, the route case-split combinator).

**H. Do NOT re-issue the `OfSizeGe` framing** for the M7 doc claim. It was
supplied twice by a coordinator and refused twice, correctly:
`WholeQueryInstr.evalGlobalWordTraceOfSizeGe` takes its size premise
**underscore-prefixed and unused**, and its `.lcaClose` arm dispatches to the
same accepted interior leg. The correct contrast is `...AllSizeStructural`
(accepted) vs `...AtSegmentsAllSizeStructuralLegacy`.

**Recorded, deliberately NOT fixed** (owner direction: spend usage on semantic
work, not on prose drift) — owed to REQ-E1-09's closure pass:
`README.md` asserts the retired `207` at `:70`, `:76`, `:140`, `:334` while
`:80` cites the `...SumLe210` identifier, i.e. it is internally inconsistent;
`docs/FAMILY_SUMMARY.md` still carries the PRE-B7 algebra (`interior30 ... = 207`)
at `:9`, `:43`, `:48`, `:133`, `:446`, `:1041`. Neither gate catches this:
`CLAIM_DRIFT_POLICY.json` has no `207`/`210` term and `paper_topology_lint.ps1`
anchors on identifiers, not prose numerals. Separately, REQ-E1-09 instructs
fixing four "fresh segment 21" surfaces that ALREADY read `23`, and a 33-cap
attribution that is ALREADY correct.
