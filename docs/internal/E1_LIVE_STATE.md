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

**THE COST-ALGEBRA BRANCH IS NOW MERGED TOO, AND THE WHOLE-QUERY STEP
LITERAL IS DERIVED (E1-LaneF).** `claude/e1-cost-algebra` (`1e8dcc5`) is in.
There is no unmerged E1 sibling lane left at all, and §11 G's list of live
lanes is history. What that merge added to this tree, on top of everything
below:

- the **charge-length ladder** — `E1CostLadder.lean`, all sixteen composite
  category-log bounds plus seventeen leaf logs, each derived by `unfold` +
  `omega` from its own algebra;
- the **`catCount`/`filter` bridge**, exercised rather than merely stated —
  `E1CostAlgebra.lean`;
- **REQ-E1-07's amended Prop** — `E1AmendedTarget.lean`;
- the **whole-program width certificate** — `E1ReviewerWidth.lean`;
- `E1FringeFoldProgram.lean` and validator phases 3k/4j executing
  `FringeFoldUntouched`.

**REQ-E1-06 CONJUNCT (c) IS CLOSED AT `11886`** —
`wholeQueryCats_machineS_length_le` (`E1WholeQueryCostLiteral.lean`), all
four branches, every shape, every query, NO size hypothesis.
`11886 = 9 + 729 + 2 + 729 + 10179 + 2 + 234 + 2`, every summand derived.
Section 15 is that lane's worklog and states what is left.

**`11886` IS A STEP BOUND. `210` IS A READ BOUND. They are not comparable**,
and neither is derived from the other — see §11 A and DD-20260719-244.

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

~~**What is still missing for whole-query is the whole-query PROGRAM
ITSELF** — no definition composes the close legs and the interior into one
runnable query program, and no `wholeQueryProgram` exists in the tree.~~
**PARTLY SUPERSEDED (E1-LaneA1).** A program now exists:
`wholeQueryValidPathThroughLca` (`E1WholeQueryProgram.lean:155`) composes
select setup, both select legs, the select join and the terminated close/LCA
leg, with every stage base computed from the preceding lengths. **The guard
and BOTH select legs are EXECUTED** (`wholeQuerySelectPrefix_runsTo`,
`:250`). Left struck through rather than deleted, per the standing rule.

**But `WholeQueryMachineAgrees` (`E1WholeQueryPublic.lean:114`) is still NOT
discharged, and validator phase 5 is still correctly OPEN.** Of the two
obligations E1-LaneA1 found, **the first is now CLEARED (E1-LaneA3) and the
second stands** - see 10d:

1. ~~`crossBlockArmProgramAt_runsTo` exports NO preservation clause~~
   **CLEARED, DD-20260719-160.** `crossBlockArmProgramAt_runsTo`
   (`E1CrossBlockArm.lean:1199`) exports
   `forall r, CloseLegUntouched r -> regsF r = regs r`, its `hInterior` having
   gained a matching fifth conjunct supplied by `interiorDispatch_hInterior`
   (`E1InteriorDispatchCompose.lean:1181`). `closeLcaProgramAt_runsTo_cross`
   (`E1WholeQueryCloseLca.lean:258`) exports it too, so preservation across
   the close/LCA leg is now SYMMETRIC with the same-block twin at `:191`
   (DD-20260719-161). Register state may be carried across BOTH arms.

2. **STANDS.** The cross-block arm's INTERIOR OBJECT is not reconciled with
   the route's: `crossBlockArmSpec_eq` (`E1CrossBlockArm.lean:181`) yields the
   interior as `if leftBlock + 1 < rightBlock then ... else pure none` while
   `crossBlockArm_withCanonicalInterior_runsTo`
   (`E1InteriorDispatchCompose.lean:1291`) produces
   `<dispatchRouteValue ..., dispatchEvents ...>`, and NO theorem identifies
   them. **The gap is on the TRACE side only** - the value side is already
   route-linked - and closing it needs three new ladder lemmas, NOT assembly.
   Scoped in detail in 10d; budget it as a moderate proof.

**BEYOND THOSE TWO, AND THIS IS THE ONE THAT WILL COST SOMEONE A SESSION:
THE COMPOSED VALID PATH FALLS THROUGH INTO THE `none` WRITER.**
DD-20260719-162, pinned by two executed theorems,
`wholeQueryValidPath_exit_is_invalidExit` (`E1WholeQueryProgram.lean:375`) and
`wholeQueryValidPath_falls_into_noneWriter` (`:384`).

`programSkeleton`'s docstring (`E1QueryProgram.lean:130`) says "the valid path
ends by writing `regOut` and halting". `wholeQueryValidPathThroughLca`
(`E1WholeQueryProgram.lean:155`) does NEITHER - grepped, there is no `.halt`
and no `regOut` write anywhere in it. And the omission is not inert: the
close/LCA leg's exit is `closeLcaExit 827 = 5580`, and the skeleton puts
`invalidExitBlock` at `8 + 5572 = 5580`. The addresses COINCIDE, so the valid
path falls straight into `.const regOut 0` then `.halt`, and `regOut = 0` is
the NONE packet.

**So the program as composed would halt carrying `none` for every valid
query**, including every branch whose route value is `some`. Nothing currently
proved is wrong - no theorem claims the whole path runs, and each leg's
`runsTo` stops at its own exit. The hazard is entirely to the next lane:
anyone who reads the two-blocker list and concludes the remainder is "compose
the executed legs" is composing toward a program that answers `none`
unconditionally, and will find out at `WholeQueryMachineAgrees`'s value clause,
far from the code responsible.

~~**Budget the remainder as THREE items past blocker 2, not one**: the select
join's simulation, a NEW output stage decoding `fRes` into `regOut` and
halting, and only then the agreement.~~ **THE FALL-THROUGH IS REPAIRED
(E1-LaneA5, DD-20260719-180/-183); the two theorems above are RETAINED as the
record of what the repair prevents, and are still true of
`wholeQueryValidPathThroughLca`, which is still the path THROUGH the
close/LCA leg.** The repaired path is `wholeQueryValidPath`; it appends a
64-instruction output stage, so `invalidExitBlock` moves from `5580` to
`5644`. See §10e.

**AND THE PARAGRAPH ABOVE UNDER-SPECIFIED THE OUTPUT STAGE, WHICH IS THE
FINDING WORTH CARRYING.** A stage that "decodes `fRes` into `regOut` and
halts" would have halted at the RIGHT ADDRESS CARRYING THE WRONG NUMBER. The
route's `.full` value is `some ((rank ... (answerClose + 1)).value - 1)`
(`wholeQueryBranchValue`, `E1RouteDecomposition.lean:330`) — a RANK LEG sits
between the close/LCA leg's answer and the output packet. `fRes` is a close
POSITION; the answer is an INDEX. The four-instruction stage would have
produced a program that halts, answers `some`, passes every layout check, and
is wrong — the same defect class as the three address coincidences, one level
up, and invisible to exactly the same checks. The stage that landed is 64
instructions: rank setup, rank leg, packet write, halt.

The select join's simulation is also now DONE, on all three of its exits.

**Validator phase-5 TEXT IS NOW STALE AGAIN**, in the opposite direction from
the staleness §10b recorded. It reads "no definition composes them into one
runnable query program"; one now does. The string lives in
`RMQ/Validation/E1MachineValidate.lean`, which is the category-algebra
sibling lane's file, so E1-LaneA1 did not edit it. The VERDICT (`OPEN`, not a
pass) remains correct — only the parenthetical is wrong.

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
| cross-block arm — **SIGNATURE CHANGED, see below** | `crossBlockArmProgramAt_runsTo` — `E1CrossBlockArm.lean:1199` |
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
| its four prologue simulations | `rangePreamble_runsTo` `E1InteriorDispatch.lean:587`, `indexDecomp_runsTo` `:715`, `localArmSetup_runsTo` `:907`, and the selector below |
| **the five arm-reachability lemmas** | `dispatchSelector_reaches_arm0` `E1InteriorDispatch.lean:1011`, `_arm4` `:1039`, `_arm6` `:1076`, `_arm7` `:1133`, `_arm8` `:1198` |
| **THE FALL-THROUGH DISCRIMINATOR** | `unterminatedDispatch_falls_through` — `E1InteriorDispatch.lean:1419` |
| its correct twin, and the boundary | `witnessDispatch_runs_none` `:1358`, `unterminatedDispatch_receipts_agree` `:1499`, `..._catLogs_differ` `:1511` |
| **#9's preservation, checked against its OWN writes** | `DispatchUntouched` `E1InteriorDispatch.lean:335`, `dispatchUntouched_of_lt` `:380` |
| **the close leg's clause, as a SEPARATE export** | `dispatchUntouched_of_closeLegUntouched` — `E1InteriorDispatch.lean:436` |
| the route's five branches, machine-free | `interiorRangeMin_of_count_zero` `E1InteriorDispatch.lean:456`, `_of_local` `:464`, `_of_adjacent` `:477`, `_of_leftMiddle` `:495`, `_of_cross` `:516` |
| the caller's guard is subsumed | `interiorRangeMin_guard_subsumed` — `E1InteriorDispatch.lean:553` |
| **`#9`'s FIVE ARMS COMPOSED — the interior leg's top** | `interiorDispatchBlock_runsTo` — `E1InteriorDispatchCompose.lean:816` |
| **`hInterior`, DISCHARGED** | `interiorDispatch_hInterior` — `E1InteriorDispatchCompose.lean:1181` |
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
| same-block leg composed — **BASE `0` ONLY, see §3b** | `sameBlockDispatchProgram_runsTo` — `E1CloseCompose.lean:95` |
| **the close/LCA leg's OWN branch split, route-side** | `lcaLeg_of_sameBlock` `E1WholeQueryLcaLeg.lean:64`, `lcaLeg_of_crossBlock` `:83` |
| its anti-vacuity | `lcaLeg_branches_exhaustive` — `E1WholeQueryLcaLeg.lean:149` |
| **THE CLOSE/LCA LEG, REBASABLE AND TERMINATED** | `closeLcaProgramAt` — `E1WholeQueryCloseLca.lean:119`, length `4753` at `:125` |
| its four hosting facts, offsets computed | `closeLcaProgramAt_hosts` — `:132` |
| **both arms executed, converging at `closeLcaExit A`** | `closeLcaProgramAt_runsTo_same` `:183`, `_runsTo_cross` `:243` |
| the convergence address checked against the length | `closeLcaExit_eq_end` — `:124` |
| **THE WHOLE-QUERY PROGRAM** | `wholeQueryValidPathThroughLca` — `E1WholeQueryProgram.lean:155`, length `5572` at `:160` |
| its select prefix | `wholeQuerySelectPrefix` `E1WholeQueryProgram.lean:143`, length `813` at `:148` |
| **the guard and BOTH selects, EXECUTED** | `wholeQuerySelectPrefix_runsTo` — `E1WholeQueryProgram.lean:268` |
| stage hosting, every offset computed | `wholeQuerySelectPrefix_hosts` `:180`, `..._hosts_closeLca` `:206` |
| the close/LCA leg's base, checked not asserted | `closeLca_base_is_827` — `:169` |

### 3b. THE CLOSE/LCA COMPOSITION WAS PINNED TO BASE `0` — do not reuse it above

`closeDispatchProgram` writes its branch target as `4 + crossArm.length`,
which is the same-block arm's ABSOLUTE address only when the program is
hosted at `0`; `sameBlockDispatchProgram_runsTo` (`E1CloseCompose.lean:95`)
accordingly runs from `⟨regs, 0, false⟩`. In the whole query the close/LCA leg
sits after the guard and BOTH select legs, so that composition is
inapplicable there — not weakened, simply unusable.

**Use `closeLcaProgramAt` (`E1WholeQueryCloseLca.lean:119`) instead**, which
takes its host base `A` and computes every target from it, AND wires the
cross arm's terminator. Layout: dispatch `4` at `A`, cross arm `4574` at
`A + 4`, terminator `2` at `A + 4578`, same-block leg `173` at `A + 4580`,
both arms converging at `A + 4753`.

**The terminator was DEFINED BUT NEVER APPLIED TO A REAL ARM before
E1-LaneA1.** `crossArmTerminated` (`E1CloseDispatch.lean:625`) and
`crossArmTerminated_converges` (`:649`) existed only against that module's own
two-instruction stub `unterminatedCrossArm` (`:444`). DD-20260719-121.

**~~PRESERVATION IS ASYMMETRIC ACROSS THE TWO ARMS~~ — SUPERSEDED
2026-07-19 by E1-LaneA3. PRESERVATION IS NOW SYMMETRIC.** Both
`closeLcaProgramAt_runsTo_same` (`E1WholeQueryCloseLca.lean:191`) and
`_runsTo_cross` (`:258`) export
`∀ r, CloseLegUntouched r → regsF r = regs r`, because
`crossBlockArmProgramAt_runsTo` (`E1CrossBlockArm.lean:1199`) now does.
DD-20260719-160, DD-20260719-161.

**Read the superseded warning carefully before reusing its reasoning**, because
its conclusion was right for the wrong reason and the difference matters. It
said a composed leg claiming preservation on both arms "would be claiming
something FALSE on one of them" — the too-strong predicate failure
DD-20260719-056 records at `TwoLegUntouched`. That was NOT the situation. The
cross arm's write set has always been disjoint from `{0..7} ∪ {28}`: each of
its fourteen segments admits the band by its own predicate, and the two writes
that look like counterexamples (`crossRepoint` writes `fClose` = 70, the merge
writes `fRes` = 69) are outside it. Nothing about the claim was ever false.

The obstruction was the INTERFACE, not the code: `hInterior` promised only
`fClose`/`fRight`/`mLV`/`mLP` across the mid-arm interior hole, so the arm
could not promise a caller more than its own hypothesis promised it. Widening
`hInterior` with a fifth conjunct closed the hole, and the clause then threaded
with **no change to any instruction**.

**The generalisable lesson**: "arm X exports no preservation clause" is a fact
about a signature. Before treating it as a fact about the arm's behaviour —
and especially before invoking the too-strong-predicate precedent — check the
arm's own WRITE SET. An operands-style check (`..._at_crossBlockArm_operands`)
cannot settle it either way, because it tests one consumer's reads.

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
**`false`** (`E1CrossBlockArm.lean:1199`, re-read this session). So a
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
(`E1CrossBlockArm.lean:1199`) no longer takes `hc`, and no longer takes the
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
(`E1InteriorDispatchCompose.lean:1291`) has had the same seven binders
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
(`E1InteriorDispatch.lean:1419`) is the first discriminator here whose
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
shipped. `missDispatch_runs_armA` (`E1InteriorDispatchCompose.lean:1429`)
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
(`E1CrossBlockArm.lean:1199`) needs, at base `A + 176`: a `RunsTo` to
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
   at `E1CrossBlockArm.lean:1199` before writing anything against it.
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
  (`E1InteriorDispatchCompose.lean:1181`) is not merely `hInterior`-shaped;
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

## 10c. Worklog — E1-LaneA1, 2026-07-19 (whole-query assembly)

Branch `claude/b1-b2-charged-fringe-tables`, base `fd59487`. Two commits:
`d46a7fc`, `fadc4aa`. DD-IDs claimed and WRITTEN into `DESIGN_DECISIONS.md`:
**`120`, `121`, `122`**. Band `123-139` remains free.

**BUILT.** Three new modules, all registered in `RMQ.lean`.

- `E1WholeQueryLcaLeg.lean` — the close/LCA leg's own branch split
  (`lcaLeg_of_sameBlock` `:57`, `lcaLeg_of_crossBlock` `:83`), **which was
  absent from the tree**, plus `lcaLeg_branches_exhaustive` `:110`.
- `E1WholeQueryCloseLca.lean` — `closeLcaProgramAt` `:111`, the close/LCA leg
  rebased off base `0` and with the cross arm's terminator wired to a REAL
  arm for the first time; both arms executed (`:183`, `:243`).
- `E1WholeQueryProgram.lean` — `wholeQueryValidPathThroughLca` `:155`, the
  first definition in the campaign composing query legs into one runnable
  program, and `wholeQuerySelectPrefix_runsTo` `:250`, which EXECUTES the
  guard and both select legs at every shape and every valid range.

**THREE COORDINATOR/FILE CLAIMS CHECKED; TWO NEEDED CORRECTION.**

1. "The cross arm has a terminator DEFINED BUT NOT YET WIRED" — **held**, and
   wiring it turned out to be inseparable from a second defect the brief did
   not name (below). DD-20260719-121.
2. "`programSkeleton`'s `validPath` instantiated with the composed close/LCA
   leg" as a one-step task — **the composition was pinned to base `0`.**
   `closeDispatchProgram`'s branch target `4 + crossArm.length` is absolute
   and correct only at base `0`, and the whole query puts the close/LCA leg
   after the guard and both selects. This is now §3b. The terminator and the
   rebasing HAD to land together: the terminator's jump target is absolute
   and cannot be written correctly until the layout is parametric in `A`.
3. "Only `5,6,7` are dead after the guard" — **UNDER-COUNTED BY TWO.** The
   dead set is `{3,4,5,6,7}`: `regZero` (3) is read only by the two
   `natEq regG _ regZero` instructions and `regN` (4) only by
   `natLe regT2 regRight regN`, all inside `guardBlock`
   (`E1QueryProgram.lean:110`) and all executed before pc `8`. Nothing in the
   valid path reads either. DD-20260719-122.

**AND ONE FALSE ALARM WORTH RECORDING.** The brief warned that the select
leg proves the CHUNKED select object while the route decomposition names the
non-chunked one. There is no gap:
`concreteBPNativeSelectCloseGlobalWordTraceResult`
(`SuccinctFinalRAM.lean:1342`) is DEFINITIONALLY the chunked one, so the
bridge is `rfl`. Grepped before budgeting time for a reconciliation.

**WHAT BLOCKS THE REST OF `WholeQueryMachineAgrees`**, and neither item is a
matter of assembly effort:

1. **The cross arm exports no preservation clause** [SUPERSEDED 2026-07-19 by E1-LaneA3, DD-20260719-160: it now exports one; see 10d. Left as written, per the standing rule.]
   (`crossBlockArmProgramAt_runsTo`, `E1CrossBlockArm.lean:1199`, deliberately
   per its header at `:1143`). Every register fact the rank and output stages
   need must cross it, and nothing entitles a caller to that. **This is the
   next thing to build** — its own header says the fix is a fifth conjunct on
   `hInterior`, and `interiorDispatch_preserves_closeLeg`
   (`E1InteriorDispatchCompose.lean:1240`) already proves that conjunct for
   the canonical interior, so the pieces are present.
2. **The cross-block arm's interior object is not reconciled with the
   route's.** `crossBlockArmSpec_eq` (`E1CrossBlockArm.lean:181`) yields the
   interior as `if leftBlock + 1 < rightBlock then … else pure none`; but
   `crossBlockArm_withCanonicalInterior_runsTo` produces
   `⟨dispatchRouteValue …, dispatchEvents …⟩`. **No theorem identifies them.**
   `interiorRangeMin_of_cross` (`E1InteriorDispatch.lean:516`) and
   `canonicalBlockSize_eq_layoutBlockSize`
   (`E1InteriorDispatchCompose.lean:1151`) are the relevant pieces; note the
   two sides also spell the block size differently (Raw vs layout), which is
   what `canonicalBlockSize_eq_layoutBlockSize` exists to bridge.

**Validator.** `lake exe rmq_e1_machine_validate` PASS at **19 s wall clock**,
phase 5 `wholeQueryComparisonAvailable=false`. **It does not exercise one line
of this session's work** — the evidence is the in-tree executed simulations.
Its phase-5 TEXT is now stale in the opposite direction from §10b's note (it
says no definition composes the legs; one now does); the verdict `OPEN` is
still right, and the file belongs to the sibling category-algebra lane, so it
was not edited here.

**`#print axioms`** on all fourteen exported declarations, through a
scratchpad driver importing the three modules directly:
`propext, Classical.choice, Quot.sound` on thirteen, `propext` alone on
`lcaLeg_branches_exhaustive`. No `sorryAx` anywhere.

**What I would take next, in order.** The cross arm's preservation clause
(item 1 above — smallest, and it unblocks all register plumbing past the
close/LCA leg); then the interior object reconciliation (item 2); then the
select join's simulation, the rank leg and the output stage, which are
straightforward once 1 and 2 land. The `none`-branch discriminator at the
whole-query PROGRAM level is still owed and is NOT covered by
`lcaNone_impostor` (`E1WholeQueryCats.lean`), which is a FIXTURE-level
category-log discriminator — it establishes that the other three checks
cannot reject some impostor, not that this program's receipt cannot.

---

## 10d. Worklog - E1-LaneA3, 2026-07-19 (blocker 1 cleared; blocker 2 scoped)

Branch `claude/b1-b2-charged-fringe-tables`, base `c19e28c`. DD-IDs claimed
and WRITTEN into `DESIGN_DECISIONS.md`: **`160`, `161`**. Band `162-179` free.

**BLOCKER 1 IS CLEARED.** `crossBlockArmProgramAt_runsTo`
(`E1CrossBlockArm.lean:1199`) exports a third conjunct
`forall r, CloseLegUntouched r -> regsF r = regs r`; its `hInterior` gains a
matching fifth conjunct; `interiorDispatch_hInterior`
(`E1InteriorDispatchCompose.lean:1181`) supplies it; and
`closeLcaProgramAt_runsTo_cross` (`E1WholeQueryCloseLca.lean:258`) now
exports the same clause as its same-block twin at `:191`. Preservation across
the close/LCA leg is SYMMETRIC. Full `lake build RMQ` green.

**THE STRUCTURAL POINT THAT MADE IT A FIFTH CONJUNCT AND NOT A NEW LEMMA.**
`interiorDispatch_preserves_closeLeg` (`:1240`) already proved the fact and
its docstring explicitly declined to widen `hInterior` ("THE ADDITIONAL
EXPORT, NOT A FIFTH CONJUNCT"). That cannot be substituted for the conjunct:
preservation is a statement about the register file `hInterior`'s EXISTENTIAL
BINDS, so a standalone lemma is about a different witness. A sibling premise
has no way to name that witness. Widening was forced, not stylistic. Both are
now derived from ONE `interiorDispatchBlock_runsTo` invocation so they cannot
drift apart.

**SOUNDNESS WAS CHECKED AGAINST THE ARM'S WRITE SET, NOT A CONSUMER'S
OPERANDS** - the brief's warning was apt and the check is recorded in
DD-20260719-160 segment by segment. Adequacy is the separate question and was
already answered by two EVALUATED checks that existed:
`closeLegUntouched_at_query_operands` (`E1SameBlockArm.lean:87`) and
`closeLegUntouched_at_guard_scratch` (`:94`).

**ONE THING THE BAND DELIBERATELY EXCLUDES, worth knowing before someone
"fixes" it.** `rVal` (9) carries the SECOND select's answer and is NOT
protected. That is correct: the select join consumes `rVal` before the
close/LCA leg begins, so it has nothing to survive. The FIRST select's answer
is the one that must cross, and it is stashed in the guard's dead bank
`{3,4,5,6,7}` (DD-20260719-122), inside the band. Widening the band to cover
`9` would be carrying a decorative clause.

**BLOCKER 2 STANDS, AND THE BRIEF'S FRAMING OF IT NEEDED CORRECTION.** My
brief said of the two blockers that "the pieces already exist and this is
assembly, not research". That is TRUE of blocker 1 and FALSE of blocker 2.

The gap is on the TRACE side only. The VALUE side is already route-linked:
`dispatchRouteValue` (`E1InteriorDispatchCompose.lean:381`) is by definition a
`.value` projection of the route's own
`canonicalRelativeRmmInteriorRangeMinComputation`, and the
`twoSpanValue_*_eq_routeValue` ladder (`E1InteriorTwoSpan.lean:1085`, `:1123`)
links machine values to route values. But `dispatchEvents` (`:194`) is built
from `localLegEvents`/`globalLegEvents` (`:119`, `:152`), both built from
`twoSpanEvents` (`E1InteriorTwoSpan.lean:212`) - a FREESTANDING list of events
that is **never once equated to any computation's `.reads`**. Grepped: every
theorem mentioning `twoSpanEvents` supplies it as a `RunsTo` receipt argument
(`E1InteriorTwoSpan.lean:369`, `E1InteriorCombine.lean:460`, `:462`, `:1040`).
`concreteBPRelativeRmmInteriorRangeMinTraceResult...` appears in ZERO
`E1Interior*` files - the two name-sets are disjoint, so no theorem in the
tree can relate them.

**The missing ladder is three new lemmas**, each equating a machine event list
to `(...Computation ...).run ... |>.reads.map (TraceEvent.readWord segment)`:
at `spanEvents`, at `twoSpanEvents`, and at `dispatchEvents` level. Estimate:
a moderate proof, not a research problem, on three pieces of evidence.

* The precedent to copy is `minCandidateMachineTrace_eq_routeReads`
  (`E1InteriorMinCandidate.lean:1296`), which does exactly this one rung
  lower, resting on `:1172`, `:1210`, `:1273`. Its proof is one `rw` chain
  distributing `List.map_append`.
* The route side already decomposes at COMPUTATION level, not value level:
  `interiorRangeMin_of_count_zero` (`E1InteriorDispatch.lean:456`) through
  `interiorRangeMin_of_cross` (`:516`) are full computation equalities, so
  `.reads` follows by congruence, and their five guards are the SAME
  expressions `dispatchEvents` branches on, in the same order.
* The target unfolds to the right shape: the route object is
  `flatStoreExecutionTraceResultAtSegment ...`, whose `trace` is literally
  `execution.reads.map fun read => TraceEvent.readWord segment read.1 read.2`.

**Two cautions for whoever takes it.** (1) Budget a segment/store
reconciliation: the machine side is fixed at
`(canonicalSummaryLayout shape).segment` with
`concreteBPNativeSuccinctRMQGlobalReadStore shape`, while the route object is
parametric in `segments.canonicalComponent` and `store`. (2) The `spanEvents`
rung's `none` arm will be TRUE BUT LOAD-FREE: `spanNoneArm_traces_empty`
(`E1InteriorSpanBlock.lean:553`) already records that the receipt is formally
incapable of separating the `none`-arm impostor there. It buys shape, not
discrimination.

**A THIRD FINDING, and the one most likely to cost the next lane a session:
THE COMPOSED VALID PATH FALLS THROUGH INTO THE `none` WRITER.**
DD-20260719-162, pinned by `wholeQueryValidPath_exit_is_invalidExit`
(`E1WholeQueryProgram.lean:375`) and `wholeQueryValidPath_falls_into_noneWriter`
(`:384`). `closeLcaExit 827 = 5580` and `invalidExitBlock` sits at
`8 + 5572 = 5580` - the SAME address - so the valid path falls into
`.const regOut 0; .halt`. The program as composed would answer `none` for every
valid query. Nothing proved is wrong; the hazard is to whoever assumes the
remainder is "compose the executed legs". Full reasoning in DESIGN_DECISIONS.

**NOT ATTEMPTED, AND WHY.** The three agreement obligations and
`WholeQueryMachineAgrees` (`E1WholeQueryPublic.lean:114`) were not reached.
Beyond blocker 2 they need the select join's simulation, and an OUTPUT STAGE
that does not exist in the tree at all - `WholeQueryMachineAgrees` requires
`final.halted = true` and `decodePacket (final.regs regOut) = ...`, and
`wholeQueryValidPathThroughLca` (`E1WholeQueryProgram.lean:155`) currently
ends at the close/LCA leg's exit with no `regOut` write and no halt. That is a
new stage, not a composition step. Nothing was weakened to make anything
close.

**The `none`-branch discriminator at PROGRAM level is still owed**, and my
predecessor's characterisation of it is confirmed: `lcaNone_impostor`
(`E1WholeQueryCats.lean`) is a FIXTURE-level discriminator. One observation to
carry forward, from the governing rule that a receipt's power over a
skipped-code defect is exactly whether the skipped code reads: on a
`selectNone` branch the skipped code is `closeLcaProgramAt` - 4753
instructions that unquestionably read - so at the REAL BLOCK the receipt is
NOT blind to a spurious close/LCA leg, unlike at the fixture, where
`fixtureStageCats` makes it read-free. The fixture's blindness is therefore
STRICTLY WIDER than the block's, and a program-level discriminator should say
so rather than inherit the fixture's statement. I did not build it.

**Validator.** `lake exe rmq_e1_machine_validate` PASS at **13 s wall clock**,
phase 5 `wholeQueryComparisonAvailable=false`, verdict `OPEN`. It does not
exercise this session's work. Its phase-5 TEXT remains stale in the direction
10c recorded (it says "no definition composes them into one runnable query
program"; one does) - the file is the sibling cost-algebra lane's, so it was
NOT edited here. Its citation `interiorDispatch_hInterior:1171` is also now
stale (`:1181`); likewise reported, not edited.

**`#print axioms`**, scratchpad driver importing the four modules directly:
`propext, Classical.choice, Quot.sound` on all six of
`crossBlockArmProgramAt_runsTo`, `interiorDispatch_hInterior`,
`interiorDispatch_preserves_closeLeg`,
`crossBlockArm_withCanonicalInterior_runsTo`,
`closeLcaProgramAt_runsTo_cross`, `closeLcaProgramAt_runsTo_same`. No
`sorryAx`.

**Citations repaired.** Widening the header moved
`crossBlockArmProgramAt_runsTo` from `:1181` to `:1199`; eight in-tree
citations were updated across seven files, and two notes stale in CONTENT (not
merely line number) were rewritten: `E1InteriorDispatch.lean:403` ("It is NOT
a fifth conjunct ... and never has") and `E1WholeQueryProgram.lean`'s
two-blocker scope note.

---

## 10e. Worklog - E1-LaneA5, 2026-07-19 (layout defect repaired; three branches executed)

Branch `claude/b1-b2-charged-fringe-tables`, base `86cbbb6`. DD-IDs claimed
and WRITTEN into `DESIGN_DECISIONS.md`: **`180`, `181`, `182`, `183`, `184`**.
Band `185-199` free. Full `lake build RMQ` green at every commit.

**ITEM 1 IS CLOSED: THE LAYOUT DEFECT IS REPAIRED, AND THE REPAIR IS
EXECUTED.**

`wholeQueryOutputStage` (`E1WholeQueryProgram.lean`), 64 instructions at the
close/LCA leg's own exit `5580`:

    5580   rank setup      2    rPos := fRes + 1
    5582   rank leg       60    `rankCloseBlock` at the canonical rank data
    5642   packet write    2    regOut := rVal ; halt
    5644   `invalidExitBlock`, ONE PAST the halt

The repaired valid path `wholeQueryValidPath` is 5636 instructions, so the
`none` writer moves from `5580` to `5644`.

**THE BRIEF'S DESCRIPTION OF THE STAGE WAS UNDER-SPECIFIED, AND THAT IS THE
FINDING MOST WORTH CARRYING FORWARD.** DD-20260719-162 and my own brief both
called for a stage that "decodes `fRes` into `regOut`'s packet and halts".
That stage halts at the right address CARRYING THE WRONG NUMBER: the route's
`.full` value is `some ((rank ... (answerClose + 1)).value - 1)`
(`E1RouteDecomposition.lean:330`), so a RANK LEG sits between the close/LCA
leg's answer and the output packet. `fRes` is a close POSITION; the answer is
an INDEX. Four instructions would have produced a program that halts, answers
`some`, passes every layout check, and is wrong. DD-20260719-180.

**`regOut := rVal` carries NO shift instruction, and that is derived, not
lucky.** The packet convention is `decodePacket (v + 1) = some v` and the
route's value is `rank.value - 1`; the two shifts cancel. No increment or
decrement appears in the stage.

**THE REPAIR IS CONFIRMED AT THREE LEVELS, THE THIRD BY EXECUTION**
(DD-20260719-183). A layout argument is not evidence here, three address
coincidences over:

1. `wholeQueryValidPath_exit_is_not_invalidExit` (`E1WholeQueryProgram.lean:884`) - `5580` against
   `5644`.
2. `wholeQueryProgram_at_closeLcaExit_is_not_noneWriter`
   (`E1WholeQueryProgram.lean:897`) - the
   program holds `.const rPos 1` at `5580`, not `invalidExitBlock`'s first
   instruction. An address argument alone does NOT settle this: two different
   blocks can begin at two different addresses and both be `none` writers.
3. `wholeQueryValidPath_does_not_reach_noneWriter`
   (`E1WholeQueryProgram.lean:927`) - from `5580` the
   program RUNS to a halted state at pc `5643`. `RunsTo` is exact-fuel
   (`E1MachineCalculus.lean:96`), so every step is enumerated and none is at
   `5644`.

The two theorems pinning the DEFECT are RETAINED and re-documented, not
deleted: `wholeQueryValidPath_exit_is_invalidExit` (`E1WholeQueryProgram.lean:418`)
and `wholeQueryValidPath_falls_into_noneWriter`
(`E1WholeQueryProgram.lean:435`) are still true of
`wholeQueryValidPathThroughLca`, which is still the path THROUGH the leg. Both
the defect and its repair are now pinned by theorems that break under a layout
drift.

**THREE OF THE ROUTE'S FOUR BRANCHES ARE EXECUTED END TO END, FROM
`initialState` TO A HALTED STATE.**

* `wholeQueryProgram_runsTo_sameBlock` (`E1WholeQueryProgram.lean:1034`) - the `.full` branch on the
  SAME-BLOCK arm. Guard, both selects, join, close/LCA same-block arm, rank
  leg, halt: ONE `RunsTo` to `<regsF, 5643, true>`, receipt positionally the
  concatenation of the four legs' route receipts, `regOut` the rank leg's
  value. Universally quantified in shape, `n` and the range - no sampling, no
  readiness guard, no size threshold.
* `wholeQueryProgram_runsTo_leftSelectNone`
  (`E1WholeQueryProgram.lean:1169`) and
  `_rightSelectNone` (`E1WholeQueryProgram.lean:1252`) - both `none` branches, against the route's OWN
  objects: receipt `= wholeQueryBranchTrace shape left right ...` and
  `decodePacket regOut = wholeQueryBranchValue shape ...`, halting at `5645`.

**THE SELECT JOIN IS SIMULATED ON ALL THREE OF ITS EXITS** -
`selectJoin_runsTo_hit` (`E1WholeQueryProgram.lean:692`), `_leftMiss`, `_rightMiss`. It was defined by
E1-LaneA1 and never executed.

**TWO PREMISE/CITATION DEFECTS FOUND BY TRYING TO INSTANTIATE AT THE REAL
TARGET.**

1. **DD-20260719-181.** `wholeQuerySelectPrefix_runsTo`'s `hguard` was pinned
   to `guardBlock n (8 + (813 : Nat))` - branch target `821`. The skeleton
   builds its guard as `guardBlock n (8 + validPath.length)`
   (`E1QueryProgram.lean:136`), which for the repaired path is
   `guardBlock n 5644`. **The premise was UNSATISFIABLE at the intended
   instantiation** - the rule-1 failure. `guard_accept_of_valid`
   (`E1QueryProgram.lean:608`) was ALREADY universal in `invalidBase` (the
   accepting path never reads the target), so the specialisation bought
   nothing. Generalised; no proof changed.
2. **DD-20260719-182.** `lcaLeg_of_sameBlock`'s docstring cited
   `lcaLeg_sameBlock_rankSeed_eq` "below". Grepped: **the name occurred
   exactly once in the whole tree - in that sentence.** The lemma did not
   exist. It is now supplied (`E1WholeQueryLcaLeg.lean:132`), as a FUNCTION
   equality because the seed enters the arm partially applied.

`wholeQuerySelectPrefix_runsTo` also now exports `regZero = 0` and
`regT2 = 1` at pc `821`, the two operands the join's tests and `sub`s consume.

**THE `none`-BRANCH DISCRIMINATOR: WHAT IS NOW ESTABLISHED AND WHAT IS NOT**
(DD-20260719-184). The value clause degenerates to `none = none` and rejects
no impostor. What is NOT degenerate: the receipt equality is POSITIONAL on the
WHOLE receipt and pinned to exactly `selL ++ selR` with nothing appended,
while the code the machine skips is `closeLcaProgramAt` - 4753 instructions
whose arms read memory on every path. **So at the REAL BLOCK the receipt is
NOT blind to a spurious close/LCA leg.** That is STRICTLY NARROWER blindness
than the fixture's: at `lcaNone_impostor` (`E1WholeQueryCats.lean`) the
skipped stage is `fixtureStageCats`, which is READ-FREE, so the receipt is
formally powerless there. **The fixture's blindness is WIDER; the block's is
narrower**, and a program-level discriminator must not inherit the fixture's
statement. Category accounting still has no discriminator anywhere, and this
lane did not change that.

**BLOCKER 2 WAS NOT ATTEMPTED, AND THE REASON IS SCOPE, NOT DISAGREEMENT.**
E1-LaneA3's scoping in 10d was re-checked and stands: `twoSpanEvents`
(`E1InteriorTwoSpan.lean:212`) is still never equated to any computation's
`.reads`. The three ladder lemmas plus the segment/store reconciliation
remain the next thing to build, and the cross arm's `.full` branch cannot be
stated against the route's receipt until they land. `minCandidateMachineTrace_eq_routeReads`
(`E1InteriorMinCandidate.lean:1296`) is still the precedent to copy.

**`WholeQueryMachineAgrees` IS NOT DISCHARGED.** What remains, named:

* the `.full` branch on the CROSS arm (blocked on blocker 2);
* the same-block run's receipt is in the ARM's vocabulary, not
  `wholeQueryBranchTrace`'s. Both bridging rewrites now exist
  (`lcaLeg_of_sameBlock` `E1WholeQueryLcaLeg.lean:64`, and
  `lcaLeg_sameBlock_rankSeed_eq` `E1WholeQueryLcaLeg.lean:132`); the bridge itself is not written;
* **the `.lcaNone` branch has NO machine stage at all, and its status is
  genuinely unsettled.** The composed leg's arm theorems conclude
  `some (regsF fRes) = arm.value`, so on this composition the leg's value is
  always `some`. Whether `.lcaNone` is therefore unreachable at these arms, or
  whether a dispatch stage is owed, was NOT determined here and should not be
  assumed either way by the next lane;
* category accounting across all four branches.

**Validator.** `lake build rmq_e1_machine_validate` green;
`lake exe rmq_e1_machine_validate` **PASS at 17.2 s wall clock**, phase 5
`wholeQueryComparisonAvailable=false`, verdict `OPEN`. Modeled steps
(reproducible): dispatch 2430, leg 30343, select 8273, compose 9222, merge
431, arm 6276. Wall-clock figures in the output are host-specific and are NOT
evidence. **It does not exercise one line of this session's work** - the
evidence is the in-tree executed simulations. Its phase-5 TEXT is now stale in
the SAME direction 10c and 10d recorded, and one notch worse: it says "no
definition composes them into one runnable query program", and one now does
AND is executed end to end on three branches. The file is the sibling
cost-algebra lane's, so it was NOT edited here.

**`#print axioms`**, scratchpad driver importing the two modules directly, 19
declarations: `propext, Classical.choice, Quot.sound` on eighteen, and
`propext, Quot.sound` on `packet_of_decodePacket_eq_some`. **No `sorryAx`
anywhere.** No `sorry`/`admit`/`axiom`/`native_decide`/`partial`/`unsafe`/
`implemented_by`/Mathlib in either file.

**Citations repaired.** The output stage moved the two pinned defect theorems
from `:375`/`:384` to `:418`/`:435`, and `wholeQuerySelectPrefix_runsTo` from
`:250` to `:268`; the rank-seed lemma's docstring moved
`lcaLeg_of_sameBlock` from `:57` to `:64` and `lcaLeg_branches_exhaustive`
from `:110` to `:149`. All four repaired in this file and in
`DESIGN_DECISIONS.md`, and every citation this section makes was verified
against the declaration it names after the edits.

---

## 10f. Worklog - E1-LaneA6, 2026-07-19 (blocker 2 cleared; `.lcaNone` settled; two obstructions reported)

Branch `claude/b1-b2-charged-fringe-tables`, base `a15ef15`. DD-IDs claimed
and WRITTEN into `DESIGN_DECISIONS.md`: **`200` through `206`**. Band
`207-219` free. Full `lake build RMQ` green at every commit.

**BLOCKER 2 IS CLEARED. THE TRACE LADDER EXISTS AND THE INTERIOR IS NO
LONGER A HOLE.**

New module `E1InteriorTraceLadder.lean`, eight rungs, no edit to any of the
four interior modules:

    rung 0  geomEvents_eq_readComputation_reads         (:85)   generic
    rung 1  legEvents_eq_routeReads                     (:111)  the precedent
    rung 2  spanEvents_localSpan_eq_routeReads          (:137)
            spanEvents_globalSpan_eq_routeReads         (:185)
    rung 3  twoSpanEvents_local_eq_routeReads           (:238)
            twoSpanEvents_global_eq_routeReads          (:285)
    rung 4  localLegEvents_eq_routeReads                (:336)
            globalLegEvents_eq_routeReads               (:348)
    rung 5  adjacentArm_reads_eq                        (:367)
            leftMiddleArm_reads_eq                      (:390)
            crossArm_reads_eq                           (:413)
    rung 6  dispatchEvents_eq_routeReads                (:465)
    rung 7  canonicalInterior_traceResult_eq_dispatch   (:549)

E1-LaneA3's scoping was RE-GREPPED before any budgeting and stood:
`twoSpanEvents` (`E1InteriorTwoSpan.lean:212`) was never once equated to a
computation's `.reads`. Every equation is positional -- both sides are lists
-- and hypothesis-free except rung 0's three alignment premises, each `rfl`
at every instantiation. DD-20260719-200.

**THE LADDER MIRRORS THE VALUE LADDER AND REUSES ITS OWN CELL LEMMAS.** The
trace rungs dispatch on `cellOpt_spanCell_localSpan`
(`E1InteriorSpanBlock.lean:702`) and `cellOpt_levelCell_localLevel`
(`E1InteriorTwoSpan.lean:981`) -- the SAME lemmas the value rungs dispatch
on -- so the two sides cannot drift.

**RUNG 6 NEEDED NO TRACE ARGUMENT, AND THAT IS WHY ALL THE WORK WAS BELOW
IT.** `dispatchEvents` and `canonicalRelativeRmmInteriorRangeMinComputation`
(`InteriorDirectory.lean:2444`) are the same five-way `if` on the same
conditions, and `interiorRangeMin_of_count_zero`
(`E1InteriorDispatch.lean:456`) through `_of_cross` (`:516`) are FULL
COMPUTATION equalities, so `.reads` follows by congruence.

**THE `count = 0` ARM IS THE ONE WITH TEETH.** The route is
`FlatStoreComputation.pure none` with an EMPTY read log and the machine's arm
emits nothing, so the receipt DOES separate the correct layout from an
unterminated one falling through into `twoSpanBlock`'s unconditional head
level read. `dispatchEvents`' docstring asserted this; it is now an equation.

**THE SEGMENT/STORE RECONCILIATION THE LAST TWO BRIEFS BUDGETED DOES NOT
EXIST, AND THAT IS A FINDING RATHER THAN A SAVING** (DD-20260719-202).
`(canonicalSummaryLayout shape).segment` is
`E1InteriorStoreConcrete.interiorSegment` (`E1InteriorSummaryGroup.lean:469`),
and `interiorSegment` is an `abbrev` for
`concreteBPNativeInteriorTraceSegments.canonicalComponent`
(`E1InteriorStoreConcrete.lean:67`). The two spellings are the SAME TERM; the
machine side was written against the segment record from the start. Recorded
because a lane that assumed the crossing was owed might have built a bridge
and "used" it, hiding that nothing was crossed.

**OBLIGATION 2 OF `E1WholeQueryProgram.lean`'s SCOPE NOTE IS CLOSED**
(DD-20260719-203), and the scope note's own prediction was exactly right: the
gap was on the TRACE side only. `…AllSizeStructuralWithStore`
(`ConcreteDirectoryRAMStoreParam.lean:3639`) is DEFINED as
`flatStoreExecutionTraceResultAtSegment _ (computation.run _)`, so its
`.value` is `dispatchRouteValue`'s own definition
(`E1InteriorDispatchCompose.lean:381`) by `rfl`. Only `.trace` needed proof.

**`.lcaNone` IS SETTLED ON THE SAME-BLOCK ARM, BY PROOF, WITH A WITNESS**
(DD-20260719-204). New module `E1WholeQueryLcaNone.lean`:
`sameBlockLcaLeg_value_eq_some` (`:86`),
`wholeQueryBranch_eq_full_of_sameBlock` (`:117`),
`wholeQueryBranch_ne_lcaNone_of_sameBlock` (`:145`),
`lcaNone_is_a_real_branch` (`:177`).

**THE PREVIOUS LANE'S PRESUPPOSITION WORRY WAS THE RIGHT WORRY AND IT DOES
NOT APPLY.** It observed that an arm theorem stated as
`some (regsF fRes) = arm.value` presupposes someness. Every hypothesis on the
producing chain was therefore inspected --
`closeLcaProgramAt_runsTo_same` (`E1WholeQueryCloseLca.lean:191`),
`sameBlockLegProgramAt_runsTo_canonical` (`E1SameBlockLeg.lean:805`),
`sameBlockLeg_runsTo_canonical` (`:453`). **NOT ONE IS `Option`-SHAPED.** No
`arm.value = some x`, no `isSome`. The someness is DERIVED by execution.

**THE WITNESS IS FOUND AT THE TARGET, NOT CONSTRUCTED FOR THE PREMISE.** No
hosting or register file is manufactured; the proof consumes
`wholeQueryProgram_runsTo_sameBlock` (`E1WholeQueryProgram.lean:1034`),
already proven at the real program from `initialState`. `n := right` makes
`hbound` `Nat.le_refl`, so neither `n` nor `hbound` appears in the statements.

**SCOPE: THE SAME-BLOCK ARM ONLY.** Cross-arm `.lcaNone` needs the route's
`bpChunkedCrossBlockClose…` identified with `crossBlockArmSpec`'s value;
DD-20260719-203 supplies the INTERIOR half of that crossing but not the ARM
half. **It must not be assumed either way.**

**THE SAME-BLOCK RECEIPT BRIDGE IS WRITTEN.** New module
`E1WholeQuerySameBlockRoute.lean`:
`wholeQueryBranchTrace_full_sameBlock_machineObjects` (`:61`) and
`wholeQueryProgram_runsTo_sameBlock_routeReceipt` (`:103`) -- the branch
executed from `initialState` to a halted state with its receipt stated as
`wholeQueryBranchTrace shape left right (.full cl cr answerClose)`, the
route's own object. The branch is DERIVED, not assumed: the first conjunct
rests on the `.lcaNone` unreachability proof.

**TWO OBSTRUCTIONS ARE REPORTED RATHER THAN FORCED. NEITHER SIDE OF ANY
THEOREM WAS WEAKENED TO MAKE A COMPOSITION CLOSE.**

**1. `WholeQueryMachineAgrees` IS NOT DISCHARGEABLE TODAY** (DD-20260719-205).
`decodePacket` (`E1QueryProgram.lean:93`) is
`if v = 0 then none else some (v - 1)`; the route's `.full` value
(`E1RouteDecomposition.lean:330`) is `some (rank.value - 1)`
UNCONDITIONALLY; and `0 - 1 = 0` in `Nat`. **The two disagree exactly when
the rank leg's value is `0`** -- machine `none`, route `some 0`. That is
`WholeQueryMachineAgrees`' third clause (`E1WholeQueryPublic.lean:124`), so
the `.full` branch cannot reach it. The two select-miss branches are
UNAFFECTED: they write `regOut := 0` against route `none`, and
`decodePacket 0 = none` agrees.

This was ALREADY NAMED in the tree and is confirmed, not discovered:
`wholeQueryOutput_agrees_with_noneWriter_iff` (`E1WholeQueryProgram.lean:972`)
states the condition and says "This lane does not prove that never happens."
The output stage's docstring (`:458`) claims "the two shifts cancel … not a
coincidence to be checked at runtime"; **that is valid only on
`rank.value ≥ 1`** and is the overreach DD-20260719-205 corrects.

So `wholeQueryProgram_runsTo_sameBlock_routeReceipt`'s value clause is stated
in the MACHINE's form, `regsF regOut = rank.value`. The side condition was NOT
carried as a hypothesis: a premise `rank.value ≠ 0` would owe a witness of
satisfiability at the intended instantiation (rule 1) and this lane cannot
supply one.

**THE DISCHARGE EXISTS ONE LAYER DOWN AND IS NAMED FOR THE NEXT LANE.**
`bpCloseOfInorder?_rankFalse_succ` (`BPShape.lean:156`) gives
`rankPrefix false shape.bpCode (pos + 1) = idx + 1`; a worked chain from it up
to a trace result's `.value` is at `BPNavigationRAM.lean:1969`; and
`concreteBPNativeRankCloseWordTraceResultAtSegment_canonical_eq`
(`SuccinctFinalRAM.lean:1550`) transfers across bases. **The real work is
obtaining `bpCloseOfInorder? shape idx = some answerClose` at the machine
site** -- `wholeQueryProgram_runsTo_sameBlock` produces `answerClose` only
through `some answerClose = (sameBlockArm …).value`, with no link to
`bpCloseOfInorder?`. The read-failure fallback
(`ChargedRankSelectLeafTrace.lean:181`) returns `pure 0`, so a SECOND route to
`0` exists and must be ruled out rather than assumed away.

**2. CATEGORY ACCOUNTING CANNOT BE DISCHARGED WITH THE CURRENT STAGE RECORD**
(DD-20260719-206). `wholeQueryBranchCats` (`E1WholeQueryCats.lean:98`) puts
the two select legs ADJACENT -- `S.prologue ++ S.select left ++
S.select (right - 1) ++ …` -- while the machine charges
`guardAcceptCats ++ [registerWrite] ++ selectCloseCats … left ++
[registerWrite, arithmetic] ++ selectCloseCats … (right - 1) ++ …`.
**The two pre-select connectives are ASYMMETRIC** and `S.select` is ONE
function applied at two positions, so it must carry the between-selects
connective as a prefix, a suffix, or a split. `Category`'s constructors are
pairwise distinct (`E1Machine.lean:107`) and `guardAcceptCats`
(`E1QueryProgram.lean:584`) ends in `.branch`, so all three splits clash --
the case analysis is in DD-20260719-206.

The record needs a field for the connective. **That changes
`WholeQueryStageCats`, hence `WholeQueryMachineAgrees` and the signature
`programSkeleton_valid_matches_public` (`E1WholeQueryPublic.lean:140`)
consumes -- a public-facing surface, so it belongs to the coordinator.**
Fabricating an `S` that "worked" by folding the connective into an opaque
`select` would be a category function fitted to the machine, which §11 F
forbids. The older finding stands unchanged: `catLog` appears ZERO times in
the validator.

**WHAT REMAINS FOR `WholeQueryMachineAgrees`, NAMED.**

* the `.full` branch on the CROSS arm -- the interior is now reconciled
  (rung 7), but the ARM-level identification of `crossBlockArmSpec`'s value
  with the route's `bpChunkedCrossBlockClose…` is not written;
* the `decodePacket` obligation above;
* the stage-record change above.

**Validator.** `lake build rmq_e1_machine_validate` green;
`lake exe rmq_e1_machine_validate` **PASS at 14.194 s wall clock**, phase 5
`wholeQueryComparisonAvailable=false`, verdict `OPEN`. Modeled steps
(reproducible, and unchanged from 10e): dispatch 2430, leg 30343, select 8273,
compose 9222, composeMax 585, legMutant 30060, merge 431, arm 6276.
Wall-clock figures are host-specific and are NOT evidence. **It does not
exercise one line of this session's work** -- the evidence is the in-tree
proofs. Its phase-5 TEXT is stale in the SAME direction 10c, 10d and 10e
recorded. The file is the sibling cost-algebra lane's and was NOT edited here.

**`#print axioms`**, scratchpad driver importing the three new modules
directly, 19 declarations: `propext, Classical.choice, Quot.sound` on all
nineteen. **No `sorryAx` anywhere.** No
`sorry`/`admit`/`axiom`/`native_decide`/`partial`/`unsafe`/`implemented_by`/
Mathlib/`maxHeartbeats`/`by_contra`/`norm_num` in any of the three files.

**Citations.** Every citation this section makes was verified against the
declaration it names AFTER the edits. No existing line number moved: all
three modules are NEW files and the only edit to an existing tree file is
three added `import` lines in `RMQ.lean`.

---

## 10g. Worklog - E1-LaneA8, 2026-07-19 (both obstructions discharged; the whole-query program is complete)

Branch `claude/b1-b2-charged-fringe-tables`, base `b8766c9`. DD-IDs claimed and
WRITTEN into `DESIGN_DECISIONS.md`: **`207`, `208`, `209`**. Band `210-219`
free. Full `lake build RMQ` green at every commit.

**BOTH OBSTRUCTIONS 10f REPORTED ARE DISCHARGED, AND ALL FOUR ROUTE BRANCHES
NOW RUN FROM `initialState` TO HALTED WITH RECEIPT, CHARGE AND VALUE STATED
AGAINST THE ROUTE'S OWN OBJECTS.** `WholeQueryMachineAgrees` is proved and the
public `List Int` corollary lands.

**THE VALUE DISAGREEMENT IS VACUOUS, BY PROOF, NEITHER SIDE WEAKENED**
(DD-20260719-207). New module `E1WholeQueryRankPositive.lean`. 10f's analysis
was confirmed exactly, not retracted: the two sides disagree exactly at
`rank.value = 0`. What is new is that the point is UNREACHABLE.
`decodePacket` keeps its guard, `wholeQueryBranchValue` keeps its
unconditional `- 1`, and **no hypothesis `rank.value != 0` is carried
anywhere.**

* `rankCloseTrace_value_eq_rankPrefix` (`:72`) -- the rank leg's TRACE value IS
  the `rankPrefix`, unconditionally, at every segment base. **This closes the
  read-failure fallback** (`ChargedRankSelectLeafTrace.lean:181`) that 10f
  correctly flagged as a second route to `0`: `refines_interpretedCosted`
  (`SuccinctFinalRAM.lean:1516`) is unconditional and base-generic because the
  store is definitionally the seed store, so the reads cannot miss.
* **That composition existed only inside proof bodies**
  (`BPNavigationRAM.lean:1969`, `SuccinctFinalRAM.lean:9186`); a grep for
  `.value = Succinct.rankPrefix` returned ZERO matches tree-wide. Sixth time a
  brief budgeted work a definition already did.
* `wholeQueryBranch_eq_full_of_bounds` (`:152`) supplies the semantic link
  CONSTRUCTIVELY -- there is no inversion lemma, only the four introduction
  lemmas at `E1RouteDecomposition.lean:241-288`, so rather than invert, it
  PROVES the branch is `.full` with `bpCloseOfInorder?` closes from
  `left < right` and `right <= shape.size` alone. **Strictly stronger than
  inversion: it is also the satisfiability witness that `.full` is reached,
  which this layer did not have.** Witness FOUND at the target, not built for
  the premise.
* `bpCloseOfInorder?_rankFalse_succ` (`BPShape.lean:156`) then makes the value
  a SUCCESSOR. `decodePacket_rankClose_eq_wholeQueryRouteValue_of_bounds`
  (`:209`) is the vacuity witness.

**THE BOUNDS ARE NOT A WEAKENING.** `left < right` and `right <= shape.size`
are exactly `ValidRange` (`Spec.lean:14`) through the shape -- the hypothesis
the public corollary already carries.

**THE STAGE RECORD GAINED EXPLICIT CONNECTIVES, PER THE COORDINATOR RULING**
(DD-20260719-208). `selectJoin` and `rankJoin` are named stages, NOT folded
into `select` or `lcaRun`, because each of those occurs TWICE and folding
would give one function two meanings. `prologue` absorbs the opening
`registerWrite` because it occurs ONCE -- that distinction is the whole
argument.

**A SECOND CLASH, NOT REACHED BY DD-20260719-206.** The old record used ONE
`lcaSkipped` on BOTH select-miss branches, making those two cases **the same
term** -- separable by no `S` whatsoever. The machine separates them: it tests
the select results in order, so left-miss charges `[comparison, branch]`
(`E1WholeQueryProgram.lean:1169`) and right-miss charges it twice (`:1252`).
Field split; `selectNone_branches_separable` (`E1WholeQueryCats.lean:424`)
states a proposition that was previously **false by `rfl`**.

**THE FOURTH BRANCH WAS A COMPOSITION, NOT A LANE** (DD-20260719-209). New
module `E1WholeQueryCrossRoute.lean`. `closeLcaProgramAt_runsTo_cross`
(`E1WholeQueryCloseLca.lean:258`) already existed as the exact twin of its
same-block sibling, and the same-block whole-query proof consumes its twin in
ONE `obtain`, so `wholeQueryProgram_runsTo_crossBlock` (`:99`) is that proof
with one lemma swapped. **Two briefs budgeted this as a lane.**

**THE ONE PLACE IT COULD HAVE HIDDEN A DEFECT WAS EXECUTED, NOT REASONED
ABOUT.** The machine's cross arm carries its interior UNGUARDED; the route
guards it, `if leftBlock + 1 < rightBlock then ... else pure none`
(`ChargedFringeTrace.lean:940`). They agree only because the guard COLLAPSES:
`count = 0` and that arm is `pure none` with an EMPTY read log.
`dispatchTraceResult_of_not_lt` (`:175`) proves it. **Had that arm read
anything the receipts would differ and the equation would have failed there.**
The block-index spellings were likewise grepped, not assumed:
`blockOfClose bs c` is `c / bs` (`BlockLocal.lean:864`) and
`(canonicalLayout shape).blockSize` is
`canonicalBPRelativeSummaryBlockSizeRaw shape` (`RelativeSummary.lean:1278`).

**`crossArmObject_eq_routeLcaLeg` (`:208`) IS THE IDENTIFICATION 10f NAMED AS
UNWRITTEN** -- the two objects are ONE TERM on the cross arm, value AND
receipt.

**CATEGORY ACCOUNTING RUNS THE RIGHT WAY ROUND.** New module
`E1WholeQueryMachineCats.lean`. `wholeQueryBranchCats` is NOT edited by this
work; an `S` cannot make a false control structure true. Where the two
disagreed the RECORD changed under a ruling, never an `S`. `lcaRunCats` is a
PARAMETER there, following `crossBlockArmCats`' precedent.

**THE SELECT-MISS BRANCHES ARE UNREACHABLE ON A VALID RANGE.**
`wholeQueryBranch_ne_selectNone_of_bounds`
(`E1WholeQueryRankPositive.lean:307`): `bpCloseOfInorder?` is total below the
shape's size (`BPShape.lean:57`), so the selects cannot miss and the route
ALWAYS takes `.full`. Their run theorems therefore describe behaviour OUTSIDE
`ValidRange` -- worth knowing, not previously stated.

**THE AGREEMENT.** New module `E1WholeQueryAgreement.lean`.
`wholeQueryLcaRunCats` (`:39`) dispatches on the route's OWN arm selector --
the same condition `lcaCloseTraceResultWithRankSeedAllSizeStructural`
(`ChargedFringeWiring.lean:50`) dispatches on -- because
`WholeQueryMachineAgrees` fixes one `S` while the two arms charge differently.
`wholeQueryMachineAgrees_of_bounds` (`:64`) and
`programSkeleton_valid_matches_public_at_machineS` (`:111`).

**Validator.** `lake build rmq_e1_machine_validate` green; `lake exe
rmq_e1_machine_validate` **PASS at 8.081 s wall clock**, phase 5
`wholeQueryComparisonAvailable=false`, verdict `OPEN`. Modeled steps
(reproducible, UNCHANGED from 10e/10f): dispatch 2430, leg 30343, select 8273,
compose 9222, composeMax 585, legMutant 30060, merge 431, arm 6276. Wall-clock
is host-specific and is NOT evidence. **Its phase-5 TEXT is now MORE stale than
10c-10f recorded**: it says no definition composes the legs into one runnable
query program, which `wholeQueryProgram` (`E1WholeQueryProgram.lean:876`) and
this session's four executed branches falsify. The file is the sibling
cost-algebra lane's and was NOT edited here.

**`#print axioms`**, scratchpad driver importing the five new/changed modules
directly, 20 declarations: `propext, Classical.choice, Quot.sound` on all
except `selectNone_branches_separable` and `fullCats_mentions_both_joins`,
which depend on NO axioms. **No `sorryAx` anywhere.** No
`sorry`/`admit`/`axiom`/`native_decide`/`partial`/`unsafe`/`implemented_by`/
Mathlib/`maxHeartbeats`/`by_contra`/`norm_num` in any new file.

**Citations.** Every citation this section makes was verified against the
declaration it names AFTER the edits; five in DD-20260719-209 and three in
DD-20260719-207/208 were off by 2-9 lines and were corrected. Four new files;
the only edits to existing tree files are `E1WholeQueryCats.lean` (the record)
and four added `import` lines in `RMQ.lean`.

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

---

## 12. Worklog — E1-LaneA2 (cost algebra), 2026-07-19

Branch `claude/e1-cost-algebra`, base `fd59487`. Commits `48a1ac6`,
`57ef6af` and this one. DD-IDs claimed and WRITTEN into
`DESIGN_DECISIONS.md`: **`140`, `141`, `142`, `143`**. Band `144-159`
remains free.

**BUILT.**

- **The `catCount`/`filter` bridge** — `catCount_eq_filter_length` and
  `catCount_le_of_filter_length_le` (`E1Machine.lean`, beside `catCount`'s
  own definition). §11 D's absence claim was CORRECT: zero hits.
- **The bridge EXERCISED, not merely stated** —
  `interiorChunkFold_readLog_le_eight` (`E1CostAlgebra.lean`, new module)
  carries `interiorChunkFoldCats_memoryRead_le_eight`, a `filter`-vocabulary
  block cap, to a bound on the MACHINE'S OWN RECEIPT LENGTH via
  `RunsTo.readLog_length_eq_memoryRead_count`, which produces a `catCount`.
- **Per-block charge bounds** — `chunkIters_le_eight`,
  `interiorChunkFoldCats_length` (the algebra, as an equation) and
  `interiorChunkFoldCats_length_le` (`<= 156 = 17 + 8*9 + 8*8 + 3`, derived,
  no size hypothesis).
- **`E1AmendedFamiliarMachineTarget`** (`E1AmendedTarget.lean`, new) with
  `amendedTarget_invalidGuard` (its invalid conjunct DISCHARGED outright)
  and `amendedTarget_of_wholeQueryAgreement` (the reduction: exactly what is
  still owed).
- **Validator phases 3j and 4i** — REQ-E1-05's guard skeleton executed on
  the three named invalid families plus VALID CONTROLS, and a
  shape-preserving mutation of the out-of-bounds branch.

**FIVE COORDINATOR/FILE CLAIMS CHECKED; FOUR HELD, ONE FAILED ON A COUNT.**

1. §11 D — no `catCount`/`filter` bridge anywhere. **HELD**, zero hits.
2. No `totalSteps` in the tree; the only `cats.length <= <literal>` is the
   guard's `<= 10`. **HELD** on both halves.
3. `E1AmendedFamiliarMachineTarget` absent. **HELD**, zero hits.
4. §11 E's four precision points about the refuted predecessor — third
   conjunct is the familiar-local-iteration lower bound; the witness is
   `e1R3CanonicalSameBlockInvocation_unbounded`; five categories, not six;
   `publicModeledCost` is an EQUALITY. **ALL FOUR HELD**, read at
   `7fe5b8b:RMQ/Core/SuccinctFinalSmallStep.lean:37016` and `:37046`.
5. "`programSkeleton` has no consumer outside its own two files."
   **FAILED ON THE COUNT.** Three files, and `E1WholeQueryPublic.lean`
   carries a real consumer, `programSkeleton_valid_matches_public` (`:140`).
   The residual the row names — the VALIDATOR — was genuinely absent, so the
   conclusion held and the work was right to do.

**A FINDING THAT CHANGED THE DELIVERABLE: the amended target Prop carries NO
width conjunct.** REQ-E1-07's evidence column asks for one, and both
spellings are unusable.
`ProgramFits (SuccinctRank.machineWordBits n) (programSkeleton n validPath)`
is FALSE at small `n` — `machineWordBits n = Nat.log2 n + 1`, so at `n = 4`
the bound is `2 ^ 3 = 8` while this construction's register file reaches
`152`. And `∀ n, ∃ w, ProgramFits w ...` is VACUOUS, since every finite
instruction list fits some width. The tree's own certificates resolve this by
taking `w` PARAMETRICALLY with side conditions
(`sameBlockLegProgramAt_fits`, `E1ProgramWidth.lean:57`, carries eleven), and
those cannot be collapsed into a Prop quantified over `xs left right`. Width
accounting stays as REQ-E1-02's row. DD-20260719-142, and it is documented in
the Prop's own docstring rather than left for a reader to notice.

**§11 B HELD AND WAS NEVER TESTED.** Every bound here is stated as `<=` per
the requirement's shape, but none of them passes through `machineWordBits` at
all — they count instructions, not bits — so `Nat.log2` was not an
obstruction and never came near one. `interiorChunkFoldCats_length` is left
as an EQUATION deliberately, being the algebra the `<=` derives from.

**THE TWO `33`s ARE KEPT APART AND NOTHING IS PROVED AGAINST EITHER.**
`E1CostAlgebra.lean`'s header separates the fringe-window cap inside
`endpointFringe = 4 + 33 = 37` from
`canonicalRelativeRmmPrincipledInteriorChargedTraceCost := 33`, and notes
`3 * rankClose = 33` as a third coincidence. The `8` this lane does prove is
the interior adapter's, not the fringe's. DD-20260719-141.

**One wrong guess, recorded because the rule caught it.** Mutant J's
rejection count was predicted `6` and is `5`: the fixture labelled
`("empty", n = 0, 0, 1)` is genuinely an out-of-bounds query at an empty
list and escapes with the two labelled ones. The `rfl` failed and the figure
was EVALUATED. Rule 3 earning its place.

**Validator.** `lake exe rmq_e1_machine_validate` PASS at **16.8 s wall
clock**. Phase 3j: `guardCases=11`, `guardFailures=0`, `guardRejected=8`,
`guardValidControlsAccepted=3`, `guardMaxInvalidSteps=10`,
`guardReadsTotal=0`, `guardMemoryReadCharges=0`. Phase 4i:
`guardMutationIsReal=true`, `mutantJ_rejected=5`,
`mutantJ_validControlsAccepted=3`, `mutantJ_caught=true`. Both contribute
verdict clauses (`okGuard`, `okGuardMutations`); the phase is not
decorative. **Phase 5 is untouched and still OPEN.**

**NOT BUILT, and the honest resume inventory.** *(As written by E1-LaneA2.
EVERY ITEM BELOW IS NOW CLOSED -- by E1-LaneA4 for the cap lemma and
`FringeFoldUntouched`, by E1-LaneA7 for the leaves and all sixteen
composites. The list is kept with its closures marked rather than deleted,
because the citations are still the fastest index into these blocks. See
section 14 for what remains after it.)*

- **CLOSED by E1-LaneA7** (`E1CostLadder.lean` section 1). Every leaf log
  listed here now has a `.length` equation proved by `rfl`, so a wrong figure
  is a build failure. `dispatchPrologueCats`'s unproved doc-comment claim of
  `19` was checked and HOLDS;
- **ALL SIXTEEN CLOSED by E1-LaneA7** (`E1CostLadder.lean`), with the
  numerals derived rather than asserted: `fringeLegCats` `<= 2067`,
  `fringeArmCats` `<= 2072`, `sameBlockArmCats` `<= 2074`,
  `sameBlockLegCats` `<= 2324`, `sameBlockDispatchCats` `<= 2328`,
  `candMerge3Cats` `<= 13`, `geomCats` `<= 158`, `legCats` `<= 653`,
  `spanCats` `<= 815`, `mergeCats` `<= 7`, `twoSpanCats` `<= 1810`,
  `twoLegCats` `<= |A| + |B| + 24`, `crossLegCats`
  `<= |A| + |B| + |C| + 43`, `dispatchArmCats` `<= 5479`, `dispatchCats`
  `<= 5498`, `crossBlockArmCats` `<= |interior| + 4669`. The two combinators
  are stated in their parameters' lengths because that is the shape their
  definitions have, following `crossBlockArmCats`'s own precedent;
- **the one genuine missing CAP LEMMA** -- **CLOSED by E1-LaneA4**
  (`cap_count_le` and `ascLog_length_le`, `E1CostAlgebra.lean`); the
  `cap_count_pos` citation below is `:245`, not `:246`, corrected by
  E1-LaneA4 after grepping. Original text: the fringe fold's `count` is
  `<= 33` only because every caller writes `Nat.min (relHi / c + 1) 33`
  (`E1FringeArmBlock.lean:594-596`, `:1020-1022`). There is no `<= 33`
  lemma, only positivity `cap_count_pos` (`:245`). The interior's twin is
  free from `chunkIters`'s own definition; the fringe's is not, and
  `fringeFoldCats`'s body is index-dependent (`fringeMergeArmCats` has four
  distinct arm lengths), so a bound needs a per-pass maximum rather than the
  constant-body identity `iterLog_const_length` supplies.
- **`FringeFoldUntouched` (`E1FringeFoldBlock.lean:962`)** -- **CLOSED by
  E1-LaneA4** (`E1FringeFoldProgram.lean`, validator phases 3k/4j); the
  validator note at `E1MachineValidate.lean:1540` cited at the end of this
  item is consequently NO LONGER accurate. Original text: STILL EXECUTED
  NOWHERE. Not attempted. It needs the fold run STANDALONE at its own base,
  not inside `armWitnessProgram`: `FringeFoldUntouched` (`r < 40 ∨ 63 ≤ r`)
  is STRICTLY STRONGER than `FringeArmUntouched`
  (`r < 40 ∨ (63 ≤ r ∧ r ≠ 67 ∧ r ≠ 68)`), so running the whole arm and
  checking the fold's predicate would fail at `67`/`68` CORRECTLY — the arm
  writes them and the fold does not. The fold loop runs `LB` to `LB + 67`
  (`fringeFoldLoop_runsTo_accepted`, `E1FringeFoldBlock.lean:1301`); a
  standalone witness program and store are what is missing, and
  `E1FringeArmProgram.lean:236-240` is the shape to copy. The validator's own
  note at `E1MachineValidate.lean:1540` already records this predicate as
  unexecuted; that note is still accurate.

**No acceptance row is marked closed by this lane.** What is supplied is in
the report; the judgement is the coordinator's.

**POST-MERGE NOTE (E1-LaneF).** This section's resume inventory is fully
closed, and so is the stage-slot list section 14 left open — the whole-query
literal is `11886` (`E1WholeQueryCostLiteral.lean`, section 15,
DD-20260719-244).

**Nothing in this section needed correcting.** The one sentence that reads
stale — "that note is still accurate", about
`E1MachineValidate.lean:1540` and `FringeFoldUntouched` — sits inside the
`Original text:` quotation of the same item, whose own preamble already
records the item as CLOSED by E1-LaneA4 and the note as NO LONGER accurate.
Checked because it looked like drift and is not; recorded so the next reader
does not re-check it.

## 13. Worklog — E1-LaneA4 (width + fold preservation + fringe cap), 2026-07-19

Branch `claude/e1-cost-algebra`, base `9151705`. Commits `34f0ca4`,
`8facc13`, `73cc485`, `9f15fb3` and this one. DD-IDs claimed and WRITTEN
into `DESIGN_DECISIONS.md`: **`144`, `145`, `146`**. Band `147-159` free.

### ITEM 1 — THE WIDTH QUESTION, SETTLED BY EVALUATION. ANSWER: (a).

**Evaluated first, argued second.** A scratchpad driver assembled the
concrete program at canonical parameters (`blockSize =
canonicalBPRelativeSummaryBlockSizeRaw shape`, `fringeSegment = 5`, matching
`E1MachineValidate.lean:361`) and computed the maximum
`ProgramFits`-constrained FIELD at sizes `1..1024`.

| n | bpCode len | mwb(n) | 2^mwb(n) | rwb(n) | maxReg | maxField | fits@mwb | fits@rwb |
|---|---|---|---|---|---|---|---|---|
| 1 | 2 | 1 | 2 | 20 | 84 | 555 | false | true |
| 4 | 8 | 3 | 8 | 21 | 84 | 555 | false | true |
| 16 | 32 | 5 | 32 | 23 | 84 | 555 | false | true |
| 64 | 128 | 7 | 128 | 25 | 84 | 555 | false | true |
| 256 | 512 | 9 | 512 | 27 | 84 | 555 | false | true |
| 512 | 1024 | 10 | 1024 | 28 | 84 | 1024 | false | true |
| 1024 | 2048 | 11 | 2048 | 29 | 84 | 2048 | false | true |

**THREE COORDINATOR PREMISES FAILED INSPECTION.**

1. **"the register file reaches `152`" — WRONG, it reaches `84`.** `152` is
   not a register index anywhere. `crossBlockArmProgramAt_fits`
   (`E1CrossBlockArm.lean:915`) carries `84 < 2 ^ w`; the largest `hreg` in
   the tree is `117`. The `152` figure was inherited from
   `E1AmendedTarget.lean:108` and is not supported.
2. **The binding field is NOT a register.** `ProgramFits` constrains every
   field including `const` VALUES and `brNZ` TARGETS. Up to `n = 256` the
   maximum is `555`, the guard invalid-exit target `8 + 547`; from `512`
   up it is `2 ^ machineWordBits |bpCode|`.
3. **`ProgramFits (machineWordBits n) ...` is FALSE AT EVERY `n`**, not "at
   small `n`". There is no crossover, so answer **(b) is ruled out
   structurally** and no size threshold could repair it.

**The reviewer-width inference was backwards.** It was put to this lane that
register `152` forces `w >= 8` hence "capacity `>= 128`". Capacity is
`400000 * (n + 1)`, so it is `>= 400000` at `n = 0` and grows. It is never
near `128`. `capacity_ge` records this.

**BUILT (`E1ReviewerWidth.lean`, new).** `#print axioms` clean on all.

- `programSkeleton_fits_reviewerWordBits (shape) : ProgramFits (shapeWidth
  shape) (programSkeleton shape.size (assembledValidPath shape))` — no size
  hypothesis, no parametric `w`, no threshold.
- `programSkeleton_not_fits_machineWordBits (shape) (hsmall : shape.size <=
  255)` — the ANTI-VACUITY half: the same program FAILS the same predicate
  at the other width, on the named instruction `brNZ regG 555`. The `255` is
  an artifact of cheap statement, not of where failure stops.
- Arithmetic core: `two_pow_machineWordBits_le`, `machineWordBits_le`,
  `sq_le_two_pow` (needed because `hmix` is QUADRATIC in the chunk width
  while the envelope is only LINEAR in the size).
- The one reduction: `lt_reviewerWordBits_of_lt_capacity`. Past it no goal
  mentions `Nat.log2`, so section 11 B kernel boundary is never reached.

**A FINDING WORTH MORE THAN THE THEOREM.** `sameBlockLegProgramAt_fits`
(`E1ProgramWidth.lean:57`), `sameBlockDispatchProgram_fits` (`:145`) and
`crossBlockArmProgramAt_fits` (`E1CrossBlockArm.lean:913`) take eleven to
seventeen side conditions each. Grep finds only their own statements and ONE
internal use (`E1ProgramWidth.lean:164`). **NOTHING IN THE TREE HAD EVER
DISCHARGED THEM AT ANY INSTANTIATION** — owed premises with no satisfiability
witness, so the width story could have been vacuous and no reader could tell.
That is now closed.

### ITEM 2 — `FringeFoldUntouched` EXECUTED. Validator phases 3k/4j.

New module `E1FringeFoldProgram.lean`: `foldWitnessProgram` hosts the fold
STANDALONE at loop base `2` (padding makes the base nonzero, per
`armWitnessProgram` discipline at `E1FringeArmProgram.lean:240`), and
`foldWitnessProgram_hosts` discharges ALL FOUR hosting hypotheses of
`fringeFoldLoop_runsTo_accepted` (`E1FringeFoldBlock.lean:1301`) at once.
`foldWitnessProgram_fold_eq` proves by `rfl` that this IS `fringeLoopBody`.

Checked bank is `40..62`, the fold OWN write set (`E1FringeFoldBlock.lean`
`:62`-`:106`), not a neighbour.

Phase 3k: `foldPresCases=27`, `foldPresCheckedRegs=87`,
`foldPresFailures=0`, `foldPresClobberedRegs=[]`,
`foldPresSeedDisagreements=0`, `foldPresReadBearingCases=27`.
Phase 4j (mutant K, consistent rename of the private scratch `fX` to `105`):
`foldPresMutationIsReal=true`, `mutantK_fold_preservationFailures=27`,
`mutantK_clobberedRegs=[105]`, `mutantK_fold_exitFailures=0`,
`mutantK_isPreservationOnly=true`. Five figures also kernel-checked by
`rfl`. Both phases contribute verdict clauses.

**The receipt argument here is NOT the interior one.** Mutant H could lean on
its block being read-free. The fringe fold is READ-BEARING and `fX` actually
reaches the read address (`fX` to `fB` to `fSlot` to `readMem fE S fSlot`).
It is invisible only because the rename is CONSISTENT. A partial rename
would move a read and the receipt would catch it, correctly.

### ITEM 4 — THE MISSING CAP LEMMA, closed in both halves.

`cap_count_le` states the `<= 33` every caller writes
(`E1FringeArmBlock.lean:594-596`, `:1020-1022`); only `cap_count_pos`
(`:245`) had covered the other side. `ascLog_length_le` supplies the
per-pass MAXIMUM that an index-dependent body forces in place of
`iterLog_const_length` constant-body identity.

`fringeFoldCats_length_le_capped : ... <= 2046 = 33 * 62`. Both factors
derived. **`62 = 32 + 8 + 21 + 1` is TIGHT**, checked by evaluating the arms:
`fringeMergeArmCats` lengths are `[6, 8, 7, 3]`, so the widest is attained.

### ITEM 3 — LARGELY NOT DONE. ONE of seventeen.

`fringeFoldCats` (`E1FringeFoldBlock.lean:952`) is now bounded. **The other
sixteen composites are still unbounded**, and the closed leaves they rest on
are still unbounded. Section 12 two lists stand except for that one entry.

`ascLog_length_le` (`E1CostAlgebra.lean`) is the REUSABLE half: any
composite with an index-dependent body can go through it. What each still
owes is its own per-pass maximum, and for the leaf logs a `.length` bound at
all. Suggested order, cheapest first: the closed leaves section 12 lists
(they are `List` literals or `.map`s of literals, so `rfl`/`decide` should
do), then `fringeLegCats`/`fringeArmCats`
(`E1FringeArmBlock.lean:559`/`:947`) which sit directly above the
now-bounded fold.

### Validator and build

`lake build RMQ` green. `lake exe rmq_e1_machine_validate` **PASS** at
**10 s wall clock**; phase 3k `foldPresWallClockMs=23`, phase 4j
`foldPresMutationWallClockMs=79` (modeled steps per pass are `61`, so
`61`/`122`/`183` for trip counts `1`/`2`/`3`). **Phase 5 untouched and still
OPEN.**

### Citations re-verified after the edits

All the file:line references above were re-grepped post-edit. Two of this
lane own first-pass numbers were WRONG and were corrected: `cap_count_pos`
is `E1FringeArmBlock.lean:245` (section 12 said `246`), and
`armWitnessProgram` is `E1FringeArmProgram.lean:240` (this lane first wrote
`238`).

**No acceptance row is marked closed by this lane.**

## 14. Worklog — E1-LaneA7 (the charge-length ladder + the summation), 2026-07-19

Branch `claude/e1-cost-algebra`, base `422660a`. Commits `d08826b`,
`fc27b17`, `4aaf225`, `f39161a` and this one. DD-IDs claimed and WRITTEN into
`DESIGN_DECISIONS.md`: **`220`-`230`**. Band `231-239` free.

### ITEM 3 IS DONE. Seventeen of seventeen.

Section 12's two lists are both closed, and section 13's "ONE of seventeen"
is now seventeen. New module `RMQ/Core/WordRAM/E1CostLadder.lean`, wired into
`RMQ.lean`. The numerals are above in section 12; each is derived by
`unfold` + `omega` from its own algebra, none asserted.

The three imports the ladder needs (`E1InteriorDispatchCompose`,
`E1InteriorCombine`, `E1InteriorMinCandidate`) are why this is a new module
rather than more of `E1CostAlgebra`: adding them there would push the whole
interior dispatch into `E1AmendedTarget` and the validator. DD-20260719-220.

### THE SUMMATION, in two parts because the tree supports two different things

**CONCRETE.** `crossBlockArmCats_withCanonicalInterior_length_le : ... <=
10167`, at the instantiation the tree ACTUALLY composes --
`crossBlockArm_withCanonicalInterior_runsTo`
(`E1InteriorDispatchCompose.lean:1302`) passes `dispatchCats` as
`interiorCats`. `10167 = 5498 + 4669`, both halves derived.
`closeLcaLegCats_length_le` puts the same literal over the same-block branch
too (`2328`).

**PARAMETRIC.** `wholeQueryBranchCats_length_le_of` sums the CONTROL
STRUCTURE over all four route branches:
`prologue + 2 * select + lca + rank + output`. The per-stage logs are
parameters (`E1WholeQueryCats.lean:98`) because select, close/LCA and rank
belong to other lanes. This lane fills the `lca` slot with `10167` and
invents no numeral for the other three. **The whole-query literal is NOT
claimed** -- filling those slots with plausible figures would produce a
number that reads as derived and is not.

### `cats.length` IS `totalSteps`, and it is not a lemma that could be missing

`RunsTo store program s s' reads cats` is DEFINED as
`run store program cats.length s = <s', reads, cats, cats.length>`
(`E1MachineCalculus.lean:96`), whose last component is `steps`. So every
bound here is already a `totalSteps <=` bound. `RunsTo.steps_le` says so;
`#print axioms` reports it depends on NO axioms at all. DD-20260719-228.

### COORDINATOR CLAIMS CHECKED

1. "`ascLog_length_le` is the reusable half for any index-dependent body."
   **HELD but NOT NEEDED AGAIN.** Of the sixteen composites, none has an
   index-dependent iterated body: `rankCloseHitCats` is a CONSTANT-body
   `iterLog` (`iterLog_const_length` applies), and the rest are finite
   compositions and branches. `ascLog_length_le` was the right tool for
   `fringeFoldCats` and is used by it; the ladder above needed plain
   composition. The suggested cheapest-order was otherwise accurate.
2. "The leaf logs are `List` literals or `.map`s of literals, so `rfl`/decide
   should do." **HELD**, all seventeen by `rfl`.
3. "`fringeLegCats`/`fringeArmCats` sit directly above the now-bounded fold
   and compose immediately." **HELD.**
4. "The kernel boundary does not block this." **HELD, and never approached** --
   no bound here passes through `machineWordBits`.
5. "The operative constant is `210`, never `207`." Not exercised by this
   lane: `210` is the READ-count bound and this lane counts STEPS. Recorded
   so no reader infers a connection that was not made.

### A CLAIM OF THIS LANE'S OWN THAT FAILED, and how

`dispatchArmCats_length_le`'s first docstring said the five arms "measure"
`4`, `1814`, `3650`, `3651`, `5479`. Four of those are BOUNDS, not
measurements. Evaluating at the fixture shape showed a one-block range
charges `602` against its bound of `1814`. Corrected; DD-20260719-224. Rule
3 earning its place again.

### ANTI-VACUITY, evaluated not argued

At `Cartesian.stackCartesianShape [3, 1, 4, 1, 5]`:
`rankSeedLegCats = 63/238`, `sameBlockArmCats = 388/2074`,
`sameBlockDispatchCats = 467/2328`, `dispatchArmCats = 4/5479` (empty) and
`602/5479` (one block), `dispatchCats = 621/5498`,
`crossBlockArmCats` with canonical interior `= 1031`-`1631` `/10167`.

The logs are substantial and the bounds are LOOSE at small size by roughly a
factor of six. Both are recorded in the module's section 12. That looseness
is the price of "all-size, no size hypothesis", which is what REQ-E1-06
conjunct (c) asks for; a tight bound would be a different theorem.

### Validator and build

`lake build RMQ` green at every commit. `lake exe rmq_e1_machine_validate`
**PASS** at **7.6 s**. This lane added no validator phase: the ladder is
symbolic arithmetic over category lists with no executed machine surface of
its own, and a phase that re-evaluated `#eval`-able lengths would duplicate
the `rfl`s. **Phase 5 untouched and still OPEN.**

All twenty-two ladder theorems clean under `#print axioms` (`propext`,
`Classical.choice`, `Quot.sound` only; `RunsTo.steps_le` none).

### Still owed after this lane

*(ALL THREE ARE NOW CLOSED OR SUPERSEDED — by E1-LaneF, after the merge. The
list is kept with its closures marked rather than deleted, per the same
convention section 12 used. See section 15.)*

- ~~The three whole-query stage slots (`prologue`, `select`, `rank`, `output`)
  and hence the whole-query literal. Owned by whole-query assembly, not
  here.~~ **CLOSED by E1-LaneF** (`E1WholeQueryCostLiteral.lean`). The slots
  are `9`, `729`, `234`, `2`, plus the two connectives at `2` each that this
  lane's record did not yet have; the literal is `11886`. DD-20260719-244.
- Phase 5 of the validator, still OPEN — but **no longer for the reason
  stated.** "No definition composes the legs into one runnable query program"
  was already false when this was written: `wholeQueryProgram`
  (`E1WholeQueryProgram.lean:876`) and E1-LaneA8's four executed branches
  falsify it, as section 10g records. What phase 5 actually lacks is a
  VALIDATOR-side comparison surface, not a definition.
- ~~A dispatcher between the same-block and cross-block close legs. None
  exists; `closeLcaLegCats_length_le` takes the disjunction as a hypothesis
  rather than inventing one. DD-20260719-230.~~ **CLOSED by E1-LaneF.**
  `wholeQueryLcaRunCats` (`E1WholeQueryAgreement.lean:39`) is that dispatcher
  and predates the discharge — it was written for the agreement proof, which
  is what makes it a witness found at the target rather than built for the
  premise. `wholeQueryLcaRunCats_length_le` bounds it at `10179` with no
  disjunction left standing. DD-20260719-241.

### Citations re-verified after the edits

All file:line references in this section and in section 12's rewritten
entries were re-grepped post-edit. Two corrections were made to text this
lane did not write: section 12's `cap_count_pos` citation said `:246` and is
`:245` (E1-LaneA4 had already corrected this in section 13 but section 12 was
left stale), and section 12's closing pointer to the validator note at
`E1MachineValidate.lean:1540` describing `FringeFoldUntouched` as unexecuted
is no longer accurate, E1-LaneA4 having executed it. Both are marked in place.

A THIRD, in the validator's own source and not in a doc. The note heading
phase 3i/4h asserted "the string `FringeFoldUntouched` does not occur in this
file". It occurs TEN times: E1-LaneA4's phases 3k/4j (`:2010` onward) execute
exactly that clause and did not update the earlier note. A sentence asserting
its own file's contents is `grep`-checkable and this one had become false, so
it is corrected in place rather than left standing. The note's original point
-- that phase 3i/4h was the first executed fold-level preservation check in
the tree -- is preserved and marked as history.

**No acceptance row is marked closed by this lane.** What is supplied against
REQ-E1-06's evidence column is in the report; the judgement is the
coordinator's.

---

## 15. Worklog — E1-LaneF (the cost-algebra merge + the whole-query step literal), 2026-07-19

Branch `claude/b1-b2-charged-fringe-tables`, base `54ceaf4`. Merge commit of
`claude/e1-cost-algebra` (`1e8dcc5`), then this lane's own commit. DD-IDs
claimed and WRITTEN into `DESIGN_DECISIONS.md`: **`240`-`244`**. Band
`245-259` free. Full build set green at every commit.

**Numbering note.** The brief for this lane asked for updates to "§12" and a
final "§13". Those numbers were the pre-merge ones; the merge brings the
cost-algebra branch's own §12, §13 and §14, so the cost ladder's stage slots
live in **§14** (updated in place) and this final section is **§15**.

### ITEM 1 — the merge

Three conflicts, two textual and one semantic.

- `RMQ.lean` — append-only, resolved as the union of both import blocks.
- `DESIGN_DECISIONS.md` — resolved BY ID, nothing renumbered. This branch's
  `120-122` and `160-209` interleave with the other branch's `140-146` and
  `220-230`. Each side's bytes are preserved exactly; the two sides use
  different separator conventions (this branch uses `---` between entries,
  the cost-algebra branch does not), so separators were added at the two
  splice points only. 146 entries after this lane's five, no duplicate IDs.
- `E1_LIVE_STATE.md` auto-merged; §1-§14 all present.

**THE SEMANTIC CONFLICT GIT MERGED CLEANLY AND LEAN REJECTED, exactly as the
brief predicted.** `E1WholeQueryCats.lean` was edited on THIS branch only, so
git took it silently, while `E1CostLadder.lean`'s summation on the other
branch was written against the OLDER record. Two files, two branches, no
conflict, and a type error only after both land — the second instance of the
pattern DD-20260719-122's round first recorded.

`wholeQueryBranchCats_length_le_of` and `wholeQueryCats_length_le_of`
referenced `S.lcaSkipped`, a field DD-20260719-208 had split into
`lcaSkippedLeftMiss`/`lcaSkippedRightMiss`; the record had also gained the
`selectJoin` and `rankJoin` connective stages. **Repaired by ACCOUNTING for
the new stages, not by reinstating the old field** — the sum is now
`prologue + 2*select + selectJoin + lca + rankJoin + rank + output`, both
connectives as their own summands. Reinstating `lcaSkipped` would have made
`selectNone_branches_separable` (`E1WholeQueryCats.lean:424`) false by `rfl`
again. DD-20260719-240.

### ITEM 2 — THE WHOLE-QUERY STEP LITERAL IS `11886`

New module `E1WholeQueryCostLiteral.lean`.
`wholeQueryCats_machineS_length_le`: on every shape, every query and all four
branches, with **no size hypothesis**,

```
  prologue        9      guardAcceptCats ++ [registerWrite]
  select        729      twice
  selectJoin      2
  lca         10179
  rankJoin        2
  rank          234
  output          2
  ------------------
               11886
```

`11886 = 9 + 729 + 2 + 729 + 10179 + 2 + 234 + 2`. Every summand is derived by
`unfold`/`rfl` plus `omega` from the algebra beneath it; `omega` performs the
addition, so the literal is kernel-checked rather than transcribed. Four of the
eight slots are frozen literal lists and are therefore EXACT.

`wholeQuery_totalSteps_le` carries the bound across `RunsTo`'s definitional
identity to `(run ... ).steps ≤ 11886`, via `RunsTo.steps_le`, which depends on
NO axioms.

**THE SELECT SLOT WAS THE ONLY ONE NEEDING NEW MATHEMATICS, AND THE THING THAT
COULD HAVE OBSTRUCTED IT DOES NOT EXIST.** `selectCloseCats`
(`E1SelectDispatch.lean:287`) is a four-level `if`/`match` tree over three legs
and nothing in the tree bounded it. It is bounded at `729` here. The all-size
property survives because `bpWordChunkCount c e := Nat.min ((e-1)/c+1) 8`
(`ChargedWordChunks.lean:150`) caps INSIDE its own definition, so
`bpWordChunkCount_le_eight` (`:153`) is `Nat.min_le_right` with no side
condition — and every chunk count reachable from the select tree is written
literally as a `bpWordChunkCount`. **Eighth instance of a brief budgeting work
a definition had already done**; settled by reading the body before proving
anything. DD-20260719-243.

**DD-20260719-230's HYPOTHESIS IS DISCHARGED.** `wholeQueryLcaRunCats`
(`E1WholeQueryAgreement.lean:39`) is the dispatcher that lane said did not
exist, and it PREDATES the discharge — written for the agreement proof, not for
this premise, which is what makes it a witness found at the target (rule 5).
`wholeQueryLcaRunCats_length_le` bounds it at `10179` outright.
`10179 = 6 + (4 + (10167 + 2))`: the dispatcher also charges the two select
tests, the address arithmetic and the cross arm's terminator, which the
leg-level `10167` did not include because at that level they had not happened.
DD-20260719-241.

**`length_cons_le`** is added beside `length_append_le` for the same reason
DD-20260719-227 gives: the select tree is built from `::` as well as `++`, and
without the cons form the proof would have to TRANSCRIBE the tree's index
expressions. Every intermediate numeral is pinned rather than inferred — with a
metavariable in the bound slot the arithmetic side condition cannot be
discharged at all, which is how the first draft failed in five places.
DD-20260719-242.

### ANTI-VACUITY, evaluated not argued

At the validator's fixture shape (`Cartesian.stackCartesianShape [3,1,4,1,5]`),
against `wholeQueryMachineS` — the real record, not a stand-in:

| stage | measured | bound |     | branch | measured |
|---|---|---|---|---|---|
| `prologue` | `9` | `9` |  | `.full 0 4 3` | `1270` |
| `select 0` | `335` | `729` |  | `.full 1 3 2` | `1256` |
| `select 3` | `387` | `729` |  | `.lcaNone 0 4` | `1209` |
| `selectJoin` | `2` | `2` |  | `.leftSelectNone` | `737` |
| `lcaRun 0 4` | `474` | `10179` |  | `.rightSelectNone 0` | `739` |
| `lcaRun 1 3` | `410` | `10179` |  | | |
| `rankJoin` | `2` | `2` |  | | |
| `rankRun 5` | `59` | `234` |  | | |
| `outputSome` | `2` | `2` |  | | |

The logs are substantial — four figures on the answering branch at a
five-element input. **The bound is about nine times loose there**, against the
six times §14 recorded for its own bounds, and the excess is ATTRIBUTED rather
than described: of the `10616` steps of slack, `9705` are in the close/LCA slot
alone, because that bound assumes the cross-block arm with a full interior
dispatch while a five-element shape takes the same-block arm and charges `474`.
That is the price of "all-size, no size hypothesis", which is what REQ-E1-06
conjunct (c) asks for. DD-20260719-244.

### A claim of this lane's own that it corrected

The first draft of the post-merge note in §12 asserted that two pointers in
that section had gone stale. **They had not.** The sentence that reads stale
sits inside the `Original text:` quotation of an item whose own preamble
already records it as closed and the pointer as no longer accurate. Rule 4
caught it — the claim about what a file contains was checked against the file
before it was allowed to stand — and the note now records the check instead of
the false finding.

### `11886` AND `210` ARE NOT COMPARABLE

`11886` bounds STEPS. `210` bounds READS. §11 A and §14 both record the
distinction; it is repeated here because the two numbers will now sit near each
other in every summary of this work, and adjacency is exactly how the two `33`s
got conflated. Nothing in this lane is proved against `210`, and neither number
is derived from the other.

### Build, validator, axioms

`lake build RMQ RMQPaper RMQExamples` green; `lake build
rmq_e1_machine_validate` green; `lake exe rmq_e1_machine_validate` **PASS**,
phase 5 `wholeQueryComparisonAvailable=false`, verdict `OPEN` — unchanged by
this lane, which added no validator phase (the ladder is symbolic arithmetic
over category lists with no executed machine surface of its own, and a phase
re-evaluating `#eval`-able lengths would duplicate the `rfl`s).

`#print axioms`, importing the new and changed modules directly: every new
declaration is `[propext, Classical.choice, Quot.sound]` or a SUBSET —
`selectCloseCats_length_le`, `denseLegCats_length_le` and `length_cons_le`
depend on `[propext, Quot.sound]` only, and `RunsTo.steps_le` on nothing at
all. **No `sorryAx` anywhere.** The frozen public identity
`listInt_flatPayloadStore_noSynthetic_two_n_plus_o_execution_story` is
unchanged and still `[propext, Classical.choice, Quot.sound]`. No
`sorry`/`admit`/`axiom`/`native_decide`/`partial`/`unsafe`/`implemented_by`/
Mathlib/`maxHeartbeats` in any new or edited file.

### WHAT REMAINS FOR COORDINATOR ADJUDICATION

This is the last substantive E1 lane. What is left is judgement, not
construction.

1. **The acceptance matrix.** No row is marked closed by this lane, by any
   lane in the merge, or by anyone since. REQ-E1-06 and REQ-E1-02 are the two
   this work bears on; what is supplied against each row's own
   `Evidence needed` column is in this lane's report. **The rows are NOT
   whole-query scoped** — most read `Local`, and the whole-query framing was a
   coordinator invention. Adjudicating REQ-E1-06 means deciding whether a
   `Local`-scoped row is answered by a whole-query theorem, which is a scope
   question, not a proof question.

2. **Validator phase 5, still OPEN.** Its stated reason is now FALSE and has
   been since E1-LaneA8: the phase text says no definition composes the legs
   into one runnable query program, and `wholeQueryProgram`
   (`E1WholeQueryProgram.lean:876`) plus four executed branches falsify it.
   What phase 5 actually lacks is a validator-side comparison surface. Whether
   that is worth building, or whether the phase text should simply be
   corrected and the verdict re-judged, is a coordinator call.

3. **REQ-E1-07's supersession note.** `E1AmendedTarget.lean` supplies the
   amended Prop and `amendedTarget_of_wholeQueryAgreement` the reduction;
   §11 E's four precision points about what was refuted were checked and all
   four held. The note itself is unwritten.

4. **The `207`/`210` prose drift**, owed to REQ-E1-09's closure pass and
   deliberately left unfixed under owner direction (§11's closing paragraph).
   `README.md` is internally inconsistent and `docs/FAMILY_SUMMARY.md` carries
   the pre-B7 algebra. Neither gate catches it. **A new numeral, `11886`, now
   also exists**, and it will drift the same way if it enters prose before
   that pass runs.

5. **Tightness, if anyone wants it.** §14's bounds and this lane's are loose by
   six to nine times at small shapes, and the attribution above says exactly
   which theorem holds the slack. Sharpening it means giving up the all-size,
   no-hypothesis property. Nobody should do that without an explicit ruling
   that the requirement wants tightness more than generality.

**No acceptance row is marked closed by this lane.** What is supplied against
REQ-E1-06's and REQ-E1-02's evidence columns is in the report; the judgement is
the coordinator's.
