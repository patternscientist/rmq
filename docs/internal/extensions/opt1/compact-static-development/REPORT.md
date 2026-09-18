Status: INCOMPLETE
Phase: static and fixed-query producers kernel checked; parent composition,
final acceptance and publication remain open. This is a bounded leaf handoff,
not full OPT-1 candidate completion or a mathematical obstruction.

Handle: OPT-1/compact_static (same source_relations agent).
Parent requested title: (OPT-1) Tighten and compact packed compilation.
Branch: codex/opt-1-packed-compiler.
Worktree: C:/Users/poin/.codex/worktrees/1580/RMQ.
Base/governance: 0e6a00f654abc64f8b68988fa9675b9a839dca2f.
Resumed/current HEAD: 8e355fda7788077f548865c1d6acf2ae5e88da55.
Repairs and new numeric producers remain uncommitted; the lead owns commits.
No other worker's files, shared Packed source or shared ledgers were edited.
Earlier unverified resource-wait evidence is superseded by the checks below.

## Scope and exact source identity

Owned source is RMQ/Core/WordRAM/Optimization/CompactStatic.lean and, after
explicit lead expansion, RMQ/Core/WordRAM/Optimization/Query.lean. Owned
evidence is this directory. CONTRACT.md preserves original frozen rows and
appends the authorized STATIC-QUERY row.

| Source | SHA-256 at final checks |
| --- | --- |
| CompactStatic.lean | 9459F014702789C6403404BD89B267E85A363F930F2B6B560D1D8D156E473074 |
| Query.lean | 6CFA64CBFAB2B18FA2D35F84BDA610901B8DF1DE296F6202B0A164BEE18B6368 |
| Unchanged Compact.lean emitter | A616631ACD50296408D5CD5D9BB6122C6F84C517C452C9FFE2DEE4177F63C434 |

Canonical preflight passed against the exact governance ref initially and
on resume. Actual runtime RMQ catalog: rmq-audit-prompt, rmq-coordinator,
rmq-proof-sprint. Required role: rmq-proof-sprint. The tracked skill, AGENTS,
completion gate, matrix and adopted independent CONTRACT_AUDIT were read.
Completion gate was reread on resume. No fallback was used.

## Exact checked propositions and composition

All theorem names below are in RMQ.SuccinctFinal.PackedWordRAM.Optimization.

Given bounded : BlockRegistersBelow fresh block, compactAt_writesOnly proves:

    ∀ instruction ∈ compactAt block fresh depth base,
      instruction.WritesOnly (fun r => r < fresh + 2 * (depth + compactDepth block))

compact_run_frame consumes this actual-list result through the existing
run_frame. For every memory, state, fuel, base and register with
fresh + 2 * (depth + compactDepth block) ≤ r, its conclusion is:

    (run memory (compactAt block fresh depth base) fuel state).final.regs r = state.regs r

No valid-query, successful-load, entry-PC or running-status premise is added.
compactAt_writesOnly_interval further places writes below fresh or inside
[fresh + 2*depth, fresh + 2*(depth + compactDepth block)).
compact_run_ancestor_frame therefore preserves every register satisfying
fresh ≤ r ∧ r < fresh + 2*depth. Nested execution and safety are separate.

compactAt_fits block width fresh depth base consumes exactly:

    block.FieldsFit width
    compactMaxCount block < 2 ^ width
    7 < 2 ^ width
    fresh + 2 * (depth + compactDepth block) ≤ 2 ^ width
    base + compactSize block < 2 ^ width

and proves:

    ∀ instruction ∈ compactAt block fresh depth base, instruction.Fits width

The pinned consumer expands the conclusion to:

    ∀ instruction ∈ compactAt block fresh depth base,
      ∀ operand ∈ instruction.encoding, operand < 2 ^ width

Source fields cover all original constants, source/destination registers,
branch/halt registers and tags. The independent count inventory covers every
repeat count, both branches and dormant syntax. Added guards cover wrapper
counts, counters, control tags and relocated PCs including the end boundary.
This is conservative syntactic coverage, including source syntax omitted by
zero loops. No maximum-destination-only width argument is substituted.

compactAt_encoding_length proves for arbitrary source and placement:

    ((compactAt block fresh depth base).map Instruction.encoding).flatten.length =
      compactEncodingWords block

The recurrence counts literal action encodings, halt as 2 words, branch plus
jump as 5 words, and the five positive-loop wrappers as 3+3+3+5+2=16 words.
Zero loops contribute 0 words. The recurrence is linked to actual emitted
encoding; it does not replace the literal code charged in complete space.

Query definitions, observation wrapper, source route, initial registers,
allocation and word width were preserved. The object-composition chain is:

    querySource -> seq querySource (exit 3) = compactQuerySource
    queryRegisterCount = compactQueryFresh
    compactAt compactQuerySource compactQueryFresh 0 0 = compactQueryProgram
    actual map Instruction.encoding / flatten / length = compactQueryProgramWords
    compactQueryFresh + 2*compactDepth compactQuerySource = compactQueryRegisterCount
    compactQueryRegisterCount + 3 = compactQueryScratchWords
    allocationWithMachineRho literalCodeWords literalScratch = compactQueryCompleteRho

| Theorem | Exact proposition |
| --- | --- |
| compactQueryProgram_length_eq | compactQueryProgram.length = 212964 |
| compactQueryProgramWords_eq | compactQueryProgramWords = 722339 |
| compactQueryBudget_eq | compactQueryBudget = 151978 |
| compactQuery_depth | compactDepth compactQuerySource = 1 |
| compactQuery_maxCount | compactMaxCount compactQuerySource = 33 |
| compactQueryRegisterCount_eq | compactQueryRegisterCount = 8273 |
| compactQueryScratchWords_eq | compactQueryScratchWords = 8276 |
| compactQuery_size_reduction | compactQueryProgram.length < queryProgram.length |

compactQuerySize_eq and compactQueryEncodingWords_eq prove recurrence values;
the actual-list numeric facts consume generic emitted length/encoding results.
compactQueryProgram_fits n applies full static fit at unchanged wordWidth n.
compactQuery_finite_registers proves, for all memory, n, left, right, fuel and
r with compactQueryRegisterCount ≤ r:

    (run memory compactQueryProgram fuel (initialState n left right)).final.regs r = 0

The capacity producer and pinned consumer use the SAME buildMemory xs, literal
emitted encoding, finite bank and width:

    ((buildMemory xs).length +
      (compactQueryProgram.map Instruction.encoding).flatten.length +
      (compactQueryRegisterCount + 3)) * wordWidth xs.length ≤
      2 * xs.length + compactQueryCompleteRho xs.length

compactQueryCompleteRho_littleO proves LittleOLinear compactQueryCompleteRho.
The fixed budget equality evaluates the compiler recurrence; connecting it
to successful actual steps requires the parent-owned semantic bridge.
Static encoded-field fit does not replace runtime arithmetic/whole-state fit.

## Acceptance evidence and challenges

| Frozen ID | Local evidence | Local result / residual |
| --- | --- | --- |
| STATIC-WRITES | Actual-membership write theorem and interval strengthening | Proved and checked; parent capstone join remains |
| STATIC-FRAME | All-fuel outer-bank and ancestor-counter frame consumers | Proved and checked, including fixed query consumer |
| STATIC-FIELDS | Constructor-complete fit and literal operand consumer | Proved and checked; runtime safety separate |
| STATIC-ENCODING | Literal encoding equality, nested32 and zero0 controls | Proved and checked |
| STATIC-CHECK | Exclusive slot, Static/Types and axioms below | Passed; final joined gate remains lead-owned |
| STATIC-QUERY | Numeric producers, exact consumers, literal measurements, bank/fit/capacity | Proved and checked; parent semantic/safety/certificate join remains |

Negative controls reject count16 at width4, counter ID16 at width4,
relocated target16 at width4, and wrapper control tag7 at width2.
The old Block.FieldsFit accepts repeat16 skip at width4, showing the precise
gap covered by the independent count premise. A positive control admits
count15 at width4. Nested positive and zero loops check actual word counting.
Exact consumers are in both source modules; Types.lean and QueryTypes.lean
print their exact propositions and axiom dependencies.
These are source proof controls, not a claim that the parent production
mutation/replay campaign has been completed by this leaf.

## Verification record

check.ps1 reuses scripts/owned_process_tree.ps1 with an explicit nonempty
module list, one sequential direct process, exact Lean4.22.0 lean.exe -j1,
task-local .lake/build/lib/lean in LEAN_PATH, 300-second per-process deadlines,
1MiB output limit and Windows owned-job cleanup. No elan download, parallel
build, full-Lake fallback, deadline termination or orphan occurred. Already
checked Compact/Scratch artifacts were reused. The lead explicitly granted
the slot; after final checks it was explicitly transferred to bound_proof,
who subsequently transferred it to the lead. No Lean process remains here.

Every artifact below is JSON in this directory with command, source hash,
process outcome, output and duration.

| Artifact | Result | Seconds | Meaning |
| --- | --- | ---: | --- |
| 20260912-085342-909-CompactStatic.json | FAIL | 18.901 | Three positive-width goals after simplification |
| 20260912-085459-926-CompactStatic.json | PASS | 15.279 | Final generic static source |
| 20260912-085506-634-Types.json | PASS | 6.565 | Exact types, consumers and axioms |
| 20260912-085620-197-Query.json | FAIL | 54.810 | Broad definitional-change recursion and frame alias rewrite |
| 20260912-085823-722-Query.json | PASS | 68.383 | Repaired static query before numeric additions |
| 20260912-085851-734-Measure.json | PASS | 27.900 | First literal emitted-list measurement |
| 20260912-090142-761-Query.json | PASS | 87.121 | Final numeric source and in-source consumers |
| 20260912-090148-784-QueryTypes.json | PASS | 5.936 | Final exact query consumers and axioms |
| 20260912-090227-589-Measure.json | PASS | 25.987 | Final literal measurement after numeric additions |

Width repair derives 0<width from the existing 7<2^width guard, with no new
premise. Query repairs normalize the small bank expression explicitly and
compose frame equality with the initial zero register before simplifying the
program alias. No emitter or object definition changed.

Final Measure.lean output compares actual program/encoding lists independently
with the source recurrences:

    literalInstructions=212964
    literalEncodingWords=722339
    recurrenceInstructions=212964
    recurrenceEncodingWords=722339
    chargedBound=151978
    depth=1
    maximumCount=33
    registerBank=8273
    scratchWords=8276

Numeric proofs use kernel reduction and generic equalities, not diagnostic
output, native_decide or Lean.ofReduceBool. Durations are development
observations, not executable RMQ complexity claims.

Checked axiom inventories contain only propext, Classical.choice and
Quot.sound where used. Upper-write/frame and encoding proofs use propext and
Quot.sound; interval/ancestor-frame/field proofs also use Classical.choice.
Numeric actual length/words use propext and Quot.sound; compactQueryBudget_eq
and its exact consumer have no axioms. No custom axiom, Mathlib or unsafe
facility was introduced.

hygiene.json records no matches for own-source trust/native scans, scoped
git diff --check exit0 and scoped original-base..current-HEAD diff check exit0.
LF/CRLF conversion notices are Git warnings. Current uncommitted changes
require the lead's final collected-commit check. Full Lake, aggregate gate,
public trust scans and mandatory exact-commit audit remain lead-owned.
No source changed after its recorded final check.

## Proof digestion and handoff

The compact emitter now has a checked static boundary: every literal
instruction is accounted for, encoded fields fit under explicit guards, and
every execution prefix preserves registers outside the charged bank.
For the fixed query this yields 212964 instructions, 722339 literal encoded
words and 8276 scratch words at the existing width. Scratch comprises 8273
finite registers and the existing three machine-state words. Code is strictly
smaller than the baseline program.

Live assumptions are complete source register bounds for generic frames and
source fields/count/tag/bank/end-PC bounds for generic fit. The actual fixed
query discharges those static premises from its source and existing width
facts. Total/successful memory replies are unnecessary for static/frame facts;
correctness, receipts, runtime arithmetic safety and successful execution
require the parent's semantic proofs.

A skeptical graduate student should next reconstruct whether the final public
theorem consumes this exact program, literal accounting, finite-bank producer
and numeric budget through actual semantic and safety bridges. The lead owns
that join, production consumers, replay/mutation evidence, final audit and
public claims. No full OPT-1 closure, publication-ready parity or Lean
wall-clock guarantee is claimed.

Design rationale for the lead's shared digest: the separate count inventory
is necessary because baseline FieldsFit erases counts; maximum destinations
miss other encoded operands and PCs. The interval frame expresses why nested
bodies cannot overwrite enclosing counters. Sixteen literal words per positive
loop, rather than five instructions, is the correct code-space charge.
These implement the adopted route/audit obligations. No workflow policy
changed; the checker reuses owned-process infrastructure and is development
evidence, not a replacement for the production replay registry. Shared
design/workflow ledger edits and final public digestion remain lead-owned.
