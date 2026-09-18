Status: INCOMPLETE
Phase: source-relations leaf proved and checked; the integrated OPT-1 compact compiler and capstone remain lead-owned.

## Identity and scope

Handle: OPT-1/source_relations. Requested parent title:
`(OPT-1) Tighten and compact packed compilation`.
Worktree: `C:/Users/poin/.codex/worktrees/1580/RMQ`.
Branch: `codex/opt-1-packed-compiler`.
Base/governance: `0e6a00f654abc64f8b68988fa9675b9a839dca2f`.
Checkout at verification: `1f3a4199eaa95324cd1daaadbab89340ca8392c4` plus
uncommitted, disjoint parent and leaf work. This leaf made no commit.
Source SHA-256:
`26B26ED4BFCBEFBA130A9A6FD26CE51FA564313707F141527763792BE39B8EFB`.

Changed paths are only `RMQ/Core/WordRAM/Optimization/SourceRelations.lean`
and files in this `relations-development/` directory. Shared Packed modules,
the acceptance matrix, ledgers, root aliases and peer files were not edited.
`CONTRACT.md` froze this leaf's requirements before source edits, referencing
the already frozen parent acceptance matrix. This report appends evidence;
it does not amend those frozen requirements or record coordinator acceptance.

Personal project preflight passed before edits with exact governance and the
actual runtime RMQ skill catalog `rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint`;
`rmq-proof-sprint` was required. All three canonical packages matched. The
canonical skill, AGENTS, completion gate, matrix, relevant roadmap and source
were read. No fallback was used.

## Checked propositions and composition

All names below are in `RMQ.SuccinctFinal.PackedWordRAM.Optimization`.

`DataAgreesBelow N a b` is exactly
`a.status = b.status AND forall r, r < N -> a.regs r = b.regs r`.
It constrains halted values because those values are inside the equal statuses.
It imposes no equality or fitting assumption on fresh registers.

`ActionRegistersBelow N` checks both destination and address for load, only
the destination for constant, both destination and source for move, and all
destination/lhs/rhs identifiers for arithmetic and comparison.
`BlockRegistersBelow N` also checks exit operands, conditional registers,
both conditional arms, both sequential bodies and every repetition body,
including a zero-count repetition. Thus this is a conservative complete source
operand inventory. Constant word values are intentionally not register indices.

The checked primary type is:

```lean
source_eval_congr (memory : Memory) (block : Block) (bound : Nat)
  (bounded : BlockRegistersBelow bound block) (left right : Data)
  (agree : DataAgreesBelow bound left right) :
  EvaluationAgreesBelow bound (block.eval memory left) (block.eval memory right)
```

Here `EvaluationAgreesBelow` is exactly agreement of final data AND equality
of the entire ordered `Receipt` lists. It does not erase duplicate occurrences,
failed replies, or their positions. Memory is the same arbitrary `Memory` in
both evaluations; there is no valid-query, successful-load or running-state
hypothesis. Proof composition is actual `Action.eval`/`execute` operand
agreement -> iteration induction -> constructor induction for `Block.eval`.
Halted/faulted entry states evaluate identically on their respective registers.
The proof matches both selected branches by the equal condition operand.

`SourceRelationsConsumers.source_congr_expectedType` pins the conclusion
independently as the conjunction of final status equality, equality at every
register below the bound, and exact evaluator receipt equality. It explicitly
projects all three facts from the relation theorem. Deleting a load-bearing
conjunct from that theorem/its relation cannot leave this consumer unchanged.
No deletion mutation campaign was executed by this leaf; the parent owns that
acceptance campaign.

The checked frame type is:

```lean
source_eval_frame (memory : Memory) (block : Block) (bound : Nat)
  (bounded : BlockRegistersBelow bound block) (r : Nat)
  (outside : bound <= r) (s : Data) :
  (block.eval memory s).final.regs r = s.regs r
```

It follows through `BlockRegistersBelow.writesOnly` to the unchanged
`Structured.Block.eval_frame`. It covers every memory/state and every fresh
register, including early stop and failed load. Its typed consumer quantifies
all `r >= bound` explicitly.

The optional safety target was also proved without narrowing it:

```lean
source_safe_transport (memory : Memory) (width bound : Nat) (block : Block)
  (bounded : BlockRegistersBelow bound block) (left right : Data)
  (agree : DataAgreesBelow bound left right) (rightFit : right.Fits width)
  (safe : block.Safe memory width left) : block.Safe memory width right
```

The left entry fitting condition is contained in `safe`; the right fitting
condition covers ALL registers, including fresh scratch, and halted values.
Every action's actual scalar operands agree, including the lookup address and
the actual reply constraint. The proof transports every arithmetic condition
in `Action.LocalSafe`: result width, subtraction order, nonzero divisor, and
shift width. Sequential and repeated safety is checked at each side's actual
evaluated intermediate state, using `source_eval_congr` and existing
`Block.eval_fits`. The independent typed consumer exposes the same hypotheses
and conclusion directly.

Support includes reflexive/symmetric/transitive/monotone data agreement,
monotone operand bounds, agreement after equal writes, and
`DataAgreesBelow.write_right_fresh` / `write_left_fresh`. The latter allow one
side's fresh register to change while preserving status and all protected
registers. These support rebasing source data after compact loop initialization.

The intended parent consumption chain is source congruence + fresh frame +
source safety transport -> actual compact compiler simulation and transition
safety -> unchanged-allocation compact query capstone. The emitted loop
simulation, count/operand/PC safety, actual `TraceSafe`, all-prefix fitting,
code accounting and final consumer are NOT proved by this module. In
particular, agreement alone does not establish a machine state's fitting.

## Requirement evidence and controls

| Frozen leaf row | Evidence now obtained | Local status / join limit |
| --- | --- | --- |
| REL-AGREEMENT | Exact definitions above are constructor-complete; immediate values excluded from identifier testing. | Proved; parent must instantiate bound for its actual source. |
| REL-EVAL | Universal `source_eval_congr` plus independently pinned three-projection consumer; no state or memory readiness guard. | Proved; parent must compose with its actual compact execution. |
| REL-FRAME | Universal outside-bound frame through baseline `Block.eval_frame`, plus pinned consumer. | Proved; parent must establish emitted counter destinations are fresh. |
| REL-SAFE | Universal safety transfer at actual evaluated intermediate states, with fitting alternate data, plus pinned consumer. | Proved; this is source safety, not emitted-transition safety. |
| REL-CHECK | Root transferred the sole build slot after the bound worker released it; bounded sequential checks passed. Slot released immediately afterward. | Checked. No heavy process remains from this leaf. |

The `SourceRelationsConsumers` namespace contains checked negative controls
for a fresh destination, load address, move source, both arithmetic inputs,
both comparison inputs, branch condition and exit source. It also rejects a
fresh address in a dormant conditional arm and in a zero-count body. These
all negate the SAME `BlockRegistersBelow` predicate used by the positive
theorems, at explicit tiny source terms. The positive
`immediate_is_not_register` theorem accepts a constant of ANY natural value
when its destination is register zero below bound one. These controls directly
challenge complete identifier accounting and constant/register separation;
they do not claim a full production replay or whole-query reachability test.

The universal proofs cover branch directions, arbitrary nested sequencing,
zero/one/repeated iterations, initial and dynamic stopping and failed loads.
The parent validation registry still must test its emitted compact program;
testing the source leaf does not substitute for REQ-OPT-COMPILE/RUN/CONTROLS.
All inherited whole-machine and space invariants remain parent join obligations.

## Verification record

Platform recorded in every JSON artifact: Windows, exact pinned Lean 4.22.0
at `C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0/bin/lean.exe`.
Every invocation used `-j1`, task-local `.lake/build/lib/lean` output/LEAN_PATH,
and the existing `Invoke-RMQOwnedBoundedProcess` kill-on-close Windows job.
Each subprocess deadline was 300 seconds with 1 MiB output limit. First-run
margin was chosen for cold Frame/Safety dependencies; actual times were short.
`check.ps1` is a proof-development builder, not an acceptance replay runner.

| Command / exact source | Evidence | Duration | Exit / outcome |
| --- | --- | --- | --- |
| check.ps1 -Modules Frame,Safety,SourceRelations,Types; Frame | `20260912-072230-413-Frame.json` | 17.239 s | 0, pass |
| Same call; Safety | `20260912-072257-771-Safety.json` | 27.092 s | 0, pass |
| Same call; first SourceRelations draft | `20260912-072317-427-SourceRelations.json` | 19.568 s | 1, elaboration repairs needed; Types not run |
| check.ps1 -Modules SourceRelations,Types; repaired draft | `20260912-072444-505-SourceRelations.json` | 12.039 s | 1, two final definitional reductions missing; Types not run |
| Same focused call after source repair; final SourceRelations hash above | `20260912-072545-457-SourceRelations.json` | 10.759 s | 0, pass, no warnings |
| Same call; Types imports final module and pins types/axioms | `20260912-072553-584-Types.json` | 7.994 s | 0, pass |

The first failures were ordinary local proof elaboration: a qualified monotonicity
lemma, an explicit register projection, receipt append equality, recursive
predicate reduction and a syntactically dependent induction argument. There
was no timeout, semantic counterexample, toolchain fallback or unchanged
expensive retry. Frame/Safety were reused after their single successful checks.

`#print axioms` reports `[propext]` for congruence and its exact consumer;
`[propext, Quot.sound]` for frame, safety transfer and their consumers. No
new axioms or native-decision trust surface occur. `hygiene.json` records empty
matches for the trust and native-decision scans of the owned module, exit 0
for scoped `git diff --check`, and a supplemental new-file `--no-index --check`
with no whitespace errors (only the repository's LF-to-CRLF conversion warning).
The supplemental no-index exit 1 means a nonempty new-file diff, not a check
failure. This leaf is deliberately uncommitted; the parent performs the
committed-range and strict design checks when integrating its owned work.

Full Lake, aggregate gates, claim scans, production replay, blind exact-commit
audit and publication acceptance were not run by this generic leaf. They are
parent-owned final checks on the composed candidate. There is no unsupported
host coverage claim, no mutation restoration claim and no runtime performance claim.

## Proof digestion and ledger handoff

Conceptually, a source program needs agreement only where it can look; all
source identifiers are inventoried, including branches and read addresses.
Changing scratch above that interval leaves final source-visible data and the
entire read sequence unchanged. The same proof permits safety to transfer,
provided the new scratch words fit the same width. The existing destination
frame theorem separately shows that source execution preserves that scratch.

In plain English, the compact compiler can place loop counters in fresh
registers without changing what the original query sees or reads. It must
still prove that its own counter and jump instructions are correct and safe.
The named downstream consumer is the parent's compact source/run simulation,
then `compactPackedQueryCapstone_holds`.

Live assumptions are exactly a common arbitrary memory, complete source
identifier bound, equal initial statuses/protected registers, and for safety
an already safe source execution plus fitting alternate entry data. There is
no assumption about input size, canonical metadata, semantic answer or query
success. A skeptical graduate student should next inspect the parent loop
simulation: does it actually rebase after setting fresh counters, preserve the
enclosing counters during nested bodies, and establish every compact prefix
fits? Those are downstream obligations, not additional restrictions silently
added to this generic theorem.

Shared ledgers were not edited because this subagent owns neither. Suggested
task-scoped design rationale for the lead: complete source operands, rather
than only destinations, are the dependency boundary; scratch state equality
is intentionally relaxed but status and ordered receipts are not. This
supports early exits and failed loads without a fictitious reset. The
development checker reuses existing process ownership and the pinned direct
toolchain; no new workflow policy or machine model was introduced.
