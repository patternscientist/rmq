# Worker Integration Checklist

This checklist is for multi-chat RMQ proof work. It keeps worker branches useful
without letting parallelism create stale claims, incompatible abstractions, or
proof churn.

The coordinator chat owns integration. Worker chats own narrow branches and
report enough evidence for the coordinator to merge, port, or reject their work.

For the active succinct-RMQ finish line, every worker should read
`docs/SUCCINCT_FINAL_PATH.md` before editing. That file is the current contract
for the descriptor-select component, concrete macro/micro BP-close component,
and final `2*n + o(n), O(1)` join.

## Worker Completion Report

Each worker branch should end with a report in this shape:

```text
Worker:        A/B/C or branch name
Owned target:  <roadmap target and join theorem this feeds>
Branch:        <git branch>
Changed files: <file list>

Goal reflection:
- Overall capstone:
- Current gap:
- Hard part:
- This branch's ambitious step:
- Explicitly avoided as lower-priority:

New theorem/def surface:
- <name> : <one-line purpose>

Commands run:
- lake build <module or whole repo>
- lake env lean scripts\axiom_check.lean       <if run>
- lake env lean scripts\hub_axiom_check.lean   <if run>
- rg hygiene scans                            <if run>
- scripts\succinct_cost_lint.ps1              <if relevant>

Result:
- Build: PASS/FAIL
- Axioms: PASS/FAIL/NOT RUN
- Hygiene: PASS/FAIL/NOT RUN
- Cost/space lint: PASS/FAIL/NOT RELEVANT

Debt delta:
- Asserted-cost or fake-O(1) paths retired:
- Gated hypothesis count changed:
- Stale docs/claims updated:

Integration notes:
- Imports or public APIs touched:
- Expected conflicts:
- Remaining construction gaps:
- Smallest next theorem:

Known-trap checklist:
- If this branch adds a local descriptor lemma, where is it consumed by a
  global descriptor-backed `selectCosted_exact` theorem over all occurrences?:
- If this branch adds a descriptor-select profile surface, which concrete
  compact payload builder instantiates its proof fields?:
- If this branch uses `descriptorIndex` or another routing/index function, why
  is it bounded arithmetic or charged payload-derived rather than an uncharged
  search/predecessor/oracle?:
- If this branch adds a packed descriptor-select profile, where is the theorem
  proving the descriptor payload is `LittleOLinear` under the machine-word side
  conditions, rather than just an exact full local-delta-slot length formula?:
- If this branch adds a BP range/min/max or block-summary table, where is it
  consumed by an answer-close `lcaCloseCosted_exact` theorem?:
- If this branch adds a BP range witness or macro candidate, where is it
  consumed by charged endpoint-fringe repair plus a global answer-close theorem?:
- If this branch proves an `_exact_of_prefix_pos` theorem, where is the theorem
  proving that the built prefix position is the semantic BP close/LCA answer?:
- If this branch proves an `_exact_of_merged_candidate` theorem, where is the
  theorem proving the supplied merge fact from built payload entries and
  BP/RMQ semantics?:
- If this branch only repairs an audit caveat on such a helper layer, why was
  the owned target explicitly scoped to caveat repair rather than C1/C2/C3?:
- For every newly charged fixed-width table or payload-word read, where is the
  machine-word bound proved?:
- Did any theorem name overstate its statement? If yes, what was renamed?:

Loop stop audit:
- Named target theorem or concrete component profile proved? YES/NO:
- Next theorem/construction obvious within owned files? YES/NO:
- Abstract hook/canonical identity witness left where a concrete witness was
  requested? YES/NO:
- Did this branch reduce the current distance to the capstone, rather than only
  producing technically substantial adjacent work? YES/NO:
- If the target is not closed, did this branch prove the target statement
  impossible as stated? If yes, name the theorem:
- If no impossibility theorem, what meaningful positive construction/profile
  did this branch land?:
- If stopping on exhaustion, which fifty serious attempts at the named positive
  construction were made, and what common brick wall did they hit?:
- Why is the next move a fundamental design/coordinator choice rather than
  another local proof iteration?:
- If stopping on impossibility, which concrete construction was attempted and
  which minimal theorem proves the target signature must change?:
- Why stopping is valid under `docs/CODEX_AUTONOMY.md`:
```

If this audit says the stop is invalid, do not send a final completion report.
Start the next loop iteration immediately, using the obvious next theorem or
construction named above. A report that admits the stop is invalid but stops
anyway is a protocol failure, not a transparent partial success.

If a worker did not run a full gate, that is acceptable only when they report
the narrow check they did run and why a full check was deferred.

Coordinator audits of worker output must always include two extra judgments:
whether the worker should actually have stopped its unattended loop, and how
the loop specs or next prompts should be modified in response. If no prompt or
spec change is needed, say so explicitly.

## Required Evidence By Worker Type

### Proof Worker

Must report:

- exact theorem names that typecheck;
- whether any public contract changed;
- whether proof-only fields are separated from payload fields;
- whether any old theorem or definition was superseded and should be retired;
- narrow module check at minimum.
- for descriptor/select work, whether exactness is global over all
  `(target, occurrence)` or conditional on a preselected local run;
- for descriptor/select work, whether exactness is supplied by a concrete
  builder or remains stored as proof fields that still need instantiation;
- for descriptor/select work, whether descriptor/routing index computation is
  bounded arithmetic or charged payload-derived;
- for BP close work, whether summary tables are consumed by a concrete
  answer-close theorem or remain helper payload.
- for BP close work, whether any range witness or macro candidate has been
  consumed by endpoint-fringe repair and a BP semantic theorem, or remains only
  conditional on a supplied prefix position.
- for BP close work, whether endpoint-fringe exactness is global or still
  conditional on a supplied merged-candidate fact such as `hmerge`.
- for BP close work, whether any `LittleOLinear` claim still assumes a budget
  for dense `interiorBlockPairRanges blockCount` entries rather than proving a
  compact close-directory payload bound from the actual layout.

Should not report "progress" only as scaffolding. A proof branch should land a
consumed lemma cluster, a representation layer, or a theorem that feeds the
active join.

A branch that is technically substantial but does not shorten the active path
to the capstone is exploratory, not complete. The worker should either keep
looping toward the named hard construction or report that the branch should be
treated as a side artifact rather than a merge-ready finish.

A branch that shortens the path but leaves the owned concrete component profile
or capstone theorem obviously unfinished is an iteration checkpoint, not a
valid unattended-loop endpoint. The worker should keep going unless it proves
the target statement itself impossible or has an extreme fifty-attempt
exhaustion dossier showing that further local progress now depends on a
fundamental design choice.

If the branch adds a new parameter, field, adapter, or bridge theorem, it must
also name the concrete instance that consumes it. If that concrete instance is
still missing and lies in the worker's owned files, the loop should continue.

A descriptor-select structure whose exactness is carried by fields such as
`descriptor_some_exact`, `descriptor_none_exact`,
`descriptor_word_choice_exact`, or a free `descriptorIndex` is a useful
obligation surface, not a closure witness. Unless the owned target explicitly
stopped at that surface, the worker should continue to the compact builder that
fills those fields from payload tables and accounts for the routing/index cost.

An exact packed descriptor-select profile with quotient/remainder routing is
likewise not a compact C1 witness if its only descriptor-space theorem is a
full per-occurrence local-delta-slot payload length. It must be followed by a
compact dense/sparse descriptor builder and a `LittleOLinear` payload theorem,
or by a formal obstruction theorem for that representation.

A BP range-witness or macro-candidate structure whose exactness is still an
`_exact_of_prefix_pos` theorem is likewise a useful obligation surface, not a
close-answer witness. Unless the owned target explicitly stopped at that
surface, the worker should continue to the charged endpoint-fringe repair and
the BP semantic theorem identifying the built prefix position with the
representative-array RMQ answer close.

An endpoint-fringe macro whose strongest exactness theorem is still
`_exact_of_merged_candidate` is also not the answer theorem. The worker should
continue until the merge fact is proved from the concrete payload entries and
BP/RMQ semantics, not supplied as a hypothesis.

For the succinct RMQ capstone, a new blocker theorem is not enough unless it
comes from an attempted positive construction and shows that the requested
target statement is mis-specified. Known blockers should be cited as design
constraints, not rediscovered as stop points.

For short-of-target stops, failed attempts alone are not enough. The report
should make clear why the branch nevertheless landed a meaningful positive
construction/profile. A formal impossibility theorem for the target statement
can justify stopping. Without that, only an extreme fifty-attempt exhaustion
dossier can replace target closure.

### Cost Or Space Worker

Must report:

- the operation model used by the new theorem;
- whether costs are derived from primitives or asserted as aggregate ticks;
- whether word operations are applied only to machine-bounded words;
- whether charged bits are the payload actually read by the decoder/query;
- the exact theorem carrying the machine-word bound for each new charged
  fixed-width table or payload-word primitive;
- any change to tracked caveats in `docs/ROADMAP.md` or
  `docs/FAMILY_SUMMARY.md`.

### Docs Or Audit Worker

Must report:

- stale claims found and fixed;
- claims intentionally left unchanged, with theorem references;
- any public theorem names mentioned in docs;
- whether those public theorem names are covered by `scripts/axiom_check.lean`,
  or why they are intentionally local-helper names;
- whether proof files were untouched.

Docs-only branches do not need a full build unless they edit imports, Lean
files, scripts, or generated theorem inventory.

## Coordinator Merge Gate

Before merging or cherry-picking a worker branch, the coordinator should run:

```powershell
git status --short
git diff --stat <base>...<worker>
git diff --name-only <base>...<worker>
```

Then inspect the diff for:

- edits outside the worker's owned file surface;
- public contract changes;
- new asserted-cost paths;
- new unbounded word primitives charged as O(1);
- decoupled payload accounting;
- stale docs caused by new theorem names or caveats;
- old superseded definitions left in source.

After merge or port, run the gate:

```powershell
lake build
lake env lean scripts\axiom_check.lean
lake env lean scripts\hub_axiom_check.lean
rg -n "\b(sorry|admit|axiom|unsafe|opaque|implemented_by|partial|extern|noncomputable)\b|import Mathlib" RMQ lakefile.toml scripts
rg -n "native_decide|Lean\.ofReduceBool" RMQ scripts
scripts\succinct_cost_lint.ps1
git diff --check
```

For proof-worker branches, also check that every new public exactness, cost,
space, or obstruction theorem mentioned in `docs/FAMILY_SUMMARY.md` is either
added to `scripts/axiom_check.lean` or explicitly classified as a local helper
in the worker report. Passing the old axiom gate is not enough if the branch
created a new public theorem surface and left it outside the curated inventory.

`git diff --check` may report repository-wide CRLF warnings. Treat new
whitespace errors as blockers; record pre-existing CRLF noise separately.

## Acceptance Rules

A worker branch is mergeable when all are true:

1. Its result feeds the current roadmap join theorem, proves a concrete
   component profile, or retires tracked debt.
2. Its file ownership is narrow enough to review.
3. The branch does not introduce forbidden terms, Mathlib, or proof-path
   `native_decide`.
4. Cost/space claims are model-faithful under `docs/CODEX_AUTONOMY.md`.
5. Any public claim drift is patched or explicitly assigned to the coordinator.
6. The worker report explains how the branch reduces the current distance to
   the active capstone, concrete component profile, or join theorem.
7. The integrated branch passes the coordinator gate, or a clear tool-only
   blocker is recorded.

## Rejection Or Port-Only Rules

Prefer cherry-picking or manually porting instead of merging when:

- the worker solved a useful lemma but redesigned a shared interface;
- the branch contains unrelated docs or formatting churn;
- the proof works only by weakening a public theorem;
- an asserted-cost shortcut appears beside a faithful path;
- the branch's theorem names conflict with current naming conventions.

Reject or send back for revision when:

- there is `sorry`, `admit`, a new axiom, or forbidden unsafe machinery;
- a headline theorem relies on uncounted linear work;
- charged bits are not tied to decoded payloads;
- the branch cannot explain how its theorem feeds the current join.
- the branch stops after adding only an API hook while its own docs/report say
  that the concrete builder, compact instance, payload-live witness, or final
  profile remains for the same owned target.
- the branch stops on another negative theorem without documenting a concrete
  construction attempt and a target-signature change forced by that theorem.
- the branch delivers docs, helper layers, adapters, or extra blockers while
  deferring the named hard construction that is still inside the worker's owned
  file surface.
- the branch proves a useful local kernel or partial profile and stops even
  though the owned concrete component profile has an obvious next local step.
- the branch claims a brick wall after only one or two proof failures, without
  attempts at nearby repaired signatures or construction variants.
- descriptor/select work proves only conditional local-run exactness, with no
  global `selectCosted` exactness over all target/occurrence queries.
- BP close work proves only charged block-summary reads, with no answer-close
  theorem consuming those summaries and endpoint-fringe repair.
- BP close work proves a sampled profile only by assuming a budget for dense
  `interiorBlockPairRanges blockCount` entries.
- a new O(1) charged word/table read lacks an explicit machine-word bound.
- theorem names suggest stronger semantics than their statements prove.

## Current Suggested Split

For the succinct RMQ capstone:

- Worker A owns the integration theorem, not just an interface. Its target is
  `concreteCompactBPCloseLCADirectory_profile` from
  `docs/SUCCINCT_FINAL_PATH.md`. If it needs an intermediate theorem, it should
  first close `bpRelativeRmmCandidateMerge_exact` and
  `concretePayloadLiveRelativeRmmBPCloseMacro_profile`, then immediately
  consume them in the directory profile. Adding a field such as
  `semantic_merge_exact`, a hypothesis such as `hmerge`, or a doc note saying
  that the concrete builder remains is an invalid final response.
- Worker B owns the compact relative-summary budget theorem. Its target is
  `concreteBPRelativeMinMaxArgSummaryTable_canonical_compact_payload_profile`
  from `docs/SUCCINCT_FINAL_PATH.md`. This is not closed while premises such as
  `hsuperPayload`, `hblockPayload`, a dense `interiorBlockPairRanges`
  envelope, or an unproved machine-word bound remain. If B closes that theorem
  before A has consumed it, B should continue to the next chain theorem it can
  own locally, rather than reporting only that the table is ready.
- Coordinator: merge order, adapter work, final `2*n + o(n), O(1)` theorem,
  gate, and docs.

Worker C can run once A/B land concrete component profiles, or earlier only if
its target is the named
`concreteBPNativeSuccinctRMQFamily_two_n_plus_o_constant_query_profile` join
or a true adapter theorem that consumes both A and B outputs.
