# A08 blind audit of the B7 charged sparse level

Date: 2026-07-19

Auditor: A08

Mode: FRESH BLIND DELTA

Base: `f6564ec`

Target: `6ad4198`

Audited branch: `claude/b7-charged-sparse-level`

Audit branch: `codex/a08-b7-sparse-level-audit`
Permission: REPORT-ONLY

## Scope and method

This was a fresh audit of `f6564ec..6ad4198`. I did not seek out or read prior
audit reports, worker completion reports, coordinator round logs, or
`docs/internal/AUDIT_AND_A_DESIGN.md`. I treated the B7 acceptance matrix and
worklogs as worker-authored claims and re-derived the conclusions from Lean
source, Git history, executable checks, and direct axiom queries.

The only worktree change made by this audit is this report. Lean sources,
scripts, matrices, and documentation were read-only.

Evidence tiers used below:

- **T1**: Lean definition/theorem body, direct caller/history inspection, or a
  direct-module `#print axioms` result.
- **T2**: successful build, executable harness, lint, or repository scan.
- **T3**: Git diff/history evidence establishing when and how a change landed.
- **T4**: prose, comments, matrix cells, or worklogs. T4 records a claim but is
  never sufficient by itself for a positive verdict.

## Overall verdict

**REJECT.** The charged sparse-level mechanism itself is live and removes the
identified runtime-derived `Nat.log2`/`bpSparseLogSpan` computation from the
accepted query route. Its width, space, provenance, atomic storage/read landing,
and harness behavior are substantially confirmed. The rung nevertheless fails
acceptance because:

1. 24 of 25 frozen matrix rows still have empty evidence cells and remain Open;
2. the claimed semantic tightness at 33, and therefore the assertion that the
   old `cost <= 30` conjunct became unprovable, is not established by the Lean
   theorems cited for it; and
3. a public historical identity silently changed from 328 to 352, while the
   README, family summary, and model-adequacy documentation retain incompatible
   pre-rung claims.

There is no P0 finding. The audit has three P1 findings, one P2 finding, and two
P3 findings.

## Findings

### P1 — The frozen acceptance matrix is not an evidence-complete freeze

At freeze commit `19e3a69`, the table at
`docs/internal/B7_SPARSE_LEVEL_ACCEPTANCE_MATRIX.md:101-127` contains 25 rows.
Only `REQ-B7-00` has a nonempty “Evidence obtained” cell and status Closed.
`REQ-B7-01` through `REQ-B7-21`, `CHK-B7-01`, `CHK-B7-02`, and `STR-B7-01`
have empty evidence cells and remain Open. HEAD itself acknowledges at
`docs/internal/B7_SPARSE_LEVEL_ACCEPTANCE_MATRIX.md:183-190` that the appended
material was not written into the frozen cells and that no additional row is
closed.

`git diff --unified=0 19e3a69..6ad4198 --
docs/internal/B7_SPARSE_LEVEL_ACCEPTANCE_MATRIX.md` shows only appended text
after the frozen table: no requirement/scope/evidence-needed/consumer/
anti-vacuity cell was weakened and no table row was added. That preserves the
words of the freeze, but it does not make 24 empty evidence cells establish
their requirements. This is especially material for rows whose appended prose
claims “tight” or “attained” without a corresponding lower-bound theorem.

Evidence: T1/T3 for the table/diff; T4 only for the appended status prose.

### P1 — “Tight at 33” and “the old slack theorem is now impossible” are not proved

The old declaration
`canonicalRelativeRmmPrincipledInteriorChargedTraceCost_announced_slack_...`
is absent at HEAD. The tombstone at
`RMQ/Core/SuccinctClose/EndpointFringe/InteriorCandidate/InteriorDirectory.lean:5541-5555`
says the cross-macro branch “attains the cap.” The actual proof surface is only
an upper-bound surface:

- local two-span cost `<= 11` at `InteriorDirectory.lean:5259-5260`;
- global two-span cost `<= 11` at `InteriorDirectory.lean:5314-5315`;
- cross-macro cost `<= 33` at `InteriorDirectory.lean:5418-5419`; and
- whole interior cost `<= 33` at `InteriorDirectory.lean:5461-5467`.

The cross-macro dispatcher branch ends with bare
`exact hcross` at `InteriorDirectory.lean:5516-5517`. This gives zero *proof
slack* against the upper bound, but it is not a witness or lower bound showing
that an execution has cost 33. A source-wide search found no `cost = 33`,
`33 <= cost`, or existential witness for this path. Consequently, deletion of
the old slack artifact is confirmed, but the stronger claim that its middle
conjunct `30 < cap` “could not have survived because the swap consumes the
headroom” is literally false: with `cap = 33`, that conjunct remains provable.
The conjunct that would have to become false is the first, `cost <= 30`, and the
current upper-bound-only theorem does not refute it.

Evidence: T1. Verdict impact: Item 3 is REFUTED as worded; Item 4 is UNCLEAR.

### P1 — A frozen-looking public historical identity silently changed 328 → 352

At the base,
`f6564ec:RMQ/Core/SuccinctRMQClassic.lean:135-138` states:

```lean
theorem canonicalTransitionalQueryCost_eq :
    canonicalTransitionalQueryCost = 328 := by
  rfl
```

At HEAD, the same public theorem name at
`RMQ/Core/SuccinctRMQClassic.lean:147-150` states `= 352`. The underlying
definition is still described as the “Checked historical U2 cost” at
`SuccinctRMQClassic.lean:101-105`, but it depends on a live compact component
rather than pinned literal components. This is exactly the historical-drift
failure that the rung says was repaired for 207 and 126. Those two identities
are pinned correctly; the 328 identity was neither pinned nor renamed.

The frozen matrix requirement at
`docs/internal/B7_SPARSE_LEVEL_ACCEPTANCE_MATRIX.md:108` explicitly names the
historical `142/76/328` pattern and requires frozen legacy anchors to remain
untouched. The same-name change therefore refutes Item 10.

Evidence: T1/T3.

### P2 — Public documentation contradicts the new public theorem surface

HEAD still presents the pre-swap route as current in multiple public places:

- `README.md:70-82`, `README.md:140`, and `README.md:334` state a 207 bound,
  interior cap 30, or the old component algebra;
- `docs/FAMILY_SUMMARY.md:9`, `:32-48`, `:133`, `:446`, and `:1041` state the
  old 207/30 story, including that logs remain uncharged; and
- `docs/PAPER_MODEL_ADEQUACY.md:229-256` refers to the removed slack theorem and
  old `...thirty_literal` bridge as live/checkable support.

This conflicts with the current `queryCost_eq = 210` and with the repository
rule that headline/public theorem changes update `docs/FAMILY_SUMMARY.md` and,
when relevant, `README.md`.

Evidence: T1/T3.

### P3 — A post-swap theorem name still says “thirty” while its statement uses 33

`InteriorDirectory.lean:5529-5539` retains the compatibility theorem name
`...cost_le_thirty...`, but the statement is against the live interior cap,
which is 33. This is not a renamed/weakened survivor of the deleted conjunction,
but the name is misleading and makes searches for the former cap ambiguous.

Evidence: T1.

### P3 — The headline “readWord of counted store” phrasing outruns the theorem

`RMQ/Headlines/RMQ.lean:502-508` describes the result as “readWord of the counted
store layout.” The consumed theorem proves `event.isReadWord` over the accepted
trace; the backing/store-location conclusion comes from separate adequacy and
provenance theorems. The needed separate results exist, so this is wording drift,
not a functional or provenance failure.

Evidence: T1.

## Item-by-item verdicts

### 1. Freeze integrity — **REFUTED**

The frozen requirement columns are byte-stable from `19e3a69` to HEAD, and no
new table row was added post-freeze. However, the evidence column fails its
purpose: every row except `REQ-B7-00` has an empty evidence cell and Open status
at `B7_SPARSE_LEVEL_ACCEPTANCE_MATRIX.md:101-127`. The append-only note at
`:183-190` explicitly confirms that state. Therefore “no row weakened” is
confirmed, but the requested stronger integrity check fails for 24 rows.

Positive evidence tiers: T1/T3. See P1 finding 1.

### 2. The silent computation is actually gone — **CONFIRMED**

The accepted whole-query caller chain is:

1. `SuccinctFinalRAM.lean:4426-4432`,
   `concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult`;
2. `SuccinctFinalRAM.lean:3265-3280`, the accepted global evaluator branch;
3. `SuccinctFinalRAM.lean:2330-2340`, the accepted all-size LCA route;
4. `ChargedFringeWiring.lean:50-64`, which calls the charged interior route;
5. `ConcreteDirectoryRAM.lean:1188-1193`; then
6. `InteriorDirectory.lean:2351-2398`.

At the two executed local/global sites in `InteriorDirectory.lean:2351-2398`,
the code reads `offsets.localLevel count` or
`offsets.globalLevel macroSpanCount`, then decodes the one cell with `/ domain`
and `% domain`. The two Costed twins at `InteriorDirectory.lean:1824-1869` do the
same through `canonicalRelativeRmmMachineReadNatCosted`. Their correspondence is
proved in the `_refines` chain at `InteriorDirectory.lean:3440-3480`.

Every surviving `Nat.log2`/`bpSparseLogSpan` occurrence was reclassified:

- `SparseLevelTable.lean:55-56`: table construction;
- `LocalGlobalSparse.lean:17-39,590-611`: logical/reference specifications;
- `WordReads.lean:190-207,247-264`: a legacy logical word-list model consumed
  by the compatibility directory at `InteriorDirectory.lean:938-959`, not by
  the accepted caller chain; and
- old `InteriorRAM.lean:559-653,805-900`: compatibility `OfReady`/`OfSizeGe`
  routes, also outside the accepted chain.

I independently followed the `WordReads.lean` consumers rather than accepting
their alleged unreachability. They do not reach the accepted headline object.

An initially plausible broader objection also fails: the recursive local BP
decoder at `LocalBPDecoder.lean:797-805` is compatibility/spec code. The accepted
same-block branch in `ChargedFringeWiring.lean:50-64` calls
`bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegment`; its definition
at `ChargedSameBlockChunks.lean:49-64` uses charged chunk reads with a literal
`Nat.min ... 33`, and its fixed bound is proved at `:66-75`.

Positive evidence tier: T1, supported by T2 builds.

### 3. The slack artifact is deleted, not weakened — **REFUTED**

The named conjunction theorem is absent, and no weakened or renamed conjunction
survivor was found. The tombstone is present at
`InteriorDirectory.lean:5541-5555`. What is not confirmed is “it could not have
survived”: the branch proves only `cost <= 33`, not equality or a lower bound.
Bare `exact hcross` at `:5516-5517` establishes zero proof slack, not semantic
attainment. Moreover, the prompt identifies `30 < cap` as the conjunct that
must become unprovable, but `cap = 33` proves exactly that conjunct. The intended
load-bearing conjunct is `cost <= 30`, and no checked lower bound refutes it.
The misleading `...cost_le_thirty...` name at `:5529-5539` is a P3 naming issue,
not the old artifact.

Positive evidence tier for deletion: T1. Insufficient evidence for
impossibility: only T4 comments plus an upper-bound theorem.

### 4. The literal is justified by reads, not by slack — **UNCLEAR**

The named algebra is real. `SuccinctFinalRAM.lean:8791-8805` defines the
component record and algebra; the live components are selected at `:8811-8818`;
and `:8823-8830` proves close cost 129 and whole cost 210 by `rfl`. This is an
algebra of named components, not a free-standing asserted numeral.

Direct-module axiom queries reported that both
`RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost_eq`
and `RMQ.SuccinctClassic.queryCost_eq` do not depend on axioms.

Historical 207/126 is pinned correctly in the definitions, not merely in
today's equalities: literal component definitions occur at
`SuccinctFinalRAM.lean:8852`, `:8858`, `:8864`, and `:8874`; the frozen algebra
uses those definitions at `:8947-8954`; and the 207/126 identities are `rfl` at
`:8959-8972`.

The four dispatcher bounds at `InteriorDirectory.lean:5461-5517` have the
claimed proof slack: within-macro 7, adjacent 11, left-middle 11, and cross-macro
zero. But “the maximizing branch attains the cap” is not derived. Because that
clause is load-bearing for semantic tightness, the compound item is UNCLEAR.

Positive evidence tiers: T1/T2 for algebra, pinning, and axiom freedom; no
sufficient evidence for attainment.

### 5. The swap is live, not decorative — **CONFIRMED**

The harness has 21 windows. Source/delta comparison gives exactly nine windows
with positive interior count moving and twelve without live interior remaining
unchanged. The nine changes are:

- n=24: 112→114, 107→109, 105→107;
- n=64: 116→118, 126→128; and
- the two n=128 shapes: 92→93, 96→97, 93→94, 95→96.

The twelve unchanged cases are three invalid windows, three cross-block windows
with count zero, and six same-block windows. A fresh harness run confirmed all
21 current values/results and the 210 cap.

The invocation condition is genuinely
`leftBlock + 1 < rightBlock` at
`ConcreteDirectoryRAM.lean:2319-2340`, with count
`rightBlock - leftBlock - 1`.

The `tie-boundary-live-interior` fixture at `CostHarness.lean:198-233` has n=24,
base=5, blockSize=10, blockCount=4. Its minimum value occurs at indices
5, 7, 9, 11, 13, 16, and 18. Cartesian-close mapping places all of those in the
three interior blocks for the full window; neither endpoint fringe block
contains a minimum. The harness returns index 5, so the leftmost decision is
load-bearing on the interior range-min rather than a fringe tie.

The observed shape-determined delta is consistent with the construction. The
charged table cell is fixed-width for a shape, and the machine-read cost depends
on that shape's packed-table/word geometry, not monotonically on the queried
count. Thus +2 at counts 1,2,3,8 for n=24/64 and +1 at counts 9,10,14 for both
n=128 shapes is expected, not evidence of an unexamined count-dependent loop.

Positive evidence tiers: T1/T2/T3.

### 6. Width fit — **CONFIRMED**

The one-word local/global theorems at `InteriorDirectory.lean:4440-4509` use the
route's macro-crossing hypothesis, not a public size threshold. The dispatcher
derives that exact hypothesis from its branch guard and bounds at
`InteriorDirectory.lean:5481-5493`. The lemma
`canonicalRelativeRmmBase_ten_le_of_macro_crossing` derives `10 <= base` at
`:4339-4365`; it is not an assumption.

The small-size case is saved by reachability. At size 4, the raw fit can fail,
but macro crossing would require `9 < 1`, which is false. It is not excluded by
a threshold. Branches without macro crossing retain unconditional local/global
`<= 7`-word bounds at `:4240-4301`, consumed in the `<= 8` read branches at
`:5190-5209`. Small successful reachability is also exercised in
`ReviewerReachabilitySmall.lean:2100-2237` and exported at `:2671-2689`.

Positive evidence tier: T1.

### 7. Space — **CONFIRMED**

The width bridge is explicit:
`bpSparseLevelWidth_le_square_width` at `InteriorDirectory.lean:5883-5898`.
The raw overhead contains separate local/global table terms at `:5921-5938`,
the decomposition is proved at `:5976-5982`, and the linear capacity is updated
from 218 to 527 at `:5984-6170`. The directory payload equality follows at
`:6172-6196`.

The asymptotic envelopes are genuinely different. The local table is bounded
through the cube lemma, while the sampled global table has the distinct
sampled/global envelope at `InteriorDirectory.lean:6313-6363`. Both feed the
little-o result at `:6429-6494`.

The public statement shape is preserved:
`FlatPayload.lean:1813-1826` defines the overhead,
`FlatPayload.lean:1929-1933` proves
`buildPayload.length <= 2 * n + overhead n`, and
`SuccinctRMQClassic.lean:958-966` retains the corresponding public theorem and
`overhead = o(n)` interface.

Positive evidence tier: T1, supported by T2 builds.

### 8. Vocabulary and provenance — **CONFIRMED**

`SuccinctFinalRAM.lean:9708-9725` proves `..._readWord_only` by unfolding and
induction over the amended accepted whole-query object. It is not an unchanged
theorem about an obsolete predecessor; the object changed in atomic commit
`c45e62c` and this proof was rebuilt over that definition.

W19 covers the new local-level successful read at
`ReviewerReachabilitySmall.lean:2028-2238`, embeds it through the LCA path at
`:2240-2266`, and exports the canonical-close source occurrence at `:2671-2808`.
The level tables are subregions of the existing canonical-close source rather
than a new segment.

`ReviewerPhysical.lean:88-113` maps canonical-close/fringe/select to 20/21/22
and maps `>= 23` to none; completeness is still equivalent to `< 23` at
`:891-928`. The accepted whole trace retains `< 23` and occurrence/value
coverage at `SuccinctFinalRAM.lean:6774-6799` and `:7008-7210`.

Positive evidence tiers: T1/T3. The separate headline wording caveat is P3.

### 9. No dead sources, ever — **CONFIRMED**

Commit history supports the atomicity claim when “counted source” is read as a
region integrated into the public counted component store:

- `78d15c3` introduces the generic table format and generic reader together;
- `af6023d` instantiates local/global table values and an overhead definition,
  but the component payload at
  `af6023d:InteriorDirectory.lean:1506-1510` still omits those table payloads;
  therefore no public counted store region is dead in that state; and
- `c45e62c` adds the local/global table payloads to the component store and, in
  the same commit, adds offsets/readers and swaps both Costed and Computation
  paths (`InteriorDirectory.lean:1824-1869,2351-2398`).

`git log -S` confirms that the actual payload append and the live
`offsets.localLevel count` read first appear together at `c45e62c`. A standalone
value/overhead definition before that commit is not a counted storage region.
No intermediate commit was found with integrated counted storage and no reader.

Positive evidence tier: T3, with T1 source confirmation.

### 10. No weakening elsewhere — **REFUTED**

The delta's Lean hygiene is clean, and the 207/126 pinned definitions are
preserved. Nevertheless, the unchanged-name public historical identity
`canonicalTransitionalQueryCost_eq` changed 328→352, contrary to the frozen
legacy requirement; see P1 finding 3. Public documentation also remains stale;
see P2.

The base-to-target `git diff --check` exits 2 solely because the committed
`docs/internal/B7_STEP2_WIP.patch` contains single-space blank context lines.
Those are patch syntax/context by construction and are not reported as a defect.

The restricted hygiene scan found no forbidden declaration/import in `RMQ` or
`lakefile.toml`. The `native_decide|Lean.ofReduceBool` scan finds only the scan
strings themselves in scripts, not an actual use in `RMQ` or `RMQExamples`.

Positive evidence tiers: T1/T2/T3. Overall item refuted by the public identity
and documentation findings.

## Objections considered and rejected

1. **“The WordReads pair still executes the logarithm.”** Rejected after
   following its consumers: it feeds a compatibility logical directory, not the
   accepted `SuccinctFinalRAM` caller chain.
2. **“The old recursive same-block scan leaves a separate growing silent loop.”**
   Rejected after resolving the accepted dispatch: it uses the charged, capped
   33-chunk fold in `ChargedSameBlockChunks.lean`; the recursive decoder is a
   compatibility/spec layer.
3. **“Bare exact proves the 33 cap is attained.”** Rejected. It proves only that
   an already available `<= 33` result closes a `<= 33` goal.
4. **“Pre-atomic instantiated table values are dead counted storage.”** Rejected.
   Before `c45e62c` they are definitions outside the integrated component-store
   payload. Store inclusion and live reads land together.
5. **“The n=128 +1 versus n=24/64 +2 delta shows a count anomaly.”** Rejected.
   It follows fixed-width, shape-dependent table-read geometry.
6. **“Size 4 was excluded by a hidden threshold.”** Rejected. The one-word
   theorem is guarded by the actual macro-crossing condition, which is
   unreachable for that shape; unconditional multiword bounds cover the other
   branches.
7. **“The committed `.patch` whitespace is a source defect.”** Rejected per
   direct inspection: the flagged lines are single-space blank patch-context
   lines, not whitespace damage in Lean or documentation source.

## Verification outcomes

Durations are wall-clock milliseconds measured by the audit wrapper. Commands
expected to be heavy were serialized with the named Windows mutex
`Global\RMQHeavyVerification`; the mutex wait is noted separately. Preliminary
sandbox/network failures and superseded raced attempts were excluded from these
authoritative results.

| Command | Exit | Duration | Result |
|---|---:|---:|---|
| `git diff --stat f6564ec..6ad4198` | 0 | 2,399 ms | 24 files, 8,362 insertions, 490 deletions |
| `git diff --check f6564ec..6ad4198` | 2 | 837 ms | Only committed `.patch` context-line whitespace; documented exception |
| `lake build RMQ` | 0 | 388,281 ms | Pass; mutex wait 7 ms; linter warnings only |
| `lake build RMQPaper RMQExamples` | 0 | 51,955 ms | Pass |
| `lake exe rmq_succinct_classic_cost_harness` | 0 | 45,036 ms | All 21 windows pass; route bound 210; mutex wait 4 ms |
| `lake env lean scripts/headline_axiom_check.lean` | 0 | 68,349 ms | Pass; headline cost alias reports no axioms; mutex wait 8 ms |
| direct-module `lake env lean --stdin` axiom check for the exact final and classic cost theorems | 0 | 3,803 ms | Both report no axioms; mutex wait 7 ms |
| `powershell -ExecutionPolicy Bypass -File scripts/paper_topology_lint.ps1` | 0 | 127,207 ms | PASS: 83 broad identifiers; 49 paper identifiers resolved; mutex wait 5 ms |
| `powershell -ExecutionPolicy Bypass -File scripts/claim_drift_scan.ps1` | 0 | 10,169 ms | 736 hits, 0 strict failures |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque\|implemented_by\|partial\|extern\|noncomputable)\b\|import Mathlib" RMQ lakefile.toml` | 1 | 85 ms | No matches (clean) |
| `rg -n "native_decide\|Lean\.ofReduceBool" RMQ RMQExamples scripts` | 0 | 80 ms | Only self-referential scan/gate strings in scripts; no actual RMQ/RMQExamples use |

The exact stdin used for the direct-module axiom row was:

```powershell
@'
import RMQ.Core.SuccinctFinalRAM
import RMQ.Core.SuccinctRMQClassic
#print axioms RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost_eq
#print axioms RMQ.SuccinctClassic.queryCost_eq
'@ | lake env lean --stdin
```

Known-red checks owned by other branches were recorded but not attributed to B7:
`scripts/wordram_axiom_check.lean`, `scripts/axiom_check.lean`, and
`lake exe rmq_succinct_classic_validate`.

The post-report strict claim-drift and tree `git diff --check` results are
recorded in the final section below after running them on this exact report tree.

## Explicit answer: remaining uncharged input-growing computation

**No — none was found on the accepted query route under the repository's
declared charged-trace model.** The runtime-derived sparse logarithm/span is
replaced by one charged packed-cell read, and all surviving executable-looking
logarithm occurrences are construction, specification, or compatibility paths.
The other tempting candidate, the old recursive same-block decoder, is also not
the accepted implementation: the live dispatcher uses the charged fixed-cap
chunk fold.

This answer is deliberately model-specific. It says that the accepted route has
no remaining uncharged operation or loop whose iteration count grows with the
input. It does not claim that every Lean/Nat arithmetic instruction is assigned
a conventional CPU-cycle cost, nor does it turn the proof-level trace model into
an executable-runtime theorem.

## Final report-tree checks

The required pre-commit checks were run on the worktree containing this report:

| Command | Exit | Duration | Result |
|---|---:|---:|---|
| `powershell -ExecutionPolicy Bypass -File scripts/claim_drift_scan.ps1 -Strict` | 0 | 4,240 ms | Scan complete: 743 hits, 0 strict failures |
| `git diff --cached --check` | 0 | 79 ms | Clean; the staged delta is this report only |

After inserting this result record, both commands were rerun once more before
the commit so that the committed report text itself was covered by the gates.
