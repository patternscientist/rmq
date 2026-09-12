# BV-1 command ledger

Base/governance: `0e6a00f654abc64f8b68988fa9675b9a839dca2f`. Windows, pinned
Lean4.22.0, one task-local `.lake` tree created from source without cache links
or peer artifacts. `commands/*.json` records exact command, stage, deadline,
exit, duration, stdout/stderr and owned-process disposition. Later records
also pin every owned Lean source and lakefile by SHA-256 at launch.

## Preflight and environment

Initial git HEAD matched base exactly; detached worktree was clean. Created
`codex/bv-1-fully-charged-rank-select` without reset. Skill preflight required
rmq-proof-sprint and supplied actual runtime rmq-coordinator, rmq-proof-sprint,
rmq-audit-prompt; complete canonical set and exact governance ancestry passed.
Repeated preflight after the coordinator's infrastructure retry also passed.
Frozen matrix hash: `80BD59A314FD33D37076802954444DA24F65C87A2A91DE23BC668B6AF9CCEB24`.

The PATH elan shim attempted a network download even though the exact toolchain
was present. It failed connecting to github.com. Direct pinned binaries at
`C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0/bin` report Lean4.22.0
commit ba2cbbf09d4978f416e0ebd1fceeebc2c4138c05 and Lake5.0.0-src+ba2cbbf.
All subsequent owned commands use that binary directory, with
LEAN_NUM_THREADS=1. No toolchain or library upgrade occurred.

WMI process-command inspection was denied. Get-Process and artifact/log
progress were available and used. The process helper reports Windows
kill-on-close-job ownership. No Linux timeout/escape behavior has been tested
by BV-1; those branches are uncovered, not passed. Git emits a warning that its
user-level ignore file is unreadable; repository operations still succeeded.

## Development-loop evidence

| Stage / JSON artifact | Scope / rows | Runtime basis and deadline | Outcome |
| --- | --- | --- | --- |
| baseline-span-assembly | Shared decoder/compiler dependency build; REQ-BV-REUSE source availability, no new-target theorem | Cold117-module build,1200s deadline; inspected owned CPU/artifacts during silence | PASS exit0,1065.589s, no stderr. No retry. |
| normalization | New semantic transport leaf; OPS, value/proof separation | Warm imports,120s | PASS exit0,9.87s; two unused-simp warnings repaired. |
| normalization-final | Recheck changed normalization source | Source-warning repair,120s | PASS exit0,18.939s, no warnings. |
| normalization-axioms | Exact-type rank/select projections and10 explicit axiom inventories | Warm import,120s | PASS exit0,11.49s; propext, plus Quot.sound for numeric identities. |
| select-experiment-compile | Full new select source + validator import | Mostly warm126 modules,300s | Experiment compiled; validator failed on unavailable String.trimAscii, exit1,74.494s. Replaced by Lean4.22 String.trim. |
| select-reader-compile-r2 | Fixed validator and exact generic reader proposition | Prior dependencies warm,180s | PASS exit0,16.072s. Reader correctness is a defined target, not proved. |
| select-startup | Mandatory executable startup before semantic replay | Warm import,60s | PASS exit0,6.438s; version1 exact registry has18 cases. |
| select-known-case | First semantic runtime case, mixed true select | Startup measured6.438s,120s | PASS exit0,14.834s; exact packet7,1969 instructions,118 actual reads. |
| select-registry-v1 | All18 canonical select fixtures | Single case14.834s,600s margin | PASS exit0,30.208s,18 executed/expected/passed. |
| allocation-facts | Selected directory serialization and bit counts | Warm imports,180s | Exact identities elaborated; inequality failed on unavailable `.trans`; repaired with Nat.le_trans. |
| allocation-facts-repair-1 | Same allocation leaf after the local proof repair | Warm imports,180s | PASS exit0,8.193s, clean build. |
| allocation-facts-axioms | Five typed consumers, eight explicit axiom inventories | Warm imports,180s | PASS exit0,9.943s; propext and Quot.sound only. See ALLOCATION_FACTS.md for exact artifact spelling. |
| selector-controls-v1 | Production PowerShell omission/binding/rejection, eight exact controls | Actual semantic suite30.208s,180s per owned child | PASS8/8; omitted executes18, valid executes1, six rejection cases return2; three checker-source files unchanged. No mutation restoration claim. |
| crossing-startup / crossing-known-case | Test whether the threshold query actually reaches a second span load | Warm import,60s/120s | Startup passed; expected crossing FAILED exit1,8.177s: correct answer121 but zero second loads. This fixture does not establish crossing coverage. |
| reader-typed-axioms | Exact reader-packet/length consumers and canonical target quantifier pin | Warm imports,120s | PASS exit0,7.564s; packet uses propext/Quot.sound, length uses propext. No proof of CanonicalGenericReaderCorrect. |
| crossing-v2-startup / crossing-v2-known-case | Actual crossing descriptor and emitted second load in the new reader component | Previous startup10.02s,60s/120s | PASS exit0,12.281s/7.859s; n127,segment2,index0,one second load,packet1. |

The crossing fixture was materially changed after that failure: version2
selects an actual crossing descriptor in the canonical n127 allocation and
runs the physical-reader component, asserting the emitted second-load
instruction and its pre-state address/backing. It is component coverage, not
a claim of whole-select reachability. Its new startup/run outcomes follow in
the corresponding JSON artifacts. The failed version1 source is retained
byte-for-byte as controls/crossing_v1_expected_fail.lean (SHA256
F9201FE1970244D968AF47EB884D42E6BC2055984ED4A853985AFB64351ED758), matching
the original launch manifest. Running its canonical-crossing case must return
exit1 with second-loads=0; the failure is not silently dropped.

The exact checked temporary leaf consumers are retained byte-for-byte under
scripts/packed_bitvector_normalization_consumers.lean (SHA256
CF7C09F2CE8DF5D364933FD0BD982BC1835610F5D2B6CCAEBE0EDD6374C529A2) and
scripts/packed_bitvector_allocation_consumers.lean (SHA256
11625C223A9EA1952FE664DFEE7D8DC9C2C3CE798A6C74A39CCD24ACC42D08DE).
Use `lake env lean` on these committed copies to reproduce the imports. Their
bytes equal the temporary paths named in the original command records; moving
the unchanged scripts did not justify repeating their identical proof checks.

## Phase policy checks

The preliminary strict design check passed on the dirty phase tree. The
preliminary strict claim scan completed with1600 hits and zero strict failures;
its verbose baseline review output is not a BV-1 finding. The task-local
verify_phase.ps1 reruns the affected phase checks and archives full results as
compressed JSON, retaining command/deadline/exit/duration and archive hashes in
one summary. This keeps the noisy baseline output durable without repeating it
in the report. Working and committed-range checks have distinct purposes; the
precommit range still names the unchanged base and does not certify the later
phase commit. Postcommit range/design results must be recorded separately.

The first archived phase run failed its claim check after136.2s: its live
stdout spool was inside docs and the production scanner read its own emitted
baseline policy examples, producing seven strict failures in that temporary
stdout file. The archived result identifies each actual failing path. This is
a verification-runner defect, not a passing scan. verify_phase.ps1 now puts
owned transient logs under .lake/bv1-phase-process and archives the completed
result only afterward. No source, policy or scanner allowance changed. The
next run has this material process correction and is recorded independently.

Subsequent evidence is recorded separately as it finishes. No ledger entry
closes the full frozen operation,
allocation, execution, safety, capstone or mutation obligations.

## Historical route-phase verification plan

After the named theorem is proved and independently reconstructed, explicitly
build its module and every exact-type consumer; inspect the new exact
declarations' axioms; execute the complete versioned registry and committed
anti-bypass/mutation runner; run trust hygiene and both diff checks; run strict
design policy with the exact base. Public family/digestion prose triggers
strict claim drift. Request the coordinator's host-wide gate slot before full
aggregate certification. No aggregate slot has been requested or used here.

Final lake build/full registry and coordinator-scheduled aggregate are deferred
because this is still contract/feasibility work, not a frozen candidate. A
timeout or partial output will never be recorded as a passing gate.

## Post-route implementation ledger

The feasibility-phase description above is historical. The coordinator's
`APPROVE_ROUTE_AND_CONTINUE` disposition at645a050 authorizes the ongoing
full implementation. Every subsequent uniquely named JSON under `commands/`
records its exact arguments, source hashes, tree identity, owned process,
deadline, duration, exit and captured output. Leaf reports map these checks
to the exact propositions and independent consumers:

- `ALLOCATION_READER_PROOFS.md`: full39-component allocation, complete retained
  capacity, logical/physical reader, metadata and actual operation joins.
- `CANONICAL_MEMORY_BOUNDS.md`, `CANONICAL_SELECT_SAFETY.md`,
  `CANONICAL_RANK_ACCESS_SAFETY.md`: unconditional canonical memory/geometry
  bounds and all-prefix compiled safety for representable arguments.
- `MACHINE_CONTROLS.md`: checked12 actual-memory/static-instruction controls
  and8 production selector controls.
- `CAPSTONE_COMPOSITION.md`, `PUBLIC_MUTATION_CONTROLS.md` and
  `EXCEPTION_CONTROLS.md`: their own frozen requirements, current evidence
  and remaining checks; a draft specification is not a passing result.

Only one heavy Lean/Lake process runs in this build tree at a time. Workers
release the slot during offline repairs. The operation-joins records are
narrow development checks, not aggregate certification. The original matrix
remains frozen, and the full build and host-scheduled aggregate remain pending
until the final content is ready for certification.

## Final campaign results and certification boundary

All finite and typed-consumer campaigns have now passed on the completed
construction. Current reports supersede the earlier planned-final-checks
paragraphs above; the frozen route-era records remain historical evidence.

- `selector-controls-main-v2-final.json`: 46 exact cases (43 primitive runs
  and three guarded APIs), all four whole-operation crossings and 8/8 selectors;
  the omitted registry took 378.344 seconds.
- `selector-controls-validation-v1-final.json`: five validation mutations,
  17 exact verdict pins and 8/8 selectors, with exact restoration.
- `machine-controls-v1-20260912111955043-999b380b-omitted.json`: 12 actual
  memory/fault/static-instruction controls; its outer selector record passed 8/8.
- `exception-controls-replay-v1-omitted.json`: four valid parameterized
  exceptional routes, with 11 outer selector/wrong-route controls.
- `leaf-replay-20260912130101742-summary.json`: 8/8 retained exact consumers,
  52 typed assertions, 68 standard-axiom reports and unchanged byte hashes.
- The public final selector summary under
  `controls/public_mutations/records/campaign-final-v1-20260912131342256-3b473507/`
  passed 32 cases and 8/8 selectors in 592.664 seconds. All constructors compile;
  the two accepts and 30 precisely located semantic rejections meet the frozen
  registry. All 276 dependency hashes and 64 generated fixtures are preserved.

These are exact retained local outcomes. The failed earlier public fixture
and resource generations remain failed evidence. Current leaf provenance is
established by the fresh retained-consumer replay, not by assuming that every
historical temporary file's original bytes can still be recovered.

The first final staging check failed: the new -text rules preserve CRLF bytes,
which Git's default whitespace checker classified as trailing whitespace.
Diagnostic-only recognition of CR-at-EOL isolated 38 recorded artifacts ending
with a blank line and no ordinary trailing-space/indentation failures. The
inventory is `commands/staged-whitespace-diagnostic-v1.json`; neither diagnostic
command is a passing policy check. Root requested a precise attribute amendment
while retaining every recorded source/fixture byte. The build manifest's index
was separately corrected to its unchanged raw 691-byte blob rather than
renormalized. Final staged/range policy checks and an actual committed-blob/
fresh-checkout comparison remain required.

The aggregate slot has been requested and is on the coordinator's diagnostic
hold after a peer aggregate timed out. No BV-1 aggregate has run. Its first
build stage will satisfy the full-build obligation when the slot is granted;
there will be no duplicate standalone broad build.


`implementation-final-policy-v1.json` subsequently passed all seven checks:
trust, native-trust, staged diff, working diff, the historical parent range,
strict design and strict claims. The strict claim scan took 221.268 seconds
under its 300-second bound. The candidate's new committed range is checked
separately after commit. `whitespace-attributes-v1.json` passed 90/90 effective
working/index comparisons: 38 exact EOF artifacts, five normal BV controls and
two unaffected outside controls on both surfaces. `frozen-rows-final-policy-v1.json`
again passed all 30 original row-byte comparisons and the full frozen hash.
