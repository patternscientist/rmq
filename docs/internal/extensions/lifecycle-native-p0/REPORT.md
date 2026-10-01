Status: CANDIDATE_COMPLETE
I found no assigned or inherited acceptance criterion unmet; coordinator acceptance is still required.

# LIFE-NATIVE-P0 — native finalization ownership and capacity

## Identity and submitted scope

Handle: LIFE-NATIVE-P0. Task: `01a0c12b-88c6-7ef2-bd68-bf63cd80b872`.
Requested task title: `(LIFE-NATIVE-P0) Validate native finalization ownership and capacity`.
Worktree: `C:/Users/poin/.codex/worktrees/af4b/RMQ`.
Private branch: `codex/life-native-p0-owned-finalization`.
Exact base: `bf31f983205175481fcb659caa4dfb70ef43e361`.
Governance: `7b227c49ef2ec044b702126cc41c9add847eed01`.
Final implementation/candidate source commit: `bea5ce75f788c4035031ba81e69d8de36eda3f92`.

The source commit freezes the final probe, runner, registry and measured receipts.
This report and final certification are a subsequent documentation commit; its
exact packaging hash is supplied with the final handoff and is recoverable with
`git log -1 --format=%H -- docs/internal/extensions/lifecycle-native-p0/REPORT.md`.
The document does not pretend to contain its own future commit hash. This follows
the source-freeze/report separation already recorded in WDD-20260912-NATIVE1-013.
No executable source changes occur in that packaging commit.

The fresh checkout was clean and distinct from the dirty primary and experiment
source. Both initial and exact-base preflights passed with actual runtime skills
`rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint`; the required role was
`rmq-proof-sprint`. [START.json](START.json) is the launch identity receipt.
All work is local and unpublished. No push, merge, production ABI change,
toolchain installation or coordinator acceptance occurred.

Complete changed paths from the exact base:

- `native/packed-rmq/tests/lifecycle_storage_probe.c`
- `scripts/packed_native_lifecycle_storage_replay.ps1`
- `docs/internal/DESIGN_DECISIONS.md` (append)
- `docs/internal/WORKFLOW_DESIGN_DECISIONS.md` (append)
- `docs/internal/extensions/lifecycle-native-p0/.gitattributes`
- `docs/internal/extensions/lifecycle-native-p0/START.json`
- `docs/internal/extensions/lifecycle-native-p0/REQUIREMENTS.json`
- `docs/internal/extensions/lifecycle-native-p0/ACCEPTANCE_ROWS.txt`
- `docs/internal/extensions/lifecycle-native-p0/ACCEPTANCE_MATRIX.md`
- `docs/internal/extensions/lifecycle-native-p0/VERIFY_CONTRACT.ps1`
- `docs/internal/extensions/lifecycle-native-p0/BASELINE.json`
- `docs/internal/extensions/lifecycle-native-p0/RUNTIME_SOURCE.json`
- `docs/internal/extensions/lifecycle-native-p0/BOUNDARY.md`
- `docs/internal/extensions/lifecycle-native-p0/REGISTRY.json`
- `docs/internal/extensions/lifecycle-native-p0/RESULTS.json`
- `docs/internal/extensions/lifecycle-native-p0/REPORT.md`
- `docs/internal/extensions/lifecycle-native-p0/CERTIFICATION.json`

## Result and measured boundary

The final complete owned replay passed **23 operational cases, 58 bounded
stages and 65 checks**, actual runner and outer wrapper exits 0, in **161.682 s**.
It held `Local\RMQLifecycleImplementationHeavy20260920` throughout. Complete
numeric projections and all stage exits, deadlines, raw-output paths and hashes
are in [RESULTS.json](RESULTS.json). Its raw source receipt is
`C:/Users/poin/.codex/worktrees/af4b/RMQ/.lake/lifecycle-native-p0/runs/7c97f92144714f9c9d126762635d07b4/SUMMARY.json`.
Outer ownership evidence is
`C:/Users/poin/.codex/worktrees/af4b/RMQ/.lake/lifecycle-native-p0/final-5a155de9bddb4157bb5ff71eb8d515aa/receipt.json`.

The independent input is `[101,-7,303,303,505,-19]`, represented by six distinct
destructor-counted external objects. The two equal values have distinct source
IDs. All ordinary input arrays start at capacity 32; empty-input pop cases start
with size zero and that same explicit capacity. Snapshots traverse only registered
live owners and store numbers, never additional Lean references.

| Handoff observation | Output size/capacity | Output requested bytes | All registered array bytes | Live elements / element references | Old array reachable |
| --- | --- | --- | --- | --- | --- |
| Unique shrink to two | 2 / 32 | 280 | 280 | 2 / 2 | Yes |
| Shared shrink to two | 2 / 32 | 280 | 560 | 6 / 8 | Yes |
| Exclusive replacement, positions [1,5) | 4 / 4 | 56 | 56 | 4 / 4 | No |
| Same replacement with old alias | 4 / 4 | 56 | 336 | 6 / 10 | Yes |
| Empty replacement | 0 / 0 | 24 | 24 | 0 / 0 | No |
| Tail replacement with discarded-element alias | 2 / 2 | 40 | 40 | 3 / 3 | No |

The requested-byte equation on this checked x64 shape is
`24 + 8 * lean_array_capacity(a)`. It is not derived from logical size.
Element reference counts read the actual single-thread runtime `m_rc` of live
objects. Destructor counters record actual external-object destruction. The
table excludes element-object bytes, static test payloads, runtime global
support, nested production arrays, allocator overhead and RSS. Old-array
reachability concerns the probe's registered owners; absence of arbitrary
foreign aliases is not inferred. Empty-container deallocation is source-backed
by the runtime release path, not measured by a nonexistent element destructor.

The consuming route allocates `lean_alloc_array(0,m)`, acquires each selected
reference with `lean_array_uget`, initializes at most m entries with push, then
releases the old owner. Source positions cover prefix, an interval overlapping
the hypothetical in-place destination, tail and empty output. Temporary
source-plus-output storage is a distinct peak (336 requested array bytes for
the four-element replacement), while final exclusive retention is 56.

Five injected failure stages have independently checked pre-cleanup states:
before allocation (no output), after allocation (output size zero), mid-copy
(size two), before handoff (full output and live source), and after consumption
(full output and absent source). Controlled failure consumes/cleans source and
initialized output, with an explicit retained-alias case. An omitted cleanup
action is measured and rejected before the harness repairs it.

The separate `--fatal-oom` mode directly invokes the pinned runtime's fatal
handler. It exits 1 with exactly `INTERNAL PANIC: out of memory\n`, no stdout,
and `cleanupClaim=false`. This is a fatal-handler observation, not actual
allocator exhaustion or a recovery guarantee. All destructor-counted semantic
fixtures finish restored, with zero registered owners and exactly one destructor
call per allocated token.

## Exact predicates, mutations and executable reach

There is no new Lean theorem, formal machine or kernel trust assumption.
These are C runtime measurements plus independently checked operational
predicates. Let S be the measured handoff, n the fixture input count, b the
selected starting position and m its length, with `0 <= b`, `b+m <= n <= 6`.
All registered cases satisfy these guards; no claim quantifies over arbitrary
foreign programs or all allocator states.

The strict successful-transfer predicate P requires: output values and source
IDs equal the independently specified interval; output size m and capacity at
most m; requested output bytes at most 24+8m; a unique new output container;
no source owner, old array alias or separate element alias; and, for every token
ID i in 0..5, actual reference count equal to the selected-interval indicator
and destructor count one exactly for discarded allocated tokens. The C
`transfer_predicate` and PowerShell `Get-LNMeasuredFailure` evaluate these
same projections. `Assert-LNSnapshot` additionally reconstructs counts from
actual observed array entries, deduplicating old array aliases.

The cleanup predicate requires absent source/output owners; exactly the allowed
old alias (0 or 1), preserving original values with owner RC 1 when present;
and the corresponding exact element reference/destructor projections.
The alias-aware transfer predicate adds its declared old-array or element
reference contributions and never labels that result exclusive.

| Negative operational fixture | Matching positive / full guard | P versus Q and exact rejecting surface |
| --- | --- | --- |
| `negative-shrink` | `replace-prefix`, n=6,b=0,m=2, aliases=0 | Q is the same strict P; actual shrink leaves capacity 32, so `capacity`, exit 3. |
| `negative-alias` | `replace-overlap`, n=6,b=1,m=4, allowed aliases=0 | Q is the same strict P; an actual old alias remains, so `ownership`, exit 3. The alias-aware positive is not substituted for P. |
| `negative-cleanup` | `fail-handoff`, n=6,b=1,m=4, old alias=0, stage=4 | Q is the same cleanup predicate; actual omission of output release leaves the buffer live, so `cleanup`, exit 3, before repair. |
| `negative-value` | `replace-overlap`, n=6,b=1,m=4, aliases=0 | Q is the same strict P; the first read copies position 0 instead of 1, so `values`, exit 3. |

The registry fixes ordered IDs, all eight case-input fields, expected exits and
failure surfaces. The runner checks both C's complete tuple and actual stage
states. Relabeling real allocation-only failure output as mid-copy, or real
pre-consumption output as post-consumption failure, rejects at
`MEASUREMENT: intermediate`. This repairs the review finding that identical
phase names alone could pass without exercising the assigned cleanup stage.

All executable expected values originate in the fixed registry/PowerShell
specification, never the implementation's result. The new C binary executes
the actual runtime array/RC operations; old RMQ replay is not its oracle.
There are no production/public theorem mutations or new public propositions,
so the inherited exact-type public consumer clause has no applicable target.
The committed operational mutation branches, registry and runner replay every
claimed native negative and repair omitted cleanup before exiting. No tracked
source is patched during replay; all checked source/tool/artifact hashes match
before and after.

## Source grounding and consuming recommendation

[RUNTIME_SOURCE.json](RUNTIME_SOURCE.json) records the exact runtime C++ source at
installed compiler commit `ba2cbbf09d4978f416e0ebd1fceeebc2c4138c05`.
The installed header defines size/capacity/requested bytes, reference-acquiring
array reads, shared-array copying and pop. Installed `Array.Basic.shrink` is
repeated pop. Runtime `lean_copy_expand_array(false)` preserves capacity and
acquires references when shared; destruction traverses initialized logical
entries then dispatches capacity-based deallocation. Source review and measured
release paths are distinct from a proof of allocator correctness.

[BOUNDARY.md](BOUNDARY.md) gives the source-line mapping and exact relevant
existing propositions. In particular:

- `Construction.ExecState` owns numeric registers, numeric memory, separate
  optional Int keys and Int key registers, plus PC/status. `ArrayRun` also
  retains ordinary categories/writes/reserves/result observations.
- `BuilderRunFacts.outputCells`, under final status `halted outBase`, gives
  `s0.extent <= outBase`, final extent `outBase + (buildMemory xs).length`,
  and exact output values for every in-range i. `inputRetained` explicitly
  preserves original numeric cells and all keys. `arrayReflects` equates
  executable projections and final abstraction under the stated initial-state
  and 400-register-bank premises. None supplies native capacity or uniqueness.
- `Native.StorageImage` stores width/input length/register count, code and
  memory. Its memory/code contain nested `Array UInt8` words. The loaded native
  refinement requires canonical memory/state, exact encoded code, fitting
  instructions, bounded register writes and safe reference execution on the same
  decoded memory.
- Existing Rust `NativeImage` owns a `LoadOwner`; C exposes a borrowed image
  and increments it for queries while retaining the load owner. This is immutable
  reuse. Existing `canonicalImage` uses the original query program; the probe
  does not imply an already implemented compact lifecycle adapter.

Recommend an explicit consuming success/controlled-failure boundary, with all
construction array and observation roots inventoried. Acquire output references
before source release; publish only the reviewed output on success; release
initialized output/source on controlled failure. State whether array and element
aliases are prohibited or separately accounted. Account for transient old-plus-new
storage separately and prove/measure nested production capacities. The output
must be the exact image consumed by the reviewed formal query refinement.
Do not freeze a production BuilderOwner-to-QueryOwner ABI before LIFE-1's formal
interface review. The generic C buffer is evidence for ownership mechanics, not
a replacement for that formal or production adapter work.

## Verification, provenance and limits

Final-required evidence is indexed by [CERTIFICATION.json](CERTIFICATION.json).
The command ledger distinguishes the following checks:

| Role | Command or executable surface | Result / scope |
| --- | --- | --- |
| Development | Bounded compiler startup, exact `pop-unique`, then focused `-SelfTest` | Passed after diagnosed header/runner repairs; full failed attempts retained. |
| Final native | `packed_native_lifecycle_storage_replay.ps1 -SelfTest` with Cases omitted | 23 cases, 58 stages, 65 checks; 161.682 s; exits 0; final frozen C/script/registry. |
| Native stage limits | Compiler 120 s; probes and shape/selector stages 30 s; descendant sleeper 8 s | Exact per-stage limits/exits/durations are in RESULTS. Overall owned deadline 1200 s. |
| Baseline regression | Direct pinned `lake.exe build`, source-verified independent copied cache, required mutex | Exit 0; native child 1.071 s, owned wrapper 2.931 s, 7200 s deadline. 1,125 matching source/config files, 4,208 copied artifacts; 188 complete warning blocks match prior baseline, empty stderr. |
| Frozen contract | `VERIFY_CONTRACT.ps1` | 12 exact ordered IDs, eight columns, full prompt cells and frozen strict UTF-8 row bytes. |
| Source-commit policy | Strict design with exact base and `-Head bea5ce75...`; committed-base whitespace | Exit 0, clean source commit, all 15 source-freeze paths classified. |
| Whole-repository claims | `scripts/claim_drift_scan.ps1 -Strict`, default roots, after draft report creation | Exit 0; 3,479 hits, zero strict failures; 2,211.841 s with a 3,600 s owned deadline; complete stdout/stderr retained. |
| Final package | Whole-base and per-commit strict design; strict claim scan after report creation; working/committed whitespace; raw Git/source bytes; final scope and clean status | Recorded in CERTIFICATION and final packaging receipt. |
| Trust hygiene | Required forbidden-token/Mathlib and native-decision scans over RMQ/lakefile | Both exit 1 meaning no matches; stderr empty. No Lean/lakefile changes or new axiom-bearing surfaces. |
| Conditional campaign | Aggregate gate, full existing native replay, independent fresh-blind final audit | Aggregate and audit are later coordinator campaign gates. Existing native replay is conditional on modifying predecessor native code, which did not occur. |

The compiler remains installed Lean leanc/Clang 19.1.2 targeting
`x86_64-w64-windows-gnu`. The bundled distribution lacks general C standard
headers; the successful command uses the existing matching Strawberry x64
MinGW standard headers plus an exact copied `mm_malloc.h`, leaving Clang's
own atomic definitions intact. It records 39 included headers, the actual link
map, 42 conservative archive/object link inputs, relevant binaries and source
headers; all are rehashed after replay. No installation was needed.

Earlier attempts are retained below the same `.lake/lifecycle-native-p0/runs`
root: `785d1a1760fd4f7d8577046bf0b8aab0` (launcher emitted a task-return
object), `44feaf2019f0445f9830f2d6976a96bc` (missing stdio),
`37d35eb5db5f4f46a5af7c90d13f925b` (missing mm_malloc), and
`3744e3da42f24a21b9d66c3b91a713c1` (whole GCC builtin include caused atomic
header conflict). Each was rejected; each retry made the stated material
environment/runner correction. Development selector newline expectations were
corrected to actual C stream bytes. No failed attempt counts as native evidence.

Raw stdout/stderr are copied as byte streams before a summary. Native and
launcher exits are separately checked. Mixed stderr, extra stdout, false verdict
labels/summaries and selector/registry anomalies reject. The output-limit control
retains oversized bytes and rejects; the final post-drain size check is also
source-reviewed. Do not infer that every overflow run traversed that final branch:
polling may catch overflow earlier. The sleeper proves root and descendant
absence after owned termination; a forcibly killed native child may have no
ordinary-exit receipt, which is explicitly distinguished from a successful
semantic run. The fatal-handler process is likewise separate.

The executed host is PowerShell 7.6.5 on Windows 10.0.26200. Only this Windows
environment is certified here. The runner fails explicitly as
UNCOVERED on unsupported operating systems; it claims no POSIX test result.
C/runtime/compiler correctness, allocation availability for successful fixtures,
single-thread ownership and the declared registered-root model remain live
assumptions. Payload bits, proof fields, model ticks, runtime state, requested
allocation bytes and wall-clock duration remain distinct. C copying and release
loops are not single charged word-RAM instructions. Arbitrary Lean Int storage
is not silently treated as finite machine words.

Full baseline outputs/provenance remain under
`C:/Users/poin/.codex/worktrees/af4b/RMQ/.lake/lifecycle-native-baseline/`;
[BASELINE.json](BASELINE.json) pins them. Baseline source was verified against
the clean exact-governance warm tree at
`C:/Users/poin/Documents/RMQ/.claude/worktrees/wf1-whole-project-audit/.lake/cold`.
Caches were copied and individually hashed, never shared. Subsequent C/docs
edits do not invalidate unchanged Lean-source regression evidence; no duplicate
build or aggregate was run.

The default-root claim scan used source commit `bea5ce75...` and draft report
SHA-256 `43F14694FC97D7B1105170E3ED36A1F38F554749E04058D60B69F00E591E620C`.
The first invocation was interrupted because `Write-Host` bypassed its draft
redirection; it has no successful-exit claim. The corrected owned invocation
retained all 4,118,433 stdout bytes and empty stderr, and exited 0. Its long
runtime came from the unchanged paragraph regex over inherited records. A prior
same-policy, same-large-file run at `d0b4cef57e87540f4e333d15a5564bda8834227d`
took 1,265.16 s; that was a reference measurement, not a deadline guarantee.

Final claim coverage composes that completed default-root PASS with a subsequent
unchanged-policy scan of the entire owned evidence directory and both decision
ledgers. The scanner evaluates each term and required attribution within one
file (`claim_drift_scan.ps1:338-456`); its final verdict only aggregates failures.
All 2,910 files outside that final rescan retain identical paths and bytes, and
the scanner, policy, ripgrep identity/configuration, repository working directory
and exclusion mode remain unchanged. This is completed full-scan plus final
changed-file coverage, not a second default-root execution or an added hit count.
Exact final package checks and content hashes are retained at
`C:/Users/poin/.codex/worktrees/af4b/RMQ/.lake/lifecycle-native-p0/checks/package-postcommit/receipt.json`.
The 230 recorded native/baseline evidence files were also rehashed successfully.

## Frozen-row dispositions and proof/ownership digestion

[ACCEPTANCE_MATRIX.md](ACCEPTANCE_MATRIX.md) preserves all frozen rows exactly
and appends evidence; `ACCEPTANCE_ROWS.txt` SHA-256 is
`F45113AE6BF3F769105A748B3D0A61EA99532A05A715410F11EF29E7E518EC29`.
`REQUIREMENTS.json` SHA-256 is
`0983881A85F9A3B42ECD54C0BFB18170C3BE3E5A65602CDE66547042CA5421C9`.
The local LF attribute fixes row transport; exact Git bytes and actual working
bytes are checked separately, not conflated with normalized historical logs.

| Frozen ID | Disposition and evidence |
| --- | --- |
| LN0-01 | Closed: actual pinned runtime operations, distinct size/capacity/requested bytes/reference observations, source and compiler identities. |
| LN0-02 | Closed: unique/shared pop/shrink, surviving values, tail references, backing capacity, explicit owner/alias release and restoration. |
| LN0-03 | Closed: bounded replacement including empty/overlap/tail/aliases, all five measured failure pre-states, cleanup and separate fatal-handler result. |
| LN0-04 | Closed: exact registry; operational capacity/alias/cleanup/value negatives and matching positive predicates; independent measured verdict. |
| LN0-05 | Closed: owned bounded processes, raw streams and exits, mixed diagnostics, selectors, output bound and descendant cleanup; explicit Windows scope. |
| LN0-06 | Closed: source-grounded resource-to-owner recommendation in BOUNDARY; formal review precedes production ABI. |
| INV-SEMANTIC-NONVACUITY | Closed: predicates reconstruct operational projections, intermediate states and actual reference/destructor effects; no label-only liveness. |
| INV-ORACLE-INDEPENDENCE | Closed: frozen independent input/interval/source-ID specification, including wrong-copy negative. |
| INV-CATEGORY-SEPARATION | Closed: native measured scope and remaining formal/allocator/Int distinctions are explicit. |
| INV-MUTATION-REPRODUCIBILITY | Closed: committed runner/registry/operational mutation cases, exact surfaces, positive controls, post-observation cleanup and source restoration. |
| CHK-FINAL | Closed in local review: complete native replay and baseline, completed default-root scan plus final changed-file scan, frozen contract, strict design, hygiene, whitespace, exact source/evidence/report identities; CERTIFICATION and the exact packaging receipt retain outcomes. |
| CHK-SCOPE | Closed in local review: exact-base private branch, 17 assigned paths, append-only ledgers, all frozen row bytes preserved, clean committed packaging verified at handoff; no publication or coordinator acceptance. |

Conceptually, the work separates losing a reference, shortening a logical array,
and reducing retained allocation capacity. In plain English, deleting four list
positions can destroy four values while leaving the entire old backing buffer.
Copying the required values to an exactly sized buffer and releasing the old
owner reduces the retained container, but an old alias prevents that reduction.

For a worked case, copying positions [1,5) gives `[-7,303,303,505]`.
Before old-owner release, selected objects have two references. Afterwards, IDs
0 and 5 are destroyed, four output objects remain with one reference each, and
only the 56-byte output container is reachable through the probe's roots. Retain
an old array alias and the same values instead coexist with 336 array bytes and
ten element references. This difference is observed, not inferred from a label.

A skeptical reviewer should next inspect whether the eventual compiled adapter
retires every construction root and transfers the exact reviewed image; whether
nested production headers/limbs and alias enforcement meet the retained succinct
target; and whether the formal lifecycle's charged transitions compose with that
native boundary. Those are the explicitly downstream adapter/campaign phases,
not unmet local probe requirements. No local candidate status closes LIFE-1,
the lifecycle roadmap node, native heap verification or publication.

DD-20260920-LIFE-NATIVE-P0-001 records representation/ownership choices;
WDD-20260920-LIFE-NATIVE-P0-001 records frozen rows, measured verdict reach,
header/dependency provenance, failure feedback and process discipline. A bounded
independent source reviewer checked the C lifetimes and matching predicates,
found the three runner issues described above, and confirmed their repairs on
the final hashes. That review is not a fresh-blind final campaign audit.
WDD-20260920-LIFE-NATIVE-P0-002 records the source/report packaging boundary and
the full-scan plus final changed-file certification method. No representation
decision changes in the documentation-only packaging commit.

## Source and artifact hashes

| Artifact | SHA-256 |
| --- | --- |
| Final C probe | `5F32F4A91B21697F86B4F2FEA855CD050E59E330CE6C6FFDA28898353B66D7B1` |
| Final replay script | `077BF8D478141F8891AB6F9C2E332CBF8C8F75ACA32C722B29BD307924957B8E` |
| Final registry | `6CD97F40E7C39D2212A8C8705D264D4832DCF2542815B72CD927906A01DC8B20` |
| Compiled probe, 7,091,712 bytes | `67E6A077C19D0D5DE89F55E28097339EA7162FDA3664F99230C179443DCE2C7C` |
| Compact RESULTS.json | `6440A963BE7A0E65222F86AFE3CFB89E4BEE1B6BDCD0226DC0D5CDA88D296FDD` |
| Reviewed exact-commit runtime object.cpp | `44C1430D9C6DA2FE9FDE073D407F9FD58860D869D09B8C7EA0BC0E27D85916FB` |

All remaining runtime/header/compiler/raw-output hashes are carried by RESULTS,
its pinned full summary and BASELINE. The final report hash and byte length are
issued after writing this entire report, in the final certification/handoff;
they are not recursively embedded into the report's own bytes.
