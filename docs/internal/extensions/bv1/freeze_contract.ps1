param()
$ErrorActionPreference = 'Stop'
$repo = (Resolve-Path (Join-Path $PSScriptRoot '../../../..')).Path
$target = Join-Path $PSScriptRoot 'ACCEPTANCE_MATRIX.md'
if (Test-Path -LiteralPath $target) { throw 'Acceptance matrix already frozen; refusing overwrite.' }
$requirements = [ordered]@{
'REQ-BV-ALLOC' = 'For every List Bool of length n, construct one numerical allocation with complete retained data/code/scratch accounting at n+rho(n), with checked LittleOLinear rho and one O(log n) word width. Count both Boolean select directories, metadata, exceptional tables, padding and input-dependent program data.'
'REQ-BV-OPS' = 'Define access, rank and select for both Boolean values with explicit index/prefix/occurrence conventions and valid/invalid guards. Prove exact all-size answers from the actual run on that allocation. Separate unbounded-Nat API guards from charged representable machine inputs.'
'REQ-BV-RUN' = 'Supply fixed uniform primitive programs with explicit constant instruction bounds, all-prefix safety, word/address/sentinel/operand bounds, successful completion and attempted aligned reads into the same counted memory. Decode/routing must consume charged replies. Derive category costs and observations from the execution.'
'REQ-BV-REUSE' = 'Reuse the actual Packed primitive ISA, physical span/decoder blocks and Structured compiler definitions. Add generic reader/frame/metadata bridges to the existing arbitrary-bitvector directory semantics. A copy of PQ1 under new names or a shape-specialized assumption on arbitrary input does not establish generic reuse. Avoid modifying shared Packed modules in this first lane; use additive generic adapters and report a precise necessary shared change if encountered.'
'REQ-BV-JOIN' = 'One inhabited capstone must quantify the same bitvector, allocation, programs and executions and connect all three operations and both bits to the n+o(n) complete capacity theorem. Required fields get exact-type consumers and anti-bypass tests.'
'CHK-BV-CONTROLS' = 'Persist all-zero/all-one/alternating/mixed vectors, empty/singleton/size-two, threshold-minus-one/threshold, invalid ranks/select occurrences, crossing-cell reads and both select values. Exercise long-superblock and sparse-local exceptional routes with valid parameterized components when canonical small fixtures cannot reach them; identify which global cases are covered only by universal proof. Validate actual new programs, not the old abstract read-count API.'
}
$evidence = @{
'REQ-BV-ALLOC' = 'For every bits, ((memory bits).length + encoded code words + scratch words) * W bits.length <= bits.length + rho bits.length; LittleOLinear rho; two select-directory component capacity inequalities, padding and metadata sum; log width lower/upper bounds.'
'REQ-BV-OPS' = 'For every bits, bit and Nat argument, guarded API equals independent List specification; for every representable argument, actual run result encodes that same specification, including invalid cases.'
'REQ-BV-RUN' = 'Literal fixed programs and constants; actual run halts, steps <= constant, every indexed transition is safe, every fuel prefix fits, every emitted receipt is the addressed cell of memory bits; six category counts partition steps.'
'REQ-BV-REUSE' = 'Actual source contains Packed spanBlock/decoder blocks and calls Structured.Block.compile; generalized reader theorem has arbitrary List Bool store plus charged metadata, packet/length/ordered receipt/frame conclusions; no shape witness premise.'
'REQ-BV-JOIN' = 'RMQ.PackedBitvector.fullyChargedBitvectorCapstone_holds : FullyChargedBitvectorCapstone with no correctness/readiness premises; independent exact-type consumers project every required field at the same builder/program/run arguments.'
'CHK-BV-CONTROLS' = 'Committed nonempty exact registry executes new programs against independent List specifications, asserts routes and receipt crossings, covers both bit values and guarded invalid inputs; parameterized exception fixtures identify canonical-global coverage limits.'
}
$attacks = @{
'REQ-BV-ALLOC' = 'Remove false-select directory, exceptional component, padding, code or scratch charge; require complete-capacity consumer failure.'
'REQ-BV-OPS' = 'Empty input; length and length+1 prefixes; zero and count-th select; invert desired bit; corrupt a decisive reply; compare returned projection.'
'REQ-BV-RUN' = 'Missing memory, crossing span, oversized dormant operand, failed load, omitted transition, unrepresentable input guard; match universal positive predicate.'
'REQ-BV-REUSE' = 'Replace primitive span/compiler dependency by sibling facade or semantic callback; exact reader/program consumers must fail.'
'REQ-BV-JOIN' = 'Field deletion, proposition weakening, sibling substitution and public proposition mutation; independently pinned consumers must reject.'
'CHK-BV-CONTROLS' = 'Wrong expected result, missing registry case, unknown/empty selector and wrong route expectation must fail production verdict; restoration control must pass.'
}
$gate = [IO.File]::ReadAllText((Join-Path $repo '.agents/skills/rmq-proof-sprint/references/COMPLETION_GATE.md'))
$section = ($gate -split '## 2\. Inherited RMQ Invariants',2)[1] -split 'If a local component cannot yet satisfy',2 | Select-Object -First 1
$matches = [regex]::Matches($section, '(?ms)^- `(INV-[A-Z-]+)`: (.*?)(?=\r?\n- `INV-|\r?\n\r?\n|\z)')
if ($matches.Count -ne 21) { throw "Expected 21 inherited invariants, found $($matches.Count)" }
foreach ($match in $matches) {
  $id = $match.Groups[1].Value
  $requirements[$id] = ([regex]::Replace($match.Groups[2].Value, '\s+', ' ')).Trim()
}
$requirements['REPLAY-EXACT-REGISTRY'] = 'any new replay must have a nonempty exact versioned case registry and report executed/expected cases; silently losing a case is failure.'
$requirements['REPLAY-SELECTOR-NONVACUITY'] = 'omitted, valid, empty, whitespace, malformed and unknown selectors have pinned behavior; focused runs cannot succeed by selecting nothing.'
$requirements['REPLAY-SUBPROCESS-DEADLINE'] = 'run subprocesses with bounded ownership/timeout, preserve exits and stderr, restore mutated bytes in finally, and verify exact clean restoration. Use existing process ownership tooling. A condition the host cannot create is uncovered/inconclusive, not passed.'
$header = @'
# BV-1 frozen acceptance matrix

Status: OPEN. Frozen before proof or construction edits.

Handle: BV-1. Title: `(BV-1) Prove fully charged generic rank select`.
Base and governance: `0e6a00f654abc64f8b68988fa9675b9a839dca2f`.
Branch: `codex/bv-1-fully-charged-rank-select`.
Worktree: `C:\Users\poin\.codex\worktrees\c974\RMQ`.
Target: `RMQ.PackedBitvector.fullyChargedBitvectorCapstone_holds` in
`RMQ/Core/WordRAM/Bitvector/Capstone.lean`.
Downstream join: reusable generic physical access/rank/select client, followed
by independent exact-commit audit and coordinator acceptance/integration.

The requirement column is frozen. No row is inapplicable to the composed
machine. Evidence and status may be appended using these stable IDs. Source
types below are planned propositions until an explicit elaboration result is
recorded; names and source readings are not closure evidence. No claim of
mathematical impossibility follows from an implementation gap.

| ID | Exact frozen requirement | Scope | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge attempted and outcome | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- | --- |
'@
$lines = [Collections.Generic.List[string]]::new()
$lines.Add($header.TrimEnd())
foreach ($item in $requirements.GetEnumerator()) {
  $id = $item.Key
  $needed = if ($evidence.ContainsKey($id)) { $evidence[$id] } else { 'Exact proposition required by this row, expanded at the same bitvector, memory, query, width and actual primitive run; see CONTRACT.md for planned quantified interfaces.' }
  $attack = if ($attacks.ContainsKey($id)) { $attacks[$id] } else { 'Not yet attempted. Attack this precise predicate with identical quantifiers/guards; require projection-specific evidence and committed replay before closure.' }
  $scope = if ($id.StartsWith('INV-')) { 'Inherited, applicable' } else { 'Assigned' }
  $lines.Add('| `' + $id + '` | ' + $item.Value + ' | ' + $scope + ' | ' + $needed + ' | bits -> counted logical payload -> numeric allocation -> charged metadata and span decoder -> compiled operation -> run -> capstone -> exact-type consumer | ' + $attack + ' | No new theorem checked at freeze. | OPEN |')
}
$lines.Add(@'

## Execution and verification contract

- Build only owned modules and exact-type consumers with one Lean/Lake job and
  task-local output; never use a mutable shared cache link.
- Development: static diff/trust checks, narrow import/type checks, then
  bounded executable startup, one exact selector, and operation-specific cases.
- Final-required: `lake build`; explicit build/import of every new capstone
  and typed consumer; full new validation registry; relevant axiom inventory;
  both trust scans; working-tree and exact-base committed-range diff checks;
  `scripts/design_decision_check.ps1 -Strict -Base
  0e6a00f654abc64f8b68988fa9675b9a839dca2f`.
- Conditional: `scripts/claim_drift_scan.ps1 -Strict` for family/digestion or
  other public prose; existing compatibility checks if executable behavior
  changes. Exact new declarations require `#print axioms`.
- Full aggregate certification is pending a coordinator-scheduled host-wide
  gate slot on frozen content. Do not run it before that slot is assigned.
- A command ledger records command, role, platform, tree/diff identity, rows,
  unique coverage, runtime basis, deadline, duration, exit, output artifact,
  skipped host branches and any material rerun reason.
- Replay registry/selectors/deadlines are mandatory production-boundary
  checks; unsupported host controls are inconclusive, never passed.

## Authorization, scope and stop conditions

The user explicitly authorizes the post-PQ1 generic client despite the old
roadmap's historical broad-expansion deferral. Preserve frozen history and
record this task-specific authorization in appended design entries.
Local commits are authorized. Push, main integration, deletion and cleanup are
outside this task. Shared Packed modules, canonical skills, gate.ps1 and public
root aliases are outside the write scope. Shared ledgers/family/digestion are
append-only task-specific entries. No peer's uncommitted files are dependencies.

Required lifecycle: baseline/freeze; contract and feasibility evidence;
evidence-dependent route review; implementation and verification; independent
exact-commit audit; repair/re-audit; coordinator acceptance. PRE builder work
belongs to its peer lane; its mandatory contract audit is not permission to
silently narrow BV-1. Any BV-1 prerequisite review checkpoint remains
INCOMPLETE with all unmet rows explicit.

No helper, fixture, passing build or honest caveat substitutes for the named
target. Continue until closure, a matching formal obstruction requiring a
coordinator decision, genuine unavailable external state, or an authorized
phase stop/redirect. No unproved field is a construction hypothesis of the
final capstone.

Explicit non-goals: compressed RRR/FID space, full BP navigation and new RMQ
query/compiler implementations. Final paper rewrite, publication strategy,
combined integration and exhaustive public-surface synchronization belong to
the coordinator. Nothing needed to make BV-1 true is deferred by those labels.

## Evidence ledger

See COMMANDS.md and phase artifacts in this folder. All 30 assigned/frozen
requirement and inherited-invariant rows remain OPEN at the initial freeze.
'@)
[IO.File]::WriteAllText($target, (($lines -join "`n") + "`n"), [Text.UTF8Encoding]::new($false))
Write-Output "BV1-FREEZE: $($requirements.Count) exact requirement rows; inherited=$($matches.Count); $target"
