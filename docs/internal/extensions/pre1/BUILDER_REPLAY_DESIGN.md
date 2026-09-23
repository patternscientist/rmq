# PRE-1 builder replay design

This is the builder-closure replay, layered over the frozen contract lane. It
does not modify `contract_cases.json` (registry version 1), its runner
`scripts/preprocessing_contract_replay.ps1`, its guard
`scripts/preprocessing_contract_firewall.ps1` or `primitive_manifest.json`; it
checks at startup that none of them changed. The production surfaces are the
builder closure modules under `RMQ/Core/WordRAM/Construction/`, the layered
guard `scripts/preprocessing_builder_firewall.ps1`, and the typed consumer
`scripts/preprocessing_builder_check.lean`. The runner contains no copied Lean,
alternate interpreter, or source-text semantic validator.

The registry is `builder_cases.json`, **version 2** (repair PRE-1-R2, 55 cases;
version 1 held B01-B52). Appending a case requires three edits in one change:
the case itself, `$script:ExpectedIds` in
`scripts/preprocessing_builder_replay.ps1` (registry order), and
`$script:ExpectedRegistrySha256` (recomputed with the one-liner below). A change
of the verdict rules also increments the registry `version` and
`$script:ExpectedRegistryVersion`; version 2 appended B53-B55 and made every
consumer-stage rejection require the absence of the profile's verdict marker.
Content pins (CRLF-to-LF normalized SHA-256): version 1
`0bc1fba4b974e05cd94830ff0d6038d6927d33b5928bb65587fc9a2dc166ffe7`, version 2
`3e27e7626f4af805820071777246d3a5c2ac101e7adbb3db028219b2f46ae495`.

## Layered firewall

`scripts/preprocessing_builder_firewall.ps1` runs these checks in order and
stops at the first failure, printing only the failing diagnostic:

1. **Contract guard first.** The frozen contract guard runs as a child process
   under the current shell. Exit 0 and an output line exactly equal to
   `PRE1-FIREWALL PASS: exact Std-only primitive closure and frozen evaluator bytes`
   are both required; otherwise
   `PRE1-BUILDER-FIREWALL contract guard failed: <child output>` where the
   child's own diagnostic is embedded verbatim.
2. **Exact allowed-imports table.** Repository-relative path to exact direct
   import list (same count, same names, no duplicates, comments and strings
   stripped by the same `Remove-LeanComments` code as the contract guard):

   | Module | Allowed direct imports |
   | --- | --- |
   | `Program.lean` | `RMQ.Core.WordRAM.Construction.Model` |
   | `Calculus.lean` | `RMQ.Core.WordRAM.Construction.Program` |
   | `Safety.lean` | `RMQ.Core.WordRAM.Construction.Program` |
   | `Structured.lean` | `...Calculus`, `...Safety` |
   | `Compiler.lean` | `RMQ.Core.WordRAM.Construction.Structured` |
   | `Loop.lean` | `RMQ.Core.WordRAM.Construction.Compiler` |
   | `ArrayRun.lean` | `RMQ.Core.WordRAM.Construction.Program` |

   A missing file is `closure module missing: <path>`; a mismatch is
   `imports rejected: <path> actual=[a,b]`; residual `import`/`prelude`
   tokens are `unrecognized import/header syntax: <path>`. Registering a
   `Builder/*.lean` module is one appended table entry plus one appended
   manifest entry.
3. **Unregistered closure files.** Every `*.lean` under
   `RMQ/Core/WordRAM/Construction/Builder/` (recursive) must be a table key:
   `unregistered closure module: <path>`.
4. **Transitive closure.** From every table key, imports of the form
   `RMQ.Core.WordRAM.Construction.<Dotted.Name>` are followed. Every import met
   must be `Std`, a table key, or one of the contract roots `Primitive`,
   `Input`, `Model` (whose own imports the contract guard owns). Anything else
   (for example `RMQ.Core.Shape`, `...Construction.Controls`,
   `RMQ.Core.WordRAM.Packed.*`) is
   `transitive closure escapes: <module> via <path>`.
5. **Manifest.** `builder_manifest.json` must have `version` 1 and exactly one
   `{path, sha256}` per table key, no duplicates, `sha256` the UPPERCASE hex
   SHA-256 of the strict-UTF-8 text with CRLF normalized to LF (identical to
   the contract guard). Mismatch: `frozen closure bytes changed: <path>`.
   Wrong version/count: `exact builder registry version/count`. The literal
   `PENDING` never matches, so an unfilled entry fails closed.

Success prints exactly
`PRE1-BUILDER-FIREWALL PASS: layered closure over the contract guard, <n> modules`.

## Stage order and producer targets

Each compile runs `firewall` (the layered guard above, administrative
deadline), then `producer`, then `consumer`, each with `LEAN_NUM_THREADS=1`. For
the default `builder` profile the producer is
`lake build RMQ.Core.WordRAM.Construction.Loop RMQ.Core.WordRAM.Construction.ArrayRun RMQ.Core.WordRAM.Construction.HeaderUse RMQ.Core.WordRAM.Construction.Proof.Constants`
(the four `$script:ProducerTargets`) and the consumer is
`lake env lean scripts/preprocessing_builder_check.lean`; the `capstone` and
`stackpass` profiles are described under "Replay extension" below. A failing
stage stops the sequence. Restoration reruns all three stages of the case's
profile and requires all three to pass. `HeaderUse` is a consumer outside the
closure and is built so a closure mutation that breaks its user is observed at
the producer stage; `Proof.Constants` builds `Builder.Program` and the literal
pins of the program constants that the consumer's V3-1..V3-6 section imports,
without the stage proof tower.

## Verdict matcher (auditor recommendation R2)

A consumer rejection registers `expectedSurface` as one or more
space-separated items each matching `^<consumer file>:[1-9][0-9]*:$`, where the
consumer file is the case profile's `SurfaceFile`
(`preprocessing_builder_check.lean`, or `PreprocessingContract.lean` for the
`capstone` profile; the registry self-test enforces this shape and rejects a
column suffix, a `scripts/` prefix, an empty item, or a surface file that does
not match the profile). The matcher first requires that the consumer stage's
output does **not** contain the profile's verdict marker
(`PRE1-BUILDER-TYPED-CONSUMERS PASS`, or `PRE1-CAPSTONE-TYPED-CONSUMERS PASS`
for `capstone`; registry version 2, repair PRE-1-R2 of audit PRE-1-A2 P2-1,
where B16-B18 exited 1 with their registered line and printed the marker). It
then extracts every match of `<consumer file>:(\d+):\d+: error` from that
output, forms the set of line numbers, and passes only if that set is nonempty
and **equals** the expected set (order-insensitive, duplicates collapsed).
`Contains` remains for firewall-stage rejections (one diagnostic line),
producer-stage rejections (a Lean location such as
`RMQ/Core/WordRAM/Construction/HeaderUse.lean:NN:` or a fixed phrase, exit
nonzero at the producer), and the accept control marker.

Matcher fixtures run by the registry self-test and in full mode:

| Fixture | Verdict |
| --- | --- |
| rejection with the registered line and without the marker (`rejection-without-marker`) | pass |
| rejection with the registered line and the builder marker (`rejection-with-marker`) | fail |
| capstone-profile rejection with the exact line set and without the capstone marker | pass |
| capstone-profile rejection with the exact line set and the capstone marker | fail |
| exact single line `{42}` | pass |
| exact set `{42,57}` reported in either order | pass |
| expected `{42,57}`, output `{42}` (missing line) | fail |
| expected `{42}`, output `{42,43}` (extra line, superset) | fail |
| line 42 reported twice (two columns) | pass |
| consumer surface at producer stage | fail |
| line 43 for expected 42 | fail |
| bare `preprocessing_builder_check.lean:42:` without `:col: error` | fail |
| unrelated error plus generic substring | fail |
| `42:7: warning` instead of error | fail |
| timed-out consumer | fail (inconclusive) |
| consumer exit 0 with error-shaped text | fail |
| accept marker at consumer, all stages 0 | pass |
| accept marker at firewall stage | fail |
| firewall rejection with registered diagnostic | pass |
| firewall rejection with a different diagnostic | fail |
| firewall surface appearing at producer | fail |
| producer rejection with registered location | pass |
| producer surface appearing at consumer | fail |

## Frozen contract-surface regression

In every Lean mode (startup, focused, full) the runner recomputes the
CRLF-to-LF-normalized lowercase SHA-256 of these files before resolving Lake
and throws `PRE-BUILDER-FROZEN: contract surface changed: <path>` on mismatch.
Values were computed 2026-09-12 at `c1c970b`:

| Path | SHA-256 |
| --- | --- |
| `docs/internal/extensions/pre1/contract_cases.json` | `aaec37a62bc74b483d09362a5d16f62afc2ae3a7be007577bc13e4c87c98574e` |
| `scripts/preprocessing_contract_firewall.ps1` | `1f6903d5ae753fb49ac0d21611ba82aeb61fe9c8aced63e2c6469473b5f28786` |
| `scripts/preprocessing_contract_replay.ps1` | `b85ff767098d3a3249a86b78d2e9e96e63d7822dd82a3752fac933479cf5424c` |
| `docs/internal/extensions/pre1/primitive_manifest.json` | `a1d31f0bc4b1d732a331d4bac3b1b2103e3be9812fd0b1eb2e9769c45931fcfa` |

A deliberate change to the contract lane must update
`$script:FrozenContractSurfaces` in the same change.

## Deadlines

| Parameter | Default | Evidence |
| --- | --- | --- |
| `-DeadlineSeconds` | 600 | Contract-lane per-stage maxima were under 25 s; a cold contract build took 77.2 s. The builder closure is larger; 600 s is more than 2x any observed stage. |
| `-AdministrativeDeadlineSeconds` | 120 | Selector-boundary child stage max 16.9 s; 2x plus shell startup. |
| `-SleeperDeadlineSeconds` | 45, `ValidateRange(1, 120)` | The contract default 12 s FAILED on this host (shell startup measured 8.997 s); 30 s passed; the PRE-1-A1 audit used 45 s. |
| `-OutputLimitBytes` | 16777216 | Unchanged from the contract runner. |
| `-ValidatorDeadlineSeconds` | 1800 | Full run of `rmq_preprocessing_validate` measured at 267.5 s (6.7x); the same deadline bounds the executable build and each negative control. |

`-LakePath` resolution is identical to the contract runner: an explicit path,
else the toolchain named by `lean-toolchain` under `ELAN_HOME` (or the user
`.elan`), never the elan proxy. Every subprocess, including Git inspection and
child script-boundary tests, uses `Invoke-RMQOwnedBoundedProcess`.

## Run modes

| Mode | Purpose | Semantic execution |
| --- | --- | --- |
| `-StartupOnly` | Frozen-surface check, bounded baseline firewall/producer/consumer | One baseline; zero mutation cases |
| `-OnlyCase B01_FIREWALL_IMPORT` | Known exact focused case before a full run | Baseline plus one case and restoration |
| No mode/selector | Full frozen registry | Registry/matcher/selector/process self-tests, baseline, all registered cases and restoration |
| `-RegistrySelfTestOnly` | Registry corruption rejection, surface-shape rules, matcher fixtures | None |
| `-SelectorBoundarySelfTestOnly` | Real script-boundary binding (`B01_FIREWALL_IMPORT` valid, `B99_UNKNOWN` unknown) | None |
| `-DeadlineSelfTestOnly` | Exit/stderr and real descendant cleanup | None |
| `-SelectorProbeOnly` | Prints `PRE-BUILDER-SELECTOR-PROBE: selected=<n> ids=<ids>` | None |

Output markers are `PRE-BUILDER-REPLAY: PASS mode=<mode> executed=<n> registry=<n> evidence=<dir>`
and `PRE-BUILDER-REPLAY: FAIL <reason>`. Reports carry `phase = 'BUILDER'`.
Evidence defaults to a fresh directory under `.lake/preprocessing-builder-replay`;
an evidence directory inside the repository must be under `.lake`. Restoration,
Git-state comparison, and `Assert-SourceHashes` (every registry case path, all
Construction sources, the four scripts `preprocessing_builder_replay.ps1`,
`preprocessing_builder_firewall.ps1`, `preprocessing_contract_firewall.ps1`,
`preprocessing_builder_check.lean`, the capstone consumer
`RMQ/Validation/PreprocessingContract.lean`, the validator
`RMQ/Validation/Preprocessing.lean`, `lakefile.toml`, both manifests,
`lean-toolchain`) are as in the contract runner.

## Registry schema

The registry object has `version` (2) and `cases`. Each case has the string
fields `id`, `kind`, `path`, `before`, `after`, `expected`, `expectedStage`,
`expectedSurface`, and optionally `profile` (`capstone` or `stackpass`),
`manifest` (`rehash`) and one `companion` object (`path`, `before`, `after`).
IDs match `^B[0-9]{2}_[A-Z][A-Z0-9_]*$` and appear in `$script:ExpectedIds`
order. `kind` is `mutation` (must `reject`) or `control` (must `accept`);
`expectedStage` is `firewall`, `producer`, or `consumer`. `path` is drawn from
the closed set of 15 paths: `Program`, `Calculus`, `Safety`, `Structured`,
`Compiler`, `Loop`, `ArrayRun`, `Builder/Program`, `Builder/Cartesian`,
`Proof/RunFacts`, `Capstone`, `HeaderUse`, `Primitive` (all under
`RMQ/Core/WordRAM/Construction/`), `RMQ/Validation/PreprocessingContract.lean`
and `scripts/preprocessing_builder_check.lean`. `manifest: rehash` is admitted
only on the nine manifest-hashed modules `Program`, `Calculus`, `Safety`,
`Structured`, `Compiler`, `Loop`, `ArrayRun`, `Builder/Program`,
`Builder/Cartesian` and never at the firewall stage; a `companion` only on
`Proof/Constants.lean` and only for a mutation. `before` must occur exactly
once in the source; fragments adopt the source's uniform LF or CRLF spelling
and mixed endings fail before mutation.

## Hash recomputation

Run from the repository root in `pwsh` or Windows PowerShell.

Registry pin (`$script:ExpectedRegistrySha256`, lowercase):

```
$u=[Text.UTF8Encoding]::new($false,$true); $t=$u.GetString([IO.File]::ReadAllBytes('docs/internal/extensions/pre1/builder_cases.json')).Replace("`r`n","`n"); [BitConverter]::ToString([Security.Cryptography.SHA256]::Create().ComputeHash($u.GetBytes($t))).Replace('-','').ToLowerInvariant()
```

Manifest entry (`builder_manifest.json` `sha256`, UPPERCASE; substitute the module path):

```
$u=[Text.UTF8Encoding]::new($false,$true); $t=$u.GetString([IO.File]::ReadAllBytes('RMQ/Core/WordRAM/Construction/Calculus.lean')).Replace("`r`n","`n"); [BitConverter]::ToString([Security.Cryptography.SHA256]::Create().ComputeHash($u.GetBytes($t))).Replace('-','')
```

The same one-liner (lowercase form) recomputes a `$script:FrozenContractSurfaces`
entry if the contract lane is deliberately changed.

## Gate checkers

`scripts/preprocessing_contract_gate.ps1` (roster label `PRE1-CONTRACT-GATE`)
runs three owned bounded stages from the repository root: the contract firewall
under the current shell (120 s, exact PASS line required), `lake build
RMQ.Core.WordRAM.Construction.Contract` (900 s; cold audit build 77.207 s, 2x
cold margin plus contention), and `lake env lean
scripts/preprocessing_contract_check.lean` (300 s; measured 2.7-9.9 s), each
with `LEAN_NUM_THREADS=1` and a 16 MiB output limit. Timeout or output limit is
inconclusive and fails. It prints each stage's exit and duration, then
`PRE1-CONTRACT-GATE PASS` / `PRE1-CONTRACT-GATE FAIL: <reason>` with the child
output, and exits 0/1.

`scripts/preprocessing_builder_gate.ps1` (roster label `PRE1-BUILDER-REPLAY`)
runs the builder replay in full mode as one owned bounded child
(`-OuterDeadlineSeconds`, default 23400 s at the `MEASURED-DEADLINE` comment, which
records every revision against a measured full run and never shortens it: 1800 s
against the first 13-case run of 516.8 s, 3600 s against the 34-case run of
1535.87 s, 10800 s against the 52-case run of 4573.59 s, 23400 s against the
55-case run of 8674.82 s with the fail-closed markers, under coordinator ruling
R-R2-1 of repair PRE-1-R2: measured times 2.5, rounded up to a multiple of
1800 s). It requires exit
0 and exactly one line starting `PRE-BUILDER-REPLAY: PASS mode=full`, echoes
that line and `PRE1-BUILDER-REPLAY duration=<s>s`, then prints
`PRE1-BUILDER-REPLAY PASS` / `PRE1-BUILDER-REPLAY FAIL: <reason>` and exits
0/1. Both checkers take `-LakePath`; without it the contract gate uses `lake`
from PATH and the builder replay resolves the pinned toolchain itself.

## Author verification

Written 2026-09-12 at `c1c970b` without running Lean or Lake. All four new
scripts parse under PowerShell 7.6.6 and Windows PowerShell 5.1.26100.9444.
The builder firewall fails closed at `closure module missing:
RMQ/Core/WordRAM/Construction/Calculus.lean` after the layered contract guard
passes; a scratch copy with a missing, failing, or wrong-text sibling guard
fails at the layering step. `-RegistrySelfTestOnly`,
`-SelectorBoundarySelfTestOnly` (both hosts) and `-DeadlineSelfTestOnly
-SleeperDeadlineSeconds 45` (pwsh) passed. `-StartupOnly`, `-OnlyCase` and full
mode need the closure modules and the typed consumer and are the lead's to run.

Lead verification (Stage 0, runner SHA-256 `a5cf0b4a...`, registry
`fdfcbb18...`, all 21 source hashes of the runs equal to the committed Stage 0
bytes): `-StartupOnly` PASS (evidence `20260912-222542-...`), `-OnlyCase
B06_WORD_MISSING_WEAKEN` PASS with exact restoration (`20260912-222642-...`),
full mode PASS with executed = expected = 13, 145 stages and 44 self-tests
(`20260912-222805-...`, 516.8 s), and under Windows PowerShell 5.1.26100.9444
`-RegistrySelfTestOnly` PASS (32 self-tests) and `-SelectorBoundarySelfTestOnly`
PASS (9). Durations, the isolated gate-checker runs and the contract replay
regression are recorded in BUILDER_STAGE_LOG.md and REPORT.md. The POSIX branch
of the process tooling was not executed on this host.

## Frozen expected failure surfaces

These are expected verdicts; only the lead's production replay establishes that
the registered mutations actually reach and fail there. The lead appends rows
as cases are added.

| Case | Mutation | Exact surface retained by the layered guard |
| --- | --- | --- |
| B01_FIREWALL_IMPORT | Add `import RMQ.Core.Shape` to `Program.lean` | Firewall: `PRE1-BUILDER-FIREWALL imports rejected: RMQ/Core/WordRAM/Construction/Program.lean` before compilation. |
| B02_CLOSURE_BYTES | `Run.steps` returns `0` instead of `r.transitions.length` | Firewall: `PRE1-BUILDER-FIREWALL frozen closure bytes changed: RMQ/Core/WordRAM/Construction/Program.lean` (imports intact, manifest hash differs). |
| B03_LAYERED_CONTRACT_GUARD | Add `import RMQ.Core.Shape` to `Primitive.lean` | Firewall: `PRE1-BUILDER-FIREWALL contract guard failed: PRE1-FIREWALL imports rejected: RMQ/Core/WordRAM/Construction/Primitive.lean`; the contract guard's diagnostic surfaces through the layered guard. |
| B04_HEADERFIRST_WEAKEN | `HeaderUse.headerFirst : program[0]? = some headerInstruction` becomes `True` | Producer: `RMQ/Core/WordRAM/Construction/HeaderUse.lean:62:` (the derived `wordMissingHeaderFault` default proof needs the actual head fact; the certificate cannot be constructed without it, so no consumer runs). |
| B05_TAIL_WEAKEN | `HeaderUse.tailNeverWritesR1` becomes `True` | Consumer line 22: for every `program` with `HeaderUse program`, `∀ i ∈ program.tail, WritesOnly (fun r => r ≠ 1) i`. |
| B06_WORD_MISSING_WEAKEN | `HeaderUse.wordMissingHeaderFault` and its default become `True := True.intro` | Consumer line 36: for all `width xs fuel ≥ 1`, the header-removed word-model run has status `.fault`, `steps = 1`, `writes = []`, `reserves = []` and the initial extent. |
| B07_COMPARISON_MISSING_WEAKEN | `HeaderUse.comparisonMissingHeaderFault` becomes `True := True.intro` | Consumer line 54: the same five conjuncts on the header-removed comparison-model run. |
| B08_WORD_RECEIPT_WEAKEN | `HeaderUse.wordHeaderReceipt` becomes `True := True.intro` | Consumer line 59: the first transition of the intact word-model run is `headerInstruction`, register 1 goes from 0 to `xs.length`, status running. |
| B09_COMPARISON_RECEIPT_WEAKEN | `HeaderUse.comparisonHeaderReceipt` becomes `True := True.intro` | Consumer line 64: the same receipt on the intact comparison-model run. |
| B10_EXTENT_SIBLING | `oracleExtentOne` replaced by the sibling fact `(comparisonInputState xs).pc = 0` | Consumer line 66: `∀ xs, (comparisonInputState xs).extent = 1`; a different true fact does not supply it. |
| B11_EXTENT_DELETE | `oracleExtentOne` field deleted | Consumer line 66: the projection `h.oracleExtentOne` no longer exists. |
| B12_ACCEPT_COMMENT | One comma removed from the HeaderUse module docstring | All three stages succeed and the consumer prints `PRE1-BUILDER-TYPED-CONSUMERS PASS`. |
| B13_TOY_PIN_DRIFT | Consumer toy pin `steps = 4` changed to `steps = 5` | Consumer line 84: the `decide`-checked toy run (`[load 1 0, reserve 2, store 2 1, halt 1]` on `wordInputState 40 [3]`) has exactly 4 steps; the pin is live. |
| B14_HEADERFIRST_CONSUMER | `HeaderUse.headerFirst` becomes `True`, the four run-level fields lose their default proofs and `headerUse_of_program` supplies them from its own `hhead` (condition C2, audit P2-3) | Consumer line 20: for every `program` with `HeaderUse program`, `program[0]? = some headerInstruction`; the certificate still elaborates, so only the projection breaks. |
| B15_ARRAYRUN_FINAL_WEAKEN | `runArray_abstract` loses its last conjunct (`(runArray ...).final.abstract = (run ...).final`) with a valid shorter proof; `"manifest": "rehash"` (condition C3) | Consumer line 335: the array-backed run agrees with the frozen run on steps, categories, writes, reserves, result and the final abstract state; the weakened producer still builds, so only the projection breaks. |

| B16_PROGRAM_PARAMETER | `def builderProgram : List BInstr :=` becomes `def builderProgram (w : Nat := 0) : List BInstr :=` in `Builder/Program.lean`; `"manifest": "rehash"` (CONTRACT.md V3-7 (i)) | Consumer line 370: `example : List BInstr := @builderProgram` (V3-2); the default argument keeps every unapplied use in the producer and in the other consumer lines elaborating, so only the `@` pin breaks. |
| B17_PROGRAMWORD_PARAMETER | The same parameter on `builderProgramWord` | Consumer line 371: `example : List BInstr := @builderProgramWord`. |
| B18_EFFICIENTBUILD_RELOCATION | `efficientBuild` (with its docstring) is removed from `Builder/Program.lean` (`"manifest": "rehash"`) and the same definition is added, in namespace `RMQ.SuccinctFinal.PackedConstruction`, to the consumer-side module `Proof/Constants.lean` by a companion edit (CONTRACT.md V3-1) | Consumer line 352: the V3-1 `run_cmd` finds `efficientBuild` in module `RMQ.Core.WordRAM.Construction.Proof.Constants`, not `...Builder.Program`; the body pin `efficientBuild_def` still elaborates. |
| B19_L_KEY_NUMERAL | Consumer `ProgramContract builderProgram (fun _ => builderProgram) 2107 8079` becomes `2108 8079` (V3-7 (ii), `L`) | Consumer line 405: the producer instance `Proof.builderProgram_contract` does not have the mutated type. |
| B20_L_WORD_NUMERAL | Consumer `ProgramContract builderProgramWord (fun _ => builderProgramWord) 2107 8089` becomes `2108 8089` (`L` at the word constant) | Consumer line 408. |
| B21_B_NUMERAL | `8079` becomes `8080` in the comparison-oracle instance (`B`) | Consumer line 405. |
| B22_BPRIME_NUMERAL | `8089` becomes `8090` in the word-model instance (`B'`) | Consumer line 408. |
| B23_P0_NUMERAL .. B32_P9_NUMERAL | Element `k` (`k = 0..9`) of the literal position list `P = [411, 412, 413, 414, 415, 429, 430, 431, 432, 433]` in the filter conjunct of `builder_leaf_difference` is increased by 1000 (V3-4, one case per element) | Consumer line 401: the proof term `Proof.builder_leaf_difference` does not have the mutated type. |
| B33_D_NUMERAL | Consumer `builderBudget n = 1000000000 + 1000000000 * n` becomes `1000000001 + 1000000000 * n` (V3-6a, `D`) | Consumer line 410: the `rfl` pin of the fuel body fails. |
| B34_C_NUMERAL | The same pin becomes `1000000000 + 1000000001 * n` (`C`) | Consumer line 410. |
| B35_COMPILE_REALIZES_WEAKEN | `EvalG.compile_realizes'` (`Compiler.lean`) loses the conjunct `ts.length = k` with a valid shorter proof; `"manifest": "rehash"` (condition C3) | Consumer line 218 (`compiler_realizes`): a realized block runs in exactly its source cost. |
| B36_COMPILE_SAFE_WEAKEN | `SafeEval.compile_safe` loses its final conjunct `s''.Fits W` | Consumer line 228 (`compiler_safe`). |
| B37_RUN_WRITE_AT_WEAKEN | `run_write_at` (`Calculus.lean`) loses its fault branch (an out-of-extent store faults, leaves memory unchanged and records no write) | Consumer line 108 (`calc_write_at`). |
| B38_RUN_LOAD_AT_WEAKEN | `run_load_at` loses its backward conjunct (a running post-state implies an in-extent, present cell) | Consumer line 123 (`calc_load_at`). |
| B39_WRITES_REPLAY_SIBLING | `writes_replay` states the sibling fact `final.extent = final.extent` | Consumer line 128 (`calc_writes_replay`): the final memory is the fold of the write log over the initial memory. |
| B40_RUN_AGREE_KEYS_WEAKEN | `run_agree_of_reads` and `run_agree_of_supplied` require key agreement at every index instead of at the run's key reads | Consumer lines 154 and 161 (`calc_agree_of_reads`, `calc_agree_of_supplied`). |
| B41_FUEL_EXTENSION_WEAKEN | `RunsTo.fuel_extension` concludes only `(run ...).final = s'` instead of `run ... = ⟨s', ts⟩` | Consumer line 142 (`calc_fuel_extension`). |
| B42_SAFETY_SHIFT_ARM_WEAKEN | The arithmetic arm of `Prim.SafeAt` (`Safety.lean`) loses `(op = .shl ∨ op = .shr → s.regs rhs < W)` | Consumer line 450 (`safety_safeAt_arms`, all thirteen arms by `Iff.rfl`); no builder-closure proof consumes the shift obligation, so the producer still builds. A `reserve`-arm drift was probed first and rejected at the producer (`Safety.lean:162`, `Prim.safe_fits`), so it was not registered. |
| B43_CARTESIAN_QUADRATIC_RESCAN | `profile: stackpass`; in `Builder/Cartesian.lean` each stack step first counts a copy of the current index down to zero before the push (quadratic total work, V2-7.6); `"manifest": "rehash"` | Producer: `RMQ/Core/WordRAM/Construction/Proof/StackPass.lean:287:` (the stack-pass cost and frame proofs no longer elaborate). |
| B44_PROGRAM_SEMANTIC_IMPORT | `import RMQ.Core.WordRAM.Packed.Allocation` added to `Builder/Program.lean` | Firewall: `PRE1-BUILDER-FIREWALL imports rejected: RMQ/Core/WordRAM/Construction/Builder/Program.lean`. |
| B45_RUNFACTS_WORK_WEAKEN | `profile: capstone`; `BuilderRunFacts.work` (`Proof/RunFacts.lean`) becomes `≤ 1000000001 * n + 1000000000` | Capstone consumer lines 231 and 353 (`check_comparisonRun_work`, `check_wordRun_work`). |
| B46_RUNFACTS_WORKSPACE_CW_WEAKEN | `BuilderRunFacts.workspace` becomes `≤ 3200001 * n + 3200000` (`Cw`) | Capstone consumer lines 275 and 397. |
| B47_RUNFACTS_WORKSPACE_DW_WEAKEN | `BuilderRunFacts.workspace` becomes `≤ 3200000 * n + 3200001` (`Dw`) | Capstone consumer lines 275 and 397. |
| B48_RUNFACTS_NOINPUTWRITES_WEAKEN | `BuilderRunFacts.noInputWrites` becomes `s0.extent ≤ e.1 + 1` (its producer proof is `omega` from the ownership fact, so the producer still builds) | Capstone consumer lines 306 and 428. |
| B49_RUNFACTS_REGISTERBANK_WEAKEN | `BuilderRunFacts.registerBank` covers registers from 401 | Capstone consumer lines 290 and 412. |
| B50_CAPSTONE_CW_NUMERAL | Capstone consumer: `3200000 * xs.length + 3200000` becomes `3200001 * ...` in `check_comparisonRun_workspace` (V3-7 (ii), `Cw`) | Capstone consumer line 275. |
| B51_CAPSTONE_DW_NUMERAL | The same check with `+ 3200001` (`Dw`) | Capstone consumer line 275. |
| B52_CAPSTONE_ACCEPT_COMMENT | `profile: capstone`; one comma added to the `Capstone.lean` module docstring | All three stages succeed and the capstone consumer prints `PRE1-CAPSTONE-TYPED-CONSUMERS PASS`. |
| B53_RUNFACTS_HALTS_WEAKEN | `profile: capstone`; `BuilderRunFacts.halts` (`Proof/RunFacts.lean`) becomes `∃ fuel, (run program fuel s0).final.status = s0.status`, true of every program's run at fuel 0 and no longer naming the halted status, with the producer proof `⟨0, rfl⟩` (registry version 2, audit PRE-1-A2 P2-2) | Capstone consumer lines 227 and 349 (`check_comparisonRun_halts`, `check_wordRun_halts`): the run at the pinned fuel `builderBudget xs.length` halts; the weakened producer builds (15 s producer stage on the probe clone), so only the projections break. |
| B54_RUNFACTS_HALTS_FUEL_LARGER | `profile: capstone`; `halts` at the larger literal budget `2000000000 + 2000000000 * xs.length`, proved from the same run by `RunsTo.fuel_extension` | Capstone consumer lines 227 and 349: halting at a larger fuel does not supply halting at `builderBudget xs.length`. |
| B55_RUN_SAFE_LENGTH_WEAKEN | `Run.Safe` (`Safety.lean`) bounds each transition's `Prim.Safe` by `program.length + 1` instead of `program.length` (a jump or branch to one past the program end is admitted), with a proved monotonicity lemma and a coercion so the unchanged `Run.Safe.of_transitions` still elaborates; `"manifest": "rehash"` (audit PRE-1-A2 P3-4). Dropping the post-state fit conjunct was probed first and stops at the producer (`Run.Safe.final_fits` consumes it) | Consumer line 457 (`safety_run_safe_definition`, the `Iff.rfl` pin of `Run.Safe`): every other builder-consumer line refers to `Run.Safe` by name and still elaborates, and the producer closure builds (100 s producer stage on the probe clone). The fit-conjunct drop stops at the producer (`Compiler.lean:60`, `:77`, `:96`). |

B01-B03 require the named firewall failure with firewall exit nonzero and no
later stage executed; B04 requires a nonzero producer after a passing firewall;
B05-B11 and B13-B15 require a nonzero consumer after passing firewall and producer
with exactly the registered failing line set; B12 requires all three stages to
pass. Stage provenance is mandatory, so a producer or consumer failure cannot
close a firewall row and a firewall failure cannot close a consumer row. Any
mutation of a closure module is caught at the firewall's hash surface first,
unless its case carries `"manifest": "rehash"` (condition C3): then the runner
replaces exactly that module's manifest digest by the mutant's for the duration
of the case and restores source and manifest bytes together, so the mutation
reaches the producer and consumer stages (B15). The committed manifest never
changes. The exit code remains the verdict. Since repair PRE-1-R2 (audit
PRE-1-A2 P2-1) both typed consumers print their marker if and only if the whole
file elaborates with no error-severity message and the witness exists without
`sorryAx` (and, for the builder consumer, `consumerGuards` holds): the marker
command re-elaborates the file's own source text in-process with itself blanked
and reads every command's message log, because Lean 4.22 resets the command
message log before each command and a later command cannot otherwise see an
earlier error. The version-1 condition (witness without `sorryAx` only) printed
the marker in B16-B18 and for maximum-recursion-depth failures; the control
matrix `repair-r2/marker_controls.json` records both behaviours, and registry
version 2 additionally requires the marker's absence for every consumer-stage
rejection.

Stage S7 constants (runner and registry version 1 extended, 34 cases): the
producer stage also builds `RMQ.Core.WordRAM.Construction.Proof.Constants`,
which imports `Builder.Program` and `Contract` and proves the V3-4 and V3-5 pins
by `rfl` on the compiled lists; it does not import the stage proof tower, so a
closure-module mutation rebuilds only the builder text and these pins.
`Builder/Program.lean` is re-hashable. A case may carry one `companion` edit
(`path`, `before`, `after`), restricted to `Proof/Constants.lean`, applied and
restored with its primary edit and checked byte-exactly after restoration; B18
uses it to move `efficientBuild` out of the program host module. The registry
self-test rejects a companion outside that path, on the primary path, without
change, or with a missing field. The numeral cases B19-B34 change only the
consumer; their failing lines were measured before registration on scratch
copies of the consumer (BUILDER_STAGE_LOG.md C7-6).

Replay extension (registry 52 cases, WDD-20260913-PRE1-023): a case may carry
`"profile": "capstone"` (producer `lake build RMQ.Core.WordRAM.Construction.Capstone`,
consumer `lake env lean RMQ/Validation/PreprocessingContract.lean`, surfaces
`PreprocessingContract.lean:<line>:`, marker `PRE1-CAPSTONE-TYPED-CONSUMERS PASS`)
or `"profile": "stackpass"` (producer `lake build RMQ.Core.WordRAM.Construction.Proof.StackPass`,
then the builder consumer); without the field the builder profile above applies,
and an explicit `builder` value, an unknown value or a surface file that does
not match the profile is rejected by the registry self-tests. Consumer error
lines are extracted for the profile's consumer file only, and a rejection also
requires that profile's marker to be absent (registry version 2). The baseline
compiles the builder profile and then the capstone profile, which must print its
marker. In full mode, after the self-tests and both baseline compiles and before
the first case, a validator stage runs `lake build
rmq_preprocessing_validate`, the executable in full mode (it must print
`PRE1-VALIDATE PASS cases=<n> mode=full`, and the executable fails unless all eleven fixture IDs ran) and each negative control selected by
`PRE1_VALIDATE_SELECTOR=id:<ID>` (nonzero exit and its pinned message
required). The B35-B52 surfaces were observed by focused `-OnlyCase` runs before
registration (BUILDER_STAGE_LOG.md R-1, R-2).
