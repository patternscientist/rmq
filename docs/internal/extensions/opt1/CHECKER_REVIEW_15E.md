Scoped verdict: **needs another worker pass for the fail-closed diagnostic contract**. I found one concrete parser counterexample and one artifact-binding limitation. Neither establishes kernel failure or a bad verdict in the actual 80-case campaign.

Fresh blind review: base `ac5af8e416f906391dc117f083a883acc053a268`, target `15e5266888c35a38733ca14846e4ad53ed119ebe`, governance `0e6a00f654abc64f8b68988fa9675b9a839dca2f`. Requirements came only from the initial acceptance matrix at `1f3a4199eaa95324cd1daaadbab89340ca8392c4`. I read no worker reports, previous verdicts, appended matrices, or campaign receipts.

Findings:

1. **P2 — An unclassified exception can accompany an accepted field rejection.** In [packed_optimized_certificate_replay.ps1:160](/C:/Users/poin/.codex/worktrees/1580/RMQ/scripts/packed_optimized_certificate_replay.ps1:160), the production predicate accepts bounded exit 1, checks every *recognized located error*, prohibits `^error:` and listed resource phrases, then requires the selected field name somewhere in output. It does not classify all remaining error output.

   I extracted the exact `Assert-CRejected` function through PowerShell’s AST and supplied `W03-widthBounds` with:

   ```text
   ExitCode=1; TimedOut=False; OutputLimitExceeded=False
   stdout:
   RMQ/Core/WordRAM/Optimization/Consumers.lean:33:2: error: type mismatch
     certificate.widthBounds
   stderr:
   uncaught exception: failed to write output
   ```

   With `Output = stdout + stderr`, **the production function accepted this fixture**. The prefix `uncaught exception:` is a supported Lean output form recognized elsewhere by [packed_optimized_runtime.ps1:137](/C:/Users/poin/.codex/worktrees/1580/RMQ/scripts/packed_optimized_runtime.ps1:137). I did **not** establish that the current compile-only cases generate this mixed stream.

   Thus, over the parser’s input domain, `P = accepted diagnostic fixture` does not imply `Q = exclusively the intended field/type rejection, with no unclassified exception`. This limits `INV-MUTATION-REPRODUCIBILITY`’s exact-failure-surface check. A narrow repair should reject the exception form and retain the valid indented-detail control. The repair is needed for the stronger parser contract; actual campaign validation additionally depends on inspecting its real output.

2. **P2 — Import stability is checked; prior source/artifact correspondence remains an external prerequisite.** [packed_optimized_runtime.ps1:284](/C:/Users/poin/.codex/worktrees/1580/RMQ/scripts/packed_optimized_runtime.ps1:284) checks artifact/source/dependency modification-time ordering and records hashes. [packed_optimized_certificate_replay.ps1:416](/C:/Users/poin/.codex/worktrees/1580/RMQ/scripts/packed_optimized_certificate_replay.ps1:416) checks that recorded bytes remain unchanged.

   These predicates do not imply that an already-present `.olean` was built from the recorded source. Counterexample: a stale artifact given sufficiently recent timestamps, then left unchanged, satisfies both checks. I did not modify artifacts or reproduce this against the running campaign.

   This is a production evidence-binding limitation, not a kernel-proof finding. Exact checked-build receipts binding the imported artifact hashes to the audited sources can address actual campaign validation. Without that external binding, the runner alone cannot establish it.

Positive checks and acceptance dispositions:

- **`REQ-OPT-CONSUMER` / `INV-CERTIFICATE-ANTI-BYPASS`: source structure supports the requested mechanism.** All 39 producer propositions and both consumer forms are compared against SHA256-pinned `FIELDS.json` bytes at replay lines 91–125. Expected types are not inferred from mutants. For example, [Consumers.lean:30](/C:/Users/poin/.codex/worktrees/1580/RMQ/RMQ/Core/WordRAM/Optimization/Consumers.lean:30) explicitly demands `∀ n, Nat.log2 (n + 2) + 1 ≤ wordWidth n ∧ wordWidth n ≤ 192 * (Nat.log2 (n + 2) + 1)` and projects `certificate.widthBounds`; its canonical consumer applies that theorem to `compactPackedQueryCapstone_holds`. This is source inspection, not a fresh Lean verification.
- **`REPLAY-EXACT-REGISTRY`: zero-Lean checks passed.** The production registry self-test rejects missing, duplicate, reordered, and mutated producer-field fixtures. Source fixes 39 D/W pairs plus two accepts; completion compares executed IDs against selected IDs.
- **`REPLAY-SELECTOR-NONVACUITY`: actual script-boundary probes passed.** Omitted selected 80; valid `W03-widthBounds` selected exactly one. Explicit empty, whitespace, malformed, unknown, and duplicate selectors exited 1. All probes used `-SelectorProbeOnly`; no Lean launched.
- **`REPLAY-SUBPROCESS-DEADLINE`: source review supports bounded execution and failure propagation.** Stage/campaign limits feed the owned process helper; timeout/output-limit results cannot reach a successful case verdict. Host ownership behavior was not exercised here.
- **`INV-MUTATION-REPRODUCIBILITY`: correct producer/consumer order is explicit**, subject to the findings above and actual campaign evidence. Replay lines 242–273 copy fixed consumer bytes, mutate both producer fields and initializers, compile Certificate and Capstone into a unique case library, then check Consumers using that library first. This avoids reuse of a previous case’s mutated producer artifacts. Finally blocks restore isolated source bytes and check hashes; final success follows original-source, selected-status, and import-hash comparisons.

The new mixed `error: cannot open file` fixture was rejected, as was a located error at another consumer’s line. Indented quoted `"error: …"` detail remained accepted. These are parser tests, **not evidence that all 78 Lean mutants reject**.

Preflight passed in explicit no-role mode with the actual runtime catalog `rmq-audit-prompt, rmq-coordinator, rmq-proof-sprint`. The inspected Lean surfaces and supporting runtime/ownership scripts are unchanged across the delta. Narrow trust scans of Certificate, Capstone, and Consumers found no listed trust-expansion constructs. No files were edited. Lean/Lake, full gates, full-repository trust certification, process campaigns, and clean-tree snapshots remained with the assigned runtime/coordinator owners.

Conceptually, this mechanism checks whether each frozen public proposition survives removal or weakening of its certificate field. Its live assumptions include the pinned Lean executable, correctly bound imported artifacts, unchanged fixed consumers, and faithful diagnostic classification. The skeptical question is: **Did every mutant fail because its exact field dependency broke after both changed producers compiled, with no other failure supplying the verdict?**

Next target: repair the narrow exception-classification gap, verify its regression and positive control, then validate exact campaign outputs and imported-artifact bindings. This chat report is the deliverable for coordinator persistence; no report file was written.
