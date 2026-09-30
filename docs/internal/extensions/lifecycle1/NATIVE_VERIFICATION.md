# LIFE-1 native verification ledger

This ledger records local candidate evidence for the new finite lifecycle executable. Final corrected native replay passed all 16 exact cases. It does not record coordinator acceptance, an aggregate gate, or the independent public dependency campaign.

## Executed objects and reference

`RMQ/Validation/PackedLifecycle.lean` imports the new `Executable` and `Controls` modules. Each fixture supplies input with `Executable.initialOwner`, executes `runOwner (Layout.program model).toArray`, and executes later requests through `Executable.queryOwner`. It never supplies a precomputed canonical allocation as implementation state. Expected answers come from its own strict-comparison half-open scan, with leftmost ties and packet zero for invalid intervals.

Validation's separate history-free `counted` fold calls actual `stepArray`. The theorem `counted_owner` proves its final owner equals the production runner for every program, fuel, initial owner and counters. `category_index_exact` proves the exhaustive category mapping. The native check compares every owner field, category sum, scalar size changes, actual allocation/release balance, actual finalizer source base/length, key retirement counts and literal empty final key arrays. Every retained numeric bank has size 8,273. Every subsequent query uses the actual four charged boundary events and preserves the exact retained memory array.

The ordered registry is pinned independently in Lean and PowerShell:

| ID | Input model / shape | Requests | Expected verdict |
| --- | --- | --- | --- |
| L01-W-EMPTY | word, empty | `(0,0)` | PASS |
| L02-C-EMPTY | comparison, empty | `(0,1)` | PASS |
| L03-W-SINGLE | word, `[-7]` | `(0,1)` | PASS |
| L04-C-SINGLE | comparison, `[-7]` | `(0,1)` | PASS |
| L05-W-REPEAT | word, `[2,2,2]` | `(0,3),(1,3)` | PASS |
| L06-C-REPEAT | comparison, `[2,2,2]` | `(0,3),(1,3)` | PASS |
| L07-W-TIE | word, `[4,-3,-3,8]` | `(0,4),(2,4)` | PASS |
| L08-C-TIE | comparison, `[4,-3,-3,8]` | `(0,4),(2,4)` | PASS |
| L09-W-INVALID | word, `[3,1]` | `(2,1),(0,3),(1,1),(0,2)` | PASS |
| L10-C-INVALID | comparison, `[3,1]` | `(2,1),(0,3),(1,1),(0,2)` | PASS |
| L11-W-DIRTY | word, actual dirty bank after first query | `(0,4),(1,3)` | Positive accepts; patched entry rejects; PASS |
| L12-C-DIRTY | comparison, actual dirty bank after first query | `(0,4),(1,3)` | Positive accepts; patched entry rejects; PASS |
| L13-W-N24 | word, 24-element geometry | `(0,24),(8,23),(12,24),(1,22)` | PASS |
| L14-C-N24 | comparison, 24-element geometry outside word domain | same as L13 | PASS |
| L15-W-N83 | word, 83-element geometry | `(0,83),(27,82),(41,83),(1,81)` | PASS |
| L16-C-N83 | comparison, 83-element geometry outside word domain | same as L15 | PASS |

Word geometry element `i` is `((17*i + i/3) % 11) - 5`, interpreted in `Int`. Comparison geometry multiplies that value by `2^(PackedWordRAM.wordWidth n + 5)` and adds 17. Cases L14/L16 explicitly assert that at least one actual key lies outside the signed word-input interval. Every word case checks the complete signed-input range and unsigned header bound; every request checks the represented endpoint bounds.

## Commands and build history

Working directory was `C:/Users/poin/.codex/worktrees/8941/RMQ`, on Windows with `leanprover/lean4:v4.22.0`. The local `.lake/dev-run.ps1` development helper takes the shared heavy-process mutex once, invokes the existing owned-process helper with `LEAN_NUM_THREADS=1`, and saves full stdout/stderr and a JSON process receipt. The native replay script also takes the mutex once, directly owns each native child, and never calls the development wrapper recursively.

Exact relevant commands:

```powershell
powershell -ExecutionPolicy Bypass -File .lake/dev-run.ps1 -Mode lean -Target RMQ/Core/WordRAM/Lifecycle/Controls.lean -Label lifecycle-controls-03 -DeadlineSeconds 300
powershell -ExecutionPolicy Bypass -File .lake/dev-run.ps1 -Mode build -Target rmq_lifecycle_validate -Label lifecycle-native-01 -DeadlineSeconds 3600
powershell -ExecutionPolicy Bypass -File .lake/dev-run.ps1 -Mode lean -Target RMQ/Validation/PackedLifecycle.lean -Label lifecycle-validator-05 -DeadlineSeconds 300
powershell -ExecutionPolicy Bypass -File .lake/dev-run.ps1 -Mode build -Target rmq_lifecycle_validate -Label lifecycle-native-02 -DeadlineSeconds 3600
powershell -ExecutionPolicy Bypass -File scripts/lifecycle_validator.ps1 -Stage full -DeadlineSeconds 1800
powershell -ExecutionPolicy Bypass -File .lake/dev-run.ps1 -Mode lean -Target RMQ/Validation/PackedLifecycle.lean -Label lifecycle-validator-06 -DeadlineSeconds 300
powershell -ExecutionPolicy Bypass -File .lake/dev-run.ps1 -Mode build -Target rmq_lifecycle_validate -Label lifecycle-native-03 -DeadlineSeconds 600
powershell -ExecutionPolicy Bypass -File scripts/lifecycle_validator.ps1 -Stage full -DeadlineSeconds 1800
```

| Receipt / command | Exit and elapsed time | Meaning |
| --- | --- | --- |
| `lifecycle-controls-03` | 0; 4.489 s | Nine kernel controls plus the two dirty-entry projection bridges compile, with empty diagnostics. |
| `lifecycle-native-01` | Interrupted; shell exit 1; no successful build receipt | Coordinator requested the cold build yield to public-interface checks. The exactly identified owned PowerShell wrapper was stopped; kill-on-close ownership ended its job. Wrapper/bootstrap/Lake PIDs 25020/14868/26736 were checked absent. The interruption record stores progress 364/716 observed before the stop; the final retained stdout had reached 416/716. This is explicitly `INTERRUPTED_NOT_CERTIFIED`, not a timeout or success. Partial completed artifacts were retained. |
| `lifecycle-validator-05` | 0; 6.253 s | Sixteen-case development source with represented-input checks compiled. |
| `lifecycle-native-02` | 0; 461.463 s | Cold C continuation and named executable build completed all 716 tasks. |
| Development full replay | 0; full child 72.571 s | Directory `.lake/lifecycle-validator/90657624f27e48dfa46d57f42591589a`. All 16 cases and selector controls passed on the earlier comparison fixture. |
| `lifecycle-validator-06` | 0; 13.122 s | Corrected outside-word-domain comparison fixtures compiled, with empty diagnostics. |
| `lifecycle-native-03` | 0; 12.593 s | Final corrected source rebuilt and linked incrementally. |
| Final full replay | 0; full child 81.505 s | Directory `.lake/lifecycle-validator/da0d7bf710d148dfa5e439022fca3ede`; nine owned process receipts below. |

The first large comparison fixtures used `2^80`. Inspection showed that 80 is below this project's size-dependent word width, so those keys did not demonstrate the intended outside-word-domain edge. The only subsequent code change strengthened that scale to `2^(W(n)+5)` and required an actual violating key in L14/L16; IDs, query shapes and production code were unchanged. This material fixture correction justified the second full replay. No full replay was repeated on an unchanged binary. The final 1,800-second full-run deadline retained margin over both the earlier PRE83 timing of approximately 267 seconds and observed development runtime; each startup/selector process has a 30-second deadline. The native build reused pre-existing predecessor modules whose linter warnings were replayed by Lake; the new narrow module checks had no diagnostics.

The development build helper is local scratch, not required for portable reproduction. In a fresh checkout with the pinned toolchain, build the named executable explicitly and invoke the committed bounded runner:

```powershell
lake build rmq_lifecycle_validate
powershell -ExecutionPolicy Bypass -File scripts/lifecycle_validator.ps1 -Stage full -DeadlineSeconds 1800
```

The committed runner has no implicit build, bytecode fallback, old-validator invocation or aggregate-gate fallback. A focused replay is `-Stage single -Case L11-W-DIRTY`. Repository-wide final certification remains coordinator-owned.

## Final nine receipts and exact surfaces

The final directory contains `processes.json`, per-process full stdout/stderr, `identity-before.json`, `identity-after.json`, and `PASS.json`. Output is saved before any verdict classification. Every completed process below reports `timedOut=false`, `outputLimitExceeded=false`, `ownership=kill-on-close-job`, and `terminatedIds=[]`.

| Process | Actual / expected exit | Seconds | Required output surface |
| --- | --- | --- | --- |
| registry | 0 / 0 | 3.056 | Exactly 16 ordered `LIFE1-REGISTRY` records, with pinned model, kind and PASS mapping. |
| startup | 0 / 0 | 2.508 | `LIFE1-STARTUP\|PASS\|cases=16` |
| focused | 0 / 0 | 2.669 | Only L01-W-EMPTY case record, then `LIFE1-PASS\|mode=single\|cases=1`. |
| reject-empty | 1 / 1 | 3.060 | stderr exactly `LIFE1-FAIL\|empty-selector`; stdout empty. |
| reject-whitespace | 1 / 1 | 4.646 | stderr exactly `LIFE1-FAIL\|whitespace-selector`; stdout empty. |
| reject-unknown | 1 / 1 | 4.601 | stderr exactly `LIFE1-FAIL\|unknown-selector`; stdout empty. |
| reject-duplicate | 1 / 1 | 3.443 | stderr exactly `LIFE1-FAIL\|duplicate-selector`; stdout empty. |
| reject-channels | 1 / 1 | 2.382 | stderr exactly `LIFE1-FAIL\|duplicate-selector-channel`; stdout empty. |
| full | 0 / 0 | 81.505 | Exactly the ordered 16 PASS case records, then `LIFE1-PASS\|mode=full\|cases=16`. |

The separator escaping above is Markdown table syntax; actual logs contain ordinary `|`. Successful processes require empty stderr. Extra/mixed diagnostics, missing or duplicate cases, wrong terminal markers, output truncation, timeout, wrong process ownership or nonempty cleanup IDs reject. Failure never prints a terminal success receipt. The top-level runner separately rejects a missing `Case` in single mode, an explicitly empty or whitespace case, unknown case IDs, and a case supplied in startup/full mode before launching a child. Native environment selection uses nonempty `LIFE1_VALIDATE_SELECTOR=id:` to preserve an explicit empty decoded selector through Windows argument handling. Simultaneous argument and environment selectors reject.

The kernel selector guards cover empty argument and empty environment selection, whitespace and padded IDs, unknown IDs, duplicate arguments, duplicate channels, missing environment prefix, and the exact positive single-ID result. PowerShell parameter-boundary checks also observed the intended missing/empty/unknown/wrong-stage rejection messages. There is no source restoration procedure to fake: the dirty challenge changes a fresh in-memory array only. Pinned source and binary hashes must match before/after every complete native replay.

## Real second-query control and results

Both L11/L12 execute the actual complete lifecycle from input `[4,-3,-3,8]` and request `(0,4)`. They discover nonzero register 400 in the real halted owner. After the actual four charged request-entry events for `(1,3)`, the positive run executes the real service setup. The challenged run starts from that exact same admitted owner and changes only `constant 400 0` to `move 400 400`. Both reach running PC 0 with the same retained memory and register-bank size; the positive entry clears register 400 and the challenged entry preserves its nonzero value.

The exact formal bridge is `Controls.query_entry_implies_clean`: for every owner, size, endpoints and `r ≥ 3`, equality of `Retained.projectQueryState owner.toState` with `PackedWordRAM.initialState n left right` implies `entryRegisterClean owner r = true`. `dirty_register_rejects_entry` proves the contrapositive. Runtime tests check this same projection on both executions and also compare the complete finite entry bank. The observed negative is an entry-ABI failure, not a claim of a wrong numerical RMQ answer. Each unmodified second query separately passes the independent answer, category, cost and unchanged-allocation checks.

Representative full-run outputs are:

| Case pair | Initial steps, word / comparison | Final logical words | Releases, word / comparison | Later query steps including boundary events |
| --- | --- | --- | --- | --- |
| L01 / L02 | 13,601 / 13,608 | 175 | 132 / 132 | 0 |
| L11 / L12 | 39,459 / 39,464 | 178 | 756 / 752 | 16,675 each |
| L13 / L14 | 84,265 / 84,270 | 186 | 2,466 / 2,442 | 76,246 each for three queries |
| L15 / L16 | 214,277 / 214,282 | 211 | 8,225 / 8,142 | 81,031 each for three queries |

## Checked identity and limits

These final identities are raw working-tree bytes, independently compared before and after final native replay:

| Artifact | Bytes | SHA-256 |
| --- | --- | --- |
| `RMQ/Validation/PackedLifecycle.lean` | 14,684 | `9da6975799204debd1a92127e4b585339da7983a55ce9fa6510d857f0dbc93b2` |
| `RMQ/Core/WordRAM/Lifecycle/Controls.lean` | 12,870 | `ddc5ed3b43c85c01e19d880ad3ebf95a0cca83f48f69396f784965d6e2956122` |
| `scripts/lifecycle_validator.ps1` | 7,768 | `376beb1533ed020d17a796a40f6d8a20941ddd8da60dc39b7b4639bd67073b29` |
| `lakefile.toml` | 1,170 | `a82e092bfd4be06ff7dc3ceb2454b633b0141f7f2e09ca00c8060592c3475898` |
| `.lake/build/bin/rmq_lifecycle_validate.exe` | 25,018,368 | `4752591ec5a7d962e09440391aa38d0e2fc534b2f04775aab9c0c735e43ba99c` |

The identity files additionally pin `Executable.lean`, `ArrayRun.lean`, `Machine.lean`, `Program.lean` and `Service.lean`. The used `scripts/owned_process_tree.ps1` is SHA-256 `6690ad4f9e3aee9596e53e89d3d242e4be59c0a04733bc50184ae35b292ff90e`; local `.lake/dev-run.ps1` is SHA-256 `3ac00dd142033ef83fcbb746dedb1dfbf5b8836f7ca6771e4826dadca05b648f`. The full contract integrity checker independently passed 43 rows and all eight columns without changing the frozen matrix. The repository scans for forbidden trust constructs and `native_decide`/`Lean.ofReduceBool` were empty, and `git diff --check` plus direct trailing-whitespace checks passed on the owned files.

This runner is Windows-specific: it expects `.exe` and verifies kill-on-close Windows job ownership. No cross-platform execution claim follows. Finite array sizes describe logical ownership; neither runtime tests nor the abstraction prove native backing-capacity reclamation or freedom from external aliases. Comparison keys are arbitrary `Int` values in their explicit input model, and their host arithmetic cost is not equated with one native machine word. The tested positive numeric-word inputs and request endpoints satisfy their represented-domain guards. Finite fixtures give operational regression evidence; the all-input correctness, refinement and cost claims come from the kernel proofs and public consumer. No old validator or aggregate gate was run for this leaf.
