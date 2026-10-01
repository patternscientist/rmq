# LIFE-1 dependency verification

Local result: all 26 registered cases passed (23 expected rejections and three expected acceptances). Coordinator acceptance of LIFE-1 remains separate.

The independent clients compile against the real public theorem and all four production-receipt groups. The producer must compile cleanly before a client rejection counts. No weaker producer compilation error, warning, timeout, unrelated client diagnostic, or altered client is accepted as the intended rejection.

## Replayed commands and scope

```powershell
pwsh -NoProfile -File scripts/lifecycle_dependency_replay.ps1 -SelfTestOnly
pwsh -NoProfile -File scripts/lifecycle_dependency_replay.ps1 -StartupOnly
pwsh -NoProfile -File scripts/lifecycle_dependency_replay.ps1 -OnlyCase D01_CONSTRUCTION
pwsh -NoProfile -File scripts/lifecycle_dependency_replay.ps1 -OnlyCase D13_ALIAS_PHYSICAL
pwsh -NoProfile -File scripts/lifecycle_dependency_replay.ps1
```

Final full receipt directory: `C:/Users/poin/.codex/worktrees/8941/RMQ/.lake/lifecycle-dependency/20260921T021035666-83fc2827`. The final invocation exited zero. Each of its 52 compiler processes had a 120-second positive deadline and a 16,777,216-byte output limit. Combined measured compiler wall time was 430.055 seconds; maximum individual stage was 17.258 seconds. Mutex waiting, private import copying, hashing and cleanup are outside those per-process measurements.

Platform at evidence collection: `Windows-11-10.0.26200-SP0` (OS API `Microsoft Windows NT 10.0.26200.0`), PowerShell `7.6.5`; pinned toolchain `leanprover/lean4:v4.22.0`. The runner uses the Windows kill-on-close owned-job helper. Its actual Lean binary, toolchain file and owned-process helper hashes are included below. Compiler invocations use `--json`, a fresh producer source and `.olean`, `LEAN_NUM_THREADS=1`, and a complete private RMQ import package. The core client imports Capstone only; the provenance client imports its independently rebuilt Provenance producer.

The runner owns one shared heavy mutex for the complete campaign and does not nest another compile wrapper. One private import tree is copied per invocation; the original Capstone and Provenance bindings are restored and hash-checked before and after every case. Source edits and fresh producer artifacts remain inside the checked `.lake` shadow root. Original source and shared artifacts are never written.

## Frozen expected propositions

`RMQ/Validation/LifecycleContract.lean` projects all seven public fields at independently written expected types. Its retained-state, readiness and prefix-profile definitions explicitly spell out memory/extent identity, empty comparison functions and extents, finite numeric support, same-width fits, peak ownership and comparison resource bounds. It does not use the producer property aliases as its expected propositions.

| Client | Required proposition and object connection |
| --- | --- |
| C01 | One actual BuildStage producer/body; bounded construction trace; canonical live entry and represented request registers; exact continuous-run concatenation, compact-query suffix, entry count 4+8271 and exact step sum. |
| C02 | Same final canonical memory/extent/resources, semantic halted packet and actual steps bounded by construction budget+160253. |
| C03 | Every actual fuel prefix has same-width fits, clean tail, finite bank, peak bound and comparison bounds; every actual instruction transition is Safe. |
| C04 | Complete ordered physical-read projection, every-prefix physical extent/value width, exact producing-prefix state for each actual read, successful checked address/value bounds and each fetched instruction encoding field backed by counted fixed code. |
| C05 | Actual runOwner projection and complete observed run, exact retained array bank, canonical state, empty key arrays and actual memory+code+register+8-control capacity. |
| C06 | Any halted retained owner plus represented next request yields the charged actual query owner/run; canonical preservation, semantic halt, same memory, exact array refinement, steps≤160257, ordered header/compact reads, every transition ActionSafe and canonical, and actual capacity. |
| C07 | One query-independent little-o residual, logarithmic same width with factor192, and every encoded program word fitting that width. |
| C08–C09 | Both word-domain and arbitrary-Int comparison public wrappers return the actual seven-field contract under their stated guards. |
| C10 | Numeric bank8273, controls8, code budget1116895, setup8271, reusable query160257, service160253, and constructionBudget(n)=1100000000*(n+1). |
| C11–C12 | Valid half-open ranges halt with the leftmost scan result packet; invalid ranges halt with packet0 on the same continuous run. |
| C13–C14 | Full fixed-program supplied-store agreement constrains final status, positional transitions, ordered reads and every category; the premise is pinned to both actual step fetches, guarded numeric loads and separate Int key reads. |
| P01 | One producer/body shared by every reservation, descriptor output/read, copy and release receipt; each occurrence is in the actual whole continuous trace and has its actual producing prefix and step equation. |

The provenance client expands occurrence, output-transfer, load, copy and release receipt predicates independently. It checks the reserved output extent kept in register3, actual transfer to register0, all four descriptor loads, copy load/store indices and memory values, and every scalar release index/frame. No retained allocation, final answer, or manufactured observation log is an extra client premise. Lower machine and builder predicates are the existing production interfaces.

## Exact registry verdicts

Every negative below compiled its producer with exit0 and empty streams, then produced exit1 with empty stderr and exactly the listed JSON diagnostic surface(s). Every positive compiled both producer and client with exit0 and empty streams. Each named surface occurs once. Extra JSON diagnostics and non-JSON fatal output reject. The registry stores the exact before/after fragments; `scripts/lifecycle_dependency_README.md` states P, Q and the checked projection/monotonicity bridge where applicable.

| Case | Expected client | Exact surface/class | Producer s | Client s |
| --- | --- | --- | ---: | ---: |
| D01_CONSTRUCTION | reject (exit1) | checkC01_construction/type-mismatch | 13.009 | 8.479 |
| D02_RETAINED | reject (exit1) | checkC02_retained/type-mismatch, checkC11_valid/type-mismatch, checkC12_invalid/type-mismatch | 2.919 | 13.298 |
| D03_SAFETY | reject (exit1) | checkC03_safety/type-mismatch | 3.124 | 13.242 |
| D04_PHYSICAL | reject (exit1) | checkC04_physical/type-mismatch | 2.755 | 13.555 |
| D05_EXECUTABLE | reject (exit1) | checkC05_executable/type-mismatch | 5.269 | 14.677 |
| D06_REUSABLE | reject (exit1) | checkC06_reusable/type-mismatch | 3.793 | 16.602 |
| D07_UNIFORM | reject (exit1) | checkC07_uniform/type-mismatch | 4.336 | 16.106 |
| D08_DELETE_PHYSICAL | reject (exit1) | checkC04_physical/invalid-field | 3.733 | 17.258 |
| D09_SIBLING_PHYSICAL | reject (exit1) | checkC04_physical/type-mismatch | 4.782 | 14.447 |
| D10_PUBLIC_TRUE | reject (exit1) | publicContract/type-mismatch, checkC08_word/type-mismatch, checkC09_comparison/type-mismatch | 4.114 | 14.570 |
| D11_WORD_TRUE | reject (exit1) | checkC08_word/type-mismatch | 4.242 | 15.628 |
| D12_COMPARISON_TRUE | reject (exit1) | checkC09_comparison/type-mismatch | 3.676 | 15.064 |
| D13_ALIAS_PHYSICAL | reject (exit1) | checkC04_physical/type-mismatch | 4.006 | 13.979 |
| D14_RETAINED_COST | reject (exit1) | checkC02_retained/type-mismatch | 3.888 | 16.209 |
| D15_CODE_FETCH_DROP | reject (exit1) | checkC04_physical/type-mismatch | 3.713 | 15.991 |
| D16_PREFIX_RESOURCES | reject (exit1) | checkC03_safety/type-mismatch | 4.544 | 14.402 |
| D17_READY_BANK | reject (exit1) | checkC05_executable/type-mismatch | 4.050 | 15.118 |
| D18_STORE_TRUE | reject (exit1) | checkC13_store/type-mismatch | 4.405 | 15.670 |
| D19_ACCEPT_COMMENT | accept (exit0) | clean acceptance | 3.024 | 13.100 |
| D20_ACCEPT_IDENTITY | accept (exit0) | clean acceptance | 4.123 | 15.450 |
| P01_OUTPUT | reject (exit1) | checkP01/type-mismatch | 4.193 | 3.634 |
| P02_METADATA | reject (exit1) | checkP01/type-mismatch | 3.960 | 4.126 |
| P03_COPY | reject (exit1) | checkP01/type-mismatch | 4.011 | 4.010 |
| P04_RELEASES | reject (exit1) | checkP01/type-mismatch | 4.519 | 3.845 |
| P05_PUBLIC_TRUE | reject (exit1) | producerContract/type-mismatch | 3.860 | 3.587 |
| P06_ACCEPT_IDENTITY | accept (exit0) | clean acceptance | 4.075 | 5.885 |

## Restoration, selector and diagnostic controls

All 26 cases record both original-byte restoration and private-import restoration. The final summary records `passed=true`, `restored=true` and `shadowRemoved=true`. The removed shadow path was resolved and checked under that invocation’s evidence root before recursive removal. Shared source/artifact bytes, runner, registry, owned-process helper, toolchain file and Lean executable matched the recorded baseline. Unrelated documentation edits are outside this scoped restoration statement; the coordinator owns complete-tree Git and source-manifest certification.

Final self-test receipt: `.lake/lifecycle-dependency/20260921T020841426-626013e0`. It checks missing/duplicate/unknown/reordered registry entries; explicitly empty, whitespace, unknown and duplicate-channel selectors; expected errors mixed with another diagnostic; wrong error class; and each of `error: unrelated compiler failure`, `uncaught exception: unrelated compiler failure`, and `PANIC: unrelated compiler failure` after an otherwise expected diagnostic. The JSON parser rejects all three unlocated forms. A hidden child process is started by the six-second owned timeout fixture and is confirmed absent after the termination barrier.

Startup receipt: `.lake/lifecycle-dependency/20260921T014935648-f11d6525` checked both unchanged producer/client pipelines. The final full run repeats current-source expected accepts D19, D20 and P06. Focused JSON rejection receipt: `.lake/lifecycle-dependency/20260921T015953601-49c6df38` (D01). Corrected alias fixture receipt: `.lake/lifecycle-dependency/20260921T020853560-a2812593` (D13).

The earlier full invocation `.lake/lifecycle-dependency/20260921T020151902-9d5810e8` is **NOT_CERTIFIED**. It passed D01–D12, then rejected D13’s producer because the weakened `True` alias introduced four unused-variable warnings. The fixture was corrected by underscore-prefixing only those now-unused binder names; the classifier was not loosened. Its preserved summary SHA256 is `00c9e784f92b49a63b1db106c8dcb77e5fc80a6366499d6f2c81bf567c948d41`; failure SHA256 is `ddb3b444f2e142bcae9042bc3161ce3cd49d3b4b9b070e70dd5530e23aa19d6c`.

Earlier development also rejected an absent toolchain path caused by .NET resolving the sandbox profile, and an initial destructuring client produced cascading errors. The final implementation uses USERPROFILE with .NET fallback and direct expected-type assignments. Independent read-only review found that the initial text classifier could absorb unlocated fatal text; the final per-line JSON classifier and replayed negative controls close that finding. Those earlier receipts are not final campaign acceptance.

## Source and artifact identity

Registry normalized UTF-8/LF SHA256: `4c9c7a4259808bb64c74656fd52559752e76f02834f2ac8567f5830968a5b80d`. Original file hashes below are raw bytes; shadow sources are deliberately normalized to LF. Git blob identities and newline serialization are not conflated.

| Original path | Raw SHA256 |
| --- | --- |
| `scripts/lifecycle_dependency_replay.ps1` | `a4acecafb1a639dd220ddf29d6586dbd907983f723070a153c6074382f31d9aa` |
| `scripts/lifecycle_dependency_cases.json` | `003343871e23c93df874a960a8af60ae7a8a2e615adb05b6e581dc4407a1c84b` |
| `scripts/owned_process_tree.ps1` | `6690ad4f9e3aee9596e53e89d3d242e4be59c0a04733bc50184ae35b292ff90e` |
| `lean-toolchain` | `ad3e6363c78908c80953282baf57162702f1134173a5247aad3dbfea108a525f` |
| `RMQ/Core/WordRAM/Lifecycle/Capstone.lean` | `ba48ee2d9d0e845df5c642dbe08879da4a19c25ef54abc744c564b331dc68a69` |
| `.lake/build/lib/lean/RMQ/Core/WordRAM/Lifecycle/Capstone.olean` | `6c84889c55148c3f9e894ace714cc786faf96a1229846582085e4539eac63337` |
| `RMQ/Core/WordRAM/Lifecycle/Provenance.lean` | `454ecb3a9615977aa2d5d52015771a187fada6e6f5ce1f90d5a125cd873d273e` |
| `.lake/build/lib/lean/RMQ/Core/WordRAM/Lifecycle/Provenance.olean` | `2d5aec69897a18cfec597263766479bcd6440537d60b441a9220847917086eb4` |
| `RMQ/Validation/LifecycleContract.lean` | `0d3ddd1d4f4851c7c919900d5a6763591eb57d6aa8e3b49a8be8f7e0d04c5c1b` |
| `.lake/build/lib/lean/RMQ/Validation/LifecycleContract.olean` | `841a84ef4082b6d92d6757d265e2f36f239dbca95a7d8e2467c636d085cf61ac` |
| `scripts/lifecycle_provenance_contract.lean` | `d7d291fb45e376ef2be54cca1d1c93a603c69fbd41ade2a702836fc3a687bb4a` |
| `C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0/bin/lean.exe` | `9b5af669d8dc9b5826a1f5427584915eeca659e9bf34c7ee72667b93c0bfdcb0` |

Final summary SHA256: `17d5798eb4a91699c2b938fa9f82e393652c43de9a28654976649c8c5ae29ed7`.
Complete case source/artifact/client hash receipt (`cases.json`) SHA256: `b28bd3e34a8cc5b487951082a8791b8a3aa6bfc24f54c0b90e5f1bf0cb451394`.
Complete stdout/stderr/stage receipt manifest (`manifest.json`) SHA256: `a8c5e47dde423a6434efe710f082618cd25724655765d4c98cfcc7661c5e6ad1`.

`cases.json` records every changed producer source hash, freshly compiled producer artifact hash, unchanged client hash, actual exit and measured durations. `manifest.json` binds every retained full stdout, stderr and process result file by raw SHA256 and byte count. These bulky local outputs are intentionally not staged. The tracked registry and runner reconstruct every mutation and verdict.

## Proof digestion and limits

The work turns the public lifecycle proposition into a checked client dependency: removing a load-bearing guarantee breaks a client that still asks for that guarantee on the same actual objects. The producer has to remain a valid Lean module, so failures cannot be credited merely to broken mutation syntax or an unadjusted constructor. Positive controls establish that the same copied import mechanism accepts the genuine producer.

Live mathematical assumptions remain the production word-input domain (for the word model), represented request endpoints, and an existing halted retained owner for re-entry. The comparison channel keeps arbitrary Int values separately counted. The replay itself is a compiler/dependency test; it does not prove native allocator capacity, external alias freedom or machine performance. The physical leaf’s checked-address routing preserves failed logical attempts without claiming an out-of-extent physical fetch. Canonical initialized states admit the counted plain-word view without a retained runtime initialization bitmap.

A skeptical reader should inspect the independent expected propositions and the actual producer edit for each case, confirm that the fresh `.olean` is the client’s import, and verify that unrelated diagnostics cannot satisfy the expected rejection. The exact source fragments, private artifact binding checks, JSON classifier, positive controls and retained hashes make those checks replayable. Final broad gates, full source-manifest closure and coordinator acceptance belong to the root task.
