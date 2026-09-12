Status: CANDIDATE_COMPLETE
Phase: BOUNDED_VALIDATOR_INVENTORY_AND_DURABLE_REPLAY_CHECKED

# Native source validator and trust inventory

This is bounded producer evidence for NATIVE-1. Full native acceptance, broad
integration, production mutations and the final independent audit belong to the
lead. Governance remains `0e6a00f654abc64f8b68988fa9675b9a839dca2f`; the canonical
proof-sprint skill, completion gate and original 31-row freeze remain in force.

## Requirements frozen before the replay implementation

The lead's original bounded target was:

> Validator must import Contract and execute ACTUAL nativeLoadEntry/nativeQueryEntry/nativeCore on binary bytes, not predecessor-only checks. Provide a small nonempty exact versioned defaultcase roster with independent literal expected status/count/ordered reads for load+query success,176bitendpoint order, checked arithmeticfault, missingmemory/fetch, invalidendpoint, malformedpadding/length, repeatedloadedimage andreads=falseprojection. Pin required IDs separately; omitted runsall; valid one; boundempty/whitespace/malformed/unknown rejects, zero-case fail. Also useful a strict `compare IMAGE LEFT_HEX RIGHT_HEX FUEL READS EXPECTED_FILE` mode with bounded inputs so full native fixture cases can exercise the Lean source layer against frozen independent expectation files; coordinate CLI withregistry_repair. AxiomChecks imports all owned Checks and Contract and prints nativeExecutionCapstone_holds plus every42typedconsumer and keypublicentrytheorems. No native_decide/extraaxioms.

The lead added this replay requirement before its implementation:

> While registry owns source mutation window, please make your validator selector/compare controls durable and replayable: new owned scripts/packed_native_validator_controls.ps1 plus versioned cases JSON, with exact nonempty roster, pinned expected verdicts/diagnostics and actual child argument/env boundaries. Include committed/generated-from-literal smoke image+golden/wrong golden bytes (not scratch-only dependencies), owned deadlines/exits/stderr, no empty CLI binding failure counted as validator rejection.

| ID | Exact bounded acceptance and composition | Evidence/status |
| --- | --- | --- |
| VN-ENTRY | `Fixture.input : ByteArray` → actual `nativeLoadEntry` → the returned `StorageImage` → actual `nativeQueryEntry` and `nativeCore`. | All 16 default cases executed successfully. |
| VN-ORACLE | Expected status, all six category counts and every ordered receipt are independent literals; no native result manufactures an expectation. | Literal microprogram observations, including duplicate address 0 and a 176-bit subtraction, match. |
| VN-REGISTRY | Nonempty `requiredIDs` equals the actual ordered default roster; selected IDs equal the IDs accumulated after successful executions; invalid/empty/duplicate channels fail before cases execute. | 16/16 default cases and all durable selector controls passed, including the real empty argument and `id:` environment boundary. |
| VN-COMPARE | Strict binary-file/hex/fuel/0-or-1 arguments → same load/query entry → exact UTF-8 expected-file bytes, preserving LF and final empty lines. | Independent 35-byte positive/wrong-answer and all argument/resource/UTF-8/newline controls passed in the complete replay. |
| VN-QUIET | Real `nativeCore ... false` has empty reads and the same registers, PC, status, steps and counts as its logging invocation. | Default case with three actual loads checked. |
| VN-REPEAT | One successful binary load is reused for queries with endpoints 7, 19 and 7; each expected answer and count is literal. | Default repeated-image case checked. |
| VN-DURABLE | Versioned 24-control JSON has an independent ordered roster and a complete byte hash; replay owns real child processes, compares exact exit/stdout/stderr, and records actual completed IDs plus unchanged sources/fixtures. | Frozen v1 passed 24/24 in 257.464 seconds. Independent extraction confirms all ordered IDs, exact verdicts, unchanged pins and oversized-fixture cleanup. |
| VN-AXIOMS | Import every limb/machine/code/binary/cursor consumer, then print the public capstone, all 42 independently typed consumers and principal source/refinement producers. | All 86 stock inventories checked; exactly the three standard Lean axioms occur. |

The script and registry paths are
`scripts/packed_native_validator_controls.ps1` and
`scripts/packed_native_validator_controls.cases.json`. Computational production
sources, the build and identity scripts, and shared ledgers are outside this
worker's edit scope.

The complete cases JSON is pinned by SHA256
`60D07EC27D7854FEB107CE8A1148F382F17F882CD8F2F18427FBD8BDE8D755EC`.
The replay can be run from the repository root after the checked import closure
is available, using PowerShell 7 on the supported Windows host. The full roster
was checked on 7.6.5; only the focused malformed-fuel diagnostic was checked on
Windows PowerShell 5.1. Native argument preservation is part of the full roster:

```powershell
./scripts/packed_native_validator_controls.ps1
./scripts/packed_native_validator_controls.ps1 -Case compare-golden
```

There is no implicit Lake build or missing-artifact fallback. The runner records
the validator, runner, registry, process helper and compiler bytes, plus 20
explicit Native source/olean pairs. Full transitive baseline validation and
establishing that cached imports were built from their sources remain the prior
proof/build validation obligation. It checks the actual pinned Lean version
through an owned child process. Each source-validation child has a 60-second
deadline. Literal
fixtures are regenerated for each replay in a unique workspace directory. The
one oversized temporary is hash-checked and removed afterward; all small fixture
bytes and the complete JSON process report remain available.

## Interface and independent fixtures

`RMQ/Validation/PackedNative.lean` imports `Native.Contract`. Its default registry
is `native1-lean-validator-v1`, with 16 independently pinned IDs. The CLI accepts
no arguments for the whole roster, `--case ID` for one case, or:

```text
compare IMAGE LEFT_HEX RIGHT_HEX FUEL 0|1 EXPECTED_FILE
```

Hex encodes little-endian bytes, with exactly twice the loaded limb count in
characters and at most 1024 bytes. Fuel is strict decimal, at most seven digits
and 1,000,000. Image and expectation inputs must be regular files, at most
134,217,728 bytes; bounded 65536-byte reads also catch growth after the initial
metadata check. The expected file must be UTF-8. No whitespace or newline
normalization occurs. Compare success prints one `NATIVE1-LEAN COMPARE PASS`
line; failure returns exit 1 with the exact `NATIVE1-LEAN ERROR` diagnostic on
stderr. The optional `NATIVE1_LEAN_SELECTOR=id:ID` channel preserves explicitly
empty/whitespace selections across process launchers.

The durable JSON carries a literal 35-byte image: width 8, input length 5,
three registers, instruction `halt 1`, and memory `[41]`. Endpoints `07` and
`09` yield literal expected bytes `halted 9\n1\n0 0 0 0 0 1\n\n`.
The wrong expectation changes only packet 9 to 8. Other controlled variants
change LF to CRLF, contain invalid UTF-8, truncate one image byte, or exceed the
file cap. These fixtures are generated from the committed literals, not from
the loader, query result or scratch files from an earlier run.

## Checks and diagnosed failures

All commands use the pinned Lean 4.22.0 compiler with `-j 1`, explicit affected
modules and owned deadlines. Command receipts are under `commands/`.

- `validator-01`: ordinary proof failure in 5.326 seconds. The termination
  argument needed the nonempty-chunk proof in the explicit `else` branch.
- `validator-02`: producer checked with C and olean output, 10.122 seconds.
- `validator-default-01`: actual executable source checks passed 16/16 in
  6.710 seconds, including every duplicate receipt and six-category vector.
- `validator-selected-01`, `validator-whitespace-01`,
  `validator-malformed-01`, `validator-unknown-01`: actual selected/rejected
  process boundaries checked with exact diagnostics.
- The first direct empty attempt stopped in `packed_native_command.ps1`'s
  mandatory argument-array binder. It did not run Lean and is not acceptance
  evidence. `validator-empty-channel-01` reached the validator and rejected
  `id:` with its exact empty-selector diagnostic in 7.198 seconds.
- `validator-compare-positive-01`: independent literal image/expectation
  accepted in 13.400 seconds. `validator-compare-wrong-01`: wrong packet
  rejected at `comparison observation mismatch` in 6.201 seconds.
- `validator-durable-positive-01`: the exact positive control failed in
  29.850 seconds because PowerShell's .NET string conversion turned a null
  environment value into a bound-empty selector. The actual Lean child
  correctly returned `selector is incompatible with compare mode`; the replay
  recorded zero completed cases and preserved the failure. The runner now
  removes the environment key through the environment provider, verifies its
  absence, and restores the original absent-or-present state afterward.
  `validator-durable-positive-02` then passed 1/1 in 24.621 seconds, with exact
  stdout and no stderr. This repair changed only the replay runner.
- `validator-durable-all-01`: stopped after 17/24 exact verdicts in 383.066
  seconds. The `compare-fuel-format` child timed out at 60.297 seconds, with
  zero stdout/stderr and exit -1, which is explicitly not the expected
  validator rejection. Its owned job terminated PIDs 34016 and 11308; both
  were confirmed absent. Every source/import/fixture hash stayed unchanged.
  Completed child runtimes were 11.239–22.945 seconds. Static inspection shows
  that literal fuel `1x` fails `parseFuel` before file loading or query execution;
  no deterministic source fault or timeout cause has yet been established.
  The full failed report is
  `commands/validator-controls-20260912T121837285.json`. A focused diagnosis
  was required before the next complete replay; no successful full24 result
  is claimed from this attempt.
- `validator-fuel-format-ps5-01`: the same literal malformed-fuel control
  passed under explicitly selected Windows PowerShell 5.1.26100.9444. Its
  actual Lean child returned exit 1, no stdout, and exactly
  `NATIVE1-LEAN ERROR malformed or oversized fuel` in 15.543 seconds against
  the unchanged 60-second deadline; the complete wrapper took 32.248 seconds.
  The receipt is `commands/validator-controls-20260912T125248495.json`.
  Source/import/fixture bytes stayed unchanged. The only validator source
  difference since the earlier timeout was a doc-comment correction about
  summing the first two loaded values. A post-completion snapshot showed other
  Lean processes; their ownership was referred to the lead, and no process was
  terminated by this worker. Neither this one-control pass nor the host change
  establishes the original timeout's cause or a full24 pass.
- `validator-fuel-format-ps7-01`: the same focused control then passed on
  PowerShell 7.6.5, the full replay's host. The child took 12.527 seconds,
  returned exit 1, no stdout and the same exact malformed-fuel diagnostic;
  its deadline remained 60 seconds. All source/import/fixture hashes matched.
  The complete wrapper took 26.963 seconds; its report is
  `commands/validator-controls-20260912T125634462.json`. The lead resolved the
  post-run process-ownership question before this check. Two focused expected
  verdicts, including one on the original host, closed the narrow failing
  control and justified a final full replay; they do not prove why the first
  full attempt timed out. No computational source or verdict was changed.
- `validator-durable-all-02`: final full replay passed 24/24 in 257.464
  seconds on PowerShell 7.6.5, with an owned 600-second outer deadline and
  unchanged 60-second child deadlines. The complete report is
  `commands/validator-controls-20260912T130117776.json`. Independent extraction
  confirms the exact 24 ordered registry IDs, zero exit/stdout/stderr mismatches,
  no timeout or output-limit event, unchanged source/import/fixture pins and
  removal of the oversized temporary. Child durations were 7.188–14.922 seconds;
  malformed fuel completed with its expected rejection in 9.041 seconds.
  The real empty-argument receipt records `--case` followed by an empty string,
  and both empty-selector controls reached Lean's exact rejection diagnostic.
- Four unchanged leaf Checks modules were materialized as oleans for the final
  import. The first Limbs attempt reached the proof end but lacked its output
  directory; after directory creation the check passed. No theorem changed.
- `native-axioms-01`: timed out at its initial 45-second budget, with no olean
  and no claimed inventory pass. The owned Windows job terminated PIDs 27112
  and 25144; both were subsequently absent.
- `native-axiom-probe-01`: timestamp helpers had an IO/BaseIO annotation error.
  `native-axiom-probe-02` repaired the annotations and passed in 6.990 seconds.
  Before/after monotonic readings 85117790 and 85120589 measure 2.799 seconds
  around the public capstone traversal. Its only axioms are `propext`,
  `Classical.choice` and `Quot.sound`.

The stock inspector starts a fresh dependency traversal for each name. Eighty-six
copies of the largest measured traversal estimate 241 seconds, plus roughly four
seconds of import overhead; many leaf roots are smaller. The lead approved one
300-second final inventory run on that evidence. `native-axioms-02` passed in
141.177 seconds with olean output. An independent scan of its complete receipt
found exactly 86 named inventories, including all 42 `ContractChecks.checkN*`
consumers, and the union of printed axioms was exactly `propext`,
`Classical.choice`, `Quot.sound`. No custom collector, enlarged proof heartbeat,
extra axiom or native decision shortcut was introduced.

The final inventory source differs from that successful run only by removal of
an extra blank line at EOF. The lead explicitly declined a redundant stock
traversal for that whitespace change; all 86 names and every declaration remain
identical. The final source pins are:

| File | Bytes | SHA256 |
| --- | ---: | --- |
| `RMQ/Validation/PackedNative.lean` | 13565 | `437808A44FA6AAA92422B544B2036AD2F6CDFAD79297DF8BF94BFB402E081EF7` |
| `RMQ/Core/WordRAM/Native/AxiomChecks.lean` | 4353 | `013D4C738E37228F323ECDD606CED8AB0B5D7E5D515225A3CFE6A8D1A2AAF379` |
| `scripts/packed_native_validator_controls.ps1` | 13716 | `719546F3020562C86DE8169CAA17FB1AB0580255E7E9FAEC4DA3BC70D62BAF9F` |
| `scripts/packed_native_validator_controls.cases.json` | 9532 | `60D07EC27D7854FEB107CE8A1148F382F17F882CD8F2F18427FBD8BDE8D755EC` |

The scoped trust-token scans find no forbidden declaration or native-decision
shortcut in either new Lean file. `git diff --check`, independent trailing-space
and EOF checks for all five owned files, and PowerShell parser validation pass.

## Proof digestion and design rationale

The new validator reaches the actual loaded-byte implementation while the
independently stated Contract types remain in its import closure. Default
expectations are small enough to inspect directly: three loads read 23, 7, 23;
the first two loaded values sum to 30; the asymmetric wide subtraction result
detects swapped endpoint initialization. Fault, missing-fetch and malformed
binary cases are distinguished by exact status, charge and diagnostic output.

The checker does not establish verified compilation or foreign ownership.
Compiler, BigNat, array, filesystem and FFI behavior remain the existing external
boundary; physical constant-time arithmetic and native memory succinctness are
unclaimed. Source execution controls complement the independent Rust/C/C++
campaign rather than replacing it. The trust inventory and the exact-type
consumers have distinct jobs: listing axioms alone does not protect a public
proposition against weakening.

Proposed design-decision prose: use independently pinned literal observations
and exact process-channel verdicts for the source validator. Pin complete replay
case bytes to prevent semantic-field downgrades; derive executed counts only
after successful child runs. Preserve binary expectations exactly, including
final blank lines, and regenerate all small fixtures from committed literals.
Reject a wrapper argument-binding failure as evidence of validator rejection.
The bounded source validator, full durable replay and 86-name stock inventory
are now checked. A skeptical reviewer should next reconstruct the delivered
native artifact's source correspondence, foreign ownership and independent
fixture/mutation controls. Those broader NATIVE-1 obligations remain with the
lead and are not closed by this leaf's candidate status. The initial timeout
remains an unsuccessful, preserved observation with an unproven cause.
