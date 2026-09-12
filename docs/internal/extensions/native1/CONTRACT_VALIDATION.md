Status: CANDIDATE_COMPLETE
Phase: ALL_NINE_CONTROLS_AND_44_CONTRACT_CASES_CHECKED

# Native public-contract replay

This is an operational replay of the frozen public-contract cases. It does not
record global NATIVE-1 acceptance. Governance remains
`0e6a00f654abc64f8b68988fa9675b9a839dca2f`; the proof-sprint completion gate applies.

The lead froze the target before execution:

> FIRST run `-Case baseline` expected-accept under bounded owned process (source/consumer90s per existingregistry), preferablyPS7 matchingregistrycontrols. Report exact producer/consumer times/restoration before full9 decision. The final target is all9controls including omitted44 exactly once: baseline+42fieldTrueweakenings+public-type-collapse, mutatedproducer mustelaborate then untouchedliteralconsumer failatdesignatedline; allsource/registry/sharedolean hashes/Gitdiffrestored.

The registry is `scripts/packed_native_contract_cases.json`, SHA256
`6E0C8E5A73F7DE47D14F7298435E7F72F2AC82A5881AEBF3EFFE0388CBF48E2C`.
Its 44 case IDs, nine control IDs, producer/consumer source pins and exact
expected verdicts remain unchanged.

| ID | Bounded acceptance | Status |
| --- | --- | --- |
| CV-BASE | Unchanged Capstone producer and independently typed Contract consumer both elaborate. | Repaired baseline passed, producer 5.127 seconds and consumer 4.712 seconds. |
| CV-44 | Omitted selection executes baseline, all 42 field weakenings and public-type collapse in exact order, once. | 44/44 passed in 736.532 seconds; the full controls invoked this omitted selection exactly once. |
| CV-9 | All nine selector/registry controls pass; omitted-full contains exactly the 44 case IDs. | 9/9 passed in 816.151 seconds with the exact ordered control roster. |
| CV-BIND | Every mutated producer elaborates into a fresh artifact; the untouched literal consumer imports those exact bytes and fails at the designated proof line. | All 43 negative cases had producer exit 0, a fresh artifact distinct from the shared original, exact before/after binding, and consumer nonzero with one designated type-mismatch match. |
| CV-RESTORE | Capstone/Contract source bytes and Git diffs, registry bytes/diff, and shared Capstone/Contract oleans are restored. | All case restoration flags passed, all three registry mutations restored exact bytes/diffs, and independent final hashes match the frozen originals. |

## Diagnosed expected-accept failure

`commands/contract-baseline-01.json` records exit 1 after 9.601 seconds.
The corresponding detailed receipt is
`binary-commands/contract-replay-20260912T131025801.json`.
Compiler identity passed in 1.884 seconds; the producer failed in 2.137 seconds,
well within its 90-second deadline. The consumer was never attempted. The exact
failure was a missing `Execution.olean` below the fresh partial RMQ overlay.

The pinned Lean 4.22.0 source `Lean/Util/Path.lean`, `SearchPath.findWithExt`,
selects the first directory containing the root package `RMQ`; it does not fall
back separately for a missing module inside that package. Therefore the partial
overlay masked the otherwise available checked dependencies. This was a replay
import-path defect, not an expected contract rejection.

The original runner SHA256 was
`94F2B9F82D685AA636DD3845300C71AB339FE1D8155AA42AD404290EC34ACF9A`.
The failed receipt is retained unchanged, including its empty results list and
legacy `executed: [null]` representation. The repaired runner enumerates actual
result IDs explicitly, so future zero-result receipts contain an empty array.

## Approved repair and boundaries

The lead explicitly approved one complete physical run-local copy of the local
olean dependency tree, fresh producer/consumer output paths per case, and an
exact hash binding from each successfully compiled producer into the private
import tree before compiling the untouched consumer. No links or shared writes
are introduced. The runner records dependency copy counts, bytes, hashes and
timing, plus producer binding hashes before and after the consumer.

The available RMQ subtree measured 396 oleans and 388,438,176 bytes before the
repair. The actual complete local copy includes 410 oleans and 396,755,200 bytes,
including the other local roots. Copying once per run avoids repeating the
entire tree for every field.
The registry, expected diagnostics, Lean production sources and shared helper
remain outside the approved edit scope.

## Calibration and focused binding control

The repaired runner SHA256 is
`AE8BC171667857E693D58E74626D425AB5C7F8AB43BDA4D6996A6FF92C8C3687`.
Its PowerShell parser and scoped whitespace checks pass. The registry hash and
every expected verdict remain unchanged.

`commands/contract-baseline-02.json` records a successful baseline in 31.464
seconds, with detailed receipt
`binary-commands/contract-replay-20260912T132003337.json`. The physical dependency
copy took 12.330 seconds; producer and consumer took 5.127 and 4.712 seconds,
both returning exit 0 without output. Fresh producer, private import before and
after the consumer, and shared original all had SHA256
`1357DB70B2FEF15D74D004639EB89797F92927706C26131A20CAA26126A8EF07`.
Exact source/Git restoration and unchanged shared oleans were checked.

`commands/contract-field-n01-01.json` records the focused weakening control in
30.119 seconds; its detailed receipt is
`binary-commands/contract-replay-20260912T132210348.json`. The producer compiled
in 5.922 seconds and the untouched consumer rejected it in 4.708 seconds:

```text
RMQ/Core/WordRAM/Native/Contract.lean:12:2: error: type mismatch
  nativeExecutionCapstone_holds.wordRoundtrip
has type
  True : Prop
but is expected to have type
  ∀ (width value : Nat), value < 2 ^ width → LimbWord.decode (LimbWord.encode width value) = value : Prop
```

The fresh output and private import before/after the consumer all had SHA256
`614863A86EE55C6F54ED6EC2FE4D01BBDC3813F2D3F29EBD49214292ED4EA59F`,
which differs from the unchanged shared producer. The source, exact Git diffs
and shared artifacts were restored.

On that calibration the lead approved the full nine controls with an owned
2100-second outer deadline, retaining the frozen 1800-second omitted-full child
deadline and 90-second producer/consumer deadlines. Forty-five compiler pairs
at the measured baseline rate estimate about 443 seconds, plus two private-copy
and process/control phases; an 8–10 minute expectation leaves margin for cold
or variable runs. The binary campaign may execute native-only controls in
parallel; its later source/Lean mutation phase is coordinated separately.

An internal read-only mechanism review by `native_policy` independently checked
the repaired runner hash above and pinned Lean's root-package lookup. It found
no concrete gap in complete private imports, fresh producer binding, exact
44-case/nine-control rosters, anchored diagnostic checks or restoration. This
review ran no Lean or mutations and is separate from the full replay evidence.
Its dependency-copy consistency assumption is the agreed exclusive compiler and
frozen dependency ownership, which the lead maintained during this campaign.

The initial full-run timing alert at 14/44 cases measured 248 seconds; a later
24/44 measurement took 427 seconds. Those totals include restoration and process
overhead omitted from a sum of compiler-only times. The lead and binary worker
were notified early to preserve the later exclusive compiler boundary. No
deadline or expected verdict was changed.

## Complete replay and independent extraction

Run the complete controls from the repository root with PowerShell 7:

```powershell
./scripts/packed_native_contract_replay.ps1 -Controls
```

The owned outer receipt is `commands/contract-controls-all-01.json`, exit 0
after 816.151 seconds. The detailed control receipt is
`binary-commands/contract-replay-20260912T132516703.json`; the single omitted
44-case child is `binary-commands/contract-replay-20260912T132610808.json`.
All nine control commands completed without timeout or output-limit failure.

Independent extraction from these receipts confirmed:

- Nine executed control IDs equal the frozen ordered control roster.
- The omitted-full control occurs once; its 44 executed case IDs equal the
  frozen ordered case roster. The baseline producer and consumer both exit 0.
- Every one of the 43 negative producers exits 0. Every untouched consumer
  exits nonzero with exactly one match at its designated proof line; every
  fresh producer differs from the shared original and matches the private
  import before and after consumer compilation.
- All 44 cases report exact starting-diff restoration, unchanged shared
  Capstone/Contract oleans, and equal original/restored Capstone source hashes.
- All 410 physical dependency copies have equal source/private hashes. The
  complete child's copy phase took 11.893 seconds.
- All three registry mutations restore the original registry hash and exact
  starting diff. Independent final source, registry and shared-object hashes
  match their frozen values.

The complete child records 89 commands: compiler identity plus 44 producer/
consumer pairs. Producer durations were 4.160–17.092 seconds; consumer durations
were 3.667–15.971 seconds. The 90-second compiler, 1800-second omitted-child and
2100-second outer deadlines were unchanged. Restoration compares each affected
path with its captured starting diff, preserving pre-existing edits.

For proposition-level digestion,
`binary-commands/contract-inventory-20260912T132610808.json` joins all 44 observed
cases with the frozen registry. Its 43 negative rows quote the literal consumer
statements, actual full diagnostics, source lines, fresh/private/shared hashes
and restoration evidence. Thus each row exposes the complete chain:

```text
frozen producer source → specified proposition/initializer weakening
→ successful fresh producer olean → exact private-import byte binding
→ untouched literal consumer statement → designated type mismatch
→ exact source/Git/shared-object restoration
```

The inventory uses SHA256
`F96D0EC22C7331BF5EEA3F66182529B6E54CDDF9AAA177BBA5BD4B13FE13FCBB`.
It is a digest of existing frozen expectations and observed receipts, not an
additional test oracle. The earlier failed partial-overlay receipt remains
unchanged alongside the successful baseline, focused probe and full replay.

Final shared/source pins are:

| Artifact | SHA256 |
| --- | --- |
| `Capstone.lean` | `E2B2FB55223A271B3383AACB70361D85126ABEB3C252ACB0E314467729C6FA0D` |
| `Contract.lean` | `A8DB1EAAC6445F2F8490A6C344A3F573FD169D3FD7B82E6637C4947159E306AE` |
| shared `Capstone.olean` | `1357DB70B2FEF15D74D004639EB89797F92927706C26131A20CAA26126A8EF07` |
| shared `Contract.olean` | `7E086A90427D71517C0080AC616FBE4C6A9B8C7321A1209AEFA49C0F72682A5F` |

Proposed design-decision prose: public-contract mutation tests require a
successfully elaborated weakened producer and an independently stated literal
consumer. Lean's root-package lookup requires a complete private import tree
when replacing one artifact; a partial overlay can fail before testing the
contract. Keep fresh per-case outputs, explicitly bind their bytes into that
private tree, and preserve the original shared artifacts and starting diffs.
This makes stale imports and unrelated compilation errors visible rather than
counting them as contract-dependency evidence.

Proof digestion: these controls test whether weakening a public promise is
detected by a separately stated expected type. A successful mutated producer is
essential: a missing import or syntax error cannot count as that evidence.
All 42 individual promises and the public theorem itself were detected in one
complete replay, with exact artifact binding and restoration. Compiler/runtime
behavior, file-copy/hash behavior and prior source-to-cache correspondence remain
live external/build assumptions. A skeptical reviewer can now reconstruct each
literal promise and its failing consumer from the joined inventory. Scope remains
the specified weakenings and frozen build state; broader native acceptance stays
with the lead.
