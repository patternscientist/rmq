# Current native refresh and recipe repair

Status: the eight delegated production/execution stages completed successfully
on the amended comments and ordinal selector guards. Review then found that the
native-control fingerprint bound only its first pin. That gate is repaired and
cheap controls passed. A new focused discovery under the repaired runner and
root's complete 48-case replay remain required. This document records measured
local results; it does not establish whole-task completion.

The heavy slot was returned after focused discovery ended and its receipt
confirmed mutex release/disposal. No native, compiler or Lean process was
launched by this leaf during the subsequent recipe repair. Native sources,
formal sources and the 48 historical expectation cases were not changed by
this leaf. Root owns the expectation provenance rebind and Rust refresh.

## Producers and retained executions

All paths in the table are under `.lake/lifecycle-native1/`. Commands used the
pinned PowerShell executable with `-NoProfile -File` from the repository root,
following `NATIVE_REFRESH_PLAN.md` in exact order. Both native build phases used
`-LeanReceipt .lake/lifecycle-native1/runs/build-20260927T062313663/RESULT.json`.
That final standard Lean receipt has SHA-256
`c68286c3166128c0794f8ad9f790c37da7687f62d6a873a0dab4d3cd3eee99b1`,
381 source pins, 742 generated pins and 4856 tool pins; its 5979-pin final
integrity check and cleanup passed.

| Stage and actual entry arguments | Retained `RESULT.json` | SHA-256 | Actual outcome |
| --- | --- | --- | --- |
| `scripts/lifecycle_native_build.ps1 -Phase dll` | `runs/build-20260927T063830290/RESULT.json` | `77984ad82686ce42a69e779ee2da5f4c81c1c07fce6947380056e9e2cb8f74eb` | Five producer children exited zero; 190.40 s; 7091 final pins. |
| `scripts/lifecycle_native_build.ps1 -Phase clients` | `runs/build-20260927T064222779/RESULT.json` | `6dd359050473a2604ab6370ef65813ba90ef0f3b4acd3ffaa776a08118caf699` | Eight producer children exited zero; 181.14 s; 7143 final pins. |
| `scripts/lifecycle_native_replay.ps1 -Phase Startup -Variant production` | `replay/20260927T064556967-9557393a/RESULT.json` | `bbbea35884980851f3bbe2b538929c245b7b7f0ef2444a8a05f50aec880c2fe3` | Native exit zero in 5.4340775 s; 7154 final pins. |
| Same replay, `-Phase Fixtures -Cases LN1-W-TIES -Variant production` | `replay/20260927T064716438-5960f47b/RESULT.json` | `11d9b8279c8701a76b8fd6d0763af0c6a73176017f42f99c807500e678ceb7f9` | Both modes exited zero, 7.5021459/7.2972285 s; 7156 final pins. |
| Same replay, `-Phase Fixtures -Variant production`, selector omitted | `replay/20260927T064849543-b1d28b93/RESULT.json` | `02060b1e4615bcb812bafff8794341271257eb447625dcfdcd62b7a319b36493` | All 13 fixtures, 26 exits zero, 142 requests/publications; 7192 final pins. |
| Same replay, `-Phase AbiBoundaries -Variant production` | `replay/20260927T065401229-f97e3be7/RESULT.json` | `166cc9a094bb54e9d08600182e7bf856cc2116d8262f104701015e747ef16f9b` | One exit zero in 2.6355578 s, all 23 internal cases; 7154 final pins. |
| `native_clients.ps1 -Phase Run`, selector omitted | `clients/20260927T065517097-e55bf689/RESULT.json` | `769cd0530d4f69667cd49288963482fbf8678c74dc4ebd1e206c56896b5c3d34` | All ten clients exited zero, full ordered roster; 7292 final pins. |
| `native_controls.ps1 -Mode Discovery -Cases NC-NONE-BUILD` | `native-controls/20260927T065740444-c4346a02/RESULT.json` | `d63456f407be4c113c2d463e068e9efd1343351cb6c3448ba2636d0d111d5ae2` | Native exit zero in 2.7822332 s; 7167 final pins. Healthy projection matches; its recipe fingerprint is superseded below. |

Every execution stage used the fresh clients receipt in row two as its
`-BuildReceipt`. Each used `-CaseDeadlineSeconds 120` and this exact rationale:
“Prior actual native maximum 6.82s; 120s permits cold runtime and host scheduling
margin; exact ordinary exit, complete streams, pins and cleanup remain
required.” Startup and ABI use the same 120-second ceiling internally. Producer
stages retained their existing independent 300-second ceilings. No timeout,
nonzero child exit or native stage failure occurred in this batch. All eight
receipts report successful integrity and cleanup independently.

Full-fixture native durations ranged from 6.8472172 to 8.1477043 seconds, with
191.6559964 seconds summed native time and 280.55 seconds wrapper time. The ten
clients ranged from 0.1209255 to 2.6918382 seconds, summing 18.7110554 seconds;
their wrapper took 112.62 seconds. These measurements update the historical
timing estimates without weakening any per-stage deadline.

Post-run review rehashed all 432 retained raw capture pins across 54 child
captures: 13 producer children and 41 native processes. It also rehashed the 31
actual JSON report pins. Sorting the 432 unique raw pins by exact ordinal path,
serializing `path<TAB>bytes<TAB>sha256` with LF and one final LF, gives SHA-256
`d4a4746b3f9c106bed83c4e4ed7223bb5fe65d97ab5f525b29343042f9ffc43c`.
Per-file identities and actual exit receipts remain in the indexed results;
this aggregate does not replace them.

## Artifact and behavior comparisons

The fresh production DLL is 12421120 bytes, SHA-256
`03c17dd0fbacff8f72e707f40ba737096daf096059ace99ec7a0c9fd69c1772d`.
The fresh testing DLL is 12426240 bytes, SHA-256
`160f2b9e0beb5d25de80d3852608d5f5bb8309a860c3faee6da9c90c92736218`.
Their whole-file hashes differ from the historical DLLs. Bit identity is not
assumed or claimed.

Root independently compared all 365 ordered derivation entries against
`runs/build-20260927T043851446`: original C, transformed C, global lists,
visitor names, signatures and object pins match exactly. All 1095 referenced
current original/derived/object files were rehashed. Only four reuse flags
changed, for ThinRun, Run, Observations and Entry. Both link-map hashes match.
The production DLL has four differing bytes, at offsets 128, 129, 9349124 and
9349125; its PE offset is 120. These are recorded comparisons, not a general
binary-equivalence theorem. The review is
`runs/build-20260927T063830290/ROOT_DERIVATION_REVIEW.json`, SHA-256
`1dd3692db1b3cc710eb52c3e1769f1c4844576eb3937a662c17c3e05c3419bb2`.
This leaf separately found unchanged ABI prototypes and all 365 original,
transformed and global-list entries, and checked all 14 fresh client artifacts.

Fresh startup JSON is 686 bytes, SHA-256
`51c279e2ea53f3013ea37b29ae259d9488cb56ef2d50490b03dda7652af9c6ce`.
Its entire text matches historical startup after replacing exactly two validated
nonzero program-array addresses with boolean liveness. No count, capacity,
signature, graph or memory property is omitted. That projected text has SHA-256
`b314026e0986b2f7f3f74a2a8263aadc87475ff30919be91081d3a2eb6ce70ab`.
The program and fixed-global inventories overlap and are not added together.

The ABI JSON is byte-identical to its historical report: 2352 bytes, SHA-256
`84b8cb2b305780f758ab77228fc78530256bce043b64b7b504a5c3f2b5d8ed7c`.
An independent read-only reviewer used Python exact integers, strict UTF-8 and
raw hashes to compare all 26 fixture reports, all ABI data and all ten client
streams/mappings. Non-pointer fixture data match exactly, while live-bank
distinctness, independent answer packets and ordered observation reads were
checked separately. That review rechecked 413 pins and is retained at
`native-refresh-review/secondary-20260927/NATIVE_SEMANTIC_REVIEW.json`, SHA-256
`6eafcedf3878f591daf7a4dad73fa5a798f22b4e386942bc69da9b2c96ac8eba`.

The focused healthy control's complete historical projection also matches
exactly: projection SHA-256
`0f0d43c6f5f6942b11b1a2489dc48a2913af3e330a1bb02cfc4aeaa355f0a0c7`.
Its actual JSON is 6630 bytes, SHA-256
`f800072f3b31e028db5fb120c1ee1ada820529c794d854d9c23cf114cda729e8`.
Its candidate file remains discovery-only. These comparisons do not assign a
new verdict to another case or change the historical 48-case oracle.

## Fingerprint defect and repaired boundary

The fresh focused discovery unexpectedly retained historical fingerprint
`4fddb88fdf3b1b8b6d3217a29fc78ff79bcc56bd27e73d39e3c9965d56785047`.
Read-only reconstruction by this leaf and root confirmed why: the expression
`$pins | Sort-Object path -Unique` received ordered dictionaries. Its named
sort-property lookup treated their path entries as missing, so unique sorting
kept only the first pin. Hashing only the old runner's path, 28829-byte length
and SHA-256 `3c80436cd3796c45a2e1a35782431b36118548bd5255edadaeb3228801327480`
reproduces the historical fingerprint exactly.

This was a defect in the cross-recipe expectation gate. Individual source,
tool, artifact, staged-copy and raw-capture checks still ran, including the
independent finally checks, and their retained measurements remain evidence.
The old fingerprint cannot establish that every expected recipe input was
bound. Earlier documentation describing it as a complete recipe is corrected
by this finding; no historical expectation gate is silently reclassified.

The repaired production `Get-ControlRecipe` uses an explicit
`Dictionary[string,object]` with `StringComparer.Ordinal`. It validates pin
shape, rejects an empty roster and conflicting duplicate path/length/hash
entries, preserves exact duplicates as one row, and sorts the complete key
array with `Array.Sort` and `StringComparer.Ordinal`. Exact supplied absolute
path spelling is the recorded identity. Case-distinct and format-distinct path
records remain distinct; this makes no claim about Windows filesystem aliases.
Byte lengths use invariant decimal text, hashes retain their exact spelling,
and complete rows use strict UTF-8 without BOM and one final LF.

The next native-control result must retain `inputRecipe` with its schema,
source/unique/duplicate pin counts, every ordered unique pin, exact recipe text
and SHA-256. `inputFingerprint` is that SHA-256. Root will independently rebuild
this record from the next actual focused discovery before rebinding expectations.
The repaired runner SHA-256 is
`6f3d2138160618e33333a3368cf6f3d38a709f71ab5b847957fdfe3238495e00`.
Its diagnostic projection, challenge predicates, 48-case mapping and native
dispatch remain unchanged.

## Replayable recipe and selector controls

Run `native_recipe_controls.ps1` for the complete ordered eleven-case pure
recipe suite. It extracts the actual production function from the pinned runner
AST and calls it in one retained, bounded PowerShell child. Synthetic pin paths
are metadata; no source file is replaced and no native/compiler process or
heavy mutex is acquired. Expected rows use independently written literal
ordering. The complete ID/input-pin/expected-row/relation/error mapping is
serialized in a fixed property order and hash-guarded before any case executes:
7879 bytes, SHA-256
`0e1b70dffe3931ac57951e30003698818bb134d924c446abb0955b340862f8f3`.
The outer runner separately checks all eleven result IDs and the mapping hash.

| Case group | Required observation |
| --- | --- |
| Complete three-pin baseline | Exact three unique rows and independent hash; no first-pin-only success. |
| Non-first hash, length and path changes | Each changes the fingerprint and matches its independent full rows. |
| Reordered inputs and exact duplicate | Same fingerprint, with exact source/unique/duplicate counts. |
| Duplicate path with conflicting hash or length | Exact `conflicting recipe pin` rejection. |
| Case-distinct and soft-hyphen-distinct path records | Four distinct ordinal keys and exact independent row order. |
| Empty roster | Exact empty-roster rejection. |

The final eleven-case run passed at
`native-recipe-controls/20260927T071017981-3341822f/RESULT.json`, SHA-256
`30d1507bdd17163174946f06221965c1141918469894e815f5648e4ee100abfe`.
Eight expected accepts and three exact rejects passed, with actual child exit
zero, exact eleven-line stdout, empty stderr, 18 final pins and cleanup success.
The retained case result has SHA-256
`e3f2fb02519c9f3d95a6ddf3fa000e7edbfeed6e56f0cb74607f9932c1622230`.
An earlier development pass without the complete mapping guard is historical
only; the final run supersedes it.

All 18 existing native-control selector cases also passed on the repaired
production runner at
`control-selector-controls/20260927T070655548-bc3d2d0d/RESULT.json`, SHA-256
`5c28fab9f31ac5681e94f6a4f348d3c80ec598e2318192a2d0fd616579b7a9e8`.
Its 87-pin integrity check and disposable restoration passed. The later test
mapping-guard change affected only `native_recipe_controls.ps1`, not the
production runner consumed by those 18 cases.

## Digestion and remaining join

The fresh native programs reproduce the measured behavior after the comment
and selector repairs. Review exposed a real gap: full per-file integrity is
different from hashing the complete recipe used to choose a frozen oracle.
The explicit recipe data structure now distinguishes those obligations, and
retained sensitivity tests challenge non-first inputs and duplicate handling.
The remaining skeptical question is whether the next actual complete recipe
and all 48 fresh projections match the unchanged root-reviewed oracle. That
requires the scheduled focused discovery, independent recipe reconstruction,
provenance rebind and full replay; cheap controls alone do not close it.
