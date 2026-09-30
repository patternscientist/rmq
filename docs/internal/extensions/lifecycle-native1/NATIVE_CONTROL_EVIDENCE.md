# Native ownership control campaign

Status: the corrected-recipe complete 48-case Replay passes. The earlier
measurements below are historical, independently reviewed oracle data. A fresh focused
control exposed a recipe fingerprint defect: ordered-dictionary deduplication
hashed only the runner pin. Individual before/finally file checks still ran.
The local recipe repair, eleven sensitivity controls, eighteen caller controls
and corrected focused discovery pass. The final section records the fresh
complete Replay; historical sections preserve their original measurement basis.
The historical nested discovery also passed, as recorded below. The exact
N1-19 through N1-22 requirements remain in `CONTRACT_REQUIREMENTS.json` (SHA-256
`736ff55b84516d1b0c7e45f5dbf8193df98846ea259f0ef5b3caefbe7cd6bc5f`) and the frozen
55-row matrix. No requirement, native source, Lean source, protected helper or
root replay script was changed by this leaf.

The downstream consumer is `native_controls.ps1`: its fixed ordered mapping
directly executes the same pinned C client's `control_discover`, which calls the actual
`packed_lifecycle_build_first` or consuming `packed_lifecycle_query`. The C
client applies its same `strict_info` function to both its healthy baseline and
any owner returned by the challenged call. Discovery exit zero means only that
measurements were obtained. It does not mean that a mutation was rejected.

| Requirement | Concrete check and anti-vacuity challenge | Current evidence |
| --- | --- | --- |
| N1-19 | Preserve full actual status, packet, ordered memory, source/replacement capacities, copied values' first mismatch, historical retained roots and post-cleanup resource balances. Root-reviewed replay checks the C client's live strict predicate and a challenge-specific state/resource predicate. Shared scalar acceptance additionally requires an actual retained boxed scalar. | All 48 measured reports reviewed: 4 accept, 1 nondistinguishing, 43 intended failures across four failure classes. Root owns expectation freezing and final Replay. |
| N1-20 | Each native OBSERVED line is an exact strict UTF-8 stream with empty stderr and actual ordinary exit zero. Full raw captures persist. Replay compares all report data other than absolute addresses, preserving address liveness and source/replacement identity relations. Full source/tool/artifact and staged-copy integrity checks and cleanup execute independently in finally. | All 48 actual streams/exits and independently recomputed report projections agree. Independent review rechecked 486 distinct report/capture/case/staged-file pins. The campaign finalizer checked 7637 pins and restored process resources. |
| N1-21 | Independent complete 48-entry ID/control/phase/argument/surface mapping with SHA-256 `ea90bd61fb7d226210aa47b3afd38cbca8953debaf3246c238a5785b20e69f2d`. Bound selectors validate before receipt reading, output creation or semantic child execution. Disposable real caller controls mutate missing/duplicate/reordered middle rows, handlers, discovery verdicts, arguments and phases. | All 18 current caller controls passed with 87 unchanged pins and disposable removal. The current direct focused invocation ran exactly `NC-NONE-BUILD`; complete discovery ran all 48 in order. |
| N1-22 | One campaign runner owns the existing heavy mutex. Each native process uses the protected owned-process/capture facility and its positive evidence-based deadline. The exact testing client, DLL and runtime are staged adjacently once, with checked build membership and PE closure. PATH, inherited noninteractive error mode and mutex resources are restored independently. | No native/compiler stage launched by this leaf. Existing independent descendant controls remain root-owned evidence. |

The registry covers all 21 C control names. It uses both build and query where
the actual injection is meaningful. `retain-input` and `retain-keys` only inject
in build; `fail-after-take` only injects in query. Malformed sign, negative zero,
Word InputFits, model fault and bounded fuel are build-only under the existing
client. The query endpoint and allocation cases test preservation before
transfer. Value and offset mutations each use indices 0 and 1 in both phases.
Partial copy uses 0, 1, 8272, 8273 and 8274 copied entries in each phase, covering
the first entry, the last register entry, and the first memory entries. The
register bank has 8273 entries; discovery must still show that each chosen
cutpoint actually fired. Fuel controls use 0, 20 and 100 without a hidden healthy
baseline.

The fixed input is `[3,-1,-1,7]`, with `[0,4)` returning one-based packet 2 from
independent leftmost-minimum semantics. A successful control must preserve that
packet and the baseline canonical memory as well as the healthy publication
predicate. The wrapper does not assume that a wrong offset necessarily changes
a value, that skipped repacking necessarily changes capacity, or that this
small input necessarily contains a retained boxed scalar. Root review must
classify nondistinguishing cases explicitly. Such a result does not become an
end-to-end failure claim or prove the missing challenge. A correct reference
oracle is not guaranteed to change answers; compiled route dependence remains
separate root-owned evidence.

`noRetainedOperationalRoots` is the native inspection's ready-shape predicate;
`cleanupComplete` records cleared local transfer pointers. Neither field by
itself is a complete heap-root proof. Handles created/live/released count the
current operation's generation, so a preserved owner after pre-transfer failure
can coexist with zero current-generation live handles. Replay therefore checks
the actual same-owner relation, live strict predicate and ordered memory for
that failure class. Full compiled-root evidence remains a separate obligation.

Receipt timing matters. `begin_operation` starts a new generation and resets
the receipt. `packed_lifecycle_test_configure` also resets it, followed by a
second reset when the challenged build/query begins. A pre-take failure leaves
the previous generation's owner live; its later release is excluded from the
current operation's native-handle and copied-entry balances. Those zero balances
therefore cannot establish either preservation or destruction of the old owner.
The pre-take oracle needs nonzero returned owner, same owner identity, unchanged
ordered memory, the live strict predicate, and absent new answer/observation.

`beforeCleanup` is the client's label for its receipt before freeing returned
handles. The native transfer's own `cleanup_transfer` has already run. The client
then inspects and snapshots the returned memory, allocating and releasing a
temporary result handle for each present memory cell, before freeing the answer,
observation and owner and taking `afterCleanup`. For example, the historical
healthy build has 3 created/0 released/3 live handles before that diagnostic
snapshot and 181 created/181 released/0 live afterwards: 178 memory-cell result
handles account for the difference. Counts need not stay constant between the
two receipts. Current-generation created/released balance is meaningful at the
final receipt, alongside the actual output and state predicates.

Likewise, `temporaryArraysLive=0` means that the temporary transfer owns no
replacement arrays. At successful publication, its four arrays belong to the
returned owner and remain live until that owner is freed. `owner_free` then adds
the published array and copied-entry release counts if its generation matches.
Partial-copy failures release only initialized entries and every actually
created temporary array before returning. The 0/1/8272/8273/8274 cutpoints must
be read with both initialized/released-entry equality and array-created/released
equality; the empty tail banks need not have been reached at these cutpoints.
These counters are not an inventory of all runtime allocations or old source
array reclamation.

The retained-root counters and source/replacement addresses preserve observations
from publication, including after cleanup. A positive historical retained-root
counter in `afterCleanup` is not itself a live leak. Conversely, cleared local
pointers do not independently prove the complete process heap is free of aliases.
`ownerExclusive`, `arraysExact`, `valuesEqual` and `strictPublication` start at
zero; for failures that never reach publication, those zeros mean the predicate
was not evaluated, rather than four separately witnessed predicate failures.
Publication-rejection claims need their intended injection and actual predicate
evidence. The fixed wrong-copy controls change only memory bank 1, so their
recorded mismatch bank/index identifies that injected discrepancy.

All registry controls call the observed API. History retention therefore has an
actual diagnostic root to challenge. `fail-before-publish` runs after strict
publication has succeeded and answer/observation handles have been allocated;
it must be reported as a consuming cleanup failure, not rejection by a false
strict predicate. `model-fault` injects the modeled fault status into the actual
initial owner and uses bounded fuel; it is not a spontaneous production fault.
Malformed endpoints/signs and Word InputFits controls use the ordinary admission
path with testing mode reset to NONE. The allocator control injects failure of
the native owner-handle allocation only; it does not exercise recovery from
arbitrary Lean-runtime allocation failure.

## Invocation and freeze procedure

Use the repository's PowerShell 7 executable and a fresh successful native client
build receipt. `Plan` creates no output directory and reads no build receipt:

```powershell
& docs/internal/extensions/lifecycle-native1/native_controls.ps1 -Mode Plan
& docs/internal/extensions/lifecycle-native1/native_controls.ps1 -Mode Plan -Cases NC-NONE-QUERY
```

After the root's fresh DLL startup and one exact healthy selector pass, dispatch
measured discovery through the same entry point:

```powershell
& docs/internal/extensions/lifecycle-native1/native_controls.ps1 -Mode Discovery `
  -Cases NC-NONE-BUILD -BuildReceipt <successful-client-RESULT.json> `
  -CaseDeadlineSeconds <positive-measured-ceiling> -DeadlineRationale <evidence>
```

Omitting `Cases` selects all 48 in the frozen order. Every selected case has a
fresh C process and an internal baseline when applicable. Source/tool/artifact
verification and staging occur once before the campaign and full pin integrity
verification runs again in finally. Each C process has its independently owned
native deadline. Actual timing should guide any adjustment. A quiet process is not
restarted. Failure preserves `RESULT.json`, stage captures and any partial
`EXPECTATIONS.candidate.json`.

The retained directory contains one adjacent `native` staging directory and
per-case `actual.json`, raw `capture` files and `CONTROL.json`. A case receipt
records the actual native capture and input fingerprint. Its success still
depends on the enclosing `RESULT.json` integrity and cleanup verdict; a case
receipt alone cannot certify the campaign.

Discovery writes `UNREVIEWED_DISCOVERY` entries, with no assigned verdict or
oracle explanation. The root reviews the complete actual evidence and writes a
full 48-case expectations document with status `FROZEN_ROOT_REVIEWED`, preserving
the exact mapping hash and input fingerprint. Each entry has its complete
projection, a measured verdict and a nonempty explanation naming the exact
state/resource oracle. Allowed verdicts are restricted by challenge surface.
The root passes that file and its exact SHA-256 to final replay:

```powershell
& docs/internal/extensions/lifecycle-native1/native_controls.ps1 -Mode Replay `
  -BuildReceipt <same-current-client-RESULT.json> `
  -ExpectationsPath <reviewed-expectations.json> -ExpectationsSHA256 <exact-sha256> `
  -CaseDeadlineSeconds <positive-measured-ceiling> -DeadlineRationale <evidence>
```

Replay refuses missing, partial, reordered or unreviewed expectations before
creating output or launching a child. Source, tool, artifact, runner or registry
changes invalidate the input fingerprint. Raw pointer values are process
specific and therefore project to presence; source/replacement identity
relations and the client's same-owner relation remain compared. Every other
report value, including diagnostic bytes, complete ordered memory and integer
counters, is compared exactly. The final task campaign remains distinct from a
native-control registry result; `campaignComplete` is always false here.

The protected raw-capture helper preserves complete bytes up to its 16 MiB
bound and rejects overflow, timeout, invalid UTF-8 or unrelated output. Its
ordinary returned line arrays are not used to reconstruct the native streams.
Retained evidence directories are intentional output, not disposable source
mutations. The selector leaf alone creates and removes disposable copies,
verifying their resolved paths and rejecting reparse points before deletion.

## Independent review of historical discovery

The complete current discovery is
`.lake/lifecycle-native1/native-controls/20260927T051058239-1758cc65/RESULT.json`,
SHA-256
`04e1b2ad7018e23573935ccec3b1df32d54855df072eeb55fdc56b8eb78f5401`.
Its `EXPECTATIONS.candidate.json` SHA-256 is
`0c9b92c9b0342611758d83c167a3753e98a54d7e5304784dcd6fa5fdb315e974`.
The input fingerprint is
`4fddb88fdf3b1b8b6d3217a29fc78ff79bcc56bd27e73d39e3c9965d56785047`.
The candidate remains `UNREVIEWED_DISCOVERY`; this review does not change its
bytes. The root separately froze `NATIVE_EXPECTATIONS.json`, SHA-256
`ac42d3ee867503737956e5c0091a5cd31d8b8822e27101aa458bf05c6844439b`,
with status `FROZEN_ROOT_REVIEWED`. Read-only comparison confirmed its 48 ordered
IDs, input fingerprint, mapping hash and all measured projections are unchanged;
each has the root's assigned verdict and nonempty oracle explanation.

An independent read-only Python check compared all 48 actual JSON reports with
the fixed ordered registry and all 48 candidate projections. It independently
normalized address presence and reconstructed all eight per-report bank identity
relations, preserving every other property, array order and full-width integer.
All projections agreed. It rehashed 486 distinct actual report, case receipt,
raw capture and source/staged-binary files; all bytes and hashes agreed. Every
native invocation used the exact case argv and common staged client, ordinary
exit zero, exact LF-terminated OBSERVED stdout, empty stderr, no timeout or
overflow, and empty retained launcher streams. No new native process was run by
this reviewer.

| Measured disposition | Count | Exact distinguishing observations |
| --- | ---: | --- |
| Accept | 4 | Healthy build/query and shared-scalar build/query return packet 2, all 178 canonical memory cells unchanged, live strict predicate true, capacities `[8273,178,0,0]`, and exact requested storage `24 + 8 * capacity`. Both shared-scalar cases record one retained boxed scalar and still satisfy the same predicate. |
| Nondistinguishing | 1 | `NC-SKIP-REPACK-QUERY` succeeds with zero copied entries. All incoming arrays already have exact capacities; all source/replacement array identities agree. Packet, ordered memory and live strict predicate remain healthy. This is not a rejected mutation. |
| Reject publication | 17 | Skipped build replacement exposes excess source capacity; extra owner aliases fail exclusivity; each retained input/arena/key/history mode records its intended root; all eight copied-value/offset cases record `valuesEqual=0` and the exact intended memory bank 1/index 0 or 1 mismatch. All return status 10 and empty owner/answer/observation outputs. |
| Reject consuming operation | 17 | Ten partial-copy cases fire at exactly the requested copied-entry count with all initialized entries and created temporary arrays released. Post-take failure and both pre-publication failures empty outputs; the latter reached `strictPublication=1` and released all three created handles. Injected fault gives status 7 and fuel 0/20/100 gives status 8, without a healthy baseline. |
| Reject before build | 6 | Short/long endpoint, negative zero and bad sign return status 1; oversized Word input returns status 2; injected native owner allocation failure returns status 9. All outputs are empty and no replacement entries were initialized. |
| Reject before transfer | 3 | Query short/long endpoint and owner-allocation failure return status 1/1/9, preserve the exact native owner identity and every canonical memory cell, keep the live strict predicate true, and return no answer/observation. |

All 48 final receipts have cleanup complete, no live current-generation handles
or temporary arrays, created/released handle and array balance,
initialized/released entry balance, and no source-copy counter overflow. These
are interpreted with the generation/timing qualifications above. No intended
state/resource oracle was missing among the measured 48 cases, and no actual
semantic failure was found. The retained-key build also shows an actual extra
four-cell source copy: 3 calls/8279 cells compared with healthy build's 2/8275.
Healthy query records zero such source copies. These are the pinned generated-C
copy-hook measurements, not a census of every runtime allocation.

The campaign took 230.96 seconds including setup, capture and integrity checks.
The 48 native-process durations sum to 100.73 seconds and range from 1.6824 to
2.4884 seconds. The 120-second per-case ceilings were not reached. Staged PE
closure contains the testing C client, testing lifecycle DLL and pinned
`libInit_shared.dll`; OS imports retain the helper's documented external boundary.

This complete dispatch proves all 48 current native cases ran in their exact
order. The 18 caller controls separately prove Plan selection and rejection
before native execution. Current direct focused evidence also passed beforehand:
`.lake/lifecycle-native1/native-controls/20260927T050953252-01ec823c/RESULT.json`,
SHA-256 `9d9d8cf61a4f1b505db64951358842b820ba68a2a651aaff2f0677ad3ba78f94`.
Independent inspection confirmed the same current input fingerprint and wrapper
hash, selected ID `NC-NONE-BUILD`, exactly one stage/result, ordinary native exit
zero and exact OBSERVED stdout/empty stderr. Native time was 2.14364 seconds;
capture launcher time was 3.936 seconds. All 7167 recorded pins and cleanup
checks passed. This establishes the current focused semantic dispatch separately
from the historical nested invocation.

## Verification ledger

The orchestration change is based on the root's actual focused
`NC-NONE-BUILD` discovery:
`.lake/lifecycle-native1/native-controls/20260927T045419192-8422f68f/RESULT.json`,
with nested replay
`.lake/lifecycle-native1/replay/20260927T045443049-c102aecb/RESULT.json`.
That C process completed in 2.159 seconds, while the nested replay took 47.295
seconds including repeated whole-build source/tool/artifact hash checks.
Multiplying that wrapper duration by 48 gives a scheduling estimate of about
37.8 minutes, not a measurement of the other controls. The enclosing control
wrapper already checked all those build pins before and after the campaign.

The current `single-stage-direct-v2` orchestration therefore stages the same
three exactly build-bound binaries once and checks their actual PE closure.
It invokes the unchanged C control argv directly through the existing owned
capture helper, holds one campaign mutex, and retains full before/finally pin
checks. Both actual exit and exact stdout/stderr are checked per case. Cleanup
restores PATH, noninteractive error mode, mutex release and mutex disposal in
independent guarded actions. The 48-case mapping, challenge arguments,
`Canonical-Control`, `Project-Control` and `Assert-ControlDisposition` are
unchanged; AST source comparison against the prior tested wrapper confirmed the
three functions byte for byte. No C, Lean, Rust, build, identity, root replay or
protected helper changed. Root owns any corresponding process-decision entry.

The old discovery and its candidate expectations are retained as historical
measurements. Their input fingerprint is stale for this orchestration, and a
new current discovery is required. They are not silently transplanted into a
current reviewed manifest.

Governance preflight passed at checkout
`3dbdebedcc6ba6b2a864df0d46dcc09ccaaa7536`, governance
`7b227c49ef2ec044b702126cc41c9add847eed01`, required role `rmq-proof-sprint`, with
all three canonical RMQ skills available. Scope is new native-control registry,
wrapper, selector-control leaf and this evidence document.

- Development: PowerShell parser and exact one-case Plan invocation passed.
- Development: the initial 13 actual selector/registry callers passed in
  `.lake/lifecycle-native1/control-selector-controls/20260927T044003455-c3f0580b/RESULT.json`.
  This predates the added integer/mixed/case-sensitive/argument/phase holdouts.
- Historical selector leaf: all 18 actual callers passed in 90.96 seconds, each under
  its existing 30-second owned deadline, in
  `.lake/lifecycle-native1/control-selector-controls/20260927T044229534-59b5fb52/RESULT.json`.
  Receipt SHA-256 is
  `412c2a2a69289bf6c6f4d46182d5c5d6f461abd08eff183b0f9a18195b6ed217`.
  All 87 live/disposable pins were unchanged; disposable removal passed. The
  nonexistent build-receipt sentinel remained unread and no shadow `.lake`
  directory was created. The historically tested wrapper SHA-256 is
  `5b2e191623c95467e4fc0fd649f49b3b0575df7cf377943439b5088c2ae0ff3b`,
  registry SHA-256 is
  `1f7476824f518b33790da70e922e64e1985e07f4aac50d74abd35773f5ca8f34`,
  and selector checker SHA-256 is
  `074fafda02681223fbddb1075d6fbad08d56c128f3f3756412e4eb64706e36a7`.
- Current direct-orchestration selector leaf: all 18 callers passed in 91.79
  seconds under the unchanged 30-second per-caller owned deadline, in
  `.lake/lifecycle-native1/control-selector-controls/20260927T050334641-01d89c82/RESULT.json`.
  All 87 pins were unchanged and disposable cleanup passed, with no native
  child, heavy mutex acquisition or shadow runtime output. Receipt SHA-256:
  `5ab17a66569b99bedc6f28ce8c78db1ec827d17ce7c1e8daf42a56674177d75d`.
  Current wrapper SHA-256:
  `3c80436cd3796c45a2e1a35782431b36118548bd5255edadaeb3228801327480`.
  Current selector checker SHA-256:
  `621d82e2b4b1845ab3eb6bdadfe1a813672543da9f5b84bdfeee4ff13a2a9c6e`.
  The 48-case registry bytes remain unchanged.
- Development: read-only projection check against the retained 100-fuel receipt
  preserved the full unsigned sentinel `18446744073709551615`, 69 measured copy
  calls and source pointer presence. This is component validation only; it does
  not rerun native execution or certify the fresh thin runner.
- Current measured discovery and root-reviewed expectation freezing passed as
  indexed above. The final complete Replay passed as indexed below.
  Checker changes invalidate the affected selector
  evidence; unchanged checker bytes do not require an extra duplicate run.
- Full Lean/Lake and aggregate gates are skipped by this script-only leaf; no
  Lean or native implementation changed. Root retains task-wide final checks.

The conceptual change is that native challenges now have a fixed replayable
dispatch registry and cannot certify themselves from exit zero. Measurements
must identify a real state/resource difference, or explicitly record that the
challenge did not distinguish the property. Live assumptions are the pinned
Windows x64 runtime, the actual C inspection predicates and the separately
audited compiled route. A skeptical reviewer should inspect the frozen native
verdicts and the measured boxed-scalar/copy/retained-root witnesses, preserving
the disclosed nondistinguishing query case.

## Historical complete replay

Root replayed every reviewed case at
`.lake/lifecycle-native1/native-controls/20260927T052620110-f51e89eb/RESULT.json` (receipt SHA256
`5b960e5cc8517adc315463cd531f4e68af600abf9e1bcdc2741cd71b14019d06`).
All 48 ordered IDs passed with exactly 4 accept, 1 nondistinguishing,
17 reject-publication, 17 reject-operation, 6 reject-before-build, and
3 reject-before-transfer verdicts. Exact full projections, strict native streams,
ordinary zero child exits and resource balances match NATIVE_EXPECTATIONS.json
SHA256 `ac42d3ee867503737956e5c0091a5cd31d8b8822e27101aa458bf05c6844439b`.
All 7638 pins remained unchanged; independent integrity and cleanup passed.
This completed that historical replay. Its defective cross-run fingerprint
does not establish the current producing recipe.

## Corrected complete recipe and current replay

The local recipe guard now keys every input by its exact ordinal absolute path,
rejects conflicting duplicates and records every resulting row. Eleven actual
recipe-function controls pass at
`native-recipe-controls/20260927T071017981-3341822f/RESULT.json` (SHA256
`30d1507bdd17163174946f06221965c1141918469894e815f5648e4ee100abfe`).
Their complete input/oracle mapping is independently frozen. Eighteen existing
selector/mapping callers pass against the repaired runner at
`control-selector-controls/20260927T070655548-bc3d2d0d/RESULT.json` (SHA256
`5c28fab9f31ac5681e94f6a4f348d3c80ec598e2318192a2d0fd616579b7a9e8`).

Corrected focused Discovery at `native-controls/20260927T072450429-92e7bea9`
passed. Root independently reconstructed all 7148 input occurrences from the
explicit entry inputs, current client-build receipt and DLL manifest; it rehashed
all 6013 distinct files and checked 1135 consistent duplicates. The complete
1034385-byte strict UTF-8 recipe has SHA256
`494eadb41c09ba18e4d27d84eec77d12a0c220abf04b817b6f1b42a839a83791`.
The independent review is
`native-refresh-review/root-rebind-20260927/RECIPE_REVIEW.json`, SHA256
`7c6f4865c6ed2d7d6e50a0f4ebce564ea773cd390cf533301d2628104745257a`.
The review did not invoke the production recipe function.

Only the top-level input fingerprint and an appended provenance note changed in
`NATIVE_EXPECTATIONS.json`; its current raw SHA256 is
`e67348c7e631fb7facbd9b580a44d1b42729e9db0526a5ac09a2b804143e5466`.
All 48 case objects, including full integer values, exact projections, expected
verdicts, explanations and historical discovery receipt pins, remain unchanged.
Their canonical exact-integer JSON SHA256 is
`5697ab0c52c768001620aeda4ab5c4363c66c8e1d1d2f116d3140ab1c4d00ba9`.

Complete current Replay passes at
`native-controls/20260927T073240346-3c38ea74/RESULT.json`, SHA256
`a4545cfc2df8cfde3e92d27c4d7f6cc59c67946dbdae939d3e5c4739d60754e4`.
All 48 ordered cases reproduce those unchanged projections and verdicts: four
accepts, one nondistinguishing case, seventeen publication rejections, seventeen
operation rejections, six pre-build rejections and three pre-transfer rejections.
All native and launcher exits are ordinary zero with exact OBSERVED lines and
empty stderr. Native durations are 2.5226322–3.1646172 seconds, totaling
128.7382997 seconds. All 7638 integrity pins pass; PATH, error mode and mutex
resources are restored. `completeRegistry` is true; `campaignComplete` remains
false because it is deliberately not a declaration about the entire task.
These finite controls supplement the compiled ownership review and do not
quantify over arbitrary foreign-caller misuse.

An independent read-only review reconstructs every actual full projection and
the entire recipe, checks all 48 argv/ordinary-exit/stream triples, and rehashes
all 7638 final pin entries. Its 6500 distinct review inputs include the raw
captures and review script. It separately checks shared-scalar acceptance,
skipped-query nondistinction, strict publication followed by cleanup, partial-copy
cutpoints, pre-transfer owner/full-memory preservation and baseline-free fault/fuel
outcomes. Exact Python integers preserve `UINT64_MAX`. The retained review is
`native-control-independent-review/20260927T073240346-3c38ea74/REVIEW.json`,
214651 bytes, SHA256
`39c6f5155edcf143b5b4a85884c5f6a96c39d5efa27bee60846ee52802de4f2f`.
