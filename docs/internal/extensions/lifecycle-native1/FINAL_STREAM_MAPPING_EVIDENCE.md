# Final stream control mapping evidence

Status: measured local helper controls; not whole-task acceptance or production
checker certification.

Read-only review found that `final_stream_controls.ps1` checked its ordered
15 IDs but only recorded the ID-to-handler/mutation/verdict/diagnostic mapping's
hash. Changing a handler while retaining the ID could silently substitute a
different control. The repair checks the complete mapping against the independent
fixed SHA256 below before selector validation, helper loading, output setup or
any child. The original 15 registry entries are unchanged verbatim.

- Complete compact UTF-8 mapping: `FINAL_STREAM_CONTROL_MAP.json`, SHA256
  `92a0cda169f378eba27a9884e5ed4a9e147845ef80ed0d528a02e95beb115813`.
- Original `$registry` assignment's exact source text, before and after repair:
  `7825ad0d1e4c237281e4e5e64289307653f6068c6ae9ba6a111bb69e28d9b156`.
- `final_stream_mapping_controls.ps1` runs actual caller processes against the
  original script in Plan mode and four disposable copies with one altered
  handler, verdict, mutation or diagnostic. The copies retain the original
  fixed mapping guard. The caller preserves the ordinary exit and writes the
  exact guard exception to stderr; transport failures are not accepted.

The five mapping controls pass on the final helper at
`.lake/lifecycle-native1/final-stream-mapping/20260927T064730316-bd56c224/RESULT.json`.
Its own five-case ID/find/replace/exit mapping is independently frozen before
setup by SHA256
`0d374704543cf0a87fde7a129920ab00415a563f3baac743a9ec0dfdf4260920`.
The original five-case assignment remains verbatim, SHA256
`300c737779bda7e2a1a6b3f0a568ff3ab11296e1a6d857e7d5f65f48d7f5bc43`.
The earlier five-control pass at
`.lake/lifecycle-native1/final-stream-mapping/20260927T064317527-63447ada/RESULT.json`
precedes this additional independent guard and is historical evidence.
The original Plan returned ordinary zero, exactly 4,615 expected stdout bytes
and empty stderr. Each altered mapping returned ordinary one, empty stdout and
exactly 86 expected stderr bytes containing the mapping-mismatch diagnostic.
All 55 source/helper/capture pins remained intact; independent final integrity
and disposable cleanup passed. No live source writes, compiler/native process,
production checker or heavy mutex were involved.

The unchanged 15 semantic output-language controls also pass with the repaired
guard at
`.lake/lifecycle-native1/final-stream-controls/20260927T064348259-8b9ba5b5/RESULT.json`.
These exercise the existing `final_streams.ps1` predicates; their fixed cases
and expected verdicts are unchanged. Full final scope/design/claim checks remain
separate production executions.

Replay commands:

```powershell
pwsh -NoProfile -File docs/internal/extensions/lifecycle-native1/final_stream_mapping_controls.ps1
pwsh -NoProfile -File docs/internal/extensions/lifecycle-native1/final_stream_controls.ps1 -Mode Replay
```

Proof digestion: a successful roster count now means the same named controls
still dispatch to the same mutations and verdicts. The actual caller holdouts
check that this guard rejects a changed mapping before the copied script could
load helpers or create output. These finite controls do not establish every
possible parser behavior or replace the required final production checks.

The accompanying read-only audit of `final_checks.ps1` and `default_build.ps1`
found one separate exact-empty Git-stream gap, which the root repaired in its
owned final helper. No additional high-confidence verification gap remained in
the reviewed helpers. The default build's actual owned no-target `lake build`,
version/tool/source pins, shared mutex and independent final integrity/cleanup
must still run on the frozen source. The final source roster and committed
prose/ledger applicability are certified by the separate final checks and
external delivery receipt, not inferred from this helper audit.
