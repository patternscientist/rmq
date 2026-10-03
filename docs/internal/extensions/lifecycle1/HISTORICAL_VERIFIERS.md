# Historical lifecycle verifier scope

This guide classifies the retained lifecycle evidence readers as inspected at
V1 evidence-hardening source checkpoint
`7e3a1d086d81eee924036afc3f84b1447ac503cb` in managed worktree
`C:/Users/poin/.codex/worktrees/v1-evidence-hardening/RMQ`. It is a source
trace, not a replay or a claim about every later integrated checkout. None of
the scripts below is invoked by `scripts/gate.ps1`, `lakefile.toml`, or a
workflow under `.github/workflows`; a bounded exact-name search over those
surfaces at that checkpoint returned no match.

The current file identities used for this trace are:

| Reader | SHA-256 |
| --- | --- |
| `repair-r1/source_manifest.py` | `d3b173d5d74929da4388476095a22f88be71e0751a9b539dbaea0636d092abc1` |
| `repair-r1/collect_evidence.py` | `d95377b9657e45226f3b894785411803051d43eb5169c9675e7208df09ec4e6d` |
| `repair-r2/verify_evidence.py` | `614081cb05f073121d02309a2f249da8d27c6535d9b069776c45a57239656cdf` |
| native `repair-r2/verify_results.py` | `ce931fd260a5fda818e06beef1c66c6152189b46984fc4510eb445376244cad2` |
| native `repair-r3/verify_results.py` | `a660cf4344a71ffb3e8e62e936836755598ba37fd483098c42e1733c4a61add4` |
| `scripts/packed_native_lifecycle_stream_check.ps1` | `71084788a6fe3e5662e187e82f74f078c65fc2f9425ecc9a0c23554bb2e641b7` |

## R1 source manifest

`repair-r1/source_manifest.py:18-20` pins base
`12bd7f0fc2c87f2c9bdef3825bd92477e48e3433`, production freeze
`122a6bedb086d1de1df8dec167c890f887a72cc2`, and source freeze
`7c406b15bdc12333d323c92641ab6c6dad6af7a2`. Line 37 pins
`.lake/build/bin/rmq_lifecycle_validate.exe` to SHA-256
`4752591ec5a7d962e09440391aa38d0e2fc534b2f04775aab9c0c735e43ba99c`,
and line 38 fixes the host tool root to the Lean 4.22.0 installation.

The old-key read is exact: `source_manifest.py:121-133` opens each
`.lake/repair-r1/checks/<name>/result.json` and iterates
`document["sources"]`. Current R1 and R2 `run_check.ps1` write
`entrySources` and `absentSources` instead (`repair-r1/run_check.ps1:83` and
`repair-r2/run_check.ps1:136`). Renaming the historical reader would not make
it current: `source_manifest.py:156-221` compares the live tree with the three
frozen Git trees and frozen working bytes, lines 264-266 require the old
executable hash, and lines 272-307 require the old build, replay, shell, and
tool receipts. Its deterministic target is the committed
`repair-r1/SOURCE_FREEZE.json` (`source_manifest.py:404-413`), currently
347,686 bytes with SHA-256
`4527e51e7e9e5cef2759957f7a1942a6bb6fab89b784d572fa0af3130a81606d`.
That packet is a frozen R1 identity receipt, not a current V1 test result.

## R1 evidence index

`repair-r1/collect_evidence.py:8-10` requires the live
`.lake/repair-r1` tree. Its old-key read is at line 28:
`value['sources']`. Lines 35-46 also follow retained validator output paths,
and lines 49-60 enumerate the old owned campaign directories. Lines 61-75
stamp the old production/source freeze identities and write the committed
`repair-r1/EVIDENCE_INDEX.json`, currently 2,136,062 bytes with SHA-256
`af8a32126da5f24ce5d43adfa2e4e8593bd2f6941480172c20a4fe62d9cf1ce6`.
The required `.lake/repair-r1` root was absent when this managed V1 worktree was
inspected at checkpoint `7e3a1d086d81eee924036afc3f84b1447ac503cb`.
A fresh index generated from another root would be a different product and
must not be described as replaying the retained R1 index.

## R2 evidence verifier

`repair-r2/verify_evidence.py:8-15` fixes `.lake/repair-r2`, base
`0485a64920a273d0830b926ee46275085222819d`, production
`cb4739220c01e6554a25ff8333652c0501486fa8`, both shell paths and versions,
the Lean 4.22.0 executable, and the dependency-replay script. Lines 29-30
require recorded sources to equal current files. The old-key read is at lines
39-49, where each check iterates `v['sources']` and copies it into
`sourcePins`. Lines 273-285 pin the R1 registry and frozen repair inputs to
their production Git blobs; lines 293-301 require the old executable and every
named `.lake/repair-r2` evidence folder before writing its packet and index.

The required `.lake/repair-r2` root and
`.lake/build/bin/rmq_lifecycle_validate.exe` were absent when this managed V1
worktree was inspected at checkpoint
`7e3a1d086d81eee924036afc3f84b1447ac503cb`. This does not describe the
coordinator's later integrated build checkout. The committed outputs remain
historical: `repair-r2/EVIDENCE_INDEX.json` is
808,355 bytes, SHA-256
`50f0b1329e91f542ee822cee2955eba136456da9bdd4d4b2192d69c62bd736ab`;
`repair-r2/RESULTS.json` is 303,999 bytes, SHA-256
`827bc69b864b71cb49c26350890bd29e8d744a97e675177ad7d89de59821dba1`.

## Native dependency-result readers

The current production stream consumer does not interpret either old or new
pin labels. `scripts/packed_native_lifecycle_stream_check.ps1:113` reads the
dependency control IDs plus `installedToolsUnchanged` and `fixtureRestored`.
The dormant R2 verifier does read the old plain keys:
`lifecycle-native-p0/repair-r2/verify_results.py:261-272` walks `r["pins"]`
and `r["oldSummary"]` as current-file pins. R3 imports that exact R2 parser by
SHA-256 at `repair-r3/verify_results.py:23-31`; it does not redefine the
dependency-result key contract.

The V1 producer therefore changes labels additively. In
`repair-r1/dependency_controls.ps1:127-130`, `entryPins` and
`entryOldSummary` retain entry snapshots, while `pins` and `oldSummary` come
from the final reads also used by `finalization.pinChecks`; an unreadable final
pin is explicit. Intact historical runs remain acceptable to the dormant
reader because their final pins still equal current files. A mutation run now
fails rather than presenting an entry value as final. The committed native R2
and R3 `RESULTS.json` files remain cached historical reports, not executions of
the V1 producer.

## V1 use

The V1 focused controls execute the current producers and consumers in owned
fixtures. This guide and the committed historical JSON files provide lineage
only. Running a source generator, hashing a cached report, or reading a
historical `passed` field is not a new test and is never counted as one in the
V1 command ledger.
