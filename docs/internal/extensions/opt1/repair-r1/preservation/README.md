# OPT-1-R1 preservation checker

Run from any directory using the supported PowerShell wrapper:

```powershell
powershell -ExecutionPolicy Bypass -File <repo>/docs/internal/extensions/opt1/repair-r1/preservation/check.ps1 `
  -RepoRoot <repo> -CandidateRef <exact-40-character-commit> `
  -OutputDirectory <new-private-receipt-directory>
```

The output directory must not already exist. The wrapper uses the existing
repository `owned_process_tree.ps1` supervisor; all Python/Git descendants
belong to that owned job or process group. Default outer deadline is 180s
and output ceiling is 8 MiB. Every binary Git capture additionally has a
30s deadline, 8 MiB proactive ceiling, separate `.stdout.bin`/`.stderr.bin`
files, exact exit and hashes. `process.json` retains supervisor cleanup and
the Python/checker/supervisor identities. `result.json` records each compared
row/object/type, raw live-file before/after hashes and all control outcomes.
No repository source, index, build tree or historical evidence is mutated.

Before the repair matrix is committed, add `-SelfTestOnly`. This runs exactly
the 17 entries in `registry.json` through the same production comparison
functions, verifies all live historical/repair rows and documentary field
types, and labels candidate-blob certification unperformed. It cannot be
used as final preservation evidence.

Final mode requires the candidate's committed repair matrix and
PROOF_IDENTITY.md. It compares the baseline's complete protected path/mode/blob
map; only additions below repair-r1 are permitted. The old entire matrix blob
must be byte-identical to the author baseline. Its 35 inherited complete row
contents, and those in the candidate/live repair matrix, must be byte-identical
to the original freeze. The four named repair IDs are the only permitted
additional matrix IDs. Physical LF/CRLF terminators are outside row content;
no content normalization or locale decoding is used. Ordinary Git live/index
object checks are separate from this direct row-byte equality. A standalone
mojibake rejection control and ordinary Unicode accept control are independent
of the byte comparison.

The selftests also reject omitted/duplicated/changed middle rows, missing or
duplicated repair rows, unknown IDs, invalid UTF-8, protected omissions,
blob/mode changes, unauthorized historical additions, and an altered field
ExpectedType. Exact rows and a permitted repair-directory addition accept.
Each registry entry pins its expected diagnostic code and executed order.

No Lean process is launched. This artifact certifies source/contract identity,
not the new build-profile linkage, 27 runtime cases, 80 certificate cases or
coordinator acceptance. POSIX runtime coverage is unexecuted until this wrapper
actually runs on a POSIX host. Receipt creation after a frozen candidate is
identified honestly as later evidence; no receipt claims to include itself
in its checked commit.
