# Preservation checker development evidence

This directory is the OPT-1-R1 preservation leaf. It does not certify fresh
Lean compilation, runtime/certificate campaigns or coordinator acceptance.
The parent owns final candidate commitment, source-profile evidence and final
preservation invocation with that exact committed CandidateRef.

All runs used the real `check.ps1` wrapper, its existing Windows
kill-on-close-job supervisor and bounded binary Git subprocess captures.
No Lean/build/cache work ran. No historical source/evidence or index entry
was intentionally mutated; controls alter private in-memory byte strings and
path/object maps and invoke the same production comparison functions.

| Receipt | Outcome and use |
| --- | --- |
| `selftest-01/result.json` and `process.json` | Initial 17/17 controls passed, with 35 inherited rows and 39 full types/78 consumers; 510 protected files unchanged. Inner duration 11.507s, owned supervisor 14.397s, outer 180s/8MiB. This version preceded explicit raw index before/after capture. |
| `selftest-02/result.json` and `process.json` | Retained setup failure: Windows rejected the attempted Git launch with WinError206 because enumerating all 512 watched file paths exceeded command-line length. No semantic control was credited. The raw protected files remained unchanged. |
| `selftest-03/result.json` and `process.json` | The command now requests the same complete protected directories and three explicit axiom scripts, then checks path identities in Python. This avoids the Windows argument limit without dropping any protected path. All17 controls pass; source and index bytes remain unchanged. Every actual Git child exits0 without timeout/overflow. |
| `selftest-04/result.json` and `process.json` | The final checker including its diagnostic-only follow-up passes all17 controls on the same frozen baseline. Source and index bytes remain unchanged; all11 Git children exit0 without timeout or overflow. This is the leaf's final development receipt, not candidate-blob certification. |

The diagnostic-only follow-up names an index restoration failure in stderr
if it is the only failure; it does not alter successful comparisons.
The parent's final invocation must identify the final checker/profile source.
The receipt hashes identify each older checker version rather than being
rewritten after edits.

The 39 ExpectedType strings in `../PROOF_IDENTITY.md` are copied from the
original FIELDS.json and compared directly with the fixed baseline Git blob.
The exact literal type payloads require a preserved LF artifact serialization;
the parent records the explicit artifact attribute at repair-r1 scope.

The local `.gitattributes` enumerates only actual files in this preservation
artifact, preserving raw receipt/stream bytes. It has no wildcard allowance
for future history, shared source or other repair directories. A later receipt
must receive its own explicit artifact-storage entry if it is committed.
