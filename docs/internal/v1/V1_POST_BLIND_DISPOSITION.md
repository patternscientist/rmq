# V1 final blind-audit disposition

The coordinator accepts the bounded source repair at
`ff92a2f94a97655a995ec744150ae7bab15ccb56`. This closes P2-01 for the supported
production process-status producer and verdict consumer. Final source/report
checks, replacement archives, hosted CI and publication remain separate gates.
The exact delivered commit and files will be bound by a new versioned external
delivery receipt; the earlier4ded delivery remains historical and unchanged.

## Evidence and decisions

The [fresh report](../audit_reports/v1-blind-4ded05c.md) remains NOT_READY at
its original4ded source. Its sole actionable finding was independently
reproduced: a child printed the expected failure, timed out, and still passed
the old negative verdict. The [continuation](../audit_reports/v1-blind-ff92a2f-continuation.md)
closes that finding atff92 with MERGE_READY_WITH_FOLLOWUPS. Both reports are
retained byte-for-byte; the continuation is the same auditor's correction loop,
not another fresh-blind assessment. The initial85-row assessment and its
unaffected formal/model/historical limitations remain in force.

| Item | Coordinator disposition |
| --- | --- |
| P2-01 | Closed. Actual producer uses the shared bounded runner; consumer requires normal exit1 plus intended failure for rejection, or normal exit0 plus required allowance for acceptance, with no timeout/overflow and completed cleanup. Real fail-then-hang and descendant controls discriminate old and repaired consumers. |
| R1–R4 | Accepted within the supported producer/consumer and inherited-descendant scope. Both full143fa Windows runs retain all134 policy and21 context cases with exact expected normal exits and completion flags. Their unchanged production inputs transfer toff92; the changed synthetic timeout has separate final three-shell checks. |
| R5 | Source repair and independent review complete. Delivery/CI steps remain required and cannot be inferred from local success. Preserve the old failed aggregate and every superseded/failed probe. |
| R6 | Accepted source/local checks. Tag workflow now supplies full history and an external log to the unchanged checkers and marks new hyphenated versions as prereleases. Actual hosted behavior and resulting release metadata still require verification. |
| Malformed object coercion | Deferred optional hardening. The actual internal producer always constructs the fields from integers/Booleans or throws; scanner text cannot replace that object. No external-record schema-validation claim is made. |
| Ownership limits | Retained existing boundary. Windows job member-enumeration failure falls back to waiting for the root; POSIX covers the inherited group, not a new session. Successful normal-descendant controls are not a universal containment theorem. |

The coordinator inspected the complete reports, authenticated their hashes,
checked exact clean source and changes, reproduced the old finding, inspected
the actual repaired consumer and shared-runner limitations, and reviewed the
raw full-run and final-control evidence. The continuation additionally derives
each expected case verdict from frozen source, rather than accepting the log's
own label. Exact report/receipt identities are in
[V1_POST_BLIND_DISPOSITION.json](V1_POST_BLIND_DISPOSITION.json).

Cached final repair `lake build` passed; hygiene/native-decision scans found no
matches; strict per-commit design and changed-ledger claim checks passed.
Final11 focused controls passed under pwsh, Windows PowerShell5.1 and POSIX.
The two full Windows policy runs are explicitly at143fa, not replayed atff92.
The first five-second POSIX control failed to reach its required diagnostic;
its isolated fifteen-second successor and final runs remain separate records.
The first coordinator old-source probe lacked Git identity and is not evidence
of an authenticated target; probe2 is. Shell-probe CRLF translation failures
remain preserved. No failed observation is renamed as a pass.

## Release sequence and scope

Preserve the failed447 aggregate and its separately verified component
composition in the earlier index. All Lean/toolchain/Lake inputs are unchanged
by these repairs. Refresh checks after integrating these reports, authenticate
the new Git-derived archive and unpacked smoke, and include both audits and
raw repair evidence in a new selected-evidence bundle. The external versioned
receipt must validate these actual outputs before publication proceeds.

Use a PR and the enforced hosted Lean gate and Reproduce artifact contexts.
Refresh and inspect origin/main before merge, preserve unrelated history and
never bypass protections. The version remains1.0.0-rc.1 and the intended tag
is v1.0.0-rc.1; neither stable promotion nor an existing-tag retarget is accepted.
Organization placement remains a separate user fork-versus-transfer choice.

Conceptually, the repair ties an expected diagnostic to a completed execution.
The mathematical contracts, model costs and formal assumptions are unchanged.
The next substantive questions concern the exact delivered bytes and actual
hosted outcomes; these documents do not answer those questions in advance.
