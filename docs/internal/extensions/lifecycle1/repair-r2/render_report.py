"""Render the worker report only from the validated complete packet and row ledger."""
from pathlib import Path
import argparse, hashlib, json, re, subprocess
ROOT=Path(__file__).resolve().parents[5]
HERE=Path(__file__).resolve().parent
def git(*a):return subprocess.run(['git',*a],cwd=ROOT,check=True,capture_output=True).stdout.decode().strip()
def identity(p):b=p.read_bytes();return {'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--control-commit',required=True);a=ap.parse_args()
    e=json.loads((ROOT/'.lake/repair-r2/evidence-verified.json').read_bytes());h=json.loads((HERE/'HISTORY_APPLICABILITY.json').read_bytes());c=json.loads((HERE/'CONTRACT.json').read_bytes());s=json.loads((HERE/'START.json').read_bytes())
    assert e['passed'] and h['status']=='PASS' and len(c['orderedIds'])==47
    rows=(HERE/'ROW_DISPOSITIONS.md').read_bytes();assert all(('### Evidence for '+i+'\n').encode() in rows for i in c['orderedIds'])
    material=json.loads((HERE/'MATERIALIZATION.json').read_bytes())
    contract=json.loads((HERE/'FINAL_CONTRACT_VERIFICATION.json').read_bytes())
    assert contract['status']=='PASS' and contract['inputFilesUnchanged']
    assert contract['controlSummary']=={'selected':22,'expectedAccept':2,'expectedReject':20,'allMatched':True,'predicate':'verify(Inputs)'}
    assert contract['verdict']['rows']==47 and contract['verdict']['inheritedRows']==45
    assert contract['verdict']['orderedIds']==c['orderedIds'] and not contract['verdict']['changedInheritedIds']
    for name,path in contract['inputPaths'].items():assert identity(Path(path))==contract['inputs'][name], 'Stale final contract input: '+name
    assert identity(HERE/'verify_contract.py')=={k:contract['verifier'][k] for k in ['bytes','sha256']}
    assert re.fullmatch(r'[0-9a-f]{40}',a.control_commit) and git('rev-parse',a.control_commit+'^{commit}')==a.control_commit
    freeze=json.loads((HERE/'SOURCE_FREEZE.json').read_bytes());assert freeze['controlCommit']==a.control_commit
    assert freeze['historyApplicability']=={'path':'HISTORY_APPLICABILITY.json',**identity(HERE/'HISTORY_APPLICABILITY.json')}
    for record in freeze['sources']:
        assert identity(ROOT/record['path'])==record['currentRaw'], 'Stale source freeze: '+record['path']
    for name in ['render_report.py','build_rows.py','verify_evidence.py']:
        record=next(x for x in freeze['sources'] if x['path']==(HERE/name).relative_to(ROOT).as_posix())
        assert record['producingCommit']==a.control_commit
        assert git('rev-parse',a.control_commit+':'+record['path'])==record['gitObject']
    changes=set(git('diff','--name-only',e['base']).splitlines())|set(git('ls-files','--others','--exclude-standard').splitlines())
    changes.update({'docs/internal/extensions/lifecycle1/repair-r2/REPORT.md','docs/internal/extensions/lifecycle1/repair-r2/RESULTS.json','docs/internal/extensions/lifecycle1/repair-r2/SOURCE_FREEZE.json'})
    check_rows=[]
    for x in e['checks']:
        meaning='PASS' if x['expectedExit']==0 else 'Expected historical failure retained'
        check_rows.append(f"| `{x['name']}` | {meaning} | {x['exit']} | {x['seconds']:.3f} / {x['deadline']} |")
    bytes_rows=[]
    for path,x in material['files'].items():bytes_rows.append(f"| `{Path(path).name}` | {x['initial']['bytes']} / `{x['initial']['sha256']}` | {x['git']['bytes']} / `{x['git']['sha256']}` | `{x['gitObject']}` |")
    controls=[]
    for profile,campaign in e['controlCampaigns'].items():
        controls.append(f"{profile}: {len(campaign['selected'])} of {len(campaign['selected'])} registered controls passed, in frozen order:\n\n```text\n"+'\n'.join(campaign['selected'])+'\n```\n')
    report=f'''Status: CANDIDATE_COMPLETE
I found no assigned or inherited acceptance criterion unmet; coordinator acceptance is still required.

LIFE-1-R2 closes the two measured local verification blockers. The unchanged
original contract checker passes after the three explicitly authorized exact-Git
materializations. The production dependency hash now has identical byte semantics
in both declared shells. All required current controls and the changed-runner
current-pwsh full26 replay pass. No Lean theorem, native source, expected-type
consumer, selector, diagnostic classifier, global helper or old report changed.

Worker LIFE-1-R2; title `(LIFE-1-R2) Complete lifecycle verification portability`;
task `01a0c23e-6fce-7542-b453-8fa7a741d7c9`; worktree
`C:/Users/poin/.codex/worktrees/e993/RMQ`; branch
`codex/life-1-r2-hash-and-contract`. Exact base is
`{e['base']}`. The preserved previous branch
`codex/life-1-r1-validator-portability` still names that exact commit.
Production and executed hash/materialization-control freeze is
`{e['productionCommit']}`. The final new evidence-verifier/row-generator freeze is
`{a.control_commit}`. Unchanged R1 dispatcher/handlers retain their reviewed
`7c406b15bdc12333d323c92641ab6c6dad6af7a2` source, with exact current raw pins.
The enclosing package commit, final report byte count/SHA256, final certification
receipts and empty porcelain are pinned outside this report at
`C:/Users/poin/.codex/worktrees/e993/RMQ/.lake/repair-r2/delivery.json`.
This avoids a report/commit self-hash cycle. No push, integration, retirement,
native adapter launch, publication, aggregate or acceptance is performed.

The canonical preflight passed before any write at governance
`7b227c49ef2ec044b702126cc41c9add847eed01`, with actual runtime catalog
`rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint` and required
`rmq-proof-sprint`. [START.json](START.json) and [PREFLIGHT.json](PREFLIGHT.json)
retain the actual output, original branch/base, clean startup, runtime/tool pins,
review identities, all 3,751 initial tracked raw/Git identities, and disclosed
materialization/new-baseline links. The coordinator disposition was read in full:
17,832 bytes, SHA256
`520d24e435ab007ee84a58ca6d0c36a93aca950ec998190d4e44535c89af4a79`.
The exact dispatched prompt is [PROMPT.md](PROMPT.md),
42,538 bytes, SHA256 `18ae1f54dcb8036416ef1b6b7ab2922a816698d22da514a02511653b7ff82873`.

The complete 47-row contract is [ACCEPTANCE_MATRIX.md](ACCEPTANCE_MATRIX.md), with
current dispositions in [ROW_DISPOSITIONS.md](ROW_DISPOSITIONS.md). All 45 inherited
complete eight-column rows are byte-for-byte equal to the exact-base R1 Git blob;
their original Open and historical cells are preserved. Two exact new requirements
follow them. The 49,039-byte frozen prefix SHA256 is
`ad03e9572fff3c630bae7b80f2235d03302d2ab48fadfcc2c6e180c489b975c2`.
The strict verifier compares ordered IDs, eight nonempty columns, all full
requirement strings, whole rows and prefix bytes. Its 22 controls comprise two
legitimate positives and 20 exact-code rejections, including missing/duplicate
IDs, late cells, mojibake and source/predicate substitution. Counts alone are
never used as preservation evidence. The row ledger quotes all 43 original
checked-conclusion/object-chain and challenge paragraphs, with exact source
identities; the global final certification requirement applies to every row.

The initial CRLF checkout was reproduced as a real failure by the actual unchanged
`scripts/lifecycle_contract_integrity.ps1`, against external original
`C:/Users/poin/Documents/RMQ/lifecycle-implementation-20260920/LIFE-1_PROMPT.md`
(33,909 bytes, SHA256
`f82a24460dfa06602fc52e2c78b0fa8402fbb84a0d203b4abb95040fa56b0c18`).
Three scratch negatives isolate the old CRLF state, JSON-only materialization,
and JSON-plus-frozen materialization. They reject respectively at CONTRACT_HASH,
frozen HEADER and active HEADER. The three-blob scratch positive and successor
live positive both pass the same unchanged 43-row checker. Every live initial
file was checked before any write. Only the named complete Git blobs were written,
and only afterward was [PROTECTED_BASELINE.json](PROTECTED_BASELINE.json) captured.

| Original file | Reviewed initial raw bytes / SHA256 | Exact final Git bytes / SHA256 | Exact Git blob |
| --- | --- | --- | --- |
{chr(10).join(bytes_rows)}

[MATERIALIZATION.json](MATERIALIZATION.json) records the exact transformation,
actual P/Q checker receipts and final equality. Each reviewed initial file equals
the immutable R1 initial manifest and differs only by LF-to-CRLF checkout
conversion. Each successor file equals the exact base blob, with zero Git content
diff. Git index metadata was refreshed after materialization; the staged content
remained empty. No Git configuration/attributes or unrelated file was normalized.
The documented LF-preserving reproduction precondition remains. Runtime integrity
failure still remains nonzero and does not restore original files.

The only production edit replaces Hash-Bytes's 100-byte body with a 195-byte body:

```powershell
$hasher = [Security.Cryptography.SHA256]::Create()
try {{ return ([BitConverter]::ToString($hasher.ComputeHash($bytes))).Replace('-', '').ToLowerInvariant() }}
finally {{ $hasher.Dispose() }}
```

The signature and every byte before/after that body remain identical. Old raw
source is 20,877 bytes, SHA256
`e2df09b1920691127c29eefc293700b7d046a7ddec7f78db18ea68a6b6c42b47`;
new raw source is 20,972 bytes, SHA256
`66d1d42b1c01288fcb362dd716493f3154cc3c606b49d65b9f1e5f8fbaed68e1`.
[HASH_CHANGE.json](HASH_CHANGE.json) and the scope verifier bind the unchanged
raw prefix/suffix at offset 1487. No text round trip changed the mixed newline
history. Hash-File continues hashing exact file bytes. The registry's existing
explicit normalization remains at its original caller; it was not moved into
Hash-Bytes. All registry, artifact, private-import and finalizer callers are
preserved, as are failure propagation and disposal.

[HASH_VECTORS.json](HASH_VECTORS.json) freezes eight independently computed
Python/hashlib vectors: empty, 00, ff, sixteen binary bytes, explicit UTF-8
for U+00E9 U+03A9 U+6F22 U+1F642, one changed UTF-8 byte, LF and CRLF.
The exact old production span on modern pwsh and the repaired production span
on each shell produce all eight same expected lowercase 64-character digests.
Three input pairs retain detectably unequal digests. Each child is bounded,
source/AST/raw-span pinned, actual-runtime bound, and checked with ordinal
string comparisons. The old WinPS component exits 7 with exactly the missing
HashData API error; it stays a failed positive, not a successful negative test.

The actual old WinPS F01 also remains failed before pin capture. Its baseline
count is zero and cannot establish intact-file integrity. After the repair,
F01 captures and verifies two real files under both shells before the complete
negative campaigns. Full current finalizer controls retain stage/integrity/
cleanup failures separately, leave changed captured originals unrestored,
remove valid shadows despite integrity failure, reject invalid paths untouched,
exercise actual exclusive-lock cleanup failures, and observe normal mutex
release and child/root absence. F00 still executes the exact old pre-R1 component
on pwsh and retains its old shadow until the separate harness cleanup. All
fixture restoration concerns only owned scratch pins in their own finally.

The observed bounded runs are:

| Check | Disposition | Exit | Seconds / deadline |
| --- | --- | --- | --- |
{chr(10).join(check_rows)}

The successful current-pwsh26 replay uses the unchanged 120-second compiler bound
inside the 7200-second outer guard. Every case first elaborates a fresh clean
producer, then runs its unchanged expected-type client. All 23 exact rejection
mappings and three expected acceptances match the frozen 26-case registry.
Independent receipt validation reconstructs producer edits/client byte hashes,
requires the complete 12-item pin roster, exact executable/stage/arguments/private
artifact paths, and exact diagnostic source boundary, declaration interval,
class and count. Final original/private restoration and shadow removal pass;
stage/integrity/cleanup errors are null. The self-test's zero-file baseline is
separately limited and is not used to prove full source integrity. Full26 was
run only in current pwsh; narrow Windows controls do not certify a Windows
full26 compiler replay.

The unchanged R1 full dispatcher uses frozen registry SHA256
`385c9bc95ac09b3cc046a7049e954cdf19361330c31f99bd83c9da0c822423f2`.
Each actual mapping, handler, predicate and positive/challenged receipt appears
in the validated packet referenced by [RESULTS.json](RESULTS.json) and the file
pins in [EVIDENCE_INDEX.json](EVIDENCE_INDEX.json). Both 12-case registry/runtime
campaigns pass with 24 bounded P/Q children each. They preserve focused/full,
explicit empty/whitespace/unknown, missing/duplicate/unknown middle IDs, extra
and changed mappings, wrong profile and wrong supplied-shell rejection.

{chr(10).join(controls)}
The runtime paths and pins are unchanged:

| Profile | Observed versions | Executable SHA256 |
| --- | --- | --- |
| Current bundled pwsh | 7.6.5 / Core / .NET10.0.11 | `362a356ce7f0940ec74f73a8fc2c990a2cc24a38a11c90bbd8eca947110ad139` |
| Windows PowerShell | 5.1.26100.9444 / Desktop / Framework4.0.30319.42000 | `8bb6fa8c283b4d92120b1ef249a9b311b0f804d4cabbe9981159976c8be76a5e` |

Exact paths are in START and every runtime receipt: bundled
`C:/Users/poin/.cache/codex-runtimes/codex-primary-runtime/dependencies/native/powershell/pwsh.exe`
and `C:/Windows/System32/WindowsPowerShell/v1.0/powershell.exe`.
The installed Lean4.22.0/Lake5.0.0-src+ba2cbbf toolchain remains at
`C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0/bin`.
The real default build passes with verified warm cache. No tool was installed,
upgraded or downloaded. Named builds were unnecessary because the actual
executable/consumer artifacts were present and their provenance checked.

[HISTORY_APPLICABILITY.json](HISTORY_APPLICABILITY.json) preserves the distinction
between old producing identities and current consumed inputs. It verifies
{h['counts']['distinctFilesRehashed']:,} files and {h['counts']['bindingsVerified']:,}
bindings, all 1,163 cache sources, 5,579 copied artifacts, 111 named consumer
artifacts, and 45 original manifest source objects. The 48 distinct old/current
raw profiles are explicitly classified, including the repaired dependency source,
three materialized contracts and append-only workflow ledger. No historical
receipt or R1 SOURCE_FREEZE/EVIDENCE_INDEX/INITIAL_WORKING_FILES/SCOPE_VERIFICATION
was rewritten. The R1 current-checkout manifest generator was not reused as a
successor equality predicate.

Both real full16 validator runs remain applicable at their original producer
`122a6bedb086d1de1df8dec167c890f887a72cc2`: current pwsh119.739s and
Windows109.269s, nine owned processes each and all16 ordered native IDs/models/
kinds. The actual validator, environment adapter, helper, Lean input closure,
native executable and runtime/artifact bytes are unchanged. The old run wrapper
also captured the dependency source hash; that incidental pin is resolved to
its old producer and is never falsely compared equal to the repaired source.
The native executable remains SHA256
`4752591ec5a7d962e09440391aa38d0e2fc534b2f04775aab9c0c735e43ba99c`.
The full16 results are reused, not rerun for an R2 label. The old full26 and67
control results remain historical and do not close the changed-runner rows.

The original exact type/axiom inventory is likewise source-bound reused evidence:
its actual 135.302-second clean result from formal producer
`299ec6527ca2fbcf73cfc34e9de75f4a1f34140c` and all three retained files match.
The 47,783-byte stdout SHA256 is
`76acd8fd09b7673e0d6a1682a418787a9252c44f48d60bcafb659c37c6c4f66b`.
The inventory's recorded axioms remain subsets of propext, Classical.choice
and Quot.sound. Hash compatibility is not a new Lean theorem.

The formal public type remains:

```lean
continuousConstructionQuery_holds
    (model : InputModel) (xs : List Int) (left right : Nat)
    (domain : InputDomain model xs)
    (hl : left < 2 ^ wordWidth xs.length)
    (hr : right < 2 ^ wordWidth xs.length) :
    ContinuousConstructionQuery model xs left right
```

All seven fields concern the same continuousRun, Layout.program, declared width,
constructed memory, retained owner and retainedRho. C01-C07 independently project
construction, retained state, safety, physical backing, finite owner, reusability
and uniform bounds; C08-C14 pin word/comparison domains, constants, valid/invalid
packets and guarded paired-prefix agreement. P01 retains actual reservation,
output/metadata/copy/release producing positions and pre-states. No final answer
or READY owner becomes an initial premise. Word input retains InputFits at one
query-independent width; arbitrary-Int comparison resources remain separate.
Endpoints must be represented. Input materialization and out-of-word admission
stay outside that type. Subsequent charged query entry starts with the proved
READY interface, preserves the same allocation and has the unchanged160257
modeled transition bound. The numeric retained bound and little-o remainder
concern these same objects. The evolving modeled arena and logical container
extents establish neither native capacity/alias freedom nor an immutable initial
whole-run snapshot.

All expensive campaigns are serialized with
`Local\\RMQLifecycleImplementationHeavy20260920`, without recursive acquisition
around production runners that own it. Current checks record ordinary exits,
elapsed times, deadlines, timeout/overflow, ownership, returned streams and
cleanup. Ordinary completed controls have no unexpected timeout/overflow.
The two T01 controls and dependency self-test intentionally exercise the real
six-second descendant timeout and retain observed PID absence. Available helper
output consists of returned nonempty lines, not original raw process bytes.
Blank-only lines are removed by the protected helper; overflow/exceptional
cleanup can prevent output recovery. Exact Console.Error capture in dependency
boundary fixtures retains trailing newlines. Existing culture-based comparisons
remain inherited boundaries; new exact string assertions use ordinal semantics.
No missing, unsupported or truncated result is credited as success.

The initial old checker, old Windows hash/F01 failures and all previous R1 failed
attempts remain identified failures. A bounded read-only review confirmed the
production raw prefix/suffix, exact input semantics and disposal. Review of the
new evidence reader tightened frozen case/spec binding, actual runtime binding,
registry P/Q expectations, complete dependency capture/invocation identities,
exact diagnostic path boundaries and both wrapper log paths. These evidence
checks were revalidated on the same truthful receipts; production predicates
were unchanged and no duplicate expensive replay was needed for reader changes.

WDD-20260921-LIFE-R2-001/002/003 record the scope/materialization/hash choice,
source-applicability and evidence-reader choices, rejected weakenings and final
packaging. No proof/model design changed, so DESIGN_DECISIONS is unchanged.
The new raw scope check verifies all 3,749 protected tracked files, exact original
Git content, only the declared Hash-Bytes body change and the complete WDD raw
prefix. Per-commit and exact-base-range strict design, working/range whitespace,
hygiene/native-decision scans and final report-sensitive unchanged-policy claim
coverage are recorded in the final certification/delivery packet. Final claim
coverage explicitly includes this report, row ledger, active matrix, verification
plan and appended WDD; policy-filtered emitted hits are not claimed as a file
visitation log. No broad report allowance was added.

Changed paths relative to exact base (the three setup-materialized files have
zero Git content diff and therefore are not listed here):

```text
{chr(10).join(sorted(changes))}
```

Conceptually, this completes commissioning of the exact contract bytes and makes
the existing byte-hash operation available on both declared runtimes. In plain
English, Windows can now capture real file pins and run all the existing failure
checks, while the original contract checker sees precisely the files it always
required. The mathematical lifecycle, cost model and retained owner are unchanged.
The skeptical next questions concern independent reconstruction of this exact
candidate and the separately assigned native ownership/consuming adapter,
joint aggregate and fresh-blind acceptance. Those campaign phases remain
mandatory and are not conclusions of this local repair.
'''
    (HERE/'REPORT.md').write_bytes(report.encode('utf-8'))
    print(json.dumps({'report':str(HERE/'REPORT.md'),**identity(HERE/'REPORT.md')},indent=2))
if __name__=='__main__':main()
