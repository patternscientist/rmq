"""LIFE-1-R3: materialize the exact Git blob bytes of the three LF-pinned frozen
control inputs in this checkout before the frozen control campaign.

The frozen control registry pins CONTROL_REGISTRY(.frozen).json and
finalizer_cases.json by their LF (Git blob) SHA-256, while this checkout uses
core.autocrlf=true and materializes them with CRLF. The Git content is not
changed: each file's CRLF-normalized working text must already equal its blob,
the blob bytes are written verbatim, and `git status` must stay clean for them.
Every other file keeps its checkout bytes (the frozen registry pins the other two
component files by their checkout bytes). Writes a JSON receipt to argv[1].

Git reports a checked-out autocrlf file whose working bytes are the LF blob as
"modified" at stat level even though `git diff` is empty and `git hash-object`
equals the index blob. The receipt therefore records the content proof (empty
`git diff --exit-code`, equal hash-object) instead of requiring an unchanged
porcelain status. `--restore <receipt>` re-checks-out the three paths from the
index (restoring the checkout representation) and requires a clean status for
them afterwards.
"""
import hashlib, json, pathlib, subprocess, sys
ROOT = pathlib.Path(__file__).resolve().parents[5]
PATHS = ['docs/internal/extensions/lifecycle1/repair-r1/CONTROL_REGISTRY.json',
         'docs/internal/extensions/lifecycle1/repair-r1/CONTROL_REGISTRY.frozen.json',
         'docs/internal/extensions/lifecycle1/repair-r1/finalizer_cases.json']
EXPECTED = {PATHS[0]: '385c9bc95ac09b3cc046a7049e954cdf19361330c31f99bd83c9da0c822423f2',
            PATHS[1]: '385c9bc95ac09b3cc046a7049e954cdf19361330c31f99bd83c9da0c822423f2',
            PATHS[2]: '1303ecf93c0a0c74e0a48023fe52258b7e847d020d009eb2f4deba7f084ab6df'}
def git(*args):
    r = subprocess.run(['git', '-C', str(ROOT), *args], capture_output=True, timeout=60)
    if r.returncode:
        raise SystemExit('git failed: ' + ' '.join(args) + ': ' + r.stderr.decode('utf-8', 'replace'))
    return r.stdout
sha = lambda b: hashlib.sha256(b).hexdigest()
def restore(receipt):
    if receipt.exists():
        raise SystemExit('receipt exists')
    git('checkout', '--', *PATHS)
    status = git('status', '--porcelain=v1', '--untracked-files=all', '--', *PATHS).decode()
    if status:
        raise SystemExit('restoration left status: ' + status)
    files = [{'path': rel, 'bytes': (ROOT / rel).stat().st_size, 'sha256': sha((ROOT / rel).read_bytes())} for rel in PATHS]
    receipt.parent.mkdir(parents=True, exist_ok=True)
    receipt.write_text(json.dumps({'schema': 'life1-r3-materialization-restore-v1', 'head': git('rev-parse', 'HEAD').decode().strip(),
                                   'files': files, 'statusForPaths': status}, indent=2) + chr(10),
                       encoding='utf-8', newline=chr(10))
    print(json.dumps(files))
if sys.argv[1] == '--restore':
    restore(pathlib.Path(sys.argv[2]))
    raise SystemExit(0)
out = pathlib.Path(sys.argv[1])
if out.exists():
    raise SystemExit('receipt exists')
head = git('rev-parse', 'HEAD').decode().strip()
status_before = git('status', '--porcelain=v1', '--untracked-files=all').decode()
records = []
for rel in PATHS:
    blob = git('cat-file', 'blob', 'HEAD:' + rel)
    if sha(blob) != EXPECTED[rel]:
        raise SystemExit('blob identity differs: ' + rel)
    p = ROOT / rel
    before = p.read_bytes()
    if before.replace(b'\r\n', b'\n') != blob:
        raise SystemExit('working content differs from the blob beyond line endings: ' + rel)
    if before != blob:
        p.write_bytes(blob)
    after = p.read_bytes()
    if after != blob:
        raise SystemExit('materialization failed: ' + rel)
    records.append({'path': rel, 'beforeBytes': len(before), 'beforeSha256': sha(before),
                    'afterBytes': len(after), 'afterSha256': sha(after), 'written': before != blob})
status_after = git('status', '--porcelain=v1', '--untracked-files=all').decode()
diff = subprocess.run(['git', '-C', str(ROOT), 'diff', '--exit-code', '--quiet', '--', *PATHS], capture_output=True, timeout=60)
if diff.returncode != 0:
    raise SystemExit('Git content diff after materialization')
for r in records:
    blob_id = git('ls-files', '-s', '--', r['path']).decode().split()[1]
    work_id = git('hash-object', '--', r['path']).decode().strip()
    if blob_id != work_id:
        raise SystemExit('hash-object differs from the index blob: ' + r['path'])
    r['indexBlob'] = blob_id
    r['workingHashObject'] = work_id
out.parent.mkdir(parents=True, exist_ok=True)
out.write_text(json.dumps({'schema': 'life1-r3-materialization-v1', 'head': head, 'files': records,
                           'statusBefore': status_before, 'statusAfter': status_after, 'gitDiffExitCode': diff.returncode,
                           'scope': 'Exact Git blob bytes of three LF-pinned frozen inputs; Git content unchanged.'}, indent=2) + '\n',
               encoding='utf-8', newline='\n')
print(json.dumps(records))
