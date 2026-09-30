import argparse, ast, hashlib, json, os, pathlib, re, shutil, subprocess

ROOT = pathlib.Path(__file__).resolve().parents[5]
OUT = pathlib.Path(__file__).resolve().parent
BASE = '0c873072e84be9e1d65edab1985bcff1d23abef1'
SOURCE = 'bea5ce75f788c4035031ba81e69d8de36eda3f92'
OLD = 'docs/internal/extensions/lifecycle-native-p0/'
REVIEW = pathlib.Path('C:/Users/poin/Documents/RMQ/lifecycle-implementation-20260920/native-p0-review')

def git(*args):
    return subprocess.check_output(['git', '-c', 'core.excludesfile=', '-C', str(ROOT), *args])
def sha(b): return hashlib.sha256(b).hexdigest().upper()
def blob(path, ref=BASE): return git('show', f'{ref}:{path}')
def readj(path): return json.loads(pathlib.Path(path).read_text(encoding='utf-8-sig'))
def pin(path):
    b=pathlib.Path(path).read_bytes()
    return dict(path=str(path), bytes=len(b), sha256=sha(b))
def rows(raw):
    raw.decode('utf-8', errors='strict')
    rs=[r for r in raw.splitlines() if re.match(rb'^\| `(?:LN0-|INV-|CHK-|NP0R1-)',r)]
    ids=[]
    for r in rs:
        cells=r.split(b'|')
        assert len(cells)==10, 'eight-column row required'
        ids.append(cells[1].strip().strip(b'`').decode())
    assert len(set(ids))==len(ids), 'duplicate IDs'
    return dict(zip(ids,rs))
def verify_rows(raw):
    original=rows(blob(OLD+'ACCEPTANCE_MATRIX.md'))
    initial=rows((OUT/'ACCEPTANCE_ROWS.txt').read_bytes())
    current=rows(raw)
    assert len(original)==12 and len(initial)==14
    assert list(current)==list(initial), 'missing/extra/reordered IDs'
    assert all(current[k]==r for k,r in initial.items()), 'frozen row bytes changed'
    assert all(current[k]==r for k,r in original.items()), 'inherited row bytes changed'
    prompt=pathlib.Path('C:/Users/poin/Documents/RMQ/lifecycle-implementation-20260920/LIFE-NATIVE-P0_PROMPT.md').read_text(encoding='utf-8-sig')
    requirements=dict(re.findall(r'^- ([A-Z0-9-]+): (.+)$',prompt,re.M))
    for key in original:
        assert current[key].split(b'|')[2].strip().decode()==requirements[key], f'prompt requirement changed: {key}'
    module=ast.parse((OUT/'freeze_contract.py').read_text(encoding='utf-8'))
    new=next(ast.literal_eval(x.value) for x in module.body if isinstance(x,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='requirements' for t in x.targets))
    for key, req in new.items(): assert current[key].split(b'|')[2].strip().decode()==req
    assert sha((OUT/'ACCEPTANCE_ROWS.txt').read_bytes()).lower()==readj(OUT/'START.json')['frozenRowsSha256']
    return list(current)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output', required=True);args=ap.parse_args()
    raw=(OUT/'ACCEPTANCE_MATRIX.md').read_bytes();ids=verify_rows(raw)
    negatives={
      'mojibake':raw.replace(b'Implement', '\u00c2\u00acImplement'.encode(),1),
      'changed-cell':raw.replace(b'Open at freeze',b'Closed at freeze',1),
      'duplicate':raw+b'\n'+next(iter(rows(raw).values()))+b'\n',
      'missing':raw.replace(next(iter(rows(raw).values())),b'',1),
    }
    for name,b in negatives.items():
        try: verify_rows(b)
        except (AssertionError,UnicodeError): pass
        else: raise AssertionError(f'negative accepted: {name}')
    changed=git('diff','--name-only',BASE).decode().splitlines()+git('ls-files','--others','--exclude-standard').decode().splitlines()
    allowed={'scripts/packed_native_lifecycle_storage_replay.ps1','scripts/packed_native_lifecycle_integrity_check.ps1','docs/internal/WORKFLOW_DESIGN_DECISIONS.md','docs/internal/DESIGN_DECISIONS.md',OLD+'BOUNDARY.md'}
    assert all(p in allowed or p.startswith(OLD+'repair-r1/') for p in changed),changed
    for p in ['docs/internal/WORKFLOW_DESIGN_DECISIONS.md','docs/internal/DESIGN_DECISIONS.md']:
        assert (ROOT/p).read_bytes().startswith(git('cat-file','--filters',f'{BASE}:{p}')), f'ledger working prefix changed: {p}'
    protected=['native/packed-rmq/tests/lifecycle_storage_probe.c','lean-toolchain',OLD+'REGISTRY.json',OLD+'ACCEPTANCE_MATRIX.md',OLD+'ACCEPTANCE_ROWS.txt',OLD+'REQUIREMENTS.json',OLD+'REPORT.md',OLD+'RESULTS.json',OLD+'BASELINE.json',OLD+'CERTIFICATION.json',OLD+'START.json',OLD+'RUNTIME_SOURCE.json']
    for p in protected: assert (ROOT/p).read_bytes()==git('cat-file','--filters',f'{BASE}:{p}'),f'protected working bytes changed {p}'
    originalRunner=blob('scripts/packed_native_lifecycle_storage_replay.ps1',SOURCE)
    assert sha(originalRunner)=='077BF8D478141F8891AB6F9C2E332CBF8C8F75ACA32C722B29BD307924957B8E'
    assert sha(blob(OLD+'RESULTS.json',SOURCE))=='6440A963BE7A0E65222F86AFE3CFB89E4BEE1B6BDCD0226DC0D5CDA88D296FDD'
    current=(ROOT/'scripts/packed_native_lifecycle_storage_replay.ps1').read_bytes()
    def funcs(b): return dict(re.findall(rb'(?ms)^function ([\w-]+)(.*?)(?=^function |\Z)',b.replace(b'\r\n',b'\n')))
    oldf,newf=funcs(originalRunner),funcs(current)
    semantic=['Read-LNRegistry','Resolve-LNSelection','Assert-LNProcess','Read-LNOneJson','Assert-LNNoStderr','Assert-LNRejected','Assert-LNProperties','Get-LNMeasuredFailure','Assert-LNSnapshot','Assert-LNMeasurement']
    for name in semantic:
        if name.encode() in oldf: assert oldf[name.encode()]==newf[name.encode()],f'semantic function changed {name}'
    review=readj(REVIEW/'IDENTITY_ROWS_PINS.json')
    for p,expected in review['pins'].items():
        actual=pin(p);assert actual['bytes']==expected['bytes'] and actual['sha256'].lower()==expected['sha256'].lower(),p
    provenance=readj('C:/Users/poin/.codex/worktrees/af4b/RMQ/.lake/lifecycle-native-baseline/source-provenance.json')
    actualBlobs={row.split(b'\t',1)[1].decode():row.split(b'\t',1)[0].split()[2].decode() for row in git('ls-tree','-rz','HEAD').split(b'\0') if row}
    for entry in provenance['sources']:
        p=entry['path'];assert p in actualBlobs
        assert pin(ROOT/p)['sha256'].lower()==entry['sha256'].lower(),p
        assert actualBlobs[p]==entry['gitBlob'],p
    context=readj('C:/Users/poin/.codex/worktrees/af4b/RMQ/.lake/lifecycle-native-p0/checks/default-claim-context.json')
    files=[ROOT/'README.md']+[p for d in ['artifact','docs','paper'] for p in (ROOT/d).rglob('*') if p.is_file()]
    def excluded(p):return p.startswith(OLD) or p in ['docs/internal/DESIGN_DECISIONS.md','docs/internal/WORKFLOW_DESIGN_DECISIONS.md']
    live={p.relative_to(ROOT).as_posix():p for p in files if not excluded(p.relative_to(ROOT).as_posix())}
    assert set(live)=={e['path'] for e in context['files']}
    for e in context['files']:
        a=pin(live[e['path']]);assert a['bytes']==e['bytes'] and a['sha256']==e['sha256'],e['path']
    for p,key in [('scripts/claim_drift_scan.ps1','scannerSha256'),('docs/internal/CLAIM_DRIFT_POLICY.json','policySha256')]:assert pin(ROOT/p)['sha256']==context[key]
    assert pathlib.Path(shutil.which('rg')).resolve()==pathlib.Path(context['ripgrepPath']).resolve()
    assert pin(context['ripgrepPath'])['sha256']==context['ripgrepSha256']
    assert (os.environ.get('RIPGREP_CONFIG_PATH') or None)==context['ripgrepConfigPath']
    result=dict(base=BASE,head=git('rev-parse','HEAD').decode().strip(),rows=ids,changedIds=[],negativeControls=list(negatives),
      changedPaths=sorted(changed),protectedPaths=protected,sourcePreservation=semantic,
      historicalSource=dict(commit=SOURCE,gitBytes=len(originalRunner),sha256=sha(originalRunner),transformation='git show subprocess bytes; no newline serialization'),
      originalPinsChecked=len(review['pins']),baselineSources=len(provenance['sources']),outsideClaimPaths=len(live),
      claimCoverage='Verified original default-root scan plus pending final unchanged-policy rescan of lifecycle-native-p0 and both ledgers; not a new full scan',
      checkoutByteRule='Frozen rows and historical source read as strict Git UTF-8/raw bytes. Protected working files and ledger prefixes compare with git cat-file --filters exact base, explicitly accounting for checkout CRLF. Current working pins are separately measured.',
      currentRunner=pin(ROOT/'scripts/packed_native_lifecycle_storage_replay.ps1'))
    pathlib.Path(args.output).write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(f'CONTRACT PASS: {len(ids)} frozen rows, {len(review["pins"])} historical pins, {len(live)} unchanged outside paths, {len(provenance["sources"])} unchanged baseline sources')
if __name__=='__main__':main()
