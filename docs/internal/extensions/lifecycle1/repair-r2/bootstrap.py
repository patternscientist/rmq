"""One-time R2 contract/initial-byte capture; no production materialization."""
from pathlib import Path
import hashlib, json, re, subprocess, sys
ROOT = Path(__file__).resolve().parents[5]
OUT = Path(__file__).resolve().parent
BASE = '0485a64920a273d0830b926ee46275085222819d'
EXT = Path('C:/Users/poin/Documents/RMQ/lifecycle-implementation-20260920')
def ident(b): return {'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
def git(*a): return subprocess.run(['git',*a],cwd=ROOT,check=True,capture_output=True).stdout
def write(n,v): (OUT/n).write_bytes((json.dumps(v,indent=2,ensure_ascii=False)+'\n').encode())
assert git('rev-parse','HEAD').decode().strip()==BASE
assert git('branch','--show-current').decode().strip()=='codex/life-1-r2-hash-and-contract'
assert git('rev-parse','refs/heads/codex/life-1-r1-validator-portability').decode().strip()==BASE
assert not (OUT/'START.json').exists(), 'Startup is one-time; retain prior evidence'
prompt=(EXT/'LIFE-1-R2_PROMPT.md').read_bytes(); prompt.decode('utf-8','strict')
(OUT/'PROMPT.md').write_bytes(prompt)
requirements=re.findall(r'^- ((?:L1-\d\d|INV-[A-Z-]+|CHK-[A-Z-]+|L1R[12]-[A-Z-]+)): ([^\r\n]+)',prompt.decode(),re.M)
assert len(requirements)==47 and len(dict(requirements))==47
old_path='docs/internal/extensions/lifecycle1/repair-r1/ACCEPTANCE_MATRIX.frozen.md'
old=git('show',BASE+':'+old_path); old.decode('utf-8','strict')
rows=[x for x in old.split(b'\n') if x.startswith(b'| `')]
assert len(rows)==45
for (name,req),row in zip(requirements[:45],rows):
    cells=row.decode().split('|')[1:-1]
    assert len(cells)==8 and all(x.strip() for x in cells)
    assert cells[0].strip()=='`'+name+'`' and cells[1].strip()==req
header=next(x for x in old.split(b'\n') if x.startswith(b'| ID |'))
separator=b'| --- | --- | --- | --- | --- | --- | --- | --- |'
matrix=b'# LIFE-1-R2 frozen acceptance matrix\n\nUses docs/internal/templates/PROOF_ACCEPTANCE_MATRIX.md. All 45 inherited complete rows are exact Git bytes at '+BASE.encode()+b'; historical Open cells remain immutable. New evidence is appended separately.\n\n'+header+b'\n'+separator+b'\n'+b'\n'.join(rows)+b'\n'
for name,req in requirements[45:]:
    cells=[f'`{name}`',req,'Local verification repair','Exact byte identities and source-bound bounded P/Q evidence under both declared shells.','Exact original checker or production Hash-Bytes -> unchanged callers -> current receipts -> coordinator review.','Challenge CRLF, tampered pins, one-byte/line-ending inputs and unavailable historical API; same-source positives precede challenges.','None at contract freeze; append observed outcomes separately.','Open; implementation and final verification required.']
    assert all('|' not in c for c in cells)
    matrix+=('| '+' | '.join(cells)+' |\n').encode()
matrix+=b'\n<!-- APPEND-ONLY-EVIDENCE -->\n'
for n in ['ACCEPTANCE_MATRIX.md','ACCEPTANCE_MATRIX.frozen.md']: (OUT/n).write_bytes(matrix)
write('CONTRACT.json',{'base':BASE,'prompt':ident(prompt),'originalFrozenGit':ident(old),'frozen':ident(matrix),'orderedIds':[x[0] for x in requirements],'requirements':[{'id':i,'requirement':r} for i,r in requirements]})
paths=[]
for entry in git('ls-tree','-rz',BASE).split(b'\0'):
    if not entry: continue
    meta,p=entry.split(b'\t',1); mode,kind,oid=meta.decode().split(); assert kind=='blob'
    paths.append((p.decode(),mode,oid))
objects=git('cat-file','--batch',) if False else subprocess.run(['git','cat-file','--batch'],input=('\n'.join(x[2] for x in paths)+'\n').encode(),cwd=ROOT,check=True,capture_output=True).stdout
offset=0; initial={}
for path,mode,oid in paths:
    end=objects.index(b'\n',offset); h=objects[offset:end].decode().split(); size=int(h[2]); blob=objects[end+1:end+1+size]; offset=end+2+size
    assert h[:2]==[oid,'blob']
    raw=(ROOT/path).read_bytes()
    initial[path]={'raw':ident(raw),'git':{'object':oid,'mode':mode,**ident(blob)},'rawEqualsGit':raw==blob,'rawIsExactCrlfTransform':raw==blob.replace(b'\n',b'\r\n')}
assert offset==len(objects)
write('INITIAL_FILES.json',initial)
r1=json.loads((ROOT/'docs/internal/extensions/lifecycle1/repair-r1/INITIAL_WORKING_FILES.json').read_bytes())
original={}
for n in ['CONTRACT_REQUIREMENTS.json','ACCEPTANCE_MATRIX.frozen.md','ACCEPTANCE_MATRIX.md']:
    p='docs/internal/extensions/lifecycle1/'+n; v=initial[p]
    assert v['raw']==r1[p] and v['rawIsExactCrlfTransform'] and not v['rawEqualsGit']
    original[p]=v
reviews={str(p):ident(p.read_bytes()) for p in [EXT/'life1-r1-review/DISPOSITION.md',EXT/'life1-r1-review/R2_PROMPT_REVIEW.md',EXT/'LIFE-1_PROMPT.md',EXT/'CAMPAIGN_PLAN.md']}
assert reviews[str(EXT/'life1-r1-review/DISPOSITION.md')]=={'bytes':17832,'sha256':'520d24e435ab007ee84a58ca6d0c36a93aca950ec998190d4e44535c89af4a79'}
shells=['C:/Users/poin/.cache/codex-runtimes/codex-primary-runtime/dependencies/native/powershell/pwsh.exe','C:/Windows/System32/WindowsPowerShell/v1.0/powershell.exe']
runtime={}
for shell in shells:
    cmd="[ordered]@{shell=(Get-Process -Id $PID).Path;version=$PSVersionTable.PSVersion.ToString();edition=$PSVersionTable.PSEdition;dotnet=[Environment]::Version.ToString()}|ConvertTo-Json -Compress"
    r=subprocess.run([shell,'-NoProfile','-Command',cmd],capture_output=True,check=True,timeout=30)
    assert not r.stderr
    runtime[shell]={**ident(Path(shell).read_bytes()),'observed':json.loads(r.stdout)}
tools={str(p):ident(p.read_bytes()) for p in [Path(sys.executable),Path('C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0/bin/lean.exe'),Path('C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0/bin/lake.exe')]}
write('START.json',{'handle':'LIFE-1-R2','title':'(LIFE-1-R2) Complete lifecycle verification portability','task':'01a0c23e-6fce-7542-b453-8fa7a741d7c9','root':str(ROOT),'base':BASE,'branch':'codex/life-1-r2-hash-and-contract','previousBranch':{'name':'codex/life-1-r1-validator-portability','commit':BASE},'initialClean':True,'initialCleanEvidence':'Exact HEAD/branch and empty porcelain observed twice before branch creation and before first file writes; Git ignore read warnings were on stderr only.','governance':'7b227c49ef2ec044b702126cc41c9add847eed01','preflight':json.loads((OUT/'PREFLIGHT.json').read_bytes()),'initialManifest':ident((OUT/'INITIAL_FILES.json').read_bytes()),'originalFiles':original,'externalSources':reviews,'runtime':runtime,'tools':tools,'materialization':'PENDING; requires actual old-checker failure first. Only the three authorized exact-base blobs may be written once before the new protected baseline.'})
print(json.dumps({'startup':'PASS','trackedFiles':len(initial),'inheritedRows':45,'totalRows':47,'prompt':ident(prompt),'frozen':ident(matrix),'originalFiles':original},indent=2))
