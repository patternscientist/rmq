"""Copy, never share, verified exact-source warm build artifacts."""
import hashlib
import json
import pathlib
import shutil
import subprocess

ROOT=pathlib.Path(__file__).resolve().parents[5]
HERE=pathlib.Path(__file__).resolve().parent
SOURCE=pathlib.Path('C:/Users/poin/.codex/worktrees/8941/RMQ')
BASE='12bd7f0fc2c87f2c9bdef3825bd92477e48e3433'

def git(root,*args):
    return subprocess.run(['git','-c','safe.directory='+root.as_posix(),'-c','core.excludesFile=',*args],
                          cwd=root,check=True,capture_output=True,timeout=30).stdout

def sha(path):
    h=hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda:f.read(1024*1024),b''): h.update(block)
    return h.hexdigest()

assert git(SOURCE,'rev-parse','HEAD').decode().strip()==BASE
assert not git(SOURCE,'status','--porcelain=v1')
assert not (ROOT/'.lake/build').exists(), 'Never overwrite a mutable build tree'
files=git(SOURCE,'ls-files','-z').decode().split('\0')[:-1]
source_pins={}
for name in files:
    if name.endswith('.lean') or name in ('lean-toolchain','lakefile.toml','lake-manifest.json'):
        source_bytes=(SOURCE/name).read_bytes()
        target_bytes=(ROOT/name).read_bytes()
        # A fresh Windows checkout may serialize the identical Git blob as CRLF.
        # Record that distinction; final builds, not this cache, certify target bytes.
        assert target_bytes.replace(b'\r\n',b'\n')==source_bytes.replace(b'\r\n',b'\n'), name
        source_pins[name]={'sourceWorking':sha(SOURCE/name),'targetWorking':sha(ROOT/name),
                          'gitBlob':git(ROOT,'rev-parse',BASE+':'+name).decode().strip()}
out=ROOT/'.lake/repair-r1'
out.mkdir(parents=True,exist_ok=True)
artifact_pins={}
for path in sorted((SOURCE/'.lake/build').rglob('*')):
    if not path.is_file(): continue
    relative=path.relative_to(SOURCE)
    target=ROOT/relative
    target.parent.mkdir(parents=True,exist_ok=True)
    before=sha(path)
    shutil.copy2(path,target)
    assert sha(target)==before==sha(path), str(path)
    artifact_pins[str(relative)]={'bytes':target.stat().st_size,'sha256':before}
assert not git(SOURCE,'status','--porcelain=v1')
assert sha(ROOT/'.lake/build/bin/rmq_lifecycle_validate.exe')=='4752591ec5a7d962e09440391aa38d0e2fc534b2f04775aab9c0c735e43ba99c'
manifest=out/'cache-manifest.json'
manifest.write_text(json.dumps({'sources':source_pins,'artifacts':artifact_pins},indent=2)+'\n',encoding='utf-8')
(HERE/'CACHE_PROVENANCE.json').write_text(json.dumps({'source':str(SOURCE),'target':str(ROOT),'base':BASE,
    'sourceCount':len(source_pins),'artifactCount':len(artifact_pins),'independentFiles':True,
    'manifest':str(manifest),'manifestBytes':manifest.stat().st_size,'manifestSha256':sha(manifest),
    'scope':'Exact source identity and copy integrity; final bounded builds still required.'},indent=2)+'\n',encoding='utf-8')
print('CACHE COPY VERIFIED',len(source_pins),'sources',len(artifact_pins),'artifacts')
