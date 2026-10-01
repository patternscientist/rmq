"""Read-only exact R2 protected-byte/Git scope verification; no restoration."""
from pathlib import Path
import argparse, hashlib, json, subprocess
ROOT=Path(__file__).resolve().parents[5]
HERE=Path(__file__).resolve().parent
BASE='0485a64920a273d0830b926ee46275085222819d'
PREFIX='docs/internal/extensions/lifecycle1/repair-r2/'
SCRIPT='scripts/lifecycle_dependency_replay.ps1'
WDD='docs/internal/WORKFLOW_DESIGN_DECISIONS.md'
ORIGINALS=['docs/internal/extensions/lifecycle1/'+s for s in ['CONTRACT_REQUIREMENTS.json','ACCEPTANCE_MATRIX.frozen.md','ACCEPTANCE_MATRIX.md']]
def ident(b):return {'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
def git(*a):return subprocess.run(['git',*a],cwd=ROOT,check=True,capture_output=True).stdout
def verify():
    initial=json.loads((HERE/'INITIAL_FILES.json').read_bytes());baseline=json.loads((HERE/'PROTECTED_BASELINE.json').read_bytes())
    assert set(initial)==set(baseline) and len(initial)==3751
    start=json.loads((HERE/'START.json').read_bytes());material=json.loads((HERE/'MATERIALIZATION.json').read_bytes());change=json.loads((HERE/'HASH_CHANGE.json').read_bytes())
    assert ident((HERE/'INITIAL_FILES.json').read_bytes())==start['initialManifest']
    assert ident((HERE/'PROTECTED_BASELINE.json').read_bytes())==material['postMaterializationBaseline']
    assert material['applied'] is True and len(material['files'])==3
    assert git('branch','--show-current').decode().strip()=='codex/life-1-r2-hash-and-contract'
    assert git('rev-parse','refs/heads/codex/life-1-r1-validator-portability').decode().strip()==BASE
    assert git('merge-base',BASE,'HEAD').decode().strip()==BASE
    for p,v in baseline.items():
        expected={k:initial[p]['git'][k] for k in ['bytes','sha256']} if p in ORIGINALS else initial[p]['raw']
        assert v==expected, 'Baseline substitution: '+p
    protected=[]
    for p,v in baseline.items():
        if p in [SCRIPT,WDD]:continue
        assert ident((ROOT/p).read_bytes())==v, 'Protected raw bytes changed: '+p
        protected.append(p)
    for p in ORIGINALS:
        exact=git('show',BASE+':'+p)
        assert (ROOT/p).read_bytes()==exact and ident(exact)==baseline[p]
        assert not git('diff',BASE,'--',p), 'Materialized Git content changed: '+p
    old=Path(change['oldRawSnapshot']).read_bytes(); current=(ROOT/SCRIPT).read_bytes()
    assert ident(old)==initial[SCRIPT]['raw']
    old_body=b'  return [Convert]::ToHexString([Security.Cryptography.SHA256]::HashData($bytes)).ToLowerInvariant()'
    new_body=b"  $hasher = [Security.Cryptography.SHA256]::Create()\r\n  try { return ([BitConverter]::ToString($hasher.ComputeHash($bytes))).Replace('-', '').ToLowerInvariant() }\r\n  finally { $hasher.Dispose() }"
    assert old.count(old_body)==1
    pos=old.index(old_body)
    assert current==old[:pos]+new_body+old[pos+len(old_body):], 'Edit outside exact Hash-Bytes body or predicate substitution'
    assert ident(current)['sha256']==change['newSha256']
    old_git=git('show',BASE+':'+SCRIPT)
    assert old.replace(b'\r\n',b'\n')==old_git, 'Old raw producer must map to immutable Git content; raw identity remains distinct'
    wdd=(ROOT/WDD).read_bytes();size=baseline[WDD]['bytes']
    assert ident(wdd[:size])==baseline[WDD] and len(wdd)>size, 'WDD prefix altered or no appended decision'
    committed={}
    for e in git('ls-tree','-rz','HEAD').split(b'\0'):
        if e:
            m,p=e.split(b'\t',1);committed[p.decode()]=m.decode().split()[2]
    for p,v in initial.items():
        if p in [SCRIPT,WDD]:continue
        assert committed[p]==v['git']['object'], 'Protected committed blob changed: '+p
    delta=set(git('diff','--name-only',BASE).decode().splitlines())
    delta.update(git('ls-files','--others','--exclude-standard').decode().splitlines())
    assert all(p in [SCRIPT,WDD] or p.startswith(PREFIX) for p in delta), 'Unexpected changed path: '+str(sorted(delta))
    return {'passed':True,'base':BASE,'head':git('rev-parse','HEAD').decode().strip(),'protectedRawCount':len(protected),'protectedRawEqual':True,'protectedGitObjectsEqual':True,'baselineFiles':len(baseline),'materializedExactGitFiles':ORIGINALS,'hashOnlyBodyChanged':True,'hashBodyOffset':pos,'hashOld':ident(old),'hashCurrent':ident(current),'wddInitialPrefixBytes':size,'wddAppendOnly':True,'changedPaths':sorted(delta),'workingPorcelain':git('status','--porcelain=v1').decode(),'scope':'No original restoration. Old raw CRLF and new Git-LF profiles remain separate; all other old raw bytes preserved.'}
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path);a=ap.parse_args();r=verify();b=(json.dumps(r,indent=2)+'\n').encode()
    if a.output:a.output.write_bytes(b)
    print(b.decode(),end='')
