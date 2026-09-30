"""Current source/tool bindings, separate from historical applicability and mutable report packaging."""
from pathlib import Path
import argparse, hashlib, json, re, subprocess
ROOT=Path(__file__).resolve().parents[5]
HERE=Path(__file__).resolve().parent
BASE='0485a64920a273d0830b926ee46275085222819d'
PRODUCTION='cb4739220c01e6554a25ff8333652c0501486fa8'
def ident(b):return {'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
def git(*a):return subprocess.run(['git',*a],cwd=ROOT,check=True,capture_output=True).stdout
def run(control):
    assert re.fullmatch(r'[0-9a-f]{40}',control), 'Control producer must be an exact commit'
    assert git('rev-parse',control+'^{commit}').decode().strip()==control
    assert git('merge-base',PRODUCTION,control).decode().strip()==PRODUCTION
    initial=json.loads((HERE/'INITIAL_FILES.json').read_bytes())
    start=json.loads((HERE/'START.json').read_bytes())
    paths=['scripts/lifecycle_dependency_replay.ps1','scripts/lifecycle_validator.ps1','scripts/lifecycle_validator_environment.ps1','scripts/lifecycle_contract_integrity.ps1','scripts/lifecycle_dependency_cases.json','scripts/owned_process_tree.ps1','lean-toolchain','lakefile.toml','scripts/lifecycle_inventory.lean','scripts/lifecycle_provenance_contract.lean','RMQ/Validation/LifecycleContract.lean','RMQ/Validation/PackedLifecycle.lean']
    paths += [p for p in initial if p.startswith('docs/internal/extensions/lifecycle1/repair-r1/') and Path(p).suffix in ['.ps1','.json','.py']]
    paths += [p.relative_to(ROOT).as_posix() for p in HERE.iterdir() if p.suffix in ['.py','.ps1']]
    immutable=['PROMPT.md','PREFLIGHT.json','START.json','INITIAL_FILES.json','PROTECTED_BASELINE.json','MATERIALIZATION.json','HASH_CHANGE.json','HASH_VECTORS.json','CONTRACT.json','ACCEPTANCE_MATRIX.frozen.md']
    paths += [(HERE/p).relative_to(ROOT).as_posix() for p in immutable]
    records=[]
    for p in sorted(set(paths)):
        raw=(ROOT/p).read_bytes();ref=control if p.startswith(HERE.relative_to(ROOT).as_posix()+'/') else (PRODUCTION if p=='scripts/lifecycle_dependency_replay.ps1' else BASE)
        blob=git('show',ref+':'+p);oid=git('rev-parse',ref+':'+p).decode().strip()
        assert raw.replace(b'\r\n',b'\n')==blob, 'Source content differs from frozen producer: '+p
        if p in initial and p!='scripts/lifecycle_dependency_replay.ps1':assert ident(raw)==initial[p]['raw']
        records.append({'path':p,'producingCommit':ref,'gitObject':oid,'gitBytes':ident(blob),'currentRaw':ident(raw),'rawEqualsGit':raw==blob,'relation':'Exact raw identity recorded; LF/CRLF serialization compared to immutable Git content separately, never asserted byte-equal when different.'})
    tools=[]
    for path,want in start['tools'].items():
        got=ident(Path(path).read_bytes());assert got==want;tools.append({'path':path,**got})
    for path,want in start['runtime'].items():
        got=ident(Path(path).read_bytes());assert got=={k:want[k] for k in ['bytes','sha256']};tools.append({'path':path,**got,'observedRuntime':want['observed']})
    exe=ROOT/'.lake/build/bin/rmq_lifecycle_validate.exe';assert ident(exe.read_bytes())['sha256']=='4752591ec5a7d962e09440391aa38d0e2fc534b2f04775aab9c0c735e43ba99c'
    return {'schema':'life1-r2-source-freeze-v1','base':BASE,'productionCommit':PRODUCTION,'controlCommit':control,'sources':records,'tools':tools,'nativeExecutable':{'path':str(exe),**ident(exe.read_bytes())},'historyApplicability':{'path':'HISTORY_APPLICABILITY.json',**ident((HERE/'HISTORY_APPLICABILITY.json').read_bytes())},'coverage':'All old tracked raw sources and actual cache/artifact closure are separately exhaustively checked by verify_scope.py and verify_history.py. This manifest records executed scripts, registries, formal consumers and current evidence-generator code at immutable producing commits. Final report/rows/active matrix/WDD and delivery are packaging and have separate final pins.'}
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--control-commit');ap.add_argument('--check',action='store_true');a=ap.parse_args();out=HERE/'SOURCE_FREEZE.json'
    control=a.control_commit or json.loads(out.read_bytes())['controlCommit'];value=run(control);data=(json.dumps(value,indent=2)+'\n').encode()
    if a.check:assert out.read_bytes()==data, 'Frozen source manifest changed'
    else:out.write_bytes(data)
    print(json.dumps({'passed':True,'sources':len(value['sources']),'tools':len(value['tools']),'output':str(out),**ident(data)},indent=2))
