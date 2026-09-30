"""Replay the unchanged checker on four scratch roots; optionally perform authorized setup once."""
from pathlib import Path
import argparse, hashlib, json, subprocess
ROOT=Path(__file__).resolve().parents[5]
HERE=Path(__file__).resolve().parent
BASE='0485a64920a273d0830b926ee46275085222819d'
SHELL='C:/Users/poin/.cache/codex-runtimes/codex-primary-runtime/dependencies/native/powershell/pwsh.exe'
ORIGINAL='C:/Users/poin/Documents/RMQ/lifecycle-implementation-20260920/LIFE-1_PROMPT.md'
NAMES=['CONTRACT_REQUIREMENTS.json','ACCEPTANCE_MATRIX.frozen.md','ACCEPTANCE_MATRIX.md']
PREFIX='docs/internal/extensions/lifecycle1/'
def ident(b):return {'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
def save(p,v):p.write_bytes((json.dumps(v,indent=2)+'\n').encode())
def blob(path):return subprocess.run(['git','show',BASE+':'+path],cwd=ROOT,capture_output=True,check=True).stdout
def check(name,root):
    spec={'name':name,'file':SHELL,'arguments':['-NoProfile','-File',str(ROOT/'scripts/lifecycle_contract_integrity.ps1'),'-RepositoryRoot',str(root),'-SourcePrompt',ORIGINAL],'mutex':False,'deadline':60}
    p=ROOT/'.lake/repair-r2/specs'/f'{name}.json'; assert not p.exists();save(p,spec)
    completed=subprocess.run([SHELL,'-NoProfile','-File',str(HERE/'run_check.ps1'),'-SpecPath',str(p)],cwd=ROOT,capture_output=True,timeout=90)
    rp=ROOT/'.lake/repair-r2/checks'/name/'result.json'; r=json.loads(rp.read_bytes())['result']
    assert completed.returncode==r['ExitCode'] and not completed.stderr
    assert not r['TimedOut'] and not r['OutputLimitExceeded'] and r['Ownership']=='kill-on-close-job' and not r['TerminatedIds'] and not r['StandardError']
    return {'receipt':str(rp),**ident(rp.read_bytes()),'result':r}
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--apply-once',action='store_true');ap.add_argument('--run-name',required=True);a=ap.parse_args()
    assert a.run_name and all(c in 'abcdefghijklmnopqrstuvwxyz0123456789-' for c in a.run_name)
    evidence=ROOT/'.lake/repair-r2'/a.run_name; evidence.mkdir(parents=True,exist_ok=False)
    initial=json.loads((HERE/'INITIAL_FILES.json').read_bytes()); old=json.loads((ROOT/(PREFIX+'repair-r1/INITIAL_WORKING_FILES.json')).read_bytes())
    data={}; identities={}
    for name in NAMES:
        path=PREFIX+name; exact=blob(path); raw=exact.replace(b'\n',b'\r\n')
        assert b'\r' not in exact and ident(raw)==initial[path]['raw']==old[path]
        assert ident(exact)=={k:initial[path]['git'][k] for k in ['bytes','sha256']}
        data[name]=(raw,exact);identities[path]={'initial':ident(raw),'git':ident(exact),'gitObject':initial[path]['git']['object'],'transformation':'Exact LF byte -> CRLF byte sequence at every LF; no other byte difference'}
    records=[]
    expected=['CONTRACT_HASH: frozen source/requirements JSON changed','HEADER: frozen baseline requires the exact eight-column header','HEADER: candidate matrix requires the exact eight-column header']
    for count in range(4):
        scratch=evidence/f'git-files-{count}'; dest=scratch/PREFIX;dest.mkdir(parents=True)
        for i,name in enumerate(NAMES):(dest/name).write_bytes(data[name][1 if i<count else 0])
        r=check(a.run_name+f'-{count}',scratch); result=r['result']
        if count<3:
            assert result['ExitCode']==1 and result['StandardOutput']==['LIFECYCLE-CONTRACT: FAIL '+expected[count]]
        else:
            assert result['ExitCode']==0 and len(result['StandardOutput'])==4 and result['StandardOutput'][0]=='LIFECYCLE-CONTRACT: PASS rows=43 columns=8 changed_ids=[]'
        r['gitFiles']=count;r['scratchRoot']=str(scratch);records.append(r)
    receipt={'base':BASE,'checker':ident((ROOT/'scripts/lifecycle_contract_integrity.ps1').read_bytes()),'sourcePrompt':ident(Path(ORIGINAL).read_bytes()),'files':identities,'controls':records,'positiveCount':1,'negativeCount':3,'applied':False}
    save(evidence/'result.json',receipt)
    if a.apply_once:
        assert not (HERE/'MATERIALIZATION.json').exists() and not (HERE/'PROTECTED_BASELINE.json').exists()
        # All live files are checked before any live byte write. A mismatch stops; no repair occurs.
        for name in NAMES: assert (ROOT/(PREFIX+name)).read_bytes()==data[name][0], 'Live initial bytes differ; stop before setup'
        old_failure=json.loads((ROOT/'.lake/repair-r2/checks/initial-original-contract/result.json').read_bytes())['result']
        assert old_failure['ExitCode']==1 and old_failure['StandardOutput']==['LIFECYCLE-CONTRACT: FAIL CONTRACT_HASH: frozen source/requirements JSON changed'] and not old_failure['StandardError'] and not old_failure['TimedOut'] and not old_failure['OutputLimitExceeded']
        intent={**receipt,'operation':'Explicit one-time three-file exact-base Git-blob materialization authorized by frozen LIFE-1-R2 prompt; not runtime finalizer restoration','initialFailureReceipt':str(ROOT/'.lake/repair-r2/checks/initial-original-contract/result.json')}
        save(evidence/'materialization-intent.json',intent)
        for name in NAMES:(ROOT/(PREFIX+name)).write_bytes(data[name][1])
        for name in NAMES:assert (ROOT/(PREFIX+name)).read_bytes()==data[name][1]
        diff=subprocess.run(['git','diff',BASE,'--',*[PREFIX+n for n in NAMES]],cwd=ROOT,capture_output=True,check=True)
        assert not diff.stdout, 'Materialized Git content changed'
        live=check(a.run_name+'-live',ROOT)
        assert live['result']['ExitCode']==0 and live['result']['StandardOutput'][0]=='LIFECYCLE-CONTRACT: PASS rows=43 columns=8 changed_ids=[]'
        baseline={p:ident((ROOT/p).read_bytes()) for p in initial}
        for p,v in baseline.items(): assert v==(identities[p]['git'] if p in identities else initial[p]['raw'])
        save(HERE/'PROTECTED_BASELINE.json',baseline)
        receipt.update({'applied':True,'operation':intent['operation'],'livePositive':live,'gitContentDiff':'','postMaterializationBaseline':ident((HERE/'PROTECTED_BASELINE.json').read_bytes())})
        save(HERE/'MATERIALIZATION.json',receipt)
        start=json.loads((HERE/'START.json').read_bytes());start['materialization']={'receipt':'MATERIALIZATION.json',**ident((HERE/'MATERIALIZATION.json').read_bytes()),'postBaseline':'PROTECTED_BASELINE.json','postBaselineIdentity':receipt['postMaterializationBaseline']};save(HERE/'START.json',start)
    print(json.dumps({'passed':True,'applied':receipt['applied'],'positiveCount':1,'negativeCount':3,'evidence':str(evidence)},indent=2))
if __name__=='__main__':main()
