"""Prepare exact command specifications; execution is the bounded run_check.ps1."""
from pathlib import Path
import json, hashlib
ROOT=Path(__file__).resolve().parents[5]
HERE=Path(__file__).resolve().parent
OLD=HERE.parent/'repair-r1'
OUT=ROOT/'.lake/repair-r2'
SHELLS={'pwsh':'C:/Users/poin/.cache/codex-runtimes/codex-primary-runtime/dependencies/native/powershell/pwsh.exe','winps':'C:/Windows/System32/WindowsPowerShell/v1.0/powershell.exe'}
def spec(name,file,args,deadline,mutex=False):
    return {'name':name,'file':str(file),'arguments':[str(x) for x in args],'mutex':mutex,'deadline':deadline}
def ps(name,profile,file,args=(),deadline=180,mutex=False):return spec(name,SHELLS[profile],['-NoProfile','-ExecutionPolicy','Bypass','-File',file,*args],deadline,mutex)
def recipes():
    source=ROOT/'scripts/lifecycle_dependency_replay.ps1'
    change=json.loads((HERE/'HASH_CHANGE.json').read_bytes())
    assert hashlib.sha256(source.read_bytes()).hexdigest()==change['newSha256']
    entries=[]
    for profile,shell in SHELLS.items():
        for variant in ['old','current']:
            p=Path(change['oldRawSnapshot']) if variant=='old' else source
            sha=change['oldSha256'] if variant=='old' else change['newSha256']
            name=f'hash-{variant}-{profile}'
            entries.append(ps(name,profile,HERE/'hash_control.ps1',['-SourcePath',p,'-ExpectedSourceSha256',sha,'-OutputPath',OUT/(name+'.json')],60,True))
        entries.append(ps('positive-f01-'+profile,profile,OLD/'run_controls.ps1',['-Shell',shell,'-Profile',profile,'-OnlyCase','F01_INTACT_SUCCESS','-EvidenceRoot',OUT/('positive-f01-'+profile)],180))
        entries.append(ps('controls-'+profile,profile,OLD/'run_controls.ps1',['-Shell',shell,'-Profile',profile,'-EvidenceRoot',OUT/('controls-'+profile)],2700))
        entries.append(ps('registry-'+profile,profile,OLD/'registry_controls.ps1',['-Shell',shell,'-Profile',profile,'-EvidenceRoot',OUT/('registry-'+profile)],2700))
    for name,flags,mutex in [('dependency-selftest',['-SelfTestOnly'],True),('dependency-startup',['-StartupOnly'],False),('dependency-focused',['-OnlyCase','D15_CODE_FETCH_DROP'],False),('dependency-full',[],False)]:
        entries.append(ps(name,'pwsh',source,[*flags,'-DeadlineSeconds','120','-EvidenceDirectory','.lake/repair-r2/'+name],7200,mutex))
    entries.append(spec('default-build','C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0/bin/lake.exe',['build'],7200,True))
    entries.append(ps('final-original-contract','pwsh',ROOT/'scripts/lifecycle_contract_integrity.ps1',['-RepositoryRoot',ROOT,'-SourcePrompt','C:/Users/poin/Documents/RMQ/lifecycle-implementation-20260920/LIFE-1_PROMPT.md'],60))
    return entries
if __name__=='__main__':
    (OUT/'specs').mkdir(parents=True,exist_ok=True)
    for item in recipes():
        p=OUT/'specs'/(item['name']+'.json');data=(json.dumps(item,indent=2)+'\n').encode()
        if p.exists():assert p.read_bytes()==data, 'Existing spec differs: '+str(p)
        else:p.write_bytes(data)
    print('R2 prepared '+str(len(recipes()))+' exact specifications; no process launched')
