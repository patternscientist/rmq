"""Bind complete R2 executions to exact production/control source and retain failed history."""
from pathlib import Path
import argparse, hashlib, importlib.util, json, re, subprocess, sys
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[5]
HERE=Path(__file__).resolve().parent
OLD=HERE.parent/'repair-r1'
E=ROOT/'.lake/repair-r2'
BASE='0485a64920a273d0830b926ee46275085222819d'
PRODUCTION='cb4739220c01e6554a25ff8333652c0501486fa8'
SCRIPT='scripts/lifecycle_dependency_replay.ps1'
FILES={}
SHELLS={'pwsh':'C:/Users/poin/.cache/codex-runtimes/codex-primary-runtime/dependencies/native/powershell/pwsh.exe','winps':'C:/Windows/System32/WindowsPowerShell/v1.0/powershell.exe'}
RUNTIME={'pwsh':('7.6.5','10.0.11','Core'),'winps':('5.1.26100.9444','4.0.30319.42000','Desktop')}
LEAN=Path('C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0/bin/lean.exe')
def shell_equal(actual,profile):assert Path(actual).resolve()==Path(SHELLS[profile]).resolve()
def runtime(actual,profile,pathkey='shell'):
    shell_equal(actual[pathkey],profile)
    assert (actual['version'],actual['dotnet'],actual['edition'])==RUNTIME[profile]
def pin(p):
    p=Path(p).resolve();b=p.read_bytes();v={'path':str(p),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()};FILES[str(p)]=v;return v
def read(p):pin(p);return json.loads(Path(p).read_bytes())
def sha(p):return pin(p)['sha256']
def git(*a):return subprocess.run(['git',*a],cwd=ROOT,capture_output=True,check=True).stdout
def process(r,exit=0,timeout=False):
    assert r['TimedOut'] is timeout and not r['OutputLimitExceeded'] and r['Ownership']=='kill-on-close-job'
    assert r['DeadlineSeconds']>0 and r['DurationSeconds']>=0
    if not timeout:assert r['ExitCode']==exit and r['TerminatedIds']==[]
def current_pins(pins):
    for p,v in pins.items():assert sha(ROOT/p)==v.lower(), 'Current source pin differs: '+p
def only(items):
    items=list(items);assert len(items)==1, items;return items[0]
def safe_evidence(p):
    p=Path(p).resolve();p.relative_to((ROOT/'.lake').resolve());return p
def check(name,expected=0,old=False):
    p=E/'checks'/name/'result.json';v=read(p);r=v['result'];process(r,expected)
    assert v['spec']['name']==name and r['Stage']==name
    if name in RECIPES:assert v['spec']==RECIPES[name], 'Actual command differs from frozen recipe: '+name
    for path,value in v['sources'].items():
        expect=INITIAL[path]['raw']['sha256'] if old and path==SCRIPT else sha(ROOT/path)
        assert value.lower()==expect
    inv=v['invocation'];assert inv['head'] in [BASE,PRODUCTION] or git('merge-base',PRODUCTION,inv['head']).decode().strip()==PRODUCTION
    assert inv['driverSha256'].lower()==sha(HERE/'run_check.ps1')
    assert inv['executableSha256'].lower()==sha(v['spec']['file']) and inv['hostSha256'].lower()==sha(v['shell'])
    for path,value in inv['argumentFilePins'].items():assert sha(path)==value.lower()
    spec_path=E/'specs'/(name+'.json');assert sha(spec_path)==inv['specSha256'].lower() and read(spec_path)==v['spec']
    assert (E/'checks'/name/'stdout.txt').read_bytes()=='\n'.join(r['StandardOutput']).encode()
    assert (E/'checks'/name/'stderr.txt').read_bytes()=='\n'.join(r['StandardError']).encode()
    CHECKS.append({'name':name,'receipt':pin(p),'producingHead':inv['head'],'exit':r['ExitCode'],'expectedExit':expected,'seconds':r['DurationSeconds'],'deadline':r['DeadlineSeconds'],'passed':True,'sourcePins':v['sources']})
    return v
def hash_controls():
    vectors=read(HERE/'HASH_VECTORS.json');assert sha(HERE/'HASH_VECTORS.json')=='6e2f6e3592a715b0dc497184ef38a7345827d9d8f834f7729a143c314ff67080'
    expected=[]
    for v in vectors['vectors']:
        b=bytes.fromhex(v['hex']);assert len(b)==v['bytes'] and hashlib.sha256(b).hexdigest()==v['sha256'];expected.append(v['id'])
    receipts=[]
    for variant,profile in [('old','pwsh'),('old','winps'),('current','pwsh'),('current','winps')]:
        name=f'hash-{variant}-{profile}';failure=variant=='old' and profile=='winps';c=check(name,7 if failure else 0);p=E/(name+'.json');r=read(p)
        runtime(r,profile);shell_equal(c['spec']['file'],profile)
        assert c['spec']['arguments'][c['spec']['arguments'].index('-SourcePath')+1]==r['sourcePath']
        assert r['selected']==expected and r['sourceSha256']==CHANGE['oldSha256' if variant=='old' else 'newSha256']
        assert sha(r['sourcePath'])==r['sourceSha256'] and sha(r['spanPath'])==r['spanSha256']
        raw=Path(r['sourcePath']).read_bytes();assert raw[r['spanStartByte']:r['spanStartByte']+r['spanBytes']]==Path(r['spanPath']).read_bytes()
        assert r['harnessSha256'].lower()==sha(HERE/'hash_control.ps1') and r['shellSha256'].lower()==sha(r['shell'])
        assert r['vectorsSha256']==sha(HERE/'HASH_VECTORS.json')
        if failure:
            message="Method invocation failed because [System.Security.Cryptography.SHA256] does not contain a method named 'HashData'."
            assert not r['passed'] and r['error']==message and r['results']==[] and c['result']['StandardOutput']==[] and c['result']['StandardError']==[message]
        else:
            assert r['passed'] and r['error'] is None and c['result']['StandardError']==[] and c['result']['StandardOutput']==['L1R2-HASH PASS vectors=8 distinctions=3']
            assert [x['id'] for x in r['results']]==expected
            for v,x in zip(vectors['vectors'],r['results']):assert x['passed'] and x['inputHex']==v['hex'] and x['actual']==x['expected']==v['sha256']
        receipts.append(pin(p))
    return {'passed':True,'vectorCount':8,'successfulProfiles':['old-pwsh','current-pwsh','current-winps'],'oldWinFailureExact':True,'distinctions':3,'independentOracle':'Python hashlib.sha256 over fixed exact hex bytes, Unicode UTF-8 and one-byte/LF-CRLF pairs','receipts':receipts}
def materialization():
    initial=check('initial-original-contract',1,True)
    assert initial['result']['StandardOutput']==['LIFECYCLE-CONTRACT: FAIL CONTRACT_HASH: frozen source/requirements JSON changed'] and initial['result']['StandardError']==[]
    material=read(HERE/'MATERIALIZATION.json');assert material['applied'] and material['negativeCount']==3 and material['positiveCount']==1
    exact_errors=['CONTRACT_HASH: frozen source/requirements JSON changed','HEADER: frozen baseline requires the exact eight-column header','HEADER: candidate matrix requires the exact eight-column header']
    for i,record in enumerate(material['controls']):
        result=check('materialization-'+str(i),1 if i<3 else 0,True)
        assert result['result']==record['result'] and sha(record['receipt'])==record['sha256']
        assert not result['result']['StandardError']
        if i<3:assert result['result']['StandardOutput']==['LIFECYCLE-CONTRACT: FAIL '+exact_errors[i]]
        else:assert result['result']['StandardOutput'][0]=='LIFECYCLE-CONTRACT: PASS rows=43 columns=8 changed_ids=[]'
    live=check('materialization-live',0,True)
    assert live['result']==material['livePositive']['result'] and live['result']['StandardOutput'][0]=='LIFECYCLE-CONTRACT: PASS rows=43 columns=8 changed_ids=[]'
    final=check('final-original-contract');assert final['result']['StandardOutput'][0]==live['result']['StandardOutput'][0] and not final['result']['StandardError']
    return {'passed':True,'initialFailureExact':True,'negativeCount':3,'positiveCount':1,'livePassed':True,'receipt':pin(HERE/'MATERIALIZATION.json'),'files':material['files']}
def old_f01():
    c=check('old-winps-f01',1,True);s=read(E/'old-winps-f01/summary.json')
    assert s['selected']==['F01_INTACT_SUCCESS'] and s['results']==[] and not s['passed']
    leaf=only((E/'old-winps-f01/F01_INTACT_SUCCESS/fixtures').glob('F01*/result.json'));r=read(leaf)
    assert not r['passed'] and r['records']==[] and r['source']['sourceSha256']==CHANGE['oldSha256']
    p=read(leaf.parent/'P/process.json');process(p,1)
    message="Method invocation failed because [System.Security.Cryptography.SHA256] does not contain a method named 'HashData'."
    assert p['StandardOutput']==[] and p['StandardError']==[message]
    observed=read(leaf.parent/'P/production-evidence/fixture-finally-entry.json')
    assert observed['baselineCount']==0
    return {'passedAsExpectedHistoricalFailure':True,'actualProductionPositivePassed':False,'failedBeforePinCapture':True,'receipt':pin(leaf),'sourceSha256':CHANGE['oldSha256']}
def finalizer(leaf,case,profile,current=True):
    r=read(leaf);assert r['passed'] and len(r['records'])==2 and r['error'] is None
    assert r['id']==case['id'] and r['expected']==case['spec']
    source=r['source'];assert source['harnessSha256']==sha(OLD/'finalizer_control.ps1')
    assert source['sourceVariant']==case['spec']['sourceVariant'];shell_equal(source['shell'],profile)
    assert source['shellSha256']==sha(source['shell']) and source['helperSha256']==sha(ROOT/'scripts/owned_process_tree.ps1')
    assert source['workingProductionSha256']==CHANGE['newSha256']
    source_path=leaf.parent/'production.source.ps1';assert sha(source_path)==source['sourceSha256']
    if current:assert source['sourceSha256']==CHANGE['newSha256']
    else:assert source_path.read_bytes()==git('show','12bd7f0fc2c87f2c9bdef3825bd92477e48e3433:'+SCRIPT)
    raw=source_path.read_bytes()
    for part in source['pieces']:
        assert sha(part['path'])==part['sha256'] and Path(part['path']).read_bytes()==raw[part['startByte']:part['startByte']+part['byteLength']]
    assert sha(leaf.parent/'child.ps1')==r['childSourceSha256']
    for role,x in zip(['P','Q'],r['records']):
        assert x['role']==role and x['passed'] and x['requestedChildAbsent'] and x['rootAbsent'] and x['mutexReleasedWithoutAbandonment']
        shell_equal(x['runtime']['shell'],profile)
        assert x['runtime']['psVersion']==RUNTIME[profile][0] and x['runtime']['clrVersion']==RUNTIME[profile][1]
        assert x['runtime']['sourceSha256']==source['sourceSha256']
        process(x['process'],0 if role=='P' else r['expected']['expectedExit'])
        assert x['fixture']['enteredMain'] and x['restoration']['ownedPinRestored'] and x['restoration']['ownedSecondPinRestored'] and x['restoration']['lockDisposed']
        if role=='P':assert x['fixture']['baselineCount']==2 and x['summary']['passed'] and x['summary']['restored'] and x['summary']['shadowRemoved']
        else:
            expected=case['spec'];assert x['mode']==expected['mode'] and x['fixture']['baselineCount']==expected['baselineCount']
            assert x['summary']['passed']==(expected['expectedExit']==0) and x['summary']['restored']==(not expected['integrityFailure']) and x['summary']['shadowRemoved']==expected['shadowRemoved']
            if current:
                for field,flag in [('stageError','stageFailure'),('integrityError','integrityFailure'),('cleanupError','cleanupFailure')]:assert (x['summary'][field] is not None)==expected[flag]
                errors=[]
                if expected['stageFailure']:
                    message='L1R1-FIXTURE: capture-stage failure after one pin' if expected['mode'] in ['partial','partial-and-pin'] else 'L1R1-FIXTURE: prior stage failure'
                    assert x['summary']['stageError']==message;errors.append(message)
                if expected['integrityFailure']:
                    message='LIFE1-RESTORATION: original bytes changed: '+str(leaf.parent/'Q/captured-pin.txt');assert x['summary']['integrityError']==message;errors.append(message)
                    assert x['fixture']['pinBeforeRestore']=='changed captured fixture'
                if expected['cleanupFailure']:
                    message=x['summary']['cleanupError']
                    if expected['mode'] in ['outside','basename']:
                        assert message=='LIFE1-CLEANUP: shadow path escaped evidence root' and x['fixture']['sentinelPresent'] and x['fixture']['sentinelText']=='owned shadow sentinel'
                    else:
                        assert x['fixture']['lockAcquired']
                        assert message in ["The process cannot access the file '"+str(leaf.parent/'Q/production-evidence/shadow/locked.txt')+"' because it is being used by another process.","The process cannot access the file 'locked.txt' because it is being used by another process."]
                    errors.append(message)
                assert x['process']['StandardError']==errors
            assert x['process']['StandardOutput']==(['LIFE1-DEPENDENCY PASS '+str(leaf.parent/'Q/production-evidence')] if expected['expectedExit']==0 else [])
    return r
def controls(profile,focused=False):
    name=('positive-f01-' if focused else 'controls-')+profile;c=check(name)
    root=E/name;s=read(root/'summary.json');selected=[x for x in REGISTRY['cases'] if profile in x['profiles'] and (not focused or x['id']=='F01_INTACT_SUCCESS')]
    assert s['passed'] and s['selected']==[x['id'] for x in selected] and [x['id'] for x in s['results']]==s['selected']
    assert s['registrySha256']==sha(OLD/'CONTROL_REGISTRY.json') and s['shellSha256'].lower()==sha(s['shell']);current_pins(s['sourcePins'])
    runtime(s['runtime'],profile,'path');shell_equal(c['spec']['file'],profile);shell_equal(s['shell'],profile)
    assert not c['result']['StandardError'] and c['result']['StandardOutput']==['L1R1 CASE '+x['id']+' PASS' for x in selected]+['L1R1 CONTROLS PASS '+str(root)]
    records=[]
    for case,result in zip(selected,s['results']):
        path=root/case['id'];assert result['passed'];outer=read(path/'process.json');process(outer)
        assert not outer['StandardError'] and len(outer['StandardOutput'])==1
        if case['kind']=='finalizer':
            leaf=only((path/'fixtures').glob(case['id']+'-*/result.json'));r=finalizer(leaf,case,profile,case['id']!='F00_OLD_CHANGED_PIN');positive,negative=r['records']
            assert outer['StandardOutput']==['L1R1-FINALIZER CONTROL PASS '+case['id']+' '+str(leaf.parent)]
        elif case['kind']=='deadline':
            leaf=path/'fixture/result.json';r=read(leaf);assert r['passed'] and r['allObservedAbsent'] and r['environmentRestored'];process(r['result'],timeout=True)
            assert r['result']['TerminatedIds'] and r['pids']['root']!=r['pids']['descendant']
            positive={'scope':'Owned actual root and descendant were launched','pids':r['pids']};negative=r
            assert outer['StandardOutput']==['L1R1-CONTROL|'+case['id']+'|PASS']
        else:
            leaf=path/'fixture/receipt.json';r=read(leaf);assert r['passed'] and r['id']==case['id'] and r['restored']
            shell_equal(r['shell'],profile);assert r['version']==RUNTIME[profile][0] and r['dotnet']==RUNTIME[profile][1]
            assert outer['StandardOutput']==['L1R1-CONTROL|'+case['id']+'|PASS']
            if 'spec' in r:assert r['spec']==case['spec']
            positive=r.get('positive',{'scope':'This registered positive case is its own accepted control','result':r.get('result')});negative=r
            if case['kind'].startswith('dependency'):
                assert r['sourceSha256'].lower()==CHANGE['newSha256']==r['copiedSourceSha256'].lower()
                assert r['positive']['exit']==0 and r['positive']['stderr']=='' and len(r['positive']['stdout'])==1
                expected=case['spec']['legacyExpected'] if profile=='winps' and case['id']=='D13_PRESENT_EMPTY' else case['spec']['expected']
                assert r['exit']==expected['exit']
                if case['id']=='D12_DUPLICATE_ARGUMENT':assert r['errorId']=='ParameterAlreadyBound,lifecycle_dependency_replay.ps1' and r['stdout']==[] and r['stderr']==''
                elif expected['exit']==0:assert r['stdout']==[expected['output']] and r['stderr']=='' and r['exception'] is None
                else:assert r['stdout']==[] and r['stderr']==expected['error']+'\r\n' and r['exception'] is None
            elif case['kind']=='native':
                process(r['result'],case['spec']['expected']['exit'] if case['id']!='S04_PRESENT_EMPTY_REGISTRY' or profile!='winps' else 0)
                if 'positive' in r and 'result' in r['positive']:process(r['positive']['result'])
                if case['spec']['expected']['exit']!=0 and not (case['id']=='S04_PRESENT_EMPTY_REGISTRY' and profile=='winps'):
                    assert r['result']['StandardOutput']==[] and r['result']['StandardError']==([] if case['spec']['expected']['error'] is None else [case['spec']['expected']['error']])
            if case['kind']=='wrapper' and 'positive' in r:
                pr=r['positive']['receipt'];assert pr['stage']=='startup' and pr['processCount']==2 and pr['identityPreserved']
                for p in safe_evidence(r['positive']['logRoot']).rglob('*'):
                    if p.is_file():pin(p)
            if case['kind']=='wrapper' and 'productionLogRoot' in r:
                production_log=safe_evidence(r['productionLogRoot']);actual=read(production_log/'PASS.json')
                assert actual['identityPreserved'] and actual['stage']==case['spec']['parameters']['Stage']
                for p in production_log.rglob('*'):
                    if p.is_file():pin(p)
        records.append({'id':case['id'],'kind':case['kind'],'handler':case['handler'],'mapping':case['spec'],'passed':True,'receipt':pin(leaf),'positive':positive,'negative':negative})
    return {'passed':True,'selected':s['selected'],'results':records,'receipt':pin(root/'summary.json'),'sourcePins':s['sourcePins']}
def registry_controls(profile):
    c=check('registry-'+profile);p=E/('registry-'+profile)/'summary.json';s=read(p);expected=read(OLD/'registry_control_cases.json')
    assert s['passed'] and s['sourcesUnchanged'] and s['stageError'] is None and s['integrityError'] is None and s['semanticCasesExecuted']==0
    assert s['selected']==[x['id'] for x in expected['cases']]==[x['id'] for x in s['results']];current_pins(s['sourcePins'])
    runtime(s['runtime'],profile,'path');shell_equal(s['shell'],profile);shell_equal(c['spec']['file'],profile)
    for case,x in zip(expected['cases'],s['results']):
        assert x['passed'] and x['mutation']==case['mutation'] and x['production']==case['production']
        for label in ['positive','challenged']:
            y=x[label];positive=label=='positive';assert y['passed'] and y['childAbsent'] and y['label']==('P' if positive else 'Q')
            mode=case['positiveSelector'] if positive else case['expected']['stdout']
            wanted_output='' if mode=='empty' else 'L1R1 SELECT '+(','.join(expected['expectedProfiles'][profile]) if mode=='full' else 'S01_ABSENT_REGISTRY')
            wanted_exit=0 if positive else case['expected']['exit'];wanted_error='' if positive else (case['expected']['error'] or '')
            assert y['expectedExit']==wanted_exit and y['expectedOutput']==wanted_output and y['expectedError']==wanted_error
            process_result=read(y['processReceipt']);process(process_result,wanted_exit)
            assert process_result['StandardOutput']==([wanted_output] if wanted_output else []) and process_result['StandardError']==([wanted_error] if wanted_error else [])
            wanted_selector={'present':mode=='one','value':'S01_ABSENT_REGISTRY' if mode=='one' else None} if positive else case['selector']
            assert y['selector']==wanted_selector;shell_equal(y['actualRuntime'],profile)
            opposite='winps' if profile=='pwsh' else 'pwsh';challenge=None if positive else case.get('runtimeChallenge')
            assert y['declaredProfile']==(opposite if challenge=='opposite-profile' else profile)
            shell_equal(y['suppliedShell'],opposite if challenge=='opposite-shell' else profile)
            assert y['runtimeHelperSha256'].lower()==sha(OLD/'runtime_profile.ps1')
    return {'passed':True,'selected':s['selected'],'results':s['results'],'receipt':pin(p)}
def dependency(name):
    c=check('dependency-'+name);line=c['result']['StandardOutput'][-1];assert line.startswith('LIFE1-DEPENDENCY PASS ')
    folder=safe_evidence(line[len('LIFE1-DEPENDENCY PASS '):]);s=read(folder/'summary.json')
    assert s['passed'] and s['restored'] and s['shadowRemoved'] and all(s[k] is None for k in ['stageError','integrityError','cleanupError']) and not (folder/'shadow').exists()
    assert s['registrySha256']=='4c9c7a4259808bb64c74656fd52559752e76f02834f2ac8567f5830968a5b80d'
    if name=='selftest':
        t=read(folder/'selftest.json');assert t['registry'] and t['selectors'] and t['mixedDiagnostics'] and t['ownedDeadline'];process(t['result'],timeout=True)
        return {'passed':True,'receipt':pin(folder/'summary.json'),'scope':'Empty original baseline in self-test; real descendant timeout observed; not whole-tree integrity'}
    expected=DEPS['cases'] if name=='full' else [x for x in DEPS['cases'] if x['id'] in (['D20_ACCEPT_IDENTITY','P06_ACCEPT_IDENTITY'] if name=='startup' else ['D15_CODE_FETCH_DROP'])]
    assert s['selected']==[x['id'] for x in expected] and [x['id'] for x in s['cases']]==s['selected']
    baseline=read(folder/'baseline.json')
    original_paths=list(dict.fromkeys([SCRIPT,'scripts/lifecycle_dependency_cases.json','scripts/owned_process_tree.ps1','lean-toolchain']+[x['producer'] for x in DEPS['cases']]+[x['consumer'] for x in DEPS['cases']]))
    expected_baseline=[]
    for p in original_paths:
        expected_baseline.append((ROOT/p).resolve())
        if p.startswith('RMQ/'):expected_baseline.append((ROOT/'.lake/build/lib/lean'/Path(p).with_suffix('.olean')).resolve())
    expected_baseline.append(LEAN.resolve())
    assert [Path(b['path']).resolve() for b in baseline]==expected_baseline and len(set(expected_baseline))==len(expected_baseline), 'Complete nonempty capture roster required'
    for b in baseline:assert sha(b['path'])==b['sha256']
    rows=[]
    for case,row in zip(expected,s['cases']):
        assert row['expected']==case['expected'] and row['restored'] and row['privateRestored']
        producer=(ROOT/case['producer']).read_bytes().decode('utf-8').replace('\r\n','\n')
        for edit in case['edits']:
            assert producer.count(edit['before'])==1;producer=producer.replace(edit['before'],edit['after'])
        client=(ROOT/case['consumer']).read_bytes().decode('utf-8').replace('\r\n','\n')
        assert hashlib.sha256(producer.encode()).hexdigest()==row['producerSourceHash'] and hashlib.sha256(client.encode()).hexdigest()==row['consumerHash']
        a=read(folder/(case['id']+'-producer.json'));b=read(folder/(case['id']+'-consumer.json'));process(a['result']);process(b['result'],0 if case['expected']=='accept' else 1)
        assert a['stage']==a['result']['Stage']==case['id']+'-producer' and b['stage']==b['result']['Stage']==case['id']+'-consumer'
        assert Path(a['executable']).resolve()==Path(b['executable']).resolve()==LEAN.resolve()
        case_root=folder/'shadow'/case['id'];imports=folder/'shadow/imports';artifact=imports/Path(case['producer']).with_suffix('.olean')
        assert a['arguments']==['--json','--root='+str(case_root),'-o',str(artifact),str(case_root/case['producer'])]
        assert b['arguments']==['--json','--root='+str(case_root),str(case_root/case['consumer'])]
        assert Path(a['workingDirectory']).resolve()==Path(b['workingDirectory']).resolve()==case_root
        assert a['environment']==b['environment']=={'LEAN_PATH':str(imports)+';'+str(LEAN.parent.parent/'lib/lean'),'LEAN_NUM_THREADS':'1'}
        assert not a['result']['StandardOutput'] and not a['result']['StandardError'] and not b['result']['StandardError']
        assert a['result']['DeadlineSeconds']==b['result']['DeadlineSeconds']==120 and a['executable']==b['executable']
        if case['expected']=='accept':assert b['result']['StandardOutput']==[]
        else:
            assert row['producerArtifactHash']!=sha(ROOT/'.lake/build/lib/lean'/Path(case['producer']).with_suffix('.olean'))
            diagnostics=[json.loads(x) for x in b['result']['StandardOutput']];assert len(diagnostics)==len(case['diagnostics'])>0
            lines=client.split('\n');ranges={}
            for i,text in enumerate(lines):
                match=re.match(r'^theorem ([A-Za-z0-9_]+)\b',text)
                if match:ranges[match[1]]=(i+1,next((j for j in range(i+1,len(lines)) if re.match(r'^(theorem |def |structure |end |omit )',lines[j])),len(lines)))
            used=set()
            for d in diagnostics:
                diagnostic_path=d['fileName'].replace('\\','/')
                assert d['severity']=='error' and (diagnostic_path==case['consumer'] or diagnostic_path.endswith('/'+case['consumer']))
                matches=[e for e in case['diagnostics'] if ranges[e['surface']][0]<=d['pos']['line']<=ranges[e['surface']][1]];ex=only(matches);assert ex['surface'] not in used;used.add(ex['surface'])
                pattern={'type-mismatch':r'^(Type mismatch|type mismatch)\b','destructure':r'^rcases tactic failed:','invalid-field':r'^(Invalid field|invalid field)\b'}[ex['errorClass']];assert re.match(pattern,d['data'])
        rows.append({**row,'producerExit':0,'producerReceipt':pin(folder/(case['id']+'-producer.json')),'consumerReceipt':pin(folder/(case['id']+'-consumer.json')),'expectedDiagnostics':case['diagnostics']})
    return {'passed':True,'selected':s['selected'],'acceptCount':sum(x['expected']=='accept' for x in rows),'rejectCount':sum(x['expected']=='reject' for x in rows),'cases':rows,'restored':True,'shadowRemoved':True,'stageError':None,'integrityError':None,'cleanupError':None,'receipt':pin(folder/'summary.json'),'baseline':baseline}
def main():
    global INITIAL,CHANGE,REGISTRY,DEPS,CHECKS,RECIPES
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,default=E/'evidence-verified.json');ap.add_argument('--index-output',type=Path,default=HERE/'EVIDENCE_INDEX.json');a=ap.parse_args()
    INITIAL=read(HERE/'INITIAL_FILES.json');CHANGE=read(HERE/'HASH_CHANGE.json');REGISTRY=read(OLD/'CONTROL_REGISTRY.json');DEPS=read(ROOT/'scripts/lifecycle_dependency_cases.json');CHECKS=[]
    recipe_spec=importlib.util.spec_from_file_location('r2_recipes',HERE/'prepare_runs.py');recipe_module=importlib.util.module_from_spec(recipe_spec);recipe_spec.loader.exec_module(recipe_module);RECIPES={x['name']:x for x in recipe_module.recipes()}
    for name in ['INITIAL_FILES.json','PROTECTED_BASELINE.json','START.json','MATERIALIZATION.json','HASH_CHANGE.json','HASH_VECTORS.json','hash_control.ps1','run_check.ps1','prepare_runs.py','CONTRACT.json','PROMPT.md','ACCEPTANCE_MATRIX.frozen.md']:
        path=HERE/name;raw=path.read_bytes();blob=git('show',PRODUCTION+':'+path.relative_to(ROOT).as_posix())
        if name=='HASH_CHANGE.json':
            # The production commit stores LF; this one receipt was originally
            # emitted as CRLF. Pin that exact observed raw representation too.
            assert sha(path)=='b5459aa84f31d8263da9ee3540312a09c07308f879bd46d5fc79533e75b76c71'
            assert raw==blob.replace(b'\n',b'\r\n'), 'Hash-change receipt serialization differs'
        else:assert raw==blob, 'Production-freeze input substitution: '+name
    assert sha(OLD/'CONTROL_REGISTRY.json')==sha(OLD/'CONTROL_REGISTRY.frozen.json')=='385c9bc95ac09b3cc046a7049e954cdf19361330c31f99bd83c9da0c822423f2'
    assert len(REGISTRY['cases'])==67 and len(DEPS['cases'])==26 and sha(ROOT/SCRIPT)==CHANGE['newSha256']
    for x in REGISTRY['components']:assert sha(OLD/x['path'])==x['sha256']
    hashes=hash_controls();mat=materialization();historical=old_f01()
    positives={p:controls(p,True) for p in ['pwsh','winps']}
    campaigns={p:controls(p) for p in ['pwsh','winps']};assert len(campaigns['pwsh']['selected'])==67 and len(campaigns['winps']['selected'])==66
    registry={p:registry_controls(p) for p in ['pwsh','winps']}
    deps={n:dependency(n) for n in ['selftest','startup','focused','full']};assert deps['full']['acceptCount']==3 and deps['full']['rejectCount']==23
    build=check('default-build');assert not build['result']['StandardError']
    scope_spec=importlib.util.spec_from_file_location('r2_scope',HERE/'verify_scope.py');scope_module=importlib.util.module_from_spec(scope_spec);scope_spec.loader.exec_module(scope_module);scope=scope_module.verify()
    source_pins={p:sha(ROOT/p) for p in [SCRIPT,'scripts/lifecycle_validator.ps1','scripts/lifecycle_validator_environment.ps1','scripts/owned_process_tree.ps1','scripts/lifecycle_dependency_cases.json','scripts/lifecycle_contract_integrity.ps1','.lake/build/bin/rmq_lifecycle_validate.exe']}
    for name in ['run_check.ps1','hash_control.ps1','verify_evidence.py','verify_scope.py']:source_pins[str((HERE/name).relative_to(ROOT)).replace('\\','/')]=sha(HERE/name)
    for folder in ['checks','specs','materialization','old-source','old-winps-f01','positive-f01-pwsh','positive-f01-winps','controls-pwsh','controls-winps','registry-pwsh','registry-winps','dependency-selftest','dependency-startup','dependency-focused','dependency-full']:
        for p in (E/folder).rglob('*'):
            if p.is_file():pin(p)
    index={'schema':'life1-r2-evidence-index-v1','productionCommit':PRODUCTION,'files':sorted(FILES.values(),key=lambda x:x['path']),'checks':CHECKS,'limits':'Pin index only; semantic validation is in verify_evidence.py and unchanged production/control handlers.'}
    a.index_output.write_bytes((json.dumps(index,indent=2)+'\n').encode());index_pin=pin(a.index_output)
    packet={'schema':'life1-r2-evidence-v1','passed':True,'base':BASE,'productionCommit':PRODUCTION,'observedHead':git('rev-parse','HEAD').decode().strip(),'sourcePins':source_pins,'checks':CHECKS,'controlCampaigns':campaigns,'registryCampaigns':registry,'dependency':deps,'hash':hashes,'materialization':mat,'oldWindowsPositive':historical,'firstIntactPositives':positives,'scope':scope,'fileIndex':index_pin,'limitations':['Returned helper lines are not raw process bytes.','Empty self-test baseline cannot establish whole-tree integrity.','Full26 replay observed only in current pwsh.','No theorem, native capacity, aggregate or coordinator acceptance follows.']}
    a.output.write_bytes((json.dumps(packet,indent=2)+'\n').encode());print(json.dumps({'passed':True,'controls':{p:len(x['selected']) for p,x in campaigns.items()},'dependency':{'reject':23,'accept':3},'checks':len(CHECKS),'files':len(FILES),'packet':pin(a.output),'index':index_pin},indent=2))
if __name__=='__main__':main()
