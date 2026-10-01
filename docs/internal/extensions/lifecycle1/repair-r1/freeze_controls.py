import hashlib,json,pathlib
here=pathlib.Path(__file__).resolve().parent
assert not (here/'CONTROL_REGISTRY.frozen.json').exists()
cases=[];components=[]
for name in ['selector_cases.json','dependency_boundary_cases.json','finalizer_cases.json']:
    data=(here/name).read_bytes()
    components.append(dict(path=name,sha256=hashlib.sha256(data).hexdigest()))
    for spec in json.loads(data)['cases']:
        kind=spec.get('kind','finalizer')
        handler='finalizer_control.ps1' if kind=='finalizer' else 'dependency_child.ps1' if kind.startswith('dependency') else 'selector_child.ps1'
        cases.append(dict(id=spec['id'],kind=kind,handler=handler,profiles=['pwsh'] if spec['id']=='F00_OLD_CHANGED_PIN' else ['pwsh','winps'],spec=spec))
cases.append(dict(id='T01_DESCENDANT_TIMEOUT',kind='deadline',handler='deadline_control.ps1',profiles=['pwsh','winps'],
    spec=dict(predicate='Real owned root plus descendant timeout at6s, all observed PIDs absent; production adapter restores ambient selector.',
              production='Invoke-LifecycleValidatorProcess -> unchanged Invoke-RMQOwnedBoundedProcess -> actual shell sleeper and descendant')))
assert len(cases)==67 and len({c['id'] for c in cases})==67
data=(json.dumps(dict(version=1,components=components,cases=cases),indent=2)+'\n').encode()
for name in ['CONTROL_REGISTRY.json','CONTROL_REGISTRY.frozen.json']:(here/name).write_bytes(data)
path=here/'run_controls.ps1'
source=path.read_bytes()
assert source.count(b'CONTROL_REGISTRY_SHA256_PENDING')==1
path.write_bytes(source.replace(b'CONTROL_REGISTRY_SHA256_PENDING',hashlib.sha256(data).hexdigest().encode()))
print('Frozen exact67 controls; current pwsh67, Windows66 (old regression is pwsh-only).',hashlib.sha256(data).hexdigest())
