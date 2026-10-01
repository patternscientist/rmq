import json
from pathlib import Path
here=Path(__file__).resolve().parent
root=here.parents[4]
ids=[c['id'] for c in json.loads((root/'scripts/lifecycle_dependency_cases.json').read_text())['cases']]
absent={'present':False,'value':None}
cases=[]
def add(id,params,error=None,env=None,selected=None,mutation=None):
    cases.append(dict(id=id,kind='dependency-registry' if mutation else 'dependency',
        production='Exact production lifecycle_dependency_replay.ps1 parameter binding / Select-Cases / Assert-Registry / mode guards before compiler work.',
        parameters=params,ambient={'present':True,'value':env} if env is not None else absent,mutation=mutation,
        expected=dict(exit=1 if error else 0,error=error,output='LIFE1-DEPENDENCY SELECT '+','.join(ids if selected is None else selected)),
        predicate='Actual script invocation; exact exit, Console stderr, output cardinality/ordered selected IDs and unchanged original source.',
        challenge='Challenge real parameter/environment/registry/mode boundary, with exact script bytes; registry mutations affect only an owned scratch copy.'))
probe={'SelectorProbeOnly':True}
add('D01_OMITTED',probe)
add('D02_ARGUMENT_VALID',dict(SelectorProbeOnly=True,OnlyCase=ids[0]),selected=[ids[0]])
add('D03_BOUND_EMPTY',dict(SelectorProbeOnly=True,OnlyCase=''),'LIFE1-SELECTOR: explicitly empty selector')
add('D04_BOUND_WHITESPACE',dict(SelectorProbeOnly=True,OnlyCase=' '),'LIFE1-SELECTOR: explicitly empty selector')
add('D05_ARGUMENT_UNKNOWN',dict(SelectorProbeOnly=True,OnlyCase='D99_UNKNOWN'),'LIFE1-SELECTOR: unknown selector')
add('D06_ARGUMENT_MALFORMED',dict(SelectorProbeOnly=True,OnlyCase='wrong'),'LIFE1-SELECTOR: malformed selector')
add('D07_ENV_VALID',probe,env='id:'+ids[0],selected=[ids[0]])
add('D08_ENV_EMPTY_ID',probe,'LIFE1-SELECTOR: explicitly empty selector',env='id:')
add('D09_ENV_WHITESPACE',probe,'LIFE1-SELECTOR: explicitly empty selector',env='id: ')
add('D10_ENV_MALFORMED',probe,'LIFE1-SELECTOR: environment requires id: prefix',env=ids[0])
add('D11_DUPLICATE_CHANNEL',dict(SelectorProbeOnly=True,OnlyCase=ids[0]),'LIFE1-SELECTOR: duplicate parameter/environment channels',env='id:'+ids[0])
add('D12_DUPLICATE_ARGUMENT',probe,'PARAMETER_ALREADY_BOUND')
add('D13_PRESENT_EMPTY',probe,'LIFE1-SELECTOR: environment requires id: prefix',env='')
cases[-1]['legacyExpected']=dict(exit=0,error=None,output='LIFE1-DEPENDENCY SELECT '+','.join(ids))
add('D14_PROBE_SELFTEST',dict(SelectorProbeOnly=True,SelfTestOnly=True),'LIFE1-SELECTOR: incompatible modes')
add('D15_PROBE_STARTUP',dict(SelectorProbeOnly=True,StartupOnly=True),'LIFE1-SELECTOR: incompatible modes')
add('D16_STARTUP_SELFTEST',dict(StartupOnly=True,SelfTestOnly=True),'LIFE1-SELECTOR: incompatible modes')
add('D17_STARTUP_SELECTED',dict(StartupOnly=True,OnlyCase=ids[0]),'LIFE1-SELECTOR: incompatible modes')
add('D18_SELFTEST_SELECTED',dict(SelfTestOnly=True,OnlyCase=ids[0]),'LIFE1-SELECTOR: incompatible modes')
add('D19_REGISTRY_MISSING_MIDDLE',probe,'LIFE1-REGISTRY: exact nonempty case count required',mutation='missing-middle')
add('D20_REGISTRY_DUPLICATE_MIDDLE',probe,'LIFE1-REGISTRY: missing, duplicate, unknown or reordered ID',mutation='duplicate-middle')
add('D21_REGISTRY_UNKNOWN_MIDDLE',probe,'LIFE1-REGISTRY: missing, duplicate, unknown or reordered ID',mutation='unknown-middle')
add('D22_REGISTRY_UNUSED_EDIT',probe,'LIFE1-REGISTRY: frozen normalized-byte SHA256 mismatch',mutation='unused-edit')
assert not (here/'CONTROL_REGISTRY.frozen.json').exists()
(here/'dependency_boundary_cases.json').write_text(json.dumps({'version':1,'cases':cases},indent=2)+'\n',encoding='utf-8')
print('Dependency boundary mapping',len(cases))
