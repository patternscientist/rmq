"""Create the exact reviewed selector/control mapping before the campaign."""
import json
from pathlib import Path
here=Path(__file__).resolve().parent
absent={'present':False,'value':None}
def present(value): return {'present':True,'value':value}
cases=[]
def native(id,args,selector=None,ambient=None,mode='registry',error=None):
    cases.append(dict(id=id,kind='native',production='Invoke-LifecycleValidatorProcess -> Invoke-RMQOwnedBoundedProcess -> rmq_lifecycle_validate.mainImpl/select',
        arguments=args,selector=selector or absent,ambient=ambient or absent,
        expected=dict(exit=1 if error else 0,mode=mode,error=error),
        predicate='Exact native exit/returned stdout/stderr/order plus identical caller process key presence/value after the actual child.',
        challenge='Change selector channel/value/ambient while retaining the same executable, adapter, helper and bounded process predicate.'))
native('S01_ABSENT_REGISTRY',['--registry'])
native('S02_ABSENT_STARTUP',['--startup'],mode='startup')
native('S03_ARGUMENT_SINGLE',['L01-W-EMPTY'],mode='single')
native('S04_PRESENT_EMPTY_REGISTRY',['--registry'],present(''),error='LIFE1-FAIL|duplicate-selector-channel')
cases[-1]['legacyExpected']=dict(exit=0,mode='registry',error=None)
native('S05_EXPLICIT_ID_EMPTY',[],present('id:'),error='LIFE1-FAIL|empty-selector')
native('S06_ENV_WHITESPACE',[],present('id: '),error='LIFE1-FAIL|whitespace-selector')
native('S07_ENV_VALID',[],present('id:L01-W-EMPTY'),mode='single')
native('S08_ENV_UNKNOWN',[],present('id:UNKNOWN'),error='LIFE1-FAIL|unknown-selector')
native('S09_ENV_MALFORMED',[],present('L01-W-EMPTY'),error='LIFE1-FAIL|selector-environment-prefix')
native('S10_ARGUMENT_UNKNOWN',['UNKNOWN'],error='LIFE1-FAIL|unknown-selector')
native('S11_DUPLICATE_ARGUMENT',['L01-W-EMPTY','L01-W-EMPTY'],error='LIFE1-FAIL|duplicate-selector')
native('S12_DUPLICATE_CHANNEL',['L01-W-EMPTY'],present('id:L01-W-EMPTY'),error='LIFE1-FAIL|duplicate-selector-channel')
native('S13_AMBIENT_VALID_OMITTED',['--registry'],ambient=present('id:L01-W-EMPTY'))
native('S14_AMBIENT_MALFORMED_OMITTED',['--startup'],ambient=present('malformed'),mode='startup')
native('S15_AMBIENT_EMPTY_OMITTED',['--registry'],ambient=present(''))
native('S16_AMBIENT_ID_EMPTY_ARGUMENT',['L01-W-EMPTY'],ambient=present('id:'),mode='single')
native('S17_AMBIENT_REPLACED_ENV',[],present('id:L01-W-EMPTY'),present('id:UNKNOWN'),mode='single')
native('S18_FAILURE_RESTORES_AMBIENT',[],present('id:'),present('id:L01-W-EMPTY'),error='LIFE1-FAIL|empty-selector')
native('S19_FAILURE_RESTORES_EMPTY',[],present('id: '),present(''),error='LIFE1-FAIL|whitespace-selector')
native('S20_FAILURE_RESTORES_ABSENCE',[],present('bad-prefix'),error='LIFE1-FAIL|selector-environment-prefix')
native('S21_ARGUMENT_WHITESPACE',[' '],error='LIFE1-FAIL|whitespace-selector')
native('S22_ENV_LEADING_SPACE',[],present('id: L01-W-EMPTY'),error='LIFE1-FAIL|whitespace-selector')
native('S23_LAUNCH_FAILURE',[],ambient=present('id:L01-W-EMPTY'),mode='child-exit-failure',error=None)
cases[-1]['expected']['exit']=7
cases[-1]['production']='Production adapter -> unchanged owned helper -> owned shell child exit7; exact empty streams and restored ambient after failure.'
def wrapper(id,params,error=None,ambient=None,pattern=None):
    cases.append(dict(id=id,kind='wrapper',production='actual scripts/lifecycle_validator.ps1 Stage/Case -> production adapter -> actual native child',
        parameters=params,ambient=ambient or absent,expected=dict(exit=1 if error else 0,error=error,pattern=pattern),
        predicate='Actual script parameter binding, exact expected error or terminal success, caller environment restored.',
        challenge='Bound-empty, whitespace, unknown, missing, duplicate or incompatible Case is rejected before any semantic fixture; legitimate script selectors reach real children.'))
wrapper('W01_STARTUP_AMBIENT',{'Stage':'startup'},ambient=present('id:UNKNOWN'),pattern=r'^LIFE1-VALIDATOR PASS stage=startup processes=2 logs=')
wrapper('W02_SINGLE_AMBIENT',{'Stage':'single','Case':'L01-W-EMPTY'},ambient=present('id:'),pattern=r'^LIFE1-VALIDATOR PASS stage=single processes=3 logs=')
wrapper('W03_BOUND_EMPTY',{'Stage':'single','Case':''},'Empty or whitespace Case selector')
wrapper('W04_BOUND_SPACE',{'Stage':'single','Case':' '},'Empty or whitespace Case selector')
wrapper('W05_UNKNOWN',{'Stage':'single','Case':'UNKNOWN'},'Unknown exact Case selector')
wrapper('W06_MISSING',{'Stage':'single'},'Missing exact Case selector')
wrapper('W07_WRONG_STAGE',{'Stage':'startup','Case':'L01-W-EMPTY'},'Case selector requires Stage single')
wrapper('W08_FULL_BOUND_EMPTY',{'Stage':'full','Case':''},'Case selector requires Stage single')
wrapper('W09_DUPLICATE_CASE',{'Stage':'single','Case':'L01-W-EMPTY'},'PARAMETER_ALREADY_BOUND')
path=here/'selector_cases.json'
assert not (here/'CONTROL_REGISTRY.frozen.json').exists(),'Final campaign registry freeze already exists'
path.write_text(json.dumps({'version':1,'cases':cases},indent=2)+'\n',encoding='utf-8')
print('Selector registry frozen',len(cases))
