"""Finite independent-answer, width, read-backing and value-dependency checks."""
import json
from run_experiment import ROOT, build, independent
from machine import run,digest


def main():
    rows=[]
    shapes={}
    for path in sorted(ROOT.glob('fixture-*.json')):
        if path.name.endswith('-vm.json'):continue
        f=json.loads(path.read_text())
        n,w=f['n'],f['cellWidth']
        program,_=build(n,w,f['geometry'])
        cells=list(map(int,f['cells']))
        xs=list(map(int,f['input']))
        h=digest(program['code'])
        if n in shapes:assert shapes[n]==h, 'same-n code differs by shape'
        shapes[n]=h
        # Exhaustive small fixtures; larger fixtures have a deterministic grid
        # and all singleton/full-prefix/full-suffix cases.
        pairs={(l,r) for l in range(n+2) for r in range(n+2)} if n<=16 else (
            {(l,r) for l in range(0,n+2,3) for r in range(0,n+2,3)} |
            {(i,i+1) for i in range(n)} | {(0,i) for i in range(n+2)} |
            {(i,n) for i in range(n+2)} | {(n+1,0),(0,n+1),(n,n)})
        valid=invalid=peak_steps=peak_reads=peak_value=0
        for l,r in sorted(pairs):
            out=run(program,cells,w,l,r)
            assert out['failure'] is None,(path.name,l,r,out['failure'])
            expected=independent(xs,l,r)
            assert out['resultTag']==expected,(path.name,l,r,expected,out['resultTag'])
            assert all(e['reply']==cells[e['address']] for e in out['reads'])
            if expected:
                valid+=1
            else:
                invalid+=1
                assert not out['reads']
            peak_steps=max(peak_steps,out['steps'])
            peak_reads=max(peak_reads,len(out['reads']))
            peak_value=max(peak_value,out['maxRegisterValue'])
        rows.append({'fixture':path.name,'n':n,'width':w,'valid':valid,'invalid':invalid,
                     'maxSteps':peak_steps,'maxReads':peak_reads,'maxRegisterValue':peak_value,
                     'programHash':h})
        print(rows[-1],flush=True)

    f=json.loads((ROOT/'fixture-n9-balanced.json').read_text())
    p,_=build(f['n'],f['cellWidth'],f['geometry'])
    cells=list(map(int,f['cells']))
    base=run(p,cells,f['cellWidth'],f['left'],f['right'])
    absent=run(p,[],f['cellWidth'],f['left'],f['right'])
    assert absent['failure']=='missing-cell' and len(absent['reads'])==1
    mutations=[]
    # Corrupt each actual read cell's least significant bit, without changing
    # code or expected answer. Distinguish changed answers/failure from logs.
    for addr in sorted({x['address'] for x in base['reads']}):
        mem=cells.copy()
        mem[addr]^=1
        try:
            out=run(p,mem,f['cellWidth'],f['left'],f['right'])
            result={'address':addr,'resultTag':out['resultTag'],'failure':out['failure'],
                    'answerChanged':out['resultTag']!=base['resultTag'],
                    'steps':out['steps'],'reads':len(out['reads'])}
        except OverflowError as exc:
            result={'address':addr,'failure':'width-trap','detail':str(exc)}
        mutations.append(result)
    assert any(m.get('answerChanged') and m.get('failure') is None for m in mutations)
    assert any(m.get('failure') for m in mutations)
    report={'queryChecks':rows,'totalQueries':sum(r['valid']+r['invalid'] for r in rows),
            'sameNProgramIdentity':True,'missingHeader':{k:v for k,v in absent.items()
                if k not in ['reads','logical','phases','execution']},
            'cellMutations':mutations,'scope':'finite experiments, not a universal theorem'}
    (ROOT/'validation-results.json').write_text(json.dumps(report,indent=2))
    print('VALIDATION PASS',report['totalQueries'],'queries',len(mutations),'cell mutations',flush=True)


if __name__=='__main__':main()
