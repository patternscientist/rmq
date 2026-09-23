"""End-to-end experiment. Reference fields never reach compile() or run()."""
import json
import pathlib
import sys
from machine import SubroutineCompiler, run, digest

ROOT = pathlib.Path(__file__).resolve().parent


def affine(d, prefix):
    return f"({d[prefix+'0']} + {d[prefix+'Long1']} * LONG + {d[prefix+'Sparse1']} * SPARSE)"


def geometry_source(n, g):
    lines = ['def locate(segment,index):', '    global LOC_OK, LOC_BIT, LOC_LEN',
             '    LOC_OK = 0', '    LOC_BIT = 0', '    LOC_LEN = 0',
             '    if segment == 0 or segment == 19:',
             '        count = (2 * N + BPW - 1) // BPW',
             '        if segment == 19:', '            count = count + 2 * N + 1',
             '        if index < count:', '            LOC_OK = 1',
             '            LOC_BIT = W + index * BPW',
             '            LOC_LEN = min(BPW, 2 * N - index * BPW)',
             '        return 0', '    prefix = W + 2 * N']
    for d in g['sourceDescriptors']:
        lines += [f"    bits = {affine(d,'bits')}",f"    if segment == {d['segment']}:",
                  f"        if index < {affine(d,'count')}:",
                  '            LOC_OK = 1', f"            LOC_BIT = prefix + index * {d['stride']}",
                  f"            LOC_LEN = min({d['stride']}, bits - index * {d['stride']})",
                  '        return 0','    prefix = prefix + bits']
    lines += ['    if segment == 20:']
    for d in g['interiorComponents']:
        w,b = d['width'],g['packedBpCodeWordWidth']
        chunks = (w+b-1)//b
        lines += [f"        if index < {d['wordPrefix']+d['wordCount']}:",
                  f"            local = index - {d['wordPrefix']}",
                  f"            entry = local // {chunks}",f"            chunk = local % {chunks}",
                  '            LOC_OK = 1',
                  f"            LOC_BIT = prefix + {d['bitPrefix']} + entry * {w} + chunk * BPW",
                  f"            LOC_LEN = min(BPW, {w} - chunk * BPW)", '            return 0']
    lines += ['        return 0',f"    prefix = prefix + {g['interiorOverhead']}",
              '    if segment == 21:',f"        if index < {g['packedFringeCount']}:",
              '            LOC_OK = 1',f"            LOC_LEN = {g['packedFringeWidth']}",
              '            LOC_BIT = prefix + index * LOC_LEN','        return 0',
              f"    prefix = prefix + {g['fringeOverhead']}", '    if segment == 22:',
              f"        if index < {g['packedSelectChunkCount']}:", '            LOC_OK = 1',
              f"            LOC_LEN = {g['packedSelectChunkWidth']}",
              '            LOC_BIT = prefix + index * LOC_LEN', '    return 0']
    return '\n'.join(lines)+'\n'


def build(n, width, geometry):
    # Intentionally accepts no input values, endpoint pair, reference answer,
    # reference trace, or decoded content-dependent counts.
    constants = dict(geometry['vmGlobals'], N=n, W=width,
        SS=geometry['packedSelectSuperStride'],LS=geometry['packedSelectLocalStride'],
        LPS=geometry['packedSelectLocalSlotsPerSuper'],SUPERSLOTS=geometry['packedSuperSlots'],
        SPARSESLOTS=geometry['packedSparseSlots'],LONGW=geometry['packedLongFlagWordSize'],
        SPARSEW=geometry['packedSparseWordSize'])
    source = '\n'.join((ROOT/p).read_text() for p in [
        'physical_program.py','rank_select_program.py','lca_interior_program.py'])
    source += '\n'+geometry_source(n, geometry)
    program = SubroutineCompiler(source,constants).compile()
    return program,source


def independent(xs,l,r):
    return min(range(l,r),key=lambda i: (xs[i],i))+1 if 0<=l<r<=len(xs) else 0


def main(path):
    fixture = json.loads(path.read_text())
    n,w,g = fixture['n'],fixture['cellWidth'],fixture['geometry']
    program,source = build(n,w,g)
    print('compiled',len(program['code']),'instructions',program['registers'],'registers',flush=True)
    (ROOT/f'program-n{n}.json').write_text(json.dumps(program))
    (ROOT/f'program-n{n}-source.py').write_text(source)
    cells = list(map(int,fixture['cells']))
    result = run(program,cells,w,fixture['left'],fixture['right'])
    result['programHash']=digest(program['code'])
    result['memoryHash']=digest(cells)
    result['fixture']=path.name
    result['instructionCount']=len(program['code'])
    result['registerCount']=program['registers']
    ref=fixture['reference']
    print('result',result['resultTag'],'expected',None if ref['answer'] is None else ref['answer']+1,
          'steps',result['steps'],'reads',len(result['reads']),flush=True)
    (ROOT/(path.stem+'-vm.json')).write_text(json.dumps(result,indent=2))
    # Compare physical receipts positionally, including repeats.
    expected=[(x['address'],int(x['reply']['value']) if x['reply'] is not None else None)
              for x in ref['physicalTrace']]
    actual=[(x['address'],x['reply']) for x in result['reads']]
    if expected!=actual:
        for i in range(max(len(expected),len(actual))):
            a=actual[i] if i<len(actual) else None
            e=expected[i] if i<len(expected) else None
            if a!=e:
                print('physical mismatch',i,'expected',e,'actual',a)
                if i<len(result['reads']):print(result['reads'][i]['phase'])
                break
    assert actual==expected, 'physical receipt mismatch'
    logical_expected=[(x['request']['segment'],x['request']['index'],
                       int(x['reply']['value'])+1 if x['reply'] is not None else 0)
                      for x in ref['logicalTrace']]
    logical_actual=[(x['segment'],x['index'],x['valueTag']) for x in result['logical'][3:]]
    if logical_actual!=logical_expected:
        for i,(a,e) in enumerate(zip(logical_actual,logical_expected)):
            if a!=e:
                print('logical mismatch',i,e,a)
                break
    assert logical_actual==logical_expected, 'logical receipt mismatch'
    # Each logical reply's ordinal range must contain exactly its expected plan.
    for a,e in zip(result['logical'][3:],ref['logicalTrace']):
        addresses=[x['address'] for x in result['reads'][a['readStart']:a['readEnd']]]
        assert addresses==e['physicalPlan'], ('logical physical-plan mismatch',a,e)
    xs=list(map(int,fixture['input']))
    assert result['failure'] is None
    assert result['resultTag']==independent(xs,fixture['left'],fixture['right'])
    whole=fixture['coverage'].get('wholePathCovered',fixture['coverage']['accepted'])
    assert fixture['coverage']['accepted']
    result['checks']={'physicalReceipts':True,'logicalReceipts':True,'perLogicalPlans':True,
                      'independentAnswer':True,'wholePathCoverage':whole}
    (ROOT/(path.stem+'-vm.json')).write_text(json.dumps(result,indent=2))
    print('WHOLE-PATH PASS' if whole else 'REFERENCE PATH PASS (partial coverage)',flush=True)


if __name__=='__main__':
    main(pathlib.Path(sys.argv[1]))
