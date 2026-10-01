"""Compare exact Git blobs and conservative local Lean import closures."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--repo', type=Path, required=True)
parser.add_argument('--output', type=Path, required=True)
args = parser.parse_args()
repo = args.repo.resolve()
refs = [
    '3849ecbb53bbedfcd679352cc68d095fa5a304c2',
    'eb8e4f250ee13eaf378f4a42028ce32e7cf0b94a',
    'd27ffa341f4ed8ceccc46817455eb26c73b319a1',
    '68163d9496559f06038d108c74bfcb0781175eda',
    '5a5f8f2e239aaab48a955ec86b9adf0a3cab0a71',
    'ee44f04a561f2194b3713f071c26b6faf9ba7fab',
]
cmd = ['git', '-c', 'safe.directory='+repo.as_posix(), '-C', str(repo)]
trees = {}
for ref in refs:
    tree = {}
    for row in subprocess.check_output(cmd+['ls-tree','-r',ref]).decode().splitlines():
        meta, path = row.split('\t',1)
        tree[path] = meta.split()[2]
    trees[ref] = tree
oids = sorted({oid for tree in trees.values() for path,oid in tree.items() if path.endswith('.lean')})
raw = subprocess.check_output(cmd+['cat-file','--batch'], input=('\n'.join(oids)+'\n').encode())
blobs = {}
position = 0
for oid in oids:
    end = raw.index(b'\n',position)
    header = raw[position:end].split()
    size = int(header[2])
    data = raw[end+1:end+1+size]
    assert header[0].decode() == oid and len(data) == size
    blobs[oid] = data.decode('utf-8-sig')
    position = end+size+2

def imports(source):
    """Read the Lean header, skipping whitespace and nested comments."""
    pos = 0
    names = []
    while pos < len(source):
        if source[pos].isspace():
            pos += 1
        elif source.startswith('--',pos):
            end = source.find('\n',pos)
            pos = len(source) if end < 0 else end+1
        elif source.startswith('/-',pos):
            depth = 1
            pos += 2
            while depth and pos < len(source):
                if source.startswith('/-',pos):
                    depth += 1
                    pos += 2
                elif source.startswith('-/',pos):
                    depth -= 1
                    pos += 2
                else:
                    pos += 1
            assert depth == 0
        elif source.startswith('prelude',pos) and not source[pos+7:pos+8].isalnum():
            pos += 7
        else:
            match = re.match(r'import\s+([A-Za-z_][A-Za-z_0-9.]*)',source[pos:])
            if match is None:
                break
            names.append(match.group(1))
            pos += match.end()
    return names

def closure(ref, roots):
    todo = list(roots)
    seen = set()
    external = set()
    tree = trees[ref]
    while todo:
        path = todo.pop()
        if path in seen:
            continue
        if path not in tree:
            external.add(path)
            continue
        seen.add(path)
        for name in imports(blobs[tree[path]]):
            todo.append(name.replace('.','/')+'.lean')
    return sorted(seen), sorted(external)

groups = {
    'paper': ['RMQPaper.lean'],
    'lifecycle': ['RMQ/Headlines/Lifecycle.lean','RMQ/Validation/LifecycleContract.lean',
                  'RMQ/Core/WordRAM/Lifecycle/Provenance.lean','RMQ/Validation/PackedLifecycle.lean'],
}
result = {'schema':'rmq-git-source-closure/1','base':refs[-1], 'method':
    'Conservative local import closure at each exact Git object. External Lean/Std imports are reported separately; toolchain identity must also match.', 'groups':{}}
for label, roots in groups.items():
    selected = refs if label == 'paper' else refs[1:]
    closures = {ref: closure(ref, roots) for ref in selected}
    paths = sorted(set().union(*(set(item[0]) for item in closures.values())))
    baseline = trees[refs[-1]]
    result['groups'][label] = {
        'roots':roots,
        'closures':{ref:{'paths':items[0], 'external_or_missing':items[1],
                        'lean_toolchain_blob':trees[ref].get('lean-toolchain'),
                        'different_from_base':[p for p in paths if trees[ref].get(p)!=baseline.get(p)]}
                    for ref,items in closures.items()},
        'blobs':{path:{ref:trees[ref].get(path) for ref in selected} for path in paths},
    }
path = args.output
path.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
print(json.dumps({'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
    'groups':{k:{ref:{'paths':len(v['paths']), 'differences':v['different_from_base'], 'external_or_missing':v['external_or_missing']}
                 for ref,v in group['closures'].items()} for k,group in result['groups'].items()}},indent=2))
