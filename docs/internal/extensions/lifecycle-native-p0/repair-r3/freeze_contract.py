"""One-time strict-byte acceptance freeze before production edits."""
import hashlib
import json
import pathlib
import re
import subprocess

ROOT = pathlib.Path(__file__).resolve().parents[5]
OUT = pathlib.Path(__file__).resolve().parent
BASE = '9519b2c1af5e2cf59536b311db5e8dc81376a32f'
PROMPT = pathlib.Path('C:/Users/poin/Documents/RMQ/lifecycle-implementation-20260920/LIFE-NATIVE-P0-R3_PROMPT.md')
IDS = ['LN0-01', 'LN0-02', 'LN0-03', 'LN0-04', 'LN0-05', 'LN0-06',
       'INV-SEMANTIC-NONVACUITY', 'INV-ORACLE-INDEPENDENCE',
       'INV-CATEGORY-SEPARATION', 'INV-MUTATION-REPRODUCIBILITY',
       'CHK-FINAL', 'CHK-SCOPE', 'NP0R1-INTEGRITY', 'NP0R1-TOOLCHAIN',
       'NP0R2-STREAMS', 'NP0R2-REPORT', 'NP0R3-LITERAL', 'NP0R3-SELECTOR']

def git(*args):
    return subprocess.check_output(['git', '-c', 'core.excludesfile=', '-C', str(ROOT), *args])

assert git('rev-parse', 'HEAD').decode().strip() == BASE
assert git('branch', '--show-current').decode().strip() == 'codex/life-native-p0-r3-literal-streams'
assert not git('diff', '--name-only') and not git('diff', '--cached', '--name-only')
prompt = PROMPT.read_bytes()
requirements = dict(re.findall(r'^- ([A-Z0-9-]+): (.+)$', prompt.decode('utf-8').replace('\r\n', '\n'), re.M))
raw = git('show', BASE + ':docs/internal/extensions/lifecycle-native-p0/repair-r2/ACCEPTANCE_MATRIX.md')
raw.decode('utf-8', errors='strict')
rows = [r for r in raw.splitlines() if r.startswith(b'| `')]
assert len(rows) == 16
for key, row in zip(IDS, rows):
    cells = row.split(b'|')
    assert len(cells) == 10
    assert cells[1].strip().strip(b'`').decode('utf-8') == key
    assert cells[2].strip().decode('utf-8') == requirements[key], key
for key in IDS[16:]:
    rows.append(f'| `{key}` | {requirements[key]} | Narrow local verifier repair | Strict decoded literal equality and direct nonempty selector controls | Actual capture -> common production predicate; actual certify_profiles boundary -> run_owned | Exact positives, unequal Unicode/transport holdouts, rejected empty selectors and one actual focused run | Pending; append evidence | Open at freeze |'.encode('utf-8'))
frozen = b'\n'.join(rows) + b'\n'
for name in ('ACCEPTANCE_ROWS.txt', 'ACCEPTANCE_MATRIX.md', 'FREEZE.json'):
    assert not (OUT / name).exists(), name
header = b'# LIFE-NATIVE-P0-R3 frozen acceptance matrix\n\nSixteen complete inherited rows retain exact base bytes and historical pending cells. All eighteen rows are frozen; append evidence separately.\n\n| ID | Exact frozen requirement | Scope | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge attempted and outcome | Evidence obtained | Status / residual gap |\n| --- | --- | --- | --- | --- | --- | --- | --- |\n'
plan = '''
## Target and verification coverage plan

The join is the reviewed native prerequisite plus reviewed formal producer, then consuming adapter and final campaign certification. This local task closes literal comparison and explicit nonempty selection only. No Lean/C/ABI or public-source edits. No weakened predicate, normalization, parallel test comparator, live candidate mutation, policy expansion, historical relabeling or new outer wrapper hierarchy.

Development-loop: exact identity/scope and all eighteen complete row bytes against exact-base rows and independently pinned prompt; literal references, actual emitted Unicode stdout/stderr, retained root/leaf counterexamples, ASCII and newline/normalization/invalid UTF-8 holdouts; upfront direct selector controls. Controls consume the production predicate with the same expected strings, transport flags and ordinary exits.

Final-required: complete new frozen registry; one actual focused native invocation through certify_profiles (1200 s outer, prior 49.522 s); source-derived integrity caller preserving native 0/7 and runner 0/1; six historical legitimate captures and fifteen integrity diagnostic captures revalidated with historical source/producing-root expectations; fresh checks and claims at current HEAD. Tiny children use 60 s and control groups 300 s (root four captures prior 10.106 s). Use unchanged bounded helper and Local\\RMQLifecycleImplementationHeavy20260920, preserve all streams/exits, cleanup and finally identities. Synthetic launcher components and copied-capture profile tests remain separate from actual emitted children.

Final package: eighteen-row successor contract/negative mutations/protected sources, hygiene/native-decision scans, working and exact-base committed whitespace, production strict design against base and each new commit parent, clean final HEAD and complete-report claims. Reuse 23/65/58, fifteen/nineteen and eleven/120 historical registries plus baseline build only after exact source/registry/raw-pin verification; literal change cannot by itself invalidate unchanged native operations. Re-establish whole-root historical claim coverage with unchanged outside paths/scanner/policy/rg/config and fresh entire native subtree/both-ledger scan, else one 7200 s full scan. No duplicate native campaign or Lake build solely to rename evidence. Adapter, final joint aggregate, fresh-blind audit and acceptance remain deferred to coordinator. Stop only on completed local rows, precise obstruction, external blocker or redirection.
'''.encode('utf-8')
(OUT / 'ACCEPTANCE_ROWS.txt').write_bytes(frozen)
(OUT / 'ACCEPTANCE_MATRIX.md').write_bytes(header + frozen + plan)
record = dict(base=BASE, ids=IDS, inherited=16,
              rowsSha256=hashlib.sha256(frozen).hexdigest(),
              prompt=dict(path=str(PROMPT), bytes=len(prompt), sha256=hashlib.sha256(prompt).hexdigest()),
              template='docs/internal/templates/PROOF_ACCEPTANCE_MATRIX.md')
(OUT / 'FREEZE.json').write_text(json.dumps(record, indent=2) + '\n', encoding='utf-8')
print('FROZEN: 18 complete rows; 16 exact-base rows; all 18 requirements match commissioning prompt')
