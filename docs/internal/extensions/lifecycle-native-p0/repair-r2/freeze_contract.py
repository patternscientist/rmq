"""One-time exact-base freeze, before diagnostic implementation edits."""
import hashlib
import json
import pathlib
import re
import subprocess

ROOT = pathlib.Path(__file__).resolve().parents[5]
OUT = pathlib.Path(__file__).resolve().parent
BASE = '2307e3ad0739e0e1d9c3f186cdc568631086fddf'
PROMPT = pathlib.Path('C:/Users/poin/Documents/RMQ/lifecycle-implementation-20260920/LIFE-NATIVE-P0-R2_PROMPT.md')

def git(*args):
    return subprocess.check_output(['git', '-c', 'core.excludesfile=', '-C', str(ROOT), *args])

assert git('rev-parse', 'HEAD').decode().strip() == BASE
assert git('branch', '--show-current').decode().strip() == 'codex/life-native-p0-r2-outer-diagnostics'
assert not git('diff', '--name-only') and not git('diff', '--cached', '--name-only')
prompt = PROMPT.read_bytes()
requirements = dict(re.findall(r'^- ([A-Z0-9-]+): (.+)$', '\n'.join(prompt.decode('utf-8-sig').splitlines()), re.M))
raw = git('show', BASE + ':docs/internal/extensions/lifecycle-native-p0/repair-r1/ACCEPTANCE_MATRIX.md')
raw.decode('utf-8', errors='strict')
rows = [r for r in raw.splitlines() if r.startswith(b'| `')]
assert len(rows) == 14
for row in rows:
    cells = row.split(b'|')
    assert len(cells) == 10
    key = cells[1].strip().strip(b'`').decode()
    assert cells[2].strip().decode() == requirements[key], key
for key in ('NP0R2-STREAMS', 'NP0R2-REPORT'):
    rows.append(f'| `{key}` | {requirements[key]} | Narrow outer diagnostic repair | Exact production stream and exit predicates with replayable controls | Actual owned child capture -> caller-used validator -> certification verdict | Legitimate profiles plus extra, missing, duplicate, mixed and misleading output | Pending; append evidence | Open at freeze |'.encode())
frozen = b'\n'.join(rows) + b'\n'
for name in ('ACCEPTANCE_ROWS.txt', 'ACCEPTANCE_MATRIX.md', 'START.json'):
    assert not (OUT / name).exists(), name
(OUT / 'ACCEPTANCE_ROWS.txt').write_bytes(frozen)
header = b'# LIFE-NATIVE-P0-R2 frozen acceptance matrix\n\nThe fourteen inherited eight-column rows retain exact base bytes and historical pending cells. Evidence is append-only.\n\n| ID | Exact frozen requirement | Scope | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge attempted and outcome | Evidence obtained | Status / residual gap |\n| --- | --- | --- | --- | --- | --- | --- | --- |\n'
plan = '''
## Target and verification plan

Join: reviewed native diagnostic prerequisite feeds the later consuming adapter; formal/native aggregate, blind audit and acceptance remain coordinator-owned. Hard obligation: actual outer stdout/stderr/exit objects must satisfy the same precise caller predicate used by positive and negative controls. Inner production semantics/finally/provenance are protected. No Lean/C/ABI, installed tool, old evidence or live candidate mutation is permitted.

Development: exact base/scope/row/prompt checks; immutable old two-case reproduction (prior 60 s, 300 s guard); focused legitimate and real extra-stream cases plus component holdouts. Final-required: fifteen integrity controls (prior 467 s, 2400 s outer), full native SelfTest 23/65/58 (prior 178 s, 1200 s), nineteen dependency controls (prior 49 s, 1200 s), focused native selection, every wrapper profile positive and new exact stream registry. Serialize expensive work using Local\\RMQLifecycleImplementationHeavy20260920; preserve 120/30/8 s fixture/stage/timeout limits. Complete raw streams/exits, cleanup and fixture restoration are evidence.

Final certification: successor contract and strict UTF-8 frozen-row mutations, hygiene/native-decision scans, working/range whitespace, exact-base and each-commit strict design, clean identity, report claim coverage. Claims may compose verified original complete coverage with a final unchanged-policy subtree/both-ledger scan only after outside bytes/scanner/policy/rg/config verification (prior subtree 11 s, 1200 s; full fallback prior 2212 s, 7200 s). Historical source hashes bind exact Git objects, current hashes bind current working bytes. Conditional build skipped if protected Lean/C/lake/toolchain and baseline evidence verify. No campaign aggregate slot. Stop only at target closure, precise obstruction, external blocker or explicit redirection.
'''.encode()
(OUT / 'ACCEPTANCE_MATRIX.md').write_bytes(header + frozen + plan)
start = dict(handle='LIFE-NATIVE-P0-R2', worktree=str(ROOT), base=BASE,
             branch=git('branch', '--show-current').decode().strip(), initialHead=BASE,
             initialClean=True, initialCleanObservedBeforeScaffold=True,
             governance='7b227c49ef2ec044b702126cc41c9add847eed01',
             runtimeCatalog=['rmq-audit-prompt', 'rmq-coordinator', 'rmq-proof-sprint'],
             runtimeCatalogNote='Coordinator and audit-prompt appear both canonically and in user skill catalog; names deduplicated.',
             requiredSkill='rmq-proof-sprint', preflight='PASS',
             frozenRowsSha256=hashlib.sha256(frozen).hexdigest(),
             prompt=dict(path=str(PROMPT), bytes=len(prompt), sha256=hashlib.sha256(prompt).hexdigest()))
(OUT / 'START.json').write_text(json.dumps(start, indent=2) + '\n', encoding='utf-8')
print('FROZEN: 16 complete rows; 14 exact-base rows; all 16 requirements match commissioning prompt')
