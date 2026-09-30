"""One-time LIFE-1-R1 launch freeze; never rewrites an existing freeze."""
import hashlib
import json
import pathlib
import re
import subprocess

ROOT = pathlib.Path(__file__).resolve().parents[5]
HERE = pathlib.Path(__file__).resolve().parent
BASE = '12bd7f0fc2c87f2c9bdef3825bd92477e48e3433'
CAMPAIGN = pathlib.Path('C:/Users/poin/Documents/RMQ/lifecycle-implementation-20260920')

def git(*args):
    return subprocess.run(['git', *args], cwd=ROOT, check=True, capture_output=True, timeout=30).stdout

def pin(data):
    return {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}

def write_json(name, value):
    (HERE / name).write_bytes((json.dumps(value, indent=2, ensure_ascii=False)+'\n').encode())

def main():
    assert git('rev-parse', 'HEAD').decode().strip() == BASE
    assert not (HERE / 'ACCEPTANCE_MATRIX.frozen.md').exists(), 'Existing freeze is immutable'
    original_path = 'docs/internal/extensions/lifecycle1/ACCEPTANCE_MATRIX.frozen.md'
    old = git('show', BASE+':'+original_path)
    assert pin(old)['sha256'] == '8b08e2d7c7f284634d88bfa4262ee447f79a401c78b27dc346ea34d76ccba4a7'
    rows = [line for line in old.splitlines(keepends=True) if line.startswith(b'| `')]
    assert len(rows) == 43
    prompt = (CAMPAIGN/'LIFE-1-R1_PROMPT.md').read_bytes()
    text = prompt.decode('utf-8', errors='strict')
    new_ids = ['L1R1-SELECTOR', 'L1R1-CLEANUP']
    requirements = {}
    for line in rows:
        columns = line.decode('utf-8').strip().split('|')[1:-1]
        assert len(columns) == 8 and all(x.strip() for x in columns)
        identity = columns[0].strip().strip('`')
        required = re.search(r'^- '+re.escape(identity)+r': (.+)$', text, re.M).group(1)
        assert columns[1].strip() == required
        requirements[identity] = required
    for identity in new_ids:
        required = re.search(r'^- '+identity+r': (.+)$', text, re.M).group(1)
        requirements[identity] = required
        fields = [f'`{identity}`', required, 'Local verification repair',
                  'Actual bounded production child controls and complete changed-script replays under the declared runtime profiles.',
                  'Production validator adapter or dependency finally -> unchanged child/verdict -> pinned receipts -> coordinator review.',
                  'Challenge omission/inherited environments or changed owned captured pins against the same production path; preserve exact failure surfaces.',
                  'Pending source-bound replay; no closure asserted at freeze.', 'Open; repair and final verification required.']
        rows.append(('| '+' | '.join(fields)+' |\n').encode())
    template = (ROOT/'docs/internal/templates/PROOF_ACCEPTANCE_MATRIX.md').read_bytes().decode('utf-8')
    header = next(x for x in template.splitlines() if x.startswith('| ID |'))
    prefix = ('# LIFE-1-R1 frozen acceptance matrix\n\n'
              'Exact inherited rows copied from Git base '+BASE+'. Historical Open cells are immutable.\n'
              'This matrix uses docs/internal/templates/PROOF_ACCEPTANCE_MATRIX.md; evidence is appended below the marker.\n\n'
              +header+'\n| --- | --- | --- | --- | --- | --- | --- | --- |\n').encode()
    frozen = prefix + b''.join(rows) + b'\n<!-- APPEND-ONLY-EVIDENCE -->\n'
    for name in ['ACCEPTANCE_MATRIX.md', 'ACCEPTANCE_MATRIX.frozen.md']:
        (HERE/name).write_bytes(frozen)
    (HERE/'PROMPT.md').write_bytes(prompt)
    tracked = git('ls-files', '-z').decode().split('\0')[:-1]
    manifest = {p: pin((ROOT/p).read_bytes()) for p in tracked}
    write_json('INITIAL_WORKING_FILES.json', manifest)
    write_json('CONTRACT.json', {'base':BASE, 'prompt':pin(prompt), 'originalFrozenGit':pin(old),
              'originalFrozenWorking':pin((ROOT/original_path).read_bytes()),
              'frozen':pin(frozen), 'orderedIds':list(requirements), 'requirements':requirements})
    write_json('START.json', {'handle':'LIFE-1-R1', 'task':'01a0c23e-6fce-7542-b453-8fa7a741d7c9',
        'worktree':str(ROOT), 'branch':git('branch','--show-current').decode().strip(), 'base':BASE,
        'governance':'7b227c49ef2ec044b702126cc41c9add847eed01', 'initialClean':True,
        'initialCleanEvidence':'First tool invocation git status --short returned no entries before branch creation.',
        'runtimeProjectSkills':['rmq-audit-prompt','rmq-coordinator','rmq-proof-sprint'],
        'expectedProjectSkills':['rmq-audit-prompt','rmq-coordinator','rmq-proof-sprint'],
        'requiredSkills':['rmq-proof-sprint'], 'preflight':(HERE/'preflight.txt').read_text(encoding='utf-8'),
        'sourceManifest':'INITIAL_WORKING_FILES.json', 'contract':'CONTRACT.json',
        'externalReview':{p:pin((CAMPAIGN/'life1-review'/p).read_bytes()) for p in ['DISPOSITION.md','VALIDATION_SOURCE_REVIEW.md']},
        'originalPrompt':pin((CAMPAIGN/'LIFE-1_PROMPT.md').read_bytes()),
        'shells':{p:pin(pathlib.Path(p).read_bytes()) for p in [
            'C:/Users/poin/.cache/codex-runtimes/codex-primary-runtime/dependencies/native/powershell/pwsh.exe',
            'C:/Windows/System32/WindowsPowerShell/v1.0/powershell.exe']},
        'scope':'Local unpublished validator omission and independent dependency cleanup repair only.'})
    print('LIFE1-R1 FREEZE: 45 ordered eight-column rows; all 43 inherited row bytes and requirements match exact base/prompt.')

if __name__ == '__main__':
    main()
