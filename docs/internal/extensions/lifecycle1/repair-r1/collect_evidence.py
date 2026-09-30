"""Index owned repair receipts without copying binaries or raw output into Git."""
from pathlib import Path
import hashlib
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parents[5]
HERE = Path(__file__).resolve().parent
EVIDENCE = ROOT / '.lake/repair-r1'


def pin(path):
    raw = path.read_bytes()
    return {'path': str(path.resolve()), 'bytes': len(raw),
            'sha256': hashlib.sha256(raw).hexdigest()}


def main():
    checks = []
    files = {}
    campaigns = []
    native = []
    for result_path in sorted((EVIDENCE / 'checks').glob('*/result.json')):
        value = json.loads(result_path.read_bytes())
        result = value['result']
        checks.append({'name': value['spec']['name'], 'spec': value['spec'],
                       'receipt': pin(result_path), 'sourcePins': value['sources'],
                       'exit': result['ExitCode'], 'seconds': result['DurationSeconds'],
                       'deadline': result['DeadlineSeconds'], 'timeout': result['TimedOut'],
                       'overflow': result['OutputLimitExceeded'], 'ownership': result['Ownership'],
                       'terminatedIds': result['TerminatedIds'],
                       'stdoutLines': len(result['StandardOutput']),
                       'stderrLines': len(result['StandardError'])})
        for line in result['StandardOutput']:
            match = re.fullmatch(r'LIFE1-VALIDATOR PASS stage=(\w+) processes=(\d+) logs=(.+)', line)
            if match:
                directory = Path(match.group(3))
                directory.resolve().relative_to(ROOT.resolve() / '.lake')
                processes = json.loads((directory / 'processes.json').read_bytes())
                passed = json.loads((directory / 'PASS.json').read_bytes())
                native.append({'check': value['spec']['name'], 'path': str(directory),
                               'pass': passed, 'processes': processes})
                for path in directory.rglob('*'):
                    if path.is_file() and path.suffix in ('.json', '.txt'):
                        files[str(path)] = pin(path)
    # All owned receipt campaigns except the copied binary/cache/source trees.
    omitted = {'old-root', 'checks', 'specs'}
    for directory in sorted(EVIDENCE.iterdir()):
        if not directory.is_dir() or directory.name in omitted:
            continue
        for path in sorted(directory.rglob('*')):
            if path.is_file() and path.suffix in ('.json', '.txt', '.ps1'):
                files[str(path)] = pin(path)
                if path.name == 'summary.json':
                    value = json.loads(path.read_bytes())
                    campaigns.append({'receipt': pin(path), 'summary': value})
    for path in sorted((EVIDENCE / 'checks').rglob('*')):
        if path.is_file() and path.suffix in ('.json', '.txt'):
            files[str(path)] = pin(path)
    value = {'schema': 'life1-r1-evidence-index-v1',
             'productionFreeze': '122a6bedb086d1de1df8dec167c890f887a72cc2',
             'sourceFreeze': '7c406b15bdc12333d323c92641ab6c6dad6af7a2',
             'observedHead': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
             'workspace': str(ROOT), 'checks': checks, 'native': native,
             'campaigns': campaigns, 'files': list(files.values()),
             'limits': ['Historical/development failures are retained, not relabeled as final passes.',
                        'The protected helper returns nonempty lines, not original stream bytes.',
                        'Overflow or exceptional helper cleanup can prevent output recovery.',
                        'No theorem or coordinator acceptance is inferred from this index.']}
    output = HERE / 'EVIDENCE_INDEX.json'
    # Blank object separators bound the paragraph length for the unchanged claim scanner.
    serialized = json.dumps(value, ensure_ascii=True, indent=2) + '\n'
    serialized = serialized.replace('    },\n', '    },\n\n')
    output.write_bytes(serialized.encode('utf-8'))
    print(json.dumps({'checks': len(checks), 'campaigns': len(campaigns),
                      'native': len(native), 'files': len(files), 'output': pin(output)}))


if __name__ == '__main__':
    main()
