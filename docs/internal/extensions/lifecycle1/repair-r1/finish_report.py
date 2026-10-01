"""Render observed check metadata into the blocked report; does not assign verdicts."""
from pathlib import Path
import hashlib
import json
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
CHECKS = ROOT / '.lake/repair-r1/checks'
BASE = '12bd7f0fc2c87f2c9bdef3825bd92477e48e3433'


def read(path):
    return json.loads(path.read_bytes())


def main():
    specifications = [
        ('final-default-build-pinned', 'Default build', 'PASS; warm verified cache'),
        ('final-named-build-pinned', 'Named lifecycle builds', 'PASS; five named targets'),
        ('final-validator-pwsh-startup', 'Current PowerShell startup', 'PASS; registry/startup only'),
        ('final-validator-pwsh-full', 'Current PowerShell full16', 'PASS; nine owned child launches'),
        ('final-validator-winps-startup', 'Windows PowerShell startup', 'PASS; registry/startup only'),
        ('final-validator-winps-full', 'Windows PowerShell full16', 'PASS; nine owned child launches'),
        ('final-dependency-selftest', 'Dependency self-test', 'PASS; empty baseline limitation remains'),
        ('final-dependency-startup', 'Dependency startup', 'PASS; D20/P06 positives'),
        ('final-dependency-focused', 'Dependency focused D15', 'PASS; exact expected rejection'),
        ('final-dependency-full', 'Dependency full26', 'PASS; 23 rejects, three accepts'),
        ('f2-controls-pwsh', 'Final control revision, current PowerShell', 'PASS; exact 67 controls'),
        ('f2-registry-pwsh', 'Current PowerShell registry campaign', 'PASS; 12 controls / 24 P-Q children'),
        ('f2-controls-winps', 'Final control revision, Windows PowerShell', 'BLOCKED; 32 selector/wrapper controls pass, D01 HashData failure'),
        ('f2-registry-winps', 'Windows PowerShell registry campaign', 'PASS; 12 controls / 24 P-Q children'),
        ('f2-winps-finalizer', 'Windows intact-pin finalizer P', 'BLOCKED; exact protected HashData failure'),
        ('f2-winps-timeout', 'Windows descendant timeout', 'PASS; intended timeout, cleanup and restoration'),
        ('final-original-contract', 'Original contract integrity', 'BLOCKED; inherited contract serialization'),
        ('final-hygiene', 'Trust hygiene scan', 'PASS; rg exit 1 with zero matches/diagnostics'),
        ('final-native-trust', 'Native-decision scan', 'PASS; rg exit 1 with zero matches/diagnostics'),
    ]
    lines = ['<!-- BEGIN-OBSERVED-CHECKS -->', '',
             '| Check | Observed disposition | Outer exit | Seconds / deadline |',
             '| --- | --- | --- | --- |']
    for name, title, disposition in specifications:
        value = read(CHECKS / name / 'result.json')
        result = value['result']
        lines.append(f'| {title} (`{name}`) | {disposition} | {result["ExitCode"]} | {result["DurationSeconds"]} / {result["DeadlineSeconds"]} |')
    lines += ['', 'The table is a display of the bound receipts, not a replacement verdict',
              'predicate. ROW_DISPOSITIONS.md generation checks the exact successful',
              'prefixes, mappings, source pins and specific failure surfaces. EVIDENCE_INDEX.json',
              'retains every attempt, including development and failed launches. All listed',
              'outer checks completed without an unexpected timeout or output overflow.',
              'The intentional inner sleeper timeouts are separate expected outcomes.', '',
              'Final control source is 7c406b15bdc12333d323c92641ab6c6dad6af7a2.',
              'Current PowerShell completes every frozen control; Windows full selection',
              'remains all 66 applicable IDs, of which exactly S01-S23 and W01-W09 finish',
              'before D01 fails. The remaining dependency/finalizer positives cannot run',
              'through the protected hash implementation. They are not skipped passes.', '',
              'The source-bound Windows F01 positive exits 1 with exactly:', '',
              '```text',
              "Method invocation failed because [System.Security.Cryptography.SHA256] does not contain a method named 'HashData'.",
              '```', '',
              'Its captured baseline is empty because capture itself fails; restored=true',
              'there establishes no intact-pin result. The component is BLOCKED, not an',
              'expected-reject success. The actual dependency boundary records the same',
              'specific failure in its accepted P before any Q can be credited.', '']
    for profile, directory in [('pwsh', 'f2-controls-pwsh'), ('winps', 'f2-winps-timeout')]:
        fixture = read(ROOT / f'.lake/repair-r1/{directory}/T01_DESCENDANT_TIMEOUT/fixture/result.json')
        lines.append(f'The final {profile} timeout observed child root PID {fixture["pids"]["root"]} and descendant PID {fixture["pids"]["descendant"]}; all observed owned IDs were absent afterward and the ambient selector was restored.')
        lines.append('')
    lines += ['Current-pwsh finalizer F03 separately retains the prior stage failure and',
              'the changed-pin integrity failure, exits 1, reports restored=false, removes',
              'the valid shadow, and releases its mutex without abandonment. F10/F11',
              'retain actual locked-file cleanup failures. All fixture cleanup is separately',
              'recorded after the production verdict.', '',
              'The changed paths relative to the exact base are:', '', '```text']
    changed = subprocess.check_output(['git', 'diff', '--name-only', BASE, '--'], cwd=ROOT, text=True).splitlines()
    new = subprocess.check_output(['git', 'ls-files', '--others', '--exclude-standard'], cwd=ROOT, text=True).splitlines()
    lines += sorted(set(changed + new))
    lines += ['```', '', '<!-- END-OBSERVED-CHECKS -->']
    report = HERE / 'REPORT.md'
    text = report.read_text(encoding='utf-8')
    marker = '<!-- FINAL-OBSERVED-CHECKS -->'
    begin = '<!-- BEGIN-OBSERVED-CHECKS -->'
    end = '<!-- END-OBSERVED-CHECKS -->'
    if marker in text:
        text = text.replace(marker, '\n'.join(lines))
    elif begin in text and end in text:
        left, remainder = text.split(begin, 1)
        _, right = remainder.split(end, 1)
        text = left + '\n'.join(lines) + right
    else:
        raise ValueError('report observation marker absent')
    report.write_bytes(text.encode('utf-8'))
    raw = report.read_bytes()
    print(json.dumps({'report': str(report), 'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest(),
                      'changedPaths': len(set(changed + new)), 'status': 'BLOCKED'}))


if __name__ == '__main__':
    main()
