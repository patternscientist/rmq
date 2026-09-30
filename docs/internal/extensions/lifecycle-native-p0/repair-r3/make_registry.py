"""Freeze explicit expected bytes before executing any regression."""
import base64
import json
from pathlib import Path

out = Path(__file__).resolve().parent / 'CONTROL_REGISTRY.json'
assert not out.exists()
b64 = lambda b: base64.b64encode(b).decode('ascii')
rows = []
for context, code, stdout, stderr in [
    ('success', 0, b'EXPECTED SUCCESS\r\n', b''),
    ('error', 7, b'EXPECTED CONTEXT\r\n', b'PROCESS: expected failure\r\n')]:
    variants = [('exact', 'none', b'')]
    variants += [(name + '-' + stream, stream, extra)
                 for name, extra in [('bom', b'\xef\xbb\xbf'), ('nul', b'\0'),
                                     ('shy', b'\xc2\xad'), ('ascii', b'EXTRA\r\n')]
                 for stream in ['stdout', 'stderr']]
    for name, stream, extra in variants:
        rows.append(dict(id=f'literal-{context}-{name}', mode='literal',
                         predicate='Assert-LNOuterCapture', tier='actual emitted child',
                         stdout=b64(stdout + (extra if stream == 'stdout' else b'')),
                         stderr=b64(stderr + (extra if stream == 'stderr' else b'')),
                         expectedStdout=b64(stdout), expectedStderr=b64(stderr),
                         exit=code, verdict='accept' if stream == 'none' else 'reject',
                         failure='' if stream == 'none' else f'STREAM: literal-{context}-{name} {stream} differs'))
for name, emitted, expected, failure in [
    ('lf-crlf', b'line\n', b'line\r\n', 'differs'),
    ('normalization', 'caf\u0065\u0301\r\n'.encode(), 'caf\u00e9\r\n'.encode(), 'differs'),
    ('zero-width', 'line\u200b\r\n'.encode(), b'line\r\n', 'differs'),
    ('nonbreaking-space', 'a\u00a0b\r\n'.encode(), b'a b\r\n', 'differs'),
    ('invalid-utf8', b'\xff', b'', 'invalid-utf8'),
    ('overlong-utf8', b'\xc0\x80', b'', 'invalid-utf8'),
    ('literal-codepoints', '\ufeff\x00\u00ad\r\n'.encode(), '\ufeff\x00\u00ad\r\n'.encode(), '')]:
    rows.append(dict(id='holdout-'+name, mode='literal', predicate='Assert-LNOuterCapture',
                     tier='actual emitted child', stdout=b64(emitted), stderr='',
                     expectedStdout=b64(expected), expectedStderr='', exit=0,
                     verdict='accept' if not failure else 'reject',
                     failure=('STREAM: holdout-'+name+' stdout differs') if failure == 'differs' else failure))
for name, expression, category in [
    ('null', '$null', 'empty'), ('empty-array', '@()', 'empty'),
    ('empty-string', "@('')", 'empty'), ('whitespace', "@('  ')", 'empty'),
    ('unknown', "@('unknown')", 'unknown'), ('duplicate', "@('focused','focused')", 'duplicate'),
    ('late-empty', "@('focused','')", 'empty'),
    ('late-unknown', "@('focused','unknown')", 'unknown'),
    ('unknown-bom', "@(('focused'+[char]0xFEFF))", 'unknown'),
    ('unknown-nul', "@(('focused'+[char]0))", 'unknown')]:
    rows.append(dict(id='selector-'+name, mode='selector', predicate='certify_profiles parameter boundary',
                     tier='actual script boundary in captured child', expression=expression,
                     verdict='reject', failure='CERTIFY-SELECTOR: '+category))
rows += [dict(id='selector-focused', mode='focused', predicate='certify_profiles -> run_owned -> Assert-LNWrapperCapture',
              tier='actual focused native run', verdict='accept'),
         dict(id='integrity-caller-pair', mode='integrity', predicate='unchanged harness_stream_controls -> integrity_controls -> Assert-LNOuterCapture',
              tier='source-derived integrity callers, native 0/7, runner 0/1', verdict='accept')]
out.write_bytes((json.dumps(dict(version=1, defaultProfiles=['focused','full','integrity','dependencies','checks','claims'], controls=rows), indent=2) + '\n').encode('utf-8'))
print(f'FROZEN: {len(rows)} exact controls')
