"""LIFE-1-R4 receipt collector.

Usage: python collect_receipts.py <receipt-name> <source>=<committed-name> [...]

Copies each source file (an evidence file produced under this worktree's .lake)
into docs/internal/extensions/lifecycle1/repair-r4/receipts/<receipt-name>/.
Text is stored as UTF-8 with LF line endings: CRLF pairs written by Windows
PowerShell/.NET are normalized to LF, and a lone CR anywhere is refused, so no
committed receipt can make Git treat it as binary. INDEX.json records, for each
file, the source path, source bytes and SHA-256, the committed name and the
committed SHA-256, and whether normalization changed the bytes (then
sourceBytes == committedBytes + removed CR count). An existing receipt
directory is never overwritten: receipts are append-only evidence.
"""
import hashlib, json, pathlib, sys

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parents[4]

def main(argv):
    if len(argv) < 3:
        raise SystemExit('usage: collect_receipts.py <name> <source>=<committed> ...')
    name = argv[1]
    if not name or any(c not in 'abcdefghijklmnopqrstuvwxyz0123456789-' for c in name):
        raise SystemExit('receipt name must be lowercase [a-z0-9-]')
    out = HERE / 'receipts' / name
    if out.exists():
        raise SystemExit('receipt directory exists: ' + str(out))
    lake = (ROOT / '.lake').resolve()
    pairs = []
    for arg in argv[2:]:
        src, sep, dst = arg.partition('=')
        if not sep or not dst or dst.startswith('/') or '..' in pathlib.PurePosixPath(dst).parts or dst == 'INDEX.json':
            raise SystemExit('bad pair: ' + arg)
        p = pathlib.Path(src).resolve()
        if lake not in p.parents:
            raise SystemExit('source outside this worktree .lake: ' + src)
        pairs.append((p, dst))
    if len({d for _, d in pairs}) != len(pairs):
        raise SystemExit('duplicate committed name')
    files = []
    staged = []
    for p, dst in pairs:
        raw = p.read_bytes()
        raw.decode('utf-8')
        body = raw.replace(b'\r\n', b'\n')
        if b'\r' in body:
            raise SystemExit('lone CR in ' + str(p))
        staged.append((dst, body))
        files.append({'source': str(p), 'sourceBytes': len(raw), 'sourceSha256': hashlib.sha256(raw).hexdigest(),
                      'committed': dst, 'committedBytes': len(body), 'committedSha256': hashlib.sha256(body).hexdigest(),
                      'normalized': body != raw})
    out.mkdir(parents=True)
    for dst, body in staged:
        t = out / dst
        t.parent.mkdir(parents=True, exist_ok=True)
        t.write_bytes(body)
    index = json.dumps({'schema': 'life1-r4-receipt-index-v1', 'receipt': name, 'files': files}, indent=2) + '\n'
    (out / 'INDEX.json').write_bytes(index.encode('utf-8'))
    print(json.dumps({'receipt': name, 'files': len(files)}))

if __name__ == '__main__':
    main(sys.argv)
