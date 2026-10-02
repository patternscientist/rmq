#!/usr/bin/env python3
"""Create and verify an unpublished, Git-derived RMQ source bundle (stdlib only)."""

import argparse
import hashlib
import json
import re
from pathlib import Path, PurePosixPath
import subprocess
import zipfile

MANIFEST = 'RMQ-SOURCE-MANIFEST.json'


def git(repo, *args):
    return subprocess.check_output(['git', '-C', str(repo), *args])


def safe_name(name):
    path = PurePosixPath(name)
    if (not name or '\\' in name or ':' in name or path.is_absolute()
            or any(p in ('', '.', '..') for p in name.split('/'))):
        raise ValueError(f'Unsafe archive path: {name!r}')
    return name


def digest(data):
    return hashlib.sha256(data).hexdigest()


def verify(archive):
    with zipfile.ZipFile(archive) as bundle:
        names = bundle.namelist()
        if len(names) != len(set(names)):
            raise ValueError('Duplicate archive paths')
        for name in names:
            safe_name(name)
        manifest = json.loads(bundle.read(MANIFEST))
        if manifest.get('schema') != 'rmq-source-bundle/1':
            raise ValueError('Unknown manifest schema')
        files = manifest['files']
        if set(names) != set(files) | {MANIFEST}:
            raise ValueError('Manifest/archive file set differs')
        for name, entry in files.items():
            data = bundle.read(name)
            if len(data) != entry['bytes'] or digest(data) != entry['sha256']:
                raise ValueError(f'Content mismatch: {name}')
        if bundle.read('lean-toolchain').decode().strip() != manifest['lean_toolchain']:
            raise ValueError('Toolchain mismatch')
        if f'version = "{manifest["version"]}"' not in bundle.read('lakefile.toml').decode():
            raise ValueError('Package version mismatch')
    return manifest


def create(repo, destination):
    repo = repo.resolve()
    if git(repo, 'status', '--porcelain').strip():
        raise ValueError('Commit or account for working-tree changes before packaging')
    commit = git(repo, 'rev-parse', 'HEAD').decode().strip()
    # Read objects directly. git archive can apply checkout conversions and
    # export attributes; neither belongs in an exact-blob source bundle.
    entries = []
    for record in git(repo, 'ls-tree', '-rz', commit).split(b'\0'):
        if not record:
            continue
        metadata, raw_name = record.split(b'\t', 1)
        mode, kind, oid = metadata.decode('ascii').split()
        name = safe_name(raw_name.decode('utf-8'))
        if kind != 'blob' or mode not in ('100644', '100755'):
            raise ValueError(f'Unsupported Git tree entry: {name}')
        if name == MANIFEST:
            raise ValueError('Reserved manifest path is already tracked')
        entries.append((name, mode, oid))
    objects = subprocess.check_output(
        ['git', '-C', str(repo), 'cat-file', '--batch'],
        input=''.join(oid + '\n' for _, _, oid in entries).encode('ascii'))
    payloads = {}
    modes = {}
    offset = 0
    for name, mode, oid in entries:
        end = objects.index(b'\n', offset)
        actual_oid, kind, raw_size = objects[offset:end].decode('ascii').split()
        if actual_oid != oid or kind != 'blob':
            raise ValueError(f'Unexpected Git object response: {name}')
        size = int(raw_size)
        start = end + 1
        end = start + size
        if size < 0 or end >= len(objects) or objects[end:end + 1] != b'\n':
            raise ValueError(f'Truncated Git object response: {name}')
        payloads[name] = objects[start:end]
        modes[name] = int(mode, 8) & 0o777
        offset = end + 1
    if offset != len(objects):
        raise ValueError('Trailing Git object response bytes')
    required = ('lakefile.toml', 'CITATION.cff', 'lean-toolchain')
    missing = [name for name in required if name not in payloads]
    if missing:
        raise ValueError('Missing tracked package metadata: ' + ', '.join(missing))
    match = re.search(r'^version\s*=\s*"([^"]+)"', payloads['lakefile.toml'].decode(), re.M)
    if match is None:
        raise ValueError('Missing package version')
    version = match.group(1)
    citation_versions = re.findall(r'^version:[ \t]*([^\r\n]*?)[ \t]*\r?$',
                                   payloads['CITATION.cff'].decode(), re.M)
    if citation_versions != [version]:
        raise ValueError('CITATION.cff and lakefile.toml versions differ')
    manifest = {
        'schema': 'rmq-source-bundle/1', 'commit': commit, 'version': version,
        'lean_toolchain': payloads['lean-toolchain'].decode().strip(),
        'files': {name: {'bytes': len(data), 'sha256': digest(data)}
                  for name, data in sorted(payloads.items())},
    }
    payloads[MANIFEST] = (json.dumps(manifest, indent=2, sort_keys=True)+'\n').encode()
    modes[MANIFEST] = 0o644
    destination.parent.mkdir(parents=True, exist_ok=True)
    # Exclusive creation avoids silently replacing a previously reviewed artifact.
    with destination.open('xb') as output:
        with zipfile.ZipFile(output, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as bundle:
            for name, data in sorted(payloads.items()):
                info = zipfile.ZipInfo(name, date_time=(1980, 1, 1, 0, 0, 0))
                info.create_system = 3
                info.external_attr = (0o100000 | modes[name]) << 16
                info.compress_type = zipfile.ZIP_DEFLATED
                bundle.writestr(info, data)
    verify(destination)
    return manifest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, default=Path(__file__).resolve().parents[1])
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument('--output', type=Path, help='new local ZIP path; never publishes')
    action.add_argument('--verify', type=Path, help='verify existing ZIP contents against its manifest')
    args = parser.parse_args()
    archive = args.verify or args.output
    manifest = verify(archive) if args.verify else create(args.repo, archive)
    print(json.dumps({'archive': str(archive.resolve()), 'sha256': digest(archive.read_bytes()),
                      'commit': manifest['commit'], 'version': manifest['version'],
                      'files': len(manifest['files']), 'verified': True,
                      'verification': 'manifest consistency; claimed commit is not authenticated'}, indent=2))


if __name__ == '__main__':
    main()
