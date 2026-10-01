"""Integrity and clean-source checks for the local release bundle command."""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
import zipfile

sys.dont_write_bytecode = True

spec = importlib.util.spec_from_file_location('package_release', Path(__file__).with_name('package_release.py'))
package = importlib.util.module_from_spec(spec)
spec.loader.exec_module(package)


class PackageTests(unittest.TestCase):
    def setUp(self):
        # All temporary files live under this explicit task-owned test directory.
        self.parent = (Path(__file__).resolve().parents[1] / '.lake' / 'package-tests').resolve()
        self.parent.mkdir(parents=True, exist_ok=True)
        self.temporary = tempfile.TemporaryDirectory(dir=self.parent)
        self.root = Path(self.temporary.name).resolve()
        self.assertTrue(self.root.is_relative_to(self.parent))
        self.repo = self.root/'repo'
        self.repo.mkdir()
        self.git('init', '-q')
        (self.repo/'lakefile.toml').write_text('name = "rmq"\nversion = "1.0.0-rc.1"\n')
        (self.repo/'CITATION.cff').write_text('version: 1.0.0-rc.1\n')
        (self.repo/'lean-toolchain').write_text('leanprover/lean4:v4.22.0\n')
        (self.repo/'README.md').write_text('Test source\n')
        self.git('add', '.')
        self.git('-c', 'user.name=RMQ packaging fixture', '-c', 'user.email=fixture@example.invalid', 'commit', '-qm', 'fixture')
        self.archive = self.root/'source.zip'

    def tearDown(self):
        # Check the resolved recursive-cleanup target before removing the fixture.
        self.assertTrue(self.root.is_relative_to(self.parent))
        self.temporary.cleanup()

    def git(self, *args):
        return subprocess.check_output(['git', '-C', str(self.repo), *args], stderr=subprocess.STDOUT)

    def test_roundtrip_is_reproducible_and_commit_bound(self):
        first = package.create(self.repo, self.archive)
        second_path = self.root/'again.zip'
        package.create(self.repo, second_path)
        self.assertEqual(self.archive.read_bytes(), second_path.read_bytes())
        self.assertEqual(first['commit'], self.git('rev-parse', 'HEAD').decode().strip())
        self.assertEqual(set(first['files']), {'README.md','lakefile.toml','CITATION.cff','lean-toolchain'})
        self.assertEqual(package.verify(self.archive)['version'], '1.0.0-rc.1')

    def test_git_tar_mask_cannot_change_bundle_or_executable_modes(self):
        (self.repo/'run.sh').write_text('#!/bin/sh\nexit 0\n')
        self.git('add', 'run.sh')
        self.git('update-index', '--chmod=+x', 'run.sh')
        self.git('-c', 'user.name=RMQ packaging fixture', '-c',
                 'user.email=fixture@example.invalid', 'commit', '-qm', 'executable')
        self.git('config', 'tar.umask', '0002')
        package.create(self.repo, self.archive)
        self.git('config', 'tar.umask', '0077')
        second = self.root/'different-config.zip'
        package.create(self.repo, second)
        self.assertEqual(self.archive.read_bytes(), second.read_bytes())
        with zipfile.ZipFile(self.archive) as bundle:
            self.assertEqual(bundle.getinfo('README.md').external_attr >> 16, 0o100644)
            self.assertEqual(bundle.getinfo('run.sh').external_attr >> 16, 0o100755)

    def test_dirty_tree_and_overwrite_are_rejected(self):
        package.create(self.repo, self.archive)
        with self.assertRaises(FileExistsError):
            package.create(self.repo, self.archive)
        (self.repo/'README.md').write_text('Uncommitted change\n')
        with self.assertRaisesRegex(ValueError, 'working-tree'):
            package.create(self.repo, self.root/'dirty.zip')

    def test_changed_content_and_extra_file_are_rejected(self):
        package.create(self.repo, self.archive)
        with zipfile.ZipFile(self.archive) as original:
            entries = {n:original.read(n) for n in original.namelist()}
        entries['README.md'] = b'Changed source\n'
        altered = self.root/'altered.zip'
        with zipfile.ZipFile(altered, 'w') as output:
            for name,data in entries.items(): output.writestr(name,data)
        with self.assertRaisesRegex(ValueError, 'Content mismatch'):
            package.verify(altered)
        entries['unexpected.txt'] = b'extra'
        extra = self.root/'extra.zip'
        with zipfile.ZipFile(extra, 'w') as output:
            for name,data in entries.items(): output.writestr(name,data)
        with self.assertRaisesRegex(ValueError, 'file set differs'):
            package.verify(extra)

    def test_citation_version_mismatch_is_rejected_before_output(self):
        (self.repo/'CITATION.cff').write_text('version: 0.0.0\n')
        self.git('add', 'CITATION.cff')
        self.git('-c', 'user.name=RMQ packaging fixture', '-c',
                 'user.email=fixture@example.invalid', 'commit', '-qm', 'wrong citation')
        with self.assertRaisesRegex(ValueError, 'CITATION.cff and lakefile.toml versions differ'):
            package.create(self.repo, self.archive)
        self.assertFalse(self.archive.exists())

    def test_citation_version_prefix_is_rejected(self):
        (self.repo/'CITATION.cff').write_text('version: 1.0.0-rc.10\n')
        self.git('add', 'CITATION.cff')
        self.git('-c', 'user.name=RMQ packaging fixture', '-c',
                 'user.email=fixture@example.invalid', 'commit', '-qm', 'longer citation version')
        with self.assertRaisesRegex(ValueError, 'CITATION.cff and lakefile.toml versions differ'):
            package.create(self.repo, self.archive)
        self.assertFalse(self.archive.exists())

    def test_toolchain_metadata_mismatch_is_rejected(self):
        package.create(self.repo, self.archive)
        with zipfile.ZipFile(self.archive) as original:
            entries = {n:original.read(n) for n in original.namelist()}
        manifest = json.loads(entries[package.MANIFEST])
        # Keep every file and its digest intact; corrupt only the metadata.
        manifest['lean_toolchain'] = 'leanprover/lean4:v0.0.0'
        entries[package.MANIFEST] = json.dumps(manifest).encode()
        altered = self.root/'wrong-toolchain.zip'
        with zipfile.ZipFile(altered, 'w') as output:
            for name, data in entries.items():
                output.writestr(name, data)
        with self.assertRaisesRegex(ValueError, 'Toolchain mismatch'):
            package.verify(altered)

    def test_unsafe_archive_path_is_rejected(self):
        package.create(self.repo, self.archive)
        with zipfile.ZipFile(self.archive, 'a') as output:
            output.writestr('../escape.txt', b'not extracted')
        with self.assertRaisesRegex(ValueError, 'Unsafe archive path'):
            package.verify(self.archive)


if __name__ == '__main__':
    unittest.main()
