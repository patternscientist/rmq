"""Check the native supplement's exact-byte inputs under Git checkout settings."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True

ROOT = Path(__file__).resolve().parents[1]
CONTRACT = 'docs/internal/extensions/lifecycle-native1/CONTRACT_REQUIREMENTS.json'
MATRIX = 'docs/internal/extensions/lifecycle-native1/ACCEPTANCE_MATRIX.frozen.md'
CASES = 'scripts/lifecycle_native_cases.json'
SOURCES = {
    'RMQ/Core/SuccinctClose/EndpointFringe/InteriorCandidate/InteriorDirectory/SparseLevelWidth.lean': (
        'canonicalRelativeRmmInteriorCost33WitnessShape',
        'canonicalRelativeRmmInteriorCost33WitnessInput'),
    'RMQ/Core/SuccinctFinal/RAM/ReviewerReachabilitySmall.lean': (
        'reviewerSingletonBeforeLCAState', 'reviewerSingletonBeforeRankState',
        'reviewerIncreasingSixteenBeforeLCAState'),
}
PATHS = [CONTRACT, MATRIX, CASES, *SOURCES]


def git(repo, *args):
    try:
        return subprocess.check_output(['git', '-C', str(repo), *args], stderr=subprocess.PIPE)
    except subprocess.CalledProcessError as error:
        raise RuntimeError(error.stderr.decode('utf-8', errors='replace')) from error


def sha(data):
    return hashlib.sha256(data).hexdigest()


class CheckoutTests(unittest.TestCase):
    def setUp(self):
        self.parent = (ROOT / '.lake/native-checkout-tests').resolve()
        self.parent.mkdir(parents=True, exist_ok=True)
        self.temporary = tempfile.TemporaryDirectory(dir=self.parent)
        self.root = Path(self.temporary.name).resolve()
        self.assertTrue(self.root.is_relative_to(self.parent))
        self.repo = self.root / 'repo'
        self.repo.mkdir()
        git(self.repo, 'init', '-q')
        self.attributes = (ROOT / '.gitattributes').read_bytes()
        for path in PATHS:
            target = self.repo / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(git(ROOT, 'show', 'HEAD:' + path))
        self.base = json.loads((ROOT / 'docs/internal/extensions/lifecycle-native1/BASE_IDENTITY.json').read_text(encoding='utf-8'))

    def tearDown(self):
        self.assertTrue(self.root.is_relative_to(self.parent))
        self.temporary.cleanup()

    def checkout(self, setting, name, attributes=None):
        (self.repo / '.gitattributes').write_bytes(self.attributes if attributes is None else attributes)
        git(self.repo, '-c', 'core.autocrlf=false', 'add', '.')
        git(self.repo, '-c', 'user.name=RMQ checkout fixture', '-c',
            'user.email=fixture@example.invalid', 'commit', '--allow-empty', '-qm', 'checkout fixture')
        output = self.root / name
        # A separate clone has its own index and stat cache. checkout-index
        # --prefix plus the donor index does not model a clean Git checkout.
        git(self.root, 'clone', '--quiet', '--no-hardlinks', '--no-checkout',
            str(self.repo), str(output))
        git(output, 'config', 'core.autocrlf', setting)
        git(output, 'checkout', '--quiet', 'HEAD', '--', '.')
        self.assertEqual(git(output, 'status', '--porcelain').strip(), b'')
        git(output, 'diff', '--check')
        return output

    def assert_frozen_inputs(self, output):
        # These pins are the actual production predicates' independent values.
        contract = (output / CONTRACT).read_bytes()
        self.assertEqual(sha(contract), '736ff55b84516d1b0c7e45f5dbf8193df98846ea259f0ef5b3caefbe7cd6bc5f')
        frozen = json.loads(contract)['frozen_matrix']
        matrix = (output / MATRIX).read_bytes()
        self.assertEqual(len(matrix), frozen['bytes'])
        self.assertEqual(sha(matrix), frozen['sha256'])
        self.assertEqual(sha((output / CASES).read_bytes()), '9dc72366b51592f18dc50e52d2b799c736dc047e6166538a0a880192062985fd')
        for path, names in SOURCES.items():
            source = (output / path).read_bytes()
            for name in names:
                source, count = re.subn(
                    rb'(?m)^@\[macro_inline\]\r?\n(?=(?:private )?def ' + name.encode() + rb'\b)',
                    b'', source)
                self.assertEqual(count, 1)
            pins = [entry for entry in self.base['files'] if entry['path'] == path]
            self.assertEqual(len(pins), 1)
            self.assertEqual(sha(source), pins[0]['rawSHA256'])

    def test_all_five_inputs_under_each_git_setting(self):
        for setting in ('true', 'false', 'input'):
            with self.subTest(autocrlf=setting):
                self.assert_frozen_inputs(self.checkout(setting, setting))

    def test_each_missing_rule_reproduces_its_own_byte_failure(self):
        for index, path in enumerate(PATHS):
            with self.subTest(path=path):
                lf = path in (CONTRACT, MATRIX)
                suffix = ' -text' if lf else ' text eol=crlf'
                attributes = self.attributes.replace((path + suffix).encode(), b'# omitted one rule')
                self.assertNotEqual(attributes, self.attributes)
                output = self.checkout('true' if lf else 'false', 'missing-' + str(index), attributes)
                with self.assertRaises(AssertionError):
                    self.assert_frozen_inputs(output)
                blob = git(ROOT, 'show', 'HEAD:' + path)
                expected = blob if lf else blob.replace(b'\r\n', b'\n').replace(b'\n', b'\r\n')
                self.assertNotEqual(sha((output / path).read_bytes()), sha(expected))


if __name__ == '__main__':
    unittest.main()
