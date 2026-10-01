"""Replay the immutable old diagnostic counterexample in owned ignored fixtures."""
import hashlib
import json
import os
import pathlib
import subprocess
import uuid

ROOT = pathlib.Path(__file__).resolve().parents[5]
BASE = '2307e3ad0739e0e1d9c3f186cdc568631086fddf'
REVIEW = pathlib.Path('C:/Users/poin/Documents/RMQ/lifecycle-implementation-20260920/native-p0-r1-review')
out = ROOT / '.lake/repair-r2' / ('old-reproduction-' + uuid.uuid4().hex)
out.mkdir(parents=True)
carrier = out / 'immutable-source'
carrier.mkdir()
paths = ['scripts/packed_native_lifecycle_storage_replay.ps1', 'scripts/packed_native_lifecycle_integrity_check.ps1', 'scripts/owned_process_tree.ps1', 'native/packed-rmq/tests/lifecycle_storage_probe.c', 'lean-toolchain', 'docs/internal/extensions/lifecycle-native-p0/REGISTRY.json']
source_pins = []
for name in paths:
    data = subprocess.check_output(['git', '-C', str(ROOT), 'show', BASE + ':' + name])
    path = carrier / name
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(data)
    source_pins.append(dict(path=name, bytes=len(data), sha256=hashlib.sha256(data).hexdigest()))
(carrier / '.gitignore').write_text('.lake/\n', encoding='utf-8')
for args in [('init', '-q'), ('config', 'core.autocrlf', 'false'), ('-c', 'core.excludesfile=', 'add', '--all'), ('-c', 'user.name=RMQFixture', '-c', 'user.email=fixture@invalid', 'commit', '-qm', 'immutable exact-base source carrier')]:
    subprocess.check_call(['git', '-C', str(carrier), *args], env=dict(os.environ))
old = subprocess.check_output(['git', '-C', str(ROOT), 'show', BASE + ':docs/internal/extensions/lifecycle-native-p0/repair-r1/integrity_controls.ps1'])
(out / 'old-controls.ps1').write_bytes(old)
source = (REVIEW / 'run_actual_outer_control.ps1').read_text(encoding='utf-8-sig')
source = source.replace("$repo='C:/Users/poin/.codex/worktrees/587c/RMQ'", "$repo='" + carrier.as_posix() + "'")
source = source.replace("$control=Join-Path $repo 'docs/internal/extensions/lifecycle-native-p0/repair-r1/integrity_controls.ps1'", "$control='" + (out / 'old-controls.ps1').as_posix() + "'")
source = source.replace("$held=$mutex.WaitOne(0)", "$held=$mutex.WaitOne(600000)")
source = source.replace("Write-Output 'DEFERRED_MUTEX_BUSY';exit 0", "throw 'host mutex unavailable'")
driver = out / 'replay.ps1'
driver.write_text(source, encoding='utf-8')
receipt = REVIEW / 'actual-outer-diagnostic-68bbac4f331c4ff5b154e4c68e983681/RECEIPT.json'
assert hashlib.sha256(receipt.read_bytes()).hexdigest().upper() == 'D47623CC4480AD592093871D59224ED8DB3B33B5E34D65C64F3BBD08BF7C83F7'
record = dict(base=BASE, immutableSource=str(carrier), sourcePins=source_pins, oldSource=dict(path=str(out/'old-controls.ps1'), bytes=len(old), sha256=hashlib.sha256(old).hexdigest()), historicalReceipt=str(receipt), driver=str(driver), output=str(out))
(out/'IDENTITY.json').write_text(json.dumps(record, indent=2)+'\n', encoding='utf-8')
print(str(out), flush=True)
raise SystemExit(subprocess.call(['pwsh', '-NoProfile', '-ExecutionPolicy', 'Bypass', '-File', str(driver)], env=dict(os.environ)))
