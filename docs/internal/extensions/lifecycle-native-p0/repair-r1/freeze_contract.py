"""One-time pre-edit freeze; strict Git bytes, never PowerShell text serialization."""
import hashlib, json, pathlib, subprocess

ROOT = pathlib.Path(__file__).resolve().parents[5]
OUT = pathlib.Path(__file__).resolve().parent
BASE = '0c873072e84be9e1d65edab1985bcff1d23abef1'
P = 'docs/internal/extensions/lifecycle-native-p0/ACCEPTANCE_MATRIX.md'
raw = subprocess.check_output(['git', '-C', str(ROOT), 'show', f'{BASE}:{P}'])
raw.decode('utf-8', errors='strict')
rows = [r for r in raw.splitlines() if r.startswith(b'| `')]
assert len(rows) == 12 and all(len(r.split(b'|')) == 10 for r in rows)
requirements = {
 'NP0R1-INTEGRITY': 'Every entered native replay verification lifecycle records and enforces an independent final integrity outcome in finally, including prior compiler/probe errors, unexpected diagnostics, timeout and partially initialized identity inventories. Verify every captured source/tool/generated-artifact pin and the declared live tracked/index/untracked baseline; absence of required final verification is failure or explicitly uncovered, never success. Preserve the original stage error separately from integrity errors. Detect unexpected changes without silently overwriting unrelated user data. Commit positive and changed-pin/tree controls through the actual production verifier/finalization path, including failure plus integrity failure, success plus integrity failure, and an ordinary failed stage with intact inputs. All owned fixture mutations are restored in their own finally and leave the real candidate unchanged. Keep existing owned-process cleanup and exact diagnostics/exits.',
 'NP0R1-TOOLCHAIN': "Bind the substantive local implementation dependencies of the actually invoked pinned compiler/runtime to the replay receipt and final identity verification. In particular include clang's normal-import libclang-cpp.dll, libLLVM-19.dll and libc++.dll and inspect the invoked tools' remaining local non-system dependency closure; state the external OS/system-library and dynamic-loading boundary honestly. Include the generated link map in final available-artifact integrity checks. Commit a completeness/tamper control using actual dependency inventory and isolated manifest/file fixtures, without modifying installed tools. The original bea5ce75 runner/receipt must fail the new completeness predicate for the independently measured missing dependencies while a complete unchanged inventory passes. No installation, runtime upgrade, tool replacement or claim of universal loader/compiler verification."
}
for key, req in requirements.items():
 rows.append(f'| `{key}` | {req} | Local verification repair | Production finalizer and exact dependency checks | Captured run inputs -> final verification -> success/receipt | Isolated unchanged, tampered, failed-stage and incomplete inventories | Pending; append evidence | Open at freeze |'.encode())
frozen = b'\n'.join(rows) + b'\n'
for name in ('ACCEPTANCE_ROWS.txt', 'ACCEPTANCE_MATRIX.md', 'START.json'):
 assert not (OUT / name).exists(), f'refuse to overwrite freeze: {name}'
(OUT / 'ACCEPTANCE_ROWS.txt').write_bytes(frozen)
header = b'# LIFE-NATIVE-P0-R1 frozen acceptance matrix\n\nFrozen from the canonical template before runner edits. Historical inherited rows remain byte-identical; dispositions are appended.\n\n'
header += b'| ID | Exact frozen requirement | Scope | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge attempted and outcome | Evidence obtained | Status / residual gap |\n| --- | --- | --- | --- | --- | --- | --- | --- |\n'
plan = b'\n## Verification plan\n\nDevelopment: strict frozen-row and scope checks, isolated production finalizer and dependency controls, bounded startup and real one-case selection. Final: frozen full native SelfTest under Local\\RMQLifecycleImplementationHeavy20260920, outer 1200 s (prior 113-162 s), unchanged compiler/probe/descendant 120/30/8 s; exact 23 cases and 65 inherited checks; pin/tree integrity; diff, per-commit/exact-base strict design, final claim coverage and hygiene. Claims compose verified original full coverage with unchanged-policy changed-root rescan only if outside paths/bytes and scanner environment match; otherwise full scan with 7200 s deadline. Conditional: no new Lean build if all formal/toolchain bytes and baseline receipts verify; aggregate and fresh-blind campaign audit remain coordinator-owned.\n\nTarget: repair integrity/provenance for the existing ownership probe and future reviewed adapter. No Lean/C/ABI mutation or changed semantic oracle. Stop only on closure, exact obstruction, external blocker or redirection.\n'
(OUT / 'ACCEPTANCE_MATRIX.md').write_bytes(header + frozen + plan)
start = dict(handle='LIFE-NATIVE-P0-R1', worktree=str(ROOT), base=BASE,
 branch=subprocess.check_output(['git', '-C', str(ROOT), 'branch', '--show-current'], text=True).strip(),
 initialHead=BASE, initialClean=True, governance='7b227c49ef2ec044b702126cc41c9add847eed01',
 runtimeCatalog=['rmq-audit-prompt','rmq-coordinator','rmq-proof-sprint'], requiredSkill='rmq-proof-sprint', preflight='PASS',
 frozenRowsSha256=hashlib.sha256(frozen).hexdigest(),
 scope=['scripts/packed_native_lifecycle_storage_replay.ps1','scripts/packed_native_lifecycle_integrity_check.ps1','docs/internal/extensions/lifecycle-native-p0/repair-r1/','docs/internal/extensions/lifecycle-native-p0/BOUNDARY.md: optional citation only','docs/internal/WORKFLOW_DESIGN_DECISIONS.md: append','docs/internal/DESIGN_DECISIONS.md: conditional append'])
(OUT/'START.json').write_text(json.dumps(start, indent=2)+'\n', encoding='utf-8')
print(json.dumps(start, indent=2))
