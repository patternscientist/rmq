"""LIFE-1-R4: build FAILURE_CONTROL_REGISTRY.json (v2) from the R3 v1 registry.

The 47 R3 control objects are copied from the exact Git blob of
repair-r3/FAILURE_CONTROL_REGISTRY.json at d27ffa34 with only these changes:
  * `baseExpectation` is re-derived for the v2 base ref d27ffa34 (every R3
    control is expected to satisfy its core predicates there, because the nine
    harness blobs at d27ffa34 equal those of the R3 candidate runs at a2e40779);
    the R3 value (relative to eb8e4f25) is kept as `r3BaseExpectation`;
  * setup-failure (S) controls gain `expect.capturedPins`, the number of pins
    the harness captures before the removed file, derived from the harness's
    capture order (see `CAPTURED`), never from a run of the repaired harness.
The thirteen R4 controls follow in a fixed order. Run from any directory:
  python make_registry.py <output-path>
"""
import copy, json, pathlib, subprocess, sys

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parents[4]
BASE = 'd27ffa341f4ed8ceccc46817455eb26c73b319a1'
V1 = 'docs/internal/extensions/lifecycle1/repair-r3/FAILURE_CONTROL_REGISTRY.json'

# Pins captured before the removed file, in each harness's capture order:
# RC  pins lifecycle_validator, environment, dependency_replay, owned_process_tree,
#     dependency_cases.json, then the removed validator executable -> 5.
# FC  registry (pinned before the try), the harness itself, then the removed
#     owned-process helper -> 2.
# K1  hashes every present source before dot-sourcing the removed helper; the
#     copy has 10 of the 11 source paths minus the removed helper -> 9 (the
#     helper and the absent executable are absent-verified, not captured).
# K2  dot-sources the removed helper before any capture -> 0.
# DC  the removed production script is the first pin -> 0.
# LV  per-path identity capture of 12 paths without Service.lean -> 11.
# IC  replay, integrity helper, owned-process helper, stream check, then the
#     removed probe source -> 4.
# DP  the removed historical RESULTS.json is the first pin -> 0.
# HS  stream registry, integrity_controls, replay, integrity helper,
#     owned-process helper, stream check, then the removed probe source -> 6.
CAPTURED = {'RC-S': 5, 'FC-S': 2, 'K1-S': 9, 'K2-S': 0, 'DC-S': 0, 'LV-S': 11, 'IC-S': 4, 'DP-S': 0, 'HS-S': 6}

def control(id_, harness, shape, fault, expect, base, rationale, deadline=180, variant=None, remove=False, **extra):
    e = {'exit': 'nonzero', 'stage': None, 'stageValue': None, 'integrity': None}
    e.update(expect)
    c = {'id': id_, 'harness': harness, 'shape': shape, 'profiles': ['pwsh', 'winps'], 'deadlineSeconds': deadline,
         'fault': fault, 'removeAtSetup': remove, 'variant': variant, 'expect': e, 'baseExpectation': base,
         'rationale': rationale, 'introducedIn': 'r4'}
    c.update(extra)
    return c

NEW = [
    control('K1-F', 'K1', 'F', 'fail', {'exitCode': 7, 'stage': [['child exit 7']], 'stageValue': {'name': 'ExitCode', 'value': 7}, 'verdict': 'fail'},
            'reject', 'Ordinary child failure (exit 7) with every pin intact: the durable verdict must be fail (audit P2-1); d27ffa34 records pass.'),
    control('K2-F', 'K2', 'F', 'fail', {'exitCode': 7, 'stage': [['child exit 7']], 'stageValue': {'name': 'ExitCode', 'value': 7}, 'verdict': 'fail'},
            'reject', 'Ordinary child failure (exit 7) with every pin intact: the durable verdict must be fail (audit P2-1); d27ffa34 records pass.'),
    control('K1-T', 'K1', 'T', 'sleep', {'exitCode': 2, 'stage': [['timed out or exceeded its output limit']], 'verdict': 'fail',
            'values': [{'name': 'TimedOut', 'value': True}, {'name': 'DeadlineSeconds', 'value': 3}]},
            'reject', 'A stage that sleeps 60 s under a real 3 s owned deadline: the helper times out and kills it, and the durable verdict must be fail (audit P2-1).',
            variant='deadline-short'),
    control('K2-T', 'K2', 'T', 'sleep', {'exitCode': 2, 'stage': [['timed out or exceeded its output limit']], 'verdict': 'fail',
            'values': [{'name': 'TimedOut', 'value': True}, {'name': 'DeadlineSeconds', 'value': 3}]},
            'reject', 'A stage that sleeps 60 s under a real 3 s owned deadline: the helper times out and kills it, and the durable verdict must be fail (audit P2-1).',
            variant='deadline-short'),
    control('K1-W', 'K1', 'W', 'block-durable', {'durableAbsent': True, 'stderr': [['R1-CHECK: durable result write failed']]},
            'reject', 'The stage turns result.json into a directory, so the durable write fails: the run must exit nonzero (audit P3-1); d27ffa34 exits 0.',
            faultTarget='.lake/repair-r1/checks/r3-control/result.json'),
    control('K2-W', 'K2', 'W', 'block-durable', {'durableAbsent': True, 'stderr': [['R2-CHECK: durable result write failed']]},
            'reject', 'The stage turns result.json into a directory, so the durable write fails: the run must exit nonzero (audit P3-1); d27ffa34 exits 0.',
            faultTarget='.lake/repair-r2/checks/r3-control/result.json'),
    control('LV-W', 'LV', 'W', 'block-durable', {'durableAbsent': True, 'stderr': [['LIFE1-VALIDATOR: durable result write failed']],
            'absentFiles': ['PASS.json'], 'stdoutAbsent': ['LIFE1-VALIDATOR PASS']},
            'reject', 'The validator double turns RESULT.json into a directory: no PASS.json, no PASS line, nonzero exit (audit P3-1); d27ffa34 writes PASS.json and exits 0.'),
    control('IC-U', 'IC', 'U', 'lock-cleanup', {'stage': [['fixture outer deadline/output failure']], 'cleanup': [['untracked restoration']],
            'pins': 'all-verified', 'values': [{'name': 'candidateUnchanged', 'value': True}, {'name': 'fixtureRestoration', 'value': False}]},
            'accept', 'An exclusive lock held until process exit makes the fixture restoration throw inside cleanup while the stage fails: stage error, cleanup error and all 7 verified pins plus the tree check are recorded (audit P3-2 (a)). R3 already handles this path, so d27ffa34 is expected to accept.',
            deadline=600),
    control('LV-E', 'LV', 'E', 'intact', {'stage': [['Missing rmq_lifecycle_validate.exe']], 'capturedPins': 11},
            'reject', 'The pinned validator executable is missing: the repaired validator records the unchanged diagnostic in RESULT.json with the other 11 identity pins re-verified (audit P3-3); d27ffa34 throws before its log root.',
            remove=True, removePath='.lake/build/bin/rmq_lifecycle_validate.exe'),
    control('IC-L', 'IC', 'L', 'change', {'integrity': [['INTEGRITY', 'packed_native_lifecycle_integrity_check.ps1'], ['real candidate changed']],
            'labels': [{'key': 'helper', 'entryKey': 'entryHelper', 'path': 'scripts/packed_native_lifecycle_integrity_check.ps1', 'status': 'changed'},
                       {'key': 'source', 'entryKey': 'entrySource', 'path': 'scripts/packed_native_lifecycle_storage_replay.ps1', 'status': 'verified'}]},
            'reject', 'A labelled pin (the integrity helper) changes during a passing stage: its entry value must appear only under entryHelper and helper must hold the changed post-run pin (audit P3-5).',
            deadline=600, faultTarget='scripts/packed_native_lifecycle_integrity_check.ps1'),
    control('HS-L', 'HS', 'L', 'change', {'integrity': [['INTEGRITY', 'integrity_controls.ps1']],
            'labels': [{'key': 'source', 'entryKey': 'entrySource', 'path': 'docs/internal/extensions/lifecycle-native-p0/repair-r1/integrity_controls.ps1', 'status': 'changed'},
                       {'key': 'registry', 'entryKey': 'entryRegistry', 'path': 'docs/internal/extensions/lifecycle-native-p0/repair-r2/HARNESS_STREAM_REGISTRY.json', 'status': 'verified'},
                       {'key': 'validator', 'entryKey': 'entryValidator', 'path': 'scripts/packed_native_lifecycle_stream_check.ps1', 'status': 'verified'}]},
            'reject', 'A labelled pin (the copied integrity_controls source) changes during a passing stage: its entry value must appear only under entrySource and source must hold the changed post-run pin (audit P3-5).',
            deadline=300, faultTarget='docs/internal/extensions/lifecycle-native-p0/repair-r1/integrity_controls.ps1'),
    control('K2-G', 'K2', 'G', 'git-hang', {'exitCode': 3, 'integrity': [['final HEAD unavailable', 'timed out after 60 s']], 'verdict': 'fail',
            'values': [{'name': 'timedOut', 'value': True}]},
            'timeout', 'A git double on PATH hangs once the stage has run: the final HEAD read must time out under the owned 60 s deadline and be recorded as an integrity error (audit P3-7); d27ffa34 hangs until the control deadline.',
            gitDouble=True),
    control('HS-G', 'HS', 'G', 'git-fail', {'stage': [['incomplete bounded capture']],
            'integrity': [['owned fixture/carrier status failed', 'git exit 128', 'R3-DOUBLE: injected git failure']]},
            'reject', 'A git double on PATH fails every call once the capture completes: the finalization carrier/fixture status must record the exit and stderr as integrity errors (audit P3-7).',
            deadline=900, variant='harness-carrier', gitDouble=True),
]

def main(out):
    v1 = json.loads(subprocess.run(['git', '-C', str(ROOT), 'cat-file', 'blob', BASE + ':' + V1], capture_output=True, check=True).stdout.decode('utf-8'))
    assert v1['schema'] == 'life1-r3-failure-controls-v1' and len(v1['controls']) == 47
    controls = []
    for c in v1['controls']:
        c = copy.deepcopy(c)
        c['r3BaseExpectation'] = c['baseExpectation']
        c['baseExpectation'] = 'accept'
        c['introducedIn'] = 'r3'
        if c['id'] in CAPTURED:
            c['expect']['capturedPins'] = CAPTURED[c['id']]
        controls.append(c)
    assert set(CAPTURED) == {c['id'] for c in controls if c['shape'] == 'S'}
    controls += NEW
    shapes = dict(v1['shapes'])
    shapes.update({
        'F': 'the child stage fails (exit 7) with every pin intact; the durable verdict is fail',
        'T': 'the child stage outlives a real short owned deadline; the durable verdict is fail and the helper records the timeout',
        'W': 'the durable result path is a directory, so the durable write fails; the run exits nonzero with no success marker',
        'U': 'an exception is raised inside cleanup/restoration (not the integrity step) while the stage fails; stage, cleanup and integrity results are all recorded',
        'E': 'the pinned validator executable is missing; the check runs inside the evidence region and the durable result records it',
        'L': 'a labelled entry pin changes; entry values appear only under entry* keys and the plain key holds the post-run pin',
        'G': 'a git double fails or hangs during finalization; the owned git call records exit, stderr or timeout as an integrity error',
    })
    reg = {
        'schema': 'life1-r4-failure-controls-v2', 'version': 2, 'baseRef': BASE,
        'harnessKeys': v1['harnessKeys'], 'shapes': shapes,
        'textSemantics': v1['textSemantics'] + ' R4 fields: expect.verdict is the exact finalization.verdict; expect.exitCode the exact process exit; expect.values exact typed values (repair-r4/predicates.ps1 Test-R4Values); expect.cleanup groups over the durable values and, structurally, over finalization.cleanupErrors; expect.labels entry-label predicates (Test-R4Labels); expect.durableAbsent/stderr/absentFiles/stdoutAbsent the durable-write-failure surface; expect.capturedPins the independent count of pins captured before the injected setup failure (Test-R4PinCoverage); expect.pins=all-verified requires every captured pin verified. Control fields: faultTarget and removePath override the recipe target/remove path; gitDouble prepends the R4 git double to PATH. baseExpectation timeout means the base harness does not finish before the control deadline.',
        'controls': controls,
    }
    data = (json.dumps(reg, indent=2, ensure_ascii=False) + '\n').encode('utf-8')
    pathlib.Path(out).write_bytes(data)
    print(len(controls), len(data))

if __name__ == '__main__':
    main(sys.argv[1])
