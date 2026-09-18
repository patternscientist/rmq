"""Append the PRE-1-R2 cases to builder_cases.json and bump its version to 2.

Reads the base blob text (LF), writes LF text. Fragments are taken from the
base blobs of the mutated modules so that each `before` occurs exactly once.
"""
import json
import subprocess
import sys

REPO = r'C:/Users/poin/Documents/RMQ/.claude/worktrees/pre1-r2-consumer-markers'
BASE = 'a0c93e9cf4d3c93856f5756ff6a7271da2b821ff'
surfaces = dict(arg.split('=', 1) for arg in sys.argv[2:])


def blob(path):
    return subprocess.run(['git', '-C', REPO, 'show', '%s:%s' % (BASE, path)], capture_output=True, check=True).stdout.decode('utf-8')


runfacts = blob('RMQ/Core/WordRAM/Construction/Proof/RunFacts.lean')
start_line = '  halts : ∃ outBase, (run program (builderBudget xs.length) s0).final.status = .halted outBase\n'
end_line = '    { halts := ⟨sF.regs 3, by rw [hrun]; exact hst⟩\n'
refine_line = '  refine\n' + end_line
a = runfacts.index(start_line)
b = runfacts.index(refine_line) + len(refine_line)
fragment = runfacts[a:b]
assert runfacts.count(fragment) == 1
middle = fragment[len(start_line):-len(refine_line)]

halts_weak = ('  halts : ∃ fuel, (run program fuel s0).final.status = s0.status\n' + middle +
              '  refine\n    { halts := ⟨0, rfl⟩\n')
halts_larger = ('  halts : ∃ outBase, (run program (2000000000 + 2000000000 * xs.length) s0).final.status = .halted outBase\n' +
                middle +
                '  have hlargerHalts : ∃ outBase,\n'
                '      (run program (2000000000 + 2000000000 * xs.length) s0).final.status = .halted outBase := by\n'
                '    have hle : ts.length ≤ 2000000000 + 2000000000 * xs.length := by\n'
                '      have := builderBudget_eq_mul_add xs.length\n'
                '      omega\n'
                '    have hbig := hR.fuel_extension hstop (2000000000 + 2000000000 * xs.length - ts.length)\n'
                '    rw [Nat.add_sub_cancel\' hle] at hbig\n'
                '    exact ⟨sF.regs 3, by rw [hbig]; exact hst⟩\n'
                '  refine\n    { halts := hlargerHalts\n')

safety = blob('RMQ/Core/WordRAM/Construction/Safety.lean')
safe_before = ('/-- Every transition of a run is safe and lands in a fitting state. -/\n'
               'def Run.Safe (W : Nat) (program : List BInstr) (r : Run) : Prop :=\n'
               '  ∀ t ∈ r.transitions,\n'
               '    Prim.Safe W program.length t.before t.instruction.primitive ∧ t.after.Fits W\n')
assert safety.count(safe_before) == 1
safe_after = ('/-- Every transition of a run is safe and lands in a fitting state. -/\n'
              'def Run.Safe (W : Nat) (program : List BInstr) (r : Run) : Prop :=\n'
              '  ∀ t ∈ r.transitions,\n'
              '    Prim.Safe W (program.length + 1) t.before t.instruction.primitive ∧ t.after.Fits W\n'
              '\n'
              'theorem Prim.Safe.succ_length {W len : Nat} {s : State} {p : Prim} (h : Prim.Safe W len s p) :\n'
              '    Prim.Safe W (len + 1) s p := by\n'
              '  refine ⟨h.1, ?_⟩\n'
              '  have h2 := h.2\n'
              '  cases p <;> simp only [Prim.SafeAt] at h2 ⊢ <;> first | exact h2 | omega\n'
              '\n'
              'instance {W len : Nat} {s : State} {p : Prim} : Coe (Prim.Safe W len s p) (Prim.Safe W (len + 1) s p) :=\n'
              '  ⟨Prim.Safe.succ_length⟩\n')

new_cases = [
    {"id": "B53_RUNFACTS_HALTS_WEAKEN", "kind": "mutation", "path": "RMQ/Core/WordRAM/Construction/Proof/RunFacts.lean",
     "profile": "capstone", "before": fragment, "after": halts_weak, "expected": "reject", "expectedStage": "consumer",
     "expectedSurface": surfaces['B53']},
    {"id": "B54_RUNFACTS_HALTS_FUEL_LARGER", "kind": "mutation", "path": "RMQ/Core/WordRAM/Construction/Proof/RunFacts.lean",
     "profile": "capstone", "before": fragment, "after": halts_larger, "expected": "reject", "expectedStage": "consumer",
     "expectedSurface": surfaces['B54']},
    {"id": "B55_RUN_SAFE_LENGTH_WEAKEN", "kind": "mutation", "path": "RMQ/Core/WordRAM/Construction/Safety.lean",
     "manifest": "rehash", "before": safe_before, "after": safe_after, "expected": "reject", "expectedStage": "consumer",
     "expectedSurface": surfaces['B55']},
]

text = blob('docs/internal/extensions/pre1/builder_cases.json')
assert text.startswith('{\n  "version": 1,\n  "cases": [\n')
assert text.endswith('\n    }\n  ]\n}\n')
text = text.replace('{\n  "version": 1,\n', '{\n  "version": 2,\n', 1)


def render(case):
    parts = ['    {']
    keys = list(case.keys())
    for i, k in enumerate(keys):
        comma = ',' if i < len(keys) - 1 else ''
        parts.append('      %s: %s%s' % (json.dumps(k), json.dumps(case[k], ensure_ascii=False), comma))
    parts.append('    }')
    return '\n'.join(parts)


body = text[:-len('\n  ]\n}\n')]
body += ',\n' + ',\n'.join(render(c) for c in new_cases) + '\n  ]\n}\n'
parsed = json.loads(body)
assert parsed['version'] == 2 and len(parsed['cases']) == 55
open(sys.argv[1], 'w', encoding='utf-8', newline='\n').write(body)
import hashlib
print('content sha256', hashlib.sha256(body.encode('utf-8')).hexdigest())
print('fragment lines', fragment.count('\n'))
