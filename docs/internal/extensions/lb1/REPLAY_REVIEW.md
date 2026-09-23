Status: INCOMPLETE
Phase: independent source-only replay review; semantic campaign remains open.

# LB-1 replay source review

Reviewer: `/root/contract_review`. Review date: 2026-09-12 (UTC). This report's
original review covers replay registry version 1 (56 source cases); the parent
subsequently introduced version 2 (62 source cases). The exact version-1 registry
is retained at `evidence/REPLAY_REGISTRY_v1.json`. Source HEAD at review:
`0bbbe8ca4a937bc9782b2f7c5cc5419faa1a75a2`, with the new implementation and replay
files in the working tree. This is neither a semantic campaign verdict nor an
exact-commit acceptance audit. The auditor made no replay-source edits and ran
no Lean/Lake builds or semantic cases. The parent applied the fixes below while
the review continued.

Reviewed surfaces: `scripts/variable_payload_replay.ps1`,
`scripts/variable_payload_build.ps1`, `REPLAY_REGISTRY.json`,
`RMQ/Validation/VariablePayloadLowerBound.lean`, its generic consumer, the
producer marker regions, and the existing `owned_process_tree.ps1` interfaces.
The frozen replay and control requirements from this directory governed the
review.

## Findings and observed repairs

1. The original diagnostic-range calculation included the next declaration's
   first line. On the actual consumer, `checkO01` began at line 21 and its
   advertised last line was 26, also the start of `checkO02`. A neighboring error
   could therefore satisfy the wrong expected failing surface. The parent now
   computes the final included line from the half-open span end and includes
   inside/adjacent diagnostic controls using the same production predicate.

2. The omitted-selector full replay originally ran all 56 source cases before
   runtime startup. The runtime routine internally ordered list, known selector,
   and full runtime correctly, but this did not enforce startup before the source
   campaign. The parent now invokes that routine before the mutation loop and
   removes the later duplicate invocation.

3. Candidate-HEAD retrieval in the replay and Lean-version retrieval in the build
   script originally bypassed owned bounded subprocesses. The parent now uses
   `Invoke-RMQCheckedGit` for HEAD and `Invoke-RMQOwnedBoundedProcess` for version,
   preserving checked exits and stderr. Existing substantive Lean stages and
   repository-state queries already used the owned tooling.

No additional blocking source-level defect was found after these repairs. Their
semantic execution and final campaign results remain the parent's responsibility.

## Source reconstruction

- The literal script registry independently pins 56 cases: 16 optimality field
  weakenings, 33 reconstructed-machine field weakenings, one expected-accept
  baseline, and six additional public/generic/exactness/decoder/serializer cases.
  The JSON registry and six runtime IDs are compared in exact order. Empty,
  whitespace, malformed, unknown, and nonunique selections fail rather than
  selecting no work.
- All 49 field weakenings require a successful compilation of the mutated
  producer before the independently typed consumer fails at its specified
  declaration. The source mutations replace the corresponding proposition and
  initializer together, so failure of a stale constructor is not the advertised
  verdict. Public and generic proposition changes likewise require their
  producer to pass before their pinned consumers reject.
- Exactness deletion, null/wrong decoder, and zero-serializer mutations target
  their named original theorem propositions. The decoder failures concern the
  answer equation; the serializer failure concerns its actual inverse. These
  controls do not rely on differences in surrounding logs.
- Per-case and outer `finally` blocks restore the two mutated source files and
  their `.olean` files. Byte comparisons follow restoration. Bounded Git state
  checks then cover status including untracked files, worktree changes, and the
  index. Runtime fixture data consists of small tags; allocations are constructed
  inside the selected cases after selector validation.
- Process results preserve exit code, stdout, stderr, timeout, output limit and
  ownership. Resource limits are inconclusive. The existing owned primitive
  checks removal of its root and descendants. The parent-reported first deadline
  probe lacked a produced descendant and remains inconclusive; the later
  deadline probe and six command-boundary selector results are external campaign
  evidence, not results rerun by this auditor.

## Checks actually performed

- Both repaired PowerShell scripts parsed with zero syntax errors.
- Production mutation functions were invoked on in-memory copies for all 49
  field cases. Every case produced exactly one weakened field and one matching
  initializer; no source files were written by that exercise.
- The exactness deletion expression matched exactly one generic record field.
- `publicContract`, `composedConsumer`, and the individually typed `checkO01`
  through `checkO16` and `checkM01` through `checkM33` consumers were present.
- No actual producer/consumer mutation build, runtime case, subprocess deadline
  fixture, complete replay, or Lean trust check was executed in this review.

Source hashes after the observed repairs:

| Surface | SHA256 |
| --- | --- |
| `scripts/variable_payload_replay.ps1` | `FA9B1A331F9875BC7901B609384846C412673EB7BB29F292AE1CE292A31E41B4` |
| `scripts/variable_payload_build.ps1` | `5CD249C2CC350FC18F1758171D35A9D107E3221318174594A64614B213C04629` |
| Version-1 registry, now `evidence/REPLAY_REGISTRY_v1.json` | `8DBE317327D506F33430AF857C9AEB4238B8569A122672328247B2FEFF32A3D0` |

## Version-2 source addendum

After completing the frozen-row checker, the auditor inspected the six new
version-2 mutation branches statically on 2026-09-12 (UTC). The parent expanded
the registry to 62 cases; the original 49 cases remain proposition weakenings.

| New case | Mutation | Pinned failing consumer |
| --- | --- | --- |
| `F01-DELETE-MEMORY-RECOVERY` | Remove the optimality memory-recovery field and initializer | `checkO04` |
| `F02-DELETE-READ-BACKING` | Remove the reconstructed-machine positional-backing field and initializer | `checkM27` |
| `S01-SIBLING-MEMORY` | Replace recovery of the built memory by reflexivity on reconstructed memory | `checkO04` |
| `S02-SIBLING-RUN` | Replace the constructed/built run equality by reconstructed-run reflexivity | `checkO15` |
| `S03-SIBLING-BUDGET` | Replace the arbitrary budget B conclusion by the canonical upper-budget conclusion | `checkO09` |
| `H01-EMPTY-ONLY-DECODER` | Add `xs.length = 0` to the formerly all-input decoder contract | `checkO05` |

The `Custom` switch distinguishes an intentionally empty deletion replacement
from the default proposition-weakening text. Each branch changes the field and
its initializer together, requires the producer to compile, and then requires
the original exact-type consumer to fail. The substitutions preserve the
advertised category while changing its object, budget quantifier or input
domain; the specified consumers pin those distinctions. No additional source
bug was identified in this bounded inspection. No new case was executed or
kernel-checked by the auditor.

Version-2 snapshot hashes:

| Surface | SHA256 |
| --- | --- |
| `scripts/variable_payload_replay.ps1` | `A7281C8939FE044BE827FCCDD6CDEEF23DA31E1607FAB2FED07BE7A67420B8C9` |
| `REPLAY_REGISTRY.json` | `4DA98452C313B80C9E204BD2BE8DEE58522A8D5438351561690B99D22BD746B1` |

The next target is the bounded semantic campaign on frozen content, followed by
independent exact-commit acceptance. This source review narrows no frozen row.
