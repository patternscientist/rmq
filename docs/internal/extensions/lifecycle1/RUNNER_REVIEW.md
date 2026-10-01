# LIFE-1 runner review

This is a bounded source review and an isolated PowerShell classifier check.
It is not a mutation replay, native validation run, final-tree certification,
or acceptance decision. The reviewer did not run Lean, Lake, the dependency
campaign, or the native validator. Only this review file was edited. Actual
campaign evidence must supply its own source identities, complete process
outputs, expected verdicts, restoration checks, and final receipts.

Reviewed sources: [dependency runner](../../../../scripts/lifecycle_dependency_replay.ps1),
[26-case registry](../../../../scripts/lifecycle_dependency_cases.json),
[native wrapper](../../../../scripts/lifecycle_validator.ps1), and
[native validator](../../../../RMQ/Validation/PackedLifecycle.lean).

## Concrete finding and follow-up

The original text classifier (`Assert-Reject`, then lines 115-139) counted only
located `.lean:line:column:` diagnostic headers. With exit code 1 and empty
stderr, it accepted this stdout:

```text
RMQ/Validation/LifecycleContract.lean:1:1: error: Type mismatch
error: unrelated compiler failure
```

Replacing the second line with either `uncaught exception: unrelated compiler
failure` or `PANIC: unrelated compiler failure` was also accepted. The expected
surface was `checkC02_retained` at lines 1-2 with one `type-mismatch` diagnostic.
This demonstrated that an expected failure could conceal an unrelated failure.
The reproduction extracted only the `Assert-Reject` function through the
PowerShell AST; it did not invoke the runner's top-level code or any compiler.

The required correction was to classify the complete output, reject unrelated
diagnostics, preserve legitimate multiline Lean message bodies, and retain an
expected-accept control. The owner changed both compiler invocations to
`--json` (lines 291 and 297 in the reviewed revision). The revised classifier
(lines 111-149) parses every stdout line as a diagnostic JSON object, requires
the exact diagnostic count, source, theorem range, error severity and class,
and continues to reject stderr, timeout and output truncation.

An isolated follow-up check accepted one valid expected JSON diagnostic and
rejected each of the three trailing text lines above with
`LIFE1-DIAGNOSTIC: non-JSON compiler output`. The runner also contains these
three negative controls at lines 230-232, plus extra-diagnostic and wrong-class
controls. The original counterexamples are therefore covered in this reviewed
revision. This check does not substitute for running the committed self-test
or the full producer/consumer campaign.

The dependency-runner bytes checked after the correction had SHA-256
`ee6bfc344da3c03bcfaf1bb80a068eed7e2bf87109900321033556db4dc6bd3b`.
Line numbers above refer to that snapshot; later changes need their own receipt.

## Other reviewed boundaries

- Registry and selection: the dependency runner fixes all 26 IDs, order,
  producer/consumer paths and normalized registry hash. Negative edits must
  change a unique source fragment. Empty, malformed, unknown and duplicate
  selector channels reject. Startup selects the two identity cases; focused
  selection and full selection remain distinct.
- Failure ownership: the mutated producer must compile with empty output
  before its expected consumer rejection can count. Negative producer artifact
  hashes must change. Consumer rejection checks exact mapped theorem surfaces;
  producer compile failures cannot pass as dependency sensitivity.
- Restoration: original source and selected artifact hashes are checked before
  and after cases. Each case restores private Capstone and Provenance imports
  from original artifacts and verifies their hashes. The finalizer checks
  originals and removes the bounded private shadow directory. Source review
  establishes these checks exist; campaign receipts establish they executed.
- Native boundaries: the wrapper requires the named executable, checks exactly
  16 registry IDs and output ordering, separates startup/single/full modes,
  checks selector failures, uses the owned bounded process helper, and compares
  selected source/binary identities before and after. It does not implicitly
  build or fall back to an older validator.
- Native reach: `runFixture` executes `Executable.initialOwner` through
  `runOwner` on `Layout.program`, then `Executable.queryOwner` for later
  requests. `counted_owner` connects the independent counting fold's endpoint
  to production execution. Checks cover the independent strict-minimum answer,
  retained arrays, scalar allocation/release counts, resource peak, and a dirty
  entry control that changes one witnessed register-clear instruction.

No other concrete defect was found in the reviewed boundaries. This statement
is limited to the inspection above and makes no claim that a campaign, final
gate, exact-commit audit, or acceptance row has passed.
