# Trust Base

This document is the short external-facing trust-base summary for the RMQ
artifact. It complements the detailed theorem inventory in
`docs/FAMILY_SUMMARY.md`.

## Build And Gate

The repository is pinned by `lean-toolchain` to Lean 4.22.0. The public gate is:

```powershell
powershell -ExecutionPolicy Bypass -File scripts\gate.ps1
```

That gate runs:

- `lake build`;
- `lake build RMQHub`;
- `lake build RMQRankSelect`;
- `lake build RMQArchive`;
- `lake build RMQExamples`;
- hygiene scans for `sorry`, `admit`, custom `axiom`, `unsafe`, `opaque`,
  `implemented_by`, `partial`, `extern`, `noncomputable`, and `import Mathlib`;
- a scan rejecting `native_decide` and `Lean.ofReduceBool` in checked source;
- the curated theorem axiom audits in `scripts/axiom_check.lean`,
  `scripts/archive_axiom_check.lean`, and
  `scripts/rank_select_axiom_check.lean`;
- succinct cost/space anti-vacuity linting; and
- compatibility-shim import linting.

GitHub Actions runs the same gate on pushes and pull requests.

## Expected Axioms

The load-bearing theorem checks are ordinary Lean `#print axioms` scripts. The
gate rejects `sorryAx` and `ofReduceBool`. The expected non-computational axioms
are the standard Lean axioms that can arise from propositional extensionality,
quotients, and classical choice, such as:

- `propext`;
- `Quot.sound`;
- `Classical.choice`.

There are no project-specific axioms in the checked theorem surface.

## Dependency Policy

The project is intentionally Mathlib-free at this stage. It uses Lean/Std plus
the `omega` tactic shipped with Lean. This is a local engineering choice, not a
claim that Mathlib would be inappropriate forever.

## Modeling Assumptions

The cost and space theorems are model-scoped:

- `Costed` and `RAM.Exec` count abstract operations such as indexed reads,
  branches, arithmetic primitives, and word operations.
- Payload-bit theorems count the modeled stored payload, not every proof-only
  field in a Lean structure.
- Theorems about `List`-level semantics are reference specifications, not
  claims that Lean's executable `List` representation has constant-time random
  access.

The repository documents these distinctions because hiding reference
computation behind a dummy constant-cost field is one of the main failure modes
for succinct-data-structure formalizations.

## Public Theorem Checks

For a concise public check of the headline theorem aliases, run:

```powershell
powershell -ExecutionPolicy Bypass -File scripts\headline_check.ps1
```

For the standalone rank/select spoke:

```powershell
lake build RMQRankSelect
lake env lean scripts\rank_select_axiom_check.lean
```

The small external import examples are checked by:

```powershell
lake build RMQExamples
```
