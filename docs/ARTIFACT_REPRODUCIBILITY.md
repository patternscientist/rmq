# Artifact Reproducibility

This repository is a Mathlib-free Lean 4 artifact pinned by `lean-toolchain`.
The expected toolchain is:

```text
leanprover/lean4:v4.22.0
```

## Build And Axiom Checks

Run these commands from the repository root:

```bash
lake build
lake env lean scripts/headline_axiom_check.lean
lake env lean scripts/wordram_axiom_check.lean
lake env lean scripts/axiom_check.lean
```

The one-command artifact gate is:

```bash
scripts/reproduce_artifact.sh
```

It prints the `elan`, `lean`, and `lake` versions, runs the build and curated
axiom checks, performs the forbidden-token scans below, and finishes with
`git diff --check`.

## Forbidden-Token Scans

The artifact gate rejects project source matches for:

```bash
rg -n "\b(sorry|admit|axiom|unsafe|opaque|implemented_by|partial|extern|noncomputable)\b|import Mathlib" RMQ lakefile.toml
rg -n "native_decide|Lean\.ofReduceBool" RMQ
```

Expected result: no matches. The curated `#print axioms` commands may report
Lean's ordinary logical axioms, such as propositional extensionality or
classical choice, but should not report `sorryAx` or project-specific axioms.

## Release Tags

For an artifact release, tag the checked commit and push the tag:

```bash
git tag -a vYYYY.MM.DD -m "RMQ paper artifact vYYYY.MM.DD"
git push origin vYYYY.MM.DD
```

The tag workflows run the same reproduction script and publish logs plus the
theorem-map documents as release artifacts.

## Expected Outputs And Non-Claims

Expected successful output is a completed Lake build, successful Lean execution
of the three axiom-check scripts, no forbidden-token matches, and a clean
whitespace diff check.

The artifact does not claim extracted-code performance, compiler/runtime
behavior, CPU-level timing, benchmarking, or constant optimization. The
declared final footprint is a safe layout overapproximation, not a proof of an
exact or minimal dynamic read set.
