# Artifact Reproducibility

This repository is a Mathlib-free Lean 4 artifact pinned by `lean-toolchain`.
The expected toolchain is:

```text
leanprover/lean4:v4.22.0
```

## One-Command Paper Artifact Gate

Run this command from the repository root:

```bash
scripts/reproduce_artifact.sh
```

It prints the `elan`, `lean`, and `lake` versions; runs `lake build`; explicitly
builds the public roots needed by broad axiom imports; runs the three
paper-facing axiom checks; runs the full repository gate when `pwsh` is
available; performs the forbidden-token scans below; checks local dirty-tree
whitespace with `git diff --check`; and, when `HEAD^` exists, checks the latest
committed patch with `git diff --check HEAD^..HEAD`.

In GitHub Actions, `pwsh` is required so that `scripts/gate.ps1` runs as part
of this artifact gate. Outside CI, the script reports a skipped full repository
gate if `pwsh` is unavailable.

## Paper Build And Axiom Checks

The paper-facing Lean checks run by the artifact gate are:

```bash
lake build
lake build RMQHub
lake build RMQRankSelect
lake build RMQBPNavigation
lake build RMQUnionFind
lake build VerifiedDS
lake build RMQArchive
lake build RMQExamples
lake build RMQ.Core.GenericSelectBPCompat
lake env lean scripts/headline_axiom_check.lean
lake env lean scripts/wordram_axiom_check.lean
lake env lean scripts/axiom_check.lean
```

## Full Repository Gate

The broader repository acceptance gate is:

```powershell
powershell -ExecutionPolicy Bypass -File scripts\gate.ps1
```

That gate builds the public roots, runs broader hygiene scans, checks the
curated spoke axiom scripts, runs succinct cost/space lints, checks shim-import
boundaries, and performs `git diff --check`.

## GitHub Actions

The `CI` workflow runs `scripts/gate.ps1` directly on push and pull request.
The `Artifact Reproducibility` workflow runs `scripts/reproduce_artifact.sh` on
push and tag events, tees output to `artifact-reproduction.log`, and uploads
that log as a workflow artifact. The release workflow reruns the reproduction
script for `v*` tags and attaches the reproduction log, theorem-map documents,
axiom-check scripts, and a source archive to the GitHub release.

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
