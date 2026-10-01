# Artifact Reproducibility

This repository is a Mathlib-free Lean 4 artifact pinned by `lean-toolchain`.
The expected toolchain is:

```text
leanprover/lean4:v4.22.0
```

For the reviewer path through the artifact, see `../artifact/README.md`. For
paper claim rows and exact theorem/check correspondence, see
`PAPER_CLAIM_CORRESPONDENCE.md`.

## V1 source bundle

`scripts/package_release.py` uses only Python's standard library and Git. From
a clean committed candidate tree, choose a new output path outside tracked
source (for example under `.lake/release/`):

```powershell
python scripts/package_release.py --output .lake/release/rmq-1.0.0-rc.1-source.zip
python scripts/package_release.py --verify .lake/release/rmq-1.0.0-rc.1-source.zip
```

The ZIP contains exact Git-derived source plus `RMQ-SOURCE-MANIFEST.json` with
the commit, version, toolchain and each file's SHA256 digest. The command also
prints the archive digest, rejects a dirty tree and refuses to overwrite an
existing bundle. It does not publish, push or create a tag. Hash verification
establishes internal consistency against the recorded manifest. The manifest's
commit field is self-reported: `--verify` does not authenticate that commit or
compare archive files with a repository. Bind a distributed bundle to a reviewed
candidate by recording its archive SHA256 through a trusted channel and comparing
its file set, Git blob identities and modes with the expected commit. A consistently
rewritten archive and manifest can pass `--verify`; neither check proves theorem
correctness. The V1 delivery record includes the independent repository comparison.

The cheap packaging regressions run with `python scripts/test_package_release.py`.
CI runs them and the native checkout-byte regression on both Windows and Linux,
separately from the long Lean gate. The historical EH campaigns remain separate
manual evidence controls with exact commands in `internal/v1/evidence/COMMAND_LOG.md`.

After unpacking, the Lean smoke path in [V1_GUIDE.md](V1_GUIDE.md) works without
Git metadata. The full mutation campaigns below require a clean repository and
the historical Git objects they inspect. A source-only ZIP deliberately does
not replace that Git history. To reproduce the full gate, use the repository
checkout at the exact manifest commit; preserve the command logs and timings.

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
lake exe rmq_succinct_classic_validate
lake exe rmq_succinct_classic_cost_harness
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
curated spoke and lifecycle axiom scripts, compiles the independent lifecycle
contract/provenance clients, runs succinct cost/space lints, checks shim-import
boundaries, and performs `git diff --check`. It also runs
`scripts/packed_query_replay.ps1`, the committed replay campaign for the
accepted primitive-machine query
`RMQ.Headlines.succinctRMQFullyChargedPackedQuery`: each certificate field is
weakened in turn and must break its typed consumer, and the numeric-memory
runtime fixtures run on the actual program. The replay requires a clean
committed tree. The earlier query campaign has coordinator acceptance in
`internal/packed_query/PQ1_COORDINATOR_ACCEPTANCE.md`; a new V1 candidate
requires its own integrated verification and release audit.

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
of the two classic RMQ executables and the three axiom-check scripts, no
forbidden-token matches, and a clean whitespace diff check.

The artifact does not claim extracted-code performance, compiler/runtime
behavior, CPU-level timing, benchmarking, or constant optimization. The
declared final footprint is a safe layout overapproximation, not a proof of an
exact or minimal dynamic read set.
