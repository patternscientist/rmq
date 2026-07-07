# Reviewer Artifact Guide

This guide gives one reviewer path through the artifact. It complements the
compact claim packet in `CLAIMS.md`, the paper correspondence table in
`../docs/PAPER_CLAIM_CORRESPONDENCE.md`, and the code-orientation map in
`../docs/CODE_MAP.md`.

## Prerequisites

- Lean toolchain managed by `elan`, pinned by `lean-toolchain` to
  `leanprover/lean4:v4.22.0`.
- `lake`, supplied by the Lean toolchain.
- `bash` for `scripts/reproduce_artifact.sh`.
- `rg` for reviewer and hygiene scans.
- `git` for whitespace checks.
- `pwsh` or Windows PowerShell for `scripts/gate.ps1`. The reproduction script
  requires this in CI; outside CI it reports a skipped PowerShell gate if
  `pwsh` is not available.

The artifact is intended to run without Mathlib. Network access should not be
needed once the pinned Lean toolchain and Lake dependencies are available.

## One-Command Reproduction

From the repository root:

```bash
bash scripts/reproduce_artifact.sh
```

Expected successful output includes these section headers:

```text
== Tool versions ==
== lake build ==
== public root builds for axiom checks ==
== classic RMQ concrete validation ==
== headline axiom check ==
== WordRAM axiom check ==
== full axiom check ==
== full repository gate ==
== forbidden source tokens ==
== forbidden reduction shortcuts ==
== whitespace dirty-tree diff check ==
== whitespace committed-patch diff check ==
Artifact reproduction completed successfully
```

The forbidden-token sections should print:

```text
No forbidden source tokens found
No forbidden reduction shortcuts found
```

Rough timing is environment-dependent and dominated by `lake build` plus the
public root builds. Reviewers should record wall-clock time with the command
their shell provides, for example:

```bash
time bash scripts/reproduce_artifact.sh
```

On a warm checkout, later root builds may reuse Lake artifacts from the first
full build. On a cold checkout or a machine that must install the Lean
toolchain first, the first run may be substantially slower.

## Component Checks

If the full reproduction script is unavailable because `bash` or `pwsh` is
missing, run the explicit component checks below from the repository root and
record the blocker.

```powershell
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
lake env lean scripts\headline_axiom_check.lean
lake env lean scripts\wordram_axiom_check.lean
lake env lean scripts\axiom_check.lean
powershell -ExecutionPolicy Bypass -File scripts\gate.ps1
git diff --check
```

The two forbidden-token scans are:

```powershell
rg -n "\b(sorry|admit|axiom|unsafe|opaque|implemented_by|partial|extern|noncomputable)\b|import Mathlib" RMQ lakefile.toml
rg -n "native_decide|Lean\.ofReduceBool" RMQ
```

Expected result for both scans: no matches.

## Theorem Inspection

The fastest theorem-surface inspection route is:

```powershell
lake env lean scripts\headline_axiom_check.lean
lake env lean scripts\wordram_axiom_check.lean
lake env lean scripts\axiom_check.lean
```

These scripts print curated `#print axioms` results for the public headline
theorems, the WordRAM/read-store boundary, and the broad repository gate. The
expected result may include Lean's ordinary logical axioms such as classical
choice or propositional extensionality. It should not include `sorryAx`,
`Lean.ofReduceBool`, or project-specific axioms.

The main paper-facing names to inspect are listed in
`../docs/PAPER_CLAIM_CORRESPONDENCE.md`. Short public aliases live in
`../RMQ/Headlines.lean`; construction-heavy source theorem names and files are
in the correspondence table.

## What The Artifact Proves

The proof trust base is Lean kernel checking of committed theorem declarations
under the pinned toolchain. The public theorem surface proves, among other
things:

- exact half-open leftmost RMQ answers for the list-facing succinct RMQ theorem;
- `2*n + o(n)` payload accounting for the advertised succinct construction;
- model-level constant query cost, not Lean runtime or compiled-code
  performance;
- a final global trace with no synthetic cost-only marker events;
- successful final-query reads backed by counted flat payload words;
- supplied-store replay and exactness/cost transfer under footprint agreement;
- the conservative all-size modeled query-cost constant `196727`;
- the fast-regime modeled query-cost constant `118` under the real `2^15`
  readiness threshold; and
- an information-theoretic Catalan/Cartesian-shape RMQ lower bound.

## Validation And Examples

`lake exe rmq_succinct_classic_validate` runs executable validation for the
classic public succinct RMQ API. `lake build RMQExamples` checks small external
import examples.

Validation and examples are useful reviewer smoke tests. They are not part of
the proof trust base, and they do not replace Lean kernel checking of theorem
declarations.

## Non-Claims

The artifact does not claim:

- compiled Lean runtime performance;
- compiler correctness;
- CPU, cache, or memory-hierarchy semantics;
- extraction or benchmarking;
- production serialization;
- optimized constants;
- an exact or minimal dynamic read set; or
- unqualified priority status for the mechanization.

AI assistance and ADD records are workflow/provenance evidence, not proof
objects. See `../docs/AI_ASSISTED_DEVELOPMENT_NOTE.md` and
`../docs/ADD_PROVENANCE.md`.
