# RMQ Import Closure

This note separates the narrow RMQ paper import root from the broader checked
repository/testbed. The paper-facing root is:

```lean
import RMQPaper
```

`RMQPaper` imports `RMQ.Headlines.RMQ`, which exposes the RMQ-facing theorem
aliases without importing standalone rank/select public capstones,
standalone BP-navigation public capstones, union-find, archive roots, proposal
shims, legacy/compatibility barrels, or old `RMQ/Impl` roots.

## Commands Used

Build commands:

```powershell
lake build RMQPaper
lake build RMQ.Headlines
lake build RMQ
```

Closure counts were generated from workspace `import` lines with this
PowerShell import-graph walker:

```powershell
$root = (Get-Location).Path
function ModuleToPath([string]$module) {
  $rel = ($module -replace '\.', [IO.Path]::DirectorySeparatorChar) + '.lean'
  $path = Join-Path $root $rel
  if (Test-Path -LiteralPath $path) { return (Resolve-Path -LiteralPath $path).Path }
}
function Get-Imports([string]$path) {
  Get-Content -LiteralPath $path | ForEach-Object {
    if ($_ -match '^import\s+(.+)\s*$') {
      $Matches[1].Trim() -split '\s+' | Where-Object { $_ -ne '' }
    }
  }
}
function Get-Closure([string]$rootFile) {
  $resolved = (Resolve-Path -LiteralPath (Join-Path $root $rootFile)).Path
  $seen = [ordered]@{}
  function Visit([string]$path) {
    $full = (Resolve-Path -LiteralPath $path).Path
    if ($seen.Contains($full)) { return }
    $seen[$full] = $true
    foreach ($imp in Get-Imports $full) {
      $ipath = ModuleToPath $imp
      if ($ipath) { Visit $ipath }
    }
  }
  Visit $resolved
  @($seen.Keys)
}
function CountLines($files) {
  $sum = 0
  foreach ($f in $files) { $sum += (Get-Content -LiteralPath $f | Measure-Object -Line).Lines }
  $sum
}
```

The whole-workspace source count used:

```powershell
Get-ChildItem -Recurse -File -Include *.lean |
  Where-Object { $_.FullName -notmatch '\\.lake\\' -and $_.FullName -notmatch '\\.git\\' }
```

The public-root union row used these top-level roots:

```powershell
$publicRootFiles = @(
  'RMQPaper.lean',
  'RMQ.lean',
  'RMQExamples.lean',
  'RMQRankSelect.lean',
  'RMQBPNavigation.lean',
  'RMQUnionFind.lean',
  'RMQArchive.lean',
  'RMQHub.lean',
  'VerifiedDS.lean')
```

The smell-audit rows used this pattern over each import closure:

```powershell
$smell = 'RankSelectPublic|BPNavigationPublic|BPNavigationRAM|UnionFind|Archive|Proposal|Legacy|Compat|Obstruction|RMQ/Impl|RMQ\.Impl'
```

## Results

| Root / scope | Files | Lean LOC | Role | Smell audit |
| --- | ---: | ---: | --- | --- |
| `import RMQPaper` | 126 | 111555 | Required RMQ paper theorem root. | No rank/select public spokes, BP-navigation public spokes, union-find, archive, proposal, legacy, compat, obstruction, or old `RMQ/Impl` modules. |
| `import RMQ.Headlines.RMQ` | 125 | 111545 | RMQ-only headline alias surface used by `RMQPaper`. | Same clean result as `RMQPaper`. |
| `import RMQ.Headlines` | 160 | 147315 | Aggregate public alias barrel for RMQ plus standalone spokes. | No archive/proposal/legacy/compat/obstruction modules; it deliberately imports rank/select and BP-navigation public spokes. |
| `import RMQ` | 192 | 157243 | Broad stable RMQ library root with implementation families and historical checks. | Still imports checked obstruction modules listed below. |
| All public roots union | 226 | 169898 | Checked library/testbed public surface: RMQ, examples, rank/select, BP navigation, union-find, archive, hub, and VerifiedDS facades. | Broader than the paper theorem root by design. |
| Whole workspace Lean source | 250 | 174230 | Entire checked Lean workspace, including scripts and optional roots. | This is the source of the large presentation number, not the minimal paper root. |

The broad `import RMQ` root still reaches:

- `RMQ/Core/SuccinctSelect/Obstructions.lean`
- `RMQ/Core/SuccinctSelect/CloseSelect/TwoLevelObstruction.lean`
- `RMQ/Core/SuccinctSelect/CloseSelect/SparseExceptionCloseData/Obstructions.lean`

Those modules are checked negative/history surfaces retained under the broad
library root. They are not imported by `RMQPaper`. Neutral facts formerly mixed
into `SuccinctSelect/Obstructions.lean` now live in
`RMQ/Core/SuccinctSelect/AsymptoticFacts.lean`, which is the active positive
dependency used by the paper closure.

## Interpretation

The approximate 170k-line presentation number describes the whole repository
as a checked data-structure testbed: RMQ, lower bounds, rank/select,
BP-navigation, union-find, examples, validation, compatibility shims, archive,
and reviewer scripts. In this worktree the measured whole-workspace Lean source
count is 174230 lines.

The RMQ paper root is smaller: `RMQPaper` has 126 workspace source files and
111555 Lean LOC. That closure still includes the construction-heavy succinct
RMQ, lower-bound, and WordRAM/model-adequacy machinery needed for the paper
claims, but it no longer asks reviewers to mentally subtract unrelated public
spokes or historical/proposal/obstruction roots.
