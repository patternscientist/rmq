#!/usr/bin/env pwsh
# Hub import-closure guard.
#
# The repository claims, in RMQHub.lean's own docstring, that the hub layer
# "imports only modules that do not depend on RMQ ranges, Cartesian shapes,
# Euler tours, or any RMQ backend". That claim was TRUE at 745a3c5 but enforced
# by nothing: `lake build RMQHub` and scripts/hub_axiom_check.lean would both
# still pass if someone added `import RMQ.Core.Spec` to ModelHub.lean, and no
# lint had a hub rule. This script converts the assertion into a checked
# property.
#
# It is a NEGATIVE check: it fails when the closure GROWS beyond the pinned set,
# not when it shrinks. Growth is the direction that silently breaks the
# architectural claim; shrinking is reported so the pin can be tightened.
#
# Exit 0 iff the transitive import closure of RMQ/Core/ModelHub.lean is exactly
# the pinned allowlist below.
#
# Run with -SelfTest to verify the walker actually detects an injected
# RMQ-specific import. A guard that cannot fail is not a guard.

[CmdletBinding()]
param(
  [switch]$SelfTest
)

$ErrorActionPreference = 'Stop'
$repoRoot = (Resolve-Path (Join-Path (Split-Path -Parent $MyInvocation.MyCommand.Path) '..')).Path
$failures = 0

function Fail([string]$m) { Write-Host "HUB-CLOSURE: FAIL: $m"; $script:failures = $script:failures + 1 }
function Info([string]$m) { Write-Host "HUB-CLOSURE: $m" }

# Pinned closure, measured at commit e3362d4. Every entry is a model-layer or
# generic-utility module. Nothing here mentions RMQ ranges, Cartesian shapes,
# Euler tours, or an RMQ backend. Adding to this list is a deliberate act and
# needs a workflow decision explaining why the hub grew.
$allowed = @(
  'RMQ.Core.Amortized',
  'RMQ.Core.AmortizedSequence',
  'RMQ.Core.Cost',
  'RMQ.Core.ListLemmas',
  'RMQ.Core.LowerBound',
  'RMQ.Core.ModelHub',
  'RMQ.Core.PayloadLowerBound',
  'RMQ.Core.RAM',
  'RMQ.Core.Refine',
  'RMQ.Core.TableModel',
  'RMQ.Core.WordRAM'
)

# Modules whose presence in the hub closure would falsify the docstring claim
# outright. Reported separately from a mere allowlist miss because the diagnosis
# is different: this is not "the hub grew", it is "the hub is no longer a hub".
$rmqSpecific = @(
  'RMQ.Core.Spec', 'RMQ.Core.Cartesian', 'RMQ.Core.Shape', 'RMQ.Core.Backend',
  'RMQ.Core.Window', 'RMQ.Core.LCA', 'RMQ.Core.Reduction', 'RMQ.Core.Succinct',
  'RMQ.Core.SuccinctFinal', 'RMQ.Core.EncodingLowerBound'
)

function ModuleToPath([string]$root, [string]$module) {
  $rel = ($module -replace '\.', [IO.Path]::DirectorySeparatorChar) + '.lean'
  $path = Join-Path $root $rel
  if (Test-Path -LiteralPath $path) { return (Resolve-Path -LiteralPath $path).Path }
  return $null
}

function Get-Closure([string]$root, [string]$entryFile) {
  $seen = [ordered]@{}
  $stack = New-Object System.Collections.Stack
  $stack.Push((Resolve-Path -LiteralPath $entryFile).Path)
  while ($stack.Count -gt 0) {
    $f = $stack.Pop()
    if ($seen.Contains($f)) { continue }
    $seen[$f] = $true
    foreach ($line in (Get-Content -LiteralPath $f)) {
      if ($line -match '^import\s+(.+?)\s*$') {
        foreach ($mod in ($Matches[1].Trim() -split '\s+')) {
          if ($mod -eq '') { continue }
          $p = ModuleToPath $root $mod
          if ($p -and -not $seen.Contains($p)) { $stack.Push($p) }
        }
      }
    }
  }
  return @($seen.Keys | ForEach-Object {
    ($_.Substring($root.Length + 1) -replace '[\\/]', '.') -replace '\.lean$', ''
  })
}

$entry = Join-Path $repoRoot 'RMQ/Core/ModelHub.lean'
if (-not (Test-Path -LiteralPath $entry)) {
  Fail 'RMQ/Core/ModelHub.lean not found'
}
else {
  $closure = Get-Closure $repoRoot $entry | Sort-Object

  $unexpected = @($closure | Where-Object { $allowed -notcontains $_ })
  $missing = @($allowed | Where-Object { $closure -notcontains $_ })
  $tainted = @($closure | Where-Object { $rmqSpecific -contains $_ })

  foreach ($m in $tainted) {
    Fail "hub closure reaches RMQ-specific module '$m'; RMQHub.lean's docstring claim is falsified"
  }
  foreach ($m in $unexpected) {
    if ($rmqSpecific -notcontains $m) {
      Fail "hub closure grew: '$m' is not in the pinned allowlist (add it deliberately, with a workflow decision)"
    }
  }
  if ($missing.Count -gt 0) {
    # Shrinking is not a soundness problem, but a stale pin hides future growth.
    Info ("note: pinned modules no longer in the closure (tighten the pin): {0}" -f ($missing -join ', '))
  }
  if ($failures -eq 0) {
    Info ("closure of RMQ/Core/ModelHub.lean is exactly the pinned {0} modules; no RMQ-specific module reachable" -f $closure.Count)
  }
}

if ($SelfTest) {
  Info '--- self-test: can this guard actually fail? ---'
  $tmp = Join-Path ([IO.Path]::GetTempPath()) ("hubselftest-" + [Guid]::NewGuid().ToString('N'))
  try {
    # Minimal fake tree: a hub that imports an RMQ-specific module.
    $core = Join-Path $tmp 'RMQ/Core'
    New-Item -ItemType Directory -Force -Path $core | Out-Null
    Set-Content -LiteralPath (Join-Path $core 'Spec.lean') -Value '-- fake' -Encoding utf8
    Set-Content -LiteralPath (Join-Path $core 'ModelHub.lean') -Value 'import RMQ.Core.Spec' -Encoding utf8
    $c2 = Get-Closure $tmp (Join-Path $core 'ModelHub.lean')
    $detected = ($c2 -contains 'RMQ.Core.Spec')
    if ($detected) { Info '  SELFTEST PASS injected RMQ.Core.Spec import is reached by the walker' }
    else { Write-Host 'HUB-CLOSURE: SELFTEST FAIL walker did not reach the injected import'; $failures = $failures + 1 }

    # And that such a module is classified as tainting, not merely unexpected.
    if ($rmqSpecific -contains 'RMQ.Core.Spec') { Info '  SELFTEST PASS RMQ.Core.Spec is classified RMQ-specific' }
    else { Write-Host 'HUB-CLOSURE: SELFTEST FAIL RMQ.Core.Spec not in the RMQ-specific list'; $failures = $failures + 1 }
  }
  finally {
    if (Test-Path -LiteralPath $tmp) { Remove-Item -Recurse -Force -LiteralPath $tmp -ErrorAction SilentlyContinue }
  }
}

if ($failures -gt 0) {
  Write-Host ("HUB-CLOSURE: RESULT: FAIL ({0} failure(s))" -f $failures)
  exit 1
}
Write-Host 'HUB-CLOSURE: RESULT: PASS'
exit 0
