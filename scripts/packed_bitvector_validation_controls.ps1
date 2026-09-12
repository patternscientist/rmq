param(
  [AllowEmptyString()][string]$Case,
  [switch]$Startup,
  [switch]$ListRegistry,
  [string]$EvidenceTag = ('v1-' + [DateTime]::UtcNow.ToString('yyyyMMddHHmmssfff')),
  [int]$DeadlineSeconds = 300
)
$ErrorActionPreference = 'Stop'
$expected = @('baseline','wrong-packet','removed-fixture','wrong-crossing','restored')
$boundCase = $PSBoundParameters.ContainsKey('Case')
if (($Startup -and $ListRegistry) -or ($boundCase -and ($Startup -or $ListRegistry))) {
  [Console]::Error.WriteLine('BV1-SELECTOR FAIL: incompatible selectors')
  exit 2
}
if ($boundCase -and ([string]::IsNullOrWhiteSpace($Case) -or
    $Case -cne $Case.Trim() -or -not ($expected -ccontains $Case))) {
  [Console]::Error.WriteLine('BV1-SELECTOR FAIL: Case must be one exact nonempty registry name')
  exit 2
}
if ($EvidenceTag -notmatch '^[a-z0-9-]+$') { throw 'EvidenceTag must use lowercase letters, digits and hyphens.' }
if ($DeadlineSeconds -le 0) { throw 'DeadlineSeconds must be positive.' }
$repo = (Resolve-Path (Join-Path $PSScriptRoot '..')).Path
$fixtureRoot = Join-Path $repo 'docs/internal/extensions/bv1/controls/validation_v2'
$registryPath = Join-Path $fixtureRoot 'registry.json'
$registry = Get-Content -LiteralPath $registryPath -Raw | ConvertFrom-Json
if ($registry.version -ne 1 -or $registry.productionVersion -ne 2 -or
    ($registry.expected -join '|') -cne ($expected -join '|') -or
    ($registry.cases.id -join '|') -cne ($expected -join '|') -or $registry.cases.Count -ne 5) {
  throw 'Exact five-case validation-control registry mismatch.'
}
$productionPath = Join-Path $repo $registry.productionSource
if ((Get-FileHash -LiteralPath $productionPath -Algorithm SHA256).Hash -cne $registry.baselineSha256) {
  throw 'Production source differs from the frozen validation-control baseline.'
}
$utf8 = [Text.UTF8Encoding]::new($false,$true)
$baselineBytes = [IO.File]::ReadAllBytes((Join-Path $fixtureRoot 'baseline.lean'))
$baselineText = $utf8.GetString($baselineBytes)
if ((Get-FileHash -LiteralPath (Join-Path $fixtureRoot 'baseline.lean')).Hash -cne $registry.baselineSha256) {
  throw 'Frozen baseline fixture hash mismatch.'
}
foreach ($entry in $registry.cases) {
  if ($entry.file -notmatch '^[a-z_]+\.lean$') { throw 'Fixture file must be a local Lean basename.' }
  $path = Join-Path $fixtureRoot $entry.file
  if ((Get-FileHash -LiteralPath $path -Algorithm SHA256).Hash -cne $entry.sourceSha256) {
    throw ('Immutable fixture hash mismatch: ' + $entry.id)
  }
  $requiredText = $baselineText
  if ($entry.beforeText -cne '') {
    $count = [regex]::Matches($baselineText,[regex]::Escape($entry.beforeText)).Count
    if ($count -ne $entry.expectedOccurrences -or $count -ne 1) {
      throw ('Exact mutation occurrence mismatch: ' + $entry.id)
    }
    $requiredText = $baselineText.Replace($entry.beforeText,$entry.afterText)
  } elseif ($entry.afterText -cne '' -or $entry.expectedOccurrences -ne 0) {
    throw ('Invalid unchanged fixture mutation: ' + $entry.id)
  }
  $requiredBytes = $utf8.GetBytes($requiredText)
  $actualBytes = [IO.File]::ReadAllBytes($path)
  if ([Convert]::ToBase64String($requiredBytes) -cne [Convert]::ToBase64String($actualBytes)) {
    throw ('Fixture is not the exact recorded mutation: ' + $entry.id)
  }
}
if (($registry.cases | Where-Object id -CEQ 'restored').sourceSha256 -cne $registry.baselineSha256) {
  throw 'Restored fixture must be byte-identical to baseline.'
}
if ($Startup) {
  Write-Output 'BV1-VALIDATION-CONTROL-STARTUP version=1 expected=5'
  exit 0
}
if ($ListRegistry) { $expected | ForEach-Object { Write-Output $_ }; exit 0 }
$selected = if ($boundCase) { @($registry.cases | Where-Object id -CEQ $Case) } else { @($registry.cases) }
if ($selected.Count -eq 0) { throw 'Empty control selection is forbidden.' }
. (Join-Path $PSScriptRoot 'owned_process_tree.ps1')
$logs = Join-Path $repo 'docs/internal/extensions/bv1/commands'
$recordPath = Join-Path $logs ('validation-controls-' + $EvidenceTag + '.json')
if (Test-Path -LiteralPath $recordPath) { throw 'Validation-control evidence already exists.' }
$watchedRelative = @(
  'RMQ/Validation/PackedBitvector.lean',
  'scripts/packed_bitvector_probe.ps1',
  'scripts/packed_bitvector_selector_controls.ps1',
  'scripts/packed_bitvector_crossing.lean',
  'scripts/packed_bitvector_validation_controls.ps1',
  'docs/internal/extensions/bv1/controls/validation_v2/registry.json'
) + @($registry.cases | ForEach-Object { 'docs/internal/extensions/bv1/controls/validation_v2/' + $_.file })
$watchedPaths = @($watchedRelative | ForEach-Object { Join-Path $repo $_ })
$beforeHashes = @(Get-FileHash -LiteralPath $watchedPaths -Algorithm SHA256 | Select-Object Path,Hash)
$beforeStatus = @(& git -C $repo status --porcelain=v1 -- $watchedRelative)
$toolBin = 'C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0/bin'
$results = @()
foreach ($entry in $selected) {
  $path = Join-Path $fixtureRoot $entry.file
  $arguments = @('env','lean','--run',$path) + @($entry.arguments)
  $result = Invoke-RMQOwnedBoundedProcess -FilePath (Join-Path $toolBin 'lake.exe') `
    -Arguments $arguments -WorkingDirectory $repo -Stage ('validation-control-' + $entry.id + '-' + $EvidenceTag) `
    -DeadlineSeconds $DeadlineSeconds -OutputLimitBytes 8388608 -TempRoot $logs `
    -Environment @{ PATH = $toolBin + ';' + $env:PATH; LEAN_NUM_THREADS = '1' }
  $output = (@($result.Output) + @($result.StandardError)) -join "`n"
  $resourceFailure = $result.TimedOut -or $result.OutputLimitExceeded -or
    $output -match '(?im)(^|\s)error:|PANIC|stack overflow|out of memory|failed to synthesize'
  $surfaces = @($entry.expectedSurfaces | ForEach-Object {
    [pscustomobject]@{ exactText=$_; present=$output.Contains($_) }
  })
  $pass = -not $resourceFailure -and $result.ExitCode -eq $entry.expectedExit -and
    @($surfaces | Where-Object { -not $_.present }).Count -eq 0
  $results += [pscustomobject]@{
    id=$entry.id; sourceSha256=$entry.sourceSha256; arguments=$arguments
    expectedExit=$entry.expectedExit; expectedSurfaces=$surfaces
    resourceFailure=$resourceFailure; passed=$pass; result=$result
  }
  Write-Output "BV1-VALIDATION-CONTROL $($entry.id) passed=$pass expected-exit=$($entry.expectedExit) actual-exit=$($result.ExitCode)"
}
$afterHashes = @(Get-FileHash -LiteralPath $watchedPaths -Algorithm SHA256 | Select-Object Path,Hash)
$afterStatus = @(& git -C $repo status --porcelain=v1 -- $watchedRelative)
$unchanged = ($beforeHashes.Hash -join '|') -ceq ($afterHashes.Hash -join '|')
$statusUnchanged = ($beforeStatus -join "`n") -ceq ($afterStatus -join "`n")
$allPassed = $unchanged -and $statusUnchanged -and $results.Count -eq $selected.Count -and
  @($results | Where-Object { -not $_.passed }).Count -eq 0
$record = [ordered]@{
  version=1; productionVersion=2; evidenceTag=$EvidenceTag; platform='Windows'
  head=(& git -C $repo rev-parse HEAD); expected=$expected; selected=@($selected.id); executed=@($results.id)
  passed=$allPassed; sourceHashesBefore=$beforeHashes; sourceHashesAfter=$afterHashes
  scopedStatusBefore=$beforeStatus; scopedStatusAfter=$afterStatus
  exactRestoration=$unchanged; statusUnchanged=$statusUnchanged; deadlineSeconds=$DeadlineSeconds
  results=$results
}
[IO.File]::WriteAllText($recordPath,($record | ConvertTo-Json -Depth 16),[Text.UTF8Encoding]::new($false))
Write-Output "BV1-VALIDATION-CONTROL-REGISTRY executed=$($results.Count) expected=$($selected.Count) passed=$allPassed total=5 unchanged=$unchanged status-unchanged=$statusUnchanged"
if (-not $allPassed) { exit 1 }
exit 0

