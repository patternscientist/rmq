param(
  [AllowEmptyString()][string]$Case,
  [switch]$ListRegistry,
  [switch]$Startup,
  [switch]$ReplaySelectors,
  [int]$DeadlineSeconds = 180,
  [string]$EvidenceTag = ('v1-' + [DateTime]::UtcNow.ToString('yyyyMMddHHmmssfff') + '-' + [Guid]::NewGuid().ToString('N').Substring(0,8))
)
$ErrorActionPreference = 'Stop'
$caseNames = @(
  'access-original', 'access-raw-cell', 'rank-original', 'rank-length-cell',
  'select-original', 'select-count-cell', 'access-empty-memory', 'rank-empty-memory',
  'select-empty-memory', 'access-dormant-oversized', 'rank-dormant-oversized',
  'select-dormant-oversized'
)
$expectedRegistry = 'access-original|access-raw-cell|rank-original|rank-length-cell|select-original|select-count-cell|access-empty-memory|rank-empty-memory|select-empty-memory|access-dormant-oversized|rank-dormant-oversized|select-dormant-oversized'
if ($caseNames.Count -ne 12 -or @($caseNames | Select-Object -Unique).Count -ne 12 -or
    ($caseNames -join '|') -cne $expectedRegistry) {
  [Console]::Error.WriteLine('BV1-MACHINE-REGISTRY FAIL version=1 expected=12')
  exit 2
}
$boundCase = $PSBoundParameters.ContainsKey('Case')
$modeCount = [int]$boundCase + [int][bool]$ListRegistry + [int][bool]$Startup + [int][bool]$ReplaySelectors
if ($modeCount -gt 1 -or ($boundCase -and
    ([string]::IsNullOrWhiteSpace($Case) -or $Case -cne $Case.Trim() -or -not ($caseNames -ccontains $Case)))) {
  [Console]::Error.WriteLine('BV1-MACHINE-SELECTOR FAIL: choose one exact nonempty registry name or one mode')
  exit 2
}
if ($EvidenceTag -notmatch '^[a-z0-9-]+$' -or $DeadlineSeconds -lt 1 -or $DeadlineSeconds -gt 3600) {
  throw 'EvidenceTag must use lowercase letters, digits and hyphens; deadline must be1..3600 seconds.'
}
$repo = (Resolve-Path (Join-Path $PSScriptRoot '..')).Path
. (Join-Path $PSScriptRoot 'owned_process_tree.ps1')
$logs = Join-Path $repo 'docs/internal/extensions/bv1/commands'
[void](New-Item -ItemType Directory -Path $logs -Force)
$record = Join-Path $logs ('machine-controls-' + $EvidenceTag + '.json')
if (Test-Path -LiteralPath $record) { throw 'Machine control evidence already exists; choose a fresh EvidenceTag.' }
$toolBin = 'C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0/bin'
$startedUtc = [DateTime]::UtcNow.ToString('o')
$head = (& git -C $repo rev-parse HEAD).Trim()
$globalStatusBefore = @(& git -C $repo status --porcelain=v1)
if ($LASTEXITCODE -ne 0) { throw 'Unable to record initial repository status.' }

# Hash the local import closure of the actual executable fixture. Independent
# proof modules edited concurrently by other workers are outside this closure.
$queue = [Collections.Generic.Queue[string]]::new()
$queue.Enqueue('scripts/packed_bitvector_machine_controls.lean')
$sourceSet = [Collections.Generic.HashSet[string]]::new([StringComparer]::OrdinalIgnoreCase)
while ($queue.Count -gt 0) {
  $relative = $queue.Dequeue()
  if (-not $sourceSet.Add($relative)) { continue }
  $path = Join-Path $repo $relative
  if (-not (Test-Path -LiteralPath $path -PathType Leaf)) { throw "Missing source dependency: $relative" }
  $content = [IO.File]::ReadAllText($path)
  foreach ($line in [regex]::Matches($content, '(?m)^import[ \t]+([^\r\n]+)')) {
    foreach ($module in ($line.Groups[1].Value -split '[ \t]+')) {
      if ($module -eq '--') { break }
      if ($module -notmatch '^[A-Za-z_][A-Za-z0-9_.]*$') { continue }
      $modulePath = $module.Replace('.', '/') + '.lean'
      if (Test-Path -LiteralPath (Join-Path $repo $modulePath) -PathType Leaf) {
        $queue.Enqueue($modulePath)
      }
    }
  }
}
foreach ($relative in @('scripts/packed_bitvector_machine_controls.ps1', 'scripts/owned_process_tree.ps1',
    'lean-toolchain', 'lakefile.toml')) { [void]$sourceSet.Add($relative) }
$sourcePaths = @($sourceSet | Sort-Object)
$initialHashes = @($sourcePaths | ForEach-Object {
  $hash = Get-FileHash -LiteralPath (Join-Path $repo $_) -Algorithm SHA256
  [pscustomobject]@{ path=$_; sha256=$hash.Hash }
})
$initialStatus = @(& git -C $repo status --porcelain=v1 -- $sourcePaths)
if ($LASTEXITCODE -ne 0) { throw 'Unable to record scoped source status.' }
& git -C $repo diff --check -- $sourcePaths
if ($LASTEXITCODE -ne 0) { throw 'Initial scoped whitespace check failed.' }
$results = @()

if ($ReplaySelectors) {
  $selectorCases = @(
    @{ Id='omitted'; Args=@(); Exit=0; Match='BV1-MACHINE-SUMMARY version=1 executed=12 expected=12 passed=12 total=12' },
    @{ Id='valid'; Args=@('-Case','access-raw-cell'); Exit=0; Match='BV1-MACHINE-SUMMARY version=1 executed=1 expected=1 passed=1 total=12' },
    @{ Id='empty'; Args=@('-Case',''); Exit=2; Match='BV1-MACHINE-SELECTOR FAIL' },
    @{ Id='whitespace'; Args=@('-Case','   '); Exit=2; Match='BV1-MACHINE-SELECTOR FAIL' },
    @{ Id='malformed'; Args=@('-Case','access raw'); Exit=2; Match='BV1-MACHINE-SELECTOR FAIL' },
    @{ Id='unknown'; Args=@('-Case','no-such-case'); Exit=2; Match='BV1-MACHINE-SELECTOR FAIL' },
    @{ Id='padded'; Args=@('-Case',' access-raw-cell '); Exit=2; Match='BV1-MACHINE-SELECTOR FAIL' },
    @{ Id='incompatible'; Args=@('-Case','access-raw-cell','-ListRegistry'); Exit=2; Match='BV1-MACHINE-SELECTOR FAIL' }
  )
  $expected = @('omitted','valid','empty','whitespace','malformed','unknown','padded','incompatible')
  if ($selectorCases.Count -ne 8 -or ($selectorCases.Id -join '|') -cne ($expected -join '|')) {
    throw 'Exact machine selector registry mismatch.'
  }
  foreach ($selector in $selectorCases) {
    $arguments = @('-NoProfile','-File', $PSCommandPath, '-DeadlineSeconds', "$DeadlineSeconds",
      '-EvidenceTag', ($EvidenceTag + '-' + $selector.Id)) + $selector.Args
    $result = Invoke-RMQOwnedBoundedProcess -FilePath (Get-Command pwsh).Source -Arguments $arguments `
      -WorkingDirectory $repo -Stage ('machine-selector-' + $selector.Id + '-' + $EvidenceTag) `
      -DeadlineSeconds ($DeadlineSeconds + 60) -OutputLimitBytes 8388608 -TempRoot $logs
    $pass = -not $result.TimedOut -and -not $result.OutputLimitExceeded -and
      $result.ExitCode -eq $selector.Exit -and (($result.Output -join "`n").Contains($selector.Match))
    $results += [pscustomobject]@{ id=$selector.Id; expectedExit=$selector.Exit; expectedSurface=$selector.Match; passed=$pass; result=$result }
    Write-Output "BV1-MACHINE-SELECTOR-CONTROL $($selector.Id) $pass"
  }
} else {
  $arguments = @('env','lean','--run','scripts/packed_bitvector_machine_controls.lean')
  $selected = if ($boundCase) { @($Case) } else { $caseNames }
  if ($Startup) { $arguments += '--startup'; $expectedSurface='BV1-MACHINE-STARTUP version=1 expected=12' }
  elseif ($ListRegistry) { $arguments += '--list'; $expectedSurface='BV1-MACHINE-REGISTRY version=1 cases=' }
  else {
    if ($boundCase) { $arguments += @('--case',$Case) }
    $expectedSurface = "BV1-MACHINE-SUMMARY version=1 executed=$($selected.Count) expected=$($selected.Count) passed=$($selected.Count) total=12"
  }
  $result = Invoke-RMQOwnedBoundedProcess -FilePath (Join-Path $toolBin 'lake.exe') -Arguments $arguments `
    -WorkingDirectory $repo -Stage ('machine-run-' + $EvidenceTag) -DeadlineSeconds $DeadlineSeconds `
    -OutputLimitBytes 8388608 -TempRoot $logs -Environment @{ PATH=$toolBin+';'+$env:PATH; LEAN_NUM_THREADS='1' }
  $casePass = $true
  if (-not $Startup -and -not $ListRegistry) {
    $observed = @($result.Output | Where-Object { $_ -match '^BV1-MACHINE-CASE ' } |
      ForEach-Object { if ($_ -match '^BV1-MACHINE-CASE ([a-z0-9-]+) PASS version=1$') { $Matches[1] } else { '!failure!' } })
    $casePass = ($observed -join '|') -ceq ($selected -join '|')
  } elseif ($ListRegistry) {
    $registryLines = @($result.Output | Where-Object { $_ -match '^BV1-MACHINE-REGISTRY version=1 cases=(\[.*\]) expected=12$' })
    $casePass = $false
    if ($registryLines.Count -eq 1 -and $registryLines[0] -match '^BV1-MACHINE-REGISTRY version=1 cases=(\[.*\]) expected=12$') {
      $listed = @($Matches[1] | ConvertFrom-Json)
      $casePass = ($listed -join '|') -ceq $expectedRegistry
    }
  }
  $pass = -not $result.TimedOut -and -not $result.OutputLimitExceeded -and $result.ExitCode -eq 0 -and
    (($result.Output -join "`n").Contains($expectedSurface)) -and $casePass
  $results += [pscustomobject]@{ id='machine-run'; expectedExit=0; expectedSurface=$expectedSurface; passed=$pass; result=$result }
  $result.Output | ForEach-Object { Write-Output $_ }
  $expected = @('machine-run')
}

$finalHashes = @($sourcePaths | ForEach-Object {
  $hash = Get-FileHash -LiteralPath (Join-Path $repo $_) -Algorithm SHA256
  [pscustomobject]@{ path=$_; sha256=$hash.Hash }
})
$finalStatus = @(& git -C $repo status --porcelain=v1 -- $sourcePaths)
$statusOK = $LASTEXITCODE -eq 0 -and ($initialStatus -join "`n") -ceq ($finalStatus -join "`n")
& git -C $repo diff --check -- $sourcePaths
$whitespaceOK = $LASTEXITCODE -eq 0
$unchanged = ($initialHashes.sha256 -join '|') -ceq ($finalHashes.sha256 -join '|')
$allPassed = $unchanged -and $statusOK -and $whitespaceOK -and $results.Count -eq $expected.Count -and
  @($results | Where-Object { -not $_.passed }).Count -eq 0
[IO.File]::WriteAllText($record, ([ordered]@{
  version=1; registry=$caseNames; evidenceTag=$EvidenceTag; startedUtc=$startedUtc; finishedUtc=[DateTime]::UtcNow.ToString('o')
  head=$head; mode=$(if ($ReplaySelectors) {'selector-replay'} elseif ($Startup) {'startup'} elseif ($ListRegistry) {'list'} else {'machine-run'})
  expected=$expected; executed=@($results.id); passed=$allPassed; sourceHashesBefore=$initialHashes; sourceHashesAfter=$finalHashes
  exactRestoration=$unchanged; scopedStatusBefore=$initialStatus; scopedStatusAfter=$finalStatus; scopedStatusRestored=$statusOK
  whitespaceCheck=$whitespaceOK; baselineWasGloballyClean=($globalStatusBefore.Count -eq 0); initialRepositoryStatus=$globalStatusBefore
  cleanScope='Exact source import closure and control/runner files; pre-existing shared-tree changes preserved'
  platform='Windows'; leanNumThreads=1; deadlineSeconds=$DeadlineSeconds; results=$results
} | ConvertTo-Json -Depth 18), [Text.UTF8Encoding]::new($false))
Write-Output "BV1-MACHINE-REPLAY version=1 executed=$($results.Count) expected=$($expected.Count) passed=$allPassed unchanged=$unchanged statusRestored=$statusOK whitespace=$whitespaceOK"
if (-not $allPassed) { exit 1 }
