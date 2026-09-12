param([int]$DeadlineSeconds = 180)
$ErrorActionPreference = 'Stop'
$repo = (Resolve-Path (Join-Path $PSScriptRoot '..')).Path
. (Join-Path $PSScriptRoot 'owned_process_tree.ps1')
$logs = Join-Path $repo 'docs/internal/extensions/bv1/commands'
$record = Join-Path $logs 'selector-controls-v1.json'
if (Test-Path -LiteralPath $record) { throw 'Selector control evidence already exists.' }
$probe = Join-Path $PSScriptRoot 'packed_bitvector_probe.ps1'
$cases = @(
  @{ Id='omitted'; Args=@('-Stage','selector-omitted-v1','-DeadlineSeconds','120'); Exit=0; Match='executed=18 expected=18 passed=18 total=18' },
  @{ Id='valid'; Args=@('-Case','mixed-true','-Stage','selector-valid-v1'); Exit=0; Match='executed=1 expected=1 passed=1 total=18' },
  @{ Id='empty'; Args=@('-Case',''); Exit=2; Match='BV1-SELECTOR FAIL' },
  @{ Id='whitespace'; Args=@('-Case','   '); Exit=2; Match='BV1-SELECTOR FAIL' },
  @{ Id='malformed'; Args=@('-Case','mixed true'); Exit=2; Match='BV1-SELECTOR FAIL' },
  @{ Id='unknown'; Args=@('-Case','no-such-case'); Exit=2; Match='BV1-SELECTOR FAIL' },
  @{ Id='padded'; Args=@('-Case',' mixed-true '); Exit=2; Match='BV1-SELECTOR FAIL' },
  @{ Id='incompatible'; Args=@('-Case','mixed-true','-Startup'); Exit=2; Match='BV1-SELECTOR FAIL' }
)
$expected = @('omitted','valid','empty','whitespace','malformed','unknown','padded','incompatible')
if (($cases.Id -join '|') -cne ($expected -join '|') -or $cases.Count -ne 8) {
  throw 'Exact selector control registry mismatch.'
}
$initialHashes = @(Get-FileHash -LiteralPath $probe,
  (Join-Path $PSScriptRoot 'packed_bitvector_selector_controls.ps1'),
  (Join-Path $repo 'RMQ/Validation/PackedBitvector.lean') -Algorithm SHA256)
$results = @()
foreach ($case in $cases) {
  $result = Invoke-RMQOwnedBoundedProcess -FilePath (Get-Command pwsh).Source `
    -Arguments (@('-NoProfile','-File',$probe) + $case.Args) `
    -WorkingDirectory $repo -Stage ('bv1-selector-' + $case.Id) `
    -DeadlineSeconds $DeadlineSeconds -OutputLimitBytes 8388608 -TempRoot $logs
  $pass = -not $result.TimedOut -and -not $result.OutputLimitExceeded -and
    $result.ExitCode -eq $case.Exit -and (($result.Output -join "`n").Contains($case.Match))
  $results += [pscustomobject]@{ id=$case.Id; expectedExit=$case.Exit; expectedSurface=$case.Match; passed=$pass; result=$result }
  Write-Output "BV1-SELECTOR-CONTROL $($case.Id) $pass"
}
$finalHashes = @($initialHashes | ForEach-Object { Get-FileHash -LiteralPath $_.Path -Algorithm SHA256 })
$unchanged = (($initialHashes.Hash -join '|') -ceq ($finalHashes.Hash -join '|'))
$allPassed = $unchanged -and $results.Count -eq 8 -and @($results | Where-Object { -not $_.passed }).Count -eq 0
[IO.File]::WriteAllText($record, ([ordered]@{
  version=1; expected=$expected; executed=@($results.id); passed=$allPassed
  sourceHashesBefore=$initialHashes; sourceHashesAfter=$finalHashes; exactRestoration=$unchanged
  results=$results; platform='Windows'; deadlineSeconds=$DeadlineSeconds
} | ConvertTo-Json -Depth 16), [Text.UTF8Encoding]::new($false))
Write-Output "BV1-SELECTOR-REGISTRY executed=$($results.Count) expected=8 passed=$allPassed unchanged=$unchanged"
if (-not $allPassed) { exit 1 }
