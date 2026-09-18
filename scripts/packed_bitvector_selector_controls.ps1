param(
  [int]$DeadlineSeconds = 660,
  [string]$EvidenceTag = ('v2-' + [DateTime]::UtcNow.ToString('yyyyMMddHHmmssfff')),
  [ValidateSet('Main','ValidationControls')][string]$Runner = 'Main'
)
$ErrorActionPreference = 'Stop'
if ($EvidenceTag -notmatch '^[a-z0-9-]+$') { throw 'EvidenceTag must use lowercase letters, digits and hyphens.' }
$repo = (Resolve-Path (Join-Path $PSScriptRoot '..')).Path
. (Join-Path $PSScriptRoot 'owned_process_tree.ps1')
$logs = Join-Path $repo 'docs/internal/extensions/bv1/commands'
$record = Join-Path $logs ('selector-controls-' + $EvidenceTag + '.json')
if (Test-Path -LiteralPath $record) { throw 'Selector control evidence already exists.' }
$probe = Join-Path $PSScriptRoot $(if ($Runner -eq 'Main') {
  'packed_bitvector_probe.ps1'
} else { 'packed_bitvector_validation_controls.ps1' })
$fullArgs = if ($Runner -eq 'Main') {
  @('-Stage',('selector-omitted-' + $EvidenceTag),'-DeadlineSeconds','600')
} else {
  @('-EvidenceTag',('selector-omitted-' + $EvidenceTag),'-DeadlineSeconds','300')
}
$validCase = if ($Runner -eq 'Main') { 'mixed-true' } else { 'baseline' }
$validArgs = if ($Runner -eq 'Main') {
  @('-Case',$validCase,'-Stage',('selector-valid-' + $EvidenceTag))
} else { @('-Case',$validCase,'-EvidenceTag',('selector-valid-' + $EvidenceTag)) }
$fullMatch = if ($Runner -eq 'Main') { 'executed=46 expected=46 passed=46 total=46' }
  else { 'executed=5 expected=5 passed=True total=5' }
$validMatch = if ($Runner -eq 'Main') { 'executed=1 expected=1 passed=1 total=46' }
  else { 'executed=1 expected=1 passed=True total=5' }
$cases = @(
  @{ Id='omitted'; Args=$fullArgs; Exit=0; Match=$fullMatch },
  @{ Id='valid'; Args=$validArgs; Exit=0; Match=$validMatch },
  @{ Id='empty'; Args=@('-Case',''); Exit=2; Match='BV1-SELECTOR FAIL' },
  @{ Id='whitespace'; Args=@('-Case','   '); Exit=2; Match='BV1-SELECTOR FAIL' },
  @{ Id='malformed'; Args=@('-Case','mixed true'); Exit=2; Match='BV1-SELECTOR FAIL' },
  @{ Id='unknown'; Args=@('-Case','no-such-case'); Exit=2; Match='BV1-SELECTOR FAIL' },
  @{ Id='padded'; Args=@('-Case',(' ' + $validCase + ' ')); Exit=2; Match='BV1-SELECTOR FAIL' },
  @{ Id='incompatible'; Args=@('-Case',$validCase,'-Startup'); Exit=2; Match='BV1-SELECTOR FAIL' }
)
$expected = @('omitted','valid','empty','whitespace','malformed','unknown','padded','incompatible')
if (($cases.Id -join '|') -cne ($expected -join '|') -or $cases.Count -ne 8) {
  throw 'Exact selector control registry mismatch.'
}
$initialHashes = @(Get-FileHash -LiteralPath $probe,
  (Join-Path $PSScriptRoot 'packed_bitvector_selector_controls.ps1'),
  (Join-Path $repo 'RMQ/Validation/PackedBitvector.lean'),
  (Join-Path $PSScriptRoot 'packed_bitvector_validation_controls.ps1') -Algorithm SHA256)
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
  version=2; runner=$Runner; evidenceTag=$EvidenceTag; expected=$expected; executed=@($results.id); passed=$allPassed
  sourceHashesBefore=$initialHashes; sourceHashesAfter=$finalHashes; exactRestoration=$unchanged
  results=$results; platform='Windows'; deadlineSeconds=$DeadlineSeconds
} | ConvertTo-Json -Depth 16), [Text.UTF8Encoding]::new($false))
Write-Output "BV1-SELECTOR-REGISTRY executed=$($results.Count) expected=8 passed=$allPassed unchanged=$unchanged"
if (-not $allPassed) { exit 1 }
