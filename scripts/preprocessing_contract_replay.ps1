#!/usr/bin/env pwsh
<#
PRE-1 contract replay. This script changes only the exact registered source
fragment, then builds the production contract and elaborates its typed consumer.
No new builder is invoked. Run StartupOnly, then one OnlyCase, before full mode.
#>
[CmdletBinding()]
param(
  [AllowEmptyString()][string]$OnlyCase,
  [switch]$StartupOnly,
  [switch]$SelectorProbeOnly,
  [switch]$SelectorBoundarySelfTestOnly,
  [switch]$RegistrySelfTestOnly,
  [switch]$DeadlineSelfTestOnly,
  [ValidateRange(1, 86400)][int]$DeadlineSeconds = 300,
  [ValidateRange(1, 300)][int]$AdministrativeDeadlineSeconds = 60,
  [ValidateRange(1, 60)][int]$SleeperDeadlineSeconds = 12,
  [ValidateRange(1024, 1073741824)][int]$OutputLimitBytes = 16777216,
  [string]$LakePath = '',
  [string]$EvidenceDirectory = '.lake/preprocessing-contract-replay'
)

Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'
$script:SelectorWasBound = $PSBoundParameters.ContainsKey('OnlyCase')
$script:RepositoryRoot = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot '..'))
$script:Utf8 = [Text.UTF8Encoding]::new($false, $true)
$script:RegistryPath = Join-Path $script:RepositoryRoot 'docs/internal/extensions/pre1/contract_cases.json'
$script:ExpectedIds = @(
  'C01_REFLECTION', 'C02_CAP', 'C03_CONSTANTS', 'C04_HEADER',
  'C05_POINTWISE', 'C06_ORACLE', 'C07_UNIFORM', 'C08_STORE_VALUE',
  'C09_FRESH_RESERVE', 'C10_CODE_ACCOUNTING', 'C11_FIELD_DELETE',
  'C12_FIELD_WEAKEN', 'C13_SIBLING', 'C14_ACCEPT_COMMENT',
  'C15_CODE_ALIAS', 'C16_CODE_COUNT', 'C17_FIREWALL_IMPORT', 'C18_PRIMITIVE_BYTES'
)
# Frozen independently of parsed contents. Only Git's CRLF/LF transport is
# normalized for this pin; raw file hashes remain in the evidence/restoration.
$script:ExpectedRegistrySha256 = 'aaec37a62bc74b483d09362a5d16f62afc2ae3a7be007577bc13e4c87c98574e'
$script:StageResults = [Collections.Generic.List[object]]::new()
$script:CaseResults = [Collections.Generic.List[object]]::new()
$script:SelfTestResults = [Collections.Generic.List[object]]::new()
$script:EvidenceRoot = ''
$script:Report = $null

function Get-ByteHash([byte[]]$Bytes) {
  $sha = [Security.Cryptography.SHA256]::Create()
  try { return ([BitConverter]::ToString($sha.ComputeHash($Bytes))).Replace('-', '').ToLowerInvariant() }
  finally { $sha.Dispose() }
}

function Get-FileHashExact([string]$Path) {
  return Get-ByteHash ([IO.File]::ReadAllBytes($Path))
}

function Get-RegistryContentHash([byte[]]$Bytes) {
  $text = $script:Utf8.GetString($Bytes).Replace("`r`n", "`n")
  return Get-ByteHash ($script:Utf8.GetBytes($text))
}

function Save-Json([string]$Name, [object]$Value) {
  [IO.File]::WriteAllText((Join-Path $script:EvidenceRoot $Name),
    ($Value | ConvertTo-Json -Depth 30), $script:Utf8)
}

function Assert-Registry([object]$Registry, [string]$ObservedHash) {
  if ($null -eq $Registry -or $null -eq $Registry.PSObject.Properties['version'] -or
      $Registry.version -cne 1 -or $null -eq $Registry.PSObject.Properties['cases']) {
    throw 'PRE-REGISTRY: expected version=1 and cases'
  }
  $cases = @($Registry.cases)
  if ($cases.Count -eq 0 -or $cases.Count -ne $script:ExpectedIds.Count) {
    throw 'PRE-REGISTRY: nonempty exact registry count required'
  }
  $seen = [Collections.Generic.HashSet[string]]::new([StringComparer]::Ordinal)
  for ($i = 0; $i -lt $cases.Count; $i += 1) {
    $case = $cases[$i]
    foreach ($field in @('id', 'kind', 'path', 'before', 'after', 'expected', 'expectedStage', 'expectedSurface')) {
      if ($null -eq $case.PSObject.Properties[$field] -or $case.$field -isnot [string]) {
        throw "PRE-REGISTRY: missing or non-string field $field at index $i"
      }
    }
    if (-not $seen.Add($case.id) -or $case.id -cne $script:ExpectedIds[$i]) {
      throw "PRE-REGISTRY: duplicate, missing, unexpected or reordered ID at index $i"
    }
    if ($case.kind -cnotin @('mutation', 'control') -or
        $case.expected -cnotin @('reject', 'accept') -or
        $case.expectedStage -cnotin @('firewall', 'producer', 'consumer') -or
        [string]::IsNullOrWhiteSpace($case.before) -or
        $case.before -ceq $case.after -or
        [string]::IsNullOrWhiteSpace($case.expectedSurface)) {
      throw "PRE-REGISTRY: malformed case $($case.id)"
    }
    if (($case.kind -ceq 'mutation' -and $case.expected -cne 'reject') -or
        ($case.kind -ceq 'control' -and $case.expected -cne 'accept')) {
      throw "PRE-REGISTRY: kind/verdict mismatch for $($case.id)"
    }
    if ($case.expected -ceq 'reject' -and $case.expectedStage -ceq 'consumer' -and
        $case.expectedSurface -cnotmatch '^preprocessing_contract_check\.lean:[1-9][0-9]*:$') {
      throw "PRE-REGISTRY: consumer rejection must pin filename and exact line: $($case.id)"
    }
    # A closed path set prevents the data registry from mutating any other lane.
    if ($case.path -cnotin @(
        'RMQ/Core/WordRAM/Construction/Contract.lean',
        'RMQ/Core/WordRAM/Construction/Primitive.lean',
        'RMQ/Core/WordRAM/Construction/Model.lean',
        'RMQ/Core/WordRAM/Construction/Input.lean',
        'RMQ/Core/WordRAM/Construction/Controls.lean',
        'scripts/preprocessing_contract_check.lean')) {
      throw "PRE-REGISTRY: mutation path is outside the PRE contract surface: $($case.path)"
    }
  }
  if ($ObservedHash -cne $script:ExpectedRegistrySha256) {
    throw "PRE-REGISTRY: frozen SHA-256 mismatch: $ObservedHash"
  }
}

function Select-Cases([object[]]$Cases) {
  if (-not $script:SelectorWasBound) { return @($Cases) }
  if ([string]::IsNullOrWhiteSpace($OnlyCase)) { throw 'PRE-SELECTOR: explicitly empty or whitespace selector' }
  if ($OnlyCase -cnotmatch '^C[0-9]{2}_[A-Z][A-Z0-9_]*$') { throw 'PRE-SELECTOR: malformed selector' }
  $selected = @($Cases | Where-Object { $_.id -ceq $OnlyCase })
  if ($selected.Count -ne 1) { throw 'PRE-SELECTOR: unknown selector' }
  return $selected
}

function Invoke-Stage([string]$Stage, [string]$FilePath, [string[]]$Arguments,
    [int]$Seconds = $DeadlineSeconds, [hashtable]$Environment = @{}) {
  $result = Invoke-RMQOwnedBoundedProcess -FilePath $FilePath -Arguments $Arguments `
    -WorkingDirectory $script:RepositoryRoot -Stage $Stage -DeadlineSeconds $Seconds `
    -OutputLimitBytes $OutputLimitBytes -TempRoot (Join-Path $script:EvidenceRoot 'process') `
    -Environment $Environment
  $entry = [pscustomobject][ordered]@{
    command = $FilePath; arguments = @($Arguments); environment = $Environment
    platform = [Environment]::OSVersion.ToString(); powershell = $PSVersionTable.PSVersion.ToString()
    result = $result
  }
  $script:StageResults.Add($entry)
  Save-Json ('stage-' + ('{0:D3}' -f $script:StageResults.Count) + '.json') $entry
  return $result
}

function Assert-Completed([object]$Result) {
  if ($Result.TimedOut -or $Result.OutputLimitExceeded) {
    throw "PRE-PROCESS: inconclusive $($Result.Stage); timeout=$($Result.TimedOut), outputLimit=$($Result.OutputLimitExceeded)"
  }
}

function Assert-Success([object]$Result) {
  Assert-Completed $Result
  if ($Result.ExitCode -ne 0) {
    throw "PRE-PROCESS: $($Result.Stage) exited $($Result.ExitCode): $($Result.Output -join ' | ')"
  }
}

function Invoke-Compile([string]$Prefix) {
  $results = [Collections.Generic.List[object]]::new()
  $firewall = Invoke-Stage "$Prefix-firewall" (Get-Process -Id $PID).Path `
    @('-NoLogo', '-NoProfile', '-ExecutionPolicy', 'Bypass', '-File',
      (Join-Path $PSScriptRoot 'preprocessing_contract_firewall.ps1')) `
    -Seconds $AdministrativeDeadlineSeconds
  $results.Add($firewall)
  Assert-Completed $firewall
  if ($firewall.ExitCode -ne 0) { return @($results) }
  # This pinned Lake version has no -j option. The environment constrains Lean
  # worker threads; producer/consumer invocations are sequential in this runner.
  $producer = Invoke-Stage "$Prefix-producer" $script:LakePath `
    @('build', 'RMQ.Core.WordRAM.Construction.Contract') `
    -Environment @{ LEAN_NUM_THREADS = '1' }
  $results.Add($producer)
  Assert-Completed $producer
  if ($producer.ExitCode -eq 0) {
    $consumer = Invoke-Stage "$Prefix-consumer" $script:LakePath `
      @('env', 'lean', 'scripts/preprocessing_contract_check.lean') `
      -Environment @{ LEAN_NUM_THREADS = '1' }
    $results.Add($consumer)
    Assert-Completed $consumer
  }
  return @($results)
}

function Resolve-PinnedLake([string]$ExplicitPath) {
  if (-not [string]::IsNullOrWhiteSpace($ExplicitPath)) {
    $resolved = if ([IO.Path]::IsPathRooted($ExplicitPath)) {
      [IO.Path]::GetFullPath($ExplicitPath)
    } else { [IO.Path]::GetFullPath((Join-Path $script:RepositoryRoot $ExplicitPath)) }
  } else {
    # Avoid the elan proxy: it can attempt a network installation rather than
    # execute the already installed pinned compiler on a restricted host.
    $toolchain = [IO.File]::ReadAllText((Join-Path $script:RepositoryRoot 'lean-toolchain')).Trim()
    $elanRoot = [Environment]::GetEnvironmentVariable('ELAN_HOME')
    if ([string]::IsNullOrWhiteSpace($elanRoot)) {
      $elanRoot = Join-Path ([Environment]::GetFolderPath('UserProfile')) '.elan'
    }
    $directoryName = $toolchain.Replace('/', '--').Replace(':', '---')
    $binaryName = if (Test-RMQOwnedProcessWindows) { 'lake.exe' } else { 'lake' }
    $resolved = Join-Path (Join-Path (Join-Path $elanRoot 'toolchains') $directoryName) ('bin/' + $binaryName)
  }
  if (-not (Test-Path -LiteralPath $resolved -PathType Leaf)) {
    throw "PRE-TOOLCHAIN: installed pinned Lake unavailable at $resolved; supply -LakePath to the installed actual binary"
  }
  return [IO.Path]::GetFullPath($resolved)
}

function Read-Git([string[]]$Arguments, [string]$Label) {
  $result = Invoke-Stage $Label $script:GitPath (@('-c', 'core.excludesfile=') + @($Arguments)) `
    -Seconds $AdministrativeDeadlineSeconds
  Assert-Success $result
  return @($result.StandardOutput) -join "`n"
}

function Get-State([string]$Label) {
  return [pscustomobject][ordered]@{
    head = Read-Git @('rev-parse', 'HEAD') "$Label-head"
    status = Read-Git @('status', '--porcelain=v1', '--untracked-files=all') "$Label-status"
    worktree = Read-Git @('diff', '--binary', '--no-ext-diff') "$Label-worktree"
    index = Read-Git @('diff', '--cached', '--binary', '--no-ext-diff') "$Label-index"
  }
}

function Assert-State([object]$Before, [object]$After) {
  foreach ($field in @('head', 'status', 'worktree', 'index')) {
    if ($Before.$field -cne $After.$field) { throw "PRE-RESTORE: repository $field changed" }
  }
}

function Assert-SourceHashes {
  foreach ($source in $script:Report.sourceHashes) {
    if ((Get-FileHashExact (Join-Path $script:RepositoryRoot $source.path)) -cne $source.sha256) {
      throw "PRE-RESTORE: source changed: $($source.path)"
    }
  }
  if ((Get-FileHashExact $script:RegistryPath) -cne $script:Report.registrySha256) {
    throw 'PRE-RESTORE: raw registry bytes changed'
  }
}

function Test-CaseVerdict([object]$Case, [object[]]$Results) {
  $stages = @('firewall', 'producer', 'consumer')
  if ($Results.Count -eq 0 -or $Results.Count -gt $stages.Count) { return $false }
  for ($i = 0; $i -lt $Results.Count; $i += 1) {
    if ($Results[$i].Stage -cne "$($Case.id)-$($stages[$i])" -or
        $Results[$i].TimedOut -or $Results[$i].OutputLimitExceeded) { return $false }
  }
  $expectedIndex = [Array]::IndexOf($stages, [string]$Case.expectedStage)
  if ($expectedIndex -lt 0) { return $false }
  if ($Case.expected -ceq 'accept') {
    if ($Results.Count -ne 3 -or @($Results | Where-Object { $_.ExitCode -ne 0 }).Count -ne 0) {
      return $false
    }
  } elseif ($Case.expected -ceq 'reject') {
    if ($Results.Count -ne ($expectedIndex + 1) -or $Results[$expectedIndex].ExitCode -eq 0) {
      return $false
    }
    for ($i = 0; $i -lt $expectedIndex; $i += 1) {
      if ($Results[$i].ExitCode -ne 0) { return $false }
    }
  } else { return $false }
  return ($Results[$expectedIndex].Output -join "`n").Contains($Case.expectedSurface)
}

function New-MatcherStage([string]$Stage, [int]$Exit, [string]$Output, [bool]$TimedOut = $false) {
  return [pscustomobject]@{
    Stage = "T00_MATCHER-$Stage"; ExitCode = $Exit; Output = @($Output)
    TimedOut = $TimedOut; OutputLimitExceeded = $false
  }
}

function Invoke-MatcherTests {
  $reject = [pscustomobject]@{
    id = 'T00_MATCHER'; expected = 'reject'; expectedStage = 'consumer'
    expectedSurface = 'preprocessing_contract_check.lean:42:'
  }
  $accept = [pscustomobject]@{
    id = 'T00_MATCHER'; expected = 'accept'; expectedStage = 'consumer'
    expectedSurface = 'PRE1-CONTRACT-TYPED-CONSUMERS PASS'
  }
  $prefix = @((New-MatcherStage 'firewall' 0 ''), (New-MatcherStage 'producer' 0 ''))
  $fixtures = @(
    @{ id='exact-rejection'; case=$reject; expected=$true; stages=@($prefix) + @((New-MatcherStage 'consumer' 1 'scripts/preprocessing_contract_check.lean:42:7: error: mismatch')) },
    @{ id='wrong-stage'; case=$reject; expected=$false; stages=@((New-MatcherStage 'firewall' 0 ''), (New-MatcherStage 'producer' 1 'scripts/preprocessing_contract_check.lean:42:7: error: mismatch')) },
    @{ id='wrong-location'; case=$reject; expected=$false; stages=@($prefix) + @((New-MatcherStage 'consumer' 1 'scripts/preprocessing_contract_check.lean:43:7: error: mismatch')) },
    @{ id='generic-substring-only'; case=$reject; expected=$false; stages=@($prefix) + @((New-MatcherStage 'consumer' 1 'preprocessing_contract_check.lean contractPrerequisites_holds.reflection')) },
    @{ id='unrelated-error-plus-generic-substring'; case=$reject; expected=$false; stages=@($prefix) + @((New-MatcherStage 'consumer' 1 "scripts/preprocessing_contract_check.lean:43:7: unrelated error`npreprocessing_contract_check.lean contractPrerequisites_holds.reflection")) },
    @{ id='timeout-is-inconclusive'; case=$reject; expected=$false; stages=@($prefix) + @((New-MatcherStage 'consumer' -1 'preprocessing_contract_check.lean:42:' $true)) },
    @{ id='success-is-not-rejection'; case=$reject; expected=$false; stages=@($prefix) + @((New-MatcherStage 'consumer' 0 'preprocessing_contract_check.lean:42:')) },
    @{ id='exact-acceptance'; case=$accept; expected=$true; stages=@($prefix) + @((New-MatcherStage 'consumer' 0 'PRE1-CONTRACT-TYPED-CONSUMERS PASS')) },
    @{ id='acceptance-at-wrong-stage'; case=$accept; expected=$false; stages=@((New-MatcherStage 'firewall' 0 'PRE1-CONTRACT-TYPED-CONSUMERS PASS'), (New-MatcherStage 'producer' 0 ''), (New-MatcherStage 'consumer' 0 '')) }
  )
  foreach ($fixture in $fixtures) {
    $observed = Test-CaseVerdict $fixture.case @($fixture.stages)
    if ($observed -ne $fixture.expected) { throw "PRE-SELFTEST: production verdict matcher $($fixture.id) returned $observed" }
    $script:SelfTestResults.Add([pscustomobject]@{
      category = 'matcher'; case = $fixture.id; expected = $fixture.expected; observed = $observed; verdict = 'PASS'
    })
  }
}

function Invoke-RegistryTests([object]$Registry, [string]$Hash) {
  $tests = @('empty', 'missing', 'extra', 'duplicate', 'reordered', 'version', 'hash')
  foreach ($test in $tests) {
    $copy = ($Registry | ConvertTo-Json -Depth 20) | ConvertFrom-Json
    $testHash = $Hash
    switch ($test) {
      'empty' { $copy.cases = @() }
      'missing' { $copy.cases = @($copy.cases | Select-Object -Skip 1) }
      'extra' { $copy.cases = @($copy.cases) + @($copy.cases[0]) }
      'duplicate' { $copy.cases[1] = $copy.cases[0] }
      'reordered' { $first = $copy.cases[0]; $copy.cases[0] = $copy.cases[1]; $copy.cases[1] = $first }
      'version' { $copy.version = 2 }
      'hash' { $testHash = 'invalid' }
    }
    $rejected = $false
    try { Assert-Registry $copy $testHash }
    catch { if ($_.Exception.Message.StartsWith('PRE-REGISTRY:')) { $rejected = $true } else { throw } }
    if (-not $rejected) { throw "PRE-SELFTEST: registry $test accepted" }
    $script:SelfTestResults.Add([pscustomobject]@{ category = 'registry'; case = $test; verdict = 'PASS' })
  }
  Invoke-MatcherTests
}

function Invoke-SelectorBoundaryTests {
  # A child PowerShell script invokes the actual public parameter boundary.
  # Literal '' survives both PowerShell 5 and 7; a native argv empty argument
  # may not, so relying on native forwarding would not test bound-empty state.
  $targetLiteral = (Join-Path $PSScriptRoot 'preprocessing_contract_replay.ps1').Replace("'", "''")
  $wrapper = Join-Path $script:EvidenceRoot 'selector-boundary.ps1'
  $body = @'
param([string]$BoundaryCase, [string]$EvidenceRoot)
$ErrorActionPreference = 'Stop'
$ErrorView = 'NormalView'
$target = '__TARGET__'
switch ($BoundaryCase) {
  'omitted' { & $target -SelectorProbeOnly -EvidenceDirectory $EvidenceRoot }
  'valid' { & $target -SelectorProbeOnly -EvidenceDirectory $EvidenceRoot -OnlyCase 'C01_REFLECTION' }
  'empty' { & $target -SelectorProbeOnly -EvidenceDirectory $EvidenceRoot -OnlyCase '' }
  'whitespace' { & $target -SelectorProbeOnly -EvidenceDirectory $EvidenceRoot -OnlyCase ' ' }
  'malformed' { & $target -SelectorProbeOnly -EvidenceDirectory $EvidenceRoot -OnlyCase 'C01_REFLECTION,C02_CAP' }
  'unknown' { & $target -SelectorProbeOnly -EvidenceDirectory $EvidenceRoot -OnlyCase 'C99_UNKNOWN' }
  'zero' { & $target -SelectorProbeOnly -EvidenceDirectory $EvidenceRoot -OnlyCase '0' }
  'missing' { & $target -SelectorProbeOnly -EvidenceDirectory $EvidenceRoot -OnlyCase }
  'duplicate' { & $target -SelectorProbeOnly -EvidenceDirectory $EvidenceRoot -OnlyCase 'C01_REFLECTION' -OnlyCase 'C02_CAP' }
  default { throw 'unknown boundary fixture' }
}
exit $LASTEXITCODE
'@
  [IO.File]::WriteAllText($wrapper, $body.Replace('__TARGET__', $targetLiteral), $script:Utf8)
  $shell = (Get-Process -Id $PID).Path
  foreach ($test in @('omitted', 'valid', 'empty', 'whitespace', 'malformed', 'unknown', 'zero', 'missing', 'duplicate')) {
    $result = Invoke-Stage "selector-$test" $shell `
      @('-NoLogo', '-NoProfile', '-ExecutionPolicy', 'Bypass', '-File', $wrapper,
        '-BoundaryCase', $test, '-EvidenceRoot', $script:EvidenceRoot) `
      -Seconds $AdministrativeDeadlineSeconds
    Assert-Completed $result
    $positive = $test -cin @('omitted', 'valid')
    $output = $result.Output -join "`n"
    if ($positive) {
      $expectedCount = if ($test -ceq 'omitted') { $script:ExpectedIds.Count } else { 1 }
      $expectedIds = if ($test -ceq 'omitted') { $script:ExpectedIds -join ',' } else { 'C01_REFLECTION' }
      if ($result.ExitCode -ne 0 -or -not $output.Contains("PRE-SELECTOR-PROBE: selected=$expectedCount ids=$expectedIds")) {
        throw "PRE-SELFTEST: selector $test did not select $expectedCount"
      }
    } elseif ($result.ExitCode -eq 0 -or $output.Contains('PRE-SELECTOR-PROBE:')) {
      throw "PRE-SELFTEST: selector $test was not rejected at script boundary"
    } else {
      $surface = switch ($test) {
        'empty' { 'PRE-SELECTOR: explicitly empty or whitespace selector' }
        'whitespace' { 'PRE-SELECTOR: explicitly empty or whitespace selector' }
        'malformed' { 'PRE-SELECTOR: malformed selector' }
        'unknown' { 'PRE-SELECTOR: unknown selector' }
        'zero' { 'PRE-SELECTOR: malformed selector' }
        'missing' { 'MissingArgument' }
        'duplicate' { 'ParameterAlreadyBound' }
      }
      if (-not $output.Contains($surface)) { throw "PRE-SELFTEST: selector $test failed outside its pinned surface $surface" }
    }
    $script:SelfTestResults.Add([pscustomobject]@{ category = 'selector'; case = $test; verdict = 'PASS'; exit = $result.ExitCode })
  }
}

function Invoke-DeadlineTests {
  Invoke-RMQOwnedProcessDeterministicTests
  Invoke-RMQOwnedProcessCollectionSelfTest
  $script:SelfTestResults.Add([pscustomobject]@{
    category = 'deadline'; case = 'deterministic-plans-and-collections'; verdict = 'PASS'
    scope = 'Production launch-plan branches and process-ID collection logic; foreign-host execution is not implied'
  })
  $shell = (Get-Process -Id $PID).Path
  $failurePath = Join-Path $script:EvidenceRoot 'known-failure.ps1'
  [IO.File]::WriteAllText($failurePath, "[Console]::Error.WriteLine('PRE-EXPECTED-STDERR'); exit 23", $script:Utf8)
  $failed = Invoke-Stage 'known-failure' $shell @('-NoLogo', '-NoProfile', '-File', $failurePath) `
    -Seconds $AdministrativeDeadlineSeconds
  Assert-Completed $failed
  if ($failed.ExitCode -ne 23 -or -not (@($failed.StandardError) -join "`n").Contains('PRE-EXPECTED-STDERR')) {
    throw 'PRE-SELFTEST: exit/stderr preservation failed'
  }
  $script:SelfTestResults.Add([pscustomobject]@{ category = 'deadline'; case = 'exit-stderr'; verdict = 'PASS' })
  $sleeper = Join-Path $script:EvidenceRoot 'owned-sleeper.ps1'
  $pidFile = Join-Path $script:EvidenceRoot 'owned-descendant.pid'
  $body = @'
$shell = (Get-Process -Id $PID).Path
$options = @{ FilePath = $shell; ArgumentList = @('-NoLogo', '-NoProfile', '-Command', 'Start-Sleep -Seconds 120'); PassThru = $true }
if ([Environment]::OSVersion.Platform -eq [PlatformID]::Win32NT) { $options.WindowStyle = 'Hidden' }
$child = Start-Process @options
[IO.File]::WriteAllText('__PIDFILE__', [string]$child.Id)
Start-Sleep -Seconds 120
'@
  [IO.File]::WriteAllText($sleeper, $body.Replace('__PIDFILE__', $pidFile.Replace("'", "''")), $script:Utf8)
  $timed = Invoke-Stage 'owned-descendant-timeout' $shell @('-NoLogo', '-NoProfile', '-File', $sleeper) `
    -Seconds $SleeperDeadlineSeconds
  if (-not $timed.TimedOut) { throw 'PRE-SELFTEST: sleeper did not reach timeout' }
  if (-not (Test-Path -LiteralPath $pidFile -PathType Leaf)) {
    throw 'PRE-SELFTEST: INCONCLUSIVE descendant did not start; this host condition is uncovered'
  }
  $childId = [int][IO.File]::ReadAllText($pidFile)
  if (@(Get-RMQAliveProcessIds @($childId)).Count -ne 0) {
    throw "PRE-SELFTEST: owned descendant $childId survived"
  }
  $script:SelfTestResults.Add([pscustomobject]@{
    category = 'deadline'; case = 'owned-descendant'; verdict = 'PASS'; descendant = $childId
    platform = [Environment]::OSVersion.ToString(); ownership = $timed.Ownership
    unexecutedHost = if (Test-RMQOwnedProcessWindows) { 'POSIX execution not covered by this run' } else { 'Windows execution not covered by this run' }
  })
}

function Invoke-Case([object]$Case, [object]$InitialState, [string]$RegistryHash) {
  $path = Join-Path $script:RepositoryRoot $Case.path
  $original = [IO.File]::ReadAllBytes($path)
  $beforeHash = Get-ByteHash $original
  $text = $script:Utf8.GetString($original)
  $sourceWithoutCrlf = $text.Replace("`r`n", '')
  if ($sourceWithoutCrlf.Contains("`r") -or
      ($text.Contains("`r`n") -and $sourceWithoutCrlf.Contains("`n"))) {
    throw "PRE-MUTATION: $($Case.id) source has unsupported mixed line endings"
  }
  $needle = $Case.before.Replace("`r`n", "`n")
  $replacement = $Case.after.Replace("`r`n", "`n")
  if ($text.Contains("`r`n")) {
    $needle = $needle.Replace("`n", "`r`n")
    $replacement = $replacement.Replace("`n", "`r`n")
  }
  $at = $text.IndexOf($needle, [StringComparison]::Ordinal)
  if ($at -lt 0 -or $text.IndexOf($needle, $at + $needle.Length, [StringComparison]::Ordinal) -ge 0) {
    throw "PRE-MUTATION: $($Case.id) before fragment must occur exactly once"
  }
  $mutant = $text.Substring(0, $at) + $replacement + $text.Substring($at + $needle.Length)
  $entry = [ordered]@{
    id = $Case.id; expected = $Case.expected; expectedStage = $Case.expectedStage; expectedSurface = $Case.expectedSurface
    source = $Case.path; beforeSha256 = $beforeHash; mutationSha256 = Get-ByteHash ($script:Utf8.GetBytes($mutant))
    afterSha256 = ''; verdict = 'INCOMPLETE'; compile = @(); restoreCompile = @(); restoration = 'PENDING'; error = ''
  }
  try {
    [IO.File]::WriteAllBytes($path, $script:Utf8.GetBytes($mutant))
    $entry.compile = @(Invoke-Compile $Case.id)
    if (-not (Test-CaseVerdict $Case @($entry.compile))) {
      throw "PRE-MUTATION: $($Case.id) did not produce $($Case.expected) at exact stage=$($Case.expectedStage) surface=$($Case.expectedSurface)"
    }
    $entry.verdict = 'PASS'
  } catch {
    $entry.error = $_.Exception.Message
    $entry.verdict = 'FAIL'
    throw
  } finally {
    # Restoration happens even after failed compilation, timeout, or mismatch.
    [IO.File]::WriteAllBytes($path, $original)
    $entry.afterSha256 = Get-FileHashExact $path
    try {
      if ($entry.afterSha256 -cne $beforeHash) { throw 'PRE-RESTORE: byte SHA-256 differs' }
      if ((Get-FileHashExact $script:RegistryPath) -cne $RegistryHash) { throw 'PRE-RESTORE: registry changed during replay' }
      $entry.restoreCompile = @(Invoke-Compile "$($Case.id)-restored")
      foreach ($stage in $entry.restoreCompile) { Assert-Success $stage }
      if ($entry.restoreCompile.Count -ne 3) { throw 'PRE-RESTORE: firewall, producer and consumer restoration were not all checked' }
      Assert-SourceHashes
      Assert-State $InitialState (Get-State "$($Case.id)-restored")
      $entry.restoration = 'EXACT'
    } catch {
      $entry.verdict = 'FAIL'; $entry.restoration = 'FAIL'
      $entry.error = ($entry.error + ' | ' + $_.Exception.Message).Trim(' ', '|')
      throw
    } finally {
      $script:CaseResults.Add([pscustomobject]$entry)
      Save-Json ("case-$($Case.id).json") $entry
    }
  }
}

try {
  $exclusive = @($StartupOnly, $SelectorProbeOnly, $SelectorBoundarySelfTestOnly,
    $RegistrySelfTestOnly, $DeadlineSelfTestOnly) | Where-Object { $_ }
  if (@($exclusive).Count -gt 1 -or
      ($script:SelectorWasBound -and ($StartupOnly -or $SelectorBoundarySelfTestOnly -or $RegistrySelfTestOnly -or $DeadlineSelfTestOnly))) {
    throw 'PRE-MODE: incompatible modes or selector'
  }
  $registryBytes = [IO.File]::ReadAllBytes($script:RegistryPath)
  $registryHash = Get-ByteHash $registryBytes
  $registryContentHash = Get-RegistryContentHash $registryBytes
  $registry = $script:Utf8.GetString($registryBytes) | ConvertFrom-Json
  Assert-Registry $registry $registryContentHash
  $selected = @(Select-Cases @($registry.cases))
  if ($SelectorProbeOnly) {
    Write-Host "PRE-SELECTOR-PROBE: selected=$($selected.Count) ids=$(@($selected | ForEach-Object { $_.id }) -join ',')"
    exit 0
  }
  $evidenceBase = if ([IO.Path]::IsPathRooted($EvidenceDirectory)) {
    [IO.Path]::GetFullPath($EvidenceDirectory)
  } else { [IO.Path]::GetFullPath((Join-Path $script:RepositoryRoot $EvidenceDirectory)) }
  $repoPrefix = $script:RepositoryRoot.TrimEnd('\', '/') + [IO.Path]::DirectorySeparatorChar
  $cacheRoot = [IO.Path]::GetFullPath((Join-Path $script:RepositoryRoot '.lake'))
  $cachePrefix = $cacheRoot.TrimEnd('\', '/') + [IO.Path]::DirectorySeparatorChar
  $withinRepository = $evidenceBase.Equals($script:RepositoryRoot, [StringComparison]::OrdinalIgnoreCase) -or
    $evidenceBase.StartsWith($repoPrefix, [StringComparison]::OrdinalIgnoreCase)
  $withinCache = $evidenceBase.Equals($cacheRoot, [StringComparison]::OrdinalIgnoreCase) -or
    $evidenceBase.StartsWith($cachePrefix, [StringComparison]::OrdinalIgnoreCase)
  if ($withinRepository -and -not $withinCache) {
    throw 'PRE-EVIDENCE: inside this repository, evidence must be under ignored .lake; copy final evidence after replay'
  }
  $script:EvidenceRoot = Join-Path $evidenceBase ((Get-Date -Format 'yyyyMMdd-HHmmss') + '-' + [Guid]::NewGuid().ToString('N'))
  [void](New-Item -ItemType Directory -Path $script:EvidenceRoot -Force)
  . (Join-Path $PSScriptRoot 'owned_process_tree.ps1')
  $script:Report = [ordered]@{
    schemaVersion = 1; phase = 'CONTRACT'; verdict = 'INCOMPLETE'; registrySha256 = $registryHash
    registryContentSha256 = $registryContentHash
    runnerSha256 = Get-FileHashExact (Join-Path $PSScriptRoot 'preprocessing_contract_replay.ps1')
    registryExpected = $script:ExpectedIds; selectedExpected = @($selected | ForEach-Object { $_.id })
    executed = @(); sourceHashes = @(); baseline = $null; restored = $null
    mode = if ($StartupOnly) { 'startup' } elseif ($SelectorBoundarySelfTestOnly) { 'selector-selftest' } elseif ($RegistrySelfTestOnly) { 'registry-selftest' } elseif ($DeadlineSelfTestOnly) { 'deadline-selftest' } elseif ($script:SelectorWasBound) { 'focused' } else { 'full' }
    platform = [Environment]::OSVersion.ToString(); powershell = $PSVersionTable.PSVersion.ToString()
    deadlineSeconds = $DeadlineSeconds; administrationDeadlineSeconds = $AdministrativeDeadlineSeconds
    cases = @(); selfTests = @(); stages = @(); error = ''
  }
  if ($SelectorBoundarySelfTestOnly) { Invoke-SelectorBoundaryTests }
  elseif ($RegistrySelfTestOnly) { Invoke-RegistryTests $registry $registryContentHash }
  elseif ($DeadlineSelfTestOnly) { Invoke-DeadlineTests }
  else {
    $script:LakePath = Resolve-PinnedLake $LakePath
    $script:GitPath = Resolve-RMQScalarApplicationPath @(Get-Command git -CommandType Application -ErrorAction Stop) 'git'
    $script:Report.baseline = Get-State 'baseline'
    $constructionRoot = Join-Path $script:RepositoryRoot 'RMQ/Core/WordRAM/Construction'
    $constructionSources = @([IO.Directory]::EnumerateFiles($constructionRoot, '*.lean', [IO.SearchOption]::AllDirectories) |
      ForEach-Object { $_.Substring($script:RepositoryRoot.Length + 1).Replace('\', '/') })
    $sourcePaths = @(@($registry.cases | ForEach-Object { $_.path }) + $constructionSources +
      @('scripts/preprocessing_contract_replay.ps1', 'scripts/preprocessing_contract_firewall.ps1',
        'scripts/preprocessing_contract_check.lean', 'docs/internal/extensions/pre1/primitive_manifest.json',
        'lean-toolchain') |
      Sort-Object -Unique)
    $script:Report.sourceHashes = @($sourcePaths | ForEach-Object {
      [pscustomobject]@{ path = $_; sha256 = Get-FileHashExact (Join-Path $script:RepositoryRoot $_) }
    })
    if (-not $StartupOnly -and -not $script:SelectorWasBound) {
      Invoke-RegistryTests $registry $registryContentHash
      Invoke-SelectorBoundaryTests
      Invoke-DeadlineTests
    }
    $baselineCompile = @(Invoke-Compile 'baseline')
    foreach ($stage in $baselineCompile) { Assert-Success $stage }
    if ($baselineCompile.Count -ne 3) { throw 'PRE-BASELINE: firewall, producer and typed consumer must all pass' }
    if (-not $StartupOnly) {
      foreach ($case in $selected) {
        Invoke-Case $case $script:Report.baseline $registryHash
        Write-Host "PRE-CASE: $($case.id) PASS, exact restoration verified"
      }
      $executed = @($script:CaseResults | ForEach-Object { $_.id })
      if (($executed -join ',') -cne ($script:Report.selectedExpected -join ',')) {
        throw 'PRE-REGISTRY: executed IDs differ from selected expected IDs'
      }
    }
    Assert-SourceHashes
    $script:Report.restored = Get-State 'final'
    Assert-State $script:Report.baseline $script:Report.restored
  }
  $script:Report.verdict = 'PASS'
} catch {
  if ($null -ne $script:Report) { $script:Report.verdict = 'FAIL'; $script:Report.error = $_.Exception.Message }
  Write-Host "PRE-CONTRACT-REPLAY: FAIL $($_.Exception.Message)"
  exit 1
} finally {
  if ($null -ne $script:Report -and -not [string]::IsNullOrEmpty($script:EvidenceRoot)) {
    $script:Report.executed = @($script:CaseResults | ForEach-Object { $_.id })
    $script:Report.cases = @($script:CaseResults)
    $script:Report.selfTests = @($script:SelfTestResults)
    $script:Report.stages = @($script:StageResults)
    Save-Json 'report.json' $script:Report
  }
}
Write-Host "PRE-CONTRACT-REPLAY: PASS mode=$($script:Report.mode) executed=$($script:CaseResults.Count) registry=$($script:ExpectedIds.Count) evidence=$script:EvidenceRoot"
exit 0
