#!/usr/bin/env pwsh
[CmdletBinding()]
param(
  [AllowEmptyString()][string]$OnlyCase,
  [string]$LeanPath = 'C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0/bin/lean.exe',
  [ValidateRange(5, 600)][int]$StartupDeadlineSeconds = 120,
  [ValidateRange(30, 7200)][int]$RuntimeDeadlineSeconds = 1200,
  [switch]$RegistrySelfTestOnly,
  [switch]$SelectorBoundarySelfTestOnly,
  [switch]$DeadlineSelfTestOnly,
  [switch]$ArtifactCheckOnly,
  [switch]$SelectorProbeOnly,
  [switch]$StartupOnly
)

$ErrorActionPreference = 'Stop'
Set-StrictMode -Version Latest
$onlyCaseBound = $PSBoundParameters.ContainsKey('OnlyCase')
$repoRoot = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot '..'))
$scriptPath = Join-Path $PSScriptRoot 'packed_optimized_runtime.ps1'
$runtimePath = 'RMQ/Validation/PackedOptimized.lean'
$registryPath = 'docs/internal/extensions/opt1/runtime-replay/REGISTRY.md'
$selectorVariable = 'OPT1_RUNTIME_SELECTOR'
$hadSelector = Test-Path -LiteralPath "Env:$selectorVariable"
$savedSelector = if ($hadSelector) { (Get-Item -LiteralPath "Env:$selectorVariable").Value } else { $null }
$utf8 = [Text.UTF8Encoding]::new($false, $true)
$exitCode = 0
$artifactRoot = $null
$before = $null
$completionReceipt = $null
$stages = [Collections.Generic.List[object]]::new()

# Independent literals: never derive expected IDs/counts from the producer.
$registryVersion = 'v1'
$positiveIDs = @(
  'C01-ZERO-BRANCH', 'C02-NONZERO-BRANCH', 'C03-ZERO-LOOP', 'C04-ONE-LOOP',
  'C05-REPEATED-LOAD', 'C06-NESTED-LOOP', 'C07-EARLY-HALT', 'C08-FAILED-LOAD',
  'C09-EMPTY-BODY-BOUNDARY', 'C10-NESTED-SEQUENCE', 'C11-INITIALLY-HALTED',
  'C12-INITIALLY-FAULTED', 'C13-EMPTY-BRANCHES', 'Q01-EMPTY', 'Q02-SINGLE',
  'Q03-LEFTMOST-TIE', 'Q04-REVERSED', 'Q05-OUT-OF-RANGE', 'Q06-DIFFERENT-BLOCKS',
  'Q07-SAME-BLOCK', 'Q08-ADJACENT-BLOCKS', 'Q09-MALFORMED-METADATA', 'Q10-WORD-MAX')
$negativeIDs = @('N01-JUMP', 'N02-COUNTER', 'N03-BUDGET', 'N04-FRESH-COLLISION')
$allIDs = @($positiveIDs) + @($negativeIDs)

function Read-OPT1Source([string]$Path) {
  return [IO.File]::ReadAllText((Join-Path $repoRoot $Path), $utf8)
}

function Assert-OPT1Exact([string[]]$Actual, [string[]]$Expected, [string]$Label) {
  if (@($Expected).Count -eq 0 -or @($Actual).Count -ne @($Expected).Count -or
      ($Actual -join "`n") -cne ($Expected -join "`n") -or
      @($Actual | Select-Object -Unique).Count -ne @($Actual).Count) {
    throw "OPT1-REGISTRY: $Label missing, duplicate, extra, reordered or changed case"
  }
}

function Assert-OPT1Registry([string[]]$Cases = $allIDs, [string]$Markdown = '', [string]$Source = '') {
  if ($positiveIDs.Count -ne 23 -or $negativeIDs.Count -ne 4 -or $registryVersion -cne 'v1') {
    throw 'OPT1-REGISTRY: independent registry version/count mismatch'
  }
  Assert-OPT1Exact $Cases $allIDs 'literal registry'
  if ($Markdown -ceq '') { $Markdown = Read-OPT1Source $registryPath }
  if ($Source -ceq '') { $Source = Read-OPT1Source $runtimePath }
  if ([regex]::Matches($Markdown, '(?m)^Version: `v1`\. Exactly 27 cases: 23 expected accepts and four expected rejects\.\r?$').Count -ne 1) {
    throw 'OPT1-REGISTRY: Markdown version mismatch'
  }
  $rows = @([regex]::Matches($Markdown, '(?m)^\| ([CNQ][0-9]{2}-[^|]+?) \| (ACCEPT|REJECT) \| ([^|]+?) \|\r?$') |
    ForEach-Object { $_.Groups[1].Value + '|' + $_.Groups[2].Value + '|' + $_.Groups[3].Value })
  $expectedRows = @($positiveIDs | ForEach-Object { "$_|ACCEPT|none" }) +
    @($negativeIDs | ForEach-Object { "$_|REJECT|${_}: compiler observation mismatch" })
  Assert-OPT1Exact $rows $expectedRows 'Markdown registry'
  foreach ($entry in @(@{ Name='requiredIDs'; IDs=$positiveIDs }, @{ Name='negativeIDs'; IDs=$negativeIDs })) {
    $pattern = '(?ms)^def ' + $entry.Name + ' : List String := \[([^\]]*)\]'
    $declarations = [regex]::Matches($Source, $pattern)
    if ($declarations.Count -ne 1) { throw "OPT1-REGISTRY: source $($entry.Name) missing or duplicate" }
    $ids = @([regex]::Matches($declarations[0].Groups[1].Value, '"([^"]+)"') | ForEach-Object { $_.Groups[1].Value })
    Assert-OPT1Exact $ids $entry.IDs "source $($entry.Name)"
  }
  if (-not $Source.Contains('registry=v1') -or
      -not $Source.Contains('check (executed == selected)') -or
      -not $Source.Contains('check (actual.final.status == fixture.expected && actual.reads == fixture.receipts)') -or
      -not $Source.Contains('(fixture.id ++ ": compiler observation mismatch")') -or
      -not $Source.Contains('verifyCompiler fixture changed fuel')) {
    throw 'OPT1-REGISTRY: exact observation/receipt contract missing'
  }
}

function Get-OPT1Selection {
  if (-not $onlyCaseBound) { return $allIDs }
  if ([string]::IsNullOrWhiteSpace($OnlyCase)) { throw 'OPT1-SELECTOR: explicitly empty selector' }
  if ($OnlyCase -cnotmatch '^[CNQ][0-9]{2}-[A-Z][A-Z0-9-]*$') { throw 'OPT1-SELECTOR: malformed selector' }
  if (-not ($allIDs -ccontains $OnlyCase)) { throw "OPT1-SELECTOR: unknown selector $OnlyCase" }
  return @($OnlyCase)
}

function Write-OPT1Json([string]$Name, [object]$Value) {
  [IO.File]::WriteAllText((Join-Path $artifactRoot $Name), ($Value | ConvertTo-Json -Depth 12), $utf8)
}

function Invoke-OPT1Process([string]$Name, [string]$Executable, [string[]]$Arguments,
    [int]$Deadline, [hashtable]$Environment = @{}) {
  Write-Host "OPT1-STAGE $Name deadline=${Deadline}s"
  $result = Invoke-RMQOwnedBoundedProcess -FilePath $Executable -Arguments $Arguments `
    -WorkingDirectory $repoRoot -Stage $Name -DeadlineSeconds $Deadline `
    -OutputLimitBytes 4194304 -TempRoot $artifactRoot -Environment $Environment
  $record = [ordered]@{ Name=$Name; Executable=$Executable; Arguments=@($Arguments); Environment=$Environment; Result=$result }
  $stages.Add($record)
  Write-OPT1Json "$Name.json" $record
  [IO.File]::WriteAllLines((Join-Path $artifactRoot "$Name.stdout.log"), [string[]]$result.StandardOutput, $utf8)
  [IO.File]::WriteAllLines((Join-Path $artifactRoot "$Name.stderr.log"), [string[]]$result.StandardError, $utf8)
  return $result
}

function Assert-OPT1Bounded([object]$Result) {
  if ($Result.TimedOut -or $Result.OutputLimitExceeded) {
    throw "OPT1-PROCESS: $($Result.Stage) incomplete timeout=$($Result.TimedOut) outputLimit=$($Result.OutputLimitExceeded)"
  }
}

function Assert-OPT1Accepted([object]$Result, [string[]]$IDs) {
  Assert-OPT1Bounded $Result
  if ($Result.ExitCode -ne 0 -or @($Result.StandardError).Count -ne 0) {
    throw "OPT1-VERDICT: positive exit/stderr failure in $($Result.Stage)"
  }
  $text = $Result.StandardOutput -join "`n"
  $markers = @([regex]::Matches($text, '(?m)^OPT1 CASE ([CNQ][0-9]{2}-[A-Z0-9-]+) PASS steps=[0-9]+ reads=[0-9]+\r?$') |
    ForEach-Object { $_.Groups[1].Value })
  Assert-OPT1Exact $markers $IDs 'executed positive markers'
  $expected = "OPT1 PASS executed=$($IDs.Count) expected=$($IDs.Count) registry=$registryVersion"
  $summaries = @($Result.StandardOutput | Where-Object { $_ -cmatch '^OPT1 PASS ' })
  if ($summaries.Count -ne 1 -or $summaries[0] -cne $expected -or
      @($Result.StandardOutput | Where-Object { $_ -cmatch '^OPT1 CASE ' }).Count -ne $IDs.Count) {
    throw 'OPT1-VERDICT: missing, duplicate or malformed final/case receipt'
  }
}

function Assert-OPT1Rejected([object]$Result, [string]$Surface) {
  Assert-OPT1Bounded $Result
  $expected = "uncaught exception: $Surface"
  # The owned reader removes empty transport lines. Among retained lines the
  # complete grammar is one unpadded, case-sensitive diagnostic on exactly one
  # stream, with the other stream empty. Do not classify by finding a matching
  # substring: an additional exception, success record, resource error, or any
  # other nonempty output invalidates the intended semantic rejection.
  $lines = @($Result.StandardOutput) + @($Result.StandardError)
  if ($Result.ExitCode -ne 1 -or $lines.Count -ne 1 -or
      $lines[0] -cne $expected) {
    throw "OPT1-VERDICT: expected exact rejection '$Surface', observed exit=$($Result.ExitCode)"
  }
}

function Invoke-OPT1Lean([string]$Name, [AllowNull()][string]$Channel, [int]$Deadline, [string[]]$Extra = @()) {
  $environment = @{ LEAN_PATH=(Join-Path $repoRoot '.lake/build/lib/lean');
    LEAN_SYSROOT=[IO.Path]::GetFullPath((Join-Path ([IO.Path]::GetDirectoryName($LeanPath)) '..')) }
  if ($null -ne $Channel -and $Channel -cne '') { $environment[$selectorVariable] = $Channel }
  return Invoke-OPT1Process $Name $LeanPath (@('-j1', '--run', $runtimePath) + $Extra) $Deadline $environment
}

function Expect-OPT1Rejection([scriptblock]$Action, [string]$Prefix) {
  $rejected = $false
  try { & $Action } catch {
    if (-not $_.Exception.Message.StartsWith($Prefix, [StringComparison]::Ordinal)) { throw }
    $rejected = $true
  }
  if (-not $rejected) { throw 'OPT1-SELFTEST: corrupt control unexpectedly accepted' }
}

function Invoke-OPT1RegistryTests {
  Assert-OPT1Registry
  Expect-OPT1Rejection { Assert-OPT1Registry -Cases @() } 'OPT1-REGISTRY:'
  Expect-OPT1Rejection { Assert-OPT1Registry -Cases $allIDs[1..26] } 'OPT1-REGISTRY:'
  Expect-OPT1Rejection { Assert-OPT1Registry -Cases (@($allIDs) + @($allIDs[0])) } 'OPT1-REGISTRY:'
  Expect-OPT1Rejection { Assert-OPT1Registry -Cases (@($allIDs) + @('C99-UNKNOWN')) } 'OPT1-REGISTRY:'
  $swapped = $allIDs.Clone(); $swapped[0] = $allIDs[1]; $swapped[1] = $allIDs[0]
  Expect-OPT1Rejection { Assert-OPT1Registry -Cases $swapped } 'OPT1-REGISTRY:'
  $markdown = Read-OPT1Source $registryPath
  Expect-OPT1Rejection { Assert-OPT1Registry -Markdown $markdown.Replace('| C01-ZERO-BRANCH | ACCEPT | none |', '') } 'OPT1-REGISTRY:'
  $source = Read-OPT1Source $runtimePath
  Expect-OPT1Rejection { Assert-OPT1Registry -Source $source.Replace('"C01-ZERO-BRANCH", "C02-NONZERO-BRANCH"', '"C02-NONZERO-BRANCH"') } 'OPT1-REGISTRY:'
  $good = [pscustomobject]@{ Stage='fixture'; ExitCode=0; TimedOut=$false; OutputLimitExceeded=$false;
    StandardError=@(); StandardOutput=@('OPT1 CASE C01-ZERO-BRANCH PASS steps=3 reads=0', 'OPT1 PASS executed=1 expected=1 registry=v1') }
  Assert-OPT1Accepted $good @('C01-ZERO-BRANCH')
  $good.StandardOutput = @('OPT1 PASS executed=0 expected=0 registry=v1')
  Expect-OPT1Rejection { Assert-OPT1Accepted $good @('C01-ZERO-BRANCH') } 'OPT1-REGISTRY:'
  $bad = [pscustomobject]@{ Stage='fixture'; ExitCode=1; TimedOut=$false; OutputLimitExceeded=$false;
    StandardOutput=@('uncaught exception: N01-JUMP: compiler observation mismatch'); StandardError=@();
    Output=@('uncaught exception: N01-JUMP: compiler observation mismatch') }
  Assert-OPT1Rejected $bad 'N01-JUMP: compiler observation mismatch'
  Expect-OPT1Rejection { Assert-OPT1Rejected $bad 'N02-COUNTER: compiler observation mismatch' } 'OPT1-VERDICT:'
  $bad.TimedOut = $true
  Expect-OPT1Rejection { Assert-OPT1Rejected $bad 'N01-JUMP: compiler observation mismatch' } 'OPT1-PROCESS:'
  Write-Host 'OPT1-REGISTRY SELF-TEST PASS expected=27 empty/missing/duplicate/extra/reordered/source/markdown/zero-executed/wrong-reject/timeout'
}

function Invoke-OPT1SelectorTests {
  $wrapper = Join-Path $artifactRoot 'selector-boundary.ps1'
  [IO.File]::WriteAllText($wrapper, @'
param([string]$Target, [string]$Mode, [string]$Initial)
$ErrorActionPreference = 'Stop'
if ($Initial -eq 'present') { $env:OPT1_RUNTIME_SELECTOR = 'id:STALE-INHERITED-SELECTOR' }
else { Remove-Item Env:OPT1_RUNTIME_SELECTOR -ErrorAction SilentlyContinue }
switch ($Mode) {
  'omitted' { & $Target -SelectorProbeOnly }
  'valid' { & $Target -SelectorProbeOnly -OnlyCase 'C01-ZERO-BRANCH' }
  'empty' { & $Target -OnlyCase '' }
  'whitespace' { & $Target -OnlyCase ' ' }
  'malformed' { & $Target -OnlyCase 'C01-ZERO-BRANCH,C02-NONZERO-BRANCH' }
  'zero' { & $Target -OnlyCase '0' }
  'unknown' { & $Target -OnlyCase 'C99-UNKNOWN' }
  'duplicate' { try { & $Target -OnlyCase 'C01-ZERO-BRANCH' -OnlyCase 'C02-NONZERO-BRANCH' } catch { Write-Host 'OPT1-BOUNDARY: duplicate parameter rejected'; $global:LASTEXITCODE = 1 } }
}
$code = [int]$LASTEXITCODE
$exists = Test-Path Env:OPT1_RUNTIME_SELECTOR
if (($Initial -eq 'present' -and (-not $exists -or $env:OPT1_RUNTIME_SELECTOR -cne 'id:STALE-INHERITED-SELECTOR')) -or
    ($Initial -eq 'absent' -and $exists)) { throw 'OPT1-BOUNDARY: initial environment not restored' }
Write-Host "OPT1-BOUNDARY ENV PASS initial=$Initial"
exit $code
'@, $utf8)
  $shellPath = (Get-Process -Id $PID).Path
  foreach ($initial in @('present', 'absent')) {
    foreach ($mode in @('omitted', 'valid', 'empty', 'whitespace', 'malformed', 'zero', 'unknown', 'duplicate')) {
      $result = Invoke-OPT1Process "selector-$initial-$mode" $shellPath `
        @('-NoLogo', '-NoProfile', '-ExecutionPolicy', 'Bypass', '-File', $wrapper, '-Target', $scriptPath, '-Mode', $mode, '-Initial', $initial) 30
      Assert-OPT1Bounded $result
      $token = switch ($mode) {
        'omitted' { 'OPT1-SELECTOR PROBE PASS bound=False selected=27' }
        'valid' { 'OPT1-SELECTOR PROBE PASS bound=True selected=1 ids=C01-ZERO-BRANCH' }
        'empty' { 'OPT1-SELECTOR: explicitly empty selector' }
        'whitespace' { 'OPT1-SELECTOR: explicitly empty selector' }
        'malformed' { 'OPT1-SELECTOR: malformed selector' }
        'zero' { 'OPT1-SELECTOR: malformed selector' }
        'unknown' { 'OPT1-SELECTOR: unknown selector C99-UNKNOWN' }
        'duplicate' { 'OPT1-BOUNDARY: duplicate parameter rejected' }
      }
      $expectedExit = if ($mode -in @('omitted', 'valid')) { 0 } else { 1 }
      $joined = $result.Output -join "`n"
      if ($result.ExitCode -ne $expectedExit -or -not $joined.Contains($token) -or
          -not $joined.Contains("OPT1-BOUNDARY ENV PASS initial=$initial") -or
          $joined -match 'OPT1-STAGE|OPT1 CASE|OPT1 PASS executed') {
        throw "OPT1-BOUNDARY: $initial/$mode incorrect exit, selector receipt, environment restoration or semantic launch"
      }
    }
  }
  Write-Host 'OPT1-BOUNDARY SELF-TEST PASS executed=16 expected=16 host-script-only'
}

function Invoke-OPT1DeadlineTests {
  $shellPath = (Get-Process -Id $PID).Path
  $failure = Join-Path $artifactRoot 'nonzero.ps1'
  [IO.File]::WriteAllText($failure, '[Console]::Error.WriteLine("OPT1 controlled stderr"); exit 7', $utf8)
  $result = Invoke-OPT1Process 'nonzero-stderr' $shellPath @('-NoProfile', '-File', $failure) 30
  Assert-OPT1Bounded $result
  if ($result.ExitCode -ne 7 -or ($result.StandardError -join "`n") -cne 'OPT1 controlled stderr') {
    throw 'OPT1-DEADLINE: nonzero exit or stderr was lost'
  }
  $sleeper = Join-Path $artifactRoot 'owned-descendant.ps1'
  $pidPath = Join-Path $artifactRoot 'descendant.pid'
  $quotedShell = $shellPath.Replace("'", "''")
  $quotedPid = $pidPath.Replace("'", "''")
  $windowOption = if (Test-RMQOwnedProcessWindows) { '-WindowStyle Hidden' } else { '' }
  [IO.File]::WriteAllText($sleeper, @"
`$child = Start-Process -FilePath '$quotedShell' -ArgumentList @('-NoProfile', '-Command', 'Start-Sleep -Seconds 120') -PassThru $windowOption
[IO.File]::WriteAllText('$quotedPid', [string]`$child.Id)
Start-Sleep -Seconds 120
"@, $utf8)
  # The first 8s probe expired before the descendant started; an observed
  # 6.331s two-shell launch requires margin for the additional child startup.
  $result = Invoke-OPT1Process 'owned-descendant-timeout' $shellPath @('-NoProfile', '-File', $sleeper) 20
  if (-not $result.TimedOut) { throw 'OPT1-DEADLINE: sleeper did not time out' }
  if (-not (Test-Path -LiteralPath $pidPath)) { throw 'OPT1-DEADLINE: UNCOVERED descendant never started' }
  $childId = [int]([IO.File]::ReadAllText($pidPath).Trim())
  if ($null -ne (Get-Process -Id $childId -ErrorAction SilentlyContinue)) {
    Stop-Process -Id $childId -Force
    throw 'OPT1-DEADLINE: descendant survived owned barrier'
  }
  Write-OPT1Json 'deadline-coverage.json' @{ Host=[Environment]::OSVersion.Platform.ToString(); Descendant=$childId;
    Absent=$true; Ownership=$result.Ownership; OtherHost='UNCOVERED'; TrackedMutation='none' }
  Write-Host "OPT1-DEADLINE SELF-TEST PASS descendant=$childId absent=True ownership=$($result.Ownership); other host UNCOVERED"
}

function Get-OPT1ImportArtifacts {
  # --run elaborates its source but consumes existing imported artifacts.
  # Fail closed on a missing/stale local closure; never silently build it.
  $records = [Collections.Generic.Dictionary[string, object]]::new([StringComparer]::Ordinal)
  function Visit-OPT1Import([string]$Module) {
    if ($records.ContainsKey($Module)) { return }
    $relative = $Module.Replace('.', '/')
    $sourceRelative = $relative + '.lean'
    $artifactRelative = '.lake/build/lib/lean/' + $relative + '.olean'
    $source = Get-Item -LiteralPath (Join-Path $repoRoot $sourceRelative) -ErrorAction Stop
    $artifact = Get-Item -LiteralPath (Join-Path $repoRoot $artifactRelative) -ErrorAction Stop
    if ($artifact.LastWriteTimeUtc -lt $source.LastWriteTimeUtc) {
      throw "OPT1-IMPORT: stale artifact for $Module; rebuild the affected import closure before replay"
    }
    $record = [pscustomobject]@{ Module=$Module; Source=$sourceRelative; Artifact=$artifactRelative;
      SourceSHA256=(Get-FileHash -LiteralPath $source.FullName -Algorithm SHA256).Hash.ToLowerInvariant();
      ArtifactSHA256=(Get-FileHash -LiteralPath $artifact.FullName -Algorithm SHA256).Hash.ToLowerInvariant();
      SourceTimeUtc=$source.LastWriteTimeUtc.ToString('o'); ArtifactTimeUtc=$artifact.LastWriteTimeUtc.ToString('o') }
    $records.Add($Module, $record)
    foreach ($line in [regex]::Split((Read-OPT1Source $sourceRelative), '\r?\n')) {
      if ($line -match '^import\s+(.+)$') {
        foreach ($dependency in ($Matches[1] -split '\s+')) {
          if ($dependency -cnotmatch '^RMQ(?:\.[A-Za-z_][A-Za-z0-9_]*)*$') { continue }
          Visit-OPT1Import $dependency
          if ([DateTime]::Parse($records[$dependency].ArtifactTimeUtc).ToUniversalTime() -gt $artifact.LastWriteTimeUtc) {
            throw "OPT1-IMPORT: $Module predates rebuilt direct import $dependency"
          }
        }
      }
    }
  }
  foreach ($line in [regex]::Split((Read-OPT1Source $runtimePath), '\r?\n')) {
    if ($line -match '^import\s+(.+)$') {
      foreach ($module in ($Matches[1] -split '\s+')) {
        if ($module -cmatch '^RMQ(?:\.[A-Za-z_][A-Za-z0-9_]*)*$') { Visit-OPT1Import $module }
      }
    }
  }
  if ($records.Count -eq 0) { throw 'OPT1-IMPORT: local runtime import closure is empty' }
  return @($records.Values | Sort-Object Module)
}

function Get-OPT1Snapshot([string]$Name) {
  $gitPath = Resolve-RMQScalarApplicationPath @(Get-Command git -CommandType Application) 'git'
  $result = Invoke-OPT1Process "source-inventory-$Name" $gitPath @('ls-files', '--', 'RMQ', 'lean-toolchain', 'lakefile.toml') 30
  Assert-OPT1Bounded $result
  if ($result.ExitCode -ne 0) { throw 'OPT1-SOURCE: cannot inventory tracked sources' }
  $imports = @(Get-OPT1ImportArtifacts)
  Write-OPT1Json "imports-$Name.json" $imports
  $paths = @($result.StandardOutput) + @($runtimePath, 'scripts/packed_optimized_runtime.ps1', 'scripts/owned_process_tree.ps1', $registryPath) +
    @($imports | ForEach-Object { $_.Artifact }) +
    @(Get-ChildItem (Join-Path $repoRoot 'RMQ/Core/WordRAM/Optimization') -Filter '*.lean' | ForEach-Object { 'RMQ/Core/WordRAM/Optimization/' + $_.Name })
  $snapshot = [ordered]@{}
  foreach ($path in @($paths | Sort-Object -Unique)) {
    $snapshot[$path] = (Get-FileHash -LiteralPath (Join-Path $repoRoot $path) -Algorithm SHA256).Hash.ToLowerInvariant()
  }
  Write-OPT1Json "source-$Name.json" $snapshot
  return $snapshot
}

try {
  # Removal, rather than assigning $null, preserves genuine absence on PS 7.
  Remove-Item -LiteralPath "Env:$selectorVariable" -ErrorAction SilentlyContinue
  $selected = @(Get-OPT1Selection)
  Assert-OPT1Registry
  if (@(@($RegistrySelfTestOnly, $SelectorBoundarySelfTestOnly, $DeadlineSelfTestOnly, $ArtifactCheckOnly, $SelectorProbeOnly, $StartupOnly) | Where-Object { $_ }).Count -gt 1 -or
      ($onlyCaseBound -and ($RegistrySelfTestOnly -or $SelectorBoundarySelfTestOnly -or $DeadlineSelfTestOnly -or $ArtifactCheckOnly -or $StartupOnly))) {
    throw 'OPT1-SELECTOR: incompatible modes'
  }
  if ($SelectorProbeOnly) {
    Write-Host "OPT1-SELECTOR PROBE PASS bound=$onlyCaseBound selected=$($selected.Count) ids=$($selected -join ',')"
  } elseif ($RegistrySelfTestOnly) {
    Invoke-OPT1RegistryTests
  } else {
    . (Join-Path $PSScriptRoot 'owned_process_tree.ps1')
    $artifactRoot = Join-Path $repoRoot ('.lake/opt1-runtime-replay/' + [DateTime]::UtcNow.ToString('yyyyMMddTHHmmssZ') + '-' + [Guid]::NewGuid().ToString('N'))
    [void][IO.Directory]::CreateDirectory($artifactRoot)
    Write-Host "OPT1-ARTIFACTS $artifactRoot"
    if ($SelectorBoundarySelfTestOnly) { Invoke-OPT1SelectorTests }
    elseif ($DeadlineSelfTestOnly) { Invoke-OPT1DeadlineTests }
    elseif ($ArtifactCheckOnly) {
      $imports = @(Get-OPT1ImportArtifacts)
      Write-OPT1Json 'imports-check.json' $imports
      Write-Host "OPT1-IMPORT PASS checked=$($imports.Count) source/artifact/dependency freshness; no Lean launched"
    }
    else {
      if (-not (Test-Path -LiteralPath $LeanPath -PathType Leaf)) { throw "OPT1-PROCESS: exact Lean unavailable: $LeanPath" }
      if ((Read-OPT1Source 'lean-toolchain').Trim() -cne 'leanprover/lean4:v4.22.0') { throw 'OPT1-PROCESS: toolchain mismatch' }
      $before = Get-OPT1Snapshot 'before'
      if (-not $onlyCaseBound) {
        foreach ($id in @('C01-ZERO-BRANCH', 'C05-REPEATED-LOAD')) {
          $result = Invoke-OPT1Lean "startup-$id" "id:$id" $StartupDeadlineSeconds
          Assert-OPT1Accepted $result @($id)
        }
      }
      if ($StartupOnly) { Write-Host 'OPT1-STARTUP PASS executed=2 expected=2' }
      else {
        $executed = [Collections.Generic.List[string]]::new()
        $positives = @($selected | Where-Object { $positiveIDs -ccontains $_ })
        if ($positives.Count -gt 0) {
          $channel = if ($onlyCaseBound) { "id:$OnlyCase" } else { $null }
          $deadline = if ($onlyCaseBound) { $StartupDeadlineSeconds } else { $RuntimeDeadlineSeconds }
          $result = Invoke-OPT1Lean 'positive-cases' $channel $deadline
          Assert-OPT1Accepted $result $positives
          foreach ($id in $positives) { $executed.Add($id) }
        }
        foreach ($id in @($selected | Where-Object { $negativeIDs -ccontains $_ })) {
          $result = Invoke-OPT1Lean $id "id:$id" $StartupDeadlineSeconds
          Assert-OPT1Rejected $result "${id}: compiler observation mismatch"
          $executed.Add($id)
          Write-Host "OPT1 EXPECTED REJECT $id surface=compiler observation mismatch"
        }
        Assert-OPT1Exact @($executed) $selected 'final executed registry'
        if (-not $onlyCaseBound) {
          Invoke-OPT1SelectorTests
          foreach ($entry in @(
              @{ Name='empty'; Channel='id:'; Surface='OPT1 explicitly empty selector'; Args=@() },
              @{ Name='whitespace'; Channel='id: '; Surface='OPT1 explicitly empty selector'; Args=@() },
              @{ Name='malformed'; Channel='bad-channel'; Surface='OPT1 malformed selector channel'; Args=@() },
              @{ Name='unknown'; Channel='id:C99-UNKNOWN'; Surface='OPT1 unknown selector: C99-UNKNOWN'; Args=@() },
              @{ Name='duplicate'; Channel='id:C01-ZERO-BRANCH'; Surface='OPT1 duplicate or multiple selectors'; Args=@('C01-ZERO-BRANCH') })) {
            $result = Invoke-OPT1Lean "lean-selector-$($entry.Name)" $entry.Channel $StartupDeadlineSeconds $entry.Args
            Assert-OPT1Rejected $result $entry.Surface
          }
        }
        Write-OPT1Json 'executed.json' @{ Registry=$registryVersion; Expected=@($selected); Executed=@($executed) }
        $completionReceipt = "OPT1-REPLAY PASS executed=$($executed.Count) expected=$($selected.Count) registry=$registryVersion"
      }
    }
  }
} catch {
  $exitCode = 1
  [Console]::Error.WriteLine($_.Exception.Message)
} finally {
  if ($null -ne $before) {
    try {
      $after = Get-OPT1Snapshot 'after'
      if (($before | ConvertTo-Json -Compress) -cne ($after | ConvertTo-Json -Compress)) { throw 'OPT1-SOURCE: source hashes changed during replay' }
      Write-Host 'OPT1-SOURCE PASS exact source/import SHA256 before=after; tracked byte mutations=0; restoration not needed'
    } catch { $exitCode = 1; [Console]::Error.WriteLine($_.Exception.Message) }
  }
  if ($hadSelector) { Set-Item -LiteralPath "Env:$selectorVariable" -Value $savedSelector }
  else { Remove-Item -LiteralPath "Env:$selectorVariable" -ErrorAction SilentlyContinue }
  if ($null -ne $artifactRoot) { Write-OPT1Json 'summary.json' @{ ExitCode=$exitCode; Registry=$registryVersion; Stages=@($stages); InitialSelectorPresent=$hadSelector; TrackedMutations=0 } }
}
if ($exitCode -eq 0 -and $null -ne $completionReceipt) { Write-Host $completionReceipt }
exit $exitCode
