param([AllowEmptyString()][string]$Case)
$ErrorActionPreference = 'Stop'
$validatorRoot = Split-Path $PSScriptRoot -Parent
. (Join-Path $PSScriptRoot 'owned_process_tree.ps1')
$validatorRegistryPath = Join-Path $PSScriptRoot 'packed_native_validator_controls.cases.json'
$validatorRegistryHash = '60D07EC27D7854FEB107CE8A1148F382F17F882CD8F2F18427FBD8BDE8D755EC'
if ((Get-FileHash -LiteralPath $validatorRegistryPath -Algorithm SHA256).Hash -cne $validatorRegistryHash) {
  throw 'exact validator controls registry bytes mismatch'
}
$validatorRegistry = [Text.UTF8Encoding]::new($false,$true).GetString(
  [IO.File]::ReadAllBytes($validatorRegistryPath)) | ConvertFrom-Json
$validatorControlIDs = @(
  'omitted-default',
  'selector-valid-argument',
  'selector-valid-environment',
  'selector-empty-argument',
  'selector-empty-environment',
  'selector-whitespace-argument',
  'selector-whitespace-environment',
  'selector-malformed-argument',
  'selector-malformed-environment',
  'selector-unknown',
  'selector-duplicate',
  'compare-golden',
  'compare-quiet',
  'compare-wrong-golden',
  'compare-malformed-hex',
  'compare-wrong-hex-length',
  'compare-fuel-limit',
  'compare-fuel-format',
  'compare-read-mode',
  'compare-oversized-file',
  'compare-nonutf8',
  'compare-truncated',
  'compare-crlf',
  'compare-selector-channel'
)
if ($validatorRegistry.schema -cne 'native1-lean-validator-controls-v1' -or
    $validatorControlIDs.Count -ne 24 -or
    @($validatorControlIDs | Select-Object -Unique).Count -ne 24 -or
    (@($validatorRegistry.cases.id) -join '|') -cne ($validatorControlIDs -join '|')) {
  throw 'exact nonempty validator controls registry mismatch'
}
if ($PSBoundParameters.ContainsKey('Case')) {
  if ([string]::IsNullOrWhiteSpace($Case) -or $Case -cnotmatch '^[a-z0-9-]+$' -or
      $validatorControlIDs -cnotcontains $Case) {
    throw 'invalid exact validator controls selector'
  }
  $validatorSelectedIDs = @($Case)
} else { $validatorSelectedIDs = @($validatorControlIDs) }
if ([Environment]::OSVersion.Platform -ne [PlatformID]::Win32NT) {
  throw 'validator process replay currently supports the pinned Windows Lean distribution only'
}
$validatorLean = Join-Path $env:USERPROFILE '.elan/toolchains/leanprover--lean4---v4.22.0/bin/lean.exe'
if (-not (Test-Path -LiteralPath $validatorLean -PathType Leaf) -or
    ([IO.File]::ReadAllText((Join-Path $validatorRoot 'lean-toolchain'))).Trim() -cne
      'leanprover/lean4:v4.22.0') { throw 'pinned Lean compiler is unavailable' }
$validatorLeanPath = Join-Path $validatorRoot '.lake/build/lib/lean'
$validatorArtifactDirectory = Join-Path $validatorRoot (
  '.lake/native1/validator-replay/' + [Guid]::NewGuid().ToString('N'))
$validatorProcessDirectory = Join-Path $validatorRoot '.lake/native1/validator-replay-process'
$validatorReportDirectory = Join-Path $validatorRoot 'docs/internal/extensions/native1/commands'
[void](New-Item -ItemType Directory -Force -Path $validatorArtifactDirectory,$validatorReportDirectory)
$validatorUtf8 = [Text.UTF8Encoding]::new($false,$true)

# These files preserve the committed input/expected literals. No native result
# is consulted while preparing either side of a comparison.
$validatorFiles = @{
  '@image' = Join-Path $validatorArtifactDirectory 'smoke.bin'
  '@golden' = Join-Path $validatorArtifactDirectory 'smoke.expected'
  '@wrong' = Join-Path $validatorArtifactDirectory 'wrong.expected'
  '@crlf' = Join-Path $validatorArtifactDirectory 'crlf.expected'
  '@nonutf8' = Join-Path $validatorArtifactDirectory 'nonutf8.expected'
  '@truncated' = Join-Path $validatorArtifactDirectory 'truncated.bin'
  '@oversized' = Join-Path $validatorArtifactDirectory 'oversized.bin'
}
$validatorImage = [byte[]]@($validatorRegistry.fixtures.image)
if ($validatorImage.Length -ne 35) { throw 'literal smoke image length mismatch' }
[IO.File]::WriteAllBytes($validatorFiles['@image'], $validatorImage)
[IO.File]::WriteAllBytes($validatorFiles['@golden'],
  $validatorUtf8.GetBytes([string]$validatorRegistry.fixtures.golden))
[IO.File]::WriteAllBytes($validatorFiles['@wrong'],
  $validatorUtf8.GetBytes([string]$validatorRegistry.fixtures.wrong))
[IO.File]::WriteAllBytes($validatorFiles['@crlf'],
  $validatorUtf8.GetBytes(([string]$validatorRegistry.fixtures.golden).Replace("`n","`r`n")))
[IO.File]::WriteAllBytes($validatorFiles['@nonutf8'], [byte[]]@(255))
[IO.File]::WriteAllBytes($validatorFiles['@truncated'], [byte[]]@($validatorImage[0..33]))
$validatorNeedsOversize = $validatorSelectedIDs -ccontains 'compare-oversized-file'
if ($validatorNeedsOversize) {
  $stream = [IO.File]::Open($validatorFiles['@oversized'], [IO.FileMode]::CreateNew)
  try { $stream.SetLength([long]$validatorRegistry.fixtures.oversizedLength) }
  finally { $stream.Dispose() }
}

function Get-ValidatorFilePin([string]$Path) {
  return [ordered]@{path=[IO.Path]::GetFullPath($Path);
    bytes=(Get-Item -LiteralPath $Path).Length;
    sha256=(Get-FileHash -LiteralPath $Path -Algorithm SHA256).Hash}
}
$validatorAliases = [string[]]@($validatorFiles.Keys)
[Array]::Sort($validatorAliases,[StringComparer]::Ordinal)
$validatorFixturePins = @($validatorAliases | ForEach-Object {
  if (Test-Path -LiteralPath $validatorFiles[$_] -PathType Leaf) {
    $pin = Get-ValidatorFilePin $validatorFiles[$_]
    $pin.alias = $_
    $pin
  }
})
$validatorModules = @('Contract','Capstone','Execution','Host','CanonicalImage','Canonical',
  'Entry','Runtime','Observations','Binary','Binary/Bounds','Binary/Codec','Binary/Cursor',
  'Binary/Cursor/Core','Machine','Machine/CodeFacts','Limbs','Route','Thin','Finite')
$validatorSourcePins = @(
  Get-ValidatorFilePin $PSCommandPath
  Get-ValidatorFilePin $validatorRegistryPath
  Get-ValidatorFilePin (Join-Path $validatorRoot 'RMQ/Validation/PackedNative.lean')
  Get-ValidatorFilePin (Join-Path $PSScriptRoot 'owned_process_tree.ps1')
  Get-ValidatorFilePin (Join-Path $validatorRoot 'lean-toolchain')
  Get-ValidatorFilePin $validatorLean
  foreach ($module in $validatorModules) {
    Get-ValidatorFilePin (Join-Path $validatorRoot ('RMQ/Core/WordRAM/Native/' + $module + '.lean'))
    # No build fallback: require the previously checked import closure and record
    # its exact object bytes as well as source bytes for this execution.
    Get-ValidatorFilePin (Join-Path $validatorLeanPath ('RMQ/Core/WordRAM/Native/' + $module + '.olean'))
  }
)

function Assert-ValidatorExactLines([object[]]$Actual, [object[]]$Expected, [string]$Label) {
  if (@($Actual).Count -ne @($Expected).Count -or
      (@($Actual) -join "`n") -cne (@($Expected) -join "`n")) {
    throw ($Label + ' mismatch')
  }
}
$validatorResults = [Collections.Generic.List[object]]::new()
$validatorSuccess = $false
$validatorFailure = $null
$validatorToolchain = $null
$validatorSourceUnchanged = $false
$validatorFixturesUnchanged = $false
$validatorSavedSelector = [Environment]::GetEnvironmentVariable('NATIVE1_LEAN_SELECTOR','Process')
try {
  # PowerShell's .NET string conversion can turn null into an empty value.
  # The environment provider removes the key, preserving absent versus bound-empty.
  Remove-Item -LiteralPath Env:NATIVE1_LEAN_SELECTOR -ErrorAction SilentlyContinue
  if ([Environment]::GetEnvironmentVariables('Process').Contains('NATIVE1_LEAN_SELECTOR')) {
    throw 'validator selector environment was not removed'
  }
  $validatorToolchain = Invoke-RMQOwnedBoundedProcess -FilePath $validatorLean -Arguments @('--version') `
    -WorkingDirectory $validatorRoot -Stage 'validator-replay-toolchain' -DeadlineSeconds 30 `
    -OutputLimitBytes 1048576 -TempRoot $validatorProcessDirectory
  if ($validatorToolchain.ExitCode -ne 0 -or $validatorToolchain.TimedOut -or
      $validatorToolchain.OutputLimitExceeded) { throw 'bounded Lean identity check failed' }
  Assert-ValidatorExactLines $validatorToolchain.StandardOutput @(
    'Lean (version 4.22.0, x86_64-w64-windows-gnu, commit ba2cbbf09d4978f416e0ebd1fceeebc2c4138c05, Release)'
  ) 'pinned Lean identity stdout'
  Assert-ValidatorExactLines $validatorToolchain.StandardError @() 'pinned Lean identity stderr'

  foreach ($id in $validatorSelectedIDs) {
    $row = @($validatorRegistry.cases | Where-Object { $_.id -ceq $id })
    if ($row.Count -ne 1) { throw 'selected control was not unique' }
    $row = $row[0]
    $childArguments = @('-j','1','--run','RMQ/Validation/PackedNative.lean')
    foreach ($argument in @($row.arguments)) {
      if ($validatorFiles.ContainsKey([string]$argument)) {
        $childArguments += @([string]$validatorFiles[[string]$argument])
      } else { $childArguments += @([string]$argument) }
    }
    $childEnvironment = @{LEAN_PATH=$validatorLeanPath}
    if ($null -ne $row.selectorEnvironment) {
      $childEnvironment.NATIVE1_LEAN_SELECTOR = [string]$row.selectorEnvironment
    }
    # Invoke the process-tree helper directly. The older mandatory argument
    # wrapper rejects an empty element before Lean starts and is not used here.
    $result = Invoke-RMQOwnedBoundedProcess -FilePath $validatorLean -Arguments $childArguments `
      -WorkingDirectory $validatorRoot -Stage ('validator-replay-' + $id) -DeadlineSeconds 60 `
      -OutputLimitBytes 8388608 -TempRoot $validatorProcessDirectory -Environment $childEnvironment
    $evidence = [ordered]@{id=$id;pass=$false;expectedExit=$row.exit;
      expectedStdout=@($row.stdout);expectedStderr=@($row.stderr);
      invokedFile=$validatorLean;invokedArguments=@($childArguments);
      invokedEnvironment=$childEnvironment;process=$result}
    $validatorResults.Add($evidence)
    if ($result.TimedOut -or $result.OutputLimitExceeded) {
      throw ('incomplete bounded validator child: ' + $id)
    }
    if ($result.ExitCode -ne $row.exit) { throw ('validator exit mismatch: ' + $id) }
    Assert-ValidatorExactLines $result.StandardOutput @($row.stdout) ($id + ' stdout')
    Assert-ValidatorExactLines $result.StandardError @($row.stderr) ($id + ' stderr')
    $evidence.pass = $true
    Write-Output ('NATIVE1-VALIDATOR-CONTROL PASS ' + $id)
  }
  if ($validatorResults.Count -eq 0 -or
      (@($validatorResults | ForEach-Object { $_.id }) -join '|') -cne ($validatorSelectedIDs -join '|')) {
    throw 'executed/expected validator controls registry mismatch'
  }
  $validatorSuccess = $true
} catch {
  $validatorFailure = $_.Exception.Message
} finally {
  if ($null -eq $validatorSavedSelector) {
    Remove-Item -LiteralPath Env:NATIVE1_LEAN_SELECTOR -ErrorAction SilentlyContinue
  } else {
    [Environment]::SetEnvironmentVariable('NATIVE1_LEAN_SELECTOR',$validatorSavedSelector,'Process')
  }
  $validatorSourceUnchanged = $true
  $validatorFixturesUnchanged = $true
  foreach ($pin in $validatorSourcePins) {
    if (-not (Test-Path -LiteralPath $pin.path -PathType Leaf) -or
        (Get-FileHash -LiteralPath $pin.path -Algorithm SHA256).Hash -cne $pin.sha256) {
      $validatorSourceUnchanged = $false
    }
  }
  foreach ($pin in $validatorFixturePins) {
    if (-not (Test-Path -LiteralPath $pin.path -PathType Leaf) -or
        (Get-FileHash -LiteralPath $pin.path -Algorithm SHA256).Hash -cne $pin.sha256) {
      $validatorFixturesUnchanged = $false
    }
  }
  if (-not $validatorSourceUnchanged -or -not $validatorFixturesUnchanged) {
    $validatorSuccess = $false
    $validatorFailure = 'source/import/fixture bytes changed during validator replay'
  }
  # The one oversized temporary is removed only after its unchanged hash was
  # checked; all small literal fixture files remain with the report.
  if ($validatorNeedsOversize -and (Test-Path -LiteralPath $validatorFiles['@oversized'])) {
    $oversizeTarget = [IO.Path]::GetFullPath($validatorFiles['@oversized'])
    $artifactPrefix = [IO.Path]::GetFullPath($validatorArtifactDirectory) + [IO.Path]::DirectorySeparatorChar
    if (-not $oversizeTarget.StartsWith($artifactPrefix,[StringComparison]::OrdinalIgnoreCase)) {
      throw 'oversized fixture cleanup path escaped its declared directory'
    }
    Remove-Item -LiteralPath $oversizeTarget -Force
  }
  $validatorCompletedIDs = @($validatorResults | Where-Object { $_.pass } | ForEach-Object { $_.id })
  $record = [ordered]@{schema='native1-validator-controls-results-v1';
    success=$validatorSuccess;failure=$validatorFailure;
    platform=[Environment]::OSVersion.VersionString;powershell=$PSVersionTable.PSVersion.ToString();
    registrySha256=$validatorRegistryHash;registryCases=$validatorControlIDs;registryCount=24;
    selectorBound=$PSBoundParameters.ContainsKey('Case');selector=$Case;
    expectedCases=$validatorSelectedIDs;
    executedCases=$validatorCompletedIDs;
    attemptedCases=@($validatorResults | ForEach-Object { $_.id });
    expectedCount=$validatorSelectedIDs.Count;executedCount=$validatorCompletedIDs.Count;
    sourcePins=$validatorSourcePins;sourceAndImportsUnchanged=$validatorSourceUnchanged;
    literalFixtures=$validatorFixturePins;literalFixturesUnchanged=$validatorFixturesUnchanged;
    oversizedTemporaryRemoved=$validatorNeedsOversize;
    toolchain=$validatorToolchain;results=@($validatorResults.ToArray());
    unsupportedHosts=@('Non-Windows process replay is not covered by this runner')}
  $reportPath = Join-Path $validatorReportDirectory (
    'validator-controls-' + [DateTime]::UtcNow.ToString('yyyyMMddTHHmmssfff') + '.json')
  [IO.File]::WriteAllText($reportPath, ($record | ConvertTo-Json -Depth 24), $validatorUtf8)
  Write-Output ('NATIVE1-VALIDATOR-CONTROLS-REPORT ' + $reportPath)
}
if (-not $validatorSuccess) { throw ('validator controls failed: ' + $validatorFailure) }
Write-Output ('NATIVE1-VALIDATOR-CONTROLS PASS executed=' + $validatorResults.Count +
  ' expected=' + $validatorSelectedIDs.Count)
