param([AllowEmptyString()][string]$Case)
$ErrorActionPreference = 'Stop'
$taskRoot = Split-Path $PSScriptRoot -Parent
. (Join-Path $PSScriptRoot 'owned_process_tree.ps1')
$taskBuild = Join-Path $taskRoot '.lake/native1/build'
$taskLogs = Join-Path $taskRoot 'docs/internal/extensions/native1/commands'
$taskFixtures = Join-Path $taskRoot 'native/packed-rmq/fixtures'
$taskScratch = Join-Path $taskBuild 'replay'
[void](New-Item -ItemType Directory -Force -Path $taskScratch, $taskLogs)
$taskRegistryPath = Join-Path $taskRoot 'native/packed-rmq/route-registry.json'
$taskRegistry = Get-Content -LiteralPath $taskRegistryPath -Raw | ConvertFrom-Json
$taskExactIds = @('smoke','n9-full','n9-empty','n9-range','n9-corrupt','n9-missing',
  'n12-interior','n12-same','n12-adjacent','n9-no-reads','malformed-instruction',
  'malformed-fixture','source-core-mutation','stale-source-rejection')
if ($taskRegistry.schema -cne 'native1-route-registry-v1' -or
    (($taskRegistry.cases.id -join ',') -cne ($taskExactIds -join ','))) {
  throw 'exact nonempty versioned registry mismatch'
}
if ($PSBoundParameters.ContainsKey('Case')) {
  if ([string]::IsNullOrWhiteSpace($Case) -or $Case -cnotmatch '^[a-z0-9-]+$' -or
      $taskExactIds -cnotcontains $Case) { throw 'invalid exact selector' }
  $taskSelected = @($taskRegistry.cases | Where-Object { $_.id -ceq $Case })
} else { $taskSelected = @($taskRegistry.cases) }
if ($taskSelected.Count -eq 0) { throw 'empty selection' }
$taskBuildManifest = Get-Content (Join-Path $taskBuild 'build-manifest.json') -Raw | ConvertFrom-Json
function Assert-NativeBuildIdentity {
  $exactSources = @('RMQ/Core/WordRAM/Packed/Primitive.lean',
    'RMQ/Core/WordRAM/Packed/Calculus.lean','RMQ/Core/WordRAM/Packed/Structured.lean',
    'RMQ/Core/WordRAM/Packed/Compiler.lean','RMQ/Core/WordRAM/Packed/Frame.lean',
    'RMQ/Core/WordRAM/Packed/Scratch.lean','RMQ/Core/WordRAM/Native/Finite.lean',
    'RMQ/Core/WordRAM/Native/Thin.lean','RMQ/Core/WordRAM/Native/Route.lean',
    'native/packed-rmq/route_shim.c','native/packed-rmq/include/packed_rmq_route.h',
    'native/packed-rmq/src/lib.rs','native/packed-rmq/src/main.rs',
    'native/packed-rmq/Cargo.toml','scripts/packed_native_build.ps1')
  if ($taskBuildManifest.schema -cne 'native1-build-v1' -or
      (($taskBuildManifest.sources.path -join ',') -cne ($exactSources -join ',')) -or
      (($taskBuildManifest.artifacts.path -join ',') -cne 'packed_route.dll,packed-rmq-route.exe')) {
    throw 'build manifest shape'
  }
  foreach ($pin in $taskBuildManifest.sources) {
    if ((Get-FileHash (Join-Path $taskRoot $pin.path)).Hash -cne $pin.sha256) {
      throw ('stale native source: ' + $pin.path)
    }
  }
  foreach ($pin in $taskBuildManifest.artifacts) {
    if ((Get-FileHash (Join-Path $taskBuild $pin.path)).Hash -cne $pin.sha256) {
      throw ('stale native artifact: ' + $pin.path)
    }
  }
}
Assert-NativeBuildIdentity
$taskLean = $taskBuildManifest.leanRoot
$env:LEAN_PATH = Join-Path $taskRoot '.lake/build/lib/lean'
$env:PATH = (Join-Path $taskLean 'bin') + ';' + $env:PATH
$taskManifest = Get-Content (Join-Path $taskFixtures 'manifest.json') -Raw | ConvertFrom-Json
$taskExactFixtures = @('n9-full','n9-empty','n9-range','n9-corrupt','n9-missing',
  'n12-interior','n12-same','n12-adjacent')
$taskExactFiles = @(@($taskExactFixtures | ForEach-Object { $_ + '.fixture'; $_ + '.expected' }) +
  @('program.txt.gz') | Sort-Object)
if ($taskManifest.schema -cne 'native1-fixtures-v1' -or
    $taskManifest.sourceCommit -cne '0e6a00f654abc64f8b68988fa9675b9a839dca2f' -or
    (($taskManifest.cases -join ',') -cne ($taskExactFixtures -join ',')) -or
    (($taskManifest.files.name -join ',') -cne ($taskExactFiles -join ','))) {
  throw 'exact fixture manifest mismatch'
}
foreach ($pin in $taskManifest.files) {
  if ((Get-FileHash (Join-Path $taskFixtures $pin.name)).Hash -cne $pin.sha256) {
    throw ('fixture hash mismatch: ' + $pin.name)
  }
}
$taskProgram = Join-Path $taskScratch 'program.txt'
$taskInput = [IO.File]::OpenRead((Join-Path $taskFixtures 'program.txt.gz'))
$taskOutput = [IO.File]::Create($taskProgram)
try {
  $taskGzip = [IO.Compression.GZipStream]::new($taskInput, [IO.Compression.CompressionMode]::Decompress)
  try { $taskGzip.CopyTo($taskOutput) } finally { $taskGzip.Dispose() }
} finally { $taskInput.Dispose(); $taskOutput.Dispose() }
if ((Get-FileHash $taskProgram).Hash -cne $taskManifest.programSha256) { throw 'program hash mismatch' }
$taskResults = [Collections.Generic.List[object]]::new()
$taskRunId = [DateTime]::UtcNow.ToString('yyyyMMddTHHmmssfff')
$taskSuccess = $false
function Invoke-NativeReplayProcess([string]$Stage, [string]$Exe, [string[]]$StageArgs, [int]$Deadline = 120) {
  $r = Invoke-RMQOwnedBoundedProcess -FilePath $Exe -Arguments $StageArgs `
    -WorkingDirectory $taskRoot -Stage $Stage -DeadlineSeconds $Deadline `
    -OutputLimitBytes 8388608 -TempRoot (Join-Path $taskScratch 'process')
  if ($r.TimedOut -or $r.OutputLimitExceeded) {
    $taskResults.Add(@{id=$Stage; pass=$false; process=$r; incomplete=$true})
    throw ("bounded process incomplete: " + $Stage)
  }
  return $r
}
try {
  foreach ($entry in $taskSelected) {
    Assert-NativeBuildIdentity
    $details = $null
    if ($entry.kind -eq 'source-mutation' -or $entry.kind -eq 'source-pin') {
      $source = Join-Path $taskRoot 'RMQ/Core/WordRAM/Native/Route.lean'
      $saved = [IO.File]::ReadAllBytes($source)
      $before = (Get-FileHash $source).Hash
      $stateBefore = ((& git diff --binary -- RMQ/Core/WordRAM/Native/Route.lean) -join "\n")
      try {
        $text = [Text.UTF8Encoding]::new($false,$true).GetString($saved)
        if ($entry.kind -eq 'source-pin') {
          [IO.File]::WriteAllText($source, $text + "\n-- stale-source control\n", [Text.UTF8Encoding]::new($false))
          $rejected = $false
          try { Assert-NativeBuildIdentity } catch {
            if ($_.Exception.Message -notlike 'stale native source:*') { throw }
            $rejected = $true
          }
          if (-not $rejected) { throw 'stale source accepted' }
          $details = @{verdict='stale-source rejected'; beforeSha256=$before}
        } else {
          $old = 'runThin observeReads memory program fuel s {}'
          if ([regex]::Matches($text, [regex]::Escape($old)).Count -ne 1) { throw 'source mutation anchor not unique' }
          [IO.File]::WriteAllText($source, $text.Replace($old, 'runThin observeReads memory program 0 s {}'),
            [Text.UTF8Encoding]::new($false))
          $r = Invoke-NativeReplayProcess $entry.id (Join-Path $taskLean 'bin/lean.exe') `
            @('-j','1','-o',(Join-Path $taskScratch 'mutated.olean'),
              'RMQ/Core/WordRAM/Native/Route.lean') 120
          $proofLine = '  runThin_projection observeReads memory program fuel s {}'
          $proofLines = @([regex]::Split($text, '\r?\n'))
          $line = [Array]::IndexOf($proofLines, $proofLine) + 1
          if ($line -le 0 -or @($proofLines | Where-Object { $_ -ceq $proofLine }).Count -ne 1) {
            throw 'exact routeCore_source consumer line is not unique'
          }
          $failurePattern = '^RMQ/Core/WordRAM/Native/Route\.lean:' + $line + ':\d+: error: (?i:type mismatch)'
          $matching = @($r.Output | Where-Object { $_ -match $failurePattern })
          if ($r.ExitCode -eq 0 -or $matching.Count -ne 1) {
            throw 'core mutation did not fail at the expected type-checking surface'
          }
          $details = @{process=$r; failingSurface='routeCore_source'; expectedLine=$line;
            matchedDiagnostics=$matching; beforeSha256=$before}
        }
      } finally {
        [IO.File]::WriteAllBytes($source, $saved)
        if ((Get-FileHash $source).Hash -cne $before) { throw 'source restoration hash mismatch' }
        $stateAfter = ((& git diff --binary -- RMQ/Core/WordRAM/Native/Route.lean) -join "\n")
        if ($stateAfter -cne $stateBefore) { throw 'source restoration diff mismatch' }
      }
      Assert-NativeBuildIdentity
    } else {
      $p = $taskProgram
      $f = Join-Path $taskScratch ($entry.id + '.fixture')
      $mode = 'reads'
      $exitExpected = 0
      if ($entry.kind -eq 'fixture') {
        $f = Join-Path $taskFixtures ($entry.fixture + '.fixture')
        $expected = [IO.File]::ReadAllText((Join-Path $taskFixtures ($entry.fixture + '.expected'))).TrimEnd()
        $mode = $entry.mode
        if ($mode -eq 'quiet') { $expected = (($expected -split "\r?\n" | Select-Object -First 2) -join "`n") }
      } else {
        $p = Join-Path $taskScratch ($entry.id + '.program')
        if ($entry.kind -eq 'smoke') {
          [IO.File]::WriteAllText($p, "1 3 8`n8 3`n")
          [IO.File]::WriteAllText($f, "9 0 9 168 100`n")
        } else {
          [IO.File]::WriteAllText($p, $entry.program)
          [IO.File]::WriteAllText($f, $entry.fixture)
          $exitExpected = $entry.exit
        }
        $expected = $entry.expected
      }
      $r = Invoke-NativeReplayProcess $entry.id (Join-Path $taskBuild 'packed-rmq-route.exe') @($p,$f,$mode)
      $actual = ($r.StandardOutput -join "`n").TrimEnd()
      $expected = ($expected -replace "\r\n","`n").TrimEnd()
      if ($r.ExitCode -ne $exitExpected -or $actual -cne $expected) {
        $taskResults.Add(@{id=$entry.id; pass=$false; expected=$expected; actual=$actual; process=$r})
        throw ('exact observation comparison failed: ' + $entry.id)
      }
      $details = @{process=$r; expectedExit=$exitExpected; exactOutput=$true; outputLines=$r.StandardOutput.Count}
    }
    $taskResults.Add(@{id=$entry.id; pass=$true; evidence=$details})
    Write-Output ('NATIVE1-ROUTE PASS ' + $entry.id)
  }
  if (($taskResults.id -join ',') -cne ($taskSelected.id -join ',')) { throw 'executed registry mismatch' }
  $taskSuccess = $true
} finally {
  $report = [ordered]@{
    schema='native1-route-results-v1'; success=$taskSuccess; run=$taskRunId
    platform=[Environment]::OSVersion.VersionString
    registrySha256=(Get-FileHash $taskRegistryPath).Hash
    expectedCases=@($taskSelected.id); executedCases=@($taskResults.id)
    expectedCount=$taskSelected.Count; executedCount=$taskResults.Count
    results=@($taskResults.ToArray())
    unsupportedHosts=@('Non-Windows execution not covered by this experiment')
  }
  [IO.File]::WriteAllText((Join-Path $taskLogs ('route-' + $taskRunId + '.json')),
    ($report | ConvertTo-Json -Depth 14), [Text.UTF8Encoding]::new($false))
}
