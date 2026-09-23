param([AllowEmptyString()][string]$Case)
$ErrorActionPreference = 'Stop'
$taskRoot = Split-Path $PSScriptRoot -Parent
$taskRegistryPath = Join-Path $PSScriptRoot 'packed_native_binary_cases.json'
$taskBuild = Join-Path $taskRoot '.lake/native1/binary-build'
$taskScratch = Join-Path $taskBuild 'replay'
$taskLogs = Join-Path $taskRoot 'docs/internal/extensions/native1/binary-commands'
$taskProducer = Join-Path $PSScriptRoot 'packed_native_cases.py'
$taskPython = 'C:/Users/poin/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe'
# This whole-byte pin includes every nested semantic property and formatting.
# Intentional semantic/format changes require authoring a new version and pin.
$taskExactRegistrySha256 = '2D38A1002C1E8A72DF5E164144EC4E8F5410511F2C585831AEFBBC0D1BD4C637'
if ((Get-FileHash -LiteralPath $taskRegistryPath).Hash -cne $taskExactRegistrySha256) {
  throw 'exact binary semantic registry mismatch'
}
$taskRegistry = Get-Content -LiteralPath $taskRegistryPath -Raw | ConvertFrom-Json
if ($taskRegistry.schema -cne 'native1-binary-cases-v1' -or $taskRegistry.cases.Count -ne 109 -or
    @($taskRegistry.cases.id | Select-Object -Unique).Count -ne 109) {
  throw 'exact nonempty versioned binary registry mismatch'
}
$taskIds = @($taskRegistry.cases.id)
if ($PSBoundParameters.ContainsKey('Case')) {
  if ([string]::IsNullOrWhiteSpace($Case) -or $Case -cnotmatch '^[a-z0-9-]+$' -or
      $taskIds -cnotcontains $Case) { throw 'invalid exact binary selector' }
  $taskSelected = @($taskRegistry.cases | Where-Object id -CEQ $Case)
} else { $taskSelected = @($taskRegistry.cases) }
if ($taskSelected.Count -eq 0) { throw 'empty binary selection' }
if ($taskRegistry.status -cne 'FROZEN') { throw 'binary registry not frozen for execution' }
if ((Get-FileHash -LiteralPath $taskProducer).Hash -cne $taskRegistry.producerSha256 -or
    (Get-FileHash -LiteralPath (Join-Path $PSScriptRoot 'packed_native_image.py')).Hash -cne $taskRegistry.encoderSha256) {
  throw 'binary fixture producer identity mismatch'
}
$taskBuildManifest = Get-Content -LiteralPath (Join-Path $taskBuild 'build-manifest.json') -Raw | ConvertFrom-Json
# Complete independently frozen Entry import closure and native build inputs.
$taskExactSources = @(
  'RMQ/Core/WordRAM/Packed/Primitive.lean','RMQ/Core/WordRAM/Packed/Calculus.lean',
  'RMQ/Core/WordRAM/Packed/Structured.lean','RMQ/Core/WordRAM/Packed/Compiler.lean',
  'RMQ/Core/WordRAM/Packed/Frame.lean','RMQ/Core/WordRAM/Packed/Scratch.lean',
  'RMQ/Core/WordRAM/Native/Finite.lean','RMQ/Core/WordRAM/Native/Thin.lean',
  'RMQ/Core/WordRAM/Native/Route.lean','RMQ/Core/WordRAM/Native/Limbs.lean',
  'RMQ/Core/WordRAM/Native/Machine.lean','RMQ/Core/WordRAM/Native/Observations.lean',
  'RMQ/Core/WordRAM/Native/Binary/Codec.lean','RMQ/Core/WordRAM/Native/Binary.lean',
  'RMQ/Core/WordRAM/Native/Binary/Bounds.lean','RMQ/Core/WordRAM/Native/Binary/Cursor/Core.lean',
  'RMQ/Core/WordRAM/Native/Binary/Cursor.lean','RMQ/Core/WordRAM/Native/Runtime.lean',
  'RMQ/Core/WordRAM/Native/Entry.lean',
  'native/packed-rmq/native_shim.c','native/packed-rmq/include/packed_rmq.h',
  'native/packed-rmq/src/lib.rs','native/packed-rmq/src/native.rs',
  'native/packed-rmq/src/native_main.rs','native/packed-rmq/Cargo.toml',
  'scripts/packed_native_binary_build.ps1','native/packed-rmq/Cargo.lock',
  'native/packed-rmq/examples/native.cpp','native/packed-rmq/packed_rmq.def',
  'scripts/packed_native_identity.ps1','scripts/owned_process_tree.ps1')
$taskExactGeneratedC = @($taskExactSources | Where-Object { $_.EndsWith('.lean') } |
  ForEach-Object { '.lake/build/ir/' + $_.Substring(0,$_.Length - 5) + '.c' })
function Assert-BinaryBuildIdentity {
  if ($taskExactSources.Count -eq 0) { throw 'binary source inventory not frozen' }
  if ($taskBuildManifest.schema -cne 'native1-binary-build-v1' -or
      ($null -ne $taskBuildManifest.toolchainIdentity -and
       [IO.Path]::GetFullPath([string]$taskBuildManifest.leanRoot) -cne $taskBuildManifest.toolchainIdentity.leanRoot) -or
      (($taskBuildManifest.sources.path -join ',') -cne ($taskExactSources -join ',')) -or
      (($taskBuildManifest.generatedC.path -join ',') -cne ($taskExactGeneratedC -join ',')) -or
      (($taskBuildManifest.artifacts.path -join ',') -cne 'packed_rmq.dll,packed-rmq-native.exe,packed-rmq-native-cpp.exe')) {
    throw 'binary build manifest shape'
  }
  foreach ($pin in $taskBuildManifest.sources) {
    if ((Get-FileHash -LiteralPath (Join-Path $taskRoot $pin.path)).Hash -cne $pin.sha256) {
      throw ('stale native source: ' + $pin.path)
    }
  }
  foreach ($pin in $taskBuildManifest.artifacts) {
    if ((Get-FileHash -LiteralPath (Join-Path $taskBuild $pin.path)).Hash -cne $pin.sha256) {
      throw ('stale native artifact: ' + $pin.path)
    }
  }
}
function Assert-BinaryGeneratedCIdentity {
  foreach ($pin in $taskBuildManifest.generatedC) {
    if ((Get-FileHash -LiteralPath (Join-Path $taskRoot $pin.path)).Hash -cne $pin.sha256) {
      throw ('stale generated native C: ' + $pin.path)
    }
  }
}
Assert-BinaryBuildIdentity
# Pure malformed registry/selector/build inputs reject before initializing the
# process-owner C# runtime. Both helpers' source hashes were verified above;
# every actual subprocess still uses the same ownership/deadline mechanism.
. (Join-Path $PSScriptRoot 'packed_native_identity.ps1')
Assert-NativeIdentityShape $taskBuildManifest.toolchainIdentity
. (Join-Path $PSScriptRoot 'owned_process_tree.ps1')
$taskLean = $taskBuildManifest.leanRoot
$env:LEAN_PATH = Join-Path $taskRoot '.lake/build/lib/lean'
$env:PATH = (Join-Path $taskLean 'bin') + ';' + $env:PATH
[void](New-Item -ItemType Directory -Force -Path $taskScratch, $taskLogs)
$taskResults = [Collections.Generic.List[object]]::new()
$taskCommands = [Collections.Generic.List[object]]::new()
$taskRunId = [DateTime]::UtcNow.ToString('yyyyMMddTHHmmssfff')
$taskStarted = [DateTime]::UtcNow.ToString('o')
$taskExpected = @($taskSelected | ForEach-Object {
  if ($_.kind -cin @('native','ffi-mutation')) { foreach ($consumer in $_.consumers) { $_.id + '/' + $consumer } }
  else { $_.id }
})
if ($taskExpected.Count -eq 0 -or @($taskExpected | Select-Object -Unique).Count -ne $taskExpected.Count) {
  throw 'nonempty exact expanded dispatch registry mismatch'
}
$taskSuccess = $false
$taskFailure = $null
$taskIdentitySeconds = $null
$taskToolchainProbes = @()
$taskPythonIdentity = $null
function Invoke-BinaryOwned([string]$Stage, [string]$Exe, [string[]]$Arguments, [int]$Deadline) {
  $started = [DateTime]::UtcNow.ToString('o')
  $result = Invoke-RMQOwnedBoundedProcess -FilePath $Exe -Arguments $Arguments `
    -WorkingDirectory $taskRoot -Stage $Stage -DeadlineSeconds $Deadline `
    -OutputLimitBytes 8388608 -TempRoot (Join-Path $taskScratch 'process')
  $result | Add-Member -NotePropertyName StartedUtc -NotePropertyValue $started
  $result | Add-Member -NotePropertyName CompletedUtc -NotePropertyValue ([DateTime]::UtcNow.ToString('o'))
  $result | Add-Member -NotePropertyName InvokedFilePath -NotePropertyValue $Exe
  $result | Add-Member -NotePropertyName InvokedArguments -NotePropertyValue @($Arguments)
  $taskCommands.Add($result)
  if ($result.TimedOut -or $result.OutputLimitExceeded) {
    $taskResults.Add(@{id=$Stage;pass=$false;incomplete=$true;process=$result})
    throw ('bounded binary process incomplete: ' + $Stage)
  }
  return $result
}
function Get-BinaryGitState([string]$Path) {
  $state = @(& git diff --binary -- $Path)
  if ($LASTEXITCODE -ne 0) { throw 'binary source Git state read failed' }
  return ($state -join "`n")
}
function Invoke-BinaryObservation($Entry,[string]$Consumer,[string]$ImagePath,[string]$Directory,[bool]$Mutant=$false) {
  $id = $Entry.id + '/' + $Consumer
  $arguments = @($Entry.arguments | ForEach-Object { if ($_ -ceq '{image}') { $ImagePath } else { [string]$_ } })
  $captureArgs = @($taskProducer,'capture','--executable',(Join-Path $Directory $Consumer),
    '--scratch',$taskScratch,'--deadline',[string]$Entry.deadlineSeconds,'--output-limit','4194304','--') + $arguments
  $owned = Invoke-BinaryOwned $id $taskPython $captureArgs ($Entry.deadlineSeconds + 30)
  # Preserve explicit child UTC strings instead of JSON's local DateTime conversion.
  $raw = ($owned.StandardOutput -join "`n") | ConvertFrom-Json -DateKind String
  if ($owned.ExitCode -ne 0 -or $owned.StandardError.Count -ne 0 -or
      $raw.schema -cne 'native1-raw-process-v1' -or $raw.timedOut -or $raw.outputLimitExceeded) {
    $taskResults.Add(@{id=$id;pass=$false;incomplete=$true;process=$owned;raw=$raw})
    throw ('raw binary capture incomplete: ' + $id)
  }
  $encoding = [Text.UTF8Encoding]::new($false,$true)
  $stdout = $encoding.GetString([Convert]::FromBase64String($raw.stdoutBase64))
  $stderr = $encoding.GetString([Convert]::FromBase64String($raw.stderrBase64))
  $normalMatches = $raw.exitCode -eq $Entry.expectedExit -and $stdout -ceq $Entry.expectedStdout -and $stderr -ceq $Entry.expectedStderr
  $pass = if ($Mutant) {
    -not $normalMatches -and $raw.exitCode -eq $Entry.mutantExpectedExit -and
      $stdout -ceq $Entry.mutantExpectedStdout -and $stderr -ceq $Entry.mutantExpectedStderr
  } else { $normalMatches }
  return @{id=$id;pass=$pass;process=$owned;raw=$raw;normalExpectationMatches=$normalMatches;
    expectedExit=$Entry.expectedExit;expectedStdout=$Entry.expectedStdout;expectedStderr=$Entry.expectedStderr}
}
try {
  $pythonProbe = Invoke-BinaryOwned 'python-producer-identity' $taskPython @('--version') 30
  if ($pythonProbe.ExitCode -ne 0) { throw 'binary producer Python identity failed' }
  $taskPythonIdentity = [ordered]@{path=[IO.Path]::GetFullPath($taskPython);
    version=($pythonProbe.StandardOutput -join "`n").Trim();sha256=(Get-FileHash -LiteralPath $taskPython).Hash;
    runtimeDlls=@(Get-ChildItem -LiteralPath (Split-Path $taskPython -Parent) -File -Filter 'python*.dll' |
      Sort-Object Name | ForEach-Object { @{path=$_.FullName;sha256=(Get-FileHash -LiteralPath $_.FullName).Hash} });
    process=$pythonProbe}
  if ($taskPythonIdentity.version -cnotmatch '^Python 3\.(1[0-9]|[2-9][0-9])\.[0-9]+') { throw 'unsupported binary producer Python version' }
  $identityWatch = [Diagnostics.Stopwatch]::StartNew()
  try {
    $actualIdentity = Assert-NativeToolchainIdentity $taskRoot $taskBuildManifest.toolchainIdentity
    $taskToolchainProbes = @($actualIdentity.commands) + @($actualIdentity.cppDependencies.probe)
    $actualIdentity = $null
    if ($taskToolchainProbes.Count -ne 6) { throw 'exact toolchain probe receipt roster mismatch' }
  } finally {
    $identityWatch.Stop()
    $taskIdentitySeconds = $identityWatch.Elapsed.TotalSeconds
  }
  foreach ($entry in $taskSelected) {
    Assert-BinaryBuildIdentity
    if ($entry.kind -ceq 'native') {
      if ($entry.operation -cne 'exact-cli-observation' -or
          (($entry.consumers -join ',') -cne 'packed-rmq-native.exe,packed-rmq-native-cpp.exe')) {
        throw 'binary native dispatch operation mismatch'
      }
      $imagePath = Join-Path $taskScratch ($entry.id + '.bin')
      $prepare = Invoke-BinaryOwned ($entry.id + '-prepare') $taskPython `
        @($taskProducer,'prepare','--registry',$taskRegistryPath,'--case',$entry.id,'--output',$imagePath) 180
      if ($prepare.ExitCode -ne 0 -or $prepare.StandardError.Count -ne 0) { throw ('binary fixture preparation failed: ' + $entry.id) }
      $image = ($prepare.StandardOutput -join "`n") | ConvertFrom-Json
      if ((Get-FileHash -LiteralPath $imagePath).Hash -cne $image.imageSha256 -or
          (Get-Item -LiteralPath $imagePath).Length -ne $image.imageBytes) { throw 'prepared binary image identity mismatch' }
      foreach ($consumer in $entry.consumers) {
        Assert-BinaryBuildIdentity
        $details = Invoke-BinaryObservation $entry $consumer $imagePath $taskBuild
        $details.image=$image; $details.prepare=$prepare
        $taskResults.Add($details)
        if (-not $details.pass) { throw ('exact binary observation mismatch: ' + $details.id) }
        Write-Output ('NATIVE1-BINARY PASS ' + $details.id)
      }
    } elseif ($entry.kind -ceq 'ffi-mutation') {
      if ($entry.operation -cne 'rebuild-shim-and-challenge' -or
          (($entry.consumers -join ',') -cne 'packed-rmq-native.exe,packed-rmq-native-cpp.exe')) { throw 'FFI mutation dispatch mismatch' }
      Assert-BinaryGeneratedCIdentity
      $path = Join-Path $taskRoot $entry.source
      $saved = [IO.File]::ReadAllBytes($path)
      $before = (Get-FileHash -LiteralPath $path).Hash
      $state = Get-BinaryGitState $entry.source
      $isolated = Join-Path $taskScratch ('ffi-' + [Guid]::NewGuid().ToString('N'))
      [void](New-Item -ItemType Directory -Path $isolated)
      $ffiResults = [Collections.Generic.List[object]]::new()
      try {
        $imagePath = Join-Path $isolated 'asymmetric.bin'
        $prepare = Invoke-BinaryOwned ($entry.id + '-prepare') $taskPython `
          @($taskProducer,'prepare','--registry',$taskRegistryPath,'--case',$entry.id,'--output',$imagePath) 180
        if ($prepare.ExitCode -ne 0 -or $prepare.StandardError.Count -ne 0) { throw 'FFI mutation fixture preparation failed' }
        $image = ($prepare.StandardOutput -join "`n") | ConvertFrom-Json
        if ((Get-FileHash -LiteralPath $imagePath).Hash -cne $image.imageSha256 -or
            (Get-Item -LiteralPath $imagePath).Length -ne $image.imageBytes) { throw 'FFI fixture image identity mismatch' }
        $baselineObservations = @{}
        foreach ($consumer in $entry.consumers) {
          $baseline = Invoke-BinaryObservation $entry $consumer $imagePath $taskBuild
          if (-not $baseline.pass) { throw ('unchanged asymmetric FFI consumer failed: ' + $baseline.id) }
          $baselineObservations[$consumer] = $baseline
        }
        $text = [Text.UTF8Encoding]::new($false,$true).GetString($saved)
        if ([regex]::Matches($text,[regex]::Escape($entry.anchor)).Count -ne 1) { throw 'FFI source anchor not unique' }
        [IO.File]::WriteAllText($path,$text.Replace($entry.anchor,$entry.replacement),[Text.UTF8Encoding]::new($false))
        $mutatedHash = (Get-FileHash -LiteralPath $path).Hash
        $compileArgs = @('-shared','-O1','-DPACKED_RMQ_BUILD') +
          @($taskBuildManifest.generatedC.path) + @($entry.source,'-o',(Join-Path $isolated 'packed_rmq.dll'))
        $compile = Invoke-BinaryOwned ($entry.id + '-rebuild') (Join-Path $taskLean 'bin/leanc.exe') $compileArgs $entry.compileDeadlineSeconds
        if ($compile.ExitCode -ne 0) { throw 'isolated FFI mutation compilation failed' }
        $mutatedDll = (Get-FileHash -LiteralPath (Join-Path $isolated 'packed_rmq.dll')).Hash
        foreach ($consumer in $entry.consumers) {
          Copy-Item -LiteralPath (Join-Path $taskBuild $consumer) -Destination (Join-Path $isolated $consumer)
          $pin = @($taskBuildManifest.artifacts | Where-Object path -CEQ $consumer)[0]
          if ((Get-FileHash -LiteralPath (Join-Path $isolated $consumer)).Hash -cne $pin.sha256) { throw 'isolated FFI consumer bytes changed' }
          $details = Invoke-BinaryObservation $entry $consumer $imagePath $isolated $true
          $details.sourceBeforeSha256=$before; $details.mutatedSourceSha256=$mutatedHash
          $details.mutatedDllSha256=$mutatedDll; $details.generatedC=$taskBuildManifest.generatedC
          $details.compile=$compile; $details.prepare=$prepare; $details.image=$image; $details.surface=$entry.surface
          $details.baselineObservation=$baselineObservations[$consumer]
          $details.mutantExpectedExit=$entry.mutantExpectedExit; $details.mutantExpectedStdout=$entry.mutantExpectedStdout
          $details.mutantExpectedStderr=$entry.mutantExpectedStderr
          $ffiResults.Add($details)
          if (-not $details.pass) { throw ('FFI mutation did not produce exact independent challenge failure: ' + $details.id) }
        }
      } finally {
        [IO.File]::WriteAllBytes($path,$saved)
        if ((Get-FileHash -LiteralPath $path).Hash -cne $before -or (Get-BinaryGitState $entry.source) -cne $state) { throw 'FFI source restoration mismatch' }
        Assert-BinaryBuildIdentity
        Assert-BinaryGeneratedCIdentity
        foreach ($details in $ffiResults) {
          $details.restoredSourceSha256=$before; $details.exactGitRestoration=$true
          $details.baselineArtifactsUnchanged=$true; $taskResults.Add($details)
        }
      }
      foreach ($details in $ffiResults) { Write-Output ('NATIVE1-BINARY PASS ' + $details.id) }
    } elseif ($entry.kind -ceq 'source-mutation' -or $entry.kind -ceq 'source-pin') {
      $path = Join-Path $taskRoot $entry.source
      $saved = [IO.File]::ReadAllBytes($path)
      $before = (Get-FileHash -LiteralPath $path).Hash
      $state = Get-BinaryGitState $entry.source
      $details = $null
      try {
        $text = [Text.UTF8Encoding]::new($false,$true).GetString($saved)
        if ($entry.kind -ceq 'source-pin') {
          if ($entry.operation -cne 'source-identity-rejection' -or $entry.expectedExit -cne 'rejection' -or
              $entry.surface -cne 'Assert-BinaryBuildIdentity') { throw 'binary source-pin operation mismatch' }
          [IO.File]::WriteAllText($path, $text + $entry.append, [Text.UTF8Encoding]::new($false))
          $rejected = $false
          try { Assert-BinaryBuildIdentity } catch {
            if ($_.Exception.Message -cne $entry.expectedDiagnostic) { throw }
            $rejected = $true
          }
          if (-not $rejected) { throw 'binary stale source accepted' }
          $details = @{surface=$entry.surface;expectedDiagnostic=$entry.expectedDiagnostic;beforeSha256=$before}
        } else {
          if ($entry.operation -cne 'lean-type-rejection' -or $entry.expectedExit -cne 'nonzero') {
            throw 'binary source mutation operation mismatch'
          }
          if ([regex]::Matches($text,[regex]::Escape($entry.anchor)).Count -ne 1) { throw 'binary source anchor not unique' }
          $lines = @([regex]::Split($text,'\r?\n'))
          $line = [Array]::IndexOf($lines,[string]$entry.proofLine) + 1
          if ($line -le 0 -or @($lines | Where-Object { $_ -ceq $entry.proofLine }).Count -ne 1) { throw 'binary exact proof consumer line not unique' }
          [IO.File]::WriteAllText($path,$text.Replace($entry.anchor,$entry.replacement),[Text.UTF8Encoding]::new($false))
          $result = Invoke-BinaryOwned $entry.id (Join-Path $taskLean 'bin/lean.exe') `
            @('-j','1','-o',(Join-Path $taskScratch ($entry.id + '.olean')),$entry.source) $entry.deadlineSeconds
          $pattern = '^' + [regex]::Escape($entry.source) + ':' + $line + ':\d+: error: (?i:' + [regex]::Escape($entry.expectedDiagnostic) + ')'
          $matched = @($result.Output | Where-Object { $_ -match $pattern })
          if ($result.ExitCode -eq 0 -or $matched.Count -ne 1) {
            $taskResults.Add(@{id=$entry.id;pass=$false;process=$result;surface=$entry.surface;expectedLine=$line})
            throw ('binary mutation missed exact source consumer: ' + $entry.id)
          }
          $details = @{process=$result;surface=$entry.surface;expectedLine=$line;matchedDiagnostics=$matched;beforeSha256=$before}
        }
      } finally {
        [IO.File]::WriteAllBytes($path,$saved)
        if ((Get-FileHash -LiteralPath $path).Hash -cne $before -or (Get-BinaryGitState $entry.source) -cne $state) {
          throw 'binary source restoration mismatch'
        }
      }
      $details.restoredSha256 = (Get-FileHash -LiteralPath $path).Hash
      $details.exactGitRestoration = $true
      Assert-BinaryBuildIdentity
      $taskResults.Add(@{id=$entry.id;pass=$true;details=$details})
      Write-Output ('NATIVE1-BINARY PASS ' + $entry.id)
    } else { throw 'unknown binary case variant' }
  }
  if (($taskResults.id -join ',') -cne ($taskExpected -join ',') -or
      @($taskResults | Where-Object { -not $_.pass }).Count -ne 0) { throw 'binary executed/expected inventory mismatch' }
  $taskSuccess = $true
} catch { $taskFailure = $_.Exception.Message; throw }
finally {
  $receipt = [ordered]@{schema='native1-binary-replay-v1';startedUtc=$taskStarted;completedUtc=[DateTime]::UtcNow.ToString('o');
    pass=$taskSuccess;failure=$taskFailure;registrySha256=$taskExactRegistrySha256;
    runnerSha256=(Get-FileHash -LiteralPath $PSCommandPath).Hash;
    buildManifestSha256=(Get-FileHash -LiteralPath (Join-Path $taskBuild 'build-manifest.json')).Hash;
    producerRuntime=$taskPythonIdentity;
    toolchainProbes=$taskToolchainProbes;
    toolchainIdentitySeconds=$taskIdentitySeconds;selectorBound=$PSBoundParameters.ContainsKey('Case');selector=$Case;
    expected=$taskExpected;executed=@($taskResults.id);results=@($taskResults.ToArray());commands=@($taskCommands.ToArray())}
  $receipt | ConvertTo-Json -Depth 30 | Set-Content -LiteralPath (Join-Path $taskLogs ('binary-replay-' + $taskRunId + '.json')) -Encoding utf8
}
