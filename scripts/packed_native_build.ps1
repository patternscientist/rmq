param([string]$LeanRoot = 'C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0')
$ErrorActionPreference = 'Stop'
$taskRoot = Split-Path $PSScriptRoot -Parent
. (Join-Path $PSScriptRoot 'owned_process_tree.ps1')
$taskBuild = Join-Path $taskRoot '.lake/native1/build'
$taskLogs = Join-Path $taskRoot 'docs/internal/extensions/native1/commands'
$taskLib = Join-Path $taskRoot '.lake/build/lib/lean'
$taskIR = Join-Path $taskRoot '.lake/build/ir'
[void](New-Item -ItemType Directory -Force -Path $taskBuild, $taskLogs, $taskLib, $taskIR)
$env:LEAN_PATH = $taskLib
$env:PATH = (Join-Path $LeanRoot 'bin') + ';' + $env:PATH
$taskResults = [Collections.Generic.List[object]]::new()
$taskSources = @(
  'RMQ/Core/WordRAM/Packed/Primitive.lean',
  'RMQ/Core/WordRAM/Packed/Calculus.lean',
  'RMQ/Core/WordRAM/Packed/Structured.lean',
  'RMQ/Core/WordRAM/Packed/Compiler.lean',
  'RMQ/Core/WordRAM/Packed/Frame.lean',
  'RMQ/Core/WordRAM/Packed/Scratch.lean',
  'RMQ/Core/WordRAM/Native/Finite.lean',
  'RMQ/Core/WordRAM/Native/Thin.lean',
  'RMQ/Core/WordRAM/Native/Route.lean'
)
$taskPinPaths = $taskSources + @(
  'native/packed-rmq/route_shim.c', 'native/packed-rmq/include/packed_rmq_route.h',
  'native/packed-rmq/src/lib.rs', 'native/packed-rmq/src/main.rs',
  'native/packed-rmq/Cargo.toml', 'scripts/packed_native_build.ps1'
)
function Invoke-NativeStage([string]$Stage, [string]$Exe, [string[]]$StageArgs, [int]$Deadline = 300) {
  $r = Invoke-RMQOwnedBoundedProcess -FilePath $Exe -Arguments $StageArgs `
    -WorkingDirectory $taskRoot -Stage $Stage -DeadlineSeconds $Deadline `
    -OutputLimitBytes 8388608 -TempRoot (Join-Path $taskBuild 'process')
  $taskResults.Add([ordered]@{ command = @{file=$Exe; arguments=$StageArgs}; result=$r })
  $r.Output | Write-Output
  Write-Output ("NATIVE1-BUILD " + $Stage + " exit=" + $r.ExitCode + " seconds=" + $r.DurationSeconds)
  if ($r.TimedOut -or $r.OutputLimitExceeded -or $r.ExitCode -ne 0) { throw ("stage failed: " + $Stage) }
}
$taskRunId = [DateTime]::UtcNow.ToString('yyyyMMddTHHmmssfff')
$taskInitialPins = @($taskPinPaths | ForEach-Object {
  @{path=$_; sha256=(Get-FileHash (Join-Path $taskRoot $_)).Hash}
})
$taskSuccess = $false
try {
  Invoke-NativeStage 'lean-version' (Join-Path $LeanRoot 'bin/lean.exe') @('--version') 60
  $taskCSources = @()
  $taskPrefix = [Collections.Generic.List[string]]::new()
  foreach ($source in $taskSources) {
    $relative = $source.Substring(0, $source.Length - '.lean'.Length)
    $o = Join-Path $taskLib ($relative + '.olean')
    $c = Join-Path $taskIR ($relative + '.c')
    [void](New-Item -ItemType Directory -Force -Path (Split-Path $o), (Split-Path $c))
    $taskPrefix.Add($source + ':' + (Get-FileHash (Join-Path $taskRoot $source)).Hash)
    $signature = $taskPrefix -join '|'
    $cachePath = $c + '.native1-cache.json'
    $reuse = $false
    if ((Test-Path $cachePath) -and (Test-Path $o) -and (Test-Path $c)) {
      $cache = Get-Content $cachePath -Raw | ConvertFrom-Json
      $reuse = $cache.schema -ceq 'native1-module-v1' -and $cache.signature -ceq $signature -and
        $cache.olean -ceq (Get-FileHash $o).Hash -and $cache.c -ceq (Get-FileHash $c).Hash
    }
    if ($reuse) {
      Write-Output ('NATIVE1-BUILD verified local artifact reuse ' + $source)
      $taskResults.Add(@{reuse=$source; signature=$signature; olean=$cache.olean; c=$cache.c})
    } else {
      Invoke-NativeStage ('lean-' + [IO.Path]::GetFileNameWithoutExtension($source)) `
        (Join-Path $LeanRoot 'bin/lean.exe') @('-j','1','-o',$o,'-c',$c,$source)
      $cache = @{schema='native1-module-v1';signature=$signature;
        olean=(Get-FileHash $o).Hash;c=(Get-FileHash $c).Hash}
      [IO.File]::WriteAllText($cachePath, ($cache | ConvertTo-Json), [Text.UTF8Encoding]::new($false))
    }
    $taskCSources += $c
  }
  $routeC = [IO.File]::ReadAllText((Join-Path $taskIR 'RMQ/Core/WordRAM/Native/Route.c'))
  if ($routeC -notmatch 'lean_object\* rmq_native_route\(lean_object\*, lean_object\*, uint8_t\)' -or
      $routeC -notmatch 'initialize_RMQ_Core_WordRAM_Native_Route\(uint8_t builtin, lean_object\* w\)') {
    throw 'emitted ABI prototype/initializer differs from frozen shim boundary'
  }
  Invoke-NativeStage 'link-dll' (Join-Path $LeanRoot 'bin/leanc.exe') `
    (@('-shared','-O1','-DPACKED_ROUTE_BUILD') + $taskCSources + @('native/packed-rmq/route_shim.c','-o',
      (Join-Path $taskBuild 'packed_route.dll')))
  Invoke-NativeStage 'cargo-lock' (Get-Command cargo -CommandType Application | Select-Object -First 1 -ExpandProperty Source) `
    @('generate-lockfile','--offline','--manifest-path','native/packed-rmq/Cargo.toml') 60
  Invoke-NativeStage 'rust-version' (Get-Command rustc -CommandType Application | Select-Object -First 1 -ExpandProperty Source) @('-vV') 60
  Invoke-NativeStage 'cargo-build' (Get-Command cargo -CommandType Application | Select-Object -First 1 -ExpandProperty Source) `
    @('build','--locked','--offline','--release','--manifest-path','native/packed-rmq/Cargo.toml',
      '--target-dir',(Join-Path $taskBuild 'rust-target'))
  Copy-Item -LiteralPath (Join-Path $taskBuild 'rust-target/release/packed-rmq-route.exe') `
    -Destination (Join-Path $taskBuild 'packed-rmq-route.exe')
  foreach ($pin in $taskInitialPins) {
    if ((Get-FileHash (Join-Path $taskRoot $pin.path)).Hash -cne $pin.sha256) {
      throw ('source changed during build: ' + $pin.path)
    }
  }
  $taskPins = $taskInitialPins
  $taskArtifactPins = @('packed_route.dll','packed-rmq-route.exe') | ForEach-Object {
    @{path=$_; sha256=(Get-FileHash (Join-Path $taskBuild $_)).Hash}
  }
  $manifest = @{schema='native1-build-v1'; leanRoot=$LeanRoot; sources=$taskPins; artifacts=@($taskArtifactPins)}
  [IO.File]::WriteAllText((Join-Path $taskBuild 'build-manifest.json'),
    ($manifest | ConvertTo-Json -Depth 8), [Text.UTF8Encoding]::new($false))
  $taskSuccess = $true
} finally {
  $report = [ordered]@{
    schema='native1-build-commands-v1'; run=$taskRunId; success=$taskSuccess
    platform=[Environment]::OSVersion.VersionString
    base='0e6a00f654abc64f8b68988fa9675b9a839dca2f'
    initialSourceHashes=$taskInitialPins
    sourceHashes=@($taskPinPaths | ForEach-Object {
      @{path=$_; sha256=(Get-FileHash (Join-Path $taskRoot $_)).Hash}
    })
    stages=@($taskResults.ToArray())
  }
  [IO.File]::WriteAllText((Join-Path $taskLogs ('build-' + $taskRunId + '.json')),
    ($report | ConvertTo-Json -Depth 14), [Text.UTF8Encoding]::new($false))
}
