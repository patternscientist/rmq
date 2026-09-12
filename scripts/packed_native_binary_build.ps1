param(
  [string]$LeanRoot = 'C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0',
  [string]$RustRoot = 'C:/Users/poin/.rustup/toolchains/stable-x86_64-pc-windows-msvc',
  [string]$CppCompiler = 'C:/Program Files/Microsoft Visual Studio/2022/Community/VC/Tools/Llvm/x64/bin/clang.exe',
  [string]$ImportLibrarian = 'C:/Program Files/Microsoft Visual Studio/2022/Community/VC/Tools/MSVC/14.44.35207/bin/Hostx64/x64/lib.exe',
  [string]$RustLinker = 'C:/Program Files/Microsoft Visual Studio/2022/Community/VC/Tools/MSVC/14.44.35207/bin/Hostx64/x64/link.exe'
)
$ErrorActionPreference = 'Stop'
$taskRoot = Split-Path $PSScriptRoot -Parent
. (Join-Path $PSScriptRoot 'owned_process_tree.ps1')
. (Join-Path $PSScriptRoot 'packed_native_identity.ps1')
$taskBuild = Join-Path $taskRoot '.lake/native1/binary-build'
$taskLogs = Join-Path $taskRoot 'docs/internal/extensions/native1/commands'
$taskLib = Join-Path $taskRoot '.lake/build/lib/lean'
$taskIR = Join-Path $taskRoot '.lake/build/ir'
[void](New-Item -ItemType Directory -Force -Path $taskBuild, $taskLogs, $taskLib, $taskIR)
$env:LEAN_PATH = $taskLib
$env:PATH = (Join-Path $LeanRoot 'bin') + ';' + $env:PATH
if ($env:RUSTC_WRAPPER -or $env:RUSTC_WORKSPACE_WRAPPER) { throw 'unrecorded Rust compiler wrapper' }
$env:RUSTC = Join-Path $RustRoot 'bin/rustc.exe'
$env:CARGO_HOME = Join-Path $taskBuild 'cargo-home'
$env:CARGO_TARGET_X86_64_PC_WINDOWS_MSVC_LINKER = $RustLinker
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
  'RMQ/Core/WordRAM/Native/Route.lean',
  'RMQ/Core/WordRAM/Native/Limbs.lean',
  'RMQ/Core/WordRAM/Native/Machine.lean',
  'RMQ/Core/WordRAM/Native/Observations.lean',
  'RMQ/Core/WordRAM/Native/Binary/Codec.lean',
  'RMQ/Core/WordRAM/Native/Binary.lean',
  'RMQ/Core/WordRAM/Native/Binary/Bounds.lean',
  'RMQ/Core/WordRAM/Native/Binary/Cursor/Core.lean',
  'RMQ/Core/WordRAM/Native/Binary/Cursor.lean',
  'RMQ/Core/WordRAM/Native/Runtime.lean',
  'RMQ/Core/WordRAM/Native/Entry.lean'
)
$taskPinPaths = $taskSources + @(
  'native/packed-rmq/native_shim.c', 'native/packed-rmq/include/packed_rmq.h',
  'native/packed-rmq/src/lib.rs', 'native/packed-rmq/src/native.rs',
  'native/packed-rmq/src/native_main.rs',
  'native/packed-rmq/Cargo.toml', 'scripts/packed_native_binary_build.ps1',
  'native/packed-rmq/Cargo.lock', 'native/packed-rmq/examples/native.cpp',
  'native/packed-rmq/packed_rmq.def', 'scripts/packed_native_identity.ps1',
  'scripts/owned_process_tree.ps1'
)
function Invoke-NativeStage([string]$Stage, [string]$Exe, [string[]]$StageArgs, [int]$Deadline = 300) {
  $startedUtc = [DateTime]::UtcNow.ToString('o')
  $r = Invoke-RMQOwnedBoundedProcess -FilePath $Exe -Arguments $StageArgs `
    -WorkingDirectory $taskRoot -Stage $Stage -DeadlineSeconds $Deadline `
    -OutputLimitBytes 8388608 -TempRoot (Join-Path $taskBuild 'process')
  $taskResults.Add([ordered]@{ command = @{file=$Exe; arguments=$StageArgs};
    startedUtc=$startedUtc; completedUtc=[DateTime]::UtcNow.ToString('o'); result=$r })
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
  $taskToolchain = Get-NativeToolchainIdentity $taskRoot $LeanRoot $RustRoot $CppCompiler $ImportLibrarian $RustLinker
  Write-Output ('NATIVE1-BUILD toolchain identity ' + $taskToolchain.digest)
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
      $reuse = Test-NativeModuleCache $cache $signature $taskToolchain.digest $o $c
    }
    if ($reuse) {
      Write-Output ('NATIVE1-BUILD verified local artifact reuse ' + $source)
      $taskResults.Add(@{reuse=$source; signature=$signature; olean=$cache.olean; c=$cache.c})
    } else {
      Invoke-NativeStage ('lean-' + [IO.Path]::GetFileNameWithoutExtension($source)) `
        (Join-Path $LeanRoot 'bin/lean.exe') @('-j','1','-o',$o,'-c',$c,$source)
      $cache = @{schema='native1-module-v2';signature=$signature;toolchainDigest=$taskToolchain.digest;
        olean=(Get-FileHash $o).Hash;c=(Get-FileHash $c).Hash}
      [IO.File]::WriteAllText($cachePath, ($cache | ConvertTo-Json), [Text.UTF8Encoding]::new($false))
    }
    $taskCSources += $c
  }
  $entryC = [IO.File]::ReadAllText((Join-Path $taskIR 'RMQ/Core/WordRAM/Native/Entry.c'))
  if ($entryC -notmatch 'lean_object\* rmq_native_load\(lean_object\*\)' -or
      $entryC -notmatch 'lean_object\* rmq_native_query\(lean_object\*, lean_object\*, lean_object\*, lean_object\*, uint8_t\)' -or
      $entryC -notmatch 'size_t rmq_native_word_bytes\(lean_object\*\)' -or
      $entryC -notmatch 'initialize_RMQ_Core_WordRAM_Native_Entry\(uint8_t builtin, lean_object\* w\)') {
    throw 'emitted ABI prototype/initializer differs from frozen shim boundary'
  }
  $taskGeneratedPins = @($taskSources | ForEach-Object {
    $path = '.lake/build/ir/' + $_.Substring(0, $_.Length - 5) + '.c'
    @{path=$path;sha256=(Get-FileHash -LiteralPath (Join-Path $taskRoot $path)).Hash}
  })
  Invoke-NativeStage 'link-dll' (Join-Path $LeanRoot 'bin/leanc.exe') `
    (@('-shared','-O1','-DPACKED_RMQ_BUILD') + $taskCSources + @('native/packed-rmq/native_shim.c','-o',
      (Join-Path $taskBuild 'packed_rmq.dll')))
  Invoke-NativeStage 'cargo-build' (Join-Path $RustRoot 'bin/cargo.exe') `
    @('build','--locked','--offline','--release','--bin','packed-rmq-native','--manifest-path','native/packed-rmq/Cargo.toml',
      '--target-dir',(Join-Path $taskBuild 'rust-target'))
  Copy-Item -LiteralPath (Join-Path $taskBuild 'rust-target/release/packed-rmq-native.exe') `
    -Destination (Join-Path $taskBuild 'packed-rmq-native.exe')
  Invoke-NativeStage 'cpp-import-library' $ImportLibrarian `
    @('/nologo','/def:native/packed-rmq/packed_rmq.def',('/out:' + (Join-Path $taskBuild 'packed_rmq.lib')),'/machine:X64') 60
  Invoke-NativeStage 'cpp-build' $CppCompiler `
    @('-std=c++17','native/packed-rmq/examples/native.cpp',(Join-Path $taskBuild 'packed_rmq.lib'),
      '-o',(Join-Path $taskBuild 'packed-rmq-native-cpp.exe')) 120
  foreach ($pin in $taskInitialPins) {
    if ((Get-FileHash (Join-Path $taskRoot $pin.path)).Hash -cne $pin.sha256) {
      throw ('source changed during build: ' + $pin.path)
    }
  }
  foreach ($pin in $taskGeneratedPins) {
    if ((Get-FileHash -LiteralPath (Join-Path $taskRoot $pin.path)).Hash -cne $pin.sha256) {
      throw ('generated C changed during build: ' + $pin.path)
    }
  }
  $taskPins = $taskInitialPins
  $taskFinalToolchain = Assert-NativeToolchainIdentity $taskRoot $taskToolchain
  $taskArtifactPins = @('packed_rmq.dll','packed-rmq-native.exe','packed-rmq-native-cpp.exe') | ForEach-Object {
    @{path=$_; sha256=(Get-FileHash (Join-Path $taskBuild $_)).Hash}
  }
  $manifest = @{schema='native1-binary-build-v1'; leanRoot=$LeanRoot; sources=$taskPins;
    toolchainIdentity=$taskFinalToolchain; artifacts=@($taskArtifactPins); generatedC=$taskGeneratedPins;
    cppImportLibrarySHA256=(Get-FileHash -LiteralPath (Join-Path $taskBuild 'packed_rmq.lib')).Hash}
  [IO.File]::WriteAllText((Join-Path $taskBuild 'build-manifest.json'),
    ($manifest | ConvertTo-Json -Depth 14), [Text.UTF8Encoding]::new($false))
  $taskSuccess = $true
} finally {
  $report = [ordered]@{
    schema='native1-binary-build-commands-v1'; run=$taskRunId; success=$taskSuccess
    platform=[Environment]::OSVersion.VersionString
    base='0e6a00f654abc64f8b68988fa9675b9a839dca2f'
    initialSourceHashes=$taskInitialPins
    generatedC=$taskGeneratedPins
    toolchainIdentity=$taskToolchain
    sourceHashes=@($taskPinPaths | ForEach-Object {
      @{path=$_; sha256=(Get-FileHash (Join-Path $taskRoot $_)).Hash}
    })
    stages=@($taskResults.ToArray())
  }
  [IO.File]::WriteAllText((Join-Path $taskLogs ('binary-build-' + $taskRunId + '.json')),
    ($report | ConvertTo-Json -Depth 14), [Text.UTF8Encoding]::new($false))
}
