[CmdletBinding()]
param(
  [ValidateRange(1,7200)][int]$DeadlineSeconds=3600,
  [string]$DeadlineRationale='Required final default build: current focused four-root Lean stage took 56.835 seconds; inherited default imports may have cold artifacts, so reserve the planned 3600-second ceiling.',
  [string]$LeanRoot='C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0'
)
$ErrorActionPreference='Stop'
if([string]::IsNullOrWhiteSpace($DeadlineRationale)){throw 'DEFAULT-BUILD: deadline rationale required'}
$root=[IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../../../..'))
. (Join-Path $root 'scripts/lifecycle_native_identity.ps1')
. (Join-Path $root 'scripts/packed_native_identity.ps1')
$utf8=[Text.UTF8Encoding]::new($false,$true)
$run=Join-Path $root ('.lake/lifecycle-native1/default-build/'+[DateTime]::UtcNow.ToString('yyyyMMddTHHmmssfff'))
[void][IO.Directory]::CreateDirectory($run)
$pins=[Collections.Generic.List[object]]::new()
$mutex=[Threading.Mutex]::new($false,'Local\RMQLifecycleImplementationHeavy20260920')
$locked=$false;$savedPath=$env:PATH
$report=[ordered]@{schema='lifecycle-native1-default-build-v1';success=$false;
  startedUtc=[DateTime]::UtcNow.ToString('o');command=@('lake','build');
  deadlineSeconds=$DeadlineSeconds;deadlineRationale=$DeadlineRationale;
  sourcePins=@();toolPins=@();capture=$null;failure=$null;integrity=$null;cleanup=$null}
function Pin-DefaultBuild([string]$Path){$p=Get-LN1Pin $Path;$pins.Add($p);return $p}
try{
  $locked=$mutex.WaitOne(0);if(-not $locked){throw 'DEFAULT-BUILD: shared heavy slot busy; no child launched'}
  $report.contract=Assert-LN1FrozenContract $root
  $report.host=Pin-DefaultBuild (Get-Process -Id $PID).Path
  # Pin every original Lean source plus the complete new lifecycle/consumer
  # subtree. The separate scope check rejects unassigned new source locations.
  $basePath=Join-Path $PSScriptRoot 'BASE_IDENTITY.json'
  $baseBytes=[IO.File]::ReadAllBytes($basePath)
  if((Get-LN1BytesHash $baseBytes) -cne 'cfeb23f578e9ec014f2302220de4c08960f2c96892f8be5c60608ff8c4cb6997'){
    throw 'DEFAULT-BUILD: base source inventory changed'
  }
  $baseline=$utf8.GetString($baseBytes)|ConvertFrom-Json
  $paths=[Collections.Generic.HashSet[string]]::new([StringComparer]::OrdinalIgnoreCase)
  foreach($f in $baseline.files){if($f.path.EndsWith('.lean',[StringComparison]::Ordinal)){[void]$paths.Add((Join-Path $root $f.path))}}
  foreach($f in Get-ChildItem -LiteralPath (Join-Path $root 'RMQ/Core/WordRAM/Native/Lifecycle') -Recurse -File -Filter '*.lean'){
    [void]$paths.Add($f.FullName)
  }
  foreach($p in @('RMQ/Core/WordRAM/Native/Lifecycle.lean','RMQ/Validation/LifecycleNativeContract.lean',
      'RMQ/Validation/PackedLifecycleNative.lean')){
    $path=Join-Path $root $p;if([IO.File]::Exists($path)){[void]$paths.Add($path)}
  }
  foreach($p in @('lean-toolchain','lakefile.toml','lake-manifest.json',
      'scripts/lifecycle_native_identity.ps1','scripts/packed_native_identity.ps1',
      'scripts/owned_process_tree.ps1','scripts/packed_native_lifecycle_stream_check.ps1',
      'scripts/packed_native_lifecycle_storage_replay.ps1','scripts/packed_native_lifecycle_integrity_check.ps1')){
    [void]$paths.Add((Join-Path $root $p))
  }
  [void]$paths.Add($PSCommandPath);[void]$paths.Add($basePath)
  $report.sourcePins=@($paths|Sort-Object|ForEach-Object{Pin-DefaultBuild $_})
  $report.toolPins=@(Get-NativeFileInventory $LeanRoot @('bin','include','lib')|ForEach-Object{
    Pin-DefaultBuild (Join-Path $LeanRoot $_.path)
  })
  # Exact raw version bytes were independently observed at version-raw/
  # 20260927T053140196. Keep that LF and reject BOM/NUL/extra diagnostics.
  $report.tool=Invoke-LNStreamCapture $root (Join-Path $LeanRoot 'bin/lean.exe') @('--version') $root (Join-Path $run 'lean-version') 60 'final-default-lean-identity'
  foreach($p in $report.tool.raw){[void](Pin-DefaultBuild $p.path)}
  $expectedVersion="Lean (version 4.22.0, x86_64-w64-windows-gnu, commit ba2cbbf09d4978f416e0ebd1fceeebc2c4138c05, Release)`n"
  Assert-LNOuterCapture $report.tool $expectedVersion '' 0 'final-default-lean-identity'
  Assert-NativeLeanPin ([IO.File]::ReadAllText((Join-Path $root 'lean-toolchain')).Trim()) $expectedVersion
  [IO.File]::WriteAllText((Join-Path $run 'PLAN.json'),($report|ConvertTo-Json -Depth 20),$utf8)
  $env:PATH=[IO.Path]::GetFullPath((Join-Path $LeanRoot 'bin'))+';'+$savedPath
  $report.capture=Invoke-LNStreamCapture $root (Join-Path $LeanRoot 'bin/lake.exe') @('build') $root (Join-Path $run 'build') $DeadlineSeconds 'default-lake-build'
  foreach($p in $report.capture.raw){[void](Pin-DefaultBuild $p.path)}
  # A default build has a variable progress/warning language, not an expected
  # rejection diagnostic. Retain both complete raw streams and require exit0.
  $stdout=Read-LNExactStream $report.capture.spec.stdout
  $stderr=Read-LNExactStream $report.capture.spec.stderr
  Assert-LNOuterCapture $report.capture $stdout $stderr 0 'default-lake-build'
  $report.success=$true
}catch{$report.failure=$_.Exception.Message}
finally{
  $errors=[Collections.Generic.List[string]]::new()
  foreach($pin in $pins){try{
    $now=Get-LN1Pin $pin.path
    if($now.bytes -ne $pin.bytes -or $now.sha256 -cne $pin.sha256){throw ('changed pin '+$pin.path)}
  }catch{$errors.Add($_.Exception.Message)}}
  $report.integrity=@{success=($errors.Count -eq 0);checked=$pins.Count;errors=@($errors.ToArray())}
  if($errors.Count){$report.success=$false}
  $cleanupErrors=[Collections.Generic.List[string]]::new();$released=$false
  try{$env:PATH=$savedPath}catch{$cleanupErrors.Add($_.Exception.Message)}
  try{if($locked){$mutex.ReleaseMutex();$released=$true}}catch{$cleanupErrors.Add($_.Exception.Message)}
  try{$mutex.Dispose()}catch{$cleanupErrors.Add($_.Exception.Message)}
  $report.cleanup=@{success=($cleanupErrors.Count -eq 0);mutexReleased=$released;errors=@($cleanupErrors.ToArray())}
  if($cleanupErrors.Count){$report.success=$false}
  $report.completedUtc=[DateTime]::UtcNow.ToString('o')
  [IO.File]::WriteAllText((Join-Path $run 'RESULT.json'),($report|ConvertTo-Json -Depth 30),$utf8)
}
Write-Output ('DEFAULT-BUILD evidence='+$run)
if(-not $report.success){Write-Output ('DEFAULT-BUILD FAIL '+$report.failure);exit 1}
Write-Output 'DEFAULT-BUILD PASS'
