param()
$ErrorActionPreference = 'Stop'
$taskRoot = Split-Path $PSScriptRoot -Parent
. (Join-Path $PSScriptRoot 'owned_process_tree.ps1')
. (Join-Path $PSScriptRoot 'packed_native_identity.ps1')
$taskScratch = Join-Path $taskRoot '.lake/native1/identity-controls'
[void](New-Item -ItemType Directory -Force -Path $taskScratch)
$taskExpected = @('pinned-actual-lean','changed-repository-pin','changed-compiler-version',
  'same-toolchain-cache','changed-toolchain-cache','old-cache-schema','changed-source-prefix',
  'missing-olean','changed-generated-c','restored-cache')
$taskResults = [Collections.Generic.List[object]]::new()
$taskLean = 'C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0'
$taskActual = Get-NativeCommandIdentity $taskRoot (Join-Path $taskLean 'bin/lean.exe') @('--version') 'identity-control-version'
$taskPin = [IO.File]::ReadAllText((Join-Path $taskRoot 'lean-toolchain')).Trim()
function Add-IdentityControl([string]$Id, [bool]$Pass, [string]$Evidence) {
  $taskResults.Add([ordered]@{id=$Id;pass=$Pass;evidence=$Evidence})
  if (-not $Pass) { throw ('identity control failed: ' + $Id) }
}
$taskOlean = Join-Path $taskRoot '.lake/build/lib/lean/RMQ/Core/WordRAM/Native/Route.olean'
$taskC = Join-Path $taskRoot '.lake/build/ir/RMQ/Core/WordRAM/Native/Route.c'
$taskCopyC = Join-Path $taskScratch 'Route.c'
Copy-Item -LiteralPath $taskC -Destination $taskCopyC
$taskBefore = [IO.File]::ReadAllBytes($taskCopyC)
$taskIdentity = Get-NativeDigest @($taskPin,$taskActual.text,(Get-FileHash -LiteralPath (Join-Path $taskLean 'bin/lean.exe')).Hash)
$taskCache = @{schema='native1-module-v2';toolchainDigest=$taskIdentity;signature='actual-source-prefix';
  olean=(Get-FileHash -LiteralPath $taskOlean).Hash;c=(Get-FileHash -LiteralPath $taskCopyC).Hash}
$taskSuccess = $false
try {
  Assert-NativeLeanPin $taskPin $taskActual.text
  Add-IdentityControl 'pinned-actual-lean' $true $taskActual.text
  $rejected = $false
  try { Assert-NativeLeanPin 'leanprover/lean4:v4.23.0' $taskActual.text }
  catch { $rejected = $_.Exception.Message -ceq 'native Lean compiler does not match the repository toolchain pin' }
  Add-IdentityControl 'changed-repository-pin' $rejected 'real production pin predicate rejected changed pin'
  $rejected = $false
  try { Assert-NativeLeanPin $taskPin ($taskActual.text.Replace('version 4.22.0','version 4.23.0')) }
  catch { $rejected = $_.Exception.Message -ceq 'native Lean compiler does not match the repository toolchain pin' }
  Add-IdentityControl 'changed-compiler-version' $rejected 'real production pin predicate rejected changed version banner; no alternate compiler executed'
  Add-IdentityControl 'same-toolchain-cache' (Test-NativeModuleCache $taskCache 'actual-source-prefix' $taskIdentity $taskOlean $taskCopyC) 'actual olean/C bytes, same identity: reuse'
  Add-IdentityControl 'changed-toolchain-cache' (-not (Test-NativeModuleCache $taskCache 'actual-source-prefix' ($taskIdentity + 'changed') $taskOlean $taskCopyC)) 'same source/artifacts, changed identity: rebuild required'
  $old = $taskCache.Clone(); $old.schema = 'native1-module-v1'
  Add-IdentityControl 'old-cache-schema' (-not (Test-NativeModuleCache $old 'actual-source-prefix' $taskIdentity $taskOlean $taskCopyC)) 'unqualified historical cache cannot be reused'
  Add-IdentityControl 'changed-source-prefix' (-not (Test-NativeModuleCache $taskCache 'changed-source-prefix' $taskIdentity $taskOlean $taskCopyC)) 'source-prefix mismatch requires rebuild'
  Add-IdentityControl 'missing-olean' (-not (Test-NativeModuleCache $taskCache 'actual-source-prefix' $taskIdentity (Join-Path $taskScratch 'absent.olean') $taskCopyC)) 'absent artifact cannot be reused'
  [IO.File]::AppendAllText($taskCopyC, "`n/* identity negative control */`n")
  Add-IdentityControl 'changed-generated-c' (-not (Test-NativeModuleCache $taskCache 'actual-source-prefix' $taskIdentity $taskOlean $taskCopyC)) 'changed actual generated C copy rejected'
  [IO.File]::WriteAllBytes($taskCopyC,$taskBefore)
  Add-IdentityControl 'restored-cache' (Test-NativeModuleCache $taskCache 'actual-source-prefix' $taskIdentity $taskOlean $taskCopyC) 'exact restored generated C accepted'
  if (($taskResults.id -join ',') -cne ($taskExpected -join ',')) { throw 'identity control registry mismatch' }
  $taskSuccess = $true
} finally {
  [IO.File]::WriteAllBytes($taskCopyC,$taskBefore)
  $restored = (Get-FileHash -LiteralPath $taskCopyC).Hash -ceq $taskCache.c
  $report = [ordered]@{schema='native1-identity-controls-v1';success=($taskSuccess -and $restored);
    sourceHead=((git -C $taskRoot rev-parse HEAD) -join '').Trim(); platform=[Environment]::OSVersion.VersionString;
    expectedCases=$taskExpected;expectedCount=$taskExpected.Count;executedCount=$taskResults.Count;
    results=@($taskResults.ToArray());restored=$restored;compilerProbe=$taskActual;
    limits='Production predicates are exercised on actual cached bytes; no alternate compiler or binary from it was executed.'}
  $path = Join-Path $taskRoot ('docs/internal/extensions/native1/commands/identity-controls-' + [DateTime]::UtcNow.ToString('yyyyMMddTHHmmssfff') + '.json')
  [IO.File]::WriteAllText($path, ($report | ConvertTo-Json -Depth 12), [Text.UTF8Encoding]::new($false))
}
Write-Output ('NATIVE1-IDENTITY PASS ' + $taskResults.Count + '/' + $taskExpected.Count)
