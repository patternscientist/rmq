
# LIFE-1-R3 injected test double appended to a disposable copy of
# scripts/packed_native_lifecycle_stream_check.ps1. It wraps the real capture and
# injects its fault only for the harness rooted at R3_FAULT_SCOPE, after the real
# owned stage has completed. LIFE-1-R4: lock-cleanup additionally holds an
# exclusive lock on the harness fixture's existing-untracked.txt until the
# harness process exits, so its restoration step throws inside cleanup.
# R3-FAULT-FUNCTION
${function:R3RealInvokeLNStreamCapture}=${function:Invoke-LNStreamCapture}
function Invoke-LNStreamCapture([string]$RepositoryRoot,[string]$File,[string[]]$Arguments,[string]$WorkingDirectory,[string]$OutputRoot,[int]$DeadlineSeconds,[string]$Stage) {
  $capture=R3RealInvokeLNStreamCapture $RepositoryRoot $File $Arguments $WorkingDirectory $OutputRoot $DeadlineSeconds $Stage
  $scope=[Environment]::GetEnvironmentVariable('R3_FAULT_SCOPE')
  if(-not [string]::IsNullOrEmpty($scope) -and [string]::Equals([IO.Path]::GetFullPath($RepositoryRoot).TrimEnd('\','/'),[IO.Path]::GetFullPath($scope).TrimEnd('\','/'),[StringComparison]::OrdinalIgnoreCase)){
    $fail=$false
    if([Environment]::GetEnvironmentVariable('R3_FAULT_MODE') -ceq 'carrier-fail'){
      $marker=[Environment]::GetEnvironmentVariable('R3_FAULT_MARKER')
      if(-not [IO.File]::Exists($marker)){
        [IO.File]::WriteAllText($marker,'carrier-fail')
        $carrier=Join-Path (Split-Path -Parent $OutputRoot) 'source'
        [IO.File]::WriteAllText((Join-Path $carrier 'r3-carrier-dirt.txt'),'r3-injected-carrier-change')
        $fail=$true
      }
    } elseif([Environment]::GetEnvironmentVariable('R3_FAULT_MODE') -ceq 'lock-cleanup'){
      $marker=[Environment]::GetEnvironmentVariable('R3_FAULT_MARKER')
      if(-not [IO.File]::Exists($marker)){
        [IO.File]::WriteAllText($marker,'lock-cleanup')
        $global:R4CleanupLock=[IO.File]::Open((Join-Path $WorkingDirectory 'existing-untracked.txt'),[IO.FileMode]::Open,[IO.FileAccess]::ReadWrite,[IO.FileShare]::None)
        $fail=$true
      }
    } else {$fail=Invoke-R3Fault}
    if($fail){$capture.launcher.TimedOut=$true}
  }
  return $capture
}
