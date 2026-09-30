# LIFE-1-R3 injected fault primitive. Text is inlined by failure_controls.ps1 into
# the disposable test doubles at the `# R3-FAULT-FUNCTION` placeholder; it never
# runs against tracked files. The fault fires at most once per control (marker).
# LIFE-1-R4 adds modes (the R3 modes are unchanged): sleep outlives a short
# owned deadline; block-durable makes the target path a directory so the
# harness's durable write fails; git-hang/git-fail arm the R4 git double (the
# marker is its trigger), with git-fail also reporting an ordinary failure.
function Invoke-R3Fault {
  $mode=[Environment]::GetEnvironmentVariable('R3_FAULT_MODE')
  if([string]::IsNullOrEmpty($mode) -or $mode -ceq 'intact'){return $false}
  $marker=[Environment]::GetEnvironmentVariable('R3_FAULT_MARKER')
  if([string]::IsNullOrEmpty($marker) -or [IO.File]::Exists($marker)){return $false}
  [IO.File]::WriteAllText($marker,$mode)
  $target=[Environment]::GetEnvironmentVariable('R3_FAULT_TARGET')
  switch -CaseSensitive ($mode) {
    'change' {[IO.File]::AppendAllText($target,'r3-injected-change');return $false}
    'change-fail' {[IO.File]::AppendAllText($target,'r3-injected-change');return $true}
    'delete-fail' {[IO.File]::Delete($target);return $true}
    'fail' {return $true}
    'sleep' {Start-Sleep -Seconds 60;return $false}
    'block-durable' {[void][IO.Directory]::CreateDirectory($target);return $false}
    'git-hang' {return $false}
    'git-fail' {return $true}
    default {throw ('R3-DOUBLE: unsupported fault mode '+$mode)}
  }
}
