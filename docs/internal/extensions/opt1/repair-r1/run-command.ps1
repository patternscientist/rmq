# Bounded command/evidence adapter; the specification is an explicit local plan.
[CmdletBinding()]
param(
 [Parameter(Mandatory=$true)][string]$Specification,
 [Parameter(Mandatory=$true)][string]$ReceiptDirectory
)
$ErrorActionPreference='Stop'
Set-StrictMode -Version Latest
$repo=[IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../../../../..'))
$utf8=[Text.UTF8Encoding]::new($false,$true)
$bytes=[IO.File]::ReadAllBytes([IO.Path]::GetFullPath($Specification))
$plan=$utf8.GetString($bytes)|ConvertFrom-Json
if($plan.Version -cne 'opt1-r1-command-v1' -or $plan.Name -cnotmatch '^[a-zA-Z0-9-]+$' -or
 $plan.SourceCommit -cnotmatch '^[0-9a-f]{40}$' -or
 $plan.DeadlineSeconds -lt 1 -or $plan.DeadlineSeconds -gt 21600 -or
 $plan.OutputLimitBytes -lt 1024 -or $plan.OutputLimitBytes -gt 268435456){throw 'OPT1-R1-COMMAND: invalid explicit command contract'}
$out=[IO.Path]::GetFullPath($ReceiptDirectory)
if(Test-Path -LiteralPath $out){throw 'OPT1-R1-COMMAND: evidence directory already exists'}
[void][IO.Directory]::CreateDirectory($out)
[IO.File]::WriteAllBytes((Join-Path $out 'SPECIFICATION.json'),$bytes)
. (Join-Path $repo 'scripts/owned_process_tree.ps1')
$git=Resolve-RMQScalarApplicationPath @(Get-Command git -CommandType Application) 'git'
$identity=Invoke-RMQOwnedBoundedProcess -FilePath $git -Arguments @('rev-parse','HEAD') `
 -WorkingDirectory $plan.WorkingDirectory -Stage ($plan.Name+'-head') -DeadlineSeconds 60 `
 -OutputLimitBytes 1048576 -TempRoot (Join-Path $out 'owned') -Environment @{GIT_OPTIONAL_LOCKS='0'}
[IO.File]::WriteAllText((Join-Path $out 'IDENTITY.json'),($identity|ConvertTo-Json -Depth 12),$utf8)
if($identity.ExitCode -ne 0 -or $identity.TimedOut -or $identity.OutputLimitExceeded -or
 @($identity.StandardOutput).Count -ne 1 -or $identity.StandardOutput[0] -cne $plan.SourceCommit){
 throw 'OPT1-R1-COMMAND: actual checkout differs from exact command contract'
}
function Get-CommandTrackedState([string]$Suffix) {
 $tracked=Invoke-RMQOwnedBoundedProcess -FilePath $git -Arguments @('-c','core.excludesfile=','status','--porcelain=v1','--untracked-files=no') `
  -WorkingDirectory $plan.WorkingDirectory -Stage ($plan.Name+'-status-'+$Suffix) -DeadlineSeconds 60 `
  -OutputLimitBytes 1048576 -TempRoot (Join-Path $out 'owned') -Environment @{GIT_OPTIONAL_LOCKS='0'}
 $index=Invoke-RMQOwnedBoundedProcess -FilePath $git -Arguments @('rev-parse','--path-format=absolute','--git-path','index') `
  -WorkingDirectory $plan.WorkingDirectory -Stage ($plan.Name+'-index-'+$Suffix) -DeadlineSeconds 60 `
  -OutputLimitBytes 1048576 -TempRoot (Join-Path $out 'owned') -Environment @{GIT_OPTIONAL_LOCKS='0'}
 foreach($child in @($tracked,$index)) {
  if($child.ExitCode -ne 0 -or $child.TimedOut -or $child.OutputLimitExceeded -or @($child.StandardError).Count -ne 0){throw 'OPT1-R1-COMMAND: tracked-state inventory failed'}
 }
 if(@($index.StandardOutput).Count -ne 1){throw 'OPT1-R1-COMMAND: index location is not scalar'}
 return [pscustomobject]@{Status=($tracked.StandardOutput -join "`n");IndexSHA256=(Get-FileHash -LiteralPath $index.StandardOutput[0]).Hash;StatusResult=$tracked;IndexResult=$index}
}
$trackedBefore=Get-CommandTrackedState 'before'
if($trackedBefore.Status.Length -ne 0){throw 'OPT1-R1-COMMAND: tracked checkout must be clean before final command'}
$environment=@{}
foreach($entry in $plan.Environment.PSObject.Properties){$environment[$entry.Name]=[string]$entry.Value}
$before=[ordered]@{}
foreach($relative in @($plan.Inputs)){
 $before[$relative]=(Get-FileHash -LiteralPath (Join-Path $plan.WorkingDirectory $relative)).Hash
}
$started=[datetime]::UtcNow.ToString('o')
$result=Invoke-RMQOwnedBoundedProcess -FilePath $plan.Executable -Arguments @($plan.Arguments) `
 -WorkingDirectory $plan.WorkingDirectory -Stage $plan.Name -DeadlineSeconds $plan.DeadlineSeconds `
 -OutputLimitBytes $plan.OutputLimitBytes -TempRoot (Join-Path $out 'owned') -Environment $environment
$trackedAfter=Get-CommandTrackedState 'after'
$after=[ordered]@{}
foreach($relative in @($plan.Inputs)){
 $after[$relative]=(Get-FileHash -LiteralPath (Join-Path $plan.WorkingDirectory $relative)).Hash
}
$unchanged=(($before|ConvertTo-Json -Compress) -ceq ($after|ConvertTo-Json -Compress)) -and
 $trackedBefore.Status -ceq $trackedAfter.Status -and $trackedBefore.IndexSHA256 -ceq $trackedAfter.IndexSHA256
$absent=@($result.TerminatedIds|Where-Object {$null -ne (Get-Process -Id $_ -ErrorAction SilentlyContinue)}).Count -eq 0
$record=[ordered]@{Version='opt1-r1-command-receipt-v1';Name=$plan.Name;SourceCommit=$plan.SourceCommit;
 SourceProfileSHA256=$plan.SourceProfileSHA256;BuildReceiptSHA256=$plan.BuildReceiptSHA256;
 Coverage=@($plan.Coverage);ClosestMeasuredSeconds=$plan.ClosestMeasuredSeconds;
 StartedUTC=$started;FinishedUTC=[datetime]::UtcNow.ToString('o');
 Executable=$plan.Executable;Arguments=@($plan.Arguments);WorkingDirectory=$plan.WorkingDirectory;
 Environment=$environment;InputsBefore=$before;InputsAfter=$after;InputsUnchanged=$unchanged;
 TrackedBefore=$trackedBefore;TrackedAfter=$trackedAfter;
 ActualIdentity=$identity;
 ReportedTerminatedProcessesAbsent=$absent;POSIX='UNEXECUTED';Result=$result;
 AdapterSHA256=(Get-FileHash -LiteralPath $PSCommandPath).Hash;
 SupervisorSHA256=(Get-FileHash -LiteralPath (Join-Path $repo 'scripts/owned_process_tree.ps1')).Hash}
[IO.File]::WriteAllText((Join-Path $out 'RESULT.json'),($record|ConvertTo-Json -Depth 24),$utf8)
[IO.File]::WriteAllLines((Join-Path $out 'stdout.log'),[string[]]$result.StandardOutput,$utf8)
[IO.File]::WriteAllLines((Join-Path $out 'stderr.log'),[string[]]$result.StandardError,$utf8)
Write-Host "OPT1-R1-COMMAND $($plan.Name) exit=$($result.ExitCode) seconds=$($result.DurationSeconds) timeout=$($result.TimedOut) overflow=$($result.OutputLimitExceeded) inputsUnchanged=$unchanged"
if(-not $unchanged -or -not $absent -or $result.TimedOut -or $result.OutputLimitExceeded){exit 1}
exit $result.ExitCode
