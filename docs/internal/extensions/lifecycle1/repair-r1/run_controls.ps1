[CmdletBinding()]
param(
  [Parameter(Mandatory=$true)][string]$Shell,
  [Parameter(Mandatory=$true)][ValidateSet('pwsh','winps')][string]$Profile,
  [AllowEmptyString()][string]$OnlyCase,
  [switch]$ProbeOnly,
  [string]$RegistryPath,
  [string]$EvidenceRoot
)
Set-StrictMode -Version Latest
$ErrorActionPreference='Stop'
$root=[IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../../../../..'))
$utf8=[Text.UTF8Encoding]::new($false,$true)
if(-not $PSBoundParameters.ContainsKey('RegistryPath')){$RegistryPath=Join-Path $PSScriptRoot 'CONTROL_REGISTRY.json'}
. (Join-Path $PSScriptRoot 'runtime_profile.ps1')
$runtime=Assert-LifecycleRepairRuntime $Shell $Profile
$frozenPath=Join-Path $PSScriptRoot 'CONTROL_REGISTRY.frozen.json'
$frozenHash='385c9bc95ac09b3cc046a7049e954cdf19361330c31f99bd83c9da0c822423f2'
if((Get-FileHash -LiteralPath $frozenPath).Hash.ToLowerInvariant() -cne $frozenHash){throw 'L1R1-REGISTRY: frozen registry identity changed'}
$frozen=$utf8.GetString([IO.File]::ReadAllBytes($frozenPath))|ConvertFrom-Json
$bytes=[IO.File]::ReadAllBytes($RegistryPath)
$registry=$utf8.GetString($bytes)|ConvertFrom-Json
if(@($registry.cases).Count -ne @($frozen.cases).Count){throw 'L1R1-REGISTRY: exact count mismatch'}
for($i=0;$i -lt @($frozen.cases).Count;$i++) {
  if($registry.cases[$i].id -cne $frozen.cases[$i].id){throw 'L1R1-REGISTRY: missing duplicate unknown or reordered ID'}
}
if([Convert]::ToBase64String($bytes) -cne [Convert]::ToBase64String([IO.File]::ReadAllBytes($frozenPath))){throw 'L1R1-REGISTRY: exact mapping bytes mismatch'}
foreach($component in $frozen.components) {
  if((Get-FileHash -LiteralPath (Join-Path $PSScriptRoot $component.path)).Hash.ToLowerInvariant() -cne $component.sha256){throw 'L1R1-REGISTRY: component mapping identity changed'}
}
$selected=@($registry.cases|Where-Object {$_.profiles -ccontains $Profile})
if($PSBoundParameters.ContainsKey('OnlyCase')) {
  if([string]::IsNullOrWhiteSpace($OnlyCase)){throw 'L1R1-SELECTOR: explicitly empty selector'}
  $selected=@($selected|Where-Object {$_.id -ceq $OnlyCase})
  if($selected.Count -ne 1){throw 'L1R1-SELECTOR: unknown or unavailable exact ID'}
}
if($ProbeOnly){Write-Output ('L1R1 SELECT '+($selected.id -join ','));exit 0}
if([string]::IsNullOrWhiteSpace($EvidenceRoot)){$EvidenceRoot=Join-Path $root ('.lake/repair-r1/controls-'+$Profile+'-'+[Guid]::NewGuid().ToString('N'))}
$evidence=[IO.Path]::GetFullPath($EvidenceRoot)
$allowed=[IO.Path]::GetFullPath((Join-Path $root '.lake')).TrimEnd('\','/')+[IO.Path]::DirectorySeparatorChar
if(-not $evidence.StartsWith($allowed,[StringComparison]::OrdinalIgnoreCase) -or (Test-Path -LiteralPath $evidence)){throw 'L1R1-EVIDENCE: fresh owned descendant required'}
[void][IO.Directory]::CreateDirectory($evidence)
# LIFE-1-R3: from here on every exit path writes summary.json. The stage error,
# every independent pin comparison and every finalization error are recorded
# separately; none of them can replace another.
$pinPaths=@('scripts/lifecycle_validator.ps1','scripts/lifecycle_validator_environment.ps1','scripts/lifecycle_dependency_replay.ps1','scripts/owned_process_tree.ps1',
    'scripts/lifecycle_dependency_cases.json','.lake/build/bin/rmq_lifecycle_validate.exe')
foreach($name in @('run_controls.ps1','runtime_profile.ps1','selector_child.ps1','dependency_child.ps1','deadline_control.ps1','finalizer_control.ps1')) {
  $pinPaths+=('docs/internal/extensions/lifecycle1/repair-r1/'+$name)
}
$pins=[ordered]@{}
$results=[Collections.Generic.List[object]]::new()
$passed=$false
$completed=$false
$stageError=$null;$stageRecord=$null
$integrityErrors=[Collections.Generic.List[string]]::new()
$cleanupErrors=[Collections.Generic.List[string]]::new()
$pinChecks=[Collections.Generic.List[object]]::new()
$caseSlotChecks=[Collections.Generic.List[object]]::new()
$durableFailed=$false
try {
  foreach($path in $pinPaths){$pins[$path]=(Get-FileHash -LiteralPath (Join-Path $root $path)).Hash}
  . (Join-Path $root 'scripts/owned_process_tree.ps1')
  foreach($case in $selected) {
    $caseRoot=Join-Path $evidence $case.id
    [void][IO.Directory]::CreateDirectory($caseRoot)
    $arguments=@('-NoProfile','-ExecutionPolicy','Bypass','-File',(Join-Path $PSScriptRoot $case.handler))
    if($case.kind -ceq 'finalizer') {
      $arguments+=@('-Case',$case.id,'-Shell',$Shell,'-RepositoryRoot',$root,'-EvidenceRoot',(Join-Path $caseRoot 'fixtures'))
    } elseif($case.kind -ceq 'deadline') {
      $arguments+=@('-RepositoryRoot',$root,'-EvidenceRoot',(Join-Path $caseRoot 'fixture'))
    } else {
      $specPath=Join-Path $caseRoot 'case.json'
      [IO.File]::WriteAllText($specPath,($case.spec|ConvertTo-Json -Depth 40),$utf8)
      $arguments+=@('-SpecPath',$specPath,'-RepositoryRoot',$root,'-EvidenceRoot',(Join-Path $caseRoot 'fixture'))
    }
    $mutex=$null;$locked=$false
    try {
      # The actual validator wrapper owns the shared mutex itself.
      if($case.kind -cne 'wrapper') {
        $mutex=[Threading.Mutex]::new($false,'Local\RMQLifecycleImplementationHeavy20260920')
        try{$locked=$mutex.WaitOne(7200000)}catch [Threading.AbandonedMutexException]{$locked=$true}
        if(-not $locked){throw 'L1R1-SCHEDULING: no heavy slot'}
      }
      $r=Invoke-RMQOwnedBoundedProcess -FilePath $Shell -Arguments $arguments -WorkingDirectory $root -Stage $case.id `
        -DeadlineSeconds 180 -OutputLimitBytes 1048576 -TempRoot (Join-Path $caseRoot 'process')
      [IO.File]::WriteAllText((Join-Path $caseRoot 'process.json'),($r|ConvertTo-Json -Depth 30),$utf8)
      [IO.File]::WriteAllText((Join-Path $caseRoot 'stdout.returned-lines.txt'),($r.StandardOutput -join "`n"),$utf8)
      [IO.File]::WriteAllText((Join-Path $caseRoot 'stderr.returned-lines.txt'),($r.StandardError -join "`n"),$utf8)
      if($r.TimedOut -or $r.OutputLimitExceeded -or $r.ExitCode -ne 0 -or $r.Ownership -cne 'kill-on-close-job' -or @($r.TerminatedIds).Count -ne 0 -or
         @($r.StandardError).Count -ne 0 -or @($r.StandardOutput).Count -ne 1){throw ('L1R1-CONTROL: failed/incomplete '+$case.id)}
      if($case.kind -ceq 'finalizer') {
        $prefix='L1R1-FINALIZER CONTROL PASS '+$case.id+' '
        if(-not $r.StandardOutput[0].StartsWith($prefix,[StringComparison]::Ordinal)){throw 'L1R1-CONTROL: wrong finalizer terminal record'}
        $leaf=$r.StandardOutput[0].Substring($prefix.Length)
        $leafExpected='^'+[regex]::Escape((Join-Path $caseRoot ('fixtures/'+$case.id+'-')))+'[0-9a-f]{32}$'
        if($leaf -cnotmatch $leafExpected){throw 'L1R1-CONTROL: unexpected finalizer evidence path'}
        $receipt=Get-Content -LiteralPath (Join-Path $leaf 'result.json') -Raw|ConvertFrom-Json
        if(-not $receipt.passed -or $receipt.id -cne $case.id -or @($receipt.records).Count -ne 2){throw 'L1R1-CONTROL: missing finalizer P/Q receipt'}
      } elseif($r.StandardOutput[0] -cne ('L1R1-CONTROL|'+$case.id+'|PASS')){throw 'L1R1-CONTROL: wrong terminal record'}
      $results.Add([ordered]@{id=$case.id;passed=$true;seconds=$r.DurationSeconds;receipt=(Join-Path $caseRoot 'process.json')})
      Write-Output ('L1R1 CASE '+$case.id+' PASS')
    } finally {
      # LIFE-1-R4: re-check every captured pin while this case's heavy slot is
      # still held, so a change made during the case is recorded before release.
      $caseChecks=[Collections.Generic.List[object]]::new()
      foreach($path in $pinPaths){
        if(-not $pins.Contains($path)){continue}
        $final=$null;$status='verified'
        try{$final=(Get-FileHash -LiteralPath (Join-Path $root $path)).Hash}catch{$status='unreadable-final';$integrityErrors.Add('L1R1-INTEGRITY: case '+$case.id+' final hash failed '+$path+': '+$_.Exception.Message)}
        if($null -ne $final -and $final -cne $pins[$path]){$status='changed';$integrityErrors.Add('L1R1-INTEGRITY: source changed during case '+$case.id+' '+$path)}
        $caseChecks.Add([ordered]@{path=$path;finalSha256=$final;status=$status})
      }
      $caseSlotChecks.Add([ordered]@{id=$case.id;slotHeld=$locked;checks=@($caseChecks.ToArray())})
      if($locked){try{$mutex.ReleaseMutex()}catch{$cleanupErrors.Add('L1R1-CLEANUP: mutex release '+$case.id+': '+$_.Exception.Message)}}
      if($null -ne $mutex){try{$mutex.Dispose()}catch{$cleanupErrors.Add('L1R1-CLEANUP: mutex dispose '+$case.id+': '+$_.Exception.Message)}}
    }
  }
  if($results.Count -ne $selected.Count){throw 'L1R1-CONTROL: incomplete selected registry'}
  $completed=$true
} catch {$stageError=$_.Exception.Message;$stageRecord=$_}
finally {
  # Independent integrity: every entry pin, in its own guard, all differences kept.
  foreach($path in $pinPaths){
    $entry=if($pins.Contains($path)){$pins[$path]}else{$null}
    $final=$null;$status='not-captured'
    if($null -ne $entry){
      $status='verified'
      try{$final=(Get-FileHash -LiteralPath (Join-Path $root $path)).Hash}catch{$status='unreadable-final';$integrityErrors.Add('L1R1-INTEGRITY: final hash failed '+$path+': '+$_.Exception.Message)}
      if($null -ne $final -and $final -cne $entry){$status='changed';$integrityErrors.Add('L1R1-INTEGRITY: source changed '+$path)}
    }
    $pinChecks.Add([ordered]@{path=$path;entrySha256=$entry;finalSha256=$final;status=$status})
  }
  $shellHash=$null
  try{$shellHash=(Get-FileHash -LiteralPath $Shell).Hash}catch{$cleanupErrors.Add('L1R1-SUMMARY: shell hash unavailable: '+$_.Exception.Message)}
  $passed=$completed -and $null -eq $stageError -and $integrityErrors.Count -eq 0 -and $cleanupErrors.Count -eq 0
  $finalization=[ordered]@{schema='life1-r3-finalization-v1';verdict=$(if($passed){'pass'}else{'fail'});stageError=$stageError
    integrityErrors=@($integrityErrors.ToArray());cleanupErrors=@($cleanupErrors.ToArray());pinChecks=@($pinChecks.ToArray())
    entryPinCount=$pins.Count;verifiedPinCount=@($pinChecks|Where-Object {$_.status -ceq 'verified'}).Count
    caseSlotChecks=@($caseSlotChecks.ToArray())}
  try {
    [IO.File]::WriteAllText((Join-Path $evidence 'summary.json'),([ordered]@{passed=$passed;profile=$Profile;shell=$Shell;runtime=$runtime;
      shellSha256=$shellHash;registrySha256=$frozenHash;selected=@($selected.id);results=@($results.ToArray());entrySourcePins=$pins;
      finalization=$finalization;
      streamLimit='Inherited helper returned nonempty lines; overflow/exception may prevent output recovery.'}|ConvertTo-Json -Depth 40),$utf8)
  } catch {$durableFailed=$true;$passed=$false;[Console]::Error.WriteLine('L1R1-SUMMARY: durable summary write failed: '+$_.Exception.Message)}
}
if(-not $passed){
  foreach($message in @($integrityErrors)+@($cleanupErrors)){[Console]::Error.WriteLine($message)}
  if($null -ne $stageRecord){throw $stageRecord}
  exit 1
}
Write-Output ('L1R1 CONTROLS PASS '+$evidence)
