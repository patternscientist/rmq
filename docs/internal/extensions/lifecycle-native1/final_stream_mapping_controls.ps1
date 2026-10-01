[CmdletBinding()]
param()
$ErrorActionPreference='Stop'
$root=[IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../../../..'))
. (Join-Path $root 'scripts/lifecycle_native_identity.ps1')
$utf8=[Text.UTF8Encoding]::new($false,$true)
$expectedHash='92a0cda169f378eba27a9884e5ed4a9e147845ef80ed0d528a02e95beb115813'
$target=Join-Path $PSScriptRoot 'final_stream_controls.ps1'
$manifest=Join-Path $PSScriptRoot 'FINAL_STREAM_CONTROL_MAP.json'
$run=Join-Path $root ('.lake/lifecycle-native1/final-stream-mapping/'+[DateTime]::UtcNow.ToString('yyyyMMddTHHmmssfff')+'-'+[Guid]::NewGuid().ToString('N').Substring(0,8))
$scratch=Join-Path $run 'disposable'
$pins=[Collections.Generic.List[object]]::new()
$results=[Collections.Generic.List[object]]::new()
$cases=@(
  @{id='original-plan';find='';replace='';exit=0},
  @{id='changed-handler';find="id='design-accept-exact-counts';handler='design'";replace="id='design-accept-exact-counts';handler='claims-zero'";exit=1},
  @{id='changed-verdict';find="handler='design';mutation='identity';verdict='accept'";replace="handler='design';mutation='identity';verdict='reject'";exit=1},
  @{id='changed-mutation';find="handler='design';mutation='identity'";replace="handler='design';mutation='append-unrelated-line'";exit=1},
  @{id='changed-diagnostic';find="id='design-accept-exact-counts';handler='design';mutation='identity';verdict='accept';diagnostic=''";replace="id='design-accept-exact-counts';handler='design';mutation='identity';verdict='accept';diagnostic='unexpected'";exit=1}
)
$expectedIds=@('original-plan','changed-handler','changed-verdict','changed-mutation','changed-diagnostic')
$caseMapping=@($cases|ForEach-Object{[ordered]@{id=$_.id;find=$_.find;replace=$_.replace;exit=$_.exit}})
$caseMappingHash=Get-LN1BytesHash ($utf8.GetBytes(($caseMapping|ConvertTo-Json -Depth 5 -Compress)))
if(-not [StringComparer]::Ordinal.Equals($caseMappingHash,'0d374704543cf0a87fde7a129920ab00415a563f3baac743a9ec0dfdf4260920')){
  throw 'FINAL-MAPPING: frozen ID/find/replace/exit mapping differs'
}
$report=[ordered]@{schema='lifecycle-native1-final-stream-mapping-controls-v1';success=$false;
  startedUtc=[DateTime]::UtcNow.ToString('o');mappingSHA256=$expectedHash;
  caseMappingSHA256=$caseMappingHash;
  expectedIds=$expectedIds;cases=$cases;results=@();pins=@();failure=$null;integrity=$null;cleanup=$null;
  deadlineSeconds=30;deadlineRationale='Current owned PowerShell caller controls use a measured 30-second ceiling; these callers run Plan or reject before helper loading, with no Lean/native/compiler work.';
  heavyMutexAcquired=$false;compilerInvocations=0;nativeInvocations=0;liveSourceWrites=0}
function Pin-FSM([string]$Path){$p=Get-LN1Pin $Path;$pins.Add($p);return $p}
try{
  [void][IO.Directory]::CreateDirectory($scratch)
  $shell=(Get-Process -Id $PID).Path
  foreach($path in @($PSCommandPath,$shell,$target,$manifest,
      (Join-Path $PSScriptRoot 'final_streams.ps1'),
      (Join-Path $root 'scripts/lifecycle_native_identity.ps1'),
      (Join-Path $root 'scripts/owned_process_tree.ps1'),
      (Join-Path $root 'scripts/packed_native_lifecycle_stream_check.ps1'),
      (Join-Path $root 'scripts/packed_native_lifecycle_storage_replay.ps1'),
      (Join-Path $root 'scripts/packed_native_lifecycle_integrity_check.ps1'))){[void](Pin-FSM $path)}
  $manifestBytes=[IO.File]::ReadAllBytes($manifest)
  if(-not [StringComparer]::Ordinal.Equals((Get-LN1BytesHash $manifestBytes),$expectedHash)){
    throw 'FINAL-MAPPING: frozen manifest differs'
  }
  $mapping=$utf8.GetString($manifestBytes)|ConvertFrom-Json -ErrorAction Stop
  if(@($mapping).Count -ne 15){throw 'FINAL-MAPPING: original mapping count differs'}
  $expectedPlan=[ordered]@{schema='lifecycle-native1-final-stream-controls-plan-v1';count=15;
    orderedIds=@($mapping.id);selectedIds=@($mapping.id);mapping=@($mapping);mappingSHA256=$expectedHash;
    boundary='Output-language/helper controls only. No production scope checker, Lean or native process is invoked.'}
  $planText=($expectedPlan|ConvertTo-Json -Depth 8)+[Environment]::NewLine
  $source=Read-LNExactStream $target
  $driver=Join-Path $run 'caller.ps1'
  $driverText=@'
param([Parameter(Mandatory)][string]$Target)
$ErrorActionPreference='Stop'
try { & $Target -Mode Plan; exit 0 }
catch { [Console]::Error.Write($_.Exception.Message+[Environment]::NewLine); exit 1 }
'@
  [IO.File]::WriteAllText($driver,($driverText+[Environment]::NewLine),$utf8);[void](Pin-FSM $driver)
  foreach($case in $cases){
    $caseTarget=$target
    if($case.exit -eq 1){
      if([regex]::Matches($source,[regex]::Escape($case.find)).Count -ne 1){throw ('FINAL-MAPPING: nonunique mutation '+$case.id)}
      $caseTarget=Join-Path $scratch ($case.id+'.ps1')
      [IO.File]::WriteAllText($caseTarget,$source.Replace($case.find,$case.replace),$utf8)
      [void](Pin-FSM $caseTarget)
    }
    $entry=[ordered]@{id=$case.id;target=$caseTarget;capture=$null;success=$false}
    $results.Add($entry)
    $capture=Invoke-LNStreamCapture $root $shell @('-NoProfile','-File',$driver,'-Target',$caseTarget) $root `
      (Join-Path $run $case.id) 30 $case.id
    $entry.capture=$capture
    foreach($pin in $capture.raw){
      $current=Pin-FSM $pin.path
      if($current.bytes -ne $pin.bytes -or $current.sha256 -cne $pin.sha256){throw 'FINAL-MAPPING: capture pin changed'}
    }
    $stdout=if($case.exit -eq 0){$planText}else{''}
    $stderr=if($case.exit -eq 0){''}else{'FINAL-STREAM-CONTROLS: frozen ID/handler/mutation/verdict/diagnostic mapping differs'+[Environment]::NewLine}
    Assert-LNOuterCapture $capture $stdout $stderr $case.exit $case.id
    $entry.success=$true
  }
  if($results.Count -ne 5 -or -not [StringComparer]::Ordinal.Equals(($results.id -join '|'),($expectedIds -join '|')) -or
      @($results|Where-Object{-not $_.success}).Count){throw 'FINAL-MAPPING: incomplete or reordered controls'}
  $report.success=$true
}catch{$report.failure=$_.Exception.Message}
finally{
  $integrityErrors=[Collections.Generic.List[string]]::new()
  foreach($pin in $pins){try{
    $current=Get-LN1Pin $pin.path
    if($current.bytes -ne $pin.bytes -or $current.sha256 -cne $pin.sha256){throw ('changed pin '+$pin.path)}
  }catch{$integrityErrors.Add($_.Exception.Message)}}
  $report.integrity=@{success=($integrityErrors.Count -eq 0);checked=$pins.Count;errors=@($integrityErrors.ToArray())}
  $cleanupErrors=[Collections.Generic.List[string]]::new()
  try{
    $full=[IO.Path]::GetFullPath($scratch)
    $prefix=[IO.Path]::GetFullPath($run).TrimEnd('\','/')+[IO.Path]::DirectorySeparatorChar
    if(-not $full.StartsWith($prefix,[StringComparison]::OrdinalIgnoreCase) -or
        -not [StringComparer]::OrdinalIgnoreCase.Equals($full,[IO.Path]::GetFullPath((Join-Path $run 'disposable')))){
      throw 'FINAL-MAPPING: unsafe cleanup target'
    }
    if([IO.Directory]::Exists($full)){
      foreach($item in @((Get-Item -LiteralPath $full))+@(Get-ChildItem -LiteralPath $full -Recurse -Force)){
        if($item.Attributes -band [IO.FileAttributes]::ReparsePoint){throw 'FINAL-MAPPING: cleanup refuses reparse point'}
      }
      Remove-Item -LiteralPath $full -Recurse -Force
    }
    if([IO.Directory]::Exists($full)){throw 'FINAL-MAPPING: disposable remains'}
  }catch{$cleanupErrors.Add($_.Exception.Message)}
  $report.cleanup=@{success=($cleanupErrors.Count -eq 0);disposableAbsent=(-not [IO.Directory]::Exists($scratch));errors=@($cleanupErrors.ToArray())}
  $report.success=$report.success -and $report.integrity.success -and $report.cleanup.success
  $report.results=@($results.ToArray());$report.pins=@($pins.ToArray());$report.completedUtc=[DateTime]::UtcNow.ToString('o')
  [void][IO.Directory]::CreateDirectory($run)
  [IO.File]::WriteAllText((Join-Path $run 'RESULT.json'),($report|ConvertTo-Json -Depth 35),$utf8)
}
Write-Output ('FINAL-MAPPING evidence='+$run)
if(-not $report.success){Write-Output ('FINAL-MAPPING FAIL '+$report.failure);exit 1}
Write-Output 'FINAL-MAPPING PASS count=5'
