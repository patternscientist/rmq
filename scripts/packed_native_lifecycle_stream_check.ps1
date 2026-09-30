# Exact outer stream contracts. This does not replace native semantic or finally checks.
function Assert-LNExactStreamText([string]$Actual,[string]$Expected,[string]$Surface) {
  if(-not [string]::Equals($Actual,$Expected,[StringComparison]::Ordinal)){throw ('STREAM: '+$Surface+' differs')}
}
function Read-LNExactStream([string]$Path) {
  if(-not [IO.File]::Exists($Path)){throw ('STREAM: raw capture missing: '+$Path)}
  try {return ([Text.UTF8Encoding]::new($false,$true)).GetString([IO.File]::ReadAllBytes($Path))}
  catch {throw ('STREAM: invalid UTF-8 capture: '+$Path)}
}
function Invoke-LNRetainedLauncher {
  param([string]$FilePath,[string[]]$Arguments,[string]$WorkingDirectory,[string]$Stage,
    [int]$DeadlineSeconds,[long]$OutputLimitBytes,[string]$TempRoot,[switch]$ReleaseGatedScript)
  # Scope-local capture at the unchanged helper's cleanup boundary. Forward every
  # deletion to the real cmdlet, including after a copy failure. No global helper
  # or cleanup implementation is replaced, and unrelated paths are never copied.
  $retainedRoot=[IO.Path]::GetFullPath($TempRoot).TrimEnd('\','/')+[IO.Path]::DirectorySeparatorChar
  $retainedOut=Join-Path $TempRoot 'retained.stdout'
  $retainedErr=Join-Path $TempRoot 'retained.stderr'
  $retentionErrors=[Collections.Generic.List[string]]::new()
  function Remove-Item {
    [CmdletBinding()]param([string]$LiteralPath,[switch]$Force)
    $full=[IO.Path]::GetFullPath($LiteralPath)
    if($full.StartsWith($retainedRoot,[StringComparison]::OrdinalIgnoreCase) -and [IO.File]::Exists($full)){
      $destination=if($full.EndsWith('.stdout.log',[StringComparison]::Ordinal)){$retainedOut}elseif($full.EndsWith('.stderr.log',[StringComparison]::Ordinal)){$retainedErr}else{$null}
      if($null -ne $destination){try{[IO.File]::Copy($full,$destination,$false)}catch{$retentionErrors.Add($_.Exception.Message)}}
    }
    Microsoft.PowerShell.Management\Remove-Item @PSBoundParameters
  }
  $result=Invoke-RMQOwnedBoundedProcess @PSBoundParameters
  $result|Add-Member -NotePropertyName RawStandardOutput -NotePropertyValue $retainedOut
  $result|Add-Member -NotePropertyName RawStandardError -NotePropertyValue $retainedErr
  $result|Add-Member -NotePropertyName RetentionErrors -NotePropertyValue @($retentionErrors.ToArray())
  return $result
}
function Assert-LNOuterCapture([object]$Capture,[string]$ExpectedStdout,[string]$ExpectedStderr,[int]$ExpectedExit,[string]$Profile) {
  $launch=$Capture.launcher
  if($null -eq $launch -or $launch.TimedOut -or $launch.OutputLimitExceeded -or
     [IO.File]::Exists($Capture.spec.error) -or [IO.File]::Exists($Capture.spec.overflow)){
    throw ('STREAM: '+$Profile+' incomplete bounded capture')
  }
  if(@($launch.StandardOutput).Count -ne 0 -or @($launch.StandardError).Count -ne 0){throw ('STREAM: '+$Profile+' launcher output')}
  if(@($launch.RetentionErrors).Count -ne 0){throw ('STREAM: '+$Profile+' launcher retention failed')}
  Assert-LNExactStreamText (Read-LNExactStream $launch.RawStandardOutput) '' ($Profile+' launcher stdout')
  Assert-LNExactStreamText (Read-LNExactStream $launch.RawStandardError) '' ($Profile+' launcher stderr')
  if($null -eq $Capture.actual -or $Capture.actual.exitCode -ne $ExpectedExit -or $launch.ExitCode -ne $ExpectedExit){throw ('STREAM: '+$Profile+' ordinary exit differs')}
  Assert-LNExactStreamText (Read-LNExactStream $Capture.spec.stdout) $ExpectedStdout ($Profile+' stdout')
  Assert-LNExactStreamText (Read-LNExactStream $Capture.spec.stderr) $ExpectedStderr ($Profile+' stderr')
}
function Invoke-LNStreamCapture([string]$RepositoryRoot,[string]$File,[string[]]$Arguments,[string]$WorkingDirectory,[string]$OutputRoot,[int]$DeadlineSeconds,[string]$Stage) {
  # Reuse the protected production byte-copy child and existing ownership helper.
  [void][IO.Directory]::CreateDirectory($OutputRoot)
  $encoding=[Text.UTF8Encoding]::new($false,$true)
  $source=[IO.File]::ReadAllText((Join-Path $RepositoryRoot 'scripts/packed_native_lifecycle_storage_replay.ps1'),$encoding)
  $match=[regex]::Match($source,"(?s)\`$taskChildScript = @'\r?\n(.*?)\r?\n'@")
  if(-not $match.Success){throw 'STREAM: production raw child missing'}
  $child=Join-Path $OutputRoot 'raw-child.ps1'
  [IO.File]::WriteAllText($child,$match.Groups[1].Value,$encoding)
  $spec=@{file=$File;arguments=@($Arguments);cwd=$WorkingDirectory;environment=@{};
    stdout=(Join-Path $OutputRoot 'stdout.log');stderr=(Join-Path $OutputRoot 'stderr.log');
    exit=(Join-Path $OutputRoot 'exit.json');pid=(Join-Path $OutputRoot 'pid');
    error=(Join-Path $OutputRoot 'error');overflow=(Join-Path $OutputRoot 'overflow');outputLimit=16777216}
  $specPath=Join-Path $OutputRoot 'spec.json'
  [IO.File]::WriteAllText($specPath,($spec|ConvertTo-Json -Depth 8),$encoding)
  $shell=(Get-Process -Id $PID).Path
  $launch=Invoke-LNRetainedLauncher -FilePath $shell -Arguments @('-NoProfile','-File',$child,'-SpecPath',$specPath) `
    -WorkingDirectory $WorkingDirectory -Stage $Stage -DeadlineSeconds $DeadlineSeconds -OutputLimitBytes 16777216 `
    -TempRoot (Join-Path $OutputRoot 'launcher') -ReleaseGatedScript
  $actual=if([IO.File]::Exists($spec.exit)){[IO.File]::ReadAllText($spec.exit,$encoding)|ConvertFrom-Json}else{$null}
  $capture=@{launcher=$launch;actual=$actual;spec=$spec;raw=@()}
  foreach($p in @($spec.stdout,$spec.stderr,$spec.exit,$spec.pid,$spec.error,$spec.overflow,$child,$specPath,$launch.RawStandardOutput,$launch.RawStandardError)){
    if([IO.File]::Exists($p)){$capture.raw+=@{path=$p;bytes=([IO.FileInfo]$p).Length;sha256=(Get-FileHash -LiteralPath $p).Hash}}
  }
  [IO.File]::WriteAllText((Join-Path $OutputRoot 'CAPTURE.json'),($capture|ConvertTo-Json -Depth 15),$encoding)
  return $capture
}
function Get-LNStreamEvidencePath([string]$Text,[string]$Prefix,[string]$Root) {
  $nl=[Environment]::NewLine
  $first=$Text.Split(@($nl),[StringSplitOptions]::None)[0]
  if(-not $first.StartsWith($Prefix,[StringComparison]::Ordinal)){throw 'STREAM: evidence line missing'}
  $path=$first.Substring($Prefix.Length)
  $full=[IO.Path]::GetFullPath($path)
  $parent=[IO.Path]::GetFullPath($Root).TrimEnd('\','/')+[IO.Path]::DirectorySeparatorChar
  if(-not $full.StartsWith($parent,[StringComparison]::OrdinalIgnoreCase)){throw 'STREAM: evidence path outside owned root'}
  return $path
}
function Assert-LNWrapperCapture([object]$Capture,[string]$Kind,[string]$RepositoryRoot,[object]$ClaimExpectation=$null) {
  $nl=[Environment]::NewLine
  $stdout=Read-LNExactStream $Capture.spec.stdout
  $expected=''
  switch -CaseSensitive ($Kind) {
    {$_ -in @('focused','full')} {
      $path=Get-LNStreamEvidencePath $stdout 'LIFECYCLE-REPLAY evidence=' (Join-Path $RepositoryRoot '.lake/lifecycle-native-p0/runs')
      $summary=[IO.File]::ReadAllText((Join-Path $path 'SUMMARY.json'))|ConvertFrom-Json
      $count=if($Kind -ceq 'full'){23}else{1}
      $selfTest=$Kind -ceq 'full'
      if(-not $summary.success -or $null -ne $summary.failure -or -not $summary.integrity.attempted -or -not $summary.integrity.success -or @($summary.selected).Count -ne $count){throw 'STREAM: native summary differs'}
      if($Kind -ceq 'focused' -and $summary.selected[0] -cne 'pop-unique'){throw 'STREAM: focused selector differs'}
      $expected='LIFECYCLE-REPLAY evidence='+$path+$nl+'LIFECYCLE-REPLAY PASS cases='+$count+' selfTest='+$selfTest+$nl
    }
    'integrity' {
      $ids=@('intact-success','intact-stage-error','malformed-stdout-intact','stage-error-and-pin-change','stage-error-and-capture-error','success-and-pin-change','mixed-diagnostic-and-pin-change','timeout-and-pin-change','success-and-tracked-change','success-and-index-change','success-and-untracked-addition','success-and-untracked-byte-change','success-and-link-map-change','partial-identity-and-pin-change','missing-baseline')
      $prefix=($ids|ForEach-Object {'CONTROL PASS '+$_+$nl}) -join ''
      if(-not $stdout.StartsWith($prefix,[StringComparison]::Ordinal)){throw 'STREAM: integrity control roster differs'}
      $path=Get-LNStreamEvidencePath $stdout.Substring($prefix.Length) 'INTEGRITY CONTROLS evidence=' (Join-Path $RepositoryRoot '.lake/repair-r1')
      $result=[IO.File]::ReadAllText((Join-Path $path 'RESULTS.json'))|ConvertFrom-Json
      if((@($result.controls.id)-join ',') -cne ($ids-join ',') -or -not $result.fixtureRestoration -or -not $result.candidateUnchanged){throw 'STREAM: integrity result roster/restoration differs'}
      $expected=$prefix+'INTEGRITY CONTROLS evidence='+$path+$nl
    }
    'dependencies' {
      $path=Get-LNStreamEvidencePath $stdout 'DEPENDENCY CONTROLS PASS evidence=' (Join-Path $RepositoryRoot '.lake/repair-r1')
      $result=[IO.File]::ReadAllText((Join-Path $path 'RESULTS.json'))|ConvertFrom-Json
      $ids=@('complete-inventory','bea5ce75-incomplete','omit-lean.exe','omit-leanc.exe','omit-clang.exe','omit-ld.lld.exe','omit-libleanshared.dll','omit-libInit_shared.dll','omit-libclang-cpp.dll','omit-libLLVM-19.dll','omit-libc++.dll','omit-zlib1.dll','omit-libleanshared_1.dll','same-name-wrong-path','complete-unchanged-finalizer','tamper-zlib1.dll','tamper-link.map','tamper-manifest-hash','restored-finalizer')
      if((@($result.controls.id|Sort-Object)-join ',') -cne (@($ids|Sort-Object)-join ',') -or -not $result.installedToolsUnchanged -or -not $result.fixtureRestored){throw 'STREAM: dependency result roster/restoration differs'}
      $expected='DEPENDENCY CONTROLS PASS evidence='+$path+$nl
    }
    'checks' {
      $ids=@('contract','hygiene','native-decision','working-whitespace','range-whitespace','design-whole')
      $commits=@(& git -C $RepositoryRoot rev-list --reverse '9519b2c1af5e2cf59536b311db5e8dc81376a32f..HEAD')
      if($LASTEXITCODE){throw 'STREAM: commit inventory failed'}
      $ids+=@($commits|ForEach-Object {'design-'+$_.Substring(0,12)});$ids+='clean'
      $prefix=($ids|ForEach-Object {'CHECK PASS '+$_+$nl}) -join ''
      if(-not $stdout.StartsWith($prefix,[StringComparison]::Ordinal)){throw 'STREAM: check roster differs'}
      $path=Get-LNStreamEvidencePath $stdout.Substring($prefix.Length) 'FINAL CHECKS evidence=' (Join-Path $RepositoryRoot '.lake/repair-r1')
      $result=[IO.File]::ReadAllText((Join-Path $path 'RESULTS.json'))|ConvertFrom-Json
      if((@($result.checks.name)-join ',') -cne ($ids-join ',') -or @($result.checks|Where-Object {$_.exit -ne $_.expected}).Count){throw 'STREAM: check result differs'}
      $expected=$prefix+'FINAL CHECKS evidence='+$path+$nl
    }
    'claims' {
      if($null -eq $ClaimExpectation){throw 'STREAM: claim expectation missing'}
      Assert-LNClaimStreamExpectation $stdout $ClaimExpectation
      # Exact roster validation above consumes every captured byte. Pass the
      # already checked text through the shared transport/exit guards below.
      $expected=$stdout
    }
    default {throw 'STREAM: unsupported wrapper profile'}
  }
  Assert-LNOuterCapture $Capture $expected '' 0 ('wrapper-'+$Kind)
  return @{profile=$Kind;expectedStdout=$expected;expectedStderr='';expectedExit=0;validated=$true}
}
