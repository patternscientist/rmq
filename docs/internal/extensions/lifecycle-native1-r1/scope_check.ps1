[CmdletBinding()]
param([string]$Root=[IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../../../..')),[switch]$Complete)
$ErrorActionPreference='Stop'
. (Join-Path $PSScriptRoot 'identity.ps1')
$run=Join-Path $Root ('.lake/lifecycle-native1-r1/scope/'+[DateTime]::UtcNow.ToString('yyyyMMddTHHmmssfff')+'-'+[Guid]::NewGuid().ToString('N').Substring(0,8))
[void][IO.Directory]::CreateDirectory($run)
$git=(Get-Command git -CommandType Application|Select-Object -First 1).Source
$pins=[Collections.Generic.List[object]]::new();$stages=[Collections.Generic.List[object]]::new()
$result=[ordered]@{schema='lifecycle-native1-r1-scope-v1';success=$false;base=$script:R1Base;
  originalBase=$script:R1OriginalBase;head=$null;branch=$null;complete=[bool]$Complete;
  startedUtc=[DateTime]::UtcNow.ToString('o');paths=@();cumulativePaths=@();checked=$null;stages=@();pins=@();failure=$null;integrity=$null}
function Git-R1Scope([string]$Name,[string[]]$Arguments){
  $capture=Invoke-LNStreamCapture $Root $git (@('-c','core.excludesfile=','-c','core.safecrlf=false')+$Arguments) $Root (Join-Path $run $Name) 60 $Name
  $stages.Add(@{name=$Name;file=$git;arguments=$Arguments;capture=$capture})
  $out=Read-LNExactStream $capture.spec.stdout
  Assert-LNOuterCapture $capture $out '' 0 $Name
  return $out
}
try{
  $baselinePath=Join-Path $PSScriptRoot 'BASE_IDENTITY.json'
  foreach($p in @($PSCommandPath,(Join-Path $PSScriptRoot 'identity.ps1'),$baselinePath,$git,
      (Join-Path $PSScriptRoot 'START.json'),(Join-Path $Root 'scripts/lifecycle_native_identity.ps1'))){$pins.Add((Get-LN1Pin $p))}
  $baselineBytes=[IO.File]::ReadAllBytes($baselinePath)
  # This literal freezes the startup inventory; a coordinator-authorized checkout
  # restoration must explicitly replace it with the retained corrected inventory.
  if(-not [string]::Equals((Get-LN1BytesHash $baselineBytes),'D580D08779FA5699BBD15022F11B66AE8EBBBD3E989890816A6BF82387D25B68',[StringComparison]::OrdinalIgnoreCase)){
    throw 'R1-SCOPE: frozen baseline inventory bytes differ'
  }
  $baseline=$script:R1Utf8.GetString($baselineBytes)|ConvertFrom-Json
  $start=[IO.File]::ReadAllText((Join-Path $PSScriptRoot 'START.json'),$script:R1Utf8)|ConvertFrom-Json
  if(-not (Test-R1Exact $start.base $script:R1Base) -or -not (Test-R1Exact $start.branch $script:R1Branch) -or
      -not (Test-R1Exact $start.preflight 'PASS') -or -not $start.cleanExactStart){throw 'R1-SCOPE: start identity differs'}
  $result.head=(Git-R1Scope 'head' @('rev-parse','HEAD')).Trim()
  $result.branch=(Git-R1Scope 'branch' @('branch','--show-current')).Trim()
  if(-not (Test-R1Exact $result.branch $script:R1Branch)){throw 'R1-SCOPE: branch differs'}
  [void](Git-R1Scope 'ancestry' @('merge-base','--is-ancestor',$script:R1Base,'HEAD'))
  [void](Git-R1Scope 'original-ancestry' @('merge-base','--is-ancestor',$script:R1OriginalBase,$script:R1Base))
  $tree=Git-R1Scope 'base-tree' @('ls-tree','-r','-z',$script:R1Base)
  $baseGit=[Collections.Generic.Dictionary[string,object]]::new([StringComparer]::Ordinal)
  foreach($row in ($tree -split [char]0|Where-Object{$_})){
    if($row -cnotmatch '^([0-9]+) blob ([0-9a-f]{40})\t([^\r\n]+)$'){throw 'R1-SCOPE: unsupported base Git entry'}
    $baseGit.Add($Matches[3],@{mode=$Matches[1];blob=$Matches[2]})
  }
  if($baseGit.Count -ne @($baseline.files).Count){throw 'R1-SCOPE: base Git roster differs'}
  foreach($f in $baseline.files){
    if(-not $baseGit.ContainsKey($f.path) -or -not (Test-R1Exact $baseGit[$f.path].mode $f.mode) -or
        -not (Test-R1Exact $baseGit[$f.path].blob $f.gitBlob)){throw ('R1-SCOPE: base Git identity differs '+$f.path)}
  }
  $paths=@((Git-R1Scope 'current-paths' @('ls-files','--cached','--others','--exclude-standard','-z')) -split [char]0|Where-Object{$_})
  $result.paths=$paths
  $result.checked=Assert-R1ScopeFiles $Root $baseline $paths -RequireComplete:$Complete
  $currentStages=Git-R1Scope 'current-stages' @('ls-files','--stage','-z')
  $repairChanged=@((Git-R1Scope 'repair-changed' @('diff','--name-only','-z',$script:R1Base)) -split [char]0|Where-Object{$_})
  $result.gitScope=Assert-R1GitScope $baseline $currentStages $repairChanged
  $result.startup=Assert-LN1StartupWitnesses $Root
  $result.cumulativePaths=@((Git-R1Scope 'cumulative-paths' @('diff','--name-only','-z',$script:R1OriginalBase)) -split [char]0|Where-Object{$_})
  $result.untracked=@((Git-R1Scope 'untracked-paths' @('ls-files','--others','--exclude-standard','-z')) -split [char]0|Where-Object{$_})
  if($result.cumulativePaths.Count -eq 0){throw 'R1-SCOPE: vacuous original-base surface'}
  $result.success=$true
}catch{$result.failure=$_.Exception.Message}
finally{
  $errors=[Collections.Generic.List[string]]::new()
  foreach($p in $pins){try{Assert-R1Pin $p}catch{$errors.Add($_.Exception.Message)}}
  $result.integrity=@{success=($errors.Count -eq 0);errors=@($errors.ToArray());checked=$pins.Count}
  $result.success=$result.success -and $result.integrity.success
  $result.pins=@($pins.ToArray());$result.stages=@($stages.ToArray());$result.completedUtc=[DateTime]::UtcNow.ToString('o')
  Write-R1Json (Join-Path $run 'RESULT.json') $result
}
Write-Output ('R1-SCOPE success='+$result.success+' receipt='+$run)
if(-not $result.success){Write-Output $result.failure;exit 1}
