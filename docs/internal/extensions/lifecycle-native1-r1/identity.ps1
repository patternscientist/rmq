# R1 consumers use the unchanged raw-process/contract helpers.
$script:R1Root=[IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../../../..'))
. (Join-Path $script:R1Root 'scripts/lifecycle_native_identity.ps1')
$script:R1Utf8=[Text.UTF8Encoding]::new($false,$true)
$script:R1Base='c52c453a2f0f49c568886f502687e4d0667838e9'
$script:R1OriginalBase='3dbdebedcc6ba6b2a864df0d46dcc09ccaaa7536'
$script:R1Branch='codex/life-native-1-certification-repair'
$script:R1Old=@('scripts/lifecycle_native_build.ps1',
  'docs/internal/extensions/lifecycle-native1/native_controls.ps1',
  'docs/internal/extensions/lifecycle-native1/native_clients.ps1',
  'docs/internal/extensions/lifecycle-native1/native_selector_controls.ps1')
$script:R1Ledger='docs/internal/WORKFLOW_DESIGN_DECISIONS.md'
$script:R1New=@('START.json','BASE_IDENTITY.json','REPAIR_CASES.json','controls.ps1','identity.ps1',
  'scope_check.ps1','final_checks.ps1','NATIVE_EXPECTATIONS.json','REUSE_APPLICABILITY.json',
  'REPORT.md','ACCEPTANCE_MATRIX.md','COMMANDS.md','GUIDE.md','VERIFICATION_PLAN.md') |
  ForEach-Object{'docs/internal/extensions/lifecycle-native1-r1/'+$_}
function Test-R1Exact($Actual,$Expected){
  return $Actual -is [string] -and $Expected -is [string] -and
    [string]::Equals($Actual,$Expected,[StringComparison]::Ordinal)
}
function Write-R1Json([string]$Path,$Value){
  [IO.File]::WriteAllText($Path,($Value|ConvertTo-Json -Depth 80),$script:R1Utf8)
}
function Quote-R1([string]$Text){return "'"+$Text.Replace("'","''")+"'"}
function Assert-R1Pin($Pin){
  $now=Get-LN1Pin $Pin.path
  if($now.bytes -ne $Pin.bytes -or ($Pin.sha256 -isnot [string]) -or $Pin.sha256 -cnotmatch '\A[0-9a-fA-F]{64}\z' -or -not [string]::Equals($now.sha256,$Pin.sha256,[StringComparison]::OrdinalIgnoreCase)){
    throw ('R1-IDENTITY: changed pin '+$Pin.path)
  }
}
function Remove-R1Scratch([string]$Scratch,[string]$Run){
  $full=[IO.Path]::GetFullPath($Scratch)
  $expected=[IO.Path]::GetFullPath((Join-Path $Run 'disposable'))
  if(-not (Test-R1Exact $full $expected)){throw 'R1-CLEANUP: not the owned disposable directory'}
  if([IO.Directory]::Exists($full)){
    foreach($entry in @((Get-Item -LiteralPath $full))+@(Get-ChildItem -LiteralPath $full -Recurse -Force)){
      if($entry.Attributes -band [IO.FileAttributes]::ReparsePoint){throw 'R1-CLEANUP: reparse point'}
    }
    Remove-Item -LiteralPath $full -Recurse -Force
  }
  if([IO.Directory]::Exists($full)){throw 'R1-CLEANUP: scratch remains'}
}
function Assert-R1ScopeFiles([string]$Root,$Baseline,[string[]]$Paths,[switch]$RequireComplete){
  if(-not (Test-R1Exact $Baseline.base $script:R1Base) -or
      -not (Test-R1Exact $Baseline.originalBase $script:R1OriginalBase)){
    throw 'R1-SCOPE: baseline base identity differs'
  }
  $known=[Collections.Generic.HashSet[string]]::new([StringComparer]::Ordinal)
  $roster=[Collections.Generic.HashSet[string]]::new([StringComparer]::Ordinal)
  foreach($p in $Paths){if(-not $roster.Add($p)){throw 'R1-SCOPE: duplicate current path'}}
  $changed=[Collections.Generic.List[object]]::new()
  foreach($old in $Baseline.files){
    if(-not $known.Add($old.path)){throw 'R1-SCOPE: duplicate baseline path'}
    if(-not $roster.Contains($old.path)){throw ('R1-SCOPE: missing original path '+$old.path)}
    $path=Join-Path $Root $old.path
    if(-not [IO.File]::Exists($path)){throw ('R1-SCOPE: missing original file '+$old.path)}
    $bytes=[IO.File]::ReadAllBytes($path);$hash=Get-LN1BytesHash $bytes
    if($bytes.Length -eq $old.rawBytes -and [string]::Equals($hash,$old.rawSHA256,[StringComparison]::OrdinalIgnoreCase)){continue}
    if(Test-R1Exact $old.path $script:R1Ledger){
      if($bytes.Length -lt $old.rawBytes){throw 'R1-SCOPE: ledger prefix shortened'}
      $prefix=[byte[]]::new($old.rawBytes);[Array]::Copy($bytes,$prefix,$prefix.Length)
      if(-not [string]::Equals((Get-LN1BytesHash $prefix),$old.rawSHA256,[StringComparison]::OrdinalIgnoreCase)){
        throw 'R1-SCOPE: ledger prefix rewritten'
      }
    }elseif(-not [Linq.Enumerable]::Contains([string[]]$script:R1Old,[string]$old.path,[StringComparer]::Ordinal)){
      throw ('R1-SCOPE: protected raw bytes changed '+$old.path)
    }
    $changed.Add(@{path=$old.path;pin=(Get-LN1Pin $path)})
  }
  $added=[Collections.Generic.List[object]]::new()
  foreach($p in $Paths){
    if($known.Contains($p)){continue}
    if(-not [Linq.Enumerable]::Contains([string[]]$script:R1New,$p,[StringComparer]::Ordinal)){
      throw ('R1-SCOPE: new path outside exact roster '+$p)
    }
    $added.Add(@{path=$p;pin=(Get-LN1Pin (Join-Path $Root $p))})
  }
  if($RequireComplete){foreach($p in $script:R1New){if(-not $roster.Contains($p)){throw ('R1-SCOPE: missing required new path '+$p)}}}
  return @{checkedBaseFiles=$known.Count;changes=@($changed.ToArray());newFiles=@($added.ToArray());
    contract=(Assert-LN1FrozenContract $Root)}
}
function Assert-R1GitScope($Baseline,[string]$StageText,[string[]]$ChangedPaths){
  $allowed=[Collections.Generic.HashSet[string]]::new([StringComparer]::Ordinal)
  foreach($p in @($script:R1Old)+@($script:R1Ledger)+@($script:R1New)){[void]$allowed.Add($p)}
  foreach($p in $ChangedPaths){if(-not $allowed.Contains($p)){throw ('R1-SCOPE: Git change outside exact roster '+$p)}}
  $entries=[Collections.Generic.Dictionary[string,object]]::new([StringComparer]::Ordinal)
  foreach($row in ($StageText -split [char]0|Where-Object{$_})){
    if($row -cnotmatch '\A([0-9]+) ([0-9a-f]{40}) 0\t([^\r\n]+)\z'){throw 'R1-SCOPE: unresolved or malformed current Git entry'}
    if($entries.ContainsKey($Matches[3])){throw 'R1-SCOPE: duplicate current Git entry'}
    $entries.Add($Matches[3],@{mode=$Matches[1];blob=$Matches[2]})
  }
  foreach($f in $Baseline.files){
    if(-not $entries.ContainsKey($f.path)){throw ('R1-SCOPE: missing current Git entry '+$f.path)}
    $entry=$entries[$f.path]
    if(-not (Test-R1Exact $entry.mode $f.mode)){throw ('R1-SCOPE: current Git mode changed '+$f.path)}
    if(-not $allowed.Contains($f.path) -and -not (Test-R1Exact $entry.blob $f.gitBlob)){
      throw ('R1-SCOPE: protected Git blob changed '+$f.path)
    }
    [void]$entries.Remove($f.path)
  }
  foreach($p in $entries.Keys){
    if(-not [Linq.Enumerable]::Contains([string[]]$script:R1New,[string]$p,[StringComparer]::Ordinal) -or
        -not (Test-R1Exact $entries[$p].mode '100644')){throw ('R1-SCOPE: new Git entry outside regular-file roster '+$p)}
  }
  return @{success=$true;protectedBaseModes=$Baseline.files.Count;protectedBaseBlobs=($Baseline.files.Count-$script:R1Old.Count-1);newStaged=$entries.Count;changedPaths=$ChangedPaths}
}
function Assert-R1FinalScope($Capture,[string]$Root,[string]$Head,[string[]]$Paths){
  $stdout=Read-LNExactStream $Capture.spec.stdout
  Assert-LNOuterCapture $Capture $stdout '' 0 'r1-final-scope'
  $match=[regex]::Match($stdout,'\AR1-SCOPE success=True receipt=([^\r\n\x00]+)\r\n\z')
  if(-not $match.Success){throw 'R1-FINAL-SCOPE: unexpected complete output language'}
  $dir=$match.Groups[1].Value;$stamp=[IO.Path]::GetFileName($dir)
  if($stamp -cnotmatch '\A[0-9]{8}T[0-9]{9}-[0-9a-f]{8}\z' -or
      -not (Test-R1Exact $dir (Join-Path $Root ('.lake/lifecycle-native1-r1/scope/'+$stamp)))){
    throw 'R1-FINAL-SCOPE: misplaced receipt'
  }
  $path=Join-Path $dir 'RESULT.json';$pin=Get-LN1Pin $path
  $r=[IO.File]::ReadAllText($path,$script:R1Utf8)|ConvertFrom-Json
  if(-not (Test-R1Exact $r.schema 'lifecycle-native1-r1-scope-v1') -or $r.success -ne $true -or
      $r.integrity.success -ne $true -or $r.complete -ne $true -or $null -ne $r.failure -or
      -not (Test-R1Exact $r.base $script:R1Base) -or -not (Test-R1Exact $r.originalBase $script:R1OriginalBase) -or
      -not (Test-R1Exact $r.branch $script:R1Branch) -or -not (Test-R1Exact $r.head $Head) -or
      $r.checked.checkedBaseFiles -ne 3930 -or $r.checked.contract.count -ne 55 -or
      $r.startup.success -ne $true -or $r.startup.exactInsertions -ne 5 -or
      $r.gitScope.success -ne $true -or $r.gitScope.protectedBaseModes -ne 3930 -or $r.gitScope.protectedBaseBlobs -ne 3925){throw 'R1-FINAL-SCOPE: unsuccessful or differently bound receipt'}
  $actual=[Collections.Generic.HashSet[string]]::new([StringComparer]::Ordinal)
  foreach($p in @($r.cumulativePaths)+@($r.untracked)){[void]$actual.Add($p)}
  $expected=[Collections.Generic.HashSet[string]]::new([StringComparer]::Ordinal)
  foreach($p in $Paths){if(-not $expected.Add($p)){throw 'R1-FINAL-SCOPE: duplicate expected path'}}
  if(-not $actual.SetEquals($expected)){throw 'R1-FINAL-SCOPE: complete cumulative path roster differs'}
  foreach($p in $r.pins){Assert-R1Pin $p}
  $baseline=[IO.File]::ReadAllText((Join-Path $Root 'docs/internal/extensions/lifecycle-native1-r1/BASE_IDENTITY.json'),$script:R1Utf8)|ConvertFrom-Json
  $checked=Assert-R1ScopeFiles $Root $baseline @($r.paths) -RequireComplete
  if($checked.changes.Count -ne $r.checked.changes.Count -or $checked.newFiles.Count -ne $r.checked.newFiles.Count){throw 'R1-FINAL-SCOPE: current scope differs'}
  $allPins=@($r.pins)+@($r.checked.changes|ForEach-Object pin)+@($r.checked.newFiles|ForEach-Object pin)
  foreach($p in $allPins){Assert-R1Pin $p}
  return @{pin=$pin;pins=$allPins;checkedBaseFiles=$checked.checkedBaseFiles;newFileCount=$checked.newFiles.Count;paths=$Paths}
}
