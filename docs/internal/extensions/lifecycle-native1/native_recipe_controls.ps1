[CmdletBinding()]
param([ValidateRange(1,60)][int]$DeadlineSeconds=30)
$ErrorActionPreference='Stop'
$root=[IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../../../..'))
. (Join-Path $root 'scripts/lifecycle_native_identity.ps1')
$utf8=[Text.UTF8Encoding]::new($false,$true)
if([Environment]::OSVersion.Platform -ne [PlatformID]::Win32NT){throw 'NATIVE-RECIPE-CONTROLS: Windows path profile required'}
$runner=Join-Path $PSScriptRoot 'native_controls.ps1'
$identity=Join-Path $root 'scripts/lifecycle_native_identity.ps1'
$shell=(Get-Process -Id $PID).Path
$ids=@('complete-three-pins','non-first-hash-change','non-first-length-change','non-first-path-change',
  'reordered-input','exact-duplicate','conflicting-duplicate-hash','conflicting-duplicate-length',
  'ordinal-case-distinct-path','ordinal-format-distinct-path','empty-roster')
$expectedMappingSHA256='0e1b70dffe3931ac57951e30003698818bb134d924c446abb0955b340862f8f3'
$run=Join-Path $root ('.lake/lifecycle-native1/native-recipe-controls/'+[DateTime]::UtcNow.ToString('yyyyMMddTHHmmssfff')+'-'+[Guid]::NewGuid().ToString('N').Substring(0,8))
[void][IO.Directory]::CreateDirectory($run)
$pins=[Collections.Generic.List[object]]::new()
$report=[ordered]@{schema='lifecycle-native1-native-recipe-controls-v1';success=$false;
  boundary='Pure production recipe-function controls on synthetic pin records; paths are metadata, not claims about filesystem aliases or native execution.';
  startedUtc=[DateTime]::UtcNow.ToString('o');expectedIds=$ids;expectedCount=11;expectedMappingSHA256=$expectedMappingSHA256;
  capture=$null;cases=$null;failure=$null;integrity=$null;cleanup=$null;pins=@();
  heavyMutexAcquired=$false;nativeInvocations=0;compilerInvocations=0;
  deadlineSeconds=$DeadlineSeconds;deadlineRationale='One bounded PowerShell child executes eleven pure recipe cases; 30 seconds retains the existing cheap selector-control ceiling.'}
function Pin-RecipeControl([string]$Path){$pin=Get-LN1Pin $Path;$pins.Add($pin);return $pin}
try{
  foreach($path in @($PSCommandPath,$runner,$identity,$shell,
      (Join-Path $root 'scripts/owned_process_tree.ps1'),
      (Join-Path $root 'scripts/packed_native_lifecycle_stream_check.ps1'),
      (Join-Path $root 'scripts/packed_native_lifecycle_storage_replay.ps1'),
      (Join-Path $root 'scripts/packed_native_lifecycle_integrity_check.ps1'))){[void](Pin-RecipeControl $path)}
  $driver=Join-Path $run 'recipe-caller.ps1'
  $casePath=Join-Path $run 'CASES.json'
  $driverText=@'
param([string]$Runner,[string]$Identity,[string]$ResultPath)
Set-StrictMode -Version Latest
$ErrorActionPreference='Stop'
[Console]::OutputEncoding=[Text.UTF8Encoding]::new($false,$true)
. $Identity
$utf8=[Text.UTF8Encoding]::new($false,$true)
$tokens=$null;$errors=$null
$ast=[Management.Automation.Language.Parser]::ParseFile($Runner,[ref]$tokens,[ref]$errors)
if($errors.Count){throw 'NATIVE-RECIPE: runner parser error'}
$functions=@($ast.FindAll({param($n)$n -is [Management.Automation.Language.FunctionDefinitionAst] -and $n.Name -ceq 'Get-ControlRecipe'},$false))
if($functions.Count -ne 1){throw 'NATIVE-RECIPE: exact production function missing or duplicated'}
# Execute the actual pinned function body; never dot-source the campaign entry.
Invoke-Expression $functions[0].Extent.Text
$a=[ordered]@{path='C:\recipe-fixture\a';bytes=10;sha256=('A'*64)}
$b=[ordered]@{path='C:\recipe-fixture\b';bytes=20;sha256=('B'*64)}
$c=[ordered]@{path='C:\recipe-fixture\c';bytes=30;sha256=('C'*64)}
$bh=[ordered]@{path='C:\recipe-fixture\b';bytes=20;sha256=('D'*64)}
$bl=[ordered]@{path='C:\recipe-fixture\b';bytes=21;sha256=('B'*64)}
$bp=[ordered]@{path='C:\recipe-fixture\d';bytes=20;sha256=('B'*64)}
$bc=[ordered]@{path='C:\recipe-fixture\B';bytes=20;sha256=('B'*64)}
$bf=[ordered]@{path=('C:\recipe-fixture\b'+[char]173);bytes=20;sha256=('B'*64)}
# Literal expected row order is independent of production's dictionary/sort.
$ra="C:\recipe-fixture\a`t10`t"+('A'*64)
$rb="C:\recipe-fixture\b`t20`t"+('B'*64)
$rc="C:\recipe-fixture\c`t30`t"+('C'*64)
$rh="C:\recipe-fixture\b`t20`t"+('D'*64)
$rl="C:\recipe-fixture\b`t21`t"+('B'*64)
$rp="C:\recipe-fixture\d`t20`t"+('B'*64)
$rCase="C:\recipe-fixture\B`t20`t"+('B'*64)
$rFormat='C:\recipe-fixture\b'+[char]173+"`t20`t"+('B'*64)
$conflict='NATIVE-CONTROLS: conflicting recipe pin C:\recipe-fixture\b'
$cases=@(
  @{id='complete-three-pins';pins=@($a,$b,$c);rows=@($ra,$rb,$rc);relation='baseline'},
  @{id='non-first-hash-change';pins=@($a,$bh,$c);rows=@($ra,$rh,$rc);relation='different'},
  @{id='non-first-length-change';pins=@($a,$bl,$c);rows=@($ra,$rl,$rc);relation='different'},
  @{id='non-first-path-change';pins=@($a,$bp,$c);rows=@($ra,$rc,$rp);relation='different'},
  @{id='reordered-input';pins=@($c,$a,$b);rows=@($ra,$rb,$rc);relation='same'},
  @{id='exact-duplicate';pins=@($a,$b,$c,$b);rows=@($ra,$rb,$rc);relation='same'},
  @{id='conflicting-duplicate-hash';pins=@($a,$b,$c,$bh);error=$conflict},
  @{id='conflicting-duplicate-length';pins=@($a,$b,$c,$bl);error=$conflict},
  @{id='ordinal-case-distinct-path';pins=@($a,$b,$c,$bc);rows=@($rCase,$ra,$rb,$rc);relation='different'},
  @{id='ordinal-format-distinct-path';pins=@($a,$b,$c,$bf);rows=@($ra,$rb,$rFormat,$rc);relation='different'},
  @{id='empty-roster';pins=@();error='NATIVE-CONTROLS: empty recipe pin roster'}
)
$mapping=@(foreach($case in $cases){[ordered]@{
  id=$case.id;
  pins=@($case.pins|ForEach-Object{[ordered]@{path=$_.path;bytes=$_.bytes;sha256=$_.sha256}});
  expectedRows=$(if($case.ContainsKey('rows')){@($case.rows)}else{@()});
  relation=$(if($case.ContainsKey('relation')){$case.relation}else{$null});
  error=$(if($case.ContainsKey('error')){$case.error}else{$null})
}})
$mappingText=([ordered]@{schema='lifecycle-native1-native-recipe-case-mapping-v1';cases=$mapping}|ConvertTo-Json -Depth 12 -Compress)+"`n"
$mappingSHA256=Get-LN1BytesHash ($utf8.GetBytes($mappingText))
if($cases.Count -ne 11 -or $mappingSHA256 -cne '0e1b70dffe3931ac57951e30003698818bb134d924c446abb0955b340862f8f3'){
  throw 'NATIVE-RECIPE: complete ordered input/oracle mapping differs'
}
$baseline=$null;$results=[Collections.Generic.List[object]]::new()
foreach($case in $cases){
  $actual=$null;$diagnostic=$null
  try{$actual=Get-ControlRecipe @($case.pins)}catch{$diagnostic=$_.Exception.Message}
  if($case.ContainsKey('error')){
    if($null -ne $actual -or -not [string]::Equals($diagnostic,$case.error,[StringComparison]::Ordinal)){
      throw ('NATIVE-RECIPE: exact rejection differs '+$case.id)
    }
    $results.Add([ordered]@{id=$case.id;passed=$true;expectedVerdict='reject';actualDiagnostic=$diagnostic;expectedDiagnostic=$case.error})
  }else{
    if($null -ne $diagnostic -or $null -eq $actual){throw ('NATIVE-RECIPE: unexpected rejection '+$case.id+' '+$diagnostic)}
    $text=($case.rows -join "`n")+"`n"
    $expectedHash=([Convert]::ToHexString([Security.Cryptography.SHA256]::HashData($utf8.GetBytes($text)))).ToLowerInvariant()
    $returnedRows=@($actual.pins|ForEach-Object{$_.path+"`t"+$_.bytes.ToString([Globalization.CultureInfo]::InvariantCulture)+"`t"+$_.sha256})
    if($actual.schema -cne 'lifecycle-native1-control-input-recipe-v1' -or
        $actual.sourcePinCount -ne $case.pins.Count -or $actual.uniquePinCount -ne $case.rows.Count -or
        $actual.duplicatePinCount -ne ($case.pins.Count-$case.rows.Count) -or $actual.pins.Count -ne $case.rows.Count -or
        -not [string]::Equals($actual.text,$text,[StringComparison]::Ordinal) -or
        -not [string]::Equals(($returnedRows -join "`n"),($case.rows -join "`n"),[StringComparison]::Ordinal) -or
        $actual.sha256 -cne $expectedHash){throw ('NATIVE-RECIPE: complete exact recipe differs '+$case.id)}
    if($case.relation -ceq 'baseline'){$baseline=$expectedHash}
    elseif(($case.relation -ceq 'same' -and $actual.sha256 -cne $baseline) -or
        ($case.relation -ceq 'different' -and $actual.sha256 -ceq $baseline)){
      throw ('NATIVE-RECIPE: fingerprint sensitivity differs '+$case.id)
    }
    $results.Add([ordered]@{id=$case.id;passed=$true;expectedVerdict='accept';relation=$case.relation;
      expectedText=$text;expectedSHA256=$expectedHash;actual=$actual})
  }
  Write-Output ('NATIVE-RECIPE CASE PASS '+$case.id)
}
[IO.File]::WriteAllText($ResultPath,([ordered]@{schema='lifecycle-native1-native-recipe-case-results-v1';success=$true;
  mappingSHA256=$mappingSHA256;
  functionSource=(Get-LN1Pin $Runner);functionTextSHA256=(Get-LN1BytesHash ($utf8.GetBytes($functions[0].Extent.Text)));
  caseCount=$results.Count;cases=@($results.ToArray())}|ConvertTo-Json -Depth 20),$utf8)
'@
  [IO.File]::WriteAllText($driver,$driverText,$utf8)
  [void](Pin-RecipeControl $driver)
  $report.capture=Invoke-LNStreamCapture $root $shell @('-NoProfile','-File',$driver,'-Runner',$runner,'-Identity',$identity,'-ResultPath',$casePath) $root (Join-Path $run 'capture') $DeadlineSeconds 'native-recipe-controls'
  foreach($pin in $report.capture.raw){[void](Pin-RecipeControl $pin.path)}
  $expected=(@($ids|ForEach-Object{'NATIVE-RECIPE CASE PASS '+$_}) -join "`r`n")+"`r`n"
  Assert-LNOuterCapture $report.capture $expected '' 0 'native-recipe-controls'
  $report.cases=Pin-RecipeControl $casePath
  $actual=[IO.File]::ReadAllText($casePath,$utf8)|ConvertFrom-Json
  if($actual.schema -cne 'lifecycle-native1-native-recipe-case-results-v1' -or -not $actual.success -or
      $actual.mappingSHA256 -cne $expectedMappingSHA256 -or
      $actual.caseCount -ne 11 -or (@($actual.cases.id) -join '|') -cne ($ids -join '|') -or
      @($actual.cases|Where-Object{-not $_.passed}).Count){throw 'NATIVE-RECIPE-CONTROLS: complete case result differs'}
  $report.success=$true
}catch{$report.failure=$_.Exception.Message}
finally{
  $errors=[Collections.Generic.List[string]]::new()
  foreach($pin in $pins){try{$now=Get-LN1Pin $pin.path;if($now.bytes -ne $pin.bytes -or $now.sha256 -cne $pin.sha256){throw ('changed pin '+$pin.path)}}catch{$errors.Add($_.Exception.Message)}}
  $report.integrity=@{attempted=$true;success=($errors.Count -eq 0);checkedPins=$pins.Count;errors=@($errors.ToArray());liveSourceWrites=0}
  $report.cleanup=@{attempted=$true;success=$true;disposableWrites=0;environmentWrites=0;retainedEvidence=$run}
  if($errors.Count){$report.success=$false}
  $report.pins=@($pins.ToArray());$report.completedUtc=[DateTime]::UtcNow.ToString('o')
  [IO.File]::WriteAllText((Join-Path $run 'RESULT.json'),($report|ConvertTo-Json -Depth 30),$utf8)
}
Write-Output ('NATIVE-RECIPE-CONTROLS evidence='+$run)
if(-not $report.success){Write-Output ('NATIVE-RECIPE-CONTROLS FAIL '+$report.failure);exit 1}
Write-Output ('NATIVE-RECIPE-CONTROLS PASS cases='+$ids.Count)
