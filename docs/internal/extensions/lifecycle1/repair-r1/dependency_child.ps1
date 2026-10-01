param([string]$SpecPath,[string]$RepositoryRoot,[string]$EvidenceRoot)
Set-StrictMode -Version Latest
$ErrorActionPreference='Stop'
$utf8=[Text.UTF8Encoding]::new($false,$true)
$spec=Get-Content -LiteralPath $SpecPath -Raw|ConvertFrom-Json
[void][IO.Directory]::CreateDirectory($EvidenceRoot)
# LIFE-1-R3: once the evidence directory exists, every exit path writes
# receipt.json with the stage error, each independent entry-pin comparison and
# each cleanup error recorded separately.
$productionPath=Join-Path $RepositoryRoot 'scripts/lifecycle_dependency_replay.ps1'
$registryPath=Join-Path $RepositoryRoot 'scripts/lifecycle_dependency_cases.json'
$scriptPath=$productionPath
$entryPins=[ordered]@{}
$sourceHash=$null
$registryTarget=$null;$registryChallenge=$null
$key='LIFE1_DEPENDENCY_SELECTOR'
$initial=[Environment]::GetEnvironmentVariables('Process')
$savedError=[Console]::Error
$record=$null
$stageError=$null;$stageRecord=$null
$integrityErrors=[Collections.Generic.List[string]]::new()
$cleanupErrors=[Collections.Generic.List[string]]::new()
$pinChecks=[Collections.Generic.List[object]]::new()
$passed=$false
$durableFailed=$false
try {
$sourceHash=(Get-FileHash -LiteralPath $productionPath).Hash
$entryPins[$productionPath]=$sourceHash
$entryPins[$registryPath]=(Get-FileHash -LiteralPath $registryPath).Hash
if($spec.kind -ceq 'dependency-registry') {
  $scratchRoot=Join-Path $EvidenceRoot 'source-root'
  [void][IO.Directory]::CreateDirectory((Join-Path $scratchRoot 'scripts'))
  $copy=Join-Path $scratchRoot 'scripts/lifecycle_dependency_replay.ps1'
  [IO.File]::WriteAllBytes($copy,[IO.File]::ReadAllBytes($scriptPath))
  $originalRegistryBytes=[IO.File]::ReadAllBytes((Join-Path $RepositoryRoot 'scripts/lifecycle_dependency_cases.json'))
  $registryText=$utf8.GetString($originalRegistryBytes)
  $registry=$registryText|ConvertFrom-Json
  switch($spec.mutation) {
    'missing-middle' {$registry.cases=@($registry.cases|Where-Object {$_.id -cne 'D13_ALIAS_PHYSICAL'})}
    'duplicate-middle' {$registry.cases[12].id=$registry.cases[11].id}
    'unknown-middle' {$registry.cases[12].id='D99_UNKNOWN'}
    'unused-edit' {
      $idOffset=$registryText.IndexOf('"id": "D13_ALIAS_PHYSICAL"',[StringComparison]::Ordinal)
      $token='"after": "'
      $start=$registryText.IndexOf($token,$idOffset,[StringComparison]::Ordinal)
      if($idOffset -lt 0 -or $start -lt 0){throw 'CONTROL: unique D22 edit anchor absent'}
      $cursor=$start+$token.Length;$escaped=$false
      while($cursor -lt $registryText.Length) {
        $char=$registryText[$cursor]
        if(-not $escaped -and $char -ceq '"'){break}
        if(-not $escaped -and $char -ceq '\'){$escaped=$true}else{$escaped=$false}
        $cursor++
      }
      if($cursor -ge $registryText.Length){throw 'CONTROL: D22 JSON string end absent'}
      $registryChallenge=$utf8.GetBytes($registryText.Insert($cursor,' '))
      $changed=$utf8.GetString($registryChallenge)|ConvertFrom-Json
      if($changed.cases[12].edits[0].after -cne ($registry.cases[12].edits[0].after+' ')){throw 'CONTROL: D22 intended value did not change exactly'}
      if($registryChallenge.Length -ne $originalRegistryBytes.Length+1){throw 'CONTROL: D22 changed unrelated serialization'}
    }
    default {throw 'CONTROL: unknown registry mutation'}
  }
  if($null -eq $registryChallenge){$registryChallenge=$utf8.GetBytes(($registry|ConvertTo-Json -Depth 40))}
  $registryTarget=Join-Path $scratchRoot 'scripts/lifecycle_dependency_cases.json'
  [IO.File]::WriteAllBytes($registryTarget,$originalRegistryBytes)
  $scriptPath=$copy
}
$params=@{}
foreach($property in $spec.parameters.PSObject.Properties){$params[$property.Name]=$property.Value}
$message=$null;$errorId=$null;$output=@();$exit=0
$err=[IO.StringWriter]::new()
$positive=$null
  if($spec.ambient.present){[Environment]::SetEnvironmentVariable($key,[string]$spec.ambient.value,'Process')}
  else{[Environment]::SetEnvironmentVariable($key,[NullString]::Value,'Process')}
  $before=[Environment]::GetEnvironmentVariables('Process')
  # Execute P through the same actual script/root before installing Q. The
  # registry P uses its exact original bytes, including its terminal newline.
  $positiveParams=@{SelectorProbeOnly=$true}
  $positiveIds=@((Get-Content -LiteralPath (Join-Path $RepositoryRoot 'scripts/lifecycle_dependency_cases.json') -Raw|ConvertFrom-Json).cases.id)
  $positiveEnv=$null
  if($spec.ambient.present){$positiveEnv='id:D01_CONSTRUCTION';$positiveIds=@('D01_CONSTRUCTION')}
  $positiveWriter=[IO.StringWriter]::new()
  try {
    if($null -eq $positiveEnv){[Environment]::SetEnvironmentVariable($key,[NullString]::Value,'Process')}
    else{[Environment]::SetEnvironmentVariable($key,$positiveEnv,'Process')}
    [Console]::SetError($positiveWriter)
    $global:LASTEXITCODE=0
    $positiveOutput=@(& $scriptPath @positiveParams)
    $positive=[ordered]@{exit=$LASTEXITCODE;stdout=$positiveOutput;stderr=$positiveWriter.ToString();scriptPath=$scriptPath;selector=$positiveEnv}
  } finally {
    [Console]::SetError($savedError)
    if($before.Contains($key)){[Environment]::SetEnvironmentVariable($key,[string]$before[$key],'Process')}
    else{[Environment]::SetEnvironmentVariable($key,[NullString]::Value,'Process')}
  }
  [IO.File]::WriteAllText((Join-Path $EvidenceRoot 'positive.json'),($positive|ConvertTo-Json -Depth 20),$utf8)
  if($positive.exit -ne 0 -or $positive.stderr -cne '' -or $positive.stdout.Count -ne 1 -or
     $positive.stdout[0] -cne ('LIFE1-DEPENDENCY SELECT '+($positiveIds -join ','))){throw 'CONTROL: exact same-root positive boundary failed'}
  if($null -ne $registryTarget){[IO.File]::WriteAllBytes($registryTarget,$registryChallenge)}
  try {
    [Console]::SetError($err)
    $global:LASTEXITCODE=0
    if($spec.id -ceq 'D12_DUPLICATE_ARGUMENT') {
      $output=@(& $scriptPath -OnlyCase D01_CONSTRUCTION -OnlyCase D01_CONSTRUCTION -SelectorProbeOnly)
    } else {$output=@(& $scriptPath @params)}
    $exit=$LASTEXITCODE
  } catch {$message=$_.Exception.Message;$errorId=$_.FullyQualifiedErrorId;$exit=1}
  finally {[Console]::SetError($savedError)}
  $after=[Environment]::GetEnvironmentVariables('Process')
  $restored=$before.Contains($key) -eq $after.Contains($key) -and (-not $before.Contains($key) -or [string]$before[$key] -ceq [string]$after[$key])
  $stderr=$err.ToString()
  $expected=$spec.expected
  if($spec.id -ceq 'D13_PRESENT_EMPTY' -and $PSVersionTable.PSEdition -ceq 'Desktop'){$expected=$spec.legacyExpected}
  $record=[ordered]@{id=$spec.id;sourcePath=$scriptPath;sourceSha256=$sourceHash;copiedSourceSha256=(Get-FileHash -LiteralPath $scriptPath).Hash;
    shell=(Get-Process -Id $PID).Path;version=$PSVersionTable.PSVersion.ToString();dotnet=[Environment]::Version.ToString();
    parameters=$params;ambient=$spec.ambient;actualEnvironmentPresent=$before.Contains($key);exit=$exit;stdout=$output;stderr=$stderr;
    exception=$message;errorId=$errorId;restored=$restored;passed=$false;positive=$positive;
    stderrRepresentation='Exact Console.Error captured text, including all trailing newlines; no added filtering.'}
  [IO.File]::WriteAllText((Join-Path $EvidenceRoot 'receipt.json'),($record|ConvertTo-Json -Depth 30),$utf8)
  if(-not $restored -or $exit -ne $expected.exit){throw 'CONTROL: dependency exit/restoration mismatch'}
  if($spec.id -ceq 'D12_DUPLICATE_ARGUMENT') {
    if($output.Count -ne 0 -or $stderr -cne '' -or $errorId -cne 'ParameterAlreadyBound,lifecycle_dependency_replay.ps1'){throw 'CONTROL: wrong duplicate parameter binding'}
  } elseif($null -ne $message){throw ('CONTROL: unexpected boundary exception '+$message)}
  elseif($expected.exit -eq 0) {
    if($stderr -cne '' -or $output.Count -ne 1 -or $output[0] -cne $expected.output){throw 'CONTROL: dependency focused/full registry selection mismatch'}
  } elseif($output.Count -ne 0 -or $stderr -cne ($expected.error+[Environment]::NewLine)){throw 'CONTROL: wrong or mixed dependency diagnostic'}
  $passed=$true
} catch {$stageError=$_.Exception.Message;$stageRecord=$_}
finally {
  try{[Console]::SetError($savedError)}catch{$cleanupErrors.Add('CONTROL-CLEANUP: Console.Error restoration: '+$_.Exception.Message)}
  try {
    if($initial.Contains($key)){[Environment]::SetEnvironmentVariable($key,[string]$initial[$key],'Process')}
    else{[Environment]::SetEnvironmentVariable($key,[NullString]::Value,'Process')}
  } catch {$cleanupErrors.Add('CONTROL-CLEANUP: selector environment restoration: '+$_.Exception.Message)}
  # Independent integrity on every exit path: each captured entry pin in its own guard.
  foreach($path in @($productionPath,$registryPath)){
    $entry=if($entryPins.Contains($path)){$entryPins[$path]}else{$null}
    $final=$null;$status='not-captured'
    if($null -ne $entry){
      $status='verified'
      $label=if($path -ceq $productionPath){'production source'}else{'production registry'}
      try{$final=(Get-FileHash -LiteralPath $path).Hash}catch{$status='unreadable-final';$integrityErrors.Add('CONTROL: '+$label+' final hash failed: '+$_.Exception.Message)}
      if($null -ne $final -and $final -cne $entry){$status='changed';$integrityErrors.Add('CONTROL: '+$label+' changed')}
    }
    $pinChecks.Add([ordered]@{path=$path;entrySha256=$entry;finalSha256=$final;status=$status})
  }
  $passed=$passed -and $null -eq $stageError -and $integrityErrors.Count -eq 0 -and $cleanupErrors.Count -eq 0
  $finalization=[ordered]@{schema='life1-r3-finalization-v1';verdict=$(if($passed){'pass'}else{'fail'});stageError=$stageError
    integrityErrors=@($integrityErrors.ToArray());cleanupErrors=@($cleanupErrors.ToArray());pinChecks=@($pinChecks.ToArray())
    entryPinCount=$entryPins.Count;verifiedPinCount=@($pinChecks|Where-Object {$_.status -ceq 'verified'}).Count}
  if($null -eq $record){$record=[ordered]@{id=$spec.id;sourcePath=$scriptPath;sourceSha256=$sourceHash;passed=$false}}
  $record.passed=$passed
  $record.finalization=$finalization
  try{[IO.File]::WriteAllText((Join-Path $EvidenceRoot 'receipt.json'),($record|ConvertTo-Json -Depth 30),$utf8)}
  catch{$durableFailed=$true;$passed=$false;[Console]::Error.WriteLine('CONTROL: durable receipt write failed: '+$_.Exception.Message)}
}
if(-not $passed){
  foreach($message in @($integrityErrors)+@($cleanupErrors)){[Console]::Error.WriteLine($message)}
  if($null -ne $stageRecord){throw $stageRecord}
  exit 1
}
Write-Output ('L1R1-CONTROL|'+$spec.id+'|PASS')
