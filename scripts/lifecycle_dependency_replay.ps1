#!/usr/bin/env pwsh
[CmdletBinding()]
param(
  [AllowEmptyString()][string]$OnlyCase,
  [switch]$SelectorProbeOnly,
  [switch]$SelfTestOnly,
  [switch]$StartupOnly,
  [ValidateRange(1,86400)][int]$DeadlineSeconds=120,
  [ValidateRange(1024,1073741824)][int]$OutputLimitBytes=16777216,
  [string]$EvidenceDirectory='.lake/lifecycle-dependency'
)

Set-StrictMode -Version Latest
$ErrorActionPreference='Stop'
$root=[IO.Path]::GetFullPath((Join-Path $PSScriptRoot '..'))
$utf8=[Text.UTF8Encoding]::new($false,$true)
$ids=@('D01_CONSTRUCTION','D02_RETAINED','D03_SAFETY','D04_PHYSICAL','D05_EXECUTABLE',
 'D06_REUSABLE','D07_UNIFORM','D08_DELETE_PHYSICAL','D09_SIBLING_PHYSICAL','D10_PUBLIC_TRUE',
 'D11_WORD_TRUE','D12_COMPARISON_TRUE','D13_ALIAS_PHYSICAL','D14_RETAINED_COST','D15_CODE_FETCH_DROP',
 'D16_PREFIX_RESOURCES','D17_READY_BANK','D18_STORE_TRUE','D19_ACCEPT_COMMENT','D20_ACCEPT_IDENTITY',
 'P01_OUTPUT','P02_METADATA','P03_COPY','P04_RELEASES','P05_PUBLIC_TRUE','P06_ACCEPT_IDENTITY')
$registryHash='4c9c7a4259808bb64c74656fd52559752e76f02834f2ac8567f5830968a5b80d'
$registryPath=Join-Path $root 'scripts/lifecycle_dependency_cases.json'
$stages=[Collections.Generic.List[object]]::new()
$results=[Collections.Generic.List[object]]::new()
$mutex=$null
$locked=$false
$evidence=$null
$shadow=$null
$baseline=@()
$completed=$false
$restored=$false
$stageError=$null
$integrityError=$null
$cleanupError=$null

function Hash-Bytes([byte[]]$bytes) {
  $hasher = [Security.Cryptography.SHA256]::Create()
  try { return ([BitConverter]::ToString($hasher.ComputeHash($bytes))).Replace('-', '').ToLowerInvariant() }
  finally { $hasher.Dispose() }
}
function Hash-File([string]$path) { return Hash-Bytes ([IO.File]::ReadAllBytes($path)) }
function Read-Normalized([string]$path) { return [IO.File]::ReadAllText($path,$utf8).Replace("`r`n","`n") }
function Write-Json([string]$name,[object]$value) {
  [IO.File]::WriteAllText((Join-Path $evidence $name),($value|ConvertTo-Json -Depth 40),$utf8)
}
function Assert-Registry([object]$document,[string]$hash) {
  if($document.version -cne 1 -or @($document.cases).Count -ne $ids.Count){throw 'LIFE1-REGISTRY: exact nonempty case count required'}
  for($i=0;$i -lt $ids.Count;$i++) {
    $c=$document.cases[$i]
    if($c.id -cne $ids[$i]){throw 'LIFE1-REGISTRY: missing, duplicate, unknown or reordered ID'}
    $prov=$c.id.StartsWith('P',[StringComparison]::Ordinal)
    $producer=if($prov){'RMQ/Core/WordRAM/Lifecycle/Provenance.lean'}else{'RMQ/Core/WordRAM/Lifecycle/Capstone.lean'}
    $consumer=if($prov){'scripts/lifecycle_provenance_contract.lean'}else{'RMQ/Validation/LifecycleContract.lean'}
    if($c.producer -cne $producer -or $c.consumer -cne $consumer){throw 'LIFE1-REGISTRY: producer/consumer mapping mismatch'}
    if($c.expected -cnotin @('accept','reject')){throw 'LIFE1-REGISTRY: expected verdict missing'}
    if($c.expected -ceq 'reject' -and (@($c.edits).Count -eq 0 -or @($c.diagnostics).Count -eq 0)){
      throw 'LIFE1-REGISTRY: vacuous reject case'
    }
    if($c.expected -ceq 'accept' -and @($c.diagnostics).Count -ne 0){throw 'LIFE1-REGISTRY: accept case has error surface'}
    foreach($edit in @($c.edits)) {
      if($edit.before -isnot [string] -or $edit.after -isnot [string] -or
         [string]::IsNullOrEmpty($edit.before) -or $edit.before -ceq $edit.after){throw 'LIFE1-REGISTRY: vacuous or malformed edit'}
    }
    foreach($d in @($c.diagnostics)) {
      if($d.surface -cnotmatch '^(publicContract|producerContract|checkC[0-9]{2}_[a-z]+|checkP01)$' -or
         $d.errorClass -cnotin @('type-mismatch','destructure','invalid-field') -or $d.count -ne 1){
        throw 'LIFE1-REGISTRY: invalid exact diagnostic mapping'
      }
    }
  }
  if($hash -cne $registryHash){throw 'LIFE1-REGISTRY: frozen normalized-byte SHA256 mismatch'}
}
function Select-Cases([object[]]$cases,[bool]$wasBound,[string]$selector,[object]$environment) {
  if($wasBound -and $null -ne $environment){throw 'LIFE1-SELECTOR: duplicate parameter/environment channels'}
  if($null -ne $environment) {
    if(-not $environment.StartsWith('id:',[StringComparison]::Ordinal)){throw 'LIFE1-SELECTOR: environment requires id: prefix'}
    $selector=$environment.Substring(3); $wasBound=$true
  }
  if(-not $wasBound){return @($cases)}
  if([string]::IsNullOrWhiteSpace($selector)){throw 'LIFE1-SELECTOR: explicitly empty selector'}
  if($selector -cnotmatch '^[DP][0-9]{2}_[A-Z][A-Z0-9_]*$'){throw 'LIFE1-SELECTOR: malformed selector'}
  $selected=@($cases|Where-Object {$_.id -ceq $selector})
  if($selected.Count -ne 1){throw 'LIFE1-SELECTOR: unknown selector'}
  return $selected
}
function Apply-Edits([string]$source,[object]$case) {
  $changed=$source
  foreach($edit in @($case.edits)) {
    if([regex]::Matches($changed,[regex]::Escape($edit.before)).Count -ne 1){throw "LIFE1-ANCHOR: $($case.id) source fragment not unique"}
    $changed=$changed.Replace($edit.before,$edit.after)
  }
  if($case.expected -ceq 'reject' -and $changed -ceq $source){throw 'LIFE1-MUTATION: negative source unchanged'}
  return $changed
}
function Surface-Ranges([string]$source) {
  $lines=$source.Split("`n")
  $ranges=@{}
  for($i=0;$i -lt $lines.Count;$i++) {
    if($lines[$i] -cmatch '^theorem ([A-Za-z0-9_]+)\b') {
      $name=$Matches[1]; $end=$lines.Count
      for($j=$i+1;$j -lt $lines.Count;$j++) {
        if($lines[$j] -cmatch '^(theorem |def |structure |end |omit )'){$end=$j;break}
      }
      $ranges[$name]=@(($i+1),$end)
    }
  }
  return $ranges
}
function Assert-Accept([object]$r) {
  if($r.TimedOut -or $r.OutputLimitExceeded -or $r.ExitCode -ne 0 -or
     @($r.StandardOutput).Count -ne 0 -or @($r.StandardError).Count -ne 0){
    throw 'LIFE1-STAGE: expected clean compiler acceptance'
  }
}
function Assert-Reject([object]$r,[object]$case,[hashtable]$ranges) {
  if($r.TimedOut -or $r.OutputLimitExceeded -or $r.ExitCode -ne 1 -or @($r.StandardError).Count -ne 0){
    throw 'LIFE1-DIAGNOSTIC: expected exit 1, complete stdout and empty stderr'
  }
  $headers=@()
  foreach($line in @($r.StandardOutput)) {
    try {$diagnostic=ConvertFrom-Json -InputObject $line -ErrorAction Stop}
    catch {throw 'LIFE1-DIAGNOSTIC: non-JSON compiler output'}
    foreach($property in @('fileName','pos','severity','data')) {
      if($null -eq $diagnostic.PSObject.Properties[$property]){throw 'LIFE1-DIAGNOSTIC: non-diagnostic JSON output'}
    }
    if($diagnostic.fileName -isnot [string] -or $diagnostic.data -isnot [string] -or
       $null -eq $diagnostic.pos.PSObject.Properties['line']){throw 'LIFE1-DIAGNOSTIC: malformed diagnostic JSON'}
    $headers+=@($diagnostic)
  }
  $expected=@($case.diagnostics)
  if($headers.Count -ne $expected.Count -or $headers.Count -eq 0){
    throw 'LIFE1-DIAGNOSTIC: exact error count mismatch'
  }
  $used=[Collections.Generic.HashSet[string]]::new([StringComparer]::Ordinal)
  foreach($header in $headers) {
    $path=$header.fileName.Replace('\','/')
    if(-not $path.EndsWith('/'+$case.consumer,[StringComparison]::Ordinal) -and $path -cne $case.consumer){
      throw 'LIFE1-DIAGNOSTIC: wrong source surface'
    }
    if($header.severity -cne 'error'){throw 'LIFE1-DIAGNOSTIC: unexpected non-error diagnostic'}
    $line=[int]$header.pos.line
    $matched=@($expected|Where-Object {$ranges.ContainsKey($_.surface) -and
      $ranges[$_.surface][0] -le $line -and $line -le $ranges[$_.surface][1]})
    if($matched.Count -ne 1 -or -not $used.Add($matched[0].surface)){throw 'LIFE1-DIAGNOSTIC: unexpected or duplicate theorem surface'}
    $message=$header.data
    $pattern=switch($matched[0].errorClass) {
      'type-mismatch' {'^(Type mismatch|type mismatch)\b'}
      'destructure' {'^rcases tactic failed:'}
      'invalid-field' {'^(Invalid field|invalid field)\b'}
    }
    if($message -cnotmatch $pattern){throw 'LIFE1-DIAGNOSTIC: unexpected error class'}
  }
}
function Invoke-Stage([string]$stage,[string]$exe,[string[]]$arguments,[string]$cwd,
    [hashtable]$environment=@{},[int]$seconds=$DeadlineSeconds) {
  $r=Invoke-RMQOwnedBoundedProcess -FilePath $exe -Arguments $arguments -WorkingDirectory $cwd `
    -Stage $stage -DeadlineSeconds $seconds -OutputLimitBytes $OutputLimitBytes `
    -TempRoot (Join-Path $evidence 'process') -Environment $environment
  # Persist the complete returned streams and process verdict before classification.
  [IO.File]::WriteAllText((Join-Path $evidence ($stage+'.stdout.txt')),($r.StandardOutput -join "`n"),$utf8)
  [IO.File]::WriteAllText((Join-Path $evidence ($stage+'.stderr.txt')),($r.StandardError -join "`n"),$utf8)
  $entry=[ordered]@{stage=$stage;executable=$exe;arguments=$arguments;environment=$environment;workingDirectory=$cwd;result=$r}
  $stages.Add($entry)
  Write-Json ($stage+'.json') $entry
  return $r
}
function Assert-Restored {
  foreach($item in $baseline) {
    if(-not(Test-Path -LiteralPath $item.path -PathType Leaf) -or (Hash-File $item.path) -cne $item.sha256){
      throw ('LIFE1-RESTORATION: original bytes changed: '+$item.path)
    }
  }
}
function Restore-Private([string]$imports,[string]$library) {
  foreach($module in @('Capstone','Provenance')) {
    $relative='RMQ/Core/WordRAM/Lifecycle/'+$module+'.olean'
    $original=Join-Path $library $relative
    $private=Join-Path $imports $relative
    Copy-Item -LiteralPath $original -Destination $private -Force
    if((Hash-File $original) -cne (Hash-File $private)){throw 'LIFE1-RESTORATION: private import binding differs from pristine artifact'}
  }
}
function Remove-Shadow {
  if($null -eq $shadow -or -not(Test-Path -LiteralPath $shadow)){return}
  $resolved=[IO.Path]::GetFullPath($shadow)
  $allowed=[IO.Path]::GetFullPath($evidence).TrimEnd('\','/')+[IO.Path]::DirectorySeparatorChar
  if(-not $resolved.StartsWith($allowed,[StringComparison]::OrdinalIgnoreCase) -or
     [IO.Path]::GetFileName($resolved) -cne 'shadow'){throw 'LIFE1-CLEANUP: shadow path escaped evidence root'}
  Remove-Item -LiteralPath $resolved -Recurse -Force
}
function Expect-Failure([scriptblock]$operation,[string]$message) {
  try {& $operation | Out-Null} catch {if($_.Exception.Message -ceq $message){return};throw}
  throw ('LIFE1-SELFTEST: expected rejection absent: '+$message)
}

try {
  $normalized=Read-Normalized $registryPath
  $registry=$normalized|ConvertFrom-Json
  Assert-Registry $registry (Hash-Bytes $utf8.GetBytes($normalized))
  $selected=@(Select-Cases @($registry.cases) $PSBoundParameters.ContainsKey('OnlyCase') $OnlyCase `
    ([Environment]::GetEnvironmentVariable('LIFE1_DEPENDENCY_SELECTOR','Process')))
  if(($SelfTestOnly -and $StartupOnly) -or ($SelectorProbeOnly -and ($SelfTestOnly -or $StartupOnly)) -or
      (($SelfTestOnly -or $StartupOnly) -and $selected.Count -ne $ids.Count)){throw 'LIFE1-SELECTOR: incompatible modes'}
  if($SelectorProbeOnly){Write-Output ('LIFE1-DEPENDENCY SELECT '+($selected.id -join ','));exit 0}
  foreach($case in @($registry.cases)) { $null=Apply-Edits (Read-Normalized (Join-Path $root $case.producer)) $case }
  $baseEvidence=[IO.Path]::GetFullPath((Join-Path $root $EvidenceDirectory))
  $allowed=[IO.Path]::GetFullPath((Join-Path $root '.lake')).TrimEnd('\','/')+[IO.Path]::DirectorySeparatorChar
  if(-not $baseEvidence.StartsWith($allowed,[StringComparison]::OrdinalIgnoreCase)){throw 'LIFE1-EVIDENCE: path must stay under workspace .lake'}
  $evidence=Join-Path $baseEvidence ([DateTime]::UtcNow.ToString('yyyyMMddTHHmmssfff')+'-'+[Guid]::NewGuid().ToString('N').Substring(0,8))
  [void](New-Item -ItemType Directory -Path $evidence -Force)
  . (Join-Path $root 'scripts/owned_process_tree.ps1')
  if($SelfTestOnly) {
    foreach($text in @('',' ')) { Expect-Failure {Select-Cases @($registry.cases) $true $text $null} 'LIFE1-SELECTOR: explicitly empty selector' }
    Expect-Failure {Select-Cases @($registry.cases) $true 'D99_UNKNOWN' $null} 'LIFE1-SELECTOR: unknown selector'
    Expect-Failure {Select-Cases @($registry.cases) $true $ids[0] ('id:'+$ids[0])} 'LIFE1-SELECTOR: duplicate parameter/environment channels'
    Expect-Failure {Select-Cases @($registry.cases) $false '' 'id:'} 'LIFE1-SELECTOR: explicitly empty selector'
    foreach($kind in @('missing','duplicate','unknown','reorder')) {
      $copy=$normalized|ConvertFrom-Json
      switch($kind) {
        'missing' {$copy.cases=@($copy.cases|Select-Object -Skip 1)}
        'duplicate' {$copy.cases[1].id=$copy.cases[0].id}
        'unknown' {$copy.cases[1].id='D99_UNKNOWN'}
        'reorder' {$tmp=$copy.cases[0];$copy.cases[0]=$copy.cases[1];$copy.cases[1]=$tmp}
      }
      $message=if($kind -ceq 'missing'){'LIFE1-REGISTRY: exact nonempty case count required'}else{'LIFE1-REGISTRY: missing, duplicate, unknown or reordered ID'}
      Expect-Failure {Assert-Registry $copy $registryHash} $message
    }
    $goodDiagnostic=(@{fileName='RMQ/Validation/LifecycleContract.lean';pos=@{line=1;column=1};severity='error';data='Type mismatch'}|ConvertTo-Json -Compress)
    $fake=[pscustomobject]@{ExitCode=1;TimedOut=$false;OutputLimitExceeded=$false;StandardError=@();StandardOutput=@($goodDiagnostic)}
    $testCase=[pscustomobject]@{consumer='RMQ/Validation/LifecycleContract.lean';diagnostics=@([pscustomobject]@{surface='checkC02_retained';errorClass='type-mismatch';count=1})}
    Assert-Reject $fake $testCase @{checkC02_retained=@(1,2)}
    $fake.StandardOutput+=@((@{fileName='RMQ/Validation/LifecycleContract.lean';pos=@{line=9;column=1};severity='error';data='unknown identifier bad'}|ConvertTo-Json -Compress))
    Expect-Failure {Assert-Reject $fake $testCase @{checkC02_retained=@(1,2)}} 'LIFE1-DIAGNOSTIC: exact error count mismatch'
    foreach($trailing in @('error: unrelated compiler failure','uncaught exception: unrelated compiler failure','PANIC: unrelated compiler failure')) {
      $fake.StandardOutput=@($goodDiagnostic,$trailing)
      Expect-Failure {Assert-Reject $fake $testCase @{checkC02_retained=@(1,2)}} 'LIFE1-DIAGNOSTIC: non-JSON compiler output'
    }
    $fake.StandardOutput=@((@{fileName='RMQ/Validation/LifecycleContract.lean';pos=@{line=1;column=1};severity='error';data='unknown identifier bad'}|ConvertTo-Json -Compress))
    Expect-Failure {Assert-Reject $fake $testCase @{checkC02_retained=@(1,2)}} 'LIFE1-DIAGNOSTIC: unexpected error class'
    $shell=(Get-Process -Id $PID).Path
    $childFile=Join-Path $evidence 'child.pid'
    $sleeper=Join-Path $evidence 'sleeper.ps1'
    $quotedShell=$shell.Replace("'","''");$quotedChild=$childFile.Replace("'","''")
    [IO.File]::WriteAllText($sleeper,"`$p=Start-Process -FilePath '$quotedShell' -ArgumentList '-NoProfile','-Command','Start-Sleep -Seconds 120' -WindowStyle Hidden -PassThru`n[IO.File]::WriteAllText('$quotedChild',[string]`$p.Id)`nStart-Sleep -Seconds 120",$utf8)
    $r=Invoke-Stage 'deadline-control' $shell @('-NoProfile','-File',$sleeper) $root @{} 6
    if(-not $r.TimedOut -or -not(Test-Path -LiteralPath $childFile)){throw 'LIFE1-SELFTEST: descendant deadline control did not execute'}
    $childId=[int][IO.File]::ReadAllText($childFile)
    if($null -ne (Get-Process -Id $childId -ErrorAction SilentlyContinue)){throw 'LIFE1-SELFTEST: owned descendant survived deadline'}
    Write-Json 'selftest.json' @{registry=$true;selectors=$true;mixedDiagnostics=$true;ownedDeadline=$true;child=$childId;result=$r}
    $completed=$true
  } else {
    $mutex=[Threading.Mutex]::new($false,'Local\RMQLifecycleImplementationHeavy20260920')
    try {$locked=$mutex.WaitOne(7200000)}catch [Threading.AbandonedMutexException]{$locked=$true}
    if(-not $locked){throw 'LIFE1-SCHEDULING: heavy mutex wait expired; no compiler launched'}
    $library=Join-Path $root '.lake/build/lib/lean'
    $toolchain=(Read-Normalized (Join-Path $root 'lean-toolchain')).Trim().Replace(':','---').Replace('/','--')
    $profilePath=$env:USERPROFILE
    if([string]::IsNullOrWhiteSpace($profilePath)){$profilePath=[Environment]::GetFolderPath('UserProfile')}
    $toolRoot=Join-Path $profilePath ('.elan/toolchains/'+$toolchain)
    $lean=Join-Path $toolRoot 'bin/lean.exe'
    if(-not(Test-Path -LiteralPath $lean)){throw 'LIFE1-PREREQUISITE: pinned Lean binary absent'}
    $paths=@('scripts/lifecycle_dependency_replay.ps1','scripts/lifecycle_dependency_cases.json',
      'scripts/owned_process_tree.ps1','lean-toolchain')+
      @($registry.cases.producer)+@($registry.cases.consumer)
    foreach($path in @($paths|Select-Object -Unique)) {
      $full=Join-Path $root $path
      $baseline+=@([pscustomobject]@{path=$full;sha256=(Hash-File $full)})
      if($path.StartsWith('RMQ/')) {
        $artifact=Join-Path $library ([IO.Path]::ChangeExtension($path,'.olean'))
        if(-not(Test-Path -LiteralPath $artifact)){throw ('LIFE1-PREREQUISITE: baseline artifact absent: '+$path)}
        $baseline+=@([pscustomobject]@{path=$artifact;sha256=(Hash-File $artifact)})
      }
    }
    $baseline+=@([pscustomobject]@{path=$lean;sha256=(Hash-File $lean)})
    Write-Json 'baseline.json' $baseline
    $shadow=Join-Path $evidence 'shadow'
    $imports=Join-Path $shadow 'imports'
    [void](New-Item -ItemType Directory -Path $imports -Force)
    # Lean chooses one root package, so the private RMQ package is complete.
    Copy-Item -LiteralPath (Join-Path $library 'RMQ') -Destination (Join-Path $imports 'RMQ') -Recurse
    if($StartupOnly){$selected=@($registry.cases|Where-Object {$_.id -cin @('D20_ACCEPT_IDENTITY','P06_ACCEPT_IDENTITY')})}
    foreach($case in $selected) {
      Assert-Restored
      $caseRoot=Join-Path $shadow $case.id
      $sourcePath=Join-Path $caseRoot $case.producer
      $consumerPath=Join-Path $caseRoot $case.consumer
      foreach($file in @($sourcePath,$consumerPath)){[void](New-Item -ItemType Directory -Path ([IO.Path]::GetDirectoryName($file)) -Force)}
      # Bind each case to the original dependency artifacts before its own producer is replaced.
      Restore-Private $imports $library
      $original=Read-Normalized (Join-Path $root $case.producer)
      $changed=Apply-Edits $original $case
      $client=Read-Normalized (Join-Path $root $case.consumer)
      [IO.File]::WriteAllText($sourcePath,$changed,$utf8)
      [IO.File]::WriteAllText($consumerPath,$client,$utf8)
      $out=Join-Path $imports ([IO.Path]::ChangeExtension($case.producer,'.olean'))
      $environment=@{LEAN_PATH=($imports+[IO.Path]::PathSeparator+(Join-Path $toolRoot 'lib/lean'));LEAN_NUM_THREADS='1'}
      $producer=Invoke-Stage ($case.id+'-producer') $lean @('--json',"--root=$caseRoot",'-o',$out,$sourcePath) $caseRoot $environment
      Assert-Accept $producer
      $freshHash=Hash-File $out
      if($case.expected -ceq 'reject' -and $freshHash -ceq (Hash-File (Join-Path $library ([IO.Path]::ChangeExtension($case.producer,'.olean'))))){
        throw 'LIFE1-BINDING: negative artifact did not change'
      }
      $consumer=Invoke-Stage ($case.id+'-consumer') $lean @('--json',"--root=$caseRoot",$consumerPath) $caseRoot $environment
      if($case.expected -ceq 'accept'){Assert-Accept $consumer}else{Assert-Reject $consumer $case (Surface-Ranges $client)}
      Assert-Restored
      Restore-Private $imports $library
      $results.Add([ordered]@{id=$case.id;expected=$case.expected;producerSourceHash=(Hash-File $sourcePath);
        producerArtifactHash=$freshHash;consumerHash=(Hash-File $consumerPath);producerSeconds=$producer.DurationSeconds;
        consumerSeconds=$consumer.DurationSeconds;consumerExit=$consumer.ExitCode;restored=$true;privateRestored=$true})
      Write-Json 'cases.json' $results
      Write-Output ('LIFE1-DEPENDENCY CASE '+$case.id+' PASS')
    }
    Assert-Restored
    $completed=$true
  }
} catch {
  $stageError=$_.Exception.Message
  [Console]::Error.WriteLine($_.Exception.Message)
  if($null -ne $evidence){Write-Json 'failure.json' @{message=$_.Exception.Message;stack=$_.ScriptStackTrace;stages=$stages;cases=$results}}
} finally {
  try {Assert-Restored;$restored=$true} catch {
    $completed=$false;$integrityError=$_.Exception.Message
    [Console]::Error.WriteLine($integrityError)
  }
  try {Remove-Shadow} catch {
    $completed=$false;$cleanupError=$_.Exception.Message
    [Console]::Error.WriteLine($cleanupError)
  }
  if($locked){$mutex.ReleaseMutex()}
  if($null -ne $mutex){$mutex.Dispose()}
  if($null -ne $evidence){Write-Json 'summary.json' @{passed=$completed;registrySha256=$registryHash;selected=@($selected.id);cases=$results;restored=$restored;shadowRemoved=($null -eq $shadow -or -not(Test-Path -LiteralPath $shadow));stageError=$stageError;integrityError=$integrityError;cleanupError=$cleanupError}}
}
if(-not $completed){exit 1}
Write-Output ('LIFE1-DEPENDENCY PASS '+$evidence)
exit 0
