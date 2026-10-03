[CmdletBinding()]
param(
  [Parameter(Mandatory=$true)][string]$Shell,
  [Parameter(Mandatory=$true)][ValidateSet('pwsh','winps')][string]$Profile,
  [AllowEmptyString()][string]$OnlyCase,
  [string]$EvidenceRoot
)
Set-StrictMode -Version Latest
$ErrorActionPreference='Stop'
$root=[IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../../../../..'))
$utf8=[Text.UTF8Encoding]::new($false,$true)
$runtimeProfilePath=Join-Path $PSScriptRoot 'runtime_profile.ps1'
. $runtimeProfilePath
$runtime=Assert-LifecycleRepairRuntime $Shell $Profile
$registryPath=Join-Path $PSScriptRoot 'registry_control_cases.json'
$registryHash='59d2a546c64eef274e878407583b51164d0676edd98fef46b04549d6fdf44a4a'
function Get-L1R1RegistryControlSha256([byte[]]$Bytes){
  $algorithm=[Security.Cryptography.SHA256]::Create()
  try{return ([BitConverter]::ToString($algorithm.ComputeHash($Bytes))).Replace('-','').ToLowerInvariant()}
  finally{$algorithm.Dispose()}
}
function Test-L1R1RegistryControlTextIdentity([byte[]]$Bytes,[string]$Expected){
  $normalized=$utf8.GetBytes($utf8.GetString($Bytes).Replace("`r`n","`n"))
  return (Get-L1R1RegistryControlSha256 $Bytes) -ceq $Expected -or (Get-L1R1RegistryControlSha256 $normalized) -ceq $Expected
}
$expectedIds=@('R01_FULL_REGISTRY','R02_ONE_ID','R03_BOUND_EMPTY','R04_BOUND_WHITESPACE',
  'R05_UNKNOWN_SELECTOR','R06_MISSING_MIDDLE','R07_DUPLICATE_MIDDLE','R08_UNKNOWN_MIDDLE',
  'R09_UNUSED_EXTRA','R10_CHANGED_MAPPING','R11_WRONG_PROFILE','R12_WRONG_SUPPLIED_SHELL')
$registryBytes=[IO.File]::ReadAllBytes($registryPath)
if(-not (Test-L1R1RegistryControlTextIdentity $registryBytes $registryHash)){throw 'L1R1-REGISTRY-CONTROL: frozen control mapping identity changed'}
$registry=$utf8.GetString($registryBytes)|ConvertFrom-Json
if(@($registry.cases).Count -ne $expectedIds.Count){throw 'L1R1-REGISTRY-CONTROL: exact control count mismatch'}
for($i=0;$i -lt $expectedIds.Count;$i++){
  if($registry.cases[$i].id -cne $expectedIds[$i]){throw 'L1R1-REGISTRY-CONTROL: exact ordered control IDs differ'}
}
$selected=@($registry.cases)
if($PSBoundParameters.ContainsKey('OnlyCase')){
  if([string]::IsNullOrWhiteSpace($OnlyCase)){throw 'L1R1-REGISTRY-CONTROL: explicitly empty selector'}
  $selected=@($selected|Where-Object {$_.id -ceq $OnlyCase})
  if($selected.Count -ne 1){throw 'L1R1-REGISTRY-CONTROL: unknown exact control ID'}
}
$driver=Join-Path $PSScriptRoot $registry.driver
$frozenPath=Join-Path $PSScriptRoot 'CONTROL_REGISTRY.frozen.json'
$activePath=Join-Path $PSScriptRoot 'CONTROL_REGISTRY.json'
$frozenBytes=[IO.File]::ReadAllBytes($frozenPath)
if(-not (Test-L1R1RegistryControlTextIdentity $frozenBytes $registry.productionRegistrySha256)){throw 'L1R1-REGISTRY-CONTROL: production registry identity changed'}
if([Convert]::ToBase64String([IO.File]::ReadAllBytes($activePath)) -cne [Convert]::ToBase64String($frozenBytes)){throw 'L1R1-REGISTRY-CONTROL: actual driver registry differs from frozen bytes'}
$frozenText=$utf8.GetString($frozenBytes)
$frozen=$frozenText|ConvertFrom-Json
$expectedProfile=@($registry.expectedProfiles.$Profile)
$actualProfile=@($frozen.cases|Where-Object {$_.profiles -ccontains $Profile}|ForEach-Object {$_.id})
if(($actualProfile -join ',') -cne ($expectedProfile -join ',') -or @($frozen.cases).Count -ne $registry.productionRegistryCaseCount){throw 'L1R1-REGISTRY-CONTROL: production profile does not match frozen exact list'}
if($frozen.cases[$registry.middleIndex].id -cne $registry.middleId){throw 'L1R1-REGISTRY-CONTROL: middle mutation target changed'}
$Shell=[IO.Path]::GetFullPath($Shell)
if(-not (Test-Path -LiteralPath $Shell -PathType Leaf)){throw 'L1R1-REGISTRY-CONTROL: selected runtime unavailable'}
$helper=Join-Path $root 'scripts/owned_process_tree.ps1'
$pins=[ordered]@{}
foreach($path in @($driver,$frozenPath,$activePath,$registryPath,$helper,$Shell,$PSCommandPath,$runtimeProfilePath)){
  $pins[$path]=(Get-FileHash -LiteralPath $path).Hash
}
foreach($component in $frozen.components){
  $path=Join-Path $PSScriptRoot $component.path
  $pins[$path]=(Get-FileHash -LiteralPath $path).Hash
}
if([string]::IsNullOrWhiteSpace($EvidenceRoot)){$EvidenceRoot=Join-Path $root ('.lake/repair-r1/registry-'+$Profile+'-'+[Guid]::NewGuid().ToString('N'))}
$evidence=[IO.Path]::GetFullPath($EvidenceRoot)
$allowed=[IO.Path]::GetFullPath((Join-Path $root '.lake')).TrimEnd('\','/')+[IO.Path]::DirectorySeparatorChar
if(-not $evidence.StartsWith($allowed,[StringComparison]::OrdinalIgnoreCase) -or (Test-Path -LiteralPath $evidence)){throw 'L1R1-REGISTRY-CONTROL: fresh owned evidence descendant required'}
[void][IO.Directory]::CreateDirectory($evidence)
. $helper

function Write-RegistryJson([string]$Path,[object]$Value){
  [IO.File]::WriteAllText($Path,($Value|ConvertTo-Json -Depth 60),$utf8)
}

function Replace-FirstLiteral([string]$Text,[string]$Before,[string]$After){
  $index=$Text.IndexOf($Before,[StringComparison]::Ordinal)
  if($index -lt 0){throw 'L1R1-REGISTRY-CONTROL: exact mutation anchor missing'}
  return $Text.Substring(0,$index)+$After+$Text.Substring($index+$Before.Length)
}

function New-ChallengedRegistry([string]$Mutation,[string]$Path){
  # JSON reserialization is used only for count changes. ID/mapping changes
  # preserve every byte outside the first exact literal occurrence.
  $text=$frozenText
  switch -CaseSensitive ($Mutation){
    'none' {[IO.File]::WriteAllBytes($Path,$frozenBytes);return}
    'missing-middle' {
      $copy=$frozenText|ConvertFrom-Json
      $copy.cases=@(for($j=0;$j -lt @($copy.cases).Count;$j++){if($j -ne $registry.middleIndex){$copy.cases[$j]}})
      Write-RegistryJson $Path $copy
      return
    }
    'duplicate-middle' {
      $before='"id": "'+$registry.middleId+'"'
      $after='"id": "'+$frozen.cases[$registry.middleIndex-1].id+'"'
      $text=Replace-FirstLiteral $text $before $after
    }
    'unknown-middle' {
      $text=Replace-FirstLiteral $text ('"id": "'+$registry.middleId+'"') '"id": "UNDECLARED_CONTROL"'
    }
    'unused-extra' {
      $copy=$frozenText|ConvertFrom-Json
      $extra=($frozen.cases[$registry.middleIndex]|ConvertTo-Json -Depth 60)|ConvertFrom-Json
      $extra.id='UNUSED_EXTRA_CONTROL'
      $copy.cases=@($copy.cases)+@($extra)
      Write-RegistryJson $Path $copy
      return
    }
    'changed-mapping' {
      $text=Replace-FirstLiteral $text '"handler": "selector_child.ps1"' '"handler": "UNUSED_HANDLER.ps1"'
    }
    default {throw 'L1R1-REGISTRY-CONTROL: unused or unknown mutation'}
  }
  [IO.File]::WriteAllText($Path,$text,$utf8)
}

$childPath=Join-Path $evidence 'invoke-driver.ps1'
# The child only supplies parameters, records its runtime, and exposes the
# actual driver's thrown message. No copied loader or replacement predicate.
[IO.File]::WriteAllText($childPath,@'
param([Parameter(Mandatory=$true)][string]$InvocationPath)
Set-StrictMode -Version Latest
$ErrorActionPreference='Stop'
$utf8=[Text.UTF8Encoding]::new($false,$true)
try {
  $spec=$utf8.GetString([IO.File]::ReadAllBytes($InvocationPath))|ConvertFrom-Json
  $runtime=(Get-Process -Id $PID).Path
  $identity=[ordered]@{pid=$PID;runtime=$runtime;runtimeSha256=(Get-FileHash -LiteralPath $runtime).Hash;
    psVersion=$PSVersionTable.PSVersion.ToString();dotnetVersion=[Environment]::Version.ToString();
    driver=$spec.driver;driverSha256=(Get-FileHash -LiteralPath $spec.driver).Hash;
    registryPath=$spec.registryPath;registrySha256=(Get-FileHash -LiteralPath $spec.registryPath).Hash;
    selectorPresent=$spec.selector.present;selectorValue=$spec.selector.value;profile=$spec.profile;suppliedShell=$spec.shell;
    runtimeHelper=$spec.runtimeHelper;runtimeHelperSha256=(Get-FileHash -LiteralPath $spec.runtimeHelper).Hash}
  [IO.File]::WriteAllText($spec.identityPath,($identity|ConvertTo-Json -Depth 20),$utf8)
  $parameters=@{Shell=[string]$spec.shell;Profile=[string]$spec.profile;RegistryPath=[string]$spec.registryPath;ProbeOnly=$true}
  if($spec.selector.present){$parameters.OnlyCase=[string]$spec.selector.value}
  $global:LASTEXITCODE=0
  & ([string]$spec.driver) @parameters
  exit ([int]$LASTEXITCODE)
} catch {
  [Console]::Error.WriteLine($_.Exception.Message)
  exit 1
}
'@,$utf8)

function Invoke-RegistryProbe([object]$Case,[string]$Label,[string]$Directory,[string]$RegistryFile,[object]$Selector,[int]$ExpectedExit,[string]$ExpectedOutput,[AllowNull()][string]$ExpectedError,[string]$DriverShell,[string]$DriverProfile){
  $invocation=Join-Path $Directory ($Label+'.invocation.json')
  $identityPath=Join-Path $Directory ($Label+'.child.json')
  Write-RegistryJson $invocation ([ordered]@{driver=$driver;shell=$DriverShell;profile=$DriverProfile;registryPath=$RegistryFile;selector=$Selector;identityPath=$identityPath;runtimeHelper=$runtimeProfilePath})
  $result=$null
  $caught=$null
  $passed=$false
  try {
    $result=Invoke-RMQOwnedBoundedProcess -FilePath $Shell -Arguments @('-NoLogo','-NoProfile','-ExecutionPolicy','Bypass','-File',$childPath,'-InvocationPath',$invocation) `
      -WorkingDirectory $root -Stage ($Case.id+'-'+$Label) -DeadlineSeconds 30 -OutputLimitBytes 1048576 -TempRoot (Join-Path $Directory ($Label+'-process'))
    # Retain all available returned data before evaluating the verdict.
    Write-RegistryJson (Join-Path $Directory ($Label+'.process.json')) $result
    [IO.File]::WriteAllText((Join-Path $Directory ($Label+'.stdout.returned-lines.txt')),($result.StandardOutput -join "`n"),$utf8)
    [IO.File]::WriteAllText((Join-Path $Directory ($Label+'.stderr.returned-lines.txt')),($result.StandardError -join "`n"),$utf8)
    if($result.TimedOut -or $result.OutputLimitExceeded -or $result.Ownership -cne 'kill-on-close-job' -or @($result.TerminatedIds).Count -ne 0){throw 'L1R1-REGISTRY-CONTROL: incomplete owned child'}
    if($result.ExitCode -ne $ExpectedExit){throw 'L1R1-REGISTRY-CONTROL: unexpected actual exit'}
    if($ExpectedExit -eq 0){
      if(@($result.StandardError).Count -ne 0 -or @($result.StandardOutput).Count -ne 1 -or $result.StandardOutput[0] -cne $ExpectedOutput){throw 'L1R1-REGISTRY-CONTROL: exact positive stream predicate failed'}
    } else {
      if(@($result.StandardOutput).Count -ne 0 -or @($result.StandardError).Count -ne 1 -or $result.StandardError[0] -cne $ExpectedError){throw 'L1R1-REGISTRY-CONTROL: exact negative stream predicate failed'}
    }
    if(-not (Test-Path -LiteralPath $identityPath -PathType Leaf)){throw 'L1R1-REGISTRY-CONTROL: missing actual child identity'}
    $child=Get-Content -LiteralPath $identityPath -Raw|ConvertFrom-Json
    if(-not ([IO.Path]::GetFullPath($child.runtime)).Equals($Shell,[StringComparison]::OrdinalIgnoreCase) -or $child.runtimeSha256 -cne $pins[$Shell] -or $child.driverSha256 -cne $pins[$driver]){throw 'L1R1-REGISTRY-CONTROL: actual child source/runtime mismatch'}
    if($child.runtimeHelperSha256 -cne $pins[$runtimeProfilePath] -or $child.profile -cne $DriverProfile -or $child.suppliedShell -cne $DriverShell){throw 'L1R1-REGISTRY-CONTROL: actual runtime contract input mismatch'}
    if($child.registrySha256 -cne (Get-FileHash -LiteralPath $RegistryFile).Hash -or [bool]$child.selectorPresent -ne [bool]$Selector.present -or $child.selectorValue -cne $Selector.value){throw 'L1R1-REGISTRY-CONTROL: actual child input mismatch'}
    if($null -ne (Get-Process -Id $child.pid -ErrorAction SilentlyContinue)){throw 'L1R1-REGISTRY-CONTROL: child survived owned process return'}
    $passed=$true
    return [pscustomobject]@{label=$Label;passed=$true;expectedExit=$ExpectedExit;expectedOutput=$ExpectedOutput;expectedError=$ExpectedError;
      childPid=$child.pid;childAbsent=$true;durationSeconds=$result.DurationSeconds;deadlineSeconds=30;processReceipt=(Join-Path $Directory ($Label+'.process.json'));
      actualChildIdentity=$identityPath;registrySha256=$child.registrySha256;selector=$Selector;
      actualRuntime=$Shell;suppliedShell=$DriverShell;declaredProfile=$DriverProfile;runtimeHelperSha256=$child.runtimeHelperSha256}
  } catch {
    $caught=$_.Exception.Message
    throw
  } finally {
    Write-RegistryJson (Join-Path $Directory ($Label+'.verdict.json')) ([ordered]@{passed=$passed;error=$caught;
      expectedExit=$ExpectedExit;expectedOutput=$ExpectedOutput;expectedError=$ExpectedError;returnedResultAvailable=($null -ne $result);
      semantics='Actual driver ProbeOnly only; zero semantic cases executed.';streamLimit=$registry.streamLimit})
  }
}

$results=[Collections.Generic.List[object]]::new()
$mutex=$null
$locked=$false
$passed=$false
$stageError=$null
$integrityError=$null
$sourcesUnchanged=$false
try {
  # ProbeOnly exits before the driver acquires this mutex. The outer caller
  # must not hold it while awaiting this runner, even under another runtime.
  $mutex=[Threading.Mutex]::new($false,'Local\RMQLifecycleImplementationHeavy20260920')
  try{$locked=$mutex.WaitOne(7200000)}catch [Threading.AbandonedMutexException]{$locked=$true}
  if(-not $locked){throw 'L1R1-REGISTRY-CONTROL: no shared control campaign slot'}
  foreach($case in $selected){
    $directory=Join-Path $evidence $case.id
    [void][IO.Directory]::CreateDirectory($directory)
    $positivePath=Join-Path $directory 'P.registry.json'
    $challengedPath=Join-Path $directory 'Q.registry.json'
    [IO.File]::WriteAllBytes($positivePath,$frozenBytes)
    New-ChallengedRegistry $case.mutation $challengedPath
    $positiveSelector=if($case.positiveSelector -ceq 'one'){
      [pscustomobject]@{present=$true;value=$registry.knownCase}
    } else {[pscustomobject]@{present=$false;value=$null}}
    $positiveOutput=if($positiveSelector.present){'L1R1 SELECT '+$registry.knownCase}else{'L1R1 SELECT '+($expectedProfile -join ',')}
    $p=Invoke-RegistryProbe $case 'P' $directory $positivePath $positiveSelector 0 $positiveOutput $null $Shell $Profile
    $challengedOutput=if($case.expected.stdout -ceq 'full'){'L1R1 SELECT '+($expectedProfile -join ',')}elseif($case.expected.stdout -ceq 'one'){'L1R1 SELECT '+$registry.knownCase}else{''}
    $challengedShell=$Shell
    $challengedProfile=$Profile
    if($null -ne $case.PSObject.Properties['runtimeChallenge']){
      switch -CaseSensitive ($case.runtimeChallenge){
        'opposite-profile' {$challengedProfile=if($Profile -ceq 'pwsh'){'winps'}else{'pwsh'}}
        'opposite-shell' {
          $challengedShell=if($Profile -ceq 'pwsh'){'C:/Windows/System32/WindowsPowerShell/v1.0/powershell.exe'}else{'C:/Users/poin/.cache/codex-runtimes/codex-primary-runtime/dependencies/native/powershell/pwsh.exe'}
        }
        default {throw 'L1R1-REGISTRY-CONTROL: unknown runtime challenge'}
      }
    }
    $q=Invoke-RegistryProbe $case 'Q' $directory $challengedPath $case.selector ([int]$case.expected.exit) $challengedOutput $case.expected.error $challengedShell $challengedProfile
    $record=[ordered]@{id=$case.id;passed=$true;mutation=$case.mutation;production=$case.production;positive=$p;challenged=$q}
    Write-RegistryJson (Join-Path $directory 'result.json') $record
    $results.Add($record)
    Write-Output ('L1R1 REGISTRY CASE '+$case.id+' PASS')
  }
  if($results.Count -ne $selected.Count){throw 'L1R1-REGISTRY-CONTROL: incomplete selected controls'}
  $passed=$true
} catch {
  $stageError=$_.Exception.Message
  $passed=$false
} finally {
  try {
    foreach($path in $pins.Keys){if((Get-FileHash -LiteralPath $path).Hash -cne $pins[$path]){throw ('L1R1-REGISTRY-CONTROL: source changed '+$path)}}
    $sourcesUnchanged=$true
  } catch {
    $integrityError=$_.Exception.Message
    $passed=$false
  }
  try {
    Write-RegistryJson (Join-Path $evidence 'summary.json') ([ordered]@{passed=$passed;profile=$Profile;shell=$Shell;registrySha256=$registryHash;
      sourcePins=$pins;runtime=$runtime;runtimeHelperSha256=$pins[$runtimeProfilePath];draftPredecessor=$registry.draftPredecessor;registryFreeze=$registry.freezeStatus;
      selected=@($selected.id);results=@($results.ToArray());stageError=$stageError;integrityError=$integrityError;sourcesUnchanged=$sourcesUnchanged;
      semanticCasesExecuted=0;streamLimit=$registry.streamLimit;deadlineSeconds=30;outputLimitBytes=1048576;
      fixtureDisposition='Owned P/Q registry copies and child specifications retained as evidence; original sources never modified.'})
  } finally {
    if($locked){$mutex.ReleaseMutex()}
    if($null -ne $mutex){$mutex.Dispose()}
  }
}
if(-not $passed){
  if($null -ne $stageError){[Console]::Error.WriteLine($stageError)}
  if($null -ne $integrityError){[Console]::Error.WriteLine($integrityError)}
  exit 1
}
Write-Output ('L1R1 REGISTRY CONTROLS PASS '+$evidence)
