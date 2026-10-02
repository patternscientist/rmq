[CmdletBinding()]
param(
  [Parameter(Mandatory=$true)][string]$HarnessRef,
  [Parameter(Mandatory=$true)][ValidateSet('pwsh','winps')][string]$Profile,
  [AllowEmptyCollection()][AllowEmptyString()][string[]]$OnlyControl,
  [switch]$ProbeOnly,
  [string]$RegistryPath,
  [string]$OutputRoot
)
# LIFE-1-R3 failure-path control runner.
#
# Each selected control builds a disposable copy of the files one lifecycle
# harness needs under this worktree's .lake, places the minimal injected test
# double (fixed before the harness takes its entry pins), launches the WHOLE
# harness file through the unchanged scripts/owned_process_tree.ps1 helper with
# a positive deadline, evaluates the harness's durable result, restores the copy
# and verifies its exact bytes. -HarnessRef base runs the unchanged harness
# bytes of the audited candidate and checks the predicted base outcome; any other
# ref runs that commit's harness bytes and requires every control to pass.
#
# LIFE-1-R4/V1 versioning. The runner accepts exactly three pinned registries: the R3
# v1 registry (repair-r3/FAILURE_CONTROL_REGISTRY.json, 47 controls, base
# eb8e4f25; still the default and replayable unchanged) and the R4 v2 registry
# (repair-r4/FAILURE_CONTROL_REGISTRY.json, the 47 R3 controls plus 13 R4
# controls, base d27ffa34). V1 v3 keeps the same 60 IDs/mappings and adds the
# independent ordered pin rosters consumed by Test-R4PinCoverage. Registry
# generation is chosen by schema/version and pinned by normalized SHA-256; v1
# and v2 remain replayable from their frozen bytes.
Set-StrictMode -Version Latest
$ErrorActionPreference='Stop'
$utf8=[Text.UTF8Encoding]::new($false,$true)
$here=$PSScriptRoot
$repo=[IO.Path]::GetFullPath((Join-Path $here '../../../../..'))
$r3Ids=@('RC-P','RC-C','RC-Q','RC-S','RC-M','FC-P','FC-C','FC-Q','FC-S','FC-M',
  'K1-P','K1-C','K1-Q','K1-S','K1-M','K1-X','K2-P','K2-C','K2-Q','K2-S','K2-M',
  'DC-P','DC-C','DC-Q','DC-S','DC-M','LV-P','LV-C','LV-Q','LV-S','LV-M',
  'IC-P','IC-C','IC-Q','IC-S','IC-M','DP-P','DP-C','DP-Q','DP-S','DP-M',
  'HS-P','HS-C','HS-Q','HS-S','HS-M','HS-R')
$registryVersions=@{
  1=@{schema='life1-r3-failure-controls-v1';sha='500dd96074bb0c5049f2f76627e9ff1d31f1085c8fab11ff8c795e72e22936ad'
    base='eb8e4f250ee13eaf378f4a42028ce32e7cf0b94a';ids=$r3Ids}
  2=@{schema='life1-r4-failure-controls-v2';sha='cf5ef090543773ef0a4fa473164e56633fabeef140301aad737bb2a7a3226dbc'
    base='d27ffa341f4ed8ceccc46817455eb26c73b319a1'
    ids=$r3Ids+@('K1-F','K2-F','K1-T','K2-T','K1-W','K2-W','LV-W','IC-U','LV-E','IC-L','HS-L','K2-G','HS-G')}
  3=@{schema='life1-v1-evidence-failure-controls-v3';sha='3a42563c43e8d035073a6451342e05fa1548ef0487113cbf3f2dc0618785784d'
    base='ee44f04a561f2194b3713f071c26b6faf9ba7fab'
    ids=$r3Ids+@('K1-F','K2-F','K1-T','K2-T','K1-W','K2-W','LV-W','IC-U','LV-E','IC-L','HS-L','K2-G','HS-G')}
}
$r4Dir=Join-Path $repo 'docs/internal/extensions/lifecycle1/repair-r4'
$shells=@{pwsh='C:/Users/poin/.cache/codex-runtimes/codex-primary-runtime/dependencies/native/powershell/pwsh.exe';
  winps='C:/Windows/System32/WindowsPowerShell/v1.0/powershell.exe'}

function Get-R3Sha256([byte[]]$Bytes) {
  $a=[Security.Cryptography.SHA256]::Create()
  try {return ([BitConverter]::ToString($a.ComputeHash($Bytes))).Replace('-','').ToLowerInvariant()} finally {$a.Dispose()}
}
function Get-R3NormalizedSha256([byte[]]$Bytes) {
  return Get-R3Sha256 ($utf8.GetBytes($utf8.GetString($Bytes).Replace("`r`n","`n")))
}
function Get-R3FileSha256([string]$Path) {return Get-R3Sha256 ([IO.File]::ReadAllBytes($Path))}
function Get-R4Field([object]$Object,[string]$Name) {
  if($null -eq $Object){return $null}
  $p=$Object.PSObject.Properties[$Name]
  if($null -eq $p){return $null}
  return $p.Value
}

# ---- Pre-execution validation: registry and selector (nothing pinned or launched yet).
if($PSVersionTable.PSVersion.Major -lt 7){throw 'R3-RUNTIME: the runner itself requires PowerShell 7'}
if(-not $PSBoundParameters.ContainsKey('RegistryPath')){$RegistryPath=Join-Path $here 'FAILURE_CONTROL_REGISTRY.json'}
$registryBytes=[IO.File]::ReadAllBytes($RegistryPath)
$registry=$utf8.GetString($registryBytes)|ConvertFrom-Json
$registryVersion=$null
foreach($k in @(1,2,3)){if($registry.version -eq $k -and $registry.schema -ceq $registryVersions[$k].schema){$registryVersion=$k}}
if($null -eq $registryVersion){throw 'R3-REGISTRY: unsupported registry version'}
$expectedIds=$registryVersions[$registryVersion].ids
$registryNormalizedSha256=$registryVersions[$registryVersion].sha
$baseSha=$registryVersions[$registryVersion].base
$ids=@($registry.controls|ForEach-Object {[string]$_.id})
if($ids.Count -eq 0){throw 'R3-REGISTRY: empty registry'}
$seen=[Collections.Generic.HashSet[string]]::new([StringComparer]::Ordinal)
foreach($id in $ids){if(-not $seen.Add($id)){throw ('R3-REGISTRY: duplicate ID '+$id)}}
foreach($id in $expectedIds){if(-not $seen.Contains($id)){throw ('R3-REGISTRY: missing ID '+$id)}}
foreach($id in $ids){if($expectedIds -cnotcontains $id){throw ('R3-REGISTRY: unknown ID '+$id)}}
if(($ids -join ',') -cne ($expectedIds -join ',')){throw 'R3-REGISTRY: reordered IDs'}
if((Get-R3NormalizedSha256 $registryBytes) -cne $registryNormalizedSha256){throw 'R3-REGISTRY: registry bytes differ from the pinned version'}
if($registryVersion -eq 3){
  $rosterProp=$registry.PSObject.Properties['pinRosters']
  if($null -eq $rosterProp){throw 'R3-REGISTRY: v3 pin rosters absent'}
  $rosterKeys=@($rosterProp.Value.PSObject.Properties|ForEach-Object {$_.Name})
  $harnessKeys=@($registry.harnessKeys.PSObject.Properties|ForEach-Object {$_.Name})
  if(($rosterKeys -join ',') -cne ($harnessKeys -join ',')){throw 'R3-REGISTRY: v3 pin roster keys differ from harness keys'}
  $contextProp=$registry.PSObject.Properties['trustedPathContexts']
  if($null -eq $contextProp -or $null -eq $contextProp.Value.PSObject.Properties['DP']){throw 'R3-REGISTRY: v3 trusted path contexts absent'}
  $dpToolchain=[string](Get-R4Field $contextProp.Value.DP 'toolchainBin')
  if([string]::IsNullOrWhiteSpace($dpToolchain) -or -not [IO.Path]::IsPathRooted($dpToolchain)){throw 'R3-REGISTRY: DP toolchain path context invalid'}
  $declaredNoReceipt=@($registry.receiptSemantics.guardedNoReceiptControlIds|ForEach-Object {[string]$_})
  $actualNoReceipt=@($registry.controls|Where-Object {[bool](Get-R4Field $_.expect 'durableAbsent')}|ForEach-Object {[string]$_.id})
  if(($declaredNoReceipt -join ',') -cne 'K1-W,K2-W,LV-W' -or ($actualNoReceipt -join ',') -cne ($declaredNoReceipt -join ',') -or
     [int]$registry.receiptSemantics.receiptBearingControlCount -ne ($registry.controls.Count-$actualNoReceipt.Count)){
    throw 'R3-REGISTRY: v3 receipt-bearing/no-receipt partition differs'
  }
  foreach($control in $registry.controls){
    $roster=$rosterProp.Value.PSObject.Properties[[string]$control.harness]
    if($null -eq $roster){throw ('R3-REGISTRY: no pin roster for '+$control.id)}
    $rules=[Collections.Generic.List[string]]::new()
    foreach($row in @($roster.Value.rows)){$rules.Add([string]$row)}
    foreach($stageProperty in $roster.Value.stages.PSObject.Properties){
      $stageRows=$stageProperty.Value.PSObject.Properties['rows']
      if($null -ne $stageRows){foreach($row in @($stageRows.Value)){$rules.Add([string]$row)}}
    }
    foreach($rule in $rules){
      if([string]::IsNullOrWhiteSpace($rule) -or $rule.StartsWith('suffix:',[StringComparison]::Ordinal) -or $rule.StartsWith('regex:',[StringComparison]::Ordinal)){
        throw ('R3-REGISTRY: broad or empty v3 roster rule '+$rule+' for '+$control.harness)
      }
      if($rule.StartsWith('shell:',[StringComparison]::Ordinal) -and @('shell:child','shell:host') -cnotcontains $rule){throw ('R3-REGISTRY: unknown shell roster rule '+$rule)}
      if($rule.StartsWith('history:',[StringComparison]::Ordinal) -and $rule -cne 'history:raw-summary'){throw ('R3-REGISTRY: unknown history roster rule '+$rule)}
    }
    $kinds=$roster.Value.PSObject.Properties['identityKinds']
    if($null -ne $kinds){
      $baseRows=@($roster.Value.rows)
      foreach($kind in $kinds.Value.PSObject.Properties){
        $kindIndex=0
        if(-not [int]::TryParse($kind.Name,[ref]$kindIndex) -or $kindIndex -lt 0 -or $kindIndex -ge $baseRows.Count -or [string]$kind.Value -cne 'git-sha1'){
          throw ('R3-REGISTRY: invalid identity kind '+$kind.Name+' for '+$control.harness)
        }
      }
    }
    $stage=[string](Get-R4Field $control.expect 'pinStage')
    if([string]::IsNullOrWhiteSpace($stage)){$stage='complete'}
    if($null -eq $roster.Value.stages.PSObject.Properties[$stage]){throw ('R3-REGISTRY: unknown pin stage '+$stage+' for '+$control.id)}
  }
}
$available=@($registry.controls|Where-Object {@($_.profiles) -ccontains $Profile})
if($PSBoundParameters.ContainsKey('OnlyControl')){
  if($null -eq $OnlyControl -or $OnlyControl.Count -eq 0){throw 'R3-SELECTOR: explicitly empty selector'}
  $pick=[Collections.Generic.HashSet[string]]::new([StringComparer]::Ordinal)
  foreach($id in $OnlyControl){
    if([string]::IsNullOrWhiteSpace($id)){throw 'R3-SELECTOR: empty or whitespace selector'}
    if($id -cnotmatch '^[A-Z0-9]+-[A-Z0-9]+$'){throw 'R3-SELECTOR: malformed selector'}
    if(-not $pick.Add($id)){throw 'R3-SELECTOR: duplicate selector'}
    if($expectedIds -cnotcontains $id){throw 'R3-SELECTOR: unknown selector'}
    if(@($available|Where-Object {$_.id -ceq $id}).Count -ne 1){throw 'R3-SELECTOR: control unavailable for profile'}
  }
  $selected=@($available|Where-Object {$pick.Contains([string]$_.id)})
}else{$selected=@($available)}
if($selected.Count -eq 0){throw 'R3-SELECTOR: nothing selected'}
if($ProbeOnly){Write-Output ('R3 SELECT '+(@($selected|ForEach-Object {$_.id}) -join ','));exit 0}
$mode=if($HarnessRef -ceq 'base'){'base'}elseif($HarnessRef -ceq 'worktree'){'worktree'}else{'candidate'}

# ---- Evidence root; everything after this point writes RESULT.json.
if([string]::IsNullOrWhiteSpace($OutputRoot)){$OutputRoot=Join-Path $repo ('.lake/life1-r3/controls/'+$mode+'-'+$Profile+'-'+[Guid]::NewGuid().ToString('N'))}
$evidence=[IO.Path]::GetFullPath($OutputRoot)
$lakePrefix=[IO.Path]::GetFullPath((Join-Path $repo '.lake')).TrimEnd('\','/')+[IO.Path]::DirectorySeparatorChar
if(-not $evidence.StartsWith($lakePrefix,[StringComparison]::OrdinalIgnoreCase) -or (Test-Path -LiteralPath $evidence)){throw 'R3-EVIDENCE: fresh owned descendant of .lake required'}
[void][IO.Directory]::CreateDirectory($evidence)

$recipes=@{
  RC=@{harness='docs/internal/extensions/lifecycle1/repair-r1/run_controls.ps1';laneOwned=$true
    files=@(@('docs/internal/extensions/lifecycle1/repair-r1/run_controls.ps1','ref'),
      @('docs/internal/extensions/lifecycle1/repair-r1/runtime_profile.ps1','worktree'),
      @('docs/internal/extensions/lifecycle1/repair-r1/CONTROL_REGISTRY.json','ref'),
      @('docs/internal/extensions/lifecycle1/repair-r1/CONTROL_REGISTRY.frozen.json','ref'),
      @('docs/internal/extensions/lifecycle1/repair-r1/selector_cases.json','worktree'),
      @('docs/internal/extensions/lifecycle1/repair-r1/dependency_boundary_cases.json','worktree'),
      @('docs/internal/extensions/lifecycle1/repair-r1/finalizer_cases.json','ref'),
      @('docs/internal/extensions/lifecycle1/repair-r1/selector_child.ps1','worktree'),
      @('docs/internal/extensions/lifecycle1/repair-r1/deadline_control.ps1','worktree'),
      @('docs/internal/extensions/lifecycle1/repair-r1/finalizer_control.ps1','ref'),
      @('docs/internal/extensions/lifecycle1/repair-r1/dependency_child.ps1','double:control_child.ps1'),
      @('scripts/lifecycle_validator.ps1','ref'),@('scripts/lifecycle_validator_environment.ps1','worktree'),
      @('scripts/lifecycle_dependency_replay.ps1','worktree'),@('scripts/owned_process_tree.ps1','worktree'),
      @('scripts/lifecycle_dependency_cases.json','worktree'),@('.lake/build/bin/rmq_lifecycle_validate.exe','inert'))
    args=@('-Shell','{SHELL}','-Profile','{PROFILE}','-OnlyCase','D07_ENV_VALID','-EvidenceRoot','{ROOT}/.lake/r3-evidence')
    durable=@{dir='.lake/r3-evidence';child=$null;files=@('summary.json')}
    target='scripts/lifecycle_validator.ps1';remove='.lake/build/bin/rmq_lifecycle_validate.exe'}
  FC=@{harness='docs/internal/extensions/lifecycle1/repair-r1/finalizer_control.ps1';laneOwned=$false
    files=@(@('docs/internal/extensions/lifecycle1/repair-r1/finalizer_control.ps1','ref'),
      @('docs/internal/extensions/lifecycle1/repair-r1/finalizer_cases.json','ref'),
      @('scripts/owned_process_tree.ps1','worktree'),@('scripts/lifecycle_dependency_replay.ps1','generated:finalizer-production'))
    args=@('-Case','F01_INTACT_SUCCESS','-Shell','{SHELL}','-RepositoryRoot','{ROOT}','-EvidenceRoot','{ROOT}/.lake/r3-evidence')
    durable=@{dir='.lake/r3-evidence';child='^F01_INTACT_SUCCESS-[0-9a-f]{32}$';files=@('result.json')}
    target='scripts/lifecycle_dependency_replay.ps1';remove='scripts/owned_process_tree.ps1'}
  K1=@{harness='docs/internal/extensions/lifecycle1/repair-r1/run_check.ps1';laneOwned=$false
    files=@(,@('docs/internal/extensions/lifecycle1/repair-r1/run_check.ps1','ref'))
    args=@('-SpecPath','{ROOT}/r3-spec.json')
    durable=@{dir='.lake/repair-r1/checks/r3-control';child=$null;files=@('result.json')}
    target='lakefile.toml';remove='scripts/owned_process_tree.ps1'}
  K2=@{harness='docs/internal/extensions/lifecycle1/repair-r2/run_check.ps1';laneOwned=$false
    files=@(,@('docs/internal/extensions/lifecycle1/repair-r2/run_check.ps1','ref'))
    args=@('-SpecPath','{ROOT}/r3-spec.json')
    durable=@{dir='.lake/repair-r2/checks/r3-control';child=$null;files=@('result.json')}
    target='lakefile.toml';remove='scripts/owned_process_tree.ps1'}
  DC=@{harness='docs/internal/extensions/lifecycle1/repair-r1/dependency_child.ps1';laneOwned=$false
    files=@(@('docs/internal/extensions/lifecycle1/repair-r1/dependency_child.ps1','ref'),
      @('scripts/lifecycle_dependency_replay.ps1','double:dependency_replay.ps1'),
      @('scripts/lifecycle_dependency_cases.json','worktree'),@('r3-spec.json','generated:dc-spec'))
    args=@('-SpecPath','{ROOT}/r3-spec.json','-RepositoryRoot','{ROOT}','-EvidenceRoot','{ROOT}/.lake/r3-evidence')
    durable=@{dir='.lake/r3-evidence';child=$null;files=@('receipt.json')}
    target='scripts/lifecycle_dependency_replay.ps1';remove='scripts/lifecycle_dependency_replay.ps1'}
  LV=@{harness='scripts/lifecycle_validator.ps1';laneOwned=$true
    files=@(@('scripts/lifecycle_validator.ps1','ref'),@('scripts/lifecycle_validator_environment.ps1','worktree'),
      @('scripts/owned_process_tree.ps1','worktree'),@('lakefile.toml','worktree'),
      @('RMQ/Validation/PackedLifecycle.lean','worktree'),@('RMQ/Core/WordRAM/Lifecycle/Executable.lean','worktree'),
      @('RMQ/Core/WordRAM/Lifecycle/Controls.lean','worktree'),@('RMQ/Core/WordRAM/Lifecycle/ArrayRun.lean','worktree'),
      @('RMQ/Core/WordRAM/Lifecycle/Machine.lean','worktree'),@('RMQ/Core/WordRAM/Lifecycle/Program.lean','worktree'),
      @('RMQ/Core/WordRAM/Lifecycle/Service.lean','worktree'),@('.lake/build/bin/rmq_lifecycle_validate.exe','exe-double'))
    args=@('-Stage','single','-Case','L01-W-EMPTY','-DeadlineSeconds','60')
    durable=@{dir='.lake/lifecycle-validator';child='^[0-9a-f]{32}$';files=@('RESULT.json','PASS.json')}
    target='lakefile.toml';remove='RMQ/Core/WordRAM/Lifecycle/Service.lean'}
  IC=@{harness='docs/internal/extensions/lifecycle-native-p0/repair-r1/integrity_controls.ps1';laneOwned=$false
    files=@(@('docs/internal/extensions/lifecycle-native-p0/repair-r1/integrity_controls.ps1','ref'),
      @('scripts/packed_native_lifecycle_storage_replay.ps1','worktree'),@('scripts/packed_native_lifecycle_integrity_check.ps1','worktree'),
      @('scripts/owned_process_tree.ps1','worktree'),@('scripts/packed_native_lifecycle_stream_check.ps1','generated:stream-double'),
      @('native/packed-rmq/tests/lifecycle_storage_probe.c','worktree'),@('lean-toolchain','worktree'),
      @('docs/internal/extensions/lifecycle-native-p0/REGISTRY.json','worktree'))
    args=@('-OutputRoot','{ROOT}/.lake/r3-out','-ControlIds','intact-success')
    durable=@{dir='.lake/r3-out';child=$null;files=@('RESULTS.json')}
    target='lean-toolchain';remove='native/packed-rmq/tests/lifecycle_storage_probe.c'}
  DP=@{harness='docs/internal/extensions/lifecycle-native-p0/repair-r1/dependency_controls.ps1';laneOwned=$false
    files=@(@('docs/internal/extensions/lifecycle-native-p0/repair-r1/dependency_controls.ps1','ref'),
      @('scripts/owned_process_tree.ps1','worktree'),@('scripts/packed_native_lifecycle_integrity_check.ps1','generated:integrity-double'),
      @('docs/internal/extensions/lifecycle-native-p0/RESULTS.json','worktree'))
    args=@('-OutputRoot','{ROOT}/.lake/r3-out')
    durable=@{dir='.lake/r3-out';child=$null;files=@('RESULTS.json')}
    target='docs/internal/extensions/lifecycle-native-p0/RESULTS.json';remove='docs/internal/extensions/lifecycle-native-p0/RESULTS.json'}
  HS=@{harness='docs/internal/extensions/lifecycle-native-p0/repair-r2/harness_stream_controls.ps1';laneOwned=$true
    files=@(@('docs/internal/extensions/lifecycle-native-p0/repair-r2/harness_stream_controls.ps1','ref'),
      @('docs/internal/extensions/lifecycle-native-p0/repair-r2/HARNESS_STREAM_REGISTRY.json','worktree'),
      @('docs/internal/extensions/lifecycle-native-p0/repair-r1/integrity_controls.ps1','ref'),
      @('scripts/packed_native_lifecycle_storage_replay.ps1','worktree'),@('scripts/packed_native_lifecycle_integrity_check.ps1','worktree'),
      @('scripts/owned_process_tree.ps1','worktree'),@('scripts/packed_native_lifecycle_stream_check.ps1','generated:stream-double'),
      @('native/packed-rmq/tests/lifecycle_storage_probe.c','worktree'),@('lean-toolchain','worktree'),
      @('docs/internal/extensions/lifecycle-native-p0/REGISTRY.json','worktree'))
    args=@('-OutputRoot','{ROOT}/.lake/r3-out','-ControlIds','selector-empty')
    durable=@{dir='.lake/r3-out';child=$null;files=@('RESULTS.json')}
    target='lean-toolchain';remove='native/packed-rmq/tests/lifecycle_storage_probe.c'}
}
$runCheckSupport=@('scripts/owned_process_tree.ps1','scripts/lifecycle_validator.ps1','scripts/lifecycle_validator_environment.ps1',
  'scripts/lifecycle_dependency_replay.ps1','scripts/lifecycle_dependency_cases.json','RMQ/Validation/PackedLifecycle.lean',
  'RMQ/Validation/LifecycleContract.lean','scripts/lifecycle_provenance_contract.lean','lean-toolchain','lakefile.toml')
foreach($k in @('K1','K2')){
  foreach($p in $runCheckSupport){$recipes[$k].files+=,@($p,$(if($p -ceq 'scripts/lifecycle_validator.ps1'){'ref'}else{'worktree'}))}
  $recipes[$k].files+=,@('r3-stage.ps1','double:stage.ps1')
  $recipes[$k].files+=,@('r3-spec.json','generated:k-spec')
}

function Get-R3Values([object]$Node,[string]$Name,[Collections.Generic.List[object]]$Sink) {
  if($null -eq $Node){return}
  if($Node -is [string]){$Sink.Add([pscustomobject]@{name=$Name;value=$Node});return}
  if($Node -is [ValueType]){$Sink.Add([pscustomobject]@{name=$Name;value=$Node});return}
  if($Node -is [Management.Automation.PSCustomObject]){
    foreach($p in $Node.PSObject.Properties){if($p.Name -cne 'pinChecks'){Get-R3Values $p.Value $p.Name $Sink}}
    return
  }
  if($Node -is [Collections.IEnumerable]){foreach($item in $Node){Get-R3Values $item $Name $Sink};return}
}
function Test-R3Groups([object[]]$Groups,[object[]]$Strings) {
  foreach($group in @($Groups)){
    $hit=$false
    foreach($s in @($Strings)){
      if($s -isnot [string]){continue}
      $all=$true
      foreach($needle in @($group)){if($s.IndexOf([string]$needle,[StringComparison]::Ordinal) -lt 0){$all=$false;break}}
      if($all){$hit=$true;break}
    }
    if(-not $hit){return $false}
  }
  return $true
}
function Invoke-R3Owned([string]$File,[string[]]$Arguments,[string]$Cwd,[string]$Stage,[int]$Deadline,[string]$Temp,[hashtable]$Environment=@{}) {
  return Invoke-RMQOwnedBoundedProcess -FilePath $File -Arguments $Arguments -WorkingDirectory $Cwd -Stage $Stage `
    -DeadlineSeconds $Deadline -OutputLimitBytes 8388608 -TempRoot $Temp -Environment $Environment
}
function Assert-R3Completed([object]$R,[string]$What) {
  if($R.TimedOut -or $R.OutputLimitExceeded -or $R.ExitCode -ne 0 -or $R.Ownership -cne 'kill-on-close-job' -or @($R.TerminatedIds).Count -ne 0){
    throw ('R3-SETUP: '+$What+' failed: exit='+$R.ExitCode+' timeout='+$R.TimedOut+' stderr='+(@($R.StandardError) -join ' | '))
  }
}
function Get-R3TreeFiles([string]$Root) {
  $prefix=[IO.Path]::GetFullPath($Root).TrimEnd('\','/')+[IO.Path]::DirectorySeparatorChar
  $list=[Collections.Generic.List[string]]::new()
  foreach($f in [IO.Directory]::EnumerateFiles($Root,'*',[IO.SearchOption]::AllDirectories)){
    $rel=$f.Substring($prefix.Length).Replace('\','/')
    if($rel.StartsWith('.git/') -or $rel.StartsWith('.lake/')){continue}
    $list.Add($rel)
  }
  return @($list.ToArray())
}

$results=[Collections.Generic.List[object]]::new()
$stageError=$null;$stageRecord=$null
$integrityErrors=[Collections.Generic.List[string]]::new()
$cleanupErrors=[Collections.Generic.List[string]]::new()
$pinChecks=[Collections.Generic.List[object]]::new()
$entryPins=[ordered]@{}
$worktreeBefore=$null;$refSha=$null;$completed=$false
$startedUtc=[DateTime]::UtcNow
$exeDouble=$null
try {
  . (Join-Path $repo 'scripts/owned_process_tree.ps1')
  $inputs=@('FAILURE_CONTROL_REGISTRY.json','failure_controls.ps1','doubles/fault_function.ps1','doubles/control_child.ps1',
    'doubles/stage.ps1','doubles/dependency_replay.ps1','doubles/stream_capture_override.ps1',
    'doubles/complete_integrity_override.ps1','doubles/validator_double.cs')
  foreach($name in $inputs){$entryPins['docs/internal/extensions/lifecycle1/repair-r3/'+$name]=Get-R3FileSha256 (Join-Path $here $name)}
  $entryPins['scripts/owned_process_tree.ps1']=Get-R3FileSha256 (Join-Path $repo 'scripts/owned_process_tree.ps1')
  foreach($name in @('predicates.ps1','doubles/git_double.cs','FAILURE_CONTROL_REGISTRY.json')){$entryPins['docs/internal/extensions/lifecycle1/repair-r4/'+$name]=Get-R3FileSha256 (Join-Path $r4Dir $name)}
  $registryFull=[IO.Path]::GetFullPath($RegistryPath)
  if(@($entryPins.Keys|Where-Object {[IO.Path]::GetFullPath((Join-Path $repo $_)) -ieq $registryFull}).Count -eq 0){$entryPins[$registryFull]=Get-R3FileSha256 $registryFull}
  . (Join-Path $r4Dir 'predicates.ps1')
  $git=(Get-Command git -CommandType Application|Select-Object -First 1).Source
  $work=Join-Path $evidence 'work'
  [void][IO.Directory]::CreateDirectory($work)
  $statusScript=Join-Path $work 'git-state.ps1'
  [IO.File]::WriteAllText($statusScript,@'
param([string]$Git,[string]$Root,[string]$Out)
$ErrorActionPreference='Stop'
$lines=@(& $Git -C $Root -c core.excludesfile= status --porcelain=v1 --untracked-files=all)
if($LASTEXITCODE){throw 'git status failed'}
$head=@(& $Git -C $Root rev-parse HEAD)
if($LASTEXITCODE){throw 'git rev-parse failed'}
[IO.File]::WriteAllText($Out,(($head+@('--')+$lines) -join "`n"),[Text.UTF8Encoding]::new($false))
'@,$utf8)
  function Get-R3GitState([string]$Root,[string]$Label) {
    $out=Join-Path $work ($Label+'-'+[Guid]::NewGuid().ToString('N')+'.txt')
    $r=Invoke-R3Owned $shells.pwsh @('-NoLogo','-NoProfile','-File',$statusScript,'-Git',$git,'-Root',$Root,'-Out',$out) $Root ('git-state-'+$Label) 120 (Join-Path $work 'git-process')
    Assert-R3Completed $r ('git state '+$Label)
    return [IO.File]::ReadAllText($out,$utf8)
  }
  $worktreeBefore=Get-R3GitState $repo 'worktree-before'
  # Resolve the harness ref and export every needed blob with exact bytes.
  $resolveOut=Join-Path $work 'ref.txt'
  $exportScript=Join-Path $work 'export-blobs.ps1'
  [IO.File]::WriteAllText($exportScript,@'
param([string]$Git,[string]$Root,[string]$Ref,[string]$ListPath,[string]$RefOut)
$ErrorActionPreference='Stop'
$sha=(& $Git -C $Root rev-parse --verify ($Ref+'^{commit}')).Trim()
if($LASTEXITCODE -or $sha -cnotmatch '^[0-9a-f]{40}$'){throw 'ref resolution failed'}
[IO.File]::WriteAllText($RefOut,$sha,[Text.UTF8Encoding]::new($false))
foreach($line in [IO.File]::ReadAllLines($ListPath)){
  if(-not $line){continue}
  $parts=$line.Split([char]9)
  $p=[Diagnostics.Process]::new()
  $p.StartInfo.FileName=$Git
  $p.StartInfo.Arguments='-C "'+$Root+'" cat-file blob '+$sha+':'+$parts[0]
  $p.StartInfo.UseShellExecute=$false
  $p.StartInfo.RedirectStandardOutput=$true
  $p.StartInfo.RedirectStandardError=$true
  $f=$null
  try {
    if(-not $p.Start()){throw 'git did not start'}
    [void][IO.Directory]::CreateDirectory([IO.Path]::GetDirectoryName($parts[1]))
    $f=[IO.File]::Create($parts[1])
    $p.StandardOutput.BaseStream.CopyTo($f)
    $f.Dispose();$f=$null
    $err=$p.StandardError.ReadToEnd()
    $p.WaitForExit()
    if($p.ExitCode -ne 0 -or $err.Length -ne 0){throw ('blob export failed '+$parts[0]+': '+$err)}
  } finally {if($null -ne $f){$f.Dispose()};$p.Dispose()}
}
'@,$utf8)
  $refPath=if($mode -ceq 'base'){$baseSha}elseif($mode -ceq 'worktree'){'HEAD'}else{$HarnessRef}
  $blobRoot=Join-Path $work 'blobs'
  $needed=[Collections.Generic.HashSet[string]]::new([StringComparer]::Ordinal)
  foreach($c in $selected){foreach($f in $recipes[[string]$c.harness].files){if($f[1] -ceq 'ref'){[void]$needed.Add($f[0])}}}
  [void]$needed.Add('docs/internal/extensions/lifecycle1/repair-r1/CONTROL_REGISTRY.frozen.json')
  $listPath=Join-Path $work 'blobs.tsv'
  [IO.File]::WriteAllText($listPath,((@($needed)|Sort-Object|ForEach-Object {$_+[char]9+(Join-Path $blobRoot $_)}) -join "`n"),$utf8)
  $r=Invoke-R3Owned $shells.pwsh @('-NoLogo','-NoProfile','-File',$exportScript,'-Git',$git,'-Root',$repo,'-Ref',$refPath,'-ListPath',$listPath,'-RefOut',$resolveOut) $repo 'export-blobs' 300 (Join-Path $work 'export-process')
  Assert-R3Completed $r 'blob export'
  $refSha=[IO.File]::ReadAllText($resolveOut,$utf8)
  if($mode -ceq 'base' -and $refSha -cne $baseSha){throw 'R3-SETUP: base ref resolution differs'}
  if($mode -ceq 'worktree'){
    # Development-loop only: the nine harness files come from the working tree
    # (line endings normalized to the Git blob form); receipts record this mode.
    foreach($prop in $registry.harnessKeys.PSObject.Properties){
      $rel=[string]$prop.Value;$dst=Join-Path $blobRoot $rel
      if([IO.File]::Exists($dst)){[IO.File]::WriteAllBytes($dst,$utf8.GetBytes([IO.File]::ReadAllText((Join-Path $repo $rel),$utf8).Replace("`r`n","`n")))}
    }
  }
  $faultText=[IO.File]::ReadAllText((Join-Path $here 'doubles/fault_function.ps1'),$utf8).Replace("`r`n","`n")
  function Get-R3Double([string]$Name) {
    $t=[IO.File]::ReadAllText((Join-Path $here ('doubles/'+$Name)),$utf8).Replace("`r`n","`n")
    if(([regex]::Matches($t,'(?m)^# R3-FAULT-FUNCTION$')).Count -ne 1){throw ('R3-SETUP: double placeholder differs '+$Name)}
    return $t.Replace('# R3-FAULT-FUNCTION',$faultText.TrimEnd("`n"))
  }
  if(@($selected|Where-Object {$_.harness -ceq 'LV'}).Count){
    $csc='C:/Windows/Microsoft.NET/Framework64/v4.0.30319/csc.exe'
    $exeDouble=Join-Path $work 'bin/rmq_lifecycle_validate.exe'
    [void][IO.Directory]::CreateDirectory((Split-Path -Parent $exeDouble))
    $r=Invoke-R3Owned $csc @('/nologo','/target:exe','/optimize+',('/out:'+$exeDouble),(Join-Path $here 'doubles/validator_double.cs')) $work 'compile-validator-double' 180 (Join-Path $work 'csc-process')
    Assert-R3Completed $r 'validator double compilation'
  }
  $gitDoubleDir=$null
  if(@($selected|Where-Object {[bool](Get-R4Field $_ 'gitDouble')}).Count){
    $csc='C:/Windows/Microsoft.NET/Framework64/v4.0.30319/csc.exe'
    $gitDoubleDir=Join-Path $work 'gitbin'
    [void][IO.Directory]::CreateDirectory($gitDoubleDir)
    $r=Invoke-R3Owned $csc @('/nologo','/target:exe','/optimize+',('/out:'+(Join-Path $gitDoubleDir 'git.exe')),(Join-Path $r4Dir 'doubles/git_double.cs')) $work 'compile-git-double' 180 (Join-Path $work 'csc-git-process')
    Assert-R3Completed $r 'git double compilation'
  }
  $d07=@(([IO.File]::ReadAllText((Join-Path $blobRoot 'docs/internal/extensions/lifecycle1/repair-r1/CONTROL_REGISTRY.frozen.json'),$utf8)|ConvertFrom-Json).cases|Where-Object {$_.id -ceq 'D07_ENV_VALID'})
  if($d07.Count -ne 1){throw 'R3-SETUP: frozen D07 spec unavailable'}
  $setupScript=Join-Path $work 'git-setup.ps1'
  [IO.File]::WriteAllText($setupScript,@'
param([string]$Git,[string]$Root)
$ErrorActionPreference='Stop'
& $Git -C $Root init -q
if($LASTEXITCODE){throw 'git init failed'}
& $Git -C $Root config core.autocrlf false
if($LASTEXITCODE){throw 'git config failed'}
& $Git -C $Root -c core.excludesfile= add --all
if($LASTEXITCODE){throw 'git add failed'}
& $Git -C $Root -c user.name=RMQR3Control -c user.email=control@invalid commit -qm r3-disposable-baseline
if($LASTEXITCODE){throw 'git commit failed'}
'@,$utf8)

  foreach($control in $selected){
    $id=[string]$control.id
    $recipe=$recipes[[string]$control.harness]
    $ctl=Join-Path $evidence ('controls/'+$id)
    $root=Join-Path $ctl 'root'
    $pristine=Join-Path $ctl 'pristine'
    $record=[ordered]@{id=$id;harness=[string]$control.harness;shape=[string]$control.shape;fault=[string]$control.fault
      mode=$mode;profile=$Profile;deadlineSeconds=[int]$control.deadlineSeconds;root=$root;setupError=$null;launchError=$null
      process=$null;durable=$null;core=$null;structural=$null;restoration=$null;verdict='FAIL';expected=$null;lockWaitSeconds=$null;trustedPinContext=$null}
    $lane=$null;$laneHeld=$false
    try {
      [void][IO.Directory]::CreateDirectory($root)
      $shellPath=$shells[$Profile]
      $trustedPinContext=[ordered]@{
        fixtureRoot=[IO.Path]::GetFullPath($root)
        childShell=[IO.Path]::GetFullPath($shellPath)
        hostShell=[IO.Path]::GetFullPath($shellPath)
        toolchainBin=$null
        historicalSummary=$null
        historicalSummarySource=$null
      }
      if($registryVersion -eq 3 -and [string]$control.harness -ceq 'DP'){
        $trustedPinContext.toolchainBin=[IO.Path]::GetFullPath([string]$registry.trustedPathContexts.DP.toolchainBin)
      }
      $manifestPaths=[Collections.Generic.List[string]]::new()
      foreach($f in $recipe.files){
        $rel=[string]$f[0];$source=[string]$f[1]
        $dest=Join-Path $root $rel
        [void][IO.Directory]::CreateDirectory((Split-Path -Parent $dest))
        $bytes=$null
        if($source -ceq 'ref'){$bytes=[IO.File]::ReadAllBytes((Join-Path $blobRoot $rel))}
        elseif($source -ceq 'worktree'){$bytes=[IO.File]::ReadAllBytes((Join-Path $repo $rel))}
        elseif($source -ceq 'inert'){$bytes=$utf8.GetBytes('LIFE-1-R3 inert pinned placeholder; never executed')}
        elseif($source -ceq 'exe-double'){$bytes=[IO.File]::ReadAllBytes($exeDouble)}
        elseif($source.StartsWith('double:')){$bytes=$utf8.GetBytes((Get-R3Double $source.Substring(7)))}
        elseif($source -ceq 'generated:finalizer-production'){
          $t=[IO.File]::ReadAllText((Join-Path $repo $rel),$utf8)
          $nl=if($t.Contains("`r`n")){"`r`n"}else{"`n"}
          $anchor='function Write-Json([string]$name,[object]$value) {'+$nl
          if(([regex]::Matches($t,[regex]::Escape($anchor))).Count -ne 1){throw 'R3-SETUP: production Write-Json anchor differs'}
          $hook=($faultText.TrimEnd("`n")+"`n"+"if(Invoke-R3Fault){throw 'R3-DOUBLE: injected ordinary stage failure'}").Replace("`n",$nl)+$nl
          $bytes=$utf8.GetBytes($t.Replace($anchor,$anchor+$hook))
        }
        elseif($source -ceq 'generated:stream-double' -or $source -ceq 'generated:integrity-double'){
          $t=[IO.File]::ReadAllText((Join-Path $repo $rel),$utf8)
          $nl=if($t.Contains("`r`n")){"`r`n"}else{"`n"}
          $name=if($source -ceq 'generated:stream-double'){'stream_capture_override.ps1'}else{'complete_integrity_override.ps1'}
          $bytes=$utf8.GetBytes($t+$nl+(Get-R3Double $name).Replace("`n",$nl))
        }
        elseif($source -ceq 'generated:k-spec'){
          $deadline=if([string]$control.variant -ceq 'deadline-zero'){0}elseif([string]$control.variant -ceq 'deadline-short'){3}else{60}
          $spec=[ordered]@{name='r3-control';file=$shellPath;arguments=@('-NoLogo','-NoProfile','-File',(Join-Path $root 'r3-stage.ps1'));mutex=$false;deadline=$deadline}
          $bytes=$utf8.GetBytes(($spec|ConvertTo-Json -Depth 5))
        }
        elseif($source -ceq 'generated:dc-spec'){$bytes=$utf8.GetBytes(($d07[0].spec|ConvertTo-Json -Depth 40))}
        else{throw ('R3-SETUP: unknown file source '+$source)}
        [IO.File]::WriteAllBytes($dest,$bytes)
        $manifestPaths.Add($rel)
      }
      if($registryVersion -eq 3 -and [string]$control.harness -ceq 'DP'){
        # Read the pinned copied input before the child runs. The returned
        # pinChecks never define their own expected historical-summary path.
        $resultsInput=[IO.Path]::GetFullPath((Join-Path $root 'docs/internal/extensions/lifecycle-native-p0/RESULTS.json'))
        $trustedResults=[IO.File]::ReadAllText($resultsInput,$utf8)|ConvertFrom-Json
        $rawSummary=$trustedResults.PSObject.Properties['rawSummary']
        $rawPath=if($null -ne $rawSummary){[string](Get-R4Field $rawSummary.Value 'path')}else{$null}
        if([string]::IsNullOrWhiteSpace($rawPath) -or -not [IO.Path]::IsPathRooted($rawPath)){throw 'R3-SETUP: trusted DP historical summary path unavailable'}
        $trustedPinContext.historicalSummary=[IO.Path]::GetFullPath($rawPath)
        $trustedPinContext.historicalSummarySource=$resultsInput
      }
      $record.trustedPinContext=$trustedPinContext
      [IO.File]::WriteAllText((Join-Path $root '.gitignore'),".lake/`n",$utf8)
      $manifestPaths.Add('.gitignore')
      if([bool]$control.removeAtSetup){
        $removeRel=if($null -ne (Get-R4Field $control 'removePath')){[string]$control.removePath}else{[string]$recipe.remove}
        $gone=Join-Path $root $removeRel
        if(-not [IO.File]::Exists($gone)){throw ('R3-SETUP: file to remove is absent '+$removeRel)}
        [IO.File]::Delete($gone)
        [void]$manifestPaths.Remove($removeRel)
        $record.removedAtSetup=$removeRel
      }
      $r=Invoke-R3Owned $shells.pwsh @('-NoLogo','-NoProfile','-File',$setupScript,'-Git',$git,'-Root',$root) $root ('git-setup-'+$id) 120 (Join-Path $ctl 'setup-process')
      Assert-R3Completed $r 'disposable git baseline'
      $manifest=[ordered]@{}
      foreach($rel in $manifestPaths){
        $src=Join-Path $root $rel;$dst=Join-Path $pristine $rel
        [void][IO.Directory]::CreateDirectory((Split-Path -Parent $dst))
        [IO.File]::Copy($src,$dst,$true)
        $manifest[$rel]=Get-R3FileSha256 $src
      }
      $record.manifest=$manifest
      $record.harnessSha256=$manifest[$recipe.harness]
      $arguments=@('-NoLogo','-NoProfile','-ExecutionPolicy','Bypass','-File',(Join-Path $root $recipe.harness))
      $variantArgs=@($recipe.args)
      if([string]$control.variant -ceq 'harness-carrier'){$variantArgs=@('-OutputRoot','{ROOT}/.lake/r3-out','-ControlIds','success-positive')}
      foreach($a in $variantArgs){$arguments+=([string]$a).Replace('{ROOT}',$root).Replace('{SHELL}',$shellPath).Replace('{PROFILE}',$Profile)}
      $targetRel=if($null -ne (Get-R4Field $control 'faultTarget')){[string]$control.faultTarget}else{[string]$recipe.target}
      $environment=@{R3_FAULT_MODE=[string]$control.fault;R3_FAULT_TARGET=(Join-Path $root $targetRel);R3_FAULT_MARKER=(Join-Path $ctl 'fault.marker');R3_FAULT_SCOPE=$root}
      if([bool](Get-R4Field $control 'gitDouble')){
        $environment.PATH=$gitDoubleDir+[IO.Path]::PathSeparator+[Environment]::GetEnvironmentVariable('PATH')
        $environment.R3_REAL_GIT=$git
      }
      $record.arguments=$arguments;$record.environment=$environment
      if(-not $recipe.laneOwned){
        $lane=[Threading.Mutex]::new($false,'Local\RMQLifecycleImplementationHeavy20260920')
        $watch=[Diagnostics.Stopwatch]::StartNew()
        try{$laneHeld=$lane.WaitOne(7200000)}catch [Threading.AbandonedMutexException]{$laneHeld=$true}
        $record.lockWaitSeconds=[Math]::Round($watch.Elapsed.TotalSeconds,3)
        if(-not $laneHeld){throw 'R3-SCHEDULING: lane mutex unavailable'}
      }
      try {
        $p=Invoke-R3Owned $shellPath $arguments $root $id ([int]$control.deadlineSeconds) (Join-Path $ctl 'process') $environment
        $record.process=$p
      } catch {$record.launchError=$_.Exception.Message}
      finally {
        if($laneHeld){try{$lane.ReleaseMutex()}catch{$cleanupErrors.Add($id+': lane release: '+$_.Exception.Message)}}
        if($null -ne $lane){$lane.Dispose()}
        $laneHeld=$false;$lane=$null
      }
      # Durable result.
      $dir=Join-Path $root $recipe.durable.dir
      $durablePath=$null;$ambiguous=$false
      if($null -ne $recipe.durable.child){
        $kids=@(if([IO.Directory]::Exists($dir)){Get-ChildItem -LiteralPath $dir -Directory|Where-Object {$_.Name -cmatch $recipe.durable.child}})
        if($kids.Count -gt 1){$ambiguous=$true}elseif($kids.Count -eq 1){$dir=$kids[0].FullName}else{$dir=$null}
      }
      if($null -ne $dir -and -not $ambiguous){foreach($name in $recipe.durable.files){$c=Join-Path $dir $name;if([IO.File]::Exists($c)){$durablePath=$c;break}}}
      $doc=$null;$parseError=$null
      if($null -ne $durablePath){try{$doc=[IO.File]::ReadAllText($durablePath,$utf8)|ConvertFrom-Json}catch{$parseError=$_.Exception.Message}}
      $record.durable=[ordered]@{path=$durablePath;ambiguous=$ambiguous;parseError=$parseError
        sha256=$(if($null -ne $durablePath){Get-R3FileSha256 $durablePath}else{$null})}
      $values=[Collections.Generic.List[object]]::new()
      if($null -ne $doc){Get-R3Values $doc '' $values}
      $strings=@($values|ForEach-Object {$_.value}|Where-Object {$_ -is [string]})
      $expect=$control.expect
      $proc=$record.process
      $completedLaunch=$null -ne $proc -and -not $proc.TimedOut -and -not $proc.OutputLimitExceeded -and $proc.Ownership -ceq 'kill-on-close-job' -and @($proc.TerminatedIds).Count -eq 0
      $exitOk=$completedLaunch -and $(if($expect.exit -ceq 'zero'){$proc.ExitCode -eq 0}else{$proc.ExitCode -ne 0})
      $exitCodeWanted=Get-R4Field $expect 'exitCode'
      if($null -ne $exitCodeWanted){$exitOk=$exitOk -and $proc.ExitCode -eq [int]$exitCodeWanted}
      $durableAbsentWanted=[bool](Get-R4Field $expect 'durableAbsent')
      $stageOk=$true
      if($null -ne $expect.stage -or $null -ne $expect.stageValue){
        $byText=($null -ne $expect.stage) -and (Test-R3Groups @($expect.stage) $strings)
        $byValue=$false
        if($null -ne $expect.stageValue){$byValue=@($values|Where-Object {$_.name -ceq [string]$expect.stageValue.name -and $_.value -is [ValueType] -and [double]$_.value -eq [double]$expect.stageValue.value}).Count -gt 0}
        $stageOk=$byText -or $byValue
      }
      $integrityOk=$true
      if($null -ne $expect.integrity){$integrityOk=Test-R3Groups @($expect.integrity) $strings}
      # LIFE-1-R4 optional core predicates (absent fields are vacuously true).
      $fin=$null
      if($null -ne $doc -and $null -ne $doc.PSObject.Properties['finalization']){$fin=$doc.finalization}
      $durableOk=if($durableAbsentWanted){$null -eq $durablePath -and -not $ambiguous}else{$null -ne $doc}
      $cleanupWanted=Get-R4Field $expect 'cleanup'
      $cleanupOk=if($null -ne $cleanupWanted){Test-R3Groups @($cleanupWanted) $strings}else{$true}
      $verdictWanted=Get-R4Field $expect 'verdict'
      $verdictOk=if($null -ne $verdictWanted){$null -ne $fin -and [string]$fin.verdict -ceq [string]$verdictWanted}else{$true}
      $valuesWanted=Get-R4Field $expect 'values'
      $valuesCheck=if($null -ne $valuesWanted){Test-R4Values @($values.ToArray()) @($valuesWanted)}else{$null}
      $labelsWanted=Get-R4Field $expect 'labels'
      $labelsCheck=if($null -ne $labelsWanted){Test-R4Labels $doc @($labelsWanted)}else{$null}
      $stderrWanted=Get-R4Field $expect 'stderr'
      $stderrOk=if($null -ne $stderrWanted){$null -ne $proc -and (Test-R3Groups @($stderrWanted) @(@($proc.StandardError)|ForEach-Object {[string]$_}))}else{$true}
      $absentFiles=@(Get-R4Field $expect 'absentFiles'|Where-Object {$null -ne $_})
      $absentOk=$true
      foreach($name in $absentFiles){if($null -ne $dir -and [IO.File]::Exists((Join-Path $dir ([string]$name)))){$absentOk=$false}}
      $stdoutAbsent=@(Get-R4Field $expect 'stdoutAbsent'|Where-Object {$null -ne $_})
      $stdoutOk=$true
      foreach($needle in $stdoutAbsent){if($null -ne $proc -and @(@($proc.StandardOutput)|Where-Object {([string]$_).Contains([string]$needle)}).Count){$stdoutOk=$false}}
      $record.core=[ordered]@{launchCompleted=$completedLaunch;exitClass=$exitOk;durablePresent=($null -ne $doc);durableAsExpected=$durableOk;
        stageRecorded=$stageOk;integrityRecorded=$integrityOk;cleanupRecorded=$cleanupOk;verdictAsExpected=$verdictOk
        values=$valuesCheck;labels=$labelsCheck;stderrAsExpected=$stderrOk;absentFiles=$absentOk;stdoutWithoutSuccess=$stdoutOk}
      $coreAll=$completedLaunch -and $exitOk -and $durableOk -and $stageOk -and $integrityOk -and $cleanupOk -and $verdictOk -and
        ($null -eq $valuesCheck -or $valuesCheck.ok) -and ($null -eq $labelsCheck -or $labelsCheck.ok) -and $stderrOk -and $absentOk -and $stdoutOk
      # Structural predicates of the repaired finalization contract.
      $structural=[ordered]@{applicable=($mode -cne 'base');finalizationPresent=$false;verdictMatches=$false
        stageFieldMatches=$false;integrityFieldMatches=$false;cleanupEmpty=$false;pinCoverageApplicable=$true;pinsVerified=$false;pinCoverage=$null}
      if($durableAbsentWanted){
        # A W control has no durable result by construction. Its failed
        # exit/diagnostics are guarded by the core predicate; pin coverage is
        # inapplicable, never represented as a positive verification result.
        $structural=[ordered]@{applicable=$false;reason='no durable result by construction (durable-write failure)';finalizationPresent=$true;verdictMatches=$true
          stageFieldMatches=$true;integrityFieldMatches=$true;cleanupEmpty=$true;pinCoverageApplicable=$false;pinsVerified=$null
          pinCoverage='not applicable: guarded durable-write failure has no finalization receipt'}
      }
      elseif($null -ne $fin -and $fin.schema -ceq 'life1-r3-finalization-v1'){
        $structural.finalizationPresent=$true
        $isP=[string]$control.shape -ceq 'P'
        $structural.verdictMatches=($fin.verdict -ceq $(if($isP){'pass'}else{'fail'}))
        $stageStrings=@(@($fin.stageError)+@($(if($null -ne $fin.PSObject.Properties['childFailure']){$fin.childFailure}else{$null}))|Where-Object {$_ -is [string]})
        if($null -ne $expect.stage){$structural.stageFieldMatches=Test-R3Groups @($expect.stage) $stageStrings}
        else{$structural.stageFieldMatches=($stageStrings.Count -eq 0)}
        $integrityStrings=@(@($fin.integrityErrors)|Where-Object {$_ -is [string]})
        if($null -ne $expect.integrity){$structural.integrityFieldMatches=Test-R3Groups @($expect.integrity) $integrityStrings}
        else{$structural.integrityFieldMatches=($integrityStrings.Count -eq 0)}
        $cleanupStrings=@(@($fin.cleanupErrors)|Where-Object {$_ -is [string]})
        if($null -ne $cleanupWanted){$structural.cleanupEmpty=Test-R3Groups @($cleanupWanted) $cleanupStrings}
        else{$structural.cleanupEmpty=($cleanupStrings.Count -eq 0)}
        # V1: v3 checks the independent ordered harness roster and named capture
        # stage for every control. v1/v2 keep their historical count predicate.
        $pinRoster=$null;$pinStage=$null;$legacyCaptured=Get-R4Field $expect 'capturedPins'
        if($registryVersion -eq 3){
          $pinRoster=$registry.pinRosters.PSObject.Properties[[string]$control.harness].Value
          $pinStage=[string](Get-R4Field $expect 'pinStage')
          if([string]::IsNullOrWhiteSpace($pinStage)){$pinStage='complete'}
          $legacyCaptured=$null
        }
        $coverage=Test-R4PinCoverage $fin $legacyCaptured ($isP -or [string](Get-R4Field $expect 'pins') -ceq 'all-verified') $pinRoster $pinStage $trustedPinContext
        $structural.pinsVerified=$coverage.ok
        $structural.pinCoverage=$coverage.reason
      }
      $record.structural=$structural
      $pinStructureOk=(-not [bool]$structural.pinCoverageApplicable) -or [bool]$structural.pinsVerified
      $structuralAll=$structural.finalizationPresent -and $structural.verdictMatches -and $structural.stageFieldMatches -and $structural.integrityFieldMatches -and $structural.cleanupEmpty -and $pinStructureOk
      $record.coreAll=$coreAll;$record.structuralAll=$structuralAll
      if($mode -cne 'base'){$record.expected='accept-all-predicates';$observed=$coreAll -and $structuralAll}
      else{
        $record.expected=[string]$control.baseExpectation
        # A base rejection is attributable only when the launch completed and the
        # same harness's expected-accept P control passed in this run.
        $pairId=[string]$control.harness+'-P'
        $pair=@($results|Where-Object {$_.id -ceq $pairId})
        $record.pairing=if([string]$control.shape -ceq 'P'){'self'}elseif($pair.Count -eq 0){'P not selected in this run'}elseif($pair[0].verdict -ceq 'PASS'){'P passed'}else{'P failed'}
        $observed=if($control.baseExpectation -ceq 'accept'){$coreAll}
          elseif($control.baseExpectation -ceq 'timeout'){$null -ne $proc -and [bool]$proc.TimedOut -and $record.pairing -cne 'P failed'}
          else{(-not $coreAll) -and $completedLaunch -and $record.pairing -cne 'P failed'}
      }
      $record.predicateOutcome=$observed
    } catch {$record.setupError=$_.Exception.Message;$observed=$false}
    finally {
      # Restore every disposable byte and verify the exact prepared manifest.
      $restoration=[ordered]@{restored=@();removed=@();errors=@();verified=$false;gitClean=$false}
      try {
        if($null -ne $record['manifest']){
          foreach($rel in $record.manifest.Keys){
            $cur=Join-Path $root $rel
            if(-not [IO.File]::Exists($cur) -or (Get-R3FileSha256 $cur) -cne $record.manifest[$rel]){
              [void][IO.Directory]::CreateDirectory((Split-Path -Parent $cur))
              [IO.File]::Copy((Join-Path $pristine $rel),$cur,$true)
              $restoration.restored+=$rel
            }
          }
          foreach($rel in (Get-R3TreeFiles $root)){
            if(-not $record.manifest.Contains($rel)){[IO.File]::Delete((Join-Path $root $rel));$restoration.removed+=$rel}
          }
          $ok=$true
          foreach($rel in $record.manifest.Keys){$cur=Join-Path $root $rel;if(-not [IO.File]::Exists($cur) -or (Get-R3FileSha256 $cur) -cne $record.manifest[$rel]){$ok=$false}}
          if(@(Get-R3TreeFiles $root).Count -ne @($record.manifest.Keys|Where-Object {-not $_.StartsWith('.lake/')}).Count){$ok=$false}
          $restoration.verified=$ok
          $state=Get-R3GitState $root ('copy-'+$id)
          $restoration.gitState=$state
          $restoration.gitClean=(@($state.Split("`n")|Select-Object -Skip 2|Where-Object {$_}).Count -eq 0)
        }
      } catch {$restoration.errors+=$_.Exception.Message}
      $record.restoration=$restoration
      $record.verdict=if($observed -and $null -eq $record.setupError -and $restoration.verified -and $restoration.gitClean -and @($restoration.errors).Count -eq 0){'PASS'}else{'FAIL'}
      $results.Add($record)
      try{[IO.File]::WriteAllText((Join-Path $ctl 'CONTROL.json'),($record|ConvertTo-Json -Depth 30),$utf8)}catch{$cleanupErrors.Add($id+': control record write: '+$_.Exception.Message)}
      Write-Output ('R3 CONTROL '+$id+' '+$record.verdict+' expected='+$record.expected+' core='+$record['coreAll']+' structural='+$record['structuralAll'])
    }
  }
  if($results.Count -ne $selected.Count){throw 'R3-REGISTRY: executed control count differs from selection'}
  $completed=$true
} catch {$stageError=$_.Exception.Message;$stageRecord=$_}
finally {
  foreach($path in $entryPins.Keys){
    $final=$null;$status='verified'
    $pinFile=if([IO.Path]::IsPathRooted($path)){$path}else{Join-Path $repo $path}
    try{$final=Get-R3FileSha256 $pinFile}catch{$status='unreadable';$integrityErrors.Add('R3-INTEGRITY: final hash failed '+$path+': '+$_.Exception.Message)}
    if($null -ne $final -and $final -cne $entryPins[$path]){$status='changed';$integrityErrors.Add('R3-INTEGRITY: input changed '+$path)}
    $pinChecks.Add([ordered]@{path=$path;entrySha256=$entryPins[$path];finalSha256=$final;status=$status})
  }
  $worktreeAfter=$null
  if($null -ne $worktreeBefore){
    try{$worktreeAfter=Get-R3GitState $repo 'worktree-after';if($worktreeAfter -cne $worktreeBefore){$integrityErrors.Add('R3-INTEGRITY: real worktree Git state changed')}}
    catch{$integrityErrors.Add('R3-INTEGRITY: real worktree Git state unavailable: '+$_.Exception.Message)}
  }
  $failed=@($results|Where-Object {$_.verdict -cne 'PASS'})
  $selectedNoReceipt=@($selected|Where-Object {[bool](Get-R4Field $_.expect 'durableAbsent')}|ForEach-Object {[string]$_.id})
  $verdict=if($completed -and $null -eq $stageError -and $integrityErrors.Count -eq 0 -and $cleanupErrors.Count -eq 0 -and $failed.Count -eq 0){'pass'}else{'fail'}
  $summary=[ordered]@{schema='life1-r3-failure-control-run-v1';mode=$mode;harnessRef=$HarnessRef;harnessSha=$refSha;profile=$Profile
    registryVersion=$registryVersion;registryPath=[IO.Path]::GetFullPath($RegistryPath);registryNormalizedSha256=$registryNormalizedSha256;baseRef=$baseSha
    shell=$shells[$Profile];runnerShell=(Get-Process -Id $PID).Path;startedUtc=$startedUtc.ToString('o');finishedUtc=[DateTime]::UtcNow.ToString('o')
    selected=@($selected|ForEach-Object {$_.id});expectedCount=$selected.Count;executedCount=$results.Count
    passedCount=($results.Count-$failed.Count);failedIds=@($failed|ForEach-Object {$_.id})
    pinCoverage=[ordered]@{receiptBearingCount=($selected.Count-$selectedNoReceipt.Count);guardedNoReceiptCount=$selectedNoReceipt.Count
      guardedNoReceiptIds=$selectedNoReceipt;meaning='No-receipt guards validate failed durable writes; pin coverage is inapplicable for those controls.'}
    worktreeStateBefore=$worktreeBefore;worktreeStateAfter=$worktreeAfter
    controls=@($results.ToArray())
    finalization=[ordered]@{schema='life1-r3-finalization-v1';verdict=$verdict;stageError=$stageError
      integrityErrors=@($integrityErrors.ToArray());cleanupErrors=@($cleanupErrors.ToArray());pinChecks=@($pinChecks.ToArray())}}
  try{[IO.File]::WriteAllText((Join-Path $evidence 'RESULT.json'),($summary|ConvertTo-Json -Depth 40),$utf8)}
  catch{$verdict='fail';[Console]::Error.WriteLine('R3-RESULT: durable result write failed: '+$_.Exception.Message)}
}
foreach($e in @($integrityErrors)+@($cleanupErrors)){[Console]::Error.WriteLine($e)}
if($null -ne $stageRecord){throw $stageRecord}
Write-Output ('R3 CONTROLS '+$verdict.ToUpperInvariant()+' mode='+$mode+' profile='+$Profile+' executed='+$results.Count+' expected='+$selected.Count+' passed='+($results.Count-$failed.Count)+' evidence='+$evidence)
if($verdict -cne 'pass'){exit 1}
exit 0
