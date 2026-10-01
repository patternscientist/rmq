param([string]$Root=(Resolve-Path (Join-Path $PSScriptRoot '../../../..')).Path)
$ErrorActionPreference='Stop'
. (Join-Path $Root 'scripts/lifecycle_native_identity.ps1')
$utf8=[Text.UTF8Encoding]::new($false,$true)
$basePath=Join-Path $Root 'docs/internal/extensions/lifecycle-native1/BASE_IDENTITY.json'
$baseBytes=[IO.File]::ReadAllBytes($basePath)
if((Get-LN1BytesHash $baseBytes) -cne 'cfeb23f578e9ec014f2302220de4c08960f2c96892f8be5c60608ff8c4cb6997'){
  throw 'LIFECYCLE-SCOPE: immutable base inventory differs'
}
$baseline=$utf8.GetString($baseBytes)|ConvertFrom-Json
$run=Join-Path $Root ('.lake/lifecycle-native1/scope/'+[DateTime]::UtcNow.ToString('yyyyMMddTHHmmssfff'))
[void][IO.Directory]::CreateDirectory($run)
$git=(Get-Command git -CommandType Application|Select-Object -First 1).Source
function Git-LN1Scope([string[]]$Arguments,[string]$Name){
  $r=Invoke-RMQOwnedBoundedProcess -FilePath $git -Arguments (@('-c','core.excludesfile=')+$Arguments) `
    -WorkingDirectory $Root -Stage $Name -DeadlineSeconds 30 -OutputLimitBytes 8388608 -TempRoot (Join-Path $run $Name)
  if($r.TimedOut -or $r.OutputLimitExceeded -or $r.ExitCode -ne 0 -or @($r.StandardError).Count){throw ('LIFECYCLE-SCOPE: Git failure '+$Name)}
  return (@($r.StandardOutput)-join "`n")
}
function Hash-LN1Prefix([byte[]]$Bytes,[int]$Length){
  if($Bytes.Length -lt $Length){return ''}
  $prefix=[byte[]]::new($Length);[Array]::Copy($Bytes,$prefix,$Length)
  return Get-LN1BytesHash $prefix
}
$allowedExisting=@('lakefile.toml','native/packed-rmq/src/lib.rs','native/packed-rmq/Cargo.toml',
  'native/packed-rmq/README.md','docs/internal/DESIGN_DECISIONS.md','docs/internal/WORKFLOW_DESIGN_DECISIONS.md',
  'docs/FAMILY_SUMMARY.md','docs/DIGESTION_LOG.md',
  'RMQ/Core/SuccinctClose/EndpointFringe/InteriorCandidate/InteriorDirectory/SparseLevelWidth.lean',
  'RMQ/Core/SuccinctFinal/RAM/ReviewerReachabilitySmall.lean')
$allowedNew=@('RMQ/Core/WordRAM/Native/Lifecycle.lean','RMQ/Validation/PackedLifecycleNative.lean',
  'RMQ/Validation/LifecycleNativeContract.lean','native/packed-rmq/lifecycle_shim.c',
  'native/packed-rmq/include/packed_rmq_lifecycle.h','native/packed-rmq/packed_rmq_lifecycle.def',
  'native/packed-rmq/src/lifecycle.rs','native/packed-rmq/src/lifecycle_main.rs',
  'native/packed-rmq/examples/lifecycle.cpp','native/packed-rmq/tests/lifecycle_owner.c',
  'native/packed-rmq/tests/lifecycle_rust.rs','scripts/lifecycle_native_build.ps1',
  'scripts/lifecycle_native_replay.ps1','scripts/lifecycle_native_identity.ps1','scripts/lifecycle_native_cases.json')
$known=[Collections.Generic.Dictionary[string,object]]::new([StringComparer]::Ordinal)
foreach($file in $baseline.files){$known.Add($file.path,$file)}
$changes=[Collections.Generic.List[object]]::new();$newFiles=[Collections.Generic.List[object]]::new()
$result=[ordered]@{schema='lifecycle-native1-scope-v1';success=$false;base=$baseline.base;head=$null;branch=$null;
  checkedBaseFiles=0;changes=@();newFiles=@();startupAmendment=$null;contract=$null;failure=$null;
  boundary='Complete original tracked raw/Git identity and allowed path classification; narrow additive prose/target semantics additionally require reviewer inspection.'}
try{
  $result.head=Git-LN1Scope @('rev-parse','HEAD') 'head'
  $result.branch=Git-LN1Scope @('branch','--show-current') 'branch'
  if($result.branch -cne 'codex/life-native-1-consuming-owner'){throw 'LIFECYCLE-SCOPE: branch differs'}
  [void](Git-LN1Scope @('merge-base','--is-ancestor',$baseline.base,'HEAD') 'ancestry')
  $tree=Git-LN1Scope @('ls-tree','-r','-z',$baseline.base) 'base-tree'
  $baseGit=[Collections.Generic.Dictionary[string,object]]::new([StringComparer]::Ordinal)
  foreach($record in ($tree -split [char]0|Where-Object{$_})){if($record -cnotmatch '^([0-9]+) blob ([0-9a-f]{40})\t([^\r\n]+)$'){throw 'LIFECYCLE-SCOPE: unsupported base Git entry'};$baseGit.Add($Matches[3],@{mode=$Matches[1];blob=$Matches[2]})}
  if($baseGit.Count -ne $known.Count){throw 'LIFECYCLE-SCOPE: base Git roster differs'}
  foreach($old in $baseline.files){
    if(-not $baseGit.ContainsKey($old.path) -or $baseGit[$old.path].mode -cne $old.mode -or $baseGit[$old.path].blob -cne $old.gitBlob){throw ('LIFECYCLE-SCOPE: base Git identity '+$old.path)}
    $path=Join-Path $Root $old.path
    if(-not [IO.File]::Exists($path)){throw ('LIFECYCLE-SCOPE: original file removed '+$old.path)}
    $bytes=[IO.File]::ReadAllBytes($path);$hash=Get-LN1BytesHash $bytes
    if($bytes.Length -ne $old.rawBytes -or $hash -cne $old.rawSHA256){
      if($allowedExisting -cnotcontains $old.path){throw ('LIFECYCLE-SCOPE: protected raw bytes changed '+$old.path)}
      if($old.path -cin @('docs/internal/DESIGN_DECISIONS.md','docs/internal/WORKFLOW_DESIGN_DECISIONS.md','native/packed-rmq/Cargo.toml','lakefile.toml')){
        if((Hash-LN1Prefix $bytes $old.rawBytes) -cne $old.rawSHA256){throw ('LIFECYCLE-SCOPE: original prefix changed '+$old.path)}
      }
      if($old.path -ceq 'native/packed-rmq/src/lib.rs'){
        $text=$utf8.GetString($bytes)
        $insertion='(?m)^/// Construction, retirement and repeated queries through the lifecycle ABI\.\r?\npub mod lifecycle;\r?\n'
        if([regex]::Matches($text,$insertion).Count -ne 1 -or (Get-LN1BytesHash ($utf8.GetBytes([regex]::Replace($text,$insertion,'')))) -cne $old.rawSHA256){throw 'LIFECYCLE-SCOPE: existing Rust facade changed beyond additive module/doc glue'}
      }
      $changes.Add(@{path=$old.path;bytes=$bytes.Length;sha256=$hash})
    }
    $result.checkedBaseFiles++
  }
  $paths=(Git-LN1Scope @('ls-files','--cached','--others','--exclude-standard','-z') 'current-paths') -split [char]0 |Where-Object{$_}
  foreach($relative in $paths){
    if($relative -match '[\r\n]' -or $relative.Contains('..')){throw 'LIFECYCLE-SCOPE: unsupported path'}
    if($known.ContainsKey($relative)){continue}
    if($allowedNew -cnotcontains $relative -and $relative -cnotmatch '^RMQ/Core/WordRAM/Native/Lifecycle/(?:[A-Za-z0-9_]+/)*[A-Za-z0-9_]+\.lean$' -and $relative -cnotmatch '^docs/internal/extensions/lifecycle-native1/[^\r\n]+$'){
      throw ('LIFECYCLE-SCOPE: new path outside scope '+$relative)
    }
    if($relative -match '\.(?:log|zip|7z|tar|gz)$'){throw ('LIFECYCLE-SCOPE: raw transcript/archive '+$relative)}
    $newFiles.Add(@{path=$relative;pin=(Get-LN1Pin (Join-Path $Root $relative))})
  }
  foreach($frozen in @(
      @{path='STARTUP_AMENDMENT.patch';sha='3a4600648173001ecf52cbe18a63454e8b1f99e09fcb3c2c39a210beb6c6142f'},
      @{path='STARTUP_AMENDMENT.md';sha='2c4a5c7b4e837b61649a495690a75269eb355fb41d4f9366e568da634e1a9779'})){
    if((Get-LN1BytesHash ([IO.File]::ReadAllBytes((Join-Path $PSScriptRoot $frozen.path)))) -cne $frozen.sha){throw ('LIFECYCLE-SCOPE: approved amendment evidence changed '+$frozen.path)}
  }
  $result.startupAmendment=Assert-LN1StartupWitnesses $Root
  $result.contract=Assert-LN1FrozenContract $Root
  $result.success=$true
}catch{$result.failure=$_.Exception.Message}
finally{
  $result.changes=@($changes.ToArray());$result.newFiles=@($newFiles.ToArray());$result.completedUtc=[DateTime]::UtcNow.ToString('o')
  [IO.File]::WriteAllText((Join-Path $run 'RESULT.json'),($result|ConvertTo-Json -Depth 20),$utf8)
}
Write-Output ('LIFECYCLE-SCOPE success='+$result.success+' receipt='+$run)
if(-not $result.success){Write-Output $result.failure;exit 1}
