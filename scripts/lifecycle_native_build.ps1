param(
  [ValidateSet('lean','dll','clients','all')][string]$Phase='all',
  [string[]]$LeanTargets=@('RMQ.Core.WordRAM.Native.Lifecycle',
    'RMQ.Core.WordRAM.Native.Lifecycle.Observations',
    'RMQ.Core.WordRAM.Native.Lifecycle.AdmissionContract',
    'RMQ.Validation.LifecycleNativeContract'),
  [int]$LeanDeadlineSeconds=900,
  [string]$LeanDeadlineRationale='',
  [string]$RecoveryReceipt='',
  [string]$LeanReceipt='',
  [string]$LeanRoot='C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0',
  [string]$RustRoot='C:/Users/poin/.rustup/toolchains/stable-x86_64-pc-windows-msvc',
  [string]$CppCompiler='C:/Program Files/Microsoft Visual Studio/2022/Community/VC/Tools/Llvm/x64/bin/clang.exe',
  [string]$ImportLibrarian='C:/Program Files/Microsoft Visual Studio/2022/Community/VC/Tools/MSVC/14.44.35207/bin/Hostx64/x64/lib.exe',
  [string]$RustLinker='C:/Program Files/Microsoft Visual Studio/2022/Community/VC/Tools/MSVC/14.44.35207/bin/Hostx64/x64/link.exe'
)
$ErrorActionPreference='Stop'
. (Join-Path $PSScriptRoot 'lifecycle_native_identity.ps1')
. (Join-Path $PSScriptRoot 'packed_native_identity.ps1')
$taskRoot=$script:LN1Root
$buildRoot=Join-Path $taskRoot '.lake/lifecycle-native1/build'
$runRoot=Join-Path $taskRoot ('.lake/lifecycle-native1/runs/build-'+[DateTime]::UtcNow.ToString('yyyyMMddTHHmmssfff'))
if($LeanDeadlineSeconds -le 0){throw 'LIFECYCLE-BUILD: positive deadline required'}
if($null -eq $LeanTargets -or $LeanTargets.Count -eq 0){throw 'LIFECYCLE-BUILD: empty target list'}
foreach($target in $LeanTargets){
  if($target -notmatch '^RMQ\.(Core\.WordRAM\.Native\.Lifecycle(?:\.[A-Za-z0-9_]+)*|Validation\.(LifecycleNativeContract|PackedLifecycleNative))$'){
    throw ('LIFECYCLE-BUILD: unsupported focused target '+$target)
  }
}
# The actual native consumer determines the required compilation certificate.
# Reject unsupported focused/native combinations before outputs, mutex or tools.
$modules=Get-LN1ImportClosure $LeanTargets
$nativeModules=@()
if($Phase -ne 'lean'){
  $nativeModules=Get-LN1ImportClosure @('RMQ.Core.WordRAM.Native.Lifecycle.Entry')
  $selectedModules=[Collections.Generic.HashSet[string]]::new([StringComparer]::Ordinal)
  foreach($module in $modules){[void]$selectedModules.Add($module)}
  $uncovered=@($nativeModules|Where-Object{-not $selectedModules.Contains($_)})
  if($uncovered.Count){
    throw ('LIFECYCLE-BUILD: LeanTargets omit native Entry closure modules='+$uncovered.Count+'; use the default targets or a covering selection')
  }
}
[void][IO.Directory]::CreateDirectory($runRoot)
[void][IO.Directory]::CreateDirectory($buildRoot)
$mutex=[Threading.Mutex]::new($false,'Local\RMQLifecycleImplementationHeavy20260920')
$locked=$false
$savedPath=$env:PATH
$savedRust=@{RUSTC=$env:RUSTC;CARGO_HOME=$env:CARGO_HOME;CARGO_TARGET_X86_64_PC_WINDOWS_MSVC_LINKER=$env:CARGO_TARGET_X86_64_PC_WINDOWS_MSVC_LINKER}
$toolchain=$null
$pins=[Collections.Generic.List[object]]::new()
$stages=[Collections.Generic.List[object]]::new()
$report=[ordered]@{schema='lifecycle-native1-build-v1';phase=$Phase;success=$false;
  startedUtc=[DateTime]::UtcNow.ToString('o');workingDirectory=$taskRoot;
  sourcePins=@();toolPins=@();generatedPins=@();artifactPins=@();
  compilationClosure=@{selected=$modules;native=$nativeModules;nativeCovered=($Phase -ne 'lean')};
  plan=@{leanDeadlineSeconds=$LeanDeadlineSeconds;nativeStageDeadlineSeconds=300;
    baseline='Focused new proofs follow the separately captured cold Ownership closure; native compile batches contain at most 20 translation units and inherit the 300-second predecessor 19-module builder ceiling. Link/Rust stages have independent 300-second ceilings; no aggregate timeout substitutes for individual results.'};
  stages=@();failure=$null;integrity=$null;cleanup=$null;recovery=$null;contract=$null}
function Add-LN1BuildPin([string]$Path){$pin=Get-LN1Pin $Path;$pins.Add($pin);return $pin}
# The unchanged PE closure helper records each encountered file through this hook.
function Get-LNPin([string]$Path){return Add-LN1BuildPin $Path}
function Invoke-LN1BuildStage([string]$Name,[string]$File,[string[]]$StageArguments,[int]$Deadline=300,[string]$Directory=$taskRoot){
  $stage=[ordered]@{name=$Name;file=$File;arguments=$StageArguments;workingDirectory=$Directory;
    deadlineSeconds=$Deadline;startedUtc=[DateTime]::UtcNow.ToString('o');capture=$null;failure=$null}
  try {
    $stage.capture=Invoke-LN1Stage -File $File -Arguments $StageArguments -Stage $Name `
      -DeadlineSeconds $Deadline -OutputRoot (Join-Path $runRoot $Name) -WorkingDirectory $Directory
  } catch {$stage.failure=$_.Exception.Message;throw}
  finally {$stage.completedUtc=[DateTime]::UtcNow.ToString('o');$stages.Add($stage)}
  Write-Output ('LIFECYCLE-BUILD stage='+$Name+' exit=0')
}
function Write-LN1Json([string]$Path,$Value){
  [IO.File]::WriteAllText($Path,($Value|ConvertTo-Json -Depth 30),[Text.UTF8Encoding]::new($false))
}
function Write-LN1Response([string]$Path,[string[]]$Arguments){
  foreach($arg in $Arguments){if($arg.Contains('"') -or $arg.Contains("`n") -or $arg.Contains("`r")){throw 'LIFECYCLE-BUILD: unsupported response-file argument'}}
  [IO.File]::WriteAllText($Path,((@($Arguments|ForEach-Object{'"'+$_.Replace('\','/')+'"'}) -join "`n")+"`n"),[Text.UTF8Encoding]::new($false))
  return Add-LN1BuildPin $Path
}
function Assert-LN1LeanReceipt([string]$Path,[string[]]$Modules){
  if(-not $Path){throw 'LIFECYCLE-BUILD: native-only phase requires successful LeanReceipt'}
  $prior=[IO.File]::ReadAllText($Path,[Text.UTF8Encoding]::new($false,$true))|ConvertFrom-Json
  if($prior.schema -cne 'lifecycle-native1-build-v1' -or -not $prior.success -or -not $prior.integrity.success){throw 'LIFECYCLE-BUILD: unsuccessful LeanReceipt'}
  $required=@($Modules|ForEach-Object{Join-Path $taskRoot ($_.Replace('.','/')+'.lean')})+
    @('lean-toolchain','lakefile.toml','lake-manifest.json'|ForEach-Object{Join-Path $taskRoot $_})+
    @($Modules|ForEach-Object{$m=$_;@('.lake/build/lib/lean/','.lake/build/ir/')|ForEach-Object{
      $ext=if($_ -like '*ir/') {'.c'} else {'.olean'};Join-Path $taskRoot ($_+$m.Replace('.','/')+$ext)}})
  $priorPins=@($prior.sourcePins)+@($prior.generatedPins)+@($prior.toolPins)
  $priorByPath=[Collections.Generic.Dictionary[string,object]]::new([StringComparer]::OrdinalIgnoreCase)
  foreach($pin in $priorPins){
    $key=[IO.Path]::GetFullPath($pin.path)
    if($priorByPath.ContainsKey($key)){throw ('LIFECYCLE-BUILD: duplicate prior pin '+$key)}
    $priorByPath.Add($key,$pin)
  }
  foreach($p in $required){
    $key=[IO.Path]::GetFullPath($p)
    if(-not $priorByPath.ContainsKey($key)){throw ('LIFECYCLE-BUILD: missing prior source or artifact '+$p)}
    $old=$priorByPath[$key]
    $now=Get-LN1Pin $p
    if($now.bytes -ne $old.bytes -or $now.sha256 -cne $old.sha256){throw ('LIFECYCLE-BUILD: stale LeanReceipt '+$p)}
  }
  # Lean imports and dynamic compiler/runtime dependencies are part of provenance.
  foreach($old in $prior.toolPins){$now=Get-LN1Pin $old.path;if($now.bytes -ne $old.bytes -or $now.sha256 -cne $old.sha256){throw ('LIFECYCLE-BUILD: prior tool changed '+$old.path)}}
  return Add-LN1BuildPin $Path
}
function Build-LN1Native([string[]]$Modules){
  $utf8=[Text.UTF8Encoding]::new($false,$true)
  $objectRoot=Join-Path $buildRoot 'objects'
  [void][IO.Directory]::CreateDirectory($objectRoot)
  $entries=[Collections.Generic.List[object]]::new()
  $objects=[Collections.Generic.List[string]]::new()
  $pending=[Collections.Generic.List[object]]::new()
  $aggregator=[Text.StringBuilder]::new("#include <lean/lean.h>`n")
  $calls=[Text.StringBuilder]::new()
  $index=0
  foreach($module in $Modules){
    $original=Join-Path $taskRoot ('.lake/build/ir/'+$module.Replace('.','/')+'.c')
    $originalPin=Add-LN1BuildPin $original
    $bytes=[IO.File]::ReadAllBytes($original);$source=$utf8.GetString($bytes)
    $imports=[regex]::Match($source,'(?m)^// Imports: ([^\r\n]*)$')
    if(-not $imports.Success){throw ('LIFECYCLE-BUILD: missing emitted import header '+$module)}
    foreach($dependency in ($imports.Groups[1].Value -split ' ' | Where-Object{$_ -like 'RMQ.*'})){
      if($Modules -cnotcontains $dependency){throw ('LIFECYCLE-BUILD: uncovered emitted dependency '+$dependency)}
    }
    # Compiler globals have one declaration per line in the pinned emitter.
    # Reject any unrecognized object-valued global declaration instead of skipping it.
    $globals=[Collections.Generic.List[string]]::new()
    $firstBody=[regex]::Match($source,'(?m)^(?:LEAN_EXPORT |static )?[^;\r\n{}]+\([^;\r\n{}]*\) \{\r?$')
    if(-not $firstBody.Success){throw ('LIFECYCLE-BUILD: missing emitted function boundary '+$module)}
    foreach($line in ($source.Substring(0,$firstBody.Index) -split "`n")){
      if($line -match '^(?:static|LEAN_EXPORT) lean_object\* ([A-Za-z_][A-Za-z0-9_]*);\r?$'){$globals.Add($Matches[1])}
      elseif($line -match '^(?:static |LEAN_EXPORT )?lean_object\* [^(){}]+;\r?$'){throw ('LIFECYCLE-BUILD: unsupported generated global '+$line)}
    }
    if([regex]::IsMatch($source.Substring($firstBody.Index),'(?m)^(?:static|LEAN_EXPORT) lean_object\* [A-Za-z_][A-Za-z0-9_]*;\r?$')){
      throw ('LIFECYCLE-BUILD: global after function boundary '+$module)
    }
    $name='ln1_globals_'+$index.ToString('D4')
    $suffix=[Text.StringBuilder]::new("`n/* LIFE-NATIVE-1 read-only global-root visitor. Original generated bytes above are unchanged. */`n")
    [void]$suffix.Append("void $name(void (*visit)(lean_object*, void*), void* context) {`n")
    foreach($global in $globals){[void]$suffix.Append("  if ($global != NULL) visit($global, context);`n")}
    [void]$suffix.Append("}`n")
    $suffixBytes=$utf8.GetBytes($suffix.ToString())
    $transformed=[byte[]]::new($bytes.Length+$suffixBytes.Length)
    [Buffer]::BlockCopy($bytes,0,$transformed,0,$bytes.Length)
    [Buffer]::BlockCopy($suffixBytes,0,$transformed,$bytes.Length,$suffixBytes.Length)
    $hash=Get-LN1BytesHash $transformed
    $stem=$index.ToString('D4')+'_'+$hash.Substring(0,16)
    $cpath=Join-Path $objectRoot ($stem+'.c');$opath=Join-Path $objectRoot ($stem+'.o')
    [IO.File]::WriteAllBytes($cpath,$transformed)
    $cpin=Add-LN1BuildPin $cpath
    $signature=Get-NativeDigest @('lifecycle-native-c-v1',$toolchain.digest,$cpin.sha256,'-c','-O1','-Dlean_copy_expand_array=ln1_counted_copy_expand_array')
    $cachePath=$opath+'.json';$reuse=$false
    if([IO.File]::Exists($cachePath) -and [IO.File]::Exists($opath)){
      $cache=[IO.File]::ReadAllText($cachePath,$utf8)|ConvertFrom-Json
      $op=Get-LN1Pin $opath
      $reuse=$cache.signature -ceq $signature -and $cache.object.bytes -eq $op.bytes -and $cache.object.sha256 -ceq $op.sha256
    }
    $entry=[ordered]@{module=$module;original=$originalPin;transformed=$cpin;globals=@($globals.ToArray());visitor=$name;
      signature=$signature;objectPath=$opath;cachePath=$cachePath;reuse=$reuse;object=$null}
    $entries.Add($entry);$objects.Add($opath)
    if(-not $reuse){$pending.Add($entry)}else{$entry.object=Add-LN1BuildPin $opath}
    [void]$aggregator.Append("void $name(void (*visit)(lean_object*, void*), void* context);`n")
    [void]$calls.Append("  $name(visit, context);`n")
    $index++
    if($index%50 -eq 0){Write-Output ('LIFECYCLE-BUILD derived='+$index+'/'+$Modules.Count)}
  }
  [void]$aggregator.Append("void ln1_visit_fixed_globals(void (*visit)(lean_object*, void*), void* context) {`n"+$calls.ToString()+"}`n")
  $aggregateC=Join-Path $objectRoot 'fixed_globals.c'
  [IO.File]::WriteAllText($aggregateC,$aggregator.ToString(),$utf8)
  [void](Add-LN1BuildPin $aggregateC)
  $report.derivation=[ordered]@{recipe='original emitted C bytes followed by exact read-only visitor; all RMQ closure global object slots; no initializer/code removal';entries=@($entries.ToArray());aggregator=(Get-LN1Pin $aggregateC)}
  Write-LN1Json (Join-Path $runRoot 'DERIVATION.json') $report.derivation
  $batch=0
  for($at=0;$at -lt $pending.Count;$at+=20){
    $group=@($pending.ToArray()|Select-Object -Skip $at -First 20)
    $response=Join-Path $runRoot ('compile-'+$batch+'.rsp')
    [void](Write-LN1Response $response @($group|ForEach-Object{$_.transformed.path}))
    Invoke-LN1BuildStage ('c-batch-'+$batch) (Join-Path $LeanRoot 'bin/leanc.exe') @('-c','-O1','-Dlean_copy_expand_array=ln1_counted_copy_expand_array',('@'+$response)) 300 $objectRoot
    foreach($entry in $group){
      $entry.object=Add-LN1BuildPin $entry.objectPath
      Write-LN1Json $entry.cachePath @{schema='lifecycle-native-c-v1';signature=$entry.signature;object=$entry.object}
    }
    $batch++
  }
  $aggregateO=Join-Path $objectRoot 'fixed_globals.o'
  Invoke-LN1BuildStage 'c-global-visitors' (Join-Path $LeanRoot 'bin/leanc.exe') @('-c','-O1',$aggregateC,'-o',$aggregateO)
  [void](Add-LN1BuildPin $aggregateO);$objects.Add($aggregateO)
  foreach($variant in @('production','testing')){
    $variantRoot=Join-Path $buildRoot $variant;[void][IO.Directory]::CreateDirectory($variantRoot)
    $shimO=Join-Path $variantRoot 'lifecycle_shim.o'
    $flags=@('-c','-O1','-DPACKED_LIFECYCLE_BUILD')
    if($variant -ceq 'testing'){$flags+=@('-DPACKED_LIFECYCLE_TESTING')}
    Invoke-LN1BuildStage ('c-shim-'+$variant) (Join-Path $LeanRoot 'bin/leanc.exe') ($flags+@((Join-Path $taskRoot 'native/packed-rmq/lifecycle_shim.c'),'-o',$shimO))
    [void](Add-LN1BuildPin $shimO)
    $response=Join-Path $runRoot ('link-'+$variant+'.rsp')
    [void](Write-LN1Response $response (@($objects.ToArray())+@($shimO)))
    $dll=Join-Path $variantRoot 'packed_rmq_lifecycle.dll';$map=Join-Path $variantRoot 'packed_rmq_lifecycle.map'
    Invoke-LN1BuildStage ('link-'+$variant) (Join-Path $LeanRoot 'bin/leanc.exe') @('-shared','-O1',('@'+$response),('-Wl,-Map,'+$map),'-o',$dll)
    $report.artifactPins+=@(Add-LN1BuildPin $dll);$report.artifactPins+=@(Add-LN1BuildPin $map)
  }
  Write-LN1Json (Join-Path $runRoot 'DERIVATION.json') $report.derivation
}
function Build-LN1Clients {
  if($env:RUSTC_WRAPPER -or $env:RUSTC_WORKSPACE_WRAPPER){throw 'LIFECYCLE-BUILD: unrecorded Rust compiler wrapper'}
  $env:RUSTC=Join-Path $RustRoot 'bin/rustc.exe';$env:CARGO_HOME=Join-Path $buildRoot 'cargo-home'
  $env:CARGO_TARGET_X86_64_PC_WINDOWS_MSVC_LINKER=$RustLinker
  $target=Join-Path $buildRoot 'rust-target'
  Invoke-LN1BuildStage 'rust-production' (Join-Path $RustRoot 'bin/cargo.exe') @('build','--locked','--offline','--release','--bin','packed-rmq-lifecycle','--manifest-path','native/packed-rmq/Cargo.toml','--target-dir',$target)
  Invoke-LN1BuildStage 'rust-tests-compile' (Join-Path $RustRoot 'bin/cargo.exe') @('test','--no-run','--locked','--offline','--release','--test','lifecycle_rust','--manifest-path','native/packed-rmq/Cargo.toml','--target-dir',$target)
  $rustTest=@(Get-ChildItem -LiteralPath (Join-Path $target 'release/deps') -Filter 'lifecycle_rust-*.exe')
  if($rustTest.Count -ne 1){throw 'LIFECYCLE-BUILD: ambiguous Rust test executable'}
  foreach($variant in @('production','testing')){
    $dir=Join-Path $buildRoot $variant
    Copy-Item -LiteralPath (Join-Path $target 'release/packed-rmq-lifecycle.exe') -Destination (Join-Path $dir 'packed-rmq-lifecycle.exe')
    Copy-Item -LiteralPath $rustTest[0].FullName -Destination (Join-Path $dir 'lifecycle-rust-tests.exe')
    $lib=Join-Path $dir 'packed_rmq_lifecycle.lib'
    $definition=Join-Path $taskRoot 'native/packed-rmq/packed_rmq_lifecycle.def'
    if($variant -ceq 'production'){
      $text=[IO.File]::ReadAllText($definition)
      foreach($symbol in @('packed_lifecycle_test_configure','packed_lifecycle_test_receipt')){
        $pattern='(?m)^    '+$symbol+'\r?\n'
        if([regex]::Matches($text,$pattern).Count -ne 1){throw 'LIFECYCLE-BUILD: test export derivation differs'}
        $text=[regex]::Replace($text,$pattern,'')
      }
      $definition=Join-Path $dir 'production.def'
      [IO.File]::WriteAllText($definition,$text,[Text.UTF8Encoding]::new($false))
      [void](Add-LN1BuildPin $definition)
    }
    Invoke-LN1BuildStage ('import-library-'+$variant) $ImportLibrarian @('/nologo',('/def:'+$definition),('/out:'+$lib),'/machine:X64') 60
    $cflags=@('-std=c11','-Inative/packed-rmq/include')
    if($variant -ceq 'testing'){$cflags+=@('-DPACKED_LIFECYCLE_TESTING')}
    Invoke-LN1BuildStage ('c-client-'+$variant) $CppCompiler ($cflags+@('native/packed-rmq/tests/lifecycle_owner.c',$lib,'-o',(Join-Path $dir 'lifecycle-owner.exe'))) 120
    Invoke-LN1BuildStage ('cpp-client-'+$variant) $CppCompiler @('-std=c++17','-Inative/packed-rmq/include','native/packed-rmq/examples/lifecycle.cpp',$lib,'-o',(Join-Path $dir 'lifecycle-cpp.exe')) 120
    foreach($name in @('packed-rmq-lifecycle.exe','lifecycle-rust-tests.exe','lifecycle-owner.exe','lifecycle-cpp.exe','packed_rmq_lifecycle.lib')){
      $report.artifactPins+=@(Add-LN1BuildPin (Join-Path $dir $name))
    }
  }
}
try {
  $locked=$mutex.WaitOne(0)
  if(-not $locked){throw 'LIFECYCLE-BUILD: shared heavy slot busy; no child launched'}
  $report.contract=Assert-LN1FrozenContract $taskRoot
  if($RecoveryReceipt){
    $receipt=[IO.File]::ReadAllText($RecoveryReceipt,[Text.UTF8Encoding]::new($false,$true))|ConvertFrom-Json
    if(-not $receipt.ownedProcessesStopped -or -not $receipt.sourceIntegrityPassed){throw 'LIFECYCLE-BUILD: incomplete recovery diagnosis'}
    foreach($pin in $receipt.completedArtifacts){
      $now=Get-LN1Pin $pin.path
      if($now.bytes -ne $pin.bytes -or $now.sha256 -cne $pin.sha256){throw ('LIFECYCLE-BUILD: recovery artifact changed '+$pin.path)}
    }
    $report.recovery=Add-LN1BuildPin $RecoveryReceipt
    $report.plan.baseline=$receipt.nextDeadlineRationale
  }
  if($LeanDeadlineRationale){$report.plan.baseline=$LeanDeadlineRationale}
  $sourcePaths=@($modules|ForEach-Object{Join-Path $taskRoot ($_.Replace('.','/')+'.lean')})+
    @('lean-toolchain','lakefile.toml','lake-manifest.json','scripts/lifecycle_native_build.ps1',
      'scripts/lifecycle_native_identity.ps1','scripts/owned_process_tree.ps1',
      'scripts/packed_native_identity.ps1','scripts/packed_native_lifecycle_stream_check.ps1',
      'scripts/packed_native_lifecycle_storage_replay.ps1','scripts/packed_native_lifecycle_integrity_check.ps1'|
      ForEach-Object{Join-Path $taskRoot $_})
  $report.sourcePins=@($sourcePaths|ForEach-Object{Add-LN1BuildPin $_})
  $report.toolPins=@(Get-NativeFileInventory $LeanRoot @('bin','include','lib')|
    ForEach-Object{Add-LN1BuildPin (Join-Path $LeanRoot $_.path)})
  [IO.File]::WriteAllText((Join-Path $runRoot 'PLAN.json'),($report|ConvertTo-Json -Depth 12),[Text.UTF8Encoding]::new($false))
  $env:PATH=(Join-Path $LeanRoot 'bin')+';'+$env:PATH
  if($Phase -in @('lean','all')){
    Invoke-LN1BuildStage 'lean-focused' (Join-Path $LeanRoot 'bin/lake.exe') (@('build')+$LeanTargets) $LeanDeadlineSeconds
    $report.generatedPins=@(foreach($module in $modules){
      foreach($kind in @(@{root='.lake/build/lib/lean';ext='.olean'},@{root='.lake/build/ir';ext='.c'})){
        Add-LN1BuildPin (Join-Path $taskRoot ($kind.root+'/'+$module.Replace('.','/')+$kind.ext))
      }
    })
  }
  if($Phase -ne 'lean'){
    if($Phase -ne 'all'){$report.leanReceipt=Assert-LN1LeanReceipt $LeanReceipt $modules}
    $nativePaths=@('native/packed-rmq/lifecycle_shim.c','native/packed-rmq/include/packed_rmq_lifecycle.h',
      'native/packed-rmq/packed_rmq_lifecycle.def')
    if($Phase -in @('all','clients')){$nativePaths+=@('native/packed-rmq/Cargo.toml','native/packed-rmq/Cargo.lock',
      'native/packed-rmq/src/lib.rs','native/packed-rmq/src/native.rs','native/packed-rmq/src/lifecycle.rs',
      'native/packed-rmq/src/lifecycle_main.rs','native/packed-rmq/tests/lifecycle_rust.rs',
      'native/packed-rmq/tests/lifecycle_owner.c','native/packed-rmq/examples/lifecycle.cpp')}
    $report.sourcePins+=@($nativePaths|ForEach-Object{Add-LN1BuildPin (Join-Path $taskRoot $_)})
    $report.generatedPins=@(foreach($module in $modules){
      foreach($kind in @(@{root='.lake/build/lib/lean';ext='.olean'},@{root='.lake/build/ir';ext='.c'})){
        Add-LN1BuildPin (Join-Path $taskRoot ($kind.root+'/'+$module.Replace('.','/')+$kind.ext))
      }
    })
    $report.startupWitnesses=Assert-LN1StartupWitnesses $taskRoot
    $toolchain=Get-NativeToolchainIdentity $taskRoot $LeanRoot $RustRoot $CppCompiler $ImportLibrarian $RustLinker
    $report.toolchainIdentity=$toolchain
    $abi=[IO.File]::ReadAllText((Join-Path $taskRoot '.lake/build/ir/RMQ/Core/WordRAM/Native/Lifecycle/Entry.c'))
    $prototypes=@([regex]::Matches($abi,'(?m)^LEAN_EXPORT (?:lean_object\*|uint8_t) rmq_lifecycle_[A-Za-z0-9_]+\([^;\r\n]*\);')|ForEach-Object{$_.Value})
    $expected=@(
      'lean_object* rmq_lifecycle_run_first_observed(uint8_t, lean_object*, lean_object*)',
      'uint8_t rmq_lifecycle_signed_format(uint8_t, lean_object*)',
      'lean_object* rmq_lifecycle_observation_counter(lean_object*, uint8_t)',
      'lean_object* rmq_lifecycle_decode_signed(uint8_t, lean_object*)',
      'lean_object* rmq_lifecycle_run_first(uint8_t, lean_object*, lean_object*)',
      'lean_object* rmq_lifecycle_metadata(lean_object*, lean_object*)','lean_object* rmq_lifecycle_program(uint8_t)',
      'lean_object* rmq_lifecycle_build_first(uint8_t, lean_object*, lean_object*, lean_object*)',
      'lean_object* rmq_lifecycle_query_observed(uint8_t, lean_object*, lean_object*, lean_object*)',
      'lean_object* rmq_lifecycle_observation_route(lean_object*, uint8_t)',
      'lean_object* rmq_lifecycle_initial(uint8_t, lean_object*, lean_object*, lean_object*)',
      'lean_object* rmq_lifecycle_build_first_observed(uint8_t, lean_object*, lean_object*, lean_object*)',
      'lean_object* rmq_lifecycle_packet(lean_object*)','lean_object* rmq_lifecycle_observation_reads(lean_object*)',
      'uint8_t rmq_lifecycle_status(lean_object*)','lean_object* rmq_lifecycle_signature_count(uint8_t, uint8_t)',
      'uint8_t rmq_lifecycle_admit(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*)',
      'lean_object* rmq_lifecycle_run_fuel(uint8_t, lean_object*, lean_object*)','lean_object* rmq_lifecycle_profile(lean_object*)',
      'uint8_t rmq_lifecycle_query_admit(lean_object*, lean_object*, lean_object*)',
      'lean_object* rmq_lifecycle_query(uint8_t, lean_object*, lean_object*, lean_object*)',
      'lean_object* rmq_lifecycle_encode_natural(lean_object*)')|ForEach-Object{'LEAN_EXPORT '+$_+';'}
    if(((Get-NativeOrdinalUnique $prototypes)-join "`n") -cne ((Get-NativeOrdinalUnique $expected)-join "`n")){
      throw 'LIFECYCLE-BUILD: actual compiled ABI differs from frozen prototypes'
    }
    $report.abi=@{prototypes=$expected;entry=(Get-LN1Pin (Join-Path $taskRoot '.lake/build/ir/RMQ/Core/WordRAM/Native/Lifecycle/Entry.c'))}
    Write-LN1Json (Join-Path $runRoot 'PLAN-NATIVE.json') $report
    if($Phase -in @('dll','all')){Build-LN1Native $nativeModules}
    if($Phase -ceq 'clients'){
      $manifestPath=Join-Path $buildRoot 'DLL_MANIFEST.json'
      $manifest=[IO.File]::ReadAllText($manifestPath)|ConvertFrom-Json
      if(-not $manifest.success -or $manifest.toolchainDigest -cne $toolchain.digest){throw 'LIFECYCLE-BUILD: stale DLL manifest'}
      foreach($pin in @($manifest.sourcePins)+@($manifest.generatedPins)+@($manifest.artifactPins)){
        $now=Add-LN1BuildPin $pin.path;if($now.bytes -ne $pin.bytes -or $now.sha256 -cne $pin.sha256){throw ('LIFECYCLE-BUILD: stale native dependency '+$pin.path)}
      }
      $report.nativeReceipt=Add-LN1BuildPin $manifestPath
      $report.artifactPins+=@($manifest.artifactPins)
    }
    if($Phase -in @('clients','all')){Build-LN1Clients}
    $peRoots=@($report.artifactPins|Where-Object{$_.path -match '\.(dll|exe)$' -and $_.path -notmatch 'lifecycle-rust-tests\.exe$'}|ForEach-Object{$_.path})
    $report.dependencies=Get-LNDependencyClosure $peRoots (Join-Path $LeanRoot 'bin')
    Assert-LNDependencyCoverage $report.dependencies @($pins.ToArray())
  }
  $report.success=$true
} catch {$report.failure=$_.Exception.Message}
finally {
  $errors=[Collections.Generic.List[string]]::new()
  foreach($pin in $pins){
    try{$now=Get-LN1Pin $pin.path;if($now.bytes -ne $pin.bytes -or $now.sha256 -cne $pin.sha256){throw ('changed pin '+$pin.path)}}
    catch{$errors.Add($_.Exception.Message)}
  }
  if($null -ne $toolchain){try{$report.finalToolchain=Assert-NativeToolchainIdentity $taskRoot $toolchain}catch{$errors.Add($_.Exception.Message)}}
  $report.integrity=@{success=($errors.Count -eq 0);checked=$pins.Count;errors=@($errors.ToArray())}
  if($errors.Count){$report.success=$false}
  $env:PATH=$savedPath
  foreach($name in $savedRust.Keys){[Environment]::SetEnvironmentVariable($name,$savedRust[$name],'Process')}
  try{if($locked){$mutex.ReleaseMutex()};$mutex.Dispose();$report.cleanup=@{success=$true;mutexReleased=$locked}}
  catch{$report.cleanup=@{success=$false;error=$_.Exception.Message};$report.success=$false}
  $report.stages=@($stages.ToArray())
  $report.completedUtc=[DateTime]::UtcNow.ToString('o')
  [IO.File]::WriteAllText((Join-Path $runRoot 'RESULT.json'),($report|ConvertTo-Json -Depth 20),[Text.UTF8Encoding]::new($false))
  if($report.success -and $Phase -in @('dll','all')){
    Write-LN1Json (Join-Path $buildRoot 'DLL_MANIFEST.json') @{schema='lifecycle-native-dll-v1';success=$true;
      toolchainDigest=$toolchain.digest;sourcePins=$report.sourcePins;generatedPins=$report.generatedPins;
      artifactPins=$report.artifactPins;receipt=(Get-LN1Pin (Join-Path $runRoot 'RESULT.json'))}
  }
}
Write-Output ('LIFECYCLE-BUILD success='+$report.success+' receipt='+$runRoot)
if(-not $report.success){Write-Output $report.failure;exit 1}
