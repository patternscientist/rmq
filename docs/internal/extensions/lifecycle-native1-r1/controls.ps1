[CmdletBinding()]
param([ValidateSet('registry','setup','closure','scope-final','all')][string]$Group='all',
  [ValidateRange(1,120)][int]$DeadlineSeconds=30)
$ErrorActionPreference='Stop'
. (Join-Path $PSScriptRoot 'identity.ps1')
$root=$script:R1Root;$utf8=$script:R1Utf8
$casePath=Join-Path $PSScriptRoot 'REPAIR_CASES.json'
$caseBytes=[IO.File]::ReadAllBytes($casePath)
if(-not (Test-R1Exact (Get-LN1BytesHash $caseBytes) 'b51c7c5bc0505f1e9c913c021fdfcd4f4ea0d8efcb1ac2ae8a439a99d3cb0549')){
  throw 'R1-CONTROLS: frozen repair mapping differs'
}
$registry=$utf8.GetString($caseBytes)|ConvertFrom-Json
$selected=@($registry.cases|Where-Object{$Group -eq 'all' -or $_.handler -eq $Group -or ($Group -eq 'closure' -and $_.handler.StartsWith('closure-'))})
if($selected.Count -eq 0){throw 'R1-CONTROLS: empty selection'}
$run=Join-Path $root ('.lake/lifecycle-native1-r1/controls/'+[DateTime]::UtcNow.ToString('yyyyMMddTHHmmssfff')+'-'+[Guid]::NewGuid().ToString('N').Substring(0,8))
$scratch=Join-Path $run 'disposable'
$pins=[Collections.Generic.List[object]]::new();$results=[Collections.Generic.List[object]]::new()
$report=[ordered]@{schema='lifecycle-native1-r1-controls-v1';success=$false;group=$Group;
  startedUtc=[DateTime]::UtcNow.ToString('o');selected=@($selected.id);results=@();pins=@();failure=$null;integrity=$null;cleanup=$null}
$scopeShadow=$null
$shell=(Get-Process -Id $PID).Path
$prefix='docs/internal/extensions/lifecycle-native1/'
$helpers=@('scripts/lifecycle_native_identity.ps1','scripts/owned_process_tree.ps1',
  'scripts/packed_native_lifecycle_stream_check.ps1','scripts/packed_native_lifecycle_integrity_check.ps1',
  'scripts/packed_native_lifecycle_storage_replay.ps1')
function Copy-R1ControlFile([string]$Relative,[string]$Shadow){
  $source=Join-Path $root $Relative;$dest=Join-Path $Shadow $Relative
  $pin=Get-LN1Pin $source;$pins.Add($pin)
  [void][IO.Directory]::CreateDirectory((Split-Path $dest -Parent))
  [IO.File]::Copy($source,$dest,$false)
  $copy=Get-LN1Pin $dest
  if(-not (Test-R1Exact $copy.sha256 $pin.sha256) -or $copy.bytes -ne $pin.bytes){throw 'R1-CONTROLS: source copy differs'}
}
function Invoke-R1Caller([string]$Body,[string]$Name,[string]$Directory,[int]$Limit=$DeadlineSeconds){
  $driver=Join-Path $run ($Name+'-caller.ps1')
  $text='$ErrorActionPreference="Stop"'+"`n"+'[Console]::OutputEncoding=[Text.UTF8Encoding]::new($false,$true)'+
    "`ntry {`n"+$Body+"`n"+'exit $LASTEXITCODE'+"`n} catch {`n"+
    '[Console]::Error.Write("R1-CALL ERROR: "+$_.Exception.Message+"`n"); exit 1'+"`n}`n"
  [IO.File]::WriteAllText($driver,$text,$utf8);$pins.Add((Get-LN1Pin $driver))
  return Invoke-LNStreamCapture $root $shell @('-NoProfile','-File',$driver) $Directory (Join-Path $run $Name) $Limit $Name
}
try{
  [void][IO.Directory]::CreateDirectory($scratch)
  foreach($p in @($PSCommandPath,(Join-Path $PSScriptRoot 'identity.ps1'),$casePath,$shell)){$pins.Add((Get-LN1Pin $p))}
  foreach($case in $selected){
    $shadow=Join-Path $scratch $case.id
    if($case.handler -ne 'scope-final'){foreach($p in $helpers){Copy-R1ControlFile $p $shadow}}
    if($case.handler -eq 'registry'){
      $runner=$prefix+$case.runner+'.ps1';$data=$prefix+$case.runner+'.json'
      Copy-R1ControlFile $runner $shadow;Copy-R1ControlFile $data $shadow
      $r=[IO.File]::ReadAllText((Join-Path $shadow $data),$utf8)|ConvertFrom-Json
      $ids=@($r.orderedIds)
      switch($case.mutation){
        'healthy' {}
        'omit' {$r.cases=@($r.cases[0..3])+@($r.cases[5..($r.cases.Count-1)]);$r.orderedIds=@($r.orderedIds[0..3])+@($r.orderedIds[5..($r.orderedIds.Count-1)])}
        'duplicate' {$r.cases[4]=$r.cases[3];$r.orderedIds[4]=$r.orderedIds[3]}
        {$_ -in @('field','type')} {
          $target=if($case.field -in @('schema','status')){$r}else{$r.cases[4]}
          $value=if($case.mutation -eq 'type'){$case.value}else{[string]$target.($case.field)+$case.suffix}
          $target.($case.field)=$value
          if($case.field -eq 'id'){$r.orderedIds[4]=$value}
        }
        default {throw 'R1-CONTROLS: unknown mutation'}
      }
      if($case.mutation -ne 'healthy'){Write-R1Json (Join-Path $shadow $data) $r}
      $retained=Join-Path $run ($case.id+'-registry.json')
      [IO.File]::Copy((Join-Path $shadow $data),$retained,$false);$pins.Add((Get-LN1Pin $retained))
      $args=if($case.runner -eq 'native_controls'){' -Mode Plan'}else{' -Phase Validate'}
      $capture=Invoke-R1Caller ('& '+(Quote-R1 (Join-Path $shadow $runner))+$args) $case.id $shadow
      $out='';$err=''
      $label=if($case.runner -eq 'native_controls'){'NATIVE-CONTROLS'}else{'NATIVE-CLIENTS'}
      if($case.expectedExit -eq 0){
        $verb=if($case.runner -eq 'native_controls'){' PLAN'}else{' VALIDATED'}
        $out=$label+$verb+' cases='+$ids.Count+' ids='+($ids -join ',')+"`r`n"
      }else{
        $message=if($case.mutation -eq 'omit' -or $case.field -in @('schema','status')){'registry schema/count differs'}else{'frozen mapping differs at '+$ids[4]}
        $err='R1-CALL ERROR: '+$label+': '+$message+"`n"
      }
      Assert-LNOuterCapture $capture $out $err $case.expectedExit $case.id
      if([IO.Directory]::Exists((Join-Path $shadow '.lake'))){throw 'R1-CONTROLS: registry preflight mutated output'}
      $results.Add(@{id=$case.id;passed=$true;capture=$capture;registry=(Get-LN1Pin $retained);
        expectedExit=$case.expectedExit;expectedStdout=$out;expectedStderr=$err;outputMutation=$false;
        boundary='Actual byte-identical Plan/Validate caller; production early return/rejection precedes semantic dispatch and output creation.'})
    }elseif($case.handler -eq 'setup'){
      $runner=$prefix+'native_selector_controls.ps1'
      foreach($p in @($runner,($prefix+'native_selector_controls.json'),'scripts/lifecycle_native_cases.json')){Copy-R1ControlFile $p $shadow}
      $faultPin=$null
      if($case.fault -eq 'changed-pin-then-missing-replay'){
        # Only this disposable helper gains a fault injector: change the already
        # pinned owner script just before its first missing replay-source pin.
        # The actual owning runner and its finalizers remain byte-identical code.
        $helper=Join-Path $shadow 'scripts/lifecycle_native_identity.ps1'
        $fault=@'
$script:R1OriginalPin=${function:Get-LN1Pin}
$script:R1FaultFired=$false
function Get-LN1Pin([string]$Path){
  if(-not $script:R1FaultFired -and $Path.EndsWith('lifecycle_native_replay.ps1',[StringComparison]::Ordinal)){
    $script:R1FaultFired=$true
    [IO.File]::AppendAllText((Join-Path $script:LN1Root 'docs/internal/extensions/lifecycle-native1/native_selector_controls.ps1'),"`n# R1 disposable integrity fault after owner pin.`n",[Text.UTF8Encoding]::new($false))
  }
  & $script:R1OriginalPin $Path
}
'@
        [IO.File]::AppendAllText($helper,"`n"+$fault+"`n",$utf8)
        $retainedHelper=Join-Path $run ($case.id+'-fault-helper.ps1')
        [IO.File]::Copy($helper,$retainedHelper,$false);$faultPin=Get-LN1Pin $retainedHelper;$pins.Add($faultPin)
      }
      $missing=Join-Path $shadow 'scripts/lifecycle_native_replay.ps1'
      if([IO.File]::Exists($missing)){throw 'R1-CONTROLS: missing-source fixture is present'}
      $capture=Invoke-R1Caller ('& '+(Quote-R1 (Join-Path $shadow $runner))) $case.id $shadow
      $innerRuns=@(Get-ChildItem -LiteralPath (Join-Path $shadow '.lake/lifecycle-native1/selector-controls') -Directory)
      if($innerRuns.Count -ne 1){throw 'R1-CONTROLS: setup caller did not retain exactly one run'}
      $inner=$innerRuns[0].FullName;$innerPath=Join-Path $inner 'RESULT.json'
      $r=[IO.File]::ReadAllText($innerPath,$utf8)|ConvertFrom-Json
      $expectedFailure="Could not find file '"+$missing+"'."
      if($r.success -ne $false -or -not (Test-R1Exact $r.failureStage 'setup') -or
          -not (Test-R1Exact $r.failure $expectedFailure) -or $r.setup.complete -ne $false -or
          $r.setup.pinSetComplete -ne $false -or $r.integrity.initialPinSetComplete -ne $false -or
          $r.integrity.attempted -ne $true -or $r.cleanup.attempted -ne $true -or
          $r.finalReceiptAttempted -ne $true -or $r.semanticChildInvocations -ne 0 -or
          $r.integrity.success -ne $case.integritySuccess -or $r.cleanup.success -ne $true -or
          @($r.controls).Count -ne 0 -or $r.integrity.checked -ne 3 -or
          [IO.Directory]::Exists((Join-Path $inner 'disposable'))){throw 'R1-CONTROLS: setup/finalization obligations differ'}
      if($case.integritySuccess){
        if(@($r.integrity.errors).Count -ne 0){throw 'R1-CONTROLS: unexpected intact-pin error'}
      }else{
        if(@($r.integrity.errors).Count -ne 1 -or
            -not (Test-R1Exact $r.integrity.errors[0] ('changed source '+(Join-Path $shadow $runner)))){throw 'R1-CONTROLS: exact independent integrity failure absent'}
      }
      $out='NATIVE-SELECTOR-CONTROLS evidence='+$inner+"`r`n"+'NATIVE-SELECTOR-CONTROLS FAIL '+$expectedFailure+"`r`n"
      Assert-LNOuterCapture $capture $out '' 1 $case.id
      $saved=Join-Path $run ($case.id+'-inner-RESULT.json');[IO.File]::Copy($innerPath,$saved,$false)
      $pins.Add((Get-LN1Pin $saved))
      $results.Add(@{id=$case.id;passed=$true;capture=$capture;innerReceipt=(Get-LN1Pin $saved);
        faultHelper=$faultPin;failureStage='setup';initialPinSetComplete=$false;
        ordinaryExit=1;semanticChildInvocations=0;disposableRemoved=$true;
        integrityAttempted=$true;cleanupAttempted=$true;failureReceiptPersisted=$true})
    }elseif($case.handler.StartsWith('closure-')){
      Copy-R1ControlFile 'scripts/lifecycle_native_build.ps1' $shadow
      Copy-R1ControlFile 'scripts/packed_native_identity.ps1' $shadow
      $defaults=@('RMQ.Core.WordRAM.Native.Lifecycle','RMQ.Core.WordRAM.Native.Lifecycle.Observations',
        'RMQ.Core.WordRAM.Native.Lifecycle.AdmissionContract','RMQ.Validation.LifecycleNativeContract')
      $modules=@(Get-LN1ImportClosure $defaults)
      $native=@(Get-LN1ImportClosure @('RMQ.Core.WordRAM.Native.Lifecycle.Entry'))
      $codec=@(Get-LN1ImportClosure @('RMQ.Core.WordRAM.Native.Lifecycle.Codec'))
      if($modules.Count -ne 371 -or $native.Count -ne 365 -or $codec.Count -ne 3 -or
          @($native|Where-Object{$_ -cnotin $codec}).Count -ne 362 -or
          @($native|Where-Object{$_ -cnotin $modules}).Count -ne 0){throw 'R1-CONTROLS: recorded source closure fixture differs'}
      foreach($module in $modules){Copy-R1ControlFile ($module.Replace('.','/')+'.lean') $shadow}
      $builder=Join-Path $shadow 'scripts/lifecycle_native_build.ps1'
      if($case.handler -eq 'closure-caller'){
        $capture=Invoke-R1Caller ('& '+(Quote-R1 $builder)+' -Phase '+$case.phase+' -LeanTargets RMQ.Core.WordRAM.Native.Lifecycle.Codec') $case.id $shadow
        $err="R1-CALL ERROR: LIFECYCLE-BUILD: LeanTargets omit native Entry closure modules=362; use the default targets or a covering selection`n"
        Assert-LNOuterCapture $capture '' $err 1 $case.id
        if([IO.Directory]::Exists((Join-Path $shadow '.lake'))){throw 'R1-CONTROLS: unsupported native selection acquired outputs'}
        $results.Add(@{id=$case.id;passed=$true;capture=$capture;selectedCount=3;compiledCount=365;uncovered=362;outputMutation=$false;compilerInvocations=0})
      }elseif($case.id -in @('H3-default-coverage','H3-lean-codec-supported')){
        # Execute the exact production prefix up to the FIRST resource acquisition;
        # the appended marker is test instrumentation, not a copied guard.
        $source=[IO.File]::ReadAllText($builder,$utf8)
        $marker='[void][IO.Directory]::CreateDirectory($runRoot)'
        $at=$source.IndexOf($marker,[StringComparison]::Ordinal)
        if($at -lt 0 -or $source.LastIndexOf($marker,[StringComparison]::Ordinal) -ne $at){throw 'R1-CONTROLS: ambiguous acquisition boundary'}
        $probe=$source.Substring(0,$at)+"`n"+'Write-Output ("R1-PREFLIGHT selected="+$modules.Count+" native="+$nativeModules.Count); exit 0'+"`n"
        $probePath=Join-Path $shadow 'scripts/preflight.ps1';[IO.File]::WriteAllText($probePath,$probe,$utf8)
        $saved=Join-Path $run ($case.id+'-production-prefix.ps1');[IO.File]::Copy($probePath,$saved,$false);$pins.Add((Get-LN1Pin $saved))
        $args=if($case.id -eq 'H3-lean-codec-supported'){' -Phase lean -LeanTargets RMQ.Core.WordRAM.Native.Lifecycle.Codec'}else{' -Phase dll'}
        $expected=if($case.id -eq 'H3-lean-codec-supported'){"R1-PREFLIGHT selected=3 native=0`r`n"}else{"R1-PREFLIGHT selected=371 native=365`r`n"}
        $capture=Invoke-R1Caller ('& '+(Quote-R1 $probePath)+$args) $case.id $shadow
        Assert-LNOuterCapture $capture $expected '' 0 $case.id
        if([IO.Directory]::Exists((Join-Path $shadow '.lake'))){throw 'R1-CONTROLS: preflight probe acquired outputs'}
        $results.Add(@{id=$case.id;passed=$true;capture=$capture;prefix=(Get-LN1Pin $saved);compilerInvocations=0;boundary='Exact production prefix through closure guard, stopped before acquisition. Fresh full native positive execution is separately required.'})
      }else{
        # A clearly labeled component fixture exercises the ACTUAL receipt
        # predicate over the FULL default set. It is never a build certificate.
        $origin='C:/Users/poin/.codex/worktrees/44d6/RMQ'
        $delivery=[IO.File]::ReadAllText((Join-Path $origin '.lake/lifecycle-native1/delivery/DELIVERY.json'),$utf8)|ConvertFrom-Json
        Assert-R1Pin $delivery.verification.leanFourRoots.receipt
        $old=[IO.File]::ReadAllText($delivery.verification.leanFourRoots.receipt.path,$utf8)|ConvertFrom-Json
        $sourcePins=@(foreach($module in $modules){Get-LN1Pin (Join-Path $shadow ($module.Replace('.','/')+'.lean'))})
        foreach($relative in @('lean-toolchain','lakefile.toml','lake-manifest.json')){Copy-R1ControlFile $relative $shadow;$sourcePins+=@(Get-LN1Pin (Join-Path $shadow $relative))}
        $generated=@(foreach($oldPin in $old.generatedPins){
          Assert-R1Pin $oldPin
          $relative=[IO.Path]::GetRelativePath($origin,$oldPin.path)
          $dest=Join-Path $shadow $relative
          [void][IO.Directory]::CreateDirectory((Split-Path $dest -Parent));[IO.File]::Copy($oldPin.path,$dest,$false)
          $now=Get-LN1Pin $dest
          if($now.bytes -ne $oldPin.bytes -or -not (Test-R1Exact $now.sha256 $oldPin.sha256)){throw 'R1-CONTROLS: generated fixture copy differs'}
          $now
        })
        $fixture=Join-Path $run ($case.id+'-TEST-ONLY-RECEIPT.json')
        Write-R1Json $fixture @{schema='lifecycle-native1-build-v1';success=$true;integrity=@{success=$true};
          testFixtureOnly=$true;origin=$delivery.verification.leanFourRoots.receipt;
          boundary='Synthetic predicate input with exact isolated source/artifact copies. Not an actual compiler execution or current-worktree certificate.';
          sourcePins=$sourcePins;generatedPins=$generated;toolPins=$old.toolPins}
        $tokens=$null;$errors=$null;$ast=[Management.Automation.Language.Parser]::ParseFile($builder,[ref]$tokens,[ref]$errors)
        $function=@($ast.FindAll({param($n)$n -is [Management.Automation.Language.FunctionDefinitionAst] -and $n.Name -eq 'Assert-LN1LeanReceipt'},$true))
        if($errors.Count -or $function.Count -ne 1){throw 'R1-CONTROLS: actual receipt predicate extraction differs'}
        $moduleList=(@($modules|ForEach-Object{Quote-R1 $_}) -join ',')
        $predicateBody='. '+(Quote-R1 (Join-Path $shadow 'scripts/lifecycle_native_identity.ps1'))+"`n"+
          '$taskRoot='+(Quote-R1 $shadow)+"`n"+'function Add-LN1BuildPin([string]$Path){Get-LN1Pin $Path}'+"`n"+
          $function[0].Extent.Text+"`n"+'Assert-LN1LeanReceipt '+(Quote-R1 $fixture)+' @('+$moduleList+') | Out-Null'
        $positive=Invoke-R1Caller ($predicateBody+"`n"+'Write-Output "R1-RECEIPT accepted"') ($case.id+'-healthy') $shadow 600
        Assert-LNOuterCapture $positive "R1-RECEIPT accepted`r`n" '' 0 ($case.id+'-healthy')
        $healthyFixture=Join-Path $run ($case.id+'-TEST-ONLY-HEALTHY.json')
        [IO.File]::Copy($fixture,$healthyFixture,$false);$pins.Add((Get-LN1Pin $healthyFixture))
        $target=Join-Path $shadow 'RMQ/Core/WordRAM/Native/Lifecycle/Entry.lean'
        if($case.id -eq 'H3-native-body-mutation'){
          $body=[IO.File]::ReadAllBytes($target)
          $text=$utf8.GetString($body)
          $needle="PackedLifecycle.Executable.initialOwner (modelOfComparison comparison) xs`n    (decodeMagnitude left) (decodeMagnitude right)"
          if($text.Split([string[]]@($needle),[StringSplitOptions]::None).Count -ne 2){throw 'R1-CONTROLS: body mutation source anchor absent'}
          $mutated=$text.Replace($needle,"PackedLifecycle.Executable.initialOwner (modelOfComparison comparison) xs`n    (decodeMagnitude right) (decodeMagnitude left)")
          [IO.File]::WriteAllText($target,$mutated,$utf8)
          $savedBody=Join-Path $run ($case.id+'-mutated-Entry.lean');[IO.File]::WriteAllText($savedBody,$mutated,$utf8);$pins.Add((Get-LN1Pin $savedBody))
          $expectedError='LIFECYCLE-BUILD: stale LeanReceipt '+$target
        }else{
          $fixtureData=[IO.File]::ReadAllText($fixture,$utf8)|ConvertFrom-Json
          $missing=Join-Path $shadow '.lake/build/ir/RMQ/Core/WordRAM/Native/Lifecycle/Entry.c'
          $fixtureData.generatedPins=@($fixtureData.generatedPins|Where-Object{-not (Test-R1Exact $_.path $missing)})
          Write-R1Json $fixture $fixtureData
          $expectedError='LIFECYCLE-BUILD: missing prior source or artifact '+$missing
        }
        $capture=Invoke-R1Caller $predicateBody $case.id $shadow
        Assert-LNOuterCapture $capture '' ('R1-CALL ERROR: '+$expectedError+"`n") 1 $case.id
        $pins.Add((Get-LN1Pin $fixture))
        $results.Add(@{id=$case.id;passed=$true;capture=$capture;healthyCapture=$positive;healthyFixture=(Get-LN1Pin $healthyFixture);fixture=(Get-LN1Pin $fixture);selectedCount=371;
          predicateSHA256=(Get-LN1BytesHash ($utf8.GetBytes($function[0].Extent.Text)));compilerInvocations=0;
          boundary='Actual full-domain receipt predicate on isolated test-only pins; no fabricated stale DLL or compiler failure.'})
      }
    }elseif($case.handler -eq 'scope-final'){
      $baseline=[IO.File]::ReadAllText((Join-Path $PSScriptRoot 'BASE_IDENTITY.json'),$utf8)|ConvertFrom-Json
      if($case.id -in @('R1-FINAL-extra-stdout','R1-FINAL-extra-stderr','R1-FINAL-wrong-exit')){
        $suffix=switch($case.id){
          'R1-FINAL-extra-stdout' {'[Console]::Out.Write("unexpected`n")'}
          'R1-FINAL-extra-stderr' {'[Console]::Error.Write("unexpected`n")'}
          'R1-FINAL-wrong-exit' {'exit 7'}
        }
        $capture=Invoke-R1Caller ('& '+(Quote-R1 (Join-Path $PSScriptRoot 'scope_check.ps1'))+' -Complete'+"`n"+$suffix) $case.id $root 600
        $head=(& git -c core.excludesfile= -c core.safecrlf=false rev-parse HEAD).Trim()
        $paths=@(@(& git -c core.excludesfile= -c core.safecrlf=false diff --name-only $script:R1OriginalBase)+@(& git -c core.excludesfile= -c core.safecrlf=false ls-files --others --exclude-standard)|Sort-Object -Unique)
        $rejected=$null
        try{[void](Assert-R1FinalScope $capture $root $head $paths)}catch{$rejected=$_.Exception.Message}
        $expected=switch($case.id){
          'R1-FINAL-extra-stdout' {'R1-FINAL-SCOPE: unexpected complete output language'}
          'R1-FINAL-extra-stderr' {'STREAM: r1-final-scope stderr differs'}
          'R1-FINAL-wrong-exit' {'STREAM: r1-final-scope ordinary exit differs'}
        }
        if(-not (Test-R1Exact $rejected $expected)){throw ('R1-CONTROLS: exact final-stream rejection differs '+$rejected)}
        $results.Add(@{id=$case.id;passed=$true;capture=$capture;rejection=$rejected;actualScopeCaller=$true})
      }else{
        # Full file domain, copied once; only isolated bytes are challenged.
        if(-not $scopeShadow){
          $scopeShadow=Join-Path $scratch 'scope-repository'
          foreach($f in $baseline.files){Copy-R1ControlFile $f.path $scopeShadow}
          foreach($p in $script:R1New){if([IO.File]::Exists((Join-Path $root $p))){Copy-R1ControlFile $p $scopeShadow}}
        }
        $paths=@($baseline.files.path)+@($script:R1New|Where-Object{[IO.File]::Exists((Join-Path $scopeShadow $_))})
        $changedPath=$null;$before=$null;$expected=$null;$rejected=$null;$pin=$null
        try{
          switch($case.id){
            'R1-FINAL-healthy' {}
            'R1-FINAL-out-of-scope' {$changedPath=Join-Path $scopeShadow 'lean-toolchain';$expected='R1-SCOPE: protected raw bytes changed lean-toolchain'}
            'R1-FINAL-frozen-row' {$changedPath=Join-Path $scopeShadow 'docs/internal/extensions/lifecycle-native1/ACCEPTANCE_MATRIX.frozen.md';$expected='R1-SCOPE: protected raw bytes changed docs/internal/extensions/lifecycle-native1/ACCEPTANCE_MATRIX.frozen.md'}
            'R1-FINAL-ledger-prefix' {$changedPath=Join-Path $scopeShadow $script:R1Ledger;$expected='R1-SCOPE: ledger prefix rewritten'}
            'R1-FINAL-missing-path' {$paths=@($paths|Where-Object{$_ -cne 'lean-toolchain'});$expected='R1-SCOPE: missing original path lean-toolchain'}
            'R1-FINAL-extra-path' {$paths+=@('R1_OUTSIDE_SCOPE.txt');$expected='R1-SCOPE: new path outside exact roster R1_OUTSIDE_SCOPE.txt'}
            'R1-FINAL-changed-pin' {$changedPath=Join-Path $scopeShadow 'lean-toolchain';$pin=Get-LN1Pin $changedPath;$expected='R1-IDENTITY: changed pin '+$changedPath}
            default {throw 'R1-CONTROLS: unknown scope holdout'}
          }
          if($changedPath){
            $before=[IO.File]::ReadAllBytes($changedPath);$mutated=[byte[]]$before.Clone();$mutated[0]=$mutated[0] -bxor 1
            [IO.File]::WriteAllBytes($changedPath,$mutated)
            $saved=Join-Path $run ($case.id+'-mutated.bin');[IO.File]::WriteAllBytes($saved,$mutated);$pins.Add((Get-LN1Pin $saved))
          }
          try{
            if($pin){Assert-R1Pin $pin}else{[void](Assert-R1ScopeFiles $scopeShadow $baseline $paths)}
          }catch{$rejected=$_.Exception.Message}
          if($case.id -eq 'R1-FINAL-out-of-scope'){
            # Additional metadata holdouts exercise the same production Git
            # predicate used by the actual scope caller, without editing an index.
            $stageRows=@($baseline.files|ForEach-Object{$_.mode+' '+$_.gitBlob+" 0`t"+$_.path+[char]0})
            $stageText=$stageRows -join ''
            [void](Assert-R1GitScope $baseline $stageText @())
            $entry=@($baseline.files|Where-Object{Test-R1Exact $_.path 'lean-toolchain'})[0]
            $needle=$entry.mode+' '+$entry.gitBlob+" 0`tlean-toolchain"+[char]0
            $probes=@(
              @{name='mode';text=$stageText.Replace($needle,('100755 '+$entry.gitBlob+" 0`tlean-toolchain"+[char]0));changed=@();expected='R1-SCOPE: current Git mode changed lean-toolchain'},
              @{name='blob';text=$stageText.Replace($needle,($entry.mode+' '+('0'*40)+" 0`tlean-toolchain"+[char]0));changed=@();expected='R1-SCOPE: protected Git blob changed lean-toolchain'},
              @{name='path';text=$stageText;changed=@('lean-toolchain');expected='R1-SCOPE: Git change outside exact roster lean-toolchain'})
            $gitHoldouts=@(foreach($probe in $probes){
              $failure=$null
              try{[void](Assert-R1GitScope $baseline $probe.text $probe.changed)}catch{$failure=$_.Exception.Message}
              if(-not (Test-R1Exact $failure $probe.expected)){throw ('R1-CONTROLS: Git metadata rejection differs '+$failure)}
              $fixturePath=Join-Path $run ('R1-GIT-'+$probe.name+'-TEST-ONLY.json')
              Write-R1Json $fixturePath $probe;$pins.Add((Get-LN1Pin $fixturePath))
              @{name=$probe.name;fixture=(Get-LN1Pin $fixturePath);rejection=$failure;actualPredicate=$true;liveIndexWrites=0}
            })
            $report.gitMetadataHoldouts=$gitHoldouts
          }
          if($case.expectedVerdict -eq 'accept'){
            if($null -ne $rejected){throw ('R1-CONTROLS: healthy complete file-domain rejected '+$rejected)}
            $healthyScope=Invoke-R1Caller ('& '+(Quote-R1 (Join-Path $PSScriptRoot 'scope_check.ps1'))+' -Complete') ($case.id+'-caller') $root 600
            $head=(& git -c core.excludesfile= -c core.safecrlf=false rev-parse HEAD).Trim()
            $currentPaths=@(@(& git -c core.excludesfile= -c core.safecrlf=false diff --name-only $script:R1OriginalBase)+@(& git -c core.excludesfile= -c core.safecrlf=false ls-files --others --exclude-standard)|Sort-Object -Unique)
            $healthyConsumed=Assert-R1FinalScope $healthyScope $root $head $currentPaths
            $report.healthyFinalScope=@{capture=$healthyScope;consumed=$healthyConsumed}
          }elseif(-not (Test-R1Exact $rejected $expected)){throw ('R1-CONTROLS: wrong scope rejection '+$rejected)}
          $results.Add(@{id=$case.id;passed=$true;checkedOriginalFiles=3930;rejection=$rejected;
            boundary='Actual R1 file/pin predicate on complete isolated current source roster; no live protected bytes changed.'})
        }finally{
          if($changedPath -and $null -ne $before){
            [IO.File]::WriteAllBytes($changedPath,$before)
            if(-not (Test-R1Exact (Get-LN1BytesHash ([IO.File]::ReadAllBytes($changedPath))) (Get-LN1BytesHash $before))){throw 'R1-CONTROLS: shadow restoration failed'}
          }
        }
      }
    }else{throw ('R1-CONTROLS: unknown handler '+$case.handler)}
  }
  if(-not (Test-R1Exact ($results.id -join '|') ($selected.id -join '|'))){throw 'R1-CONTROLS: completed ordered roster differs'}
  $report.success=$true
}catch{$report.failure=$_.Exception.Message}
finally{
  $errors=[Collections.Generic.List[string]]::new()
  foreach($p in $pins){try{Assert-R1Pin $p}catch{$errors.Add($_.Exception.Message)}}
  $report.integrity=@{success=($errors.Count -eq 0);checked=$pins.Count;errors=@($errors.ToArray())}
  try{Remove-R1Scratch $scratch $run;$report.cleanup=@{success=$true;scratchAbsent=$true}}
  catch{$report.cleanup=@{success=$false;error=$_.Exception.Message}}
  $report.success=$report.success -and $report.integrity.success -and $report.cleanup.success
  $report.results=@($results.ToArray());$report.pins=@($pins.ToArray());$report.completedUtc=[DateTime]::UtcNow.ToString('o')
  [void][IO.Directory]::CreateDirectory($run)
  Write-R1Json (Join-Path $run 'RESULT.json') $report
}
Write-Output ('R1-CONTROLS evidence='+$run)
if(-not $report.success){Write-Output ('R1-CONTROLS FAIL '+$report.failure);exit 1}
Write-Output ('R1-CONTROLS PASS count='+$results.Count)
