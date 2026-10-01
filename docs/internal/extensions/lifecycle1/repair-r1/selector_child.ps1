param([string]$SpecPath,[string]$RepositoryRoot,[string]$EvidenceRoot)
Set-StrictMode -Version Latest
$ErrorActionPreference='Stop'
$utf8=[Text.UTF8Encoding]::new($false,$true)
$spec=Get-Content -LiteralPath $SpecPath -Raw|ConvertFrom-Json
[void][IO.Directory]::CreateDirectory($EvidenceRoot)
. (Join-Path $RepositoryRoot 'scripts/owned_process_tree.ps1')
. (Join-Path $RepositoryRoot 'scripts/lifecycle_validator_environment.ps1')
$key=if($spec.kind -ceq 'dependency'){'LIFE1_DEPENDENCY_SELECTOR'}else{'LIFE1_VALIDATE_SELECTOR'}
function Snapshot {
  $vars=[Environment]::GetEnvironmentVariables('Process')
  return [ordered]@{present=$vars.Contains($key);value=if($vars.Contains($key)){[string]$vars[$key]}else{$null}}
}
function Same([object]$a,[object]$b) {
  return $a.present -eq $b.present -and (-not $a.present -or $a.value -ceq $b.value)
}
function Set-Ambient([object]$state) {
  if($state.present){[Environment]::SetEnvironmentVariable($key,[string]$state.value,'Process')}
  else{[Environment]::SetEnvironmentVariable($key,[NullString]::Value,'Process')}
}
function Write-Receipt([string]$name,[object]$value) {
  [IO.File]::WriteAllText((Join-Path $EvidenceRoot $name),($value|ConvertTo-Json -Depth 40),$utf8)
}
function Registry-Lines {
  $nativeIds=@('L01-W-EMPTY','L02-C-EMPTY','L03-W-SINGLE','L04-C-SINGLE','L05-W-REPEAT','L06-C-REPEAT','L07-W-TIE','L08-C-TIE','L09-W-INVALID','L10-C-INVALID','L11-W-DIRTY','L12-C-DIRTY','L13-W-N24','L14-C-N24','L15-W-N83','L16-C-N83')
  for($i=0;$i -lt 16;$i++) {
    $model=if($i%2 -eq 0){'word'}else{'comparison'}
    $kind=if($i -ge 10 -and $i -lt 12){'dirty-entry'}else{'lifecycle'}
    'LIFE1-REGISTRY|'+$nativeIds[$i]+'|'+$model+'|'+$kind+'|PASS'
  }
}
function Assert-SingleLines([object[]]$lines) {
  if($lines.Count -ne 2 -or $lines[0] -cnotmatch '^LIFE1-CASE\|L01-W-EMPTY\|PASS\|steps=\d+\|queries=\d+\|querySteps=\d+\|extent=\d+\|peak=\d+\|release=\d+\|dirty=\d+$' -or
     $lines[1] -cne 'LIFE1-PASS|mode=single|cases=1'){throw 'CONTROL: focused selector did not execute exactly its actual fixture'}
}
$initial=Snapshot
$record=[ordered]@{id=$spec.id;spec=$spec;shell=(Get-Process -Id $PID).Path;pid=$PID;
  version=$PSVersionTable.PSVersion.ToString();dotnet=[Environment]::Version.ToString();
  initial=$initial;passed=$false;streamRepresentation='unchanged owned helper returned lines'}
try {
  Set-Ambient $spec.ambient
  $before=Snapshot
  $record.before=$before
  if($spec.ambient.present -and $spec.ambient.value -ceq '' -and -not $before.present) {
    $record.emptyEnvironmentRepresentation='This runtime removes present-empty; observed absence, not a fabricated empty value.'
  }
  if($spec.kind -ceq 'native') {
    $selector=if($spec.selector.present){[string]$spec.selector.value}else{$null}
    $exe=Join-Path $RepositoryRoot '.lake/build/bin/rmq_lifecycle_validate.exe'
    $arguments=@($spec.arguments)
    $expected=$spec.expected
    if($spec.id -ceq 'S04_PRESENT_EMPTY_REGISTRY' -and $PSVersionTable.PSEdition -ceq 'Desktop'){$expected=$spec.legacyExpected}
    if($spec.id -ceq 'S23_LAUNCH_FAILURE'){
      $exe=(Get-Process -Id $PID).Path
      $fixture=Join-Path $EvidenceRoot 'exit7.ps1'
      [IO.File]::WriteAllText($fixture,"param([int]`$Code)`nexit `$Code",$utf8)
      $arguments=@('-NoProfile','-ExecutionPolicy','Bypass','-File',$fixture,'-Code','7')
    }
    if($expected.exit -ne 0) {
      $positiveSelector=$null;$positiveMode='single'
      if($spec.id -ceq 'S23_LAUNCH_FAILURE') {
        $positiveArguments=@($arguments);$positiveArguments[-1]='0';$positiveMode='empty'
      } elseif($arguments.Count -eq 0) {
        $positiveArguments=@();$positiveSelector='id:L01-W-EMPTY'
      } elseif($arguments[0] -ceq '--registry') {
        $positiveArguments=@('--registry');$positiveMode='registry'
      } else {$positiveArguments=@('L01-W-EMPTY')}
      $positive=Invoke-LifecycleValidatorProcess -FilePath $exe -Arguments $positiveArguments -WorkingDirectory $RepositoryRoot `
        -Stage ($spec.id+'-P') -DeadlineSeconds 30 -TempRoot $EvidenceRoot -Selector $positiveSelector
      $record.positive=[ordered]@{result=$positive;arguments=$positiveArguments;selector=$positiveSelector;ambient=$before;after=(Snapshot)}
      Write-Receipt 'positive.json' $record.positive
      if(-not (Same $before (Snapshot)) -or $positive.ExitCode -ne 0 -or $positive.TimedOut -or $positive.OutputLimitExceeded -or
         $positive.Ownership -cne 'kill-on-close-job' -or @($positive.TerminatedIds).Count -ne 0 -or @($positive.StandardError).Count -ne 0){throw 'CONTROL: same-environment positive process failed'}
      if($positiveMode -ceq 'single'){Assert-SingleLines @($positive.StandardOutput)}
      elseif($positiveMode -ceq 'empty'){if(@($positive.StandardOutput).Count -ne 0){throw 'CONTROL: unexpected positive output'}}
      elseif((@($positive.StandardOutput) -join "`n") -cne (@(Registry-Lines) -join "`n")){throw 'CONTROL: positive registry differs'}
    }
    $result=Invoke-LifecycleValidatorProcess -FilePath $exe -Arguments $arguments `
      -WorkingDirectory $RepositoryRoot -Stage $spec.id -DeadlineSeconds 30 -TempRoot $EvidenceRoot -Selector $selector
    $record.result=$result
    $after=Snapshot;$record.after=$after
    $record.restored=Same $before $after
    Write-Receipt 'receipt.json' $record
    if(-not $record.restored){throw 'CONTROL: ambient state was not restored'}
    if($result.TimedOut -or $result.OutputLimitExceeded -or $result.Ownership -cne 'kill-on-close-job' -or @($result.TerminatedIds).Count -ne 0) {throw 'CONTROL: incomplete process outcome'}
    if($result.ExitCode -ne $expected.exit){throw ('CONTROL: wrong native exit '+$result.ExitCode)}
    $stdout=@($result.StandardOutput);$stderr=@($result.StandardError)
    if($expected.mode -ceq 'child-exit-failure') {
      if($stdout.Count -ne 0 -or $stderr.Count -ne 0) {throw 'CONTROL: unexpected child failure diagnostics'}
    } elseif($expected.exit -ne 0) {
      if($stdout.Count -ne 0 -or $stderr.Count -ne 1 -or $stderr[0] -cne $expected.error){throw 'CONTROL: wrong or mixed rejection diagnostics'}
    } else {
      if($stderr.Count){throw 'CONTROL: unexpected native stderr'}
      if($expected.mode -ceq 'registry') {
        $lines=@(Registry-Lines)
        if(($stdout -join "`n") -cne ($lines -join "`n")){throw 'CONTROL: exact registry mismatch'}
      } elseif($expected.mode -ceq 'startup') {
        if($stdout.Count -ne 1 -or $stdout[0] -cne 'LIFE1-STARTUP|PASS|cases=16'){throw 'CONTROL: wrong startup/no-case boundary'}
      } elseif($expected.mode -ceq 'single') {
        Assert-SingleLines $stdout
      } else {throw 'CONTROL: unused native expectation'}
    }
  } elseif($spec.kind -ceq 'wrapper') {
    $params=@{}
    foreach($property in $spec.parameters.PSObject.Properties){$params[$property.Name]=$property.Value}
    $message=$null;$output=@()
    if($spec.expected.exit -ne 0) {
      $positiveOutput=@(& (Join-Path $RepositoryRoot 'scripts/lifecycle_validator.ps1') -Stage startup)
      $prefix='LIFE1-VALIDATOR PASS stage=startup processes=2 logs='
      if($positiveOutput.Count -ne 1 -or -not $positiveOutput[0].StartsWith($prefix,[StringComparison]::Ordinal) -or -not(Same $before (Snapshot))){throw 'CONTROL: same-environment positive wrapper failed'}
      $positiveLog=$positiveOutput[0].Substring($prefix.Length)
      $expectedLog='^'+[regex]::Escape([IO.Path]::GetFullPath((Join-Path $RepositoryRoot '.lake/lifecycle-validator')).TrimEnd('\','/')+[IO.Path]::DirectorySeparatorChar)+'[0-9a-f]{32}$'
      if($positiveLog -cnotmatch $expectedLog){throw 'CONTROL: positive wrapper log path differs'}
      $positivePass=Get-Content -LiteralPath (Join-Path $positiveLog 'PASS.json') -Raw|ConvertFrom-Json
      if(-not $positivePass.identityPreserved -or $positivePass.stage -cne 'startup' -or $positivePass.processCount -ne 2){throw 'CONTROL: positive wrapper receipt differs'}
      $record.positive=[ordered]@{output=$positiveOutput;logRoot=$positiveLog;receipt=$positivePass;ambient=$before}
      Write-Receipt 'positive.json' $record.positive
    }
    try {
      if($spec.id -ceq 'W09_DUPLICATE_CASE') {
        $output=@(& (Join-Path $RepositoryRoot 'scripts/lifecycle_validator.ps1') -Stage single -Case L01-W-EMPTY -Case L01-W-EMPTY)
      } else {$output=@(& (Join-Path $RepositoryRoot 'scripts/lifecycle_validator.ps1') @params)}
    }
    catch {
      $message=$_.Exception.Message
      $record.errorId=$_.FullyQualifiedErrorId
      if($spec.id -ceq 'W09_DUPLICATE_CASE' -and $_.FullyQualifiedErrorId -ceq 'ParameterAlreadyBound,lifecycle_validator.ps1') {
        $record.originalError=$message;$message='PARAMETER_ALREADY_BOUND'
      }
    }
    $after=Snapshot
    $record.output=$output;$record.error=$message;$record.after=$after;$record.restored=Same $before $after
    Write-Receipt 'receipt.json' $record
    if(-not $record.restored){throw 'CONTROL: wrapper changed caller environment'}
    if($spec.expected.exit -ne 0) {
      if($output.Count -ne 0 -or $message -cne $spec.expected.error){throw ('CONTROL: wrong wrapper failure: '+$message)}
    } elseif($null -ne $message -or $output.Count -ne 1 -or $output[0] -cnotmatch $spec.expected.pattern) {
      throw ('CONTROL: wrapper success mismatch: '+$message)
    } else {
      $logRoot=$output[0].Substring($output[0].IndexOf(' logs=')+6)
      $allowed=(Join-Path $RepositoryRoot '.lake/lifecycle-validator')
      $expectedPath='^'+[regex]::Escape([IO.Path]::GetFullPath($allowed).TrimEnd('\','/')+[IO.Path]::DirectorySeparatorChar)+'[0-9a-f]{32}$'
      if($logRoot -cnotmatch $expectedPath){throw 'CONTROL: unexpected production log path'}
      $pass=Get-Content -LiteralPath (Join-Path $logRoot 'PASS.json') -Raw|ConvertFrom-Json
      # Assign the JSON value first: Windows PowerShell does not enumerate a
      # ConvertFrom-Json array on its pipeline, unlike current PowerShell.
      $processes=Get-Content -LiteralPath (Join-Path $logRoot 'processes.json') -Raw|ConvertFrom-Json
      $count=if($params.Stage -ceq 'startup'){2}else{3}
      if(-not $pass.identityPreserved -or $pass.expectedVerdict -cne 'PASS' -or $pass.stage -cne $params.Stage -or $pass.processCount -ne $count -or $processes.Count -ne $count) {throw 'CONTROL: production receipt mismatch'}
      $record.productionLogRoot=$logRoot
    }
  } else {throw 'CONTROL: unknown/unused selector control kind'}
  $record.passed=$true
} finally {
  Set-Ambient $initial
  $record.fixtureRestored=Same $initial (Snapshot)
  Write-Receipt 'receipt.json' $record
}
if(-not $record.passed -or -not $record.fixtureRestored){throw 'CONTROL: incomplete fixture'}
Write-Output ('L1R1-CONTROL|'+$spec.id+'|PASS')
