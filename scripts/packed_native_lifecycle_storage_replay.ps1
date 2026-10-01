param(
  [AllowEmptyString()][string]$Cases,
  [switch]$List,
  [switch]$SelfTest,
  [string]$LeanRoot = 'C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0',
  [string]$CHeaderRoot = 'C:/Strawberry/c/x86_64-w64-mingw32/include',
  [string]$CCompilerHeaderRoot = 'C:/Strawberry/c/lib/gcc/x86_64-w64-mingw32/13.2.0/include',
  [string]$RegistryPath,
  [ValidateRange(1,600)][int]$CompilerDeadlineSeconds = 120,
  [ValidateRange(1,120)][int]$ProbeDeadlineSeconds = 30
)
# This is a Windows native-runtime experiment, outside the Lean kernel.
# No cached executable is trusted: each semantic run rebuilds its owned probe.
$ErrorActionPreference = 'Stop'
Set-StrictMode -Version Latest
$taskRoot = [IO.Path]::GetFullPath((Split-Path $PSScriptRoot -Parent))
$taskScript = [IO.Path]::GetFullPath($PSCommandPath)
$taskEncoding = [Text.UTF8Encoding]::new($false, $true)
$taskSelectedBound = $PSBoundParameters.ContainsKey('Cases')
$taskStageResults = [Collections.Generic.List[object]]::new()
$taskChecks = [Collections.Generic.List[object]]::new()
$taskRunRoot = $null
$taskSuccess = $false
$taskFailure = $null
$taskIdentity = $null
$taskSources = @()
$taskSelected = @()
$taskIntegrityState = [ordered]@{root=$taskRoot;temp=$null;baseline=$null;pins=[Collections.Generic.List[object]]::new();captureErrors=[Collections.Generic.List[string]]::new()}
$taskIntegrity = $null
$taskShell = (Get-Process -Id $PID).Path
$taskExpectedIds = @(
  'pop-unique','shrink-unique','pop-shared','shrink-shared',
  'pop-empty-unique','pop-empty-shared','shrink-noop',
  'replace-prefix','replace-overlap','replace-tail','replace-empty',
  'replace-alias','replace-element-alias','fail-alloc','fail-after-alloc',
  'fail-mid-copy','fail-handoff','fail-after-consume','fail-alias',
  'negative-shrink','negative-alias','negative-cleanup','negative-value'
)
$taskSpecification = @(101,-7,303,303,505,-19)
# Independent frozen fixture mapping: operation,n,start,count,alias,elementAlias,
# failStage,mutation. Runtime results never supply these expected inputs.
$taskExpectedInputs = @(
  '0,6,0,5,0,0,0,0','1,6,0,2,0,0,0,0','0,6,0,5,1,0,0,0',
  '1,6,0,2,1,0,0,0','0,0,0,0,0,0,0,0','0,0,0,0,1,0,0,0',
  '1,6,0,6,0,0,0,0','2,6,0,2,0,0,0,0','2,6,1,4,0,0,0,0',
  '2,6,4,2,0,0,0,0','2,6,0,0,0,0,0,0','2,6,1,4,1,0,0,0',
  '2,6,4,2,0,1,0,0','3,6,1,4,0,0,1,0','3,6,1,4,0,0,2,0',
  '3,6,1,4,0,0,3,0','3,6,1,4,0,0,4,0','3,6,1,4,0,0,5,0',
  '3,6,1,4,1,0,3,0','2,6,0,2,0,0,0,1','2,6,1,4,1,0,0,2',
  '3,6,1,4,0,0,4,3','2,6,1,4,0,0,0,4'
)
if (-not $PSBoundParameters.ContainsKey('RegistryPath')) {
  $RegistryPath = Join-Path $taskRoot 'docs/internal/extensions/lifecycle-native-p0/REGISTRY.json'
}

function Write-LNJson([string]$Path, [object]$Value) {
  [IO.File]::WriteAllText($Path, ($Value | ConvertTo-Json -Depth 40), $taskEncoding)
}
function Get-LNPin([string]$Path) {
  $resolved = [IO.Path]::GetFullPath($Path)
  if (-not (Test-Path -LiteralPath $resolved -PathType Leaf)) { throw "IDENTITY: missing file $resolved" }
  $pin = [ordered]@{ path=$resolved; bytes=(Get-Item -LiteralPath $resolved).Length;
    sha256=(Get-FileHash -LiteralPath $resolved -Algorithm SHA256).Hash }
  $taskIntegrityState.pins.Add($pin)
  return $pin
}
function Assert-LNEqual([object]$Actual, [object]$Expected, [string]$Surface) {
  if (($Actual | ConvertTo-Json -Depth 30 -Compress) -cne ($Expected | ConvertTo-Json -Depth 30 -Compress)) {
    throw "MEASUREMENT: $Surface differs"
  }
}
function Get-LNAvailablePin([string]$Path,[switch]$Required) {
  if(-not [IO.File]::Exists($Path)){
    if($Required){$taskIntegrityState.captureErrors.Add('INTEGRITY: required artifact unavailable: '+$Path)}
    return $null
  }
  try {return Get-LNPin $Path}
  catch {$taskIntegrityState.captureErrors.Add('INTEGRITY: artifact capture failed: '+$Path+'; '+$_.Exception.Message);return $null}
}
function Read-LNRegistry([string]$Path) {
  try { $registry = [IO.File]::ReadAllText([IO.Path]::GetFullPath($Path), $taskEncoding) | ConvertFrom-Json }
  catch { throw 'REGISTRY: invalid JSON or unavailable file' }
  try {
    Assert-LNProperties $registry @('schema','inputSpecification','initialCapacity','cases') 'registry'
    foreach($row in @($registry.cases)) {
      Assert-LNProperties $row @('id','operation','n','start','count','alias','elementAlias','failStage','mutation','expectedExit','failure') 'registry row'
    }
  } catch {throw 'REGISTRY: property set differs'}
  if ($registry.schema -ne 1) { throw 'REGISTRY: schema differs' }
  if (($registry.inputSpecification -join ',') -cne ($taskSpecification -join ',') -or
      $registry.initialCapacity -ne 32) { throw 'REGISTRY: independent input specification differs' }
  $rows = @($registry.cases)
  $ids = @($rows | ForEach-Object { [string]$_.id })
  if ($ids.Count -ne $taskExpectedIds.Count) { throw 'REGISTRY: cardinality differs' }
  if (@($ids | Select-Object -Unique).Count -ne $ids.Count) { throw 'REGISTRY: duplicate ID' }
  for ($i=0; $i -lt $taskExpectedIds.Count; $i++) {
    if ($ids[$i] -cne $taskExpectedIds[$i]) { throw 'REGISTRY: ordered IDs differ' }
    $failure = switch ($ids[$i]) {
      'negative-shrink' {'capacity'} 'negative-alias' {'ownership'}
      'negative-cleanup' {'cleanup'} 'negative-value' {'values'} default {'none'}
    }
    $exit = if ($failure -ceq 'none') {0} else {3}
    if ($rows[$i].expectedExit -ne $exit -or $rows[$i].failure -cne $failure) {
      throw 'REGISTRY: verdict mapping differs'
    }
    $row=$rows[$i]
    $inputs=@($row.operation,$row.n,$row.start,$row.count,$row.alias,$row.elementAlias,$row.failStage,$row.mutation)
    if (($inputs -join ',') -cne $taskExpectedInputs[$i]) { throw 'REGISTRY: input mapping differs' }
  }
  return $registry
}
function Resolve-LNSelection([object]$Registry, [bool]$Bound, [string]$Selector) {
  if (-not $Bound) { return @($Registry.cases) }
  if ([string]::IsNullOrWhiteSpace($Selector)) { throw 'SELECTOR: explicit empty selector' }
  $ids = @($Selector.Split(',') | ForEach-Object { $_.Trim() })
  if (@($ids | Where-Object { [string]::IsNullOrWhiteSpace($_) }).Count -ne 0) {
    throw 'SELECTOR: missing ID'
  }
  if (@($ids | Select-Object -Unique).Count -ne $ids.Count) { throw 'SELECTOR: duplicate ID' }
  foreach ($id in $ids) {
    if ($taskExpectedIds -cnotcontains $id) { throw 'SELECTOR: unknown ID' }
  }
  # Selection order is canonical registry order, independent of CLI ordering.
  return @($Registry.cases | Where-Object { $ids -ccontains $_.id })
}

# The child belongs to the shared helper's release-gated job before it starts
# any compiler/probe. Byte-stream copies retain the native output exactly.
$taskChildScript = @'
param([string]$SpecPath,[string]$LaunchReleasePath)
$ErrorActionPreference = 'Stop'
while (-not (Test-Path -LiteralPath $LaunchReleasePath -PathType Leaf)) { Start-Sleep -Milliseconds 10 }
$spec = [IO.File]::ReadAllText($SpecPath) | ConvertFrom-Json
$encoding = [Text.UTF8Encoding]::new($false)
$process = [Diagnostics.Process]::new()
$stdout = $null
$stderr = $null
try {
  $info = [Diagnostics.ProcessStartInfo]::new()
  $info.FileName = [string]$spec.file
  $info.WorkingDirectory = [string]$spec.cwd
  $info.UseShellExecute = $false
  $info.CreateNoWindow = $true
  $info.RedirectStandardOutput = $true
  $info.RedirectStandardError = $true
  # Win32 quoting, including empty arguments and trailing backslashes.
  $quoted = foreach ($arg in @($spec.arguments)) {
    $value = [string]$arg
    '"' + ([regex]::Replace([regex]::Replace($value, '(\\*)"', '$1$1\"'), '(\\+)$', '$1$1')) + '"'
  }
  $info.Arguments = $quoted -join ' '
  foreach ($property in $spec.environment.PSObject.Properties) {
    $info.EnvironmentVariables[$property.Name] = [string]$property.Value
  }
  $process.StartInfo = $info
  $stdout = [IO.FileStream]::new([string]$spec.stdout, [IO.FileMode]::Create, [IO.FileAccess]::Write, [IO.FileShare]::Read, 1, [IO.FileOptions]::WriteThrough)
  $stderr = [IO.FileStream]::new([string]$spec.stderr, [IO.FileMode]::Create, [IO.FileAccess]::Write, [IO.FileShare]::Read, 1, [IO.FileOptions]::WriteThrough)
  $watch = [Diagnostics.Stopwatch]::StartNew()
  if (-not $process.Start()) { throw 'native process did not start' }
  [IO.File]::WriteAllText([string]$spec.pid, [string]$process.Id, $encoding)
  $copyOut = $process.StandardOutput.BaseStream.CopyToAsync($stdout)
  $copyErr = $process.StandardError.BaseStream.CopyToAsync($stderr)
  $overflow = $false
  while (-not $process.WaitForExit(50)) {
    if (($stdout.Length + $stderr.Length) -gt [long]$spec.outputLimit) { $overflow=$true; break }
  }
  if ($overflow) {
    [IO.File]::WriteAllText([string]$spec.overflow, 'native redirected output limit exceeded', $encoding)
    # Root exits; the owning job barrier reaps the still-live native tree.
    exit 125
  }
  $process.WaitForExit()
  $null = $copyOut.GetAwaiter().GetResult()
  $null = $copyErr.GetAwaiter().GetResult()
  $watch.Stop()
  $actualExit = [int]$process.ExitCode
  $receipt = [ordered]@{pid=$process.Id; exitCode=$actualExit; durationSeconds=$watch.Elapsed.TotalSeconds}
  [IO.File]::WriteAllText([string]$spec.exit, ($receipt | ConvertTo-Json -Compress), $encoding)
  if (($stdout.Length + $stderr.Length) -gt [long]$spec.outputLimit) {
    [IO.File]::WriteAllText([string]$spec.overflow, 'native redirected output limit exceeded after stream drain', $encoding)
    exit 125
  }
  exit $actualExit
} catch {
  [IO.File]::WriteAllText([string]$spec.error, $_.ToString(), $encoding)
  exit 124
} finally {
  if ($null -ne $stdout) { $stdout.Dispose() }
  if ($null -ne $stderr) { $stderr.Dispose() }
  $process.Dispose()
}
'@
function Invoke-LNStage([string]$Name,[string]$File,[string[]]$Arguments,[int]$Deadline,
    [hashtable]$Environment=@{}) {
  $stem = Join-Path $taskRunRoot ('{0:D3}-{1}' -f $taskStageResults.Count,$Name)
  $spec = [ordered]@{file=$File; arguments=@($Arguments); cwd=$taskRoot; environment=$Environment;
    stdout=($stem+'.stdout');stderr=($stem+'.stderr');exit=($stem+'.exit.json');
    pid=($stem+'.pid');error=($stem+'.child-error');overflow=($stem+'.overflow');outputLimit=8388608}
  $specPath = $stem+'.spec.json'
  Write-LNJson $specPath $spec
  $null=Get-LNPin $specPath
  $launch = $null
  $launchError = $null
  try {
    $launch = Invoke-RMQOwnedBoundedProcess -FilePath $taskShell `
      -Arguments @('-NoLogo','-NoProfile','-ExecutionPolicy','Bypass','-File',
        (Join-Path $taskRunRoot 'stage-child.ps1'),'-SpecPath',$specPath) `
      -WorkingDirectory $taskRoot -Stage $Name -DeadlineSeconds $Deadline `
      -OutputLimitBytes 8388608 -TempRoot (Join-Path $taskRunRoot 'launcher-temporary') -ReleaseGatedScript
  } catch { $launchError = $_.ToString() }
  # Pin raw evidence before any strict decoding/parsing can throw.
  $rawPins=@{}
  foreach($p in @($spec.stdout,$spec.stderr,$spec.exit,$spec.pid,$spec.error,$spec.overflow)) {
    $rawPins[$p]=Get-LNAvailablePin $p -Required:($p -in @($spec.stdout,$spec.stderr))
  }
  try {
    $child = if (Test-Path -LiteralPath $spec.exit) {
    [IO.File]::ReadAllText($spec.exit,$taskEncoding) | ConvertFrom-Json
  } else { $null }
  $stdoutText = if (Test-Path -LiteralPath $spec.stdout) { [IO.File]::ReadAllText($spec.stdout,$taskEncoding) } else { '' }
  $stderrText = if (Test-Path -LiteralPath $spec.stderr) { [IO.File]::ReadAllText($spec.stderr,$taskEncoding) } else { '' }
  } catch {throw "DIAGNOSTIC: invalid raw stage evidence for $Name; $($_.Exception.Message)"}
  $stage = [ordered]@{name=$Name;command=@{file=$File;arguments=@($Arguments)};deadlineSeconds=$Deadline;
    launcher=$launch;launcherError=$launchError;child=$child;
    stdout=$rawPins[$spec.stdout];
    stderr=$rawPins[$spec.stderr];
    nativePid=if(Test-Path -LiteralPath $spec.pid){[int][IO.File]::ReadAllText($spec.pid)}else{$null};
    childError=if(Test-Path -LiteralPath $spec.error){[IO.File]::ReadAllText($spec.error)}else{$null};
    nativeOutputLimitExceeded=(Test-Path -LiteralPath $spec.overflow)}
  $taskStageResults.Add($stage)
  Write-LNJson ($stem+'.stage.json') $stage
  foreach($p in @(($stem+'.stage.json'),$spec.exit,$spec.pid,$spec.error,$spec.overflow)) {
    $null=Get-LNAvailablePin $p
  }
  return [pscustomobject]@{Record=$stage;Stdout=$stdoutText;Stderr=$stderrText}
}
function Assert-LNProcess([object]$Stage,[int]$ExpectedExit) {
  $r = $Stage.Record
  if ($r.launcherError -or $null -eq $r.launcher -or $r.childError -or
      $r.launcher.TimedOut -or $r.launcher.OutputLimitExceeded -or $r.nativeOutputLimitExceeded) {
    throw "PROCESS: $($r.name) was not a completed bounded process; see retained logs"
  }
  if (@($r.launcher.StandardOutput).Count -ne 0 -or @($r.launcher.StandardError).Count -ne 0) {
    throw "DIAGNOSTIC: unexpected launcher output for $($r.name)"
  }
  if ($null -eq $r.child -or $r.child.exitCode -ne $ExpectedExit -or $r.launcher.ExitCode -ne $ExpectedExit) {
    throw "PROCESS: $($r.name) actual child or launcher exit differs from $ExpectedExit"
  }
}
function Read-LNOneJson([string]$Text,[string]$Surface) {
  # Native protocol is one compact JSON value on one line, with one line ending.
  if ($Text -notmatch '\A[^\r\n]+\r?\n\z') { throw "DIAGNOSTIC: $Surface is not exactly one JSON line" }
  try { return ($Text | ConvertFrom-Json) } catch { throw "DIAGNOSTIC: $Surface invalid JSON" }
}
function Assert-LNNoStderr([object]$Stage) {
  if ($Stage.Stderr.Length -ne 0) { throw "DIAGNOSTIC: unexpected or mixed stderr for $($Stage.Record.name)" }
}
function Assert-LNRejected([scriptblock]$Action,[string]$ExpectedPrefix,[string]$Name) {
  $rejected = $false
  try { & $Action } catch {
    if (-not $_.Exception.Message.StartsWith($ExpectedPrefix,[StringComparison]::Ordinal)) { throw }
    $rejected = $true
  }
  if (-not $rejected) { throw "SELFTEST: $Name unexpectedly accepted" }
  $taskChecks.Add(@{id=$Name;outcome='expected-reject';surface=$ExpectedPrefix})
}

function Assert-LNProperties([object]$Object,[string[]]$Names,[string]$Surface) {
  $actual=@($Object.PSObject.Properties.Name | Sort-Object)
  $wanted=@($Names | Sort-Object)
  if (($actual -join ',') -cne ($wanted -join ',')) { throw "MEASUREMENT: $Surface property set differs" }
}
function Test-LNValues([object]$Root,[int]$Start,[int]$Count) {
  if ($Root.present -ne 1 -or $Root.size -ne $Count) { return $false }
  for($i=0;$i -lt $Count;$i++) {
    if ($Root.values[$i] -ne $taskSpecification[$Start+$i] -or $Root.ids[$i] -ne ($Start+$i)) {return $false}
  }
  return $true
}
function Test-LNReferences([object]$Snapshot,[int]$N,[int]$Start,[int]$Count,[int]$Alias,[int]$ElementAlias) {
  for($i=0;$i -lt 6;$i++) {
    $expected=[int]($i -lt $N -and $Alias -eq 1)+[int]($i -ge $Start -and $i -lt ($Start+$Count))+[int]($i -eq 0 -and $ElementAlias -eq 1)
    $dead=[int]($i -lt $N -and $expected -eq 0)
    if ($Snapshot.elementRC[$i] -ne $expected -or $Snapshot.destroyed[$i] -ne $dead) {return $false}
  }
  return $true
}
function Get-LNMeasuredFailure([object]$Row,[object]$Snapshot) {
  $v=$Snapshot.roots[2]
  if ($Row.operation -eq 3) {
    if ($Snapshot.roots[0].present -ne 0 -or $v.present -ne 0 -or
        $Snapshot.roots[1].present -ne $Row.alias -or $Snapshot.oldReachable -ne $Row.alias) {return 'cleanup'}
    if ($Row.alias -eq 1 -and (-not (Test-LNValues $Snapshot.roots[1] 0 $Row.n) -or $Snapshot.roots[1].rc -ne 1)) {return 'cleanup'}
    if (-not (Test-LNReferences $Snapshot $Row.n 0 0 $Row.alias 0)) {return 'cleanup'}
    return 'none'
  }
  if ($Row.operation -lt 2) {
    if (-not (Test-LNValues $v 0 $Row.count)) {return 'values'}
    if ($v.capacity -ne 32) {return 'capacity'}
    if ($Row.alias -eq 0 -and ($v.old -ne 1 -or $v.rc -ne 1)) {return 'capacity'}
    if ($Row.alias -eq 1 -and ($Snapshot.roots[1].old -ne 1 -or
        -not (Test-LNValues $Snapshot.roots[1] 0 $Row.n) -or $v.old -ne 0 -or
        $v.rc -ne 1 -or $Snapshot.roots[1].rc -ne 1)) {return 'ownership'}
    if ($v.capacity -lt $v.size) {return 'capacity'}
    if (-not (Test-LNReferences $Snapshot $Row.n 0 $Row.count $Row.alias 0)) {return 'references'}
    return 'none'
  }
  $allowedAlias=if($Row.mutation -eq 2){0}else{$Row.alias}
  if (-not (Test-LNValues $v $Row.start $Row.count)) {return 'values'}
  if ($v.capacity -gt $Row.count -or $v.bytes -gt (24+8*$Row.count)) {return 'capacity'}
  $externalExpected=if($Row.elementAlias -eq 1){0}else{-1}
  if ($Snapshot.roots[0].present -ne 0 -or $v.old -ne 0 -or $v.rc -ne 1 -or
      $Snapshot.roots[1].present -ne $allowedAlias -or $Snapshot.oldReachable -ne $allowedAlias -or
      $Snapshot.externalElement -ne $externalExpected) {return 'ownership'}
  if ($allowedAlias -eq 1 -and ($Snapshot.roots[1].old -ne 1 -or $Snapshot.roots[1].rc -ne 1 -or
      -not (Test-LNValues $Snapshot.roots[1] 0 $Row.n))) {return 'ownership'}
  if (-not (Test-LNReferences $Snapshot $Row.n $Row.start $Row.count $allowedAlias $Row.elementAlias)) {return 'references'}
  return 'none'
}
function Assert-LNSnapshot([object]$Snapshot,[object]$Row) {
  Assert-LNProperties $Snapshot @('phase','roots','destroyed','elementRC','liveElements',
    'elementReferences','uniqueArrays','containerBytes','oldReachable','externalElement') 'snapshot'
  if (@($Snapshot.roots).Count -ne 3 -or @($Snapshot.destroyed).Count -ne 6 -or
      @($Snapshot.elementRC).Count -ne 6) {throw 'MEASUREMENT: snapshot dimensions differ'}
  $references=@(0,0,0,0,0,0)
  $arrays=0; $bytes=0; $oldSeen=$false; $oldRoots=@($Snapshot.roots|Where-Object {$_.present -eq 1 -and $_.old -eq 1})
  foreach($v in $Snapshot.roots) {
    Assert-LNProperties $v @('present','old','rc','size','capacity','bytes','values','ids') 'root'
    if ($v.present -notin @(0,1) -or $v.old -notin @(0,1)) {throw 'MEASUREMENT: non-boolean root flag'}
    if (@($v.values).Count -ne $v.size -or @($v.ids).Count -ne $v.size) {throw 'MEASUREMENT: root size mismatch'}
    if ($v.present -eq 0) {
      if ($v.old -ne 0 -or $v.rc -ne 0 -or $v.size -ne 0 -or $v.capacity -ne 0 -or $v.bytes -ne 0) {throw 'MEASUREMENT: absent root retains data'}
      continue
    }
    if ($v.size -lt 0 -or $v.size -gt 6 -or $v.capacity -lt $v.size -or $v.bytes -ne (24+8*$v.capacity)) {
      throw 'MEASUREMENT: live size/capacity/requested-byte relation differs'
    }
    $expectedRootRC=if($v.old -eq 1){$oldRoots.Count}else{1}
    if ($v.rc -ne $expectedRootRC) {throw 'MEASUREMENT: root alias reference count differs'}
    if ($v.old -eq 1 -and $oldSeen) {
      Assert-LNEqual $v $oldRoots[0] 'duplicate aliases observe identical live array'
      continue
    }
    if ($v.old -eq 1) {$oldSeen=$true}
    $arrays++; $bytes+=$v.bytes
    for($i=0;$i -lt $v.size;$i++) {
      $id=$v.ids[$i]
      if ($id -lt 0 -or $id -ge $Row.n -or $v.values[$i] -ne $taskSpecification[$id]) {throw 'MEASUREMENT: element ID/value differs from independent input'}
      $references[$id]++
    }
  }
  if ($Snapshot.externalElement -notin @(-1,0)) {throw 'MEASUREMENT: unexpected external element owner'}
  if ($Snapshot.externalElement -eq 0) {$references[0]++}
  $live=0; $referenceSum=0
  for($i=0;$i -lt 6;$i++) {
    if ($references[$i] -gt 0) {$live++}
    $referenceSum+=$references[$i]
    if ($Snapshot.elementRC[$i] -ne $references[$i] -or
        $Snapshot.destroyed[$i] -ne [int]($i -lt $Row.n -and $references[$i] -eq 0)) {
      throw 'MEASUREMENT: reachability/destructor/reference accounting differs'
    }
  }
  if ($Snapshot.liveElements -ne $live -or $Snapshot.elementReferences -ne $referenceSum -or
      $Snapshot.uniqueArrays -ne $arrays -or $Snapshot.containerBytes -ne $bytes -or
      $Snapshot.oldReachable -ne [int]$oldSeen) {throw 'MEASUREMENT: derived summary differs'}
}
function Assert-LNMeasurement([object]$Row,[object]$Observation) {
  Assert-LNProperties $Observation @('schema','case','n','start','count','operation','alias','elementAlias','failStage','mutation','expectedValues',
    'snapshots','verdict','failure','cleanupComplete') 'observation'
  if ($Observation.schema -ne 1 -or $Observation.case -cne $Row.id -or $Observation.n -ne $Row.n -or
      $Observation.start -ne $Row.start -or $Observation.count -ne $Row.count -or $Observation.operation -ne $Row.operation -or
      $Observation.alias -ne $Row.alias -or $Observation.elementAlias -ne $Row.elementAlias -or
      $Observation.failStage -ne $Row.failStage -or $Observation.mutation -ne $Row.mutation) {
    throw 'MEASUREMENT: case input mapping differs'
  }
  $expectedValues=@(for($i=0;$i -lt $Row.count;$i++) {$taskSpecification[$Row.start+$i]})
  Assert-LNEqual @($Observation.expectedValues) $expectedValues 'independent expected values'
  $phases=@('before')
  if ($Row.operation -ge 2 -and $Row.mutation -ne 1) {
    if ($Row.failStage -ne 1) {$phases+=@('allocated')}
    if ($Row.failStage -notin @(1,2,3)) {$phases+=@('copied')}
    if ($Row.failStage -gt 0) {$phases+=@('failure-before-cleanup')}
  }
  $phases+=@('handoff','restored')
  Assert-LNEqual @($Observation.snapshots | ForEach-Object {$_.phase}) $phases 'ordered operational phases'
  foreach($snapshot in $Observation.snapshots) {Assert-LNSnapshot $snapshot $Row}
  # Stage names alone cannot establish a partial copy or a consumed source.
  # Check actual live roots and initialized slots at each intermediate boundary.
  foreach($snapshot in @($Observation.snapshots|Where-Object {$_.phase -in @('allocated','copied','failure-before-cleanup')})) {
    $sourcePresent=if($snapshot.phase -ceq 'failure-before-cleanup' -and $Row.failStage -eq 5){0}else{1}
    $outPresent=if($snapshot.phase -ceq 'failure-before-cleanup' -and $Row.failStage -eq 1){0}else{1}
    $copied=if($snapshot.phase -ceq 'allocated' -or $Row.failStage -in @(1,2)){0}
      elseif($snapshot.phase -ceq 'failure-before-cleanup' -and $Row.failStage -eq 3){2}else{$Row.count}
    if ($snapshot.roots[0].present -ne $sourcePresent -or $snapshot.roots[1].present -ne $Row.alias -or
        $snapshot.roots[2].present -ne $outPresent) {throw 'MEASUREMENT: intermediate stage ownership differs'}
    if ($sourcePresent -eq 1 -and ($snapshot.roots[0].old -ne 1 -or
        -not (Test-LNValues $snapshot.roots[0] 0 $Row.n))) {throw 'MEASUREMENT: intermediate source differs'}
    if ($outPresent -eq 1) {
      $v=$snapshot.roots[2]
      if ($v.old -ne 0 -or $v.size -ne $copied -or $v.capacity -ne $Row.count) {throw 'MEASUREMENT: intermediate initialized-copy extent differs'}
      for($i=0;$i -lt $copied;$i++) {
        $position=if($Row.mutation -eq 4 -and $i -eq 0){0}else{$Row.start+$i}
        if ($v.ids[$i] -ne $position -or $v.values[$i] -ne $taskSpecification[$position]) {throw 'MEASUREMENT: intermediate copied source position differs'}
      }
    }
  }
  $before=$Observation.snapshots[0]
  if (-not (Test-LNValues $before.roots[0] 0 $Row.n) -or $before.roots[0].capacity -ne 32 -or
      $before.roots[0].old -ne 1 -or $before.roots[1].present -ne $Row.alias -or $before.roots[2].present -ne 0) {
    throw 'MEASUREMENT: initial input construction differs'
  }
  $handoff=@($Observation.snapshots|Where-Object {$_.phase -ceq 'handoff'})[0]
  $measuredFailure=Get-LNMeasuredFailure $Row $handoff
  if ($measuredFailure -cne $Row.failure -or $Observation.failure -cne $measuredFailure) {throw 'MEASUREMENT: observed predicate failure differs'}
  $measuredVerdict=if($measuredFailure -ceq 'none'){'ACCEPT'}else{'REJECT'}
  if ($Observation.verdict -cne $measuredVerdict) {throw 'MEASUREMENT: verdict label contradicts projections'}
  $restored=$Observation.snapshots[-1]
  if ($restored.uniqueArrays -ne 0 -or $restored.liveElements -ne 0 -or $restored.containerBytes -ne 0 -or
      $restored.elementReferences -ne 0 -or $restored.externalElement -ne -1 -or
      $Observation.cleanupComplete -isnot [bool] -or -not $Observation.cleanupComplete) {throw 'MEASUREMENT: final restoration incomplete'}
}

function Invoke-LNSelfTests([object]$Registry,[string]$Binary,[hashtable]$Environment) {
  # These enter the actual script command boundary; none calls only the selector
  # helper. -List is the shape-only route and cannot start a compiler or probe.
  $selectorTests=@(
    @{id='selector-omitted';bound=$false;value='';error='';ids=$taskExpectedIds},
    @{id='selector-focused';bound=$true;value='pop-unique';error='';ids=@('pop-unique')},
    @{id='selector-reordered';bound=$true;value='shrink-unique,pop-unique';error='';ids=@('pop-unique','shrink-unique')},
    @{id='selector-empty';bound=$true;value='';error='SELECTOR: explicit empty selector'},
    @{id='selector-whitespace';bound=$true;value='  ';error='SELECTOR: explicit empty selector'},
    @{id='selector-unknown';bound=$true;value='unregistered';error='SELECTOR: unknown ID'},
    @{id='selector-zero';bound=$true;value='0';error='SELECTOR: unknown ID'},
    @{id='selector-case';bound=$true;value='POP-UNIQUE';error='SELECTOR: unknown ID'},
    @{id='selector-duplicate';bound=$true;value='pop-unique,pop-unique';error='SELECTOR: duplicate ID'},
    @{id='selector-missing';bound=$true;value='pop-unique,';error='SELECTOR: missing ID'}
  )
  foreach($test in $selectorTests) {
    $invoke="& '"+$taskScript.Replace("'","''")+"' -List"
    if ($test.bound) {$invoke+=" -Cases '"+$test.value.Replace("'","''")+"'"}
    $fixture=Join-Path $taskRunRoot ($test.id+'.ps1')
    [IO.File]::WriteAllText($fixture,($invoke+"`nexit `$LASTEXITCODE`n"),$taskEncoding)
    $null=Get-LNPin $fixture
    $stage=Invoke-LNStage $test.id $taskShell @('-NoLogo','-NoProfile','-ExecutionPolicy','Bypass','-File',$fixture) 30
    if ($test.error -ceq '') {
      Assert-LNProcess $stage 0; Assert-LNNoStderr $stage
      Assert-LNEqual @(Read-LNOneJson $stage.Stdout $test.id) @($test.ids) $test.id
    } else {
      Assert-LNProcess $stage 1
      if ($stage.Stdout -cne '' -or $stage.Stderr -cne ($test.error+"`r`n")) {throw ('SELFTEST: '+$test.id+' diagnostic surface differs')}
    }
    $taskChecks.Add(@{id=$test.id;outcome='matched';surface=$test.error})
  }
  $registryTests=@('missing','duplicate','unknown','reordered','mapping','unknown-key','missing-key')
  foreach($kind in $registryTests) {
    $mutant=$Registry | ConvertTo-Json -Depth 15 | ConvertFrom-Json
    $expected='REGISTRY: ordered IDs differ'
    switch($kind) {
      'missing' {$mutant.cases=@($mutant.cases|Select-Object -Skip 1);$expected='REGISTRY: cardinality differs'}
      'duplicate' {$mutant.cases[1]=$mutant.cases[0];$expected='REGISTRY: duplicate ID'}
      'unknown' {$mutant.cases[0].id='unregistered'}
      'reordered' {$tmp=$mutant.cases[0];$mutant.cases[0]=$mutant.cases[1];$mutant.cases[1]=$tmp}
      'mapping' {$mutant.cases[0].operation=2;$expected='REGISTRY: input mapping differs'}
      'unknown-key' {$mutant.cases[0]|Add-Member -NotePropertyName extra -NotePropertyValue 1;$expected='REGISTRY: property set differs'}
      'missing-key' {$mutant.cases[0].PSObject.Properties.Remove('operation');$expected='REGISTRY: property set differs'}
    }
    $mutantPath=Join-Path $taskRunRoot ('registry-'+$kind+'.json')
    Write-LNJson $mutantPath $mutant
    $null=Get-LNPin $mutantPath
    $stage=Invoke-LNStage ('registry-'+$kind) $taskShell @('-NoLogo','-NoProfile','-ExecutionPolicy','Bypass','-File',
      $taskScript,'-List','-RegistryPath',$mutantPath) 30
    Assert-LNProcess $stage 1
    if ($stage.Stdout -cne '' -or $stage.Stderr -cne ($expected+"`r`n")) {throw ('SELFTEST: registry-'+$kind+' diagnostic surface differs')}
    $taskChecks.Add(@{id=('registry-'+$kind);outcome='expected-reject';surface=$expected})
  }
  $nativeSelectors=@(
    @{id='native-missing-command';arguments=@();error='SELECTOR: invalid invocation'},
    @{id='native-missing-id';arguments=@('--case');error='SELECTOR: invalid invocation'},
    @{id='native-empty';arguments=@('--case','');error='SELECTOR: invalid invocation'},
    @{id='native-whitespace';arguments=@('--case',' ');error='SELECTOR: unknown case'},
    @{id='native-unknown';arguments=@('--case','unregistered');error='SELECTOR: unknown case'},
    @{id='native-duplicate';arguments=@('--case','pop-unique','--case','pop-unique');error='SELECTOR: invalid invocation'}
  )
  foreach($test in $nativeSelectors) {
    $stage=Invoke-LNStage $test.id $Binary $test.arguments 30 $Environment
    Assert-LNProcess $stage 2
    if ($stage.Stdout -cne '' -or $stage.Stderr -cne ($test.error+"`r`n")) {throw ('SELFTEST: '+$test.id+' diagnostic surface differs')}
    $taskChecks.Add(@{id=$test.id;outcome='expected-reject';surface=$test.error})
  }
  # Fresh native operations provide both predicate controls; copied fixtures are
  # only parser counterfactuals and are identified separately in the receipt.
  foreach($caseId in @('replace-prefix','negative-shrink')) {
    $row=@($Registry.cases|Where-Object {$_.id -ceq $caseId})[0]
    $stage=Invoke-LNStage ('verdict-control-'+$caseId) $Binary @('--case',$caseId) 30 $Environment
    Assert-LNProcess $stage $row.expectedExit; Assert-LNNoStderr $stage
    $observed=Read-LNOneJson $stage.Stdout $caseId
    Assert-LNMeasurement $row $observed
    $taskChecks.Add(@{id=('verdict-control-'+$caseId);outcome='measured-control';surface=$row.failure})
    $extra=[pscustomobject]@{Record=$stage.Record;Stdout=$stage.Stdout;Stderr="unexpected warning`n"}
    Assert-LNRejected {Assert-LNNoStderr $extra} 'DIAGNOSTIC:' ('mixed-stderr-'+$caseId)
    Assert-LNRejected {Read-LNOneJson ($stage.Stdout+"unexpected warning`n") $caseId} 'DIAGNOSTIC:' ('mixed-stdout-'+$caseId)
    $bad=$observed|ConvertTo-Json -Depth 30|ConvertFrom-Json
    $bad.verdict=if($observed.verdict -ceq 'ACCEPT'){'REJECT'}else{'ACCEPT'}
    Assert-LNRejected {Assert-LNMeasurement $row $bad} 'MEASUREMENT:' ('false-label-'+$caseId)
    $bad=$observed|ConvertTo-Json -Depth 30|ConvertFrom-Json
    $handoff=@($bad.snapshots|Where-Object {$_.phase -ceq 'handoff'})[0]
    $handoff.containerBytes++
    Assert-LNRejected {Assert-LNMeasurement $row $bad} 'MEASUREMENT:' ('false-summary-'+$caseId)
  }
  foreach($pair in @(@('fail-after-alloc','fail-mid-copy'),@('fail-handoff','fail-after-consume'))) {
    $row=@($Registry.cases|Where-Object {$_.id -ceq $pair[0]})[0]
    $challenged=@($Registry.cases|Where-Object {$_.id -ceq $pair[1]})[0]
    $stage=Invoke-LNStage ('stage-control-'+$row.id) $Binary @('--case',$row.id) 30 $Environment
    Assert-LNProcess $stage 0; Assert-LNNoStderr $stage
    $observed=Read-LNOneJson $stage.Stdout $row.id
    Assert-LNMeasurement $row $observed
    # Re-label a real earlier operational boundary as the later stage while
    # preserving internally consistent measured roots, counts and destructors.
    $bad=$observed|ConvertTo-Json -Depth 30|ConvertFrom-Json
    $bad.case=$challenged.id; $bad.failStage=$challenged.failStage
    Assert-LNRejected {Assert-LNMeasurement $challenged $bad} 'MEASUREMENT: intermediate' ('omitted-stage-'+$challenged.id)
    $taskChecks.Add(@{id=('stage-control-'+$row.id);outcome='actual-boundary-accepts';challenged=$challenged.id})
  }
  # A real process writes raw bytes and exits quickly. The final stream-drain
  # check must reject overflow even if a polling iteration never observes it.
  $overflowFixture=Join-Path $taskRunRoot 'fast-overflow.ps1'
  [IO.File]::WriteAllText($overflowFixture,@'
$bytes=New-Object byte[] 9437184
$stream=[Console]::OpenStandardOutput()
$stream.Write($bytes,0,$bytes.Length)
$stream.Flush()
exit 0
'@,$taskEncoding)
  $null=Get-LNPin $overflowFixture
  $overflow=Invoke-LNStage 'fast-overflow' $taskShell @('-NoLogo','-NoProfile','-File',$overflowFixture) 30
  if (-not $overflow.Record.nativeOutputLimitExceeded -or $overflow.Record.launcher.ExitCode -ne 125 -or
      $overflow.Record.launcher.TimedOut -or $overflow.Record.stdout.bytes -le 8388608) {throw 'SELFTEST: quick-exit overflow did not reject'}
  Assert-LNRejected {Assert-LNProcess $overflow 0} 'PROCESS:' 'fast-overflow-verdict'
  $taskChecks.Add(@{id='fast-overflow';outcome='expected-reject';bytes=$overflow.Record.stdout.bytes;
    actualChildExit=if($null -ne $overflow.Record.child){$overflow.Record.child.exitCode}else{$null}})

  $grandchildPidPath=Join-Path $taskRunRoot 'sleeper-grandchild.pid'
  $sleeperFixture=Join-Path $taskRunRoot 'sleeper-root.ps1'
  $sleeperText="`$p=Start-Process -FilePath '"+$taskShell.Replace("'","''")+"' -ArgumentList @('-NoLogo','-NoProfile','-Command','Start-Sleep -Seconds 120') -WindowStyle Hidden -PassThru`n"+
    "[IO.File]::WriteAllText('"+$grandchildPidPath.Replace("'","''")+"',[string]`$p.Id)`n"+
    "[Console]::WriteLine('owned descendant started')`nStart-Sleep -Seconds 120`n"
  [IO.File]::WriteAllText($sleeperFixture,$sleeperText,$taskEncoding)
  $null=Get-LNPin $sleeperFixture
  # Normal shell/probe startup measured below 3s; 8s supplies substantial margin
  # while keeping this timeout control intentionally far below its 120s sleep.
  $sleeper=Invoke-LNStage 'owned-descendant-timeout' $taskShell @('-NoLogo','-NoProfile','-File',$sleeperFixture) 8
  if ($null -eq $sleeper.Record.launcher -or -not $sleeper.Record.launcher.TimedOut -or
      $sleeper.Record.launcherError -or -not (Test-Path -LiteralPath $grandchildPidPath)) {
    throw 'SELFTEST: UNCOVERED owned descendant timeout (required live descendant not established)'
  }
  $grandchildId=[int][IO.File]::ReadAllText($grandchildPidPath)
  foreach($ownedId in @($sleeper.Record.nativePid,$grandchildId)) {
    if ($null -eq $ownedId -or $ownedId -le 0 -or
        $sleeper.Record.launcher.TerminatedIds -notcontains $ownedId -or
        $null -ne (Get-Process -Id $ownedId -ErrorAction SilentlyContinue)) {
      throw 'SELFTEST: owned root/descendant termination barrier not established'
    }
  }
  if ($sleeper.Stderr -cne '' -or $sleeper.Stdout -cne "owned descendant started`r`n") {throw 'SELFTEST: sleeper output preservation differs'}
  Assert-LNRejected {Assert-LNProcess $sleeper 0} 'PROCESS:' 'timeout-no-success'
  $taskChecks.Add(@{id='owned-descendant-timeout';outcome='expected-timeout-root-and-descendant-absent';
    nativeRoot=$sleeper.Record.nativePid;grandchild=$grandchildId;actualExitAvailable=($null -ne $sleeper.Record.child)})
}

try {
  $registry = Read-LNRegistry $RegistryPath
  $taskSelected = @(Resolve-LNSelection $registry $taskSelectedBound $Cases)
  if ($List) {
    if ($SelfTest) { throw 'SELECTOR: List and SelfTest cannot be combined' }
    Write-Output (ConvertTo-Json -InputObject @($taskSelected | ForEach-Object {$_.id}) -Compress)
    exit 0
  }
  if ([Environment]::OSVersion.Platform -ne [PlatformID]::Win32NT) {
    throw 'PLATFORM: UNCOVERED; this runner requires Windows job-object ownership and the pinned Windows runtime'
  }
  $taskRunRoot = Join-Path $taskRoot ('.lake/lifecycle-native-p0/runs/' + [Guid]::NewGuid().ToString('N'))
  [void](New-Item -ItemType Directory -Force -Path $taskRunRoot)
  . (Join-Path $PSScriptRoot 'owned_process_tree.ps1')
  . (Join-Path $PSScriptRoot 'packed_native_lifecycle_integrity_check.ps1')
  $taskIntegrityState.temp=Join-Path $taskRunRoot 'integrity-git'
  $taskIntegrityState.baseline=Get-LNTreeSnapshot $taskRoot $taskIntegrityState.temp
  Write-LNJson (Join-Path $taskRunRoot 'TREE_BASELINE.json') $taskIntegrityState.baseline
  $null=Get-LNPin (Join-Path $taskRunRoot 'TREE_BASELINE.json')
  [IO.File]::WriteAllText((Join-Path $taskRunRoot 'stage-child.ps1'),$taskChildScript,$taskEncoding)
  $null=Get-LNPin (Join-Path $taskRunRoot 'stage-child.ps1')
  $sourcePaths = @($taskScript,[IO.Path]::GetFullPath($RegistryPath),
    (Join-Path $taskRoot 'native/packed-rmq/tests/lifecycle_storage_probe.c'),
    (Join-Path $PSScriptRoot 'packed_native_lifecycle_integrity_check.ps1'),
    (Join-Path $taskRoot 'scripts/owned_process_tree.ps1'),(Join-Path $taskRoot 'lean-toolchain'))
  $taskSources = @($sourcePaths | ForEach-Object {Get-LNPin $_})
  $LeanRoot = [IO.Path]::GetFullPath($LeanRoot)
  foreach($override in @('LEAN_CC','LEAN_SYSROOT','CPATH','C_INCLUDE_PATH','CPLUS_INCLUDE_PATH','LIBRARY_PATH','COMPILER_PATH','GCC_EXEC_PREFIX')) {
    if (-not [string]::IsNullOrEmpty([Environment]::GetEnvironmentVariable($override,'Process'))) {
      throw ('IDENTITY: unrecorded compiler/runtime override '+$override)
    }
  }
  if ([IO.File]::ReadAllText((Join-Path $taskRoot 'lean-toolchain')).Trim() -cne 'leanprover/lean4:v4.22.0') {
    throw 'IDENTITY: repository Lean pin differs'
  }
  $toolPaths = @('bin/lean.exe','bin/leanc.exe','bin/clang.exe','bin/ld.lld.exe',
    'bin/libInit_shared.dll','bin/libleanshared.dll','bin/libleanshared_1.dll',
    'include/lean/lean.h','src/lean/Init/Data/Array/Basic.lean','lib/lean/libleanrt.a')
  $taskIdentity = [ordered]@{leanRoot=$LeanRoot; platform=[Environment]::OSVersion.VersionString;
    powershell=$PSVersionTable.PSVersion.ToString(); shell=(Get-LNPin $taskShell);
    files=@($toolPaths | ForEach-Object {Get-LNPin (Join-Path $LeanRoot $_)})}
  $taskIdentity.dependencyClosure=Get-LNDependencyClosure `
    @('lean.exe','leanc.exe','clang.exe','ld.lld.exe' | ForEach-Object {Join-Path $LeanRoot ('bin/'+$_)}) (Join-Path $LeanRoot 'bin')
  $taskIdentity.localDependencies=@($taskIdentity.dependencyClosure.nodes | ForEach-Object {Get-LNPin $_.path})
  Assert-LNDependencyCoverage $taskIdentity.dependencyClosure $taskIdentity.localDependencies
  $CHeaderRoot=[IO.Path]::GetFullPath($CHeaderRoot)
  $CCompilerHeaderRoot=[IO.Path]::GetFullPath($CCompilerHeaderRoot)
  $taskIdentity.cHeaderRoot=$CHeaderRoot
  $taskIdentity.compilerHeader=Get-LNPin (Join-Path $CCompilerHeaderRoot 'mm_malloc.h')
  $fallbackHeaders=Join-Path $taskRunRoot 'compiler-header-fallback'
  [void](New-Item -ItemType Directory -Path $fallbackHeaders)
  Copy-Item -LiteralPath $taskIdentity.compilerHeader.path -Destination (Join-Path $fallbackHeaders 'mm_malloc.h')
  $null=Get-LNPin (Join-Path $fallbackHeaders 'mm_malloc.h')
  $taskIdentity.cHeaders=@('stdio.h','stdlib.h','string.h','_mingw.h','_mingw_mac.h','_mingw_secapi.h','corecrt.h') |
    ForEach-Object {Get-LNPin (Join-Path $CHeaderRoot $_)}
  $nativeEnvironment = @{PATH=((Join-Path $LeanRoot 'bin')+';'+$env:PATH)}
  $leanVersion = Invoke-LNStage 'lean-version' (Join-Path $LeanRoot 'bin/lean.exe') @('--version') 30 $nativeEnvironment
  Assert-LNProcess $leanVersion 0
  Assert-LNNoStderr $leanVersion
  if ($leanVersion.Stdout -notmatch '\ALean \(version 4\.22\.0, [^\r\n]+\)\r?\n\z') { throw 'IDENTITY: Lean version output differs' }
  $compilerVersion = Invoke-LNStage 'clang-version' (Join-Path $LeanRoot 'bin/clang.exe') @('--version') 30 $nativeEnvironment
  Assert-LNProcess $compilerVersion 0
  Assert-LNNoStderr $compilerVersion
  $expectedClang='\Aclang version 19\.1\.2\r?\nTarget: x86_64-w64-windows-gnu\r?\nThread model: posix\r?\nInstalledDir: '+
    [regex]::Escape(($LeanRoot.Replace('\','/')+'/bin'))+'\r?\n\z'
  if ($compilerVersion.Stdout -cnotmatch $expectedClang) {throw 'IDENTITY: compiler version output differs or includes mixed diagnostics'}
  $taskIdentity.leanVersion = $leanVersion.Stdout
  $taskIdentity.compilerVersion = $compilerVersion.Stdout
  $binary = Join-Path $taskRunRoot 'lifecycle_storage_probe.exe'
  $linkMap=Join-Path $taskRunRoot 'link.map'
  # Pin installed link inputs before compilation and check them again at exit.
  # This roster is a conservative superset; the map identifies consumed members.
  $taskIdentity.linkerInputs=@(Get-ChildItem -LiteralPath (Join-Path $LeanRoot 'lib') -Recurse -File |
    Where-Object {$_.Extension -in @('.a','.o')} | Sort-Object FullName | ForEach-Object {Get-LNPin $_.FullName})
  try {
    $compile = Invoke-LNStage 'compile' (Join-Path $LeanRoot 'bin/leanc.exe') `
    @('-O1','-std=c11','-Wall','-Wextra','-Werror','-H','-isystem',$CHeaderRoot,
      '-idirafter',$fallbackHeaders,'-D__USE_MINGW_ANSI_STDIO=0',
      (Join-Path $taskRoot 'native/packed-rmq/tests/lifecycle_storage_probe.c'),'-o',$binary,('-Wl,-Map,'+$linkMap)) `
      $CompilerDeadlineSeconds $nativeEnvironment
  } finally {
    # Available outputs survive stage decoding, diagnostics and timeout errors.
    foreach($p in @($linkMap,$binary)){$null=Get-LNAvailablePin $p}
  }
  Assert-LNProcess $compile 0
  if ($compile.Stdout.Length -ne 0) { throw 'DIAGNOSTIC: unexpected compiler stdout' }
  $includedHeaders=@(foreach($line in @($compile.Stderr -split '\r?\n' | Where-Object {$_ -cne ''})) {
    if ($line -notmatch '^\.+ (.+)$') {throw 'DIAGNOSTIC: compiler output other than requested include inventory'}
    [IO.Path]::GetFullPath($Matches[1])
  })
  if ($includedHeaders.Count -lt 4) {throw 'IDENTITY: empty/incomplete compiler include inventory'}
  $taskIdentity.includedHeaders=@($includedHeaders | Sort-Object -Unique | ForEach-Object {Get-LNPin $_})
  $taskIdentity.linkMap=Get-LNPin $linkMap
  $taskIdentity.binary = Get-LNPin $binary
  $startup = Invoke-LNStage 'startup' $binary @('--startup') $ProbeDeadlineSeconds $nativeEnvironment
  Assert-LNProcess $startup 0
  Assert-LNNoStderr $startup
  $shape = Read-LNOneJson $startup.Stdout 'startup'
  Assert-LNProperties $shape @('schema','runtime','pointerBytes','arrayHeaderBytes') 'startup'
  if ($shape.schema -ne 1 -or $shape.runtime -cne '4.22.0' -or $shape.pointerBytes -ne 8 -or $shape.arrayHeaderBytes -ne 24) {
    throw 'MEASUREMENT: startup runtime/header shape differs'
  }
  $nativeList = Invoke-LNStage 'native-list' $binary @('--list') $ProbeDeadlineSeconds $nativeEnvironment
  Assert-LNProcess $nativeList 0
  Assert-LNNoStderr $nativeList
  Assert-LNEqual @(Read-LNOneJson $nativeList.Stdout 'native-list') $taskExpectedIds 'native ordered registry'
  $fatal=Invoke-LNStage 'fatal-runtime-handler' $binary @('--fatal-oom') $ProbeDeadlineSeconds $nativeEnvironment
  Assert-LNProcess $fatal 1
  if ($fatal.Stdout -cne '' -or $fatal.Stderr -cne "INTERNAL PANIC: out of memory`n") {
    throw 'DIAGNOSTIC: fatal runtime handler outcome differs or includes mixed diagnostics'
  }
  $taskChecks.Add(@{id='fatal-runtime-handler';outcome='fatal-process-observed';actualExit=1;
    cleanupClaim=$false;scope='Direct fatal-handler invocation; neither actual exhaustion nor recoverable allocator failure'})
  foreach ($row in $taskSelected) {
    $stage = Invoke-LNStage $row.id $binary @('--case',$row.id) $ProbeDeadlineSeconds $nativeEnvironment
    Assert-LNProcess $stage $row.expectedExit
    Assert-LNNoStderr $stage
    $observation = Read-LNOneJson $stage.Stdout $row.id
    Assert-LNMeasurement $row $observation
    $taskChecks.Add(@{id=$row.id;outcome='matched';expectedExit=$row.expectedExit;failure=$row.failure})
  }
  if ($SelfTest) { Invoke-LNSelfTests $registry $binary $nativeEnvironment }
  $taskSuccess = $true
} catch {
  $taskFailure = $_.Exception.Message
  [Console]::Error.WriteLine($taskFailure)
} finally {
  if ($null -ne $taskRunRoot) {
    try {$taskIntegrity=Complete-LNIntegrity $taskIntegrityState}
    catch {$taskIntegrity=@{attempted=$true;success=$false;errors=@('INTEGRITY: final verification unavailable: '+$_.Exception.Message)}}
    if(-not $taskIntegrity.success){
      $taskSuccess=$false
      foreach($message in $taskIntegrity.errors){[Console]::Error.WriteLine($message)}
    }
    $report = [ordered]@{schema=2;success=$taskSuccess;failure=$taskFailure;integrity=$taskIntegrity;
      capturedPins=@($taskIntegrityState.pins.ToArray());
      runRoot=$taskRunRoot;repositoryRoot=$taskRoot;base='bf31f983205175481fcb659caa4dfb70ef43e361';
      selected=@($taskSelected | ForEach-Object {$_.id});sources=$taskSources;identity=$taskIdentity;
      checks=@($taskChecks.ToArray());stages=@($taskStageResults.ToArray());
      platformLimit='Windows pinned Lean runtime measurements; POSIX and universal heap claims uncovered'}
    Write-LNJson (Join-Path $taskRunRoot 'SUMMARY.json') $report
    Write-Output ('LIFECYCLE-REPLAY evidence='+$taskRunRoot)
  }
}
if (-not $taskSuccess) { exit 1 }
Write-Output ('LIFECYCLE-REPLAY PASS cases='+$taskSelected.Count+' selfTest='+[bool]$SelfTest)
exit 0
