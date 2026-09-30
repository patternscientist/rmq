[CmdletBinding()]
param(
  [ValidateSet('Plan','Replay')][string]$Mode='Replay',
  [AllowNull()][AllowEmptyCollection()][AllowEmptyString()][string[]]$Case,
  [ValidateRange(1,120)][int]$DeadlineSeconds=30
)
$ErrorActionPreference='Stop'
$registry=@(
  @{id='design-accept-exact-counts';handler='design';mutation='identity';verdict='accept';diagnostic=''},
  @{id='design-extra-stdout';handler='design';mutation='append-unrelated-line';verdict='reject';diagnostic='STREAM: final-design stdout differs'},
  @{id='design-wrong-count';handler='design';mutation='change-code-count-1-to-2';verdict='reject';diagnostic='STREAM: final-design stdout differs'},
  @{id='claims-accept-source-bound-record';handler='claims-review';mutation='identity';verdict='accept';diagnostic=''},
  @{id='claims-duplicate-record';handler='claims-review';mutation='duplicate-record';verdict='reject';diagnostic='FINAL-CLAIMS: duplicate finding'},
  @{id='claims-forged-payload';handler='claims-review';mutation='replace-source-payload';verdict='reject';diagnostic='FINAL-CLAIMS: finding payload differs from source'},
  @{id='claims-extra-line';handler='claims-review';mutation='prepend-unrelated-line';verdict='reject';diagnostic='FINAL-CLAIMS: unrelated diagnostic at record 0'},
  @{id='claims-missing-final-newline';handler='claims-review';mutation='remove-final-host-newline';verdict='reject';diagnostic='FINAL-STREAM: missing final host newline'},
  @{id='claims-bom-output';handler='claims-review';mutation='prepend-utf8-bom';verdict='reject';diagnostic='FINAL-CLAIMS: unrelated diagnostic at record 0'},
  @{id='claims-extra-stderr';handler='claims-review';mutation='add-unrelated-stderr';verdict='reject';diagnostic='STREAM: final-claims stderr differs'},
  @{id='scope-reject-stale-real-receipt';handler='scope-stale';mutation='historical-changed-file-pin';verdict='reject';diagnostic='FINAL-STREAM: receipt input changed {fixtureRoot}/docs/internal/DESIGN_DECISIONS.md'},
  @{id='claims-zero-hit-grammar';handler='claims-zero';mutation='identity';verdict='accept';diagnostic=''},
  @{id='claims-source-bound-allowed-attribution';handler='claims-attribution';mutation='identity';verdict='accept';diagnostic=''},
  @{id='claims-attribution-wrong-line';handler='claims-attribution';mutation='increment-first-claim-line';verdict='reject';diagnostic='FINAL-CLAIMS: attribution line differs'},
  @{id='claims-ordinary-exit-mismatch';handler='claims-attribution';mutation='ordinary-exit-1';verdict='reject';diagnostic='STREAM: final-claims ordinary exit differs'}
)
$expectedIds=@('design-accept-exact-counts','design-extra-stdout','design-wrong-count',
  'claims-accept-source-bound-record','claims-duplicate-record','claims-forged-payload','claims-extra-line',
  'claims-missing-final-newline','claims-bom-output','claims-extra-stderr','scope-reject-stale-real-receipt',
  'claims-zero-hit-grammar','claims-source-bound-allowed-attribution','claims-attribution-wrong-line','claims-ordinary-exit-mismatch')
$byId=[Collections.Generic.Dictionary[string,object]]::new([StringComparer]::Ordinal)
foreach($row in $registry){if($byId.ContainsKey($row.id)){throw 'FINAL-STREAM-CONTROLS: duplicate registry ID'};$byId.Add($row.id,$row)}
if($registry.Count -ne 15 -or ($registry.id -join '|') -cne ($expectedIds -join '|')){throw 'FINAL-STREAM-CONTROLS: ordered registry differs'}
$mapping=@($registry|ForEach-Object{[ordered]@{id=$_.id;handler=$_.handler;mutation=$_.mutation;verdict=$_.verdict;diagnostic=$_.diagnostic}})
$mappingBytes=([Text.UTF8Encoding]::new($false,$true)).GetBytes(($mapping|ConvertTo-Json -Depth 5 -Compress))
$mappingSHA=[Security.Cryptography.SHA256]::Create()
try{$mappingHash=([BitConverter]::ToString($mappingSHA.ComputeHash($mappingBytes))).Replace('-','').ToLowerInvariant()}
finally{$mappingSHA.Dispose()}
if(-not [StringComparer]::Ordinal.Equals($mappingHash,'92a0cda169f378eba27a9884e5ed4a9e147845ef80ed0d528a02e95beb115813')){
  throw 'FINAL-STREAM-CONTROLS: frozen ID/handler/mutation/verdict/diagnostic mapping differs'
}
if($PSBoundParameters.ContainsKey('Case')){
  if($null -eq $Case -or $Case.Count -eq 0){throw 'FINAL-STREAM-CONTROLS: explicitly empty selector'}
  $selectedSet=[Collections.Generic.HashSet[string]]::new([StringComparer]::Ordinal)
  foreach($id in $Case){
    if([string]::IsNullOrWhiteSpace($id) -or -not $byId.ContainsKey($id) -or -not $selectedSet.Add($id)){
      throw ('FINAL-STREAM-CONTROLS: invalid/unknown/duplicate selector '+$id)
    }
  }
  $selected=@($registry|Where-Object{$selectedSet.Contains($_.id)})
}else{$selected=$registry}
# Complete selector validation precedes helper loading, output mutation or a child.
$root=[IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../../../..'))
. (Join-Path $root 'scripts/lifecycle_native_identity.ps1')
. (Join-Path $PSScriptRoot 'final_streams.ps1')
$utf8=[Text.UTF8Encoding]::new($false,$true);$eol=[Environment]::NewLine
if($Mode -ceq 'Plan'){
  [ordered]@{schema='lifecycle-native1-final-stream-controls-plan-v1';count=$registry.Count;orderedIds=$expectedIds;
    selectedIds=@($selected.id);mapping=$mapping;mappingSHA256=$mappingHash;
    boundary='Output-language/helper controls only. No production scope checker, Lean or native process is invoked.'}|ConvertTo-Json -Depth 8
  return
}
$run=Join-Path $root ('.lake/lifecycle-native1/final-stream-controls/'+[DateTime]::UtcNow.ToString('yyyyMMddTHHmmssfff')+'-'+[Guid]::NewGuid().ToString('N').Substring(0,8))
$scratch=Join-Path $run 'disposable';$fixtureRoot=Join-Path $scratch 'repository'
$pins=[Collections.Generic.List[object]]::new();$results=[Collections.Generic.List[object]]::new()
$report=[ordered]@{schema='lifecycle-native1-final-stream-controls-v1';success=$false;startedUtc=[DateTime]::UtcNow.ToString('o');
  boundary='Fresh owned PowerShell byte emitters exercise final_streams helper predicates. This is not actual production scope, claim, design or native execution.';
  orderedIds=$expectedIds;selectedIds=@($selected.id);mapping=$mapping;mappingSHA256=$mappingHash;
  deadlineSeconds=$DeadlineSeconds;deadlineRationale='Existing18 owned PowerShell selector callers averaged about5.1seconds each; reserve30seconds for each smaller byte emitter. No Lean/native work or heavy mutex.';
  expectedCount=$selected.Count;results=@();pins=@();failure=$null;integrity=$null;cleanup=$null;sourceFixture=$null;
  heavyMutexAcquired=$false;nativeInvocations=0;compilerInvocations=0;productionCheckerInvocations=0}
function Pin-FSC([string]$Path){$p=Get-LN1Pin $Path;$pins.Add($p);return $p}
function Write-FSCJson([string]$Path,$Value){[IO.File]::WriteAllText($Path,($Value|ConvertTo-Json -Depth 25),$utf8)}
function Copy-FSCFixture([string]$Relative){
  $source=Join-Path $root $Relative;$destination=Join-Path $fixtureRoot $Relative
  [void][IO.Directory]::CreateDirectory([IO.Path]::GetDirectoryName($destination))
  [IO.File]::Copy($source,$destination,$false)
  $original=Pin-FSC $source;$copy=Pin-FSC $destination
  if($original.bytes -ne $copy.bytes -or $original.sha256 -cne $copy.sha256){throw 'FINAL-STREAM-CONTROLS: fixture copy differs'}
}
function Remove-FSCScratch {
  $full=[IO.Path]::GetFullPath($scratch)
  $prefix=[IO.Path]::GetFullPath($run).TrimEnd('\','/')+[IO.Path]::DirectorySeparatorChar
  if(-not $full.StartsWith($prefix,[StringComparison]::OrdinalIgnoreCase) -or
      $full -cne [IO.Path]::GetFullPath((Join-Path $run 'disposable'))){throw 'FINAL-STREAM-CONTROLS: unsafe cleanup target'}
  if([IO.Directory]::Exists($full)){
    foreach($entry in @((Get-Item -LiteralPath $full))+@(Get-ChildItem -LiteralPath $full -Recurse -Force)){
      if($entry.Attributes -band [IO.FileAttributes]::ReparsePoint){throw 'FINAL-STREAM-CONTROLS: cleanup refuses reparse point'}
    }
    Remove-Item -LiteralPath $full -Recurse -Force
  }
  if([IO.Directory]::Exists($full)){throw 'FINAL-STREAM-CONTROLS: disposable fixture remains'}
}
try{
  [void][IO.Directory]::CreateDirectory($run)
  $shell=(Get-Process -Id $PID).Path
  foreach($path in @($PSCommandPath,$shell,(Join-Path $PSScriptRoot 'final_streams.ps1'),
      (Join-Path $PSScriptRoot 'final_stream_controls.scope_seed.json'))+@(@(
      'scripts/lifecycle_native_identity.ps1','scripts/owned_process_tree.ps1',
      'scripts/packed_native_lifecycle_stream_check.ps1','scripts/packed_native_lifecycle_storage_replay.ps1',
      'scripts/packed_native_lifecycle_integrity_check.ps1','scripts/design_decision_check.ps1',
      'scripts/claim_drift_scan.ps1','docs/internal/CLAIM_DRIFT_POLICY.json',
      'docs/internal/extensions/lifecycle-native1/scope_check.ps1','docs/internal/extensions/lifecycle-native1/BASE_IDENTITY.json',
      'native/packed-rmq/README.md','docs/FAMILY_SUMMARY.md','lean-toolchain')|ForEach-Object{Join-Path $root $_})){
    [void](Pin-FSC $path)
  }
  $policyPath=Join-Path $root 'docs/internal/CLAIM_DRIFT_POLICY.json'
  $policy=(Read-LNExactStream $policyPath)|ConvertFrom-Json -ErrorAction Stop
  $designPaths=@('RMQ/Core/WordRAM/Native/Lifecycle.lean','scripts/lifecycle_native_build.ps1',
    'docs/internal/DESIGN_DECISIONS.md','docs/internal/WORKFLOW_DESIGN_DECISIONS.md','docs/DIGESTION_LOG.md')
  $design='DESIGN-CHECK: checked 5 changed files (1 code, 1 workflow, 3 neutral)'+$eol
  $reviewPath='native/packed-rmq/README.md';$reviewTerm=@($policy.terms|Where-Object id -CEQ 'invalid-range-rejection')
  if($reviewTerm.Count -ne 1 -or $reviewTerm[0].strict){throw 'FINAL-STREAM-CONTROLS: review seed policy differs'}
  $reviewLines=(Read-LNExactStream (Join-Path $root $reviewPath)).Split([char]10)
  $reviewLine=0
  for($i=0;$i -lt $reviewLines.Count;$i++){if([regex]::IsMatch($reviewLines[$i],[string]$reviewTerm[0].pattern)){$reviewLine=$i+1;break}}
  if($reviewLine -eq 0){throw 'FINAL-STREAM-CONTROLS: missing source review seed'}
  $reviewBody=$reviewLines[$reviewLine-1].Trim()
  $reviewPrefix='CLAIM-DRIFT['+$reviewTerm[0].id+']['+$reviewTerm[0].status+'][review] '+$reviewPath+':'+$reviewLine+': '
  $review=$reviewPrefix+$reviewBody+$eol
  $summary='CLAIM-DRIFT: scan complete (1 hits, 0 strict failures)'+$eol
  $attribution=@($policy.requiredAttributions|Where-Object id -CEQ 'required-current-readword-only-theorem-attribution')
  if($attribution.Count -ne 1){throw 'FINAL-STREAM-CONTROLS: attribution seed policy differs'}
  $attribution=$attribution[0];$attributionPath='docs/FAMILY_SUMMARY.md'
  $content=Read-LNExactStream (Join-Path $root $attributionPath)
  $match=[regex]::Match($content,[string]$attribution.claimPattern)
  if(-not $match.Success -or -not [regex]::IsMatch($content,[string]$attribution.requiredPattern)){
    throw 'FINAL-STREAM-CONTROLS: required attribution seed is absent'
  }
  $attributionLine=1+[regex]::Matches($content.Substring(0,$match.Index),"`n").Count
  $attributionPrefix='CLAIM-DRIFT['+$attribution.id+']['+$attribution.status+'][allowed] '+$attributionPath+':'
  $attributionSuffix=': strong claim has its required theorem identity'+$eol
  $attributionText=$attributionPrefix+$attributionLine+$attributionSuffix
  if(@($selected|Where-Object handler -CEQ 'scope-stale').Count){
    foreach($relative in @('docs/internal/extensions/lifecycle-native1/BASE_IDENTITY.json',
        'docs/internal/extensions/lifecycle-native1/scope_check.ps1','docs/internal/DESIGN_DECISIONS.md')){Copy-FSCFixture $relative}
    $seed=(Read-LNExactStream (Join-Path $PSScriptRoot 'final_stream_controls.scope_seed.json'))|ConvertFrom-Json -ErrorAction Stop
    if($seed.schema -cne 'lifecycle-native1-final-stream-scope-seed-v1' -or
        $seed.change.path -cne 'docs/internal/DESIGN_DECISIONS.md'){throw 'FINAL-STREAM-CONTROLS: stale scope seed differs'}
    $current=Get-LN1Pin (Join-Path $fixtureRoot $seed.change.path)
    if($current.bytes -eq $seed.change.bytes -and $current.sha256 -ieq $seed.change.sha256){
      throw 'FINAL-STREAM-CONTROLS: historical scope pin no longer challenges current bytes'
    }
    $scopeDirectory=Join-Path $fixtureRoot '.lake/lifecycle-native1/scope/20260923T082034341'
    [void][IO.Directory]::CreateDirectory($scopeDirectory)
    $scopeReceipt=[ordered]@{schema='lifecycle-native1-scope-v1';success=$true;base=$seed.base;head=$seed.head;
      branch=$seed.branch;checkedBaseFiles=3844;changes=@($seed.change);newFiles=@();failure=$null;
      contract=$null;startupAmendment=$null;
      boundary='Reduced historical changed-file pin helper fixture; rejection must occur at the changed-file pin before later receipt fields.'}
    Write-FSCJson (Join-Path $scopeDirectory 'RESULT.json') $scopeReceipt
    Write-FSCJson (Join-Path $run 'scope-fixture.json') $scopeReceipt
    [void](Pin-FSC (Join-Path $scopeDirectory 'RESULT.json'));[void](Pin-FSC (Join-Path $run 'scope-fixture.json'))
    $report.sourceFixture=@{seedOrigin=$seed.origin;historicalPin=$seed.change;currentCopy=$current;root=$fixtureRoot;liveSourceWrites=0}
  }
  $emitter=Join-Path $run 'emit-bytes.ps1'
  $emitterText=@'
param([Parameter(Mandatory)][string]$Payload)
$ErrorActionPreference='Stop'
$data=([Text.UTF8Encoding]::new($false,$true)).GetString([IO.File]::ReadAllBytes($Payload))|ConvertFrom-Json -ErrorAction Stop
$out=[Convert]::FromBase64String([string]$data.stdoutBase64)
$err=[Convert]::FromBase64String([string]$data.stderrBase64)
$outStream=[Console]::OpenStandardOutput();$errStream=[Console]::OpenStandardError()
$outStream.Write($out,0,$out.Length);$outStream.Flush()
$errStream.Write($err,0,$err.Length);$errStream.Flush()
exit ([int]$data.exitCode)
'@
  [IO.File]::WriteAllText($emitter,$emitterText,$utf8);[void](Pin-FSC $emitter)
  foreach($row in $selected){
    $out='';$err='';$exitCode=0;$expectedDiagnostic=[string]$row.diagnostic
    switch -CaseSensitive ($row.handler){
      'design' {$out=$design}
      'claims-review' {$out=$review+$summary}
      'claims-zero' {$out='CLAIM-DRIFT: no sensitive terms found'+$eol+'CLAIM-DRIFT: scan complete (0 hits, 0 strict failures)'+$eol}
      'claims-attribution' {$out=$attributionText+$summary}
      'scope-stale' {$out='LIFECYCLE-SCOPE success=True receipt='+$scopeDirectory+$eol
        $expectedDiagnostic='FINAL-STREAM: receipt input changed '+(Join-Path $fixtureRoot 'docs/internal/DESIGN_DECISIONS.md')}
      default {throw 'FINAL-STREAM-CONTROLS: unknown handler'}
    }
    switch -CaseSensitive ($row.mutation){
      'identity' {}
      'append-unrelated-line' {$out+='unrelated'+$eol}
      'change-code-count-1-to-2' {$out=$out.Replace('1 code','2 code')}
      'duplicate-record' {$out=$review+$review+$summary}
      'replace-source-payload' {$out=$reviewPrefix+'unrelated diagnostic'+$eol+$summary}
      'prepend-unrelated-line' {$out='unrelated'+$eol+$out}
      'remove-final-host-newline' {$out=$out.Substring(0,$out.Length-$eol.Length)}
      'prepend-utf8-bom' {$out=[string][char]0xfeff+$out}
      'add-unrelated-stderr' {$err='unrelated'+$eol}
      'historical-changed-file-pin' {}
      'increment-first-claim-line' {$out=$attributionPrefix+($attributionLine+1)+$attributionSuffix+$summary}
      'ordinary-exit-1' {$exitCode=1}
      default {throw 'FINAL-STREAM-CONTROLS: unknown mutation'}
    }
    $caseRoot=Join-Path $run $row.id;[void][IO.Directory]::CreateDirectory($caseRoot)
    $payload=Join-Path $caseRoot 'payload.json'
    Write-FSCJson $payload @{stdoutBase64=[Convert]::ToBase64String($utf8.GetBytes($out));
      stderrBase64=[Convert]::ToBase64String($utf8.GetBytes($err));exitCode=$exitCode}
    $payloadPin=Pin-FSC $payload
    $result=[ordered]@{id=$row.id;handler=$row.handler;mutation=$row.mutation;expectedVerdict=$row.verdict;
      expectedDiagnostic=$expectedDiagnostic;payload=$payloadPin;capture=$null;verdict=$null;diagnostic=$null;value=$null;success=$false}
    $results.Add($result)
    $capture=Invoke-LNStreamCapture $root $shell @('-NoProfile','-File',$emitter,'-Payload',$payload) $root `
      (Join-Path $caseRoot 'capture') $DeadlineSeconds $row.id
    $result.capture=$capture
    foreach($pin in $capture.raw){$now=Pin-FSC $pin.path;if($now.bytes -ne $pin.bytes -or $now.sha256 -cne $pin.sha256){throw 'FINAL-STREAM-CONTROLS: raw capture pin changed'}}
    # A transport failure is never mistaken for the expected semantic rejection.
    Assert-LNOuterCapture $capture $out $err $exitCode ('emitter-'+$row.id)
    try{
      switch -CaseSensitive ($row.handler){
        'design' {$result.value=Assert-LNFinalDesign $capture $designPaths}
        'claims-review' {$result.value=Assert-LNFinalClaims $capture $root $policyPath @($reviewPath)}
        'claims-zero' {$result.value=Assert-LNFinalClaims $capture $root $policyPath @('lean-toolchain')}
        'claims-attribution' {$result.value=Assert-LNFinalClaims $capture $root $policyPath @($attributionPath)}
        'scope-stale' {$result.value=Assert-LNFinalScope $capture $fixtureRoot $seed.base $seed.head @($seed.change.path)}
      }
      $result.verdict='accept';$result.diagnostic=''
    }catch{$result.verdict='reject';$result.diagnostic=$_.Exception.Message}
    if($result.verdict -cne $row.verdict -or $result.diagnostic -cne $expectedDiagnostic){
      throw ('FINAL-STREAM-CONTROLS: verdict/diagnostic differs '+$row.id+' actual='+$result.diagnostic)
    }
    if($row.verdict -ceq 'accept'){
      $s=$result.value.summary
      if($null -eq $s){throw 'FINAL-STREAM-CONTROLS: expected-accept result absent'}
      switch -CaseSensitive ($row.handler){
        'design' {if($s.paths -ne 5 -or $s.code -ne 1 -or $s.workflow -ne 1 -or $s.neutral -ne 3){throw 'FINAL-STREAM-CONTROLS: accepted design summary differs'}}
        'claims-review' {if($s.hits -ne 1 -or $s.reviewRecords -ne 1 -or $s.attributionRecords -ne 0 -or $s.strictFailures -ne 0){throw 'FINAL-STREAM-CONTROLS: accepted review summary differs'}}
        'claims-zero' {if($s.hits -ne 0 -or $s.visibleRecords -ne 0 -or $s.strictFailures -ne 0){throw 'FINAL-STREAM-CONTROLS: accepted zero summary differs'}}
        'claims-attribution' {if($s.hits -ne 1 -or $s.reviewRecords -ne 0 -or $s.attributionRecords -ne 1 -or $s.strictFailures -ne 0){throw 'FINAL-STREAM-CONTROLS: accepted attribution summary differs'}}
      }
    }
    $result.success=$true
  }
  if($results.Count -ne $selected.Count -or ($results.id -join '|') -cne ($selected.id -join '|') -or
      @($results|Where-Object{-not $_.success}).Count){throw 'FINAL-STREAM-CONTROLS: incomplete or reordered execution'}
  $report.success=$true
}catch{$report.failure=$_.Exception.Message}
finally{
  $integrityErrors=[Collections.Generic.List[string]]::new()
  foreach($pin in $pins){try{
    $current=Get-LN1Pin $pin.path
    if($current.bytes -ne $pin.bytes -or $current.sha256 -cne $pin.sha256){throw ('changed pin '+$pin.path)}
  }catch{$integrityErrors.Add($_.Exception.Message)}}
  $report.integrity=@{success=($integrityErrors.Count -eq 0);checked=$pins.Count;errors=@($integrityErrors.ToArray())}
  $cleanupErrors=[Collections.Generic.List[string]]::new()
  try{Remove-FSCScratch}catch{$cleanupErrors.Add($_.Exception.Message)}
  $report.cleanup=@{success=($cleanupErrors.Count -eq 0);disposableAbsent=(-not [IO.Directory]::Exists($scratch));
    liveSourceWrites=0;environmentWrites=0;errors=@($cleanupErrors.ToArray())}
  $report.success=$report.success -and $report.integrity.success -and $report.cleanup.success
  $report.results=@($results.ToArray());$report.pins=@($pins.ToArray());$report.completedUtc=[DateTime]::UtcNow.ToString('o')
  if(-not [IO.Directory]::Exists($run)){[void][IO.Directory]::CreateDirectory($run)}
  Write-FSCJson (Join-Path $run 'RESULT.json') $report
}
Write-Output ('FINAL-STREAM-CONTROLS evidence='+$run)
if(-not $report.success){Write-Output ('FINAL-STREAM-CONTROLS FAIL '+$report.failure);exit 1}
Write-Output ('FINAL-STREAM-CONTROLS PASS count='+$results.Count)
