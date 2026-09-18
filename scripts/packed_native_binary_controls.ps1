param([AllowEmptyString()][string]$Case)
$ErrorActionPreference = 'Stop'
$controlRoot = Split-Path $PSScriptRoot -Parent
. (Join-Path $PSScriptRoot 'owned_process_tree.ps1')
$controlReplay = Join-Path $PSScriptRoot 'packed_native_binary_replay.ps1'
$controlRegistryPath = Join-Path $PSScriptRoot 'packed_native_binary_cases.json'
$controlProducer = Join-Path $PSScriptRoot 'packed_native_cases.py'
$controlPython = 'C:/Users/poin/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe'
$controlShell = (Get-Process -Id $PID).Path
$controlScratch = Join-Path $controlRoot '.lake/native1/binary-build/controls'
$controlLogs = Join-Path $controlRoot 'docs/internal/extensions/native1/binary-commands'
[void](New-Item -ItemType Directory -Force -Path $controlScratch,$controlLogs)
$controlRegistryBytes = [IO.File]::ReadAllBytes($controlRegistryPath)
$controlRegistryHash = (Get-FileHash -LiteralPath $controlRegistryPath).Hash
if ($controlRegistryHash -cne '2D38A1002C1E8A72DF5E164144EC4E8F5410511F2C585831AEFBBC0D1BD4C637') { throw 'binary controls baseline registry mismatch' }
$controlRegistry = Get-Content -LiteralPath $controlRegistryPath -Raw | ConvertFrom-Json
# Independent field representatives cover dispatch, every expected stream/exit,
# each image variant and each source mutation consumer. Minimal property spans
# make same-ID changes observable without unrelated reformatting.
$controlFields = [ordered]@{
  id=@('query-smoke','id'); kind=@('source-core-fuel','kind');
  operation=@('source-core-fuel','operation'); consumers=@('query-smoke','consumers');
  image=@('query-smoke','image'); arguments=@('query-smoke','arguments');
  expectedExit=@('query-smoke','expectedExit'); expectedStdout=@('query-smoke','expectedStdout');
  expectedStderr=@('reject-query-padding','expectedStderr'); deadlineSeconds=@('query-smoke','deadlineSeconds');
  coverage=@('query-smoke','coverage'); source=@('source-core-fuel','source');
  anchor=@('source-core-fuel','anchor'); replacement=@('source-core-fuel','replacement');
  proofLine=@('source-core-fuel','proofLine'); expectedDiagnostic=@('source-core-fuel','expectedDiagnostic');
  surface=@('source-core-fuel','surface'); append=@('stale-source-rejection','append');
  mutantExpectedExit=@('source-ffi-order','mutantExpectedExit');
  mutantExpectedStdout=@('source-ffi-order','mutantExpectedStdout');
  mutantExpectedStderr=@('source-ffi-order','mutantExpectedStderr');
  compileDeadlineSeconds=@('source-ffi-order','compileDeadlineSeconds');
  imageKind=@('query-smoke','image.kind'); imageWidth=@('query-smoke','image.width');
  imageInputLength=@('query-smoke','image.inputLength'); imageRegisters=@('query-smoke','image.registerCount');
  imageCode=@('query-smoke','image.code'); imageMemory=@('memory-identity-176','image.memory');
  imageFixture=@('pq1-n9-full','image.fixture'); imageSourceCommit=@('pq1-n9-full','image.sourceCommit');
  imageProgramHash=@('pq1-n9-full','image.programSha256'); imageFixtureHash=@('pq1-n9-full','image.fixtureSha256');
  imageExpectedHash=@('pq1-n9-full','image.expectedSha256'); imageBase=@('reject-image-magic','image.base');
  imageMutation=@('reject-image-magic','image.mutation'); imageByteCount=@('reject-file-cap','image.bytes');
  imageFixturePath=@('canonical-select-left','image.fixturePath');
  imageSourcePins=@('canonical-select-left','image.sourcePins');
  imageSourcePinPath=@('canonical-select-left','image.sourcePins.0.path');
  imageSourcePinHash=@('canonical-select-left','image.sourcePins.0.sha256');
  schema=@('','schema'); status=@('','status'); producerHash=@('','producerSha256');
  encoderHash=@('','encoderSha256'); cases=@('','cases')
}
$controlWitnessChallenges = [ordered]@{
  stage=@('canonical-select-left','canonical occurrence belongs to the wrong actual source stage');
  ordinal=@('canonical-cross-cell','canonical occurrence ordinal/transition mismatch');
  transition=@('canonical-cross-cell','canonical occurrence ordinal/transition mismatch');
  pc=@('canonical-cross-cell','canonical occurrence PC does not fetch the declared load');
  'load-register'=@('canonical-cross-cell','canonical occurrence PC does not fetch the declared load');
  'prestate-pc'=@('canonical-cross-cell','canonical occurrence prestate/address disagreement');
  'prestate-address'=@('canonical-cross-cell','canonical occurrence prestate/address disagreement');
  address=@('canonical-cross-cell','canonical occurrence differs from exact ordered expected read');
  reply=@('canonical-cross-cell','canonical occurrence differs from exact ordered expected read');
  memory=@('canonical-cross-cell','canonical occurrence reply differs from exact loaded memory');
  span=@('canonical-cross-cell','canonical logical span/physical embedding mismatch');
  'logical-reply'=@('canonical-cross-cell','canonical logical reply does not reconstruct from physical cells');
  crossing=@('canonical-cross-cell','canonical cross-cell witness does not cross two cells');
  'empty-physical'=@('canonical-cross-cell','empty canonical physical occurrence witness');
  'missing-second-cell'=@('canonical-cross-cell','canonical logical span physical count mismatch');
  oracle=@('canonical-cross-cell','independent leftmost RMQ witness answer mismatch');
  program=@('canonical-cross-cell','canonical/independent original program identity mismatch')
}
$controlIds = @('empty','whitespace','malformed','unknown',
  'source-kind-downgrade','source-pin-substitution','source-fixture-substitution','pin-fixture-substitution',
  'registry-empty-cases','registry-duplicate-case','registry-extra-top-field','registry-extra-case-field',
  'registry-duplicate-key','registry-format-change') +
  @($controlFields.Keys | ForEach-Object { 'delete-' + $_; 'change-' + $_ }) +
  @($controlWitnessChallenges.Keys | ForEach-Object { 'witness-' + $_ }) +
  @('source-manifest-missing','artifact-manifest-empty','toolchain-manifest-missing','generatedC-manifest-missing',
    'lean-root-manifest-mismatch','valid-smoke','omitted-full')
if ($controlIds.Count -ne 128 -or @($controlIds | Select-Object -Unique).Count -ne 128) {
  throw 'exact binary controls roster mismatch'
}
if ($PSBoundParameters.ContainsKey('Case')) {
  if ([string]::IsNullOrWhiteSpace($Case) -or $Case -cnotmatch '^[a-zA-Z0-9-]+$' -or
      $controlIds -cnotcontains $Case) { throw 'invalid exact binary controls selector' }
  $controlSelected = @($Case)
} else { $controlSelected = @($controlIds) }
$controlResults = [Collections.Generic.List[object]]::new()
$controlCommands = [Collections.Generic.List[object]]::new()
$controlStarted = [DateTime]::UtcNow.ToString('o')
$controlRunId = [DateTime]::UtcNow.ToString('yyyyMMddTHHmmssfff')
$controlSuccess = $false
$controlFailure = $null
$controlPythonIdentity = $null
function Invoke-BinaryControlOwned([string]$Stage,[string]$Exe,[string[]]$Arguments,[int]$Deadline) {
  $started = [DateTime]::UtcNow.ToString('o')
  $r = Invoke-RMQOwnedBoundedProcess -FilePath $Exe -Arguments $Arguments -WorkingDirectory $controlRoot `
    -Stage $Stage -DeadlineSeconds $Deadline -OutputLimitBytes 8388608 -TempRoot $controlScratch
  $r | Add-Member -NotePropertyName StartedUtc -NotePropertyValue $started
  $r | Add-Member -NotePropertyName CompletedUtc -NotePropertyValue ([DateTime]::UtcNow.ToString('o'))
  $r | Add-Member -NotePropertyName InvokedFilePath -NotePropertyValue $Exe
  $r | Add-Member -NotePropertyName InvokedArguments -NotePropertyValue @($Arguments)
  $controlCommands.Add($r)
  if ($r.TimedOut -or $r.OutputLimitExceeded) {
    $controlResults.Add(@{id=$Stage;pass=$false;incomplete=$true;process=$r})
    throw ('bounded binary control incomplete: ' + $Stage)
  }
  return $r
}
function Invoke-BinaryControlChild([string]$Id,[bool]$Bound,[AllowEmptyString()][string]$Selector,[int]$Deadline=120) {
  $arguments = @('-NoLogo','-NoProfile','-ExecutionPolicy','Bypass','-File',$controlReplay)
  if ($Bound) { $arguments += @('-Case',$Selector) }
  return Invoke-BinaryControlOwned $Id $controlShell $arguments $Deadline
}
function Assert-BinaryControlRejected([string]$Id,[AllowEmptyString()][string]$Selector,[string]$Surface) {
  $r = Invoke-BinaryControlChild $Id $true $Selector
  if ($r.ExitCode -eq 0 -or (($r.Output -join "`n") -notmatch [regex]::Escape($Surface)) -or
      @($r.StandardOutput | Where-Object { $_ -like 'NATIVE1-BINARY PASS *' }).Count -ne 0) {
    $controlResults.Add(@{id=$Id;pass=$false;surface=$Surface;process=$r})
    throw ('binary control missed exact rejection surface: ' + $Id)
  }
  return @{surface=$Surface;process=$r;selector=$Selector;selectorBound=$true}
}
function Get-BinaryControlGitState([string]$Path) {
  $state = @(& git diff --binary -- $Path)
  if ($LASTEXITCODE -ne 0) { throw 'binary control Git state read failed' }
  return ($state -join "`n")
}
function Invoke-BinaryRegistryMutation([string]$Id) {
  $saved = [IO.File]::ReadAllBytes($controlRegistryPath)
  $before = (Get-FileHash -LiteralPath $controlRegistryPath).Hash
  $state = Get-BinaryControlGitState 'scripts/packed_native_binary_cases.json'
  $details = $null
  try {
    $text = [Text.UTF8Encoding]::new($false,$true).GetString($saved)
    $parsed = $text | ConvertFrom-Json
    $mutation = $null
    if ($Id -clike 'delete-*' -or $Id -clike 'change-*' -or $Id -ceq 'source-kind-downgrade') {
      if ($Id -ceq 'source-kind-downgrade') { $action='change';$field=@('source-core-fuel','kind');$value='"source-pin"' }
      else {
        $action,$name = $Id.Split('-',2)
        $field = $controlFields[$name]
        $value = '"changed-semantic-value"'
      }
      $temporary = Join-Path $controlScratch ($Id + '-mutated.json')
      $arguments = @($controlProducer,'mutate-property','--registry',$controlRegistryPath,'--case',$field[0],
        '--field',$field[1],'--action',$action,'--value-json',$value,'--output',$temporary)
      $mutation = Invoke-BinaryControlOwned ($Id + '-prepare') $controlPython $arguments 30
      if ($mutation.ExitCode -ne 0 -or $mutation.StandardError.Count -ne 0) { throw 'minimal binary registry mutation failed' }
      $change = ($mutation.StandardOutput -join "`n") | ConvertFrom-Json
      if (-not $change.onlyIntendedSemanticChange -or $change.beforeSha256 -cne $before -or
          (Get-FileHash -LiteralPath $temporary).Hash -cne $change.afterSha256) { throw 'binary mutation span evidence mismatch' }
      [IO.File]::WriteAllBytes($controlRegistryPath,[IO.File]::ReadAllBytes($temporary))
    } elseif ($Id -cin @('source-pin-substitution','source-fixture-substitution','pin-fixture-substitution')) {
      $victim = if ($Id -ceq 'pin-fixture-substitution') { 'stale-source-rejection' } else { 'source-core-fuel' }
      $span = [regex]::Matches($text,'(?m)\{"id":"' + [regex]::Escape($victim) + '",[^\r\n]*\}')
      if ($span.Count -ne 1) { throw 'binary substitution anchor not unique' }
      # Substitute a COMPLETE valid ordinary case, retaining only the victim ID.
      # An incomplete object would confound kind downgrade with missing fields.
      $donor = if ($Id -ceq 'source-pin-substitution') { 'stale-source-rejection' } else { 'pq1-n9-full' }
      $replacementCase = @($parsed.cases | Where-Object id -CEQ $donor)[0] |
        ConvertTo-Json -Depth 30 | ConvertFrom-Json
      $replacementCase.id = $victim
      $replacement = ConvertTo-Json -InputObject $replacementCase -Depth 30 -Compress
      $changed = $text.Substring(0,$span[0].Index) + $replacement + $text.Substring($span[0].Index + $span[0].Length)
      $parsed.cases = @($parsed.cases | ForEach-Object { if ($_.id -ceq $victim) { $replacementCase } else { $_ } })
      $parsedChanged = $changed | ConvertFrom-Json
      if ((ConvertTo-Json -InputObject $parsedChanged -Depth 30 -Compress) -cne
          (ConvertTo-Json -InputObject $parsed -Depth 30 -Compress)) { throw 'binary complete-case substitution changed other fields' }
      [IO.File]::WriteAllText($controlRegistryPath,$changed,[Text.UTF8Encoding]::new($false))
    } elseif ($Id -ceq 'registry-format-change') {
      [IO.File]::WriteAllText($controlRegistryPath,$text + "`n",[Text.UTF8Encoding]::new($false))
    } elseif ($Id -ceq 'registry-duplicate-key') {
      $changed = $text.Replace('"schema": "native1-binary-cases-v1"','"schema": "native1-binary-cases-v1", "schema": "native1-binary-cases-v1"')
      if ($changed -ceq $text) { throw 'binary duplicate-key anchor missing' }
      [IO.File]::WriteAllText($controlRegistryPath,$changed,[Text.UTF8Encoding]::new($false))
    } else {
      if ($Id -ceq 'registry-empty-cases') { $parsed.cases=@() }
      elseif ($Id -ceq 'registry-duplicate-case') { $parsed.cases += @($parsed.cases[0]) }
      elseif ($Id -ceq 'registry-extra-top-field') { $parsed | Add-Member -NotePropertyName bypass -NotePropertyValue $true }
      elseif ($Id -ceq 'registry-extra-case-field') { $parsed.cases[0] | Add-Member -NotePropertyName bypass -NotePropertyValue $true }
      else { throw 'unknown binary registry mutation' }
      $parsed | ConvertTo-Json -Depth 30 | Set-Content -LiteralPath $controlRegistryPath -Encoding utf8
    }
    if ((Get-FileHash -LiteralPath $controlRegistryPath).Hash -ceq $before) { throw 'vacuous binary registry mutation' }
    $details = Assert-BinaryControlRejected $Id 'query-smoke' 'exact binary semantic registry mismatch'
    $details.mutation = $mutation
    $details.beforeSha256 = $before
    $details.mutatedSha256 = (Get-FileHash -LiteralPath $controlRegistryPath).Hash
  } finally {
    [IO.File]::WriteAllBytes($controlRegistryPath,$saved)
    if ((Get-FileHash -LiteralPath $controlRegistryPath).Hash -cne $before -or
        (Get-BinaryControlGitState 'scripts/packed_native_binary_cases.json') -cne $state) { throw 'binary registry restoration mismatch' }
  }
  $details.restoredSha256 = (Get-FileHash -LiteralPath $controlRegistryPath).Hash
  $details.exactGitRestoration = $true
  return $details
}
try {
  $pythonProbe = Invoke-BinaryControlOwned 'python-control-producer-identity' $controlPython @('--version') 30
  if ($pythonProbe.ExitCode -ne 0) { throw 'binary controls Python identity failed' }
  $controlPythonIdentity = [ordered]@{path=[IO.Path]::GetFullPath($controlPython);
    version=($pythonProbe.StandardOutput -join "`n").Trim();sha256=(Get-FileHash -LiteralPath $controlPython).Hash;
    runtimeDlls=@(Get-ChildItem -LiteralPath (Split-Path $controlPython -Parent) -File -Filter 'python*.dll' |
      Sort-Object Name | ForEach-Object { @{path=$_.FullName;sha256=(Get-FileHash -LiteralPath $_.FullName).Hash} });
    process=$pythonProbe}
  if ($controlPythonIdentity.version -cnotmatch '^Python 3\.(1[0-9]|[2-9][0-9])\.[0-9]+') { throw 'unsupported binary controls Python version' }
  foreach ($id in $controlSelected) {
    if ($id -cin @('empty','whitespace','malformed','unknown')) {
      $selector = switch -CaseSensitive ($id) { 'empty' { '' } 'whitespace' { ' ' } 'malformed' { 'query-smoke,' } 'unknown' { 'not-a-binary-case' } }
      $details = Assert-BinaryControlRejected $id $selector 'invalid exact binary selector'
    } elseif ($id -cin @('valid-smoke','omitted-full')) {
      $bound = $id -ceq 'valid-smoke'
      $r = Invoke-BinaryControlChild $id $bound 'query-smoke' $(if ($bound) { 600 } else { 3600 })
      $expected = if ($bound) { @('query-smoke/packed-rmq-native.exe','query-smoke/packed-rmq-native-cpp.exe') }
        else { @($controlRegistry.cases | ForEach-Object { if ($_.kind -cin @('native','ffi-mutation')) { foreach ($consumer in $_.consumers) { $_.id + '/' + $consumer } } else { $_.id } }) }
      $executed = @($r.StandardOutput | Where-Object { $_ -clike 'NATIVE1-BINARY PASS *' } | ForEach-Object { $_.Substring('NATIVE1-BINARY PASS '.Length) })
      if ($r.ExitCode -ne 0 -or ($executed -join ',') -cne ($expected -join ',') -or $expected.Count -eq 0) {
        $controlResults.Add(@{id=$id;pass=$false;expected=$expected;executed=$executed;process=$r})
        throw ('binary positive selector failed: ' + $id)
      }
      $details = @{process=$r;expected=$expected;executed=$executed;selectorBound=$bound}
    } elseif ($id -clike 'witness-*') {
      $mutation = $id.Substring('witness-'.Length)
      $contract = $controlWitnessChallenges[$mutation]
      $mutatedPath = Join-Path $controlScratch ($id + '.fixture')
      $r = Invoke-BinaryControlOwned $id $controlPython @($controlProducer,'witness-challenge',
        '--registry',$controlRegistryPath,'--mutation',$mutation,'--output',$mutatedPath) 90
      if ($r.ExitCode -eq 0 -or $r.StandardOutput.Count -ne 2 -or
          $r.StandardOutput[0] -cne ('NATIVE1-WITNESS-BASELINE PASS ' + $contract[0]) -or
          $r.StandardError[-1] -cne ('ValueError: ' + $contract[1])) {
        throw ('witness semantic mutation missed its baseline or exact failing surface: ' + $id)
      }
      $change = $r.StandardOutput[1] | ConvertFrom-Json
      $spec = @($controlRegistry.cases | Where-Object id -CEQ $contract[0])[0].image
      if ($change.case -cne $contract[0] -or $change.mutation -cne $mutation -or
          $change.expectedDiagnostic -cne $contract[1] -or
          $change.baselineFixtureSha256 -cne $spec.fixtureSha256 -or
          (Get-FileHash -LiteralPath $mutatedPath).Hash -cne $change.mutatedFixtureSha256 -or
          (Get-FileHash -LiteralPath (Join-Path $controlRoot $spec.fixturePath)).Hash -cne $spec.fixtureSha256) {
        throw 'witness semantic mutation or source restoration identity mismatch'
      }
      $details = @{process=$r;change=$change;unchangedProductionCheckPassed=$true;sourceFixtureUnchanged=$true}
    } elseif ($id -clike '*-manifest-*') {
      $path = Join-Path $controlRoot '.lake/native1/binary-build/build-manifest.json'
      $saved = [IO.File]::ReadAllBytes($path)
      $before = (Get-FileHash -LiteralPath $path).Hash
      try {
        $manifest = [Text.UTF8Encoding]::new($false,$true).GetString($saved) | ConvertFrom-Json
        if ($id -ceq 'source-manifest-missing') { $manifest.sources=@($manifest.sources | Select-Object -SkipLast 1) }
        elseif ($id -ceq 'artifact-manifest-empty') { $manifest.artifacts=@() }
        elseif ($id -ceq 'toolchain-manifest-missing') { $manifest.PSObject.Properties.Remove('toolchainIdentity') }
        elseif ($id -ceq 'generatedC-manifest-missing') { $manifest.generatedC=@($manifest.generatedC | Select-Object -SkipLast 1) }
        elseif ($id -ceq 'lean-root-manifest-mismatch') { $manifest.leanRoot=Join-Path $controlScratch 'unverified-lean-root' }
        else { throw 'unknown binary manifest mutation' }
        $manifest | ConvertTo-Json -Depth 30 | Set-Content -LiteralPath $path -Encoding utf8
        $surface = if ($id -ceq 'toolchain-manifest-missing') { 'native toolchain manifest shape' } else { 'binary build manifest shape' }
        $details = Assert-BinaryControlRejected $id 'query-smoke' $surface
      } finally {
        [IO.File]::WriteAllBytes($path,$saved)
        if ((Get-FileHash -LiteralPath $path).Hash -cne $before) { throw 'binary manifest restoration mismatch' }
      }
      $details.restoredSha256=$before
    } else { $details = Invoke-BinaryRegistryMutation $id }
    $controlResults.Add(@{id=$id;pass=$true;details=$details})
    Write-Output ('NATIVE1-BINARY-CONTROL PASS ' + $id)
  }
  if (($controlResults.id -join ',') -cne ($controlSelected -join ',')) { throw 'binary control executed/expected mismatch' }
  $controlSuccess = $true
} catch { $controlFailure=$_.Exception.Message; throw }
finally {
  if ((Get-FileHash -LiteralPath $controlRegistryPath).Hash -cne $controlRegistryHash) { throw 'final binary registry restoration mismatch' }
  [ordered]@{schema='native1-binary-controls-v1';startedUtc=$controlStarted;completedUtc=[DateTime]::UtcNow.ToString('o');
    pass=$controlSuccess;failure=$controlFailure;registrySha256=$controlRegistryHash;
    controlSha256=(Get-FileHash -LiteralPath $PSCommandPath).Hash;selectorBound=$PSBoundParameters.ContainsKey('Case');selector=$Case;
    producerRuntime=$controlPythonIdentity;
    expected=$controlSelected;executed=@($controlResults.id);results=@($controlResults.ToArray());commands=@($controlCommands.ToArray())} | ConvertTo-Json -Depth 35 |
    Set-Content -LiteralPath (Join-Path $controlLogs ('binary-controls-' + $controlRunId + '.json')) -Encoding utf8
}
