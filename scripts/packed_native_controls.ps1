param([AllowEmptyString()][string]$Case)
$ErrorActionPreference = 'Stop'
$controlRoot = Split-Path $PSScriptRoot -Parent
. (Join-Path $PSScriptRoot 'owned_process_tree.ps1')
$controlRoute = Join-Path $PSScriptRoot 'packed_native_route.ps1'
$controlRegistryPath = Join-Path $controlRoot 'native/packed-rmq/route-registry.json'
$controlRegistryBytes = [IO.File]::ReadAllBytes($controlRegistryPath)
$controlRegistry = [Text.UTF8Encoding]::new($false,$true).GetString($controlRegistryBytes) | ConvertFrom-Json
$controlRegistryHash = (Get-FileHash -LiteralPath $controlRegistryPath).Hash
$controlShell = (Get-Process -Id $PID).Path
$controlScratch = Join-Path $controlRoot '.lake/native1/build/control-process'
$controlOut = Join-Path $controlRoot 'docs/internal/extensions/native1/commands'
[void](New-Item -ItemType Directory -Force -Path $controlOut)
# The roster is independent of the mutable registry. Each representative pins a
# distinct semantic field; controls mutate the real file and invoke the real CLI.
$controlFields = [ordered]@{
  id='smoke'; kind='source-core-mutation'; operation='source-core-mutation';
  executable='cpp-n9-full'; mode='n9-no-reads'; program='malformed-instruction';
  fixture='n9-full'; exit='cpp-malformed-instruction'; expected='n9-full';
  source='source-core-mutation'; anchor='source-core-mutation';
  replacement='source-core-mutation'; proofLine='source-core-mutation';
  surface='source-core-mutation'; append='stale-source-rejection';
  outputChannel='cpp-malformed-instruction'; expectedOtherOutput='malformed-instruction'
}
$controlIds = @('empty','whitespace','malformed','unknown',
  'registry-source-pin-downgrade','registry-fixture-substitution',
  'registry-stale-fixture-substitution','registry-missing-schema','registry-changed-schema',
  'registry-empty-cases','registry-missing-cases','registry-duplicate-case',
  'registry-extra-top-field','registry-extra-case-field','registry-duplicate-json-key',
  'registry-format-change') +
  @($controlFields.Keys | ForEach-Object { 'registry-delete-' + $_; 'registry-change-' + $_ }) +
  @('source-manifest-missing','artifact-manifest-empty','fixture-manifest-missing',
    'valid-smoke','omitted-full')
if ($controlIds.Count -ne 55 -or @($controlIds | Select-Object -Unique).Count -ne 55) {
  throw 'exact nonempty controls registry mismatch'
}
if ($PSBoundParameters.ContainsKey('Case')) {
  if ([string]::IsNullOrWhiteSpace($Case) -or $Case -cnotmatch '^[a-zA-Z0-9-]+$' -or
      $controlIds -cnotcontains $Case) { throw 'invalid exact controls selector' }
  $controlSelected = @($Case)
} else { $controlSelected = @($controlIds) }
$controlResults = [Collections.Generic.List[object]]::new()
function Invoke-ControlChild([string]$Id, [bool]$SelectorBound, [string]$Selector, [int]$Deadline = 120) {
  $childArgs = @('-NoLogo','-NoProfile','-ExecutionPolicy','Bypass','-File',$controlRoute)
  if ($SelectorBound) { $childArgs += @('-Case',$Selector) }
  $result = Invoke-RMQOwnedBoundedProcess -FilePath $controlShell -Arguments $childArgs `
    -WorkingDirectory $controlRoot -Stage ('native1-control-' + $Id) `
    -DeadlineSeconds $Deadline -OutputLimitBytes 8388608 -TempRoot $controlScratch
  $result | Add-Member -NotePropertyName InvokedFilePath -NotePropertyValue $controlShell
  $result | Add-Member -NotePropertyName InvokedArguments -NotePropertyValue @($childArgs)
  if ($result.TimedOut -or $result.OutputLimitExceeded) {
    $controlResults.Add(@{id=$Id;pass=$false;incomplete=$true;process=$result})
    throw ('bounded control process incomplete: ' + $Id)
  }
  return $result
}
function Assert-ControlRejected([string]$Id, [string]$Selector, [string]$Message) {
  $r = Invoke-ControlChild $Id $true $Selector
  if ($r.ExitCode -eq 0 -or (($r.Output -join "`n") -notmatch [regex]::Escape($Message)) -or
      @($r.StandardOutput | Where-Object { $_ -like 'NATIVE1-ROUTE PASS *' }).Count -ne 0) {
    $controlResults.Add(@{id=$Id;pass=$false;expectedSurface=$Message;process=$r})
    throw ('control did not reject at expected boundary: ' + $Id)
  }
  return @{verdict='expected rejection';surface=$Message;process=$r;
    selectorBound=$true;selector=$Selector}
}
function Get-ControlGitState([string]$Path) {
  $output = @(& git -c core.excludesfile= diff --binary -- $Path)
  if ($LASTEXITCODE -ne 0) { throw 'could not read control restoration state' }
  return ($output -join "`n")
}
function Set-ControlCaseFieldText([string]$Text, [string]$Id, [string]$Field,
    [string]$Action, [string]$ValueJson) {
  # Change one property span in the committed one-line case representation.
  # Reformatting all cases would make a formatting rejection confound the
  # measured same-ID downgrade and the semantic field mutations.
  $lineMatches = [regex]::Matches($Text, '(?m)^ *\{"id":"' + [regex]::Escape($Id) + '",[^\r\n]*')
  if ($lineMatches.Count -ne 1) { throw 'case text mutation anchor not unique' }
  $line = $lineMatches[0]
  $fieldMatches = [regex]::Matches($line.Value, '"' + [regex]::Escape($Field) +
    '":(?:"(?:[^"\\]|\\.)*"|-?[0-9]+|true|false|null)')
  if ($fieldMatches.Count -ne 1) { throw 'field text mutation anchor not unique' }
  $span = $fieldMatches[0]
  $offset = $span.Index
  $length = $span.Length
  if ($Action -ceq 'delete') {
    if ($offset -gt 0 -and $line.Value[$offset - 1] -ceq ',') { $offset--; $length++ }
    elseif ($line.Value[$offset + $length] -ceq ',') { $length++ }
    else { throw 'field removal has no comma anchor' }
    $replacement = ''
  } else { $replacement = '"' + $Field + '":' + $ValueJson }
  $newLine = $line.Value.Substring(0,$offset) + $replacement + $line.Value.Substring($offset + $length)
  return $Text.Substring(0,$line.Index) + $newLine + $Text.Substring($line.Index + $line.Length)
}
function Invoke-ControlRegistryMutation([string]$Id) {
  $saved = [IO.File]::ReadAllBytes($controlRegistryPath)
  $hash = (Get-FileHash -LiteralPath $controlRegistryPath).Hash
  $state = Get-ControlGitState 'native/packed-rmq/route-registry.json'
  $receipt = $null
  try {
    $text = [Text.UTF8Encoding]::new($false,$true).GetString($saved)
    $registry = $text | ConvertFrom-Json
    $mutated = $null
    if ($Id -eq 'registry-source-pin-downgrade') {
      ($registry.cases | Where-Object id -CEQ 'source-core-mutation').kind = 'source-pin'
      $mutated = Set-ControlCaseFieldText $text 'source-core-mutation' 'kind' 'change' '"source-pin"'
    } elseif ($Id -eq 'registry-fixture-substitution' -or $Id -eq 'registry-stale-fixture-substitution') {
      $victim = if ($Id -eq 'registry-fixture-substitution') { 'source-core-mutation' } else { 'stale-source-rejection' }
      $registry.cases = @($registry.cases | ForEach-Object {
        if ($_.id -ceq $victim) { [pscustomobject]@{id=$victim;kind='fixture';fixture='n9-full';mode='reads'} }
        else { $_ }
      })
      $span = [regex]::Matches($text, '(?m)\{"id":"' + [regex]::Escape($victim) + '",[^\r\n]*\}')
      if ($span.Count -ne 1) { throw 'case substitution text anchor not unique' }
      $replacement = '{"id":"' + $victim + '","kind":"fixture","fixture":"n9-full","mode":"reads"}'
      $mutated = $text.Substring(0,$span[0].Index) + $replacement + $text.Substring($span[0].Index + $span[0].Length)
    } elseif ($Id -eq 'registry-missing-schema') { $registry.PSObject.Properties.Remove('schema')
    } elseif ($Id -eq 'registry-changed-schema') { $registry.schema = 'native1-route-registry-v999'
    } elseif ($Id -eq 'registry-empty-cases') { $registry.cases = @()
    } elseif ($Id -eq 'registry-missing-cases') { $registry.PSObject.Properties.Remove('cases')
    } elseif ($Id -eq 'registry-duplicate-case') { $registry.cases += @($registry.cases[0])
    } elseif ($Id -eq 'registry-extra-top-field') { $registry | Add-Member -NotePropertyName bypass -NotePropertyValue $true
    } elseif ($Id -eq 'registry-extra-case-field') { $registry.cases[0] | Add-Member -NotePropertyName bypass -NotePropertyValue $true
    } elseif ($Id -like 'registry-delete-*' -or $Id -like 'registry-change-*') {
      $action = if ($Id.StartsWith('registry-delete-')) { 'delete' } else { 'change' }
      $field = $Id.Substring(('registry-' + $action + '-').Length)
      $entry = @($registry.cases | Where-Object { $_.id -ceq $controlFields[$field] })
      if ($entry.Count -ne 1 -or $entry[0].PSObject.Properties.Name -cnotcontains $field) { throw 'control field anchor missing' }
      if ($action -eq 'delete') {
        $entry[0].PSObject.Properties.Remove($field)
        $mutated = Set-ControlCaseFieldText $text $controlFields[$field] $field 'delete' ''
      } else {
        $newValue = if ($field -ceq 'exit') { 99 } else { 'changed-field-value' }
        $entry[0].$field = $newValue
        $valueJson = ConvertTo-Json -InputObject $newValue -Compress
        $mutated = Set-ControlCaseFieldText $text $controlFields[$field] $field 'change' $valueJson
      }
    }
    if ($null -ne $mutated) {
      $expectedJson = ConvertTo-Json -InputObject $registry -Compress -Depth 12
      $actualJson = ConvertTo-Json -InputObject ($mutated | ConvertFrom-Json) -Compress -Depth 12
      if ($actualJson -cne $expectedJson) { throw 'minimal text mutation changed unintended semantics' }
    } else {
      $mutated = if ($Id -eq 'registry-format-change') { $text + "`n" }
      elseif ($Id -eq 'registry-duplicate-json-key') {
        $text.Replace('"schema": "native1-route-registry-v3",', '"schema": "discarded-variant", "schema": "native1-route-registry-v3",')
      } else { $registry | ConvertTo-Json -Depth 12 }
    }
    [IO.File]::WriteAllText($controlRegistryPath, $mutated, [Text.UTF8Encoding]::new($false))
    $mutatedHash = (Get-FileHash -LiteralPath $controlRegistryPath).Hash
    if ($mutatedHash -ceq $hash) { throw 'registry control did not mutate bytes' }
    $receipt = Assert-ControlRejected $Id 'smoke' 'exact semantic registry mismatch'
    $receipt.beforeSha256 = $hash
    $receipt.mutatedSha256 = $mutatedHash
    $receipt.mutation = $Id
  } finally {
    [IO.File]::WriteAllBytes($controlRegistryPath, $saved)
    if ((Get-FileHash -LiteralPath $controlRegistryPath).Hash -cne $hash -or
        (Get-ControlGitState 'native/packed-rmq/route-registry.json') -cne $state) {
      throw ('registry control restoration failed: ' + $Id)
    }
  }
  $receipt.restoredSha256 = $hash
  $receipt.exactGitRestoration = $true
  return $receipt
}
$controlSuccess = $false
try {
  foreach ($id in $controlSelected) {
    if (@('empty','whitespace','malformed','unknown') -ccontains $id) {
      $selector = switch ($id) { empty {''}; whitespace {'   '}; malformed {'n9-full,n9-empty'}; unknown {'unknown'} }
      $details = Assert-ControlRejected $id $selector 'invalid exact selector'
    } elseif ($id.StartsWith('registry-')) {
      $details = Invoke-ControlRegistryMutation $id
    } elseif (@('source-manifest-missing','artifact-manifest-empty','fixture-manifest-missing') -ccontains $id) {
      $relative = if ($id -eq 'fixture-manifest-missing') { 'native/packed-rmq/fixtures/manifest.json' }
        else { '.lake/native1/build/build-manifest.json' }
      $path = Join-Path $controlRoot $relative
      $saved = [IO.File]::ReadAllBytes($path)
      $hash = (Get-FileHash -LiteralPath $path).Hash
      $state = Get-ControlGitState $relative
      try {
        $manifest = [Text.UTF8Encoding]::new($false,$true).GetString($saved) | ConvertFrom-Json
        if ($id -eq 'source-manifest-missing') {
          $manifest.sources = @($manifest.sources | Where-Object { $_.path -cne 'RMQ/Core/WordRAM/Native/Thin.lean' })
        } elseif ($id -eq 'artifact-manifest-empty') { $manifest.artifacts = @() }
        else { $manifest.files = @($manifest.files | Select-Object -Skip 1) }
        [IO.File]::WriteAllText($path, ($manifest | ConvertTo-Json -Depth 30), [Text.UTF8Encoding]::new($false))
        $message = if ($id -eq 'fixture-manifest-missing') { 'exact fixture manifest mismatch' } else { 'build manifest shape' }
        $details = Assert-ControlRejected $id 'smoke' $message
        $details.beforeSha256 = $hash
        $details.mutatedSha256 = (Get-FileHash -LiteralPath $path).Hash
      } finally {
        [IO.File]::WriteAllBytes($path, $saved)
        if ((Get-FileHash -LiteralPath $path).Hash -cne $hash -or (Get-ControlGitState $relative) -cne $state) {
          throw ('control restoration failed: ' + $id)
        }
      }
      $details.restoredSha256 = $hash
      $details.exactGitRestoration = $true
    } else {
      $bound = $id -ceq 'valid-smoke'
      $r = Invoke-ControlChild $id $bound 'smoke' 900
      $reportLines = @($r.StandardOutput | Where-Object { $_.StartsWith('NATIVE1-ROUTE-REPORT ') })
      if ($r.ExitCode -ne 0 -or $reportLines.Count -ne 1) {
        $controlResults.Add(@{id=$id;pass=$false;process=$r})
        throw ('positive subprocess control failed: ' + $id)
      }
      $reportPath = $reportLines[0].Substring('NATIVE1-ROUTE-REPORT '.Length)
      if (-not [IO.Path]::GetFullPath($reportPath).StartsWith([IO.Path]::GetFullPath($controlOut) + [IO.Path]::DirectorySeparatorChar)) {
        throw 'route report escaped declared output directory'
      }
      $report = Get-Content -LiteralPath $reportPath -Raw | ConvertFrom-Json
      $expected = if ($bound) { @('smoke') } else { @($controlRegistry.cases.id) }
      if ($report.schema -cne 'native1-route-results-v3' -or -not $report.success -or
          $report.selectorBound -ne $bound -or $report.expectedCount -ne $expected.Count -or
          $report.executedCount -ne $expected.Count -or
          ($report.expectedCases -join ',') -cne ($expected -join ',') -or
          ($report.executedCases -join ',') -cne ($expected -join ',') -or
          $report.registrySha256 -cne $controlRegistryHash -or
          @($report.results | Where-Object { -not $_.pass }).Count -ne 0) {
        throw 'positive subprocess report did not preserve exact selection'
      }
      if (-not $bound) {
        $mutation = @($report.results | Where-Object id -CEQ 'source-core-mutation')
        $pin = @($report.results | Where-Object id -CEQ 'stale-source-rejection')
        if ($mutation.Count -ne 1 -or $mutation[0].operation -cne 'lean-type-rejection' -or
            $mutation[0].evidence.failingSurface -cne 'routeCore_source' -or
            $mutation[0].evidence.process.ExitCode -eq 0 -or
            $pin.Count -ne 1 -or $pin[0].operation -cne 'source-identity-rejection' -or
            $pin[0].evidence.verdict -cne 'stale-source rejected') {
          throw 'source control positive lost its operation-specific evidence'
        }
      }
      $details = @{verdict='expected accept';process=$r;routeReport=$reportPath;
        routeReportSha256=(Get-FileHash -LiteralPath $reportPath).Hash;
        selectorBound=$bound;expectedCases=$expected;executedCases=$report.executedCases}
    }
    $controlResults.Add(@{id=$id;pass=$true;evidence=$details})
    Write-Output ('NATIVE1-CONTROL PASS ' + $id)
  }
  if (($controlResults.id -join ',') -cne ($controlSelected -join ',')) { throw 'executed controls registry mismatch' }
  $controlSuccess = $true
} finally {
  if ((Get-FileHash -LiteralPath $controlRegistryPath).Hash -cne $controlRegistryHash) { throw 'control registry final restoration mismatch' }
  $record = [ordered]@{schema='native1-route-controls-v3';success=$controlSuccess;
    platform=[Environment]::OSVersion.VersionString;powershell=$PSVersionTable.PSVersion.ToString();
    runnerSha256=(Get-FileHash -LiteralPath $controlRoute).Hash;
    controlsSha256=(Get-FileHash -LiteralPath $PSCommandPath).Hash;registrySha256=$controlRegistryHash;
    registryCases=$controlIds;registryCount=$controlIds.Count;
    expectedCases=$controlSelected;executedCases=@($controlResults.id);
    expectedCount=$controlSelected.Count;executedCount=$controlResults.Count;results=@($controlResults.ToArray());
    unsupportedHosts=@('Non-Windows process boundary and native execution are not covered by this campaign')}
  $outPath = Join-Path $controlOut ('controls-' + [DateTime]::UtcNow.ToString('yyyyMMddTHHmmssfff') + '.json')
  [IO.File]::WriteAllText($outPath, ($record | ConvertTo-Json -Depth 24), [Text.UTF8Encoding]::new($false))
  Write-Output ('NATIVE1-CONTROLS-REPORT ' + $outPath)
}
