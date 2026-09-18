#!/usr/bin/env pwsh
# Read-only, exact-candidate evidence inspection. Never invokes Lean or the replay runner.
# Do not execute until the coordinator confirms the full campaign has completed.
# Assigned coverage: V01 literal registry/order/verdicts; V02 all raw/summary stages;
# V03 exact diagnostic declarations; V04 six runtime cases and selector boundaries;
# V05 restoration assertions/current source hashes; V06 no resource-failure rejection.
# This verifies recorded evidence, not independent kernel execution or acceptance.
[CmdletBinding()]
param([string]$OutputJsonPath = '')
Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'
$repo = 'C:\Users\poin\.codex\worktrees\2270\RMQ'
$candidate = '5033ce54da233fc7a3df319d50ab09a2ebee523a'
$runRoot = Join-Path $repo '.lake/lb1-replay/20260912T101947006'
$reportRoot = Join-Path $repo '.lake/lb1-finalization'
$utf8 = [Text.UTF8Encoding]::new($false, $true)
$gitPath = (Get-Command git -CommandType Application | Select-Object -First 1).Source
$checks = [Collections.Generic.List[string]]::new()
$stageEvidence = [Collections.Generic.List[object]]::new()
$sourceEvidence = [Collections.Generic.List[object]]::new()
$artifactEvidence = [Collections.Generic.List[object]]::new()
$scriptHash = $null
$summaryHash = $null
$registryHash = $null
$runnerHash = $null
$failure = $null
$validatedOutputPath = $null

# Independent literals: neither the mutable registry nor runner supplies expectations.
$caseLiterals = @'
O01-wordRoundTrip|OPTIMALITY|wordRoundTrip|REJECT|checkO01
O02-wordSerializationInjective|OPTIMALITY|wordSerializationInjective|REJECT|checkO02
O03-serializedLength|OPTIMALITY|serializedLength|REJECT|checkO03
O04-memoryRecovery|OPTIMALITY|memoryRecovery|REJECT|checkO04
O05-decoderExact|OPTIMALITY|decoderExact|REJECT|checkO05
O06-decoderLeftmost|OPTIMALITY|decoderLeftmost|REJECT|checkO06
O07-sameShapeMemory|OPTIMALITY|sameShapeMemory|REJECT|checkO07
O08-shapeInjectivity|OPTIMALITY|shapeInjectivity|REJECT|checkO08
O09-uniformBudgetCount|OPTIMALITY|uniformBudgetCount|REJECT|checkO09
O10-uniformBudgetLower|OPTIMALITY|uniformBudgetLower|REJECT|checkO10
O11-canonicalCount|OPTIMALITY|canonicalCount|REJECT|checkO11
O12-canonicalLower|OPTIMALITY|canonicalLower|REJECT|checkO12
O13-upperCapacity|OPTIMALITY|upperCapacity|REJECT|checkO13
O14-allocationResidualLittleO|OPTIMALITY|allocationResidualLittleO|REJECT|checkO14
O15-runIdentity|OPTIMALITY|runIdentity|REJECT|checkO15
O16-machine|OPTIMALITY|machine|REJECT|checkO16
M01-allocationResidualLittleO|MACHINE|allocationResidualLittleO|REJECT|checkM01
M02-completeResidualLittleO|MACHINE|completeResidualLittleO|REJECT|checkM02
M03-widthBounds|MACHINE|widthBounds|REJECT|checkM03
M04-dataCapacity|MACHINE|dataCapacity|REJECT|checkM04
M05-completeCapacity|MACHINE|completeCapacity|REJECT|checkM05
M06-memoryWordsFit|MACHINE|memoryWordsFit|REJECT|checkM06
M07-allocationAddressesFit|MACHINE|allocationAddressesFit|REJECT|checkM07
M08-programFieldsFit|MACHINE|programFieldsFit|REJECT|checkM08
M09-budgetExact|MACHINE|budgetExact|REJECT|checkM09
M10-programLength|MACHINE|programLength|REJECT|checkM10
M11-encodedProgramBound|MACHINE|encodedProgramBound|REJECT|checkM11
M12-registerCount|MACHINE|registerCount|REJECT|checkM12
M13-scratchCount|MACHINE|scratchCount|REJECT|checkM13
M14-unusedRegisters|MACHINE|unusedRegisters|REJECT|checkM14
M15-validInputs|MACHINE|validInputs|REJECT|checkM15
M16-natContract|MACHINE|natContract|REJECT|checkM16
M17-leftmost|MACHINE|leftmost|REJECT|checkM17
M18-result|MACHINE|result|REJECT|checkM18
M19-halt|MACHINE|halt|REJECT|checkM19
M20-invalidGuard|MACHINE|invalidGuard|REJECT|checkM20
M21-stepBound|MACHINE|stepBound|REJECT|checkM21
M22-categoryPartition|MACHINE|categoryPartition|REJECT|checkM22
M23-finalStateFit|MACHINE|finalStateFit|REJECT|checkM23
M24-transitionSafety|MACHINE|transitionSafety|REJECT|checkM24
M25-prefixSafety|MACHINE|prefixSafety|REJECT|checkM25
M26-readWidth|MACHINE|readWidth|REJECT|checkM26
M27-positionalReadBacking|MACHINE|positionalReadBacking|REJECT|checkM27
M28-orderedLogicalRefinement|MACHINE|orderedLogicalRefinement|REJECT|checkM28
M29-logicalReadOnly|MACHINE|logicalReadOnly|REJECT|checkM29
M30-suppliedMemoryAgreement|MACHINE|suppliedMemoryAgreement|REJECT|checkM30
M31-specResult|MACHINE|specResult|REJECT|checkM31
M32-noFailedLoads|MACHINE|noFailedLoads|REJECT|checkM32
M33-invalidGuardSteps|MACHINE|invalidGuardSteps|REJECT|checkM33
A01-BASELINE|ACCEPT||ACCEPT|publicContract
P01-PUBLIC-PROPOSITION|PUBLIC||REJECT|publicContract
G01-LOWER-PROPOSITION|GENERIC||REJECT|genericBoundConsumer
G02-DELETED-EXACTNESS|EXACTNESS||REJECT|sameRMQBehavior_of_encode_eq
D01-NULL-DECODER|NULL||REJECT|allocationDecoder_exact
D02-WRONG-DECODER|WRONG||REJECT|allocationDecoder_exact
D03-ZERO-SERIALIZER|ZERO||REJECT|serializeWords_length
F01-DELETE-MEMORY-RECOVERY|DELETE|OPTIMALITY.memoryRecovery|REJECT|checkO04
F02-DELETE-READ-BACKING|DELETE|MACHINE.positionalReadBacking|REJECT|checkM27
S01-SIBLING-MEMORY|SIBLING|memoryRecovery|REJECT|checkO04
S02-SIBLING-RUN|SIBLING|runIdentity|REJECT|checkO15
S03-SIBLING-BUDGET|SIBLING|uniformBudgetCount|REJECT|checkO09
H01-EMPTY-ONLY-DECODER|GUARD|decoderExact|REJECT|checkO05
A02-PROOF-ONLY-WRAPPER|WRAPPER||ACCEPT|publicContract
'@ -split '\r?\n'
$runtimeIDs = @('R01-EMPTY','R02-SINGLETON','R03-LEFTMOST','R04-ZERO-LENGTH','R05-ZERO-WORDS','R06-SAME-SHAPE')
$inventoryLine = 'LB1-FIELDS PASS actual=4,16,33; unchanged and ordered controls accepted; defaulted, indented, underscore, apostrophe, Unicode, escaped, absent, missing, reversed and parent controls rejected'
$producer = 'RMQ/Core/WordRAM/Packed/AllocationLowerBound.lean'
$generic = 'RMQ/Core/EncodingVariableLowerBound.lean'
$consumer = 'RMQ/Validation/VariablePayloadLowerBound.lean'
$genericConsumer = 'scripts/variable_payload_generic_consumer.lean'
$registryPath = 'docs/internal/extensions/lb1/REPLAY_REGISTRY.json'
$runnerPath = 'scripts/variable_payload_replay.ps1'

function Assert-Check([bool]$condition, [string]$message) {
  if (-not $condition) { throw $message }
}
function Get-SHA256([byte[]]$data) {
  [Convert]::ToHexString([Security.Cryptography.SHA256]::HashData($data)).ToLowerInvariant()
}
function Convert-LF([string]$text) { $text.Replace("`r`n", "`n") }
function Assert-Sequence([object[]]$actual, [object[]]$expected, [string]$label) {
  Assert-Check ($actual.Count -eq $expected.Count) "$label count: actual=$($actual.Count), expected=$($expected.Count)"
  for ($index = 0; $index -lt $expected.Count; $index++) {
    Assert-Check ($actual[$index] -is [string] -and $actual[$index] -ceq $expected[$index]) "$label mismatch at index $index"
  }
}
function Invoke-ReadOnlyGit([string[]]$arguments, [string]$inputText = '') {
  # All call sites use only show/ls-tree/cat-file/rev-parse/status/check-ignore.
  $allowed = @('show','ls-tree','cat-file','rev-parse','status','check-ignore')
  Assert-Check ($arguments.Count -gt 0 -and $arguments[0] -cin $allowed) 'Disallowed Git operation'
  $start = [Diagnostics.ProcessStartInfo]::new()
  $start.FileName = $gitPath
  $start.WorkingDirectory = $repo
  $start.UseShellExecute = $false
  $start.CreateNoWindow = $true
  $start.RedirectStandardOutput = $true
  $start.RedirectStandardError = $true
  $start.RedirectStandardInput = $true
  $start.Environment['GIT_OPTIONAL_LOCKS'] = '0'
  # Repository ignore files remain active; the empty value disables inaccessible
  # per-user global ignores without reinterpreting repository patterns globally.
  foreach ($arg in @('--no-optional-locks','-c','core.fsmonitor=false','-c','core.excludesfile=') + $arguments) { $start.ArgumentList.Add($arg) }
  $process = [Diagnostics.Process]::new()
  $process.StartInfo = $start
  $buffer = [IO.MemoryStream]::new()
  try {
    Assert-Check ($process.Start()) 'Could not start read-only Git process'
    $copy = $process.StandardOutput.BaseStream.CopyToAsync($buffer)
    $stderrTask = $process.StandardError.ReadToEndAsync()
    if ($inputText.Length -gt 0) { $process.StandardInput.Write($inputText) }
    $process.StandardInput.Close()
    if (-not $process.WaitForExit(60000)) {
      # Only this verifier's own read-only Git child; never inspect or kill Lean.
      $process.Kill($true)
      $process.WaitForExit()
      throw "Read-only Git deadline exceeded: $($arguments[0])"
    }
    # PowerShell exposes the concrete async task's VoidTaskResult; suppress it so
    # the helper returns exactly one object containing Bytes.
    [void]$copy.GetAwaiter().GetResult()
    $stderr = $stderrTask.GetAwaiter().GetResult()
    Assert-Check ($process.ExitCode -eq 0) "Git $($arguments[0]) failed: $stderr"
    Assert-Check ($stderr.Length -eq 0) "Git $($arguments[0]) emitted stderr: $stderr"
    return [pscustomobject]@{Bytes=$buffer.ToArray()}
  } finally { $buffer.Dispose(); $process.Dispose() }
}
function Get-CommittedText([string]$path) {
  $result = Invoke-ReadOnlyGit @('show', "${candidate}:$path")
  $utf8.GetString($result.Bytes)
}
function Read-JSON([string]$path) {
  Assert-Check ([IO.File]::Exists($path)) "Required completed evidence missing: $path"
  # Reject duplicate JSON keys as well as malformed JSON before PowerShell conversion.
  $text = [IO.File]::ReadAllText($path, $utf8)
  $document = [Text.Json.JsonDocument]::Parse($text)
  try { Assert-UniqueJSONKeys $document.RootElement $path } finally { $document.Dispose() }
  ConvertFrom-Json -InputObject $text -AsHashtable -NoEnumerate
}
function Assert-UniqueJSONKeys([Text.Json.JsonElement]$element, [string]$label) {
  if ($element.ValueKind -eq [Text.Json.JsonValueKind]::Object) {
    $names = [Collections.Generic.HashSet[string]]::new([StringComparer]::Ordinal)
    foreach ($property in $element.EnumerateObject()) {
      Assert-Check ($names.Add($property.Name)) "Duplicate JSON property $label/$($property.Name)"
      Assert-UniqueJSONKeys $property.Value "$label/$($property.Name)"
    }
  } elseif ($element.ValueKind -eq [Text.Json.JsonValueKind]::Array) {
    foreach ($item in $element.EnumerateArray()) { Assert-UniqueJSONKeys $item $label }
  }
}
function Assert-Keys($object, [string[]]$keys, [string]$label) {
  Assert-Check ($object -is [Collections.IDictionary]) "$label must be a JSON object"
  Assert-Sequence @($object.Keys | Sort-Object -CaseSensitive) @($keys | Sort-Object -CaseSensitive) "$label keys"
}
function Get-Declaration([string]$text, [string]$name) {
  # Independent span calculation. The first following top-level declaration/comment
  # ends this declaration; the following line is excluded, including adjacent errors.
  $text = Convert-LF $text
  $starts = [regex]::Matches($text, '(?m)^(?:theorem|def|structure) ' + [regex]::Escape($name) + '\b')
  Assert-Check ($starts.Count -eq 1) "Declaration not unique: $name"
  $start = $starts[0].Index
  $tailStart = $start + $starts[0].Length
  $next = [regex]::Match($text.Substring($tailStart), '(?m)^(?:theorem |def |structure |namespace |end |/--)')
  $end = if ($next.Success) { $tailStart + $next.Index } else { $text.Length }
  $first = 1 + [regex]::Matches($text.Substring(0,$start), "`n").Count
  # Trim only trailing whitespace for the diagnostic span, never for source equality.
  $body = $text.Substring($start,$end-$start).TrimEnd()
  $last = $first + [regex]::Matches($body, "`n").Count
  [pscustomobject]@{Start=$start; End=$end; First=$first; Last=$last; Text=$body}
}
function Replace-DeclarationInMemory([string]$text, [string]$name, [string]$replacement) {
  $text = Convert-LF $text
  $span = Get-Declaration $text $name
  $text.Substring(0,$span.Start) + $replacement + "`n`n" + $text.Substring($span.End)
}
function Add-Stage([string]$name, [int]$exitCode, [string]$path = '', [string]$surface = '', [string]$text = '') {
  $span = if ($surface.Length -gt 0) { Get-Declaration $text $surface } else { $null }
  $expectedStages.Add([pscustomobject]@{Name=$name; ExitCode=$exitCode; Path=$path; Surface=$surface; Span=$span})
}
function Assert-SourcePathSafe([string]$path) {
  # Reject links/junctions, including ancestor links, before any optional report write.
  $current = [IO.Path]::GetFullPath($path)
  while ($current.Length -gt 0) {
    if ([IO.File]::Exists($current) -or [IO.Directory]::Exists($current)) {
      Assert-Check (([IO.File]::GetAttributes($current) -band [IO.FileAttributes]::ReparsePoint) -eq 0) "Reparse point not allowed: $current"
    }
    $parent = [IO.Path]::GetDirectoryName($current)
    if ($null -eq $parent -or $parent -eq $current) { break }
    $current = $parent
  }
}

try {
  Assert-Check ($PSVersionTable.PSVersion.Major -ge 7) 'PowerShell 7 or later is required'
  $scriptHash = Get-SHA256 ([IO.File]::ReadAllBytes($PSCommandPath))
  if ($OutputJsonPath.Length -gt 0) {
    $resolved = if ([IO.Path]::IsPathRooted($OutputJsonPath)) { [IO.Path]::GetFullPath($OutputJsonPath) } else { [IO.Path]::GetFullPath((Join-Path $repo $OutputJsonPath)) }
    Assert-Check ([IO.Path]::GetDirectoryName($resolved) -ieq [IO.Path]::GetFullPath($reportRoot)) 'Reports may be saved only directly under ignored .lake/lb1-finalization'
    Assert-Check ([IO.Path]::GetFileName($resolved) -cmatch '^[A-Za-z0-9][A-Za-z0-9_.-]*\.json$') 'Report filename must be a simple .json name'
    Assert-SourcePathSafe $resolved
    $null = Invoke-ReadOnlyGit @('check-ignore','--quiet','--no-index','--',$resolved)
    $validatedOutputPath = $resolved
  }
  $summaryPath = Join-Path $runRoot 'summary.json'
  $summary = Read-JSON $summaryPath
  $summaryHash = Get-SHA256 ([IO.File]::ReadAllBytes($summaryPath))
  Assert-Keys $summary @('Version','Commit','Expected','Executed','Stages','SourceRestored','ArtifactsRestored','CleanTree') 'summary'
  Assert-Check ($summary.Version -is [long] -and $summary.Version -eq 3) 'Summary version is not integer 3'
  Assert-Check ($summary.Commit -ceq $candidate) 'Summary is for a different implementation'
  Assert-Check ([IO.File]::ReadAllText((Join-Path $runRoot 'candidate.txt'),$utf8) -ceq $candidate) 'candidate.txt does not exactly match the implementation'
  foreach ($property in @('SourceRestored','ArtifactsRestored','CleanTree')) {
    Assert-Check ($summary[$property] -is [bool] -and $summary[$property]) "Summary restoration assertion is not true: $property"
  }
  $head = $utf8.GetString((Invoke-ReadOnlyGit @('rev-parse','HEAD')).Bytes).TrimEnd("`r","`n")
  Assert-Check ($head -ceq $candidate) 'Current HEAD differs from the frozen implementation; run before later documentation commits'
  Assert-Check ((Invoke-ReadOnlyGit @('status','--porcelain=v1','--untracked-files=normal')).Bytes.Length -eq 0) 'Current Git tree is not clean'
  $checks.Add('Completed version-3 summary, exact candidate.txt/HEAD, restoration assertions, and read-only clean-tree check')

  $registryText = Get-CommittedText $registryPath
  $runnerText = Get-CommittedText $runnerPath
  $registryHash = Get-SHA256 ($utf8.GetBytes($registryText))
  $runnerHash = Get-SHA256 ($utf8.GetBytes($runnerText))
  $registry = ConvertFrom-Json -InputObject $registryText -AsHashtable
  Assert-Check ($registry.version -eq 3) 'Committed registry version differs'
  $signatures = @($registry.cases | ForEach-Object { "$($_.id)|$($_.kind)|$($_.field)|$($_.verdict)|$($_.surface)" })
  Assert-Sequence $signatures $caseLiterals 'Committed registry'
  Assert-Sequence @($registry.runtime) $runtimeIDs 'Committed runtime registry'
  # Parse literals as data, never dot-source/evaluate the committed runner.
  $runnerBlock = [regex]::Match($runnerText, '(?ms)^\$expected=@\(\r?\n(.*?)^\)')
  Assert-Check $runnerBlock.Success 'Committed runner expected-list block missing'
  $runnerLiterals = @([regex]::Matches($runnerBlock.Groups[1].Value, "(?m)^  '([^']+)'[,]?\r?$") | ForEach-Object { $_.Groups[1].Value })
  Assert-Sequence $runnerLiterals $caseLiterals 'Committed runner registry'
  $runtimeBlock = [regex]::Match($runnerText, '(?m)^\$runtimeIDs=@\(([^\r\n]+)\)\r?$')
  Assert-Check $runtimeBlock.Success 'Committed runner runtime-list block missing'
  Assert-Sequence @([regex]::Matches($runtimeBlock.Groups[1].Value,"'([^']+)'") | ForEach-Object { $_.Groups[1].Value }) $runtimeIDs 'Committed runner runtime registry'
  $cases = @($caseLiterals | ForEach-Object { $parts=$_.Split('|'); [pscustomobject]@{ID=$parts[0]; Kind=$parts[1]; Field=$parts[2]; Verdict=$parts[3]; Surface=$parts[4]} })
  Assert-Check ($cases.Count -eq 63 -and @($cases.ID | Select-Object -Unique).Count -eq 63) 'Literal cases not exactly 63 unique IDs'
  Assert-Check (@($cases | Where-Object Verdict -CEQ 'REJECT').Count -eq 61 -and @($cases | Where-Object Verdict -CEQ 'ACCEPT').Count -eq 2) 'Literal verdict split not 61 REJECT / 2 ACCEPT'
  Assert-Sequence @($summary.Expected) @($cases.ID) 'Summary expected case IDs'
  Assert-Sequence @($summary.Executed) @($cases.ID) 'Summary executed case IDs'
  $checks.Add('Independent literal 63 IDs/order/kinds/fields/surfaces; 61 REJECT and 2 ACCEPT; exact committed registry and runner')

  $producerText = Convert-LF (Get-CommittedText $producer)
  $genericText = Convert-LF (Get-CommittedText $generic)
  $consumerText = Convert-LF (Get-CommittedText $consumer)
  $genericConsumerText = Convert-LF (Get-CommittedText $genericConsumer)
  $expectedStages = [Collections.Generic.List[object]]::new()
  foreach ($name in @('baseline-generic-producer','baseline-packed-producer','baseline-inventory','baseline-consumer','baseline-generic-consumer','runtime-startup','runtime-known-selector')) { Add-Stage $name 0 }
  foreach ($name in @('empty','whitespace','malformed','unknown')) { Add-Stage "runtime-selector-$name" 1 }
  Add-Stage 'runtime-full' 0
  foreach ($case in $cases) {
    switch -CaseSensitive ($case.Kind) {
      'ACCEPT' { Add-Stage $case.ID 0 }
      'WRAPPER' { Add-Stage "$($case.ID)-producer" 0; Add-Stage "$($case.ID)-inventory" 0; Add-Stage "$($case.ID)-consumer" 0 }
      'EXACTNESS' {
        $pattern = '(?ms)^  query_exact :(?![=]).*?(?=^\s*$)'
        Assert-Check ([regex]::Matches($genericText,$pattern).Count -eq 1) 'Exactness field deletion is ambiguous'
        $mutated = [regex]::Replace($genericText,$pattern,'')
        Add-Stage "$($case.ID)-producer" 1 $generic $case.Surface $mutated
      }
      { $_ -cin @('NULL','WRONG','ZERO') } {
        if ($case.Kind -ceq 'ZERO') {
          $mutated = Replace-DeclarationInMemory $producerText 'serializeWords' 'def serializeWords (width : Nat) (words : List Nat) : List Bool := []'
        } else {
          $answer = if ($case.Kind -ceq 'NULL') { 'none' } else { 'some 0' }
          $mutated = Replace-DeclarationInMemory $producerText 'allocationDecoder' ("def allocationDecoder (n : Nat) (bits : List Bool) (left right : Nat) : Option Nat := $answer")
        }
        Add-Stage "$($case.ID)-producer" 1 $producer $case.Surface $mutated
      }
      'GENERIC' { Add-Stage "$($case.ID)-producer" 0; Add-Stage "$($case.ID)-consumer" 1 $genericConsumer $case.Surface $genericConsumerText }
      { $_ -cin @('OPTIMALITY','MACHINE','PUBLIC','DELETE','SIBLING','GUARD') } {
        Add-Stage "$($case.ID)-producer" 0
        Add-Stage "$($case.ID)-consumer" 1 $consumer $case.Surface $consumerText
      }
      default { throw "Unrecognized literal case kind $($case.Kind)" }
    }
  }
  Assert-Check ($expectedStages.Count -eq 134 -and @($expectedStages | Where-Object ExitCode -EQ 0).Count -eq 69 -and @($expectedStages | Where-Object ExitCode -EQ 1).Count -eq 65) 'Stage construction does not give 134 = 69 positive + 65 negative'
  Assert-Sequence @($summary.Stages | ForEach-Object { $_.Stage }) @($expectedStages.Name) 'Summary stage order'
  $expectedJSONNames = @(@($expectedStages.Name | ForEach-Object { "$_.json" }) + 'summary.json' | Sort-Object -CaseSensitive)
  $actualJSONNames = @(Get-ChildItem -LiteralPath $runRoot -File -Filter '*.json' | ForEach-Object Name | Sort-Object -CaseSensitive)
  Assert-Sequence $actualJSONNames $expectedJSONNames 'Top-level raw stage JSON set'
  $stageKeys = @('Stage','ExitCode','Output','StandardOutput','StandardError','TimedOut','OutputLimitExceeded','TerminatedIds','DurationSeconds','DeadlineSeconds','Ownership')
  $resourcePattern = '(?i)maxRecDepth|maximum recursion depth|maximum number of heartbeats|heartbeats? exceeded|out of memory|stack overflow|unknown module|unknown package|(?:object file|\.olean)[^\r\n]*(?:does not exist|not found|missing|invalid|corrupt)|(?:failed|unable|cannot) to (?:import|load|open)|failed to synthesize.*(?:module|import)|no such file or directory|permission denied|segmentation fault|access violation|fatal error|process (?:crash|killed)|output.?limit|timed? ?out|deadline exceeded'
  for ($index=0; $index -lt $expectedStages.Count; $index++) {
    $expectedStage = $expectedStages[$index]
    $stage = $summary.Stages[$index]
    $rawPath = Join-Path $runRoot "$($expectedStage.Name).json"
    $raw = Read-JSON $rawPath
    Assert-Keys $stage $stageKeys "$($expectedStage.Name) summary stage"
    Assert-Keys $raw $stageKeys "$($expectedStage.Name) raw stage"
    foreach ($key in $stageKeys) {
      $first = ConvertTo-Json -InputObject $stage[$key] -Depth 30 -Compress
      $second = ConvertTo-Json -InputObject $raw[$key] -Depth 30 -Compress
      Assert-Check ($first -ceq $second) "$($expectedStage.Name): raw/summary mismatch in $key"
    }
    Assert-Check ($stage.ExitCode -is [long] -and $stage.ExitCode -eq $expectedStage.ExitCode) "$($expectedStage.Name): wrong exact exit code"
    foreach ($flag in @('TimedOut','OutputLimitExceeded')) { Assert-Check ($stage[$flag] -is [bool] -and -not $stage[$flag]) "$($expectedStage.Name): $flag not false" }
    foreach ($array in @('Output','StandardOutput','StandardError','TerminatedIds')) { Assert-Check ($stage[$array] -is [array]) "$($expectedStage.Name): $array not an array" }
    Assert-Check ($stage.TerminatedIds.Count -eq 0) "$($expectedStage.Name): process termination occurred"
    Assert-Check ($stage.Ownership -ceq 'kill-on-close-job') "$($expectedStage.Name): unexpected recorded ownership method"
    Assert-Check ($stage.DeadlineSeconds -is [long] -and $stage.DeadlineSeconds -eq 600 -and ($stage.DurationSeconds -is [double] -or $stage.DurationSeconds -is [long]) -and $stage.DurationSeconds -ge 0 -and $stage.DurationSeconds -lt 605) "$($expectedStage.Name): invalid duration/deadline"
    Assert-Sequence @($stage.Output) @(@($stage.StandardOutput) + @($stage.StandardError)) "$($expectedStage.Name) combined streams"
    $joined = $stage.Output -join "`n"
    Assert-Check ($joined -notmatch $resourcePattern) "$($expectedStage.Name): resource/import/operational failure contaminates evidence"
    if ($expectedStage.ExitCode -eq 0) { Assert-Check ($joined -notmatch '(?im)(?:^|: )error:|uncaught exception|LB1-RUNTIME CASE FAIL') "$($expectedStage.Name): positive stage contains error" }
    $hits = @()
    if ($expectedStage.Surface.Length -gt 0) {
      Assert-Check ($stage.StandardError.Count -eq 0) "$($expectedStage.Name): unexpected semantic-check stderr"
      $diagnostics = [regex]::Matches($joined, '(?m)^(.+):([0-9]+):([0-9]+): error:([^\r\n]*)')
      $expectedPath = [IO.Path]::GetFullPath((Join-Path $repo $expectedStage.Path)).Replace('\','/')
      $hits = @($diagnostics | Where-Object {
        $_.Groups[1].Value.Replace('\','/') -ieq $expectedPath -and
        [int]$_.Groups[2].Value -ge $expectedStage.Span.First -and
        [int]$_.Groups[2].Value -le $expectedStage.Span.Last
      } | ForEach-Object { [pscustomobject]@{Line=[int]$_.Groups[2].Value; Column=[int]$_.Groups[3].Value; Message=$_.Groups[4].Value.Trim()} })
      Assert-Check ($hits.Count -gt 0) "$($expectedStage.Name): no diagnostic in $($expectedStage.Path)/$($expectedStage.Surface) [$($expectedStage.Span.First),$($expectedStage.Span.Last)]"
      $semanticHeader = switch -CaseSensitive ($expectedStage.Name) {
        'G02-DELETED-EXACTNESS-producer' { '^Invalid field `query_exact`:' }
        'F01-DELETE-MEMORY-RECOVERY-consumer' { '^Invalid field `memoryRecovery`:' }
        'F02-DELETE-READ-BACKING-consumer' { '^Invalid field `positionalReadBacking`:' }
        { $_ -cin @('D01-NULL-DECODER-producer','D02-WRONG-DECODER-producer') } { '^''change'' tactic failed, pattern$' }
        'D03-ZERO-SERIALIZER-producer' { '^type mismatch, term$' }
        default { '^type mismatch$' }
      }
      Assert-Check (@($hits | Where-Object { $_.Message -cmatch $semanticHeader }).Count -gt 0) "$($expectedStage.Name): intended semantic error class missing at the exact declaration"
      if ($expectedStage.Name -ceq 'S03-SIBLING-BUDGET-consumer') {
        $sibling = '  ∀ (n B : Nat), UniformAllocationBudget n B → shapeCount n ≤ 2 ^ (2 * n + allocationRho n + 1) - 1 : Prop'
        $required = '  ∀ (n B : Nat), UniformAllocationBudget n B → shapeCount n ≤ 2 ^ (B + 1) - 1 : Prop'
        Assert-Check ($stage.Output -ccontains $sibling -and $stage.Output -ccontains $required) 'S03 diagnostic does not expose the canonical-budget sibling Q and frozen uniform-budget P'
      }
    }
    $stageEvidence.Add([pscustomobject]@{Stage=$stage.Stage; ExitCode=$stage.ExitCode; DurationSeconds=$stage.DurationSeconds; RawSHA256=(Get-SHA256 ([IO.File]::ReadAllBytes($rawPath))); Surface=$expectedStage.Surface; Path=$expectedStage.Path; Span=$expectedStage.Span; Diagnostics=$hits})
  }
  $checks.Add('134 stages in exact order; 69 exit-0 and 65 exit-1 outcomes; all individual JSON equals summary; 61 exact semantic declaration spans; no resource/import failures')

  $byStage = @{}
  foreach ($stage in $summary.Stages) { $byStage.Add($stage.Stage,$stage) }
  foreach ($name in @('baseline-inventory','A02-PROOF-ONLY-WRAPPER-inventory')) { Assert-Sequence @($byStage[$name].Output) @($inventoryLine) $name }
  $listExpected = @('LB1-RUNTIME LIST LB1-RUNTIME-V1') + $runtimeIDs + @('LB1-RUNTIME LIST count=6')
  Assert-Sequence @($byStage['runtime-startup'].StandardOutput) $listExpected 'Runtime startup list'
  Assert-Sequence @($byStage['runtime-known-selector'].StandardOutput) @('LB1-RUNTIME CASE PASS R04-ZERO-LENGTH','LB1-RUNTIME PASS version=LB1-RUNTIME-V1 executed=1 expected=1 ids=R04-ZERO-LENGTH') 'Runtime known selector'
  $fullExpected = @($runtimeIDs | ForEach-Object { "LB1-RUNTIME CASE PASS $_" }) + @('LB1-RUNTIME PASS version=LB1-RUNTIME-V1 executed=6 expected=6 ids=' + ($runtimeIDs -join ','))
  Assert-Sequence @($byStage['runtime-full'].StandardOutput) $fullExpected 'Runtime full six cases'
  foreach ($name in @('runtime-startup','runtime-known-selector','runtime-full')) { Assert-Check ($byStage[$name].StandardError.Count -eq 0) "$name emitted stderr" }
  $selectorErrors = @{empty='empty selector'; whitespace='whitespace selector'; malformed='malformed selector channel'; unknown='unknown selector: R99-UNKNOWN'}
  foreach ($name in @('empty','whitespace','malformed','unknown')) {
    $stage = $byStage["runtime-selector-$name"]
    Assert-Sequence @($stage.StandardOutput) @() "Runtime $name selector stdout"
    Assert-Sequence @($stage.StandardError) @("uncaught exception: LB1-RUNTIME $($selectorErrors[$name])") "Runtime $name selector explicit error"
  }
  $checks.Add('Exact runtime list/startup, R04 known selector, four explicit selector rejections before case execution, six full IDs and exact final PASS')

  # Raw bytes come from Git plumbing, never PowerShell's native-command text decoder.
  # Read every tracked Lean file, scripts/*.ps1, build configuration, and the registry.
  $treeBytes = (Invoke-ReadOnlyGit @('ls-tree','-r','-z',$candidate)).Bytes
  $entries = @($utf8.GetString($treeBytes).Split([char]0) | Where-Object { $_.Length -gt 0 } | ForEach-Object {
    Assert-Check ($_ -cmatch '^([0-9]{6}) blob ([0-9a-f]{40})\t(.+)$') 'Unexpected committed tree entry'
    [pscustomobject]@{Mode=$Matches[1]; OID=$Matches[2]; Path=$Matches[3]}
  })
  $sources = @($entries | Where-Object { $_.Path -cmatch '\.lean$|^scripts/.*\.ps1$|^(?:lakefile\.toml|lean-toolchain|\.gitattributes)$' -or $_.Path -ceq $registryPath })
  Assert-Check ($sources.Count -gt 100) 'Unexpectedly small source inventory'
  $objectIDs = @($sources.OID | Select-Object -Unique)
  $batch = (Invoke-ReadOnlyGit @('cat-file','--batch') (($objectIDs -join "`n") + "`n")).Bytes
  $offset=0
  $blobs=@{}
  foreach ($oid in $objectIDs) {
    $end=$offset
    while ($end -lt $batch.Length -and $batch[$end] -ne 10) { $end++ }
    Assert-Check ($end -lt $batch.Length) 'Truncated Git batch header'
    $header=$utf8.GetString($batch,$offset,$end-$offset)
    Assert-Check ($header -cmatch ('^'+$oid+' blob ([0-9]+)$')) 'Invalid Git batch header'
    $length=[int]$Matches[1]
    $offset=$end+1
    Assert-Check ($offset+$length -lt $batch.Length -and $batch[$offset+$length] -eq 10) 'Truncated Git batch blob'
    $bytes=[byte[]]::new($length)
    [Array]::Copy($batch,$offset,$bytes,0,$length)
    $blobs.Add($oid,$bytes)
    $offset += $length+1
  }
  Assert-Check ($offset -eq $batch.Length) 'Unexpected trailing Git batch bytes'
  foreach ($source in $sources) {
    Assert-Check ($source.Mode -cin @('100644','100755')) "Source is not a regular blob: $($source.Path)"
    $path=Join-Path $repo $source.Path
    Assert-SourcePathSafe $path
    Assert-Check ([IO.File]::Exists($path)) "Current source missing: $($source.Path)"
    $committedBytes=$blobs[$source.OID]
    $currentBytes=[IO.File]::ReadAllBytes($path)
    $committedHash=Get-SHA256 $committedBytes
    $currentHash=Get-SHA256 $currentBytes
    $comparison='RAW_BYTES_EQUAL'
    if ($committedHash -cne $currentHash) {
      # Only CRLF to LF is allowed. No BOM removal, trimming, Unicode normalization,
      # lone-CR conversion, or final-newline normalization is performed.
      $left=Convert-LF ($utf8.GetString($committedBytes))
      $right=Convert-LF ($utf8.GetString($currentBytes))
      Assert-Check ($left -ceq $right) "Current source differs beyond CRLF/LF: $($source.Path)"
      $comparison='CRLF_LF_ONLY_RAW_HASHES_DIFFER'
    }
    $sourceEvidence.Add([pscustomobject]@{Path=$source.Path; GitBlob=$source.OID; CommittedRawSHA256=$committedHash; CurrentRawSHA256=$currentHash; Comparison=$comparison})
  }
  foreach ($path in @($producer,$generic)) {
    $artifact=Join-Path $repo ('.lake/build/lib/lean/'+[IO.Path]::ChangeExtension($path,'.olean'))
    Assert-Check ([IO.File]::Exists($artifact)) "Restored artifact currently missing: $artifact"
    $artifactEvidence.Add([pscustomobject]@{Path=$artifact; CurrentRawSHA256=(Get-SHA256 ([IO.File]::ReadAllBytes($artifact))); RestorationBasis='Runner assertion only; pre-run artifact bytes/hashes were not persisted'})
  }
  Assert-Check ((Invoke-ReadOnlyGit @('status','--porcelain=v1','--untracked-files=normal')).Bytes.Length -eq 0) 'Git tree changed during evidence verification'
  $checks.Add("Current raw hashes for $($sources.Count) committed source/configuration files, with only explicit CRLF/LF exceptions; restored artifacts exist; final clean-tree check")
} catch { $failure = $_.Exception.Message }

$report = [ordered]@{
  VerifierVersion=1
  Verdict=$(if ($null -eq $failure) {'EVIDENCE_CONSISTENT'} else {'EVIDENCE_REJECTED'})
  Candidate=$candidate
  RunRoot=$runRoot
  CheckedAtUTC=[DateTime]::UtcNow.ToString('o')
  VerifierSHA256=$scriptHash
  SummaryRawSHA256=$summaryHash
  CommittedRegistrySHA256=$registryHash
  CommittedRunnerSHA256=$runnerHash
  Failure=$failure
  CompletedChecks=@($checks.ToArray())
  CaseCount=63
  ExpectedCaseVerdicts=@{REJECT=61; ACCEPT=2}
  ExpectedStageVerdicts=@{ExitZero=69; ExitOne=65; Total=134}
  RuntimeIDs=$runtimeIDs
  StageEvidence=@($stageEvidence.ToArray())
  CurrentSources=@($sourceEvidence.ToArray())
  CurrentArtifacts=@($artifactEvidence.ToArray())
  Limitations=@(
    'This inspects recorded runner evidence; it does not independently execute Lean, prove diagnostic authenticity, reproduce mutations, or grant coordinator acceptance.',
    'SourceRestored, ArtifactsRestored, CleanTree and per-case restoration are runner assertions. Current source equality and current clean Git status are independently checked; pre-run artifact bytes/hashes were not persisted.',
    'Current source coverage is every tracked .lean, scripts/*.ps1, lakefile.toml, lean-toolchain, .gitattributes, and the exact replay registry. Documentation prose and external toolchain binaries are not source-hash checked.',
    'CRLF/LF-only equality is reported separately from raw byte/hash equality; no other text normalization is accepted.',
    'The 63 cases and six runtime cases are a finite campaign, not a universal mutation or runtime correctness claim.',
    'Separate replay-selector command-boundary, diagnostic-boundary, Windows descendant-timeout and POSIX ownership probes are not independently established by this full-summary verifier.',
    'Exact current HEAD is required; execute after replay restoration and before any subsequent documentation commit. No Lean processes are inspected or controlled.'
  )
}
if ($null -ne $validatedOutputPath) {
  # The only filesystem write in this script: an optional report at a checked ignored path.
  [IO.File]::WriteAllText($validatedOutputPath,(ConvertTo-Json -InputObject $report -Depth 30),$utf8)
}
Write-Output ("LB1-EVIDENCE {0} candidate={1} checks={2} stages={3} sources={4}" -f $report.Verdict,$candidate,$checks.Count,$stageEvidence.Count,$sourceEvidence.Count)
if ($null -ne $failure) { Write-Output "Failure: $failure"; exit 1 }
if ($null -ne $validatedOutputPath) { Write-Output "Report: $validatedOutputPath" }
Write-Output 'Recorded evidence is consistent; independent kernel execution and coordinator acceptance are separate.'
exit 0
