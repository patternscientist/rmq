#!/usr/bin/env pwsh
[CmdletBinding()]
param(
  [string]$OnlyCase = '',
  [string]$LeanPath = '',
  [ValidateRange(30, 3600)][int]$StageDeadlineSeconds = 600,
  [switch]$RegistrySelfTestOnly,
  [switch]$DeadlineSelfTestOnly,
  [switch]$RuntimeOnly
)

$ErrorActionPreference = 'Stop'
Set-StrictMode -Version Latest
. (Join-Path $PSScriptRoot 'owned_process_tree.ps1')
$repoRoot = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot '..'))
$utf8 = [Text.UTF8Encoding]::new($false, $true)
$onlyCaseBound = $PSBoundParameters.ContainsKey('OnlyCase')
$corePath = 'RMQ/Core/WordRAM/Packed/Capstone.lean'
$headlinePath = 'RMQ/Headlines/RMQ.lean'
$consumerPath = 'RMQ/Validation/PackedQueryContract.lean'
$planPath = 'docs/internal/packed_query/PQ1_VALIDATION_PLAN.md'

# This literal registry is checked against the separately frozen Markdown
# contract, the complete source inventory, and the independently typed client.
# It is never generated from the producer or from the Markdown it checks.
$registry = @(
  'C01-ALLOCATION-RESIDUAL|allocationResidualLittleO|REJECT',
  'C02-COMPLETE-RESIDUAL|completeResidualLittleO|REJECT',
  'C03-WIDTH-SCALING|widthBounds|REJECT',
  'C04-DATA-CAPACITY|dataCapacity|REJECT',
  'C05-COMPLETE-CAPACITY|completeCapacity|REJECT',
  'C06-MEMORY-WORDS|memoryWordsFit|REJECT',
  'C07-ALLOCATION-ADDRESSES|allocationAddressesFit|REJECT',
  'C08-DORMANT-FIELDS|programFieldsFit|REJECT',
  'C09-FIXED-BUDGET|budgetExact|REJECT',
  'C10-PROGRAM-LENGTH|programLength|REJECT',
  'C11-ENCODED-PROGRAM|encodedProgramBound|REJECT',
  'C12-REGISTER-COUNT|registerCount|REJECT',
  'C13-SCRATCH-COUNT|scratchCount|REJECT',
  'C14-UNUSED-REGISTERS|unusedRegisters|REJECT',
  'C15-VALID-INPUTS|validInputs|REJECT',
  'C16-TOTAL-NAT-CONTRACT|natContract|REJECT',
  'C17-LEFTMOST|leftmost|REJECT',
  'C18-ACTUAL-RESULT|result|REJECT',
  'C19-ACTUAL-HALT|halt|REJECT',
  'C20-INVALID-GUARD|invalidGuard|REJECT',
  'C21-EXECUTED-STEPS|stepBound|REJECT',
  'C22-CATEGORY-PARTITION|categoryPartition|REJECT',
  'C23-FINAL-STATE|finalStateFit|REJECT',
  'C24-TRANSITION-SAFETY|transitionSafety|REJECT',
  'C25-EVERY-PREFIX|prefixSafety|REJECT',
  'C26-READ-WIDTH|readWidth|REJECT',
  'C27-POSITIONAL-BACKING|positionalReadBacking|REJECT',
  'C28-ORDERED-REFINEMENT|orderedLogicalRefinement|REJECT',
  'C29-READ-ONLY|logicalReadOnly|REJECT',
  'C30-MEMORY-AGREEMENT|suppliedMemoryAgreement|REJECT',
  'P01-PUBLIC-ALIAS-TRUE|replace public proof alias by True.intro|REJECT',
  'A01-UNCHANGED-CONTRACT|unchanged core/export/consumer|ACCEPT'
)
$runtimeIDs = @('S01-EMPTY', 'S02-SINGLE', 'S03-LEFTMOST-TIE', 'S04-SLICE',
  'S05-REVERSED', 'S06-OUT-OF-RANGE', 'S07-WORD-MAX', 'S08-OUTER-CAPACITY',
  'S09-LONG-INTERVAL', 'S10-CORRUPT-METADATA', 'S11-UNREAD-REPLACEMENT')

function Read-Source([string]$RelativePath) {
  return [IO.File]::ReadAllText((Join-Path $repoRoot $RelativePath), $utf8)
}

function Get-MarkedRegion([string]$Text, [string]$Kind) {
  $begin = "  -- PQ1-REPLAY-$Kind-BEGIN"
  $end = "  -- PQ1-REPLAY-$Kind-END"
  if ([regex]::Matches($Text, [regex]::Escape($begin)).Count -ne 1 -or
      [regex]::Matches($Text, [regex]::Escape($end)).Count -ne 1) {
    throw "PQ1-REGISTRY: missing or duplicate $Kind markers"
  }
  $start = $Text.IndexOf("`n", $Text.IndexOf($begin)) + 1
  $finish = $Text.IndexOf($end)
  if ($start -le 0 -or $finish -le $start) { throw "PQ1-REGISTRY: invalid $Kind marker order" }
  return [pscustomobject]@{ Start=$start; End=$finish; Text=$Text.Substring($start, $finish-$start) }
}

function Assert-Registry([string[]]$Cases, [string]$CoreOverride = '') {
  $planRows = @([regex]::Matches((Read-Source $planPath),
    '(?m)^\| ((?:C[0-9]{2}|P01|A01)-[^|]+?) \| ([^|]+?) \| (REJECT|ACCEPT) / PackedQueryContract\.lean \|\r?$') |
    ForEach-Object { $_.Groups[1].Value + '|' + $_.Groups[2].Value + '|' + $_.Groups[3].Value })
  if ($planRows.Count -ne 32 -or $Cases.Count -ne 32 -or
      ($planRows -join "`n") -cne ($Cases -join "`n")) {
    throw 'PQ1-REGISTRY: missing, duplicate, extra, reordered or changed case mapping'
  }
  $core = if ($CoreOverride -eq '') { Read-Source $corePath } else { $CoreOverride }
  $completeFields = [regex]::Matches($core,
    '(?ms)^structure FullyChargedPackedQueryCapstone : Prop where\r?\n(.*?)^set_option maxRecDepth 3000 in\r?$')
  $completeInitializers = [regex]::Matches($core,
    '(?ms)^theorem fullyChargedPackedQueryCapstone_of_runtime_safety\b.*?: FullyChargedPackedQueryCapstone where\r?\n(.*?)(?=^\S|\z)')
  if ($completeFields.Count -ne 1 -or $completeInitializers.Count -ne 1) {
    throw 'PQ1-REGISTRY: complete producer declarations could not be uniquely bounded'
  }
  $fieldNames = @([regex]::Matches((Get-MarkedRegion $core 'FIELDS').Text,
    '(?m)^  ([A-Za-z][A-Za-z0-9]*) :') | ForEach-Object { $_.Groups[1].Value })
  $initializerNames = @([regex]::Matches((Get-MarkedRegion $core 'INITIALIZERS').Text,
    '(?m)^  ([A-Za-z][A-Za-z0-9]*)(?: [^\r\n]*?)? :=') | ForEach-Object { $_.Groups[1].Value })
  $expectedFields = @($Cases[0..29] | ForEach-Object { ($_ -split '\|')[1] })
  $allFields = @([regex]::Matches($completeFields[0].Groups[1].Value,
    '(?m)^  ([A-Za-z][A-Za-z0-9]*) :') | ForEach-Object { $_.Groups[1].Value })
  $allInitializers = @([regex]::Matches($completeInitializers[0].Groups[1].Value,
    '(?m)^  ([A-Za-z][A-Za-z0-9]*)(?: [^\r\n]*?)? :=') | ForEach-Object { $_.Groups[1].Value })
  if ($fieldNames.Count -ne 30 -or $initializerNames.Count -ne 30 -or
      ($fieldNames -join '|') -cne ($expectedFields -join '|') -or
      ($initializerNames -join '|') -cne ($expectedFields -join '|') -or
      ($allFields -join '|') -cne ($fieldNames -join '|') -or
      ($allInitializers -join '|') -cne ($initializerNames -join '|')) {
    throw 'PQ1-REGISTRY: source field/initializer inventory differs from frozen registry'
  }
  $consumerNames = @([regex]::Matches((Read-Source $consumerPath),
    '(?m)^theorem check(C[0-9]{2})\b') | ForEach-Object { $_.Groups[1].Value })
  $expectedChecks = @($Cases[0..29] | ForEach-Object { ($_ -split '-')[0] })
  if (($consumerNames -join '|') -cne ($expectedChecks -join '|')) {
    throw 'PQ1-REGISTRY: independent consumer inventory differs from frozen registry'
  }
}

function Select-Cases([string[]]$Cases, [bool]$WasBound, [string]$Selector) {
  Assert-Registry $Cases
  if (-not $WasBound) { return $Cases }
  if ([string]::IsNullOrWhiteSpace($Selector)) { throw 'PQ1-SELECTOR: explicitly empty selector' }
  $selected = @($Cases | Where-Object { ($_ -split '\|')[0] -ceq $Selector })
  if ($selected.Count -ne 1) { throw "PQ1-SELECTOR: unknown selector $Selector" }
  return $selected
}

function Expect-Rejection([scriptblock]$Action, [string]$Prefix) {
  $message = $null
  try { & $Action | Out-Null } catch { $message = $_.Exception.Message }
  if ($null -eq $message -or -not $message.StartsWith($Prefix)) {
    throw "PQ1-SELFTEST: expected $Prefix rejection; received '$message'"
  }
}

function Assert-RuntimeIDs([string[]]$IDs) {
  $section = [regex]::Matches((Read-Source $planPath),
    '(?s)## Runtime registry\r?\n(.*?)\r?\nAll expect')
  if ($section.Count -ne 1) { throw 'PQ1-RUNTIME-REGISTRY: missing unique frozen section' }
  $planIDs = @([regex]::Matches($section[0].Groups[1].Value, 'S[0-9]{2}-[A-Z-]+') |
    ForEach-Object { $_.Value })
  if (($planIDs -join '|') -cne ($runtimeIDs -join '|') -or
      ($IDs -join '|') -cne ($runtimeIDs -join '|')) {
    throw 'PQ1-RUNTIME-REGISTRY: missing, duplicate, changed or reordered runtime IDs'
  }
}

function Get-ConsumerTypeErrors([string]$Output) {
  $errors = [regex]::Matches($Output,
    '(?m)^RMQ[/\\]Validation[/\\]PackedQueryContract\.lean:(\d+):\d+: error:([^\r\n]*)')
  if ($errors.Count -eq 0) { throw 'PQ1-REJECTION: no typed-client diagnostics' }
  foreach ($diagnostic in $errors) {
    if ($diagnostic.Groups[2].Value -notmatch '^\s*(type mismatch|application type mismatch|function expected|invalid field|invalid projection|Application type mismatch|Type mismatch)\b') {
      throw 'PQ1-REJECTION: unrecognized diagnostic cannot count as type rejection'
    }
  }
  # Resource/setup failures can accompany an ordinary type mismatch. Inspect
  # the complete output as well as whitelisting each located diagnostic.
  if ($Output -match 'deep recursion|stack overflow|internal exception|interrupted|unknown module|object file.*does not exist|maximum.*(recursion|heartbeats)|out of memory') {
    throw 'PQ1-REJECTION: setup/resource failure cannot count as type rejection'
  }
  return $errors
}

function Invoke-RegistryTests {
  Assert-Registry $registry
  Expect-Rejection { Assert-Registry @($registry[1..31]) } 'PQ1-REGISTRY:'
  Expect-Rejection { Assert-Registry @($registry[0..30] + $registry[0]) } 'PQ1-REGISTRY:'
  Expect-Rejection { Assert-Registry @($registry + 'EXTRA|bad|REJECT') } 'PQ1-REGISTRY:'
  $reordered = @($registry); $reordered[0] = $registry[1]; $reordered[1] = $registry[0]
  Expect-Rejection { Assert-Registry $reordered } 'PQ1-REGISTRY:'
  $extraField = (Read-Source $corePath).Replace('  -- PQ1-REPLAY-FIELDS-END',
    "  -- PQ1-REPLAY-FIELDS-END`n  unregisteredField : True")
  Expect-Rejection { Assert-Registry $registry $extraField } 'PQ1-REGISTRY:'
  $extraInitializer = (Read-Source $corePath).Replace('  -- PQ1-REPLAY-INITIALIZERS-END',
    "  -- PQ1-REPLAY-INITIALIZERS-END`n  unregisteredField := True.intro")
  Expect-Rejection { Assert-Registry $registry $extraInitializer } 'PQ1-REGISTRY:'
  foreach ($bad in @('', ' ', "`t", 'UNKNOWN')) {
    Expect-Rejection { Select-Cases $registry $true $bad } 'PQ1-SELECTOR:'
  }
  $control = @(Select-Cases $registry $true 'A01-UNCHANGED-CONTRACT')
  $full = @(Select-Cases $registry $false '')
  if ($control.Count -ne 1 -or $control[0] -cne $registry[31] -or $full.Count -ne 32) {
    throw 'PQ1-SELFTEST: focused/full selector control failed'
  }
  Assert-RuntimeIDs $runtimeIDs
  Expect-Rejection { Assert-RuntimeIDs @($runtimeIDs[1..10]) } 'PQ1-RUNTIME-REGISTRY:'
  Expect-Rejection { Assert-RuntimeIDs @($runtimeIDs[0..9] + $runtimeIDs[0]) } 'PQ1-RUNTIME-REGISTRY:'
  $reorderedRuntime = @($runtimeIDs); $reorderedRuntime[0] = $runtimeIDs[1]; $reorderedRuntime[1] = $runtimeIDs[0]
  Expect-Rejection { Assert-RuntimeIDs $reorderedRuntime } 'PQ1-RUNTIME-REGISTRY:'
  foreach ($diagnostic in @('(kernel) deep recursion detected', 'stack overflow',
      'internal exception', 'interrupted', 'unknown module Missing', 'maximum heartbeats exceeded')) {
    Expect-Rejection { Get-ConsumerTypeErrors "RMQ/Validation/PackedQueryContract.lean:18:1: error: $diagnostic" } 'PQ1-REJECTION:'
  }
  foreach ($diagnostic in @('type mismatch', 'application type mismatch', 'function expected', 'invalid field')) {
    $positive = @(Get-ConsumerTypeErrors "RMQ/Validation/PackedQueryContract.lean:18:1: error: $diagnostic")
    if ($positive.Count -ne 1) { throw 'PQ1-SELFTEST: diagnostic success control failed' }
  }
  Write-Host 'PQ1-REGISTRY SELF-TEST PASS missing/duplicate/extra/reordered/outside-markers/empty/whitespace/unknown/focused/full'
  Write-Host 'PQ1-REJECTION SELF-TEST PASS runtime IDs and typed/resource diagnostic controls'
}

# Selection precedes tool resolution or any child process. Even self-test
# modes reject an explicitly malformed production selector.
$selectedCases = @(Select-Cases $registry $onlyCaseBound $OnlyCase)
if ($RegistrySelfTestOnly) { Invoke-RegistryTests; exit 0 }
if (($RuntimeOnly -or $DeadlineSelfTestOnly) -and $onlyCaseBound) {
  throw 'PQ1-SELECTOR: OnlyCase cannot be combined with runtime/deadline mode'
}

$runRoot = Join-Path $repoRoot ('.lake/pq1-replay/run-' + [Guid]::NewGuid().ToString('N'))
[void][IO.Directory]::CreateDirectory($runRoot)
$stageResults = [Collections.Generic.List[object]]::new()

function Invoke-Stage([string]$File, [string[]]$Arguments, [string]$Stage,
    [int]$Deadline = $StageDeadlineSeconds, [hashtable]$Environment = @{}) {
  $result = Invoke-RMQOwnedBoundedProcess -FilePath $File -Arguments $Arguments `
    -WorkingDirectory $repoRoot -Stage $Stage -DeadlineSeconds $Deadline `
    -OutputLimitBytes 8388608 -TempRoot $runRoot -Environment $Environment
  $stageResults.Add($result)
  [IO.File]::WriteAllText((Join-Path $runRoot ($Stage + '.json')),
    ($result | ConvertTo-Json -Depth 8), $utf8)
  if ($result.TimedOut -or $result.OutputLimitExceeded) {
    throw "PQ1-STAGE: $Stage exceeded its deadline/output limit; this is never expected type rejection"
  }
  return $result
}

function Invoke-DeadlineTest {
  Invoke-RMQOwnedProcessDeterministicTests
  $shellPath = (Get-Process -Id $PID).Path
  $pidPath = Join-Path $runRoot 'deadline-grandchild.pid'
  $fixturePath = Join-Path $runRoot 'deadline-fixture.ps1'
  $quotedShell = $shellPath.Replace("'", "''")
  $quotedPid = $pidPath.Replace("'", "''")
  $fixture = @"
`$options = @{ FilePath='$quotedShell'; ArgumentList=@('-NoProfile','-Command','Start-Sleep -Seconds 120'); PassThru=`$true }
if (`$env:OS -eq 'Windows_NT') { `$options.WindowStyle = 'Hidden' }
`$child = Start-Process @options
[IO.File]::WriteAllText('$quotedPid', [string]`$child.Id)
Start-Sleep -Seconds 120
"@
  [IO.File]::WriteAllText($fixturePath, $fixture, $utf8)
  $result = Invoke-RMQOwnedBoundedProcess -FilePath $shellPath `
    -Arguments @('-NoProfile','-ExecutionPolicy','Bypass','-File',$fixturePath) `
    -WorkingDirectory $repoRoot -Stage 'deadline-descendant' -DeadlineSeconds 8 `
    -OutputLimitBytes 1048576 -TempRoot $runRoot
  $stageResults.Add($result)
  [IO.File]::WriteAllText((Join-Path $runRoot 'deadline-descendant.json'),
    ($result | ConvertTo-Json -Depth 8), $utf8)
  if (-not $result.TimedOut -or -not [IO.File]::Exists($pidPath)) {
    throw 'PQ1-DEADLINE: deadline was not exercised with a live descendant'
  }
  $childId = [int][IO.File]::ReadAllText($pidPath)
  if ($null -ne (Get-Process -Id $childId -ErrorAction SilentlyContinue)) {
    throw "PQ1-DEADLINE: owned descendant $childId survived termination"
  }
  Write-Host "PQ1-DEADLINE SELF-TEST PASS descendant=$childId absent after owned deadline"
}

if ($DeadlineSelfTestOnly) { Invoke-DeadlineTest; exit 0 }
if ([string]::IsNullOrEmpty($LeanPath)) { $LeanPath = Resolve-RMQScalarApplicationPath (Get-Command lean -CommandType Application) 'lean' }
$gitPath = Resolve-RMQScalarApplicationPath (Get-Command git -CommandType Application) 'git'
$cacheRoot = Join-Path $repoRoot '.lake/build/lib/lean'
$leanEnvironment = @{ LEAN_PATH=$cacheRoot }

function Assert-Clean([string]$Stage) {
  $state = Get-RMQRepositoryStateBounded -RepositoryRoot $repoRoot -GitPath $gitPath `
    -DeadlineSeconds 30 -OutputLimitBytes 1048576 -TempRoot $runRoot -StagePrefix $Stage
  Assert-RMQCleanRepositoryStateText $state $Stage
}

function Invoke-Lean([string]$Path, [string]$Stage) {
  $outputPath = Join-Path $cacheRoot ([IO.Path]::ChangeExtension($Path, '.olean'))
  [void][IO.Directory]::CreateDirectory([IO.Path]::GetDirectoryName($outputPath))
  return Invoke-Stage $LeanPath @('-o', $outputPath, $Path) $Stage $StageDeadlineSeconds $leanEnvironment
}

function Require-Pass([object]$Result) {
  if ($Result.ExitCode -ne 0) {
    throw "PQ1-STAGE: $($Result.Stage) failed before an expected consumer rejection: $($Result.Output -join ' | ')"
  }
}

function Build-Public([string]$Stage) {
  Require-Pass (Invoke-Lean $corePath "$Stage-core")
  Require-Pass (Invoke-Lean $headlinePath "$Stage-headline")
  Require-Pass (Invoke-Lean 'RMQPaper.lean' "$Stage-root")
}

function Weaken-Field([string]$Text, [string]$Kind, [string]$Field) {
  $region = Get-MarkedRegion $Text $Kind
  $pattern = if ($Kind -eq 'FIELDS') { '(?m)^  ([A-Za-z][A-Za-z0-9]*) :' } else {
    '(?m)^  ([A-Za-z][A-Za-z0-9]*)(?: [^\r\n]*?)? :=' }
  $entries = [regex]::Matches($region.Text, $pattern)
  $target = @($entries | Where-Object { $_.Groups[1].Value -ceq $Field })
  if ($target.Count -ne 1) { throw "PQ1-MUTATION: expected one $Kind entry for $Field" }
  $start = $target[0].Index
  $next = @($entries | Where-Object { $_.Index -gt $start } | Select-Object -First 1)
  $end = if ($next.Count -eq 0) { $region.Text.Length } else { $next[0].Index }
  $newline = if ($region.Text.Contains("`r`n")) { "`r`n" } else { "`n" }
  $replacement = if ($Kind -eq 'FIELDS') { "  $Field : True$newline" } else { "  $Field := True.intro$newline" }
  return $Text.Substring(0, $region.Start + $start) + $replacement + $Text.Substring($region.Start + $end)
}

function Assert-ConsumerRejection([object]$Result, [string]$Check, [bool]$PublicMutation) {
  if ($Result.ExitCode -eq 0) { throw "PQ1-MUTATION: $Check was accepted" }
  $source = Read-Source $consumerPath
  $decls = [regex]::Matches($source, '(?m)^theorem ([A-Za-z][A-Za-z0-9]*)\b')
  $target = @($decls | Where-Object { $_.Groups[1].Value -ceq $Check })
  if ($target.Count -ne 1) { throw "PQ1-MUTATION: missing exact consumer $Check" }
  $startLine = ($source.Substring(0, $target[0].Index) -split "`n").Count
  $next = @($decls | Where-Object { $_.Index -gt $target[0].Index } | Select-Object -First 1)
  $endLine = if ($next.Count -eq 0) { ($source -split "`n").Count + 1 } else {
    ($source.Substring(0, $next[0].Index) -split "`n").Count }
  $errors = @(Get-ConsumerTypeErrors ($Result.Output -join "`n"))
  $atTarget = @($errors | Where-Object { [int]$_.Groups[1].Value -ge $startLine -and [int]$_.Groups[1].Value -lt $endLine })
  if ($atTarget.Count -eq 0 -or (-not $PublicMutation -and $atTarget.Count -ne $errors.Count)) {
    throw "PQ1-MUTATION: rejection did not occur at the exact $Check consumer surface"
  }
}

function Invoke-Runtime {
  $result = Invoke-Stage $LeanPath @('--run', 'RMQ/Validation/PackedQueryRuntime.lean') `
    'runtime-full' $StageDeadlineSeconds $leanEnvironment
  Require-Pass $result
  $actualIDs = @([regex]::Matches(($result.Output -join "`n"),
    '(?m)^PQ1-RUNTIME CASE (S[0-9]{2}-[A-Z-]+) PASS ') | ForEach-Object { $_.Groups[1].Value })
  Assert-RuntimeIDs $actualIDs
  if (@($result.Output | Where-Object { $_ -ceq 'PQ1-RUNTIME PASS cases=11' }).Count -ne 1) {
    throw 'PQ1-RUNTIME: full run did not report exactly all eleven fixtures'
  }
  foreach ($selector in @('', ' ', 'UNKNOWN')) {
    $label = if ($selector -eq 'UNKNOWN') { 'unknown' } elseif ($selector -eq '') { 'empty' } else { 'whitespace' }
    $bad = Invoke-Stage $LeanPath @('--run', 'RMQ/Validation/PackedQueryRuntime.lean', $selector) `
      "runtime-selector-$label" $StageDeadlineSeconds $leanEnvironment
    if ($bad.ExitCode -eq 0 -or ($bad.Output -join "`n") -notmatch 'PQ1-RUNTIME (explicitly empty|unknown) selector' -or
        ($bad.Output -join "`n") -match 'PQ1-RUNTIME CASE ') { throw "PQ1-RUNTIME: selector $label control failed" }
  }
  Write-Host 'PQ1-RUNTIME PASS full registry and invalid-selector controls'
}

Assert-Clean 'baseline'
$commit = @(Invoke-RMQCheckedGit $gitPath $repoRoot @('rev-parse','HEAD') 'source-commit' 30 1048576 $runRoot)[0]
$saved = @{}
foreach ($path in @($corePath, $headlinePath, $consumerPath, 'RMQPaper.lean', $planPath, 'scripts/packed_query_replay.ps1')) {
  $saved[$path] = [IO.File]::ReadAllBytes((Join-Path $repoRoot $path))
}
$caseResults = [Collections.Generic.List[object]]::new()
$completed = $false
try {
  if ($RuntimeOnly) { Invoke-Runtime } else {
    Invoke-RegistryTests
    if (-not $onlyCaseBound) { Invoke-DeadlineTest }
    Build-Public 'baseline'
    Require-Pass (Invoke-Lean $consumerPath 'baseline-consumer')
    foreach ($entry in $selectedCases) {
      $parts = $entry -split '\|'
      $id = $parts[0]; $field = $parts[1]; $verdict = $parts[2]
      try {
        if ($id.StartsWith('C')) {
          $text = $utf8.GetString($saved[$corePath])
          $text = Weaken-Field $text 'FIELDS' $field
          $text = Weaken-Field $text 'INITIALIZERS' $field
          [IO.File]::WriteAllText((Join-Path $repoRoot $corePath), $text, $utf8)
        } elseif ($id -eq 'P01-PUBLIC-ALIAS-TRUE') {
          $text = $utf8.GetString($saved[$headlinePath])
          $pattern = '(?ms)^-- PQ1-REPLAY-PUBLIC-BEGIN\r?\n.*?^-- PQ1-REPLAY-PUBLIC-END'
          if ([regex]::Matches($text, $pattern).Count -ne 1) { throw 'PQ1-MUTATION: public alias markers missing/duplicate' }
          $replacement = "-- PQ1-REPLAY-PUBLIC-BEGIN`nabbrev succinctRMQFullyChargedPackedQuery : True := True.intro`n-- PQ1-REPLAY-PUBLIC-END"
          [IO.File]::WriteAllText((Join-Path $repoRoot $headlinePath), [regex]::Replace($text, $pattern, $replacement), $utf8)
        }
        Build-Public $id
        $result = Invoke-Lean $consumerPath "$id-consumer"
        if ($verdict -eq 'ACCEPT') { Require-Pass $result } else {
          $check = if ($id.StartsWith('C')) { 'check' + ($id -split '-')[0] } else { 'publicContract' }
          Assert-ConsumerRejection $result $check ($id.StartsWith('P'))
        }
        $caseResults.Add([pscustomobject]@{ Id=$id; Field=$field; Expected=$verdict; Actual=$verdict; Surface=$consumerPath })
      } finally {
        foreach ($path in @($corePath, $headlinePath)) { [IO.File]::WriteAllBytes((Join-Path $repoRoot $path), $saved[$path]) }
        foreach ($path in $saved.Keys) {
          $bytes = [IO.File]::ReadAllBytes((Join-Path $repoRoot $path))
          if ([Convert]::ToBase64String($bytes) -cne [Convert]::ToBase64String($saved[$path])) {
            throw "PQ1-RESTORE: byte mismatch in $path"
          }
        }
        Build-Public "$id-restored"
        Require-Pass (Invoke-Lean $consumerPath "$id-restored-consumer")
        Assert-Clean "$id-clean"
      }
      Write-Host "PQ1-REPLAY CASE $id PASS expected=$verdict surface=$consumerPath restored=true"
    }
    if (-not $onlyCaseBound) { Invoke-Runtime }
  }
  Assert-Clean 'final'
  $completed = $true
} finally {
  $hashes = [ordered]@{}
  foreach ($path in $saved.Keys) {
    $hasher = [Security.Cryptography.SHA256]::Create()
    try { $hashes[$path] = ([BitConverter]::ToString($hasher.ComputeHash($saved[$path]))).Replace('-','').ToLowerInvariant() }
    finally { $hasher.Dispose() }
  }
  $report = [ordered]@{ SourceCommit=$commit; Completed=$completed; Registry=$registry; Selected=$selectedCases;
    Cases=@($caseResults.ToArray()); SourceHashes=$hashes; Stages=@($stageResults.ToArray()); ReportDirectory=$runRoot }
  [IO.File]::WriteAllText((Join-Path $runRoot 'report.json'), ($report | ConvertTo-Json -Depth 12), $utf8)
  Write-Host "PQ1-REPLAY REPORT $runRoot/report.json"
}
Write-Host "PQ1-REPLAY PASS source=$commit cases=$($caseResults.Count) clean=true"
