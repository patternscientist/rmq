#!/usr/bin/env pwsh
[CmdletBinding()]
param(
  [string]$OnlyCase = '',
  [string]$LeanPath = '',
  [ValidateRange(30, 3600)][int]$StageDeadlineSeconds = 600,
  [ValidateRange(30, 7200)][int]$RuntimeDeadlineSeconds = 1200,
  [ValidateRange(60, 7200)][int]$ProducerRebuildDeadlineSeconds = 2400,
  [switch]$RegistrySelfTestOnly,
  [switch]$DeadlineSelfTestOnly,
  [switch]$SelectorProbeOnly,
  [switch]$SelectorBoundarySelfTestOnly,
  [switch]$ProvenanceSelfTestOnly,
  [ValidatePattern('^[0-9A-Za-z][0-9A-Za-z._/~^-]*$')][string]$ProvenanceRevision = 'HEAD',
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
$runtimePath = 'RMQ/Validation/PackedQueryRuntime.lean'
$arrayRunPath = 'RMQ/Core/WordRAM/Packed/ArrayRun.lean'
$primitivePath = 'RMQ/Core/WordRAM/Packed/Primitive.lean'
$planPath = 'docs/internal/packed_query/PQ1_VALIDATION_PLAN.md'
$experimentPath = 'docs/internal/packed_query/experiment-rc6'
$runtimeSelectorVariable = 'PQ1_RUNTIME_SELECTOR'
# The runtime selector channel is inherited by every Lean child, so a stale
# value in the caller's environment must never turn a full run into a focused one.
[Environment]::SetEnvironmentVariable($runtimeSelectorVariable, $null, 'Process')

# This literal registry is checked against the separately frozen Markdown
# contract, the complete source inventory, and the independently typed client.
# It is never generated from the producer or from the Markdown it checks.
# Columns: case ID | exact target | expected verdict | rejecting surface.
$registry = @(
  'C01-ALLOCATION-RESIDUAL|allocationResidualLittleO|REJECT|PackedQueryContract.lean',
  'C02-COMPLETE-RESIDUAL|completeResidualLittleO|REJECT|PackedQueryContract.lean',
  'C03-WIDTH-SCALING|widthBounds|REJECT|PackedQueryContract.lean',
  'C04-DATA-CAPACITY|dataCapacity|REJECT|PackedQueryContract.lean',
  'C05-COMPLETE-CAPACITY|completeCapacity|REJECT|PackedQueryContract.lean',
  'C06-MEMORY-WORDS|memoryWordsFit|REJECT|PackedQueryContract.lean',
  'C07-ALLOCATION-ADDRESSES|allocationAddressesFit|REJECT|PackedQueryContract.lean',
  'C08-DORMANT-FIELDS|programFieldsFit|REJECT|PackedQueryContract.lean',
  'C09-FIXED-BUDGET|budgetExact|REJECT|PackedQueryContract.lean',
  'C10-PROGRAM-LENGTH|programLength|REJECT|PackedQueryContract.lean',
  'C11-ENCODED-PROGRAM|encodedProgramBound|REJECT|PackedQueryContract.lean',
  'C12-REGISTER-COUNT|registerCount|REJECT|PackedQueryContract.lean',
  'C13-SCRATCH-COUNT|scratchCount|REJECT|PackedQueryContract.lean',
  'C14-UNUSED-REGISTERS|unusedRegisters|REJECT|PackedQueryContract.lean',
  'C15-VALID-INPUTS|validInputs|REJECT|PackedQueryContract.lean',
  'C16-TOTAL-NAT-CONTRACT|natContract|REJECT|PackedQueryContract.lean',
  'C17-LEFTMOST|leftmost|REJECT|PackedQueryContract.lean',
  'C18-ACTUAL-RESULT|result|REJECT|PackedQueryContract.lean',
  'C19-ACTUAL-HALT|halt|REJECT|PackedQueryContract.lean',
  'C20-INVALID-GUARD|invalidGuard|REJECT|PackedQueryContract.lean',
  'C21-EXECUTED-STEPS|stepBound|REJECT|PackedQueryContract.lean',
  'C22-CATEGORY-PARTITION|categoryPartition|REJECT|PackedQueryContract.lean',
  'C23-FINAL-STATE|finalStateFit|REJECT|PackedQueryContract.lean',
  'C24-TRANSITION-SAFETY|transitionSafety|REJECT|PackedQueryContract.lean',
  'C25-EVERY-PREFIX|prefixSafety|REJECT|PackedQueryContract.lean',
  'C26-READ-WIDTH|readWidth|REJECT|PackedQueryContract.lean',
  'C27-POSITIONAL-BACKING|positionalReadBacking|REJECT|PackedQueryContract.lean',
  'C28-ORDERED-REFINEMENT|orderedLogicalRefinement|REJECT|PackedQueryContract.lean',
  'C29-READ-ONLY|logicalReadOnly|REJECT|PackedQueryContract.lean',
  'C30-MEMORY-AGREEMENT|suppliedMemoryAgreement|REJECT|PackedQueryContract.lean',
  'C31-SPEC-RESULT|specResult|REJECT|PackedQueryContract.lean',
  'C32-NO-FAILED-LOADS|noFailedLoads|REJECT|PackedQueryContract.lean',
  'C33-INVALID-GUARD-STEPS|invalidGuardSteps|REJECT|PackedQueryContract.lean',
  'P01-PUBLIC-ALIAS-TRUE|replace public proof alias by True.intro|REJECT|PackedQueryContract.lean',
  'A01-UNCHANGED-CONTRACT|unchanged core/export/consumer|ACCEPT|PackedQueryContract.lean',
  'D01-CATEGORY-COLLAPSE|Instruction.category non-load arms collapsed to control|REJECT|PackedQueryContract.lean',
  'R01-SPEC-PROJECTION|specResult packet changed from answer plus one to plus two|REJECT|Capstone.lean',
  'N01-WRONG-EXPECTED|runtime fixture with a wrong literal answer|REJECT|PackedQueryRuntime.lean'
)
$registryCount = 38
$fieldCaseCount = 33
$runtimeIDs = @('S01-EMPTY', 'S02-SINGLE', 'S03-LEFTMOST-TIE', 'S04-SLICE',
  'S05-REVERSED', 'S06-OUT-OF-RANGE', 'S07-WORD-MAX', 'S08-OUTER-CAPACITY',
  'S09-LONG-INTERVAL', 'S10-CORRUPT-METADATA', 'S11-UNREAD-REPLACEMENT',
  'S12-EMPTY-INTERVAL', 'S13-CROSS-BLOCK', 'S14-SAME-BLOCK', 'S15-ADJACENT-BLOCKS')
$runtimeNegativeIDs = @('N01-WRONG-EXPECTED')
$runtimeListRunIDs = @('S02-SINGLE', 'S05-REVERSED')
# Definitions reachable from the field types whose change need not break a
# producer proof. Each has one rfl pin in the consumer, in this order.
$pinInventory = @('pinMemory', 'pinRegisters', 'pinProgram', 'pinStateShape',
  'pinReceiptShape', 'pinTransitionShape', 'pinRunShape', 'pinRegistersWrite',
  'pinArithmeticEval', 'pinComparisonEval', 'pinArithmeticCode', 'pinComparisonCode',
  'pinInstructionCategory', 'pinInstructionOperands', 'pinInstructionEncoding',
  'pinInstructionFits', 'pinStateWriteNext', 'pinExecute', 'pinStep', 'pinRunZero',
  'pinRunSucc', 'pinRunReads', 'pinRunCategories', 'pinRunSteps', 'pinRunResult',
  'pinRunCategoryCount', 'pinStateFits', 'pinInstructionSafe', 'pinInputRegisters',
  'pinInitialState', 'pinEncodeInputs', 'pinQueryNat', 'pinValidRange',
  'pinLeftmostArgMin', 'pinOptionNatPacket', 'pinLittleOLinear', 'pinReadOnlyTrace',
  'pinIsReadWord')
# Literal definition collapses. The source text is ASCII apart from the arrow.
$arrow = [string][char]0x2192
$definitionCollapses = @{
  'D01-CATEGORY-COLLAPSE' = [pscustomobject]@{
    File = $primitivePath
    Original = ("def Instruction.category : Instruction $arrow Category`n" +
      "  | .load .. => .memoryRead`n" +
      "  | .constant .. | .move .. => .registerWrite`n" +
      "  | .arithmetic .. => .arithmetic`n" +
      "  | .comparison .. => .comparison`n" +
      "  | .jump .. | .jumpRegister .. | .branchZero .. => .branch`n" +
      "  | .halt .. => .control`n")
    Replacement = ("def Instruction.category : Instruction $arrow Category`n" +
      "  | .load .. => .memoryRead`n" +
      "  | _ => .control`n")
    Check = 'pinInstructionCategory'
  }
}
$projectionMutations = @{
  'R01-SPEC-PROJECTION' = [pscustomobject]@{
    File = $corePath
    Original = 'some (scanWindow xs left (right - left) + 1)'
    Replacement = 'some (scanWindow xs left (right - left) + 2)'
    Initializer = 'specResult'
  }
}
$experimentEntryCount = 45

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

# Match a literal source excerpt against either checkout line-ending style.
function Convert-ToSourceNewlines([string]$Text, [string]$Excerpt) {
  if ($Text.Contains("`r`n")) { return $Excerpt.Replace("`n", "`r`n") }
  return $Excerpt
}

function Get-UniqueIndex([string]$Text, [string]$Excerpt, [string]$Label) {
  $first = $Text.IndexOf($Excerpt, [StringComparison]::Ordinal)
  if ($first -lt 0 -or
      $Text.IndexOf($Excerpt, $first + $Excerpt.Length, [StringComparison]::Ordinal) -ge 0) {
    throw "PQ1-REGISTRY: $Label excerpt is missing or not unique"
  }
  return $first
}

function Replace-Unique([string]$Text, [string]$Original, [string]$Replacement, [string]$Label) {
  $excerpt = Convert-ToSourceNewlines $Text $Original
  $at = Get-UniqueIndex $Text $excerpt $Label
  return $Text.Substring(0, $at) + (Convert-ToSourceNewlines $Text $Replacement) +
    $Text.Substring($at + $excerpt.Length)
}

function Get-CaseParts([string]$Entry) {
  $parts = $Entry -split '\|'
  return [pscustomobject]@{ Id=$parts[0]; Target=$parts[1]; Verdict=$parts[2]; Surface=$parts[3] }
}

function Get-CertificateMemberNames([string]$Body) {
  # This early source-format check puts every known member at two spaces and every
  # continuation at four or more. Inventory every member-leading token, not
  # merely tokens matching an ASCII Lean-name subset. Unknown spelling then
  # fails the literal registry comparison; unsupported layout fails here.
  # Lean also admits more-indented fields: the elaborated metadata check after
  # baseline compilation is the authoritative complete field inventory.
  foreach ($line in [regex]::Split($Body, '\r?\n')) {
    if ($line -match '^\s*$' -or $line -match '^  --') { continue }
    if ($line -match '^  (\S+)') { $Matches[1]; continue }
    if ($line -match '^ {4,}\S') { continue }
    throw 'PQ1-REGISTRY: unsupported certificate member layout'
  }
}

function Assert-Registry([string[]]$Cases, [string]$CoreOverride = '', [string]$ConsumerOverride = '') {
  $planRows = @([regex]::Matches((Read-Source $planPath),
    '(?m)^\| ((?:C[0-9]{2}|P01|A01|D[0-9]{2}|R[0-9]{2}|N[0-9]{2})-[^|]+?) \| ([^|]+?) \| (REJECT|ACCEPT) / ([A-Za-z]+\.lean) \|\r?$') |
    ForEach-Object { $_.Groups[1].Value + '|' + $_.Groups[2].Value + '|' + $_.Groups[3].Value + '|' + $_.Groups[4].Value })
  if ($planRows.Count -ne $registryCount -or $Cases.Count -ne $registryCount -or
      ($planRows -join "`n") -cne ($Cases -join "`n")) {
    throw 'PQ1-REGISTRY: missing, duplicate, extra, reordered or changed case mapping'
  }
  $fieldCases = @($Cases[0..($fieldCaseCount - 1)])
  if (@($fieldCases | Where-Object { -not $_.StartsWith('C') }).Count -ne 0 -or
      @($Cases | Where-Object { $_.StartsWith('C') }).Count -ne $fieldCaseCount) {
    throw 'PQ1-REGISTRY: field cases must be exactly the leading C entries'
  }
  $core = if ($CoreOverride -eq '') { Read-Source $corePath } else { $CoreOverride }
  $completeFields = [regex]::Matches($core,
    '(?ms)^structure FullyChargedPackedQueryCapstone : Prop where\r?\n(.*?)^set_option maxRecDepth 3000 in\r?$')
  $completeInitializers = [regex]::Matches($core,
    '(?ms)^theorem fullyChargedPackedQueryCapstone_of_runtime_safety\b.*?: FullyChargedPackedQueryCapstone where\r?\n(.*?)(?=^\S|\z)')
  if ($completeFields.Count -ne 1 -or $completeInitializers.Count -ne 1) {
    throw 'PQ1-REGISTRY: complete producer declarations could not be uniquely bounded'
  }
  $fieldNames = @(Get-CertificateMemberNames (Get-MarkedRegion $core 'FIELDS').Text)
  $initializerNames = @(Get-CertificateMemberNames (Get-MarkedRegion $core 'INITIALIZERS').Text)
  $expectedFields = @($fieldCases | ForEach-Object { (Get-CaseParts $_).Target })
  $allFields = @(Get-CertificateMemberNames $completeFields[0].Groups[1].Value)
  $allInitializers = @(Get-CertificateMemberNames $completeInitializers[0].Groups[1].Value)
  if ($fieldNames.Count -ne $fieldCaseCount -or $initializerNames.Count -ne $fieldCaseCount -or
      ($fieldNames -join '|') -cne ($expectedFields -join '|') -or
      ($initializerNames -join '|') -cne ($expectedFields -join '|') -or
      ($allFields -join '|') -cne ($fieldNames -join '|') -or
      ($allInitializers -join '|') -cne ($initializerNames -join '|')) {
    throw 'PQ1-REGISTRY: source field/initializer inventory differs from frozen registry'
  }
  $consumer = if ($ConsumerOverride -eq '') { Read-Source $consumerPath } else { $ConsumerOverride }
  $consumerNames = @([regex]::Matches($consumer,
    '(?m)^theorem check(C[0-9]{2})\b') | ForEach-Object { $_.Groups[1].Value })
  $expectedChecks = @($fieldCases | ForEach-Object { ((Get-CaseParts $_).Id -split '-')[0] })
  if (($consumerNames -join '|') -cne ($expectedChecks -join '|')) {
    throw 'PQ1-REGISTRY: independent consumer inventory differs from frozen registry'
  }
  $consumerPins = @([regex]::Matches($consumer, '(?m)^theorem (pin[A-Z][A-Za-z0-9]*)\b') |
    ForEach-Object { $_.Groups[1].Value })
  $planPinSection = [regex]::Matches((Read-Source $planPath), '(?s)## Definitional pins\r?\n(.*?)\r?\n## ')
  if ($planPinSection.Count -ne 1) { throw 'PQ1-REGISTRY: missing unique frozen pin section' }
  $planPins = @([regex]::Matches($planPinSection[0].Groups[1].Value, '\bpin[A-Z][A-Za-z0-9]*\b') |
    ForEach-Object { $_.Value })
  if (($consumerPins -join '|') -cne ($pinInventory -join '|') -or
      ($planPins -join '|') -cne ($pinInventory -join '|')) {
    throw 'PQ1-REGISTRY: definitional pin inventory differs between runner, plan and consumer'
  }
  foreach ($entry in @($Cases | Where-Object { $_.StartsWith('D') })) {
    $id = (Get-CaseParts $entry).Id
    if (-not $definitionCollapses.ContainsKey($id)) { throw "PQ1-REGISTRY: no collapse specification for $id" }
    $spec = $definitionCollapses[$id]
    $text = Read-Source $spec.File
    [void](Get-UniqueIndex $text (Convert-ToSourceNewlines $text $spec.Original) $id)
    if ($pinInventory -cnotcontains $spec.Check) { throw "PQ1-REGISTRY: $id names no inventoried pin" }
  }
  foreach ($entry in @($Cases | Where-Object { $_.StartsWith('R') })) {
    $id = (Get-CaseParts $entry).Id
    if (-not $projectionMutations.ContainsKey($id)) { throw "PQ1-REGISTRY: no projection specification for $id" }
    $spec = $projectionMutations[$id]
    $fields = Get-MarkedRegion $core 'FIELDS'
    $at = Get-UniqueIndex $core $spec.Original $id
    if ($at -lt $fields.Start -or $at -ge $fields.End) { throw "PQ1-REGISTRY: $id excerpt lies outside the field markers" }
    if ($expectedFields -cnotcontains $spec.Initializer) { throw "PQ1-REGISTRY: $id names no registered field" }
  }
  foreach ($entry in @($Cases | Where-Object { $_.StartsWith('N') })) {
    if ($runtimeNegativeIDs -cnotcontains (Get-CaseParts $entry).Id) {
      throw 'PQ1-REGISTRY: negative runtime case is not a frozen runtime control'
    }
  }
}

function Select-Cases([string[]]$Cases, [bool]$WasBound, [string]$Selector) {
  Assert-Registry $Cases
  if (-not $WasBound) { return $Cases }
  if ([string]::IsNullOrWhiteSpace($Selector)) { throw 'PQ1-SELECTOR: explicitly empty selector' }
  $selected = @($Cases | Where-Object { (Get-CaseParts $_).Id -ceq $Selector })
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

function Assert-RuntimeIDs([string[]]$IDs, [string[]]$NegativeIDs = $runtimeNegativeIDs) {
  $plan = Read-Source $planPath
  $section = [regex]::Matches($plan, '(?s)## Runtime registry\r?\n(.*?)\r?\nAll expect')
  $whole = [regex]::Matches($plan, '(?s)## Runtime registry\r?\n(.*?)\r?\n## ')
  if ($section.Count -ne 1 -or $whole.Count -ne 1) { throw 'PQ1-RUNTIME-REGISTRY: missing unique frozen section' }
  $planIDs = @([regex]::Matches($section[0].Groups[1].Value, 'S[0-9]{2}-[A-Z-]+') |
    ForEach-Object { $_.Value })
  $planNegative = @([regex]::Matches($whole[0].Groups[1].Value, 'N[0-9]{2}-[A-Z-]+') |
    ForEach-Object { $_.Value })
  if (($planIDs -join '|') -cne ($runtimeIDs -join '|') -or
      ($IDs -join '|') -cne ($runtimeIDs -join '|') -or
      ($planNegative -join '|') -cne ($runtimeNegativeIDs -join '|') -or
      ($NegativeIDs -join '|') -cne ($runtimeNegativeIDs -join '|')) {
    throw 'PQ1-RUNTIME-REGISTRY: missing, duplicate, changed or reordered runtime IDs'
  }
}

# A failed rfl pin is reported as a type mismatch and, for a theorem proved by
# rfl, also as "Not a definitional equality"; both are expected type rejections.
$typeRejectionPattern = '^\s*(type mismatch|application type mismatch|function expected|invalid field|invalid projection|Application type mismatch|Type mismatch|The rfl tactic failed|Not a definitional equality)\b'
$resourceFailurePattern = 'deep recursion|stack overflow|internal exception|interrupted|unknown module|object file.*does not exist|maximum.*(recursion|heartbeats)|out of memory'

function Get-LocatedTypeErrors([string]$Output, [string]$FilePattern, [string]$Label) {
  $errors = [regex]::Matches($Output, '(?m)^' + $FilePattern + ':(\d+):\d+: error:([^\r\n]*)')
  if ($errors.Count -eq 0) { throw "PQ1-REJECTION: no $Label diagnostics" }
  foreach ($diagnostic in $errors) {
    if ($diagnostic.Groups[2].Value -notmatch $typeRejectionPattern) {
      throw 'PQ1-REJECTION: unrecognized diagnostic cannot count as type rejection'
    }
  }
  # Resource/setup failures can accompany an ordinary type mismatch. Inspect
  # the complete output as well as whitelisting each located diagnostic.
  if ($Output -match $resourceFailurePattern) {
    throw 'PQ1-REJECTION: setup/resource failure cannot count as type rejection'
  }
  return $errors
}

function Get-ConsumerTypeErrors([string]$Output) {
  return Get-LocatedTypeErrors $Output 'RMQ[/\\]Validation[/\\]PackedQueryContract\.lean' 'typed-client'
}

function Get-ProducerTypeErrors([string]$Output) {
  return Get-LocatedTypeErrors $Output 'RMQ[/\\]Core[/\\]WordRAM[/\\]Packed[/\\]Capstone\.lean' 'producer'
}

function Get-LineOf([string]$Text, [int]$Index) {
  return ($Text.Substring(0, $Index) -split "`n").Count
}

# Lines [Start, End) of one initializer entry, in the text that was compiled.
function Get-InitializerSpan([string]$Text, [string]$Field) {
  $region = Get-MarkedRegion $Text 'INITIALIZERS'
  $entries = [regex]::Matches($region.Text, '(?m)^  ([A-Za-z][A-Za-z0-9]*)(?: [^\r\n]*?)? :=')
  $target = @($entries | Where-Object { $_.Groups[1].Value -ceq $Field })
  if ($target.Count -ne 1) { throw "PQ1-MUTATION: expected one initializer for $Field" }
  $next = @($entries | Where-Object { $_.Index -gt $target[0].Index } | Select-Object -First 1)
  $endIndex = if ($next.Count -eq 0) { $region.End } else { $region.Start + $next[0].Index }
  return [pscustomobject]@{
    Start = Get-LineOf $Text ($region.Start + $target[0].Index)
    End = Get-LineOf $Text $endIndex
  }
}

function Assert-ProducerRejection([object]$Result, [string]$Text, [string]$Field) {
  if ($Result.ExitCode -eq 0) { throw "PQ1-MUTATION: producer accepted the $Field projection change" }
  $span = Get-InitializerSpan $Text $Field
  $errors = @(Get-ProducerTypeErrors ($Result.Output -join "`n"))
  $outside = @($errors | Where-Object { [int]$_.Groups[1].Value -lt $span.Start -or [int]$_.Groups[1].Value -ge $span.End })
  if ($outside.Count -ne 0) {
    throw "PQ1-MUTATION: producer rejection did not occur only at the $Field initializer"
  }
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

function Invoke-RegistryTests {
  Assert-Registry $registry
  $last = $registryCount - 1
  Expect-Rejection { Assert-Registry @($registry[1..$last]) } 'PQ1-REGISTRY:'
  Expect-Rejection { Assert-Registry @($registry[0..($last - 1)] + $registry[0]) } 'PQ1-REGISTRY:'
  Expect-Rejection { Assert-Registry @($registry + 'EXTRA|bad|REJECT|PackedQueryContract.lean') } 'PQ1-REGISTRY:'
  $reordered = @($registry); $reordered[0] = $registry[1]; $reordered[1] = $registry[0]
  Expect-Rejection { Assert-Registry $reordered } 'PQ1-REGISTRY:'
  $resurfaced = @($registry); $resurfaced[$last] = $registry[$last].Replace('PackedQueryRuntime.lean', 'PackedQueryContract.lean')
  Expect-Rejection { Assert-Registry $resurfaced } 'PQ1-REGISTRY:'
  $extraField = (Read-Source $corePath).Replace('  -- PQ1-REPLAY-FIELDS-END',
    "  -- PQ1-REPLAY-FIELDS-END`n  unregisteredField : True")
  Expect-Rejection { Assert-Registry $registry $extraField } 'PQ1-REGISTRY:'
  $extraInitializer = (Read-Source $corePath).Replace('  -- PQ1-REPLAY-INITIALIZERS-END',
    "  -- PQ1-REPLAY-INITIALIZERS-END`n  unregisteredField := True.intro")
  Expect-Rejection { Assert-Registry $registry $extraInitializer } 'PQ1-REGISTRY:'
  # Legal Lean names outside the former ASCII-only subset, both inside and
  # outside each marked inventory. Escaped names can contain whitespace.
  $extraNames = @('unregistered_field', "unregisteredField'",
    ([string][char]0x03B1), ([string][char]0x00AB + 'extra field' + [char]0x00BB))
  foreach ($name in $extraNames) {
    foreach ($kind in @('FIELDS', 'INITIALIZERS')) {
      $marker = "  -- PQ1-REPLAY-$kind-END"
      $member = if ($kind -ceq 'FIELDS') { "  $name : True" } else { "  $name := True.intro" }
      foreach ($replacement in @("$member`n$marker", "$marker`n$member")) {
        $extra = (Read-Source $corePath).Replace($marker, $replacement)
        Expect-Rejection { Assert-Registry $registry $extra } 'PQ1-REGISTRY:'
      }
    }
  }
  $unsupportedLayout = (Read-Source $corePath).Replace(
    '  allocationResidualLittleO :', '   allocationResidualLittleO :')
  Expect-Rejection { Assert-Registry $registry $unsupportedLayout } 'PQ1-REGISTRY:'
  $missingPin = (Read-Source $consumerPath).Replace('theorem pinIsReadWord', 'theorem unpinnedIsReadWord')
  Expect-Rejection { Assert-Registry $registry '' $missingPin } 'PQ1-REGISTRY:'
  $extraPin = (Read-Source $consumerPath) + "`ntheorem pinExtra : True := trivial`n"
  Expect-Rejection { Assert-Registry $registry '' $extraPin } 'PQ1-REGISTRY:'
  $missingCheck = (Read-Source $consumerPath).Replace('theorem checkC32 ', 'theorem uncheckedC32 ')
  Expect-Rejection { Assert-Registry $registry '' $missingCheck } 'PQ1-REGISTRY:'
  # Each literal mutation applies to either checkout newline style and changes the text.
  foreach ($spec in @(@($definitionCollapses.Values) + @($projectionMutations.Values))) {
    $plain = (Read-Source $spec.File).Replace("`r`n", "`n")
    foreach ($variant in @($plain, $plain.Replace("`n", "`r`n"))) {
      $mutated = Replace-Unique $variant $spec.Original $spec.Replacement 'mutation fixture'
      if ($mutated -ceq $variant) { throw 'PQ1-SELFTEST: literal mutation did not change the source' }
    }
  }
  Expect-Rejection { Replace-Unique 'no excerpt here' 'absent' 'x' 'fixture' } 'PQ1-REGISTRY:'
  Expect-Rejection { Replace-Unique 'twice twice' 'twice' 'x' 'fixture' } 'PQ1-REGISTRY:'
  $movedProjection = (Read-Source $corePath).Replace($projectionMutations['R01-SPEC-PROJECTION'].Original,
    $projectionMutations['R01-SPEC-PROJECTION'].Replacement)
  Expect-Rejection { Assert-Registry $registry $movedProjection } 'PQ1-REGISTRY:'
  foreach ($bad in @('', ' ', "`t", 'UNKNOWN')) {
    Expect-Rejection { Select-Cases $registry $true $bad } 'PQ1-SELECTOR:'
  }
  $control = @(Select-Cases $registry $true 'A01-UNCHANGED-CONTRACT')
  $full = @(Select-Cases $registry $false '')
  if ($control.Count -ne 1 -or $control[0] -cne $registry[$fieldCaseCount + 1] -or $full.Count -ne $registryCount) {
    throw 'PQ1-SELFTEST: focused/full selector control failed'
  }
  Assert-RuntimeIDs $runtimeIDs
  $lastRuntime = $runtimeIDs.Count - 1
  Expect-Rejection { Assert-RuntimeIDs @($runtimeIDs[1..$lastRuntime]) } 'PQ1-RUNTIME-REGISTRY:'
  Expect-Rejection { Assert-RuntimeIDs @($runtimeIDs[0..($lastRuntime - 1)] + $runtimeIDs[0]) } 'PQ1-RUNTIME-REGISTRY:'
  $reorderedRuntime = @($runtimeIDs); $reorderedRuntime[0] = $runtimeIDs[1]; $reorderedRuntime[1] = $runtimeIDs[0]
  Expect-Rejection { Assert-RuntimeIDs $reorderedRuntime } 'PQ1-RUNTIME-REGISTRY:'
  Expect-Rejection { Assert-RuntimeIDs $runtimeIDs @() } 'PQ1-RUNTIME-REGISTRY:'
  foreach ($diagnostic in @('(kernel) deep recursion detected', 'stack overflow',
      'internal exception', 'interrupted', 'unknown module Missing', 'maximum heartbeats exceeded')) {
    Expect-Rejection { Get-ConsumerTypeErrors "RMQ/Validation/PackedQueryContract.lean:18:1: error: $diagnostic" } 'PQ1-REJECTION:'
  }
  foreach ($diagnostic in @('type mismatch', 'application type mismatch', 'function expected', 'invalid field',
      'Not a definitional equality: the left-hand side')) {
    $positive = @(Get-ConsumerTypeErrors "RMQ/Validation/PackedQueryContract.lean:18:1: error: $diagnostic")
    if ($positive.Count -ne 1) { throw 'PQ1-SELFTEST: diagnostic success control failed' }
  }
  $core = Read-Source $corePath
  $span = Get-InitializerSpan $core 'specResult'
  $inside = [pscustomobject]@{ ExitCode=1; Output=@("RMQ/Core/WordRAM/Packed/Capstone.lean:$($span.Start):2: error: type mismatch") }
  Assert-ProducerRejection $inside $core 'specResult'
  $outsideLine = $span.End + 1
  $outside = [pscustomobject]@{ ExitCode=1; Output=@("RMQ/Core/WordRAM/Packed/Capstone.lean:$($outsideLine):2: error: type mismatch") }
  Expect-Rejection { Assert-ProducerRejection $outside $core 'specResult' } 'PQ1-MUTATION:'
  $accepted = [pscustomobject]@{ ExitCode=0; Output=@() }
  Expect-Rejection { Assert-ProducerRejection $accepted $core 'specResult' } 'PQ1-MUTATION:'
  # The located pin diagnostics observed for the D01 collapse count only at their own pin.
  $consumerText = Read-Source $consumerPath
  $pinLine = Get-LineOf $consumerText $consumerText.IndexOf('theorem pinInstructionCategory')
  $pinResult = [pscustomobject]@{ ExitCode=1; Output=@(
    "RMQ/Validation/PackedQueryContract.lean:$($pinLine):0: error: Not a definitional equality: the left-hand side",
    "RMQ/Validation/PackedQueryContract.lean:$($pinLine):32: error: type mismatch") }
  Assert-ConsumerRejection $pinResult 'pinInstructionCategory' $false
  Expect-Rejection { Assert-ConsumerRejection $pinResult 'pinInstructionOperands' $false } 'PQ1-MUTATION:'
  Write-Host 'PQ1-REGISTRY SELF-TEST PASS missing/duplicate/extra/reordered/resurfaced/outside-markers/pins/checks/projection/empty/whitespace/unknown/focused/full'
  Write-Host 'PQ1-REJECTION SELF-TEST PASS runtime IDs, producer span and typed/resource diagnostic controls'
}

# Exercises the real script boundary: a bounded child of the same shell calls
# this script with an explicitly bound selector. An empty, whitespace or unknown
# value must fail with the selector diagnostic before any Lean stage; a valid
# value must select exactly that case; omission must select every case.
function Invoke-SelectorBoundaryTests {
  $boundaryRoot = Join-Path $repoRoot ('.lake/pq1-replay/boundary-' + [Guid]::NewGuid().ToString('N'))
  [void][IO.Directory]::CreateDirectory($boundaryRoot)
  $shellPath = (Get-Process -Id $PID).Path
  $wrapperPath = Join-Path $boundaryRoot 'selector-boundary-wrapper.ps1'
  $wrapper = @'
param([string]$Target, [string]$Mode)
$ErrorActionPreference = 'Continue'
switch ($Mode) {
  'omitted' { & $Target -SelectorProbeOnly }
  'empty' { & $Target -SelectorProbeOnly -OnlyCase '' }
  'whitespace' { & $Target -SelectorProbeOnly -OnlyCase ' ' }
  'unknown' { & $Target -SelectorProbeOnly -OnlyCase 'UNKNOWN' }
  'valid' { & $Target -SelectorProbeOnly -OnlyCase 'C31-SPEC-RESULT' }
  'empty-runtime' { & $Target -RuntimeOnly -OnlyCase '' }
  default { throw "unknown boundary wrapper mode $Mode" }
}
exit ([int]$LASTEXITCODE)
'@
  [IO.File]::WriteAllText($wrapperPath, $wrapper, $utf8)
  $cases = @(
    [pscustomobject]@{ Mode='omitted'; Exit=0; Token="PQ1-SELECTOR PROBE PASS bound=False selected=$registryCount" },
    [pscustomobject]@{ Mode='valid'; Exit=0; Token='PQ1-SELECTOR PROBE PASS bound=True selected=1 ids=C31-SPEC-RESULT' },
    [pscustomobject]@{ Mode='empty'; Exit=1; Token='PQ1-SELECTOR: explicitly empty selector' },
    [pscustomobject]@{ Mode='whitespace'; Exit=1; Token='PQ1-SELECTOR: explicitly empty selector' },
    [pscustomobject]@{ Mode='unknown'; Exit=1; Token='PQ1-SELECTOR: unknown selector UNKNOWN' },
    [pscustomobject]@{ Mode='empty-runtime'; Exit=1; Token='PQ1-SELECTOR: explicitly empty selector' }
  )
  try {
    foreach ($case in $cases) {
      $result = Invoke-RMQOwnedBoundedProcess -FilePath $shellPath `
        -Arguments @('-NoLogo', '-NoProfile', '-ExecutionPolicy', 'Bypass', '-File', $wrapperPath,
          '-Target', (Join-Path $PSScriptRoot 'packed_query_replay.ps1'), '-Mode', $case.Mode) `
        -WorkingDirectory $repoRoot -Stage "selector-boundary-$($case.Mode)" -DeadlineSeconds 120 `
        -OutputLimitBytes 1048576 -TempRoot $boundaryRoot
      $joined = $result.Output -join "`n"
      if ($result.TimedOut -or $result.OutputLimitExceeded -or $result.ExitCode -ne $case.Exit -or
          -not $joined.Contains($case.Token)) {
        throw ("PQ1-BOUNDARY: $($case.Mode) expected exit=$($case.Exit) token='$($case.Token)'; " +
          "observed exit=$($result.ExitCode) timeout=$($result.TimedOut) output=$joined")
      }
      if ($joined -match 'PQ1-REPLAY CASE|PQ1-STAGE|PQ1-RUNTIME|PQ1-DEADLINE|OWNED-PROCESS') {
        throw "PQ1-BOUNDARY: $($case.Mode) reached a stage beyond selection"
      }
      Write-Host "PQ1-BOUNDARY CONTROL PASS [$($case.Mode)] exit=$($result.ExitCode)"
    }
  } finally {
    Remove-Item -LiteralPath $boundaryRoot -Recurse -Force -ErrorAction SilentlyContinue
  }
  $edition = $PSVersionTable.PSEdition
  Write-Host "PQ1-BOUNDARY SELF-TEST PASS host=$edition/$($PSVersionTable.PSVersion) omitted/valid/empty/whitespace/unknown/empty-runtime"
}

function Get-Sha256Hex([byte[]]$Bytes) {
  $hasher = [Security.Cryptography.SHA256]::Create()
  try { return ([BitConverter]::ToString($hasher.ComputeHash($Bytes))).Replace('-', '').ToLowerInvariant() }
  finally { $hasher.Dispose() }
}

# Raw committed bytes of one blob. The standard output stream is copied as
# bytes, never decoded, so no shell re-encoding or newline conversion applies.
function Read-GitBlobBytes([string]$GitPath, [string]$Spec, [int]$DeadlineSeconds = 60) {
  $info = New-Object Diagnostics.ProcessStartInfo
  $info.FileName = $GitPath
  $info.Arguments = 'cat-file blob "' + $Spec + '"'
  $info.WorkingDirectory = $repoRoot
  $info.UseShellExecute = $false
  $info.RedirectStandardOutput = $true
  $info.RedirectStandardError = $true
  $info.CreateNoWindow = $true
  $process = [Diagnostics.Process]::Start($info)
  try {
    $buffer = New-Object IO.MemoryStream
    $copy = $process.StandardOutput.BaseStream.CopyToAsync($buffer)
    $errorText = $process.StandardError.ReadToEndAsync()
    if (-not $process.WaitForExit($DeadlineSeconds * 1000) -or -not $copy.Wait($DeadlineSeconds * 1000)) {
      throw "PQ1-PROVENANCE: reading $Spec exceeded $DeadlineSeconds seconds"
    }
    $process.WaitForExit()
    if ($process.ExitCode -ne 0) { throw "PQ1-PROVENANCE: git cat-file $Spec failed: $($errorText.Result)" }
    return ,$buffer.ToArray()
  } finally {
    if (-not $process.HasExited) { $process.Kill(); [void]$process.WaitForExit(10000) }
    $process.Dispose()
  }
}

function Test-ManifestEntry([byte[]]$Bytes, [object]$Entry) {
  return ($Bytes.Length -eq [long]$Entry.bytes) -and ((Get-Sha256Hex $Bytes) -ceq [string]$Entry.sha256)
}

# Lean-free provenance check of the imported RC6 experiment against the
# committed blobs of HEAD (or of -ProvenanceRevision, for a known-bad control),
# so a working-copy normalization cannot mask a bad commit or the reverse.
function Invoke-ProvenanceSelfTest {
  $git = Resolve-RMQScalarApplicationPath (Get-Command git -CommandType Application) 'git'
  $head = @(Invoke-RMQCheckedGit $git $repoRoot @('rev-parse', '--verify', "$ProvenanceRevision^{commit}") `
    'provenance-head' 30 1048576 (Join-Path $repoRoot '.lake/pq1-replay'))[0]
  $manifestBytes = Read-GitBlobBytes $git "${head}:$experimentPath/manifest.json"
  $manifest = $utf8.GetString($manifestBytes) | ConvertFrom-Json
  $names = @($manifest.PSObject.Properties | ForEach-Object { $_.Name })
  if ($names.Count -ne $experimentEntryCount) {
    throw "PQ1-PROVENANCE: manifest lists $($names.Count) entries, expected $experimentEntryCount"
  }
  $tracked = @(Invoke-RMQCheckedGit $git $repoRoot @('ls-tree', '--name-only', "${head}:$experimentPath") `
    'provenance-tree' 30 1048576 (Join-Path $repoRoot '.lake/pq1-replay'))
  $expectedTracked = @(@($names) + @('manifest.json', '.gitattributes') | Sort-Object)
  if ((@($tracked | Sort-Object) -join '|') -cne ($expectedTracked -join '|')) {
    throw 'PQ1-PROVENANCE: committed experiment directory differs from the manifest inventory'
  }
  $failures = [Collections.Generic.List[string]]::new()
  $firstBytes = $null
  foreach ($name in $names) {
    $bytes = Read-GitBlobBytes $git "${head}:$experimentPath/$name"
    if ($null -eq $firstBytes) { $firstBytes = $bytes }
    if (-not (Test-ManifestEntry $bytes $manifest.$name)) { $failures.Add($name) }
  }
  if ($failures.Count -ne 0) {
    throw "PQ1-PROVENANCE: $($failures.Count) committed blobs fail the manifest: $($failures -join ', ')"
  }
  # The comparison is not vacuous: one flipped byte and one appended byte fail.
  $flipped = [byte[]]$firstBytes.Clone(); $flipped[0] = $flipped[0] -bxor 1
  $appended = [byte[]]($firstBytes + [byte]10)
  if ((Test-ManifestEntry $flipped $manifest.($names[0])) -or (Test-ManifestEntry $appended $manifest.($names[0]))) {
    throw 'PQ1-PROVENANCE: altered bytes were accepted'
  }
  Write-Host "PQ1-PROVENANCE SELF-TEST PASS entries=$($names.Count) source=$ProvenanceRevision=$head flipped/appended controls rejected"
}

# Selection precedes tool resolution or any child process. Even self-test
# modes reject an explicitly malformed production selector.
$selectedCases = @(Select-Cases $registry $onlyCaseBound $OnlyCase)
if ($SelectorProbeOnly) {
  $ids = @($selectedCases | ForEach-Object { (Get-CaseParts $_).Id }) -join ','
  Write-Host "PQ1-SELECTOR PROBE PASS bound=$onlyCaseBound selected=$($selectedCases.Count) ids=$ids"
  exit 0
}
if ($RegistrySelfTestOnly) { Invoke-RegistryTests; exit 0 }
if (($RuntimeOnly -or $DeadlineSelfTestOnly -or $SelectorBoundarySelfTestOnly -or $ProvenanceSelfTestOnly) -and
    $onlyCaseBound) {
  throw 'PQ1-SELECTOR: OnlyCase cannot be combined with runtime/deadline/boundary/provenance mode'
}
if ($SelectorBoundarySelfTestOnly) { Invoke-SelectorBoundaryTests; exit 0 }
if ($ProvenanceSelfTestOnly) { Invoke-ProvenanceSelfTest; exit 0 }

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
$lakePath = Resolve-RMQScalarApplicationPath (Get-Command lake -CommandType Application) 'lake'
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

# A definition collapse sits upstream of the whole packed closure, so the
# producer is rebuilt through Lake rather than by recompiling three files.
function Build-ProducerClosure([string]$Stage) {
  Require-Pass (Invoke-Stage $lakePath @('build', 'RMQPaper') "$Stage-lake" $ProducerRebuildDeadlineSeconds)
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

function Invoke-RuntimeStage([string]$Stage, [string]$Selector) {
  $environment = @{ LEAN_PATH=$cacheRoot }
  if ($Selector -cne '') { $environment[$runtimeSelectorVariable] = $Selector }
  return Invoke-Stage $LeanPath @('--run', $runtimePath) $Stage $RuntimeDeadlineSeconds $environment
}

# The runtime imports the array evaluator; rebuild its olean so a runtime-only
# invocation does not depend on which Lake targets were built before it.
function Initialize-RuntimeImports {
  Require-Pass (Invoke-Lean $arrayRunPath 'runtime-array-evaluator')
}

function Assert-RuntimeNegative([object]$Result, [string]$Id) {
  $joined = $Result.Output -join "`n"
  if ($Result.ExitCode -eq 0 -or -not $joined.Contains("${Id}: result mismatch") -or
      $joined.Contains("PQ1-RUNTIME CASE $Id PASS") -or $joined.Contains('PQ1-RUNTIME PASS') -or
      $joined -match $resourceFailurePattern) {
    throw "PQ1-RUNTIME: negative control $Id was not rejected by its result check: $joined"
  }
}

function Invoke-Runtime {
  Initialize-RuntimeImports
  $result = Invoke-RuntimeStage 'runtime-full' ''
  Require-Pass $result
  $joined = $result.Output -join "`n"
  $actualIDs = @([regex]::Matches($joined, '(?m)^PQ1-RUNTIME CASE (S[0-9]{2}-[A-Z-]+) PASS ') |
    ForEach-Object { $_.Groups[1].Value })
  Assert-RuntimeIDs $actualIDs
  $listIDs = @([regex]::Matches($joined, '(?m)^PQ1-RUNTIME LIST-RUN (S[0-9]{2}-[A-Z-]+) PASS ') |
    ForEach-Object { $_.Groups[1].Value })
  if (($listIDs -join '|') -cne ($runtimeListRunIDs -join '|')) {
    throw 'PQ1-RUNTIME: list-program execution controls are missing or changed'
  }
  $summary = "PQ1-RUNTIME PASS cases=$($runtimeIDs.Count) mode=full"
  if (@($result.Output | Where-Object { $_ -ceq $summary }).Count -ne 1 -or $joined -match 'N[0-9]{2}-[A-Z-]+') {
    throw 'PQ1-RUNTIME: full run did not report exactly the positive registry'
  }
  Write-Host "PQ1-RUNTIME full registry seconds=$($result.DurationSeconds) deadline=$RuntimeDeadlineSeconds"
  # Selectors travel through an environment channel as id:<ID>, because a host
  # may drop an empty native argument and silently turn a control into a full run.
  foreach ($control in @(
      [pscustomobject]@{ Label='empty'; Value='id:'; Token='PQ1-RUNTIME explicitly empty selector' },
      [pscustomobject]@{ Label='whitespace'; Value='id: '; Token='PQ1-RUNTIME explicitly empty selector' },
      [pscustomobject]@{ Label='unknown'; Value='id:UNKNOWN'; Token='PQ1-RUNTIME unknown selector' },
      [pscustomobject]@{ Label='malformed'; Value='S05-REVERSED'; Token='PQ1-RUNTIME malformed selector channel' })) {
    $bad = Invoke-RuntimeStage "runtime-selector-$($control.Label)" $control.Value
    $badText = $bad.Output -join "`n"
    if ($bad.ExitCode -eq 0 -or -not $badText.Contains($control.Token) -or $badText.Contains('PQ1-RUNTIME CASE ')) {
      throw "PQ1-RUNTIME: selector $($control.Label) control failed"
    }
  }
  $focused = Invoke-RuntimeStage 'runtime-selector-valid' 'id:S05-REVERSED'
  Require-Pass $focused
  $focusedIDs = @([regex]::Matches(($focused.Output -join "`n"), '(?m)^PQ1-RUNTIME CASE ([A-Z0-9-]+) PASS ') |
    ForEach-Object { $_.Groups[1].Value })
  if (($focusedIDs -join '|') -cne 'S05-REVERSED' -or
      @($focused.Output | Where-Object { $_ -ceq 'PQ1-RUNTIME PASS cases=1 mode=selected' }).Count -ne 1) {
    throw 'PQ1-RUNTIME: a valid selector did not run exactly its one fixture'
  }
  Write-Host 'PQ1-RUNTIME PASS full registry, list-program controls and empty/whitespace/unknown/malformed/valid selector controls'
}

Assert-Clean 'baseline'
$commit = @(Invoke-RMQCheckedGit $gitPath $repoRoot @('rev-parse','HEAD') 'source-commit' 30 1048576 $runRoot)[0]
$mutableFiles = @($corePath, $headlinePath) + @($definitionCollapses.Values | ForEach-Object { $_.File } | Sort-Object -Unique)
$saved = @{}
foreach ($path in @($mutableFiles + @($consumerPath, 'RMQPaper.lean', $planPath, $runtimePath,
    'scripts/packed_query_replay.ps1', 'scripts/packed_query_inventory_check.lean') | Sort-Object -Unique)) {
  $saved[$path] = [IO.File]::ReadAllBytes((Join-Path $repoRoot $path))
}
$caseResults = [Collections.Generic.List[object]]::new()
$completed = $false
try {
  if ($RuntimeOnly) { Invoke-Runtime } else {
    Invoke-RegistryTests
    if (-not $onlyCaseBound) {
      Invoke-SelectorBoundaryTests
      Invoke-ProvenanceSelfTest
      Invoke-DeadlineTest
    }
    Build-Public 'baseline'
    Require-Pass (Invoke-Lean 'scripts/packed_query_inventory_check.lean' 'baseline-field-inventory')
    Require-Pass (Invoke-Lean $consumerPath 'baseline-consumer')
    foreach ($entry in $selectedCases) {
      $case = Get-CaseParts $entry
      $id = $case.Id; $verdict = $case.Verdict
      try {
        if ($id.StartsWith('C')) {
          $text = $utf8.GetString($saved[$corePath])
          $text = Weaken-Field $text 'FIELDS' $case.Target
          $text = Weaken-Field $text 'INITIALIZERS' $case.Target
          [IO.File]::WriteAllText((Join-Path $repoRoot $corePath), $text, $utf8)
          Build-Public $id
          Assert-ConsumerRejection (Invoke-Lean $consumerPath "$id-consumer") ('check' + ($id -split '-')[0]) $false
        } elseif ($id -eq 'P01-PUBLIC-ALIAS-TRUE') {
          $text = $utf8.GetString($saved[$headlinePath])
          $pattern = '(?ms)^-- PQ1-REPLAY-PUBLIC-BEGIN\r?\n.*?^-- PQ1-REPLAY-PUBLIC-END'
          if ([regex]::Matches($text, $pattern).Count -ne 1) { throw 'PQ1-MUTATION: public alias markers missing/duplicate' }
          $replacement = "-- PQ1-REPLAY-PUBLIC-BEGIN`nabbrev succinctRMQFullyChargedPackedQuery : True := True.intro`n-- PQ1-REPLAY-PUBLIC-END"
          [IO.File]::WriteAllText((Join-Path $repoRoot $headlinePath), [regex]::Replace($text, $pattern, $replacement), $utf8)
          Build-Public $id
          Assert-ConsumerRejection (Invoke-Lean $consumerPath "$id-consumer") 'publicContract' $true
        } elseif ($id -eq 'A01-UNCHANGED-CONTRACT') {
          Build-Public $id
          Require-Pass (Invoke-Lean $consumerPath "$id-consumer")
        } elseif ($id.StartsWith('D')) {
          $spec = $definitionCollapses[$id]
          $pristine = $utf8.GetString($saved[$spec.File])
          $text = Replace-Unique $pristine $spec.Original $spec.Replacement $id
          [IO.File]::WriteAllText((Join-Path $repoRoot $spec.File), $text, $utf8)
          Build-ProducerClosure $id
          Assert-ConsumerRejection (Invoke-Lean $consumerPath "$id-consumer") $spec.Check $false
        } elseif ($id.StartsWith('R')) {
          $spec = $projectionMutations[$id]
          $pristine = $utf8.GetString($saved[$spec.File])
          $text = Replace-Unique $pristine $spec.Original $spec.Replacement $id
          [IO.File]::WriteAllText((Join-Path $repoRoot $spec.File), $text, $utf8)
          Assert-ProducerRejection (Invoke-Lean $spec.File "$id-core") $text $spec.Initializer
        } elseif ($id.StartsWith('N')) {
          Initialize-RuntimeImports
          Assert-RuntimeNegative (Invoke-RuntimeStage "$id-runtime" "id:$id") $id
        } else {
          throw "PQ1-MUTATION: no handler for $id"
        }
        $caseResults.Add([pscustomobject]@{ Id=$id; Target=$case.Target; Expected=$verdict; Actual=$verdict; Surface=$case.Surface })
      } finally {
        foreach ($path in $mutableFiles) { [IO.File]::WriteAllBytes((Join-Path $repoRoot $path), $saved[$path]) }
        foreach ($path in $saved.Keys) {
          $bytes = [IO.File]::ReadAllBytes((Join-Path $repoRoot $path))
          if ([Convert]::ToBase64String($bytes) -cne [Convert]::ToBase64String($saved[$path])) {
            throw "PQ1-RESTORE: byte mismatch in $path"
          }
        }
        # A runtime control mutates nothing; every other case rebuilds the
        # restored producer before the unchanged consumer must accept again.
        if ($id.StartsWith('D')) { Build-ProducerClosure "$id-restored" }
        elseif (-not $id.StartsWith('N')) { Build-Public "$id-restored" }
        Require-Pass (Invoke-Lean $consumerPath "$id-restored-consumer")
        Assert-Clean "$id-clean"
      }
      Write-Host "PQ1-REPLAY CASE $id PASS expected=$verdict surface=$($case.Surface) restored=true"
    }
    if (-not $onlyCaseBound) { Invoke-Runtime }
  }
  Assert-Clean 'final'
  $completed = $true
} finally {
  $hashes = [ordered]@{}
  foreach ($path in ($saved.Keys | Sort-Object)) { $hashes[$path] = Get-Sha256Hex $saved[$path] }
  $report = [ordered]@{ SourceCommit=$commit; Completed=$completed; Registry=$registry; Selected=$selectedCases;
    Cases=@($caseResults.ToArray()); SourceHashes=$hashes; Stages=@($stageResults.ToArray()); ReportDirectory=$runRoot }
  [IO.File]::WriteAllText((Join-Path $runRoot 'report.json'), ($report | ConvertTo-Json -Depth 12), $utf8)
  Write-Host "PQ1-REPLAY REPORT $runRoot/report.json"
}
Write-Host "PQ1-REPLAY PASS source=$commit cases=$($caseResults.Count) clean=true"
