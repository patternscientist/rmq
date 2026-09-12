param(
  [AllowEmptyString()][string]$Case,
  [switch]$ListRegistry,
  [switch]$Prepare,
  [switch]$Startup,
  [switch]$ReplaySelectors,
  [int]$DeadlineSeconds = 180,
  [int]$CampaignDeadlineSeconds = 2700,
  [string]$EvidenceTag = ('v1-' + [DateTime]::UtcNow.ToString('yyyyMMddHHmmssfff') + '-' + [Guid]::NewGuid().ToString('N').Substring(0,8))
)
$ErrorActionPreference = 'Stop'
$fields = @('completeCapacity','overheadLittleO','widthBounds','memoryWordsFit','readerGeometry',
  'readerCorrect','accessCorrect','rankCorrect','selectCorrect','accessExecution','rankExecution',
  'selectExecution','accessSafety','rankSafety','selectSafety','programLengths','sourceBudgets',
  'stepsBound','categoryPartition','categoryBounds','finiteScratch','suppliedMemoryAgreement','validArgumentFits')
$caseNames = @('unchanged','harmless-comment') + @($fields | ForEach-Object { 'weaken-' + $_ }) +
  @('delete-accessCorrect','sibling-completeCapacity','sibling-selectSafety','sibling-readerCorrect',
    'public-proposition-True','capacity-without-code','capacity-without-scratch')
$expectedNames = @('unchanged','harmless-comment','weaken-completeCapacity','weaken-overheadLittleO',
  'weaken-widthBounds','weaken-memoryWordsFit','weaken-readerGeometry','weaken-readerCorrect',
  'weaken-accessCorrect','weaken-rankCorrect','weaken-selectCorrect','weaken-accessExecution',
  'weaken-rankExecution','weaken-selectExecution','weaken-accessSafety','weaken-rankSafety',
  'weaken-selectSafety','weaken-programLengths','weaken-sourceBudgets','weaken-stepsBound',
  'weaken-categoryPartition','weaken-categoryBounds','weaken-finiteScratch','weaken-suppliedMemoryAgreement',
  'weaken-validArgumentFits','delete-accessCorrect','sibling-completeCapacity','sibling-selectSafety',
  'sibling-readerCorrect','public-proposition-True','capacity-without-code','capacity-without-scratch')
if ($fields.Count -ne 23 -or $caseNames.Count -ne 32 -or
    @($caseNames | Select-Object -Unique).Count -ne 32 -or
    ($caseNames -join '|') -cne ($expectedNames -join '|')) { throw 'Exact version1 public registry mismatch.' }
$boundCase = $PSBoundParameters.ContainsKey('Case')
$modeCount = [int]$boundCase + [int][bool]$ListRegistry + [int][bool]$Prepare +
  [int][bool]$Startup + [int][bool]$ReplaySelectors
if ($modeCount -gt 1 -or ($boundCase -and ([string]::IsNullOrWhiteSpace($Case) -or
    $Case -cne $Case.Trim() -or -not ($caseNames -ccontains $Case)))) {
  [Console]::Error.WriteLine('BV1-PUBLIC-SELECTOR FAIL: choose one exact nonempty registry name or one mode')
  exit 2
}
if ($EvidenceTag -notmatch '^[a-z0-9-]+$' -or $DeadlineSeconds -lt 1 -or $DeadlineSeconds -gt 3600 -or
    $CampaignDeadlineSeconds -lt 1 -or $CampaignDeadlineSeconds -gt 7200) {
  throw 'Invalid evidence tag or deadline.'
}
if ($ListRegistry) {
  Write-Output ('BV1-PUBLIC-REGISTRY version=1 expected=32 cases=' + ($caseNames | ConvertTo-Json -Compress))
  exit 0
}
$repo = (Resolve-Path (Join-Path $PSScriptRoot '..')).Path
$root = Join-Path $repo 'docs/internal/extensions/bv1/controls/public_mutations'
[void](New-Item -ItemType Directory -Path $root -Force)
$utf8 = [Text.UTF8Encoding]::new($false,$true)
$capstonePath = 'RMQ/Core/WordRAM/Bitvector/Capstone.lean'
$consumerPath = 'docs/internal/extensions/bv1/controls/public_expected_type.lean'
$runnerPath = 'scripts/packed_bitvector_public_controls.ps1'
$pointerPath = Join-Path $root 'registry-v1.json'
$replayEpilogue = "`n-- Uniform replay-only elaborator unfolding boundary; propositions and semantics are unchanged.`nattribute [local irreducible] RMQ.PackedBitvector.program RMQ.PackedBitvector.Allocation.memory RMQ.PackedBitvector.Experiment.width`n"
function Hash-Bytes([byte[]]$Bytes) {
  return [Convert]::ToHexString([Security.Cryptography.SHA256]::HashData($Bytes))
}
function Hash-Text([string]$Value) { return Hash-Bytes ($utf8.GetBytes($Value)) }
function Read-Strict([string]$Path) {
  $bytes = [IO.File]::ReadAllBytes($Path)
  $value = $utf8.GetString($bytes)
  if ((Hash-Text $value) -cne (Hash-Bytes $bytes)) { throw "UTF8 byte identity failed: $Path" }
  return $value
}
function Write-Immutable([string]$Path,[string]$Value) {
  if (Test-Path -LiteralPath $Path) {
    if ((Hash-Bytes ([IO.File]::ReadAllBytes($Path))) -cne (Hash-Text $Value)) {
      throw "Immutable fixture mismatch: $Path"
    }
  } else {
    [void](New-Item -ItemType Directory -Path (Split-Path -Parent $Path) -Force)
    [IO.File]::WriteAllBytes($Path,$utf8.GetBytes($Value))
  }
}
function Get-Block([string]$Text,[string]$Kind,[string]$Field) {
  $pattern = '(?ms)^  -- BV1-' + $Kind + '-BEGIN ' + [regex]::Escape($Field) +
    '\r?\n.*?^  -- BV1-' + $Kind + '-END ' + [regex]::Escape($Field) + '(?:\r?\n|$)'
  $matches = [regex]::Matches($Text,$pattern)
  if ($matches.Count -ne 1) { throw "Expected one exact $Kind block for $Field" }
  return $matches[0].Value
}
function Replace-Exact([string]$Text,[string]$Before,[string]$After) {
  if ([string]::IsNullOrEmpty($Before) -or [regex]::Matches($Text,[regex]::Escape($Before)).Count -ne 1) {
    throw 'Replacement must identify exactly one nonempty baseline byte string.'
  }
  return $Text.Replace($Before,$After)
}
function Make-Block([string]$Kind,[string]$Field,[string]$Body) {
  return "  -- BV1-$Kind-BEGIN $Field`n$Body`n  -- BV1-$Kind-END $Field`n"
}
function Consumer-Pin([string]$Body,[string]$Field) {
  $lines = $Body -split "`n"
  $pattern = if ($Field -eq 'inhabitant') { '^  fullyChargedBitvectorCapstone_holds\s*$' }
    else { '\bc\.' + [regex]::Escape($Field) + '\b' }
  $found = @(for ($i=0; $i -lt $lines.Count; $i++) { if ($lines[$i] -match $pattern) { $i+1 } })
  if ($found.Count -ne 1) { throw "Independent consumer must contain one projection for $Field" }
  return [int]$found[0]
}
function Diagnostic-Classes([string]$Name) {
  if ($Name -in @('unchanged','harmless-comment')) { return @() }
  if ($Name -eq 'delete-accessCorrect') { return @('invalid field') }
  if ($Name.StartsWith('weaken-')) { return @('type mismatch','application type mismatch','function expected') }
  return @('type mismatch','application type mismatch')
}
function Diagnostic-Class([string]$Message) {
  foreach ($class in @('application type mismatch','type mismatch','function expected','invalid field')) {
    if ($Message -imatch ('^' + [regex]::Escape($class) + '\b')) { return $class }
  }
  return 'unexpected'
}
function Trust-Failures($OutputLines) {
  foreach ($line in $OutputLines) {
    if ($line -match 'sorryAx|declaration uses.+sorry') { $line; continue }
    if ($line -match 'depends on axioms: \[(?<axioms>[^\]]*)\]') {
      $names = @($Matches.axioms -split ',\s*' | Where-Object {$_ -ne ''})
      if (@($names | Where-Object {$_ -cnotin @('propext','Classical.choice','Quot.sound')}).Count -gt 0) { $line }
    }
  }
}

if ($Prepare) {
  $baseline = Read-Strict (Join-Path $repo $capstonePath)
  $consumer = Read-Strict (Join-Path $repo $consumerPath)
  $importMatches = [regex]::Matches($consumer,'(?m)^import RMQ\.Core\.WordRAM\.Bitvector\.Capstone\r?\n')
  if ($importMatches.Count -ne 1) { throw 'Expected precisely one removable Capstone import.' }
  $consumerBody = Replace-Exact $consumer $importMatches[0].Value ''
  $actualFields = @([regex]::Matches($baseline,'(?m)^  -- BV1-FIELD-BEGIN ([A-Za-z]+)\r?$') |
    ForEach-Object { $_.Groups[1].Value })
  $actualValues = @([regex]::Matches($baseline,'(?m)^  -- BV1-VALUE-BEGIN ([A-Za-z]+)\r?$') |
    ForEach-Object { $_.Groups[1].Value })
  if (($actualFields -join '|') -cne ($fields -join '|') -or ($actualValues -join '|') -cne ($fields -join '|')) {
    throw 'Capstone marked field/value order differs from the exact23 registry.'
  }
  foreach ($field in $fields) { [void](Consumer-Pin $consumerBody $field) }
  [void](Consumer-Pin $consumerBody 'inhabitant')
  $sourceHash = Hash-Text $baseline
  $consumerHash = Hash-Text $consumer
  $snapshotId = Hash-Text ($sourceHash + ':' + $consumerHash)
  $snapshotRoot = Join-Path $root ('snapshots/' + $snapshotId)
  Write-Immutable (Join-Path $snapshotRoot 'Capstone.lean') $baseline
  Write-Immutable (Join-Path $snapshotRoot 'public_expected_type.lean') $consumer
  $preparedCases = @()
  $preparedContent = @{}
  foreach ($name in $caseNames) {
    $mutant = $baseline
    $replacements = @()
    $field = ''
    $expectedExit = if ($name -in @('unchanged','harmless-comment')) { 0 } else { 1 }
    if ($name -eq 'harmless-comment') {
      $before = 'structure FullyChargedBitvectorCapstone : Prop where'
      $after = "-- Harmless version1 acceptance control; the proposition is unchanged.`n$before"
      $replacements += [ordered]@{before=$before;after=$after}
    } elseif ($name.StartsWith('weaken-')) {
      $field = $name.Substring(7)
      $replacements += [ordered]@{ before=(Get-Block $baseline 'FIELD' $field); after=(Make-Block 'FIELD' $field "  $field : True") }
      $replacements += [ordered]@{ before=(Get-Block $baseline 'VALUE' $field); after=(Make-Block 'VALUE' $field "  $field := True.intro") }
    } elseif ($name -eq 'delete-accessCorrect') {
      $field = 'accessCorrect'
      $replacements += [ordered]@{before=(Get-Block $baseline 'FIELD' $field);after=''}
      $replacements += [ordered]@{before=(Get-Block $baseline 'VALUE' $field);after=''}
    } elseif ($name -in @('sibling-completeCapacity','capacity-without-code','capacity-without-scratch')) {
      $field = 'completeCapacity'
      $memory = '(Allocation.memory bits).length'
      $code = '((program .access).map Instruction.encoding).flatten.length + ((program .rank).map Instruction.encoding).flatten.length + ((program .select).map Instruction.encoding).flatten.length'
      $full = "$memory + $code + (8271 + 3)"
      $smaller = if ($name -eq 'sibling-completeCapacity') { "((Allocation.memory bits).take 1).length + $code + (8271 + 3)" }
        elseif ($name -eq 'capacity-without-code') { "$memory + (8271 + 3)" }
        else { "$memory + $code" }
      $fieldBody = "  completeCapacity : ∀ bits : List Bool,`n    ($smaller) * Experiment.width bits.length ≤ bits.length + completeRho bits.length"
      $extra = if ($name -eq 'sibling-completeCapacity') {
        "    have hm : ((Allocation.memory bits).take 1).length ≤ (Allocation.memory bits).length := List.length_take_le' _ _`n"
      } else { '' }
      $valueBody = "  completeCapacity := by`n    intro bits`n    have hfull := complete_capacity bits`n    simp only [registerCount] at hfull`n${extra}    have hcount : $smaller ≤ $full := by omega`n    exact Nat.le_trans (Nat.mul_le_mul_right (Experiment.width bits.length) hcount) hfull"
      $replacements += [ordered]@{before=(Get-Block $baseline 'FIELD' $field);after=(Make-Block 'FIELD' $field $fieldBody)}
      $replacements += [ordered]@{before=(Get-Block $baseline 'VALUE' $field);after=(Make-Block 'VALUE' $field $valueBody)}
    } elseif ($name -eq 'sibling-selectSafety') {
      $field = 'selectSafety'
      $before = Get-Block $baseline 'FIELD' $field
      $after = $before.Replace('(program .select)','(program .access)').Replace('(source .select)','(source .access)').Replace('(initial .select target argument)','(initial .access false argument)')
      if ($after -ceq $before) { throw 'Select sibling did not change the actual program.' }
      $replacements += [ordered]@{before=$before;after=$after}
      $replacements += [ordered]@{before=(Get-Block $baseline 'VALUE' $field);after=(Make-Block 'VALUE' $field '  selectSafety := fun bits _target argument ha => canonical_access_execution_safe bits argument ha')}
    } elseif ($name -eq 'sibling-readerCorrect') {
      $field = 'readerCorrect'
      $fieldBody = "  readerCorrect : ∀ (bits : List Bool) (target : Bool) (regs : Registers),`n    regs 3 = target.toNat → regs 22 = Experiment.width bits.length →`n    access bits 0 = bits[0]?"
      $valueBody = '  readerCorrect := fun bits _target _regs _ht _hw => access_eq bits 0'
      $replacements += [ordered]@{before=(Get-Block $baseline 'FIELD' $field);after=(Make-Block 'FIELD' $field $fieldBody)}
      $replacements += [ordered]@{before=(Get-Block $baseline 'VALUE' $field);after=(Make-Block 'VALUE' $field $valueBody)}
    } elseif ($name -eq 'public-proposition-True') {
      $field = 'inhabitant'
      $matches = [regex]::Matches($baseline,'(?ms)^theorem fullyChargedBitvectorCapstone_holds : FullyChargedBitvectorCapstone where\r?\n.*?(?=^#print axioms fullyChargedBitvectorCapstone_holds)')
      if ($matches.Count -ne 1) { throw 'Expected one exact public theorem plus constructor.' }
      $replacements += [ordered]@{before=$matches[0].Value;after="theorem fullyChargedBitvectorCapstone_holds : True := True.intro`n`n"}
    }
    foreach ($replacement in $replacements) {
      $mutant = Replace-Exact $mutant $replacement.before $replacement.after
      $replacement.beforeSHA256 = Hash-Text $replacement.before
      $replacement.afterSHA256 = Hash-Text $replacement.after
      $replacement.beforeBytes = $utf8.GetByteCount($replacement.before)
      $replacement.afterBytes = $utf8.GetByteCount($replacement.after)
    }
    $constructor = $mutant + $replayEpilogue
    $joined = $constructor + "`n" + $consumerBody
    $offset = [regex]::Matches($constructor + "`n","`n").Count
    $line = if ($field) { $offset + (Consumer-Pin $consumerBody $field) } else { 0 }
    $preparedCases += [ordered]@{id=$name; field=$field; constructorExit=0; consumerExit=$expectedExit;
      expectedDiagnosticClasses=@(Diagnostic-Classes $name);
      expectedErrorLines=$(if ($field) {@($line)} else {@()}); consumerOriginalLine=$(if ($field) {Consumer-Pin $consumerBody $field} else {0});
      constructorFile=($name+'.constructor.lean');consumerFile=($name+'.consumer.lean');
      mutatedCapstoneSHA256=(Hash-Text $mutant);constructorSHA256=(Hash-Text $constructor);consumerSHA256=(Hash-Text $joined);
      consumerBodySHA256=(Hash-Text $consumerBody);replacements=$replacements}
    $preparedContent[$name] = @($constructor,$joined)
  }
  $manifest = [ordered]@{version=1;registry=$caseNames;fields=$fields;snapshotId=$snapshotId;
    capstonePath=$capstonePath;consumerPath=$consumerPath;capstoneSHA256=$sourceHash;consumerSHA256=$consumerHash;
    consumerRemovedImport=$importMatches[0].Value;consumerBodySHA256=(Hash-Text $consumerBody);
    replayEpilogue=$replayEpilogue;replayEpilogueSHA256=(Hash-Text $replayEpilogue);replayEpilogueBytes=$utf8.GetByteCount($replayEpilogue);
    replayBounds=[ordered]@{perLeanSeconds=180;omittedChildSeconds=2700;outerDriverSeconds=3000;leanResourceLimits='unchanged'};
    runnerSHA256=(Hash-Bytes ([IO.File]::ReadAllBytes($PSCommandPath)));cases=$preparedCases}
  $manifestText = $manifest | ConvertTo-Json -Depth 12
  $manifestHash = Hash-Text $manifestText
  $fixtureRoot = Join-Path $root ('fixtures/' + $manifestHash)
  foreach ($item in $preparedCases) {
    Write-Immutable (Join-Path $fixtureRoot $item.constructorFile) $preparedContent[$item.id][0]
    Write-Immutable (Join-Path $fixtureRoot $item.consumerFile) $preparedContent[$item.id][1]
  }
  Write-Immutable (Join-Path $root ('manifests/' + $manifestHash + '.json')) $manifestText
  [IO.File]::WriteAllText($pointerPath,([ordered]@{version=1;manifestSHA256=$manifestHash;snapshotId=$snapshotId} | ConvertTo-Json),$utf8)
  Write-Output "BV1-PUBLIC-PREPARED version=1 expected=32 manifest=$manifestHash snapshot=$snapshotId"
  exit 0
}

if (-not (Test-Path -LiteralPath $pointerPath)) { throw 'Prepare immutable baseline fixtures before replay.' }
$pointer = Read-Strict $pointerPath | ConvertFrom-Json
$manifestPath = Join-Path $root ('manifests/' + $pointer.manifestSHA256 + '.json')
$manifestText = Read-Strict $manifestPath
if ((Hash-Text $manifestText) -cne $pointer.manifestSHA256) { throw 'Manifest identity mismatch.' }
$manifest = $manifestText | ConvertFrom-Json
if ($manifest.version -ne 1 -or ($manifest.registry -join '|') -cne ($caseNames -join '|') -or
    ($manifest.cases.id -join '|') -cne ($caseNames -join '|') -or $manifest.cases.Count -ne 32) {
  throw 'Prepared registry differs from the exact version1 production registry.'
}
if ((Hash-Bytes ([IO.File]::ReadAllBytes($PSCommandPath))) -cne $manifest.runnerSHA256) { throw 'Runner changed: prepare a new immutable manifest before replay.' }
if ($manifest.replayBounds.perLeanSeconds -ne 180 -or $manifest.replayBounds.omittedChildSeconds -ne 2700 -or
    $manifest.replayBounds.outerDriverSeconds -ne 3000 -or $manifest.replayBounds.leanResourceLimits -cne 'unchanged' -or
    $DeadlineSeconds -ne 180 -or $CampaignDeadlineSeconds -ne 2700) { throw 'Replay bounds differ from the frozen measured campaign contract.' }
foreach ($pair in @(@($capstonePath,$manifest.capstoneSHA256),@($consumerPath,$manifest.consumerSHA256))) {
  if ((Hash-Bytes ([IO.File]::ReadAllBytes((Join-Path $repo $pair[0])))) -cne $pair[1]) {
    throw "Live baseline identity changed: $($pair[0])"
  }
}
$snapshotRoot = Join-Path $root ('snapshots/' + $manifest.snapshotId)
$baseline = Read-Strict (Join-Path $snapshotRoot 'Capstone.lean')
$consumer = Read-Strict (Join-Path $snapshotRoot 'public_expected_type.lean')
if ((Hash-Text $baseline) -cne $manifest.capstoneSHA256 -or (Hash-Text $consumer) -cne $manifest.consumerSHA256) { throw 'Immutable baseline identity mismatch.' }
$consumerBody = Replace-Exact $consumer $manifest.consumerRemovedImport ''
if ((Hash-Text $consumerBody) -cne $manifest.consumerBodySHA256) { throw 'Independent consumer body mismatch.' }
if ($manifest.replayEpilogue -cne $replayEpilogue -or
    $manifest.replayEpilogueSHA256 -cne (Hash-Text $replayEpilogue) -or
    $manifest.replayEpilogueBytes -ne $utf8.GetByteCount($replayEpilogue)) {
  throw 'Uniform replay-only reducibility boundary changed.'
}
$fixtureRoot = Join-Path $root ('fixtures/' + $pointer.manifestSHA256)
foreach ($item in $manifest.cases) {
  $requiredField = if ($item.id.StartsWith('weaken-')) { $item.id.Substring(7) }
    elseif ($item.id -eq 'delete-accessCorrect') { 'accessCorrect' }
    elseif ($item.id -in @('sibling-completeCapacity','capacity-without-code','capacity-without-scratch')) { 'completeCapacity' }
    elseif ($item.id -eq 'sibling-selectSafety') { 'selectSafety' }
    elseif ($item.id -eq 'sibling-readerCorrect') { 'readerCorrect' }
    elseif ($item.id -eq 'public-proposition-True') { 'inhabitant' } else { '' }
  $requiredExit = if ($item.id -in @('unchanged','harmless-comment')) { 0 } else { 1 }
  if ($item.field -cne $requiredField -or $item.constructorExit -ne 0 -or $item.consumerExit -ne $requiredExit -or
      $item.constructorFile -cne ($item.id+'.constructor.lean') -or $item.consumerFile -cne ($item.id+'.consumer.lean') -or
      ($item.expectedDiagnosticClasses -join '|') -cne ((@(Diagnostic-Classes $item.id)) -join '|')) {
    throw 'Manifest cannot override the independently frozen verdict or projection.'
  }
  $rebuilt = $baseline
  foreach ($replacement in $item.replacements) {
    if ((Hash-Text $replacement.before) -cne $replacement.beforeSHA256 -or
        (Hash-Text $replacement.after) -cne $replacement.afterSHA256 -or
        $utf8.GetByteCount($replacement.before) -ne $replacement.beforeBytes -or
        $utf8.GetByteCount($replacement.after) -ne $replacement.afterBytes) { throw 'Exact replacement bytes mismatch.' }
    $rebuilt = Replace-Exact $rebuilt $replacement.before $replacement.after
  }
  if ((Hash-Text $rebuilt) -cne $item.mutatedCapstoneSHA256) { throw 'Copied Capstone transformation identity mismatch.' }
  $rebuilt += $replayEpilogue
  if ((Hash-Text $rebuilt) -cne $item.constructorSHA256 -or
      (Hash-Text ($rebuilt+"`n"+$consumerBody)) -cne $item.consumerSHA256 -or
      (Hash-Bytes ([IO.File]::ReadAllBytes((Join-Path $fixtureRoot $item.constructorFile)))) -cne $item.constructorSHA256 -or
      (Hash-Bytes ([IO.File]::ReadAllBytes((Join-Path $fixtureRoot $item.consumerFile)))) -cne $item.consumerSHA256) {
    throw "Prepared fixture bytes mismatch: $($item.id)"
  }
  $requiredLines = if ($requiredField) {
    @([regex]::Matches($rebuilt+"`n","`n").Count + (Consumer-Pin $consumerBody $requiredField))
  } else { @() }
  if (($item.expectedErrorLines -join '|') -cne ($requiredLines -join '|')) { throw 'Independent consumer line pin changed.' }
}

. (Join-Path $PSScriptRoot 'owned_process_tree.ps1')
$runRoot = Join-Path $root ('records/' + $EvidenceTag)
if (Test-Path -LiteralPath $runRoot) { throw 'Evidence tag already exists; default timestamp/GUID tags are replayable.' }
[void](New-Item -ItemType Directory -Path $runRoot)
$toolBin = 'C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0/bin'
$startedUtc = [DateTime]::UtcNow.ToString('o')
$initialGlobalStatus = @(& git -C $repo status --porcelain=v1)
if ($LASTEXITCODE -ne 0) { throw 'Initial repository status failed.' }
$sourceSet = [Collections.Generic.HashSet[string]]::new([StringComparer]::OrdinalIgnoreCase)
$queue = [Collections.Generic.Queue[string]]::new()
$queue.Enqueue($capstonePath)
$queue.Enqueue($consumerPath)
while ($queue.Count -gt 0) {
  $relative = $queue.Dequeue()
  if (-not $sourceSet.Add($relative)) { continue }
  foreach ($match in [regex]::Matches((Read-Strict (Join-Path $repo $relative)),'(?m)^import[ \t]+([^\r\n]+)')) {
    foreach ($module in ($match.Groups[1].Value -split '[ \t]+')) {
      if ($module -eq '--') { break }
      if ($module -notmatch '^[A-Za-z_][A-Za-z0-9_.]*$') { continue }
      $path = $module.Replace('.','/') + '.lean'
      if (Test-Path -LiteralPath (Join-Path $repo $path) -PathType Leaf) { $queue.Enqueue($path) }
    }
  }
}
foreach ($path in @($runnerPath,'scripts/owned_process_tree.ps1','lean-toolchain','lakefile.toml')) { [void]$sourceSet.Add($path) }
$sourcePaths = @($sourceSet | Sort-Object)
$initialHashes = @($sourcePaths | ForEach-Object { [ordered]@{path=$_;sha256=(Hash-Bytes ([IO.File]::ReadAllBytes((Join-Path $repo $_))))} })
$initialStatus = @(& git -C $repo status --porcelain=v1 -- $sourcePaths)
if ($LASTEXITCODE -ne 0) { throw 'Initial scoped status failed.' }
& git -C $repo diff --check -- $sourcePaths
if ($LASTEXITCODE -ne 0) { throw 'Initial scoped whitespace failed.' }
$results = @()
$failure = $null
try {
  if ($ReplaySelectors) {
    $selectors = @(
      @{id='omitted';args=@();exit=0;surface='BV1-PUBLIC-SUMMARY version=1 executed=32 expected=32 passed=32 total=32'},
      @{id='valid';args=@('-Case','weaken-accessCorrect');exit=0;surface='BV1-PUBLIC-SUMMARY version=1 executed=1 expected=1 passed=1 total=32'},
      @{id='empty';args=@('-Case','');exit=2;surface='BV1-PUBLIC-SELECTOR FAIL'},
      @{id='whitespace';args=@('-Case','   ');exit=2;surface='BV1-PUBLIC-SELECTOR FAIL'},
      @{id='malformed';args=@('-Case','weaken accessCorrect');exit=2;surface='BV1-PUBLIC-SELECTOR FAIL'},
      @{id='unknown';args=@('-Case','no-such-case');exit=2;surface='BV1-PUBLIC-SELECTOR FAIL'},
      @{id='padded';args=@('-Case',' weaken-accessCorrect ');exit=2;surface='BV1-PUBLIC-SELECTOR FAIL'},
      @{id='incompatible';args=@('-Case','weaken-accessCorrect','-ListRegistry');exit=2;surface='BV1-PUBLIC-SELECTOR FAIL'})
    $expected = @('omitted','valid','empty','whitespace','malformed','unknown','padded','incompatible')
    if ($selectors.Count -ne 8 -or ($selectors.id -join '|') -cne ($expected -join '|')) { throw 'Exact eight-selector registry mismatch.' }
    foreach ($selector in $selectors) {
      $arguments = @('-NoProfile','-File',$PSCommandPath,'-DeadlineSeconds',"$DeadlineSeconds",'-CampaignDeadlineSeconds',"$CampaignDeadlineSeconds",'-EvidenceTag',($EvidenceTag+'-'+$selector.id)) + $selector.args
      $childDeadline = if ($selector.id -eq 'omitted') { $CampaignDeadlineSeconds } else { 2*$DeadlineSeconds+120 }
      $result = Invoke-RMQOwnedBoundedProcess -FilePath (Get-Command pwsh).Source -Arguments $arguments -WorkingDirectory $repo `
        -Stage ('public-selector-'+$selector.id+'-'+$EvidenceTag) -DeadlineSeconds $childDeadline -OutputLimitBytes 16777216 -TempRoot $runRoot
      $pass = -not $result.TimedOut -and -not $result.OutputLimitExceeded -and $result.ExitCode -eq $selector.exit -and
        (($result.Output -join "`n").Contains($selector.surface))
      $results += [ordered]@{id=$selector.id;expectedExit=$selector.exit;expectedSurface=$selector.surface;passed=$pass;result=$result}
      Write-Output "BV1-PUBLIC-SELECTOR-CONTROL $($selector.id) $pass"
    }
  } else {
    $selected = if ($Startup) { @('unchanged') } elseif ($boundCase) { @($Case) } else { $caseNames }
    $expected = $selected
    foreach ($name in $selected) {
      $item = @($manifest.cases | Where-Object {$_.id -ceq $name})
      if ($item.Count -ne 1) { throw 'Exactly one fixture must match each selected name.' }
      $item = $item[0]
      $constructorPath = Join-Path $fixtureRoot $item.constructorFile
      $joinedPath = Join-Path $fixtureRoot $item.consumerFile
      $constructor = Invoke-RMQOwnedBoundedProcess -FilePath (Join-Path $toolBin 'lake.exe') `
        -Arguments @('env','lean',$constructorPath) -WorkingDirectory $repo -Stage ($name+'-constructor-'+$EvidenceTag) `
        -DeadlineSeconds $DeadlineSeconds -OutputLimitBytes 8388608 -TempRoot $runRoot `
        -Environment @{PATH=$toolBin+';'+$env:PATH;LEAN_NUM_THREADS='1'}
      $constructorTrustFailures = @(Trust-Failures $constructor.Output)
      $constructorOK = $constructor.ExitCode -eq 0 -and -not $constructor.TimedOut -and
        -not $constructor.OutputLimitExceeded -and $constructorTrustFailures.Count -eq 0
      $consumerResult = $null
      $errors = @()
      $unparsedErrors = @()
      $resourceErrors = @()
      $consumerTrustFailures = @()
      $consumerOK = $false
      if ($constructorOK) {
        $consumerResult = Invoke-RMQOwnedBoundedProcess -FilePath (Join-Path $toolBin 'lake.exe') `
          -Arguments @('env','lean',$joinedPath) -WorkingDirectory $repo -Stage ($name+'-consumer-'+$EvidenceTag) `
          -DeadlineSeconds $DeadlineSeconds -OutputLimitBytes 8388608 -TempRoot $runRoot `
          -Environment @{PATH=$toolBin+';'+$env:PATH;LEAN_NUM_THREADS='1'}
        $errors = @($consumerResult.Output | ForEach-Object {
          if ($_ -match '^(?<path>.+\.lean):(?<line>\d+):(?<column>\d+): error: (?<message>.*)$') {
            $parsedMessage = $Matches.message
            $parsedPath = $Matches.path
            $parsedLine = [int]$Matches.line
            $parsedColumn = [int]$Matches.column
            [ordered]@{path=$parsedPath;line=$parsedLine;column=$parsedColumn;message=$parsedMessage;diagnosticClass=(Diagnostic-Class $parsedMessage)}
          }
        })
        $unparsedErrors = @($consumerResult.Output | Where-Object {
          $_ -match '(^|[ \t])error:' -and $_ -notmatch '^.+\.lean:\d+:\d+: error: '
        })
        $resourceErrors = @($consumerResult.Output | Where-Object {
          $_ -imatch 'deterministic timeout|maximum recursion depth|maxRecDepth|maximum number of heartbeats|maxHeartbeats|stack overflow|out of memory|resource exhausted|allocation failed|process interrupted'
        })
        if ($item.consumerExit -eq 0) { $consumerTrustFailures = @(Trust-Failures $consumerResult.Output) }
        $errorOK = if ($item.consumerExit -eq 0) { $errors.Count -eq 0 } else {
          $errors.Count -gt 0 -and @($errors | Where-Object {
            -not ($item.expectedErrorLines -contains $_.line) -or
              [IO.Path]::GetFileName($_.path) -cne $item.consumerFile -or
              -not ($item.expectedDiagnosticClasses -contains $_.diagnosticClass)
          }).Count -eq 0
        }
        $consumerOK = $consumerResult.ExitCode -eq $item.consumerExit -and -not $consumerResult.TimedOut -and
          -not $consumerResult.OutputLimitExceeded -and $unparsedErrors.Count -eq 0 -and $resourceErrors.Count -eq 0 -and
          $consumerTrustFailures.Count -eq 0 -and $errorOK
      }
      $pass = $constructorOK -and $consumerOK
      $entry = [ordered]@{id=$name;passed=$pass;constructorExpectedExit=0;consumerExpectedExit=$item.consumerExit;
        expectedErrorLines=$item.expectedErrorLines;expectedDiagnosticClasses=$item.expectedDiagnosticClasses;
        observedErrors=$errors;unparsedErrors=$unparsedErrors;resourceErrors=$resourceErrors;
        constructorTrustFailures=$constructorTrustFailures;consumerTrustFailures=$consumerTrustFailures;constructorPassed=$constructorOK;
        consumerPassed=$consumerOK;constructor=$constructor;consumer=$consumerResult}
      $results += $entry
      [IO.File]::WriteAllText((Join-Path $runRoot ($name+'.json')),($entry|ConvertTo-Json -Depth 16),$utf8)
      Write-Output "BV1-PUBLIC-CASE $name $(if ($pass) {'PASS'} else {'FAIL'}) version=1 constructor=$constructorOK consumer=$consumerOK"
    }
    $passedCount = @($results | Where-Object {$_.passed}).Count
    Write-Output "BV1-PUBLIC-SUMMARY version=1 executed=$($results.Count) expected=$($selected.Count) passed=$passedCount total=32"
    if ($Startup -and $passedCount -eq 1) { Write-Output 'BV1-PUBLIC-STARTUP version=1 expected=32' }
  }
} catch {
  $failure = $_.ToString()
} finally {
  $finalHashes = @($sourcePaths | ForEach-Object { [ordered]@{path=$_;sha256=(Hash-Bytes ([IO.File]::ReadAllBytes((Join-Path $repo $_))))} })
  $finalStatus = @(& git -C $repo status --porcelain=v1 -- $sourcePaths)
  $statusOK = $LASTEXITCODE -eq 0 -and ($initialStatus -join "`n") -ceq ($finalStatus -join "`n")
  & git -C $repo diff --check -- $sourcePaths
  $whitespaceOK = $LASTEXITCODE -eq 0
  $unchanged = ($initialHashes.sha256 -join '|') -ceq ($finalHashes.sha256 -join '|')
  $fixturesUnchanged = (Hash-Text (Read-Strict $manifestPath)) -ceq $pointer.manifestSHA256 -and
    (Hash-Text (Read-Strict (Join-Path $snapshotRoot 'Capstone.lean'))) -ceq $manifest.capstoneSHA256 -and
    (Hash-Text (Read-Strict (Join-Path $snapshotRoot 'public_expected_type.lean'))) -ceq $manifest.consumerSHA256
  foreach ($item in $manifest.cases) {
    $fixturesUnchanged = $fixturesUnchanged -and
      (Hash-Bytes ([IO.File]::ReadAllBytes((Join-Path $fixtureRoot $item.constructorFile)))) -ceq $item.constructorSHA256 -and
      (Hash-Bytes ([IO.File]::ReadAllBytes((Join-Path $fixtureRoot $item.consumerFile)))) -ceq $item.consumerSHA256
  }
  $allPassed = -not $failure -and $unchanged -and $fixturesUnchanged -and $statusOK -and $whitespaceOK -and
    $results.Count -eq $expected.Count -and ($results.id -join '|') -ceq ($expected -join '|') -and
    @($results | Where-Object {-not $_.passed}).Count -eq 0
  $record = [ordered]@{version=1;registry=$caseNames;manifestSHA256=$pointer.manifestSHA256;snapshotId=$manifest.snapshotId;
    evidenceTag=$EvidenceTag;mode=$(if ($ReplaySelectors) {'selectors'} elseif ($Startup) {'startup'} else {'cases'});
    startedUtc=$startedUtc;finishedUtc=[DateTime]::UtcNow.ToString('o');head=(& git -C $repo rev-parse HEAD).Trim();
    expected=$expected;executed=@($results.id);passed=$allPassed;failure=$failure;results=$results;
    sourceHashesBefore=$initialHashes;sourceHashesAfter=$finalHashes;exactRestoration=$unchanged;
    fixturesUnchanged=$fixturesUnchanged;scopedStatusBefore=$initialStatus;scopedStatusAfter=$finalStatus;
    scopedStatusRestored=$statusOK;whitespaceCheck=$whitespaceOK;baselineWasGloballyClean=($initialGlobalStatus.Count -eq 0);
    initialRepositoryStatus=$initialGlobalStatus;platform='Windows';leanNumThreads=1;deadlineSeconds=$DeadlineSeconds;campaignDeadlineSeconds=$CampaignDeadlineSeconds;
    cleanScope='Exact live public source import closure, immutable snapshots and generated fixtures; pre-existing shared changes preserved'}
  [IO.File]::WriteAllText((Join-Path $runRoot 'summary.json'),($record|ConvertTo-Json -Depth 20),$utf8)
}
Write-Output "BV1-PUBLIC-REPLAY version=1 executed=$($results.Count) expected=$($expected.Count) passed=$allPassed unchanged=$unchanged fixtures=$fixturesUnchanged statusRestored=$statusOK whitespace=$whitespaceOK"
if ($failure) { [Console]::Error.WriteLine($failure) }
if (-not $allPassed) { exit 1 }
